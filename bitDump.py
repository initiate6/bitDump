#!/usr/bin/env python
# bitDump.py - will dump a bitcoin wallet full report and bitcrack.conf.
# fulldump - will contain all the address and their current amount each bitcoin holds. if it has anything but zero it edits out the priv_Key for your protection
# bitcrack.conf is the configuration file for bitcrack.cpp that will help you crack the encrypted wallet.
#
# If you like this code please donate to [bitcoin address]
#
#stole code from PyWallet. Not really stealing when its public domain.
# PyWallet 1.2.1 (Public Domain)
# http://github.com/joric/pywallet
# Most of the actual PyWallet code placed in the public domain.
# PyWallet includes portions of free software, listed below.

from bsddb.db import *
import os, sys, time
import json
import logging
import struct
import StringIO
import traceback
import socket
import types
import string
import exceptions
import hashlib
import random
import math

max_version = 60000
addrtype = 0
json_db = {}
private_keys = []
password = None



# bitcointools hashes and base58 implementation

def hash_160(public_key):
    md = hashlib.new('ripemd160')
    md.update(hashlib.sha256(public_key).digest())
    return md.digest()

def public_key_to_bc_address(public_key):
    h160 = hash_160(public_key)
    return hash_160_to_bc_address(h160)

def hash_160_to_bc_address(h160):
    vh160 = chr(addrtype) + h160
    h = Hash(vh160)
    addr = vh160 + h[0:4]
    return b58encode(addr)

def bc_address_to_hash_160(addr):
    bytes = b58decode(addr, 25)
    return bytes[1:21]

__b58chars = '123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz'
__b58base = len(__b58chars)

def b58encode(v):
    """ encode v, which is a string of bytes, to base58.        
    """

    long_value = 0L
    for (i, c) in enumerate(v[::-1]):
        long_value += (256**i) * ord(c)

    result = ''
    while long_value >= __b58base:
        div, mod = divmod(long_value, __b58base)
        result = __b58chars[mod] + result
        long_value = div
    result = __b58chars[long_value] + result

    # Bitcoin does a little leading-zero-compression:
    # leading 0-bytes in the input become leading-1s
    nPad = 0
    for c in v:
        if c == '\0': nPad += 1
        else: break

    return (__b58chars[0]*nPad) + result

def b58decode(v, length):
    """ decode v into a string of len bytes
    """
    long_value = 0L
    for (i, c) in enumerate(v[::-1]):
        long_value += __b58chars.find(c) * (__b58base**i)

    result = ''
    while long_value >= 256:
        div, mod = divmod(long_value, 256)
        result = chr(mod) + result
        long_value = div
    result = chr(long_value) + result

    nPad = 0
    for c in v:
        if c == __b58chars[0]: nPad += 1
        else: break

    result = chr(0)*nPad + result
    if length is not None and len(result) != length:
        return None

    return result

# end of bitcointools base58 implementation


# address handling code

def Hash(data):
    return hashlib.sha256(hashlib.sha256(data).digest()).digest()

def EncodeBase58Check(secret):
    hash = Hash(secret)
    return b58encode(secret + hash[0:4])

def DecodeBase58Check(sec):
    vchRet = b58decode(sec, None)
    secret = vchRet[0:-4]
    csum = vchRet[-4:]
    hash = Hash(secret)
    cs32 = hash[0:4]
    if cs32 != csum:
        return None
    else:
        return secret

def PrivKeyToSecret(privkey):
    if len(privkey) == 279:
        return privkey[9:9+32]
    else:
        return privkey[8:8+32]

def SecretToASecret(secret, compressed=False):
    vchIn = chr((addrtype+128)&255) + secret
    if compressed: vchIn += '\01'
    return EncodeBase58Check(vchIn)

def ASecretToSecret(sec):
    vch = DecodeBase58Check(sec)
    if vch and vch[0] == chr((addrtype+128)&255):
        return vch[1:]
    else:
        return False

def regenerate_key(sec):
    b = ASecretToSecret(sec)
    if not b:
        return False
    b = b[0:32]
    secret = int('0x' + b.encode('hex'), 16)
    return EC_KEY(secret)

def GetPubKey(pkey, compressed=False):
    return i2o_ECPublicKey(pkey, compressed)

def GetPrivKey(pkey, compressed=False):
    return i2d_ECPrivateKey(pkey, compressed)

def GetSecret(pkey):
    return ('%064x' % pkey.secret).decode('hex')

def is_compressed(sec):
    b = ASecretToSecret(sec)
    return len(b) == 33

# bitcointools wallet.dat handling code

def create_env(db_dir):
    db_env = DBEnv(0)
    r = db_env.open(db_dir, (DB_CREATE|DB_INIT_LOCK|DB_INIT_LOG|DB_INIT_MPOOL|DB_INIT_TXN|DB_THREAD|DB_RECOVER))
    return db_env

def parse_CAddress(vds):
    d = {'ip':'0.0.0.0','port':0,'nTime': 0}
    try:
        d['nVersion'] = vds.read_int32()
        d['nTime'] = vds.read_uint32()
        d['nServices'] = vds.read_uint64()
        d['pchReserved'] = vds.read_bytes(12)
        d['ip'] = socket.inet_ntoa(vds.read_bytes(4))
        d['port'] = vds.read_uint16()
    except:
        pass
    return d

def deserialize_CAddress(d):
    return d['ip']+":"+str(d['port'])

def parse_BlockLocator(vds):
    d = { 'hashes' : [] }
    nHashes = vds.read_compact_size()
    for i in xrange(nHashes):
        d['hashes'].append(vds.read_bytes(32))
        return d

def deserialize_BlockLocator(d):
  result = "Block Locator top: "+d['hashes'][0][::-1].encode('hex_codec')
  return result

def parse_setting(setting, vds):
    if setting[0] == "f":    # flag (boolean) settings
        return str(vds.read_boolean())
    elif setting[0:4] == "addr": # CAddress
        d = parse_CAddress(vds)
        return deserialize_CAddress(d)
    elif setting == "nTransactionFee":
        return vds.read_int64()
    elif setting == "nLimitProcessors":
        return vds.read_int32()
    return 'unknown setting'

class SerializationError(Exception):
    """ Thrown when there's a problem deserializing or serializing """

class BCDataStream(object):
    def __init__(self):
        self.input = None
        self.read_cursor = 0

    def clear(self):
        self.input = None
        self.read_cursor = 0

    def write(self, bytes):    # Initialize with string of bytes
        if self.input is None:
            self.input = bytes
        else:
            self.input += bytes

    def map_file(self, file, start):    # Initialize with bytes from file
        self.input = mmap.mmap(file.fileno(), 0, access=mmap.ACCESS_READ)
        self.read_cursor = start
    def seek_file(self, position):
        self.read_cursor = position
    def close_file(self):
        self.input.close()

    def read_string(self):
        # Strings are encoded depending on length:
        # 0 to 252 :    1-byte-length followed by bytes (if any)
        # 253 to 65,535 : byte'253' 2-byte-length followed by bytes
        # 65,536 to 4,294,967,295 : byte '254' 4-byte-length followed by bytes
        # ... and the Bitcoin client is coded to understand:
        # greater than 4,294,967,295 : byte '255' 8-byte-length followed by bytes of string
        # ... but I don't think it actually handles any strings that big.
        if self.input is None:
            raise SerializationError("call write(bytes) before trying to deserialize")

        try:
            length = self.read_compact_size()
        except IndexError:
            raise SerializationError("attempt to read past end of buffer")

        return self.read_bytes(length)

    def write_string(self, string):
        # Length-encoded as with read-string
        self.write_compact_size(len(string))
        self.write(string)

    def read_bytes(self, length):
        try:
            result = self.input[self.read_cursor:self.read_cursor+length]
            self.read_cursor += length
            return result
        except IndexError:
            raise SerializationError("attempt to read past end of buffer")

        return ''

    def read_boolean(self): return self.read_bytes(1)[0] != chr(0)
    def read_int16(self): return self._read_num('<h')
    def read_uint16(self): return self._read_num('<H')
    def read_int32(self): return self._read_num('<i')
    def read_uint32(self): return self._read_num('<I')
    def read_int64(self): return self._read_num('<q')
    def read_uint64(self): return self._read_num('<Q')

    def write_boolean(self, val): return self.write(chr(1) if val else chr(0))
    def write_int16(self, val): return self._write_num('<h', val)
    def write_uint16(self, val): return self._write_num('<H', val)
    def write_int32(self, val): return self._write_num('<i', val)
    def write_uint32(self, val): return self._write_num('<I', val)
    def write_int64(self, val): return self._write_num('<q', val)
    def write_uint64(self, val): return self._write_num('<Q', val)

    def read_compact_size(self):
        size = ord(self.input[self.read_cursor])
        self.read_cursor += 1
        if size == 253:
            size = self._read_num('<H')
        elif size == 254:
            size = self._read_num('<I')
        elif size == 255:
            size = self._read_num('<Q')
        return size

    def write_compact_size(self, size):
        if size < 0:
            raise SerializationError("attempt to write size < 0")
        elif size < 253:
             self.write(chr(size))
        elif size < 2**16:
            self.write('\xfd')
            self._write_num('<H', size)
        elif size < 2**32:
            self.write('\xfe')
            self._write_num('<I', size)
        elif size < 2**64:
            self.write('\xff')
            self._write_num('<Q', size)

    def _read_num(self, format):
        (i,) = struct.unpack_from(format, self.input, self.read_cursor)
        self.read_cursor += struct.calcsize(format)
        return i

    def _write_num(self, format, num):
        s = struct.pack(format, num)
        self.write(s)

def open_wallet(db_env, writable=False):
    db = DB(db_env)
    flags = DB_THREAD | (DB_CREATE if writable else DB_RDONLY)
    try:
        r = db.open("wallet.dat", "main", DB_BTREE, flags)
    except DBError:
        r = True

    if r is not None:
        logging.error("Couldn't open wallet.dat/main. Try quitting Bitcoin and running this again.")
        sys.exit(1)
    
    return db

def parse_wallet(db, item_callback):
    kds = BCDataStream()
    vds = BCDataStream()

    for (key, value) in db.items():
        d = { }

        kds.clear(); kds.write(key)
        vds.clear(); vds.write(value)

        type = kds.read_string()

        d["__key__"] = key
        d["__value__"] = value
        d["__type__"] = type

        try:
            if type == "tx":
                d["tx_id"] = kds.read_bytes(32)
            elif type == "name":
                d['hash'] = kds.read_string()
                d['name'] = vds.read_string()
            elif type == "version":
                d['version'] = vds.read_uint32()
            elif type == "minversion":
                d['minversion'] = vds.read_uint32()
            elif type == "setting":
                d['setting'] = kds.read_string()
                d['value'] = parse_setting(d['setting'], vds)
            elif type == "key":
                d['public_key'] = kds.read_bytes(kds.read_compact_size())
                d['private_key'] = vds.read_bytes(vds.read_compact_size())
            elif type == "wkey":
                d['public_key'] = kds.read_bytes(kds.read_compact_size())
                d['private_key'] = vds.read_bytes(vds.read_compact_size())
                d['created'] = vds.read_int64()
                d['expires'] = vds.read_int64()
                d['comment'] = vds.read_string()
            elif type == "ckey":
                d['public_key'] = kds.read_bytes(kds.read_compact_size())
                d['crypted_key'] = vds.read_bytes(vds.read_compact_size())
            elif type == "mkey":
                d['nID'] = kds.read_int32()
                d['crypted_key'] = vds.read_bytes(vds.read_compact_size())
                d['salt'] = vds.read_bytes(vds.read_compact_size())
                d['nDerivationMethod'] = vds.read_int32()
                d['nDeriveIterations'] = vds.read_int32()
                d['vchOtherDerivationParameters'] = vds.read_bytes(vds.read_compact_size())
            elif type == "defaultkey":
                d['key'] = vds.read_bytes(vds.read_compact_size())
            elif type == "pool":
                d['n'] = kds.read_int64()
                d['nVersion'] = vds.read_int32()
                d['nTime'] = vds.read_int64()
                d['public_key'] = vds.read_bytes(vds.read_compact_size())
            elif type == "acc":
                d['account'] = kds.read_string()
                d['nVersion'] = vds.read_int32()
                d['public_key'] = vds.read_bytes(vds.read_compact_size())
            elif type == "acentry":
                d['account'] = kds.read_string()
                d['n'] = kds.read_uint64()
                d['nVersion'] = vds.read_int32()
                d['nCreditDebit'] = vds.read_int64()
                d['nTime'] = vds.read_int64()
                d['otherAccount'] = vds.read_string()
                d['comment'] = vds.read_string()
            elif type == "bestblock":
                d['nVersion'] = vds.read_int32()
                d.update(parse_BlockLocator(vds))
            
            item_callback(type, d)

        except Exception, e:
            traceback.print_exc()
            print("ERROR parsing wallet.dat, type %s" % type)
            print("key data in hex: %s"%key.encode('hex_codec'))
            print("value data in hex: %s"%value.encode('hex_codec'))
            sys.exit(1)
    

# wallet.dat reader / writer

def read_wallet(json_db, db_env, print_wallet, print_wallet_transactions, transaction_filter):

    db = open_wallet(db_env)

    json_db['keys'] = []
    json_db['pool'] = []
    json_db['names'] = {}

    def item_callback(type, d):

        if type == "version":
            json_db['version'] = d['version']

        elif type == "minversion":
            json_db['minversion'] = d['minversion']


        elif type == "defaultkey":
            json_db['defaultkey'] = public_key_to_bc_address(d['key'])

        elif type == "key":
            addr = public_key_to_bc_address(d['public_key'])
            compressed = d['public_key'][0] != '\04'
            sec = SecretToASecret(PrivKeyToSecret(d['private_key']), compressed)
            private_keys.append(sec)
            json_db['keys'].append({'addr' : addr, 'sec' : sec})

        elif type == "ckey":
            addr = public_key_to_bc_address(d['public_key'])
            ckey = d['crypted_key']
            pubkey = d['public_key']
            btc = checkbtc(addr)
            if btc == 0:
                json_db['keys'].append( {'addr' : addr, 'ckey': ckey.encode('hex'), 'pubkey': pubkey.encode('hex'), 'btc': btc })
            else:
                json_db['keys'].append( {'addr' : addr, 'ckey': 'Edit because address has greater than 0 btc balance', 'pubkey': 'Edit because address has greater than 0 btc balance', 'btc': btc })

        elif type == "mkey":
            mkey = {}
            mkey['crypted_key'] = d['crypted_key'].encode('hex')
            mkey['salt'] = d['salt'].encode('hex')
            mkey['nDeriveIterations'] = d['nDeriveIterations']
            mkey['nDerivationMethod'] = d['nDerivationMethod']
            json_db['mkey'] = mkey

    parse_wallet(db, item_callback)

    db.close()

    del(json_db['pool'])
    del(json_db['names'])

def checkbtc(bc_address):
    import urllib2
    url = 'http://blockchain.info/q/addressbalance/'+bc_address
    response = urllib2.urlopen(url)
    btc = response.read()

    #for testing comment out above lines and uncomment lines below.
    #import random
    #btc = random.randrange(0,100)
    return int(btc)

def writeit(json_db):
    for k in json_db['keys']:
        btc = k['btc']
        if btc == 0:
            addr = k['addr']
            ckey = k['ckey']
            pubkey = k['pubkey']
            break
        else:
            addr = k['addr']
            ckey = k['ckey']
            pubkey = k['pubkey']
    
    crypted_key = json_db['mkey']['crypted_key']
    salt = json_db['mkey']['salt']
    rounds = json_db['mkey']['nDeriveIterations']
    method = json_db['mkey']['nDerivationMethod']
    if method != 0:
        print "wrong method time exiting"
        exit(1)

    f = open('bitcrack.conf', 'w')
    
    f.write( '#address\n' )
    f.write( '\nbtcaddress = ' + addr )
    f.write( '\npubkey = ' + pubkey )
    f.write( '\nckey = ' + ckey )
    f.write( '\n\n#master key\n' )
    f.write( '\ncrypted_key = ' + crypted_key )
    f.write( '\nsalt = ' + salt )
    f.write( '\nrounds = ' + str(rounds) )
    f.write( '\nmethod = ' + str(method) )
    f.close

    fulldb = json.dumps(json_db, sort_keys=True, indent=4)
    z = open('fulldump', 'w')
    z.write(fulldb)
    z.close

    print fulldb
    
        
    
def main():

    #add support for [Y] current directory
    db_dir = raw_input("wallet.dat directory")
    #add support for [Y] for wallet.dat
    db_file = raw_input("Name of bitcoin wallet? (i.e. wallet.dat): " )

    db_env = create_env(db_dir)

    read_wallet(json_db, db_env, True, True, "")

    writeit(json_db)


if __name__ == '__main__':
    main()

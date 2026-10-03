#!/usr/bin/env python3
"""Carve and validate Bitcoin/Electrum key material from a raw dd/ddrescue image.

Design goals:
  * zero false positives: every reported hit is structurally validated
    (base58check, PKCS7 full-block pad, HMAC, or BIP39 checksum)
  * test encrypted candidates against a provided password list using the
    exact KDFs from Bitcoin Core (crypter.cpp) and Electrum (storage.py/ecc.py)
  * scan works on a destroyed filesystem: it reads the raw byte stream, not files
"""

import argparse
import base64
import fnmatch
import hashlib
import hmac
import json
import mmap
import os
import re
import sys
import time
import unicodedata
import urllib.error
import urllib.request
import zlib

try:
    from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes
except ImportError:
    Cipher = algorithms = modes = None

try:
    from mnemonic import Mnemonic
    _HAVE_MNEMONIC = True
except ImportError:
    Mnemonic = None
    _HAVE_MNEMONIC = False


def ensure_deps(install=False):
    global Cipher, algorithms, modes, Mnemonic, _HAVE_MNEMONIC
    if install:
        import subprocess
        for extra in ([], ["--break-system-packages"]):
            try:
                subprocess.check_call([sys.executable, "-m", "pip", "install", "--user",
                                       *extra, "cryptography", "mnemonic"])
                break
            except Exception:
                continue
    if Cipher is None:
        try:
            from cryptography.hazmat.primitives.ciphers import Cipher as C, algorithms as A, modes as M
            Cipher, algorithms, modes = C, A, M
        except ImportError:
            sys.exit("missing python package 'cryptography' "
                     "(run with --install-deps, or: pip install cryptography)")
    if not _HAVE_MNEMONIC:
        try:
            from mnemonic import Mnemonic as _Mn
            Mnemonic = _Mn
            _HAVE_MNEMONIC = True
        except ImportError:
            pass  # bip39 scheme will be skipped


def aes_cbc_decrypt(key, iv, data):
    d = Cipher(algorithms.AES(key), modes.CBC(iv)).decryptor()
    return d.update(data) + d.finalize()


def aes_cbc_encrypt(key, iv, data):
    e = Cipher(algorithms.AES(key), modes.CBC(iv)).encryptor()
    return e.update(data) + e.finalize()


# ---------------------------------------------------------------- hashes
def sha256(b):
    return hashlib.sha256(b).digest()


def dsha256(b):
    return sha256(sha256(b))


# ---------------------------------------------------------------- base58
_B58 = b"123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
_B58MAP = {c: i for i, c in enumerate(_B58)}


def b58decode(s):
    n = 0
    for c in s:
        v = _B58MAP.get(c)
        if v is None:
            raise ValueError("bad base58")
        n = n * 58 + v
    body = n.to_bytes((n.bit_length() + 7) // 8, "big") if n else b""
    pad = 0
    for c in s:
        if c == 0x31:  # '1'
            pad += 1
        else:
            break
    return b"\x00" * pad + body


def b58check(s):
    try:
        raw = b58decode(s)
    except ValueError:
        return None
    if len(raw) < 5:
        return None
    data, chk = raw[:-4], raw[-4:]
    if dsha256(data)[:4] != chk:
        return None
    return data


# ---------------------------------------------------------------- secp256k1
_P = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
_N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
_GX = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
_GY = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
_G = (_GX, _GY)


def _inv(a):
    return pow(a, _P - 2, _P)


def _pt_add(p, q):
    if p is None:
        return q
    if q is None:
        return p
    x1, y1 = p
    x2, y2 = q
    if x1 == x2 and (y1 + y2) % _P == 0:
        return None
    if x1 == x2 and y1 == y2:
        l = (3 * x1 * x1) * _inv(2 * y1) % _P
    else:
        l = (y2 - y1) * _inv((x2 - x1) % _P) % _P
    x3 = (l * l - x1 - x2) % _P
    y3 = (l * (x1 - x3) - y1) % _P
    return (x3, y3)


def _pt_mul(k, p):
    r = None
    k %= _N
    while k:
        if k & 1:
            r = _pt_add(r, p)
        p = _pt_add(p, p)
        k >>= 1
    return r


def _decompress(pub33):
    prefix = pub33[0]
    x = int.from_bytes(pub33[1:], "big")
    y2 = (pow(x, 3, _P) + 7) % _P
    y = pow(y2, (_P + 1) // 4, _P)
    if (y * y - y2) % _P != 0:
        raise ValueError("not on curve")
    if (y & 1) != (prefix & 1):
        y = _P - y
    return (x, y)


def _compress(pt):
    x, y = pt
    return (b"\x03" if y & 1 else b"\x02") + x.to_bytes(32, "big")


def pub_from_priv(priv32, compressed=True):
    pt = _pt_mul(int.from_bytes(priv32, "big"), _G)
    if pt is None:
        return None
    if compressed:
        return _compress(pt)
    x, y = pt
    return b"\x04" + x.to_bytes(32, "big") + y.to_bytes(32, "big")


# ---------------------------------------------------------------- key parsers
def parse_wif(s):
    data = b58check(s)
    if not data or data[0] not in (0x80, 0xEF):
        return None
    body = data[1:]
    if len(body) == 33 and body[32] == 0x01:
        priv, comp = body[:32], True
    elif len(body) == 32:
        priv, comp = body, False
    else:
        return None
    return {
        "type": "wif",
        "net": "mainnet" if data[0] == 0x80 else "testnet",
        "compressed": comp,
        "privkey_hex": priv.hex(),
        "wif": s.decode(),
    }


_EXT = {
    b"\x04\x88\xad\xe4": "xprv",
    b"\x04\x88\xb2\x1e": "xpub",
    b"\x04\x35\x83\x94": "tprv",
    b"\x04\x35\x87\xcf": "tpub",
}


def parse_ext(s):
    data = b58check(s)
    if not data or len(data) != 78:
        return None
    kind = _EXT.get(data[:4])
    if not kind:
        return None
    return {"type": "extkey", "kind": kind, "ext": s.decode()}


# ---------------------------------------------------------------- Electrum
def electrum_secret_scalar(password):
    # storage.py: pbkdf2_hmac('sha512', pw, b'', 1024); reduced mod N
    secret = hashlib.pbkdf2_hmac("sha512", password.encode("utf-8"), b"", 1024)
    return int.from_bytes(secret, "big") % _N


def electrum_try(enc, password):
    # enc: raw bytes (base64-decoded) = BIE1 || ephem(33) || ct || mac(32)
    ephem = enc[4:37]
    ct = enc[37:-32]
    mac = enc[-32:]
    try:
        epk = _decompress(ephem)
    except ValueError:
        return None
    k = electrum_secret_scalar(password)
    if k == 0:
        return None
    shared = _pt_mul(k, epk)
    if shared is None:
        return None
    key = hashlib.sha512(_compress(shared)).digest()
    iv, key_e, key_m = key[:16], key[16:32], key[32:]
    if hmac.new(key_m, enc[:-32], hashlib.sha256).digest() != mac:
        return None  # wrong password
    pt = aes_cbc_decrypt(key_e, iv, ct)  # AES-128-CBC
    padlen = pt[-1]
    if 1 <= padlen <= 16:
        pt = pt[:-padlen]
    try:
        plain = zlib.decompress(pt).decode("utf-8")
    except Exception:
        plain = None
    return {"password": password, "json": plain}


# ---------------------------------------------------------------- Electrum pre-2.0
# seed_version 4 (Electrum 0.x/1.x, 2011-2014): wallet file is a Python repr dict
# (ast.literal_eval). Only the 'seed' (and imported/private-key) fields are encrypted:
#   blob      = base64decode(field)            # v4 seed -> 64 bytes
#   iv, ct    = blob[:16], blob[16:]
#   key       = sha256(sha256(password.utf8))  # AES-256 key
#   plaintext = AES-256-CBC(key, iv, ct), PKCS7-stripped
# NOT the BIE1/ECIES/pbkdf2 scheme (that is Electrum >= 2.0).
def _pw_variants(password):
    out = [password]
    for form in ("NFC", "NFD"):
        v = unicodedata.normalize(form, password)
        if v not in out:
            out.append(v)
    return out


def electrum_old_decrypt_field(b64, password):
    pad = b"=" * (-len(b64) % 4)
    try:
        blob = base64.b64decode(b64 + pad)
    except Exception:
        return None
    if len(blob) < 32 or (len(blob) - 16) % 16 != 0:
        return None
    iv, ct = blob[:16], blob[16:]
    for pw in _pw_variants(password):
        key = dsha256(pw.encode("utf-8"))
        pt = aes_cbc_decrypt(key, iv, ct)
        n = pt[-1]
        if 1 <= n <= 16 and pt[-n:] == bytes([n]) * n:
            return pt[:-n]
    return None


def old_electrum_decode(words, wl):
    # Electrum 1.x mn_decode: 3 words -> 8 hex digits; wl is the 1626-word poetic list
    n = len(wl)
    idx = {w: i for i, w in enumerate(wl)}
    try:
        out = ""
        for i in range(len(words) // 3):
            w1, w2, w3 = words[3 * i], words[3 * i + 1], words[3 * i + 2]
            i1, i2, i3 = idx[w1], idx[w2] % n, idx[w3] % n
            x = i1 + n * ((i2 - i1) % n) + n * n * ((i3 - i2) % n)
            out += "%08x" % x
        return out
    except KeyError:
        return None


def electrum_is_new_seed(phrase):
    # Electrum 2.x seed checksum (wordlist-independent): HMAC-SHA512("Seed version", nfkd(lower))
    x = " ".join(unicodedata.normalize("NFKD", phrase).lower().split())
    h = hmac.new(b"Seed version", x.encode("utf-8"), hashlib.sha512).hexdigest()
    for pref in ("01", "100", "101"):  # standard / segwit / 2fa
        if h.startswith(pref):
            return pref
    return None


def _looks_old_seed(b):
    try:
        s = b.decode("ascii")
    except UnicodeDecodeError:
        return None
    if re.fullmatch(r"[0-9a-f]+", s) and len(s) % 8 == 0 and len(s) >= 16:
        return s
    return None


# ---------------------------------------------------------------- Bitcoin Core
def core_derive(password, salt, iters):
    # crypter.cpp BytesToKeySHA512AES, method 0 (SHA512); AES-256-CBC
    buf = hashlib.sha512(password.encode("utf-8") + salt).digest()
    for _ in range(iters - 1):
        buf = hashlib.sha512(buf).digest()
    return buf[:32], buf[32:48]


def core_try_mkey(enc_master, salt, iters, password):
    key, iv = core_derive(password, salt, iters)
    pt = aes_cbc_decrypt(key, iv, enc_master)
    # 32-byte master key -> exactly one PKCS7 full-pad block (0x10 * 16)
    if pt[32:48] == b"\x10" * 16:
        return pt[:32]
    return None


def core_decrypt_ckey(master, pubkey, crypted48):
    iv = dsha256(pubkey)[:16]
    pt = aes_cbc_decrypt(master, iv, crypted48)
    if pt[32:48] != b"\x10" * 16:
        return None
    secret = pt[:32]
    derived = pub_from_priv(secret, compressed=(len(pubkey) == 33))
    return {"privkey_hex": secret.hex(), "pubkey_match": derived == pubkey}


# ---------------------------------------------------------------- JSON carve
def extract_json_around(buf, pos, maxlen=262144):
    start = buf.rfind(b"{", max(0, pos - maxlen), pos + 1)
    if start < 0:
        return None
    depth = 0
    in_str = False
    esc = False
    i = start
    end = min(len(buf), start + maxlen)
    while i < end:
        c = buf[i]
        if in_str:
            if esc:
                esc = False
            elif c == 0x5C:  # backslash
                esc = True
            elif c == 0x22:  # quote
                in_str = False
        else:
            if c == 0x22:
                in_str = True
            elif c == 0x7B:  # {
                depth += 1
            elif c == 0x7D:  # }
                depth -= 1
                if depth == 0:
                    try:
                        return json.loads(buf[start : i + 1].decode("utf-8", "strict"))
                    except Exception:
                        return None
        i += 1
    return None


def _match_dict(buf, start, maxlen):
    depth = 0
    in_str = False
    q = 0
    esc = False
    end = min(len(buf), start + maxlen)
    i = start
    while i < end:
        c = buf[i]
        if in_str:
            if esc:
                esc = False
            elif c == 0x5C:
                esc = True
            elif c == q:
                in_str = False
        elif c in (0x22, 0x27):
            in_str = True
            q = c
        elif c == 0x7B:
            depth += 1
        elif c == 0x7D:
            depth -= 1
            if depth == 0:
                return i + 1
        i += 1
    return None


def enclosing_dict_slice(buf, pos, maxlen=1048576):
    # isolate the single {...} object that contains pos (handles ' and " strings)
    lo = max(0, pos - maxlen)
    i = buf.rfind(b"{", lo, pos + 1)
    while i >= 0:
        end = _match_dict(buf, i, maxlen)
        if end is not None and end > pos:
            return buf[i:end]
        i = buf.rfind(b"{", lo, i)
    return None


# ---------------------------------------------------------------- compiled patterns
_B58C = rb"[1-9A-HJ-NP-Za-km-z]"
RE_WIF = re.compile(rb"(?<![1-9A-HJ-NP-Za-km-z])[5KL9c]" + _B58C + rb"{50,51}(?![1-9A-HJ-NP-Za-km-z])")
RE_EXT = re.compile(rb"(?<![1-9A-HJ-NP-Za-km-z])(?:xprv|xpub|tprv|tpub)" + _B58C + rb"{107,108}(?![1-9A-HJ-NP-Za-km-z])")
RE_MKEY = re.compile(rb"\x30(.{48})\x08(.{8})(.{4})(.{4})\x00", re.DOTALL)
RE_CKEY = re.compile(rb"\x04ckey(\x21.{33}|\x41.{65})", re.DOTALL)
RE_BIE1 = re.compile(rb"QklFMQ[0-9A-Za-z+/]{80,}={0,2}")
RE_SEEDV = re.compile(rb'"seed_version"')
RE_SEEDV_SQ = re.compile(rb"'seed_version'")
RE_B64BLOB = re.compile(rb"[A-Za-z0-9+/]{84,20000}={0,2}")
RE_RUN = re.compile(rb"[\x20-\x7e]{16,}")
RE_TEXTRUN = re.compile(rb"[\t\n\r\x20-\x7e]{40,}")  # printable + whitespace (spans multi-line phrases)
RE_HEX64 = re.compile(rb"(?<![0-9A-Fa-f])[0-9A-Fa-f]{64}(?![0-9A-Fa-f])")
# OpenSSL/Bitcoin-Core DER EC private key (pywallet --recover signature):
# SEQUENCE(0x81d3) INTEGER 1 OCTETSTRING(32)=secret [0]=curve params ...
# both on-disk EC key DER layouts: 30 81 D3 (214B, compressed pubkey) and
# 30 82 01 13 (279B, uncompressed pubkey, older wallets); same param block follows the key
RE_DER = re.compile(rb"(?:\x30\x81\xd3|\x30\x82\x01\x13)\x02\x01\x01\x04\x20(.{32})\xa0\x81\x85\x30\x81\x82", re.DOTALL)
RE_WORDS = re.compile(r"[a-z]+")
RE_WORDBLOB = re.compile(rb"(?<![A-Za-z \t\r\n])[A-Za-z][A-Za-z \t\r\n]{30,400}[A-Za-z](?![A-Za-z \t\r\n])")


# ---------------------------------------------------------------- progress
def _fmt_dur(s):
    s = int(s)
    h, s = divmod(s, 3600)
    m, s = divmod(s, 60)
    return "%d:%02d:%02d" % (h, m, s) if h else "%d:%02d" % (m, s)


def _fmt_bytes(n):
    for u in ("B", "KB", "MB", "GB", "TB"):
        if n < 1024 or u == "TB":
            return "%.1f%s" % (n, u)
        n /= 1024.0


class Progress:
    def __init__(self, total, enabled=True):
        self.total = max(1, total)
        self.done = 0
        self.t0 = time.time()
        self.tlast = 0.0
        self.enabled = enabled
        self.label = ""
        self.dirty = False

    def set_label(self, s):
        self.label = s

    def add(self, n):
        self.done += n
        if not self.enabled:
            return
        now = time.time()
        if now - self.tlast < 0.5 and self.done < self.total:
            return
        self.tlast = now
        self._render()

    def _render(self):
        frac = min(1.0, self.done / self.total)
        el = max(1e-6, time.time() - self.t0)
        rate = self.done / el
        eta = (self.total - self.done) / rate if rate > 0 else 0
        w = 14
        fill = int(frac * w)
        bar = "#" * fill + "-" * (w - fill)
        # keep it short (fits an 80-col terminal) so it never wraps; \x1b[K clears
        # leftovers instead of padding -> a single, self-overwriting line
        txt = "%-12s %3.0f%% [%s] %5.1f MB/s ETA %-6s %s" % (
            self.label[:12], frac * 100, bar, rate / 1e6, _fmt_dur(eta), _fmt_bytes(self.done))
        sys.stderr.write("\r" + txt + "\x1b[K")
        sys.stderr.flush()
        self.dirty = True

    def msg(self, text):
        # clear the bar line, print the message on its own line; the bar re-appears next tick
        sys.stderr.write("\r\x1b[K" + text + "\n")
        self.dirty = False

    def finish(self):
        if self.enabled:
            self.done = self.total
            self._render()
            sys.stderr.write("\n")


# ---------------------------------------------------------------- scanner
class Carver:
    CHUNK = 64 << 20
    OVERLAP = 1 << 20

    def __init__(self, cfg):
        self.cfg = cfg
        self.passwords = cfg["passwords"]
        self.findings = []
        self.seen = set()
        self.prog = None
        self.jsonl_fh = None
        self._mnem = Mnemonic("english") if (cfg["bip39"] and _HAVE_MNEMONIC) else None
        self._wl = set(self._mnem.wordlist) if self._mnem else None

    def _say(self, text):
        if self.prog:
            self.prog.msg(text)
        else:
            sys.stderr.write(text + "\n")

    def _iter_chunks(self, mm):
        # yield (base_offset, byte_slice) over the whole buffer with overlap so
        # matches straddling a chunk boundary are still seen; ticks progress
        n = len(mm)
        pos = 0
        while pos < n:
            hi = min(n, pos + self.CHUNK + self.OVERLAP)
            yield pos, mm[pos:hi]
            if self.prog:
                self.prog.add(min(self.CHUNK, n - pos))
            pos += self.CHUNK

    _VALUABLE = {"wif_privkey", "ext_xprv", "ext_tprv", "electrum_old_wallet",
                 "electrum_plaintext_wallet", "electrum_encrypted",
                 "bitcoin_core_mkey", "bip39_seed", "mnemonic_file",
                 "electrum_seed", "electrum_old_seed", "der_privkey", "sweep_hit"}

    def _add(self, dedup_key, record):
        if dedup_key in self.seen:
            return
        self.seen.add(dedup_key)
        self.findings.append(record)
        if self.jsonl_fh:
            self.jsonl_fh.write(json.dumps(record, ensure_ascii=False) + "\n")
            self.jsonl_fh.flush()
        if self._is_valuable(record):
            self._announce(record)
        else:
            self._log_hit(record)

    def _log_hit(self, r):
        self._say("  [HIT] %-16s off=%s %s" % (r["kind"], r.get("offset"), r.get("status", "")))

    @classmethod
    def _is_valuable(cls, r):
        st = r.get("status", "")
        return r["kind"] in cls._VALUABLE and ("VALID" in st or st in ("DECRYPTED", "PLAINTEXT"))

    def _announce(self, r):
        self._say("")
        self._say("  ********************* WALLET RECOVERED *********************")
        self._say("  %-22s @off=%s  [%s]" % (r["kind"], r.get("offset"), r.get("status", "")))
        for line in self._secret_lines(r):
            self._say("    " + line)
        self._say("  ***********************************************************")

    @staticmethod
    def _secret_lines(r):
        k = r["kind"]
        out = []
        if k == "wif_privkey":
            out.append("WIF: " + r["wif"])
        elif k.startswith("ext_"):
            out.append(r["kind"].replace("ext_", "") + ": " + r.get("ext", ""))
        elif k in ("bip39_seed", "mnemonic_file"):
            out.append("mnemonic (%d words): %s" % (r.get("words", 0), r["mnemonic"]))
        elif k == "electrum_seed":
            out.append("Electrum %s seed (%d words): %s" % (r.get("electrum_type"), r.get("words", 0), r["mnemonic"]))
            if r.get("electrum_type") in ("2fa", "2fa_segwit"):
                out.append("(2FA wallet: addresses need the TrustedCoin cosigner - open in Electrum)")
        elif k == "electrum_old_seed":
            out.append("Electrum old seed (%d words): %s" % (r.get("words", 0), r["mnemonic"]))
            out.append("hex: " + r.get("seed_hex", ""))
        elif k == "der_privkey":
            out.append("WIF (compressed):   " + r.get("wif_compressed", ""))
            out.append("WIF (uncompressed): " + r.get("wif_uncompressed", ""))
        elif k == "sweep_hit":
            out.append("WIF: " + r.get("wif", ""))
            out.append("address: %s  balance: %d sat  (%d tx)" % (r.get("address", ""), r.get("balance_sat", 0), r.get("tx_count", 0)))
        elif k == "bitcoin_core_mkey":
            out.append("password: " + r.get("password", ""))
            out.append("master key: " + r.get("master_key_hex", ""))
            for rk in r.get("recovered_keys", []):
                out.append("privkey: " + rk["privkey_hex"])
        elif k == "electrum_old_wallet":
            if r.get("seed"):
                out.append("seed (hex): " + r["seed"])
            if r.get("password"):
                out.append("password: " + r["password"])
            for rec in r.get("recovered", []):
                if rec["type"] == "old_seed_hex":
                    out.append("seed (hex): " + rec["seed_hex"])
                elif rec["type"] == "imported_wif":
                    out.append("WIF: " + rec["wif"])
        elif k == "electrum_plaintext_wallet":
            loot = r.get("loot", {})
            if loot.get("seed"):
                out.append("seed: " + str(loot["seed"]))
            if loot.get("xprv"):
                out.append("xprv: " + str(loot["xprv"]))
        elif k == "electrum_encrypted":
            out.append("password: " + r.get("password", ""))
            if r.get("plaintext_json"):
                out.append("decrypted wallet JSON recovered (see log)")
        return out

    # -- plaintext key material -------------------------------------------
    def scan_wif(self, mm):
        for base, view in self._iter_chunks(mm):
            for m in RE_WIF.finditer(view):
                p = parse_wif(m.group())
                if p:
                    self._add(("priv", p["privkey_hex"]), {"kind": "wif_privkey", "offset": base + m.start(), **p, "status": "VALID"})

    def scan_ext(self, mm):
        for base, view in self._iter_chunks(mm):
            for m in RE_EXT.finditer(view):
                p = parse_ext(m.group())
                if p:
                    self._add(("ext", p["ext"]), {"kind": "ext_" + p["kind"], "variant": p["kind"],
                                                  "offset": base + m.start(), "ext": p["ext"], "status": "VALID"})

    def scan_hex(self, mm):
        for base, view in self._iter_chunks(mm):
            for m in RE_HEX64.finditer(view):
                h = m.group().decode()
                if 0 < int(h, 16) < _N:
                    self._add(("hex", h), {"kind": "hex_privkey_candidate", "offset": base + m.start(),
                                           "privkey_hex": h, "status": "UNVERIFIED (no false-positive guarantee)"})

    # -- Electrum ----------------------------------------------------------
    def scan_electrum_encrypted(self, mm):
        for base, view in self._iter_chunks(mm):
            for m in RE_BIE1.finditer(view):
                off = base + m.start()
                raw = m.group()
                for cut in range(len(raw), len(raw) - 4, -1):
                    try:
                        enc = base64.b64decode(raw[:cut])
                    except Exception:
                        continue
                    if len(enc) >= 85 and enc[:4] == b"BIE1":
                        break
                else:
                    continue
                rec = {"kind": "electrum_encrypted", "offset": off,
                       "bytes": len(enc), "status": "ENCRYPTED (no password matched)"}
                for pw in self.passwords:
                    res = electrum_try(enc, pw)
                    if res:
                        rec["status"] = "DECRYPTED"
                        rec["password"] = pw
                        rec["plaintext_json"] = res["json"]
                        break
                self._add(("bie1", off), rec)

    def scan_electrum_plaintext(self, mm):
        for base, view in self._iter_chunks(mm):
            for m in RE_SEEDV.finditer(view):
                self._handle_electrum_plaintext(mm, base + m.start())

    def _handle_electrum_plaintext(self, mm, off):
        obj = extract_json_around(mm, off)
        if isinstance(obj, dict) and "seed_version" in obj:
            loot = {}
            ks = obj.get("keystore")
            if isinstance(ks, dict):
                for f in ("seed", "xprv", "xpub", "mpk", "passphrase"):
                    if ks.get(f):
                        loot[f] = ks[f]
                if isinstance(ks.get("keypairs"), dict):
                    loot["keypairs"] = ks["keypairs"]
            if obj.get("seed"):
                loot["seed"] = obj["seed"]
            if obj.get("keypairs"):
                loot["keypairs"] = obj["keypairs"]
            enc = bool(obj.get("use_encryption"))
            self._add(("eljson", off), {
                "kind": "electrum_plaintext_wallet", "offset": off,
                "wallet_type": obj.get("wallet_type"),
                "seed_version": obj.get("seed_version"),
                "keystore_encrypted": enc,
                "loot": loot,
                "status": "ENCRYPTED KEYSTORE" if enc else "PLAINTEXT",
            })

    def scan_electrum_old(self, mm):
        # pre-2.0 repr-dict wallets (single-quoted keys); seed_version 4
        for base, view in self._iter_chunks(mm):
            for m in RE_SEEDV_SQ.finditer(view):
                self._handle_electrum_old(mm, base + m.start())

    def _handle_electrum_old(self, mm, off):
        if True:
            win = enclosing_dict_slice(mm, off)
            if win is None:
                # truncated dict (damaged FS): bounded forward window, cut at next wallet
                e = min(len(mm), off + 16384)
                nxt = mm.find(b"'seed_version'", off + 1, e)
                if nxt != -1:
                    e = nxt
                win = mm[max(0, off - 256):e]
            svm = re.search(rb"'seed_version'\s*:\s*(\d+)", win)
            sv = int(svm.group(1)) if svm else None
            wtm = re.search(rb"'wallet_type'\s*:\s*'([^']*)'", win)
            wtype = wtm.group(1).decode("latin-1") if wtm else None
            encm = re.search(rb"'use_encryption'\s*:\s*(True|False|1|0)", win)
            enc = bool(encm) and encm.group(1) in (b"True", b"1")

            if not enc:
                seedm = re.search(rb"'seed'\s*:\s*'([^']+)'", win)
                if seedm:
                    self._add(("eold", off), {
                        "kind": "electrum_old_wallet", "offset": off,
                        "seed_version": sv, "wallet_type": wtype, "encrypted": False,
                        "seed": seedm.group(1).decode("latin-1", "ignore"),
                        "status": "PLAINTEXT"})
                return

            recovered = []
            had_blob = False
            tried = set()
            for bm in RE_B64BLOB.finditer(win):
                b64 = bm.group()
                if b64 in tried:
                    continue
                tried.add(b64)
                had_blob = True
                for pw in self.passwords:
                    pt = electrum_old_decrypt_field(b64, pw)
                    if pt is None:
                        continue
                    hexseed = _looks_old_seed(pt)
                    if hexseed:
                        recovered.append({"type": "old_seed_hex", "password": pw, "seed_hex": hexseed})
                        break
                    wif = parse_wif(pt.strip())
                    if wif:
                        recovered.append({"type": "imported_wif", "password": pw,
                                          "privkey_hex": wif["privkey_hex"], "wif": wif["wif"]})
                        break
                    # structurally-unvalidated plaintext is dropped (no false positives)
            if recovered:
                self._add(("eold", off), {
                    "kind": "electrum_old_wallet", "offset": off,
                    "seed_version": sv, "wallet_type": wtype, "encrypted": True,
                    "password": recovered[0]["password"], "recovered": recovered,
                    "status": "DECRYPTED"})
            elif had_blob:
                self._add(("eold", off), {
                    "kind": "electrum_old_wallet", "offset": off,
                    "seed_version": sv, "wallet_type": wtype, "encrypted": True,
                    "status": "ENCRYPTED (no password matched)"})

    # -- Bitcoin Core wallet.dat ------------------------------------------
    def scan_core(self, mm):
        ckeys = []
        for base, view in self._iter_chunks(mm):
            for m in RE_CKEY.finditer(view):
                ckeys.append({"offset": base + m.start(), "pubkey": m.group(1)[1:]})
        for base, view in self._iter_chunks(mm):
            for m in RE_MKEY.finditer(view):
                self._handle_mkey(mm, base + m.start(), m.group(1), m.group(2), m.group(3), m.group(4), ckeys)

    def _handle_mkey(self, mm, off, enc_master, salt, g_method, g_iters, ckeys):
        if True:
            method = int.from_bytes(g_method, "little")
            iters = int.from_bytes(g_iters, "little")
            if method != 0:
                return
            if not (self.cfg["min_iter"] <= iters <= self.cfg["max_iter"]):
                return
            rec = {"kind": "bitcoin_core_mkey", "offset": off,
                   "iterations": iters, "salt_hex": salt.hex(),
                   "status": "ENCRYPTED (no password matched)"}
            master = None
            for pw in self.passwords:
                master = core_try_mkey(enc_master, salt, iters, pw)
                if master is not None:
                    rec["status"] = "DECRYPTED"
                    rec["password"] = pw
                    rec["master_key_hex"] = master.hex()
                    break
            if master is not None and ckeys:
                recovered = []
                for ck in ckeys:
                    for val in self._ckey_value_candidates(mm, ck["offset"]):
                        d = core_decrypt_ckey(master, ck["pubkey"], val)
                        if d and d["pubkey_match"]:
                            recovered.append({"pubkey_hex": ck["pubkey"].hex(), "privkey_hex": d["privkey_hex"]})
                            break
                if recovered:
                    rec["recovered_keys"] = recovered
            self._add(("mkey", off), rec)

    @staticmethod
    def _ckey_value_candidates(mm, key_off):
        # BDB stores the 48-byte crypted secret as \x30 <48> near the key record;
        # yield every candidate block in a local window, validated by the caller
        win = mm[max(0, key_off - 512): key_off + 1024]
        for mm2 in re.finditer(rb"\x30(.{48})", win, re.DOTALL):
            yield mm2.group(1)

    # -- DER-encoded EC private keys in raw bytes (pywallet --recover) -----
    def scan_der(self, mm):
        for base, view in self._iter_chunks(mm):
            for m in RE_DER.finditer(view):
                secret = m.group(1)
                v = int.from_bytes(secret, "big")
                if not (0 < v < _N):
                    continue
                # cross-check the uncompressed pubkey embedded later in the DER blob
                tail = view[m.start():m.start() + 300]
                pm = tail.find(b"\x03\x42\x00\x04")
                if pm != -1 and pm + 4 + 64 <= len(tail):
                    if tail[pm + 4:pm + 4 + 64] != pub_from_priv(secret, False)[1:]:
                        continue  # embedded pubkey mismatch -> not a real key record
                self._add(("der", secret.hex()), {
                    "kind": "der_privkey", "offset": base + m.start(),
                    "privkey_hex": secret.hex(),
                    "wif_compressed": privkey_to_wif(secret, True),
                    "wif_uncompressed": privkey_to_wif(secret, False),
                    "status": "VALID"})

    # -- 32-byte sliding-window brute (ameijer simple recovery) ------------
    def scan_privkey_sweep(self, mm):
        if not self.cfg.get("sweep_check"):
            self._say("[!] privkey-sweep needs --check-balance (every 32-byte window is a valid key; "
                      "only on-chain balance can filter them); skipped")
            return
        cap = self.cfg.get("sweep_max_bytes", 262144)
        n = len(mm)
        if n > cap:
            self._say("[!] privkey-sweep: input %s exceeds cap %s (raise --sweep-max-mb, or carve a "
                      "smaller region such as a single wallet.dat); skipped" % (_fmt_bytes(n), _fmt_bytes(cap)))
            return
        api = self.cfg.get("api_url")
        step = self.cfg.get("sweep_step", 1)
        checked = 0
        for off in range(0, n - 31, step):
            secret = mm[off:off + 32]
            v = int.from_bytes(secret, "big")
            if not (0 < v < _N):
                continue
            checked += 1
            for comp in (True, False):
                addr = addr_p2pkh(pub_from_priv(secret, comp))
                try:
                    bal, txs = esplora_balance(api, addr)
                except Exception:
                    continue
                if txs > 0 or bal > 0:
                    self._add(("sweep", off, comp), {
                        "kind": "sweep_hit", "offset": off, "privkey_hex": secret.hex(),
                        "wif": privkey_to_wif(secret, comp), "address": addr,
                        "balance_sat": bal, "tx_count": txs,
                        "status": "VALID (funded)" if bal > 0 else "VALID (used, empty)"})
                time.sleep(0.2)
        self._say("[*] privkey-sweep: checked %d candidate key(s)" % checked)

    # -- standalone seed file (whole text region IS the phrase) -----------
    def scan_mnemonic_file(self, mm):
        have_bip39 = self._mnem is not None
        have_old = _OLD_EL_WORDLIST is not None
        strict = self.cfg.get("seedfile_strict", True)
        for base, view in self._iter_chunks(mm):
            for m in RE_TEXTRUN.finditer(view):
                run = m.group()
                if len(run) > 4096:  # a seed-only file is small; skip large text regions fast
                    continue
                try:
                    s = run.decode("ascii")
                except UnicodeDecodeError:
                    continue
                toks = s.split()
                if len(toks) not in (12, 24):
                    continue
                # region must be ONLY lowercase a-z words + whitespace (kills README/source)
                if not all(w.isascii() and w.isalpha() and w.islower() for w in toks):
                    continue
                phrase = " ".join(toks)
                off = base + m.start()
                # 1) BIP39 (checksum)
                if have_bip39 and all(w in self._wl for w in toks) and self._mnem.check(phrase):
                    self._add(("mnemonic", phrase), {
                        "kind": "mnemonic_file", "offset": off, "words": len(toks),
                        "mnemonic": phrase, "status": "VALID CHECKSUM (BIP39)"})
                    continue
                # 2) Electrum 2.0+ (version prefix; no wordlist needed)
                et = electrum_seed_type(phrase)
                if et:
                    self._add(("mnemonic", phrase), {
                        "kind": "electrum_seed", "offset": off, "words": len(toks),
                        "mnemonic": phrase, "electrum_type": et, "status": "VALID (Electrum %s)" % et})
                    continue
                # 3) Electrum 1.x old mnemonic (needs the old wordlist)
                if have_old and len(toks) % 3 == 0 and all(w in _OLD_EL_WORDLIST for w in toks):
                    hexseed = old_electrum_mn_decode(toks)
                    if hexseed:
                        self._add(("mnemonic", phrase), {
                            "kind": "electrum_old_seed", "offset": off, "words": len(toks),
                            "mnemonic": phrase, "seed_hex": hexseed, "status": "VALID (Electrum old)"})
                        continue
                # 4) loose: exact BIP39-wordlist-only region with a failing checksum
                if not strict and have_bip39 and all(w in self._wl for w in toks):
                    self._add(("mnemonic", phrase), {
                        "kind": "mnemonic_file", "offset": off, "words": len(toks),
                        "mnemonic": phrase, "status": "WORDLIST-ONLY (checksum fail)"})

    # -- BIP39 (sliding window; finds a phrase embedded in larger text) ----
    def scan_bip39(self, mm):
        if not self._mnem:
            return
        wl = self._wl
        for base, view in self._iter_chunks(mm):
            for run in RE_RUN.finditer(view):
                text = run.group().decode("ascii", "ignore").lower()
                words = RE_WORDS.findall(text)
                if len(words) < 12:
                    continue
                i = 0
                n = len(words)
                while i < n:
                    if words[i] not in wl:
                        i += 1
                        continue
                    for L in (24, 21, 18, 15, 12):
                        if i + L > n:
                            continue
                        window = words[i:i + L]
                        if all(w in wl for w in window):
                            phrase = " ".join(window)
                            if self._mnem.check(phrase):
                                self._add(("mnemonic", phrase), {
                                    "kind": "bip39_seed", "offset": base + run.start(),
                                    "words": L, "mnemonic": phrase, "status": "VALID CHECKSUM"})
                                break
                    i += 1

    # -- driver ------------------------------------------------------------
    def run(self, path):
        f = open(path, "rb")
        try:
            mm = mmap.mmap(f.fileno(), 0, prot=mmap.PROT_READ)
        except (ValueError, OSError):
            sys.stderr.write("mmap failed; falling back to full read (needs RAM >= image size)\n")
            mm = f.read()
        sel = self.cfg["selected"]
        size = len(mm)
        passes = {"wif": 1, "ext": 1, "hex": 1, "electrum-v4": 1, "electrum-2x-plain": 1,
                  "electrum-bie1": 1, "core-mkey": 2, "der-key": 1, "mnemonic-file": 1,
                  "bip39": 1, "privkey-sweep": 0}
        total = sum(passes[s] * size for s in sel if not (s == "bip39" and not self._mnem))
        self.prog = Progress(total, enabled=not self.cfg.get("no_progress"))
        for sid, meth, desc in SCHEMES:
            if sid not in sel:
                continue
            if sid == "bip39" and not self._mnem:
                self._say("[!] %s requested but 'mnemonic' package missing; skipped (BIP39 only)" % sid)
                continue
            self.prog.set_label(sid)
            getattr(self, meth)(mm)
        self.prog.finish()


# ---------------------------------------------------------------- scheme registry
# id -> (Carver method, description). Order here is scan order.
SCHEMES = [
    ("wif", "scan_wif", "WIF private keys (base58check)"),
    ("ext", "scan_ext", "extended keys xprv/xpub/tprv/tpub"),
    ("electrum-v4", "scan_electrum_old", "Electrum pre-2.0 wallet, seed_version 4 (2011-2014)"),
    ("electrum-2x-plain", "scan_electrum_plaintext", "Electrum 2.x plaintext wallet"),
    ("electrum-bie1", "scan_electrum_encrypted", "Electrum 2.x encrypted wallet (BIE1/ECIES)"),
    ("core-mkey", "scan_core", "Bitcoin Core wallet.dat (mkey/ckey)"),
    ("der-key", "scan_der", "DER-encoded EC private keys in raw bytes (pywallet --recover)"),
    ("mnemonic-file", "scan_mnemonic_file", "standalone file whose whole content is ONLY a seed (BIP39 or any Electrum type)"),
    ("bip39", "scan_bip39", "BIP39 seed phrase embedded anywhere (sliding window)"),
    ("hex", "scan_hex", "raw 64-hex privkey candidates (UNVERIFIED, off in 'all')"),
    ("privkey-sweep", "scan_privkey_sweep", "32-byte sliding-window brute, balance-filtered (ameijer; needs --check-balance, small input)"),
]
_SCHEME_IDS = [s[0] for s in SCHEMES]


def resolve_schemes(tokens):
    # token matching: 'all' = every validated scheme (not hex); '*' = everything;
    # exact id; fnmatch wildcard (e.g. 'electrum-*'); or a group prefix (e.g. 'electrum')
    sel = set()
    for sid in _SCHEME_IDS:
        for tk in tokens:
            tk = tk.strip()
            if not tk:
                continue
            if tk == "all":
                if sid not in ("hex", "privkey-sweep"):
                    sel.add(sid)
            elif tk == "*":
                sel.add(sid)
            elif sid == tk or fnmatch.fnmatch(sid, tk) or fnmatch.fnmatch(sid, tk + "-*"):
                sel.add(sid)
    return sel


# ---------------------------------------------------------------- addresses + balance
def _ripemd160_py(msg):
    # compact pure-python RIPEMD-160 (fallback for OpenSSL builds without it)
    import struct as _st
    rol = lambda x, n: ((x << n) | (x >> (32 - n))) & 0xFFFFFFFF
    rl = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
          7, 4, 13, 1, 10, 6, 15, 3, 12, 0, 9, 5, 2, 14, 11, 8,
          3, 10, 14, 4, 9, 15, 8, 1, 2, 7, 0, 6, 13, 11, 5, 12,
          1, 9, 11, 10, 0, 8, 12, 4, 13, 3, 7, 15, 14, 5, 6, 2,
          4, 0, 5, 9, 7, 12, 2, 10, 14, 1, 3, 8, 11, 6, 15, 13]
    rr = [5, 14, 7, 0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12,
          6, 11, 3, 7, 0, 13, 5, 10, 14, 15, 8, 12, 4, 9, 1, 2,
          15, 5, 1, 3, 7, 14, 6, 9, 11, 8, 12, 2, 10, 0, 4, 13,
          8, 6, 4, 1, 3, 11, 15, 0, 5, 12, 2, 13, 9, 7, 10, 14,
          12, 15, 10, 4, 1, 5, 8, 7, 6, 2, 13, 14, 0, 3, 9, 11]
    sl = [11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8,
          7, 6, 8, 13, 11, 9, 7, 15, 7, 12, 15, 9, 11, 7, 13, 12,
          11, 13, 6, 7, 14, 9, 13, 15, 14, 8, 13, 6, 5, 12, 7, 5,
          11, 12, 14, 15, 14, 15, 9, 8, 9, 14, 5, 6, 8, 6, 5, 12,
          9, 15, 5, 11, 6, 8, 13, 12, 5, 12, 13, 14, 11, 8, 5, 6]
    sr = [8, 9, 9, 11, 13, 15, 15, 5, 7, 7, 8, 11, 14, 14, 12, 6,
          9, 13, 15, 7, 12, 8, 9, 11, 7, 7, 12, 7, 6, 15, 13, 11,
          9, 7, 15, 11, 8, 6, 6, 14, 12, 13, 5, 14, 13, 13, 7, 5,
          15, 5, 8, 11, 14, 14, 6, 14, 6, 9, 12, 9, 12, 5, 15, 8,
          8, 5, 12, 9, 12, 5, 14, 6, 8, 13, 6, 5, 15, 13, 11, 11]
    kl = [0, 0x5A827999, 0x6ED9EBA1, 0x8F1BBCDC, 0xA953FD4E]
    kr = [0x50A28BE6, 0x5C4DD124, 0x6D703EF3, 0x7A6D76E9, 0]

    def f(j, x, y, z):
        if j < 16:
            return x ^ y ^ z
        if j < 32:
            return (x & y) | (~x & z)
        if j < 48:
            return (x | ~y) ^ z
        if j < 64:
            return (x & z) | (y & ~z)
        return x ^ (y | ~z)

    ml = len(msg)
    msg = msg + b"\x80" + b"\x00" * ((55 - ml) % 64) + _st.pack("<Q", ml * 8)
    h0, h1, h2, h3, h4 = 0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0
    for off in range(0, len(msg), 64):
        X = list(_st.unpack("<16I", msg[off:off + 64]))
        al, bl, cl, dl, el = h0, h1, h2, h3, h4
        ar, br, cr, dr, er = h0, h1, h2, h3, h4
        for j in range(80):
            t = (al + f(j, bl, cl, dl) + X[rl[j]] + kl[j // 16]) & 0xFFFFFFFF
            t = (rol(t, sl[j]) + el) & 0xFFFFFFFF
            al, el, dl, cl, bl = el, dl, rol(cl, 10), bl, t
            t = (ar + f(79 - j, br, cr, dr) + X[rr[j]] + kr[j // 16]) & 0xFFFFFFFF
            t = (rol(t, sr[j]) + er) & 0xFFFFFFFF
            ar, er, dr, cr, br = er, dr, rol(cr, 10), br, t
        t = (h1 + cl + dr) & 0xFFFFFFFF
        h1 = (h2 + dl + er) & 0xFFFFFFFF
        h2 = (h3 + el + ar) & 0xFFFFFFFF
        h3 = (h4 + al + br) & 0xFFFFFFFF
        h4 = (h0 + bl + cr) & 0xFFFFFFFF
        h0 = t
    return _st.pack("<5I", h0, h1, h2, h3, h4)


def _ripemd160(b):
    try:
        h = hashlib.new("ripemd160")
        h.update(b)
        return h.digest()
    except (ValueError, TypeError):
        return _ripemd160_py(b)


def hash160(b):
    return _ripemd160(sha256(b))


def b58encode(b):
    n = int.from_bytes(b, "big")
    out = b""
    while n > 0:
        n, r = divmod(n, 58)
        out = _B58[r:r + 1] + out
    return b"1" * (len(b) - len(b.lstrip(b"\x00"))) + out


def b58check_encode(payload):
    return b58encode(payload + dsha256(payload)[:4]).decode()


def privkey_to_wif(priv32, compressed, testnet=False):
    payload = bytes([0xEF if testnet else 0x80]) + priv32 + (b"\x01" if compressed else b"")
    return b58check_encode(payload)


def addr_p2pkh(pubkey, ver=0x00):
    return b58check_encode(bytes([ver]) + hash160(pubkey))


def addr_p2sh(script_hash, ver=0x05):
    return b58check_encode(bytes([ver]) + script_hash)


_BECH = "qpzry9x8gf2tvdw0s3jn54khce6mua7l"


def _bech_polymod(values):
    gen = [0x3B6A57B2, 0x26508E6D, 0x1EA119FA, 0x3D4233DD, 0x2A1462B3]
    chk = 1
    for v in values:
        top = chk >> 25
        chk = ((chk & 0x1FFFFFF) << 5) ^ v
        for i in range(5):
            chk ^= gen[i] if ((top >> i) & 1) else 0
    return chk


def _bech_hrp_expand(hrp):
    return [ord(c) >> 5 for c in hrp] + [0] + [ord(c) & 31 for c in hrp]


def _bech_checksum(hrp, data):
    pm = _bech_polymod(_bech_hrp_expand(hrp) + data + [0] * 6) ^ 1
    return [(pm >> 5 * (5 - i)) & 31 for i in range(6)]


def _convertbits(data, frm, to, pad=True):
    acc = 0
    bits = 0
    ret = []
    maxv = (1 << to) - 1
    for b in data:
        acc = (acc << frm) | b
        bits += frm
        while bits >= to:
            bits -= to
            ret.append((acc >> bits) & maxv)
    if pad and bits:
        ret.append((acc << (to - bits)) & maxv)
    return ret


def bech32_encode(hrp, witver, witprog):
    data = [witver] + _convertbits(list(witprog), 8, 5)
    return hrp + "1" + "".join(_BECH[d] for d in data + _bech_checksum(hrp, data))


def addr_p2wpkh(pubkey_comp):
    return bech32_encode("bc", 0, hash160(pubkey_comp))


def addr_p2sh_p2wpkh(pubkey_comp):
    redeem = b"\x00\x14" + hash160(pubkey_comp)
    return addr_p2sh(hash160(redeem))


def addresses_from_priv(priv32):
    comp = pub_from_priv(priv32, True)
    unc = pub_from_priv(priv32, False)
    return [("p2pkh-c", addr_p2pkh(comp)), ("p2pkh-u", addr_p2pkh(unc)),
            ("p2wpkh", addr_p2wpkh(comp)), ("p2sh-p2wpkh", addr_p2sh_p2wpkh(comp))]


# -- Electrum pre-2.0 deterministic derivation (verified vs official vector) --
def _oe_stretch(seed_ascii):
    x = seed_ascii
    for _ in range(100000):
        x = hashlib.sha256(x + seed_ascii).digest()
    return int.from_bytes(x, "big")


def old_electrum_addresses(seed_hex, gap=20):
    seed_ascii = seed_hex.encode("ascii")
    secexp = _oe_stretch(seed_ascii)
    P = _pt_mul(secexp, _G)
    mpk = P[0].to_bytes(32, "big") + P[1].to_bytes(32, "big")
    out = []
    for for_change in (0, 1):
        for n in range(gap):
            z = int.from_bytes(dsha256(("%d:%d:" % (n, for_change)).encode() + mpk), "big")
            Q = _pt_add(P, _pt_mul(z, _G))
            unc = b"\x04" + Q[0].to_bytes(32, "big") + Q[1].to_bytes(32, "big")
            out.append(("%s/%d" % ("recv" if for_change == 0 else "chg", n), addr_p2pkh(unc)))
    return out


# -- Electrum 2.0+ seeds: version prefix + derivation (no wordlist dependency) --
def electrum_normalize(seed):
    seed = unicodedata.normalize("NFKD", seed).lower()
    seed = "".join(c for c in seed if not unicodedata.combining(c))
    return " ".join(seed.split())


_ELECTRUM_PREFIXES = (("01", "standard"), ("100", "segwit"), ("101", "2fa"), ("102", "2fa_segwit"))


def electrum_seed_type(seed):
    h = hmac.new(b"Seed version", electrum_normalize(seed).encode("utf-8"), hashlib.sha512).hexdigest()
    for pre, name in _ELECTRUM_PREFIXES:
        if h.startswith(pre):
            return name
    return None


def electrum_new_addresses(seed, gap=20, stype="standard", passphrase=""):
    # standard  -> m/0/i, m/1/i   P2PKH
    # segwit    -> m/0'/0/i, m/0'/1/i   P2WPKH
    # 2fa types -> require the TrustedCoin cosigner; cannot be derived offline
    bip32_seed = hashlib.pbkdf2_hmac("sha512", electrum_normalize(seed).encode("utf-8"),
                                     b"electrum" + passphrase.encode("utf-8"), 2048)
    k, c = _bip32_master(bip32_seed)
    out = []
    if stype == "standard":
        for ch in (0, 1):
            bk, bc = _ckd_priv(k, c, ch)
            for i in range(gap):
                lk, _lc = _ckd_priv(bk, bc, i)
                out.append(("std/%d/%d" % (ch, i), addr_p2pkh(pub_from_priv(lk, True))))
    elif stype == "segwit":
        ak, ac = _ckd_priv(k, c, 0x80000000)
        for ch in (0, 1):
            bk, bc = _ckd_priv(ak, ac, ch)
            for i in range(gap):
                lk, _lc = _ckd_priv(bk, bc, i)
                out.append(("sw/%d/%d" % (ch, i), addr_p2wpkh(pub_from_priv(lk, True))))
    return out


# -- Electrum 1.x (old) mnemonic -> hex seed (needs the 1626-word old wordlist) --
_OLD_EL_WORDLIST = None


def load_old_electrum_wordlist(path=None):
    global _OLD_EL_WORDLIST
    if path:
        try:
            with open(path) as f:
                words = [w.strip() for w in f if w.strip()]
            if len(words) == 1626:
                _OLD_EL_WORDLIST = words
                return True
        except OSError:
            pass
        return False
    for mod, attr in (("electrum.old_mnemonic", "wordlist"), ("electrum.old_mnemonic", "words")):
        try:
            m = __import__(mod, fromlist=[attr])
            w = list(getattr(m, attr))
            if len(w) == 1626:
                _OLD_EL_WORDLIST = w
                return True
        except Exception:
            continue
    return False


def old_electrum_mn_decode(toks):
    words = _OLD_EL_WORDLIST
    if not words or len(toks) % 3 != 0:
        return None
    idx = {w: i for i, w in enumerate(words)}
    n = 1626
    out = ""
    for i in range(len(toks) // 3):
        w1, w2, w3 = toks[3 * i:3 * i + 3]
        if w1 not in idx or w2 not in idx or w3 not in idx:
            return None
        x1, x2, x3 = idx[w1], idx[w2] % n, idx[w3] % n
        x = x1 + n * ((x2 - x1) % n) + n * n * ((x3 - x2) % n)
        out += "%08x" % x
    return out


# -- BIP32 (verified vs BIP32 test vector 1) --
def _bip32_master(seed):
    i = hmac.new(b"Bitcoin seed", seed, hashlib.sha512).digest()
    return i[:32], i[32:]


def _ckd_priv(k, c, index):
    if index & 0x80000000:
        data = b"\x00" + k + index.to_bytes(4, "big")
    else:
        data = pub_from_priv(k, True) + index.to_bytes(4, "big")
    i = hmac.new(c, data, hashlib.sha512).digest()
    ki = (int.from_bytes(i[:32], "big") + int.from_bytes(k, "big")) % _N
    return ki.to_bytes(32, "big"), i[32:]


def _ckd_pub(point, c, index):
    if index & 0x80000000:
        return None
    i = hmac.new(c, _compress(point) + index.to_bytes(4, "big"), hashlib.sha512).digest()
    newpt = _pt_add(_pt_mul(int.from_bytes(i[:32], "big"), _G), point)
    return newpt, i[32:]


def _derive_priv(k, c, path):
    for idx in path:
        k, c = _ckd_priv(k, c, idx)
    return k, c


def parse_bip32(ext):
    data = b58check(ext.encode())
    if not data or len(data) != 78:
        return None
    ver, chain, key = data[:4], data[13:45], data[45:78]
    if ver in (b"\x04\x88\xad\xe4", b"\x04\x35\x83\x94"):
        return ("priv", key[1:], chain) if key[0] == 0 else None
    if ver in (b"\x04\x88\xb2\x1e", b"\x04\x35\x87\xcf"):
        return ("pub", key, chain)
    return None


_H = 0x80000000
# (label, account-path-from-root, [address types]); empty path = Electrum (root/0, root/1)
_HD_SCHEMES = [
    ("bip44", [44 + _H, 0 + _H, 0 + _H], ["p2pkh"]),
    ("bip49", [49 + _H, 0 + _H, 0 + _H], ["p2sh"]),
    ("bip84", [84 + _H, 0 + _H, 0 + _H], ["p2wpkh"]),
    ("electrum", [], ["p2pkh", "p2wpkh"]),
]


def _addr_of(pub_comp, t):
    if t == "p2pkh":
        return addr_p2pkh(pub_comp)
    if t == "p2wpkh":
        return addr_p2wpkh(pub_comp)
    return addr_p2sh_p2wpkh(pub_comp)


def hd_addresses_from_root(k, c, gap):
    out = []
    for name, acct, types in _HD_SCHEMES:
        ak, ac = _derive_priv(k, c, acct)
        for change in (0, 1):
            chk, chc = _ckd_priv(ak, ac, change)
            for i in range(gap):
                lk, _lc = _ckd_priv(chk, chc, i)
                pub = pub_from_priv(lk, True)
                for t in types:
                    out.append(("%s/%d/%d-%s" % (name, change, i, t), _addr_of(pub, t)))
    return out


def hd_addresses_from_xpub(point, c, gap):
    out = []
    for change in (0, 1):
        r = _ckd_pub(point, c, change)
        if r is None:
            continue
        cpt, cc = r
        for i in range(gap):
            ri = _ckd_pub(cpt, cc, i)
            if ri is None:
                continue
            pub = _compress(ri[0])
            for t in ("p2pkh", "p2wpkh", "p2sh"):
                out.append(("xpub/%d/%d-%s" % (change, i, t), _addr_of(pub, t)))
    return out


def derive_addresses_for_finding(r, gap):
    k = r["kind"]
    out = []

    def from_priv_hex(h):
        return addresses_from_priv(bytes.fromhex(h))

    if k in ("wif_privkey", "der_privkey", "sweep_hit"):
        out += from_priv_hex(r["privkey_hex"])
    elif k == "bitcoin_core_mkey":
        for rk in r.get("recovered_keys", []):
            out += from_priv_hex(rk["privkey_hex"])
    elif k == "electrum_old_wallet":
        if r.get("seed"):
            out += old_electrum_addresses(r["seed"], gap)
        for rec in r.get("recovered", []):
            if rec["type"] == "old_seed_hex":
                out += old_electrum_addresses(rec["seed_hex"], gap)
            elif rec["type"] == "imported_wif":
                out += from_priv_hex(rec["privkey_hex"])
    elif k in ("ext_xprv", "ext_tprv"):
        p = parse_bip32(r["ext"])
        if p and p[0] == "priv":
            out += hd_addresses_from_root(p[1], p[2], gap)
    elif k in ("ext_xpub", "ext_tpub"):
        p = parse_bip32(r["ext"])
        if p and p[0] == "pub":
            out += hd_addresses_from_xpub(_decompress(p[1]), p[2], gap)
    elif k in ("bip39_seed", "mnemonic_file") and _HAVE_MNEMONIC:
        kk, cc = _bip32_master(Mnemonic.to_seed(r["mnemonic"]))
        out += hd_addresses_from_root(kk, cc, gap)
    elif k == "electrum_seed":
        out += electrum_new_addresses(r["mnemonic"], gap, r.get("electrum_type", "standard"))
    elif k == "electrum_old_seed":
        out += old_electrum_addresses(r["seed_hex"], gap)
    elif k == "electrum_plaintext_wallet":
        xprv = (r.get("loot") or {}).get("xprv")
        if xprv:
            p = parse_bip32(str(xprv))
            if p and p[0] == "priv":
                out += hd_addresses_from_root(p[1], p[2], gap)
    return out


def esplora_balance(api, addr, timeout=20):
    url = api.rstrip("/") + "/address/" + addr
    req = urllib.request.Request(url, headers={"User-Agent": "wallet-carver"})
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        j = json.loads(resp.read().decode())
    cs = j.get("chain_stats", {})
    ms = j.get("mempool_stats", {})
    funded = cs.get("funded_txo_sum", 0) + ms.get("funded_txo_sum", 0)
    spent = cs.get("spent_txo_sum", 0) + ms.get("spent_txo_sum", 0)
    txs = cs.get("tx_count", 0) + ms.get("tx_count", 0)
    return funded - spent, txs


def run_balance_check(findings, outdir, api_url, gap, query):
    entries = []
    for r in findings:
        if not Carver._is_valuable(r):
            continue
        for desc, addr in derive_addresses_for_finding(r, gap):
            entries.append((r["kind"], r.get("offset"), desc, addr))
    seen = set()
    uniq = []
    for e in entries:
        if e[3] in seen:
            continue
        seen.add(e[3])
        uniq.append(e)

    apath = os.path.join(outdir, "addresses.txt")
    with open(apath, "w") as f:
        for kind, off, desc, addr in uniq:
            f.write("%s\t%s\t%s\t%s\n" % (addr, kind, off, desc))
    sys.stderr.write("\n[*] derived %d unique address(es) -> %s\n" % (len(uniq), apath))

    if not query:
        sys.stderr.write("[*] --addresses-only: not contacting any API; check these on your own node\n")
        return
    if not uniq:
        sys.stderr.write("[*] nothing to check\n")
        return

    sys.stderr.write("[!] privacy: querying %s discloses these addresses to that server\n" % api_url)
    bpath = os.path.join(outdir, "balances.txt")
    total = 0
    funded = 0
    with open(bpath, "w") as bf:
        for idx, (kind, off, desc, addr) in enumerate(uniq, 1):
            try:
                bal, txs = esplora_balance(api_url, addr)
            except urllib.error.HTTPError as e:
                if e.code == 429:
                    time.sleep(2.0)
                sys.stderr.write("  ?  %s (HTTP %s)\n" % (addr, e.code))
                continue
            except Exception as ex:
                sys.stderr.write("  ?  %s (%s)\n" % (addr, type(ex).__name__))
                continue
            if txs > 0 or bal > 0:
                flag = ">>>" if bal > 0 else "   "
                sys.stderr.write("  %s %-42s %14d sat  %d tx  [%s %s]\n" % (flag, addr, bal, txs, kind, desc))
                bf.write("%s\t%d\t%d\t%s\t%s\n" % (addr, bal, txs, kind, desc))
                total += bal
                if bal > 0:
                    funded += 1
            time.sleep(0.25)
            if idx % 50 == 0:
                sys.stderr.write("[*] checked %d/%d ...\n" % (idx, len(uniq)))
    sys.stderr.write("\n==================== BALANCE ====================\n")
    sys.stderr.write("total: %d sat = %.8f BTC across %d funded address(es)\n" % (total, total / 1e8, funded))
    sys.stderr.write("details -> %s\n" % bpath)


# ---------------------------------------------------------------- selftest
def selftest():
    ensure_deps()
    ok = True

    def check(name, cond):
        nonlocal ok
        sys.stderr.write("  %-28s %s\n" % (name, "ok" if cond else "FAIL"))
        ok = ok and cond

    # secp256k1: priv=1 -> G
    check("secp256k1 G", pub_from_priv((1).to_bytes(32, "big")) == _compress(_G))
    # known WIF for privkey 0x01 (compressed, mainnet)
    wif = b"KwDiBf89QgGbjEhKnhXJuH7LrciVrZi3qYjgd9M7rFU73sVHnoWn"
    p = parse_wif(wif)
    check("WIF base58check", p is not None and p["privkey_hex"] == "01".zfill(64))
    # Bitcoin Core mkey round trip
    salt = os.urandom(8)
    iters = 1000
    pw = "correct horse battery staple"
    key, iv = core_derive(pw, salt, iters)
    master = os.urandom(32)
    enc_master = aes_cbc_encrypt(key, iv, master + b"\x10" * 16)
    rec = core_try_mkey(enc_master, salt, iters, pw)
    check("core mkey decrypt", rec == master)
    check("core mkey wrong-pw", core_try_mkey(enc_master, salt, iters, "wrong") is None)
    # core ckey round trip
    priv = os.urandom(32)
    pub = pub_from_priv(priv, compressed=True)
    iv2 = dsha256(pub)[:16]
    ck = aes_cbc_encrypt(master, iv2, priv + b"\x10" * 16)
    d = core_decrypt_ckey(master, pub, ck)
    check("core ckey decrypt", d is not None and d["privkey_hex"] == priv.hex() and d["pubkey_match"])
    # Electrum pre-2.0 (seed_version 4) seed round trip
    pw_old = "p\u00e4ssw\u00f6rd"
    seed_hex = "0123456789abcdef0123456789abcdef"
    key_old = dsha256(unicodedata.normalize("NFC", pw_old).encode("utf-8"))
    iv_old = os.urandom(16)
    data = seed_hex.encode("ascii")
    n = 16 - (len(data) % 16)
    field = base64.b64encode(iv_old + aes_cbc_encrypt(key_old, iv_old, data + bytes([n]) * n))
    check("electrum v4 seed", electrum_old_decrypt_field(field, pw_old) == seed_hex.encode())
    check("electrum v4 wrong-pw", electrum_old_decrypt_field(field, "nope") is None)
    # address derivation vectors
    p1 = (1).to_bytes(32, "big")
    check("P2PKH compressed", addr_p2pkh(pub_from_priv(p1, True)) == "1BgGZ9tcN4rm9KBzDn7KprQz87SZ26SAMH")
    check("P2PKH uncompressed", addr_p2pkh(pub_from_priv(p1, False)) == "1EHNa6Q4Jz2uvNExL497mE43ikXhwF6kZm")
    check("bech32 P2WPKH", bech32_encode("bc", 0, bytes.fromhex("751e76e8199196d454941c45d1b3a323f1433bd6")) == "bc1qw508d6qejxtdg4y5r3zarvary0c5xw7kv8f3t4")
    try:
        check("ripemd160 fallback", _ripemd160_py(b"abc") == hashlib.new("ripemd160", b"abc").digest())
    except Exception:
        pass
    oe = dict(old_electrum_addresses("00112233445566778899aabbccddeeff", gap=1))
    check("old-electrum m/0/0", oe.get("recv/0") == "1JWcDJsfwi2oFYdWYq3qMQPW52mu2XPUyY")
    mk, mc = _bip32_master(bytes.fromhex("000102030405060708090a0b0c0d0e0f"))
    check("BIP32 master key", mk.hex() == "e8f32e723decf4051aefac8e2c93c9c5b214313817cdb01a1494b917c8436b35")
    esd = "wild father tree among universe such mobile favorite target dynamic credit identify"
    check("electrum seed type", electrum_seed_type(esd) == "segwit")
    swa = dict(electrum_new_addresses(esd, gap=1, stype="segwit"))
    check("electrum segwit m/0'/0/0", swa.get("sw/0/0") == "bc1q4794m2uuw9jmjszmplfj4wvvr5j272fpnx2cse")
    # WIF encoder round-trips through the decoder
    check("WIF encode/decode", parse_wif(privkey_to_wif(p1, True).encode())["privkey_hex"] == p1.hex())
    # DER EC key scan extracts the embedded secret and validates the embedded pubkey
    dsecret = bytes.fromhex("0000000000000000000000000000000000000000000000000000000000000003")
    dpub = pub_from_priv(dsecret, False)[1:]
    der = (b"\x30\x81\xd3\x02\x01\x01\x04\x20" + dsecret + b"\xa0\x81\x85\x30\x81\x82"
           + b"\x00" * 100 + b"\x03\x42\x00\x04" + dpub + b"\x00" * 8)
    cfg = {"passwords": [], "selected": {"der-key"}, "min_iter": 1, "max_iter": 5,
           "bip39": False, "no_progress": True}
    cv = Carver(cfg)
    cv.scan_der(b"\x00" * 64 + der + b"\x00" * 64)
    check("DER key scan", any(r["kind"] == "der_privkey" and r["privkey_hex"] == dsecret.hex() for r in cv.findings))
    sys.stderr.write("selftest: %s\n" % ("PASS" if ok else "FAIL"))
    return 0 if ok else 1


# ---------------------------------------------------------------- main
def main():
    ap = argparse.ArgumentParser(description="wallet carver engine")
    ap.add_argument("-i", "--image")
    ap.add_argument("-p", "--passwords")
    ap.add_argument("-o", "--out", default="carver_out")
    ap.add_argument("-s", "-t", "--schemes", "--types", dest="schemes", default="all")
    ap.add_argument("--min-iter", type=int, default=1)
    ap.add_argument("--max-iter", type=int, default=5_000_000)
    ap.add_argument("--hex", action="store_true")
    ap.add_argument("--seedfile-nochecksum", action="store_true",
                    help="mnemonic-file: also report exact 12/24-word wordlist-only regions with a failing checksum")
    ap.add_argument("--electrum-old-wordlist", metavar="FILE",
                    help="path to Electrum 1.x 1626-word list (enables detection of standalone OLD Electrum mnemonics)")
    ap.add_argument("--check-balance", action="store_true",
                    help="derive addresses from recovered material and query on-chain balance (needs network)")
    ap.add_argument("--addresses-only", action="store_true",
                    help="derive addresses but do NOT query any API (OPSEC-safe; check on your own node)")
    ap.add_argument("--api-url", default="https://blockstream.info/api",
                    help="Esplora-compatible API base (default blockstream.info; use your own for privacy)")
    ap.add_argument("--gap", type=int, default=20, help="address gap limit for seed/xprv derivation")
    ap.add_argument("--sweep-max-mb", type=float, default=0.25,
                    help="privkey-sweep: max input size in MiB to brute (default 0.25; sweep is API-bound)")
    ap.add_argument("--sweep-step", type=int, default=1, help="privkey-sweep: byte step between candidates")
    ap.add_argument("--no-progress", action="store_true")
    ap.add_argument("--install-deps", action="store_true")
    ap.add_argument("--list-schemes", action="store_true")
    ap.add_argument("--selftest", action="store_true")
    a = ap.parse_args()

    if a.selftest:
        sys.exit(selftest())

    if a.list_schemes:
        sys.stderr.write("available schemes (match with exact id, wildcard, group, 'all', or '*'):\n")
        for sid, _, desc in SCHEMES:
            sys.stderr.write("  %-20s %s\n" % (sid, desc))
        sys.stderr.write("\nexamples: --schemes all | --schemes 'electrum-*' | --schemes electrum-v4,core-mkey | --schemes '*'\n")
        sys.exit(0)

    if not a.image:
        ap.error("-i/--image required")

    ensure_deps(install=a.install_deps)

    if load_old_electrum_wordlist(a.electrum_old_wordlist):
        sys.stderr.write("[*] Electrum 1.x wordlist loaded -> old-mnemonic detection enabled\n")
    elif a.electrum_old_wordlist:
        sys.stderr.write("[!] could not load Electrum old wordlist from %s (need exactly 1626 words)\n" % a.electrum_old_wordlist)

    passwords = []
    if a.passwords:
        with open(a.passwords, "rb") as f:
            for line in f.read().split(b"\n"):
                if line == b"" and passwords:
                    continue
                try:
                    passwords.append(line.decode("utf-8"))
                except UnicodeDecodeError:
                    passwords.append(line.decode("latin-1"))
        # keep a possible empty password only if the file literally had a blank line kept; de-dup
        seen = set()
        passwords = [p for p in passwords if not (p in seen or seen.add(p))]

    tokens = [t.strip() for t in a.schemes.split(",") if t.strip()]
    selected = resolve_schemes(tokens)
    if a.hex:
        selected.add("hex")
    if not selected:
        sys.stderr.write("no schemes matched %r (see --list-schemes)\n" % a.schemes)
        sys.exit(2)
    cfg = {
        "passwords": passwords,
        "selected": selected,
        "min_iter": a.min_iter,
        "max_iter": a.max_iter,
        "bip39": ("bip39" in selected) or ("mnemonic-file" in selected),
        "seedfile_strict": not a.seedfile_nochecksum,
        "no_progress": a.no_progress,
        "sweep_check": a.check_balance,
        "api_url": a.api_url,
        "sweep_max_bytes": int(a.sweep_max_mb * (1 << 20)),
        "sweep_step": max(1, a.sweep_step),
    }

    os.makedirs(a.out, exist_ok=True)
    try:
        os.chmod(a.out, 0o700)
    except OSError:
        pass

    sys.stderr.write("[*] image: %s (%d bytes)\n" % (a.image, os.path.getsize(a.image)))
    sys.stderr.write("[*] passwords loaded: %d\n" % len(passwords))
    sys.stderr.write("[*] schemes: %s\n" % ",".join(s for s in _SCHEME_IDS if s in selected))

    out_jsonl = os.path.join(a.out, "findings.jsonl")
    fd = os.open(out_jsonl, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
    carver = Carver(cfg)
    carver.jsonl_fh = os.fdopen(fd, "w")  # live, flushed per finding
    try:
        carver.run(a.image)
    finally:
        carver.jsonl_fh.flush()

    if a.check_balance or a.addresses_only:
        run_balance_check(carver.findings, a.out, api_url=a.api_url,
                          gap=a.gap, query=a.check_balance)

    carver.jsonl_fh.close()

    verified = [r for r in carver.findings if "VALID" in r["status"] or r["status"] in ("DECRYPTED", "PLAINTEXT")]
    encrypted = [r for r in carver.findings if "ENCRYPTED" in r["status"]]
    unverified = [r for r in carver.findings if "UNVERIFIED" in r["status"]]

    sys.stderr.write("\n==================== SUMMARY ====================\n")
    sys.stderr.write("verified / decrypted : %d\n" % len(verified))
    sys.stderr.write("encrypted (locked)   : %d\n" % len(encrypted))
    sys.stderr.write("unverified (hex)     : %d\n" % len(unverified))
    sys.stderr.write("findings written to  : %s (mode 0600)\n" % out_jsonl)
    if encrypted:
        sys.stderr.write("note: %d encrypted candidate(s) not opened by the given password list\n" % len(encrypted))


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""A minimal IMAP server for exercising angelia's IMAP connector end to end.

Serves the ``*.eml`` files in a directory as INBOX, in name order, and notices new files while
running: a client in IDLE gets ``* n EXISTS`` within a fraction of a second. Plain TCP; point the
connector at it with ``"transport": ["nc", "127.0.0.1", "<port>"]``.

    fake_imap.py MAILDIR [PORT]

Accepts any credentials. Implements only what the connector sends.
"""

import base64
import os
import re
import socketserver
import sys
import threading
import time

MAILDIR = sys.argv[1]
PORT = int(sys.argv[2]) if len(sys.argv) > 2 else 11143
UIDVALIDITY = 1234

lock = threading.Lock()
messages = []  # (uid, bytes)
seen_files = set()
idlers = set()


def scan():
    added = False
    with lock:
        for name in sorted(os.listdir(MAILDIR)):
            if name.endswith(".eml") and name not in seen_files:
                seen_files.add(name)
                with open(os.path.join(MAILDIR, name), "rb") as f:
                    data = f.read().replace(b"\r\n", b"\n").replace(b"\n", b"\r\n")
                messages.append((len(messages) + 100, data))
                added = True
        count = len(messages)
    if added:
        for h in list(idlers):
            h.send(f"* {count} EXISTS\r\n".encode())


def watcher():
    while True:
        scan()
        time.sleep(0.2)


def parse_set(spec, values):
    """Resolve an IMAP sequence set against the sorted list of valid numbers."""
    out = set()
    top = values[-1] if values else 0
    for part in spec.split(","):
        a, _, b = part.partition(":")
        lo = top if a == "*" else int(a)
        hi = lo if not b else (top if b == "*" else int(b))
        lo, hi = min(lo, hi), max(lo, hi)
        out.update(v for v in values if lo <= v <= hi)
    return sorted(out)


class Handler(socketserver.StreamRequestHandler):
    def send(self, data):
        try:
            self.wfile.write(data)
            self.wfile.flush()
        except OSError:
            idlers.discard(self)

    def handle(self):
        self.send(b"* OK [CAPABILITY IMAP4rev1 IDLE AUTH=PLAIN] fake ready\r\n")
        while True:
            line = self.rfile.readline()
            if not line:
                return
            line = line.decode("latin-1").rstrip("\r\n")
            tag, _, rest = line.partition(" ")
            cmd, _, args = rest.partition(" ")
            cmd = cmd.upper()
            if cmd == "UID":
                sub, _, args = args.partition(" ")
                cmd = "UID " + sub.upper()
            if cmd == "CAPABILITY":
                self.send(b"* CAPABILITY IMAP4rev1 IDLE AUTH=PLAIN\r\n")
            elif cmd == "AUTHENTICATE":
                self.send(b"+ \r\n")
                creds = base64.b64decode(self.rfile.readline().strip()).split(b"\0")
                print("login", creds[1].decode(), file=sys.stderr)
            elif cmd in ("EXAMINE", "SELECT"):
                with lock:
                    n = len(messages)
                    nxt = (messages[-1][0] + 1) if messages else 100
                self.send(f"* {n} EXISTS\r\n* OK [UIDVALIDITY {UIDVALIDITY}] ok\r\n"
                          f"* OK [UIDNEXT {nxt}] ok\r\n".encode())
            elif cmd in ("FETCH", "UID FETCH"):
                spec, _, items = args.partition(" ")
                m = re.search(r"<0\.(\d+)>", items)
                limit = int(m.group(1)) if m else None
                with lock:
                    snapshot = list(messages)
                by_uid = cmd == "UID FETCH"
                keys = [u for u, _ in snapshot] if by_uid else list(range(1, len(snapshot) + 1))
                for k in parse_set(spec, keys):
                    seq = keys.index(k) + 1 if by_uid else k
                    uid, data = snapshot[seq - 1]
                    if "BODY" not in items.upper():
                        self.send(f"* {seq} FETCH (UID {uid} RFC822.SIZE {len(data)})\r\n".encode())
                        continue
                    body = data[:limit] if limit else data
                    self.send(f"* {seq} FETCH (UID {uid} FLAGS () INTERNALDATE "
                              f"\"20-Oct-2026 10:00:00 +0000\" BODY[]<0> {{{len(body)}}}\r\n"
                              .encode() + body + b")\r\n")
                print(cmd, spec, items, file=sys.stderr, flush=True)
            elif cmd == "IDLE":
                self.send(b"+ idling\r\n")
                idlers.add(self)
                self.rfile.readline()  # DONE
                idlers.discard(self)
            elif cmd == "LOGOUT":
                self.send(b"* BYE\r\n")
                self.send(f"{tag} OK bye\r\n".encode())
                return
            self.send(f"{tag} OK done\r\n".encode())


class Server(socketserver.ThreadingTCPServer):
    allow_reuse_address = True
    daemon_threads = True


if __name__ == "__main__":
    threading.Thread(target=watcher, daemon=True).start()
    with Server(("127.0.0.1", PORT), Handler) as srv:
        srv.serve_forever()
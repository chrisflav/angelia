#!/usr/bin/env python3
"""A minimal SMTP submission server for exercising angelia's sending end to end.

Writes every message it accepts to OUTDIR as ``<n>.eml``, with the envelope beside it in
``<n>.envelope``, and refuses any recipient whose address contains ``reject``. Plain TCP; point a
source's `smtp` at it with ``"transport": ["nc", "127.0.0.1", "<port>"]``.

    fake_smtp.py OUTDIR [PORT]

Accepts any credentials.
"""

import os
import socketserver
import sys

OUTDIR = sys.argv[1]
PORT = int(sys.argv[2]) if len(sys.argv) > 2 else 11587


class Handler(socketserver.StreamRequestHandler):
    def reply(self, text):
        self.wfile.write(text.encode() + b"\r\n")
        self.wfile.flush()

    def handle(self):
        self.reply("220 fake ESMTP ready")
        sender, recipients = None, []
        while True:
            line = self.rfile.readline()
            if not line:
                return
            cmd = line.decode("latin-1").rstrip("\r\n")
            verb = cmd.split(" ")[0].upper()
            if verb == "EHLO":
                self.reply("250-fake greets " + cmd[5:])
                self.reply("250-AUTH PLAIN LOGIN")
                self.reply("250 8BITMIME")
            elif verb == "AUTH":
                print("auth", cmd.split(" ")[1], file=sys.stderr, flush=True)
                self.reply("235 2.7.0 accepted")
            elif cmd.upper().startswith("MAIL FROM:"):
                sender, recipients = cmd[10:].strip("<>"), []
                self.reply("250 2.1.0 ok")
            elif cmd.upper().startswith("RCPT TO:"):
                rcpt = cmd[8:].strip("<>")
                if "reject" in rcpt:
                    self.reply(f"550 5.1.1 <{rcpt}>: no such user")
                else:
                    recipients.append(rcpt)
                    self.reply("250 2.1.5 ok")
            elif verb == "DATA":
                self.reply("354 go ahead")
                lines = []
                while True:
                    l = self.rfile.readline()
                    if l in (b".\r\n", b".\n", b""):
                        break
                    lines.append(l[1:] if l.startswith(b"..") else l)
                n = len([f for f in os.listdir(OUTDIR) if f.endswith(".eml")]) + 1
                with open(os.path.join(OUTDIR, f"{n}.eml"), "wb") as f:
                    f.write(b"".join(lines))
                with open(os.path.join(OUTDIR, f"{n}.envelope"), "w") as f:
                    f.write(f"{sender}\n" + "\n".join(recipients) + "\n")
                print("message", n, sender, recipients, file=sys.stderr, flush=True)
                self.reply("250 2.0.0 queued")
            elif verb == "QUIT":
                self.reply("221 bye")
                return
            else:
                self.reply("502 5.5.2 not implemented")


class Server(socketserver.ThreadingTCPServer):
    allow_reuse_address = True
    daemon_threads = True


if __name__ == "__main__":
    with Server(("127.0.0.1", PORT), Handler) as srv:
        srv.serve_forever()

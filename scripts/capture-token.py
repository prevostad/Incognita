#!/usr/bin/env python3
"""Run a command on a pseudo-terminal (normally `claude setup-token`), show its output to the user
with every Claude token masked, and hand the token over on a file descriptor. Used by
scripts/start-night.sh: the owner follows the link and pastes the code as with `claude auth login`,
but the token never reaches the screen, a file or a log.

Usage: python3 -I scripts/capture-token.py --token-fd 3 [--min-cols 200] -- claude setup-token

The command sees a terminal at least --min-cols wide, so that its interface never breaks the token
across lines. Output that may be the beginning of a token is held back until it is known not to be
one. Exit: 0 one token captured (written to the descriptor, followed by a newline); 1 the command
ended without printing a token; 2 it printed several different tokens (none is given); 3 usage;
4 the command failed (or could not be started) without printing a token.
"""

import argparse
import fcntl
import os
import pty
import re
import select
import signal
import struct
import sys
import termios
import time
import tty

PREFIX = b"sk-ant-oat01-"
TOKEN = re.compile(rb"sk-ant-oat01-[A-Za-z0-9_-]+")
OPEN_TOKEN = re.compile(rb"sk-ant-oat01-[A-Za-z0-9_-]*\Z")
MASK = b"sk-ant-oat01-[hidden]"
POLL_S = 0.5
FRAGMENT_FLUSH_S = 2.0


class Masker:
    """Masks tokens in a byte stream that arrives in arbitrary chunks."""

    def __init__(self):
        self.held = b""
        self.held_since = 0.0
        self.tokens = []

    def feed(self, data, final=False):
        if data:
            self.held_since = time.monotonic()  # the time of the last output
        return self._feed(data, final)

    def _feed(self, data, final):
        buf = self.held + data
        out, pos = [], 0
        for m in TOKEN.finditer(buf):
            if m.end() == len(buf) and not final:
                break  # the token may go on in the next chunk
            out += [buf[pos:m.start()], MASK]
            self.tokens.append(m.group())
            pos = m.end()
        rest, hold = buf[pos:], 0
        if not final:
            m = OPEN_TOKEN.search(rest)
            if m:
                hold = len(rest) - m.start()
            else:
                for k in range(min(len(PREFIX) - 1, len(rest)), 0, -1):
                    if rest.endswith(PREFIX[:k]):
                        hold = k
                        break
        out.append(rest[:len(rest) - hold])
        self.held = rest[len(rest) - hold:]
        return b"".join(out)

    def flush_idle(self):
        """After a pause of FRAGMENT_FLUSH_S without output, a held fragment shorter than the prefix is
        not the start of a token (an "s" at the end of a prompt): it is shown. A held fragment with the
        whole prefix stays held until the stream says more (or ends)."""
        if self.held and PREFIX not in self.held and time.monotonic() - self.held_since >= FRAGMENT_FLUSH_S:
            out, self.held = self.held, b""
            return out
        return b""


def write_all(fd, data):
    while data:
        try:
            n = os.write(fd, data)
        except InterruptedError:
            continue
        data = data[n:]


def window_size(fd):
    try:
        rows, cols, _, _ = struct.unpack("HHHH", fcntl.ioctl(fd, termios.TIOCGWINSZ, b"\0" * 8))
        if rows and cols:
            return rows, cols
    except OSError:
        pass
    return 24, 80


def set_size(fd, rows, cols):
    try:
        fcntl.ioctl(fd, termios.TIOCSWINSZ, struct.pack("HHHH", rows, cols, 0, 0))
    except OSError:
        pass


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--token-fd", type=int, required=True)
    ap.add_argument("--min-cols", type=int, default=200)
    ap.add_argument("command", nargs=argparse.REMAINDER)
    a = ap.parse_args()
    cmd = a.command[1:] if a.command[:1] == ["--"] else a.command
    if not cmd:
        print("capture-token: no command", file=sys.stderr)
        return 3
    try:
        os.fstat(a.token_fd)
    except OSError:
        print("capture-token: the token descriptor %d is not open" % a.token_fd, file=sys.stderr)
        return 3

    term = 1 if os.isatty(1) else (0 if os.isatty(0) else None)
    rows, cols = window_size(term) if term is not None else (24, 80)
    pid, master = pty.fork()
    if pid == 0:  # the command: nothing open but its terminal
        os.closerange(3, 65536)
        try:
            os.execvp(cmd[0], cmd)
        except OSError as e:
            os.write(2, ("capture-token: cannot run %s: %s\n" % (cmd[0], e)).encode())
        os._exit(127)
    set_size(master, rows, max(cols, a.min_cols))

    def on_winch(_sig, _frame):
        r, c = window_size(term) if term is not None else (24, 80)
        set_size(master, r, max(c, a.min_cols))

    signal.signal(signal.SIGWINCH, on_winch)
    saved = None
    if os.isatty(0):
        saved = termios.tcgetattr(0)
        tty.setraw(0)
    masker, stdin_open, status = Masker(), True, None
    try:
        while True:
            fds = [master] + ([0] if stdin_open else [])
            try:
                ready, _, _ = select.select(fds, [], [], POLL_S)
            except InterruptedError:
                continue
            if not ready:
                write_all(1, masker.flush_idle())
                if status is None:
                    done, st = os.waitpid(pid, os.WNOHANG)
                    if done:
                        status = st
                elif not select.select([master], [], [], 0)[0]:
                    break  # the command ended and nothing more comes (a helper keeps the terminal)
                continue
            if master in ready:
                try:
                    data = os.read(master, 65536)
                except OSError:
                    data = b""  # EIO: the terminal is closed
                if not data:
                    break
                write_all(1, masker.feed(data))
            if 0 in ready:
                data = os.read(0, 4096)
                if data:
                    write_all(master, data)
                else:
                    stdin_open = False  # end of a standard input that is not a terminal
    finally:
        write_all(1, masker.feed(b"", final=True))
        if saved is not None:
            termios.tcsetattr(0, termios.TCSAFLUSH, saved)
        os.close(master)
    if status is None:
        _, status = os.waitpid(pid, 0)
    code = os.waitstatus_to_exitcode(status)
    tokens = sorted(set(masker.tokens))
    if len(tokens) == 1:
        os.write(a.token_fd, tokens[0] + b"\n")
        return 0
    if len(tokens) > 1:
        print("\r\ncapture-token: %d different tokens in the output: none is kept" % len(tokens), file=sys.stderr)
        return 2
    return 1 if code == 0 else 4


if __name__ == "__main__":
    sys.exit(main())

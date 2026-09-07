#!/usr/bin/env python3
"""How to call a program that may not be native to the shell running this.

The three translators are not all built for the same platform. On Windows the Lean and
Dafny binaries are `.exe` and the OCaml one is ELF; under WSL it is the other way round.
The trap is that the wrong combination does not fail cleanly: WSL's binfmt interop
*launches* a Windows `.exe` quite happily, and then hands it a `/mnt/c/...` path that a
Windows program cannot open, so it dies at its first read having written nothing.

"Wrote nothing" is also how a translator refuses a net, and how `run.py` reports a net
its adapter cannot express. A caller that assumes the calling convention therefore turns
a broken toolchain into a green run. That is `Tests/docs/Findings.md` 11, found by
running `check.sh` from WSL, and this module is its Python half -- `check.sh` carries the
same logic in shell.

The rule is: **probe, do not assume.** Ask the program to do something that must work,
in each convention, and keep the one that works.

    lean = Tool("lean", "/path/to/cpn2mcrl2.exe")
    lean.probe(lambda out: [net, out])      # a net that must translate
    if lean.mode == "none": ...             # unusable: exclude it from every check

Conventions:

    native  run it directly, with the paths this interpreter uses
    winexe  a Windows .exe called from WSL: arguments through `wslpath -w`
    wsl     an ELF called from Git Bash: through wsl.exe, with /mnt/c paths

An argument beginning with `-` is a flag and is passed through untouched; anything else
is a path and is converted.
"""

import os
import shutil
import subprocess
import tempfile

MODES = ("native", "winexe", "wsl")


def to_wsl(p):
    """A path as WSL sees it: C:\\x or /c/x -> /mnt/c/x."""
    p = p.replace("\\", "/")
    if len(p) > 1 and p[1] == ":":
        return "/mnt/" + p[0].lower() + p[2:]
    if p.startswith("/c/"):
        return "/mnt" + p
    return p


def to_win(p):
    """A path as Windows sees it. Uses wslpath when there is one, else by hand."""
    try:
        r = subprocess.run(["wslpath", "-w", p], stdout=subprocess.PIPE,
                           stderr=subprocess.DEVNULL)
        out = r.stdout.decode(errors="replace").strip()
        if r.returncode == 0 and out:
            return out
    except OSError:
        pass
    q = p.replace("\\", "/")
    if q.startswith("/mnt/") and len(q) > 6 and q[6] == "/":
        return q[5].upper() + ":" + q[6:].replace("/", "\\")
    return p


def _available(mode, binary):
    if mode == "native":
        return os.path.exists(binary)
    if mode == "winexe":
        return shutil.which("wslpath") is not None
    if mode == "wsl":
        return shutil.which("wsl.exe") is not None
    return False


class Tool(object):
    """One external program, plus the calling convention that was found to work."""

    def __init__(self, name, binary):
        self.name = name
        self.binary = binary
        self.mode = "none"

    def run(self, args, mode=None):
        """Run with `args`; a leading-dash argument is a flag, the rest are paths."""
        mode = mode or self.mode
        if mode == "none":
            raise RuntimeError("%s has no working calling convention" % self.name)
        conv = {"native": lambda a: a, "winexe": to_win, "wsl": to_wsl}[mode]
        argv = [a if a.startswith("-") else conv(a) for a in args]
        if mode == "wsl":
            line = " ".join("'%s'" % a for a in [to_wsl(self.binary)] + argv)
            cmd = ["wsl.exe", "-e", "bash", "-c", line]
        else:
            # In winexe mode only the ARGUMENTS are converted. The binary keeps the path
            # this interpreter can exec -- /mnt/c/... under WSL, which binfmt interop
            # hands to Windows. Converting it too gives Linux a "C:\..." string to
            # execve, which is not a path it has.
            cmd = [self.binary] + argv
        return subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    def probe(self, args_for, suffix=".out", out_dir=None):
        """Find the convention that works. `args_for(out_path)` gives the arguments of a
        call that must produce a non-empty `out_path`. Sets and returns `self.mode`,
        which is "none" when no convention worked.

        `out_dir` matters more than it looks: the probe file has to sit where *both*
        sides can reach it. A default temporary directory under WSL is on the Linux
        filesystem, which a Windows .exe sees only as a UNC path, so probing there
        reports a perfectly good translator as unusable. Pass a directory inside the
        repository, which is on the Windows drive and visible from both."""
        for mode in MODES:
            if not _available(mode, self.binary):
                continue
            if out_dir:
                os.makedirs(out_dir, exist_ok=True)
            fd, out = tempfile.mkstemp(suffix=suffix, prefix="probe.", dir=out_dir)
            os.close(fd)
            os.remove(out)
            try:
                self.run(args_for(out), mode=mode)
            except (OSError, RuntimeError):
                continue
            finally:
                ok = os.path.exists(out) and os.path.getsize(out) > 0
                if os.path.exists(out):
                    os.remove(out)
            if ok:
                self.mode = mode
                return mode
        self.mode = "none"
        return "none"

    def __repr__(self):
        return "<Tool %s %s (%s)>" % (self.name, self.binary, self.mode)

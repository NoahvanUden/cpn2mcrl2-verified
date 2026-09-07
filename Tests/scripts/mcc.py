#!/usr/bin/env python3
"""E6: how much of a PNML corpus falls inside the native expression language.

The measurement [`InputFormat.md`](../../Implementation/docs/InputFormat.md) §2.3 asks
for and nobody has made:

> How much of that corpus falls inside the expression language of §4 should be measured
> before M7 is scheduled rather than assumed.

Point it at a directory of PNML files -- the Model Checking Contest's coloured models,
or any other collection -- and it runs `Implementation/tools/pnml2cpn.py` over all of
them and reports what happened, bucketed by *why* each one was refused. The buckets are
the finding: "12% fits" is much less useful than knowing that the other 88% is three
constructs, one of which is cheap to add.

Nets that import are then optionally run through the full pipeline, so that a corpus
run is a test and not only a survey. That is off by default because the state spaces in
that corpus are far beyond anything `Corpus.md` calls tier 1.

`--survey` answers the more useful question. The importer stops at a file's *first*
problem, so a bucket count says which construct is hit first and not what a corpus
actually needs; the survey counts, over every coloured file, which PNML constructs
appear at all. "All 61 use cyclic enumerations" is an answer someone can act on.

Usage:
    python mcc.py <dir-of-pnml> [--survey] [--translate] [--limit N]
"""

import collections
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
TESTS = os.path.dirname(HERE)
ROOT = os.path.dirname(TESTS)
IMPORTER = os.path.join(ROOT, "Implementation", "tools", "pnml2cpn.py")
LEAN = os.path.join(ROOT, "Implementation", "Lean", ".lake", "build", "bin",
                    "cpn2mcrl2.exe")


def bucket(message):
    """The reason, reduced to a phrase that groups files usefully."""
    m = message.split(":", 2)[-1].strip()
    for pattern, name in [
        (r"net type .* is not a high-level net", "a place/transition net, not coloured"),
        (r"sort .* is a cyclic enumeration", "cyclic enumeration (successor)"),
        (r"<all>", "<all>, the whole-sort term"),
        (r"has no <hlinscription>", "uninscribed arc"),
        (r"useroperator .* is not an enumeration constant", "user-defined operator"),
        (r"declaration <.*> is not supported", "user-defined declaration"),
        (r"sort .* uses <(\w+)>", "sort outside the language"),
        (r"term <(\w+)> is not in InputFormat", "term outside the language"),
        (r"multiplicity of a <numberof>", "computed multiplicity"),
        (r"could belong to any of", "ambiguous tuple sort"),
        (r"not well-formed XML", "not well-formed XML"),
        (r"no <declaration>", "no declarations block"),
        (r"has no <structure>", "unstructured (tool-specific) terms"),
    ]:
        if re.search(pattern, m):
            return name
    return m[:60]


# The PNML constructs worth counting: what the native language has, and what it lacks.
SURVEY = [
    ("cyclicenumeration", "cyclic enumeration (successor/predecessor)", False),
    ("finiteintrange", "finite integer range", False),
    ("dotconstant", "the dot sort (a black token)", False),
    ("<all", "<all>, one token of every colour", False),
    ("namedoperator", "user-defined operator", False),
    ("partition", "sort partition", False),
    ("successor", "successor", False),
    ("predecessor", "predecessor", False),
    ("finiteenumeration", "finite enumeration", True),
    ("productsort", "product sort", True),
    ("tuple", "tuple", True),
]


def is_coloured(path):
    """A high-level net: symmetric nets or HLPNG, not the P/T type."""
    try:
        head = open(path, encoding="utf-8", errors="replace").read(4000)
    except OSError:
        return False
    return "symmetricnet" in head or "highlevelnet" in head or "HLPNG" in head


def survey(files):
    """Which constructs appear at all, over every file. See the module docstring."""
    counts = collections.Counter()
    for f in files:
        try:
            text = open(f, encoding="utf-8", errors="replace").read()
        except OSError:
            continue
        for tag, _, _ in SURVEY:
            probe = tag if tag.startswith("<") else "<" + tag
            if probe in text:
                counts[tag] += 1
    print("")
    print("what the %d files use:" % len(files))
    # Zero rows are printed too: that no coloured model uses <finiteenumeration>, the
    # one sort the language does have, is the more useful half of the measurement.
    for tag, label, supported in SURVEY:
        print("  %4d  %-42s %s" % (counts[tag], label,
                                   "supported" if supported else "NOT in 4.1"))


def main(argv):
    args = [a for a in argv[1:] if not a.startswith("--")]
    translate = "--translate" in argv
    limit = None
    for a in argv[1:]:
        if a.startswith("--limit="):
            limit = int(a.split("=")[1])
    if not args:
        print(__doc__.strip())
        return 2

    root = args[0]
    files = []
    for dirpath, _, names in os.walk(root):
        for n in sorted(names):
            if n.endswith(".pnml"):
                files.append(os.path.join(dirpath, n))
    files.sort()
    if limit:
        files = files[:limit]
    if not files:
        sys.stderr.write("no .pnml files under %s\n" % root)
        return 2

    ok, refused, malformed = [], collections.Counter(), collections.Counter()
    out_dir = os.path.join(TESTS, "out", "mcc")
    os.makedirs(out_dir, exist_ok=True)

    for i, f in enumerate(files):
        dst = os.path.join(out_dir, "%04d.cpn.json" % i)
        r = subprocess.run([sys.executable, IMPORTER, f, dst],
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        msg = r.stderr.decode(errors="replace").strip()
        if r.returncode == 0:
            ok.append((f, dst))
        elif r.returncode == 3:
            refused[bucket(msg)] += 1
        else:
            malformed[bucket(msg)] += 1

    total = len(files)
    print("%d PNML files under %s" % (total, root))
    print("  %d imported (%.1f%%)" % (len(ok), 100.0 * len(ok) / total))
    print("  %d outside the expression language" % sum(refused.values()))
    for reason, n in refused.most_common():
        print("      %4d  %s" % (n, reason))
    if malformed:
        print("  %d not the PNML this reads" % sum(malformed.values()))
        for reason, n in malformed.most_common():
            print("      %4d  %s" % (n, reason))

    if "--survey" in argv:
        survey([f for f in files if is_coloured(f)])

    if translate and ok:
        print("\ntranslating the %d that imported:" % len(ok))
        good = 0
        for f, dst in ok:
            target = dst.replace(".cpn.json", ".mcrl2")
            subprocess.run([LEAN, dst, target], stdout=subprocess.DEVNULL,
                           stderr=subprocess.DEVNULL)
            if os.path.exists(target):
                good += 1
            else:
                print("  T1 refused %s" % os.path.basename(f))
        print("  %d of %d passed the T1 validation" % (good, len(ok)))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))

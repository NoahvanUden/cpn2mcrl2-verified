#!/usr/bin/env python3
"""E5: random nets within InputFormat.md 4.1, checked against the oracle, then shrunk.

Hand-written fixtures test what their author thought of. This does not, which is where
an external oracle earns its cost -- every net here is one nobody designed, and the
oracle has no idea what it was supposed to do.

The four legs of `Tests/docs/Plan.md` 6 are applied to each generated net:

    A   the three translators emit byte-identical text
    B   the emitted LTS is bisimilar to the oracle's
    B2  and on the bag encoding, identical marking by marking
    C   the two encodings are bisimilar to each other

A net that fails any of them is shrunk -- transitions dropped, places dropped, tokens
removed, guards weakened -- for as long as the failure survives, and the minimal net is
written to `corpus/fuzz/` so that it becomes a permanent fixture. That is the point of
the shrinker: a random failure nobody can read is not a finding until it is small.

Generation stays inside two rules from `Corpus.md` 1, which is what keeps the state
space finite without a cap doing the work:

  * colours are `Bool` and enumerations only;
  * every transition produces exactly as many tokens as it consumes, so no marking can
    grow without bound.

And one rule from `Oracle.md` 3.2: every variable a transition uses is bound by one of
its in-arcs. SNAKES binds variables by matching tokens, where Definition 6 quantifies
over all bindings, and the two agree only on that fragment -- so a net outside it would
be measuring the divergence rather than the translation.

Usage:
    python fuzz.py [--runs N] [--seed N] [--keep]
"""

import json
import os
import random
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
TESTS = os.path.dirname(HERE)
ROOT = os.path.dirname(TESTS)
OUT = os.path.join(TESTS, "out", "fuzz")

# The two enumerations are given DISJOINT constructor names. Sharing one is a real
# defect -- corpus/known-failing/shared-ctor.cpn.json, Findings.md 8 -- and until it is
# decided, generating it again at a quarter of all seeds would drown out everything
# else the search might turn up.
COLORS = {
    "Bool": {"kind": "bool"},
    "C2": {"kind": "enum", "ids": ["a", "b"]},
    "C3": {"kind": "enum", "ids": ["c", "d", "e"]},
}
VARS = {"Bool": "vq", "C2": "vh", "C3": "vg"}


def mcrl2_bin():
    for cand in ["/c/Program Files/mCRL2/bin", "C:\\Program Files\\mCRL2\\bin",
                 "/usr/local/bin", "/opt/mcrl2/bin"]:
        if os.path.exists(os.path.join(cand, "mcrl22lps.exe")) or \
           os.path.exists(os.path.join(cand, "mcrl22lps")):
            return cand
    p = shutil.which("mcrl22lps")
    return os.path.dirname(p) if p else None


MCRL2 = mcrl2_bin()
VENV = os.path.join(TESTS, ".venv", "Scripts", "python.exe")
if not os.path.exists(VENV):
    VENV = os.path.join(TESTS, ".venv", "bin", "python")
if not os.path.exists(VENV):
    VENV = sys.executable

TRANSLATORS = {
    "lean": [os.path.join(ROOT, "Implementation", "Lean", ".lake", "build", "bin",
                          "cpn2mcrl2.exe")],
    "dafny": [os.path.join(ROOT, "Implementation", "Dafny", "cpn2mcrl2.exe")],
}
_ocaml = os.path.join(ROOT, "Implementation", "OCaml", "_build", "default", "bin",
                      "main.exe")


def wslpath(p):
    p = p.replace("\\", "/")
    if len(p) > 1 and p[1] == ":":
        p = "/mnt/" + p[0].lower() + p[2:]
    return p


def ocaml_available():
    if not os.path.exists(_ocaml):
        return False
    try:
        subprocess.run(["wsl.exe", "-e", "bash", "-c",
                        "test -x '%s'" % wslpath(_ocaml)], check=True,
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        return True
    except Exception:
        return False


OCAML = ocaml_available()


# ------------------------------------------------------------------ generation

def gen(rng):
    """A random net that is finite, bounded, and inside the SNAKES fragment."""
    used = rng.sample(list(COLORS), rng.randint(1, 2))
    colors = {c: COLORS[c] for c in used}
    colors["Bool"] = COLORS["Bool"]          # guards need it declared
    variables = {VARS[c]: c for c in used}

    n_places = rng.randint(1, 3)
    places = {}
    for i in range(n_places):
        c = rng.choice(used)
        toks = [const(rng, colors, c) for _ in range(rng.randint(0, 2))]
        places["p%d" % i] = {
            "color": c,
            "init": ["bag", [[1, t] for t in toks]] if toks else ["emptyBag"],
        }

    transitions, in_arcs, out_arcs = {}, [], []
    for j in range(rng.randint(1, 3)):
        name = "t%d" % j
        sources = rng.sample(list(places), rng.randint(1, min(2, len(places))))
        bound = {}
        for p in sources:
            c = places[p]["color"]
            v = VARS[c]
            bound[v] = c
            in_arcs.append({"place": p, "transition": name,
                            "expr": ["bag", [[1, ["var", v]]]]})
        # Token-conserving: one token produced per token consumed, so no marking can
        # grow without bound. Tokens going to the same place are merged into one arc
        # carrying a bag of several items -- Definition 4 allows at most one arc per
        # place-transition pair, and two arcs between the same two nodes are refused by
        # the T1 validation.
        produced = {}
        for _ in sources:
            p = rng.choice(list(places))
            c = places[p]["color"]
            if VARS[c] in bound:
                e = rng.choice([["var", VARS[c]], const(rng, colors, c)])
            else:
                e = const(rng, colors, c)
            produced.setdefault(p, []).append(e)
        for p, items in produced.items():
            out_arcs.append({"transition": name, "place": p,
                             "expr": ["bag", [[1, e] for e in items]]})
        transitions[name] = {"guard": guard(rng, colors, bound)}

    return {"colors": colors, "variables": variables, "places": places,
            "transitions": transitions, "inArcs": in_arcs, "outArcs": out_arcs}


def const(rng, colors, c):
    if colors[c]["kind"] == "bool":
        return ["bool", rng.choice([True, False])]
    return ["ctor", rng.choice(colors[c]["ids"])]


def guard(rng, colors, bound):
    if not bound or rng.random() < 0.4:
        return ["bool", True]
    v = rng.choice(list(bound))
    c = bound[v]
    eq = ["=", ["var", v], const(rng, colors, c)]
    r = rng.random()
    if r < 0.45:
        return eq
    if r < 0.65:
        return ["!", eq]
    other = ["=", ["var", v], const(rng, colors, c)]
    return [rng.choice(["&&", "||"]), eq, other]


# --------------------------------------------------------------------- running

def run(cmd, **kw):
    return subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, **kw)


def translate(which, flag, src, dst):
    if os.path.exists(dst):
        os.remove(dst)
    if which == "ocaml":
        args = [wslpath(_ocaml)] + ([flag] if flag else []) + \
               [wslpath(src), wslpath(dst)]
        run(["wsl.exe", "-e", "bash", "-c", " ".join("'%s'" % a for a in args)])
    else:
        run(TRANSLATORS[which] + ([flag] if flag else []) + [src, dst])
    return os.path.exists(dst)


def bisim(a, b):
    r = run([os.path.join(MCRL2, "ltscompare"), "-ebisim", a, b])
    return r.stdout.decode(errors="replace").strip().splitlines()[-1:] == ["true"]


def check(net, tag):
    """Apply the four legs. Returns None when the net passes, else a reason."""
    os.makedirs(OUT, exist_ok=True)
    src = os.path.join(OUT, tag + ".cpn.json")
    with open(src, "w", encoding="utf-8", newline="\n") as f:
        f.write(json.dumps(net, indent=2) + "\n")

    names = ["lean", "dafny"] + (["ocaml"] if OCAML else [])
    auts = {}
    for flag, sfx in [("", ""), ("--list", ".list")]:
        texts = {}
        for w in names:
            dst = os.path.join(OUT, "%s%s.%s.mcrl2" % (tag, sfx, w))
            if not translate(w, flag, src, dst):
                return "leg A: %s emitted nothing%s" % (w, sfx)
            texts[w] = open(dst, "rb").read()
        first = texts[names[0]]
        for w in names[1:]:
            if texts[w] != first:
                return "leg A: %s and %s disagree%s" % (names[0], w, sfx)

        mcrl2 = os.path.join(OUT, "%s%s.mcrl2" % (tag, sfx))
        with open(mcrl2, "wb") as f:
            f.write(first)
        lps = os.path.join(OUT, "%s%s.lps" % (tag, sfx))
        if run([os.path.join(MCRL2, "mcrl22lps"), "-q", mcrl2, lps]).returncode:
            return "T0: mcrl22lps rejected the emitted text%s" % sfx
        aut = os.path.join(OUT, "%s%s.aut" % (tag, sfx))
        if run([os.path.join(MCRL2, "lps2lts"), "-q", lps, aut]).returncode:
            return "lps2lts failed%s" % sfx
        auts[sfx] = aut
        if sfx == "":
            nc = os.path.join(OUT, "%s.nc.lps" % tag)
            run([os.path.join(MCRL2, "mcrl22lps"), "-q", "--no-constelm", mcrl2, nc])
            run([os.path.join(MCRL2, "lps2lts"), "-q", "-ofsm", nc,
                 os.path.join(OUT, "%s.fsm" % tag)])

    if not bisim(auts[""], auts[".list"]):
        return "leg C: the two encodings are not bisimilar"

    r = run([VENV, os.path.join(TESTS, "oracle", "run.py"), src,
             os.path.join(OUT, tag)])
    if r.returncode == 2:
        return None            # the oracle cannot express it; not a verdict
    if r.returncode == 3:
        return None            # over the cap; not a verdict
    if r.returncode:
        return "the oracle adapter failed: %s" % r.stderr.decode(errors="replace").strip()

    oracle = os.path.join(OUT, tag + ".oracle.aut")
    for sfx in ("", ".list"):
        if not bisim(oracle, auts[sfx]):
            return "leg B%s: not bisimilar to the oracle" % sfx

    fsm = os.path.join(OUT, "%s.fsm" % tag)
    if os.path.exists(fsm):
        r = run([sys.executable, os.path.join(HERE, "markings.py"), fsm,
                 os.path.join(OUT, tag + ".oracle.markings"), oracle])
        if r.returncode:
            return "leg B2: markings differ\n%s" % r.stderr.decode(errors="replace")
    return None


# -------------------------------------------------------------------- shrinking

def shrink(net, reason, tag):
    """Smallest net still failing the same way. A failure nobody can read is not yet
    a finding."""
    best = net
    changed = True
    while changed:
        changed = False
        for cand in candidates(best):
            r = check(cand, tag + ".shrink")
            if r is not None and r.split(":")[0] == reason.split(":")[0]:
                best, changed = cand, True
                break
    return best


def candidates(net):
    import copy
    # Drop a transition.
    for t in list(net["transitions"]):
        c = copy.deepcopy(net)
        del c["transitions"][t]
        c["inArcs"] = [a for a in c["inArcs"] if a["transition"] != t]
        c["outArcs"] = [a for a in c["outArcs"] if a["transition"] != t]
        if c["transitions"]:
            yield c
    # Drop a place, and every arc touching it.
    for p in list(net["places"]):
        c = copy.deepcopy(net)
        del c["places"][p]
        c["inArcs"] = [a for a in c["inArcs"] if a["place"] != p]
        c["outArcs"] = [a for a in c["outArcs"] if a["place"] != p]
        if c["places"] and c["inArcs"]:
            yield c
    # Drop a token from an initial marking.
    for p, decl in net["places"].items():
        if decl["init"][0] == "bag" and decl["init"][1]:
            c = copy.deepcopy(net)
            items = c["places"][p]["init"][1][:-1]
            c["places"][p]["init"] = ["bag", items] if items else ["emptyBag"]
            yield c
    # Weaken a guard.
    for t, decl in net["transitions"].items():
        if decl["guard"] != ["bool", True]:
            c = copy.deepcopy(net)
            c["transitions"][t]["guard"] = ["bool", True]
            yield c


# ------------------------------------------------------------------------ main

def main(argv):
    runs, seed, keep = 200, 0, False
    for a in argv[1:]:
        if a.startswith("--runs="):
            runs = int(a.split("=")[1])
        elif a.startswith("--seed="):
            seed = int(a.split("=")[1])
        elif a == "--keep":
            keep = True
        elif a in ("-h", "--help"):
            print(__doc__.strip())
            return 0
    if MCRL2 is None:
        sys.stderr.write("mcrl22lps not found\n")
        return 2

    os.makedirs(OUT, exist_ok=True)
    failures = 0
    for i in range(runs):
        rng = random.Random(seed + i)
        net = gen(rng)
        tag = "fuzz%05d" % (seed + i)
        reason = check(net, tag)
        if reason is None:
            if not keep:
                for f in os.listdir(OUT):
                    if f.startswith(tag):
                        try:
                            os.remove(os.path.join(OUT, f))
                        except OSError:
                            pass
            continue
        failures += 1
        sys.stdout.write("seed %d FAILED: %s\n" % (seed + i, reason))
        small = shrink(net, reason, tag)
        dest = os.path.join(TESTS, "corpus", "fuzz")
        os.makedirs(dest, exist_ok=True)
        path = os.path.join(dest, "%s.cpn.json" % tag)
        small["_comment"] = [
            "Found by scripts/fuzz.py at seed %d, and shrunk." % (seed + i),
            "The failure was: %s" % reason.splitlines()[0],
        ]
        with open(path, "w", encoding="utf-8", newline="\n") as f:
            f.write(json.dumps(small, indent=2) + "\n")
        sys.stdout.write("  shrunk to %s\n" % path)

    sys.stdout.write("%d nets, %d failure(s)%s\n"
                     % (runs, failures, "" if OCAML else "  (OCaml not runnable)"))
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))

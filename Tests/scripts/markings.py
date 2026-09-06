#!/usr/bin/env python3
"""Leg B2: compare the emitted LTS to the oracle's, marking by marking.

`ltscompare -ebisim` answers a weaker question than the bag encoding can support. Its
process parameters *are* the marking, so the correspondence with the oracle's marking
graph ought to be an isomorphism -- and `ltscompare` has no isomorphism equivalence.

This recovers it. `lps2lts -ofsm` writes each state's parameter values, so every state
on the mCRL2 side carries the marking it stands for, and the oracle writes the same
thing in `<net>.oracle.markings`. Identifying states by their markings turns both
graphs into sets of

    (marking, transition name, marking)

triples, and two graphs are the same graph exactly when those sets agree and the
initial markings agree. That is strictly sharper than bisimilarity, and it is what
recovers most of the binding-blindness of `Tests/docs/Plan.md` 2.1: a transition fired
under the wrong binding lands in the wrong marking.

Only meaningful for the bag encoding. Under the list encoding a marking is a
*representative*, several states share one marking, and bisimilarity is the right and
only question -- so the harness does not run this there.

Usage:
    python markings.py <net.fsm> <net.oracle.markings> <net.oracle.aut>
"""

import re
import sys


# ------------------------------------------------------------------ mCRL2 side

def split_top(s, sep=","):
    """Split on `sep` at bracket depth zero, so that a record's own commas survive."""
    out, depth, cur = [], 0, ""
    for ch in s:
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        if ch == sep and depth == 0:
            out.append(cur)
            cur = ""
        else:
            cur += ch
    if cur.strip():
        out.append(cur)
    return [x.strip() for x in out]


def canon_bag(text):
    """mCRL2's `{a: 1, b: 1}` in the oracle's canonical form `{a^1,b^1}`."""
    text = text.strip()
    if text.startswith('"') and text.endswith('"'):
        text = text[1:-1]
    if not (text.startswith("{") and text.endswith("}")):
        raise ValueError("not a bag: %r" % text)
    body = text[1:-1].strip()
    if body in ("", ":"):
        return "{}"
    items = []
    for item in split_top(body):
        # "value: count", where the value may itself contain a colon inside brackets.
        idx = None
        depth = 0
        for i, ch in enumerate(item):
            if ch in "([{":
                depth += 1
            elif ch in ")]}":
                depth -= 1
            elif ch == ":" and depth == 0:
                idx = i
        if idx is None:
            raise ValueError("bag item without a count: %r" % item)
        value = item[:idx].strip()
        count = int(item[idx + 1:].strip())
        items.append("%s^%d" % (canon_value(value), count))
    return "{" + ",".join(sorted(items)) + "}"


def canon_value(v):
    """A colour value in the form the oracle writes.

    Records are the one place the two sides disagree textually: mCRL2 prints a struct
    as `Job(1, fresh)` and the oracle prints the tuple `(1,fresh)`, so the constructor
    name is dropped and the spacing normalised. That is more than sorting, and it is
    the only semantic-looking step in this file -- see `Oracle.md` 2.3.
    """
    v = v.strip()
    m = re.match(r"^([A-Za-z_][A-Za-z0-9_']*)\((.*)\)$", v)
    if m:
        inner = ",".join(canon_value(x) for x in split_top(m.group(2)))
        return "(" + inner + ")"
    if v.startswith("(") and v.endswith(")"):
        inner = ",".join(canon_value(x) for x in split_top(v[1:-1]))
        return "(" + inner + ")"
    return v


def read_fsm(path):
    """(markings by state, edges, initial state) from an mCRL2 .fsm file."""
    with open(path, encoding="utf-8") as f:
        text = f.read().replace("\r\n", "\n")
    # The three sections are separated by a line of exactly ---, and the first of them
    # is empty when the process has had its parameters eliminated.
    parts = re.split(r"^---$", text, flags=re.M)
    if len(parts) < 3:
        raise ValueError("%s is not an .fsm file with three sections" % path)
    params, states_txt, trans_txt = parts[0], parts[1], parts[2]
    if not params.strip():
        raise ValueError(
            "%s has no process parameters, so it carries no markings to compare; "
            "linearize with --no-constelm" % path)

    names, values = [], []
    for line in params.strip().splitlines():
        line = line.strip()
        if not line:
            continue
        m = re.match(r'^(\S+?)\((\d+)\)\s+(\S+)\s+(.*)$', line)
        if not m:
            raise ValueError("cannot read parameter line %r" % line)
        names.append(m.group(1))
        values.append(re.findall(r'"([^"]*)"', m.group(4)))

    markings = []
    for line in states_txt.strip().splitlines():
        line = line.strip()
        if not line:
            continue
        idxs = [int(x) for x in line.split()]
        cells = []
        for pname, vs, i in zip(names, values, idxs):
            cells.append("%s=%s" % (place_of(pname), canon_bag(vs[i])))
        markings.append(" ".join(cells))

    edges = []
    for line in trans_txt.strip().splitlines():
        line = line.strip()
        if not line:
            continue
        m = re.match(r'^(\d+)\s+(\d+)\s+"(.*)"$', line)
        if not m:
            raise ValueError("cannot read transition line %r" % line)
        # .fsm numbers states from 1, in the order they were listed above.
        edges.append((int(m.group(1)) - 1, m.group(3), int(m.group(2)) - 1))
    return markings, edges, 0


def place_of(param):
    """`p1_Spec` is the parameter Definition 14 names for the place `p1`."""
    return param[:-5] if param.endswith("_Spec") else param


# ----------------------------------------------------------------- oracle side

def read_oracle(markings_path, aut_path):
    markings = {}
    with open(markings_path, encoding="utf-8") as f:
        for line in f:
            line = line.rstrip("\n")
            if not line.strip():
                continue
            num, rest = line.split(None, 1)
            markings[int(num)] = normalise_oracle_marking(rest)
    edges = []
    init = 0
    with open(aut_path, encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if line.startswith("des"):
                init = int(line[line.index("(") + 1:].split(",")[0])
                continue
            m = re.match(r'^\((\d+),"(.*)",(\d+)\)$', line)
            if m:
                edges.append((int(m.group(1)), m.group(2), int(m.group(3))))
    return markings, edges, init


def normalise_oracle_marking(text):
    """Sort the oracle's own line, so neither side depends on emission order.

    The split has to respect brackets: a record value is written `(a,fresh)`, and
    splitting its bag on every comma turns two tokens into three nonsense ones.
    """
    cells = []
    for cell in text.split():
        place, bag = cell.split("=", 1)
        body = bag[1:-1]
        items = [x for x in split_top(body) if x]
        cells.append("%s={%s}" % (place, ",".join(sorted(items))))
    return " ".join(sorted(cells))


def normalise_fsm_marking(text):
    cells = []
    for cell in text.split():
        cells.append(cell)
    return " ".join(sorted(cells))


# ------------------------------------------------------------------- compare

def compare(fsm_path, markings_path, aut_path):
    fm, fe, fi = read_fsm(fsm_path)
    om, oe, oi = read_oracle(markings_path, aut_path)

    fm = [normalise_fsm_marking(m) for m in fm]
    f_edges = set((fm[s], l, fm[t]) for (s, l, t) in fe)
    o_edges = set((om[s], l, om[t]) for (s, l, t) in oe)
    f_states, o_states = set(fm), set(om.values())

    problems = []
    if fm[fi] != om[oi]:
        problems.append("initial marking: emitted %s, oracle %s" % (fm[fi], om[oi]))
    for extra in sorted(f_states - o_states):
        problems.append("marking reachable in the emitted LTS only: %s" % extra)
    for extra in sorted(o_states - f_states):
        problems.append("marking reachable in the oracle only: %s" % extra)
    for extra in sorted(f_edges - o_edges):
        problems.append("edge in the emitted LTS only: %s --%s--> %s" % extra)
    for extra in sorted(o_edges - f_edges):
        problems.append("edge in the oracle only: %s --%s--> %s" % extra)
    return len(f_states), len(f_edges), problems


def main(argv):
    if len(argv) != 4:
        print(__doc__.strip())
        return 2
    try:
        states, edges, problems = compare(argv[1], argv[2], argv[3])
    except Exception as e:
        sys.stderr.write("%s: %s\n" % (type(e).__name__, e))
        return 2
    if problems:
        for p in problems[:12]:
            sys.stderr.write("  %s\n" % p)
        if len(problems) > 12:
            sys.stderr.write("  ... and %d more\n" % (len(problems) - 12))
        return 1
    sys.stdout.write("%d markings, %d edges, identical\n" % (states, edges))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))

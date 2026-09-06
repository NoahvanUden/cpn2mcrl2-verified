#!/usr/bin/env python3
"""The oracle: a reachability graph for a net, computed outside this project.

The only entry point the harness calls, and the only file that knows an adapter exists
(``Tests/docs/Oracle.md`` section 5). Adding a candidate oracle is a new module in
``adapters/`` and a line in ``ADAPTERS`` below; it touches no test, no corpus file, and
no document but ``Oracle.md``.

Writes the two files of ``Oracle.md`` section 2:

    <prefix>.oracle.aut       the LTS, edges labelled with bare transition names
    <prefix>.oracle.markings  state number -> canonical marking

Exit status, per ``Oracle.md`` section 2.4:

    0  ok
    2  unsupported construct   (not a failure; recorded and counted)
    3  state cap exceeded      (not a verdict)
    1  the adapter itself failed

Usage:
    python run.py <net.cpn.json> <out-prefix> [--adapter NAME] [--cap N]
"""

import importlib
import json
import os
import sys

ADAPTERS = {
    "snakes": "adapters.snakes_adapter",
}

DEFAULT_CAP = 5000


def load(name):
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    return importlib.import_module(ADAPTERS[name])


def write_aut(path, states, edges):
    """Aldebaran format, per Oracle.md 2.2: state 0 is the initial marking."""
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        f.write("des (0,%d,%d)\n" % (len(edges), states))
        for (s, label, t) in edges:
            f.write('(%d,"%s",%d)\n' % (s, label, t))


def write_markings(path, markings):
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        for s in sorted(markings):
            f.write("%d  %s\n" % (s, markings[s]))


def main(argv):
    args = [a for a in argv[1:] if not a.startswith("--")]
    opts = [a for a in argv[1:] if a.startswith("--")]
    if len(args) < 2:
        print(__doc__.strip())
        return 1

    name = "snakes"
    cap = DEFAULT_CAP
    for o in opts:
        if o.startswith("--adapter="):
            name = o.split("=", 1)[1]
        elif o.startswith("--cap="):
            cap = int(o.split("=", 1)[1])
        elif o in ("-h", "--help"):
            print(__doc__.strip())
            return 1
    if name not in ADAPTERS:
        sys.stderr.write("unknown adapter %r; known: %s\n"
                         % (name, ", ".join(sorted(ADAPTERS))))
        return 1

    net_path, prefix = args[0], args[1]
    with open(net_path, encoding="utf-8") as f:
        net = json.load(f)
    net.pop("_comment", None)

    try:
        adapter = load(name)
    except ImportError as e:
        sys.stderr.write("oracle unavailable: %s\n" % e)
        return 1

    try:
        states, edges, markings = adapter.explore(net, cap)
    except adapter.CapExceeded as e:
        sys.stderr.write("%s: state cap exceeded: %s\n" % (net_path, e))
        return 3
    except adapter.Unsupported as e:
        sys.stderr.write("%s: the oracle cannot express this net: %s\n" % (net_path, e))
        return 2
    except Exception as e:  # the adapter itself broke
        sys.stderr.write("%s: %s failed: %s: %s\n"
                         % (net_path, name, type(e).__name__, e))
        return 1

    write_aut(prefix + ".oracle.aut", states, edges)
    write_markings(prefix + ".oracle.markings", markings)
    sys.stderr.write("%s: %d states, %d edges (%s)\n"
                     % (os.path.basename(net_path), states, len(edges),
                        adapter.describe()))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))

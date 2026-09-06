"""The SNAKES adapter.

Satisfies the contract of ``Tests/docs/Oracle.md`` section 2. Given a net in the native
JSON of ``InputFormat.md`` section 4, it builds the corresponding SNAKES net and asks
SNAKES for its state graph.

**The one rule this file exists to obey** (``Oracle.md`` section 1): it builds places,
transitions and arcs, and it never computes enabling, binding or firing. Everything
about *behaviour* comes from SNAKES. If that line is ever crossed, the oracle becomes a
mirror and the comparison stops meaning anything while continuing to pass.

Colours are represented as ordinary Python values, which is what SNAKES tokens are:

    Bool   -> bool
    Int    -> int
    enum   -> str, the constructor's own name
    record -> tuple, in field order

Enumeration constants are plain strings rather than a wrapper class, because SNAKES
evaluates arc and guard expressions in its own namespace: a wrapper would have to be
injected into that namespace, and the copy SNAKES built would not be the copy this
module compares against. `InputFormat.md` 4.1 has no string colour, so a bare `str`
is unambiguous.
"""

import snakes.nets as sn


class Unsupported(Exception):
    """A net this adapter cannot hand to SNAKES faithfully."""


# --------------------------------------------------------------- expressions

class Compiler:
    """Renders a native expression as Python source for SNAKES.

    This is a syntactic translation and nothing more. It never evaluates anything, and
    it never decides whether a transition is enabled.
    """

    def __init__(self, net):
        self.colors = net["colors"]
        self.variables = net["variables"]
        self.ctor_owner = {}
        self.field_index = {}
        for cname, decl in self.colors.items():
            if decl.get("kind") == "enum":
                for i in decl["ids"]:
                    self.ctor_owner[i] = cname
            elif decl.get("kind") == "record":
                self.field_index[cname] = [f[0] for f in decl["fields"]]

    def is_var(self, e):
        return isinstance(e, list) and e and e[0] == "var"

    def source(self, e):
        """Python source for a colour-valued expression."""
        if not isinstance(e, list) or not e:
            raise Unsupported("malformed expression %r" % (e,))
        op = e[0]
        if op == "var":
            return e[1]
        if op == "int":
            return repr(int(e[1]))
        if op == "bool":
            return "True" if e[1] else "False"
        if op == "ctor":
            return repr(str(e[1]))
        if op == "rec":
            fields = dict((f[0], f[1]) for f in e[2])
            order = self.field_index.get(e[1])
            if order is None:
                raise Unsupported("record literal for the unknown colour %r" % e[1])
            missing = [f for f in order if f not in fields]
            if missing:
                raise Unsupported("record literal for %s is missing %s"
                                  % (e[1], ", ".join(missing)))
            return "(" + "".join("%s, " % self.source(fields[f]) for f in order) + ")"
        if op == "proj":
            base, field = e[1], e[2]
            cname = self._record_color_of(base)
            idx = self.field_index[cname].index(field)
            return "(%s)[%d]" % (self.source(base), idx)
        if op in ("+", "-", "*"):
            return "(%s %s %s)" % (self.source(e[1]), op, self.source(e[2]))
        if op in ("<", "<="):
            return "(%s %s %s)" % (self.source(e[1]), op, self.source(e[2]))
        if op == "=":
            return "(%s == %s)" % (self.source(e[1]), self.source(e[2]))
        if op == "&&":
            return "(%s and %s)" % (self.source(e[1]), self.source(e[2]))
        if op == "||":
            return "(%s or %s)" % (self.source(e[1]), self.source(e[2]))
        if op == "!":
            return "(not %s)" % self.source(e[1])
        raise Unsupported("operator %r is not in InputFormat.md 4.1" % op)

    def _record_color_of(self, e):
        """The record colour a projection is taken out of.

        Recurses through projections, so that a record field which is itself a record
        can be projected twice -- `InputFormat.md` 4.1 allows a record field to name any
        colour, records included.
        """
        c = self._color_of(e)
        if c not in self.field_index:
            raise Unsupported("projection out of %r, which is not a record colour" % c)
        return c

    def _color_of(self, e):
        """The declared colour of a colour-valued expression."""
        if self.is_var(e):
            return self.variables[e[1]]
        if not isinstance(e, list) or not e:
            raise Unsupported("malformed expression %r" % (e,))
        if e[0] == "rec":
            return e[1]
        if e[0] == "proj":
            base = self._color_of(e[1])
            for fname, fcolor in self.colors[base]["fields"]:
                if fname == e[2]:
                    return fcolor
            raise Unsupported("the record %s has no field %s" % (base, e[2]))
        if e[0] == "ctor":
            return self.ctor_owner[e[1]]
        raise Unsupported("cannot determine the colour of %r" % (e[0],))

    def term(self, e):
        """One token's worth of arc inscription, as a SNAKES annotation."""
        if self.is_var(e):
            return sn.Variable(e[1])
        src = self.source(e)
        if self._closed(e):
            return sn.Value(eval(src, {}, {}))
        return sn.Expression(src)

    def _closed(self, e):
        if not isinstance(e, list) or not e:
            return True
        if e[0] == "var":
            return False
        if e[0] == "rec":
            return all(self._closed(f[1]) for f in e[2])
        return all(self._closed(x) for x in e[1:] if isinstance(x, list))

    def bag_terms(self, e):
        """The multiset an arc inscription or initial marking denotes, as a list."""
        if not isinstance(e, list) or not e:
            raise Unsupported("malformed bag %r" % (e,))
        if e[0] == "emptyBag":
            return []
        if e[0] == "bag":
            out = []
            for count, item in e[1]:
                out.extend([item] * int(count))
            return out
        raise Unsupported("bag expression %r is not in InputFormat.md 4.1" % e[0])

    def tokens(self, e):
        """A closed bag, as concrete token values, for an initial marking."""
        vals = []
        for item in self.bag_terms(e):
            if not self._closed(item):
                raise Unsupported(
                    "an initial marking contains the free variable(s) of %r; "
                    "InputFormat.md 4.3 check 6 requires I(p) to be closed" % (item,)
                )
            vals.append(eval(self.source(item), {}, {}))
        return vals


# ----------------------------------------------------------------- the net

def build(net):
    """The SNAKES net for a native CPN. Structure only."""
    c = Compiler(net)
    n = sn.PetriNet("net")

    place_order = list(net["places"].keys())
    for pname in place_order:
        n.add_place(sn.Place(pname, c.tokens(net["places"][pname]["init"])))

    for tname, t in net["transitions"].items():
        guard = t.get("guard", ["bool", True])
        if guard == ["bool", True]:
            n.add_transition(sn.Transition(tname))
        else:
            n.add_transition(sn.Transition(tname, sn.Expression(c.source(guard))))

    for a in net["inArcs"]:
        n.add_input(a["place"], a["transition"], _annotation(c, a["expr"]))
    for a in net["outArcs"]:
        n.add_output(a["place"], a["transition"], _annotation(c, a["expr"]))

    return n, place_order


def _annotation(c, expr):
    terms = [c.term(e) for e in c.bag_terms(expr)]
    if not terms:
        raise Unsupported(
            "an arc with the empty bag has no SNAKES annotation; Definition 5 allows "
            "it, and SNAKES has no way to say 'consume nothing from this place'"
        )
    if len(terms) == 1:
        return terms[0]
    return sn.MultiArc(terms)


# --------------------------------------------------------------- exploration

def explore(net, cap):
    """The reachability graph, as (states, edges, markings).

    ``edges`` are ``(source, transition name, target)`` with the binding erased, per
    ``Oracle.md`` section 2.2. ``markings`` maps a state number to a canonical marking.
    """
    n, place_order = build(net)
    g = sn.StateGraph(n)
    g.build()

    if len(g) > cap:
        raise CapExceeded(len(g))

    edges = []
    markings = {}
    for s in g:
        g.goto(s)
        markings[s] = canonical_marking(g.net.get_marking(), place_order)
        for (target, trans, _binding) in g.successors():
            edges.append((s, trans.name, target))
    return len(g), edges, markings


class CapExceeded(Exception):
    def __init__(self, count):
        Exception.__init__(self, "state graph has at least %d states" % count)
        self.count = count


def canonical_marking(marking, place_order):
    """One marking, in the canonical form Oracle.md 2.3 fixes.

    Sorted by place, then by rendered value, so that the same bag always produces the
    same line whatever order SNAKES happened to build it in.
    """
    out = []
    for p in place_order:
        try:
            tokens = list(marking(p))
        except Exception:
            tokens = []
        counts = {}
        for tok in tokens:
            counts[render(tok)] = counts.get(render(tok), 0) + 1
        items = ",".join("%s^%d" % (v, counts[v]) for v in sorted(counts))
        out.append("%s={%s}" % (p, items))
    return " ".join(out)


def render(v):
    """A colour value as canonical text, matching the mCRL2 side's normal form."""
    if isinstance(v, bool):
        return "true" if v else "false"
    if isinstance(v, int):
        return str(v)
    if isinstance(v, tuple):
        return "(" + ",".join(render(x) for x in v) + ")"
    return str(v)  # an enumeration constant


def describe():
    import snakes
    return "SNAKES %s" % snakes.version

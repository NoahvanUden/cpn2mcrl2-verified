#!/usr/bin/env python3
"""PNML to native CPN JSON.

Milestone M7 of ``Implementation/docs/Plan.md`` section 6, as scoped by
``Tests/docs/Plan.md`` section 3.1.

This converter is **outside the trust boundary**, per ``InputFormat.md`` section 3: it
turns a high-level PNML file into the native JSON AST that the three verified
translators read, and it is the translators -- not this program -- that decide whether
the result is a CPN in the sense of Definition 5.

It is written once rather than three times, because being outside the boundary is
exactly what makes that safe: its output is read by three independent implementations,
which is a better check on it than any test it could carry itself.

Everything a PNML file can express that ``InputFormat.md`` section 4.1 cannot is
rejected by name, loudly, here -- which is the other half of section 3's argument.

Usage:
    python pnml2cpn.py net.pnml [out.cpn.json]
"""

import json
import sys
import xml.etree.ElementTree as ET

PNML_NS = "http://www.pnml.org/version-2009/grammar/pnml"

SUPPORTED_NET_TYPES = {
    "http://www.pnml.org/version-2009/grammar/symmetricnet",
    "http://www.pnml.org/version-2009/grammar/hlpng",
}


class Unsupported(Exception):
    """A PNML construct outside the expression language of InputFormat.md 4.1.

    Distinct from a malformed file: the input may be perfectly good PNML that this
    project's native format has no way to represent.
    """


class Malformed(Exception):
    """The file is not the PNML this converter knows how to read."""


def tag(elem):
    """The element's local name, with any namespace stripped."""
    t = elem.tag
    return t.split("}", 1)[1] if "}" in t else t


def child(elem, name, required=True, where=""):
    for c in elem:
        if tag(c) == name:
            return c
    if required:
        raise Malformed("expected a <%s> inside <%s>%s" % (name, tag(elem), where))
    return None


def children(elem, name):
    return [c for c in elem if tag(c) == name]


def only_child(elem, where):
    """The single element child, for the wrappers PNML uses everywhere."""
    kids = list(elem)
    if len(kids) != 1:
        raise Malformed(
            "expected exactly one child of <%s>%s, found %d"
            % (tag(elem), where, len(kids))
        )
    return kids[0]


# --------------------------------------------------------------------------- sorts


class Sorts:
    """The declarations block: colours, and the variables typed by them.

    Field names are the one place this converter has to invent something. PNML product
    sorts are positional -- ISO/IEC 15909-2 has tuples, not records with named fields --
    while `InputFormat.md` 4.1's records are named. Components are therefore named
    `f1`, `f2`, ... unless the `<productsort>` carries a `<toolspecific>` block naming
    them; see `README.md` 3.2.
    """

    def __init__(self):
        self.colors = {}      # name -> native JSON colour declaration
        self.variables = {}   # name -> colour name
        self.ctor_owner = {}  # enumeration constant -> the colour declaring it
        self.field_names = {}  # product sort name -> [field name]

    def declare_from(self, decls):
        for nd in children(decls, "namedsort"):
            name = nd.get("id") or nd.get("name")
            if not name:
                raise Malformed("a <namedsort> has neither id nor name")
            body = only_child(nd, " for sort %s" % name)
            self.colors[name] = self._sort_body(name, body)
        for vd in children(decls, "variabledecl"):
            name = vd.get("id") or vd.get("name")
            us = only_child(vd, " for variable %s" % name)
            if tag(us) != "usersort":
                raise Unsupported(
                    "variable %s is declared with <%s>; only a <usersort> naming a "
                    "declared colour is supported" % (name, tag(us))
                )
            self.variables[name] = us.get("declaration")
        for other in decls:
            if tag(other) not in ("namedsort", "variabledecl"):
                raise Unsupported(
                    "declaration <%s> is not supported; InputFormat.md 4.1 has no "
                    "user-defined operators or functions" % tag(other)
                )

    def _sort_body(self, name, body):
        t = tag(body)
        if t in ("bool", "boolean"):
            return {"kind": "bool"}
        if t in ("integer", "natural", "positive"):
            return {"kind": "int"}
        if t == "finiteenumeration":
            ids = []
            for fc in children(body, "feconstant"):
                cid = fc.get("id") or fc.get("name")
                ids.append(cid)
                self.ctor_owner[cid] = name
            if not ids:
                raise Malformed("enumeration %s has no constants" % name)
            return {"kind": "enum", "ids": ids}
        if t == "productsort":
            comps = []
            for c in body:
                if tag(c) == "toolspecific":
                    continue
                if tag(c) != "usersort":
                    raise Unsupported(
                        "component <%s> of product sort %s is not a <usersort>; "
                        "nested anonymous sorts are not supported" % (tag(c), name)
                    )
                comps.append(c.get("declaration"))
            names = self._product_field_names(body, name, len(comps))
            self.field_names[name] = names
            return {"kind": "record", "fields": [[n, c] for n, c in zip(names, comps)]}
        if t == "cyclicenumeration":
            raise Unsupported(
                "sort %s is a cyclic enumeration; its successor operation is not in "
                "InputFormat.md 4.1" % name
            )
        if t in ("dot", "multisetsort", "finiteintrange", "list", "string"):
            raise Unsupported("sort %s uses <%s>, which has no colour in "
                              "InputFormat.md 4.1" % (name, t))
        raise Unsupported("sort %s uses an unrecognised body <%s>" % (name, t))

    @staticmethod
    def _product_field_names(body, name, count):
        ts = child(body, "toolspecific", required=False)
        if ts is not None and ts.get("tool") == "cpn2mcrl2":
            fields = child(ts, "fieldnames", required=False)
            if fields is not None:
                names = [f.get("name") for f in children(fields, "field")]
                if len(names) != count:
                    raise Malformed(
                        "product sort %s names %d fields but has %d components"
                        % (name, len(names), count)
                    )
                return names
        return ["f%d" % (i + 1) for i in range(count)]

    def color_of_ctor(self, cid):
        return self.ctor_owner.get(cid)


# --------------------------------------------------------------------------- terms

# PNML operator -> native operator, for the fragment InputFormat.md 4.1 has.
BINARY_OPS = {
    "equality": "=",
    "lessthan": "<",
    "lessthanorequal": "<=",
    "addition": "+",
    "subtraction": "-",
    "multiplication": "*",
}

# Operators that are the same relation with the arguments the other way round.
FLIPPED_OPS = {
    "greaterthan": "<",
    "greaterthanorequal": "<=",
}


class Terms:
    def __init__(self, sorts):
        self.sorts = sorts

    def subterms(self, elem):
        return [only_child(st, "") for st in children(elem, "subterm")]

    def value(self, elem):
        """A colour-valued term: everything in 4.1 except the bag fragment."""
        t = tag(elem)
        if t == "variable":
            name = elem.get("refvariable") or elem.get("name")
            if name not in self.sorts.variables:
                raise Malformed("term uses an undeclared variable %s" % name)
            return ["var", name]
        if t == "useroperator":
            decl = elem.get("declaration")
            if self.sorts.color_of_ctor(decl) is None:
                raise Unsupported(
                    "useroperator %s is not an enumeration constant; user-defined "
                    "operators are not in InputFormat.md 4.1" % decl
                )
            return ["ctor", decl]
        if t == "booleanconstant":
            return ["bool", elem.get("value") == "true"]
        if t == "numberconstant":
            return ["int", int(elem.get("value"))]
        if t == "tuple":
            return self._tuple(elem)
        if t in BINARY_OPS:
            a, b = self._two(elem, t)
            return [BINARY_OPS[t], self.value(a), self.value(b)]
        if t in FLIPPED_OPS:
            a, b = self._two(elem, t)
            return [FLIPPED_OPS[t], self.value(b), self.value(a)]
        if t == "inequality":
            a, b = self._two(elem, t)
            return ["!", ["=", self.value(a), self.value(b)]]
        if t == "and":
            return self._fold("&&", elem)
        if t == "or":
            return self._fold("||", elem)
        if t == "not":
            (a,) = self.subterms(elem)
            return ["!", self.value(a)]
        if t in ("all", "finiteintrangeconstant", "dotconstant"):
            raise Unsupported(
                "<%s> has no counterpart in InputFormat.md 4.1" % t
            )
        raise Unsupported("term <%s> is not in InputFormat.md 4.1" % t)

    def _two(self, elem, t):
        subs = self.subterms(elem)
        if len(subs) != 2:
            raise Malformed("<%s> takes two subterms, got %d" % (t, len(subs)))
        return subs

    def _fold(self, op, elem):
        subs = self.subterms(elem)
        if len(subs) < 2:
            raise Malformed("<%s> takes at least two subterms" % op)
        out = self.value(subs[0])
        for s in subs[1:]:
            out = [op, out, self.value(s)]
        return out

    def _tuple(self, elem):
        subs = self.subterms(elem)
        sort = self._product_sort_of(len(subs))
        names = self.sorts.field_names[sort]
        return ["rec", sort, [[n, self.value(s)] for n, s in zip(names, subs)]]

    def _product_sort_of(self, arity):
        """PNML tuples carry no sort, so it is recovered from the arity.

        Ambiguous when two product sorts have the same number of components, which is
        rejected rather than guessed.
        """
        candidates = [
            n for n, f in self.sorts.field_names.items() if len(f) == arity
        ]
        if not candidates:
            raise Malformed("a <tuple> of %d components matches no product sort" % arity)
        if len(candidates) > 1:
            raise Unsupported(
                "a <tuple> of %d components could belong to any of %s; PNML tuples "
                "carry no sort, so this file cannot be imported unambiguously"
                % (arity, ", ".join(sorted(candidates)))
            )
        return candidates[0]

    def bag(self, elem):
        """A bag-valued term: an initial marking or an arc inscription."""
        items = self._bag_items(elem)
        if not items:
            return ["emptyBag"]
        return ["bag", items]

    def _bag_items(self, elem):
        t = tag(elem)
        if t == "empty":
            return []
        if t == "numberof":
            subs = self.subterms(elem)
            if len(subs) != 2:
                raise Malformed("<numberof> takes two subterms")
            count = subs[0]
            if tag(count) != "numberconstant":
                raise Unsupported(
                    "the multiplicity of a <numberof> must be a constant; "
                    "InputFormat.md 4.1 has no computed multiplicities"
                )
            return [[int(count.get("value")), self.value(subs[1])]]
        if t == "add":
            out = []
            for s in self.subterms(elem):
                out.extend(self._bag_items(s))
            return out
        if t == "subtract":
            raise Unsupported(
                "<subtract> in a marking or inscription is not supported; arc "
                "expressions in Definition 5 are bags, not bag differences"
            )
        if t == "all":
            raise Unsupported(
                "<all> enumerates a whole sort; InputFormat.md 4.1 has no such term"
            )
        # A bare colour term is the singleton bag over it, which is how most tools
        # write an inscription of one token.
        return [[1, self.value(elem)]]


# ----------------------------------------------------------------------------- net


def structure_of(elem, what):
    """PNML wraps every term in <...><structure>TERM</structure></...>."""
    if elem is None:
        return None
    st = child(elem, "structure", required=False)
    if st is None:
        text = "".join(elem.itertext()).strip()
        raise Unsupported(
            "%s has no <structure>; this converter reads the structured form of "
            "ISO/IEC 15909-2, not the tool-specific text %r" % (what, text[:40])
        )
    return only_child(st, " of %s" % what)


def collect(root, name, into):
    """Places, transitions and arcs live inside <page>, which nests."""
    for c in root:
        if tag(c) == name:
            into.append(c)
        elif tag(c) == "page":
            collect(c, name, into)


def convert(path):
    try:
        tree = ET.parse(path)
    except ET.ParseError as e:
        raise Malformed("not well-formed XML: %s" % e)
    root = tree.getroot()
    if tag(root) != "pnml":
        raise Malformed("the root element is <%s>, not <pnml>" % tag(root))
    if "}" in root.tag and PNML_NS not in root.tag:
        raise Malformed(
            "the root element is in namespace %s, not the PNML namespace %s"
            % (root.tag.split("}")[0][1:], PNML_NS)
        )

    net = child(root, "net")
    ntype = net.get("type", "")
    if ntype not in SUPPORTED_NET_TYPES:
        raise Unsupported(
            "net type %r is not a high-level net; this converter reads Symmetric Nets "
            "and HLPNG, because InputFormat.md 4.1 is a coloured language" % ntype
        )

    sorts = Sorts()
    decl = None
    for holder in [net] + children(net, "page"):
        d = child(holder, "declaration", required=False)
        if d is not None:
            decl = d
            break
    if decl is None:
        raise Malformed(
            "the net has no <declaration>; a high-level net must declare its sorts"
        )
    sorts.declare_from(child(structure_of(decl, "the declaration"), "declarations")
                       if tag(structure_of(decl, "the declaration")) != "declarations"
                       else structure_of(decl, "the declaration"))

    terms = Terms(sorts)

    place_elems, trans_elems, arc_elems = [], [], []
    collect(net, "place", place_elems)
    collect(net, "transition", trans_elems)
    collect(net, "arc", arc_elems)

    places = {}
    for p in place_elems:
        pid = p.get("id")
        ptype = structure_of(child(p, "type", required=True, where=" for place %s" % pid),
                             "the type of place %s" % pid)
        if tag(ptype) != "usersort":
            raise Unsupported(
                "place %s is typed with <%s>; Definition 5 gives each place a declared "
                "colour, so a <usersort> is required" % (pid, tag(ptype))
            )
        color = ptype.get("declaration")
        im = child(p, "hlinitialMarking", required=False)
        if im is None:
            init = ["emptyBag"]
        else:
            init = terms.bag(structure_of(im, "the initial marking of place %s" % pid))
        places[pid] = {"color": color, "init": init}

    transitions = {}
    for t in trans_elems:
        tid = t.get("id")
        cond = child(t, "condition", required=False)
        if cond is None:
            transitions[tid] = {"guard": ["bool", True]}
        else:
            transitions[tid] = {
                "guard": terms.value(structure_of(cond, "the guard of transition %s" % tid))
            }

    in_arcs, out_arcs = [], []
    for a in arc_elems:
        src, tgt = a.get("source"), a.get("target")
        insc = child(a, "hlinscription", required=False)
        if insc is None:
            raise Unsupported(
                "arc %s has no <hlinscription>; an uninscribed arc is a P/T net arc, "
                "and Definition 5 requires a bag-valued expression" % a.get("id")
            )
        expr = terms.bag(structure_of(insc, "the inscription of arc %s" % a.get("id")))
        if src in places and tgt in transitions:
            in_arcs.append({"place": src, "transition": tgt, "expr": expr})
        elif src in transitions and tgt in places:
            out_arcs.append({"transition": src, "place": tgt, "expr": expr})
        else:
            raise Malformed(
                "arc %s runs from %r to %r, which is not a place-transition pair"
                % (a.get("id"), src, tgt)
            )

    return {
        "colors": sorts.colors,
        "variables": sorts.variables,
        "places": places,
        "transitions": transitions,
        "inArcs": in_arcs,
        "outArcs": out_arcs,
    }


def main(argv):
    if len(argv) < 2 or argv[1] in ("-h", "--help"):
        print(__doc__.strip())
        return 2
    try:
        net = convert(argv[1])
    except Unsupported as e:
        sys.stderr.write("%s: outside the native language: %s\n" % (argv[1], e))
        return 3
    except Malformed as e:
        sys.stderr.write("%s: not the PNML this reads: %s\n" % (argv[1], e))
        return 4
    text = json.dumps(net, indent=2) + "\n"
    if len(argv) > 2:
        with open(argv[2], "w", encoding="utf-8") as f:
            f.write(text)
    else:
        sys.stdout.write(text)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))

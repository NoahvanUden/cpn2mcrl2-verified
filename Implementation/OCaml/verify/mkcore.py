# Concatenate the ten core modules into one file for Cameleer, which verifies one file at a
# time: a cross-file reference is an unbound symbol to it, while nested modules inside one
# file work. The build uses the ten modules; this file is what the verifier reads.
import io, re, os
mods = [("Util","util.ml"),("Color","color.ml"),("Bag","bag.ml"),("List_ops","list_ops.ml"),
        ("Expr","expr.ml"),("Net","net.ml"),("Lpe","lpe.ml"),("Translate","translate.ml"),
        ("Semantics","semantics.ml"),("List_encoding","list_encoding.ml")]
here = os.path.dirname(os.path.abspath(__file__))
lib = os.path.join(here, "..", "lib")
out = []
for name, f in mods:
    body = io.open(os.path.join(lib, f), encoding="utf-8").read()
    body = re.sub(r'^\(\*\n \* Copyright.*?\n \*\)\n', '', body, flags=re.S)
    body = "\n".join("  " + ln if ln.strip() else ln for ln in body.split("\n"))
    out.append("module %s = struct\n%s\nend\n" % (name, body))
io.open(os.path.join(here, "core.ml"), "w", encoding="utf-8").write("\n".join(out))
print("verify/core.ml regenerated")

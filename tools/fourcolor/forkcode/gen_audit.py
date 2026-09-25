#!/usr/bin/env python3
"""Write the Lean modules of a kernel-checked fork-code audit.

The modules hold the certificate of a closure dump (see dump_to_cert.py), one
theorem per page of the checker (`PhysicalForkCodeFlat.pageOk`: one member of
the certificate against all members), and the assembly into
`PhysicalForkCode.Audit BOUND` through `audit_of_checks`.  Each page is checked
by kernel evaluation (`decide +kernel`) in its own declaration, which bounds
the memory of every check.

Usage: gen_audit.py DUMP BOUND OUTDIR [--split PAGES_PER_MODULE]

Without --split one module PhysicalForkCodeAudit<Bound>.lean is written.  With
it, the certificate goes to ...Cert.lean, the pages to ...Pages<k>.lean, and
the assembly to PhysicalForkCodeAudit<Bound>.lean, so that the page modules can
be checked one at a time.
"""
import os
import sys

from dump_to_cert import convert, lean_def

WORDS = {1: "One", 2: "Two", 3: "Three", 4: "Four", 5: "Five", 6: "Six"}
PREFIX = "Mettapedia.GraphTheory.FourColor."
NS = "Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat"


def names(bound):
    w = WORDS.get(bound, str(bound))
    return w, w.lower(), f"cert_{w.lower()}", f"(certCodes cert_{w.lower()})"


def header(bound, count):
    return f"""/-!
# The fork-code audit at interface bound {bound}

The closure `Reach {bound}` has {count} classes of codes with at least one position,
under renaming of positions.  The certificate lists one flat code per class.
Each page checks, by kernel evaluation, every legal planar fork of one member
with every member: a fork with no positions must not be rejecting, and the
canonical form of any other fork must be a member.  The soundness theorem of
the checker turns the pages into the audit.
-/
"""


def cert_part(cert, bound, count):
    W, w, c, codes = names(bound)
    return [
        lean_def(c, cert),
        f"theorem certCodes_{w}_length : {codes}.length = {count} := by decide +kernel\n",
        f"theorem leaf_{w} : leafOk {codes} = true := by decide +kernel\n",
        f"theorem roots_{w} : rootsOk {codes} = true := by decide +kernel\n",
    ]


def page_part(bound, pages):
    W, w, c, codes = names(bound)
    return [f"theorem page_{w}_{i} :\n"
            f"    pageOk {bound} {codes} ({codes}.getD {i} leafF) = true := by\n"
            f"  decide +kernel\n" for i in pages]


def assembly_part(bound, count):
    W, w, c, codes = names(bound)
    arms = "\n".join(f"  | {i}, _ => exact page_{w}_{i}" for i in range(count))
    return [f"""theorem pages_{w} : ∀ L ∈ {codes}, pageOk {bound} {codes} L = true := by
  apply forall_mem_of_getD
  rw [certCodes_{w}_length]
  intro i hi
  match i, hi with
{arms}
  | _ + {count}, h => exact absurd h (by omega)
""", f"""/-- **The audit at interface bound {bound}.**  No root code of the closure
`Reach {bound}` is rejecting. -/
theorem audit_{w} : PhysicalForkCode.Audit {bound} :=
  audit_of_checks leaf_{w} pages_{w} roots_{w}
"""]


def write_module(path, imports, doc, parts):
    with open(path, "w") as fh:
        fh.write("".join(f"import {m}\n" for m in imports) + "\n")
        if doc:
            fh.write(doc + "\n")
        fh.write(f"namespace {NS}\n\n")
        fh.write("\n".join(parts))
        fh.write(f"\nend {NS}\n")


def main(argv):
    if len(argv) not in (3, 5):
        print(__doc__, file=sys.stderr)
        return 2
    dump, bound, outdir = argv[0], int(argv[1]), argv[2]
    split = int(argv[4]) if len(argv) == 5 and argv[3] == "--split" else None
    with open(dump) as fh:
        lines = [line for line in fh.readlines() if line.split()]
    cert, count = convert(lines), len(lines)
    W = names(bound)[0]
    base = f"PhysicalForkCodeAudit{W}"
    checker = PREFIX + "PhysicalForkCodeFlatCheck"
    if split is None:
        write_module(os.path.join(outdir, base + ".lean"), [checker], header(bound, count),
                     cert_part(cert, bound, count) + page_part(bound, range(count)) +
                     assembly_part(bound, count))
        return 0
    write_module(os.path.join(outdir, base + "Cert.lean"), [checker],
                 f"/-! The certificate of the audit at interface bound {bound}. -/\n",
                 cert_part(cert, bound, count))
    page_modules = []
    for k, start in enumerate(range(0, count, split)):
        mod = f"{base}Pages{k}"
        page_modules.append(PREFIX + mod)
        stop = min(count, start + split)
        write_module(os.path.join(outdir, mod + ".lean"), [PREFIX + base + "Cert"],
                     f"/-! Pages {start} to {stop - 1} of the audit at interface bound {bound}. -/\n",
                     page_part(bound, range(start, stop)))
    write_module(os.path.join(outdir, base + ".lean"), page_modules, header(bound, count),
                 assembly_part(bound, count))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

#!/usr/bin/env python3
"""Write the Lean modules of a kernel-checked fork-code audit.

The modules hold the certificate of a closure dump (see dump_to_cert.py), one
theorem per page of the checker (`PhysicalForkCodeFlat.pageOk`: one member of
the certificate against all members), and the assembly into
`PhysicalForkCode.Audit BOUND` through `audit_of_checks`.  Each page is checked
by kernel evaluation (`decide +kernel`) in its own declaration, which bounds
the memory of every check.

Usage: gen_audit.py DUMP BOUND OUTDIR [--split PAGES_PER_MODULE | --layout RANGES]
                    [--chunk PAGE:PARTS ...]

Without --split or --layout one module PhysicalForkCodeAudit<Bound>.lean is
written.  With them, the certificate goes to ...Cert.lean, the pages to
...Pages<k>.lean, and the assembly to PhysicalForkCodeAudit<Bound>.lean, so
that the page modules can be checked one at a time.  --layout gives the page
range of every module, in module order, as comma-separated `a-b` ranges (`x`
for an unused module slot); it lets heavy pages sit in smaller modules.
--chunk checks one page in PARTS modules, each gluing the page's member with a
block of partners (`PhysicalForkCodeFlat.pairsOk`), and assembles the page with
`pageOk_of_chunks`.
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


def chunk_step(count, parts):
    return (count + parts - 1) // parts


def chunk_part(bound, count, page, parts, t):
    W, w, c, codes = names(bound)
    step = chunk_step(count, parts)
    return [f"theorem page_{w}_{page}_c{t} :\n"
            f"    pairsOk {bound} {codes} ({codes}.getD {page} leafF) {t * step} {step} = true := by\n"
            f"  decide +kernel\n"]


def chunk_assembly(bound, count, page, parts):
    W, w, c, codes = names(bound)
    step = chunk_step(count, parts)
    arms = "\n".join(f"    | {t}, _ => page_{w}_{page}_c{t}" for t in range(parts))
    return f"""theorem page_{w}_{page} :
    pageOk {bound} {codes} ({codes}.getD {page} leafF) = true :=
  pageOk_of_chunks {step} (by norm_num) fun t ht =>
    match t, ht with
{arms}
    | _ + {parts}, h => absurd h (by rw [certCodes_{w}_length]; omega)
"""


def assembly_part(bound, count, chunks=()):
    W, w, c, codes = names(bound)
    arms = "\n".join(f"  | {i}, _ => exact page_{w}_{i}" for i in range(count))
    pre = [chunk_assembly(bound, count, page, parts) for page, parts in chunks]
    return pre + [f"""theorem pages_{w} : ∀ L ∈ {codes}, pageOk {bound} {codes} L = true := by
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
    if len(argv) < 3:
        print(__doc__, file=sys.stderr)
        return 2
    dump, bound, outdir = argv[0], int(argv[1]), argv[2]
    chunks = []
    rest = argv[3:]
    while "--chunk" in rest:
        k = rest.index("--chunk")
        page, parts = rest[k + 1].split(":")
        chunks.append((int(page), int(parts)))
        rest = rest[:k] + rest[k + 2:]
    split = int(rest[1]) if len(rest) == 2 and rest[0] == "--split" else None
    layout = None
    if len(rest) == 2 and rest[0] == "--layout":
        layout = []
        for part in rest[1].split(","):
            if part == "x":
                layout.append(None)
                continue
            a, b = part.split("-")
            layout.append(range(int(a), int(b) + 1))
    with open(dump) as fh:
        lines = [line for line in fh.readlines() if line.split()]
    cert, count = convert(lines), len(lines)
    W = names(bound)[0]
    base = f"PhysicalForkCodeAudit{W}"
    checker = PREFIX + "PhysicalForkCodeFlatCheck"
    if split is None and layout is None:
        write_module(os.path.join(outdir, base + ".lean"), [checker], header(bound, count),
                     cert_part(cert, bound, count) + page_part(bound, range(count)) +
                     assembly_part(bound, count))
        return 0
    write_module(os.path.join(outdir, base + "Cert.lean"), [checker],
                 f"/-! The certificate of the audit at interface bound {bound}. -/\n",
                 cert_part(cert, bound, count))
    if layout is None:
        layout = [range(start, min(count, start + split)) for start in range(0, count, split)]
    covered = sorted([i for r in layout if r is not None for i in r] +
                     [page for page, _ in chunks])
    if covered != list(range(count)):
        print("layout does not cover every page exactly once", file=sys.stderr)
        return 2
    page_modules = []
    for k, pages in enumerate(layout):
        if pages is None:
            continue
        mod = f"{base}Pages{k}"
        page_modules.append(PREFIX + mod)
        write_module(os.path.join(outdir, mod + ".lean"), [PREFIX + base + "Cert"],
                     f"/-! Pages {pages.start} to {pages.stop - 1} of the audit at interface bound "
                     f"{bound}. -/\n",
                     page_part(bound, pages))
    for page, parts in chunks:
        for t in range(parts):
            mod = f"{base}Chunk{page}x{t}"
            page_modules.append(PREFIX + mod)
            write_module(os.path.join(outdir, mod + ".lean"),
                         [PREFIX + base + "Cert", PREFIX + "PhysicalForkCodeFlatSplit"],
                         f"/-! Part {t} of page {page} of the audit at interface bound {bound}. -/\n",
                         chunk_part(bound, count, page, parts, t))
    imports = page_modules + ([PREFIX + "PhysicalForkCodeFlatSplit"] if chunks else [])
    write_module(os.path.join(outdir, base + ".lean"), imports, header(bound, count),
                 assembly_part(bound, count, chunks))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

#!/usr/bin/env python3
"""Convert a closure dump into the flat certificate read by the Lean checker.

A dump line of `closure --dump` is
    n two ret[0] .. ret[n-1] col-words (12, hex) cut-words (8, hex)
where `two` is the bit mask of the two-edge flags and the words are the bit
sets of colour presentation indices and cut record indices.

The certificate is one list of natural numbers.  For every state it holds n,
the n flags (0 or 1), the n return values, the number of colour presentations
followed by their indices, and the number of cut records followed by their
indices (`PhysicalForkCodeFlat.decodeCodes`).

Usage: dump_to_cert.py DUMP [--lean NAME]
Without --lean the list is printed as JSON; with it, as a Lean definition.
"""
import json
import sys

COLW, CUTW = 12, 8


def bit_indices(words):
    out = []
    for w, word in enumerate(words):
        v = int(word, 16)
        b = 0
        while v:
            if v & 1:
                out.append(64 * w + b)
            v >>= 1
            b += 1
    return out


def convert(lines):
    cert = []
    for line in lines:
        f = line.split()
        if not f:
            continue
        n, two = int(f[0]), int(f[1])
        ret = [int(x) for x in f[2:2 + n]]
        col = bit_indices(f[2 + n:2 + n + COLW])
        cut = bit_indices(f[2 + n + COLW:2 + n + COLW + CUTW])
        assert len(f) == 2 + n + COLW + CUTW, line
        cert += [n] + [(two >> i) & 1 for i in range(n)] + ret
        cert += [len(col)] + col + [len(cut)] + cut
    return cert


def lean_def(name, cert, width=94):
    lines, cur = [], ""
    for i, x in enumerate(cert):
        tok = str(x) + ("," if i + 1 < len(cert) else "")
        if len(cur) + len(tok) + 1 > width:
            lines.append(cur)
            cur = ""
        cur = (cur + " " + tok) if cur else tok
    if cur:
        lines.append(cur)
    body = "\n  ".join(lines)
    return f"def {name} : List ℕ :=\n  [{body}]\n"


def main(argv):
    if not argv:
        print(__doc__, file=sys.stderr)
        return 2
    with open(argv[0]) as fh:
        cert = convert(fh.readlines())
    if len(argv) >= 3 and argv[1] == "--lean":
        sys.stdout.write(lean_def(argv[2], cert))
    else:
        print(json.dumps(cert))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

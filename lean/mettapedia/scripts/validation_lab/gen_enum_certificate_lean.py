#!/usr/bin/env python3
"""Emit an enumerated derivation certificate (`CertificateEnum`) for a tangle.

Support words are computed by exhaustive colouring; derivations by the same
depth-bounded search as the trie emitter, but the switch set of each listed
matching is emitted as a port subset, and matchings are listed in the order of
the Lean enumerator `enumPairs` (first port to each even-index partner of the
rest, inside before outside).  Digits 0,1,2 are red, blue, purple; pair
indices 0,1,2 are redBlue, redPurple, bluePurple.

Usage: gen_enum_certificate_lean.py tangle.json ModuleName [--maxdepth d] [--limit k]
"""
import sys, os, json, itertools
sys.path.insert(0, os.environ.get('KEMPE_DIR', '/home/oruzi/repos/ai-agents/lean/private/4cp-hexagon-lp'))
from cap_zero_kempe_test import load
args = sys.argv[1:]
tpath, modname = args[0], args[1]
MAXD = int(args[args.index('--maxdepth') + 1]) if '--maxdepth' in args else 6
LIMIT = int(args[args.index('--limit') + 1]) if '--limit' in args else None
n, nv, E0 = load(tpath)
PORT = 1000
E = [tuple((PORT + z[1]) if isinstance(z, tuple) else z for z in e) for e in E0]
m = len(E)
inc = {}
for k, (u, v) in enumerate(E):
    for z in (u, v): inc.setdefault(z, []).append(k)
port_edge = {i: inc[PORT + i][0] for i in range(n)}


def enum_pairs(pts):
    if not pts:
        return [[]]
    a, rest = pts[0], pts[1:]
    out = []
    for mm in range(len(rest)):
        if mm % 2 == 0:
            b = rest[mm]
            for inside in enum_pairs(rest[:mm]):
                for outside in enum_pairs(rest[mm + 1:]):
                    out.append([(a, b)] + inside + outside)
    return out


# support
supp = {}
col = [-1] * m
order = sorted(range(m), key=lambda k: (0 if any(z >= PORT for z in E[k]) else 1, k))
sys.setrecursionlimit(10000)


def rec(idx):
    if idx == m:
        w = tuple(col[port_edge[i]] for i in range(n))
        if w not in supp: supp[w] = col[:]
        return
    k = order[idx]
    for c in range(3):
        ok = True
        for z in E[k]:
            if z >= PORT: continue
            for e in inc[z]:
                if e != k and col[e] == c: ok = False; break
            if not ok: break
        if ok:
            col[k] = c; rec(idx + 1); col[k] = -1


rec(0)
S = set(supp)


def admissible(w):
    c = [w.count(t) for t in range(3)]
    return c[0] % 2 == c[1] % 2 == c[2] % 2


def switched(w, x, y, ports):
    w = list(w)
    for p in ports:
        w[p] = y if w[p] == x else x
    return tuple(w)


adm = [w for w in itertools.product(range(3), repeat=n) if admissible(w)]
pairs = ((0, 1), (0, 2), (1, 2))
cert = []  # (word, pair index, [selected port set per matching in enumPairs order])
changed = True; depth = 0
while changed and depth < MAXD:
    changed = False; depth += 1
    for w in adm:
        if w in S: continue
        for pi, (x, y) in enumerate(pairs):
            P = [i for i in range(n) if w[i] in (x, y)]
            if len(P) % 2: continue
            sels = []; ok = True
            for mu in enum_pairs(P):
                found = None
                for mask in range(1 << len(mu)):
                    chosen = [mu[t] for t in range(len(mu)) if (mask >> t) & 1]
                    ports = sorted(p for pr in chosen for p in pr)
                    if switched(w, x, y, ports) in S: found = ports; break
                if found is None: ok = False; break
                sels.append(found)
            if ok:
                cert.append((w, pi, sels)); S.add(w); changed = True; break
missing = [w for w in adm if w not in S]
print(f"ring {n} vertices {nv} edges {m} supp {len(supp)} derivations {len(cert)} missing {len(missing)}")
assert not missing
if LIMIT is not None:
    cert = cert[:LIMIT]

PAIR = ['TaitColorPair.redBlue', 'TaitColorPair.redPurple', 'TaitColorPair.bluePurple']


def word(w):
    return 'w ' + ' '.join(str(d) for d in w)


def fset(ports):
    return '(∅ : Finset (Fin ' + str(n) + '))' if not ports else '{' + ', '.join(str(p) for p in ports) + '}'


def sel_fun(sels):
    arms = ' '.join(f'| {k} => {fset(s)}' for k, s in enumerate(sels))
    return f'(fun k => match k with {arms} | _ => (∅ : Finset (Fin {n})))'


supp_words = list(supp)
lean = f'''import Mettapedia.GraphTheory.FourColor.KempeCertificateEnum

/-!
# Enumerated derivation certificate: `{os.path.basename(tpath)}` (ring {n}{', first ' + str(LIMIT) + ' nodes' if LIMIT else ''})

Support words of the tangle (base) and {len(cert)} derivation nodes, each with a switch set per
listed noncrossing matching.  `ok` is decided in the kernel; `derivable` follows by
`CertificateEnum.derivable_of_ok`.
-/

namespace Mettapedia.GraphTheory.FourColor.KempeDerivation
namespace {modname}

open GoertzelV24HexagonPairingTargetAwareBoundary

/-- a word from its digits -/
def w ({' '.join('d' + str(i) for i in range(n))} : Fin 3) : Word {n} :=
  ![{', '.join('tc d' + str(i) for i in range(n))}]

def base : Finset (Word {n}) := [
  {(',\n  '.join(word(x) for x in supp_words))}].toFinset

def nodes : List (Word {n} × TaitColorPair × (Nat → Finset (Fin {n}))) := [
  {(',\n  '.join(f'({word(x)}, {PAIR[pi]}, {sel_fun(sels)})' for (x, pi, sels) in cert))}]

def cert : CertificateEnum {n} := ⟨nodes⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok : cert.Ok base := by decide +kernel

/-- every node word is derivable into any target containing the support words -/
theorem derivable {{target : Set (Word {n})}} (hbase : ∀ u ∈ base, u ∈ target) :
    ∀ k (h : k < cert.nodes.length), Derivable target (cert.nodes[k]).1 :=
  cert.derivable_of_ok hbase ok

end {modname}
end Mettapedia.GraphTheory.FourColor.KempeDerivation
'''
out = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'Mettapedia', 'GraphTheory', 'FourColor', modname + '.lean')
open(out, 'w').write(lean)
print('wrote', modname, 'nodes', len(cert), 'base', len(supp_words))

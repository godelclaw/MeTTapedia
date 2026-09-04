"""Compact kernel witness for D/C-reducibility of a port tangle.

Certificate = (a) support words with one colouring each (needed for
soundness of supp membership), (b) the ORDERED list of closure words with
the colour pair used for each -- the kernel enumerates the noncrossing
matchings and SEARCHES the chain subsets itself (2^(k/2) per matching),
(c) the cap (or empty for D). All word lists are encoded as base-3 numerals
packed into big Nat literals (one Nat per block of 64 words) to keep the
Lean source small; sets are Nat bitmasks.

Usage: python3 gen_compact_witness_lean.py tangle.json ModuleName [CAP="i,j;..."]
"""
import sys, os, json, itertools
sys.path.insert(0, os.environ.get('KEMPE_DIR', '/home/oruzi/repos/ai-agents/lean/private/4cp-hexagon-lp'))
from kempe import noncrossing
from cap_zero_kempe_test import load

tpath, modname = sys.argv[1], sys.argv[2]
n, nv, E0 = load(tpath)
PORT = 1000
E = [tuple((PORT + z[1]) if isinstance(z, tuple) else z for z in e) for e in E0]
m = len(E)
inc = {}
for k, (u, v) in enumerate(E):
    for z in (u, v): inc.setdefault(z, []).append(k)
port_edge = {i: inc[PORT + i][0] for i in range(n)}
def code(w): return sum(c * 3 ** i for i, c in enumerate(w))
def admissible(w):
    c = [w.count(t) for t in range(3)]
    return c[0] % 2 == c[1] % 2 == c[2] % 2
# support with colourings
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
S = {code(w) for w in supp}
adm = [w for w in itertools.product(range(3), repeat=n) if admissible(w)]
def switched(w, x, y, chains):
    w = list(w)
    for (i, j) in chains:
        for p in (i, j): w[p] = y if w[p] == x else x
    return tuple(w)
cert = []   # (word, pairindex)
pairs = ((0, 1), (0, 2), (1, 2))
changed = True
while changed:
    changed = False
    for w in adm:
        if code(w) in S: continue
        for pi, (x, y) in enumerate(pairs):
            P = [i for i in range(n) if w[i] in (x, y)]
            if len(P) % 2: continue
            ok = True
            for mu in noncrossing(P):
                found = False
                for r in range(len(mu) + 1):
                    for sub in itertools.combinations(range(len(mu)), r):
                        if code(switched(w, x, y, [mu[t] for t in sub])) in S: found = True; break
                    if found: break
                if not found: ok = False; break
            if ok:
                cert.append((w, pi)); S.add(code(w)); changed = True; break
CAP = os.environ.get('CAP')
if CAP:
    mu = [tuple(int(t) for t in pr.split(',')) for pr in CAP.split(';')]
    target = [w for w in itertools.product(range(3), repeat=n) if all(w[i] == w[j] for (i, j) in mu)]
else:
    mu = []; target = adm
missing = [w for w in target if code(w) not in S]
print(f"ring {n} vertices {nv} edges {m} supp {len(supp)} closure-cert {len(cert)} target {len(target)} missing {len(missing)}")
assert not missing
# ---- packing: word codes < 3^n; pack 64 codes per Nat in base 3^n
B = 3 ** n; BLK = 64
def pack(codes_):
    out = []
    for i in range(0, len(codes_), BLK):
        blk = codes_[i:i + BLK]; v = 0
        for c in reversed(blk): v = v * B + c
        out.append((v, len(blk)))
    return out
supp_words = list(supp)
supp_packed = pack([code(w) for w in supp_words])
# colourings: pack each colouring (m trits) as one Nat base 3, 32 per block base 3^m
def pack_cols(cols):
    out = []; Bm = 3 ** m
    for i in range(0, len(cols), 32):
        blk = cols[i:i + 32]; v = 0
        for cl in reversed(blk):
            cv = sum(c * 3 ** k for k, c in enumerate(cl)); v = v * Bm + cv
        out.append((v, len(blk)))
    return out
cols_packed = pack_cols([supp[w] for w in supp_words])
cert_packed = pack([code(w) for (w, pi) in cert])
pair_packed = pack([pi for (w, pi) in cert]) if cert else []
# pairs are < 3 so use base 3^n packing too (wasteful but uniform)
def LN(blocks): return '[' + ', '.join(f'({v}, {l})' for v, l in blocks) + ']'
def LP(ps): return '[' + ', '.join(f'({a}, {b})' for a, b in ps) + ']'
lean = f'''import Mathlib

/-!
# {'C' if CAP else 'D'}-reducibility witness (compact certificate): `{os.path.basename(tpath)}`

Tangle with {n} ports and {nv} internal vertices. Support words are
certified by one colouring each; closure words are supplied in derivation
order together with the colour pair used; for each closure word the kernel
enumerates every noncrossing matching of the pair-ports and searches the
chain subsets itself. Finally every target word ({'the cap words' if CAP else 'all admissible words'})
must lie in the closure. Word lists are packed into big numerals; sets are
bitmasks. Checked by `decide +kernel` (kernel reduction only, no extra axioms).
-/

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Mettapedia.GraphTheory.{modname}

def ring : Nat := {n}
def nE : Nat := {m}
def base : Nat := 3 ^ ring
def edges : List (Nat × Nat) := {LP(E)}
def portNode (i : Nat) : Nat := {PORT} + i
def cap : List (Nat × Nat) := {LP(mu)}

/-- packed blocks: (value, count); block value = Σ item_i · base^i -/
def suppBlocks : List (Nat × Nat) := {LN(supp_packed)}
def colBlocks : List (Nat × Nat) := {LN(cols_packed)}
def certBlocks : List (Nat × Nat) := {LN(cert_packed)}
def pairBlocks : List (Nat × Nat) := {LN(pair_packed)}

def unpack (b : Nat) (v : Nat) : Nat → List Nat
  | 0 => []
  | k + 1 => (v % b) :: unpack b (v / b) k
def unpackAll (b : Nat) (blocks : List (Nat × Nat)) : List (List Nat) :=
  blocks.map fun (v, k) => unpack b v k

def decodeWord (c : Nat) : List Nat := (List.range ring).map fun i => (c / 3 ^ i) % 3
def decodeCol (c : Nat) : List Nat := (List.range nE).map fun i => (c / 3 ^ i) % 3
def mem (S : Nat) (c : Nat) : Bool := (S >>> c) % 2 == 1
def ins (S : Nat) (c : Nat) : Nat := S ||| (1 <<< c)
def code (w : List Nat) : Nat := w.foldr (fun c acc => c + 3 * acc) 0

def edgeAt (k : Nat) : Nat × Nat := edges.getD k (0, 0)
def incidentEdges (v : Nat) : List Nat :=
  (List.range nE).filter fun k => (edgeAt k).1 == v || (edgeAt k).2 == v
def colouringOk (w : List Nat) (col : List Nat) : Bool :=
  col.length == nE && col.all (· < 3) &&
  (List.range {nv}).all (fun v =>
    let cs := (incidentEdges v).map fun k => col.getD k 9
    cs.length == 3 && cs.eraseDups.length == 3) &&
  (List.range ring).all fun i =>
    (incidentEdges (portNode i)).all fun k => col.getD k 9 == w.getD i 9

/-- support: each block of words with its block of colourings -/
def suppOkAndSet : Bool × Nat :=
  let ws := unpackAll base suppBlocks
  let cs := unpackAll (3 ^ nE) colBlocks
  -- word blocks are 64 long, colouring blocks 32 long: re-flatten by index
  let wsf := ws.flatMap id
  let csf := cs.flatMap id
  let ok := wsf.length == csf.length &&
    (List.range (wsf.length / 256 + 1)).all fun b =>
      (List.range 256).all fun i =>
        let t := b * 256 + i
        t ≥ wsf.length || colouringOk (decodeWord (wsf.getD t 0)) (decodeCol (csf.getD t 0))
  let S := wsf.foldl (fun S c => ins S c) 0
  (ok, S)

def nc : Nat → List Nat → List (List (Nat × Nat))
  | 0, _ => []
  | _, [] => [[]]
  | f + 1, a :: rest =>
      (List.range rest.length).foldr (fun m acc =>
        if m % 2 == 0 then
          let b := rest.getD m 0
          ((nc f (rest.take m)).flatMap fun mi => (nc f (rest.drop (m + 1))).map fun mo => (a, b) :: (mi ++ mo)) ++ acc
        else acc) []

def flipAt (w : List Nat) (p x y : Nat) : List Nat :=
  (List.range w.length).map fun i => let c := w.getD i 9; if i == p then (if c == x then y else x) else c
def switched (w : List Nat) (x y : Nat) (chains : List (Nat × Nat)) : List Nat :=
  chains.foldl (fun acc (i, j) => flipAt (flipAt acc i x y) j x y) w
def pairPorts (w : List Nat) (x y : Nat) : List Nat :=
  (List.range ring).filter fun i => w.getD i 9 == x || w.getD i 9 == y
def pairOf (pi : Nat) : Nat × Nat := if pi == 0 then (0, 1) else if pi == 1 then (0, 2) else (1, 2)

/-- some subset of the chains of `mu` switches `w` into `S`: search all 2^|mu| subsets -/
def subsetHits (S : Nat) (w : List Nat) (x y : Nat) (mu : List (Nat × Nat)) : Bool :=
  (List.range (2 ^ mu.length)).any fun mask =>
    let chains := (List.range mu.length).filterMap fun t => if (mask >>> t) % 2 == 1 then some (mu.getD t (0, 0)) else none
    mem S (code (switched w x y chains))

def admissible (w : List Nat) : Bool :=
  (w.count 0) % 2 == (w.count 1) % 2 && (w.count 1) % 2 == (w.count 2) % 2

def wordGood (S : Nat) (w : List Nat) (pi : Nat) : Bool :=
  let (x, y) := pairOf pi
  admissible w && (nc ring (pairPorts w x y)).all fun mu => subsetHits S w x y mu

def closureRun (S0 : Nat) : Nat × Bool :=
  let cs := (unpackAll base certBlocks).flatMap id
  let ps := (unpackAll base pairBlocks).flatMap id
  (List.range cs.length).foldl (fun (S, ok) t =>
    let c := cs.getD t 0
    (ins S c, ok && wordGood S (decodeWord c) (ps.getD t 0))) (S0, true)

def isTarget (w : List Nat) : Bool :=
  if cap.isEmpty then admissible w else cap.all fun (i, j) => w.getD i 9 == w.getD j 9
def blockOk (S : Nat) (b : Nat) : Bool :=
  (List.range 2048).all fun i => let c := b * 2048 + i; c ≥ base || !(isTarget (decodeWord c)) || mem S c
def targetCovered (S : Nat) : Bool := (List.range (base / 2048 + 1)).all fun b => blockOk S b

def reducible : Bool :=
  let (ok0, S0) := suppOkAndSet
  let (S, ok1) := closureRun S0
  ok0 && ok1 && targetCovered S

theorem reducible_true : reducible = true := by decide +kernel

end Mettapedia.GraphTheory.{modname}
'''
out = f'/home/oruzi/repos/MeTTapedia-4cplab/lean/mettapedia/Mettapedia/GraphTheory/{modname}.lean'
open(out, 'w').write(lean)
print("wrote", out, "size", len(lean))

"""Emit a Lean reducibility witness in the trie/Nat encoding.

Certificate: (1) support words each with a colouring (as base-3 numerals);
(2) derivations in dependency order: word code, pair index, and one Nat per
matching giving the chain-subset bitmask, matchings in the checker's own
enumeration order (first-point recursion, ascending partner index, inside
before outside) which the emitter reproduces exactly; (3) the cap (or none
for D). Every list is short or split into blocks of 256; words and
colourings are Nats. The checker keeps the word set as a base-3 trie.

Usage: python3 gen_trie_witness_lean.py tangle.json ModuleName [--cap "i,j;..."] [--maxdepth d]
"""
import sys, os, json, itertools
sys.path.insert(0, os.environ.get('KEMPE_DIR', '/home/oruzi/repos/ai-agents/lean/private/4cp-hexagon-lp'))
from cap_zero_kempe_test import load

args = sys.argv[1:]
tpath, modname = args[0], args[1]
CAP = None; MAXD = 6
if '--cap' in args: CAP = args[args.index('--cap') + 1]
if '--maxdepth' in args: MAXD = int(args[args.index('--maxdepth') + 1])
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

# checker's matching order: first point a = P[0]; partner b = P[m] for m = 1,3,5,...; inside then outside
def nc_ordered(P):
    if not P: return [[]]
    out = []; a = P[0]
    for mm in range(1, len(P), 2):
        b = P[mm]
        for mi in nc_ordered(P[1:mm]):
            for mo in nc_ordered(P[mm + 1:]):
                out.append([(a, b)] + mi + mo)
    return out

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
pairs = ((0, 1), (0, 2), (1, 2))
cert = []   # (word, pair index, [mask per matching in checker order])
changed = True; depth = 0
while changed and depth < MAXD:
    changed = False; depth += 1
    for w in adm:
        if code(w) in S: continue
        for pi, (x, y) in enumerate(pairs):
            P = [i for i in range(n) if w[i] in (x, y)]
            if len(P) % 2: continue
            masks = []; ok = True
            for mu in nc_ordered(P):
                found = None
                mus = sorted(mu)
                for mask in range(1 << len(mus)):
                    chains = [mus[t] for t in range(len(mus)) if (mask >> t) & 1]
                    if code(switched(w, x, y, chains)) in S: found = mask; break
                if found is None: ok = False; break
                masks.append(found)
            if ok:
                cert.append((w, pi, masks)); S.add(code(w)); changed = True; break
if CAP:
    mu = [tuple(int(t) for t in pr.split(',')) for pr in CAP.split(';')]
    target = [w for w in itertools.product(range(3), repeat=n) if all(w[i] == w[j] for (i, j) in mu)]
else:
    mu = []; target = adm
missing = [w for w in target if code(w) not in S]
print(f"ring {n} vertices {nv} edges {m} supp {len(supp)} closure-cert {len(cert)} target {len(target)} missing {len(missing)}")
assert not missing, "target not covered"

def blocks(xs, B=256): return [xs[i:i + B] for i in range(0, len(xs), B)]
def L_(xs): return '[' + ', '.join(str(x) for x in xs) + ']'
def LL(xss): return '[' + ',\n   '.join(L_(x) for x in xss) + ']'
def LP(ps): return '[' + ', '.join(f'({a}, {b})' for a, b in ps) + ']'
supp_words = list(supp)
supp_codes = [code(w) for w in supp_words]
supp_cols = [sum(c * 3 ** k for k, c in enumerate(supp[w])) for w in supp_words]
cert_codes = [code(w) for (w, pi, masks) in cert]
cert_pairs = [pi for (w, pi, masks) in cert]
# masks per derivation: pack the list of masks into one Nat: Σ mask_t * 1024^t (masks < 2^10 = 1024 for ring ≤ 20)
cert_masks = [sum(mk * (1024 ** t) for t, mk in enumerate(masks)) for (w, pi, masks) in cert]

lean = f'''/-!
# {'C (cap)' if CAP else 'D'}-reducibility witness, trie encoding: `{os.path.basename(tpath)}`

Words are base-3 numerals; the word set is a base-3 trie; matchings are
enumerated lazily by the checker (first port paired with each odd-indexed
partner, inside before outside); each derivation supplies one subset
bitmask per matching, packed in that order. Support words come with an
explicit colouring, checked edge-locally. Kernel-decided.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Mettapedia.GraphTheory.{modname}

def ring : Nat := {n}
def nE : Nat := {m}
def nV : Nat := {nv}
def edges : List (Nat × Nat) := {LP(E)}
def portNode (i : Nat) : Nat := {PORT} + i
def cap : List (Nat × Nat) := {LP(mu)}

/-- support: word codes and colouring codes, in blocks -/
def suppWords : List (List Nat) := {LL(blocks(supp_codes))}
def suppCols : List (List Nat) := {LL(blocks(supp_cols))}
/-- derivations: word codes, pair indices, packed masks, in blocks -/
def certWords : List (List Nat) := {LL(blocks(cert_codes))}
def certPairs : List (List Nat) := {LL(blocks(cert_pairs))}
def certMasks : List (List Nat) := {LL(blocks(cert_masks))}

/-! ## base-3 words as numerals -/
def digit (c i : Nat) : Nat := (c / 3 ^ i) % 3
def setDigit (c i v : Nat) : Nat := c - digit c i * 3 ^ i + v * 3 ^ i
/-- flip digit `i` between `x` and `y` (must be one of them) -/
def flip (c i x y : Nat) : Nat := if digit c i == x then setDigit c i y else setDigit c i x
def admissible (c : Nat) : Bool :=
  let cnt := fun v => ((List.range ring).filter fun i => digit c i == v).length
  cnt 0 % 2 == cnt 1 % 2 && cnt 1 % 2 == cnt 2 % 2

/-! ## base-3 trie for word sets -/
inductive Trie where
  | empty : Trie
  | node (present : Bool) (t0 t1 t2 : Trie) : Trie

def Trie.child : Trie → Nat → Trie
  | .empty, _ => .empty
  | .node _ a b c, d => if d == 0 then a else if d == 1 then b else c

def Trie.mem (t : Trie) (c : Nat) : Bool :=
  go t c ring
where
  go : Trie → Nat → Nat → Bool
    | .empty, _, _ => false
    | .node p _ _ _, _, 0 => p
    | t, c, k + 1 => go (t.child (c % 3)) (c / 3) k

def Trie.ins (t : Trie) (c : Nat) : Trie :=
  go t c ring
where
  go : Trie → Nat → Nat → Trie
    | .empty, _, 0 => .node true .empty .empty .empty
    | .node _ a b d, _, 0 => .node true a b d
    | t, c, k + 1 =>
      let (p, a, b, d) := match t with
        | .empty => (false, Trie.empty, Trie.empty, Trie.empty)
        | .node p a b d => (p, a, b, d)
      let r := c % 3
      if r == 0 then .node p (go a (c / 3) k) b d
      else if r == 1 then .node p a (go b (c / 3) k) d
      else .node p a b (go d (c / 3) k)

/-! ## colourings -/
def edgeAt (k : Nat) : Nat × Nat := edges.getD k (0, 0)
def incidentEdges (v : Nat) : List Nat :=
  (List.range nE).filter fun k => (edgeAt k).1 == v || (edgeAt k).2 == v
/-- proper at every internal vertex; port edges carry the word's digits -/
def colouringOk (w col : Nat) : Bool :=
  (List.range nV).all (fun v =>
    match (incidentEdges v).map (fun k => digit col k) with
    | [a, b, c] => a != b && b != c && a != c
    | _ => false) &&
  (List.range ring).all fun i =>
    (incidentEdges (portNode i)).all fun k => digit col k == digit w i

def buildSupp : Bool × Trie :=
  let ws := suppWords.flatMap id
  let cs := suppCols.flatMap id
  let ok := ws.length == cs.length &&
    (List.range ws.length).all fun t => colouringOk (ws.getD t 0) (cs.getD t 0)
  (ok, ws.foldl (fun tr c => tr.ins c) Trie.empty)

/-! ## lazy noncrossing matchings with a subset check per matching -/
def pairOf (pi : Nat) : Nat × Nat := if pi == 0 then (0, 1) else if pi == 1 then (0, 2) else (1, 2)
def pairPorts (w x y : Nat) : List Nat :=
  (List.range ring).filter fun i => digit w i == x || digit w i == y

def insertPair (p : Nat × Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [p]
  | q :: rest => if p.1 ≤ q.1 then p :: q :: rest else q :: insertPair p rest
def sortPairs : List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | p :: rest => insertPair p (sortPairs rest)

def switchMask (w x y : Nat) (chains0 : List (Nat × Nat)) (mask : Nat) : Nat :=
  let chains := sortPairs chains0
  (List.range chains.length).foldl (fun c t =>
    if (mask >>> t) % 2 == 1 then
      let (i, j) := chains.getD t (0, 0)
      flip (flip c i x y) j x y
    else c) w

/-- enumerate matchings of `pts` (first point with each odd partner; inside, then outside),
threading the matching index `idx` through `k`; `k` receives the complete chain list and the index. -/
def forMatchings : Nat → List Nat → List (Nat × Nat) → Nat → (List (Nat × Nat) → Nat → Bool × Nat) → Bool × Nat
  | 0, _, _, idx, _ => (false, idx)
  | _, [], acc, idx, k => k acc idx
  | f + 1, a :: rest, acc, idx, k =>
      (List.range rest.length).foldl (fun (ok, idx) mm =>
        if !ok then (false, idx) else
        if mm % 2 == 0 then
          let b := rest.getD mm 0
          forMatchings f (rest.take mm) ((a, b) :: acc) idx (fun acc1 idx1 =>
            forMatchings f (rest.drop (mm + 1)) acc1 idx1 k)
        else (ok, idx)) (true, idx)

/-- derivation check: for every matching (index t), the packed mask's t-th field switches into the set -/
def derivationOk (tr : Trie) (w pi masks : Nat) : Bool :=
  let (x, y) := pairOf pi
  admissible w &&
  (forMatchings (ring + 1) (pairPorts w x y) [] 0 (fun chains idx =>
    let mask := (masks / 1024 ^ idx) % 1024
    (tr.mem (switchMask w x y chains mask), idx + 1))).1

def runDerivations (tr : Trie) : Bool × Trie :=
  let ws := certWords.flatMap id
  let ps := certPairs.flatMap id
  let ms := certMasks.flatMap id
  (List.range ws.length).foldl (fun (ok, tr) t =>
    let w := ws.getD t 0
    (ok && derivationOk tr w (ps.getD t 0) (ms.getD t 0), tr.ins w)) (true, tr)

/-! ## target coverage -/
def isTarget (w : Nat) : Bool :=
  if cap.isEmpty then admissible w else cap.all fun (i, j) => digit w i == digit w j
def targetCovered (tr : Trie) : Bool :=
  (List.range (3 ^ ring / 1024 + 1)).all fun b =>
    (List.range 1024).all fun i =>
      let c := b * 1024 + i
      c ≥ 3 ^ ring || !(isTarget c) || tr.mem c

def reducible : Bool :=
  let (ok0, tr0) := buildSupp
  let (ok1, tr1) := runDerivations tr0
  ok0 && ok1 && targetCovered tr1

theorem reducible_true : reducible = true := by decide

end Mettapedia.GraphTheory.{modname}
'''
out = f'/home/oruzi/repos/MeTTapedia-4cplab/lean/mettapedia/Mettapedia/GraphTheory/{modname}.lean'
open(out, 'w').write(lean)
print("wrote", out, "size", len(lean))

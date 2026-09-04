"""Emit a Lean module certifying D-reducibility of a flower patch:
  closure(supp K) contains every admissible boundary word.
Certificates: one edge colouring per support word; for each closure word,
the colour pair and, per noncrossing matching of its pair-ports (enumerated
in the checker's own order), the chain subset whose switch lands in the set
built so far.  Sets are Nat bitmasks over word codes.

Usage: python3 gen_dreducible_witness_lean.py s o1 o2 ... [ModuleName]
"""
import sys, os, itertools
sys.path.insert(0, os.environ.get('KEMPE_DIR', '/home/oruzi/repos/ai-agents/lean/private/4cp-hexagon-lp'))
from kempe import noncrossing
from patch_reducibility_lab import flower

s = int(sys.argv[1]); outs = [int(x) for x in sys.argv[2:2 + s]]
modname = sys.argv[2 + s] if len(sys.argv) > 2 + s else f"FlowerDReducible_{s}_{''.join(map(str, outs))}"
n, nv, E = flower(s, outs)
PORT = 1000
def node(z): return PORT + z[1] if isinstance(z, tuple) else z
edges = [(node(u), node(v)) for (u, v) in E]
m = len(edges)
inc = {}
for k, (u, v) in enumerate(edges):
    for z in (u, v): inc.setdefault(z, []).append(k)
port_edge = {i: inc[PORT + i][0] for i in range(n)}

def code(w): return sum(c * 3 ** i for i, c in enumerate(w))
def admissible(w):
    c = [w.count(t) for t in range(3)]
    return c[0] % 2 == c[1] % 2 == c[2] % 2

# ---- support with colouring certificates (backtracking over edges)
supp = {}
col = [-1] * m
order = sorted(range(m), key=lambda k: (0 if any(z >= PORT for z in edges[k]) else 1, k))
def rec(idx):
    if idx == m:
        w = tuple(col[port_edge[i]] for i in range(n))
        if w not in supp: supp[w] = col[:]
        return
    k = order[idx]
    for c in range(3):
        ok = True
        for z in edges[k]:
            if z >= PORT: continue
            for e in inc[z]:
                if e != k and col[e] == c: ok = False; break
            if not ok: break
        if ok:
            col[k] = c; rec(idx + 1); col[k] = -1
rec(0)
S = {code(w) for w in supp}
adm = [w for w in itertools.product(range(3), repeat=n) if admissible(w)]
print(f"flower {s};{outs}: ring {n}, vertices {nv}, edges {m}, supp {len(supp)}, admissible {len(adm)}")

def switched(w, x, y, chains):
    w = list(w)
    for (i, j) in chains:
        for p in (i, j):
            w[p] = y if w[p] == x else x
    return tuple(w)

cert = []
changed = True
while changed:
    changed = False
    for w in adm:
        if code(w) in S: continue
        for (x, y) in ((0, 1), (0, 2), (1, 2)):
            P = [i for i in range(n) if w[i] in (x, y)]
            if len(P) % 2: continue
            entries = []; ok = True
            for mu in noncrossing(P):
                found = None
                for r in range(len(mu) + 1):
                    for sub in itertools.combinations(range(len(mu)), r):
                        if code(switched(w, x, y, [mu[t] for t in sub])) in S:
                            found = list(sub); break
                    if found is not None: break
                if found is None: ok = False; break
                entries.append((mu, found))
            if ok:
                cert.append((w, x, y, entries)); S.add(code(w)); changed = True; break
missing = [w for w in adm if code(w) not in S]
print(f"closure certificate words: {len(cert)}; missing admissible: {len(missing)}")
assert not missing, "not D-reducible"

def L_(xs): return '[' + ', '.join(str(x) for x in xs) + ']'
def LP(ps): return '[' + ', '.join(f'({a}, {b})' for a, b in ps) + ']'
supp_lines = ',\n   '.join(f'({L_(w)}, {L_(supp[w])})' for w in supp)
cert_lines = ',\n   '.join(
    f'({L_(w)}, {x}, {y}, [' + ', '.join(f'({LP(mu)}, {L_(sub)})' for mu, sub in entries) + '])'
    for (w, x, y, entries) in cert)

lean = f'''import Mathlib

/-!
# D-reducibility of the flower patch F({s}; {','.join(map(str, outs))})

A flower patch: a central face of size {s} whose outer faces have sizes
{outs}; ring size {n} (one port per own boundary vertex of an outer face).
`supp` is the set of boundary colour words extendable to a proper
3-edge-colouring inside the patch, each certified by an explicit colouring.
The Kempe closure adds a word `w` when for some colour pair `(x,y)` and for
EVERY noncrossing perfect matching of the `x,y`-ports of `w` (the possible
exterior Kempe-chain pairings) some subset of chains can be switched to land
in the set so far; the checker enumerates the matchings itself and the
certificate supplies the subsets.  The module checks that the closure
contains every admissible word (all three colour counts of equal parity):
the patch is D-reducible, hence cannot occur in a least counterexample.
All facts are decided by the kernel from the data; sets are bitmasks.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

namespace Mettapedia.GraphTheory.{modname}

def ring : Nat := {n}
/-- vertices `0..{nv-1}`; port `i` is node `{PORT}+i` -/
def edges : List (Nat × Nat) := {LP(edges)}
def portNode (i : Nat) : Nat := {PORT} + i

def code (w : List Nat) : Nat := (w.foldr (fun c acc => c + 3 * acc) 0)
def mem (S : Nat) (c : Nat) : Bool := (S >>> c) % 2 == 1
def ins (S : Nat) (c : Nat) : Nat := S ||| (1 <<< c)

def edgeAt (k : Nat) : Nat × Nat := edges.getD k (0, 0)
def incidentEdges (v : Nat) : List Nat :=
  (List.range edges.length).filter fun k => (edgeAt k).1 == v || (edgeAt k).2 == v

/-- a colouring is proper at every internal vertex and matches the word at the ports -/
def colouringOk (w : List Nat) (col : List Nat) : Bool :=
  col.length == edges.length && col.all (· < 3) && w.length == ring &&
  (List.range {nv}).all (fun v =>
    let cs := (incidentEdges v).map fun k => col.getD k 9
    cs.length == 3 && cs.eraseDups.length == 3) &&
  (List.range ring).all fun i =>
    (incidentEdges (portNode i)).all fun k => col.getD k 9 == w.getD i 9

def suppCert : List (List Nat × List Nat) :=
  [{supp_lines}]

/-- noncrossing perfect matchings of a sorted position list, in a fixed order -/
def nc : Nat → List Nat → List (List (Nat × Nat))
  | 0, _ => []
  | _, [] => [[]]
  | f + 1, a :: rest =>
      (List.range rest.length).foldr (fun m acc =>
        if m % 2 == 0 then
          let b := rest.getD m 0
          let inside := rest.take m
          let outside := rest.drop (m + 1)
          ((nc f inside).flatMap fun mi => (nc f outside).map fun mo => (a, b) :: (mi ++ mo)) ++ acc
        else acc) []

def flipAt (w : List Nat) (p x y : Nat) : List Nat :=
  (List.range w.length).map fun i =>
    let c := w.getD i 9
    if i == p then (if c == x then y else x) else c

def switched (w : List Nat) (x y : Nat) (chains : List (Nat × Nat)) : List Nat :=
  chains.foldl (fun acc (i, j) => flipAt (flipAt acc i x y) j x y) w

def pairPorts (w : List Nat) (x y : Nat) : List Nat :=
  (List.range ring).filter fun i => w.getD i 9 == x || w.getD i 9 == y

/-- the closure certificate: (word, x, y, per-matching chain subsets) -/
def closureCert : List (List Nat × Nat × Nat × List (List (Nat × Nat) × List Nat)) :=
  [{cert_lines}]

def admissible (w : List Nat) : Bool :=
  (w.count 0) % 2 == (w.count 1) % 2 && (w.count 1) % 2 == (w.count 2) % 2

def suppSet : Nat := suppCert.foldl (fun S wc => ins S (code wc.1)) 0

def suppCertOk : Bool := suppCert.all fun wc => colouringOk wc.1 wc.2

/-- process one closure entry: all matchings enumerated must be listed, each with a landing subset -/
def entryOk (S : Nat) (e : List Nat × Nat × Nat × List (List (Nat × Nat) × List Nat)) : Bool :=
  let (w, x, y, ms) := e
  x < 3 && y < 3 && x != y && w.length == ring && admissible w &&
  (ms.map (·.1)) == nc ring (pairPorts w x y) &&
  ms.all fun (mu, sub) =>
    mem S (code (switched w x y (sub.map fun t => mu.getD t (0, 0))))

def closureRun : Nat × Bool :=
  closureCert.foldl (fun (S, ok) e => (ins S (code e.1), ok && entryOk S e)) (suppSet, true)

def decodeWord (c : Nat) : List Nat := (List.range ring).map fun i => (c / 3 ^ i) % 3

def allAdmissibleCovered (S : Nat) : Bool :=
  (List.range (3 ^ ring)).all fun c => !(admissible (decodeWord c)) || mem S c

def dReducible : Bool :=
  suppCertOk && closureRun.2 && allAdmissibleCovered closureRun.1

theorem dReducible_true : dReducible = true := by decide

end Mettapedia.GraphTheory.{modname}
'''
out = f'/home/oruzi/repos/MeTTapedia-4cplab/lean/mettapedia/Mettapedia/GraphTheory/{modname}.lean'
open(out, 'w').write(lean)
print("wrote", out, "size", len(lean))

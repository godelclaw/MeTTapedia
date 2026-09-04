"""Generate the Lean witness module for the C30 non-polar good-word closed web
with a same-sector nested chord pair (certificate from
goodword_realgraph_nest_C30.json), reusing the census module's verifiers.

Run with the v24 toolchain on PYTHONPATH."""
import json, re
from collections import defaultdict
import sector_alternation_lab as L
from lift_lab import components_of

CENSUS = '/home/oruzi/repos/MeTTapedia-4cplab/lean/mettapedia/Mettapedia/GraphTheory/ClosedWebSectorNestingWitness.lean'
OUT = '/home/oruzi/repos/MeTTapedia-4cplab/lean/mettapedia/Mettapedia/GraphTheory/GoodWordRealGraphNestingWitness.lean'

cert = json.load(open('goodword_realgraph_nest_C30.json'))['C30']['certificate']
p1, p2 = cert['caps']; col = cert['coloring']
nbrs, edges, faces, pent = L.build_small('C30')
tedges, v2e, spokes, caps = L.two_hole_tangle(nbrs, edges, faces, p1, p2)
assert len(tedges) == len(col)
pend = set(caps['outer']) | set(caps['inner'])
ok, _ = L.closure_test(col, tedges, v2e, spokes); assert ok
a, rails = L.rails_of(col, tedges, v2e, spokes, len(nbrs), pend); assert a is not None and len(rails) == 2
r = L.analyze_web(col, tedges, v2e, spokes, caps, len(nbrs), faces, {p1, p2})
assert r['violations'] and r['n_sectors'] == 2
(outer, inner) = r['violations'][0]  # (rail, lo, hi, sec, sec2, eid)
assert outer[0] == inner[0]
rail_idx = outer[0]
rail1 = rails[rail_idx]; rail0 = rails[1 - rail_idx]
e_out, e_in = outer[5], inner[5]
ftang = L.tangle_faces(None, tedges, {p1, p2}, faces)
rail_eids = {ei for ei in range(len(tedges)) if col[ei] != a}
spoke_eids = set(spokes['outer']) | set(spokes['inner'])
sector, e2f = L.face_sectors(tedges, ftang, rail_eids, spoke_eids)
roots = sorted(set(sector.values())); assert len(roots) == 2
labels = [roots.index(sector[f]) for f in range(len(ftang))]
comps = components_of(col, tedges, v2e, len(tedges))
strands = defaultdict(list)
for (pair, ce, cv) in comps:
    strands[tuple(sorted(pair))].append(sorted(ce))
for k in strands: strands[k].sort()
bad = [d for d in r['drain_bad'] if d[0] == e_out]
assert bad, "outer chord must fail drainage"
w1 = bad[0][2]
innerWord = [col[e] for e in spokes['inner']]

def L_(xs): return '[' + ', '.join(str(x) for x in xs) + ']'
def LL(xss): return '[' + ', '.join(L_(x) for x in xss) + ']'
def LP(ps): return '[' + ', '.join(f'({u}, {v})' for u, v in ps) + ']'

src = open(CENSUS).read()
verif = src[src.index('/-! ## Elementary accessors'):src.index('/-! ## The kernel-checked facts')]

header = f'''import Mathlib

/-!
# A real-graph good-word closed web refuting sector-alternation drainage

The closed-web graph of Addendum XXVII(i) is a totally closed web at a
good word.  This module records one such web on one of the manuscript's
own census graphs — the C30 (5,0)-tube with the two vertex-disjoint
pentagon caps {p1} and {p2} (not the polar pair) — and checks in the kernel,
from explicit list data, that:

* the colouring is proper and totally closed (Addendum VIII), with the
  Kempe strands supplied and verified as the component partition;
* the inner word `{' '.join(map(str, innerWord))}` is a good word: three consecutive
  majority spokes and one spoke of each other colour;
* the two rails (the non-`a` colours) are pendant-to-pendant paths
  covering every internal vertex, and the face labelling is exactly the
  two-sector partition of the annulus cut along the rails;
* on rail 1 the chord with edge id `{e_out}` strictly contains the chord with
  edge id `{e_in}` and both lie in the same sector, and the interior vertex
  `{w1}` of the outer chord sends its `α`-edge (edge `{e_in}`) strictly inside
  the outer chord's sub-arc in the same sector; hence the universal
  drainage predicate is `false`.

The verifiers are those of `ClosedWebSectorNestingWitness`; only the
specimen differs.  The specimen was found by an exhaustive sweep of all
vertex-disjoint cap pairs of C30 (60 of the 120 good-word closed webs
carry such a nest).
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Mettapedia.GraphTheory.GoodWordRealGraphNestingWitness

/-! ## The specimen -/

/-- Tangle edges of the C30 two-hole tangle at caps {p1},{p2}, indexed `0..{len(tedges)-1}`. -/
def tedges : List (Nat × Nat) := {LP(tedges)}

/-- The closed-web colouring (colour of edge `i`). -/
def color : List Nat := {L_(col)}

/-- The distinguished colour `a` (the majority colour of the good word). -/
def aColor : Nat := {a}

/-- Inner-hole and outer-hole spoke edges (in the cyclic order of the cap), and the pendant vertices. -/
def innerSpokes : List Nat := {L_(spokes['inner'])}
def outerSpokes : List Nat := {L_(spokes['outer'])}
def innerCap : List Nat := {L_(caps['inner'])}
def outerCap : List Nat := {L_(caps['outer'])}

/-- The two rails (vertex sequences), pendant to pendant; the nest lies on `rail1`. -/
def rail0 : List Nat := {L_(rail0)}
def rail1 : List Nat := {L_(rail1)}

/-- The {len(ftang)} annulus faces, each as its list of tangle edge ids. -/
def faces : List (List Nat) := {LL(ftang)}

/-- The claimed sector label of each face. -/
def sectorLabel : List Nat := {L_(labels)}

'''
strand_defs = f'''
/-- The strands of each colour pair, as lists of edge ids. -/
def strands01 : List (List Nat) := {LL(strands[(0, 1)])}
def strands02 : List (List Nat) := {LL(strands[(0, 2)])}
def strands12 : List (List Nat) := {LL(strands[(1, 2)])}
'''
# splice strand data into the verifier block in place of the census strands
verif = re.sub(r'/-- The strands of each colour pair, as lists of edge ids\. -/\ndef strands01 : List \(List Nat\) :=\n(?:.*\n)*?def strands12 : List \(List Nat\) :=\n(?:.*\n)*?(?=\ndef strandsOf)', strand_defs.lstrip('\n'), verif)
assert 'def strands01 : List (List Nat) := [[' in verif, "strand splice failed"

goodword = '''
/-! ## The good word -/

def cyc (w : List Nat) (i : Nat) : Nat := w.getD (i % w.length) 99
/-- colours of the inner spokes in the cap's cyclic order -/
def innerWord : List Nat := innerSpokes.map colorAt
/-- three consecutive spokes of the majority colour, one spoke of each other colour -/
def goodWord (w : List Nat) : Bool :=
  w.length == 5 && w.count aColor == 3 &&
  ((List.range 3).filter fun c => c != aColor).all (fun c => w.count c == 1) &&
  (List.range 5).any fun s => cyc w s == aColor && cyc w (s + 1) == aColor && cyc w (s + 2) == aColor
'''

theorems = f'''
/-! ## The kernel-checked facts -/

theorem isProper_true : isProper = true := by decide
theorem strandsValid_true : strandsValid = true := by decide
theorem totallyClosed_true : totallyClosed = true := by decide
theorem innerWord_eq : innerWord = {L_(innerWord)} := by decide
theorem innerWord_good : goodWord innerWord = true := by decide
theorem rails_true :
    (isRailPath rail0 && isRailPath rail1 && railsCover) = true := by decide
theorem sectors_true :
    (labelsRespectRails && labelClassesConnected) = true := by decide

/-- The two chords are nested on rail 1 and lie in one sector. -/
theorem nested_same_sector :
    (isRail1Chord {e_out} && isRail1Chord {e_in} &&
      chordLo {e_out} < chordLo {e_in} && chordHi {e_in} < chordHi {e_out} &&
      chordFacesSameSector {e_out} && chordFacesSameSector {e_in} &&
      chordSector {e_out} == chordSector {e_in}) = true := by decide

/-- **Universal drainage fails at a good word on a real graph**: chord `{e_out}`
does not drain — its interior vertex `{w1}` sends its `α`-edge `{e_in}` inside
the disk, in the same sector. -/
theorem universalDrainage_false : universalDrainage = false := by decide
theorem chord{e_out}_not_drains : chordDrains {e_out} = false := by decide

end Mettapedia.GraphTheory.GoodWordRealGraphNestingWitness
'''
open(OUT, 'w').write(header + verif + goodword + theorems)
print("wrote", OUT, "| caps", (p1, p2), "a", a, "chords", e_out, ">", e_in, "w1", w1, "innerWord", innerWord, "faces", len(ftang), "labels", labels)

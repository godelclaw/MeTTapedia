#!/usr/bin/env python3
"""Emit a presented configuration from a tangle JSON, with the kernel checks that instantiate
the end-to-end exclusion theorem against a sealed enumerated certificate.

The JSON has `n` ports, `nv` vertices and `edges` (pairs of vertices, a port end written
["p", i]).  Every vertex must be cubic counting its port.  Slot order at a vertex is
arbitrary: the configuration's rotation is irrelevant to its support and to the embedding
hypothesis.

The base words of the certificate are verified by the enumerator in chunks (the kernel's
cache grows with every run, so each chunk is one theorem); the cap's words are covered by the
base or the nodes, checked in chunks of boundary numerals.

Usage: gen_presented_config_lean.py tangle.json Name CertModule [--chunk c] [--cover-chunk d]
  Name        the Lean namespace of the configuration (e.g. Flower8)
  CertModule  the sealed certificate namespace (e.g. Flower8Enum), providing base, cert, ok
"""
import sys, os, json
args = sys.argv[1:]
tpath, name, certmod = args[0], args[1], args[2]
CHUNK = int(args[args.index('--chunk') + 1]) if '--chunk' in args else 10
COVER = int(args[args.index('--cover-chunk') + 1]) if '--cover-chunk' in args else 250
d = json.load(open(tpath))
n, nv, edges = d['n'], d['nv'], d['edges']
interior = [tuple(e) for e in edges if not any(isinstance(z, list) for z in e)]
ports = {}
for e in edges:
    if any(isinstance(z, list) for z in e):
        p = [z for z in e if isinstance(z, list)][0][1]
        v = [z for z in e if not isinstance(z, list)][0]
        ports[p] = v
N = len(interior)
assert sorted(ports) == list(range(n))
slots = {v: [] for v in range(nv)}          # slot list per vertex: ('edge', e, b) or ('port', i)
for k, (u, v) in enumerate(interior):
    slots[u].append(('edge', k, False))
    slots[v].append(('edge', k, True))
for i in range(n):
    slots[ports[i]].append(('port', i))
for v in range(nv):
    assert len(slots[v]) == 3, (v, slots[v])
endPos = {}
portPos = {}
for v in range(nv):
    for s, sl in enumerate(slots[v]):
        if sl[0] == 'edge':
            endPos[(sl[1], sl[2])] = (v, s)
        else:
            portPos[sl[1]] = (v, s)


def slot_lean(sl):
    return f'Slot.edge {sl[1]}' if sl[0] == 'edge' else f'Slot.port {sl[1]}'


tri_arms = '\n'.join(f'    | {v}, {s} => {slot_lean(slots[v][s])}' for v in range(nv) for s in range(3))
end_arms = '\n'.join(f'    | {e}, {str(b).lower()} => ({endPos[(e, b)][0]}, {endPos[(e, b)][1]})'
                     for e in range(N) for b in (False, True))
port_arms = '\n'.join(f'    | {i} => ({portPos[i][0]}, {portPos[i][1]})' for i in range(n))

# the base list length is needed for the chunk count; read it from the certificate data module
lab = os.path.dirname(os.path.abspath(__file__))
data_path = os.path.join(lab, '..', '..', 'Mettapedia', 'GraphTheory', 'FourColor', certmod + 'Data.lean')
src = open(data_path).read()
start = src.index('def base : List (Word')
end = src.index(']', start)
base_len = src[start:end].count('\n  w ')
chunks = (base_len + CHUNK - 1) // CHUNK
words = 3 ** n
cchunks = (words + COVER - 1) // COVER

base_theorems = '\n'.join(
    f'set_option maxRecDepth 100000 in\nset_option maxHeartbeats 0 in\n'
    f'theorem base_chunk_{j} : (({certmod}.base.drop ({CHUNK} * {j})).take {CHUNK}).all '
    f'(fun u => K.acceptsWord u) = true := by\n  decide +kernel\n'
    for j in range(chunks))
base_cases = '\n'.join(f'  · exact List.all_eq_true.1 base_chunk_{j} u hj' for j in range(chunks))

WX = f'(fun i => ⟨wordOf {n} X i, wordOf_ne_zero {n} X i⟩ : Word {n})'
cover_pred = (f'fun X => !(ngon {n}).accepts (TubeSlab.Presented.Pres.inWord X) || '
              f'decide ({WX} ∈ {certmod}.base) || '
              f'decide ({WX} ∈ {certmod}.cert.nodes.map fun t => t.1)')
cover_theorems = '\n'.join(
    f'set_option maxRecDepth 100000 in\nset_option maxHeartbeats 0 in\n'
    f'theorem cover_chunk_{j} : (((List.range {words}).drop ({COVER} * {j})).take {COVER}).all\n'
    f'    ({cover_pred}) = true := by\n  decide +kernel\n'
    for j in range(cchunks))
cover_cases = '\n'.join(f'  · exact cover_of_chunk cover_chunk_{j} X hj hacc' for j in range(cchunks))

base_lean = f'''import Mettapedia.GraphTheory.FourColor.CapEmbedding
import Mettapedia.GraphTheory.FourColor.NgonCap
import Mettapedia.GraphTheory.FourColor.{certmod}

/-!
# The configuration `{os.path.basename(tpath)}` is excluded from a least counterexample

The configuration as a presentation ({nv} vertices, {N} interior edges, ring {n}); the
sealed certificate `{certmod}` has every base word verified by the enumerator on the
configuration (in chunks of {CHUNK}), and the {n}-gon cap's words are covered by the base or
the certificate nodes (in chunks of {COVER} boundary numerals).  With the cap's disc check,
`false_of_certificate'` applies.
-/

namespace Mettapedia.GraphTheory.FourColor.KempeDerivation
namespace PresentedCap
namespace {name}

open GoertzelV24OpenTangleComposition GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24ComplementaryShoreBoundaryOrder GoertzelV24DeletedRegionRotationSplice
open GoertzelV24RetainedRegionBoundaryOrder GoertzelV24RotationCutDartDecomposition
open GoertzelV24TwoEdgeCutMinimality GoertzelV24VertexSideOpenTangle SimpleGraphDartRotation
open CapEmbedding

/-- the configuration -/
def K : Pres {nv} {N} {n} where
  tri v s := match v, s with
{tri_arms}
    | _, _ => Slot.edge 0
  endPos e b := match e, b with
{end_arms}
    | _, _ => (0, 0)
  portPos i := match i with
{port_arms}
    | _ => (0, 0)

set_option maxRecDepth 100000 in
theorem valid : K.Valid := by decide +kernel

/-! ## Every base word is a support word of the configuration -/

{base_theorems}
set_option maxRecDepth 100000 in
theorem base_length : {certmod}.base.length = {base_len} := by decide +kernel

theorem base_accepts : ∀ u ∈ {certmod}.base, K.acceptsWord u = true := by
  intro u hu
  obtain ⟨j, hj⟩ := mem_take_drop_of_mem hu {CHUNK} (by norm_num)
  have hlt := lt_of_mem_take_drop hj
  rw [base_length] at hlt
  have : j < {chunks} := by omega
  interval_cases j
{base_cases}

end {name}
end PresentedCap
end Mettapedia.GraphTheory.FourColor.KempeDerivation
'''

cfg_lean = f'''import Mettapedia.GraphTheory.FourColor.{name}Base
import Mettapedia.GraphTheory.FourColor.NgonCap

/-! The {n}-gon cap's words are covered by the base or the certificate nodes (in chunks of
{COVER} boundary numerals); with the base verification and the cap's disc check,
`false_of_certificate'` excludes the configuration. -/

namespace Mettapedia.GraphTheory.FourColor.KempeDerivation
namespace PresentedCap
namespace {name}

open GoertzelV24OpenTangleComposition GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24ComplementaryShoreBoundaryOrder GoertzelV24DeletedRegionRotationSplice
open GoertzelV24RetainedRegionBoundaryOrder GoertzelV24RotationCutDartDecomposition
open GoertzelV24TwoEdgeCutMinimality GoertzelV24VertexSideOpenTangle SimpleGraphDartRotation
open CapEmbedding ZigzagRing TubeRingOrbit

/-! ## Every word of the cap is a base word or a certificate node -/

theorem cover_of_chunk {{l : List Nat}}
    (h : l.all ({cover_pred}) = true)
    (X : Nat) (hX : X ∈ l) (hacc : (ngon {n}).accepts (TubeSlab.Presented.Pres.inWord X) = true) :
    {WX} ∈ {certmod}.base ∨ {WX} ∈ {certmod}.cert.nodes.map fun t => t.1 := by
  have := List.all_eq_true.1 h X hX
  simp only [hacc, Bool.not_true, Bool.false_or, Bool.or_eq_true, decide_eq_true_eq] at this
  exact this

{cover_theorems}
theorem cover : ∀ w ∈ (ngon {n}).capWords Ngon.valid{n},
    w ∈ {certmod}.base ∨ w ∈ {certmod}.cert.nodes.map fun t => t.1 := by
  intro w hw
  unfold Pres.capWords at hw
  simp only [List.mem_map, List.mem_filter, List.mem_range] at hw
  obtain ⟨X, ⟨hX, hacc⟩, rfl⟩ := hw
  obtain ⟨j, hj⟩ := mem_take_drop_of_mem (List.mem_range.2 hX) {COVER} (by norm_num)
  have hlt := lt_of_mem_take_drop hj
  rw [List.length_range] at hlt
  have : j < {cchunks} := by omega
  interval_cases j
{cover_cases}

variable {{V : Type}} [Fintype V] [DecidableEq V] {{G : SimpleGraph V}} [DecidableRel G.Adj]

local instance graphEdgeSetFintype : Fintype G.edgeSet :=
  SimpleGraph.fintypeEdgeSet G

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- **no least counterexample contains this configuration as a disk** -/
theorem excluded
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (deleted : Finset V)
    (hretainedConnected :
      (G.induce {{vertex | deletedRegionKeep deleted vertex}}).Connected)
    (hdeletedConnected :
      (G.induce {{vertex | ¬ deletedRegionKeep deleted vertex}}).Connected)
    (outerRetained : RetainedDart graphData.toRotationSystem (deletedRegionKeep deleted))
    (outerDeleted : RetainedDart graphData.toRotationSystem (deletedSideKeep deleted))
    (order : Fin {n} ≃ BoundaryDart graphData.toRotationSystem (deletedRegionKeep deleted))
    (hsuccessor : order.permCongr (finRotate {n}) =
      retainedRegionBoundarySuccessor graphData.toRotationSystem (deletedRegionKeep deleted))
    (iso : OpenTangleIso
      (ofVertexSide graphData.toRotationSystem (deletedSideKeep deleted) outerDeleted)
      (K.toCap valid))
    (hports : ∀ b, iso.boundary (complementBoundaryAlphaEquiv graphData.toRotationSystem
      deleted b) = order.symm b) :
    False :=
  false_of_certificate' graphData minimal deleted hretainedConnected hdeletedConnected
    outerRetained outerDeleted (by norm_num) order hsuccessor K valid iso hports
    (ngon {n}) Ngon.valid{n} Ngon.disc{n} (by norm_num) {certmod}.base base_accepts
    {certmod}.cert {certmod}.ok cover

end {name}
end PresentedCap
end Mettapedia.GraphTheory.FourColor.KempeDerivation
'''
out = os.path.join(lab, '..', '..', 'Mettapedia', 'GraphTheory', 'FourColor', name + 'Base.lean')
open(out, 'w').write(base_lean)
out2 = os.path.join(lab, '..', '..', 'Mettapedia', 'GraphTheory', 'FourColor', name + 'Config.lean')
open(out2, 'w').write(cfg_lean)
print(f'wrote {out} and {out2}: {nv} vertices, {N} edges, ring {n}, base {base_len} words in {chunks} chunks, '
      f'cover {words} numerals in {cchunks} chunks')

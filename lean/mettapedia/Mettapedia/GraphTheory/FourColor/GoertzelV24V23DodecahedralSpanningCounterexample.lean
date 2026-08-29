import Mettapedia.GraphTheory.FourColor.CAP5DodecahedralRouteData
import Mathlib.Algebra.Module.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Ring

/-!
# A positive-depth dodecahedral counterexample to v23 Theorem 4.9

This file tests the final Definition 4.8 and Theorem 4.9 in Ben Goertzel's
`4cp_proof_v23` on the dodecahedron with the interiors of two disjoint
pentagonal faces removed.  The ten remaining faces are the internal faces and
ten vertices lie off the two boundary pentagons.

The chosen Tait coloring has one connected bicolored component for each color
pair.  Consequently every source Kempe move is a global color transposition,
and its exact Kempe closure consists of global relabelings.  A linear
functional annihilates every literal Definition-4.8 generator from that
closure but evaluates to one on an explicit boundary-zero relative path.

Thus the spanning conclusion of the literal v23 Theorem 4.9 fails even in a
positive-depth two-pentagon geometry.  This does not refute later repaired
profile or weak-L2 statements.
-/

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelV24V23DodecahedralSpanningCounterexample

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open SimpleGraph
open DodecahedralCAP5RouteData

abbrev SourceColor := Fin 3

def sourceEdgeColor (e : dodecahedralGraph.edgeSet) : SourceColor :=
  if dodecahedralEdgeColor e = red then 0
  else if dodecahedralEdgeColor e = blue then 1
  else 2

theorem sourceEdgeColor_ne_of_lineGraph_adj
    {e f : dodecahedralGraph.edgeSet}
    (hadj : dodecahedralGraph.lineGraph.Adj e f) :
    sourceEdgeColor e ≠ sourceEdgeColor f := by
  decide +revert

def sourceTaitColoring : dodecahedralGraph.EdgeColoring SourceColor :=
  Coloring.mk sourceEdgeColor (by
    intro e f hadj
    exact sourceEdgeColor_ne_of_lineGraph_adj hadj)

def BicoloredConnected
    (C : dodecahedralGraph.EdgeColoring SourceColor) : Prop :=
  ∀ a b, a ≠ b → (C.bicoloredSubgraph a b).Preconnected

noncomputable instance bicoloredSetFintype
    (C : dodecahedralGraph.EdgeColoring SourceColor) (a b : SourceColor) :
    Fintype (C.bicoloredSet a b) := Fintype.ofFinite _

instance bicoloredSetDecidable
    (C : dodecahedralGraph.EdgeColoring SourceColor) (a b : SourceColor) :
    DecidablePred (C.bicoloredSet a b) := by
  intro e
  change Decidable (C e = a ∨ C e = b)
  infer_instance

/-- A bounded path predicate whose intermediate vertices remain in `selected`.
It is used only to turn the three explicit finite path certificates into
ordinary graph reachability. -/
def ReachWithinSet {V : Type*} (G : SimpleGraph V) (selected : Set V) :
    Nat → V → V → Prop
  | 0, u, v => u = v
  | n + 1, u, v =>
      u = v ∨ ∃ w, selected w ∧ G.Adj u w ∧ ReachWithinSet G selected n w v

instance reachWithinSetDecidable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (selected : Set V)
    [DecidablePred selected] :
    ∀ n u v, Decidable (ReachWithinSet G selected n u v) := by
  intro n
  induction n with
  | zero => intro u v; simp only [ReachWithinSet]; infer_instance
  | succ n ih => intro u v; simp only [ReachWithinSet]; infer_instance

theorem induce_reachable_of_reachWithinSet
    {V : Type*} {G : SimpleGraph V} {selected : Set V}
    {n : Nat} {u v : V} (h : ReachWithinSet G selected n u v)
    (hu : selected u) (hv : selected v) :
    (G.induce selected).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
  induction n generalizing u with
  | zero =>
      have huv : u = v := h
      subst v
      exact SimpleGraph.Reachable.refl _
  | succ n ih =>
      rcases h with rfl | ⟨w, hw, huw, hwv⟩
      · exact SimpleGraph.Reachable.refl _
      · exact (show (G.induce selected).Adj ⟨u, hu⟩ ⟨w, hw⟩ from huw).reachable.trans
          (ih hwv hw)

def root01 : sourceTaitColoring.bicoloredSet 0 1 := by
  refine ⟨dod0_1, ?_⟩
  left
  decide

theorem root01_path
    (e : dodecahedralGraph.edgeSet)
    (he : e ∈ sourceTaitColoring.bicoloredSet 0 1) :
    ReachWithinSet dodecahedralGraph.lineGraph
      (sourceTaitColoring.bicoloredSet 0 1) 20 root01.1 e := by
  rcases dodecahedral_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [Coloring.mem_bicoloredSet] at he
    first
    | contradiction
    | decide

theorem bicoloredPreconnected_comm
    (C : dodecahedralGraph.EdgeColoring SourceColor) (a b : SourceColor)
    (h : (C.bicoloredSubgraph a b).Preconnected) :
    (C.bicoloredSubgraph b a).Preconnected := by
  let swapHom : C.bicoloredSubgraph a b →g C.bicoloredSubgraph b a :=
    { toFun := fun e => ⟨e.1, e.2.symm⟩
      map_rel' := by intro u v huv; exact huv }
  exact h.map swapHom (by
    rintro ⟨e, he⟩
    exact ⟨⟨e, he.symm⟩, rfl⟩)

theorem preconnected01 :
    (sourceTaitColoring.bicoloredSubgraph 0 1).Preconnected := by
  intro u v
  have hu := induce_reachable_of_reachWithinSet
    (root01_path u.1 u.2) root01.2 u.2
  have hv := induce_reachable_of_reachWithinSet
    (root01_path v.1 v.2) root01.2 v.2
  exact hu.symm.trans hv

def root02 : sourceTaitColoring.bicoloredSet 0 2 := by
  refine ⟨dod0_1, ?_⟩
  left
  decide

theorem root02_path
    (e : dodecahedralGraph.edgeSet)
    (he : e ∈ sourceTaitColoring.bicoloredSet 0 2) :
    ReachWithinSet dodecahedralGraph.lineGraph
      (sourceTaitColoring.bicoloredSet 0 2) 20 root02.1 e := by
  rcases dodecahedral_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [Coloring.mem_bicoloredSet] at he
    first
    | contradiction
    | decide

theorem preconnected02 :
    (sourceTaitColoring.bicoloredSubgraph 0 2).Preconnected := by
  intro u v
  have hu := induce_reachable_of_reachWithinSet
    (root02_path u.1 u.2) root02.2 u.2
  have hv := induce_reachable_of_reachWithinSet
    (root02_path v.1 v.2) root02.2 v.2
  exact hu.symm.trans hv

def root12 : sourceTaitColoring.bicoloredSet 1 2 := by
  refine ⟨dod0_10, ?_⟩
  left
  decide

theorem root12_path
    (e : dodecahedralGraph.edgeSet)
    (he : e ∈ sourceTaitColoring.bicoloredSet 1 2) :
    ReachWithinSet dodecahedralGraph.lineGraph
      (sourceTaitColoring.bicoloredSet 1 2) 20 root12.1 e := by
  rcases dodecahedral_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [Coloring.mem_bicoloredSet] at he
    first
    | contradiction
    | decide

theorem preconnected12 :
    (sourceTaitColoring.bicoloredSubgraph 1 2).Preconnected := by
  intro u v
  have hu := induce_reachable_of_reachWithinSet
    (root12_path u.1 u.2) root12.2 u.2
  have hv := induce_reachable_of_reachWithinSet
    (root12_path v.1 v.2) root12.2 v.2
  exact hu.symm.trans hv

theorem sourceTaitColoring_bicoloredConnected :
    BicoloredConnected sourceTaitColoring := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all
  · exact preconnected01
  · exact preconnected02
  · exact bicoloredPreconnected_comm sourceTaitColoring 0 1 preconnected01
  · exact preconnected12
  · exact bicoloredPreconnected_comm sourceTaitColoring 0 2 preconnected02
  · exact bicoloredPreconnected_comm sourceTaitColoring 1 2 preconnected12

def globalRelabel (σ : Equiv.Perm SourceColor) :
    dodecahedralGraph.EdgeColoring SourceColor :=
  dodecahedralGraph.lineGraph.recolorOfEquiv σ sourceTaitColoring

@[simp] theorem globalRelabel_apply (σ : Equiv.Perm SourceColor)
    (e : dodecahedralGraph.edgeSet) :
    globalRelabel σ e = σ (sourceTaitColoring e) := rfl

theorem globalRelabel_bicoloredSet
    (σ : Equiv.Perm SourceColor) (a b : SourceColor) :
    (globalRelabel σ).bicoloredSet a b =
      sourceTaitColoring.bicoloredSet (σ.symm a) (σ.symm b) := by
  ext e
  simp only [Coloring.mem_bicoloredSet, globalRelabel_apply]
  constructor
  · rintro (h | h)
    · exact Or.inl (σ.injective (by simpa using h))
    · exact Or.inr (σ.injective (by simpa using h))
  · rintro (h | h)
    · exact Or.inl (by simpa using congrArg σ h)
    · exact Or.inr (by simpa using congrArg σ h)

theorem globalRelabel_bicoloredConnected (σ : Equiv.Perm SourceColor) :
    BicoloredConnected (globalRelabel σ) := by
  intro a b hab
  change (dodecahedralGraph.lineGraph.induce
    ((globalRelabel σ).bicoloredSet a b)).Preconnected
  rw [globalRelabel_bicoloredSet]
  exact sourceTaitColoring_bicoloredConnected _ _
    (fun h => hab (σ.symm.injective h))

theorem kempeComponentSet_eq_bicoloredSet
    (C : dodecahedralGraph.EdgeColoring SourceColor)
    {a b : SourceColor}
    (hpre : (C.bicoloredSubgraph a b).Preconnected)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent) :
    C.kempeComponentSet a b K = C.bicoloredSet a b := by
  ext e
  constructor
  · exact C.mem_bicoloredSet_of_mem_kempeComponentSet
  · intro he
    exact ⟨he, hpre.subsingleton_connectedComponent.elim _ _⟩

theorem swapOnKempeComponent_eq_globalSwap
    (C : dodecahedralGraph.EdgeColoring SourceColor)
    (a b : SourceColor)
    (hpre : (C.bicoloredSubgraph a b).Preconnected)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent) :
    C.swapOnKempeComponent a b K =
      dodecahedralGraph.lineGraph.recolorOfEquiv (Equiv.swap a b) C := by
  ext e
  by_cases he : e ∈ C.bicoloredSet a b
  · rw [C.swapOnKempeComponent_apply_of_mem]
    · rfl
    · rw [kempeComponentSet_eq_bicoloredSet C hpre K]
      exact he
  · rw [C.swapOnKempeComponent_apply_of_not_mem]
    · exact congrArg Fin.val (Equiv.swap_apply_of_ne_of_ne
        (fun h => he (Or.inl h)) (fun h => he (Or.inr h))).symm
    · rwa [kempeComponentSet_eq_bicoloredSet C hpre K]

theorem globalRelabel_after_swap
    (σ : Equiv.Perm SourceColor) (a b : SourceColor) :
    dodecahedralGraph.lineGraph.recolorOfEquiv (Equiv.swap a b)
        (globalRelabel σ) =
      globalRelabel (σ.trans (Equiv.swap a b)) := by
  ext e
  rfl

/-- Every coloring in the source's exact three-color Kempe closure is a global
relabeling of the displayed coloring. -/
theorem mem_edgeKempeClosure_exists_globalRelabel
    (C : dodecahedralGraph.EdgeColoring SourceColor)
    (hC : C ∈ dodecahedralGraph.EdgeKempeClosure sourceTaitColoring) :
    ∃ σ : Equiv.Perm SourceColor, C = globalRelabel σ := by
  induction hC with
  | refl =>
      exact ⟨Equiv.refl _, by ext e; rfl⟩
  | tail hreach hstep ih =>
      rcases ih with ⟨σ, rfl⟩
      rcases hstep with ⟨a, b, K, rfl⟩
      by_cases hab : a = b
      · subst b
        refine ⟨σ, ?_⟩
        ext e
        by_cases he : e ∈ (globalRelabel σ).kempeComponentSet a a K <;>
          simp [Coloring.swapOnKempeComponent] <;> rfl
      · refine ⟨σ.trans (Equiv.swap a b), ?_⟩
        rw [swapOnKempeComponent_eq_globalSwap
          (globalRelabel σ) a b (globalRelabel_bicoloredConnected σ a b hab) K]
        exact globalRelabel_after_swap σ a b

abbrev F₂ := ZMod 2
abbrev Pair := Fin 3
abbrev Coord := Fin 2
abbrev InternalFace := Fin 10
abbrev Chain := dodecahedralGraph.edgeSet → Coord → F₂

/-- The ten faces other than the two boundary pentagons numbered `0` and `6`. -/
def sourceFace : InternalFace → DodecahedralFace
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 3
  | ⟨3, _⟩ => 4
  | ⟨4, _⟩ => 5
  | ⟨5, _⟩ => 7
  | ⟨6, _⟩ => 8
  | ⟨7, _⟩ => 9
  | ⟨8, _⟩ => 10
  | ⟨9, _⟩ => 11

def onInternalFace (face : InternalFace)
    (edge : dodecahedralGraph.edgeSet) : Bool :=
  decide (edge ∈ dodecahedralFaceBoundary (sourceFace face))

/-- Pair 0 is `{0,1}`, pair 1 is `{0,2}`, and pair 2 is `{1,2}`. -/
def inPair (pair : Pair) (color : SourceColor) : Bool :=
  decide ((pair = 0 ∧ (color = 0 ∨ color = 1)) ∨
    (pair = 1 ∧ (color = 0 ∨ color = 2)) ∨
    (pair = 2 ∧ (color = 1 ∨ color = 2)))

def thirdColor (pair : Pair) : SourceColor :=
  if pair = 0 then 2 else if pair = 1 then 1 else 0

/-- Klein-four coordinates of the three nonzero colors. -/
def colorCoord (color : SourceColor) (coord : Coord) : F₂ :=
  if color = 0 then
    if coord = 0 then 1 else 0
  else if color = 1 then
    if coord = 0 then 0 else 1
  else
    1

/-- Ben's final Definition 4.8 after summing all boundary-hitting components:
the third-color coefficient on precisely the face edges in the selected pair. -/
def generator
    (coloring : dodecahedralGraph.EdgeColoring SourceColor)
    (face : InternalFace) (pair : Pair) : Chain :=
  fun edge coord =>
    if onInternalFace face edge && inPair pair (coloring edge) then
      colorCoord (thirdColor pair) coord
    else
      0

/-- A dual certificate found independently by row reduction. -/
def separator : Chain →ₗ[F₂] F₂ where
  toFun value :=
    value dod0_1 0 + value dod3_19 0 + value dod9_10 0 +
      value dod10_11 0 + value dod11_18 0 + value dod12_13 0 +
      value dod12_16 0 + value dod15_16 0 + value dod16_17 0 +
      value dod17_18 0 + value dod18_19 0
  map_add' left right := by
    simp only [Pi.add_apply]
    ring
  map_smul' scalar value := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem separator_generator_globalRelabel_eq_zero
    (σ : Equiv.Perm SourceColor) (face : InternalFace) (pair : Pair) :
    separator (generator (globalRelabel σ) face pair) = 0 := by
  fin_cases σ <;> fin_cases face <;> fin_cases pair <;>
    simp [separator, generator, onInternalFace, sourceFace, inPair, thirdColor,
      colorCoord, globalRelabel, sourceTaitColoring] <;> decide

def generatorSet : Set Chain :=
  {value | ∃ coloring ∈ dodecahedralGraph.EdgeKempeClosure sourceTaitColoring,
    ∃ face pair, value = generator coloring face pair}

def generatorSpan : Submodule F₂ Chain :=
  Submodule.span F₂ generatorSet

theorem generatorSpan_le_separator_ker :
    generatorSpan ≤ LinearMap.ker separator := by
  apply Submodule.span_le.mpr
  intro value hvalue
  rcases hvalue with ⟨coloring, hclosure, face, pair, rfl⟩
  rcases mem_edgeKempeClosure_exists_globalRelabel coloring hclosure with ⟨σ, rfl⟩
  exact LinearMap.mem_ker.mpr
    (separator_generator_globalRelabel_eq_zero σ face pair)

def boundaryEdges : Finset dodecahedralGraph.edgeSet :=
  dodecahedralFaceBoundary 0 ∪ dodecahedralFaceBoundary 6

def interiorVertices : Finset (Fin 20) :=
  {6, 7, 8, 9, 10, 11, 12, 13, 14, 18}

theorem boundary_face_zero_card : (dodecahedralFaceBoundary 0).card = 5 := by
  decide

theorem boundary_face_six_card : (dodecahedralFaceBoundary 6).card = 5 := by
  decide

theorem boundary_faces_disjoint :
    Disjoint (dodecahedralFaceBoundary 0) (dodecahedralFaceBoundary 6) := by
  decide

theorem interiorVertices_card : interiorVertices.card = 10 := by
  decide

theorem sourceFace_ne_boundary (face : InternalFace) :
    sourceFace face ≠ 0 ∧ sourceFace face ≠ 6 := by
  fin_cases face <;> decide

theorem exists_sourceFace_iff (face : DodecahedralFace) :
    (∃ internal : InternalFace, sourceFace internal = face) ↔
      face ≠ 0 ∧ face ≠ 6 := by
  fin_cases face <;> decide

theorem mem_interiorVertices_iff_not_boundaryVertex (vertex : Fin 20) :
    vertex ∈ interiorVertices ↔
      ¬ ∃ edge ∈ boundaryEdges, vertex ∈ (edge.1 : Sym2 (Fin 20)) := by
  fin_cases vertex <;> decide

noncomputable def incidentEdgesAt (vertex : Fin 20) :
    Finset dodecahedralGraph.edgeSet :=
  Finset.univ.filter fun edge => vertex ∈ (edge.1 : Sym2 (Fin 20))

noncomputable def kirchhoffAt
    (value : Chain) (vertex : Fin 20) (coord : Coord) : F₂ :=
  ∑ edge ∈ incidentEdgesAt vertex, value edge coord

/-- The source's `W₀`: zero on both boundary cycles and divergence-free at
every genuine interior vertex. -/
def BoundaryZero (value : Chain) : Prop :=
  (∀ edge ∈ boundaryEdges, value edge = 0) ∧
    ∀ vertex ∈ interiorVertices, ∀ coord, kirchhoffAt value vertex coord = 0

/-- A relative path from boundary vertex `0` to boundary vertex `19`, through
the interior vertices `10`, `11`, and `18`. -/
def witness : Chain :=
  fun edge coord =>
    if coord = 0 ∧
        edge ∈ ({dod0_10, dod10_11, dod11_18, dod18_19} :
          Finset dodecahedralGraph.edgeSet) then
      1
    else
      0

theorem witness_vanishes_boundary
    (edge : dodecahedralGraph.edgeSet) (hedge : edge ∈ boundaryEdges) :
    witness edge = 0 := by
  rcases dodecahedral_edge_eq edge with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    first
    | exfalso
      revert hedge
      decide
    | funext coord
      fin_cases coord <;> decide

theorem witness_kirchhoff
    (vertex : Fin 20) (hvertex : vertex ∈ interiorVertices) (coord : Coord) :
    kirchhoffAt witness vertex coord = 0 := by
  fin_cases vertex <;> fin_cases coord <;>
    simp [kirchhoffAt, incidentEdgesAt, witness, interiorVertices] at hvertex ⊢ <;>
    decide

theorem witness_boundaryZero : BoundaryZero witness := by
  exact ⟨witness_vanishes_boundary, witness_kirchhoff⟩

theorem separator_witness_eq_one : separator witness = 1 := by
  simp [separator, witness]
  decide

theorem witness_not_mem_generatorSpan : witness ∉ generatorSpan := by
  intro hwitness
  have hker := generatorSpan_le_separator_ker hwitness
  have hzero : separator witness = 0 := LinearMap.mem_ker.mp hker
  rw [separator_witness_eq_one] at hzero
  exact one_ne_zero hzero

/-- A positive-depth, two-pentagon counterexample to the literal spanning
conclusion of Goertzel v23, Theorem 4.9. -/
theorem exists_boundaryZero_not_mem_generatorSpan :
    ∃ value : Chain, BoundaryZero value ∧ value ∉ generatorSpan :=
  ⟨witness, witness_boundaryZero, witness_not_mem_generatorSpan⟩

end GoertzelV24V23DodecahedralSpanningCounterexample
end Mettapedia.GraphTheory.FourColor

import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedMeshColoringAtlas
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairCommonCoreDisagreementResidue

/-!
# The exact nine-site common-core residue on an ordered mesh row

The colouring-atlas obstruction says that arbitrary Tait colourings selected
at nine ordered row sites cannot agree on every common deletion.  The local
common-core theorem classifies the resulting disagreement while remaining
inside valid-pair Tait Kempe reachability.  This file composes the two results.

It does not prove wall exclusion.  Its three alternatives are the exact
remaining inputs for a two-dimensional coherence or replacement argument:
local branching, a boundary-reaching Kempe component, or a strict Tait repair.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OrderedMeshCommonCoreDisagreementResidue

open GoertzelV24AdjacentPairCommonCoreDisagreementResidue
open GoertzelV24AdjacentPairCommonCoreKempeBoundary
open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24MeshIsoperimetry
open GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24OrderedMeshColoringAtlas
open GoertzelV24OrderedMeshGlobalSites
open GoertzelV24RotationMultigraphAdapter
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u w

/-! ## Finite serial dynamics -/

/-- Following a chosen successor in a nonempty finite serial relation
eventually produces a nonempty directed cycle. -/
theorem exists_transGen_cycle_of_finite_serial
    {X : Type w} [Finite X] [Nonempty X]
    (relation : X → X → Prop)
    (serial : ∀ source, ∃ target, relation source target) :
    ∃ state, Relation.TransGen relation state state := by
  classical
  let next : X → X := fun source => Classical.choose (serial source)
  have nextStep (source : X) : relation source (next source) :=
    Classical.choose_spec (serial source)
  let initial : X := Classical.choice inferInstance
  obtain ⟨first, second, heq, hne⟩ :
      ∃ first second : Nat,
        next^[first] initial = next^[second] initial ∧ first ≠ second := by
    simpa [Function.Injective] using
      (not_injective_infinite_finite (fun step : Nat => next^[step] initial))
  have path (source : X) (steps : Nat) :
      Relation.TransGen relation source (next^[steps + 1] source) := by
    induction steps with
    | zero =>
        simpa using Relation.TransGen.single (nextStep source)
    | succ steps ih =>
        have finalStep : relation
            (next^[steps + 1] source) (next^[steps + 2] source) := by
          simpa [Function.iterate_succ_apply'] using
            nextStep (next^[steps + 1] source)
        exact ih.tail finalStep
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨steps, hsecond⟩ := Nat.exists_eq_add_of_lt hlt
    refine ⟨next^[first] initial, ?_⟩
    have hpath := path (next^[first] initial) steps
    have htarget :
        next^[steps + 1] (next^[first] initial) =
          next^[second] initial := by
      rw [← Function.iterate_add_apply]
      congr 2
      omega
    rw [htarget, ← heq] at hpath
    exact hpath
  · obtain ⟨steps, hfirst⟩ := Nat.exists_eq_add_of_lt hlt
    refine ⟨next^[second] initial, ?_⟩
    have hpath := path (next^[second] initial) steps
    have htarget :
        next^[steps + 1] (next^[second] initial) =
          next^[first] initial := by
      rw [← Function.iterate_add_apply]
      congr 2
      omega
    rw [htarget, heq] at hpath
    exact hpath

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {a n : Nat}

variable
  (rotation : Data G)
  (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
  (ordered : OrderedInjectiveMesh
    (toMultigraph rotation.toRotationSystem) a (n + 1))

/-- The adjacent-pair deletion data at one selected row interval. -/
abbrev rowSiteData
    (row : Fin a) (slot : Fin 9 ↪ Fin n) (index : Fin 9) :
    AdjacentPairData G :=
  (selectedGlobalKempeSite rotation minimal ordered
    (globalRowStep rotation ordered row (slot index))).data

/-- **Nine-site Tait common-core residue.**  Every assignment of Tait
colourings to nine injectively selected row intervals contains a pair for
which local branching, a valid-pair boundary-reaching component, or a strict
valid-pair Tait repair occurs. -/
theorem exists_taitCommonCoreResidue_in_any_nine_row_intervals
    (row : Fin a) (slot : Fin 9 ↪ Fin n)
    (coloring : ∀ index : Fin 9,
      (DeletedAdjacentPairGraph G
        (rowSiteData rotation minimal ordered row slot index).firstVertex
        (rowSiteData rotation minimal ordered row slot index).secondVertex).EdgeColoring
        Color)
    (tait : ∀ index : Fin 9,
      IsTaitEdgeColoring
        (DeletedAdjacentPairGraph G
          (rowSiteData rotation minimal ordered row slot index).firstVertex
          (rowSiteData rotation minimal ordered row slot index).secondVertex)
        (coloring index)) :
    ∃ first second : Fin 9,
      HasCommonCoreBranchingDiscrepancy
          (rowSiteData rotation minimal ordered row slot first)
          (rowSiteData rotation minimal ordered row slot second)
          (coloring first) (coloring second) ∨
        FirstTaitOrbitReachesSecondPair
          (rowSiteData rotation minimal ordered row slot first)
          (rowSiteData rotation minimal ordered row slot second)
          (coloring first) ∨
        HasStrictTaitCommonCoreRepair
          (rowSiteData rotation minimal ordered row slot first)
          (rowSiteData rotation minimal ordered row slot second)
          (coloring first) (coloring second) := by
  obtain ⟨first, second, hfalse⟩ :=
    exists_coloring_disagreement_in_any_nine_row_intervals
      rotation minimal ordered row slot coloring tait
  refine ⟨first, second, ?_⟩
  have hdisagrees :
      firstDeletionCommonCoreColoring
          (third := (rowSiteData rotation minimal ordered row slot second).firstVertex)
          (fourth := (rowSiteData rotation minimal ordered row slot second).secondVertex)
          (coloring first) ≠
        secondDeletionCommonCoreColoring
          (first := (rowSiteData rotation minimal ordered row slot first).firstVertex)
          (second := (rowSiteData rotation minimal ordered row slot first).secondVertex)
          (coloring second) := by
    intro hagrees
    have htrue :=
      (GoertzelV24AdjacentPairColoringAtlas.commonRestrictionAgreementBit_eq_true_iff
        (rowSiteData rotation minimal ordered row slot first)
        (rowSiteData rotation minimal ordered row slot second)
        (coloring first) (coloring second)).2 hagrees
    rw [hfalse] at htrue
    contradiction
  exact branching_or_taitReachesSecondPair_or_strictTaitRepair
    (rowSiteData rotation minimal ordered row slot first)
    (rowSiteData rotation minimal ordered row slot second)
    (coloring first) (coloring second) (tait first) (tait second) hdisagrees

/-! ## The finite repair system -/

/-- A state assigns one proper nonzero Tait colouring to each of the nine
selected adjacent-pair deletions. -/
def NineSiteTaitAssignment
    (row : Fin a) (slot : Fin 9 ↪ Fin n) :=
  ∀ index : Fin 9,
    { coloring :
        (DeletedAdjacentPairGraph G
          (rowSiteData rotation minimal ordered row slot index).firstVertex
          (rowSiteData rotation minimal ordered row slot index).secondVertex).EdgeColoring
          Color //
      IsTaitEdgeColoring
        (DeletedAdjacentPairGraph G
          (rowSiteData rotation minimal ordered row slot index).firstVertex
          (rowSiteData rotation minimal ordered row slot index).secondVertex)
        coloring }

/-- The repair process has already exposed one of its two geometrically
meaningful exceptional horns. -/
def HasNineSiteBranchingOrBoundary
    (row : Fin a) (slot : Fin 9 ↪ Fin n)
    (assignment : NineSiteTaitAssignment rotation minimal ordered row slot) : Prop :=
  ∃ first second : Fin 9,
    HasCommonCoreBranchingDiscrepancy
        (rowSiteData rotation minimal ordered row slot first)
        (rowSiteData rotation minimal ordered row slot second)
        (assignment first).1 (assignment second).1 ∨
      FirstTaitOrbitReachesSecondPair
        (rowSiteData rotation minimal ordered row slot first)
        (rowSiteData rotation minimal ordered row slot second)
        (assignment first).1

/-- One strict repair changes exactly one coordinate, stays in its valid-pair
Tait-Kempe orbit, and aligns that coordinate with a second site's common-core
restriction. -/
def NineSiteStrictRepairStep
    (row : Fin a) (slot : Fin 9 ↪ Fin n)
    (source target : NineSiteTaitAssignment rotation minimal ordered row slot) : Prop :=
  ∃ first second : Fin 9,
    GoertzelV24LocalSwapKempeGeneration.TaitKempeReachable
      (source first).1 (target first).1 ∧
    firstDeletionCommonCoreColoring
        (third := (rowSiteData rotation minimal ordered row slot second).firstVertex)
        (fourth := (rowSiteData rotation minimal ordered row slot second).secondVertex)
        (target first).1 =
      secondDeletionCommonCoreColoring
        (first := (rowSiteData rotation minimal ordered row slot first).firstVertex)
        (second := (rowSiteData rotation minimal ordered row slot first).secondVertex)
        (source second).1 ∧
    (target first).1 ≠ (source first).1 ∧
    ∀ index, index ≠ first → target index = source index

/-- The finite repair relation is irreflexive: a step changes its repaired
coordinate strictly. -/
theorem nineSiteStrictRepairStep_ne
    (row : Fin a) (slot : Fin 9 ↪ Fin n)
    {source target : NineSiteTaitAssignment rotation minimal ordered row slot}
    (hstep : NineSiteStrictRepairStep rotation minimal ordered row slot
      source target) :
    target ≠ source := by
  rcases hstep with ⟨first, _second, _hreachable, _hagrees, hstrict, _hother⟩
  intro heq
  apply hstrict
  exact congrArg Subtype.val (congrFun heq first)

/-- Every nine-site state either exposes branching/boundary geometry or has a
strict one-coordinate successor in the Tait repair system. -/
theorem branchingOrBoundary_or_exists_strictRepairStep
    (row : Fin a) (slot : Fin 9 ↪ Fin n)
    (assignment : NineSiteTaitAssignment rotation minimal ordered row slot) :
    HasNineSiteBranchingOrBoundary rotation minimal ordered row slot assignment ∨
      ∃ target, NineSiteStrictRepairStep rotation minimal ordered row slot
        assignment target := by
  let coloring := fun index : Fin 9 => (assignment index).1
  have tait : ∀ index : Fin 9,
      IsTaitEdgeColoring
        (DeletedAdjacentPairGraph G
          (rowSiteData rotation minimal ordered row slot index).firstVertex
          (rowSiteData rotation minimal ordered row slot index).secondVertex)
        (coloring index) := fun index => (assignment index).2
  obtain ⟨first, second, hbranch | hboundary | hrepair⟩ :=
    exists_taitCommonCoreResidue_in_any_nine_row_intervals
      rotation minimal ordered row slot coloring tait
  · exact Or.inl ⟨first, second, Or.inl hbranch⟩
  · exact Or.inl ⟨first, second, Or.inr hboundary⟩
  · right
    rcases hrepair with
      ⟨repaired, hreachable, hrepairedTait, hagrees, hstrict⟩
    let target : NineSiteTaitAssignment rotation minimal ordered row slot :=
      Function.update assignment first ⟨repaired, hrepairedTait⟩
    refine ⟨target, first, second, ?_, ?_, ?_, ?_⟩
    · simpa [target] using hreachable
    · simpa [target, coloring] using hagrees
    · simpa [target] using hstrict
    · intro index hne
      simp [target, hne]

/-- **Exact finite-dynamics residue.**  If no assignment ever exposes local
branching or a boundary-reaching component, the strict Tait repair relation
contains a nonempty directed cycle. -/
theorem exists_strictRepairCycle_of_no_branchingOrBoundary
    (row : Fin a) (slot : Fin 9 ↪ Fin n)
    (hno : ∀ assignment :
      NineSiteTaitAssignment rotation minimal ordered row slot,
      ¬ HasNineSiteBranchingOrBoundary rotation minimal ordered row slot
          assignment) :
    ∃ assignment,
      Relation.TransGen
        (NineSiteStrictRepairStep rotation minimal ordered row slot)
        assignment assignment := by
  let initial : NineSiteTaitAssignment rotation minimal ordered row slot :=
    fun index =>
      ⟨(selectedGlobalKempeSite rotation minimal ordered
          (globalRowStep rotation ordered row (slot index))).base,
        (selectedGlobalKempeSite rotation minimal ordered
          (globalRowStep rotation ordered row (slot index))).baseTait⟩
  letI : Nonempty
      (NineSiteTaitAssignment rotation minimal ordered row slot) :=
    ⟨initial⟩
  letI : Fintype
      (NineSiteTaitAssignment rotation minimal ordered row slot) := by
    unfold NineSiteTaitAssignment
    infer_instance
  apply exists_transGen_cycle_of_finite_serial
  intro assignment
  exact (branchingOrBoundary_or_exists_strictRepairStep
    rotation minimal ordered row slot assignment).resolve_left (hno assignment)

end

end GoertzelV24OrderedMeshCommonCoreDisagreementResidue

end Mettapedia.GraphTheory.FourColor

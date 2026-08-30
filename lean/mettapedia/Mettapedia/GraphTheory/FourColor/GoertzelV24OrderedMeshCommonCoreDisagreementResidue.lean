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

/-- Two adjacent-pair deletion colourings disagree on their exact common
four-vertex deletion. -/
def CommonCoreColoringsDisagree
    (source target : AdjacentPairData G)
    (sourceColoring : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color)
    (targetColoring : (DeletedAdjacentPairGraph G target.firstVertex
      target.secondVertex).EdgeColoring Color) : Prop :=
  firstDeletionCommonCoreColoring
      (third := target.firstVertex) (fourth := target.secondVertex)
      sourceColoring ≠
    secondDeletionCommonCoreColoring
      (first := source.firstVertex) (second := source.secondVertex)
      targetColoring

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
      first ≠ second ∧
      CommonCoreColoringsDisagree
          (rowSiteData rotation minimal ordered row slot first)
          (rowSiteData rotation minimal ordered row slot second)
          (coloring first) (coloring second) ∧
      (HasCommonCoreBranchingDiscrepancy
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
          (coloring first) (coloring second)) := by
  obtain ⟨first, second, hfalse⟩ :=
    exists_coloring_disagreement_in_any_nine_row_intervals
      rotation minimal ordered row slot coloring tait
  have hne : first ≠ second := by
    intro heq
    subst second
    have hagrees :
        firstDeletionCommonCoreColoring
            (third := (rowSiteData rotation minimal ordered row slot first).firstVertex)
            (fourth := (rowSiteData rotation minimal ordered row slot first).secondVertex)
            (coloring first) =
          secondDeletionCommonCoreColoring
            (first := (rowSiteData rotation minimal ordered row slot first).firstVertex)
            (second := (rowSiteData rotation minimal ordered row slot first).secondVertex)
            (coloring first) := by
      ext edge
      · apply congrArg Prod.fst
        apply congrArg (coloring first)
        apply Subtype.ext
        rfl
      · apply congrArg Prod.snd
        apply congrArg (coloring first)
        apply Subtype.ext
        rfl
    have htrue :=
      (GoertzelV24AdjacentPairColoringAtlas.commonRestrictionAgreementBit_eq_true_iff
        (rowSiteData rotation minimal ordered row slot first)
        (rowSiteData rotation minimal ordered row slot first)
        (coloring first) (coloring first)).2 hagrees
    rw [hfalse] at htrue
    contradiction
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
  exact ⟨first, second, hne, hdisagrees,
    branching_or_taitReachesSecondPair_or_strictTaitRepair
      (rowSiteData rotation minimal ordered row slot first)
      (rowSiteData rotation minimal ordered row slot second)
      (coloring first) (coloring second) (tait first) (tait second) hdisagrees⟩

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
    first ≠ second ∧
    GoertzelV24LocalSwapKempeGeneration.TaitKempeReachable
      (source first).1 (target first).1 ∧
    CommonCoreColoringsDisagree
      (rowSiteData rotation minimal ordered row slot first)
      (rowSiteData rotation minimal ordered row slot second)
      (source first).1 (source second).1 ∧
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

/-- The ordered pairs of sites whose current colourings agree on their exact
common four-vertex deletion. -/
def NineSiteAgreementPairs
    (row : Fin a) (slot : Fin 9 ↪ Fin n)
    (assignment : NineSiteTaitAssignment rotation minimal ordered row slot) :
    Finset (Fin 9 × Fin 9) := by
  classical
  exact Finset.univ.filter fun pair =>
    ¬ CommonCoreColoringsDisagree
      (rowSiteData rotation minimal ordered row slot pair.1)
      (rowSiteData rotation minimal ordered row slot pair.2)
      (assignment pair.1).1 (assignment pair.2).1

/-- A repair loses collateral agreement when some ordered pair agreed before
the step but disagrees afterwards. -/
def HasCollateralAgreementLoss
    (row : Fin a) (slot : Fin 9 ↪ Fin n)
    (source target : NineSiteTaitAssignment rotation minimal ordered row slot) :
    Prop :=
  ∃ first second : Fin 9,
    ¬ CommonCoreColoringsDisagree
      (rowSiteData rotation minimal ordered row slot first)
      (rowSiteData rotation minimal ordered row slot second)
      (source first).1 (source second).1 ∧
    CommonCoreColoringsDisagree
      (rowSiteData rotation minimal ordered row slot first)
      (rowSiteData rotation minimal ordered row slot second)
      (target first).1 (target second).1

/-- Without collateral loss, one strict repair strictly enlarges the finite
set of common-core agreements: the repaired pair is new and every old
agreement is retained. -/
theorem nineSiteAgreementPairs_ssubset_of_not_collateralLoss
    (row : Fin a) (slot : Fin 9 ↪ Fin n)
    {source target : NineSiteTaitAssignment rotation minimal ordered row slot}
    (hstep : NineSiteStrictRepairStep rotation minimal ordered row slot
      source target)
    (hnoLoss : ¬ HasCollateralAgreementLoss rotation minimal ordered row slot
      source target) :
    NineSiteAgreementPairs rotation minimal ordered row slot source ⊂
      NineSiteAgreementPairs rotation minimal ordered row slot target := by
  classical
  rcases hstep with
    ⟨repaired, partner, hne, _hreachable, hsourceDisagrees,
      htargetAgreesSourcePartner, _hstrict, hother⟩
  have hsubset :
      NineSiteAgreementPairs rotation minimal ordered row slot source ⊆
        NineSiteAgreementPairs rotation minimal ordered row slot target := by
    intro pair hpair
    have hsourceAgrees :
        ¬ CommonCoreColoringsDisagree
          (rowSiteData rotation minimal ordered row slot pair.1)
          (rowSiteData rotation minimal ordered row slot pair.2)
          (source pair.1).1 (source pair.2).1 := by
      simpa [NineSiteAgreementPairs] using hpair
    have htargetAgrees :
        ¬ CommonCoreColoringsDisagree
          (rowSiteData rotation minimal ordered row slot pair.1)
          (rowSiteData rotation minimal ordered row slot pair.2)
          (target pair.1).1 (target pair.2).1 := by
      intro htargetDisagrees
      exact hnoLoss ⟨pair.1, pair.2, hsourceAgrees, htargetDisagrees⟩
    simpa [NineSiteAgreementPairs] using htargetAgrees
  have hsourceNotMem :
      (repaired, partner) ∉
        NineSiteAgreementPairs rotation minimal ordered row slot source := by
    simp [NineSiteAgreementPairs, hsourceDisagrees]
  have hpartner : target partner = source partner :=
    hother partner hne.symm
  have htargetAgrees :
      ¬ CommonCoreColoringsDisagree
        (rowSiteData rotation minimal ordered row slot repaired)
        (rowSiteData rotation minimal ordered row slot partner)
        (target repaired).1 (target partner).1 := by
    intro htargetDisagrees
    apply htargetDisagrees
    rw [hpartner]
    exact htargetAgreesSourcePartner
  have htargetMem :
      (repaired, partner) ∈
        NineSiteAgreementPairs rotation minimal ordered row slot target := by
    simpa [NineSiteAgreementPairs] using htargetAgrees
  refine Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, ?_⟩
  intro heq
  apply hsourceNotMem
  rw [heq]
  exact htargetMem

/-- A nonempty closed run of strict repairs must contain a collateral
agreement loss.  Otherwise the finite agreement set would grow strictly
around a directed cycle. -/
theorem exists_collateralAgreementLoss_of_strictRepairCycle
    (row : Fin a) (slot : Fin 9 ↪ Fin n)
    {assignment : NineSiteTaitAssignment rotation minimal ordered row slot}
    (cycle : Relation.TransGen
      (NineSiteStrictRepairStep rotation minimal ordered row slot)
      assignment assignment) :
    ∃ source target,
      NineSiteStrictRepairStep rotation minimal ordered row slot source target ∧
      HasCollateralAgreementLoss rotation minimal ordered row slot source target := by
  by_contra hnone
  have hnoLoss : ∀ {source target},
      NineSiteStrictRepairStep rotation minimal ordered row slot source target →
        ¬ HasCollateralAgreementLoss rotation minimal ordered row slot
          source target := by
    intro source target hstep hloss
    exact hnone ⟨source, target, hstep, hloss⟩
  have hstrictRun {source target}
      (run : Relation.TransGen
        (NineSiteStrictRepairStep rotation minimal ordered row slot)
        source target) :
      NineSiteAgreementPairs rotation minimal ordered row slot source ⊂
        NineSiteAgreementPairs rotation minimal ordered row slot target := by
    induction run with
    | single hstep =>
        exact nineSiteAgreementPairs_ssubset_of_not_collateralLoss
          rotation minimal ordered row slot hstep (hnoLoss hstep)
    | tail hpath hstep ih =>
        exact ih.trans
          (nineSiteAgreementPairs_ssubset_of_not_collateralLoss
            rotation minimal ordered row slot hstep (hnoLoss hstep))
  have himpossible := hstrictRun cycle
  exact himpossible.ne rfl

/-- An anchored agreement trade records the exact local coherence failure:
one repaired coordinate gains agreement with its chosen partner while losing
an agreement on another ordered pair that contains the repaired coordinate. -/
def HasAnchoredAgreementTrade
    (row : Fin a) (slot : Fin 9 ↪ Fin n)
    (source target : NineSiteTaitAssignment rotation minimal ordered row slot) :
    Prop :=
  ∃ repaired gainedPartner lostFirst lostSecond : Fin 9,
    repaired ≠ gainedPartner ∧
    (lostFirst = repaired ∨ lostSecond = repaired) ∧
    CommonCoreColoringsDisagree
      (rowSiteData rotation minimal ordered row slot repaired)
      (rowSiteData rotation minimal ordered row slot gainedPartner)
      (source repaired).1 (source gainedPartner).1 ∧
    ¬ CommonCoreColoringsDisagree
      (rowSiteData rotation minimal ordered row slot repaired)
      (rowSiteData rotation minimal ordered row slot gainedPartner)
      (target repaired).1 (target gainedPartner).1 ∧
    ¬ CommonCoreColoringsDisagree
      (rowSiteData rotation minimal ordered row slot lostFirst)
      (rowSiteData rotation minimal ordered row slot lostSecond)
      (source lostFirst).1 (source lostSecond).1 ∧
    CommonCoreColoringsDisagree
      (rowSiteData rotation minimal ordered row slot lostFirst)
      (rowSiteData rotation minimal ordered row slot lostSecond)
      (target lostFirst).1 (target lostSecond).1

/-- Collateral loss in a one-coordinate repair is necessarily anchored at
the repaired coordinate. -/
theorem hasAnchoredAgreementTrade_of_strictRepairStep_of_collateralLoss
    (row : Fin a) (slot : Fin 9 ↪ Fin n)
    {source target : NineSiteTaitAssignment rotation minimal ordered row slot}
    (hstep : NineSiteStrictRepairStep rotation minimal ordered row slot
      source target)
    (hloss : HasCollateralAgreementLoss rotation minimal ordered row slot
      source target) :
    HasAnchoredAgreementTrade rotation minimal ordered row slot source target := by
  rcases hstep with
    ⟨repaired, gainedPartner, hne, _hreachable, hsourceDisagrees,
      htargetAgreesSourcePartner, _hstrict, hother⟩
  rcases hloss with
    ⟨lostFirst, lostSecond, hsourceLostAgrees, htargetLostDisagrees⟩
  have htargetGainedAgrees :
      ¬ CommonCoreColoringsDisagree
        (rowSiteData rotation minimal ordered row slot repaired)
        (rowSiteData rotation minimal ordered row slot gainedPartner)
        (target repaired).1 (target gainedPartner).1 := by
    intro htargetDisagrees
    apply htargetDisagrees
    rw [hother gainedPartner hne.symm]
    exact htargetAgreesSourcePartner
  have hlossTouches : lostFirst = repaired ∨ lostSecond = repaired := by
    by_contra hnot
    push Not at hnot
    have hfirst := hother lostFirst hnot.1
    have hsecond := hother lostSecond hnot.2
    apply hsourceLostAgrees
    simpa [hfirst, hsecond] using htargetLostDisagrees
  exact ⟨repaired, gainedPartner, lostFirst, lostSecond, hne, hlossTouches,
    hsourceDisagrees, htargetGainedAgrees, hsourceLostAgrees,
    htargetLostDisagrees⟩

/-- Every nonempty closed strict-repair run contains an anchored agreement
trade. -/
theorem exists_anchoredAgreementTrade_of_strictRepairCycle
    (row : Fin a) (slot : Fin 9 ↪ Fin n)
    {assignment : NineSiteTaitAssignment rotation minimal ordered row slot}
    (cycle : Relation.TransGen
      (NineSiteStrictRepairStep rotation minimal ordered row slot)
      assignment assignment) :
    ∃ source target,
      NineSiteStrictRepairStep rotation minimal ordered row slot source target ∧
      HasAnchoredAgreementTrade rotation minimal ordered row slot source target := by
  obtain ⟨source, target, hstep, hloss⟩ :=
    exists_collateralAgreementLoss_of_strictRepairCycle
      rotation minimal ordered row slot cycle
  exact ⟨source, target, hstep,
    hasAnchoredAgreementTrade_of_strictRepairStep_of_collateralLoss
      rotation minimal ordered row slot hstep hloss⟩

/-- The finite repair relation is irreflexive: a step changes its repaired
coordinate strictly. -/
theorem nineSiteStrictRepairStep_ne
    (row : Fin a) (slot : Fin 9 ↪ Fin n)
    {source target : NineSiteTaitAssignment rotation minimal ordered row slot}
    (hstep : NineSiteStrictRepairStep rotation minimal ordered row slot
      source target) :
    target ≠ source := by
  rcases hstep with
    ⟨first, _second, _hne, _hreachable, _hdisagrees, _hagrees, hstrict, _hother⟩
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
  obtain ⟨first, second, hne, hdisagrees, hbranch | hboundary | hrepair⟩ :=
    exists_taitCommonCoreResidue_in_any_nine_row_intervals
      rotation minimal ordered row slot coloring tait
  · exact Or.inl ⟨first, second, Or.inl hbranch⟩
  · exact Or.inl ⟨first, second, Or.inr hboundary⟩
  · right
    rcases hrepair with
      ⟨repaired, hreachable, hrepairedTait, hagrees, hstrict⟩
    let target : NineSiteTaitAssignment rotation minimal ordered row slot :=
      Function.update assignment first ⟨repaired, hrepairedTait⟩
    refine ⟨target, first, second, hne, ?_, hdisagrees, ?_, ?_, ?_⟩
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

/-- **Exact coherence residue.**  If none of the nine-site assignments exposes
local branching or a boundary-reaching Kempe component, then some strict
repair gains one common-core agreement while losing another agreement that
touches the repaired site. -/
theorem exists_anchoredAgreementTrade_of_no_branchingOrBoundary
    (row : Fin a) (slot : Fin 9 ↪ Fin n)
    (hno : ∀ assignment :
      NineSiteTaitAssignment rotation minimal ordered row slot,
      ¬ HasNineSiteBranchingOrBoundary rotation minimal ordered row slot
          assignment) :
    ∃ source target,
      NineSiteStrictRepairStep rotation minimal ordered row slot source target ∧
      HasAnchoredAgreementTrade rotation minimal ordered row slot source target := by
  obtain ⟨assignment, cycle⟩ :=
    exists_strictRepairCycle_of_no_branchingOrBoundary
      rotation minimal ordered row slot hno
  exact exists_anchoredAgreementTrade_of_strictRepairCycle
    rotation minimal ordered row slot cycle

end

end GoertzelV24OrderedMeshCommonCoreDisagreementResidue

end Mettapedia.GraphTheory.FourColor

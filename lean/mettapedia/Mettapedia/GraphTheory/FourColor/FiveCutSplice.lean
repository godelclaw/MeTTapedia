import Mettapedia.GraphTheory.FourColor.FiveCutShoreAssembly
import Mettapedia.GraphTheory.FourColor.FiveCutComplementCoordinates
import Mettapedia.GraphTheory.FourColor.GoertzelV24FourEdgeCutGluing

/-!
# The five-cut splice

The heart's common boundary word realizes proper colourings of the two
shore port tangles that agree edge-by-edge across the cut, because the
complement boundary order is the boundary-`alpha` transport of the
retained order.  Gluing the two colourings dart-by-dart yields an
ambient Tait colouring, contradicting the minimal counterexample.
Hence a graph-backed vertex-minimal Tait counterexample carries no
nontrivial exact cyclic five-edge cut.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace FiveCutSplice

open Compositional
open Compositional.FiveCutShoreLanguage
open Compositional.FiveCutWordTransfers
open FiveCutCapAssembly
open FiveCutComplementCoordinates
open FiveCutShoreAssembly
open GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FourEdgeCutGluing
open GoertzelV24OpenTangleComposition
open GoertzelV24PortTangleCutParity
open GoertzelV24PortTangleGluing
open GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24SimpleGraphFaceDualConnectedness
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24VertexSidePrimalKempeTrail
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- Evaluate the dart decomposition on an internal dart. -/
theorem retainedDartEquivInternalSumBoundary_eq_inl
    {V₁ E₁ : Type*} [Fintype V₁] [DecidableEq V₁]
    [Fintype E₁] [DecidableEq E₁]
    (RS : RotationSystem V₁ E₁) (keep : V₁ → Prop)
    (r : RetainedDart RS keep)
    (hopp : keep (RS.vertOf (RS.alpha r.1))) :
    retainedDartEquivInternalSumBoundary RS keep r =
      Sum.inl ⟨r, hopp⟩ := by
  classical
  show (if h : keep (RS.vertOf (RS.alpha r.1)) then
      (Sum.inl ⟨r, h⟩ : InternalDart RS keep ⊕ BoundaryDart RS keep)
    else Sum.inr ⟨r, h⟩) = Sum.inl ⟨r, hopp⟩
  rw [dif_pos hopp]

/-- Evaluate the dart decomposition on a boundary dart. -/
theorem retainedDartEquivInternalSumBoundary_eq_inr
    {V₁ E₁ : Type*} [Fintype V₁] [DecidableEq V₁]
    [Fintype E₁] [DecidableEq E₁]
    (RS : RotationSystem V₁ E₁) (keep : V₁ → Prop)
    (r : RetainedDart RS keep)
    (hopp : ¬ keep (RS.vertOf (RS.alpha r.1))) :
    retainedDartEquivInternalSumBoundary RS keep r =
      Sum.inr ⟨r, hopp⟩ := by
  classical
  show (if h : keep (RS.vertOf (RS.alpha r.1)) then
      (Sum.inl ⟨r, h⟩ : InternalDart RS keep ⊕ BoundaryDart RS keep)
    else Sum.inr ⟨r, h⟩) = Sum.inr ⟨r, hopp⟩
  rw [dif_neg hopp]

/-- The tangle vertex of a decomposed retained dart is its retained
ambient vertex. -/
theorem vert_retainedDartEquivInternalSumBoundary
    (graphData : Data G) (keep : V → Prop)
    (outer : RetainedDart graphData.toRotationSystem keep)
    (r : RetainedDart graphData.toRotationSystem keep) :
    (vertexSidePortTangle graphData keep outer).vert
        (retainedDartEquivInternalSumBoundary
          graphData.toRotationSystem keep r) =
      GoertzelV24OpenTangleComposition.OpenTangleData.vertexSideVertex
        graphData.toRotationSystem keep r := by
  by_cases hopp : keep (graphData.toRotationSystem.vertOf
      (graphData.toRotationSystem.alpha r.1))
  · rw [retainedDartEquivInternalSumBoundary_eq_inl _ _ r hopp]
    rfl
  · rw [retainedDartEquivInternalSumBoundary_eq_inr _ _ r hopp]
    rfl

/-- Regard a graph dart based in a shore as a retained rotation-system dart. -/
def retainedGraphDart
    (graphData : Data G) (keep : V → Prop)
    (d : G.Dart) (hbase : keep d.fst) :
    RetainedDart graphData.toRotationSystem keep := by
  exact ⟨d, hbase⟩

/-- Regard a graph dart internal to a shore as an internal tangle dart. -/
def internalGraphDart
    (graphData : Data G) (keep : V → Prop)
    (d : G.Dart) (hbase : keep d.fst) (hterminal : keep d.snd) :
    InternalDart graphData.toRotationSystem keep := by
  refine ⟨retainedGraphDart graphData keep d hbase, ?_⟩
  change keep d.snd
  exact hterminal

/-- Regard a graph dart crossing out of a shore as a boundary tangle dart. -/
def boundaryGraphDart
    (graphData : Data G) (keep : V → Prop)
    (d : G.Dart) (hbase : keep d.fst) (hterminal : ¬ keep d.snd) :
    BoundaryDart graphData.toRotationSystem keep := by
  refine ⟨retainedGraphDart graphData keep d hbase, ?_⟩
  change ¬ keep d.snd
  exact hterminal

/-- The dart of the shore port tangle represented by a retained graph dart. -/
def shoreDart
    (graphData : Data G) (keep : V → Prop)
    (d : G.Dart) (hbase : keep d.fst) :
    InternalDart graphData.toRotationSystem keep ⊕
      BoundaryDart graphData.toRotationSystem keep :=
  retainedDartEquivInternalSumBoundary graphData.toRotationSystem keep
    (retainedGraphDart graphData keep d hbase)

@[simp]
theorem shoreDart_internal
    (graphData : Data G) (keep : V → Prop)
    (d : G.Dart) (hbase : keep d.fst) (hterminal : keep d.snd) :
    shoreDart graphData keep d hbase =
      Sum.inl (internalGraphDart graphData keep d hbase hterminal) := by
  classical
  apply retainedDartEquivInternalSumBoundary_eq_inl

@[simp]
theorem shoreDart_boundary
    (graphData : Data G) (keep : V → Prop)
    (d : G.Dart) (hbase : keep d.fst) (hterminal : ¬ keep d.snd) :
    shoreDart graphData keep d hbase =
      Sum.inr (boundaryGraphDart graphData keep d hbase hterminal) := by
  classical
  apply retainedDartEquivInternalSumBoundary_eq_inr

@[simp]
theorem vert_shoreDart
    (graphData : Data G) (keep : V → Prop)
    (outer : RetainedDart graphData.toRotationSystem keep)
    (d : G.Dart) (hbase : keep d.fst) :
    (vertexSidePortTangle graphData keep outer).vert
        (shoreDart graphData keep d hbase) =
      ⟨d.fst, hbase⟩ := by
  rw [shoreDart, vert_retainedDartEquivInternalSumBoundary]
  rfl

/-- The shore-dart representation remembers its ambient graph dart. -/
theorem shoreDart_injective
    (graphData : Data G) (keep : V → Prop)
    {first second : G.Dart}
    (hfirst : keep first.fst) (hsecond : keep second.fst)
    (h : shoreDart graphData keep first hfirst =
      shoreDart graphData keep second hsecond) :
    first = second := by
  have hretained :=
    (retainedDartEquivInternalSumBoundary
      graphData.toRotationSystem keep).injective h
  exact congrArg (fun retained => retained.1) hretained

/-- Color an ambient graph dart from the coloring of the shore containing
its initial vertex.  Keeping this definition on `G.Dart` makes the final
descent to the graph-backed rotation system definitionally transparent. -/
def gluedDartColor
    (graphData : Data G)
    (keepA keepB : V → Prop)
    (hcover : ∀ v, ¬ keepA v → keepB v)
    (outerA : RetainedDart graphData.toRotationSystem keepA)
    (outerB : RetainedDart graphData.toRotationSystem keepB)
    (cA : Coloring (vertexSidePortTangle graphData keepA outerA))
    (cB : Coloring (vertexSidePortTangle graphData keepB outerB))
    (d : G.Dart) : Color := by
  classical
  exact if h : keepA d.fst then
      cA.color (shoreDart graphData keepA d h)
    else
      cB.color (shoreDart graphData keepB d (hcover d.fst h))

/-- **The splice.**  A nontrivial exact cyclic five-edge cut in a
graph-backed vertex-minimal Tait counterexample is contradictory. -/
theorem false_of_nontrivial_exactCyclicFiveEdgeCut
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 5)
    (cut : ExactSizedCyclicEdgeCut G 5)
    (hdeletedCard : 6 ≤ (exactCutVertexSide cut).card)
    (hretainedCard : 6 ≤ (exactCutVertexSide cut.compl).card) : False := by
  classical
  have hconnected : G.Connected := by
    rw [← rotationPrimalGraph_toRotationSystem_eq G graphData]
    exact minimal.primalConnected
  have hregular : G.IsRegularOfDegree 3 := by
    intro v
    have hcub :=
      (graphData.toRotationSystem_isCubic_iff).mp minimal.spherical.cubic v
    convert hcub using 2
  -- side bookkeeping
  have hsideOf : ∀ v : V,
      ¬ deletedRegionKeep (exactCutVertexSide cut) v → cut.side v :=
    fun v h => (mem_exactCutVertexSide_iff cut v).mp (not_not.mp h)
  have hkeepBOf : ∀ v : V, cut.side v →
      deletedRegionKeep (exactCutVertexSide cut.compl) v :=
    fun v hs hmem => (mem_exactCutVertexSide_iff cut.compl v).mp hmem hs
  have hnotSideOf : ∀ v : V,
      deletedRegionKeep (exactCutVertexSide cut) v → ¬ cut.side v :=
    fun v h hs => h ((mem_exactCutVertexSide_iff cut v).mpr hs)
  have hnotKeepBOf : ∀ v : V,
      deletedRegionKeep (exactCutVertexSide cut) v →
        ¬ deletedRegionKeep (exactCutVertexSide cut.compl) v :=
    fun v h hb => hb
      ((mem_exactCutVertexSide_iff cut.compl v).mpr (hnotSideOf v h))
  have hkeepAOf : ∀ v : V, ¬ cut.side v →
      deletedRegionKeep (exactCutVertexSide cut) v :=
    fun v hs hmem => hs ((mem_exactCutVertexSide_iff cut v).mp hmem)
  -- anchored outer darts for both shores
  obtain ⟨vA, hvA⟩ := Finset.card_pos.mp
    (by omega : 0 < (exactCutVertexSide cut.compl).card)
  obtain ⟨vB, hvB⟩ := Finset.card_pos.mp
    (by omega : 0 < (exactCutVertexSide cut).card)
  have hvAKeep : deletedRegionKeep (exactCutVertexSide cut) vA :=
    hkeepAOf vA ((mem_exactCutVertexSide_iff cut.compl vA).mp hvA)
  have hvBKeep : deletedRegionKeep (exactCutVertexSide cut.compl) vB :=
    hkeepBOf vB ((mem_exactCutVertexSide_iff cut vB).mp hvB)
  obtain ⟨uA, huA⟩ := Finset.card_pos.mp
    (by
      rw [SimpleGraph.card_neighborFinset_eq_degree, hregular.degree_eq]
      omega : 0 < (G.neighborFinset vA).card)
  obtain ⟨uB, huB⟩ := Finset.card_pos.mp
    (by
      rw [SimpleGraph.card_neighborFinset_eq_degree, hregular.degree_eq]
      omega : 0 < (G.neighborFinset vB).card)
  have hadjA : G.Adj vA uA := by rwa [SimpleGraph.mem_neighborFinset] at huA
  have hadjB : G.Adj vB uB := by rwa [SimpleGraph.mem_neighborFinset] at huB
  set outerA : RetainedDart graphData.toRotationSystem
      (deletedRegionKeep (exactCutVertexSide cut)) :=
    ⟨SimpleGraph.Dart.mk (vA, uA) hadjA, hvAKeep⟩ with houterA
  set outerB : RetainedDart graphData.toRotationSystem
      (deletedRegionKeep (exactCutVertexSide cut.compl)) :=
    ⟨SimpleGraph.Dart.mk (vB, uB) hadjB, hvBKeep⟩ with houterB
  -- pinned retained order on shore A, alpha-transported to shore B
  obtain ⟨orderRA, hpinA⟩ :=
    FiveEdgeCutBoundaryOrder.exists_retainedBoundaryOrder_of_exactCyclicFiveCut
      graphData minimal.spherical minimal.facesTwoSided hconnected
      minimal.vertexRotationCyclic hcyclic cut
  set alphaAB := complementBoundaryAlphaEquiv graphData.toRotationSystem cut
    with halphaAB
  set orderBF := orderRA.trans alphaAB with horderBF
  have hantiB : retainedRegionBoundarySuccessor graphData.toRotationSystem
      (deletedRegionKeep (exactCutVertexSide cut.compl)) =
      orderBF.permCongr (finRotate 5)⁻¹ := by
    rw [retainedRegionBoundarySuccessor_complement_eq_permCongr_deleted
      graphData.toRotationSystem cut]
    have hdeleted : deletedRegionBoundarySuccessor
        graphData.toRotationSystem (exactCutVertexSide cut) =
        (retainedRegionBoundarySuccessor graphData.toRotationSystem
          (deletedRegionKeep (exactCutVertexSide cut)))⁻¹ := by
      rw [FiveEdgeCutBoundaryOrder.retainedBoundarySuccessor_eq_deleted_inverse_of_exactCyclicFiveCut
        graphData minimal.spherical minimal.facesTwoSided hconnected
        minimal.vertexRotationCyclic hcyclic cut, inv_inv]
    rw [hdeleted, ← hpinA, horderBF, permCongr_trans_eq]
    exact (orderBF.permCongrHom.map_inv (finRotate 5)).symm
  -- the common word and its realizing colourings
  obtain ⟨w, hwA, hwB⟩ := exists_common_word_on_shores graphData minimal
    hcyclic cut hdeletedCard hretainedCard outerA orderRA hpinA
    outerB orderBF hantiB
  obtain ⟨boundaryA, hmemA, hvalA⟩ := hwA
  obtain ⟨⟨cA, hproperA, hwordA⟩⟩ := hmemA
  obtain ⟨boundaryB, hmemB, hvalB⟩ := hwB
  obtain ⟨⟨cB, hproperB, hwordB⟩⟩ := hmemB
  -- port colours are word letters
  have hportA : ∀ p : BoundaryDart graphData.toRotationSystem
      (deletedRegionKeep (exactCutVertexSide cut)),
      cA.color (Sum.inr p) = w (orderRA.symm p) := by
    intro p
    have h1 : cA.color (Sum.inr p) = (boundaryA (orderRA.symm p)).1 :=
      congrFun hwordA p
    rw [h1]
    exact hvalA (orderRA.symm p)
  have hportB : ∀ p : BoundaryDart graphData.toRotationSystem
      (deletedRegionKeep (exactCutVertexSide cut.compl)),
      cB.color (Sum.inr p) = w (orderBF.symm p) := by
    intro p
    have h1 : cB.color (Sum.inr p) = (boundaryB (orderBF.symm p)).1 :=
      congrFun hwordB p
    rw [h1]
    exact hvalB (orderBF.symm p)
  -- the glued dart colouring
  set dartColor : G.Dart → Color :=
    gluedDartColor graphData
      (deletedRegionKeep (exactCutVertexSide cut))
      (deletedRegionKeep (exactCutVertexSide cut.compl))
      (fun v h => hkeepBOf v (hsideOf v h)) outerA outerB cA cB
    with hdartColor
  -- alpha invariance
  have halpha : ∀ d : G.Dart,
      dartColor (graphData.toRotationSystem.alpha d) = dartColor d := by
    intro d
    have halphad : graphData.toRotationSystem.alpha d = d.symm :=
      SimpleGraphDartRotation.Data.toRotationSystem_alpha G graphData d
    rw [halphad]
    by_cases hfst : deletedRegionKeep (exactCutVertexSide cut) d.fst <;>
      by_cases hsnd : deletedRegionKeep (exactCutVertexSide cut) d.snd
    · -- internal to shore A
      have hsndSymm : deletedRegionKeep (exactCutVertexSide cut)
          d.symm.fst := by simpa using hsnd
      simp only [hdartColor, gluedDartColor, dif_pos hsndSymm,
        dif_pos hfst]
      rw [shoreDart_internal graphData _ d.symm hsndSymm hfst,
        shoreDart_internal graphData _ d hfst hsnd]
      exact cA.invariant (internalGraphDart graphData _ d hfst hsnd)
    · -- crossing, retained end first
      have hkeepBsnd : deletedRegionKeep (exactCutVertexSide cut.compl)
          d.snd := hkeepBOf d.snd (hsideOf d.snd hsnd)
      have hnotBfst : ¬ deletedRegionKeep (exactCutVertexSide cut.compl)
          d.fst := hnotKeepBOf d.fst hfst
      have hsndSymm : ¬ deletedRegionKeep (exactCutVertexSide cut)
          d.symm.fst := by simpa using hsnd
      simp only [hdartColor, gluedDartColor, dif_neg hsndSymm,
        dif_pos hfst]
      rw [shoreDart_boundary graphData _ d.symm hkeepBsnd hnotBfst,
        shoreDart_boundary graphData _ d hfst hsnd]
      set pA : BoundaryDart graphData.toRotationSystem
          (deletedRegionKeep (exactCutVertexSide cut)) :=
        boundaryGraphDart graphData _ d hfst hsnd with hpA
      set pB : BoundaryDart graphData.toRotationSystem
          (deletedRegionKeep (exactCutVertexSide cut.compl)) :=
        boundaryGraphDart graphData _ d.symm hkeepBsnd hnotBfst with hpB
      have hpBA : pB = alphaAB pA := by
        apply Subtype.ext
        apply Subtype.ext
        change d.symm = d.symm
        rfl
      rw [hportA pA, hportB pB, hpBA]
      have : orderBF.symm (alphaAB pA) = orderRA.symm pA := by
        rw [horderBF]
        rfl
      rw [this]
    · -- crossing, deleted end first
      have hkeepBfst : deletedRegionKeep (exactCutVertexSide cut.compl)
          d.fst := hkeepBOf d.fst (hsideOf d.fst hfst)
      have hnotBsnd : ¬ deletedRegionKeep (exactCutVertexSide cut.compl)
          d.snd := hnotKeepBOf d.snd hsnd
      have hsndSymm : deletedRegionKeep (exactCutVertexSide cut)
          d.symm.fst := by simpa using hsnd
      simp only [hdartColor, gluedDartColor, dif_pos hsndSymm,
        dif_neg hfst]
      rw [shoreDart_boundary graphData _ d.symm hsndSymm hfst,
        shoreDart_boundary graphData _ d hkeepBfst hnotBsnd]
      set pA : BoundaryDart graphData.toRotationSystem
          (deletedRegionKeep (exactCutVertexSide cut)) :=
        boundaryGraphDart graphData _ d.symm hsnd hfst with hpA
      set pB : BoundaryDart graphData.toRotationSystem
          (deletedRegionKeep (exactCutVertexSide cut.compl)) :=
        boundaryGraphDart graphData _ d hkeepBfst hnotBsnd with hpB
      have hpBA : pB = alphaAB pA := by
        apply Subtype.ext
        apply Subtype.ext
        change d = d.symm.symm
        rw [SimpleGraph.Dart.symm_symm]
      rw [hportA pA, hportB pB, hpBA]
      have : orderBF.symm (alphaAB pA) = orderRA.symm pA := by
        rw [horderBF]
        rfl
      rw [this]
    · -- internal to shore B
      have hsndSymm : ¬ deletedRegionKeep (exactCutVertexSide cut)
          d.symm.fst := by simpa using hsnd
      simp only [hdartColor, gluedDartColor, dif_neg hsndSymm,
        dif_neg hfst]
      have hkeepBsnd : deletedRegionKeep (exactCutVertexSide cut.compl)
          d.snd := hkeepBOf d.snd (hsideOf d.snd hsnd)
      have hkeepBfst : deletedRegionKeep (exactCutVertexSide cut.compl)
          d.fst := hkeepBOf d.fst (hsideOf d.fst hfst)
      have hkeepBsndSymm : deletedRegionKeep
          (exactCutVertexSide cut.compl) d.symm.fst := by
        simpa using hkeepBsnd
      rw [shoreDart_internal graphData _ d.symm hkeepBsndSymm hkeepBfst,
        shoreDart_internal graphData _ d hkeepBfst hkeepBsnd]
      exact cB.invariant
        (internalGraphDart graphData _ d hkeepBfst hkeepBsnd)
  -- properness
  have hproper : ∀ {left right : G.Dart},
      graphData.toRotationSystem.vertOf left =
        graphData.toRotationSystem.vertOf right → left ≠ right →
      dartColor left ≠ dartColor right := by
    intro left right hvert hne
    have hfsteq : left.fst = right.fst := hvert
    by_cases hfst : deletedRegionKeep (exactCutVertexSide cut) left.fst
    · have hright : deletedRegionKeep (exactCutVertexSide cut) right.fst :=
        hfsteq ▸ hfst
      simp only [hdartColor, gluedDartColor, dif_pos hfst, dif_pos hright]
      apply hproperA.2
      · rw [vert_shoreDart, vert_shoreDart]
        exact Subtype.ext hvert
      · intro heq
        apply hne
        exact shoreDart_injective graphData _ hfst hright heq
    · have hright : ¬ deletedRegionKeep (exactCutVertexSide cut)
          right.fst := hfsteq ▸ hfst
      simp only [hdartColor, gluedDartColor, dif_neg hfst, dif_neg hright]
      apply hproperB.2
      · rw [vert_shoreDart, vert_shoreDart]
        exact Subtype.ext hvert
      · intro heq
        apply hne
        exact shoreDart_injective graphData _ _ _ heq
  -- nonzero
  have hnonzero : ∀ d : G.Dart, dartColor d ≠ 0 := by
    intro d
    by_cases hfst : deletedRegionKeep (exactCutVertexSide cut) d.fst
    · simp only [hdartColor, gluedDartColor, dif_pos hfst]
      exact hproperA.1 _
    · simp only [hdartColor, gluedDartColor, dif_neg hfst]
      exact hproperB.1 _
  -- descend and contradict minimality
  exact minimal.notColorable
    ⟨graphData.toRotationSystem.dartDescendedColoring dartColor halpha
      (fun hvert hne => hproper hvert hne),
      graphData.toRotationSystem.dartDescendedColoring_isTait dartColor
        halpha (fun hvert hne => hproper hvert hne) hnonzero⟩

/-- An exact cyclic five-edge cut is nontrivial when neither shore is the
five-vertex fan dual to a degree-five vertex.  The threshold is written as
`6 ≤ card`; cubic cut parity later sharpens it to the usual odd threshold
`7 ≤ card`. -/
def IsNontrivialExactCyclicFiveEdgeCut
    (cut : ExactSizedCyclicEdgeCut G 5) : Prop :=
  6 ≤ (exactCutVertexSide cut).card ∧
    6 ≤ (exactCutVertexSide cut.compl).card

/-- **Birkhoff's exact-five-cut theorem, cubic-dual form.**  A graph-backed
vertex-minimal Tait counterexample has no nontrivial exact cyclic five-edge
cut.  The proof is the compositional chain: cap both shores, use minimality,
intersect their boundary languages, and splice the realizing colorings. -/
theorem no_nontrivial_exactCyclicFiveEdgeCut_of_vertexMinimalTaitCounterexample
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData) :
    ∀ cut : ExactSizedCyclicEdgeCut G 5,
      ¬ IsNontrivialExactCyclicFiveEdgeCut cut := by
  intro cut hnontrivial
  exact false_of_nontrivial_exactCyclicFiveEdgeCut graphData minimal
    (cyclicallyFiveEdgeConnected_of_vertexMinimalTaitCounterexample
      graphData minimal)
    cut hnontrivial.1 hnontrivial.2

/-- Every exact cyclic five-edge cut in a minimal counterexample has a small
shore.  Under planar duality this is the five-cycle clause of internal
six-connectivity: a separating five-cycle cannot have at least two primal
vertices on both sides. -/
theorem exactCyclicFiveEdgeCut_has_small_shore_of_vertexMinimalTaitCounterexample
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (cut : ExactSizedCyclicEdgeCut G 5) :
    (exactCutVertexSide cut).card ≤ 5 ∨
      (exactCutVertexSide cut.compl).card ≤ 5 := by
  by_contra hlarge
  push Not at hlarge
  exact no_nontrivial_exactCyclicFiveEdgeCut_of_vertexMinimalTaitCounterexample
    graphData minimal cut ⟨by omega, by omega⟩

end

end FiveCutSplice

end Mettapedia.GraphTheory.FourColor

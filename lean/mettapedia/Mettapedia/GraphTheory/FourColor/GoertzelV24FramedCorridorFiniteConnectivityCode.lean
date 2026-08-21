import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorFiniteFaceUpdateCode
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorPrefixFiniteConnectivityCoordinates
import Mettapedia.GraphTheory.FourColor.GoertzelV24BoundedCarrierGraphFamilyCode

/-!
# Graph-free connectivity code for one literal source Cell

The connectivity factorization already uses only the two incoming crossings
and the six boundary edges of the new hexagonal Cell.  This module transports
that relation from its graph-dependent edge subtype to the stable coordinate
carrier `Fin 2 ⊕ Fin 6`.

The finite geometry code retains the six-cycle position of the shared rung and
of both outgoing crossings.  These positions are part of the literal Cell
letter; they are not erased merely because two Cells have the same coarse
orientation.  The resulting relation is graph-free once the incoming profile,
the full six-edge Cell profile, and this finite geometry code are supplied.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24CorridorProfile
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationBoundaryFaceCutProfile
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorFiniteConnectivityCodeEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Reflexive--transitive closure is invariant under an exact reindexing of
the one-step relation. -/
theorem reflTransGen_equiv_iff {Alpha Beta : Type*}
    (equiv : Alpha ≃ Beta) (sourceStep : Beta → Beta → Prop)
    (targetStep : Alpha → Alpha → Prop)
    (hstep : ∀ left right,
      sourceStep (equiv left) (equiv right) ↔ targetStep left right)
    (left right : Alpha) :
    Relation.ReflTransGen sourceStep (equiv left) (equiv right) ↔
      Relation.ReflTransGen targetStep left right := by
  constructor
  · intro hpath
    simpa using hpath.lift equiv.symm (by
      intro sourceLeft sourceRight hsource
      apply (hstep (equiv.symm sourceLeft) (equiv.symm sourceRight)).1
      simpa using hsource)
  · intro hpath
    exact hpath.lift equiv (fun sourceLeft sourceRight hsource =>
      (hstep sourceLeft sourceRight).2 hsource)

/-- Stable eight-edge carrier of the one-Cell connectivity computation. -/
abbrev LocalLayerFiniteConnectivityCoordinate := Fin 2 ⊕ Fin 6

/-- The finite literal geometry needed to interpret terminals and outgoing
crossings on the six-cycle side of the stable carrier. -/
structure LocalLayerFiniteConnectivityGeometryCode where
  sharedRung : Fin 6
  outgoing : Fin 2 → Fin 6
  deriving DecidableEq, Fintype

/-- Product presentation of the finite literal geometry code. -/
def localLayerFiniteConnectivityGeometryCodeEquiv :
    LocalLayerFiniteConnectivityGeometryCode ≃ Fin 6 × (Fin 2 → Fin 6) where
  toFun geometry := (geometry.sharedRung, geometry.outgoing)
  invFun data := ⟨data.1, data.2⟩
  left_inv geometry := by cases geometry; rfl
  right_inv data := by cases data; rfl

/-- There are exactly `6 * 6^2 = 216` raw placements of the shared rung and
the two outgoing crossings on a six-cycle.  Actual source Cells occupy a
proved subset; this count is only the finite ambient alphabet. -/
theorem card_localLayerFiniteConnectivityGeometryCode :
    Fintype.card LocalLayerFiniteConnectivityGeometryCode = 216 := by
  rw [Fintype.card_congr localLayerFiniteConnectivityGeometryCodeEquiv,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin]
  norm_num

/-- Interpret an incoming crossing or the shared-rung terminal in the stable
eight-edge carrier. -/
def LocalLayerFiniteConnectivityGeometryCode.incomingPort
    (geometry : LocalLayerFiniteConnectivityGeometryCode) :
    CorridorPort 2 1 → LocalLayerFiniteConnectivityCoordinate
  | .inl step => .inl step
  | .inr _terminal => .inr geometry.sharedRung

/-- Stable coordinate of a Cell-boundary position. -/
def LocalLayerFiniteConnectivityGeometryCode.cellPosition
    (_geometry : LocalLayerFiniteConnectivityGeometryCode) (position : Fin 6) :
    LocalLayerFiniteConnectivityCoordinate :=
  .inr position

/-- Stable coordinate of an outgoing crossing. -/
def LocalLayerFiniteConnectivityGeometryCode.outgoingPort
    (geometry : LocalLayerFiniteConnectivityGeometryCode) (step : Fin 2) :
    LocalLayerFiniteConnectivityCoordinate :=
  .inr (geometry.outgoing step)

/-- Old-prefix move computed only from the terminal-aware incoming profile. -/
def localLayerFiniteOldPrefixStep
    (incoming : BoundedCorridorCutProfile 2 1 4)
    (geometry : LocalLayerFiniteConnectivityGeometryCode)
    (pair : TrackedColorPair)
    (left right : LocalLayerFiniteConnectivityCoordinate) : Prop :=
  left = right ∨
    ∃ leftPort rightPort : CorridorPort 2 1,
      geometry.incomingPort leftPort = left ∧
        geometry.incomingPort rightPort = right ∧
        incoming.profile.strandConnected pair leftPort rightPort = true

/-- Cell-internal move computed only from the full six-edge Cell profile. -/
def localLayerFiniteCellStep
    (cellProfile : CorridorCutProfile 6 0 0)
    (geometry : LocalLayerFiniteConnectivityGeometryCode)
    (pair : TrackedColorPair)
    (left right : LocalLayerFiniteConnectivityCoordinate) : Prop :=
  left = right ∨
    ∃ leftPosition rightPosition : Fin 6,
      geometry.cellPosition leftPosition = left ∧
        geometry.cellPosition rightPosition = right ∧
        cellProfile.strandConnected pair (.inl leftPosition)
          (.inl rightPosition) = true

/-- The two source-ordered residual turns, represented as a graph on the
stable eight-edge carrier. -/
def localLayerFiniteSeamGraph
    (incoming : BoundedCorridorCutProfile 2 1 4)
    (cellProfile : CorridorCutProfile 6 0 0)
    (geometry : LocalLayerFiniteConnectivityGeometryCode)
    (pair : TrackedColorPair) :
    SimpleGraph LocalLayerFiniteConnectivityCoordinate where
  Adj left right :=
    ∃ step : Fin 2,
      IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (incoming.profile.edgeColor step).toColor ∧
        IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (cellProfile.edgeColor (geometry.outgoing step)).toColor ∧
        ((left = .inl step ∧ right = geometry.outgoingPort step) ∨
          (left = geometry.outgoingPort step ∧ right = .inl step))
  symm := ⟨by
    rintro left right ⟨step, hleft, hright, horientation⟩
    refine ⟨step, hleft, hright, ?_⟩
    rcases horientation with hforward | hbackward
    · exact Or.inr ⟨hforward.2, hforward.1⟩
    · exact Or.inl ⟨hbackward.2, hbackward.1⟩⟩
  loopless := ⟨by
    intro coordinate hedge
    rcases hedge with ⟨step, _hleft, _hright, horientation⟩
    rcases horientation with hforward | hbackward
    · exact (Sum.inl_ne_inr (hforward.1.symm.trans hforward.2)).elim
    · exact (Sum.inr_ne_inl (hbackward.1.symm.trans hbackward.2)).elim⟩

/-- Complete graph-free one-Cell connectivity step. -/
def localLayerFiniteConnectivityStep
    (incoming : BoundedCorridorCutProfile 2 1 4)
    (cellProfile : CorridorCutProfile 6 0 0)
    (geometry : LocalLayerFiniteConnectivityGeometryCode)
    (pair : TrackedColorPair)
    (left right : LocalLayerFiniteConnectivityCoordinate) : Prop :=
  localLayerFiniteOldPrefixStep incoming geometry pair left right ∨
    localLayerFiniteCellStep cellProfile geometry pair left right ∨
    (localLayerFiniteSeamGraph incoming cellProfile geometry pair).Reachable
      left right

/-- Graph-free connectivity coordinate of a complete one-Cell update. -/
def LocalLayerFiniteConnectivityUpdateCode
    (incoming : BoundedCorridorCutProfile 2 1 4)
    (cellProfile : CorridorCutProfile 6 0 0)
    (geometry : LocalLayerFiniteConnectivityGeometryCode)
    (output : BoundedCorridorCutProfile 2 0 4) : Prop :=
  ∀ (pair : TrackedColorPair) (first second : Fin 2),
    output.profile.strandConnected pair (.inl first) (.inl second) = true ↔
      IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (output.profile.edgeColor first).toColor ∧
        IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (output.profile.edgeColor second).toColor ∧
        Relation.ReflTransGen
          (localLayerFiniteConnectivityStep incoming cellProfile geometry pair)
          (geometry.outgoingPort first) (geometry.outgoingPort second)

namespace SourceTrail

namespace AnnularEmbedding

namespace SourceCornerAlignedSlabInterface

variable {source : SourceTrail G}
  {embedded : source.AnnularEmbedding} {blockLength : Nat}
  {realization : BoundaryCleanCorridorRealization embedded blockLength}
  {htwoSided : OrbitFacesTwoSided
    embedded.cellulation.rotation.toRotationSystem}
  {hunique : PairwiseUniqueSharedInteriorEdges
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
    (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
  {leftInterior : CorridorInterior blockLength}
  {hnext : leftInterior.center.val + 2 < blockLength}

/-- Six-cycle coordinate of the literal shared rung. -/
noncomputable def localLayerSharedRungPosition
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) : Fin 6 :=
  Classical.choose
    ((mem_indexedCrossingEdgeSet_iff aligned.localLayerCellBoundaryEdge
      aligned.toInterface.localLayerSharedRungEdge).1 <| by
        rw [aligned.indexedLocalLayerCellBoundaryEdges_eq_cellBoundaryRegion]
        exact aligned.toInterface.localLayerSharedRungEdge_mem_cellBoundary)

@[simp]
theorem localLayerCellBoundaryEdge_sharedRungPosition
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    aligned.localLayerCellBoundaryEdge aligned.localLayerSharedRungPosition =
      aligned.toInterface.localLayerSharedRungEdge :=
  Classical.choose_spec
    ((mem_indexedCrossingEdgeSet_iff aligned.localLayerCellBoundaryEdge
      aligned.toInterface.localLayerSharedRungEdge).1 <| by
        rw [aligned.indexedLocalLayerCellBoundaryEdges_eq_cellBoundaryRegion]
        exact aligned.toInterface.localLayerSharedRungEdge_mem_cellBoundary)

/-- Finite geometry code extracted from one literal source Cell. -/
noncomputable def localLayerFiniteConnectivityGeometryCode
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) : LocalLayerFiniteConnectivityGeometryCode where
  sharedRung := aligned.localLayerSharedRungPosition
  outgoing := aligned.localLayerCellCrossingPosition

@[simp]
theorem localLayerFiniteConnectivityEquiv_incomingPort_val
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) (port : CorridorPort 2 1) :
    (aligned.localLayerFiniteConnectivityEquiv
      (aligned.localLayerFiniteConnectivityGeometryCode.incomingPort port)).1 =
        aligned.localLayerLeftPrefixSharedRungGraphCutData.portEdge port := by
  rcases port with step | terminal
  · rfl
  · simp [LocalLayerFiniteConnectivityGeometryCode.incomingPort,
      localLayerFiniteConnectivityGeometryCode]

@[simp]
theorem localLayerFiniteConnectivityEquiv_cellPosition_val
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) (position : Fin 6) :
    (aligned.localLayerFiniteConnectivityEquiv
      (aligned.localLayerFiniteConnectivityGeometryCode.cellPosition
        position)).1 = aligned.localLayerCellBoundaryEdge position :=
  rfl

@[simp]
theorem localLayerFiniteConnectivityEquiv_outgoingPort_val
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) (step : Fin 2) :
    (aligned.localLayerFiniteConnectivityEquiv
      (aligned.localLayerFiniteConnectivityGeometryCode.outgoingPort step)).1 =
        aligned.toInterface.nextLocalLayerPrefixCrossing step := by
  exact aligned.localLayerCellBoundaryEdge_crossingPosition step

/-- Transporting the old-prefix component step through the stable coordinate
equivalence removes its ambient edge subtype exactly. -/
theorem localLayerOldPrefixProfileComponentStep_iff_finite
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (incoming : BoundedCorridorCutProfile 2 1 4)
    (pair : TrackedColorPair)
    (left right : LocalLayerFiniteConnectivityCoordinate) :
    aligned.localLayerOldPrefixProfileComponentStep incoming pair
        (aligned.localLayerFiniteConnectivityEquiv left)
        (aligned.localLayerFiniteConnectivityEquiv right) ↔
      localLayerFiniteOldPrefixStep incoming
        aligned.localLayerFiniteConnectivityGeometryCode pair left right := by
  simp only [localLayerOldPrefixProfileComponentStep,
    localLayerFiniteOldPrefixStep]
  constructor
  · intro hstep
    rcases hstep with heq | ⟨leftPort, rightPort, hleft, hright, hbit⟩
    · exact Or.inl (aligned.localLayerFiniteConnectivityEquiv.injective heq)
    · refine Or.inr ⟨leftPort, rightPort, ?_, ?_, hbit⟩
      · apply aligned.localLayerFiniteConnectivityEquiv.injective
        apply Subtype.ext
        exact (aligned.localLayerFiniteConnectivityEquiv_incomingPort_val
          leftPort).trans hleft
      · apply aligned.localLayerFiniteConnectivityEquiv.injective
        apply Subtype.ext
        exact (aligned.localLayerFiniteConnectivityEquiv_incomingPort_val
          rightPort).trans hright
  · intro hstep
    rcases hstep with heq | ⟨leftPort, rightPort, hleft, hright, hbit⟩
    · exact Or.inl (congrArg aligned.localLayerFiniteConnectivityEquiv heq)
    · refine Or.inr ⟨leftPort, rightPort, ?_, ?_, hbit⟩
      · have h := congrArg
          (fun coordinate =>
            (aligned.localLayerFiniteConnectivityEquiv coordinate).1) hleft
        simpa using h
      · have h := congrArg
          (fun coordinate =>
            (aligned.localLayerFiniteConnectivityEquiv coordinate).1) hright
        simpa using h

/-- Transporting the Cell component step through the stable coordinate
equivalence removes its ambient edge subtype exactly. -/
theorem localLayerCellCutProfileComponentStep_iff_finite
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (cellProfile : CorridorCutProfile 6 0 0)
    (pair : TrackedColorPair)
    (left right : LocalLayerFiniteConnectivityCoordinate) :
    aligned.localLayerCellCutProfileComponentStep cellProfile pair
        (aligned.localLayerFiniteConnectivityEquiv left)
        (aligned.localLayerFiniteConnectivityEquiv right) ↔
      localLayerFiniteCellStep cellProfile
        aligned.localLayerFiniteConnectivityGeometryCode pair left right := by
  simp only [localLayerCellCutProfileComponentStep,
    localLayerCellProfileComponentStep, localLayerFiniteCellStep]
  constructor
  · intro hstep
    rcases hstep with heq |
      ⟨leftPosition, rightPosition, hleft, hright, hbit⟩
    · exact Or.inl (aligned.localLayerFiniteConnectivityEquiv.injective heq)
    · refine Or.inr ⟨leftPosition, rightPosition, ?_, ?_, hbit⟩
      · apply aligned.localLayerFiniteConnectivityEquiv.injective
        apply Subtype.ext
        exact (aligned.localLayerFiniteConnectivityEquiv_cellPosition_val
          leftPosition).symm.trans hleft
      · apply aligned.localLayerFiniteConnectivityEquiv.injective
        apply Subtype.ext
        exact (aligned.localLayerFiniteConnectivityEquiv_cellPosition_val
          rightPosition).symm.trans hright
  · intro hstep
    rcases hstep with heq |
      ⟨leftPosition, rightPosition, hleft, hright, hbit⟩
    · exact Or.inl (congrArg aligned.localLayerFiniteConnectivityEquiv heq)
    · refine Or.inr ⟨leftPosition, rightPosition, ?_, ?_, hbit⟩
      · have h := congrArg
          (fun coordinate =>
            (aligned.localLayerFiniteConnectivityEquiv coordinate).1) hleft
        simpa using h
      · have h := congrArg
          (fun coordinate =>
            (aligned.localLayerFiniteConnectivityEquiv coordinate).1) hright
        simpa using h

/-- Every non-isolated vertex of the literal residual seam lies in the selected
eight-edge interface. -/
theorem localLayerSeamProfileGraph_support_subset
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (incoming : BoundedCorridorCutProfile 2 1 4)
    (cellProfile : CorridorCutProfile 6 0 0)
    (pair : TrackedColorPair) :
    (aligned.localLayerSeamProfileGraph incoming cellProfile pair).support ⊆
      (aligned.localLayerFiniteConnectivityInterface : Set G.edgeSet) := by
  intro edge hedge
  rcases (SimpleGraph.mem_support
    (aligned.localLayerSeamProfileGraph incoming cellProfile pair)).1 hedge with
    ⟨neighbor, hadj⟩
  rcases hadj with ⟨step, _hleft, _hright, horientation⟩
  rcases horientation with hforward | hbackward
  · rcases hforward with ⟨rfl, _⟩
    exact aligned.localLayerPrefixCrossing_mem_finiteConnectivityInterface step
  · rcases hbackward with ⟨rfl, _⟩
    exact aligned.nextLocalLayerPrefixCrossing_mem_finiteConnectivityInterface
      step

/-- The explicit stable-coordinate seam graph is graph-isomorphic to the
literal seam induced on its eight-edge support. -/
noncomputable def localLayerFiniteSeamGraphIso
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (incoming : BoundedCorridorCutProfile 2 1 4)
    (cellProfile : CorridorCutProfile 6 0 0)
    (pair : TrackedColorPair) :
    localLayerFiniteSeamGraph incoming cellProfile
        aligned.localLayerFiniteConnectivityGeometryCode pair ≃g
      (aligned.localLayerSeamProfileGraph incoming cellProfile pair).induce
        (aligned.localLayerFiniteConnectivityInterface : Set G.edgeSet) where
  toEquiv := aligned.localLayerFiniteConnectivityEquiv
  map_rel_iff' := by
    intro left right
    apply Iff.symm
    change
      (∃ step : Fin 2,
        IsTrackedColor (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2
            (incoming.profile.edgeColor step).toColor ∧
          IsTrackedColor (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2
            (cellProfile.edgeColor
              (aligned.localLayerFiniteConnectivityGeometryCode.outgoing
                step)).toColor ∧
          ((left = .inl step ∧
              right = aligned.localLayerFiniteConnectivityGeometryCode.outgoingPort
                step) ∨
            (left = aligned.localLayerFiniteConnectivityGeometryCode.outgoingPort
                step ∧ right = .inl step))) ↔
      ∃ step : Fin 2,
        IsTrackedColor (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2
            (incoming.profile.edgeColor step).toColor ∧
          IsTrackedColor (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2
            (cellProfile.edgeColor
              (aligned.localLayerCellCrossingPosition step)).toColor ∧
          (((aligned.localLayerFiniteConnectivityEquiv left).1 =
                aligned.toInterface.localLayerPrefixCrossing step ∧
              (aligned.localLayerFiniteConnectivityEquiv right).1 =
                aligned.toInterface.nextLocalLayerPrefixCrossing step) ∨
            ((aligned.localLayerFiniteConnectivityEquiv left).1 =
                aligned.toInterface.nextLocalLayerPrefixCrossing step ∧
              (aligned.localLayerFiniteConnectivityEquiv right).1 =
                aligned.toInterface.localLayerPrefixCrossing step))
    constructor
    · rintro ⟨step, hleftColor, hrightColor, horientation⟩
      refine ⟨step, hleftColor, ?_, ?_⟩
      · exact hrightColor
      · rcases horientation with hforward | hbackward
        · rcases hforward with ⟨rfl, rfl⟩
          exact Or.inl ⟨rfl,
            aligned.localLayerFiniteConnectivityEquiv_outgoingPort_val step⟩
        · rcases hbackward with ⟨rfl, rfl⟩
          exact Or.inr
            ⟨aligned.localLayerFiniteConnectivityEquiv_outgoingPort_val step,
              rfl⟩
    · rintro ⟨step, hleftColor, hrightColor, horientation⟩
      refine ⟨step, hleftColor, ?_, ?_⟩
      · exact hrightColor
      · rcases horientation with hforward | hbackward
        · refine Or.inl ⟨?_, ?_⟩
          · apply aligned.localLayerFiniteConnectivityEquiv.injective
            apply Subtype.ext
            exact hforward.1
          · apply aligned.localLayerFiniteConnectivityEquiv.injective
            apply Subtype.ext
            exact hforward.2.trans
              (aligned.localLayerFiniteConnectivityEquiv_outgoingPort_val
                step).symm
        · refine Or.inr ⟨?_, ?_⟩
          · apply aligned.localLayerFiniteConnectivityEquiv.injective
            apply Subtype.ext
            exact hbackward.1.trans
              (aligned.localLayerFiniteConnectivityEquiv_outgoingPort_val
                step).symm
          · apply aligned.localLayerFiniteConnectivityEquiv.injective
            apply Subtype.ext
            exact hbackward.2

/-- Reachability in the literal residual seam is exactly reachability in its
stable-coordinate graph. -/
theorem localLayerSeamProfileGraph_reachable_iff_finite
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (incoming : BoundedCorridorCutProfile 2 1 4)
    (cellProfile : CorridorCutProfile 6 0 0)
    (pair : TrackedColorPair)
    (left right : LocalLayerFiniteConnectivityCoordinate) :
    (aligned.localLayerSeamProfileGraph incoming cellProfile pair).Reachable
        (aligned.localLayerFiniteConnectivityEquiv left).1
        (aligned.localLayerFiniteConnectivityEquiv right).1 ↔
      (localLayerFiniteSeamGraph incoming cellProfile
        aligned.localLayerFiniteConnectivityGeometryCode pair).Reachable
          left right := by
  rw [← induce_reachable_iff_of_support_subset
    (aligned.localLayerSeamProfileGraph incoming cellProfile pair)
    aligned.localLayerFiniteConnectivityInterface
    (aligned.localLayerSeamProfileGraph_support_subset incoming cellProfile pair)
    (aligned.localLayerFiniteConnectivityEquiv left)
    (aligned.localLayerFiniteConnectivityEquiv right)]
  exact SimpleGraph.Iso.reachable_iff
    (φ := aligned.localLayerFiniteSeamGraphIso incoming cellProfile pair)

/-- The complete profile-derived component step is exactly its graph-free
stable-coordinate relation. -/
theorem localLayerFiniteProfileComponentStep_iff_coordinateStep
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (incoming : BoundedCorridorCutProfile 2 1 4)
    (cellProfile : CorridorCutProfile 6 0 0)
    (pair : TrackedColorPair)
    (left right : LocalLayerFiniteConnectivityCoordinate) :
    aligned.localLayerFiniteProfileComponentStep incoming cellProfile pair
        (aligned.localLayerFiniteConnectivityEquiv left)
        (aligned.localLayerFiniteConnectivityEquiv right) ↔
      localLayerFiniteConnectivityStep incoming cellProfile
        aligned.localLayerFiniteConnectivityGeometryCode pair left right := by
  simp only [localLayerFiniteProfileComponentStep,
    localLayerFiniteConnectivityStep]
  rw [aligned.localLayerOldPrefixProfileComponentStep_iff_finite,
    aligned.localLayerCellCutProfileComponentStep_iff_finite,
    aligned.localLayerSeamProfileGraph_reachable_iff_finite]

/-- Actual graph-derived profiles satisfy the graph-free connectivity update
with the finite geometry code extracted from the same literal Cell. -/
theorem localLayerFiniteConnectivityUpdateCode
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (color : embedded.cellulation.rotation.toRotationSystem.EdgeColoring Color)
    (hcolor : embedded.cellulation.rotation.toRotationSystem
      |>.IsTaitEdgeColoring color)
    (hleftColor : ∀ step,
      color (aligned.toInterface.localLayerPrefixCrossing step) ≠ 0)
    (hrightColor : ∀ step,
      color (aligned.toInterface.nextLocalLayerPrefixCrossing step) ≠ 0) :
    LocalLayerFiniteConnectivityUpdateCode
      (aligned.localLayerLeftPrefixSharedRungBoundedProfile color hleftColor)
      (aligned.localLayerCellBoundaryProfile color hcolor)
      aligned.localLayerFiniteConnectivityGeometryCode
      (aligned.toInterface.localLayerRightPrefixBoundedProfile color
        hrightColor) := by
  let incoming := aligned.localLayerLeftPrefixSharedRungBoundedProfile color
    hleftColor
  let cellProfile := aligned.localLayerCellBoundaryProfile color hcolor
  let output := aligned.toInterface.localLayerRightPrefixBoundedProfile color
    hrightColor
  intro pair first second
  have hupdate := aligned.localLayerFiniteConnectivityUpdate
    hcubic hrotation color hcolor hleftColor hrightColor pair first second
  have hfirst :
      (⟨aligned.toInterface.nextLocalLayerPrefixCrossing first,
          aligned.nextLocalLayerPrefixCrossing_mem_finiteConnectivityInterface
            first⟩ :
        { edge // edge ∈ aligned.localLayerFiniteConnectivityInterface }) =
        aligned.localLayerFiniteConnectivityEquiv
          (aligned.localLayerFiniteConnectivityGeometryCode.outgoingPort
            first) := by
    apply Subtype.ext
    exact (aligned.localLayerFiniteConnectivityEquiv_outgoingPort_val first).symm
  have hsecond :
      (⟨aligned.toInterface.nextLocalLayerPrefixCrossing second,
          aligned.nextLocalLayerPrefixCrossing_mem_finiteConnectivityInterface
            second⟩ :
        { edge // edge ∈ aligned.localLayerFiniteConnectivityInterface }) =
        aligned.localLayerFiniteConnectivityEquiv
          (aligned.localLayerFiniteConnectivityGeometryCode.outgoingPort
            second) := by
    apply Subtype.ext
    exact (aligned.localLayerFiniteConnectivityEquiv_outgoingPort_val second).symm
  rw [hfirst, hsecond] at hupdate
  have hclosure := reflTransGen_equiv_iff
    aligned.localLayerFiniteConnectivityEquiv
    (aligned.localLayerFiniteProfileComponentStep incoming cellProfile pair)
    (localLayerFiniteConnectivityStep incoming cellProfile
      aligned.localLayerFiniteConnectivityGeometryCode pair)
    (aligned.localLayerFiniteProfileComponentStep_iff_coordinateStep
      incoming cellProfile pair)
    (aligned.localLayerFiniteConnectivityGeometryCode.outgoingPort first)
    (aligned.localLayerFiniteConnectivityGeometryCode.outgoingPort second)
  rw [hclosure] at hupdate
  exact hupdate

/-- Tait nonzeroness supplies the two displayed-cut premises of the exact
graph-free connectivity update. -/
theorem localLayerFiniteConnectivityUpdateCode_of_tait
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (color : embedded.cellulation.rotation.toRotationSystem.EdgeColoring Color)
    (hcolor : embedded.cellulation.rotation.toRotationSystem
      |>.IsTaitEdgeColoring color) :
    LocalLayerFiniteConnectivityUpdateCode
      (aligned.localLayerLeftPrefixSharedRungBoundedProfile color
        (fun step => hcolor
          (aligned.toInterface.localLayerPrefixCrossing step)))
      (aligned.localLayerCellBoundaryProfile color hcolor)
      aligned.localLayerFiniteConnectivityGeometryCode
      (aligned.toInterface.localLayerRightPrefixBoundedProfile color
        (fun step => hcolor
          (aligned.toInterface.nextLocalLayerPrefixCrossing step))) := by
  exact aligned.localLayerFiniteConnectivityUpdateCode hcubic hrotation color
    hcolor
    (fun step => hcolor (aligned.toInterface.localLayerPrefixCrossing step))
    (fun step => hcolor
      (aligned.toInterface.nextLocalLayerPrefixCrossing step))

end SourceCornerAlignedSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor

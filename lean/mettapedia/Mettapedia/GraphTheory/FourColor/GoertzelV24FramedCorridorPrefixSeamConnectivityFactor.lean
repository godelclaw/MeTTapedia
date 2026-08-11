import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorPrefixCellConnectivityFactor

/-!
# Factoring the source Cell seam through finite profile colors

The residual graph between the cumulative prefix and the next hexagonal
Cell consists exactly of two source-ordered corner turns.  This module reads
the colors gating those turns from the incoming cut profile and the existing
six-edge Cell profile, then proves that the resulting finite relation is the
literal seam graph.

No successor profile is selected.  The construction only removes the final
ambient-color dependency from the connectivity update; full face-profile
transport remains a separate obligation.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24CorridorProfile
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24HexCorridorFiniteColorTransition
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorPrefixSeamConnectivityFactorEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

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

/-- The unique six-cycle coordinate of one newly exposed source crossing. -/
noncomputable def localLayerCellCrossingPosition
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) (step : Fin 2) : Fin 6 :=
  Classical.choose
    ((aligned.mem_finiteConnectivityInterface_inter_cellBoundary_iff_exists_position
      (aligned.toInterface.nextLocalLayerPrefixCrossing step)).1
      (Finset.mem_inter.2
        ⟨aligned.nextLocalLayerPrefixCrossing_mem_finiteConnectivityInterface
            step,
          aligned.nextLocalLayerPrefixCrossing_mem_cellBoundaryRegion step⟩))

@[simp]
theorem localLayerCellBoundaryEdge_crossingPosition
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) (step : Fin 2) :
    aligned.localLayerCellBoundaryEdge
        (aligned.localLayerCellCrossingPosition step) =
      aligned.toInterface.nextLocalLayerPrefixCrossing step :=
  Classical.choose_spec
    ((aligned.mem_finiteConnectivityInterface_inter_cellBoundary_iff_exists_position
      (aligned.toInterface.nextLocalLayerPrefixCrossing step)).1
      (Finset.mem_inter.2
        ⟨aligned.nextLocalLayerPrefixCrossing_mem_finiteConnectivityInterface
            step,
          aligned.nextLocalLayerPrefixCrossing_mem_cellBoundaryRegion step⟩))

/-- The established six-edge placed-hex profile, now retained as one full
profile so its cut colors and connectivity matrix are read from one state. -/
noncomputable def localLayerCellBoundaryProfile
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (color : embedded.cellulation.rotation.toRotationSystem.EdgeColoring Color)
    (hcolor : embedded.cellulation.rotation.toRotationSystem
      |>.IsTaitEdgeColoring color) : CorridorCutProfile 6 0 0 :=
  placedHexBoundaryCutProfile aligned.localLayerCellPlacement
    aligned.toInterface.localLayerCellBoundaryRegion color hcolor

@[simp]
theorem localLayerCellBoundaryProfile_edgeColor_toColor
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (color : embedded.cellulation.rotation.toRotationSystem.EdgeColoring Color)
    (hcolor : embedded.cellulation.rotation.toRotationSystem
      |>.IsTaitEdgeColoring color) (position : Fin 6) :
    ((aligned.localLayerCellBoundaryProfile color hcolor).edgeColor
        position).toColor =
      color (aligned.localLayerCellBoundaryEdge position) := by
  simp [localLayerCellBoundaryProfile, localLayerCellBoundaryEdge]

@[simp]
theorem localLayerLeftPrefixSharedRungBoundedProfile_edgeColor_toColor
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (color : G.edgeSet → Color)
    (hcolor : ∀ step,
      color (aligned.toInterface.localLayerPrefixCrossing step) ≠ 0)
    (step : Fin 2) :
    (((aligned.localLayerLeftPrefixSharedRungBoundedProfile color hcolor)
        |>.profile.edgeColor step).toColor) =
      color (aligned.toInterface.localLayerPrefixCrossing step) := by
  change
    ((aligned.localLayerLeftPrefixSharedRungGraphCutData
      |>.regionalProfile color _).edgeColor step).toColor = _
  exact aligned.localLayerLeftPrefixSharedRungGraphCutData
    |>.regionalProfile_edgeColor_toColor color _ step

/-- The finite residual seam graph.  Its two possible edges are determined
only by the source positions and the two profiles' stored cut colors. -/
def localLayerSeamProfileGraph
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (incoming : BoundedCorridorCutProfile 2 1 4)
    (cellProfile : CorridorCutProfile 6 0 0)
    (pair : TrackedColorPair) : SimpleGraph G.edgeSet where
  Adj left right :=
    ∃ step : Fin 2,
      IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (incoming.profile.edgeColor step).toColor ∧
        IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (cellProfile.edgeColor
            (aligned.localLayerCellCrossingPosition step)).toColor ∧
        ((left = aligned.toInterface.localLayerPrefixCrossing step ∧
            right = aligned.toInterface.nextLocalLayerPrefixCrossing step) ∨
          (left = aligned.toInterface.nextLocalLayerPrefixCrossing step ∧
            right = aligned.toInterface.localLayerPrefixCrossing step))
  symm := ⟨by
    rintro left right ⟨step, hleftColor, hrightColor, horientation⟩
    refine ⟨step, hleftColor, hrightColor, ?_⟩
    rcases horientation with hforward | hbackward
    · exact Or.inr ⟨hforward.2, hforward.1⟩
    · exact Or.inl ⟨hbackward.2, hbackward.1⟩⟩
  loopless := ⟨by
    intro edge hedge
    rcases hedge with ⟨step, _hleftColor, _hrightColor, horientation⟩
    have heq : aligned.toInterface.localLayerPrefixCrossing step =
        aligned.toInterface.nextLocalLayerPrefixCrossing step := by
      rcases horientation with hforward | hbackward
      · exact hforward.1.symm.trans hforward.2
      · exact hbackward.2.symm.trans hbackward.1
    exact aligned.localLayerPrefixCrossing_not_mem_cellBoundaryRegion step
      (by
        rw [heq]
        exact aligned.nextLocalLayerPrefixCrossing_mem_cellBoundaryRegion step)⟩

/-- For an actual Tait coloring, the profile-derived two-turn graph is
definitionally the same graph as the literal residual seam. -/
theorem localLayerTrackedSeamGraph_eq_profileGraph
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
    (pair : TrackedColorPair) :
    aligned.toInterface.localLayerTrackedSeamGraph color
        (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2 =
      aligned.localLayerSeamProfileGraph
        (aligned.localLayerLeftPrefixSharedRungBoundedProfile color
          hleftColor)
        (aligned.localLayerCellBoundaryProfile color hcolor) pair := by
  ext left right
  rw [aligned.localLayerTrackedSeamGraph_adj_iff_exists_crossing_step
    hcubic hrotation]
  constructor
  · rintro ⟨step, hleftColor, hrightColor, horientation⟩
    refine ⟨step, ?_, ?_, horientation⟩
    · simpa using hleftColor
    · simpa using hrightColor
  · rintro ⟨step, hleftColor, hrightColor, horientation⟩
    refine ⟨step, ?_, ?_, horientation⟩
    · simpa using hleftColor
    · simpa using hrightColor

/-- Read the Cell component move from the connectivity coordinate of its
single full six-edge profile. -/
def localLayerCellCutProfileComponentStep
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (cellProfile : CorridorCutProfile 6 0 0)
    (pair : TrackedColorPair)
    (left right : Subtype fun edge =>
      edge ∈ aligned.localLayerFiniteConnectivityInterface) : Prop :=
  aligned.localLayerCellProfileComponentStep
    (fun tracked first second =>
      cellProfile.strandConnected tracked (.inl first) (.inl second))
    pair left right

@[simp]
theorem localLayerCellBoundaryProfile_strandConnected
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (color : embedded.cellulation.rotation.toRotationSystem.EdgeColoring Color)
    (hcolor : embedded.cellulation.rotation.toRotationSystem
      |>.IsTaitEdgeColoring color)
    (pair : TrackedColorPair) (left right : Fin 6) :
    (aligned.localLayerCellBoundaryProfile color hcolor).strandConnected pair
        (.inl left) (.inl right) =
      aligned.localLayerCellConnectivityProfile color pair left right :=
  rfl

/-- The complete finite connectivity step for one source Cell.  All three
factors are now read from the incoming and Cell profiles; no cumulative graph
or ambient color function occurs in this relation. -/
def localLayerFiniteProfileComponentStep
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (incoming : BoundedCorridorCutProfile 2 1 4)
    (cellProfile : CorridorCutProfile 6 0 0)
    (pair : TrackedColorPair)
    (left right : Subtype fun edge =>
      edge ∈ aligned.localLayerFiniteConnectivityInterface) : Prop :=
  aligned.localLayerOldPrefixProfileComponentStep incoming pair left right ∨
    aligned.localLayerCellCutProfileComponentStep cellProfile pair left right ∨
    (aligned.localLayerSeamProfileGraph incoming cellProfile pair).Reachable
      left right

/-- For actual graph-derived profiles, the partially factored relation from
the preceding module is exactly the fully profile-derived relation. -/
theorem localLayerIncomingAndCellProfileFactoredComponentStep_iff_finiteProfileStep
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
    (pair : TrackedColorPair)
    (left right : Subtype fun edge =>
      edge ∈ aligned.localLayerFiniteConnectivityInterface) :
    aligned.localLayerIncomingAndCellProfileFactoredComponentStep
        (aligned.localLayerLeftPrefixSharedRungBoundedProfile color hleftColor)
        (aligned.localLayerCellConnectivityProfile color) color pair
        left right ↔
      aligned.localLayerFiniteProfileComponentStep
        (aligned.localLayerLeftPrefixSharedRungBoundedProfile color hleftColor)
        (aligned.localLayerCellBoundaryProfile color hcolor) pair left right := by
  have hseam := aligned.localLayerTrackedSeamGraph_eq_profileGraph
    hcubic hrotation color hcolor hleftColor pair
  constructor
  · intro hstep
    rcases hstep with hold | hcell | hseamReach
    · exact Or.inl hold
    · exact Or.inr (Or.inl (by
        simpa [localLayerCellCutProfileComponentStep] using hcell))
    · exact Or.inr (Or.inr (by
        rw [← hseam]
        exact hseamReach))
  · intro hstep
    rcases hstep with hold | hcell | hseamReach
    · exact Or.inl hold
    · exact Or.inr (Or.inl (by
        simpa [localLayerCellCutProfileComponentStep] using hcell))
    · exact Or.inr (Or.inr (by
        rw [hseam]
        exact hseamReach))

/-- The source Cell's actual outgoing tracked connectivity is the closure of
a relation computed entirely from the incoming terminal-aware profile and
the six-edge Cell profile. -/
theorem localLayerRightPrefixTrackedGraph_reachable_iff_finiteProfileClosure
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
    (pair : TrackedColorPair) (left right : Fin 2) :
    (regionalTrackedEdgeGraph
        embedded.cellulation.rotation.toRotationSystem
        aligned.toInterface.localLayerRightPrefixRegion color
        (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2).Reachable
      (aligned.toInterface.nextLocalLayerPrefixCrossing left)
      (aligned.toInterface.nextLocalLayerPrefixCrossing right) ↔
    Relation.ReflTransGen
      (aligned.localLayerFiniteProfileComponentStep
        (aligned.localLayerLeftPrefixSharedRungBoundedProfile color hleftColor)
        (aligned.localLayerCellBoundaryProfile color hcolor) pair)
      ⟨aligned.toInterface.nextLocalLayerPrefixCrossing left,
        aligned.nextLocalLayerPrefixCrossing_mem_finiteConnectivityInterface
          left⟩
      ⟨aligned.toInterface.nextLocalLayerPrefixCrossing right,
        aligned.nextLocalLayerPrefixCrossing_mem_finiteConnectivityInterface
          right⟩ := by
  rw [aligned.localLayerRightPrefixTrackedGraph_reachable_iff_incomingAndCellProfileFactoredClosure
    hcubic hrotation color hleftColor pair left right]
  constructor
  · intro hclosure
    exact hclosure.mono (by
      intro first second hstep
      exact (aligned.localLayerIncomingAndCellProfileFactoredComponentStep_iff_finiteProfileStep
        hcubic hrotation color hcolor hleftColor pair first second).1 hstep)
  · intro hclosure
    exact hclosure.mono (by
      intro first second hstep
      exact (aligned.localLayerIncomingAndCellProfileFactoredComponentStep_iff_finiteProfileStep
        hcubic hrotation color hcolor hleftColor pair first second).2 hstep)

end SourceCornerAlignedSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor

import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorPrefixFiniteConnectivityInterface
import Mettapedia.GraphTheory.FourColor.GoertzelV24GraphDerivedTerminalProfile

/-!
# A shared-rung terminal for cumulative corridor connectivity

The incoming source cut has two crossing edges, but the old-prefix factor in
the one-Cell connectivity contraction may also be entered through the shared
rung.  This module records that rung as one genuine terminal of the incoming
graph-derived profile.  The region and all occurrence-sensitive face
fragments are unchanged.

This is a minimal interface refinement.  It does not identify the cumulative
prefix with the newly exposed Cell, choose a successor profile, or assert a
deterministic transfer.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24CorridorProfile
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24GraphDerivedTerminalProfile
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorPrefixTerminalConnectivityEdgeSetDecidableEq :
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

/-- The single extra old-prefix port is the actual rung shared with the new
source hexagon. -/
def localLayerLeftPrefixSharedRungTerminalEdge
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) (_terminal : Fin 1) : G.edgeSet :=
  aligned.toInterface.localLayerSharedRungEdge

/-- The old cumulative cut with its shared rung retained as one terminal.
Only the port family changes; the regional edge set and face fragments are
definitionally those of the established incoming cut. -/
noncomputable def localLayerLeftPrefixSharedRungGraphCutData
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) :=
  withTerminalEdges aligned.toInterface.localLayerLeftPrefixGraphCutData
    aligned.localLayerLeftPrefixSharedRungTerminalEdge

@[simp] theorem localLayerLeftPrefixSharedRungGraphCutData_regionEdges
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    aligned.localLayerLeftPrefixSharedRungGraphCutData.regionEdges =
      aligned.toInterface.localLayerLeftPrefixRegion :=
  rfl

@[simp] theorem localLayerLeftPrefixSharedRungGraphCutData_crossingEdge
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) (crossing : Fin 2) :
    aligned.localLayerLeftPrefixSharedRungGraphCutData.crossingEdge crossing =
      aligned.toInterface.localLayerPrefixCrossing crossing :=
  rfl

@[simp] theorem localLayerLeftPrefixSharedRungGraphCutData_terminalEdge
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) (terminal : Fin 1) :
    aligned.localLayerLeftPrefixSharedRungGraphCutData.terminalEdge terminal =
      aligned.toInterface.localLayerSharedRungEdge :=
  rfl

@[simp] theorem localLayerLeftPrefixSharedRungGraphCutData_portEdge_crossing
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) (crossing : Fin 2) :
    aligned.localLayerLeftPrefixSharedRungGraphCutData.portEdge (.inl crossing) =
      aligned.toInterface.localLayerPrefixCrossing crossing :=
  rfl

@[simp] theorem localLayerLeftPrefixSharedRungGraphCutData_portEdge_terminal
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) (terminal : Fin 1) :
    aligned.localLayerLeftPrefixSharedRungGraphCutData.portEdge (.inr terminal) =
      aligned.toInterface.localLayerSharedRungEdge :=
  rfl

/-- Both old cut edges and the newly named rung are actual edges of the old
cumulative prefix. -/
theorem localLayerLeftPrefixSharedRungGraphCutData_portsInRegion
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    aligned.localLayerLeftPrefixSharedRungGraphCutData.PortsInRegion := by
  rw [localLayerLeftPrefixSharedRungGraphCutData,
    withTerminalEdges_portsInRegion_iff]
  exact ⟨aligned.toInterface.localLayerLeftPrefixGraphCutData_portsInRegion,
    fun _ => aligned.toInterface.localLayerSharedRungEdge_mem_leftPrefix⟩

/-- The incoming cut edges are distinct from one another and from the shared
rung, so the three old-prefix ports are honest coordinates. -/
theorem localLayerLeftPrefixSharedRungGraphCutData_portsInjective
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    aligned.localLayerLeftPrefixSharedRungGraphCutData.PortsInjective := by
  rw [localLayerLeftPrefixSharedRungGraphCutData,
    withTerminalEdges_portsInjective_iff]
  refine ⟨aligned.toInterface.localLayerPrefixCrossing_injective, ?_, ?_⟩
  · intro first second _heq
    exact Subsingleton.elim first second
  · intro crossing terminal
    change aligned.toInterface.localLayerPrefixCrossing crossing ≠
      aligned.toInterface.localLayerSharedRungEdge
    exact aligned.localLayerPrefixCrossing_ne_sharedRungEdge crossing

/-- Terminal augmentation leaves the already validated regional face
fragments untouched. -/
theorem localLayerLeftPrefixSharedRungGraphCutData_fragmentsOnFaceInRegion
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    aligned.localLayerLeftPrefixSharedRungGraphCutData
      |>.FragmentsOnFaceInRegion := by
  rw [localLayerLeftPrefixSharedRungGraphCutData,
    withTerminalEdges_fragmentsOnFaceInRegion_iff]
  exact regionalBoundaryGraphCutData_fragmentsOnFaceInRegion
    embedded.cellulation.rotation.toRotationSystem
    aligned.toInterface.localLayerLeftPrefixRegion
    aligned.toInterface.localLayerPrefixCrossing

/-- The complete incoming source-prefix profile with one additional seam
terminal.  Its fragment count remains bounded by four because terminal
augmentation does not change the displayed crossing cut. -/
noncomputable def localLayerLeftPrefixSharedRungBoundedProfile
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (color : G.edgeSet → Color)
    (hcolor : ∀ crossing,
      color (aligned.toInterface.localLayerPrefixCrossing crossing) ≠ 0) :
    BoundedCorridorCutProfile 2 1 4 where
  faceFragmentCount :=
    (aligned.toInterface.localLayerLeftPrefixBoundedProfile color hcolor)
      |>.faceFragmentCount
  profile :=
    aligned.localLayerLeftPrefixSharedRungGraphCutData.regionalProfile color
      (fun crossing => by simpa using hcolor crossing)

/-- Every connectivity bit of the refined profile has the literal
old-prefix meaning, including queries from an incoming cut edge to the
shared-rung terminal. -/
theorem localLayerLeftPrefixSharedRungBoundedProfile_strandConnected_eq_true_iff
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (color : G.edgeSet → Color)
    (hcolor : ∀ crossing,
      color (aligned.toInterface.localLayerPrefixCrossing crossing) ≠ 0)
    (pair : TrackedColorPair) (left right : CorridorPort 2 1) :
    (((aligned.localLayerLeftPrefixSharedRungBoundedProfile color hcolor)
        |>.profile.strandConnected pair left right) = true) ↔
      IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (color (aligned.localLayerLeftPrefixSharedRungGraphCutData
            |>.portEdge left)) ∧
        IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (color (aligned.localLayerLeftPrefixSharedRungGraphCutData
            |>.portEdge right)) ∧
        (regionalTrackedEdgeGraph
          embedded.cellulation.rotation.toRotationSystem
          aligned.toInterface.localLayerLeftPrefixRegion color
          (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2).Reachable
            (aligned.localLayerLeftPrefixSharedRungGraphCutData
              |>.portEdge left)
            (aligned.localLayerLeftPrefixSharedRungGraphCutData
              |>.portEdge right) := by
  let data := aligned.localLayerLeftPrefixSharedRungGraphCutData
  change ((data.regionalProfile color _).strandConnected pair left right = true) ↔ _
  rw [data.regionalProfile_strandConnected_eq_true_iff]
  have hleft : data.portEdge left ∈ data.regionEdges :=
    aligned.localLayerLeftPrefixSharedRungGraphCutData_portsInRegion left
  have hright : data.portEdge right ∈ data.regionEdges :=
    aligned.localLayerLeftPrefixSharedRungGraphCutData_portsInRegion right
  simp only [hleft, hright, true_and]
  rfl

/-- An edge belongs both to the finite one-Cell interface and to the old
prefix exactly when it is represented by one of the two incoming ports or
by the shared-rung terminal. -/
theorem mem_finiteConnectivityInterface_inter_leftPrefix_iff_exists_port
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) (edge : G.edgeSet) :
    edge ∈ aligned.localLayerFiniteConnectivityInterface ∩
        aligned.toInterface.localLayerLeftPrefixRegion ↔
      ∃ port : CorridorPort 2 1,
        aligned.localLayerLeftPrefixSharedRungGraphCutData.portEdge port =
          edge := by
  constructor
  · intro hedge
    rcases Finset.mem_inter.1 hedge with ⟨hfinite, hleft⟩
    rcases Finset.mem_union.1 hfinite with hcrossing | hcell
    · rcases (mem_indexedCrossingEdgeSet_iff
        aligned.toInterface.localLayerPrefixCrossing edge).1 hcrossing with
        ⟨crossing, hcrossingEdge⟩
      exact ⟨.inl crossing, by simpa using hcrossingEdge⟩
    · have hinter : edge ∈
          aligned.toInterface.localLayerLeftPrefixRegion ∩
            aligned.toInterface.localLayerCellBoundaryRegion :=
        Finset.mem_inter.2 ⟨hleft, hcell⟩
      rw [aligned.toInterface.localLayerLeftPrefixRegion_inter_cellBoundary_eq_singleton]
        at hinter
      exact ⟨.inr (0 : Fin 1), by
        simpa using (Finset.mem_singleton.1 hinter).symm⟩
  · rintro ⟨port, rfl⟩
    rcases port with crossing | terminal
    · exact Finset.mem_inter.2
        ⟨aligned.localLayerPrefixCrossing_mem_finiteConnectivityInterface
            crossing,
          aligned.localLayerPrefixCrossing_mem_leftPrefixRegion crossing⟩
    · exact Finset.mem_inter.2
        ⟨aligned.localLayerCellBoundaryRegion_subset_finiteConnectivityInterface
            aligned.toInterface.localLayerSharedRungEdge_mem_cellBoundary,
          aligned.toInterface.localLayerSharedRungEdge_mem_leftPrefix⟩

end SourceCornerAlignedSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor

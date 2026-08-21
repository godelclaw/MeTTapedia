import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorFiniteConnectivityCode

/-!
# A joint finite receipt for one literal source Cell

The source letter is heterogeneous: each literal Cell carries its own local
six-edge profile.  This module does not quotient those letters by their coarse
three-way orientation.  Instead it joins, for one literal Cell and one Tait
coloring, the two finite halves already proved independently:

* the tracked-connectivity update on `Fin 2 ⊕ Fin 6`;
* the three-role face attachment and capped-progress table.

The joint receipt accounts for all five profile coordinates.  It is a finite
necessary image of the exact literal support relation.  The converse adequacy
theorem—showing which abstract receipts are realized by a literal Cell—is not
asserted here and remains necessary before an abstract reachable-closure
measurement can replace the source semantics.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24CorridorProfile
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24WindingClassification
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorFiniteOneCellSupportEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Re-embed a three-bound profile in the preceding four-bound interface.
Only the proof-carrying outer bound changes. -/
def widenFaceFragmentBoundThreeToFour
    {crossingEdgeCount terminalCount : Nat}
    (profile : BoundedCorridorCutProfile crossingEdgeCount terminalCount 3) :
    BoundedCorridorCutProfile crossingEdgeCount terminalCount 4 where
  faceFragmentCount :=
    ⟨profile.faceFragmentCount.val,
      Nat.lt_succ_of_lt profile.faceFragmentCount.isLt⟩
  profile := profile.profile

/-- Narrowing a four-bound profile known to have at most three fragments and
then restoring the outer bound is exact. -/
@[simp]
theorem widenFaceFragmentBoundThreeToFour_narrow
    {crossingEdgeCount terminalCount : Nat}
    (profile : BoundedCorridorCutProfile crossingEdgeCount terminalCount 4)
    (hbound : profile.faceFragmentCount.val ≤ 3) :
    widenFaceFragmentBoundThreeToFour
        (GoertzelV24FramedCorridorThreeFacePrefixProfileRepeat.narrowFaceFragmentBound
          profile hbound) = profile := by
  cases profile
  rfl

/-- The connectivity law at the proved three-face state bounds.  The face
bound is proof-carrying only; the relation reads just the stored profiles. -/
def LocalLayerFiniteConnectivityUpdateCodeThree
    (incoming : BoundedCorridorCutProfile 2 1 3)
    (cellProfile : CorridorCutProfile 6 0 0)
    (geometry : LocalLayerFiniteConnectivityGeometryCode)
    (output : BoundedCorridorCutProfile 2 0 3) : Prop :=
  LocalLayerFiniteConnectivityUpdateCode
    (widenFaceFragmentBoundThreeToFour incoming)
    cellProfile geometry
    (widenFaceFragmentBoundThreeToFour output)

/-- Finite data carried by a one-Cell receipt. -/
structure LocalLayerFiniteOneCellCode
    (incoming : BoundedCorridorCutProfile 2 1 4)
    (output : BoundedCorridorCutProfile 2 0 4) where
  cellProfile : CorridorCutProfile 6 0 0
  geometry : LocalLayerFiniteConnectivityGeometryCode
  roleIndex : LocalLayerRightFaceRole ≃ Fin output.faceFragmentCount.val
  faceUpdate : LocalLayerFiniteFaceUpdateCode incoming.faceFragmentCount.val
  deriving DecidableEq, Fintype

/-- Complete graph-free receipt carried by one supported literal source Cell.
The role equivalence records the semantic `first`/`center`/`second` names even
when the dependent profile carrier chose a different finite enumeration. -/
def LocalLayerFiniteOneCellReceipt
    (incoming : BoundedCorridorCutProfile 2 1 4)
    (output : BoundedCorridorCutProfile 2 0 4) : Prop :=
  ∃ code : LocalLayerFiniteOneCellCode incoming output,
    output.faceFragmentCount.val = 3 ∧
      (∀ step : Fin 2,
        output.profile.edgeColor step =
          code.cellProfile.edgeColor (code.geometry.outgoing step)) ∧
      LocalLayerFiniteConnectivityUpdateCode
        incoming code.cellProfile code.geometry output ∧
      (∀ left right : LocalLayerRightFaceRole,
        output.profile.faceContinues
            (code.roleIndex left) (code.roleIndex right) = true ↔
          left = right) ∧
      (∀ (role : LocalLayerRightFaceRole) (step : Fin 2),
        output.profile.fragmentContainsPort
            (code.roleIndex role) (.inl step) = true ↔
          role.ContainsPort step) ∧
      (∀ role : LocalLayerRightFaceRole,
        (output.profile.faceLengthCap (code.roleIndex role)).val =
          (code.faceUpdate role).updatedCap
            incoming.profile.faceLengthCap role)

/-- The same joint receipt on the proved three-face state carriers. -/
def LocalLayerFiniteOneCellReceiptThree
    (incoming : BoundedCorridorCutProfile 2 1 3)
    (output : BoundedCorridorCutProfile 2 0 3) : Prop :=
  LocalLayerFiniteOneCellReceipt
    (widenFaceFragmentBoundThreeToFour incoming)
    (widenFaceFragmentBoundThreeToFour output)

namespace SourceTrail

namespace AnnularEmbedding

namespace SourceConsecutiveSlabInterface

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

/-- Semantic face roles as an actual equivalence with the dependent outgoing
profile coordinates. -/
noncomputable def localLayerRightFaceRoleIndexEquiv
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    LocalLayerRightFaceRole ≃
      Fin (Fintype.card (BoundaryRegionalFragment
        embedded.cellulation.rotation.toRotationSystem
        (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)
        interface.localLayerRightPrefixRegion)) :=
  interface.localLayerRightFaceRoleEquivBoundaryFragment.trans
    (Fintype.equivFin _)

@[simp]
theorem localLayerRightFaceRoleIndexEquiv_apply
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) (role : LocalLayerRightFaceRole) :
    interface.localLayerRightFaceRoleIndexEquiv role =
      interface.localLayerRightFaceRoleIndex role :=
  rfl

/-- The dependent face count stored by the bounded output profile is the
literal outgoing boundary-fragment cardinality. -/
@[simp]
theorem localLayerRightPrefixBoundedProfile_faceFragmentCount_val
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (color : G.edgeSet → Color)
    (hcolor : ∀ step,
      color (interface.nextLocalLayerPrefixCrossing step) ≠ 0) :
    (interface.localLayerRightPrefixBoundedProfile color hcolor
      ).faceFragmentCount.val =
      Fintype.card (BoundaryRegionalFragment
        embedded.cellulation.rotation.toRotationSystem
        (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)
        interface.localLayerRightPrefixRegion) :=
  rfl

/-- Semantic roles reindexed directly into the dependent bounded-profile
carrier. -/
noncomputable def localLayerRightFaceRoleEquivBoundedIndex
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (color : G.edgeSet → Color)
    (hcolor : ∀ step,
      color (interface.nextLocalLayerPrefixCrossing step) ≠ 0) :
    LocalLayerRightFaceRole ≃
      Fin (interface.localLayerRightPrefixBoundedProfile color hcolor
        ).faceFragmentCount.val :=
  interface.localLayerRightFaceRoleIndexEquiv.trans
    (Equiv.cast (congrArg Fin
      (interface.localLayerRightPrefixBoundedProfile_faceFragmentCount_val
        color hcolor).symm))

@[simp]
theorem localLayerRightFaceRoleEquivBoundedIndex_apply
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (color : G.edgeSet → Color)
    (hcolor : ∀ step,
      color (interface.nextLocalLayerPrefixCrossing step) ≠ 0)
    (role : LocalLayerRightFaceRole) :
    interface.localLayerRightFaceRoleEquivBoundedIndex color hcolor role =
      interface.localLayerRightFaceRoleIndex role := by
  rfl

end SourceConsecutiveSlabInterface

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

/-- The narrowed actual profiles obey the same graph-free connectivity law as
their four-bound presentations. -/
theorem localLayerFiniteConnectivityUpdateCodeThree_of_tait
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
    LocalLayerFiniteConnectivityUpdateCodeThree
      (aligned.localLayerFiniteInputProfile color hleftColor)
      (aligned.localLayerCellBoundaryProfile color hcolor)
      aligned.localLayerFiniteConnectivityGeometryCode
      (aligned.localLayerFiniteOutputProfile color hrightColor) := by
  simpa only [LocalLayerFiniteConnectivityUpdateCodeThree,
    localLayerFiniteInputProfile, localLayerFiniteOutputProfile,
    widenFaceFragmentBoundThreeToFour_narrow]
    using
    aligned.localLayerFiniteConnectivityUpdateCode
      hcubic hrotation color hcolor hleftColor hrightColor

/-- Every actual Tait-colored source Cell produces one joint finite receipt
whose connectivity and face tables arise from that same coloring. -/
theorem exists_localLayerFiniteOneCellReceipt
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
    LocalLayerFiniteOneCellReceipt
      (aligned.localLayerLeftPrefixSharedRungBoundedProfile color hleftColor)
      (aligned.toInterface.localLayerRightPrefixBoundedProfile color
        hrightColor) := by
  rcases aligned.exists_localLayerFiniteFaceUpdateCode hcubic hrotation color
      hleftColor hrightColor with ⟨faceUpdate, hfaceUpdate⟩
  let code : LocalLayerFiniteOneCellCode
      (aligned.localLayerLeftPrefixSharedRungBoundedProfile color hleftColor)
      (aligned.toInterface.localLayerRightPrefixBoundedProfile color
        hrightColor) := {
    cellProfile := aligned.localLayerCellBoundaryProfile color hcolor
    geometry := aligned.localLayerFiniteConnectivityGeometryCode
    roleIndex := aligned.toInterface.localLayerRightFaceRoleEquivBoundedIndex
      color hrightColor
    faceUpdate := faceUpdate }
  refine ⟨code, ?_, ?_,
    aligned.localLayerFiniteConnectivityUpdateCode
      hcubic hrotation color hcolor hleftColor hrightColor, ?_, ?_, ?_⟩
  · exact aligned.toInterface
      |>.card_localLayerRightPrefixBoundaryRegionalFragment_eq_three
  · intro step
    simp only [code]
    apply StrandColor.toColor_injective
    rw [aligned.localLayerCellBoundaryProfile_edgeColor_toColor,
      aligned.localLayerRightPrefixBoundedProfile_edgeColor_toColor]
    simpa [localLayerFiniteConnectivityGeometryCode] using
      congrArg color
        (aligned.localLayerCellBoundaryEdge_crossingPosition step).symm
  · intro left right
    simp only [code]
    rw [aligned.toInterface.localLayerRightFaceRoleEquivBoundedIndex_apply,
      aligned.toInterface.localLayerRightFaceRoleEquivBoundedIndex_apply]
    exact
      (aligned.toInterface
        |>.localLayerRightPrefixBoundedProfile_faceContinues_eq_true_iff_eq
          color hrightColor
          (aligned.toInterface.localLayerRightFaceRoleIndex left)
          (aligned.toInterface.localLayerRightFaceRoleIndex right)).trans
        (aligned.toInterface.localLayerRightFaceRoleEquivBoundedIndex
          color hrightColor).injective.eq_iff
  · intro role step
    simp only [code]
    rw [aligned.toInterface.localLayerRightFaceRoleEquivBoundedIndex_apply,
      aligned.toInterface
        |>.localLayerRightPrefixBoundedProfile_fragmentContainsPort_eq_role,
      aligned.toInterface
        |>.boundaryRegionalFragmentAt_localLayerRightFaceRoleIndex,
      aligned.toInterface.localLayerRightBoundaryFragmentRole_roleEquiv]
  · intro role
    simp only [code]
    rw [aligned.toInterface.localLayerRightFaceRoleEquivBoundedIndex_apply]
    exact (hfaceUpdate role).2

/-- Tait nonzeroness supplies the two cut-color premises of the joint finite
receipt. -/
theorem exists_localLayerFiniteOneCellReceipt_of_tait
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (color : embedded.cellulation.rotation.toRotationSystem.EdgeColoring Color)
    (hcolor : embedded.cellulation.rotation.toRotationSystem
      |>.IsTaitEdgeColoring color) :
    LocalLayerFiniteOneCellReceiptThree
      (aligned.localLayerFiniteInputProfile color
        (fun step => hcolor
          (aligned.toInterface.localLayerPrefixCrossing step)))
      (aligned.localLayerFiniteOutputProfile color
        (fun step => hcolor
          (aligned.toInterface.nextLocalLayerPrefixCrossing step))) := by
  simpa [LocalLayerFiniteOneCellReceiptThree,
    localLayerFiniteInputProfile, localLayerFiniteOutputProfile] using
    aligned.exists_localLayerFiniteOneCellReceipt hcubic hrotation color
      hcolor
      (fun step => hcolor (aligned.toInterface.localLayerPrefixCrossing step))
      (fun step => hcolor
        (aligned.toInterface.nextLocalLayerPrefixCrossing step))

/-- Exact support relation of one literal source Cell on the fixed three-face
input and output carriers.  It is heterogeneous in `aligned`: no quotient by
the three coarse orientation labels is built into the definition. -/
def LiteralLocalLayerOneCellSupport
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (incoming : BoundedCorridorCutProfile 2 1 3)
    (output : BoundedCorridorCutProfile 2 0 3) : Prop :=
  ∃ color : embedded.cellulation.rotation.toRotationSystem.EdgeColoring Color,
    ∃ hcolor : embedded.cellulation.rotation.toRotationSystem
        |>.IsTaitEdgeColoring color,
      incoming = aligned.localLayerFiniteInputProfile color
        (fun step => hcolor
          (aligned.toInterface.localLayerPrefixCrossing step)) ∧
      output = aligned.localLayerFiniteOutputProfile color
        (fun step => hcolor
          (aligned.toInterface.nextLocalLayerPrefixCrossing step))

/-- Exact literal support maps into the joint finite receipt relation.  This
is the soundness direction needed before reachable-state measurement; the
converse adequacy direction is deliberately not inferred from finiteness. -/
theorem localLayerFiniteOneCellReceipt_of_literalSupport
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (incoming : BoundedCorridorCutProfile 2 1 3)
    (output : BoundedCorridorCutProfile 2 0 3)
    (hsupport : aligned.LiteralLocalLayerOneCellSupport incoming output) :
    LocalLayerFiniteOneCellReceiptThree incoming output := by
  rcases hsupport with ⟨color, hcolor, rfl, rfl⟩
  exact aligned.exists_localLayerFiniteOneCellReceipt_of_tait
    hcubic hrotation color hcolor

end SourceCornerAlignedSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor

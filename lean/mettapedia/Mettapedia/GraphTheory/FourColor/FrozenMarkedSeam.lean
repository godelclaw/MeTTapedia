import Mettapedia.GraphTheory.FourColor.FrozenSeamState
import Mettapedia.GraphTheory.FourColor.MarkedSeamFaces

/-! # The actual marked seam preserves prescribed-colour acceptance

The named darts are present, with their literal ambient names. Joint
support equality in standard coordinates transfers every prescription
through the same physical matching as structural replacement. Structural
validity and strict decrease do not require ordinary non-colourability.
-/

namespace Mettapedia.GraphTheory.FourColor.MarkedCotreeSeam.SeamPair

open SimpleGraph SimpleGraphDartRotation
open GoertzelV24TwoEdgeCutMinimality GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationCutDartDecomposition GoertzelV24OpenTangleComposition
open GoertzelV24ConnectedEdgeShoreStructuralData GoertzelV24MajorityShoreNormalizedState
open GoertzelV24MajorityShorePhysicalReplacement GoertzelV24VertexSideOpenTangle
open GoertzelV24RotationMultigraphAdapter GoertzelV24SimpleGraphFaceDualConnectedness
open FrozenCountSupport FrozenPhysicalCount FrozenVertexSideCount FrozenJointReindex

noncomputable section
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]
  {M : Type v}
local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq
variable {rotation : Data G} {marks : Finset V} {mark : M → G.Dart} {w : ℕ}

def JointEq (pair : SeamPair rotation marks mark w) : Prop :=
  FrozenSeamState.jointOfShore rotation pair.outer.shore pair.outer.innerOuter mark
    pair.width pair.outerWidth =
  FrozenSeamState.jointOfShore rotation pair.inner.shore pair.inner.innerOuter mark
    pair.width pair.innerWidth

def liftedMark (pair : SeamPair rotation marks mark w)
    (hmarks : ∀ m, (mark m).fst ∈ marks) (m : M) : pair.candidate.D :=
  Classical.choose (pair.mark_survives hmarks m)

omit [G.LocallyFinite] in
theorem liftedMark_name (pair : SeamPair rotation marks mark w)
    (hmarks : ∀ m, (mark m).fst ∈ marks) (m : M) :
    pair.ambientDart (pair.liftedMark hmarks m) = mark m :=
  Classical.choose_spec (pair.mark_survives hmarks m)

omit [G.LocallyFinite] in
theorem physicalAccepts_candidate_iff (pair : SeamPair rotation marks mark w)
    (hmarks : ∀ m, (mark m).fst ∈ marks) (value : M → Color) :
    PhysicalAccepts (outsideTangle rotation pair.outer.shore pair.outer.outsideOuter)
      (innerTangle rotation pair.inner.shore pair.inner.innerOuter) pair.matching
      (sideObservation rotation.toRotationSystem (majorityDeletedKeep G pair.outer.shore) mark)
      (sideObservation rotation.toRotationSystem (majorityRetainedKeep G pair.inner.shore) mark) value ↔
      FrozenDartTransport.Accepts pair.candidate (pair.liftedMark hmarks) value := by
  rw [physicalAccepts_iff_ambient]
  have hname : ∀ d, FrozenVertexSideCount.ambientDart pair.outer.outsideOuter
      pair.inner.innerOuter pair.matching d = pair.ambientDart d := by
    rintro ((d | d) | (d | d)) <;> rfl
  simp only [hname]
  change (∃ c : pair.candidate.EdgeColoring Color, pair.candidate.IsTaitEdgeColoring c ∧
    ∀ m d, pair.ambientDart d = mark m → c (pair.candidate.edgeOf d) = value m) ↔ _
  constructor
  · rintro ⟨c, hc, hm⟩
    exact ⟨c, hc, fun m => hm m _ (pair.liftedMark_name hmarks m)⟩
  · rintro ⟨c, hc, hm⟩
    refine ⟨c, hc, ?_⟩
    intro m d hd
    have he : d = pair.liftedMark hmarks m :=
      pair.ambientDart_injective (hd.trans (pair.liftedMark_name hmarks m).symm)
    exact he ▸ hm m

omit [G.LocallyFinite] in
theorem joint_eq_physical (pair : SeamPair rotation marks mark w) (hjoint : pair.JointEq) :
    joint (innerTangle rotation pair.outer.shore pair.outer.innerOuter)
      (oldExteriorMatching rotation pair.outer.shore)
      (sideObservation rotation.toRotationSystem (majorityRetainedKeep G pair.outer.shore) mark) =
    joint (innerTangle rotation pair.inner.shore pair.inner.innerOuter) pair.matching
      (sideObservation rotation.toRotationSystem (majorityRetainedKeep G pair.inner.shore) mark) := by
  let oc := boundaryCoordinate rotation pair.outer.shore pair.width pair.outerWidth
  let nc := boundaryCoordinate rotation pair.inner.shore pair.width pair.innerWidth
  let outside := (oldExteriorMatching rotation pair.outer.shore).trans oc
  have ho : outside.trans oc.symm = oldExteriorMatching rotation pair.outer.shore := by ext p; simp [outside]
  have hn : outside.trans nc.symm = pair.matching := by rfl
  have h := joint_eq_of_coordinate_eq
    (innerTangle rotation pair.outer.shore pair.outer.innerOuter)
    (innerTangle rotation pair.inner.shore pair.inner.innerOuter) oc nc outside
    (sideObservation rotation.toRotationSystem (majorityRetainedKeep G pair.outer.shore) mark)
    (sideObservation rotation.toRotationSystem (majorityRetainedKeep G pair.inner.shore) mark) hjoint
  simpa only [ho, hn] using h

omit [G.LocallyFinite] in
/-- An exact equivalence for every fixed prescription, even when the ambient
map is ordinarily colourable. No frozen name is dropped. -/
theorem accepts_iff (pair : SeamPair rotation marks mark w) (hjoint : pair.JointEq)
    (hmarks : ∀ m, (mark m).fst ∈ marks) (value : M → Color) :
    FrozenDartTransport.Accepts rotation.toRotationSystem mark value ↔
      FrozenDartTransport.Accepts pair.candidate (pair.liftedMark hmarks) value := by
  rw [← pair.physicalAccepts_candidate_iff hmarks value]
  rw [← physicalAccepts_reassembly_iff (majorityDeletedVertices G pair.outer.shore)
    pair.outer.outsideOuter pair.outer.innerOuter mark value]
  exact physicalAccepts_iff_of_joint_eq _ _ _ _ _ _ _ _ (pair.joint_eq_physical hjoint) value

/-- The same candidate has the ambient structural class without any
colourability premise. -/
def structuralData (pair : SeamPair rotation marks mark w)
    (ambient : BridgelessSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem) :
    BridgelessSphericalCubicMapData pair.candidate := by
  have hg : G.Connected := by
    rw [← rotationPrimalGraph_toRotationSystem_eq G rotation]
    exact ambient.primalConnected
  exact replacementStructuralData_of_normalizedState_eq rotation pair.outer.shore pair.inner.shore
    pair.outer.shoreConnected pair.outer.complementConnected
    pair.outer.majorityNonempty pair.outer.complementNonempty
    pair.inner.shoreConnected pair.inner.complementConnected
    pair.inner.majorityNonempty pair.inner.complementNonempty
    pair.outer.outsideOuter pair.outer.innerOuter pair.inner.innerOuter pair.width
    pair.outerWidth pair.innerWidth (congrArg Prod.fst pair.state_eq)
    ambient.spherical htwo hg ambient.vertexRotationCyclic
    ((bridgeless_iff_edgeBridgeFree (RS := rotation.toRotationSystem)).2 ambient.edgeBridgeFree)
    pair.outer.first pair.outer.second pair.outer.first_ne_second

theorem candidate_card_lt (pair : SeamPair rotation marks mark w)
    (ambient : BridgelessSphericalCubicMapData rotation.toRotationSystem) :
    Fintype.card ({v : V // majorityDeletedKeep G pair.outer.shore v} ⊕
      {v : V // majorityRetainedKeep G pair.inner.shore v}) < Fintype.card V :=
  replacementVertexCount_lt_of_incident_sdiff rotation pair.outer.shore pair.inner.shore
    pair.nested.1 pair.strictVertex pair.strict_star ambient.spherical.cubic

end
end Mettapedia.GraphTheory.FourColor.MarkedCotreeSeam.SeamPair

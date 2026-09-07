import Mettapedia.GraphTheory.FourColor.CofacialMarkedSeam
import Mettapedia.GraphTheory.FourColor.SphericalMeshFreeSeam

/-! # Supplied frozen reduction with named cofaciality

Both geometric branches supply enough literal shores for the refined
finite state. Their selected physical seam preserves frozen-colour
acceptance and named cofaciality simultaneously. The threshold charges
named darts, not designated-face perimeters. The ordered-mesh alternative
is explicit; no fixed-mesh exclusion or finite-base theorem is asserted.
-/

namespace Mettapedia.GraphTheory.FourColor.SphericalCofacialReduction

open SimpleGraph SimpleGraphDartRotation
open GoertzelV24TwoEdgeCutMinimality GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceTwoSided GoertzelV24PrimalCycleFacialBond
open GoertzelV24RotationMultigraphAdapter GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24ConnectedShoreLiteralNode GoertzelV24ConnectedEdgeShoreMajority
open GoertzelV24ConnectedEdgeShoreStructuralData GoertzelV24MajorityShoreNormalizedState
open SphericalContourSeparators SphericalOrderedMeshReduction SphericalMarkedCotreeChain
open MarkedCotreeSeam CofacialSeamState

noncomputable section
universe u v
attribute [local instance] Classical.propDecidable
variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]
  {M : Type v} [Fintype M]
local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

theorem exists_joint_face_seam_of_nodes (rotation : Data G)
    (ambient : BridgelessSphericalCubicMapData rotation.toRotationSystem)
    (w : ℕ) (marks : Finset V) (mark : M → G.Dart)
    (nodes : Fin (CofacialSeamState.stateBound w (Fintype.card M) + 1) →
      ConnectedShoreNode (G := G) w w)
    (hnest : ∀ i j, i < j → (nodes i).shore ⊂ (nodes j).shore)
    (hmarks : ∀ i v, v ∈ marks → (majorityVertexSide G (nodes i).shore v ↔
      majorityVertexSide G (nodes 0).shore v))
    (hstar : ∀ i j, i < j → ∃ v, v ∉ marks ∧
      majorityVertexSide G (nodes j).shore v ∧ ¬ majorityVertexSide G (nodes i).shore v ∧
      ∀ e ∈ incidentEdgeFinset G v, e ∈ (nodes j).shore \ (nodes i).shore) :
    ∃ pair : SeamPair rotation marks mark w, pair.JointEq ∧ pair.FaceEq := by
  let n := CofacialSeamState.stateBound w (Fintype.card M)
  let literal := fun i => (nodes i).toLiteralOfSpherical rotation ambient
  let state := fun i => CofacialSeamState.boundedOfShore rotation (literal i).shore
    (literal i).innerOuter mark w (literal i).widthBound
  have hcard : Fintype.card (CofacialSeamState.Bounded.{u} M w) < Fintype.card (Fin (n + 1)) := by
    rw [Fintype.card_fin]
    exact lt_of_le_of_lt (CofacialSeamState.card_bounded_le (M := M) w) (Nat.lt_succ_self n)
  obtain ⟨i, j, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt state hcard
  have hordered : ∃ i j, i < j ∧ state j = state i := by
    rcases lt_or_gt_of_ne hne with hij | hij
    · exact ⟨i, j, hij, heq.symm⟩
    · exact ⟨j, i, hij, heq⟩
  obtain ⟨i, j, hij, heq⟩ := hordered
  obtain ⟨width, outerWidth, innerWidth, hs⟩ := CofacialSeamState.boundedOfShore_eq_elim
    rotation (literal j).shore (literal i).shore (literal j).innerOuter (literal i).innerOuter
    mark w (literal j).widthBound (literal i).widthBound heq
  obtain ⟨v, hv, _, _, hvs⟩ := hstar i j hij
  let pair : SeamPair rotation marks mark w := {
    inner := literal i
    outer := literal j
    nested := hnest i j hij
    marks_constant := fun v hv => (hmarks i v hv).trans (hmarks j v hv).symm
    strictVertex := v
    strict_unmarked := hv
    strict_star := hvs
    width := width
    outerWidth := outerWidth
    innerWidth := innerWidth
    state_eq := congrArg (fun s => s.1.1) hs }
  exact ⟨pair, congrArg (fun s : CofacialSeamState.State.{u} M width => s.1.2) hs,
    congrArg Prod.snd hs⟩

def contourLength (a b vertices darts : ℕ) : ℕ :=
  (6 * SphericalMeshFreeSeam.contourWidth a b + 1) *
    ((vertices + 1) * CofacialSeamState.stateBound (SphericalMeshFreeSeam.contourWidth a b) darts) + 1

def radiusBound (a b vertices darts : ℕ) : ℕ := contourLength a b vertices darts * a

def widthBound (a b vertices darts : ℕ) : ℕ :=
  max (SphericalMeshFreeSeam.contourWidth a b) (2 * radiusBound a b vertices darts + 1)

def sizeBound (a b vertices darts : ℕ) : ℕ :=
  markedCotreeVertexBound (radiusBound a b vertices darts) vertices
    (CofacialSeamState.stateBound (2 * radiusBound a b vertices darts + 1) darts)

/-- Geometry supplies equality of the refined records; it is not an input.
The full boundaries, their order and strict material are inherited from the
contour/cotree constructions. -/
theorem exists_joint_face_seam_of_no_orderedMesh (rotation : Data G)
    (ambient : BridgelessSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (a b : ℕ) (ha : 2 ≤ a) (marks : Finset V) (mark : M → G.Dart)
    (hno : ¬ Nonempty (OrderedInjectiveMesh (toMultigraph rotation.toRotationSystem) a b))
    (hlarge : sizeBound a b marks.card (Fintype.card M) < Fintype.card V) :
    ∃ w, w ≤ widthBound a b marks.card (Fintype.card M) ∧
      ∃ pair : SeamPair rotation marks mark w, pair.JointEq ∧ pair.FaceEq := by
  let root := dartOrbitFace rotation.toRotationSystem rotation.toRotationSystem.outer
  let c := SphericalMeshFreeSeam.contourWidth a b
  let n := CofacialSeamState.stateBound c (Fintype.card M)
  let N := contourLength a b marks.card (Fintype.card M)
  let h := radiusBound a b marks.card (Fintype.card M)
  by_cases hradius : ∀ f, (orbitFaceDualGraph rotation).dist f root ≤ h
  · obtain ⟨nodes, hnest, hm, hstar⟩ := exists_marked_nodes_of_large_card rotation ambient htwo
      root h (CofacialSeamState.stateBound (2 * h + 1) (Fintype.card M)) marks hradius hlarge
    exact ⟨2 * h + 1, le_max_right _ _,
      exists_joint_face_seam_of_nodes rotation ambient _ marks mark nodes hnest hm hstar⟩
  · obtain ⟨far, hfar⟩ := not_forall.mp hradius
    have hdepth : N * a ≤ (orbitFaceDualGraph rotation).dist far root := (Nat.lt_of_not_ge hfar).le
    obtain ⟨raw, hraw⟩ := exists_nested_nodes_of_no_orderedMesh_of_spherical
      rotation ambient htwo far root a b N ha hdepth hno
    obtain ⟨nodes, hnest, hm, hstar⟩ := exists_marked_nodes_of_nested_nodes rotation ambient c n marks raw hraw
    exact ⟨c, le_max_left _ _,
      exists_joint_face_seam_of_nodes rotation ambient c marks mark nodes hnest hm hstar⟩

/-- The supplied smaller map has the same frozen-colour acceptance and
named cofaciality. No designated face length, chain, compatibility or
non-colourability hypothesis is supplied. The mesh branch stays explicit. -/
theorem exists_orderedMesh_or_cofacial_replacement (rotation : Data G)
    (ambient : BridgelessSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (a b : ℕ) (ha : 2 ≤ a) (mark : M → G.Dart)
    (hlarge : sizeBound a b (Finset.univ.image (fun m => (mark m).fst)).card
      (Fintype.card M) < Fintype.card V) :
    Nonempty (OrderedInjectiveMesh (toMultigraph rotation.toRotationSystem) a b) ∨
      ∃ w, w ≤ widthBound a b (Finset.univ.image (fun m => (mark m).fst)).card
        (Fintype.card M) ∧
      ∃ pair : SeamPair rotation (Finset.univ.image (fun m => (mark m).fst)) mark w,
        Nonempty (BridgelessSphericalCubicMapData pair.candidate) ∧
        Fintype.card ({v : V // majorityDeletedKeep G pair.outer.shore v} ⊕
          {v : V // majorityRetainedKeep G pair.inner.shore v}) < Fintype.card V ∧
        ∃ lift : M → pair.candidate.D,
          (∀ m, pair.ambientDart (lift m) = mark m) ∧
          (∀ value : M → Color, FrozenDartTransport.Accepts rotation.toRotationSystem mark value ↔
            FrozenDartTransport.Accepts pair.candidate lift value) ∧
          ∀ m n, rotation.toRotationSystem.phi.SameCycle (mark m) (mark n) ↔
            pair.candidate.phi.SameCycle (lift m) (lift n) := by
  by_cases hm : Nonempty (OrderedInjectiveMesh (toMultigraph rotation.toRotationSystem) a b)
  · exact Or.inl hm
  · obtain ⟨w, hw, pair, hjoint, hface⟩ := exists_joint_face_seam_of_no_orderedMesh
      rotation ambient htwo a b ha (Finset.univ.image (fun m => (mark m).fst)) mark hm hlarge
    have hmarks : ∀ m, (mark m).fst ∈ Finset.univ.image (fun m => (mark m).fst) := by
      intro m
      exact Finset.mem_image.mpr ⟨m, Finset.mem_univ _, rfl⟩
    exact Or.inr ⟨w, hw, pair, ⟨pair.structuralData ambient htwo⟩, pair.candidate_card_lt ambient,
      pair.liftedMark hmarks, pair.liftedMark_name hmarks,
      pair.accepts_iff hjoint hmarks, pair.cofacial_iff hface hmarks⟩

end
end Mettapedia.GraphTheory.FourColor.SphericalCofacialReduction

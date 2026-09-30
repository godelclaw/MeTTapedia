import MettapediaFourColor.JointDiamondFaceReduction
import MettapediaFourColor.JointDiamondChord
import Mettapedia.GraphTheory.FourColor.PartialCubicDartBoundaryCompletion
import Mettapedia.GraphTheory.FourColor.OpenTangleVertexSideReturn

/-!
# Geometric boundary clearance for the joint diamond

The four-face traversal has a connected fourteen-vertex image. The normal
form gives a connected exterior. Therefore all actual outgoing ports lie on
one capped face. An unrecorded internal chord contradicts that conclusion.
-/

namespace FourColor.JointDiamondPatch.Tangle.FaceClearance

open Mettapedia.GraphTheory.FourColor
open SimpleGraphDartRotation PhysicalForkCodeFaces PartialCubicDartSeparation
open GoertzelV24OpenTangleComposition GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24OrbitFaceCurvatureBulk GoertzelV24TwoEdgeCutMinimality
open GoertzelV24WeightedOrbitFaceCorridor GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24MinimalFaceSize GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationCutDartDecomposition GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24ComplementaryShoreBoundaryOrder GoertzelV24DeletedRegionRotationSplice
open GoertzelV24OrderedCutFaceReturnProfile GoertzelV24FaceOrbitIncidence
open OpenTangleMarkedFace GoertzelV24MinimalTriangleFree GoertzelV24CubicFourEdgeConnectedSides

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

variable (rotation : Data G) (root : G.Dart) (hfaces : JointDiamond.FaceLengths rotation root)
  (h : BridgelessSphericalCubicMapData rotation.toRotationSystem)
  (hminimum : OrbitFaceMinimumFive rotation.toRotationSystem)
  (hinternal : CubicDualInternallySixConnected G)

abbrev realized := Recognition.realized rotation root (FaceReduction.cubic rotation h) hfaces
abbrev injection := FaceReduction.vertex_injective rotation root hfaces h hminimum hinternal
abbrev darts := Recognition.darts rotation root (FaceReduction.cubic rotation h) hfaces
  (injection rotation root hfaces h hminimum hinternal)
abbrev actual (d : Dart) : G.Dart := JointDiamond.dart rotation root (coordinate d)

abbrev side := Recognition.keep rotation root

theorem side_eq_image : side rotation root = (realized rotation root hfaces h).imageSide :=
  funext fun v => propext (Recognition.keep_iff rotation root v)

include hfaces h hminimum hinternal in
theorem side_card : Fintype.card {v // side rotation root v} = 14 := by
  classical
  rw [side_eq_image rotation root hfaces h]
  exact (realized rotation root hfaces h).card_imageSide
    (injection rotation root hfaces h hminimum hinternal)

include h in
theorem regular : G.IsRegularOfDegree 3 := fun v =>
  (degree_instance_independent v _ _).trans
    ((rotation.toRotationSystem_isCubic_iff.mp h.spherical.cubic) v)

include hfaces h hminimum in
theorem twenty_lt_vertices : 20 < Fintype.card V := by
  apply SphericalVertexLowerBound.twenty_lt_card_vertices_of_long_face
    rotation.toRotationSystem h.spherical hminimum
  refine ⟨dartOrbitFace rotation.toRotationSystem root, ?_⟩
  rw [orbitFaceDarts_dartOrbitFace_eq_faceOrbit, hfaces.central]
  omega

include hfaces h in
theorem inside_connected : (G.induce {v | side rotation root v}).Connected := by
  rw [side_eq_image rotation root hfaces h]
  apply (realized rotation root hfaces h).image_connected 0
  intro v
  have hp : ∀ w : JointDiamond.Vertex, ∃ n : Fin 8,
      JointDiamond.diagram.pathCheck n.val 0 w = true := by decide +kernel
  obtain ⟨n, hn⟩ := hp v
  exact ⟨n.val, JointDiamond.diagram.pathCheck_sound hn⟩

include hfaces h hminimum hinternal in
theorem outside_connected : (G.induce {v | ¬ side rotation root v}).Connected := by
  classical
  let F := realized rotation root hfaces h
  have hc := side_card rotation root hfaces h hminimum hinternal
  have hv := twenty_lt_vertices rotation root hfaces h hminimum
  have hpartition := Fintype.card_subtype_compl (side rotation root)
  have hports : Fintype.card (CrossingSideDart G (side rotation root)) ≤ 8 := by
    rw [side_eq_image rotation root hfaces h]
    exact F.crossing_card_le.trans_eq unpaired_card
  have hother : HasCycleOnSide G (side rotation root) :=
    CyclicFiveBoundary.hasCycle_of_boundary_card_lt_card_add_two
      (regular rotation h) _ (Fintype.card_pos_iff.mp (by omega)) (by omega)
  apply EightPortBoundaryConnectivity.connected_of_seven_le_card_of_boundary_card_le_eight
    (regular rotation h) hinternal (fun v => ¬ side rotation root v)
  · simpa only [not_not] using hother
  · rw [← card_crossingEdgeFinset_eq_card_crossingSideDart,
      crossingEdgeFinset_compl, card_crossingEdgeFinset_eq_card_crossingSideDart]
    exact hports
  · omega
  · simpa only [not_not] using (show 6 ≤ Fintype.card {v // side rotation root v} by omega)

include hfaces h hminimum hinternal in
/-- Both actual shores are connected before boundary clearance is known. -/
theorem ports_cofacial (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (b c : BoundaryDart rotation.toRotationSystem (side rotation root)) :
    (retainedCappedFacePerm rotation.toRotationSystem (side rotation root)).SameCycle b.1 c.1 := by
  classical
  let deleted : Finset V := Finset.univ.filter (fun v => ¬ side rotation root v)
  have he : deletedRegionKeep deleted = side rotation root := by
    funext v
    simp [deletedRegionKeep, deleted]
  have hf := OpenTangleVertexSideReturn.ports_cofacial_of_planarBond rotation deleted
  rw [he] at hf
  let base := Recognition.rootIn rotation root (FaceReduction.cubic rotation h) hfaces
  have hh := hf base h.spherical htwo (by simpa only [GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq] using h.primalConnected) h.vertexRotationCyclic
    (inside_connected rotation root hfaces h)
    (outside_connected rotation root hfaces h hminimum hinternal) b c
  let e := retainedDartEquivInternalSumBoundary rotation.toRotationSystem (side rotation root)
  have hc := (permCongr_sameCycle_iff e.symm
    (openPhi (ofVertexSide rotation.toRotationSystem (side rotation root) base))
    (.inr b) (.inr c)).2 hh
  rw [← OpenTangleVertexSideReturn.face_perm] at hc
  exact hc

include hfaces h hminimum hinternal in
/-- Once one extra edge is paired, every other candidate is a genuine port. -/
theorem remaining_leaves (p q : Fin 8) (hne : p ≠ q)
    (he : (actual rotation root (.inr p)).symm = actual rotation root (.inr q))
    (b : Fin 8) (hbp : b ≠ p) (hbq : b ≠ q) :
    ¬ side rotation root (actual rotation root (.inr b)).snd := by
  let F := realized rotation root hfaces h
  have hi : ∀ r, ¬ Chord.remaining p q r → F.imageSide (F.dart r.1).snd := by
    intro r hr
    have hc : r = Chord.port p ∨ r = Chord.port q := by
      simpa only [Chord.remaining, not_and_or, not_not] using hr
    rcases hc with rfl | rfl
    · exact ⟨(Chord.port q).1.1,
        ((congrArg (fun d : G.Dart => d.fst) he).trans (F.fst _)).symm⟩
    · have hh := congrArg (fun d : G.Dart => d.snd) he
      exact ⟨(Chord.port p).1.1, (F.fst _).symm.trans hh⟩
  have ha : Chord.remaining p q (Chord.port b) :=
    ⟨fun hh => hbp (Chord.port_injective hh), fun hh => hbq (Chord.port_injective hh)⟩
  have hv := twenty_lt_vertices rotation root hfaces h hminimum
  have hb := F.allowed_leaves_of_six
    (injection rotation root hfaces h hminimum hinternal) (Chord.remaining p q)
    (Chord.remaining_card p q hne) hi (by decide +kernel) (by decide +kernel) (by change 14 + 3 ≤ _; omega)
    (regular rotation h) hinternal.1 (Chord.port b) ha
  rw [side_eq_image rotation root hfaces h]
  exact hb

theorem darts_rho (d : Dart) :
    darts rotation root hfaces h hminimum hinternal (piece.rho d) =
      retainedRho rotation.toRotationSystem (side rotation root)
        (darts rotation root hfaces h hminimum hinternal d) := by
  apply Subtype.ext
  change (realized rotation root hfaces h).dart (coordinate (piece.rho d)) =
    rotation.vertexRotation ((realized rotation root hfaces h).dart (coordinate d))
  rw [coordinate_rotate]
  exact (realized rotation root hfaces h).rotate_eq _

include hfaces h hminimum hinternal in
/-- The actual capped face permutation is the literal one-chord operation. -/
theorem chord_face_perm (p q : Fin 8) (hne : p ≠ q)
    (he : (actual rotation root (.inr p)).symm = actual rotation root (.inr q)) :
    retainedCappedFacePerm rotation.toRotationSystem (side rotation root) =
      (darts rotation root hfaces h hminimum hinternal).permCongr (Chord.phi p q) := by
  let e := darts rotation root hfaces h hminimum hinternal
  have ha (d : Dart) : retainedCappedAlpha rotation.toRotationSystem (side rotation root) (e d) =
      e (Chord.alpha p q d) := by
    cases d with
    | inl i =>
      apply Subtype.ext
      rw [retainedCappedAlpha_apply_internal _ _ _
        (Recognition.interior_kept rotation root (FaceReduction.cubic rotation h) hfaces
          (injection rotation root hfaces h hminimum hinternal) i)]
      have hc : Chord.alpha p q (.inl i) = .inl (piece.interiorAlpha i) := by
        simp [Chord.alpha, Equiv.swap_apply_def]
      rw [hc]
      exact (realized rotation root hfaces h).flip_eq _ _ (coordinate_flip i)
    | inr b =>
      by_cases hp : b = p
      · subst b
        have hk : side rotation root (actual rotation root (.inr p)).snd := by
          rw [side_eq_image rotation root hfaces h]
          exact ⟨(coordinate (.inr q)).1,
            ((congrArg (fun d : G.Dart => d.fst) he).trans
              ((realized rotation root hfaces h).fst _)).symm⟩
        apply Subtype.ext
        rw [retainedCappedAlpha_apply_internal _ _ _ hk]
        have hc : Chord.alpha p q (.inr p) = .inr q := by simp [Chord.alpha]
        rw [hc]
        exact he
      by_cases hq : b = q
      · subst b
        have hk : side rotation root (actual rotation root (.inr q)).snd := by
          rw [side_eq_image rotation root hfaces h]
          exact ⟨(coordinate (.inr p)).1,
            ((realized rotation root hfaces h).fst _).symm.trans
              (congrArg (fun d : G.Dart => d.snd) he)⟩
        apply Subtype.ext
        rw [retainedCappedAlpha_apply_internal _ _ _ hk]
        have hc : Chord.alpha p q (.inr q) = .inr p := by simp [Chord.alpha]
        rw [hc]
        exact (congrArg SimpleGraph.Dart.symm he).symm
      have hb := remaining_leaves rotation root hfaces h hminimum hinternal p q hne he b hp hq
      rw [retainedCappedAlpha_apply_boundary _ _ _ hb]
      have hc : Chord.alpha p q (.inr b) = .inr b := by
        simp [Chord.alpha, Equiv.swap_apply_def, hp, hq]
      rw [hc]
  apply Equiv.ext
  intro x
  obtain ⟨d, rfl⟩ := e.surjective x
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  change retainedRho rotation.toRotationSystem (side rotation root)
      (retainedCappedAlpha rotation.toRotationSystem (side rotation root) (e d)) =
    e (piece.rho (Chord.alpha p q d))
  rw [ha, darts_rho]

include hfaces h hminimum hinternal in
/-- No candidate port can return inside: girth and the actual spherical
boundary rule exclude every possible extra internal chord. -/
theorem boundary_clear (htwo : OrbitFacesTwoSided rotation.toRotationSystem) :
    Recognition.BoundaryClear rotation root := by
  intro p hp
  let F := realized rotation root hfaces h
  have hi : F.imageSide (F.dart (Chord.port p).1).snd := by
    change (F.dart (Chord.port p).1).snd ∈ Finset.univ.image
      (JointDiamond.vertex rotation root) at hp
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hp
    exact ⟨v, hv⟩
  obtain ⟨r, hr, he⟩ := F.unpaired_mate
    (injection rotation root hfaces h hminimum hinternal) (Chord.port p) hi
  obtain ⟨q, rfl⟩ := Chord.port_surjective r
  have hne : p ≠ q := fun hpq => hr (hpq ▸ rfl)
  have hv := twenty_lt_vertices rotation root hfaces h hminimum
  have hg := Realization.girth_of_cyclicallyFive rotation (regular rotation h) hinternal.1 (by omega)
  have hs' := F.unpaired_no_short_path
    (injection rotation root hfaces h hminimum hinternal) hg.1 hg.2
    (Chord.port p) (Chord.port q) he
  have hs : Chord.short p q = false := by simp only [Chord.short, hs'.1, hs'.2.1, hs'.2.2]; rfl
  have sep := Chord.separated_ports p q hne hs
  let e := darts rotation root hfaces h hminimum hinternal
  let b : BoundaryDart rotation.toRotationSystem (side rotation root) :=
    ⟨e (.inr (p + 1)), remaining_leaves rotation root hfaces h hminimum hinternal
      p q hne he _ sep.1 sep.2.1⟩
  let c : BoundaryDart rotation.toRotationSystem (side rotation root) :=
    ⟨e (.inr (q + 1)), remaining_leaves rotation root hfaces h hminimum hinternal
      p q hne he _ sep.2.2.1 sep.2.2.2.1⟩
  have hc := ports_cofacial rotation root hfaces h hminimum hinternal htwo b c
  rw [chord_face_perm rotation root hfaces h hminimum hinternal p q hne he] at hc
  exact Chord.not_sameCycle p q hne hs
    ((permCongr_sameCycle_iff e (Chord.phi p q) (.inr (p + 1)) (.inr (q + 1))).1 hc)

/-- The complete ordered occurrence is derived from face lengths and
ambient geometry, with no supplied boundary-clearance check. -/
def recognized (htwo : OrbitFacesTwoSided rotation.toRotationSystem) :=
  FaceReduction.recognized rotation root hfaces h hminimum hinternal
    (boundary_clear rotation root hfaces h hminimum hinternal htwo)

abbrev smaller (htwo : OrbitFacesTwoSided rotation.toRotationSystem) :=
  FaceReduction.smaller rotation root hfaces h hminimum hinternal
    (boundary_clear rotation root hfaces h hminimum hinternal htwo)

include hfaces h hminimum hinternal in
/-- A complete geometric reduction at the four-face pattern. Both introduced
vertices are counted, and the same coupled repair reconstructs colourings. -/
theorem strict_reduction_of_face_pattern
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem) :
    Fintype.card ({v : V // deletedRegionKeep (Recognition.deleted rotation root) v} ⊕ Fin 2) + 12 =
        Fintype.card V ∧
      Fintype.card ({v : V // deletedRegionKeep (Recognition.deleted rotation root) v} ⊕ Fin 2) <
        Fintype.card V ∧
      BridgelessSphericalCubicMapData (smaller rotation root hfaces h hminimum hinternal htwo) ∧
      (RotationSystemTaitColorable (smaller rotation root hfaces h hminimum hinternal htwo) →
        RotationSystemTaitColorable rotation.toRotationSystem) :=
  FaceReduction.strict_reduction_of_checked_face_pattern rotation root hfaces h hminimum hinternal
    (boundary_clear rotation root hfaces h hminimum hinternal htwo) htwo

omit h hminimum hinternal in
include hfaces in
/-- The face pattern is excluded from an actual vertex-minimal counterexample.
The smaller colouring comes from minimality, not from the Four Colour theorem. -/
theorem not_in_minimal_counterexample_of_face_pattern
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation) : False := by
  let h := minimal.toBridgelessSphericalCubicMapData
  let hm := orbitFaceMinimumFive_of_vertexMinimalTaitCounterexample rotation minimal
  let hi := cubicDualInternallySixConnected_of_vertexMinimalTaitCounterexample rotation minimal
  exact FaceReduction.not_in_minimal_counterexample_of_checked_face_pattern rotation root hfaces
    (boundary_clear rotation root hfaces h hm hi minimal.facesTwoSided) minimal

end
end FourColor.JointDiamondPatch.Tangle.FaceClearance

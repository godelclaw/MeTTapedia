import Mettapedia.GraphTheory.FourColor.FaceAttachmentDegrees
import Mettapedia.GraphTheory.FourColor.FacePathExtension

/-!
# Colouring progress from the degree word of a facial contour

An attachment of more than `r` edges forces `r` consecutive degree-three
vertices on the old boundary. If that run is absent and the added face
has at least `r + 3` edges, at least three edges are new. Every proper old
colouring then extends while retaining all its edge colours.

The final progress theorem constructs the face event toward any larger
connected facial region with connected complement. Preservation of the
run exclusion after that step is a separate geometric question.
-/

namespace Mettapedia.GraphTheory.FourColor.FaceContourExtension

open Equiv Equiv.Perm
open GoertzelV24FaceOrbitIncidence GoertzelV24TwoEdgeCutMinimality
open GoertzelV24OrbitFaceTwoSided
open SimpleGraphDartRotation FaceRegionDegree EdgeShoreRotation
open PlanePatchCurvature FaceRegionShelling FaceRegionComplement
open FaceAttachmentCount FaceAttachmentArc FaceAttachmentBoundary
open FaceAttachmentDegrees PermutationSingleExitArc
open GoertzelV24ForkInterfaceSupport

noncomputable section
attribute [local instance] Classical.propDecidable

section Boundary

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Consecutive degree-three vertices in the actual outer face order. -/
def HasThreeRun (T : RotationSystem V E) (r : ℕ) : Prop :=
  ∃ d ∈ outerDarts T, ∀ i : Fin r,
    (T.dartsAt (T.vertOf ((T.phi ^ i.val) d))).card = 3

theorem no_two_run_of_alternates {T : RotationSystem V E}
    (ha : BoundaryAlternates T) : ¬ HasThreeRun T 2 := by
  rintro ⟨d, hd, hh⟩
  have h0 := hh 0
  have h1 := hh 1
  simp only [Fin.val_zero, pow_zero, Perm.one_apply] at h0
  simp only [Fin.val_one, pow_one] at h1
  exact ha d hd (h0.trans h1.symm)

/-- At curvature six, excluding consecutive threes already forces full
alternation. Equal counts make the successor injection onto. -/
theorem alternates_of_no_two_run_of_curvature_six {T : RotationSystem V E}
    (hp : Patch T) (hc : curvature T = 6) (hn : ¬ HasThreeRun T 2) :
    BoundaryAlternates T := by
  have no33 (d : T.D) (hd : d ∈ outerDarts T)
      (h3 : (T.dartsAt (T.vertOf d)).card = 3) :
      (T.dartsAt (T.vertOf (T.phi d))).card ≠ 3 := by
    intro hnext
    apply hn
    refine ⟨d, hd, ?_⟩
    intro i
    fin_cases i
    · simpa using h3
    · simpa using hnext
  have hcount : (degreeDarts T 2).card = (degreeDarts T 3).card := by
    rw [hp.card_degreeDarts_two, hp.card_degreeDarts_three]
    have hh := hp.curvature_eq
    omega
  have him : (degreeDarts T 3).image T.phi = degreeDarts T 2 := by
    apply Finset.eq_of_subset_of_card_le
    · intro d hd
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hd
      obtain ⟨hx, h3⟩ := Finset.mem_filter.mp hx
      have hnext := (outer_phi_iff (RS := T) x).mpr hx
      exact Finset.mem_filter.mpr
        ⟨hnext, (hp.boundary_dart_degree _ hnext).resolve_right (no33 x hx h3)⟩
    · rw [Finset.card_image_of_injective _ T.phi.injective, hcount]
  intro d hd heq
  rcases hp.boundary_dart_degree d hd with h2 | h3
  · have hnext : T.phi d ∈ degreeDarts T 2 :=
      Finset.mem_filter.mpr ⟨(outer_phi_iff (RS := T) d).mpr hd, heq.symm.trans h2⟩
    rw [← him] at hnext
    obtain ⟨x, hx, he⟩ := Finset.mem_image.mp hnext
    have hxd := T.phi.injective he
    have hh := (Finset.mem_filter.mp hx).2
    rw [hxd, h2] at hh
    omega
  · exact no33 d hd h3 (heq.symm.trans h3)

end Boundary

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (data : Data G) {S R : Region data} (e : Event S R)
variable (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
variable (outer : Dart data.toRotationSystem (edges data.toRotationSystem S.faces))
variable (ho : dartOrbitFace data.toRotationSystem outer.val ∉ S.faces)

local notation "Old" => toMap data.toRotationSystem (edges data.toRotationSystem S.faces) outer

include ambient ho

/-- The run is supplied by the internal vertices of the derived attachment
arc; no boundary word or attachment order is assumed. -/
theorem run_of_long_attachment (r : ℕ) (hr : r < (attachmentEdges data e).card) :
    HasThreeRun Old r := by
  obtain ⟨a⟩ := exists_attachment_arc data ambient e
  have hlen : r < a.length := by
    rw [a.length_eq_card, attachment_darts_card data ambient e]
    exact hr
  have hfirst : oldStart data e a ∈ outerDarts Old :=
    old_attachment_on_outer data e outer ambient ho
      ((mem_oldAttachmentDarts data e _).mpr a.first_mem)
  refine ⟨(Old).phi (oldStart data e a), (outer_phi_iff (RS := Old) _).mpr hfirst, ?_⟩
  intro i
  have hi : i.val + 1 < a.length := by omega
  have hh := internal_degree data e ambient outer a (i.val + 1) (by omega) hi
  rw [pow_succ, Perm.mul_apply] at hh
  exact hh

theorem attachment_le_of_no_run (r : ℕ) (hn : ¬ HasThreeRun Old r) :
    (attachmentEdges data e).card ≤ r := by
  by_contra! hh
  exact hn (run_of_long_attachment data e ambient outer ho r hh)

omit ho in
/-- The common and exposed original edges partition the actual face. -/
theorem attachment_add_exposed :
    (attachmentEdges data e).card + (exposedEdges data e).card =
      (orbitFaceDarts data.toRotationSystem e.face).card := by
  have hh := Finset.card_sdiff_add_card_inter
    (orbitFaceBoundary data.toRotationSystem e.face) (edges data.toRotationSystem S.faces)
  rw [Finset.inter_comm] at hh
  rw [← orbitFaceBoundarySimple_of_twoSided data.toRotationSystem
    (GoertzelV24BridgelessFaceTwoSided.BridgelessSphericalCubicMapData.orbitFacesTwoSided
      data.toRotationSystem ambient) e.face]
  exact (Nat.add_comm _ _).trans hh

/-- Excluding a long degree-three run supplies the path length needed by
the colouring-extension theorem. -/
theorem three_le_exposed_of_no_run (r : ℕ) (hn : ¬ HasThreeRun Old r)
    (hface : r + 3 ≤ (orbitFaceDarts data.toRotationSystem e.face).card) :
    3 ≤ (exposedEdges data e).card := by
  have ha := attachment_le_of_no_run data e ambient outer ho r hn
  have hb := attachment_add_exposed data e ambient
  omega

/-- Every given proper old colouring extends, retaining every old edge,
under a condition read solely from the actual old contour and new face. -/
theorem extends_of_no_run (r : ℕ) (hn : ¬ HasThreeRun Old r)
    (hface : r + 3 ≤ (orbitFaceDarts data.toRotationSystem e.face).card)
    (a : G.edgeSet → Fin 3)
    (ha : Proper data.toRotationSystem.endpoints (edges data.toRotationSystem S.faces) a) :
    ∃ b : G.edgeSet → Fin 3,
      Proper data.toRotationSystem.endpoints (edges data.toRotationSystem R.faces) b ∧
        ∀ x ∈ edges data.toRotationSystem S.faces, b x = a x :=
  FacePathExtension.extends_of_three_le data e ambient
    (three_le_exposed_of_no_run data e ambient outer ho r hn hface) a ha

theorem extends_of_alternates (hn : BoundaryAlternates Old)
    (hface : 5 ≤ (orbitFaceDarts data.toRotationSystem e.face).card)
    (a : G.edgeSet → Fin 3)
    (ha : Proper data.toRotationSystem.endpoints (edges data.toRotationSystem S.faces) a) :
    ∃ b : G.edgeSet → Fin 3,
      Proper data.toRotationSystem.endpoints (edges data.toRotationSystem R.faces) b ∧
        ∀ x ∈ edges data.toRotationSystem S.faces, b x = a x :=
  extends_of_no_run data e ambient outer ho 2 (no_two_run_of_alternates hn) hface a ha

/-- A failed extension forces an actual degree-three run. This is a
necessary condition for failure, not a converse. -/
theorem blocked_forces_run (r : ℕ)
    (hface : r + 3 ≤ (orbitFaceDarts data.toRotationSystem e.face).card)
    (a : G.edgeSet → Fin 3)
    (ha : Proper data.toRotationSystem.endpoints (edges data.toRotationSystem S.faces) a)
    (hblocked : ¬ ∃ b : G.edgeSet → Fin 3,
      Proper data.toRotationSystem.endpoints (edges data.toRotationSystem R.faces) b ∧
        ∀ x ∈ edges data.toRotationSystem S.faces, b x = a x) :
    HasThreeRun Old r := by
  by_contra hn
  exact hblocked (extends_of_no_run data e ambient outer ho r hn hface a ha)

omit e in
/-- A geometric step toward the specified larger region and its colouring
are both constructed. The step strictly increases the original face count. -/
theorem exists_coloured_event_between (T : Region data) (hST : S.faces ⊂ T.faces)
    (r : ℕ) (hn : ¬ HasThreeRun Old r)
    (hfaces : ∀ f ∈ T.faces \ S.faces,
      r + 3 ≤ (orbitFaceDarts data.toRotationSystem f).card)
    (a : G.edgeSet → Fin 3)
    (ha : Proper data.toRotationSystem.endpoints (edges data.toRotationSystem S.faces) a) :
    ∃ U : Region data, ∃ _ : Event S U,
      U.faces ⊆ T.faces ∧ U.faces.card = S.faces.card + 1 ∧
        ∃ b : G.edgeSet → Fin 3,
          Proper data.toRotationSystem.endpoints (edges data.toRotationSystem U.faces) b ∧
            ∀ x ∈ edges data.toRotationSystem S.faces, b x = a x := by
  obtain ⟨U, ⟨e⟩, hUT⟩ := exists_event_between data ambient S T hST
  have hf : e.face ∈ T.faces \ S.faces := by
    refine Finset.mem_sdiff.mpr ⟨hUT ?_, e.fresh⟩
    rw [e.target]
    exact Finset.mem_insert_self _ _
  exact ⟨U, e, hUT, e.card,
    extends_of_no_run data e ambient outer ho r hn (hfaces e.face hf) a ha⟩

end
end Mettapedia.GraphTheory.FourColor.FaceContourExtension

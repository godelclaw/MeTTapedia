import Mettapedia.GraphTheory.FourColor.FaceRegionPatch

/-!
# Exact inner faces of a retained facial region

When the exterior occurrences form one outer face, the remaining quotient
faces are in bijection with the selected original faces. This bijection
preserves actual facial lengths, hence every sum depending on face length.
The facial-bond theorem supplies the exterior condition geometrically.
-/

namespace Mettapedia.GraphTheory.FourColor.FaceRegionFaces

open GoertzelV24FaceOrbitIncidence
open FaceRegionDegree EdgeShoreRotation PlanePatchCurvature FaceRegionBoundary

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

def representative (RS : RotationSystem V E) (f : OrbitFace RS) : RS.D :=
  Classical.choose (exists_dartOrbitFace_eq RS f)

theorem representative_spec (RS : RotationSystem V E) (f : OrbitFace RS) :
    dartOrbitFace RS (representative RS f) = f :=
  Classical.choose_spec (exists_dartOrbitFace_eq RS f)

variable {RS : RotationSystem V E} {R : Finset (OrbitFace RS)}
variable (outer : Dart RS (edges RS R))
variable (houter : ∀ d : Dart RS (edges RS R),
  d ∈ outerDarts (toMap RS (edges RS R) outer) ↔ dartOrbitFace RS d.val ∉ R)

include houter

/-- Send an inner face to its original quotient face, not its edge set. -/
def innerToSelected (f : innerFaces (toMap RS (edges RS R) outer)) : R :=
  ⟨dartOrbitFace RS (representative (toMap RS (edges RS R) outer) f.val).val, by
    by_contra hn
    have hh := (houter _).mpr hn
    have hf := (mem_orbitFaceDarts_iff _ _ _).mp hh
    rw [representative_spec] at hf
    have hnface : f.val ≠ outerFace (toMap RS (edges RS R) outer) := by
      simpa only [innerFaces, Finset.mem_erase, Finset.mem_univ, and_true] using f.property
    exact hnface hf⟩

theorem innerToSelected_eq (f : innerFaces (toMap RS (edges RS R) outer))
    (d : Dart RS (edges RS R))
    (hd : dartOrbitFace (toMap RS (edges RS R) outer) d = f.val) :
    (innerToSelected outer houter f).val = dartOrbitFace RS d.val := by
  have hr := representative_spec (toMap RS (edges RS R) outer) f.val
  have hc := (selected_sameCycle_iff outer
    (representative (toMap RS (edges RS R) outer) f.val) d
    (innerToSelected outer houter f).property).mp (Quotient.exact (hr.trans hd.symm))
  exact Quotient.sound hc

theorem innerToSelected_injective : Function.Injective (innerToSelected outer houter) := by
  intro f g he
  have hs : RS.phi.SameCycle
      (representative (toMap RS (edges RS R) outer) f.val).val
      (representative (toMap RS (edges RS R) outer) g.val).val :=
    Quotient.exact (congrArg Subtype.val he)
  have ht := (selected_sameCycle_iff outer _ _ (innerToSelected outer houter f).property).mpr hs
  apply Subtype.ext
  have hf : dartOrbitFace (toMap RS (edges RS R) outer)
      (representative (toMap RS (edges RS R) outer) f.val) =
      dartOrbitFace (toMap RS (edges RS R) outer)
        (representative (toMap RS (edges RS R) outer) g.val) := Quotient.sound ht
  simpa only [representative_spec] using hf

theorem innerToSelected_surjective : Function.Surjective (innerToSelected outer houter) := by
  intro f
  obtain ⟨d, hd⟩ := exists_dartOrbitFace_eq RS f.val
  have hs : dartOrbitFace RS d ∈ R := hd ▸ f.property
  let e : Dart RS (edges RS R) := ⟨d, (edge_mem_iff RS R d).mpr (Or.inl hs)⟩
  have hi : dartOrbitFace (toMap RS (edges RS R) outer) e ∈
      innerFaces (toMap RS (edges RS R) outer) := by
    simp only [innerFaces, Finset.mem_erase, Finset.mem_univ, and_true]
    intro he
    have hm : e ∈ outerDarts (toMap RS (edges RS R) outer) :=
      (mem_orbitFaceDarts_iff _ _ _).mpr he
    exact (houter e).mp hm hs
  refine ⟨⟨_, hi⟩, Subtype.ext ?_⟩
  exact (innerToSelected_eq outer houter _ e rfl).trans hd

/-- The exact original face carrier, with no identification of repeated
boundary edges and no omission of an inner facial occurrence. -/
def innerFaceEquiv : innerFaces (toMap RS (edges RS R) outer) ≃ R :=
  Equiv.ofBijective (innerToSelected outer houter)
    ⟨innerToSelected_injective outer houter, innerToSelected_surjective outer houter⟩

theorem innerFaceEquiv_length (f : innerFaces (toMap RS (edges RS R) outer)) :
    (orbitFaceDarts (toMap RS (edges RS R) outer) f.val).card =
      (orbitFaceDarts RS (innerFaceEquiv outer houter f).val).card := by
  rw [← representative_spec (toMap RS (edges RS R) outer) f.val]
  exact face_length_of_full_face outer _ (selected_full (innerToSelected outer houter f).property)

/-- All face-length observables transport through the same equivalence. -/
theorem sum_inner_face_lengths {A : Type*} [AddCommMonoid A] (weight : ℕ → A) :
    (∑ f ∈ innerFaces (toMap RS (edges RS R) outer),
      weight (orbitFaceDarts (toMap RS (edges RS R) outer) f).card) =
      ∑ f ∈ R, weight (orbitFaceDarts RS f).card := by
  let e := innerFaceEquiv outer houter
  apply Finset.sum_bij (fun f hf => (e ⟨f, hf⟩).val)
  · intro f hf
    exact (e ⟨f, hf⟩).property
  · intro f hf g hg he
    exact congrArg Subtype.val (e.injective (Subtype.ext he))
  · intro f hf
    exact ⟨(e.symm ⟨f, hf⟩).val, (e.symm ⟨f, hf⟩).property,
      congrArg Subtype.val (e.apply_symm_apply ⟨f, hf⟩)⟩
  · intro f hf
    exact congrArg weight (innerFaceEquiv_length outer houter ⟨f, hf⟩)

theorem curvature_eq_selected :
    curvature (toMap RS (edges RS R) outer) =
      ∑ f ∈ R, (6 - ((orbitFaceDarts RS f).card : ℤ)) :=
  sum_inner_face_lengths outer houter (fun n => (6 - (n : ℤ)))

theorem inner_five_or_six
    (hfaces : ∀ f ∈ R, (orbitFaceDarts RS f).card = 5 ∨ (orbitFaceDarts RS f).card = 6) :
    ∀ f ∈ innerFaces (toMap RS (edges RS R) outer),
      (orbitFaceDarts (toMap RS (edges RS R) outer) f).card = 5 ∨
      (orbitFaceDarts (toMap RS (edges RS R) outer) f).card = 6 := by
  intro f hf
  rw [innerFaceEquiv_length outer houter ⟨f, hf⟩]
  exact hfaces _ (innerFaceEquiv outer houter ⟨f, hf⟩).property

end
end Mettapedia.GraphTheory.FourColor.FaceRegionFaces

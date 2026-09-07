import Mettapedia.GraphTheory.FourColor.NamedOpenFace
import Mettapedia.GraphTheory.FourColor.FrozenVertexSideCount

/-! # Named cofaciality reassembles on literal ambient darts

The optional observations of the two vertex sides denote exactly their
surviving ambient darts. Complementary sewing reconstructs the original
face permutation, not just its edge-colouring predicate.
-/

namespace Mettapedia.GraphTheory.FourColor.VertexSideCofacial

open GoertzelV24RotationCutDartDecomposition GoertzelV24OpenTangleComposition
open GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24VertexSideReassembly GoertzelV24ComplementaryShoreBoundaryOrder
open GoertzelV24DeletedRegionRotationSplice GoertzelV24OrderedCutFaceReturnProfile
open FrozenVertexSideCount NamedOpenFace

noncomputable section
universe u v
variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  {M : Type v} (RS : RotationSystem.{u,u,u} V E)

theorem observes_iff_ambient {A B : V → Prop}
    (a : RetainedDart RS A) (b : RetainedDart RS B)
    (matching : BoundaryDart RS A ≃ BoundaryDart RS B) (mark : M → RS.D) (m : M)
    (d : (InternalDart RS A ⊕ BoundaryDart RS A) ⊕ (InternalDart RS B ⊕ BoundaryDart RS B)) :
    Observes (sideObservation RS A mark) (sideObservation RS B mark) m d ↔
      ambientDart a b matching (composeDartEquiv d) = mark m := by
  rcases d with d | d
  · change sideObservation RS A mark m = some d ↔ _
    rw [ambientDart_left, sideObservation_some_iff]
  · change sideObservation RS B mark m = some d ↔ _
    rw [ambientDart_right, sideObservation_some_iff]

theorem physicalCofacial_iff_ambient {A B : V → Prop}
    (a : RetainedDart RS A) (b : RetainedDart RS B)
    (matching : BoundaryDart RS A ≃ BoundaryDart RS B) (mark : M → RS.D) (m n : M) :
    PhysicalCofacial (ofVertexSide RS A a) (ofVertexSide RS B b) matching
        (sideObservation RS A mark) (sideObservation RS B mark) m n ↔
      ∃ d e : ((ofVertexSide RS A a).composeRotationSystem (ofVertexSide RS B b) matching).D,
        ambientDart a b matching d = mark m ∧ ambientDart a b matching e = mark n ∧
        ((ofVertexSide RS A a).composeRotationSystem (ofVertexSide RS B b) matching).phi.SameCycle d e := by
  constructor
  · rintro ⟨d, e, hd, he, hc⟩
    exact ⟨composeDartEquiv d, composeDartEquiv e,
      (observes_iff_ambient RS a b matching mark m d).mp hd,
      (observes_iff_ambient RS a b matching mark n e).mp he, hc⟩
  · rintro ⟨d, e, hd, he, hc⟩
    obtain ⟨d, rfl⟩ := composeDartEquiv.surjective d
    obtain ⟨e, rfl⟩ := composeDartEquiv.surjective e
    exact ⟨d, e, (observes_iff_ambient RS a b matching mark m d).mpr hd,
      (observes_iff_ambient RS a b matching mark n e).mpr he, hc⟩

theorem ambientDart_rho {A B : V → Prop}
    (a : RetainedDart RS A) (b : RetainedDart RS B)
    (matching : BoundaryDart RS A ≃ BoundaryDart RS B)
    (d : ((ofVertexSide RS A a).composeRotationSystem (ofVertexSide RS B b) matching).D) :
    ambientDart a b matching
        (((ofVertexSide RS A a).composeRotationSystem (ofVertexSide RS B b) matching).rho d) =
      RS.rho (ambientDart a b matching d) := by
  change ambientDart a b matching ((OpenTangleData.composeData _ _ matching).rho d) = _
  rw [OpenTangleData.composeData_rho_apply]
  obtain ⟨x, rfl⟩ := composeDartEquiv.surjective d
  simp only [Equiv.symm_apply_apply]
  rcases x with x | x
  · change ambientDart a b matching (composeDartEquiv (Sum.inl ((ofVertexSide RS A a).rho x))) = _
    rw [ambientDart_left, ofVertexSide_rho_underlying, retainedRho_val, ambientDart_left]
  · change ambientDart a b matching (composeDartEquiv (Sum.inr ((ofVertexSide RS B b).rho x))) = _
    rw [ambientDart_right, ofVertexSide_rho_underlying, retainedRho_val, ambientDart_right]

variable {RS} (deleted : Finset V)
  (outside : RetainedDart RS (deletedSideKeep deleted))
  (inside : RetainedDart RS (deletedRegionKeep deleted))

theorem reassemblyEquiv_phi
    (d : (swappedComplementaryCompositeRS RS deleted outside inside).D) :
    reassemblyEquiv deleted outside inside
        ((swappedComplementaryCompositeRS RS deleted outside inside).phi d) =
      RS.phi (reassemblyEquiv deleted outside inside d) := by
  have ha : ∀ d, reassemblyEquiv deleted outside inside
      ((swappedComplementaryCompositeRS RS deleted outside inside).alpha d) =
        RS.alpha (reassemblyEquiv deleted outside inside d) := by
    intro d
    change complementaryDartEquiv RS deleted inside outside
      (swappedCompositeDartEquiv RS deleted outside inside
        ((swappedComplementaryCompositeRS RS deleted outside inside).alpha d)) = _
    rw [swappedCompositeDartEquiv_alpha, complementaryDartEquiv_alpha]
    rfl
  have hr : ∀ d, reassemblyEquiv deleted outside inside
      ((swappedComplementaryCompositeRS RS deleted outside inside).rho d) =
        RS.rho (reassemblyEquiv deleted outside inside d) := by
    intro d
    rw [reassemblyEquiv_name, ambientDart_rho, ← reassemblyEquiv_name]
  change reassemblyEquiv deleted outside inside
    ((swappedComplementaryCompositeRS RS deleted outside inside).rho
      ((swappedComplementaryCompositeRS RS deleted outside inside).alpha d)) = _
  rw [hr, ha]
  rfl

theorem reassembly_sameCycle_iff
    (d e : (swappedComplementaryCompositeRS RS deleted outside inside).D) :
    (swappedComplementaryCompositeRS RS deleted outside inside).phi.SameCycle d e ↔
      RS.phi.SameCycle (reassemblyEquiv deleted outside inside d) (reassemblyEquiv deleted outside inside e) := by
  have hp : (reassemblyEquiv deleted outside inside).permCongr
      (swappedComplementaryCompositeRS RS deleted outside inside).phi = RS.phi := by
    apply Equiv.ext
    intro z
    obtain ⟨x, rfl⟩ := (reassemblyEquiv deleted outside inside).surjective z
    simpa only [Equiv.permCongr_apply, Equiv.symm_apply_apply] using
      reassemblyEquiv_phi deleted outside inside x
  rw [← hp]
  exact (permCongr_sameCycle_iff (reassemblyEquiv deleted outside inside) _ d e).symm

theorem physicalCofacial_reassembly_iff (mark : M → RS.D) (m n : M) :
    PhysicalCofacial (ofVertexSide RS (deletedSideKeep deleted) outside)
        (ofVertexSide RS (deletedRegionKeep deleted) inside)
        (complementBoundaryAlphaEquiv RS deleted).symm
        (sideObservation RS (deletedSideKeep deleted) mark)
        (sideObservation RS (deletedRegionKeep deleted) mark) m n ↔
      RS.phi.SameCycle (mark m) (mark n) := by
  rw [physicalCofacial_iff_ambient]
  constructor
  · rintro ⟨d, e, hd, he, hc⟩
    have h := (reassembly_sameCycle_iff deleted outside inside d e).mp hc
    simpa only [reassemblyEquiv_name, hd, he] using h
  · intro h
    let iso := reassemblyEquiv deleted outside inside
    refine ⟨iso.symm (mark m), iso.symm (mark n), ?_, ?_, ?_⟩
    · rw [← reassemblyEquiv_name]
      exact iso.apply_symm_apply _
    · rw [← reassemblyEquiv_name]
      exact iso.apply_symm_apply _
    · apply (reassembly_sameCycle_iff deleted outside inside _ _).mpr
      simpa only [iso, Equiv.apply_symm_apply] using h

end
end Mettapedia.GraphTheory.FourColor.VertexSideCofacial

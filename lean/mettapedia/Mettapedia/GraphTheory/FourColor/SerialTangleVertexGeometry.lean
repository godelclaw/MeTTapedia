import Mettapedia.GraphTheory.FourColor.OpenTangleBoundaryView
import Mettapedia.GraphTheory.FourColor.GoertzelV24CompositeSeamCubic

/-!
# Vertex fibres under literal serial sewing

Sewing pairs boundary darts without changing their vertices or rotations.
Each output vertex retains exactly its original dart fibre, so cubicity
and cyclicity of the vertex rotation pass through serial composition.
-/

namespace Mettapedia.GraphTheory.FourColor.SerialTangleVertexGeometry

open GoertzelV24OpenTangleComposition TwoSidedOpenTangleData
open GoertzelV24CompositeSeamCubic SerialTangleSmallCutTransfer

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V W I J L P R : Type*}
  [DecidableEq V] [DecidableEq W]
  [Fintype I] [Fintype J] [Fintype L] [Fintype P] [Fintype R]
  (A : TwoSidedOpenTangleData V I L P) (B : TwoSidedOpenTangleData W J P R)

theorem card_dartsAt_inl (v : V) :
    (openDartsAt (asOpen (A.serialCompose B (Equiv.refl P))) (.inl v)).card =
      (openDartsAt (asOpen A) v).card := by
  refine (Finset.card_bij (fun d _ => serialDartEquiv (Sum.inl d)) ?_ ?_ ?_).symm
  · intro d hd
    simpa only [openDartsAt, Finset.mem_filter, Finset.mem_univ, true_and,
      asOpen_vertOf, serialCompose_vertOf_serialDartEquiv, serialSourceVertOf,
      Sum.inl.injEq] using hd
  · intro d _ d' _ h
    exact Sum.inl.inj (serialDartEquiv.injective h)
  · intro d hd
    obtain ⟨x, rfl⟩ := serialDartEquiv.surjective d
    rcases x with a | b
    · refine ⟨a, ?_, rfl⟩
      simpa only [openDartsAt, Finset.mem_filter, Finset.mem_univ, true_and,
        asOpen_vertOf, serialCompose_vertOf_serialDartEquiv, serialSourceVertOf,
        Sum.inl.injEq] using hd
    · simp only [openDartsAt, Finset.mem_filter, Finset.mem_univ, true_and,
        asOpen_vertOf, serialCompose_vertOf_serialDartEquiv, serialSourceVertOf,
        Sum.inr_ne_inl] at hd

theorem card_dartsAt_inr (w : W) :
    (openDartsAt (asOpen (A.serialCompose B (Equiv.refl P))) (.inr w)).card =
      (openDartsAt (asOpen B) w).card := by
  refine (Finset.card_bij (fun d _ => serialDartEquiv (Sum.inr d)) ?_ ?_ ?_).symm
  · intro d hd
    simpa only [openDartsAt, Finset.mem_filter, Finset.mem_univ, true_and,
      asOpen_vertOf, serialCompose_vertOf_serialDartEquiv, serialSourceVertOf,
      Sum.inr.injEq] using hd
  · intro d _ d' _ h
    exact Sum.inr.inj (serialDartEquiv.injective h)
  · intro d hd
    obtain ⟨x, rfl⟩ := serialDartEquiv.surjective d
    rcases x with a | b
    · simp only [openDartsAt, Finset.mem_filter, Finset.mem_univ, true_and,
        asOpen_vertOf, serialCompose_vertOf_serialDartEquiv, serialSourceVertOf,
        Sum.inl_ne_inr] at hd
    · refine ⟨b, ?_, rfl⟩
      simpa only [openDartsAt, Finset.mem_filter, Finset.mem_univ, true_and,
        asOpen_vertOf, serialCompose_vertOf_serialDartEquiv, serialSourceVertOf,
        Sum.inr.injEq] using hd

theorem serial_isCubic (ha : OpenIsCubic (asOpen A)) (hb : OpenIsCubic (asOpen B)) :
    OpenIsCubic (asOpen (A.serialCompose B (Equiv.refl P))) := by
  rintro (v | w)
  · rw [card_dartsAt_inl]; exact ha v
  · rw [card_dartsAt_inr]; exact hb w

omit [DecidableEq V] [DecidableEq W] in
theorem serial_rotationCyclic (ha : OpenRotationCyclic (asOpen A))
    (hb : OpenRotationCyclic (asOpen B)) :
    OpenRotationCyclic (asOpen (A.serialCompose B (Equiv.refl P))) := by
  intro d d' hv
  obtain ⟨x, rfl⟩ := serialDartEquiv.surjective d
  obtain ⟨x', rfl⟩ := serialDartEquiv.surjective d'
  simp only [asOpen_vertOf, serialCompose_vertOf_serialDartEquiv] at hv
  change Equiv.Perm.SameCycle
    ((serialDartEquiv.symm.trans (Equiv.sumCongr A.rho B.rho)).trans serialDartEquiv)
    (serialDartEquiv x) (serialDartEquiv x')
  rcases x with a | b <;> rcases x' with a' | b'
  · exact sameCycle_conjEquiv _ _
      (sameCycle_sumCongr_inl _ _ (ha a a' (by simpa [asOpen_vertOf, serialSourceVertOf] using hv)))
  · simp [serialSourceVertOf] at hv
  · simp [serialSourceVertOf] at hv
  · exact sameCycle_conjEquiv _ _
      (sameCycle_sumCongr_inr _ _ (hb b b' (by simpa [asOpen_vertOf, serialSourceVertOf] using hv)))

end
end Mettapedia.GraphTheory.FourColor.SerialTangleVertexGeometry

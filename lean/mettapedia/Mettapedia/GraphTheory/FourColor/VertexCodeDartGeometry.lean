import Mettapedia.GraphTheory.FourColor.VertexCodeRealization
import Mettapedia.GraphTheory.FourColor.VertexCodeRotationCyclic

/-!
# Dart coordinates of the actual vertex-code decoder

The attachment carrier is exactly the old darts plus the three new darts.
These equations expose the existing constructor's rotation, incidence,
seams, and persistent ports for the source round-trip induction.
-/

namespace Mettapedia.GraphTheory.FourColor.VertexCodeDartGeometry

open GoertzelV24OpenTangleComposition TwoSidedOpenTangleData
open TubeSlab.VertexTransfer VertexCodePartition VertexCodeRealization
open VertexAttachmentTransfer TwoSidedBoundaryReindex VertexCodeRotationCyclic

noncomputable section
variable {V I : Type*} {l r : ℕ}

def compact : I ⊕ Fin l ≃ I ⊕ (Fin 0 ⊕ Fin l) :=
  Equiv.sumCongr (Equiv.refl I) (Equiv.emptySum (Fin 0) (Fin l)).symm

def stepDarts (a : Code l r) (h : Valid a) :
    (I ⊕ Fin l) ⊕ Fin 3 ≃ ((I ⊕ Empty) ⊕ (Consumed a ⊕ Consumed a)) ⊕ (Fin 0 ⊕ Fin r) :=
  ((Equiv.sumCongr (compact.trans (darts (inCoordinates a h)).symm)
    (dartOrder (starOrder a h))).trans serialDartEquiv).trans (darts (outCoordinates a)).symm

theorem stepDarts_interior (a : Code l r) (h : Valid a) (i : I) :
    stepDarts a h (.inl (.inl i)) = .inl (.inl (.inl i)) := rfl

theorem stepDarts_retained (a : Code l r) (h : Valid a) (p : Retained a) :
    stepDarts (I := I) a h (.inl (.inr p.1.2)) = .inr (.inr p.1.1) := by
  change (stepDarts a h) (.inl (.inr (inputEquiv a h (.inl p)))) = _
  simp only [stepDarts, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl]
  change (darts (outCoordinates a)).symm
    (serialDartEquiv (.inl (.inr ((inputEquiv a h).symm (inputEquiv a h (.inl p)))))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem stepDarts_consumed (a : Code l r) (h : Valid a) (p : Consumed a) :
    stepDarts (I := I) a h (.inl (.inr p.1)) = .inl (.inr (.inl p)) := by
  change (stepDarts a h) (.inl (.inr (inputEquiv a h (.inr p)))) = _
  simp only [stepDarts, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl]
  change (darts (outCoordinates a)).symm
    (serialDartEquiv (.inl (.inr ((inputEquiv a h).symm (inputEquiv a h (.inr p)))))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem stepDarts_new (a : Code l r) (h : Valid a) (b : Consumed a ⊕ Fresh a) :
    stepDarts (I := I) a h (.inr ((starOrder a h).symm b)) =
      match b with
      | .inl p => .inl (.inr (.inr p))
      | .inr p => .inr (.inr p.1) := by
  simp only [stepDarts, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr,
    dartOrder, Equiv.coe_fn_mk, Equiv.apply_symm_apply]
  cases b <;> rfl

theorem rho_reindex {L R L' R' : Type*} (T : TwoSidedOpenTangleData V I L R)
    (e : L' ⊕ R' ≃ L ⊕ R) (d : I ⊕ (L' ⊕ R')) :
    (reindex T e).rho d = (darts e).symm (T.rho (darts e d)) := rfl

theorem rho_serial {W J L P R : Type*}
    (A : TwoSidedOpenTangleData V I L P) (B : TwoSidedOpenTangleData W J P R)
    (d : (I ⊕ (L ⊕ P)) ⊕ (J ⊕ (P ⊕ R))) :
    (A.serialCompose B (Equiv.refl P)).rho (serialDartEquiv d) =
      serialDartEquiv (Equiv.sumCongr A.rho B.rho d) := by
  change serialDartEquiv (Equiv.sumCongr A.rho B.rho
    (serialDartEquiv.symm (serialDartEquiv d))) = _
  rw [Equiv.symm_apply_apply]

theorem rho_old (a : Code l r) (h : Valid a)
    (T : TwoSidedOpenTangleData V I (Fin 0) (Fin l)) (d : I ⊕ Fin l) :
    (attach a h T).rho (stepDarts a h (.inl d)) =
      stepDarts a h (.inl (compact.symm (T.rho (compact d)))) := by
  simp only [attach, rho_reindex, stepDarts, Equiv.trans_apply,
    Equiv.apply_symm_apply, Equiv.sumCongr_apply, Sum.map_inl, append, rho_serial,
    prepared, rho_reindex]

theorem rho_new (a : Code l r) (h : Valid a)
    (T : TwoSidedOpenTangleData V I (Fin 0) (Fin l)) (i : Fin 3) :
    (attach a h T).rho (stepDarts a h (.inr i)) = stepDarts a h (.inr (i + 1)) := by
  simp only [attach, rho_reindex, stepDarts, Equiv.trans_apply,
    Equiv.apply_symm_apply, Equiv.sumCongr_apply, Sum.map_inr, append, rho_serial]
  rw [show (dartOrder (starOrder a h)) i = .inr (starOrder a h i) from rfl,
    star_rotation]
  rfl

theorem vert_old (a : Code l r) (h : Valid a)
    (T : TwoSidedOpenTangleData V I (Fin 0) (Fin l)) (d : I ⊕ Fin l) :
    (attach a h T).vertOf (stepDarts a h (.inl d)) = .inl (T.vertOf (compact d)) := by
  rw [attach, vert_reindex]
  simp only [stepDarts, Equiv.trans_apply, Equiv.apply_symm_apply,
    Equiv.sumCongr_apply, Sum.map_inl]
  rw [append, vertOf_serialCompose, serialOutputVertOf_serialDartEquiv]
  change Sum.inl ((prepared a h T).vertOf _) = _
  rw [prepared, vert_reindex, Equiv.apply_symm_apply]

theorem vert_new (a : Code l r) (h : Valid a)
    (T : TwoSidedOpenTangleData V I (Fin 0) (Fin l)) (i : Fin 3) :
    (attach a h T).vertOf (stepDarts a h (.inr i)) = .inr () := by
  rw [attach, vert_reindex]
  simp only [stepDarts, Equiv.trans_apply, Equiv.apply_symm_apply,
    Equiv.sumCongr_apply, Sum.map_inr]
  rw [append, vertOf_serialCompose, serialOutputVertOf_serialDartEquiv]
  rfl

def initialDarts (a : Code 0 r) (h : Valid a) : Fin 3 ≃ Empty ⊕ Fin r :=
  (((dartOrder (starOrder a h)).trans (darts (initialCoordinates a)).symm).trans compact.symm)

theorem initialDarts_new (a : Code 0 r) (h : Valid a) (p : Fresh a) :
    initialDarts a h ((starOrder a h).symm (.inr p)) = .inr p.1 := by
  simp only [initialDarts, Equiv.trans_apply, dartOrder, Equiv.coe_fn_mk,
    Equiv.apply_symm_apply]
  rfl

theorem initial_rho (a : Code 0 r) (h : Valid a) (i : Fin 3) :
    compact.symm ((initial a h).rho (compact (initialDarts a h i))) =
      initialDarts a h (i + 1) := by
  simp only [initial, rho_reindex, initialDarts, Equiv.trans_apply,
    Equiv.apply_symm_apply]
  rw [show dartOrder (starOrder a h) i = .inr (starOrder a h i) from rfl, star_rotation]
  rfl

end
end Mettapedia.GraphTheory.FourColor.VertexCodeDartGeometry

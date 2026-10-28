import Mettapedia.Computability.PNP.ApproximateDecorrelationFoundation

namespace Mettapedia.Computability.PNP

/-- If `E` and `F` are coupled inside `C`, the forward approximate
decorrelation defect is exactly the product of the two conditioned source-bit
fibers. -/
theorem countIndependentWithinForwardGap_coupled
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (hcouple : ∀ ω, C ω → (E ω ↔ F ω)) :
    countIndependentWithinForwardGap (Ω := Ω) C E F =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) *
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) := by
  classical
  have hCEF :
      finiteEventCount Ω (fun ω => C ω ∧ E ω ∧ F ω) =
        finiteEventCount Ω (fun ω => C ω ∧ E ω) := by
    exact finiteEventCount_congr_approximate (Ω := Ω) (fun ω => by
      constructor
      · intro h
        exact ⟨h.1, h.2.1⟩
      · intro h
        exact ⟨h.1, h.2, (hcouple ω h.1).1 h.2⟩)
  have hCF :
      finiteEventCount Ω (fun ω => C ω ∧ F ω) =
        finiteEventCount Ω (fun ω => C ω ∧ E ω) := by
    exact finiteEventCount_congr_approximate (Ω := Ω) (fun ω => by
      constructor
      · intro h
        exact ⟨h.1, (hcouple ω h.1).2 h.2⟩
      · intro h
        exact ⟨h.1, (hcouple ω h.1).1 h.2⟩)
  have hsplit := finiteEventCount_split_by_approximate (Ω := Ω) C E
  simp only [countIndependentWithinForwardGap, hCEF, hCF, hsplit]
  rw [Nat.add_mul, Nat.add_sub_cancel_left, Nat.mul_comm]

/-- If `E` and `F` are anti-coupled inside `C`, the backward approximate
decorrelation defect is exactly the product of the two conditioned source-bit
fibers. -/
theorem countIndependentWithinBackwardGap_anticoupled
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (hanti : ∀ ω, C ω → (E ω ↔ ¬ F ω)) :
    countIndependentWithinBackwardGap (Ω := Ω) C E F =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) *
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) := by
  classical
  have hCEF :
      finiteEventCount Ω (fun ω => C ω ∧ E ω ∧ F ω) = 0 := by
    have hfalse :
        finiteEventCount Ω (fun ω => C ω ∧ E ω ∧ F ω) =
          finiteEventCount Ω (fun _ω => False) := by
      exact finiteEventCount_congr_approximate (Ω := Ω) (fun ω => by
        constructor
        · intro h
          exact ((hanti ω h.1).1 h.2.1) h.2.2
        · intro h
          cases h)
    simpa [finiteEventCount] using hfalse
  have hCF :
      finiteEventCount Ω (fun ω => C ω ∧ F ω) =
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) := by
    exact finiteEventCount_congr_approximate (Ω := Ω) (fun ω => by
      constructor
      · intro h
        refine ⟨h.1, ?_⟩
        intro hE
        exact ((hanti ω h.1).1 hE) h.2
      · intro h
        refine ⟨h.1, ?_⟩
        by_contra hnotF
        exact h.2 ((hanti ω h.1).2 hnotF))
  simp [countIndependentWithinBackwardGap, hCEF, hCF]

/-- Nondegenerate coupled conditioning leaves a strictly positive forward
defect. -/
theorem countIndependentWithinForwardGap_pos_of_coupled_nonconstant_on_condition
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (hcouple : ∀ ω, C ω → (E ω ↔ F ω))
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    0 < countIndependentWithinForwardGap (Ω := Ω) C E F := by
  rw [countIndependentWithinForwardGap_coupled C E F hcouple]
  exact Nat.mul_pos hpos hneg

/-- Nondegenerate anti-coupled conditioning leaves a strictly positive backward
defect. -/
theorem countIndependentWithinBackwardGap_pos_of_anticoupled_nonconstant_on_condition
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (hanti : ∀ ω, C ω → (E ω ↔ ¬ F ω))
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    0 < countIndependentWithinBackwardGap (Ω := Ω) C E F := by
  rw [countIndependentWithinBackwardGap_anticoupled C E F hanti]
  exact Nat.mul_pos hpos hneg

/-- A nondegenerate conditioned source bit has positive source-fiber product. -/
theorem conditionedSourceFiberProduct_pos_of_nonconstant_on_condition
    {Ω : Type*} [Fintype Ω]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    0 < conditionedSourceFiberProduct (Ω := Ω) C E := by
  exact Nat.mul_pos hpos hneg

/-- Lower bounds on the two conditioned source-bit fibers multiply into a
lower bound on the source-fiber product. -/
theorem lowerBounds_mul_le_conditionedSourceFiberProduct
    {Ω : Type*} [Fintype Ω]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    loTrue * loFalse ≤ conditionedSourceFiberProduct (Ω := Ω) C E := by
  exact Nat.mul_le_mul htrue hfalse

end Mettapedia.Computability.PNP

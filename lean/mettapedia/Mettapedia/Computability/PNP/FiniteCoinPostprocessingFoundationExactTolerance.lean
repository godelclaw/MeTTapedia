import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactObservedInjective

/-!
# Finite-coin postprocessing: exact tolerance and defect transfer

Observed-support-injective postprocessing, or an observed left inverse, preserves
finite-coin tolerance certificates and maximum output defect exactly.
-/

namespace Mettapedia.Computability.PNP

/-- On the finite-coin output surface, postprocessing that is injective on the
observed support preserves the whole tolerance certificate exactly.  Lossless
coarsening on the proof-relevant support cannot reduce the required
approximation budget. -/
theorem countIndependentWithinToleranceOutput_finiteCoinOutput_postcompose_iff_of_observedInjective
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (τ : Nat)
    (hinjObs :
      ∀ b1 c1 b2 c2,
        g (r b1 c1) = g (r b2 c2) → r b1 c1 = r b2 c2) :
    CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (fun b c => g (r b c))) τ ↔
    CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) τ := by
  rw [countIndependentWithinToleranceOutput_finiteCoinOutput_iff_forall_scaled_fiberImbalance_le,
    countIndependentWithinToleranceOutput_finiteCoinOutput_iff_forall_scaled_fiberImbalance_le]
  constructor
  · intro h y
    by_cases hobs : ∃ b : Bool, ∃ c : Coin, r b c = y
    · have htrue :=
        coinTrueFiberCount_postcompose_observedInjective r g hinjObs hobs
      have hfalse :=
        coinFalseFiberCount_postcompose_observedInjective r g hinjObs hobs
      have himb :
          finiteCoinFiberImbalance (fun b c => g (r b c)) (g y) =
            finiteCoinFiberImbalance r y := by
        simp [finiteCoinFiberImbalance, htrue, hfalse]
      simpa [himb] using h (g y)
    · have htrue_zero : coinTrueFiberCount r y = 0 := by
        exact finiteEventCount_zero_of_forall_not (Ω := Coin)
          (fun c => r true c = y)
          (fun c hc => hobs ⟨true, c, hc⟩)
      have hfalse_zero : coinFalseFiberCount r y = 0 := by
        exact finiteEventCount_zero_of_forall_not (Ω := Coin)
          (fun c => r false c = y)
          (fun c hc => hobs ⟨false, c, hc⟩)
      simp [finiteCoinFiberImbalance, htrue_zero, hfalse_zero]
  · intro h z
    by_cases hobs :
        ∃ b : Bool, ∃ c : Coin, g (r b c) = z
    · rcases hobs with ⟨b0, c0, hz⟩
      let y := r b0 c0
      have hyobs : ∃ b : Bool, ∃ c : Coin, r b c = y := ⟨b0, c0, rfl⟩
      have htrue :=
        coinTrueFiberCount_postcompose_observedInjective r g hinjObs hyobs
      have hfalse :=
        coinFalseFiberCount_postcompose_observedInjective r g hinjObs hyobs
      have hz' : z = g y := by
        simpa [y] using hz.symm
      subst z
      have himb :
          finiteCoinFiberImbalance (fun b c => g (r b c)) (g y) =
            finiteCoinFiberImbalance r y := by
        simp [finiteCoinFiberImbalance, htrue, hfalse]
      simpa [y, himb] using h y
    · have htrue_zero :
          coinTrueFiberCount (fun b c => g (r b c)) z = 0 := by
        exact finiteEventCount_zero_of_forall_not (Ω := Coin)
          (fun c => g (r true c) = z)
          (fun c hc => hobs ⟨true, c, hc⟩)
      have hfalse_zero :
          coinFalseFiberCount (fun b c => g (r b c)) z = 0 := by
        exact finiteEventCount_zero_of_forall_not (Ω := Coin)
          (fun c => g (r false c) = z)
          (fun c hc => hobs ⟨false, c, hc⟩)
      simp [finiteCoinFiberImbalance, htrue_zero, hfalse_zero]

/-- An observed left inverse on the actually observed outputs gives the same
exact tolerance preservation as observed injectivity. -/
theorem countIndependentWithinToleranceOutput_finiteCoinOutput_postcompose_iff_of_observedLeftInverse
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (recover : β → α) (τ : Nat)
    (hrecover : ∀ b c, recover (g (r b c)) = r b c) :
    CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (fun b c => g (r b c))) τ ↔
    CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) τ := by
  have hinjObs :
      ∀ b1 c1 b2 c2,
        g (r b1 c1) = g (r b2 c2) → r b1 c1 = r b2 c2 := by
    intro b1 c1 b2 c2 hEq
    calc
      r b1 c1 = recover (g (r b1 c1)) := (hrecover b1 c1).symm
      _ = recover (g (r b2 c2)) := by rw [hEq]
      _ = r b2 c2 := hrecover b2 c2
  exact
    countIndependentWithinToleranceOutput_finiteCoinOutput_postcompose_iff_of_observedInjective
      r g τ hinjObs

/-- For finite output types, observed-support-injective postprocessing
preserves the whole max output defect exactly. -/
theorem countIndependentWithinOutputDefect_finiteCoinOutput_postcompose_eq_of_observedInjective
    {Coin α β : Type*} [Fintype Coin] [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinjObs :
      ∀ b1 c1 b2 c2,
        g (r b1 c1) = g (r b2 c2) → r b1 c1 = r b2 c2) :
    countIndependentWithinOutputDefect (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (fun b c => g (r b c))) =
    countIndependentWithinOutputDefect (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) := by
  apply le_antisymm
  · let D :=
      countIndependentWithinOutputDefect (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (finiteCoinOutput r)
    have hpost :
        CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
          (fun _ω => True)
          (finiteCoinSourceTrue (Coin := Coin))
          (finiteCoinOutput (fun b c => g (r b c))) D := by
      exact
        (countIndependentWithinToleranceOutput_finiteCoinOutput_postcompose_iff_of_observedInjective
          r g D hinjObs).2
        ((countIndependentWithinToleranceOutput_iff_outputDefect_le
          (fun _ω : Bool × Coin => True)
          (finiteCoinSourceTrue (Coin := Coin))
          (finiteCoinOutput r) D).mpr le_rfl)
    exact
      (countIndependentWithinToleranceOutput_iff_outputDefect_le
        (fun _ω : Bool × Coin => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (finiteCoinOutput (fun b c => g (r b c))) D).mp hpost
  · let D :=
      countIndependentWithinOutputDefect (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (finiteCoinOutput (fun b c => g (r b c)))
    have horig :
        CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
          (fun _ω => True)
          (finiteCoinSourceTrue (Coin := Coin))
          (finiteCoinOutput r) D := by
      exact
        (countIndependentWithinToleranceOutput_finiteCoinOutput_postcompose_iff_of_observedInjective
          r g D hinjObs).1
        ((countIndependentWithinToleranceOutput_iff_outputDefect_le
          (fun _ω : Bool × Coin => True)
          (finiteCoinSourceTrue (Coin := Coin))
          (finiteCoinOutput (fun b c => g (r b c))) D).mpr le_rfl)
    exact
      (countIndependentWithinToleranceOutput_iff_outputDefect_le
        (fun _ω : Bool × Coin => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (finiteCoinOutput r) D).mp horig

/-- An observed left inverse on the actually observed outputs also preserves
the max output defect exactly. -/
theorem countIndependentWithinOutputDefect_finiteCoinOutput_postcompose_eq_of_observedLeftInverse
    {Coin α β : Type*} [Fintype Coin] [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (recover : β → α)
    (hrecover : ∀ b c, recover (g (r b c)) = r b c) :
    countIndependentWithinOutputDefect (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (fun b c => g (r b c))) =
    countIndependentWithinOutputDefect (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) := by
  have hinjObs :
      ∀ b1 c1 b2 c2,
        g (r b1 c1) = g (r b2 c2) → r b1 c1 = r b2 c2 := by
    intro b1 c1 b2 c2 hEq
    calc
      r b1 c1 = recover (g (r b1 c1)) := (hrecover b1 c1).symm
      _ = recover (g (r b2 c2)) := by rw [hEq]
      _ = r b2 c2 := hrecover b2 c2
  exact
    countIndependentWithinOutputDefect_finiteCoinOutput_postcompose_eq_of_observedInjective
      r g hinjObs

end Mettapedia.Computability.PNP

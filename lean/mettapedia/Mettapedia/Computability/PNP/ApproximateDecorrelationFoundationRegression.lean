import Mettapedia.Computability.PNP.ApproximateDecorrelationFoundation

/-!
# Regression wrappers for finite-count foundations used by approximate decorrelation.
-/

namespace Mettapedia.Computability.PNP.ApproximateDecorrelationObstructionRegression

open Mettapedia.Computability.PNP

theorem finite_event_count_fst_lift_regression
    {Ω Coin : Type*} [Fintype Ω] [Fintype Coin]
    (P : Ω → Prop) [DecidablePred P] :
    finiteEventCount (Ω × Coin) (fun xr => P xr.1) =
      finiteEventCount Ω P * Fintype.card Coin := by
  exact finiteEventCount_fst_lift P

theorem finite_event_count_fst_lift_pos_of_pos_regression
    {Ω Coin : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin]
    (P : Ω → Prop) [DecidablePred P]
    (hpos : 0 < finiteEventCount Ω P) :
    0 < finiteEventCount (Ω × Coin) (fun xr => P xr.1) := by
  exact finiteEventCount_fst_lift_pos_of_pos P hpos

theorem finite_event_count_prod_regression
    {Ω Coin : Type*} [Fintype Ω] [Fintype Coin]
    (P : Ω → Prop) (Q : Coin → Prop) [DecidablePred P] [DecidablePred Q] :
    finiteEventCount (Ω × Coin) (fun xr => P xr.1 ∧ Q xr.2) =
      finiteEventCount Ω P * finiteEventCount Coin Q := by
  exact finiteEventCount_prod P Q

theorem finite_event_count_eq_self_regression
    {α : Type*} [Fintype α] [DecidableEq α] (a : α) :
    finiteEventCount α (fun x => x = a) = 1 := by
  exact finiteEventCount_eq_self a

theorem finite_event_count_zero_of_forall_not_regression
    {Ω : Type*} [Fintype Ω] (P : Ω → Prop) [DecidablePred P]
    (hfalse : ∀ ω, ¬ P ω) :
    finiteEventCount Ω P = 0 := by
  exact finiteEventCount_zero_of_forall_not P hfalse

theorem finite_event_count_comp_eq_sum_fibers_of_maps_to_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Coin → α) (s : Finset α) (P : α → Prop) [DecidablePred P]
    (hr : ∀ c : Coin, r c ∈ s) :
    finiteEventCount Coin (fun c => P (r c)) =
      ∑ y ∈ s.filter P, finiteEventCount Coin (fun c => r c = y) := by
  exact finiteEventCount_comp_eq_sum_fibers_of_mapsTo r s P hr

theorem finite_event_count_bool_true_add_false_regression
    {Ω : Type*} [Fintype Ω] (B : Ω → Bool) :
    finiteEventCount Ω (fun ω => B ω = true) +
      finiteEventCount Ω (fun ω => B ω = false) = Fintype.card Ω := by
  exact finiteEventCount_bool_true_add_false B

end Mettapedia.Computability.PNP.ApproximateDecorrelationObstructionRegression

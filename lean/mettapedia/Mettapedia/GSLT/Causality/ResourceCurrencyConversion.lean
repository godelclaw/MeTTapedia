import Mettapedia.GSLT.Scope.ConversionPotentials
import Mettapedia.GSLT.Causality.ResourceRuns
import Mathlib.Data.Multiset.Replicate

/-!
# Admitted integer-batch currency conversions

An enzyme has independently supplied positive input and output lot sizes.
Their ratio must realize its declared graph rate. A firing retains the
enzyme, its permission proof and its positive lot multiplicity. The resource
system consumes and produces the actual token occurrences.

A common graph measure preserves value through every actual conversion
history. It does not manufacture an integer-batch realization of an arbitrary
real rate, a permission or the token occurrences required to fire.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ResourceInteraction.CurrencyConversion

open Mettapedia.GSLT.Scope.ConversionRates
open Mettapedia.GSLT.Causality.OccurrenceHistory

universe uToken uEdge

variable {Token : Type uToken} (G : Graph.{uToken, uEdge} Token)

abbrev Enzyme := Σ source, Σ target, G.Edge source target

structure Batches where
  input : Enzyme G → Nat
  output : Enzyme G → Nat
  input_positive : ∀ enzyme, 0 < input enzyme
  output_positive : ∀ enzyme, 0 < output enzyme
  realizes : ∀ enzyme, G.rate enzyme.2.2 * (input enzyme : ℝ) = (output enzyme : ℝ)

def resources (batches : Batches G) (permission : Enzyme G → Prop) :
    System.{uToken, max uToken uEdge} Token where
  Site := Enzyme G
  Instance enzyme := {quantity : ULift.{max uToken uEdge} Nat //
    0 < quantity.down ∧ permission enzyme}
  consume {enzyme} firing := Multiset.replicate (batches.input enzyme * firing.val.down) enzyme.1
  read _ := 0
  produce {enzyme} firing := Multiset.replicate (batches.output enzyme * firing.val.down) enzyme.2.1

theorem instance_permission (batches : Batches G) (permission : Enzyme G → Prop)
    {enzyme : Enzyme G} (firing : (resources G batches permission).Instance enzyme) :
    permission enzyme := firing.property.2

theorem instance_positive (batches : Batches G) (permission : Enzyme G → Prop)
    {enzyme : Enzyme G} (firing : (resources G batches permission).Instance enzyme) :
    0 < ((resources G batches permission).consume firing).card := by
  change 0 < (Multiset.replicate (batches.input enzyme * firing.val.down) enzyme.1).card
  rw [Multiset.card_replicate]
  exact Nat.mul_pos (batches.input_positive enzyme) firing.property.1

noncomputable section

def wealth (valuation : G.Valuation) : Multiset Token →+ ℝ where
  toFun inventory := (inventory.map valuation.price).sum
  map_zero' := rfl
  map_add' first second := by simp only [Multiset.map_add, Multiset.sum_add]

theorem wealth_lot (valuation : G.Valuation) (quantity : Nat) (token : Token) :
    wealth G valuation (Multiset.replicate quantity token) = (quantity : ℝ) * valuation.price token := by
  change (Multiset.map valuation.price (Multiset.replicate quantity token)).sum = _
  simp only [Multiset.map_replicate, Multiset.sum_replicate, nsmul_eq_mul]

theorem batch_value (batches : Batches G) (valuation : G.Valuation) (enzyme : Enzyme G) :
    (batches.input enzyme : ℝ) * valuation.price enzyme.1 =
      (batches.output enzyme : ℝ) * valuation.price enzyme.2.1 := by
  have equation := batches.realizes enzyme
  rw [valuation.respects enzyme.2.2] at equation
  field_simp [(valuation.positive enzyme.2.1).ne'] at equation
  simpa only [mul_comm] using equation

theorem instance_value (batches : Batches G) (permission : Enzyme G → Prop)
    (valuation : G.Valuation) {enzyme : Enzyme G}
    (firing : (resources G batches permission).Instance enzyme) :
    wealth G valuation ((resources G batches permission).consume firing) =
      wealth G valuation ((resources G batches permission).produce firing) := by
  change wealth G valuation (Multiset.replicate _ _) = wealth G valuation (Multiset.replicate _ _)
  rw [wealth_lot, wealth_lot, Nat.cast_mul, Nat.cast_mul]
  calc (batches.input enzyme : ℝ) * (firing.val.down : ℝ) * valuation.price enzyme.1
      = (firing.val.down : ℝ) * ((batches.input enzyme : ℝ) * valuation.price enzyme.1) := by ring
    _ = (firing.val.down : ℝ) * ((batches.output enzyme : ℝ) * valuation.price enzyme.2.1) := by
      rw [batch_value G batches valuation enzyme]
    _ = (batches.output enzyme : ℝ) * (firing.val.down : ℝ) * valuation.price enzyme.2.1 := by ring

variable [DecidableEq Token]

theorem history_value_conserved (batches : Batches G) (permission : Enzyme G → Prop)
    (valuation : G.Valuation) {source target : Multiset Token}
    (history : OccurrencePath (resources G batches permission).presentation source target) :
    wealth G valuation source = wealth G valuation target := by
  let system := resources G batches permission
  have balance := system.balance_observed (wealth G valuation)
    (map_zero (wealth G valuation)) (map_add (wealth G valuation)) history
  have matched := system.instanceValuation_congr
    (fun {_enzyme} firing => (instance_value G batches permission valuation firing).symm) history
  rw [matched] at balance
  exact add_right_cancel balance

end

end Mettapedia.GSLT.Causality.ResourceInteraction.CurrencyConversion

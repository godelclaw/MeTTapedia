import Mettapedia.GSLT.Causality.ResourceCurrencyConversion

/-!
# Equal currency values do not grant an enzyme or its input tokens

One left token has the value of two right tokens. A permitted left-to-right
enzyme actually exchanges them. Its reverse mathematical rate does not grant
the withheld reverse permission. Equal-valued right tokens also cannot serve
as the input occurrences of the forward firing.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ResourceInteraction.CurrencyControls

open Mettapedia.GSLT.Scope.ConversionRates
open OccurrenceHistory CurrencyConversion

noncomputable section

inductive Token where
  | left
  | right
  deriving DecidableEq

inductive Exchange : Token → Token → Type where
  | forward : Exchange .left .right
  | backward : Exchange .right .left

def rate : {source target : Token} → Exchange source target → ℝ
  | _, _, .forward => 2
  | _, _, .backward => 1 / 2

abbrev graph : Graph Token where
  Edge := Exchange
  rate := rate
  positive edge := by cases edge <;> norm_num [rate]

def tokenPrice : Token → ℝ
  | .left => 2
  | .right => 1

def commonValue : graph.Valuation where
  price := tokenPrice
  positive token := by cases token <;> norm_num [tokenPrice]
  respects edge := by cases edge <;> norm_num [rate, tokenPrice]

def inputLot : Enzyme graph → Nat
  | ⟨_, _, .forward⟩ => 1
  | ⟨_, _, .backward⟩ => 2

def outputLot : Enzyme graph → Nat
  | ⟨_, _, .forward⟩ => 2
  | ⟨_, _, .backward⟩ => 1

def lots : Batches graph where
  input := inputLot
  output := outputLot
  input_positive enzyme := by rcases enzyme with ⟨_, _, edge⟩; cases edge <;> decide
  output_positive enzyme := by rcases enzyme with ⟨_, _, edge⟩; cases edge <;> decide
  realizes enzyme := by rcases enzyme with ⟨_, _, edge⟩; cases edge <;> norm_num [rate, inputLot, outputLot]

def permission (enzyme : Enzyme graph) : Prop := enzyme.1 = Token.left

abbrev forwardEnzyme : Enzyme graph := ⟨.left, .right, .forward⟩

abbrev backwardEnzyme : Enzyme graph := ⟨.right, .left, .backward⟩

abbrev system : System Token := CurrencyConversion.resources graph lots permission

def forwardInstance : system.Instance forwardEnzyme := ⟨⟨1⟩, Nat.zero_lt_one, rfl⟩

def leftPurse : Multiset Token := Multiset.replicate 1 .left

def rightPurse : Multiset Token := Multiset.replicate 2 .right

theorem actual_input_enabled : system.Enables leftPurse forwardInstance := by
  change Multiset.replicate (1 * 1) Token.left + 0 ≤ Multiset.replicate 1 Token.left
  decide

theorem actual_exchange_result : system.fire leftPurse forwardInstance = rightPurse := by
  change Multiset.replicate 1 Token.left - Multiset.replicate (1 * 1) Token.left +
    Multiset.replicate (2 * 1) Token.right = Multiset.replicate 2 Token.right
  decide

def conversion : Occurrence system.presentation leftPurse rightPurse :=
  ⟨forwardEnzyme, ⟨forwardInstance, actual_input_enabled, actual_exchange_result.symm⟩⟩

def conversionHistory : OccurrencePath system.presentation leftPurse rightPurse :=
  .cons conversion (.refl _)

theorem actual_history_conserves_value : wealth graph commonValue leftPurse = wealth graph commonValue rightPurse :=
  history_value_conserved graph lots permission commonValue conversionHistory

theorem both_purses_have_value_two : wealth graph commonValue leftPurse = 2 ∧
    wealth graph commonValue rightPurse = 2 := by
  constructor
  · rw [leftPurse, wealth_lot]
    norm_num [commonValue, tokenPrice]
  · rw [rightPurse, wealth_lot]
    norm_num [commonValue, tokenPrice]

theorem equal_value_does_not_supply_the_forward_input :
    ¬ system.Enables rightPurse forwardInstance := by
  change ¬ Multiset.replicate (1 * 1) Token.left + 0 ≤ Multiset.replicate 2 Token.right
  decide

theorem reverse_rate_does_not_grant_the_reverse_permission :
    ¬ Nonempty (system.Instance backwardEnzyme) := by
  rintro ⟨firing⟩
  have notPermitted := firing.property.2
  cases notPermitted

theorem conversion_retains_the_actual_lot :
    system.pathEntries conversionHistory = [⟨forwardEnzyme, forwardInstance⟩] := rfl

end

end Mettapedia.GSLT.Causality.ResourceInteraction.CurrencyControls

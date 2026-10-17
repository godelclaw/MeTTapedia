import Mettapedia.Computability.StackMachineCompositionSpace
import Mettapedia.Computability.WordHomomorphismMachine

/-!
# Expansion followed by erasure

The first original word machine doubles each symbol. The second erases every
symbol. Final output size is zero, but both stages and their physical handoff
reach four live cells. Sequential peak is four, rather than the sum eight.
-/
set_option autoImplicit false

namespace Mettapedia.Computability.StackMachineCompositionSpace.Controls

open Turing ExecutionSpace StackMachineComposition

def double (symbol : Bool) : List Bool := [symbol, symbol]
def erase (_symbol : Bool) : List Bool := []
def expanding := WordHomomorphismMachine.machine double
def erasing := WordHomomorphismMachine.machine erase

local instance : Fintype (expanding.Γ expanding.k₁) := inferInstanceAs (Fintype Bool)
local instance : Inhabited (expanding.Γ expanding.k₁) := inferInstanceAs (Inhabited Bool)

def joined := machine expanding erasing (Equiv.refl Bool)

local instance : DecidableEq joined.Λ := inferInstanceAs (DecidableEq
  (WordHomomorphismMachine.Phase (WordHomomorphismMachine.capacity double) ⊕
    (Bool ⊕ WordHomomorphismMachine.Phase (WordHomomorphismMachine.capacity erase))))
local instance : DecidableEq joined.σ := inferInstanceAs (DecidableEq
  ((Option Bool × Option Bool) × (Option Bool × Option Bool) × Option Bool))
local instance : DecidableEq (joined.Γ none) := inferInstanceAs (DecidableEq Bool)

theorem expansion_peak :
    peak expanding.step (stackCells expanding) 14 (some (initList expanding [true, false])) = 4 := by
  decide +kernel

theorem erasure_peak :
    peak erasing.step (stackCells erasing) 10 (some (initList erasing [true, true, false, false])) = 4 := by
  decide +kernel

theorem joined_peak :
    peak joined.step (stackCells joined) 34 (some (initList joined [true, false])) = 4 := by
  decide +kernel

theorem original_output :
    let final := (fun state : Option joined.Cfg => state.bind joined.step)^[34]
      (some (initList joined [true, false]))
    final.map (fun state => state.l) = some none ∧
    final.map (fun state => state.var) = some ((none, none), (none, none), none) ∧
    final.map (fun state => [state.stk none,
      state.stk (some (.inl .input)), state.stk (some (.inl .output)),
      state.stk (some (.inl .result)), state.stk (some (.inr .input)),
      state.stk (some (.inr .output)), state.stk (some (.inr .result))]) =
        some [[], [], [], [], [], [], []] := by
  dsimp only
  constructor
  · decide +kernel
  constructor
  · exact @of_decide_eq_true _
      ((inferInstance : DecidableEq (Option
        ((Option Bool × Option Bool) × (Option Bool × Option Bool) × Option Bool))) _ _) rfl
  · decide +kernel

theorem output_size_is_not_peak :
    ([] : List Bool).length <
      peak joined.step (stackCells joined) 34 (some (initList joined [true, false])) := by
  rw [joined_peak]
  decide

theorem sequential_peak_is_not_additive :
    peak joined.step (stackCells joined) 34 (some (initList joined [true, false])) ≠
      peak expanding.step (stackCells expanding) 14 (some (initList expanding [true, false])) +
      peak erasing.step (stackCells erasing) 10 (some (initList erasing [true, true, false, false])) := by
  rw [joined_peak, expansion_peak, erasure_peak]
  decide

theorem empty_handoff_peak :
    peak joined.step (stackCells joined) 2
      (some (firstConfig expanding erasing (Equiv.refl Bool) (haltList expanding []))) = 0 :=
  transfer_peak expanding erasing (Equiv.refl Bool) []

end Mettapedia.Computability.StackMachineCompositionSpace.Controls

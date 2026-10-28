import Mathlib.Data.Nat.ModEq
import Lean.Elab.Tactic.Omega

/-!
# Reserved-zero serial numbers

Valid serials are `1..modulus`; zero means absent or invalid. The successor of
the maximum is one. Ordinary integer comparison therefore cannot select the
newest of two snapshots across wraparound.

The relation below uses forward distance around that serial space. It agrees
with logical history inside a bounded window, and always recognizes an
adjacent publication. It is not a global order on unbounded histories.

This is an ordering core for versioned storage and caches. It makes no claim
that a checksum detects every torn write or that native page I/O is atomic.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Storage.SerialNumbers

structure Space where
  modulus : Nat
  atLeastThree : 3 ≤ modulus

def Valid (space : Space) (serial : Nat) : Prop := 0 < serial ∧ serial ≤ space.modulus

def next (space : Space) (serial : Nat) : Nat :=
  if serial = space.modulus then 1 else serial + 1

def distance (space : Space) (new old : Nat) : Nat :=
  if old ≤ new then new - old else (space.modulus - old) + new

/-- Ties choose the first slot. A present snapshot beats an absent slot. -/
def firstCurrent (space : Space) (a b : Nat) : Bool :=
  if a = 0 then decide (b = 0)
  else if b = 0 then true
  else if a = b then true
  else decide (distance space a b ≤ space.modulus / 2)

def encode (space : Space) (logical : Nat) : Nat := logical % space.modulus + 1

theorem modulus_positive (space : Space) : 0 < space.modulus := by
  have := space.atLeastThree
  omega

theorem next_valid (space : Space) {serial : Nat} (bound : serial ≤ space.modulus) :
    Valid space (next space serial) := by
  have := space.atLeastThree
  unfold next Valid
  split <;> omega

theorem encode_valid (space : Space) (logical : Nat) : Valid space (encode space logical) := by
  have := Nat.mod_lt logical (modulus_positive space)
  unfold Valid encode
  omega

theorem successor_distance (space : Space) (serial : Nat) :
    distance space (next space serial) serial = 1 := by
  have := space.atLeastThree
  unfold next distance
  split <;> split <;> omega

theorem predecessor_distance (space : Space) {serial : Nat} (valid : Valid space serial) :
    distance space serial (next space serial) = space.modulus - 1 := by
  have := space.atLeastThree
  unfold Valid at valid
  unfold next distance
  split <;> split <;> omega

theorem next_ne_current (space : Space) (serial : Nat) :
    next space serial ≠ serial := by
  have := space.atLeastThree
  unfold next
  split <;> omega

theorem successor_selected (space : Space) {serial : Nat} (valid : Valid space serial) :
    firstCurrent space (next space serial) serial = true := by
  have newerValid := next_valid space valid.2
  have different := next_ne_current space serial
  have one := successor_distance space serial
  have large := space.atLeastThree
  simp only [firstCurrent, Nat.ne_of_gt newerValid.1, Nat.ne_of_gt valid.1, different,
    ↓reduceIte, one, decide_eq_true_eq]
  omega

theorem predecessor_rejected (space : Space) {serial : Nat} (valid : Valid space serial) :
    firstCurrent space serial (next space serial) = false := by
  have newerValid := next_valid space valid.2
  have different := next_ne_current space serial
  have back := predecessor_distance space valid
  have large := space.atLeastThree
  simp only [firstCurrent, Nat.ne_of_gt valid.1, Nat.ne_of_gt newerValid.1, Ne.symm different,
    ↓reduceIte, back, decide_eq_false_iff_not]
  omega

theorem absent_loses (space : Space) {serial : Nat} (valid : Valid space serial) :
    firstCurrent space 0 serial = false ∧ firstCurrent space serial 0 = true := by
  simp [firstCurrent, Nat.ne_of_gt valid.1]

theorem successor_wins (space : Space) {serial : Nat} (bound : serial ≤ space.modulus) :
    firstCurrent space (next space serial) serial = true ∧
    firstCurrent space serial (next space serial) = false := by
  by_cases zero : serial = 0
  · subst serial
    have positive := modulus_positive space
    simp [firstCurrent, next]
  · have valid : Valid space serial := ⟨Nat.pos_of_ne_zero zero, bound⟩
    exact ⟨successor_selected space valid, predecessor_rejected space valid⟩

theorem distance_complement (space : Space) {a b : Nat} (va : Valid space a)
    (vb : Valid space b) (different : a ≠ b) :
    distance space a b + distance space b a = space.modulus := by
  unfold Valid at va vb
  unfold distance
  split <;> split <;> omega

theorem distance_bounded (space : Space) {a b : Nat} (va : Valid space a)
    (vb : Valid space b) : distance space a b < space.modulus := by
  unfold Valid at va vb
  unfold distance
  split <;> omega

/-- An unbounded logical clock realizes the finite serial cycle. The proof
handles both sides of wraparound rather than assuming numeric order. -/
theorem encoded_forward_distance (space : Space) (logical delta : Nat)
    (positive : 0 < delta) (small : delta < space.modulus) :
    distance space (encode space (logical + delta)) (encode space logical) = delta := by
  have remainder := Nat.mod_lt logical (modulus_positive space)
  unfold encode
  rw [Nat.add_mod, Nat.mod_eq_of_lt small]
  by_cases wraps : logical % space.modulus + delta < space.modulus
  · rw [Nat.mod_eq_of_lt wraps]
    unfold distance
    split <;> omega
  · rw [Nat.mod_eq_sub_mod (by omega)]
    rw [Nat.mod_eq_of_lt (by omega)]
    unfold distance
    split <;> omega

theorem bounded_logical_history_selects_newer (space : Space) (logical delta : Nat)
    (positive : 0 < delta) (window : 2 * delta < space.modulus) :
    firstCurrent space (encode space (logical + delta)) (encode space logical) = true ∧
    firstCurrent space (encode space logical) (encode space (logical + delta)) = false := by
  have small : delta < space.modulus := by omega
  have forward := encoded_forward_distance space logical delta positive small
  have oldValid := encode_valid space logical
  have newValid := encode_valid space (logical + delta)
  have different : encode space (logical + delta) ≠ encode space logical := by
    intro same
    rw [same] at forward
    simp [distance] at forward
    omega
  have complement := distance_complement space oldValid newValid (Ne.symm different)
  have backward : distance space (encode space logical) (encode space (logical + delta)) =
      space.modulus - delta := by omega
  constructor
  · simp only [firstCurrent, Nat.ne_of_gt newValid.1, Nat.ne_of_gt oldValid.1,
      different, ↓reduceIte, forward, decide_eq_true_eq]
    omega
  · simp only [firstCurrent, Nat.ne_of_gt oldValid.1, Nat.ne_of_gt newValid.1,
      Ne.symm different, ↓reduceIte, backward, decide_eq_false_iff_not]
    omega

namespace Controls

def word32 : Space := ⟨4294967295, by decide⟩

theorem wrap_selects_one : firstCurrent word32 1 4294967295 = true := by decide +kernel

theorem ordinary_comparison_rolls_back :
    decide (4294967295 ≤ (1 : Nat)) = false ∧
    firstCurrent word32 1 4294967295 = true := by decide +kernel

theorem wrap_never_produces_absent : next word32 4294967295 = 1 := by decide +kernel

def seven : Space := ⟨7, by decide⟩

theorem even_cycle_requires_strict_window :
    firstCurrent ⟨6, by decide⟩ 1 4 = true ∧
    firstCurrent ⟨6, by decide⟩ 4 1 = true := by decide +kernel

/-- A bounded-window serial relation must not be advertised as a global order. -/
theorem unrestricted_history_has_cycle :
    firstCurrent seven 3 1 = true ∧ firstCurrent seven 5 3 = true ∧
    firstCurrent seven 1 5 = true := by decide

end Controls

end Mettapedia.Machines.Storage.SerialNumbers

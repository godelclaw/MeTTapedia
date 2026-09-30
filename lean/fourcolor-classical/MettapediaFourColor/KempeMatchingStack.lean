import MettapediaFourColor.KempeMatchingSyntax
import Mettapedia.GraphTheory.NoncrossingMatchingStack
import Mathlib.Data.List.FinRange

/-!
# A uniform matching codec from the literal stack law

An arbitrary finite prefix closed under a noncrossing involution has a
well-bracketed chromogram. Its answers retain the same paired endpoints.
The proof follows the exact stack transitions, without a width-specific
enumeration of matchings or colours.
-/

namespace FourColor.KempeMatchingChromogram.Stack

open Mettapedia.GraphTheory.NoncrossingMatchingStack
open Color

def read {α : Type*} (f : ℕ → α) (start count : ℕ) : List α :=
  (List.range' start count).map f

@[simp] theorem read_zero {α : Type*} (f : ℕ → α) (i : ℕ) : read f i 0 = [] := rfl

theorem read_succ {α : Type*} (f : ℕ → α) (i k : ℕ) :
    read f i (k + 1) = f i :: read f (i + 1) k := rfl

theorem read_ofFn {α : Type*} (f : ℕ → α) (n : ℕ) :
    read f 0 n = List.ofFn (fun i : Fin n => f i.val) := by
  apply List.ext_getElem
  · simp [read]
  · intro i hi hi'
    simp [read]

def word (mate : ℕ → ℕ) (bits : ℕ → Bool) (i : ℕ) : Color :=
  if mate i = i then .c1 else if bits i then .c3 else .c2

def symbol (mate : ℕ → ℕ) (c : ℕ → Color) (i : ℕ) : GramSymbol :=
  if mate i = i then .skip else if i < mate i then .push
    else if c i = c (mate i) then .pop0 else .pop1

def slot (mate : ℕ → ℕ) (i : ℕ) : Slot :=
  if mate i = i then .fixed else if i < mate i then .opening else .closing

variable {mate : ℕ → ℕ} (hinv : Function.Involutive mate) (hnc : Noncrossing mate)
include hinv hnc

/-- One physical pair opening/closing is one exact reference parser step. -/
theorem matchStep_eq (bits : ℕ → Bool) (i : ℕ) :
    matchStep (word mate bits i) (symbol mate (word mate bits) i)
        ((stack mate i).map bits) =
      some ((stack mate (i + 1)).map bits) := by
  rcases lt_trichotomy (mate i) i with hi | hi | hi
  · have hf : mate i ≠ i := ne_of_lt hi
    have hf' : mate (mate i) ≠ mate i := by rw [hinv]; omega
    rw [stack_close hinv hnc i hi, List.map_cons]
    cases hbi : bits i <;> cases hbm : bits (mate i) <;>
      simp [word, symbol, hf, hf', show ¬ i < mate i by omega, hbi, hbm, matchStep]
  · rw [stack_fixed hinv i hi]
    simp [word, symbol, hi, matchStep]
  · have hf : mate i ≠ i := Ne.symm (ne_of_lt hi)
    rw [stack_open hinv i hi, List.map_cons]
    cases hb : bits i <;> simp [word, symbol, hf, hi, hb, matchStep]

/-- Parser execution at an arbitrary scan interval follows the same stack. -/
theorem matchg_read (bits : ℕ → Bool) (i k : ℕ) :
    matchg ((stack mate i).map bits) (read (word mate bits) i k)
        (read (symbol mate (word mate bits)) i k) =
      ((stack mate (i + k)).map bits).isEmpty := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    rw [read_succ, read_succ, matchg_cons, matchStep_eq hinv hnc]
    simp only [Option.elim_some]
    rw [ih]
    congr 3
    omega

/-- Every successful paired-mask parse assigns the same bit at both ends
of each chord that closes in the scanned interval. -/
theorem paired_read (bits : ℕ → Bool) (i k : ℕ)
    (h : paired ((stack mate i).map bits) (read bits i k) (read (slot mate) i k)) :
    ∀ j, i ≤ j → j < i + k → mate j < j → bits j = bits (mate j) := by
  induction k generalizing i with
  | zero => intro j hj hj'; omega
  | succ k ih =>
    rw [read_succ, read_succ] at h
    have step :
        paired ((stack mate (i + 1)).map bits) (read bits (i + 1) k)
            (read (slot mate) (i + 1) k) ∧
        (mate i < i → bits i = bits (mate i)) := by
      rcases lt_trichotomy (mate i) i with hi | hi | hi
      · have hf : mate i ≠ i := ne_of_lt hi
        rw [stack_close hinv hnc i hi, List.map_cons] at h
        simp only [slot, ite_eq_right hf, ite_eq_right (show ¬ i < mate i by omega),
          paired, Bool.and_eq_true, beq_iff_eq] at h
        exact ⟨h.2, fun _ => h.1.symm⟩
      · simp only [slot, ite_eq_left hi, paired, Bool.and_eq_true] at h
        exact ⟨by simpa only [stack_fixed hinv i hi] using h.2, by omega⟩
      · have hf : mate i ≠ i := Ne.symm (ne_of_lt hi)
        simp only [slot, ite_eq_right hf, ite_eq_left hi, paired] at h
        exact ⟨by simpa only [stack_open hinv i hi, List.map_cons] using h, by omega⟩
    intro j hj hj' hclose
    by_cases he : j = i
    · subst j
      exact step.2 hclose
    · exact ih (i + 1) step.1 j (by omega) (by omega) hclose

/-- A complete finite prefix closed under the involution has no residual
stack, and the generated word is accepted. -/
theorem accepted (bits : ℕ → Bool) (n : ℕ) (hbound : ∀ j < n, mate j < n) :
    matchg [] (read (word mate bits) 0 n) (read (symbol mate (word mate bits)) 0 n) := by
  have h := matchg_read hinv hnc bits 0 n
  simpa only [stack_zero, List.map_nil, Nat.zero_add, stack_end mate n hbound,
    List.isEmpty_nil] using h

/-- An accepted boundary mask is constant on complete original pairs. -/
theorem mask_constant (bits : ℕ → Bool) (n : ℕ) (hbound : ∀ j < n, mate j < n)
    (h : paired [] (read bits 0 n) (read (slot mate) 0 n)) :
    ∀ j < n, bits j = bits (mate j) := by
  have hp := paired_read hinv hnc bits 0 n (by simpa using h)
  intro j hj
  rcases lt_trichotomy (mate j) j with he | he | he
  · exact hp j (by omega) (by omega) he
  · rw [he]
  · have hh := hp (mate j) (by omega) (by simpa using hbound j hj)
      (by simpa only [hinv j] using he)
    simpa only [hinv j] using hh.symm

end FourColor.KempeMatchingChromogram.Stack

import Mettapedia.Logic.HostingStyles.StoredPrograms.Firing

/-!
# Names in a finite alphabet

With a name written as one constant, a table would need a rule for every two
names to tell them apart.  Here a name is written with five constants: the
cells of its characters, each character the binary digits of its code, least
digit first (`letterSpelling`).

* `digits width value` are the binary digits of a number below `2 ^ width`;
  they determine the number (`undigits_digits`).
* `letterOf character` are the digits of the code of a character, and
  `lettersOf name` the letters of a name; both identify nothing
  (`letterOf_injective`, `lettersOf_injective`).
* `digitsTerm` writes digits with the constants `nought`, `one` and `end`.

So `letterSpelling` identifies no two names (`letterSpelling_injective`), and
what it writes is passive.  Positive: the name `ab` is two cells
(`letterSpelling_example`).  Negative: `a` and `b` are written apart.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.StoredPrograms

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef

/-- **The binary digits of a number**, least first and without a leading
zero, at most `width` of them. -/
def digits : Nat → Nat → List Bool
  | 0, _ => []
  | width + 1, value =>
      if value = 0 then [] else decide (value % 2 = 1) :: digits width (value / 2)

/-- The number that binary digits write. -/
def undigits : List Bool → Nat
  | [] => 0
  | digit :: rest => (if digit then 1 else 0) + 2 * undigits rest

/-- **The digits of a number below `2 ^ width` determine it.** -/
theorem undigits_digits : ∀ (width value : Nat), value < 2 ^ width →
    undigits (digits width value) = value
  | 0, value, small => by
      have isZero : value = 0 := by simpa using small
      simp [digits, undigits, isZero]
  | width + 1, value, small => by
      by_cases isZero : value = 0
      · simp [digits, undigits, isZero]
      · have half : value / 2 < 2 ^ width := by
          rw [Nat.pow_succ] at small
          omega
        simp only [digits, isZero, if_false, undigits, undigits_digits width (value / 2) half]
        rcases Nat.mod_two_eq_zero_or_one value with even | odd
        · simp [even]; omega
        · simp [odd]; omega

/-- **The letter of a character**: the binary digits of its code. -/
def letterOf (character : Char) : List Bool := digits 32 character.toNat

theorem letterOf_injective : Function.Injective letterOf := by
  intro first second same
  have codes : first.toNat = second.toNat := by
    have decoded := congrArg undigits same
    rwa [letterOf, letterOf, undigits_digits 32 first.toNat (UInt32.toNat_lt first.val),
      undigits_digits 32 second.toNat (UInt32.toNat_lt second.val)] at decoded
  exact Char.ext (UInt32.toNat_inj.mp codes)

/-- **The letters of a name.** -/
def lettersOf (name : String) : List (List Bool) := name.toList.map letterOf

theorem lettersOf_injective : Function.Injective lettersOf := fun _ _ same =>
  String.ext (List.map_injective_iff.mpr letterOf_injective same)

/-- **Binary digits as a term**: `nought` and `one` applied to the rest, and
`end`. -/
def digitsTerm : List Bool → LF.Term
  | [] => .con "end"
  | true :: rest => .app (.con "one") (digitsTerm rest)
  | false :: rest => .app (.con "nought") (digitsTerm rest)

theorem digitsTerm_injective : ∀ {first second : List Bool},
    digitsTerm first = digitsTerm second → first = second
  | [], [], _ => rfl
  | [], true :: _, same => by simp [digitsTerm] at same
  | [], false :: _, same => by simp [digitsTerm] at same
  | true :: _, [], same => by simp [digitsTerm] at same
  | false :: _, [], same => by simp [digitsTerm] at same
  | true :: _, false :: _, same => by simp [digitsTerm] at same
  | false :: _, true :: _, same => by simp [digitsTerm] at same
  | true :: _, true :: _, same => by
      simp only [digitsTerm, LF.Term.app.injEq, true_and] at same
      rw [digitsTerm_injective same]
  | false :: _, false :: _, same => by
      simp only [digitsTerm, LF.Term.app.injEq, true_and] at same
      rw [digitsTerm_injective same]

theorem passive_digitsTerm : ∀ letter : List Bool, passive (digitsTerm letter) = true
  | [] => rfl
  | true :: rest => by simp [digitsTerm, passive, opensRedex, passive_digitsTerm rest]
  | false :: rest => by simp [digitsTerm, passive, opensRedex, passive_digitsTerm rest]

/-- The cells of the letters of a name. -/
def lettersTerm (letters : List (List Bool)) : LF.Term := cells (letters.map digitsTerm)

theorem lettersTerm_injective : Function.Injective lettersTerm := fun _ _ same =>
  List.map_injective_iff.mpr (fun _ _ equal => digitsTerm_injective equal) (cells_injective same)

/-- **A name written in a finite alphabet**: the cells of its letters. -/
def letterSpelling : Spelling where
  write := fun name => lettersTerm (lettersOf name)
  quiet := fun name => passive_cells fun item member => by
    obtain ⟨letter, -, rfl⟩ := List.mem_map.mp member
    exact passive_digitsTerm letter

/-- **It identifies no two names.** -/
theorem letterSpelling_injective : Function.Injective letterSpelling.write :=
  fun _ _ same => lettersOf_injective (lettersTerm_injective same)

/-- **Positive**: the name `ab` is the cells of two letters, of seven digits
each. -/
theorem letterSpelling_example :
    letterSpelling.write "ab" =
      cells [digitsTerm [true, false, false, false, false, true, true],
        digitsTerm [false, true, false, false, false, true, true]] := by
  decide +kernel

/-- **Negative**: `a` and `b` are written apart. -/
theorem letterSpelling_a_ne_b : letterSpelling.write "a" ≠ letterSpelling.write "b" := by
  decide +kernel

#print axioms undigits_digits
#print axioms letterOf_injective
#print axioms lettersOf_injective
#print axioms letterSpelling_injective
#print axioms letterSpelling_example

end Mettapedia.Logic.HostingStyles.StoredPrograms

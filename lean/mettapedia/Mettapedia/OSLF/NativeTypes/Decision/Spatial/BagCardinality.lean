import Mettapedia.OSLF.NativeTypes.Decision.Spatial.BagModel

/-!
# Cardinality as a shared spatial formula

At least n elements means that the bag can supply n nonempty parts. Exact
cardinality additionally excludes n+1 such parts. This uses only the existing
empty-bag leaf, negation, conjunction and separation; it adds no primitive
cardinality test or decision procedure. Payload identity and order are
separate observations.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Decision.Spatial.BagModel

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Decision.Reference

def nonempty : Core.Formula Leaf := .neg (.atom .emp)

def atLeastSize : Nat → Core.Formula Leaf
  | 0 => .top
  | count + 1 => .separating 0 nonempty (atLeastSize count)

def sizeExactly (count : Nat) : Core.Formula Leaf :=
  .conj (atLeastSize count) (.neg (atLeastSize (count + 1)))

theorem nonempty_iff (items : List Pattern) : holds nonempty items ↔ items ≠ [] := by
  simp [holds, nonempty, Core.denotation, Core.complement, tests, Core.Test.ofBoolean, predicate]

theorem atLeastSize_iff (count : Nat) (items : List Pattern) :
    holds (atLeastSize count) items ↔ count ≤ items.length := by
  induction count generalizing items with
  | zero => simp [holds, atLeastSize, Core.denotation]
  | succ count ih =>
      change (∃ left right : List Pattern, (0 = 0 ∧ (left ++ right).Perm items) ∧
        holds nonempty left ∧ holds (atLeastSize count) right) ↔ _
      constructor
      · rintro ⟨left, right, ⟨_, partition⟩, first, rest⟩
        have lengths := partition.length_eq
        have positive : 0 < left.length := List.length_pos_iff.mpr ((nonempty_iff left).mp first)
        have bound := (ih right).mp rest
        simp only [List.length_append] at lengths
        omega
      · intro bound
        cases items with
        | nil => simp at bound
        | cons first rest =>
            exact ⟨[first], rest, ⟨rfl, List.Perm.refl _⟩,
              (nonempty_iff _).mpr (by simp), (ih rest).mpr (by simpa using bound)⟩

theorem sizeExactly_iff (count : Nat) (items : List Pattern) :
    holds (sizeExactly count) items ↔ items.length = count := by
  change (holds (atLeastSize count) items ∧ ¬ holds (atLeastSize (count + 1)) items) ↔ _
  rw [atLeastSize_iff, atLeastSize_iff]
  omega

theorem sizeExactly_permutation (count : Nat) (first second : List Pattern)
    (same : first.Perm second) :
    holds (sizeExactly count) first ↔ holds (sizeExactly count) second := by
  rw [sizeExactly_iff, sizeExactly_iff, same.length_eq]

end Mettapedia.OSLF.NativeTypes.Decision.Spatial.BagModel

import Mettapedia.GraphTheory.FourColor.SimpleGraphRotationSystem

/-!
# Removing points from a finite permutation

Deleting an edge from a rotation system removes one dart from each of two
vertex-rotation cycles.  This file records the generic permutation surgery:
splice the predecessor of a removed point directly to its successor, leaving
the removed point fixed.  Restriction to the complement then gives the cyclic
order on the remaining darts.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24PermutationPointDeletion

variable {A B : Type*} [DecidableEq A]

/-- Remove `point` from the moving part of a permutation, leaving it fixed.
The predecessor of `point` is sent to the old successor of `point`. -/
def erasePoint (perm : Equiv.Perm A) (point : A) : Equiv.Perm A :=
  perm * Equiv.swap point (perm.symm point)

@[simp]
theorem erasePoint_point (perm : Equiv.Perm A) (point : A) :
    erasePoint perm point point = point := by
  simp [erasePoint]

/-- Away from both the removed point and its old predecessor, point deletion
does not change the permutation. -/
theorem erasePoint_apply_of_ne_of_apply_ne
    (perm : Equiv.Perm A) (point value : A)
    (hvalue : value ≠ point) (himage : perm value ≠ point) :
    erasePoint perm point value = perm value := by
  rw [erasePoint, Equiv.Perm.mul_apply]
  apply congrArg perm
  apply Equiv.swap_apply_of_ne_of_ne hvalue
  intro hpredecessor
  apply himage
  have := congrArg perm hpredecessor
  simpa using this

/-- Deleting a point preserves every fiber already preserved by the original
permutation. -/
theorem erasePoint_preserves
    (perm : Equiv.Perm A) (point : A) (fiber : A → B)
    (hperm : ∀ value, fiber (perm value) = fiber value) :
    ∀ value, fiber (erasePoint perm point value) = fiber value := by
  intro value
  by_cases hpoint : value = point
  · subst value
    simp
  by_cases hpredecessor : value = perm.symm point
  · subst value
    rw [erasePoint, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
    calc
      fiber (perm point) = fiber point := hperm point
      _ = fiber (perm (perm.symm point)) := by simp
      _ = fiber (perm.symm point) := hperm (perm.symm point)
  · rw [erasePoint, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne hpoint hpredecessor]
    exact hperm value

/-- Removing two distinct points fixes both of them. -/
def eraseTwoPoints (perm : Equiv.Perm A) (first second : A) : Equiv.Perm A :=
  erasePoint (erasePoint perm first) second

@[simp]
theorem eraseTwoPoints_second (perm : Equiv.Perm A) (first second : A) :
    eraseTwoPoints perm first second second = second := by
  simp [eraseTwoPoints]

@[simp]
theorem eraseTwoPoints_first (perm : Equiv.Perm A) {first second : A}
    (hne : first ≠ second) :
    eraseTwoPoints perm first second first = first := by
  rw [eraseTwoPoints]
  calc
    erasePoint (erasePoint perm first) second first =
        erasePoint perm first first :=
      erasePoint_apply_of_ne_of_apply_ne
        (erasePoint perm first) second first hne (by simpa using hne)
    _ = first := erasePoint_point perm first

/-- Two point deletions retain any fiber invariant of the old permutation. -/
theorem eraseTwoPoints_preserves
    (perm : Equiv.Perm A) (first second : A) (fiber : A → B)
    (hperm : ∀ value, fiber (perm value) = fiber value) :
    ∀ value, fiber (eraseTwoPoints perm first second value) = fiber value := by
  apply erasePoint_preserves
  exact erasePoint_preserves perm first fiber hperm

/-- Away from both removed points, and provided the old image also avoids
them, deleting two points leaves the permutation value unchanged. -/
theorem eraseTwoPoints_apply_of_ne_of_image_ne
    (perm : Equiv.Perm A) (first second value : A)
    (hvalueFirst : value ≠ first) (hvalueSecond : value ≠ second)
    (himageFirst : perm value ≠ first) (himageSecond : perm value ≠ second) :
    eraseTwoPoints perm first second value = perm value := by
  have hfirst : erasePoint perm first value = perm value :=
    erasePoint_apply_of_ne_of_apply_ne perm first value
      hvalueFirst himageFirst
  calc
    eraseTwoPoints perm first second value = erasePoint perm first value :=
      erasePoint_apply_of_ne_of_apply_ne (erasePoint perm first) second value
        hvalueSecond (by simpa only [hfirst] using himageSecond)
    _ = perm value := hfirst

/-- The complement of two distinct fixed points is invariant under the
twice-erased permutation. -/
theorem eraseTwoPoints_complement_invariant
    (perm : Equiv.Perm A) {first second : A} (hne : first ≠ second) :
    ∀ value,
      (eraseTwoPoints perm first second value ≠ first ∧
          eraseTwoPoints perm first second value ≠ second) ↔
        value ≠ first ∧ value ≠ second := by
  intro value
  have hfirst : eraseTwoPoints perm first second first = first :=
    eraseTwoPoints_first perm hne
  have hsecond : eraseTwoPoints perm first second second = second := by simp
  constructor
  · rintro ⟨hnotFirst, hnotSecond⟩
    constructor
    · intro hvalue
      subst value
      exact hnotFirst hfirst
    · intro hvalue
      subst value
      exact hnotSecond hsecond
  · rintro ⟨hnotFirst, hnotSecond⟩
    constructor
    · intro himage
      have : value = first :=
        (eraseTwoPoints perm first second).injective (himage.trans hfirst.symm)
      exact hnotFirst this
    · intro himage
      have : value = second :=
        (eraseTwoPoints perm first second).injective (himage.trans hsecond.symm)
      exact hnotSecond this

/-- The cyclic permutation induced on the complement of two removed points. -/
def eraseTwoPointsSubtype
    (perm : Equiv.Perm A) {first second : A} (hne : first ≠ second) :
    Equiv.Perm { value : A // value ≠ first ∧ value ≠ second } :=
  (eraseTwoPoints perm first second).subtypePerm
    (eraseTwoPoints_complement_invariant perm hne)

@[simp]
theorem eraseTwoPointsSubtype_val
    (perm : Equiv.Perm A) {first second : A} (hne : first ≠ second)
    (value : { value : A // value ≠ first ∧ value ≠ second }) :
    (eraseTwoPointsSubtype perm hne value).1 =
      eraseTwoPoints perm first second value.1 :=
  rfl

/-- On the complement subtype, a point whose old image also remains in the
complement is acted on exactly as before deletion. -/
theorem eraseTwoPointsSubtype_apply_of_image_ne
    (perm : Equiv.Perm A) {first second : A} (hne : first ≠ second)
    (value : { value : A // value ≠ first ∧ value ≠ second })
    (himageFirst : perm value.1 ≠ first)
    (himageSecond : perm value.1 ≠ second) :
    (eraseTwoPointsSubtype perm hne value).1 = perm value.1 := by
  rw [eraseTwoPointsSubtype_val]
  exact eraseTwoPoints_apply_of_ne_of_image_ne perm first second value.1
    value.2.1 value.2.2 himageFirst himageSecond

end GoertzelV24PermutationPointDeletion

end Mettapedia.GraphTheory.FourColor

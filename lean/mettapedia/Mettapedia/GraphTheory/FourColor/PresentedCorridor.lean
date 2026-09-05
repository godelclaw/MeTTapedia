import Mettapedia.GraphTheory.FourColor.PresentedEnumCorrect

/-!
# From a presented shape's kernel table to the corridor theorem's hypothesis

For a valid presentation `P` with `tab = (List.range (3^k)).map P.enumMask`, the
image of a word set under the shape's relation is the mask step on the
corresponding bitmask (`relImage_wordSet`), so a kernel check that `m+1`
steps equal `m` steps from every singleton (`stabilizesAt`) yields the abstract
stabilisation hypothesis of `GeneralTubeChain` (`hstab_of_stabilizesAt`).
Any presented shape then plugs into `TubeOf.le_of_tubeOf` once its
`SlabShape` is checked.
-/

namespace Mettapedia.GraphTheory.FourColor
namespace TubeSlab
namespace Presented
namespace Pres

open TubeRingOrbit ZigzagRing

variable {V N k : Nat} [NeZero k] (P : Pres V N k) (hP : P.Valid)

/-- the stabilisation check at index `m` over the first `n` singletons -/
def stabilizesAt (m n : Nat) (tab : List Nat) : Bool :=
  (List.range n).all fun w => iterSet tab (m + 1) (1 <<< w) == iterSet tab m (1 <<< w)

/-- the words of a bitmask -/
def wordSet (S : Nat) : Set (Fin k → Color) :=
  {w | ∃ X, X < 3 ^ k ∧ S.testBit X = true ∧ w = wordOf k X}

theorem wordSet_singleton {X : Nat} (hX : X < 3 ^ k) :
    wordSet (k := k) (1 <<< X) = {wordOf k X} := by
  ext w
  simp only [wordSet, Set.mem_setOf_eq, Set.mem_singleton_iff, Nat.one_shiftLeft,
    Nat.testBit_two_pow]
  constructor
  · rintro ⟨X', -, h, rfl⟩
    rw [decide_eq_true_iff] at h
    rw [h]
  · rintro rfl
    exact ⟨X, hX, by simp, rfl⟩

theorem ne_zero_of_accepts {x y : Fin k → Color} (h : (P.toTangle hP).AcceptsBoundaryWords x y) :
    (∀ i, x i ≠ 0) ∧ ∀ i, y i ≠ 0 := by
  obtain ⟨c, hV⟩ := (P.accepts_iff hP x y).mp h
  exact ⟨hV.x_ne_zero, hV.y_ne_zero⟩

/-- the enumerator's table -/
def table : List Nat := (List.range (3 ^ k)).map P.enumMask

/-- one slab on word sets is one mask step -/
theorem relImage_wordSet (S : Nat) :
    relImage (P.toTangle hP) (wordSet S) = wordSet (stepSet S P.table 0) := by
  ext w'
  simp only [relImage, wordSet, Set.mem_setOf_eq, table]
  constructor
  · rintro ⟨w, ⟨X, hX, hS, rfl⟩, hacc⟩
    have hy := (P.ne_zero_of_accepts hP hacc).2
    refine ⟨encW k w', encW_lt k w', ?_, (wordOf_encW k w' hy).symm⟩
    rw [testBit_stepSet]
    refine ⟨X, hX, by simpa using hS, ?_⟩
    rw [P.enumMask_testBit_iff hP X _ (encW_lt k w'), ← P.accepts_iff hP, wordOf_encW k w' hy]
    exact hacc
  · rintro ⟨Y, hY, hb, rfl⟩
    rw [testBit_stepSet] at hb
    obtain ⟨X, hX, hS, hbit⟩ := hb
    exact ⟨wordOf k X, ⟨X, hX, by simpa using hS, rfl⟩,
      (P.accepts_iff hP _ _).mpr ((P.enumMask_testBit_iff hP X Y hY).mp hbit)⟩

theorem relImage_iterate_wordSet (S : Nat) :
    ∀ n, (relImage (P.toTangle hP))^[n] (wordSet S) = wordSet (iterSet P.table n S)
  | 0 => rfl
  | n + 1 => by
    simp only [iterSet]
    rw [Function.iterate_succ_apply, P.relImage_wordSet hP, relImage_iterate_wordSet _ n]

theorem relImage_iUnion {ι : Type} (W : ι → Set (Fin k → Color)) :
    relImage (P.toTangle hP) (⋃ i, W i) = ⋃ i, relImage (P.toTangle hP) (W i) := by
  ext w'
  simp only [relImage, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨w, ⟨i, hi⟩, h⟩; exact ⟨i, w, hi, h⟩
  · rintro ⟨i, w, hi, h⟩; exact ⟨w, ⟨i, hi⟩, h⟩

theorem relImage_iterate_iUnion {ι : Type} (W : ι → Set (Fin k → Color)) :
    ∀ n, (relImage (P.toTangle hP))^[n] (⋃ i, W i) = ⋃ i, (relImage (P.toTangle hP))^[n] (W i)
  | 0 => rfl
  | n + 1 => by
    rw [Function.iterate_succ_apply, P.relImage_iUnion hP]
    exact relImage_iterate_iUnion (fun i => relImage (P.toTangle hP) (W i)) n

theorem relImage_singleton_zero {w : Fin k → Color} (hw : ¬ ∀ i, w i ≠ 0) :
    relImage (P.toTangle hP) {w} = ∅ := by
  ext w'
  simp only [relImage, Set.mem_singleton_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false,
    iff_false, not_exists, not_and]
  rintro _ rfl h
  exact hw (P.ne_zero_of_accepts hP h).1

theorem relImage_empty : relImage (P.toTangle hP) ∅ = ∅ := by
  ext; simp [relImage]

theorem relImage_iterate_empty : ∀ n, (relImage (P.toTangle hP))^[n] ∅ = ∅
  | 0 => rfl
  | n + 1 => by
    rw [Function.iterate_succ_apply, P.relImage_empty hP]
    exact relImage_iterate_empty n

theorem iterSet_stable_of_stabilizesAt {m : Nat} {tab : List Nat}
    (h : stabilizesAt m (3 ^ k) tab = true) {X : Nat} (hX : X < 3 ^ k) :
    iterSet tab (m + 1) (1 <<< X) = iterSet tab m (1 <<< X) := by
  unfold stabilizesAt at h
  rw [List.all_eq_true] at h
  have := h X (List.mem_range.mpr hX)
  rwa [beq_iff_eq] at this

/-- **the abstract stabilisation hypothesis from the kernel check** -/
theorem hstab_of_stabilizesAt {m : Nat} (h : stabilizesAt m (3 ^ k) P.table = true)
    (hm : 0 < m) (W : Set (Fin k → Color)) :
    (relImage (P.toTangle hP))^[m + 1] W = (relImage (P.toTangle hP))^[m] W := by
  have hW : W = ⋃ w : W, ({(w : Fin k → Color)} : Set (Fin k → Color)) := by ext; simp
  rw [hW, P.relImage_iterate_iUnion hP, P.relImage_iterate_iUnion hP]
  congr 1
  funext w
  by_cases hw : ∀ i, (w : Fin k → Color) i ≠ 0
  · have hs : ({(w : Fin k → Color)} : Set (Fin k → Color)) = wordSet (1 <<< encW k w) := by
      rw [wordSet_singleton (encW_lt k w), wordOf_encW k w hw]
    rw [hs, P.relImage_iterate_wordSet hP, P.relImage_iterate_wordSet hP,
      iterSet_stable_of_stabilizesAt h (encW_lt k w)]
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have h1 : (relImage (P.toTangle hP))^[m' + 1 + 1] {(w : Fin k → Color)} = ∅ := by
      rw [Function.iterate_succ_apply, P.relImage_singleton_zero hP hw, P.relImage_iterate_empty hP]
    have h2 : (relImage (P.toTangle hP))^[m' + 1] {(w : Fin k → Color)} = ∅ := by
      rw [Function.iterate_succ_apply, P.relImage_singleton_zero hP hw, P.relImage_iterate_empty hP]
    rw [h1, h2]

end Pres
end Presented
end TubeSlab
end Mettapedia.GraphTheory.FourColor

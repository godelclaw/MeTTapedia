import Mettapedia.GraphTheory.FourColor.ZigzagRingTable

/-!
# Tait types along a zigzag tube stabilise, for any inner side

A two-sided tangle with left boundary `L` and right boundary `Fin k` is
extended by one zigzag ring through serial composition (`appendRing`).  For a
fixed left word `l`, its right support — the set of numerals `Y < 3^k` whose
colour word it accepts on the right — is pushed through the ring relation
(`rightSet_appendRing`).  The kernel-checked stabilisation of that relation
(`TubeRingOrbit.zigzag5_stabilizes`, `zigzag6_stabilizes`) then gives, for
every tangle and every left word, that `k` rings and `k-1` rings have the same
right support: `rightSet_iterate_stabilizes_five`, `…_six`.

Carriers grow under composition; `HiddenTangle` hides them.
-/

namespace Mettapedia.GraphTheory.FourColor
namespace ZigzagRing

open GoertzelV24OpenTangleComposition
open TubeRingOrbit

/-- a two-sided tangle with hidden carriers and fixed boundary types -/
structure HiddenTangle (L R : Type) : Type 1 where
  V : Type
  I : Type
  data : TwoSidedOpenTangleData V I L R

namespace HiddenTangle

variable {L R : Type}

def Accepts (T : HiddenTangle L R) (l : L → Color) (r : R → Color) : Prop :=
  T.data.AcceptsBoundaryWords l r

/-- accepted right words are nonzero everywhere -/
theorem ne_zero_of_accepts (T : HiddenTangle L R) {l : L → Color} {r : R → Color}
    (h : T.Accepts l r) (i : R) : r i ≠ 0 := by
  obtain ⟨coloring, ⟨-, -, hnz⟩, -, hr⟩ := h
  rw [← hr]
  exact hnz _

variable (k : Nat) [NeZero k]

/-- extend by one zigzag ring on the right -/
noncomputable def appendRing (T : HiddenTangle L (Fin k)) : HiddenTangle L (Fin k) where
  V := T.V ⊕ Vtx k
  I := (T.I ⊕ Dart k) ⊕ (Fin k ⊕ Fin k)
  data := TwoSidedOpenTangleData.serialCompose T.data (ring k) (Equiv.refl _)

theorem appendRing_accepts_iff (T : HiddenTangle L (Fin k)) (l : L → Color) (y : Fin k → Color) :
    (appendRing k T).Accepts l y ↔ ∃ x, T.Accepts l x ∧ (ring k).AcceptsBoundaryWords x y := by
  unfold appendRing Accepts
  simp only
  rw [TwoSidedOpenTangleData.serialCompose_acceptsBoundaryWords_iff]
  constructor
  · rintro ⟨x, hx, hy⟩
    exact ⟨x, hx, hy⟩
  · rintro ⟨x, hx, hy⟩
    exact ⟨x, hx, hy⟩

end HiddenTangle

/-! ## Numerals for words -/

variable (k : Nat) [NeZero k]

/-- the numeral of a colour word -/
def encW (x : Fin k → Color) : Nat :=
  encB 3 (fun i => if h : i < k then idx (x ⟨i, h⟩) else 0) k

theorem encW_lt (x : Fin k → Color) : encW k x < 3 ^ k :=
  encB_lt (by norm_num) k (fun i _ => by split_ifs; exact idx_lt _)

theorem wordOf_encW (x : Fin k → Color) (hx : ∀ i, x i ≠ 0) : wordOf k (encW k x) = x := by
  funext i
  simp only [wordOf, encW, digit_eq_digB]
  rw [digB_encB (by norm_num) k (fun j _ => by split_ifs; exact idx_lt _)
    i i.isLt]
  simp only [i.isLt, dite_true, Fin.eta]
  exact col_idx (hx i)

/-! ## Set-level transition -/

/-- push a set of numerals through the ring relation -/
def stepS (S : Set Nat) : Set Nat :=
  {Y | Y < 3 ^ k ∧ ∃ X, X < 3 ^ k ∧ X ∈ S ∧ (stepMask k X (2 ^ k)).testBit Y = true}

theorem stepS_iUnion {ι : Type*} (S : ι → Set Nat) : stepS k (⋃ i, S i) = ⋃ i, stepS k (S i) := by
  ext Y
  simp only [stepS, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨hY, X, hX, ⟨i, hi⟩, hb⟩; exact ⟨i, hY, X, hX, hi, hb⟩
  · rintro ⟨i, hY, X, hX, hi, hb⟩; exact ⟨hY, X, hX, ⟨i, hi⟩, hb⟩

theorem stepS_mono {S S' : Set Nat} (h : S ⊆ S') : stepS k S ⊆ stepS k S' := by
  rintro Y ⟨hY, X, hX, hXS, hb⟩; exact ⟨hY, X, hX, h hXS, hb⟩

theorem stepS_iterate_iUnion {ι : Type*} (S : ι → Set Nat) :
    ∀ n, (stepS k)^[n] (⋃ i, S i) = ⋃ i, (stepS k)^[n] (S i)
  | 0 => rfl
  | n + 1 => by
    rw [Function.iterate_succ_apply, stepS_iUnion]
    exact stepS_iterate_iUnion (fun i => stepS k (S i)) n

/-- a set of numerals below `3^k` is the union of its singletons -/
theorem eq_iUnion_singleton (S : Set Nat) : S = ⋃ X : S, {(X : Nat)} := by
  ext Y; simp

/-- the bits set by the ring relation are numerals below `3^k` -/
theorem lt_of_testBit_stepMask {X Y : Nat} (h : (stepMask k X (2 ^ k)).testBit Y = true) :
    Y < 3 ^ k := by
  rw [testBit_stepMask] at h
  obtain ⟨m, -, hm⟩ := h
  rw [outWordN_eq_some_iff] at hm
  obtain ⟨hall, rfl⟩ := hm
  exact encB_lt (by norm_num) k
    (fun j hj => yDig_lt (hall j hj) (bDig_aWord_lt (NeZero.pos k) X m j))

/-! ## The right support of a tangle -/

/-- numerals of the right words accepted at left word `l` -/
def rightSet (T : HiddenTangle L (Fin k)) (l : L → Color) : Set Nat :=
  {Y | Y < 3 ^ k ∧ T.Accepts l (wordOf k Y)}

theorem rightSet_appendRing (T : HiddenTangle L (Fin k)) (l : L → Color) :
    rightSet k (HiddenTangle.appendRing k T) l = stepS k (rightSet k T l) := by
  ext Y
  simp only [rightSet, stepS, Set.mem_setOf_eq, HiddenTangle.appendRing_accepts_iff]
  constructor
  · rintro ⟨hY, x, hx, hring⟩
    have hx0 := T.ne_zero_of_accepts hx
    refine ⟨hY, encW k x, encW_lt k x, ⟨encW_lt k x, ?_⟩, ?_⟩
    · rw [wordOf_encW k x hx0]; exact hx
    · rw [← accepts_iff_testBit k _ _ hY, wordOf_encW k x hx0]; exact hring
  · rintro ⟨hY, X, hX, ⟨-, hacc⟩, hb⟩
    exact ⟨hY, wordOf k X, hacc, (accepts_iff_testBit k X Y hY).mpr hb⟩

theorem rightSet_iterate (T : HiddenTangle L (Fin k)) (l : L → Color) :
    ∀ n, rightSet k ((HiddenTangle.appendRing k)^[n] T) l = (stepS k)^[n] (rightSet k T l)
  | 0 => rfl
  | n + 1 => by
    rw [Function.iterate_succ_apply', rightSet_appendRing, rightSet_iterate T l n,
      Function.iterate_succ_apply']

/-! ## From the kernel check to sets -/

/-- the set of a bitmask -/
def maskSet (S : Nat) : Set Nat := {X | S.testBit X = true}

theorem mem_maskSet {S X : Nat} : X ∈ maskSet S ↔ S.testBit X = true := Iff.rfl

theorem testBit_stepSet (S : Nat) :
    ∀ (n : Nat) (f : Nat → Nat) (w Y : Nat),
      (stepSet S ((List.range n).map f) w).testBit Y = true ↔
        ∃ j, j < n ∧ S.testBit (w + j) = true ∧ (f j).testBit Y = true := by
  intro n
  induction n with
  | zero => intro f w Y; simp [stepSet]
  | succ n ih =>
    intro f w Y
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [stepSet, Nat.testBit_or, Bool.or_eq_true]
    rw [show List.map (f ∘ Nat.succ) (List.range n) = (List.range n).map (fun x => f (x + 1)) from
      rfl, ih (fun x => f (x + 1)) (w + 1) Y]
    have hbit : ((S >>> w) % 2 = 1) ↔ S.testBit w = true := by
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow, decide_eq_true_iff]
    constructor
    · rintro (h | ⟨j, hj, hS, hf⟩)
      · refine ⟨0, by omega, ?_, ?_⟩
        · split_ifs at h with hb
          · simpa using hbit.mp hb
          · simp at h
        · split_ifs at h with hb
          · simpa using h
          · simp at h
      · exact ⟨j + 1, by omega, by simpa [Nat.add_assoc, Nat.add_comm 1 j] using hS, hf⟩
    · rintro ⟨j, hj, hS, hf⟩
      rcases j with _ | j
      · left
        rw [if_pos (hbit.mpr (by simpa using hS))]
        simpa using hf
      · right
        exact ⟨j, by omega, by simpa [Nat.add_assoc, Nat.add_comm 1 j] using hS, hf⟩

theorem maskSet_stepSet (S : Nat) :
    maskSet (stepSet S (computedTable k) 0) = stepS k (maskSet S) := by
  ext Y
  simp only [maskSet, computedTable, Set.mem_setOf_eq, stepS]
  rw [testBit_stepSet]
  constructor
  · rintro ⟨X, hX, hS, hb⟩
    exact ⟨lt_of_testBit_stepMask k hb, X, hX, by simpa using hS, hb⟩
  · rintro ⟨-, X, hX, hS, hb⟩
    exact ⟨X, hX, by simpa using hS, hb⟩

theorem maskSet_iterSet (S : Nat) :
    ∀ n, maskSet (iterSet (computedTable k) n S) = (stepS k)^[n] (maskSet S)
  | 0 => rfl
  | n + 1 => by
    simp only [iterSet]
    rw [maskSet_iterSet (stepSet S (computedTable k) 0) n, maskSet_stepSet,
      Function.iterate_succ_apply]

theorem maskSet_singleton (X : Nat) : maskSet (1 <<< X) = {X} := by
  ext Y
  simp [maskSet, Nat.one_shiftLeft, Nat.testBit_two_pow, eq_comm]

/-- the kernel check, read as a statement about sets -/
theorem stepS_iterate_singleton_of_stabilizes (h : stabilizes k = true) {X : Nat} (hX : X < 3 ^ k) :
    (stepS k)^[k] {X} = (stepS k)^[k - 1] {X} := by
  unfold stabilizes stabilizesWith at h
  rw [List.all_eq_true] at h
  have hX' := h X (List.mem_range.mpr hX)
  rw [beq_iff_eq] at hX'
  rw [← maskSet_singleton, ← maskSet_iterSet, ← maskSet_iterSet, hX']

/-- **Stabilisation for every set of numerals.** -/
theorem stepS_iterate_of_stabilizes (h : stabilizes k = true) (S : Set Nat) (hS : ∀ X ∈ S, X < 3 ^ k) :
    (stepS k)^[k] S = (stepS k)^[k - 1] S := by
  rw [eq_iUnion_singleton S, stepS_iterate_iUnion, stepS_iterate_iUnion]
  congr 1
  funext X
  exact stepS_iterate_singleton_of_stabilizes k h (hS X X.2)

/-- **Stabilisation for every tangle and every left word.** -/
theorem rightSet_iterate_of_stabilizes (h : stabilizes k = true)
    (T : HiddenTangle L (Fin k)) (l : L → Color) :
    rightSet k ((HiddenTangle.appendRing k)^[k] T) l =
      rightSet k ((HiddenTangle.appendRing k)^[k - 1] T) l := by
  rw [rightSet_iterate, rightSet_iterate]
  exact stepS_iterate_of_stabilizes k h _ (fun X hX => hX.1)

/-- the same, at the level of accepted words -/
theorem accepts_iterate_of_stabilizes (h : stabilizes k = true)
    (T : HiddenTangle L (Fin k)) (l : L → Color) (y : Fin k → Color) :
    ((HiddenTangle.appendRing k)^[k] T).Accepts l y ↔
      ((HiddenTangle.appendRing k)^[k - 1] T).Accepts l y := by
  by_cases hy : ∀ i, y i ≠ 0
  · have key := rightSet_iterate_of_stabilizes k h T l
    have hmem : ∀ T' : HiddenTangle L (Fin k), T'.Accepts l y ↔ encW k y ∈ rightSet k T' l := by
      intro T'
      simp only [rightSet, Set.mem_setOf_eq, wordOf_encW k y hy]
      exact ⟨fun h => ⟨encW_lt k y, h⟩, fun h => h.2⟩
    rw [hmem, hmem, key]
  · simp only [not_forall, not_not] at hy
    obtain ⟨i, hi⟩ := hy
    constructor
    · intro h; exact absurd hi (HiddenTangle.ne_zero_of_accepts _ h i)
    · intro h; exact absurd hi (HiddenTangle.ne_zero_of_accepts _ h i)

theorem rightSet_iterate_stabilizes_five (T : HiddenTangle L (Fin 5)) (l : L → Color) :
    rightSet 5 ((HiddenTangle.appendRing 5)^[5] T) l =
      rightSet 5 ((HiddenTangle.appendRing 5)^[4] T) l :=
  rightSet_iterate_of_stabilizes 5 zigzag5_stabilizes T l

theorem rightSet_iterate_stabilizes_six (T : HiddenTangle L (Fin 6)) (l : L → Color) :
    rightSet 6 ((HiddenTangle.appendRing 6)^[6] T) l =
      rightSet 6 ((HiddenTangle.appendRing 6)^[5] T) l :=
  rightSet_iterate_of_stabilizes 6 zigzag6_stabilizes T l

end ZigzagRing
end Mettapedia.GraphTheory.FourColor

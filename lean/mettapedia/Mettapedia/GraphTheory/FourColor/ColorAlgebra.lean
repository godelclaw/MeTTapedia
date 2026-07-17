import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace Mettapedia.GraphTheory.FourColor

/-- The scalar field `𝔽₂` used in the boundary-color algebra. -/
abbrev F2 := ZMod 2

@[simp] theorem f2_two_eq_zero : (2 : F2) = 0 := rfl

/-- The edge-color group `𝔽₂ × 𝔽₂` used in the Goertzel/Kauffman route. -/
abbrev Color := F2 × F2

variable {a b : Color}

/-- The standard red basis color. -/
def red : Color := (1, 0)

/-- The standard blue basis color. -/
def blue : Color := (0, 1)

/-- The standard purple basis color. -/
def purple : Color := (1, 1)

@[simp] theorem zmod2_add_self (x : F2) : x + x = 0 := by
  fin_cases x <;> decide

/-- Two binary scalars differ exactly when their sum is one. -/
theorem f2_add_eq_one_iff_ne (left right : F2) :
    left + right = 1 ↔ left ≠ right := by
  constructor
  · intro hsum heq
    subst right
    simp at hsum
  · intro hne
    fin_cases left <;> fin_cases right
    · exact (hne rfl).elim
    · exact zero_add _
    · exact add_zero _
    · exact (hne rfl).elim

@[simp] theorem color_add_self (c : Color) : c + c = 0 := by
  ext <;> simp

@[simp] theorem red_add_blue : red + blue = purple := by
  rfl

@[simp] theorem red_add_purple : red + purple = blue := by
  rfl

@[simp] theorem blue_add_purple : blue + purple = red := by
  rfl

@[simp] theorem blue_add_red : blue + red = purple := by
  simpa [add_comm] using red_add_blue

@[simp] theorem purple_add_red : purple + red = blue := by
  simpa [add_comm] using red_add_purple

@[simp] theorem purple_add_blue : purple + blue = red := by
  simp [add_comm]

@[simp] theorem red_ne_zero : red ≠ 0 := by
  decide

@[simp] theorem blue_ne_zero : blue ≠ 0 := by
  decide

@[simp] theorem purple_ne_zero : purple ≠ 0 := by
  decide

@[simp] theorem red_ne_blue : red ≠ blue := by
  decide

@[simp] theorem red_ne_purple : red ≠ purple := by
  decide

@[simp] theorem blue_ne_purple : blue ≠ purple := by
  decide

@[simp] theorem color_neg_eq (c : Color) : -c = c := by
  exact (eq_neg_of_add_eq_zero_left (color_add_self c)).symm

/-- In `𝔽₂²`, summing the same color an even number of times gives zero. -/
theorem nsmul_even_eq_zero {c : Color} {n : Nat} (h : Even n) :
    n • c = 0 := by
  rcases h with ⟨k, rfl⟩
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hnat : k.succ + k.succ = k + k + 2 := by omega
      rw [hnat, add_nsmul, ih]
      ext <;> simp [two_mul]

theorem add_eq_zero_iff_eq (a b : Color) : a + b = 0 ↔ a = b := by
  constructor
  · intro hab
    calc
      a = a + 0 := by simp
      _ = a + (b + b) := by rw [color_add_self]
      _ = (a + b) + b := by abel
      _ = 0 + b := by rw [hab]
      _ = b := by simp
  · intro hab
    simp [hab]

/-- A color in `𝔽₂ × 𝔽₂` is nonzero exactly when at least one coordinate is nonzero. -/
theorem color_ne_zero_iff_fst_or_snd_ne_zero (c : Color) :
    c ≠ 0 ↔ c.1 ≠ 0 ∨ c.2 ≠ 0 := by
  constructor
  · intro hc
    by_cases hfst : c.1 = 0
    · right
      intro hsnd
      apply hc
      ext <;> simp [hfst, hsnd]
    · exact Or.inl hfst
  · intro hcoord hzero
    rcases hcoord with hfst | hsnd
    · exact hfst (by simp [hzero])
    · exact hsnd (by simp [hzero])

theorem add_ne_zero_of_ne (hab : a ≠ b) : a + b ≠ 0 := by
  intro hzero
  exact hab ((add_eq_zero_iff_eq a b).mp hzero)

theorem add_ne_left_of_ne_zero (hb : b ≠ 0) : a + b ≠ a := by
  intro hab
  have : b = 0 := by
    calc
      b = 0 + b := by simp
      _ = (a + a) + b := by rw [color_add_self]
      _ = a + (a + b) := by abel
      _ = a + a := by rw [hab]
      _ = 0 := color_add_self a
  exact hb this

theorem add_ne_right_of_ne_zero (ha : a ≠ 0) : a + b ≠ b := by
  intro hab
  have : a = 0 := by
    calc
      a = a + 0 := by simp
      _ = a + (b + b) := by rw [color_add_self]
      _ = (a + b) + b := by abel
      _ = b + b := by rw [hab]
      _ = 0 := color_add_self b
  exact ha this

theorem third_color_properties (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    a + b ≠ 0 ∧ a + b ≠ a ∧ a + b ≠ b := by
  exact ⟨add_ne_zero_of_ne hab, add_ne_left_of_ne_zero hb, add_ne_right_of_ne_zero ha⟩

/-- The zero color-chain on an edge type. -/
def zeroChain {E : Type*} : E → Color :=
  fun _ => 0

@[simp] theorem zeroChain_apply {E : Type*} (e : E) : zeroChain e = 0 :=
  rfl

/-- The finite support of a color-chain. -/
def support {E : Type*} [Fintype E] [DecidableEq E] (x : E → Color) : Finset E :=
  Finset.univ.filter fun e => x e ≠ 0

@[simp] theorem mem_support_iff {E : Type*} [Fintype E] [DecidableEq E]
    {x : E → Color} {e : E} : e ∈ support x ↔ x e ≠ 0 := by
  simp [support]

@[simp] theorem support_zeroChain {E : Type*} [Fintype E] [DecidableEq E] :
    support (zeroChain : E → Color) = ∅ := by
  ext e
  simp [support]

theorem support_eq_empty_iff {E : Type*} [Fintype E] [DecidableEq E]
    {x : E → Color} :
    support x = ∅ ↔ ∀ e, x e = 0 := by
  constructor
  · intro h e
    by_contra hx
    have he : e ∈ support x := by
      simp [support, hx]
    rw [h] at he
    simp at he
  · intro h
    ext e
    simp [support, h e]

theorem eq_zero_of_support_eq_empty {E : Type*} [Fintype E] [DecidableEq E]
    {x : E → Color} (h : support x = ∅) (e : E) :
    x e = 0 :=
  (support_eq_empty_iff.mp h) e

/-- Support of the first `𝔽₂` coordinate of a color-chain. -/
def support₁ {E : Type*} [Fintype E] [DecidableEq E] (x : E → Color) : Finset E :=
  Finset.univ.filter fun e => (x e).1 ≠ 0

@[simp] theorem mem_support₁_iff {E : Type*} [Fintype E] [DecidableEq E]
    {x : E → Color} {e : E} : e ∈ support₁ x ↔ (x e).1 ≠ 0 := by
  simp [support₁]

@[simp] theorem support₁_zeroChain {E : Type*} [Fintype E] [DecidableEq E] :
    support₁ (zeroChain : E → Color) = ∅ := by
  ext e
  simp [support₁]

theorem support₁_eq_empty_iff {E : Type*} [Fintype E] [DecidableEq E]
    {x : E → Color} :
    support₁ x = ∅ ↔ ∀ e, (x e).1 = 0 := by
  constructor
  · intro h e
    by_contra hx
    have he : e ∈ support₁ x := by
      simp [support₁, hx]
    rw [h] at he
    simp at he
  · intro h
    ext e
    simp [support₁, h e]

/-- Support of the second `𝔽₂` coordinate of a color-chain. -/
def support₂ {E : Type*} [Fintype E] [DecidableEq E] (x : E → Color) : Finset E :=
  Finset.univ.filter fun e => (x e).2 ≠ 0

@[simp] theorem mem_support₂_iff {E : Type*} [Fintype E] [DecidableEq E]
    {x : E → Color} {e : E} : e ∈ support₂ x ↔ (x e).2 ≠ 0 := by
  simp [support₂]

@[simp] theorem support₂_zeroChain {E : Type*} [Fintype E] [DecidableEq E] :
    support₂ (zeroChain : E → Color) = ∅ := by
  ext e
  simp [support₂]

theorem support₂_eq_empty_iff {E : Type*} [Fintype E] [DecidableEq E]
    {x : E → Color} :
    support₂ x = ∅ ↔ ∀ e, (x e).2 = 0 := by
  constructor
  · intro h e
    by_contra hx
    have he : e ∈ support₂ x := by
      simp [support₂, hx]
    rw [h] at he
    simp at he
  · intro h
    ext e
    simp [support₂, h e]

namespace Color

/-- Swap two distinguished colors, leaving every other color unchanged. -/
def swap (α β x : Color) : Color :=
  if x = α then β else if x = β then α else x

@[simp] theorem swap_eq_left (α β : Color) : swap α β α = β := by
  simp [swap]

@[simp] theorem swap_eq_right (α β : Color) : swap α β β = α := by
  by_cases h : β = α
  · simp [swap, h]
  · simp [swap, h]

@[simp] theorem swap_ne (α β x : Color) (hα : x ≠ α) (hβ : x ≠ β) :
    swap α β x = x := by
  simp [swap, hα, hβ]

/-- The two-color set `{α, β}` used by a Kempe switch. -/
def twoColor (α β : Color) : Set Color :=
  {x | x = α ∨ x = β}

/-- Elementary delta for a swap: add `α + β` exactly on the two swapped colors. -/
def delta (α β x : Color) : Color :=
  if x = α ∨ x = β then α + β else 0

theorem swap_eq_add_delta (α β x : Color) :
    swap α β x = x + delta α β x := by
  unfold swap delta
  by_cases hα : x = α
  · rw [if_pos hα, if_pos (Or.inl hα), hα]
    calc
      β = 0 + β := by simp
      _ = (α + α) + β := by rw [color_add_self]
      _ = α + (α + β) := by abel
  · by_cases hβ : x = β
    · rw [if_neg hα, if_pos hβ, if_pos (Or.inr hβ), hβ]
      calc
        α = 0 + α := by simp
        _ = (β + β) + α := by rw [color_add_self]
        _ = β + (α + β) := by abel
    · have hx : ¬(x = α ∨ x = β) := by
        intro h
        exact h.elim hα hβ
      rw [if_neg hα, if_neg hβ, if_neg hx]
      simp

@[simp] theorem swap_mem_twoColor_iff (α β x : Color) :
    swap α β x ∈ twoColor α β ↔ x ∈ twoColor α β := by
  unfold twoColor
  by_cases hα : x = α
  · subst x
    simp [swap]
  · by_cases hβ : x = β
    · subst x
      simp [swap]
    · simp [swap, hα, hβ]

end Color

/-- Convenient top-level shorthand for `Color.twoColor`. -/
def twoColor (α β : Color) : Set Color :=
  Color.twoColor α β

/-- Apply a Kempe switch that toggles colors `α` and `β` on a selected edge set. -/
noncomputable def switch {E : Type*} (α β : Color) (D : Set E) (C : E → Color) :
    E → Color := by
  classical
  exact fun e => if e ∈ D then Color.swap α β (C e) else C e

@[simp] theorem switch_of_not_mem {E : Type*} (α β : Color) (D : Set E)
    (C : E → Color) {e : E} (he : e ∉ D) :
    switch α β D C e = C e := by
  classical
  simp [switch, he]

@[simp] theorem switch_of_mem {E : Type*} (α β : Color) (D : Set E)
    (C : E → Color) {e : E} (he : e ∈ D) :
    switch α β D C e = Color.swap α β (C e) := by
  classical
  simp [switch, he]

theorem switch_finset_apply_eq_add_selected_delta {E : Type*} [DecidableEq E]
    (α β : Color) (S : Finset E) (C : E → Color) (e : E) :
    switch α β (S : Set E) C e =
      C e + if e ∈ S ∧ (C e = α ∨ C e = β) then α + β else 0 := by
  classical
  by_cases he : e ∈ S
  · simp [switch, he, Color.swap_eq_add_delta, Color.delta]
  · simp [switch, he]

theorem switch_mem_twoColor_iff {E : Type*} (α β : Color) (D : Set E)
    (C : E → Color) (e : E) :
    switch α β D C e ∈ twoColor α β ↔ C e ∈ twoColor α β := by
  classical
  by_cases he : e ∈ D
  · simp [switch, he, twoColor, Color.swap_mem_twoColor_iff]
  · simp [switch, he, twoColor]

/-- The edge set whose colors lie in the selected two-color pair. -/
def twoColorSupport {E : Type*} (C : E → Color) (α β : Color) : Set E :=
  {e | C e ∈ twoColor α β}

theorem twoColorSupport_switch {E : Type*} (α β : Color) (D : Set E)
    (C : E → Color) :
    twoColorSupport (switch α β D C) α β =
      twoColorSupport C α β := by
  classical
  ext e
  simpa [twoColorSupport] using
    (switch_mem_twoColor_iff (α := α) (β := β) (D := D) (C := C) e)

/-- The color-valued indicator of a finite edge set. -/
def indicatorChain {E : Type*} [DecidableEq E] (γ : Color) (S : Finset E) : E → Color :=
  fun e => if e ∈ S then γ else 0

@[simp] theorem indicatorChain_apply_of_mem {E : Type*} [DecidableEq E]
    (γ : Color) {S : Finset E} {e : E} (he : e ∈ S) :
    indicatorChain γ S e = γ := by
  simp [indicatorChain, he]

@[simp] theorem indicatorChain_apply_of_not_mem {E : Type*} [DecidableEq E]
    (γ : Color) {S : Finset E} {e : E} (he : e ∉ S) :
    indicatorChain γ S e = 0 := by
  simp [indicatorChain, he]

@[simp] theorem fst_indicatorChain_red {E : Type*} [DecidableEq E]
    (S : Finset E) (e : E) :
    (indicatorChain red S e).1 = if e ∈ S then (1 : F2) else 0 := by
  by_cases he : e ∈ S
  · simp [indicatorChain, red, he]
  · simp [indicatorChain, he]

@[simp] theorem snd_indicatorChain_blue {E : Type*} [DecidableEq E]
    (S : Finset E) (e : E) :
    (indicatorChain blue S e).2 = if e ∈ S then (1 : F2) else 0 := by
  by_cases he : e ∈ S
  · simp [indicatorChain, blue, he]
  · simp [indicatorChain, he]

/-- Over `𝔽₂²`, every color-valued indicator chain is self-cancelling. -/
theorem indicatorChain_add_self {E : Type*} [DecidableEq E]
    (γ : Color) (S : Finset E) :
    indicatorChain γ S + indicatorChain γ S = zeroChain := by
  funext e
  by_cases he : e ∈ S
  · simp [indicatorChain, he, color_add_self, zeroChain]
  · simp [indicatorChain, he, zeroChain]

/-- A red indicator chain has first-coordinate support exactly on its selected set. -/
theorem support₁_indicatorChain_red {E : Type*} [Fintype E] [DecidableEq E]
    (S : Finset E) :
    support₁ (indicatorChain red S) = S := by
  ext e
  by_cases he : e ∈ S
  · simp [support₁, indicatorChain, red, he]
  · simp [support₁, indicatorChain, red, he]

/-- Adding a red indicator chain toggles first-coordinate support by symmetric difference. -/
theorem support₁_after_indicatorChain_red {E : Type*} [Fintype E] [DecidableEq E]
    {x : E → Color} {S : Finset E} :
    support₁ (x + indicatorChain red S) =
      (support₁ x \ S) ∪ (S \ support₁ x) := by
  ext e
  by_cases he : e ∈ S
  · generalize ha : (x e).1 = a
    fin_cases a
    · simp [support₁, indicatorChain, red, he, ha,
        Finset.mem_union, Finset.mem_sdiff]
      constructor
      · intro _; rfl
      · intro _ h; cases h
    · simp [support₁, indicatorChain, red, he, ha,
        Finset.mem_union, Finset.mem_sdiff]
      constructor
      · intro h; exact False.elim (h rfl)
      · intro h; cases h
  · simp [support₁, indicatorChain, red, he,
      Finset.mem_union, Finset.mem_sdiff]

/-- A blue indicator chain has second-coordinate support exactly on its selected set. -/
theorem support₂_indicatorChain_blue {E : Type*} [Fintype E] [DecidableEq E]
    (S : Finset E) :
    support₂ (indicatorChain blue S) = S := by
  ext e
  by_cases he : e ∈ S
  · simp [support₂, indicatorChain, blue, he]
  · simp [support₂, indicatorChain, blue, he]

/-- Adding a blue indicator chain toggles second-coordinate support by symmetric difference. -/
theorem support₂_after_indicatorChain_blue {E : Type*} [Fintype E] [DecidableEq E]
    {x : E → Color} {S : Finset E} :
    support₂ (x + indicatorChain blue S) =
      (support₂ x \ S) ∪ (S \ support₂ x) := by
  ext e
  by_cases he : e ∈ S
  · generalize ha : (x e).2 = a
    fin_cases a
    · simp [support₂, indicatorChain, blue, he, ha,
        Finset.mem_union, Finset.mem_sdiff]
      constructor
      · intro _; rfl
      · intro _ h; cases h
    · simp [support₂, indicatorChain, blue, he, ha,
        Finset.mem_union, Finset.mem_sdiff]
      constructor
      · intro h; exact False.elim (h rfl)
      · intro h; cases h
  · simp [support₂, indicatorChain, blue, he,
      Finset.mem_union, Finset.mem_sdiff]

/-- Sum of a constant color over a finite set. -/
theorem sum_const {E : Type*} [DecidableEq E] (S : Finset E) (c : Color) :
    (∑ _e ∈ S, c) = S.card • c := by
  induction S using Finset.induction with
  | empty =>
      simp
  | insert e S he ih =>
    rw [Finset.sum_insert he, ih, Finset.card_insert_of_notMem he]
    ext <;> ring_nf

/-- Pointwise XOR of two color-chains, written additively over `𝔽₂²`. -/
def chainXor {E : Type*} (x y : E → Color) : E → Color :=
  fun e => x e + (-y e)

@[simp] theorem chainXor_apply {E : Type*} (x y : E → Color) (e : E) :
    chainXor x y e = x e + (-y e) :=
  rfl

theorem chainXor_add_right_cancel {E : Type*} (x y z : E → Color) :
    chainXor (x + z) (y + z) = chainXor x y := by
  funext e
  ext <;> simp [chainXor, color_neg_eq, add_comm, add_left_comm]

theorem chain_add_self_add {E : Type*} (x y : E → Color) :
    x + (x + y) = y := by
  funext e
  change x e + (x e + y e) = y e
  rw [← add_assoc]
  simp

end Mettapedia.GraphTheory.FourColor

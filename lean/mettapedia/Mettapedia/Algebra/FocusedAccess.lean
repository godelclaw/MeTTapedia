import Mathlib.Data.Set.Basic
import Mathlib.Order.Disjoint
import Mathlib.Data.Set.Disjoint
import Mathlib.Data.List.Infix

/-!
# Focused access: lenses, nesting, independence, and prefix regions

A **lens** focuses one part of a whole: it reads the part and replaces it, with
the three laws of a very well-behaved lens (read what you wrote, writing what you
read changes nothing, the later write wins).  Lenses nest (`Lens.comp`), so a
focus inside a focus is again a focus.

Two lenses are **independent** when writing through either leaves the other's
part unchanged and their writes commute (`Lens.Independent`).  Independence is
what lets two parties write through two foci at once.  It survives nesting:
foci inside independent foci are independent (`Independent.comp`).  A lens is
never independent of itself unless its part has only one value
(`Controls.not_independent_self`).

## Prefix regions of a path-indexed store

A trie stores a value at every path.  The paths extending a prefix form its
**cone**, and the lens `below p` reads and writes the store inside the cone of
`p`, re-rooted at `p`.

* **Nesting is concatenation** (`below_comp_below`): the focus at `q` inside the
  focus at `p` is the focus at `p ++ q`.
* **Cones are laminar** (`cones_laminar`): two cones are nested or disjoint, and
  they are disjoint exactly when neither prefix extends the other
  (`cone_disjoint_iff`).
* **Two prefix foci are independent exactly when their prefixes are
  incomparable** (`independent_below_iff`).  So writers below incomparable
  prefixes may run at once, and a writer below `p` can disturb every reader below
  an extension of `p`.
* **Frame**: writing below `p` leaves every path outside the cone of `p` unchanged
  (`below_put_of_not_prefix`).
* **The longest common prefix is the least cone above two cones**
  (`prefix_lcp_iff`, `cone_subset_cone_lcp`): it is the join of two write regions,
  and a region containing both contains it.

These are the regions of a PathMap trie under its write zippers: the focus
below `p` is what a zipper rooted at `p` reads and writes, its focus confined
below its root (`Mettapedia.OSLF.PathMap.Zipper`).  The MORK kernel's write
requests and their resolution are in
`Mettapedia.Languages.ProcessCalculi.MORK.WriteResourceResolution`, and
capabilities on cones in `Mettapedia.GSLT.Contracts.ConeCapabilities`.  A focus on
a subterm of one atom, rather than on a region of a store, is the lens relation
of `Mettapedia.Languages.ProcessCalculi.MORK.AtomZipper`.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.FocusedAccess

universe u v w x

/-! ## Lenses -/

/-- A very well-behaved lens: a part `A` of a whole `S` that can be read and
replaced. -/
structure Lens (S : Type u) (A : Type v) where
  get : S → A
  put : A → S → S
  /-- Reading after writing gives what was written. -/
  get_put : ∀ part whole, get (put part whole) = part
  /-- Writing back what was read changes nothing. -/
  put_get : ∀ whole, put (get whole) whole = whole
  /-- The later write wins. -/
  put_put : ∀ first second whole, put second (put first whole) = put second whole

namespace Lens

variable {S : Type u} {A : Type v} {B : Type w} {C : Type x}

/-- Two lenses with the same reading and writing are equal. -/
theorem ext {first second : Lens S A} (get : first.get = second.get) (put : first.put = second.put) :
    first = second := by
  cases first
  cases second
  cases get
  cases put
  rfl

/-- The identity focus. -/
def id (S : Type u) : Lens S S where
  get whole := whole
  put part _ := part
  get_put _ _ := rfl
  put_get _ := rfl
  put_put _ _ _ := rfl

/-- **Nesting**: focus on `B` inside the part `A`. -/
def comp (outer : Lens S A) (inner : Lens A B) : Lens S B where
  get whole := inner.get (outer.get whole)
  put part whole := outer.put (inner.put part (outer.get whole)) whole
  get_put part whole := by rw [outer.get_put, inner.get_put]
  put_get whole := by rw [inner.put_get, outer.put_get]
  put_put first second whole := by rw [outer.get_put, inner.put_put, outer.put_put]

theorem comp_assoc (first : Lens S A) (second : Lens A B) (third : Lens B C) :
    (first.comp second).comp third = first.comp (second.comp third) := by
  apply ext
  · rfl
  · funext part whole
    simp only [comp]

/-- **Independent foci**: writing through either leaves the other's part
unchanged, and the writes commute. -/
structure Independent (left : Lens S A) (right : Lens S B) : Prop where
  get_right_put_left : ∀ part whole, right.get (left.put part whole) = right.get whole
  get_left_put_right : ∀ part whole, left.get (right.put part whole) = left.get whole
  put_comm : ∀ leftPart rightPart whole,
    left.put leftPart (right.put rightPart whole) = right.put rightPart (left.put leftPart whole)

theorem Independent.symm {left : Lens S A} {right : Lens S B} (independent : Independent left right) :
    Independent right left :=
  ⟨independent.get_left_put_right, independent.get_right_put_left,
    fun rightPart leftPart whole => (independent.put_comm leftPart rightPart whole).symm⟩

/-- **Foci inside independent foci are independent.** -/
theorem Independent.comp {A' : Type v} {B' : Type w} {left : Lens S A} {right : Lens S B}
    (independent : Independent left right) (leftInner : Lens A A') (rightInner : Lens B B') :
    Independent (left.comp leftInner) (right.comp rightInner) where
  get_right_put_left part whole := by
    simp only [Lens.comp]
    rw [independent.get_right_put_left]
  get_left_put_right part whole := by
    simp only [Lens.comp]
    rw [independent.get_left_put_right]
  put_comm leftPart rightPart whole := by
    simp only [Lens.comp]
    rw [independent.get_left_put_right, independent.get_right_put_left, independent.put_comm]

end Lens

/-! ## Prefix regions -/

section Prefixes

variable {σ : Type u} {V : Type v}

/-- The paths extending a prefix. -/
def cone (pre : List σ) : Set (List σ) := {path | pre <+: path}

theorem mem_cone {pre path : List σ} : path ∈ cone pre ↔ pre <+: path :=
  Iff.rfl

/-- One cone contains another exactly when its prefix is a prefix of the other's. -/
theorem cone_subset_iff {first second : List σ} : cone second ⊆ cone first ↔ first <+: second := by
  constructor
  · intro subset
    exact subset (List.prefix_refl second)
  · intro below path inside
    exact below.trans inside

/-- **Two cones are disjoint exactly when neither prefix extends the other.** -/
theorem cone_disjoint_iff {first second : List σ} :
    Disjoint (cone first) (cone second) ↔ ¬ first <+: second ∧ ¬ second <+: first := by
  rw [Set.disjoint_left]
  constructor
  · intro apart
    refine ⟨fun below => apart below (List.prefix_refl second), fun below => ?_⟩
    exact apart (List.prefix_refl first) below
  · rintro ⟨notFirst, notSecond⟩ path inFirst inSecond
    rcases List.prefix_or_prefix_of_prefix inFirst inSecond with below | below
    · exact notFirst below
    · exact notSecond below

/-- **Cones are laminar**: nested or disjoint. -/
theorem cones_laminar (first second : List σ) :
    cone second ⊆ cone first ∨ cone first ⊆ cone second ∨ Disjoint (cone first) (cone second) := by
  by_cases below : first <+: second
  · exact Or.inl (cone_subset_iff.mpr below)
  · by_cases above : second <+: first
    · exact Or.inr (Or.inl (cone_subset_iff.mpr above))
    · exact Or.inr (Or.inr (cone_disjoint_iff.mpr ⟨below, above⟩))

/-- A prefix of a concatenation: `p ++ q` is a prefix of `path` exactly when `p`
is, and `q` is a prefix of the rest. -/
theorem append_prefix_iff (first second path : List σ) :
    first ++ second <+: path ↔ first <+: path ∧ second <+: path.drop first.length := by
  constructor
  · rintro ⟨rest, rfl⟩
    refine ⟨(List.prefix_append first second).trans (List.prefix_append _ rest), ?_⟩
    rw [List.append_assoc, List.drop_left]
    exact List.prefix_append second rest
  · rintro ⟨⟨middle, rfl⟩, ⟨rest, restEq⟩⟩
    rw [List.drop_left] at restEq
    exact ⟨rest, by rw [List.append_assoc, restEq]⟩

variable [DecidableEq σ]

/-- **The focus below a prefix**: the store inside the cone of `pre`, re-rooted at
`pre`. -/
def below (pre : List σ) : Lens (List σ → V) (List σ → V) where
  get store := fun rest => store (pre ++ rest)
  put part store := fun path => if pre <+: path then part (path.drop pre.length) else store path
  get_put part store := by
    funext rest
    simp [List.prefix_append]
  put_get store := by
    funext path
    split_ifs with inside
    · exact congrArg store (List.prefix_iff_eq_append.mp inside)
    · rfl
  put_put first second store := by
    funext path
    by_cases inside : pre <+: path <;> simp [inside]

theorem below_get (pre : List σ) (store : List σ → V) (rest : List σ) :
    (below pre).get store rest = store (pre ++ rest) :=
  rfl

theorem below_put (pre : List σ) (part store : List σ → V) (path : List σ) :
    (below pre).put part store path =
      if pre <+: path then part (path.drop pre.length) else store path :=
  rfl

/-- **Frame**: writing below `pre` changes nothing outside its cone. -/
theorem below_put_of_not_prefix {pre path : List σ} (outside : ¬ pre <+: path)
    (part store : List σ → V) : (below pre).put part store path = store path := by
  rw [below_put, if_neg outside]

/-- **Nesting is concatenation.** -/
theorem below_comp_below (first second : List σ) :
    (below (V := V) first).comp (below second) = below (first ++ second) := by
  apply Lens.ext
  · funext store rest
    simp [Lens.comp, below_get, List.append_assoc]
  · funext part store path
    simp only [Lens.comp, below_put, below_get]
    by_cases outer : first <+: path
    · rw [if_pos outer]
      by_cases inner : second <+: path.drop first.length
      · rw [if_pos inner, if_pos ((append_prefix_iff first second path).mpr ⟨outer, inner⟩),
          List.drop_drop, List.length_append, Nat.add_comm]
      · rw [if_neg inner, if_neg fun both => inner ((append_prefix_iff first second path).mp both).2]
        exact congrArg store (List.prefix_iff_eq_append.mp outer)
    · rw [if_neg outer, if_neg fun both => outer ((append_prefix_iff first second path).mp both).1]

/-- Writing below one prefix leaves the reading below an incomparable prefix
unchanged. -/
theorem below_get_put_of_incomparable {first second : List σ} (notFirst : ¬ first <+: second)
    (notSecond : ¬ second <+: first) (part store : List σ → V) :
    (below second).get ((below first).put part store) = (below second).get store := by
  funext rest
  rw [below_get, below_get, below_put_of_not_prefix]
  intro below
  rcases List.prefix_or_prefix_of_prefix below (List.prefix_append second rest) with
    firstBelow | secondBelow
  · exact notFirst firstBelow
  · exact notSecond secondBelow

/-- **Two prefix foci are independent exactly when their prefixes are
incomparable.** -/
theorem independent_below_iff [Nontrivial V] (first second : List σ) :
    Lens.Independent (below (V := V) first) (below second) ↔
      ¬ first <+: second ∧ ¬ second <+: first := by
  constructor
  · intro independent
    obtain ⟨a, b, different⟩ := exists_pair_ne V
    constructor
    · intro firstBelow
      -- Writing `b` below `second` is seen below `first`.
      have seen := congrFun (independent.get_left_put_right (fun _ => b) (fun _ => a))
        (second.drop first.length)
      rw [below_get, below_get, List.prefix_iff_eq_append.mp firstBelow, below_put,
        if_pos (List.prefix_refl second)] at seen
      exact different seen.symm
    · intro secondBelow
      have seen := congrFun (independent.get_right_put_left (fun _ => b) (fun _ => a))
        (first.drop second.length)
      rw [below_get, below_get, List.prefix_iff_eq_append.mp secondBelow, below_put,
        if_pos (List.prefix_refl first)] at seen
      exact different seen.symm
  · rintro ⟨notFirst, notSecond⟩
    refine ⟨below_get_put_of_incomparable notFirst notSecond,
      below_get_put_of_incomparable notSecond notFirst, ?_⟩
    intro leftPart rightPart store
    funext path
    simp only [below_put]
    by_cases inFirst : first <+: path
    · have notInSecond : ¬ second <+: path := fun inSecond =>
        (List.prefix_or_prefix_of_prefix inFirst inSecond).elim notFirst notSecond
      simp [inFirst, notInSecond]
    · simp [inFirst]

/-! ## The longest common prefix -/

/-- The longest common prefix of two paths. -/
def lcp : List σ → List σ → List σ
  | a :: first, b :: second => if a = b then a :: lcp first second else []
  | _, _ => []

theorem lcp_prefix_left : ∀ first second : List σ, lcp first second <+: first
  | [], _ => List.nil_prefix
  | _ :: _, [] => List.nil_prefix
  | a :: first, b :: second => by
      unfold lcp
      split_ifs
      · exact List.cons_prefix_cons.mpr ⟨rfl, lcp_prefix_left first second⟩
      · exact List.nil_prefix

theorem lcp_prefix_right : ∀ first second : List σ, lcp first second <+: second
  | [], _ => List.nil_prefix
  | _ :: _, [] => List.nil_prefix
  | a :: first, b :: second => by
      unfold lcp
      split_ifs with same
      · subst same
        exact List.cons_prefix_cons.mpr ⟨rfl, lcp_prefix_right first second⟩
      · exact List.nil_prefix

/-- **The longest common prefix is the greatest common prefix.** -/
theorem prefix_lcp_iff : ∀ (pre first second : List σ),
    pre <+: lcp first second ↔ pre <+: first ∧ pre <+: second
  | pre, first, second => by
      constructor
      · intro below
        exact ⟨below.trans (lcp_prefix_left first second), below.trans (lcp_prefix_right first second)⟩
      · rintro ⟨belowFirst, belowSecond⟩
        induction pre generalizing first second with
        | nil => exact List.nil_prefix
        | cons c pre ih =>
            cases first with
            | nil => exact absurd belowFirst (by simp)
            | cons a first =>
                cases second with
                | nil => exact absurd belowSecond (by simp)
                | cons b second =>
                    rw [List.cons_prefix_cons] at belowFirst belowSecond
                    obtain ⟨rfl, belowFirst⟩ := belowFirst
                    obtain ⟨rfl, belowSecond⟩ := belowSecond
                    simp only [lcp, if_true, List.cons_prefix_cons, true_and]
                    exact ih first second belowFirst belowSecond

/-- Both cones lie in the cone of the longest common prefix. -/
theorem cone_subset_cone_lcp (first second : List σ) :
    cone first ⊆ cone (lcp first second) ∧ cone second ⊆ cone (lcp first second) :=
  ⟨cone_subset_iff.mpr (lcp_prefix_left first second),
    cone_subset_iff.mpr (lcp_prefix_right first second)⟩

/-- **It is the least such cone**: a cone containing both contains it. -/
theorem cone_lcp_subset_iff (first second region : List σ) :
    cone (lcp first second) ⊆ cone region ↔ cone first ⊆ cone region ∧ cone second ⊆ cone region := by
  simp only [cone_subset_iff]
  exact prefix_lcp_iff region first second

end Prefixes

/-! ## Controls -/

namespace Controls

open Lens

/-- A lens is not independent of itself when its part has two values. -/
theorem not_independent_self {S : Type u} {A : Type v} [Nontrivial A] [Nonempty S]
    (lens : Lens S A) : ¬ Lens.Independent lens lens := by
  intro independent
  obtain ⟨a, b, different⟩ := exists_pair_ne A
  obtain ⟨whole⟩ := ‹Nonempty S›
  have seen := independent.get_right_put_left a (lens.put b whole)
  rw [lens.get_put, lens.get_put] at seen
  exact different seen

/-- Nested prefixes are not independent: `[0]` and `[0, 1]`. -/
theorem nested_not_independent :
    ¬ Lens.Independent (below (σ := ℕ) (V := Bool) [0]) (below [0, 1]) := by
  rw [independent_below_iff]
  simp

/-- Incomparable prefixes are independent: `[0, 1]` and `[0, 2]`. -/
theorem siblings_independent :
    Lens.Independent (below (σ := ℕ) (V := Bool) [0, 1]) (below [0, 2]) := by
  rw [independent_below_iff]
  simp

/-- The least cone above the cones of `[0, 1]` and `[0, 2]` is that of `[0]`. -/
theorem lcp_siblings : lcp ([0, 1] : List ℕ) [0, 2] = [0] := by
  decide

end Controls

end Mettapedia.Algebra.FocusedAccess

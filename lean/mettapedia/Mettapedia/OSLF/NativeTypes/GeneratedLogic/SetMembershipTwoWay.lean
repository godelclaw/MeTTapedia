import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipPastModalities

/-!
# Two-way native types of the hereditarily finite sets are decidable

The two-way formulas nest steps forward, steps back, splits, emptiness, named sets and quantifiers over a sort, with
the connectives and no fixed point, counting or singleton (`Formula.twoWay`). Among the hereditarily finite sets every
such formula is decided by a finite evaluation.

- **A step back sees one level less.** A formula `◆ψ` at `x` asks for a set containing `x` with `ψ`, and replacing `x`
  by a set bisimilar to it up to `k` inside that set gives a set bisimilar up to `k + 1`. So the two-way depth
  (`Formula.twoWayDepth`) adds one for a step forward and takes one away for a step back, and a two-way formula holds
  alike at hereditarily finite sets bisimilar up to its two-way depth (`twoWay_sat_iff`).
- **Named sets and splits keep the depth.** A set bisimilar to a named set beyond its height is that set
  (`eq_of_bisim_height`), and a split of one set gives a split of a set bisimilar to it, with the parts bisimilar to
  the same depth (`split_bisim`). Singletons and counting do not: two members bisimilar up to a depth may be two sets.
- **Steps back and sorts by finite search** (`twoWay_sometimeBefore_iff`, `twoWay_someOf_iff` and their duals):
  a set containing `x` may be taken to be `x` with a subset of `V_n`, for `n` the depth of the body (at least one),
  and a set of the sort may be taken to be a subset of `V_n`.
- **The evaluation** (`evalTwoWay`) runs on hereditary terms: steps forward read the members, splits the coverings of
  the members, named sets compare sets, and steps back and sorts try the subsets of a finite stage. It is exact
  (`evalTwoWay_iff`), so the truth of a two-way native type at a hereditary term, read among the hereditary terms, is
  decidable (`twoWay_decide`).

This answers, for the fixed-point-free fragment, whether native types with steps back are decidable on `V_ω`. A fixed
point is not bounded by a depth; the types of `SetMembershipTypes` bound it instead when its variable does not cross a
step back (`SetMembershipFixedPoints`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax

universe u

namespace Formula

/-- **Two-way formulas**: steps forward and back, splits, emptiness, named sets and quantifiers over a sort, with the
connectives and no fixed point, variable, counting or singleton. -/
def twoWay : {n : ℕ} → Formula n → Bool
  | _, .top | _, .bot | _, .empty _ | _, .nonEmpty _ | _, .is _ | _, .isNot _ => true
  | _, .and left right | _, .or left right | _, .split _ left right | _, .everySplit _ left right =>
    twoWay left && twoWay right
  | _, .possibly _ inner | _, .necessarily _ inner | _, .sometimeBefore _ inner | _, .alwaysBefore _ inner =>
    twoWay inner
  | _, .someOf (.base _) inner | _, .everyOf (.base _) inner => twoWay inner
  | _, _ => false

/-- **The two-way depth**: one more for a step forward, one less for a step back, the height of a named set and one
more, and the greater of the two parts for a split. -/
def twoWayDepth : {n : ℕ} → Formula n → ℕ
  | _, .empty _ | _, .nonEmpty _ => 1
  | _, .is term | _, .isNot term => SetReadings.height term + 1
  | _, .and left right | _, .or left right | _, .split _ left right | _, .everySplit _ left right =>
    max (twoWayDepth left) (twoWayDepth right)
  | _, .possibly _ inner | _, .necessarily _ inner => twoWayDepth inner + 1
  | _, .sometimeBefore _ inner | _, .alwaysBefore _ inner => twoWayDepth inner - 1
  | _, _ => 0

end Formula

namespace NativeStructure

variable {Carrier : Type u} (S : NativeStructure Carrier)

theorem bisimUpTo_symm : ∀ {k : ℕ} {first second : Carrier}, S.BisimUpTo k first second →
    S.BisimUpTo k second first
  | 0, _, _, _ => trivial
  | k + 1, _, _, related => by
    obtain ⟨forth, back⟩ := (S.bisimUpTo_succ_iff).mp related
    refine (S.bisimUpTo_succ_iff).mpr ⟨fun label next step => ?_, fun label next step => ?_⟩
    · obtain ⟨next', step', related'⟩ := back label next step
      exact ⟨next', step', bisimUpTo_symm related'⟩
    · obtain ⟨next', step', related'⟩ := forth label next step
      exact ⟨next', step', bisimUpTo_symm related'⟩

end NativeStructure

end Mettapedia.OSLF.NativeTypes.GeneratedLogic

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- A hereditarily finite set. -/
abbrev HF := {z : ZFSet.{0} // IsHFSet z}

/-! ## A step back sees one level less -/

/-- **Replacing a member by a set bisimilar to it up to `k` gives a set bisimilar up to `k + 1`.** -/
theorem replace_bisim {k : ℕ} {x x' container : ZFSet.{0}} (related : extensional.BisimUpTo k x x')
    (member : x ∈ container) :
    extensional.BisimUpTo (k + 1) container (insert x' (ZFSet.sep (fun other => other ≠ x) container)) := by
  classical
  refine (extensional.bisimUpTo_succ_iff).mpr ⟨fun label next step => ?_, fun label next' step => ?_⟩
  · by_cases same : next = x
    · subst same
      exact ⟨x', ⟨step.1, ZFSet.mem_insert_iff.mpr (Or.inl rfl)⟩, related⟩
    · exact ⟨next, ⟨step.1, ZFSet.mem_insert_iff.mpr (Or.inr (ZFSet.mem_sep.mpr ⟨step.2, same⟩))⟩,
        extensional.bisimUpTo_refl k next⟩
  · rcases ZFSet.mem_insert_iff.mp step.2 with same | inside
    · subst same
      exact ⟨x, ⟨step.1, member⟩, related⟩
    · exact ⟨next', ⟨step.1, (ZFSet.mem_sep.mp inside).1⟩, extensional.bisimUpTo_refl k next'⟩

theorem isHFSet_sep {whole : ZFSet.{0}} (holds : IsHFSet whole) (test : ZFSet.{0} → Prop) :
    IsHFSet (ZFSet.sep test whole) := by
  obtain ⟨term, termHolds, rfl⟩ := holds
  exact isHFSet_of_subset termHolds fun z member => (ZFSet.mem_sep.mp member).1

/-- The container with `x` replaced by `x'`. -/
noncomputable def replaced (x x' : HF) (container : HF) : HF :=
  ⟨insert x'.1 (ZFSet.sep (fun other => other ≠ x.1) container.1), isHFSet_insert x'.2 (isHFSet_sep container.2 _)⟩

theorem isHFSet_of_subset_hf {whole part : ZFSet.{0}} (holds : IsHFSet whole) (within : part ⊆ whole) :
    IsHFSet part := by
  obtain ⟨term, termHolds, rfl⟩ := holds
  exact isHFSet_of_subset termHolds within

/-- **A set bisimilar to a named set beyond its height is that set.** -/
theorem eq_of_bisim_height {term : Pattern} (holds : IsHF term) :
    ∀ {k : ℕ} {x : ZFSet.{0}}, height term < k → extensional.BisimUpTo k x (zfOf term) → x = zfOf term := by
  induction holds with
  | atom atom => exact absurd atom (membership_pure _)
  | @members values inside recurse =>
    intro k x tall related
    cases k with
    | zero => exact absurd tall (Nat.not_lt_zero _)
    | succ k =>
      obtain ⟨forth, back⟩ := (extensional.bisimUpTo_succ_iff).mp related
      have lower : ∀ value ∈ values, height value < k := fun value member => by
        have below := height_le_heightList (values := values) member
        simp only [height, set] at tall
        omega
      apply ZFSet.ext
      intro z
      constructor
      · intro member
        obtain ⟨z', ⟨-, inside'⟩, related'⟩ := forth .any z ⟨trivial, member⟩
        rw [zfOf_set] at inside'
        obtain ⟨value, found, rfl⟩ := mem_zfOfList.mp inside'
        rw [recurse value found (lower value found) related', zfOf_set]
        exact mem_zfOfList.mpr ⟨value, found, rfl⟩
      · intro member
        rw [zfOf_set] at member
        obtain ⟨value, found, rfl⟩ := mem_zfOfList.mp member
        have inside'' : zfOf value ∈ zfOf (set values) := by
          rw [zfOf_set]
          exact mem_zfOfList.mpr ⟨value, found, rfl⟩
        obtain ⟨m, ⟨-, inside⟩, related'⟩ := back .any (zfOf value) ⟨trivial, inside''⟩
        rw [← recurse value found (lower value found) related']
        exact inside

/-- **A split of one set gives a split of a set bisimilar to it**, with the parts bisimilar to the same depth. -/
theorem split_bisim {k : ℕ} {x x' a b : ZFSet.{0}} (related : extensional.BisimUpTo k x x') (union : x = a ∪ b) :
    ∃ a' b', x' = a' ∪ b' ∧ a' ⊆ x' ∧ b' ⊆ x' ∧ extensional.BisimUpTo k a a' ∧ extensional.BisimUpTo k b b' := by
  cases k with
  | zero =>
    exact ⟨x', x', ZFSet.ext fun z => by rw [ZFSet.mem_union, or_self], fun _ h => h, fun _ h => h, trivial, trivial⟩
  | succ k =>
    obtain ⟨forth, back⟩ := (extensional.bisimUpTo_succ_iff).mp related
    let partner := fun (part : ZFSet.{0}) => ZFSet.sep (fun m' => ∃ m ∈ part, extensional.BisimUpTo k m m') x'
    have partBisim : ∀ part ⊆ x, extensional.BisimUpTo (k + 1) part (partner part) := by
      intro part within
      refine (extensional.bisimUpTo_succ_iff).mpr ⟨fun label next step => ?_, fun label next' step => ?_⟩
      · obtain ⟨next', step', related'⟩ := forth label next ⟨step.1, within step.2⟩
        exact ⟨next', ⟨step.1, ZFSet.mem_sep.mpr ⟨step'.2, next, step.2, related'⟩⟩, related'⟩
      · obtain ⟨-, m, inside, related'⟩ := ZFSet.mem_sep.mp step.2
        exact ⟨m, ⟨step.1, inside⟩, related'⟩
    refine ⟨partner a, partner b, ?_, fun _ h => (ZFSet.mem_sep.mp h).1, fun _ h => (ZFSet.mem_sep.mp h).1,
      partBisim a (fun z h => union ▸ ZFSet.mem_union.mpr (Or.inl h)),
      partBisim b (fun z h => union ▸ ZFSet.mem_union.mpr (Or.inr h))⟩
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_union]
    constructor
    · intro member
      obtain ⟨m, step, related'⟩ := back .any z ⟨trivial, member⟩
      have inside := step.2
      rw [union, ZFSet.mem_union] at inside
      rcases inside with inA | inB
      · exact Or.inl (ZFSet.mem_sep.mpr ⟨member, m, inA, related'⟩)
      · exact Or.inr (ZFSet.mem_sep.mpr ⟨member, m, inB, related'⟩)
    · rintro (inA | inB)
      · exact (ZFSet.mem_sep.mp inA).1
      · exact (ZFSet.mem_sep.mp inB).1

/-- **A two-way formula holds alike at hereditarily finite sets bisimilar up to its two-way depth.** -/
theorem twoWay_sat_iff : ∀ {n : ℕ} (formula : Formula n), formula.twoWay = true → ∀ (k : ℕ),
    formula.twoWayDepth ≤ k → ∀ (env : Env HF n) {first second : HF}, extensional.BisimUpTo k first.1 second.1 →
      (HFSets.sat env formula first ↔ HFSets.sat env formula second)
  | _, .top, _, _, _, _, _, _, _ => Iff.rfl
  | _, .bot, _, _, _, _, _, _, _ => Iff.rfl
  | _, .empty _, _, 0, depth, _, _, _, _ => absurd depth (by simp [Formula.twoWayDepth])
  | _, .empty kind, _, k + 1, _, _, first, second, related => by
    change (kind = .hashSet ∧ first.1 = ∅) ↔ (kind = .hashSet ∧ second.1 = ∅)
    exact and_congr Iff.rfl (empty_iff_of_bisim related)
  | _, .nonEmpty _, _, 0, depth, _, _, _, _ => absurd depth (by simp [Formula.twoWayDepth])
  | _, .nonEmpty kind, _, k + 1, _, _, first, second, related => by
    change ¬ (kind = .hashSet ∧ first.1 = ∅) ↔ ¬ (kind = .hashSet ∧ second.1 = ∅)
    exact not_congr (and_congr Iff.rfl (empty_iff_of_bisim related))
  | _, .and left right, fragment, k, depth, env, _, _, related => by
    simp only [Formula.twoWay, Bool.and_eq_true] at fragment
    simp only [Formula.twoWayDepth, max_le_iff] at depth
    exact and_congr (twoWay_sat_iff left fragment.1 k depth.1 env related)
      (twoWay_sat_iff right fragment.2 k depth.2 env related)
  | _, .or left right, fragment, k, depth, env, _, _, related => by
    simp only [Formula.twoWay, Bool.and_eq_true] at fragment
    simp only [Formula.twoWayDepth, max_le_iff] at depth
    exact or_congr (twoWay_sat_iff left fragment.1 k depth.1 env related)
      (twoWay_sat_iff right fragment.2 k depth.2 env related)
  | _, .possibly _ _, _, 0, depth, _, _, _, _ => absurd depth (by simp [Formula.twoWayDepth])
  | _, .possibly label inner, fragment, k + 1, depth, env, first, second, related => by
    have depth' : inner.twoWayDepth ≤ k := by simpa [Formula.twoWayDepth] using depth
    obtain ⟨forth, back⟩ := (extensional.bisimUpTo_succ_iff).mp related
    constructor
    · rintro ⟨next, step, holds⟩
      obtain ⟨next', step', related'⟩ := forth label next.1 step
      exact ⟨⟨next', hfSets_generated.step (memberLabel_own step'.1) second.2 step'⟩, step',
        (twoWay_sat_iff inner fragment k depth' env (first := next) (second := ⟨next', _⟩) related').mp holds⟩
    · rintro ⟨next', step', holds⟩
      obtain ⟨next, step, related'⟩ := back label next'.1 step'
      exact ⟨⟨next, hfSets_generated.step (memberLabel_own step.1) first.2 step⟩, step,
        (twoWay_sat_iff inner fragment k depth' env (first := ⟨next, _⟩) (second := next') related').mpr holds⟩
  | _, .necessarily _ _, _, 0, depth, _, _, _, _ => absurd depth (by simp [Formula.twoWayDepth])
  | _, .necessarily label inner, fragment, k + 1, depth, env, first, second, related => by
    have depth' : inner.twoWayDepth ≤ k := by simpa [Formula.twoWayDepth] using depth
    obtain ⟨forth, back⟩ := (extensional.bisimUpTo_succ_iff).mp related
    constructor
    · intro every next' step'
      obtain ⟨next, step, related'⟩ := back label next'.1 step'
      exact (twoWay_sat_iff inner fragment k depth' env (first := ⟨next, hfSets_generated.step (memberLabel_own step.1) first.2 step⟩)
        (second := next') related').mp (every _ step)
    · intro every next step
      obtain ⟨next', step', related'⟩ := forth label next.1 step
      exact (twoWay_sat_iff inner fragment k depth' env (first := next)
        (second := ⟨next', hfSets_generated.step (memberLabel_own step'.1) second.2 step'⟩) related').mpr (every _ step')
  | _, .sometimeBefore label inner, fragment, k, depth, env, first, second, related => by
    have depth' : inner.twoWayDepth ≤ k + 1 := by simp only [Formula.twoWayDepth] at depth; omega
    constructor
    · rintro ⟨previous, step, holds⟩
      refine ⟨replaced first second previous, ⟨step.1, ZFSet.mem_insert_iff.mpr (Or.inl rfl)⟩, ?_⟩
      exact (twoWay_sat_iff inner fragment (k + 1) depth' env (replace_bisim related step.2)).mp holds
    · rintro ⟨previous, step, holds⟩
      refine ⟨replaced second first previous, ⟨step.1, ZFSet.mem_insert_iff.mpr (Or.inl rfl)⟩, ?_⟩
      exact (twoWay_sat_iff inner fragment (k + 1) depth' env
        (replace_bisim (extensional.bisimUpTo_symm related) step.2)).mp holds
  | _, .alwaysBefore label inner, fragment, k, depth, env, first, second, related => by
    have depth' : inner.twoWayDepth ≤ k + 1 := by simp only [Formula.twoWayDepth] at depth; omega
    constructor
    · intro every previous step
      exact (twoWay_sat_iff inner fragment (k + 1) depth' env
        (replace_bisim (extensional.bisimUpTo_symm related) step.2)).mpr
          (every (replaced second first previous) ⟨step.1, ZFSet.mem_insert_iff.mpr (Or.inl rfl)⟩)
    · intro every previous step
      exact (twoWay_sat_iff inner fragment (k + 1) depth' env (replace_bisim related step.2)).mpr
        (every (replaced first second previous) ⟨step.1, ZFSet.mem_insert_iff.mpr (Or.inl rfl)⟩)
  | _, .is term, _, k, depth, _, first, second, related => by
    have tall : height term < k := by simp only [Formula.twoWayDepth] at depth; omega
    change (IsHF term ∧ first.1 = zfOf term) ↔ (IsHF term ∧ second.1 = zfOf term)
    constructor
    · rintro ⟨holds, same⟩
      refine ⟨holds, eq_of_bisim_height holds tall ?_⟩
      rw [← same]
      exact extensional.bisimUpTo_symm related
    · rintro ⟨holds, same⟩
      refine ⟨holds, eq_of_bisim_height holds tall ?_⟩
      rw [← same]
      exact related
  | _, .isNot term, _, k, depth, _, first, second, related => by
    have tall : height term < k := by simp only [Formula.twoWayDepth] at depth; omega
    change ¬ (IsHF term ∧ first.1 = zfOf term) ↔ ¬ (IsHF term ∧ second.1 = zfOf term)
    refine not_congr ⟨fun ⟨holds, same⟩ => ⟨holds, eq_of_bisim_height holds tall ?_⟩,
      fun ⟨holds, same⟩ => ⟨holds, eq_of_bisim_height holds tall ?_⟩⟩
    · rw [← same]
      exact extensional.bisimUpTo_symm related
    · rw [← same]
      exact related
  | _, .split kind left right, fragment, k, depth, env, first, second, related => by
    simp only [Formula.twoWay, Bool.and_eq_true] at fragment
    simp only [Formula.twoWayDepth, max_le_iff] at depth
    constructor
    · rintro ⟨part, other, ⟨kinded, union⟩, holdsLeft, holdsRight⟩
      obtain ⟨part', other', union', within, within', related₁, related₂⟩ := split_bisim related union
      exact ⟨⟨part', isHFSet_of_subset_hf second.2 within⟩, ⟨other', isHFSet_of_subset_hf second.2 within'⟩,
        ⟨kinded, union'⟩, (twoWay_sat_iff left fragment.1 k depth.1 env (second := ⟨part', _⟩) related₁).mp holdsLeft,
        (twoWay_sat_iff right fragment.2 k depth.2 env (second := ⟨other', _⟩) related₂).mp holdsRight⟩
    · rintro ⟨part, other, ⟨kinded, union⟩, holdsLeft, holdsRight⟩
      obtain ⟨part', other', union', within, within', related₁, related₂⟩ :=
        split_bisim (extensional.bisimUpTo_symm related) union
      exact ⟨⟨part', isHFSet_of_subset_hf first.2 within⟩, ⟨other', isHFSet_of_subset_hf first.2 within'⟩,
        ⟨kinded, union'⟩, (twoWay_sat_iff left fragment.1 k depth.1 env (second := ⟨part', _⟩) related₁).mp holdsLeft,
        (twoWay_sat_iff right fragment.2 k depth.2 env (second := ⟨other', _⟩) related₂).mp holdsRight⟩
  | _, .everySplit kind left right, fragment, k, depth, env, first, second, related => by
    simp only [Formula.twoWay, Bool.and_eq_true] at fragment
    simp only [Formula.twoWayDepth, max_le_iff] at depth
    constructor
    · intro every part' other' isSplit
      obtain ⟨part, other, union, within, within', related₁, related₂⟩ :=
        split_bisim (extensional.bisimUpTo_symm related) isSplit.2
      exact (every ⟨part, isHFSet_of_subset_hf first.2 within⟩ ⟨other, isHFSet_of_subset_hf first.2 within'⟩
        ⟨isSplit.1, union⟩).imp
        (fun holdsLeft => (twoWay_sat_iff left fragment.1 k depth.1 env (second := ⟨part, _⟩) related₁).mpr holdsLeft)
        (fun holdsRight =>
          (twoWay_sat_iff right fragment.2 k depth.2 env (second := ⟨other, _⟩) related₂).mpr holdsRight)
    · intro every part other isSplit
      obtain ⟨part', other', union', within, within', related₁, related₂⟩ := split_bisim related isSplit.2
      exact (every ⟨part', isHFSet_of_subset_hf second.2 within⟩ ⟨other', isHFSet_of_subset_hf second.2 within'⟩
        ⟨isSplit.1, union'⟩).imp
        (fun holdsLeft => (twoWay_sat_iff left fragment.1 k depth.1 env (second := ⟨part', _⟩) related₁).mpr holdsLeft)
        (fun holdsRight =>
          (twoWay_sat_iff right fragment.2 k depth.2 env (second := ⟨other', _⟩) related₂).mpr holdsRight)
  | _, .someOf (.base _) _, _, _, _, _, _, _, _ => Iff.rfl
  | _, .everyOf (.base _) _, _, _, _, _, _, _, _ => Iff.rfl
  | _, .someOf (.collection _ _) _, fragment, _, _, _, _, _, _
  | _, .someOf (.arrow _ _) _, fragment, _, _, _, _, _, _
  | _, .someOf (.multiBinder _) _, fragment, _, _, _, _, _, _
  | _, .everyOf (.collection _ _) _, fragment, _, _, _, _, _, _
  | _, .everyOf (.arrow _ _) _, fragment, _, _, _, _, _, _
  | _, .everyOf (.multiBinder _) _, fragment, _, _, _, _, _, _
  | _, .var _, fragment, _, _, _, _, _, _ | _, .typed _, fragment, _, _, _, _, _, _
  | _, .untyped _, fragment, _, _, _, _, _, _ | _, .mu _, fragment, _, _, _, _, _, _
  | _, .nu _, fragment, _, _, _, _, _, _ | _, .single _ _, fragment, _, _, _, _, _, _
  | _, .everySingle _ _, fragment, _, _, _, _, _, _ | _, .atLeast _ _ _ _, fragment, _, _, _, _, _, _
  | _, .allButFewer _ _ _ _, fragment, _, _, _, _, _, _ | _, .built _ _, fragment, _, _, _, _, _, _
  | _, .everyBuilt _ _, fragment, _, _, _, _, _, _ | _, .body _, fragment, _, _, _, _, _, _
  | _, .everyBody _, fragment, _, _, _, _, _, _ | _, .multiBody _ _, fragment, _, _, _, _, _, _
  | _, .everyMultiBody _ _, fragment, _, _, _, _, _, _ | _, .bound _, fragment, _, _, _, _, _, _
  | _, .notBound _, fragment, _, _, _, _, _, _ | _, .mapsAll _ _, fragment, _, _, _, _, _, _
  | _, .mapsSome _ _, fragment, _, _, _, _, _, _ => absurd fragment Bool.false_ne_true
where
  /-- Sets bisimilar up to a positive depth are empty together. -/
  empty_iff_of_bisim {k : ℕ} {first second : HF} (related : extensional.BisimUpTo (k + 1) first.1 second.1) :
      first.1 = ∅ ↔ second.1 = ∅ := by
    obtain ⟨forth, back⟩ := (extensional.bisimUpTo_succ_iff).mp related
    constructor
    · intro isEmpty
      refine (ZFSet.eq_empty _).mpr fun member inside => ?_
      obtain ⟨next, step, -⟩ := back .any member ⟨trivial, inside⟩
      rw [isEmpty] at step
      exact ZFSet.notMem_empty _ step.2
    · intro isEmpty
      refine (ZFSet.eq_empty _).mpr fun member inside => ?_
      obtain ⟨next, step, -⟩ := forth .any member ⟨trivial, inside⟩
      rw [isEmpty] at step
      exact ZFSet.notMem_empty _ step.2

/-! ## Steps back and sorts by finite search -/

variable {formula : Formula 0}

/-- A set containing `x` is bisimilar up to a positive stage `n` to `x` added to a subset of `V_n`. -/
theorem container_bisim_stage {n : ℕ} (positive : 1 ≤ n) {container x : ZFSet.{0}} (member : x ∈ container) :
    ∃ part ⊆ ZFSet.vonNeumann (n : Ordinal), extensional.BisimUpTo n container (insert x part) := by
  obtain ⟨part, within, related⟩ := container_bisim (n - 1) member
  have stage : n - 1 + 1 = n := Nat.sub_add_cancel positive
  rw [stage] at within related
  exact ⟨part, within, related⟩

/-- **Some set containing `x` has a two-way `ψ` of depth at most a positive stage `n` exactly when `x` added to some
subset of `V_n` has it.** -/
theorem twoWay_sometimeBefore_iff {label : StepLabel} (fragment : formula.twoWay = true) {n : ℕ} (positive : 1 ≤ n)
    (depth : formula.twoWayDepth ≤ n) (element : HF) :
    HFSets.sat Env.closed (.sometimeBefore label formula) element ↔
      memberLabel label ∧ ∃ part, ∃ within : part ⊆ ZFSet.vonNeumann (n : Ordinal),
        HFSets.sat Env.closed formula
          ⟨insert element.1 part, isHFSet_insert element.2 (isHFSet_of_subset_vonNeumann within)⟩ := by
  constructor
  · rintro ⟨previous, step, holds⟩
    obtain ⟨part, within, related⟩ := container_bisim_stage positive step.2
    exact ⟨step.1, part, within, (twoWay_sat_iff formula fragment n depth Env.closed related).mp holds⟩
  · rintro ⟨labelled, part, within, holds⟩
    exact ⟨_, ⟨labelled, ZFSet.mem_insert_iff.mpr (Or.inl rfl)⟩, holds⟩

/-- **Every set containing `x` has a two-way `ψ` of depth at most a positive stage `n` exactly when `x` added to
every subset of `V_n` has it.** -/
theorem twoWay_alwaysBefore_iff {label : StepLabel} (fragment : formula.twoWay = true) {n : ℕ} (positive : 1 ≤ n)
    (depth : formula.twoWayDepth ≤ n) (element : HF) :
    HFSets.sat Env.closed (.alwaysBefore label formula) element ↔
      (memberLabel label → ∀ part, ∀ within : part ⊆ ZFSet.vonNeumann (n : Ordinal),
        HFSets.sat Env.closed formula
          ⟨insert element.1 part, isHFSet_insert element.2 (isHFSet_of_subset_vonNeumann within)⟩) := by
  constructor
  · intro every labelled part within
    exact every _ ⟨labelled, ZFSet.mem_insert_iff.mpr (Or.inl rfl)⟩
  · intro every previous step
    obtain ⟨part, within, related⟩ := container_bisim_stage positive step.2
    exact (twoWay_sat_iff formula fragment n depth Env.closed related).mpr (every step.1 part within)

/-- **Some set of the sort has a two-way `ψ` of depth at most `d` exactly when some subset of `V_d` has it.** -/
theorem twoWay_someOf_iff (fragment : formula.twoWay = true) {d : ℕ} (depth : formula.twoWayDepth ≤ d)
    (element : HF) :
    HFSets.sat Env.closed (.someOf (.base "Set") formula) element ↔
      ∃ part, ∃ within : part ⊆ ZFSet.vonNeumann (d : Ordinal),
        HFSets.sat Env.closed formula ⟨part, isHFSet_of_subset_vonNeumann within⟩ := by
  constructor
  · rintro ⟨witness, -, holds⟩
    exact ⟨truncSet d witness.1, truncSet_subset d _,
      (twoWay_sat_iff formula fragment d depth Env.closed (second := ⟨truncSet d witness.1, _⟩)
        (bisim_truncSet d witness.1)).mp holds⟩
  · rintro ⟨part, within, holds⟩
    exact ⟨_, rfl, holds⟩

/-- **Every set of the sort has a two-way `ψ` of depth at most `d` exactly when every subset of `V_d` has it.** -/
theorem twoWay_everyOf_iff (fragment : formula.twoWay = true) {d : ℕ} (depth : formula.twoWayDepth ≤ d)
    (element : HF) :
    HFSets.sat Env.closed (.everyOf (.base "Set") formula) element ↔
      ∀ part, ∀ within : part ⊆ ZFSet.vonNeumann (d : Ordinal),
        HFSets.sat Env.closed formula ⟨part, isHFSet_of_subset_vonNeumann within⟩ := by
  constructor
  · intro every part within
    exact every _ rfl
  · intro every witness _
    exact (twoWay_sat_iff formula fragment d depth Env.closed (second := ⟨truncSet d witness.1, _⟩)
      (bisim_truncSet d witness.1)).mpr (every _ (truncSet_subset d _))

/-! ## The evaluation -/

/-- **The evaluation of a two-way formula at a hereditary term**: steps forward read the members, splits read the
coverings of the members, named sets compare sets, and steps back and sorts try the subsets of a finite stage. -/
def evalTwoWay : {n : ℕ} → Formula n → Pattern → Bool
  | _, .top, _ => true
  | _, .bot, _ => false
  | _, .empty kind, term => decide (kind = .hashSet) && (membersOf term).isEmpty
  | _, .nonEmpty kind, term => !(decide (kind = .hashSet) && (membersOf term).isEmpty)
  | _, .and left right, term => evalTwoWay left term && evalTwoWay right term
  | _, .or left right, term => evalTwoWay left term || evalTwoWay right term
  | _, .possibly label inner, term => decide (memberLabel label) && (membersOf term).any (evalTwoWay inner)
  | _, .necessarily label inner, term => !decide (memberLabel label) || (membersOf term).all (evalTwoWay inner)
  | _, .sometimeBefore label inner, term => decide (memberLabel label) &&
      (subsetTerms (max inner.twoWayDepth 1)).any fun part => evalTwoWay inner (insertTerm term part)
  | _, .alwaysBefore label inner, term => !decide (memberLabel label) ||
      (subsetTerms (max inner.twoWayDepth 1)).all fun part => evalTwoWay inner (insertTerm term part)
  | _, .is target, term => hereditary membership hfRule.category target && sameSet term target
  | _, .isNot target, term => !(hereditary membership hfRule.category target && sameSet term target)
  | _, .split kind left right, term => decide (kind = .hashSet) &&
      (coverings (membersOf term)).any fun parts => evalTwoWay left (set parts.1) && evalTwoWay right (set parts.2)
  | _, .everySplit kind left right, term => !decide (kind = .hashSet) ||
      (coverings (membersOf term)).all fun parts => evalTwoWay left (set parts.1) || evalTwoWay right (set parts.2)
  | _, .someOf (.base sort) inner, _ =>
      decide (sort = "Set") && (subsetTerms inner.twoWayDepth).any (evalTwoWay inner)
  | _, .everyOf (.base sort) inner, _ =>
      !decide (sort = "Set") || (subsetTerms inner.twoWayDepth).all (evalTwoWay inner)
  | _, _, _ => false

/-- The hereditarily finite set of a hereditary term. -/
def hfOf {term : Pattern} (holds : IsHF term) : HF := ⟨zfOf term, term, holds, rfl⟩

theorem mem_zfOf_hf {term : Pattern} (holds : IsHF term) {z : ZFSet.{0}} :
    z ∈ zfOf term ↔ ∃ member ∈ membersOf term, zfOf member = z := by
  rw [hf_eq_set holds, zfOf_set, mem_zfOfList]
  rfl

theorem hf_ext {first second : HF} (same : first.1 = second.1) : first = second := Subtype.ext same

theorem named_eval_iff {term target : Pattern} (holds : IsHF term) :
    (hereditary membership hfRule.category target && sameSet term target) = true ↔
      (IsHF target ∧ zfOf term = zfOf target) := by
  rw [Bool.and_eq_true]
  constructor
  · rintro ⟨hereditaryTarget, same⟩
    have targetHolds := (hereditary_iff target).mp hereditaryTarget
    exact ⟨targetHolds, (sameSet_iff term holds target targetHolds).mp same⟩
  · rintro ⟨targetHolds, same⟩
    exact ⟨(hereditary_iff target).mpr targetHolds, (sameSet_iff term holds target targetHolds).mpr same⟩

theorem hfSets_sat_congr {formula : Formula 0} {first second : HF} (same : first.1 = second.1) :
    HFSets.sat Env.closed formula first ↔ HFSets.sat Env.closed formula second := by
  rw [hf_ext same]

/-- **The evaluation is exact**, among the hereditarily finite sets. -/
theorem evalTwoWay_iff : ∀ (formula : Formula 0), formula.twoWay = true → ∀ {term : Pattern} (holds : IsHF term),
    evalTwoWay formula term = true ↔ HFSets.sat Env.closed formula (hfOf holds)
  | .top, _, _, _ => iff_of_true rfl trivial
  | .bot, _, _, _ => iff_of_false Bool.false_ne_true id
  | .empty kind, _, term, holds => by
    change (decide (kind = .hashSet) && (membersOf term).isEmpty) = true ↔ (kind = .hashSet ∧ zfOf term = ∅)
    rw [Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff, zfOf_eq_empty_iff holds]
  | .nonEmpty kind, _, term, holds => by
    change (!(decide (kind = .hashSet) && (membersOf term).isEmpty)) = true ↔ ¬ (kind = .hashSet ∧ zfOf term = ∅)
    rw [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not, List.isEmpty_eq_false_iff,
      zfOf_eq_empty_iff holds, not_and_or]
  | .and left right, fragment, term, holds => by
    simp only [Formula.twoWay, Bool.and_eq_true] at fragment
    simp only [evalTwoWay, Bool.and_eq_true]
    exact and_congr (evalTwoWay_iff left fragment.1 holds) (evalTwoWay_iff right fragment.2 holds)
  | .or left right, fragment, term, holds => by
    simp only [Formula.twoWay, Bool.and_eq_true] at fragment
    simp only [evalTwoWay, Bool.or_eq_true]
    exact or_congr (evalTwoWay_iff left fragment.1 holds) (evalTwoWay_iff right fragment.2 holds)
  | .possibly label inner, fragment, term, holds => by
    simp only [evalTwoWay, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
    constructor
    · rintro ⟨labelled, member, found, decided⟩
      have memberHolds := hf_members holds member found
      exact ⟨hfOf memberHolds, ⟨labelled, (mem_zfOf_hf holds).mpr ⟨member, found, rfl⟩⟩,
        (evalTwoWay_iff inner fragment memberHolds).mp decided⟩
    · rintro ⟨next, step, satisfied⟩
      obtain ⟨member, found, same⟩ := (mem_zfOf_hf holds).mp step.2
      have memberHolds := hf_members holds member found
      refine ⟨step.1, member, found, (evalTwoWay_iff inner fragment memberHolds).mpr ?_⟩
      rwa [show hfOf memberHolds = next from hf_ext same]
  | .necessarily label inner, fragment, term, holds => by
    simp only [evalTwoWay, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, List.all_eq_true]
    constructor
    · rintro (unlabelled | every) next step
      · exact absurd step.1 unlabelled
      · obtain ⟨member, found, same⟩ := (mem_zfOf_hf holds).mp step.2
        have memberHolds := hf_members holds member found
        rw [← show hfOf memberHolds = next from hf_ext same]
        exact (evalTwoWay_iff inner fragment memberHolds).mp (every member found)
    · intro every
      by_cases labelled : memberLabel label
      · refine Or.inr fun member found => ?_
        have memberHolds := hf_members holds member found
        exact (evalTwoWay_iff inner fragment memberHolds).mpr
          (every (hfOf memberHolds) ⟨labelled, (mem_zfOf_hf holds).mpr ⟨member, found, rfl⟩⟩)
      · exact Or.inl labelled
  | .sometimeBefore label inner, fragment, term, holds => by
    rw [twoWay_sometimeBefore_iff (formula := inner) fragment (le_max_right _ _) (le_max_left _ _)]
    simp only [evalTwoWay, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
    refine and_congr Iff.rfl ⟨?_, ?_⟩
    · rintro ⟨part, member, decided⟩
      have partHolds := subsetTerms_hf member
      have satisfied := (evalTwoWay_iff inner fragment (insertTerm_hf holds partHolds)).mp decided
      refine ⟨zfOf part, subset_iff_subsetTerms.mpr ⟨part, member, rfl⟩, ?_⟩
      exact (hfSets_sat_congr (zfOf_insertTerm term partHolds)).mp satisfied
    · rintro ⟨part, within, satisfied⟩
      obtain ⟨found, member, rfl⟩ := subset_iff_subsetTerms.mp within
      have partHolds := subsetTerms_hf member
      refine ⟨found, member, (evalTwoWay_iff inner fragment (insertTerm_hf holds partHolds)).mpr ?_⟩
      exact (hfSets_sat_congr (zfOf_insertTerm term partHolds)).mpr satisfied
  | .alwaysBefore label inner, fragment, term, holds => by
    rw [twoWay_alwaysBefore_iff (formula := inner) fragment (le_max_right _ _) (le_max_left _ _)]
    simp only [evalTwoWay, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, List.all_eq_true]
    constructor
    · rintro (unlabelled | every) labelled part within
      · exact absurd labelled unlabelled
      · obtain ⟨found, member, rfl⟩ := subset_iff_subsetTerms.mp within
        have partHolds := subsetTerms_hf member
        have satisfied := (evalTwoWay_iff inner fragment (insertTerm_hf holds partHolds)).mp (every found member)
        exact (hfSets_sat_congr (zfOf_insertTerm term partHolds)).mp satisfied
    · intro every
      by_cases labelled : memberLabel label
      · refine Or.inr fun part member => ?_
        have partHolds := subsetTerms_hf member
        refine (evalTwoWay_iff inner fragment (insertTerm_hf holds partHolds)).mpr ?_
        exact (hfSets_sat_congr (zfOf_insertTerm term partHolds)).mpr
          (every labelled _ (subset_iff_subsetTerms.mpr ⟨part, member, rfl⟩))
      · exact Or.inl labelled
  | .is target, _, term, holds => by
    change (hereditary membership hfRule.category target && sameSet term target) = true ↔
      (IsHF target ∧ zfOf term = zfOf target)
    exact named_eval_iff holds
  | .isNot target, _, term, holds => by
    change (!(hereditary membership hfRule.category target && sameSet term target)) = true ↔
      ¬ (IsHF target ∧ zfOf term = zfOf target)
    rw [Bool.not_eq_true', ← Bool.not_eq_true]
    exact not_congr (named_eval_iff holds)
  | .split kind left right, fragment, term, holds => by
    simp only [Formula.twoWay, Bool.and_eq_true] at fragment
    change ((decide (kind = .hashSet) && (coverings (membersOf term)).any fun parts =>
        evalTwoWay left (set parts.1) && evalTwoWay right (set parts.2)) = true) ↔
      ∃ first second : HF, (kind = .hashSet ∧ zfOf term = first.1 ∪ second.1) ∧
        HFSets.sat Env.closed left first ∧ HFSets.sat Env.closed right second
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
    constructor
    · rintro ⟨kinded, parts, member, decidedLeft, decidedRight⟩
      obtain ⟨leftHolds, rightHolds, union⟩ := covering_split holds member
      exact ⟨hfOf leftHolds, hfOf rightHolds, ⟨kinded, union⟩, (evalTwoWay_iff left fragment.1 leftHolds).mp decidedLeft,
        (evalTwoWay_iff right fragment.2 rightHolds).mp decidedRight⟩
    · rintro ⟨first, second, ⟨kinded, union⟩, holdsLeft, holdsRight⟩
      obtain ⟨parts, member, sameFirst, sameSecond⟩ := split_covering holds union
      obtain ⟨leftHolds, rightHolds, -⟩ := covering_split holds member
      refine ⟨kinded, parts, member, (evalTwoWay_iff left fragment.1 leftHolds).mpr ?_,
        (evalTwoWay_iff right fragment.2 rightHolds).mpr ?_⟩
      · rwa [show hfOf leftHolds = first from hf_ext sameFirst]
      · rwa [show hfOf rightHolds = second from hf_ext sameSecond]
  | .everySplit kind left right, fragment, term, holds => by
    simp only [Formula.twoWay, Bool.and_eq_true] at fragment
    change ((!decide (kind = .hashSet) || (coverings (membersOf term)).all fun parts =>
        evalTwoWay left (set parts.1) || evalTwoWay right (set parts.2)) = true) ↔
      ∀ first second : HF, (kind = .hashSet ∧ zfOf term = first.1 ∪ second.1) →
        HFSets.sat Env.closed left first ∨ HFSets.sat Env.closed right second
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, List.all_eq_true]
    constructor
    · rintro (unkinded | every) first second ⟨kinded, union⟩
      · exact absurd kinded unkinded
      · obtain ⟨parts, member, sameFirst, sameSecond⟩ := split_covering holds union
        obtain ⟨leftHolds, rightHolds, -⟩ := covering_split holds member
        rcases every parts member with decidedLeft | decidedRight
        · left
          rw [← show hfOf leftHolds = first from hf_ext sameFirst]
          exact (evalTwoWay_iff left fragment.1 leftHolds).mp decidedLeft
        · right
          rw [← show hfOf rightHolds = second from hf_ext sameSecond]
          exact (evalTwoWay_iff right fragment.2 rightHolds).mp decidedRight
    · intro every
      by_cases kinded : kind = .hashSet
      · refine Or.inr fun parts member => ?_
        obtain ⟨leftHolds, rightHolds, union⟩ := covering_split holds member
        rcases every (hfOf leftHolds) (hfOf rightHolds) ⟨kinded, union⟩ with holdsLeft | holdsRight
        · exact Or.inl ((evalTwoWay_iff left fragment.1 leftHolds).mpr holdsLeft)
        · exact Or.inr ((evalTwoWay_iff right fragment.2 rightHolds).mpr holdsRight)
      · exact Or.inl kinded
  | .someOf (.base sort) inner, fragment, term, holds => by
    by_cases isSet : sort = "Set"
    · subst isSet
      rw [twoWay_someOf_iff (formula := inner) fragment (d := inner.twoWayDepth) le_rfl]
      simp only [evalTwoWay, decide_true, Bool.true_and, List.any_eq_true]
      constructor
      · rintro ⟨part, member, decided⟩
        exact ⟨zfOf part, subset_iff_subsetTerms.mpr ⟨part, member, rfl⟩,
          (evalTwoWay_iff inner fragment (subsetTerms_hf member)).mp decided⟩
      · rintro ⟨part, within, satisfied⟩
        obtain ⟨found, member, rfl⟩ := subset_iff_subsetTerms.mp within
        exact ⟨found, member, (evalTwoWay_iff inner fragment (subsetTerms_hf member)).mpr satisfied⟩
    · simp only [evalTwoWay, isSet, decide_false, Bool.false_and, Bool.false_eq_true, false_iff]
      rintro ⟨witness, typed, -⟩
      exact isSet typed
  | .everyOf (.base sort) inner, fragment, term, holds => by
    by_cases isSet : sort = "Set"
    · subst isSet
      rw [twoWay_everyOf_iff (formula := inner) fragment (d := inner.twoWayDepth) le_rfl]
      simp only [evalTwoWay, decide_true, Bool.not_true, Bool.false_or, List.all_eq_true]
      constructor
      · intro every part within
        obtain ⟨found, member, rfl⟩ := subset_iff_subsetTerms.mp within
        exact (evalTwoWay_iff inner fragment (subsetTerms_hf member)).mp (every found member)
      · intro every part member
        exact (evalTwoWay_iff inner fragment (subsetTerms_hf member)).mpr
          (every _ (subset_iff_subsetTerms.mpr ⟨part, member, rfl⟩))
    · simp only [evalTwoWay, isSet, decide_false, Bool.not_false, Bool.true_or, true_iff]
      intro witness typed
      exact absurd typed isSet
  | .someOf (.collection _ _) _, fragment, _, _ | .someOf (.arrow _ _) _, fragment, _, _
  | .someOf (.multiBinder _) _, fragment, _, _ | .everyOf (.collection _ _) _, fragment, _, _
  | .everyOf (.arrow _ _) _, fragment, _, _ | .everyOf (.multiBinder _) _, fragment, _, _
  | .var _, fragment, _, _ | .typed _, fragment, _, _
  | .untyped _, fragment, _, _ | .mu _, fragment, _, _ | .nu _, fragment, _, _ | .single _ _, fragment, _, _
  | .everySingle _ _, fragment, _, _ | .atLeast _ _ _ _, fragment, _, _ | .allButFewer _ _ _ _, fragment, _, _
  | .built _ _, fragment, _, _ | .everyBuilt _ _, fragment, _, _
  | .body _, fragment, _, _ | .everyBody _, fragment, _, _
  | .multiBody _ _, fragment, _, _ | .everyMultiBody _ _, fragment, _, _ | .bound _, fragment, _, _
  | .notBound _, fragment, _, _ | .mapsAll _ _, fragment, _, _ | .mapsSome _ _, fragment, _, _ =>
    absurd fragment Bool.false_ne_true

/-- **The truth of a two-way native type at a hereditary term, read among the hereditary terms, is decided by the
evaluation.** -/
theorem twoWay_decide (fragment : formula.twoWay = true) (free : formula.contextFree = true) {term : Pattern}
    (holds : IsHF term) : evalTwoWay formula term = true ↔ HFNative.sat Env.closed formula ⟨term, holds⟩ :=
  (evalTwoWay_iff formula fragment holds).trans (sat_iff_hfSets formula free ⟨term, holds⟩).symm

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

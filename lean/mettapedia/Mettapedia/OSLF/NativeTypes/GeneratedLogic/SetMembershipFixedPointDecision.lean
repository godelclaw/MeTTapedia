import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipFixedPoints

/-!
# Guarded native types of the hereditarily finite sets are decidable

The evaluation `evalGuarded` decides every guarded formula (`Formula.guarded`) at a hereditary term, read among the
hereditarily finite sets (`guarded_decide`). It covers the two-way formulas and nested fixed points.

- **Fixed points by height** (`fixIter`): a fixed point at a term is its body iterated as many times as the term's
  height, starting from nothing. The body reads the fixed point's own variable only under a step forward, so at lower
  sets, where fewer iterations suffice; the least and the greatest fixed point agree on the hereditarily finite sets.
  Variables of enclosing binders that occur at the top of a body are read at the term itself, which their own iteration
  already covers (`Reads`).
- **Steps back and sorts by a finite stage**: by `sometimeBefore_guarded_iff` and its duals, a step back tries `x` with
  every subset of `V_(2^m)`, for the `m` entries of the body's closure (`guardedBound`), and a sort tries every set of
  that stage.

The evaluation is exact (`evalWith_iff`). The bound is doubly exponential, so it decides without being practical.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Each former at a hereditary term -/

/-! ## Heights of parts -/

theorem heightList_le_of_subset : ∀ {values others : List Pattern}, (∀ value ∈ values, value ∈ others) →
    heightList values ≤ heightList others
  | [], _, _ => Nat.zero_le _
  | value :: values, others, within => by
    rw [heightList]
    exact max_le (height_le_heightList (within value List.mem_cons_self))
      (heightList_le_of_subset fun other found => within other (List.mem_cons_of_mem _ found))

/-- A part of a term is no higher than the term. -/
theorem height_set_le {term : Pattern} (holds : IsHF term) {values : List Pattern}
    (within : ∀ value ∈ values, value ∈ membersOf term) : height (set values) ≤ height term := by
  rw [hf_eq_set holds]
  exact Nat.succ_le_succ (heightList_le_of_subset within)

theorem possibly_hf_iff {label : StepLabel} {inner : Formula 0} {term : Pattern} (holds : IsHF term)
    {decides : Pattern → Bool}
    (each : ∀ member ∈ membersOf term, ∀ memberHolds : IsHF member,
      (decides member = true ↔ HFSets.sat Env.closed inner (hfOf memberHolds))) :
    (decide (memberLabel label) && (membersOf term).any decides) = true ↔
      HFSets.sat Env.closed (.possibly label inner) (hfOf holds) := by
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
  constructor
  · rintro ⟨labelled, member, found, decided⟩
    have memberHolds := hf_members holds member found
    exact ⟨hfOf memberHolds, ⟨labelled, (mem_zfOf_hf holds).mpr ⟨member, found, rfl⟩⟩,
      (each member found memberHolds).mp decided⟩
  · rintro ⟨next, step, satisfied⟩
    obtain ⟨member, found, same⟩ := (mem_zfOf_hf holds).mp step.2
    have memberHolds := hf_members holds member found
    refine ⟨step.1, member, found, (each member found memberHolds).mpr ?_⟩
    rwa [show hfOf memberHolds = next from hf_ext same]

theorem necessarily_hf_iff {label : StepLabel} {inner : Formula 0} {term : Pattern} (holds : IsHF term)
    {decides : Pattern → Bool}
    (each : ∀ member ∈ membersOf term, ∀ memberHolds : IsHF member,
      (decides member = true ↔ HFSets.sat Env.closed inner (hfOf memberHolds))) :
    (!decide (memberLabel label) || (membersOf term).all decides) = true ↔
      HFSets.sat Env.closed (.necessarily label inner) (hfOf holds) := by
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, List.all_eq_true]
  constructor
  · rintro (unlabelled | every) next step
    · exact absurd step.1 unlabelled
    · obtain ⟨member, found, same⟩ := (mem_zfOf_hf holds).mp step.2
      have memberHolds := hf_members holds member found
      rw [← show hfOf memberHolds = next from hf_ext same]
      exact (each member found memberHolds).mp (every member found)
  · intro every
    by_cases labelled : memberLabel label
    · refine Or.inr fun member found => ?_
      have memberHolds := hf_members holds member found
      exact (each member found memberHolds).mpr
        (every (hfOf memberHolds) ⟨labelled, (mem_zfOf_hf holds).mpr ⟨member, found, rfl⟩⟩)
    · exact Or.inl labelled

theorem split_hf_iff {kind : CollType} {left right : Formula 0} {term : Pattern} (holds : IsHF term)
    {decideLeft decideRight : Pattern → Bool}
    (eachLeft : ∀ parts ∈ coverings (membersOf term), ∀ partHolds : IsHF (set parts.1),
      (decideLeft (set parts.1) = true ↔ HFSets.sat Env.closed left (hfOf partHolds)))
    (eachRight : ∀ parts ∈ coverings (membersOf term), ∀ partHolds : IsHF (set parts.2),
      (decideRight (set parts.2) = true ↔ HFSets.sat Env.closed right (hfOf partHolds))) :
    (decide (kind = .hashSet) && (coverings (membersOf term)).any fun parts =>
        decideLeft (set parts.1) && decideRight (set parts.2)) = true ↔
      HFSets.sat Env.closed (.split kind left right) (hfOf holds) := by
  change _ ↔ ∃ first second : HF, (kind = .hashSet ∧ zfOf term = first.1 ∪ second.1) ∧
    HFSets.sat Env.closed left first ∧ HFSets.sat Env.closed right second
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
  constructor
  · rintro ⟨kinded, parts, member, decidedLeft, decidedRight⟩
    obtain ⟨leftHolds, rightHolds, union⟩ := covering_split holds member
    exact ⟨hfOf leftHolds, hfOf rightHolds, ⟨kinded, union⟩, (eachLeft parts member leftHolds).mp decidedLeft,
      (eachRight parts member rightHolds).mp decidedRight⟩
  · rintro ⟨first, second, ⟨kinded, union⟩, holdsLeft, holdsRight⟩
    obtain ⟨parts, member, sameFirst, sameSecond⟩ := split_covering holds union
    obtain ⟨leftHolds, rightHolds, -⟩ := covering_split holds member
    refine ⟨kinded, parts, member, (eachLeft parts member leftHolds).mpr ?_, (eachRight parts member rightHolds).mpr ?_⟩
    · rwa [show hfOf leftHolds = first from hf_ext sameFirst]
    · rwa [show hfOf rightHolds = second from hf_ext sameSecond]

theorem everySplit_hf_iff {kind : CollType} {left right : Formula 0} {term : Pattern} (holds : IsHF term)
    {decideLeft decideRight : Pattern → Bool}
    (eachLeft : ∀ parts ∈ coverings (membersOf term), ∀ partHolds : IsHF (set parts.1),
      (decideLeft (set parts.1) = true ↔ HFSets.sat Env.closed left (hfOf partHolds)))
    (eachRight : ∀ parts ∈ coverings (membersOf term), ∀ partHolds : IsHF (set parts.2),
      (decideRight (set parts.2) = true ↔ HFSets.sat Env.closed right (hfOf partHolds))) :
    (!decide (kind = .hashSet) || (coverings (membersOf term)).all fun parts =>
        decideLeft (set parts.1) || decideRight (set parts.2)) = true ↔
      HFSets.sat Env.closed (.everySplit kind left right) (hfOf holds) := by
  change _ ↔ ∀ first second : HF, (kind = .hashSet ∧ zfOf term = first.1 ∪ second.1) →
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
        exact (eachLeft parts member leftHolds).mp decidedLeft
      · right
        rw [← show hfOf rightHolds = second from hf_ext sameSecond]
        exact (eachRight parts member rightHolds).mp decidedRight
  · intro every
    by_cases kinded : kind = .hashSet
    · refine Or.inr fun parts member => ?_
      obtain ⟨leftHolds, rightHolds, union⟩ := covering_split holds member
      rcases every (hfOf leftHolds) (hfOf rightHolds) ⟨kinded, union⟩ with holdsLeft | holdsRight
      · exact Or.inl ((eachLeft parts member leftHolds).mpr holdsLeft)
      · exact Or.inr ((eachRight parts member rightHolds).mpr holdsRight)
    · exact Or.inl kinded

theorem part_height_le {term : Pattern} (holds : IsHF term) {parts : List Pattern × List Pattern}
    (member : parts ∈ coverings (membersOf term)) :
    height (set parts.1) ≤ height term ∧ height (set parts.2) ≤ height term := by
  obtain ⟨left, right, -⟩ := mem_coverings_parts member
  exact ⟨height_set_le holds left, height_set_le holds right⟩

theorem empty_hf_iff {kind : CollType} {term : Pattern} (holds : IsHF term) :
    (decide (kind = .hashSet) && (membersOf term).isEmpty) = true ↔
      HFSets.sat Env.closed (.empty kind) (hfOf holds) := by
  change _ ↔ (kind = .hashSet ∧ zfOf term = ∅)
  rw [Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff, zfOf_eq_empty_iff holds]

theorem nonEmpty_hf_iff {kind : CollType} {term : Pattern} (holds : IsHF term) :
    (!(decide (kind = .hashSet) && (membersOf term).isEmpty)) = true ↔
      HFSets.sat Env.closed (.nonEmpty kind) (hfOf holds) := by
  change _ ↔ ¬ (kind = .hashSet ∧ zfOf term = ∅)
  rw [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not, List.isEmpty_eq_false_iff,
    zfOf_eq_empty_iff holds, not_and_or]

theorem is_hf_iff {target term : Pattern} (holds : IsHF term) :
    (hereditary membership hfRule.category target && sameSet term target) = true ↔
      HFSets.sat Env.closed (.is target) (hfOf holds) :=
  named_eval_iff holds

theorem isNot_hf_iff {target term : Pattern} (holds : IsHF term) :
    (!(hereditary membership hfRule.category target && sameSet term target)) = true ↔
      HFSets.sat Env.closed (.isNot target) (hfOf holds) := by
  change _ ↔ ¬ (IsHF target ∧ zfOf term = zfOf target)
  rw [Bool.not_eq_true', ← Bool.not_eq_true]
  exact not_congr (named_eval_iff holds)

theorem mem_stage_iff_term {k : ℕ} {z : ZFSet.{0}} :
    z ∈ stage k ↔ ∃ value ∈ membersOf (vonNeumannTerm k), zfOf value = z := by
  rw [stage, ← zfOf_vonNeumannTerm]
  exact mem_zfOf_hf (vonNeumannTerm_hf k)


/-! ## The evaluation -/

/-- **A predicate iterated from nothing**: the step applied `k` times to the predicate that holds nowhere. -/
def fixIter (step : (Pattern → Bool) → Pattern → Bool) : ℕ → Pattern → Bool
  | 0 => fun _ => false
  | k + 1 => step (fixIter step k)

/-- **The evaluation of a formula** at a hereditary term, with the free variables read by `read`: steps forward read
the members, splits the coverings of the members, named sets compare sets, steps back and sorts try the subsets of a
finite stage, and fixed points iterate their bodies as often as the term's height. -/
def evalWith : {n : ℕ} → (Fin n → Pattern → Bool) → Formula n → Pattern → Bool
  | _, _, .top, _ => true
  | _, _, .bot, _ => false
  | _, read, .var index, term => read index term
  | _, _, .empty kind, term => decide (kind = .hashSet) && (membersOf term).isEmpty
  | _, _, .nonEmpty kind, term => !(decide (kind = .hashSet) && (membersOf term).isEmpty)
  | _, read, .and left right, term => evalWith read left term && evalWith read right term
  | _, read, .or left right, term => evalWith read left term || evalWith read right term
  | _, read, .possibly label inner, term =>
    decide (memberLabel label) && (membersOf term).any (evalWith read inner)
  | _, read, .necessarily label inner, term =>
    !decide (memberLabel label) || (membersOf term).all (evalWith read inner)
  | _, read, .sometimeBefore label inner, term => decide (memberLabel label) &&
      (subsetTerms (guardedBound inner)).any fun part => evalWith read inner (insertTerm term part)
  | _, read, .alwaysBefore label inner, term => !decide (memberLabel label) ||
      (subsetTerms (guardedBound inner)).all fun part => evalWith read inner (insertTerm term part)
  | _, _, .is target, term => hereditary membership hfRule.category target && sameSet term target
  | _, _, .isNot target, term => !(hereditary membership hfRule.category target && sameSet term target)
  | _, read, .split kind left right, term => decide (kind = .hashSet) &&
      (coverings (membersOf term)).any fun parts => evalWith read left (set parts.1) && evalWith read right (set parts.2)
  | _, read, .everySplit kind left right, term => !decide (kind = .hashSet) ||
      (coverings (membersOf term)).all fun parts => evalWith read left (set parts.1) || evalWith read right (set parts.2)
  | _, read, .someOf (.base sort) inner, _ =>
      decide (sort = "Set") && (membersOf (vonNeumannTerm (guardedBound inner))).any (evalWith read inner)
  | _, read, .everyOf (.base sort) inner, _ =>
      !decide (sort = "Set") || (membersOf (vonNeumannTerm (guardedBound inner))).all (evalWith read inner)
  | _, read, .mu inner, term =>
    fixIter (fun below => evalWith (Fin.cons below read : Fin (_ + 1) → Pattern → Bool) inner) (height term) term
  | _, read, .nu inner, term =>
    fixIter (fun below => evalWith (Fin.cons below read : Fin (_ + 1) → Pattern → Bool) inner) (height term) term
  | _, _, _, _ => false

/-- **The evaluation of a closed formula.** -/
def evalGuarded (formula : Formula 0) (term : Pattern) : Bool := evalWith Fin.elim0 formula term

/-- **What the variables read**: those that may occur here read their instances at sets no higher than the bound, and
those that may occur under a step forward at lower sets. -/
def Reads {n : ℕ} (now later : Fin n → Bool) (u : Fin n → Formula 0) (read : Fin n → Pattern → Bool) (bound : ℕ) :
    Prop :=
  ∀ index (other : Pattern) (holds : IsHF other),
    (now index = true ∧ height other ≤ bound ∨ later index = true ∧ height other < bound) →
      (read index other = true ↔ HFSets.sat Env.closed (u index) (hfOf holds))

theorem Reads.below {n : ℕ} {now later : Fin n → Bool} {u : Fin n → Formula 0} {read : Fin n → Pattern → Bool}
    {bound bound' : ℕ} (reads : Reads now later u read bound) (le : bound' ≤ bound) :
    Reads now later u read bound' := by
  intro index other holds condition
  refine reads index other holds ?_
  rcases condition with ⟨allowed, high⟩ | ⟨allowed, high⟩
  · exact .inl ⟨allowed, high.trans le⟩
  · exact .inr ⟨allowed, lt_of_lt_of_le high le⟩

/-- Under a step forward, what may occur later may occur now. -/
theorem Reads.forward {n : ℕ} {now later : Fin n → Bool} {u : Fin n → Formula 0} {read : Fin n → Pattern → Bool}
    {bound bound' : ℕ} (reads : Reads now later u read bound) (lower : bound' < bound) :
    Reads later later u read bound' := by
  intro index other holds condition
  refine reads index other holds (.inr ?_)
  rcases condition with ⟨allowed, high⟩ | ⟨allowed, high⟩
  · exact ⟨allowed, lt_of_le_of_lt high lower⟩
  · exact ⟨allowed, high.trans lower⟩

/-- Where no variable may occur, nothing needs to be read. -/
theorem reads_none {n : ℕ} (u : Fin n → Formula 0) (read : Fin n → Pattern → Bool) (bound : ℕ) :
    Reads (fun _ => false) (fun _ => false) u read bound := by
  rintro index other holds (⟨never, -⟩ | ⟨never, -⟩) <;> exact absurd never Bool.false_ne_true

/-- **The evaluation is exact**, when the variables read their instances as far as they may be read. -/
theorem evalWith_iff : ∀ {n : ℕ} (now later : Fin n → Bool) (u : Fin n → Formula 0) (read : Fin n → Pattern → Bool)
    (formula : Formula n), formula.guardedIn now later = true → ∀ {term : Pattern} (holds : IsHF term),
      Reads now later u read (height term) →
        (evalWith read formula term = true ↔ HFSets.sat Env.closed (formula.subst u) (hfOf holds))
  | _, _, _, _, _, .top, _, _, _, _ => iff_of_true rfl trivial
  | _, _, _, _, _, .bot, _, _, _, _ => iff_of_false Bool.false_ne_true id
  | _, _, _, _, _, .var index, ok, term, holds, reads => reads index term holds (.inl ⟨ok, le_rfl⟩)
  | _, _, _, _, _, .empty kind, _, _, holds, _ => empty_hf_iff holds
  | _, _, _, _, _, .nonEmpty kind, _, _, holds, _ => nonEmpty_hf_iff holds
  | _, _, _, _, _, .is target, _, _, holds, _ => is_hf_iff holds
  | _, _, _, _, _, .isNot target, _, _, holds, _ => isNot_hf_iff holds
  | _, now, later, u, read, .and left right, ok, _, holds, reads => by
    simp only [Formula.guardedIn, Bool.and_eq_true] at ok
    simp only [evalWith, Bool.and_eq_true]
    exact and_congr (evalWith_iff now later u read left ok.1 holds reads)
      (evalWith_iff now later u read right ok.2 holds reads)
  | _, now, later, u, read, .or left right, ok, _, holds, reads => by
    simp only [Formula.guardedIn, Bool.and_eq_true] at ok
    simp only [evalWith, Bool.or_eq_true]
    exact or_congr (evalWith_iff now later u read left ok.1 holds reads)
      (evalWith_iff now later u read right ok.2 holds reads)
  | _, now, later, u, read, .possibly label inner, ok, _, holds, reads => by
    simp only [evalWith]
    exact possibly_hf_iff holds fun member found memberHolds =>
      evalWith_iff later later u read inner ok memberHolds (reads.forward (height_lt_of_mem found))
  | _, now, later, u, read, .necessarily label inner, ok, _, holds, reads => by
    simp only [evalWith]
    exact necessarily_hf_iff holds fun member found memberHolds =>
      evalWith_iff later later u read inner ok memberHolds (reads.forward (height_lt_of_mem found))
  | _, now, later, u, read, .split kind left right, ok, _, holds, reads => by
    simp only [Formula.guardedIn, Bool.and_eq_true] at ok
    simp only [evalWith]
    exact split_hf_iff holds
      (fun parts member partHolds => evalWith_iff now later u read left ok.1 partHolds
        (reads.below (part_height_le holds member).1))
      (fun parts member partHolds => evalWith_iff now later u read right ok.2 partHolds
        (reads.below (part_height_le holds member).2))
  | _, now, later, u, read, .everySplit kind left right, ok, _, holds, reads => by
    simp only [Formula.guardedIn, Bool.and_eq_true] at ok
    simp only [evalWith]
    exact everySplit_hf_iff holds
      (fun parts member partHolds => evalWith_iff now later u read left ok.1 partHolds
        (reads.below (part_height_le holds member).1))
      (fun parts member partHolds => evalWith_iff now later u read right ok.2 partHolds
        (reads.below (part_height_le holds member).2))
  | _, _, _, u, read, .sometimeBefore label inner, ok, term, holds, _ => by
    have inside : ∀ {part : Pattern} (partHolds : IsHF part),
        evalWith read inner (insertTerm term part) = true ↔
          HFSets.sat Env.closed (inner.subst u) (hfOf (insertTerm_hf holds partHolds)) := fun partHolds =>
      evalWith_iff _ _ u read inner ok (insertTerm_hf holds partHolds) (reads_none u read _)
    change _ ↔ HFSets.sat Env.closed (.sometimeBefore label (inner.subst u)) (hfOf holds)
    rw [sometimeBefore_guarded_iff u ok]
    simp only [evalWith, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
    refine and_congr Iff.rfl ⟨?_, ?_⟩
    · rintro ⟨part, member, decided⟩
      have partHolds := subsetTerms_hf member
      exact ⟨zfOf part, subset_iff_subsetTerms.mpr ⟨part, member, rfl⟩,
        (hfSets_sat_congr (zfOf_insertTerm term partHolds)).mp ((inside partHolds).mp decided)⟩
    · rintro ⟨part, within, satisfied⟩
      obtain ⟨found, member, rfl⟩ := subset_iff_subsetTerms.mp within
      have partHolds := subsetTerms_hf member
      exact ⟨found, member, (inside partHolds).mpr ((hfSets_sat_congr (zfOf_insertTerm term partHolds)).mpr satisfied)⟩
  | _, _, _, u, read, .alwaysBefore label inner, ok, term, holds, _ => by
    have inside : ∀ {part : Pattern} (partHolds : IsHF part),
        evalWith read inner (insertTerm term part) = true ↔
          HFSets.sat Env.closed (inner.subst u) (hfOf (insertTerm_hf holds partHolds)) := fun partHolds =>
      evalWith_iff _ _ u read inner ok (insertTerm_hf holds partHolds) (reads_none u read _)
    change _ ↔ HFSets.sat Env.closed (.alwaysBefore label (inner.subst u)) (hfOf holds)
    rw [alwaysBefore_guarded_iff u ok]
    simp only [evalWith, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, List.all_eq_true]
    constructor
    · rintro (unlabelled | every) labelled part within
      · exact absurd labelled unlabelled
      · obtain ⟨found, member, rfl⟩ := subset_iff_subsetTerms.mp within
        have partHolds := subsetTerms_hf member
        exact (hfSets_sat_congr (zfOf_insertTerm term partHolds)).mp ((inside partHolds).mp (every found member))
    · intro every
      by_cases labelled : memberLabel label
      · refine Or.inr fun part member => ?_
        have partHolds := subsetTerms_hf member
        exact (inside partHolds).mpr ((hfSets_sat_congr (zfOf_insertTerm term partHolds)).mpr
          (every labelled _ (subset_iff_subsetTerms.mpr ⟨part, member, rfl⟩)))
      · exact Or.inl labelled
  | _, _, _, u, read, .someOf (.base sort) inner, ok, _, holds, _ => by
    have inside : ∀ {value : Pattern} (valueHolds : IsHF value),
        evalWith read inner value = true ↔ HFSets.sat Env.closed (inner.subst u) (hfOf valueHolds) := fun valueHolds =>
      evalWith_iff _ _ u read inner ok valueHolds (reads_none u read _)
    change _ ↔ HFSets.sat Env.closed (.someOf (.base sort) (inner.subst u)) (hfOf holds)
    by_cases isSet : sort = "Set"
    · subst isSet
      rw [someOf_guarded_iff u ok]
      simp only [evalWith, decide_true, Bool.true_and, List.any_eq_true]
      constructor
      · rintro ⟨value, member, decided⟩
        have valueHolds := hf_members (vonNeumannTerm_hf _) value member
        exact ⟨hfOf valueHolds, mem_stage_iff_term.mpr ⟨value, member, rfl⟩, (inside valueHolds).mp decided⟩
      · rintro ⟨y, found, satisfied⟩
        obtain ⟨value, member, same⟩ := mem_stage_iff_term.mp found
        have valueHolds := hf_members (vonNeumannTerm_hf _) value member
        refine ⟨value, member, (inside valueHolds).mpr ?_⟩
        rwa [show hfOf valueHolds = y from hf_ext same]
    · simp only [evalWith, isSet, decide_false, Bool.false_and, Bool.false_eq_true, false_iff]
      rintro ⟨witness, typed, -⟩
      exact isSet typed
  | _, _, _, u, read, .everyOf (.base sort) inner, ok, _, holds, _ => by
    have inside : ∀ {value : Pattern} (valueHolds : IsHF value),
        evalWith read inner value = true ↔ HFSets.sat Env.closed (inner.subst u) (hfOf valueHolds) := fun valueHolds =>
      evalWith_iff _ _ u read inner ok valueHolds (reads_none u read _)
    change _ ↔ HFSets.sat Env.closed (.everyOf (.base sort) (inner.subst u)) (hfOf holds)
    by_cases isSet : sort = "Set"
    · subst isSet
      rw [everyOf_guarded_iff u ok]
      simp only [evalWith, decide_true, Bool.not_true, Bool.false_or, List.all_eq_true]
      constructor
      · intro every y found
        obtain ⟨value, member, same⟩ := mem_stage_iff_term.mp found
        have valueHolds := hf_members (vonNeumannTerm_hf _) value member
        rw [← show hfOf valueHolds = y from hf_ext same]
        exact (inside valueHolds).mp (every value member)
      · intro every value member
        have valueHolds := hf_members (vonNeumannTerm_hf _) value member
        exact (inside valueHolds).mpr (every (hfOf valueHolds) (mem_stage_iff_term.mpr ⟨value, member, rfl⟩))
    · simp only [evalWith, isSet, decide_false, Bool.not_false, Bool.true_or, true_iff]
      intro witness typed
      exact absurd typed isSet
  | _, now, later, u, read, .mu inner, ok, term, holds, reads => by
    simp only [evalWith]
    have iterate : ∀ (fuel : ℕ) {other : Pattern} (otherHolds : IsHF other), height other ≤ fuel →
        height other ≤ height term →
          (fixIter (fun below => evalWith (Fin.cons below read : Fin (_ + 1) → Pattern → Bool) inner) fuel other =
            true ↔ HFSets.sat Env.closed ((Formula.mu inner).subst u) (hfOf otherHolds)) := by
      intro fuel
      induction fuel with
      | zero => exact fun otherHolds enough _ => absurd enough (Nat.not_le.mpr (hf_height_pos otherHolds))
      | succ fuel previous =>
        intro other otherHolds enough below
        simp only [fixIter]
        rw [sat_subst_mu]
        refine evalWith_iff (Fin.cons false now : Fin (_ + 1) → Bool) (Fin.cons true later : Fin (_ + 1) → Bool)
          (Fin.cons ((Formula.mu inner).subst u) u : Fin (_ + 1) → Formula 0) _ inner ok otherHolds ?_
        intro index another anotherHolds condition
        induction index using Fin.cases with
        | zero =>
          simp only [Fin.cons_zero] at condition ⊢
          rcases condition with ⟨never, -⟩ | ⟨-, lower⟩
          · exact absurd never Bool.false_ne_true
          · exact previous anotherHolds (by omega) (by omega)
        | succ index =>
          simp only [Fin.cons_succ] at condition ⊢
          refine reads index another anotherHolds ?_
          rcases condition with ⟨allowed, high⟩ | ⟨allowed, high⟩
          · exact .inl ⟨allowed, high.trans below⟩
          · exact .inr ⟨allowed, lt_of_lt_of_le high below⟩
    exact iterate (height term) holds le_rfl le_rfl
  | _, now, later, u, read, .nu inner, ok, term, holds, reads => by
    simp only [evalWith]
    have iterate : ∀ (fuel : ℕ) {other : Pattern} (otherHolds : IsHF other), height other ≤ fuel →
        height other ≤ height term →
          (fixIter (fun below => evalWith (Fin.cons below read : Fin (_ + 1) → Pattern → Bool) inner) fuel other =
            true ↔ HFSets.sat Env.closed ((Formula.nu inner).subst u) (hfOf otherHolds)) := by
      intro fuel
      induction fuel with
      | zero => exact fun otherHolds enough _ => absurd enough (Nat.not_le.mpr (hf_height_pos otherHolds))
      | succ fuel previous =>
        intro other otherHolds enough below
        simp only [fixIter]
        rw [sat_subst_nu]
        refine evalWith_iff (Fin.cons false now : Fin (_ + 1) → Bool) (Fin.cons true later : Fin (_ + 1) → Bool)
          (Fin.cons ((Formula.nu inner).subst u) u : Fin (_ + 1) → Formula 0) _ inner ok otherHolds ?_
        intro index another anotherHolds condition
        induction index using Fin.cases with
        | zero =>
          simp only [Fin.cons_zero] at condition ⊢
          rcases condition with ⟨never, -⟩ | ⟨-, lower⟩
          · exact absurd never Bool.false_ne_true
          · exact previous anotherHolds (by omega) (by omega)
        | succ index =>
          simp only [Fin.cons_succ] at condition ⊢
          refine reads index another anotherHolds ?_
          rcases condition with ⟨allowed, high⟩ | ⟨allowed, high⟩
          · exact .inl ⟨allowed, high.trans below⟩
          · exact .inr ⟨allowed, lt_of_lt_of_le high below⟩
    exact iterate (height term) holds le_rfl le_rfl
  | _, _, _, _, _, .typed _, ok, _, _, _ | _, _, _, _, _, .untyped _, ok, _, _, _
  | _, _, _, _, _, .single _ _, ok, _, _, _ | _, _, _, _, _, .everySingle _ _, ok, _, _, _
  | _, _, _, _, _, .atLeast _ _ _ _, ok, _, _, _ | _, _, _, _, _, .allButFewer _ _ _ _, ok, _, _, _
  | _, _, _, _, _, .built _ _, ok, _, _, _ | _, _, _, _, _, .everyBuilt _ _, ok, _, _, _
  | _, _, _, _, _, .body _, ok, _, _, _ | _, _, _, _, _, .everyBody _, ok, _, _, _
  | _, _, _, _, _, .multiBody _ _, ok, _, _, _ | _, _, _, _, _, .everyMultiBody _ _, ok, _, _, _
  | _, _, _, _, _, .bound _, ok, _, _, _ | _, _, _, _, _, .notBound _, ok, _, _, _
  | _, _, _, _, _, .mapsAll _ _, ok, _, _, _ | _, _, _, _, _, .mapsSome _ _, ok, _, _, _
  | _, _, _, _, _, .someOf (.collection _ _) _, ok, _, _, _ | _, _, _, _, _, .someOf (.arrow _ _) _, ok, _, _, _
  | _, _, _, _, _, .someOf (.multiBinder _) _, ok, _, _, _ | _, _, _, _, _, .everyOf (.collection _ _) _, ok, _, _, _
  | _, _, _, _, _, .everyOf (.arrow _ _) _, ok, _, _, _ | _, _, _, _, _, .everyOf (.multiBinder _) _, ok, _, _, _
  | _, _, _, _, _, .inRelation _, ok, _, _, _ | _, _, _, _, _, .notInRelation _, ok, _, _, _ =>
    absurd ok Bool.false_ne_true

/-- **The evaluation of a guarded formula is exact**, among the hereditarily finite sets. -/
theorem evalGuarded_iff {formula : Formula 0} (ok : formula.guarded = true) {term : Pattern} (holds : IsHF term) :
    evalGuarded formula term = true ↔ HFSets.sat Env.closed formula (hfOf holds) := by
  rw [← sat_subst_elim0 formula]
  exact evalWith_iff Fin.elim0 Fin.elim0 Fin.elim0 Fin.elim0 formula ok holds fun index => index.elim0

/-- **The truth of a guarded native type at a hereditary term, read among the hereditary terms, is decided by the
evaluation.** -/
theorem guarded_decide {formula : Formula 0} (ok : formula.guarded = true) (free : formula.contextFree = true)
    {term : Pattern} (holds : IsHF term) :
    evalGuarded formula term = true ↔ HFNative.sat Env.closed formula ⟨term, holds⟩ :=
  (evalGuarded_iff ok holds).trans (sat_iff_hfSets formula free ⟨term, holds⟩).symm

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

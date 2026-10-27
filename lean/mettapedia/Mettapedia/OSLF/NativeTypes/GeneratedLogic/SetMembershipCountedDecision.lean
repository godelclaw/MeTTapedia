import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipCountedFixedPoints
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipFixedPointDecision

/-!
# Count-guarded native types of the hereditarily finite sets are decidable

The evaluation `evalCounted` decides every count-guarded formula (`Formula.countGuarded`) at a hereditary term, read
among the hereditarily finite sets (`countGuarded_decide`). It extends the guarded evaluation with counting members and
singletons:

- **Counting members** counts the distinct members, up to the set they denote, that the inner formula accepts
  (`countDecide`); a singleton is a term whose members all denote one set (`isSingleton`).
- **Steps back and sorts by a finite stage**: over a body without counting or singletons the guarded stage
  `V_(2^m)` serves; otherwise the counted stage `V_(2^m · (c + 1))`, for the closure cap `c` (`stageFor`,
  `sometimeBefore_countGuarded_iff`).
- Fixed points iterate their bodies as often as the term's height, as in the guarded evaluation.

The evaluation is exact (`evalCountedWith_iff`). Its bounds are doubly exponential, so it decides without being
practical.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Counting at the level of sets -/

/-- **At least `k` members with a property**, among the hereditarily finite sets and among all sets. -/
theorem hf_atLeast_iff_extensional {x : HF} {Q : HF → Prop} (k : ℕ) :
    HFSets.AtLeast k (fun m => m.1 ∈ x.1 ∧ Q m) ↔
      extensional.AtLeast k (fun z => z ∈ x.1 ∧ ∃ holds : IsHFSet z, Q ⟨z, holds⟩) := by
  constructor
  · rintro ⟨witnesses, length, apart, all⟩
    refine ⟨witnesses.map Subtype.val, by rw [List.length_map, length], ?_, fun z found => ?_⟩
    · exact List.pairwise_map.mpr (apart.imp fun differ => differ)
    · obtain ⟨m, member, rfl⟩ := List.mem_map.mp found
      exact ⟨(all m member).1, m.2, (all m member).2⟩
  · rintro ⟨witnesses, length, apart, all⟩
    refine ⟨witnesses.pmap (fun z holds => (⟨z, holds⟩ : HF)) fun z found => (all z found).2.1,
      by rw [List.length_pmap, length], ?_, fun m found => ?_⟩
    · exact List.Pairwise.pmap apart _ fun _ _ _ _ differ => differ
    · obtain ⟨z, zIn, rfl⟩ := List.mem_pmap.mp found
      obtain ⟨inside, holds, accepted⟩ := all z zIn
      exact ⟨inside, accepted⟩

/-! ## The evaluation -/

/-- **The stage for a step back or a sort over a body**: the guarded stage when the body has no counting or
singletons, the counted stage otherwise. -/
def stageFor {n : ℕ} (inner : Formula n) : ℕ :=
  if inner.guardedIn (fun _ => false) (fun _ => false) then guardedBound inner else countedStage inner

/-- **The evaluation of a formula** at a hereditary term, with the free variables read by `read`: the guarded evaluation
with counting members and singletons. -/
def evalCountedWith : {n : ℕ} → (Fin n → Pattern → Bool) → Formula n → Pattern → Bool
  | _, _, .top, _ => true
  | _, _, .bot, _ => false
  | _, read, .var index, term => read index term
  | _, _, .empty kind, term => decide (kind = .hashSet) && (membersOf term).isEmpty
  | _, _, .nonEmpty kind, term => !(decide (kind = .hashSet) && (membersOf term).isEmpty)
  | _, read, .and left right, term => evalCountedWith read left term && evalCountedWith read right term
  | _, read, .or left right, term => evalCountedWith read left term || evalCountedWith read right term
  | _, read, .possibly label inner, term =>
    decide (memberLabel label) && (membersOf term).any (evalCountedWith read inner)
  | _, read, .necessarily label inner, term =>
    !decide (memberLabel label) || (membersOf term).all (evalCountedWith read inner)
  | _, read, .atLeast count .forward label inner, term =>
    if memberLabel label then countDecide (evalCountedWith read inner) count (membersOf term) else decide (count = 0)
  | _, read, .allButFewer count .forward label inner, term =>
    if memberLabel label then !countDecide (fun value => !evalCountedWith read inner value) count (membersOf term)
    else !decide (count = 0)
  | _, read, .single kind inner, term =>
    decide (kind = .hashSet) && isSingleton term && (membersOf term).any (evalCountedWith read inner)
  | _, read, .everySingle kind inner, term =>
    !(decide (kind = .hashSet) && isSingleton term) || (membersOf term).all (evalCountedWith read inner)
  | _, read, .sometimeBefore label inner, term => decide (memberLabel label) &&
      (subsetTerms (stageFor inner)).any fun part => evalCountedWith read inner (insertTerm term part)
  | _, read, .alwaysBefore label inner, term => !decide (memberLabel label) ||
      (subsetTerms (stageFor inner)).all fun part => evalCountedWith read inner (insertTerm term part)
  | _, _, .is target, term => hereditary membership hfRule.category target && sameSet term target
  | _, _, .isNot target, term => !(hereditary membership hfRule.category target && sameSet term target)
  | _, read, .split kind left right, term => decide (kind = .hashSet) &&
      (coverings (membersOf term)).any fun parts =>
        evalCountedWith read left (set parts.1) && evalCountedWith read right (set parts.2)
  | _, read, .everySplit kind left right, term => !decide (kind = .hashSet) ||
      (coverings (membersOf term)).all fun parts =>
        evalCountedWith read left (set parts.1) || evalCountedWith read right (set parts.2)
  | _, read, .someOf (.base sort) inner, _ =>
      decide (sort = "Set") && (membersOf (vonNeumannTerm (stageFor inner))).any (evalCountedWith read inner)
  | _, read, .everyOf (.base sort) inner, _ =>
      !decide (sort = "Set") || (membersOf (vonNeumannTerm (stageFor inner))).all (evalCountedWith read inner)
  | _, read, .mu inner, term =>
    fixIter (fun below => evalCountedWith (Fin.cons below read : Fin (_ + 1) → Pattern → Bool) inner) (height term) term
  | _, read, .nu inner, term =>
    fixIter (fun below => evalCountedWith (Fin.cons below read : Fin (_ + 1) → Pattern → Bool) inner) (height term) term
  | _, _, _, _ => false

/-- **The evaluation of a closed formula.** -/
def evalCounted (formula : Formula 0) (term : Pattern) : Bool := evalCountedWith Fin.elim0 formula term

/-! ## Exactness -/

/-- A member's set, read through the inner formula, is the member read as a hereditarily finite set. -/
theorem sat_mk_zfOf {φ : Formula 0} {value : Pattern} (valueHolds : IsHF value) (holds : IsHFSet (zfOf value)) :
    HFSets.sat Env.closed φ ⟨zfOf value, holds⟩ ↔ HFSets.sat Env.closed φ (hfOf valueHolds) := Iff.rfl

theorem atLeast_hf_iff {count : ℕ} {label : StepLabel} {inner : Formula 0} {term : Pattern} (holds : IsHF term)
    {decides : Pattern → Bool}
    (each : ∀ value ∈ membersOf term, ∀ valueHolds : IsHF value,
      (decides value = true ↔ HFSets.sat Env.closed inner (hfOf valueHolds))) :
    (if memberLabel label then countDecide decides count (membersOf term) else decide (count = 0)) = true ↔
      HFSets.sat Env.closed (.atLeast count .forward label inner) (hfOf holds) := by
  change _ ↔ HFSets.AtLeast count fun other => (memberLabel label ∧ other.1 ∈ zfOf term) ∧ HFSets.sat Env.closed inner other
  by_cases labelled : memberLabel label
  · rw [if_pos labelled, countDecide_iff (fun z => ∃ zHolds : IsHFSet z, HFSets.sat Env.closed inner ⟨z, zHolds⟩) count
      (membersOf term) (hf_members holds) (fun value member => by
        rw [each value member (hf_members holds value member)]
        exact ⟨fun accepted => ⟨_, accepted⟩, fun ⟨_, accepted⟩ => accepted⟩),
      ← zfOf_eq_zfOfList holds, countIn_iff_atLeast]
    change _ ↔ HFSets.AtLeast count fun other : HF =>
      (memberLabel label ∧ other.1 ∈ (hfOf holds).1) ∧ HFSets.sat Env.closed inner other
    have shape := hf_atLeast_iff_extensional (x := hfOf holds) (Q := HFSets.sat Env.closed inner) count
    constructor
    · intro many
      exact (shape.mpr many).mono fun _ found => ⟨⟨labelled, found.1⟩, found.2⟩
    · intro many
      exact shape.mp (many.mono fun _ found => ⟨found.1.2, found.2⟩)
  · rw [if_neg labelled, decide_eq_true_eq]
    constructor
    · rintro rfl
      exact ⟨[], rfl, List.Pairwise.nil, fun _ none => absurd none List.not_mem_nil⟩
    · rintro ⟨witnesses, length, -, all⟩
      cases witnesses with
      | nil => exact length.symm
      | cons first _ => exact absurd (all first List.mem_cons_self).1.1 labelled

theorem allButFewer_hf_iff {count : ℕ} {label : StepLabel} {inner : Formula 0} {term : Pattern} (holds : IsHF term)
    {decides : Pattern → Bool}
    (each : ∀ value ∈ membersOf term, ∀ valueHolds : IsHF value,
      (decides value = true ↔ HFSets.sat Env.closed inner (hfOf valueHolds))) :
    (if memberLabel label then !countDecide (fun value => !decides value) count (membersOf term)
      else !decide (count = 0)) = true ↔
      HFSets.sat Env.closed (.allButFewer count .forward label inner) (hfOf holds) := by
  have negated := atLeast_hf_iff (count := count) (label := label) (inner := inner.dual) holds
    (decides := fun value => !decides value) fun value member valueHolds => by
      rw [Bool.not_eq_true', Bool.eq_false_iff, Ne, each value member valueHolds]
      exact (HFSets.sat_dual_closed inner (hfOf valueHolds)).symm
  change _ ↔ ¬ HFSets.AtLeast count fun other => (memberLabel label ∧ other.1 ∈ zfOf term) ∧
    ¬ HFSets.sat Env.closed inner other
  have rewritten : HFSets.AtLeast count (fun other => (memberLabel label ∧ other.1 ∈ zfOf term) ∧
      ¬ HFSets.sat Env.closed inner other) ↔ HFSets.sat Env.closed (.atLeast count .forward label inner.dual) (hfOf holds) := by
    change _ ↔ HFSets.AtLeast count fun other => (memberLabel label ∧ other.1 ∈ zfOf term) ∧
      HFSets.sat Env.closed inner.dual other
    constructor
    · exact fun many => many.mono fun other found => ⟨found.1, (HFSets.sat_dual_closed inner other).mpr found.2⟩
    · exact fun many => many.mono fun other found => ⟨found.1, (HFSets.sat_dual_closed inner other).mp found.2⟩
  rw [rewritten, ← negated]
  by_cases labelled : memberLabel label
  · simp only [if_pos labelled, Bool.not_eq_true', Bool.eq_false_iff, Ne]
  · simp only [if_neg labelled, Bool.not_eq_true', Bool.eq_false_iff, Ne]

theorem single_hf_iff {kind : CollType} {inner : Formula 0} {term : Pattern} (holds : IsHF term)
    {decides : Pattern → Bool}
    (each : ∀ value ∈ membersOf term, ∀ valueHolds : IsHF value,
      (decides value = true ↔ HFSets.sat Env.closed inner (hfOf valueHolds))) :
    (decide (kind = .hashSet) && isSingleton term && (membersOf term).any decides) = true ↔
      HFSets.sat Env.closed (.single kind inner) (hfOf holds) := by
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, isSingleton_iff holds, List.any_eq_true]
  change _ ↔ ∃ member : HF, (kind = .hashSet ∧ zfOf term = {member.1}) ∧ HFSets.sat Env.closed inner member
  constructor
  · rintro ⟨⟨set, element, single⟩, value, member, accepted⟩
    have valueHolds := hf_members holds value member
    have same := ((zfOf_eq_singleton_iff holds).mp single).2 value member
    exact ⟨hfOf valueHolds, ⟨set, by rw [single, ← same]; rfl⟩, (each value member valueHolds).mp accepted⟩
  · rintro ⟨element, ⟨set, single⟩, holdsAt⟩
    obtain ⟨⟨value, member, same⟩, -⟩ := (zfOf_eq_singleton_iff holds).mp single
    have valueHolds := hf_members holds value member
    refine ⟨⟨set, element.1, single⟩, value, member, (each value member valueHolds).mpr ?_⟩
    rwa [show hfOf valueHolds = element from hf_ext same]

theorem everySingle_hf_iff {kind : CollType} {inner : Formula 0} {term : Pattern} (holds : IsHF term)
    {decides : Pattern → Bool}
    (each : ∀ value ∈ membersOf term, ∀ valueHolds : IsHF value,
      (decides value = true ↔ HFSets.sat Env.closed inner (hfOf valueHolds))) :
    (!(decide (kind = .hashSet) && isSingleton term) || (membersOf term).all decides) = true ↔
      HFSets.sat Env.closed (.everySingle kind inner) (hfOf holds) := by
  rw [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not, List.all_eq_true]
  change _ ↔ ∀ member : HF, (kind = .hashSet ∧ zfOf term = {member.1}) → HFSets.sat Env.closed inner member
  constructor
  · rintro ((unset | notSingle) | all) element ⟨set, single⟩
    · exact absurd set unset
    · rw [Bool.eq_false_iff, Ne, isSingleton_iff holds] at notSingle
      exact absurd ⟨element.1, single⟩ notSingle
    · obtain ⟨⟨value, member, same⟩, -⟩ := (zfOf_eq_singleton_iff holds).mp single
      have valueHolds := hf_members holds value member
      rw [← show hfOf valueHolds = element from hf_ext same]
      exact (each value member valueHolds).mp (all value member)
  · intro holdsAll
    by_cases set : kind = .hashSet
    · cases single : isSingleton term
      · exact Or.inl (Or.inr rfl)
      · obtain ⟨element, isSingle⟩ := (isSingleton_iff holds).mp single
        refine Or.inr fun value member => ?_
        have valueHolds := hf_members holds value member
        refine (each value member valueHolds).mpr (holdsAll (hfOf valueHolds) ⟨set, ?_⟩)
        show zfOf term = {zfOf value}
        rw [isSingle, ((zfOf_eq_singleton_iff holds).mp isSingle).2 value member]
    · exact Or.inl (Or.inl set)

/-- Steps back try `x` with the subsets of a stage. -/
theorem stage_search_iff {inner : Formula 0} {term : Pattern} (holds : IsHF term) (bound : ℕ)
    {decides : Pattern → Bool}
    (inside : ∀ {part : Pattern} (partHolds : IsHF part),
      decides (insertTerm term part) = true ↔ HFSets.sat Env.closed inner (hfOf (insertTerm_hf holds partHolds))) :
    ((subsetTerms bound).any fun part => decides (insertTerm term part)) = true ↔
      ∃ part, ∃ within : part ⊆ stage bound, HFSets.sat Env.closed inner (insertStage (hfOf holds) within) := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨part, member, decided⟩
    have partHolds := subsetTerms_hf member
    exact ⟨zfOf part, subset_iff_subsetTerms.mpr ⟨part, member, rfl⟩,
      (hfSets_sat_congr (zfOf_insertTerm term partHolds)).mp ((inside partHolds).mp decided)⟩
  · rintro ⟨part, within, satisfied⟩
    obtain ⟨found, member, rfl⟩ := subset_iff_subsetTerms.mp within
    have partHolds := subsetTerms_hf member
    exact ⟨found, member, (inside partHolds).mpr ((hfSets_sat_congr (zfOf_insertTerm term partHolds)).mpr satisfied)⟩

theorem stage_every_iff {inner : Formula 0} {term : Pattern} (holds : IsHF term) (bound : ℕ)
    {decides : Pattern → Bool}
    (inside : ∀ {part : Pattern} (partHolds : IsHF part),
      decides (insertTerm term part) = true ↔ HFSets.sat Env.closed inner (hfOf (insertTerm_hf holds partHolds))) :
    ((subsetTerms bound).all fun part => decides (insertTerm term part)) = true ↔
      ∀ part, ∀ within : part ⊆ stage bound, HFSets.sat Env.closed inner (insertStage (hfOf holds) within) := by
  rw [List.all_eq_true]
  constructor
  · intro every part within
    obtain ⟨found, member, rfl⟩ := subset_iff_subsetTerms.mp within
    have partHolds := subsetTerms_hf member
    exact (hfSets_sat_congr (zfOf_insertTerm term partHolds)).mp ((inside partHolds).mp (every found member))
  · intro every part member
    have partHolds := subsetTerms_hf member
    exact (inside partHolds).mpr ((hfSets_sat_congr (zfOf_insertTerm term partHolds)).mpr
      (every _ (subset_iff_subsetTerms.mpr ⟨part, member, rfl⟩)))

/-- **A step back over a count-guarded body is decided by its stage.** -/
theorem sometimeBefore_stageFor_iff {n : ℕ} (u : Fin n → Formula 0) {inner : Formula n}
    (ok : inner.countGuardedIn (fun _ => false) (fun _ => false) = true) (label : StepLabel) (x : HF) :
    HFSets.sat Env.closed (.sometimeBefore label (inner.subst u)) x ↔
      memberLabel label ∧ ∃ part, ∃ within : part ⊆ stage (stageFor inner),
        HFSets.sat Env.closed (inner.subst u) (insertStage x within) := by
  by_cases plain : inner.guardedIn (fun _ => false) (fun _ => false) = true
  · rw [show stageFor inner = guardedBound inner from if_pos plain]
    exact sometimeBefore_guarded_iff u plain label x
  · rw [show stageFor inner = countedStage inner from if_neg plain]
    exact sometimeBefore_countGuarded_iff u ok label x

theorem alwaysBefore_stageFor_iff {n : ℕ} (u : Fin n → Formula 0) {inner : Formula n}
    (ok : inner.countGuardedIn (fun _ => false) (fun _ => false) = true) (label : StepLabel) (x : HF) :
    HFSets.sat Env.closed (.alwaysBefore label (inner.subst u)) x ↔
      (memberLabel label → ∀ part, ∀ within : part ⊆ stage (stageFor inner),
        HFSets.sat Env.closed (inner.subst u) (insertStage x within)) := by
  by_cases plain : inner.guardedIn (fun _ => false) (fun _ => false) = true
  · rw [show stageFor inner = guardedBound inner from if_pos plain]
    exact alwaysBefore_guarded_iff u plain label x
  · rw [show stageFor inner = countedStage inner from if_neg plain]
    exact alwaysBefore_countGuarded_iff u ok label x

theorem someOf_stageFor_iff {n : ℕ} (u : Fin n → Formula 0) {inner : Formula n}
    (ok : inner.countGuardedIn (fun _ => false) (fun _ => false) = true) (x : HF) :
    HFSets.sat Env.closed (.someOf (.base "Set") (inner.subst u)) x ↔
      ∃ y : HF, y.1 ∈ stage (stageFor inner) ∧ HFSets.sat Env.closed (inner.subst u) y := by
  by_cases plain : inner.guardedIn (fun _ => false) (fun _ => false) = true
  · rw [show stageFor inner = guardedBound inner from if_pos plain]
    exact someOf_guarded_iff u plain x
  · rw [show stageFor inner = countedStage inner from if_neg plain]
    exact someOf_countGuarded_iff u ok x

theorem everyOf_stageFor_iff {n : ℕ} (u : Fin n → Formula 0) {inner : Formula n}
    (ok : inner.countGuardedIn (fun _ => false) (fun _ => false) = true) (x : HF) :
    HFSets.sat Env.closed (.everyOf (.base "Set") (inner.subst u)) x ↔
      ∀ y : HF, y.1 ∈ stage (stageFor inner) → HFSets.sat Env.closed (inner.subst u) y := by
  by_cases plain : inner.guardedIn (fun _ => false) (fun _ => false) = true
  · rw [show stageFor inner = guardedBound inner from if_pos plain]
    exact everyOf_guarded_iff u plain x
  · rw [show stageFor inner = countedStage inner from if_neg plain]
    exact everyOf_countGuarded_iff u ok x

/-- **The evaluation is exact**, when the variables read their instances as far as they may be read. -/
theorem evalCountedWith_iff : ∀ {n : ℕ} (now later : Fin n → Bool) (u : Fin n → Formula 0)
    (read : Fin n → Pattern → Bool) (formula : Formula n), formula.countGuardedIn now later = true →
      ∀ {term : Pattern} (holds : IsHF term), Reads now later u read (height term) →
        (evalCountedWith read formula term = true ↔ HFSets.sat Env.closed (formula.subst u) (hfOf holds))
  | _, _, _, _, _, .top, _, _, _, _ => iff_of_true rfl trivial
  | _, _, _, _, _, .bot, _, _, _, _ => iff_of_false Bool.false_ne_true id
  | _, _, _, _, _, .var index, ok, term, holds, reads => reads index term holds (.inl ⟨ok, le_rfl⟩)
  | _, _, _, _, _, .empty kind, _, _, holds, _ => empty_hf_iff holds
  | _, _, _, _, _, .nonEmpty kind, _, _, holds, _ => nonEmpty_hf_iff holds
  | _, _, _, _, _, .is target, _, _, holds, _ => is_hf_iff holds
  | _, _, _, _, _, .isNot target, _, _, holds, _ => isNot_hf_iff holds
  | _, now, later, u, read, .and left right, ok, _, holds, reads => by
    simp only [Formula.countGuardedIn, Bool.and_eq_true] at ok
    simp only [evalCountedWith, Bool.and_eq_true]
    exact and_congr (evalCountedWith_iff now later u read left ok.1 holds reads)
      (evalCountedWith_iff now later u read right ok.2 holds reads)
  | _, now, later, u, read, .or left right, ok, _, holds, reads => by
    simp only [Formula.countGuardedIn, Bool.and_eq_true] at ok
    simp only [evalCountedWith, Bool.or_eq_true]
    exact or_congr (evalCountedWith_iff now later u read left ok.1 holds reads)
      (evalCountedWith_iff now later u read right ok.2 holds reads)
  | _, now, later, u, read, .possibly label inner, ok, _, holds, reads => by
    simp only [evalCountedWith]
    exact possibly_hf_iff holds fun member found memberHolds =>
      evalCountedWith_iff later later u read inner ok memberHolds (reads.forward (height_lt_of_mem found))
  | _, now, later, u, read, .necessarily label inner, ok, _, holds, reads => by
    simp only [evalCountedWith]
    exact necessarily_hf_iff holds fun member found memberHolds =>
      evalCountedWith_iff later later u read inner ok memberHolds (reads.forward (height_lt_of_mem found))
  | _, now, later, u, read, .atLeast count .forward label inner, ok, _, holds, reads => by
    simp only [evalCountedWith]
    exact atLeast_hf_iff holds fun member found memberHolds =>
      evalCountedWith_iff later later u read inner ok memberHolds (reads.forward (height_lt_of_mem found))
  | _, now, later, u, read, .allButFewer count .forward label inner, ok, _, holds, reads => by
    simp only [evalCountedWith]
    exact allButFewer_hf_iff holds fun member found memberHolds =>
      evalCountedWith_iff later later u read inner ok memberHolds (reads.forward (height_lt_of_mem found))
  | _, now, later, u, read, .single kind inner, ok, _, holds, reads => by
    simp only [evalCountedWith]
    exact single_hf_iff holds fun member found memberHolds =>
      evalCountedWith_iff later later u read inner ok memberHolds (reads.forward (height_lt_of_mem found))
  | _, now, later, u, read, .everySingle kind inner, ok, _, holds, reads => by
    simp only [evalCountedWith]
    exact everySingle_hf_iff holds fun member found memberHolds =>
      evalCountedWith_iff later later u read inner ok memberHolds (reads.forward (height_lt_of_mem found))
  | _, now, later, u, read, .split kind left right, ok, _, holds, reads => by
    simp only [Formula.countGuardedIn, Bool.and_eq_true] at ok
    simp only [evalCountedWith]
    exact split_hf_iff holds
      (fun parts member partHolds => evalCountedWith_iff now later u read left ok.1 partHolds
        (reads.below (part_height_le holds member).1))
      (fun parts member partHolds => evalCountedWith_iff now later u read right ok.2 partHolds
        (reads.below (part_height_le holds member).2))
  | _, now, later, u, read, .everySplit kind left right, ok, _, holds, reads => by
    simp only [Formula.countGuardedIn, Bool.and_eq_true] at ok
    simp only [evalCountedWith]
    exact everySplit_hf_iff holds
      (fun parts member partHolds => evalCountedWith_iff now later u read left ok.1 partHolds
        (reads.below (part_height_le holds member).1))
      (fun parts member partHolds => evalCountedWith_iff now later u read right ok.2 partHolds
        (reads.below (part_height_le holds member).2))
  | _, _, _, u, read, .sometimeBefore label inner, ok, term, holds, _ => by
    change _ ↔ HFSets.sat Env.closed (.sometimeBefore label (inner.subst u)) (hfOf holds)
    rw [sometimeBefore_stageFor_iff u ok]
    simp only [evalCountedWith, Bool.and_eq_true, decide_eq_true_eq]
    exact and_congr Iff.rfl (stage_search_iff holds _ fun partHolds =>
      evalCountedWith_iff _ _ u read inner ok (insertTerm_hf holds partHolds) (reads_none u read _))
  | _, _, _, u, read, .alwaysBefore label inner, ok, term, holds, _ => by
    change _ ↔ HFSets.sat Env.closed (.alwaysBefore label (inner.subst u)) (hfOf holds)
    rw [alwaysBefore_stageFor_iff u ok]
    simp only [evalCountedWith, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
    rw [stage_every_iff holds _ fun partHolds =>
      evalCountedWith_iff _ _ u read inner ok (insertTerm_hf holds partHolds) (reads_none u read _)]
    constructor
    · rintro (unlabelled | every) labelled
      · exact absurd labelled unlabelled
      · exact every
    · intro every
      by_cases labelled : memberLabel label
      · exact .inr (every labelled)
      · exact .inl labelled
  | _, _, _, u, read, .someOf (.base sort) inner, ok, _, holds, _ => by
    have inside : ∀ {value : Pattern} (valueHolds : IsHF value),
        evalCountedWith read inner value = true ↔ HFSets.sat Env.closed (inner.subst u) (hfOf valueHolds) :=
      fun valueHolds => evalCountedWith_iff _ _ u read inner ok valueHolds (reads_none u read _)
    change _ ↔ HFSets.sat Env.closed (.someOf (.base sort) (inner.subst u)) (hfOf holds)
    by_cases isSet : sort = "Set"
    · subst isSet
      rw [someOf_stageFor_iff u ok]
      simp only [evalCountedWith, decide_true, Bool.true_and, List.any_eq_true]
      constructor
      · rintro ⟨value, member, decided⟩
        have valueHolds := hf_members (vonNeumannTerm_hf _) value member
        exact ⟨hfOf valueHolds, mem_stage_iff_term.mpr ⟨value, member, rfl⟩, (inside valueHolds).mp decided⟩
      · rintro ⟨y, found, satisfied⟩
        obtain ⟨value, member, same⟩ := mem_stage_iff_term.mp found
        have valueHolds := hf_members (vonNeumannTerm_hf _) value member
        refine ⟨value, member, (inside valueHolds).mpr ?_⟩
        rwa [show hfOf valueHolds = y from hf_ext same]
    · simp only [evalCountedWith, isSet, decide_false, Bool.false_and, Bool.false_eq_true, false_iff]
      rintro ⟨witness, typed, -⟩
      exact isSet typed
  | _, _, _, u, read, .everyOf (.base sort) inner, ok, _, holds, _ => by
    have inside : ∀ {value : Pattern} (valueHolds : IsHF value),
        evalCountedWith read inner value = true ↔ HFSets.sat Env.closed (inner.subst u) (hfOf valueHolds) :=
      fun valueHolds => evalCountedWith_iff _ _ u read inner ok valueHolds (reads_none u read _)
    change _ ↔ HFSets.sat Env.closed (.everyOf (.base sort) (inner.subst u)) (hfOf holds)
    by_cases isSet : sort = "Set"
    · subst isSet
      rw [everyOf_stageFor_iff u ok]
      simp only [evalCountedWith, decide_true, Bool.not_true, Bool.false_or, List.all_eq_true]
      constructor
      · intro every y found
        obtain ⟨value, member, same⟩ := mem_stage_iff_term.mp found
        have valueHolds := hf_members (vonNeumannTerm_hf _) value member
        rw [← show hfOf valueHolds = y from hf_ext same]
        exact (inside valueHolds).mp (every value member)
      · intro every value member
        have valueHolds := hf_members (vonNeumannTerm_hf _) value member
        exact (inside valueHolds).mpr (every (hfOf valueHolds) (mem_stage_iff_term.mpr ⟨value, member, rfl⟩))
    · simp only [evalCountedWith, isSet, decide_false, Bool.not_false, Bool.true_or, true_iff]
      intro witness typed
      exact absurd typed isSet
  | _, now, later, u, read, .mu inner, ok, term, holds, reads => by
    simp only [evalCountedWith]
    have iterate : ∀ (fuel : ℕ) {other : Pattern} (otherHolds : IsHF other), height other ≤ fuel →
        height other ≤ height term →
          (fixIter (fun below => evalCountedWith (Fin.cons below read : Fin (_ + 1) → Pattern → Bool) inner) fuel
            other = true ↔ HFSets.sat Env.closed ((Formula.mu inner).subst u) (hfOf otherHolds)) := by
      intro fuel
      induction fuel with
      | zero => exact fun otherHolds enough _ => absurd enough (Nat.not_le.mpr (hf_height_pos otherHolds))
      | succ fuel previous =>
        intro other otherHolds enough below
        simp only [fixIter]
        rw [sat_subst_mu]
        refine evalCountedWith_iff (Fin.cons false now : Fin (_ + 1) → Bool)
          (Fin.cons true later : Fin (_ + 1) → Bool)
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
    simp only [evalCountedWith]
    have iterate : ∀ (fuel : ℕ) {other : Pattern} (otherHolds : IsHF other), height other ≤ fuel →
        height other ≤ height term →
          (fixIter (fun below => evalCountedWith (Fin.cons below read : Fin (_ + 1) → Pattern → Bool) inner) fuel
            other = true ↔ HFSets.sat Env.closed ((Formula.nu inner).subst u) (hfOf otherHolds)) := by
      intro fuel
      induction fuel with
      | zero => exact fun otherHolds enough _ => absurd enough (Nat.not_le.mpr (hf_height_pos otherHolds))
      | succ fuel previous =>
        intro other otherHolds enough below
        simp only [fixIter]
        rw [sat_subst_nu]
        refine evalCountedWith_iff (Fin.cons false now : Fin (_ + 1) → Bool)
          (Fin.cons true later : Fin (_ + 1) → Bool)
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
  | _, _, _, _, _, .atLeast _ .backward _ _, ok, _, _, _ | _, _, _, _, _, .allButFewer _ .backward _ _, ok, _, _, _
  | _, _, _, _, _, .typed _, ok, _, _, _ | _, _, _, _, _, .untyped _, ok, _, _, _
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

/-- **The evaluation of a count-guarded formula is exact**, among the hereditarily finite sets. -/
theorem evalCounted_iff {formula : Formula 0} (ok : formula.countGuarded = true) {term : Pattern} (holds : IsHF term) :
    evalCounted formula term = true ↔ HFSets.sat Env.closed formula (hfOf holds) := by
  rw [← sat_subst_elim0 formula]
  exact evalCountedWith_iff Fin.elim0 Fin.elim0 Fin.elim0 Fin.elim0 formula ok holds fun index => index.elim0

/-- **The truth of a count-guarded native type at a hereditary term, read among the hereditary terms, is decided by
the evaluation.** -/
theorem countGuarded_decide {formula : Formula 0} (ok : formula.countGuarded = true) (free : formula.contextFree = true)
    {term : Pattern} (holds : IsHF term) : evalCounted formula term = true ↔ HFNative.sat Env.closed formula ⟨term, holds⟩ :=
  (evalCounted_iff ok holds).trans (sat_iff_hfSets formula free ⟨term, holds⟩).symm

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

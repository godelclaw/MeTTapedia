import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipHFUniverse
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipSplits

/-!
# Past modalities and quantifiers over the type, by finite search

A past modality at a set ranges over the sets that contain it, and a quantifier over the type over all sets: among
the hereditarily finite sets, infinitely many either way. A plain modal formula, though, sees a set only to the depth
of its nesting of steps, and down to that depth infinitely many sets look alike.

- **Bisimilarity up to a depth** (`NativeStructure.BisimUpTo`): steps go forth and back for that many rounds. A plain
  modal formula (steps, their duals and the connectives, `Formula.plainModal`) of modal depth at most `k` holds alike
  at elements bisimilar up to `k` (`sat_iff_of_bisimUpTo`), in any native structure.
- **Truncation** (`truncSet`): a set cut off at depth `k` lies inside `V_k` and is bisimilar to it up to `k`
  (`bisim_truncSet`). A set containing `x` is bisimilar up to `d + 1` to `x` added to a subset of `V_(d+1)`
  (`container_bisim`).
- **So, for a plain modal `ψ` of depth at most `d + 1`**, some hereditarily finite set containing `x` has `ψ` exactly
  when `x` added to some subset of `V_(d+1)` has it (`sometimeBefore_iff_search`), and dually for every set containing
  `x` (`alwaysBefore_iff_search`). Some hereditarily finite set has a plain modal `ψ` of depth at most `d` exactly when
  some subset of `V_d` has it (`someOf_iff_search`, `everyOf_iff_search`). Each search is over finitely many sets.
- **The searches are computed** on terms (`decideSometimeBefore`, `decideAlwaysBefore`, `decideSomeOf`,
  `decideEveryOf`), each candidate decided by the parts-region decision, and they are exact among the hereditary
  terms (`decideSometimeBefore_iff` and the others).

In the language's own reference structure a past modality also ranges over closed object terms that are not
hereditary, such as a set with a vector among its members, so the exact reading is among the hereditary terms.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax

universe u

namespace Formula

/-- **Plain modal formulas**: steps, their duals and the connectives, with no fixed point, variable or atom. -/
def plainModal : {n : ℕ} → Formula n → Bool
  | _, .top | _, .bot => true
  | _, .and left right | _, .or left right => plainModal left && plainModal right
  | _, .possibly _ inner | _, .necessarily _ inner => plainModal inner
  | _, _ => false

/-- **The modal depth**: the longest nesting of steps. -/
def modalDepth : {n : ℕ} → Formula n → ℕ
  | _, .and left right | _, .or left right => max (modalDepth left) (modalDepth right)
  | _, .possibly _ inner | _, .necessarily _ inner => modalDepth inner + 1
  | _, _ => 0

/-- A plain modal formula is regional. -/
theorem regional_of_plainModal : ∀ {n : ℕ} (formula : Formula n), formula.plainModal = true →
    formula.regional = true
  | _, .top, _ | _, .bot, _ => rfl
  | _, .and left right, plain | _, .or left right, plain => by
    simp only [plainModal, Bool.and_eq_true] at plain
    simp only [Formula.regional, regional_of_plainModal left plain.1, regional_of_plainModal right plain.2,
      Bool.and_self]
  | _, .possibly _ inner, plain | _, .necessarily _ inner, plain => regional_of_plainModal inner plain
  | _, .var _, plain | _, .is _, plain | _, .isNot _, plain | _, .empty _, plain | _, .nonEmpty _, plain
  | _, .typed _, plain | _, .untyped _, plain | _, .mu _, plain | _, .nu _, plain | _, .single _ _, plain
  | _, .everySingle _ _, plain | _, .atLeast _ _ _ _, plain | _, .allButFewer _ _ _ _, plain
  | _, .sometimeBefore _ _, plain | _, .alwaysBefore _ _, plain | _, .built _ _, plain | _, .everyBuilt _ _, plain
  | _, .split _ _ _, plain | _, .everySplit _ _ _, plain | _, .body _, plain | _, .everyBody _, plain
  | _, .multiBody _ _, plain | _, .everyMultiBody _ _, plain | _, .bound _, plain | _, .notBound _, plain
  | _, .mapsAll _ _, plain | _, .mapsSome _ _, plain | _, .someOf _ _, plain | _, .everyOf _ _, plain =>
    absurd plain Bool.false_ne_true

end Formula

namespace NativeStructure

variable {Carrier : Type u} (S : NativeStructure Carrier)

/-- **Bisimilarity up to a depth**: for that many rounds, each step from one element is matched by a step with the
same label from the other, to elements bisimilar for one round fewer. -/
def BisimUpTo : ℕ → Carrier → Carrier → Prop
  | 0, _, _ => True
  | k + 1, first, second =>
    (∀ label next, S.step first label next → ∃ next', S.step second label next' ∧ BisimUpTo k next next') ∧
      ∀ label next', S.step second label next' → ∃ next, S.step first label next ∧ BisimUpTo k next next'

theorem bisimUpTo_succ_iff {k : ℕ} {first second : Carrier} :
    S.BisimUpTo (k + 1) first second ↔
      (∀ label next, S.step first label next → ∃ next', S.step second label next' ∧ S.BisimUpTo k next next') ∧
        ∀ label next', S.step second label next' → ∃ next, S.step first label next ∧ S.BisimUpTo k next next' :=
  Iff.rfl

theorem bisimUpTo_refl : ∀ (k : ℕ) (element : Carrier), S.BisimUpTo k element element
  | 0, _ => trivial
  | k + 1, _ => (S.bisimUpTo_succ_iff).mpr ⟨fun _ next step => ⟨next, step, bisimUpTo_refl k next⟩,
      fun _ next step => ⟨next, step, bisimUpTo_refl k next⟩⟩

/-- **A plain modal formula of depth at most `k` holds alike at elements bisimilar up to `k`.** -/
theorem sat_iff_of_bisimUpTo : ∀ {n : ℕ} (formula : Formula n), formula.plainModal = true → ∀ (k : ℕ),
    formula.modalDepth ≤ k → ∀ (env : Env Carrier n) {first second : Carrier}, S.BisimUpTo k first second →
      (S.sat env formula first ↔ S.sat env formula second)
  | _, .top, _, _, _, _, _, _, _ => Iff.rfl
  | _, .bot, _, _, _, _, _, _, _ => Iff.rfl
  | _, .and left right, plain, k, depth, env, _, _, related => by
    simp only [Formula.plainModal, Bool.and_eq_true] at plain
    simp only [Formula.modalDepth, max_le_iff] at depth
    exact and_congr (sat_iff_of_bisimUpTo left plain.1 k depth.1 env related)
      (sat_iff_of_bisimUpTo right plain.2 k depth.2 env related)
  | _, .or left right, plain, k, depth, env, _, _, related => by
    simp only [Formula.plainModal, Bool.and_eq_true] at plain
    simp only [Formula.modalDepth, max_le_iff] at depth
    exact or_congr (sat_iff_of_bisimUpTo left plain.1 k depth.1 env related)
      (sat_iff_of_bisimUpTo right plain.2 k depth.2 env related)
  | _, .possibly _ _, _, 0, depth, _, _, _, _ => absurd depth (by simp [Formula.modalDepth])
  | _, .possibly label inner, plain, k + 1, depth, env, _, _, related => by
    have depth' : inner.modalDepth ≤ k := by simpa [Formula.modalDepth] using depth
    obtain ⟨forth, back⟩ := (S.bisimUpTo_succ_iff).mp related
    constructor
    · rintro ⟨next, step, holds⟩
      obtain ⟨next', step', related'⟩ := forth label next step
      exact ⟨next', step', (sat_iff_of_bisimUpTo inner plain k depth' env related').mp holds⟩
    · rintro ⟨next', step', holds⟩
      obtain ⟨next, step, related'⟩ := back label next' step'
      exact ⟨next, step, (sat_iff_of_bisimUpTo inner plain k depth' env related').mpr holds⟩
  | _, .necessarily _ _, _, 0, depth, _, _, _, _ => absurd depth (by simp [Formula.modalDepth])
  | _, .necessarily label inner, plain, k + 1, depth, env, _, _, related => by
    have depth' : inner.modalDepth ≤ k := by simpa [Formula.modalDepth] using depth
    obtain ⟨forth, back⟩ := (S.bisimUpTo_succ_iff).mp related
    constructor
    · intro every next' step'
      obtain ⟨next, step, related'⟩ := back label next' step'
      exact (sat_iff_of_bisimUpTo inner plain k depth' env related').mp (every next step)
    · intro every next step
      obtain ⟨next', step', related'⟩ := forth label next step
      exact (sat_iff_of_bisimUpTo inner plain k depth' env related').mpr (every next' step')
  | _, .var _, plain, _, _, _, _, _, _ | _, .is _, plain, _, _, _, _, _, _
  | _, .isNot _, plain, _, _, _, _, _, _ | _, .empty _, plain, _, _, _, _, _, _
  | _, .nonEmpty _, plain, _, _, _, _, _, _ | _, .typed _, plain, _, _, _, _, _, _
  | _, .untyped _, plain, _, _, _, _, _, _ | _, .mu _, plain, _, _, _, _, _, _
  | _, .nu _, plain, _, _, _, _, _, _ | _, .single _ _, plain, _, _, _, _, _, _
  | _, .everySingle _ _, plain, _, _, _, _, _, _ | _, .atLeast _ _ _ _, plain, _, _, _, _, _, _
  | _, .allButFewer _ _ _ _, plain, _, _, _, _, _, _ | _, .sometimeBefore _ _, plain, _, _, _, _, _, _
  | _, .alwaysBefore _ _, plain, _, _, _, _, _, _ | _, .built _ _, plain, _, _, _, _, _, _
  | _, .everyBuilt _ _, plain, _, _, _, _, _, _ | _, .split _ _ _, plain, _, _, _, _, _, _
  | _, .everySplit _ _ _, plain, _, _, _, _, _, _ | _, .body _, plain, _, _, _, _, _, _
  | _, .everyBody _, plain, _, _, _, _, _, _ | _, .multiBody _ _, plain, _, _, _, _, _, _
  | _, .everyMultiBody _ _, plain, _, _, _, _, _, _ | _, .bound _, plain, _, _, _, _, _, _
  | _, .notBound _, plain, _, _, _, _, _, _ | _, .mapsAll _ _, plain, _, _, _, _, _, _
  | _, .mapsSome _ _, plain, _, _, _, _, _, _ | _, .someOf _ _, plain, _, _, _, _, _, _
  | _, .everyOf _ _, plain, _, _, _, _, _, _ => absurd plain Bool.false_ne_true

end NativeStructure

end Mettapedia.OSLF.NativeTypes.GeneratedLogic

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Truncation -/

/-- **A set cut off at a depth**: at depth `0` the empty set, and at depth `k + 1` the set of its members cut off at
depth `k`, taken inside `V_(k+1)`. -/
noncomputable def truncSet : ℕ → ZFSet.{0} → ZFSet.{0}
  | 0, _ => ∅
  | k + 1, whole =>
    ZFSet.sep (fun z => ∃ member ∈ whole, truncSet k member = z) (ZFSet.powerset (ZFSet.vonNeumann (k : Ordinal)))

theorem truncSet_subset : ∀ (k : ℕ) (whole : ZFSet.{0}), truncSet k whole ⊆ ZFSet.vonNeumann (k : Ordinal)
  | 0, _ => fun z member => by simp [truncSet] at member
  | k + 1, _ => fun z member => by
    rw [truncSet, ZFSet.mem_sep] at member
    rw [Nat.cast_succ, ZFSet.vonNeumann_add_one]
    exact member.1

theorem mem_truncSet_succ {k : ℕ} {whole z : ZFSet.{0}} :
    z ∈ truncSet (k + 1) whole ↔ ∃ member ∈ whole, truncSet k member = z := by
  rw [truncSet, ZFSet.mem_sep]
  refine ⟨fun found => found.2, ?_⟩
  rintro ⟨member, inside, rfl⟩
  exact ⟨ZFSet.mem_powerset.mpr (truncSet_subset k member), member, inside, rfl⟩

/-- **A set is bisimilar up to `k` to its truncation at `k`.** -/
theorem bisim_truncSet : ∀ (k : ℕ) (whole : ZFSet.{0}), extensional.BisimUpTo k whole (truncSet k whole)
  | 0, _ => trivial
  | k + 1, whole => (extensional.bisimUpTo_succ_iff).mpr
    ⟨fun _ next step => ⟨truncSet k next, ⟨step.1, mem_truncSet_succ.mpr ⟨next, step.2, rfl⟩⟩, bisim_truncSet k next⟩,
      fun _ next' step => by
        obtain ⟨member, inside, rfl⟩ := mem_truncSet_succ.mp step.2
        exact ⟨member, ⟨step.1, inside⟩, bisim_truncSet k member⟩⟩

/-- **A set containing `x` is bisimilar up to `d + 1` to `x` added to a subset of `V_(d+1)`**: the truncations at `d`
of its members. -/
theorem container_bisim (d : ℕ) {container x : ZFSet.{0}} (member : x ∈ container) :
    ∃ part ⊆ ZFSet.vonNeumann ((d + 1 : ℕ) : Ordinal), extensional.BisimUpTo (d + 1) container (insert x part) := by
  refine ⟨ZFSet.sep (fun z => ∃ other ∈ container, truncSet d other = z) (ZFSet.vonNeumann ((d + 1 : ℕ) : Ordinal)),
    fun z inside => (ZFSet.mem_sep.mp inside).1, (extensional.bisimUpTo_succ_iff).mpr ⟨?_, ?_⟩⟩
  · intro label next step
    refine ⟨truncSet d next, ⟨step.1, ZFSet.mem_insert_iff.mpr (Or.inr (ZFSet.mem_sep.mpr ⟨?_, next, step.2, rfl⟩))⟩,
      bisim_truncSet d next⟩
    rw [Nat.cast_succ, ZFSet.vonNeumann_add_one]
    exact ZFSet.mem_powerset.mpr (truncSet_subset d next)
  · intro label next' step
    rcases ZFSet.mem_insert_iff.mp step.2 with same | inPart
    · subst same
      exact ⟨next', ⟨step.1, member⟩, extensional.bisimUpTo_refl d next'⟩
    · obtain ⟨-, other, inside, rfl⟩ := ZFSet.mem_sep.mp inPart
      exact ⟨other, ⟨step.1, inside⟩, bisim_truncSet d other⟩

/-! ## Hereditarily finite sets -/

theorem isHFSet_of_subset_vonNeumann {whole : ZFSet.{0}} {k : ℕ} (within : whole ⊆ ZFSet.vonNeumann (k : Ordinal)) :
    IsHFSet whole := by
  obtain ⟨term, holds, same⟩ := vonNeumann_denoted k
  exact isHFSet_of_subset holds (same ▸ within)

theorem zfOf_cons_set (value : Pattern) (values : List Pattern) :
    zfOf (set (value :: values)) = insert (zfOf value) (zfOf (set values)) := by
  apply ZFSet.ext
  intro z
  rw [ZFSet.mem_insert_iff, zfOf_set, zfOf_set, mem_zfOfList, mem_zfOfList]
  constructor
  · rintro ⟨found, member, rfl⟩
    rcases List.mem_cons.mp member with rfl | member
    · exact Or.inl rfl
    · exact Or.inr ⟨found, member, rfl⟩
  · rintro (rfl | ⟨found, member, rfl⟩)
    · exact ⟨value, List.mem_cons_self, rfl⟩
    · exact ⟨found, List.mem_cons_of_mem _ member, rfl⟩

theorem isHFSet_insert {x whole : ZFSet.{0}} (xHolds : IsHFSet x) (wholeHolds : IsHFSet whole) :
    IsHFSet (insert x whole) := by
  obtain ⟨term, holds, rfl⟩ := xHolds
  obtain ⟨other, otherHolds, rfl⟩ := wholeHolds
  obtain ⟨values, rfl, inside⟩ := hf_set otherHolds
  refine ⟨set (term :: values), Hereditary.members fun value member => ?_, zfOf_cons_set term values⟩
  rcases List.mem_cons.mp member with rfl | member
  · exact holds
  · exact inside value member

/-- A plain modal formula reads the same among the hereditarily finite sets and among all sets. -/
theorem hfSets_sat_iff {formula : Formula 0} (plain : formula.plainModal = true) (element : {z // IsHFSet z}) :
    HFSets.sat Env.closed formula element ↔ extensional.sat Env.closed formula element.1 :=
  (NativeStructure.Generated.inclusion hfSets_generated).sat_iff formula
    (Formula.forward_of_regional formula (Formula.regional_of_plainModal formula plain))
    (BoundedMorphism.envPreimage_closed _) element

/-! ## Finite searches -/

variable {formula : Formula 0}

/-- **Some hereditarily finite set containing `x` has a plain modal `ψ` of depth at most `d + 1` exactly when `x` added
to some subset of `V_(d+1)` has it.** -/
theorem sometimeBefore_iff_search {label : StepLabel} (plain : formula.plainModal = true) {d : ℕ}
    (depth : formula.modalDepth ≤ d + 1) (element : {z // IsHFSet z}) :
    HFSets.sat Env.closed (.sometimeBefore label formula) element ↔
      memberLabel label ∧ ∃ part ⊆ ZFSet.vonNeumann ((d + 1 : ℕ) : Ordinal),
        extensional.sat Env.closed formula (insert element.1 part) := by
  constructor
  · rintro ⟨previous, step, holds⟩
    obtain ⟨part, within, related⟩ := container_bisim d step.2
    exact ⟨step.1, part, within, (extensional.sat_iff_of_bisimUpTo formula plain (d + 1) depth Env.closed related).mp
      ((hfSets_sat_iff plain previous).mp holds)⟩
  · rintro ⟨labelled, part, within, holds⟩
    exact ⟨⟨insert element.1 part, isHFSet_insert element.2 (isHFSet_of_subset_vonNeumann within)⟩,
      ⟨labelled, ZFSet.mem_insert_iff.mpr (Or.inl rfl)⟩, (hfSets_sat_iff plain _).mpr holds⟩

/-- **Every hereditarily finite set containing `x` has a plain modal `ψ` of depth at most `d + 1` exactly when `x`
added to every subset of `V_(d+1)` has it.** -/
theorem alwaysBefore_iff_search {label : StepLabel} (plain : formula.plainModal = true) {d : ℕ}
    (depth : formula.modalDepth ≤ d + 1) (element : {z // IsHFSet z}) :
    HFSets.sat Env.closed (.alwaysBefore label formula) element ↔
      (memberLabel label → ∀ part ⊆ ZFSet.vonNeumann ((d + 1 : ℕ) : Ordinal),
        extensional.sat Env.closed formula (insert element.1 part)) := by
  constructor
  · intro every labelled part within
    exact (hfSets_sat_iff plain _).mp
      (every ⟨insert element.1 part, isHFSet_insert element.2 (isHFSet_of_subset_vonNeumann within)⟩
        ⟨labelled, ZFSet.mem_insert_iff.mpr (Or.inl rfl)⟩)
  · intro every previous step
    obtain ⟨part, within, related⟩ := container_bisim d step.2
    exact (hfSets_sat_iff plain previous).mpr
      ((extensional.sat_iff_of_bisimUpTo formula plain (d + 1) depth Env.closed related).mpr (every step.1 part within))

/-- **Some hereditarily finite set has a plain modal `ψ` of depth at most `d` exactly when some subset of `V_d` has
it.** -/
theorem someOf_iff_search (plain : formula.plainModal = true) {d : ℕ} (depth : formula.modalDepth ≤ d)
    (element : {z // IsHFSet z}) :
    HFSets.sat Env.closed (.someOf (.base "Set") formula) element ↔
      ∃ part ⊆ ZFSet.vonNeumann (d : Ordinal), extensional.sat Env.closed formula part := by
  constructor
  · rintro ⟨witness, -, holds⟩
    exact ⟨truncSet d witness.1, truncSet_subset d _,
      (extensional.sat_iff_of_bisimUpTo formula plain d depth Env.closed (bisim_truncSet d witness.1)).mp
        ((hfSets_sat_iff plain witness).mp holds)⟩
  · rintro ⟨part, within, holds⟩
    exact ⟨⟨part, isHFSet_of_subset_vonNeumann within⟩, rfl, (hfSets_sat_iff plain _).mpr holds⟩

/-- **Every hereditarily finite set has a plain modal `ψ` of depth at most `d` exactly when every subset of `V_d` has
it.** -/
theorem everyOf_iff_search (plain : formula.plainModal = true) {d : ℕ} (depth : formula.modalDepth ≤ d)
    (element : {z // IsHFSet z}) :
    HFSets.sat Env.closed (.everyOf (.base "Set") formula) element ↔
      ∀ part ⊆ ZFSet.vonNeumann (d : Ordinal), extensional.sat Env.closed formula part := by
  constructor
  · intro every part within
    exact (hfSets_sat_iff plain _).mp (every ⟨part, isHFSet_of_subset_vonNeumann within⟩ rfl)
  · intro every witness _
    exact (hfSets_sat_iff plain witness).mpr
      ((extensional.sat_iff_of_bisimUpTo formula plain d depth Env.closed (bisim_truncSet d witness.1)).mpr
        (every _ (truncSet_subset d _)))

/-! ## The searches, computed -/

/-- **The term of `V_n`**: the empty set, then power sets. -/
def vonNeumannTerm : ℕ → Pattern
  | 0 => set []
  | n + 1 => set ((membersOf (vonNeumannTerm n)).sublists.map set)

theorem vonNeumannTerm_hf : ∀ n : ℕ, IsHF (vonNeumannTerm n)
  | 0 => Hereditary.members fun _ member => nomatch member
  | n + 1 => .members fun value member => by
    obtain ⟨list, sublist, rfl⟩ := List.mem_map.mp member
    exact .members fun other otherMember =>
      hf_members (vonNeumannTerm_hf n) other ((List.mem_sublists.mp sublist).subset otherMember)

theorem zfOf_vonNeumannTerm : ∀ n : ℕ, zfOf (vonNeumannTerm n) = ZFSet.vonNeumann (n : Ordinal)
  | 0 => by
    rw [Nat.cast_zero, ZFSet.vonNeumann_zero, vonNeumannTerm, zfOf_set]
    rfl
  | n + 1 => by
    rw [vonNeumannTerm, zfOf_sublists, ← hf_eq_set (vonNeumannTerm_hf n), zfOf_vonNeumannTerm n, Nat.cast_succ,
      ZFSet.vonNeumann_add_one]

/-- The terms of the subsets of `V_n`. -/
def subsetTerms (n : ℕ) : List Pattern := (membersOf (vonNeumannTerm n)).sublists.map set

theorem subsetTerms_hf {n : ℕ} {part : Pattern} (member : part ∈ subsetTerms n) : IsHF part := by
  obtain ⟨list, sublist, rfl⟩ := List.mem_map.mp member
  exact .members fun other otherMember =>
    hf_members (vonNeumannTerm_hf n) other ((List.mem_sublists.mp sublist).subset otherMember)

theorem subset_iff_subsetTerms {n : ℕ} {part : ZFSet.{0}} :
    part ⊆ ZFSet.vonNeumann (n : Ordinal) ↔ ∃ term ∈ subsetTerms n, zfOf term = part := by
  rw [← ZFSet.mem_powerset, ← zfOf_vonNeumannTerm, hf_eq_set (vonNeumannTerm_hf n), ← zfOf_sublists, zfOf_set,
    mem_zfOfList]
  rfl

/-- A term with one more member. -/
def insertTerm (term whole : Pattern) : Pattern := set (term :: membersOf whole)

theorem insertTerm_hf {term whole : Pattern} (termHolds : IsHF term) (wholeHolds : IsHF whole) :
    IsHF (insertTerm term whole) :=
  .members fun value member => by
    rcases List.mem_cons.mp member with rfl | member
    · exact termHolds
    · exact hf_members wholeHolds value member

theorem zfOf_insertTerm (term : Pattern) {whole : Pattern} (wholeHolds : IsHF whole) :
    zfOf (insertTerm term whole) = insert (zfOf term) (zfOf whole) := by
  rw [insertTerm, zfOf_cons_set, ← hf_eq_set wholeHolds]

/-- **Decide whether some set containing a term has a plain modal formula**: try the term added to each subset of
`V_(d+1)`. -/
def decideSometimeBefore (label : StepLabel) (formula : Formula 0) (term : Pattern) : Bool :=
  decide (memberLabel label) &&
    (subsetTerms (formula.modalDepth + 1)).any fun part => decideRegional formula (insertTerm term part)

/-- **Decide whether every set containing a term has a plain modal formula.** -/
def decideAlwaysBefore (label : StepLabel) (formula : Formula 0) (term : Pattern) : Bool :=
  !decide (memberLabel label) ||
    (subsetTerms (formula.modalDepth + 1)).all fun part => decideRegional formula (insertTerm term part)

/-- **Decide whether some set has a plain modal formula**: try each subset of `V_d`. -/
def decideSomeOf (formula : Formula 0) : Bool := (subsetTerms formula.modalDepth).any (decideRegional formula)

/-- **Decide whether every set has a plain modal formula.** -/
def decideEveryOf (formula : Formula 0) : Bool := (subsetTerms formula.modalDepth).all (decideRegional formula)

theorem decideRegional_iff_extensional (plain : formula.plainModal = true) {term : Pattern} (holds : IsHF term) :
    decideRegional formula term = true ↔ extensional.sat Env.closed formula (zfOf term) :=
  (decideRegional_iff (Formula.regional_of_plainModal formula plain) holds).trans
    (sat_iff_extensional (Formula.forward_of_regional formula (Formula.regional_of_plainModal formula plain)) holds)

/-- **The search for a containing set is exact**, among the hereditary terms. -/
theorem decideSometimeBefore_iff {label : StepLabel} (plain : formula.plainModal = true) {term : Pattern}
    (holds : IsHF term) :
    decideSometimeBefore label formula term = true ↔
      HFNative.sat Env.closed (.sometimeBefore label formula) ⟨term, holds⟩ := by
  rw [sat_iff_hfSets, sometimeBefore_iff_search plain (d := formula.modalDepth) (Nat.le_succ _)]
  simp only [decideSometimeBefore, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
  refine and_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨part, member, decided⟩
    have partHolds := subsetTerms_hf member
    refine ⟨zfOf part, subset_iff_subsetTerms.mpr ⟨part, member, rfl⟩, ?_⟩
    change extensional.sat Env.closed formula (insert (zfOf term) (zfOf part))
    rw [← zfOf_insertTerm term partHolds]
    exact (decideRegional_iff_extensional plain (insertTerm_hf holds partHolds)).mp decided
  · rintro ⟨part, within, satisfied⟩
    obtain ⟨found, member, rfl⟩ := subset_iff_subsetTerms.mp within
    refine ⟨found, member, (decideRegional_iff_extensional plain (insertTerm_hf holds (subsetTerms_hf member))).mpr ?_⟩
    rw [zfOf_insertTerm term (subsetTerms_hf member)]
    exact satisfied

/-- **The search over all containing sets is exact**, among the hereditary terms. -/
theorem decideAlwaysBefore_iff {label : StepLabel} (plain : formula.plainModal = true) {term : Pattern}
    (holds : IsHF term) :
    decideAlwaysBefore label formula term = true ↔
      HFNative.sat Env.closed (.alwaysBefore label formula) ⟨term, holds⟩ := by
  rw [sat_iff_hfSets, alwaysBefore_iff_search plain (d := formula.modalDepth) (Nat.le_succ _)]
  simp only [decideAlwaysBefore, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, List.all_eq_true]
  constructor
  · rintro (unlabelled | every) labelled part within
    · exact absurd labelled unlabelled
    · obtain ⟨found, member, rfl⟩ := subset_iff_subsetTerms.mp within
      have satisfied := (decideRegional_iff_extensional plain (insertTerm_hf holds (subsetTerms_hf member))).mp
        (every found member)
      rwa [zfOf_insertTerm term (subsetTerms_hf member)] at satisfied
  · intro every
    by_cases labelled : memberLabel label
    · refine Or.inr fun part member => (decideRegional_iff_extensional plain
        (insertTerm_hf holds (subsetTerms_hf member))).mpr ?_
      rw [zfOf_insertTerm term (subsetTerms_hf member)]
      exact every labelled _ (subset_iff_subsetTerms.mpr ⟨part, member, rfl⟩)
    · exact Or.inl labelled

/-- **The search for a set with the formula is exact.** -/
theorem decideSomeOf_iff (plain : formula.plainModal = true) {term : Pattern} (holds : IsHF term) :
    decideSomeOf formula = true ↔ HFNative.sat Env.closed (.someOf (.base "Set") formula) ⟨term, holds⟩ := by
  rw [sat_iff_hfSets, someOf_iff_search plain (d := formula.modalDepth) le_rfl]
  simp only [decideSomeOf, List.any_eq_true]
  constructor
  · rintro ⟨part, member, decided⟩
    exact ⟨zfOf part, subset_iff_subsetTerms.mpr ⟨part, member, rfl⟩,
      (decideRegional_iff_extensional plain (subsetTerms_hf member)).mp decided⟩
  · rintro ⟨part, within, satisfied⟩
    obtain ⟨found, member, rfl⟩ := subset_iff_subsetTerms.mp within
    exact ⟨found, member, (decideRegional_iff_extensional plain (subsetTerms_hf member)).mpr satisfied⟩

/-- **The search over all sets is exact.** -/
theorem decideEveryOf_iff (plain : formula.plainModal = true) {term : Pattern} (holds : IsHF term) :
    decideEveryOf formula = true ↔ HFNative.sat Env.closed (.everyOf (.base "Set") formula) ⟨term, holds⟩ := by
  rw [sat_iff_hfSets, everyOf_iff_search plain (d := formula.modalDepth) le_rfl]
  simp only [decideEveryOf, List.all_eq_true]
  constructor
  · intro every part within
    obtain ⟨found, member, rfl⟩ := subset_iff_subsetTerms.mp within
    exact (decideRegional_iff_extensional plain (subsetTerms_hf member)).mp (every found member)
  · intro every part member
    exact (decideRegional_iff_extensional plain (subsetTerms_hf member)).mpr
      (every _ (subset_iff_subsetTerms.mpr ⟨part, member, rfl⟩))

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

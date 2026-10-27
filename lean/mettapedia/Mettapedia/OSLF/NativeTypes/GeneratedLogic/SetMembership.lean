import Mettapedia.OSLF.NativeTypes.GeneratedLogic.HereditarySets
import Mathlib.SetTheory.ZFC.Basic

/-!
# The membership language: hereditarily finite sets

One carrier `Set ::= {Set*}` and one rule `{x, ...rest} ⇒ x`: a set steps to each of its members. Read modulo the set
laws, its states are the hereditarily finite sets and its steps are membership.

- **ZF sets** (`zfOf`): each hereditary term denotes a ZF set, the set of what its members denote. Two hereditary
  terms are equivalent exactly when they denote the same ZF set (`equivalent_iff_zfOf`), and a term steps to another
  exactly when the second denotes a member of what the first denotes (`member_step_iff`).
- **So the behavioural formulas are membership formulas**: `◇φ` holds at a set when `φ` holds at some member, and
  `□φ` when it holds at every member (`possibly_iff`, `necessarily_iff`).
- **The front door decides them**, since a set's canonical region is its transitive closure: the members of `3`, that
  `0 ∈ 2` and `3 ∉ 3`, that every descent from `3` ends, and that `{0, 0}` is `1`.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec (MatchRel MatchArgsRel MatchBagRel matchPattern_iff_matchRel)
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (matchPatternForRule matchPatternForRule_eq_syntactic)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (arrange arrange_mem arrange_eq_of_presents)
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars_zero)

variable {relEnv : RelationEnv} {language : LanguageDef} {carrier : GrammarRule} {sort : String}

/-! ## The language -/

/-- The carrier of hereditarily finite sets: `Set ::= {Set*}`. -/
def hfRule : GrammarRule :=
  { label := "Set", category := "Set", params := [.simple "members" (.collection .hashSet (.base "Set"))],
    syntaxPattern := [.terminal "{", .op (.sep "members" "," none), .terminal "}"] }

/-- `{x, ...rest} ⇒ x`: a set steps to each of its members. -/
def memberRule : RewriteRule :=
  { name := "Member", typeContext := [("x", .base "Set"), ("rest", .collection .hashSet (.base "Set"))],
    premises := [], left := .collection .hashSet [.fvar "x"] (some "rest"), right := .fvar "x", bindings := none }

def membership : LanguageDef :=
  { name := "SetReadings.Membership", types := [⟨"Set", .ast⟩], terms := [hfRule], equations := [],
    rewrites := [memberRule] }

theorem membership_hereditary : HereditaryLanguage membership hfRule :=
  ⟨rfl, by decide, ⟨by simp [membership], ⟨"members", rfl⟩, rfl⟩⟩

/-- **The membership language is a flat set language** of width one. -/
theorem membership_flat : FlatSetLanguage membership hfRule 1 where
  hereditary := membership_hereditary
  rules := by
    intro rule member
    rw [show membership.rewrites = [memberRule] from rfl, List.mem_singleton] at member
    subst member
    refine ⟨[.fvar "x"], some "rest", rfl, by simp, fun pattern member => ?_, rfl⟩
    rw [List.mem_singleton] at member
    subst member
    exact Or.inl ⟨"x", rfl, by simp⟩

/-- The language has no atoms: its only constructor takes a set. -/
theorem membership_pure (label : String) : ¬ AtomOf membership hfRule.category label := by
  rintro ⟨rule, member, -, -, parameters⟩
  rw [show membership.terms = [hfRule] from rfl, List.mem_singleton] at member
  subst member
  simp [hfRule] at parameters

/-! ## Steps are membership -/

theorem member_bindings (value : Pattern) (rest : List Pattern) :
    mergeBindings [("x", value)] [("rest", .collection .hashSet rest none)] =
      some [("rest", .collection .hashSet rest none), ("x", value)] := rfl

theorem member_instance (value : Pattern) (rest : List Pattern) :
    applyBindingsScoped (captureSites memberRule) [("rest", .collection .hashSet rest none), ("x", value)] 0
      memberRule.right = value := by
  have depth : captureDepth "x" 0 (captureSites memberRule) = some 0 := by decide
  have found : [("rest", Pattern.collection .hashSet rest none), ("x", value)].find? (·.1 == "x") =
      some ("x", value) := rfl
  show applyBindingsScoped (captureSites memberRule) _ 0 (.fvar "x") = value
  simp only [applyBindingsScoped, found, depth, Nat.sub_zero, liftBVars_zero]

/-- **A set steps to each member it is written with.** -/
theorem member_fires (values : List Pattern) (index : ℕ) (bound : index < values.length) :
    StepValid relEnv membership (set values)
      (.rule 0 [("rest", .collection .hashSet (values.eraseIdx index) none), ("x", values[index])] [])
      values[index] := by
  have matched : [("rest", Pattern.collection .hashSet (values.eraseIdx index) none), ("x", values[index])] ∈
      matchPatternForRule membership memberRule (set values) := by
    rw [matchPatternForRule_eq_syntactic]
    exact matchPattern_iff_matchRel.mpr (.collection (by decide) (.cons index bound .fvar .nilRest
      (member_bindings _ _)))
  have fired := StepValid.rule (relEnv := relEnv) (index := 0) rfl matched (.nil _)
  rwa [member_instance] at fired

/-- **Every step of a presentation of a set leads to one of its members.** -/
theorem member_of_step {values : List Pattern} {witness : Witness} {contractum : Pattern}
    (valid : StepValid relEnv membership (set values) witness contractum) : contractum ∈ values := by
  cases valid with
  | @rule _ index rule initial final witnesses found matched premises =>
    have isMember : rule = memberRule := List.mem_singleton.mp (List.mem_of_getElem? found)
    subst isMember
    cases premises
    rw [matchPatternForRule_eq_syntactic] at matched
    have related := matchPattern_iff_matchRel.mp matched
    cases related with
    | collection _ bag =>
      cases bag with
      | cons index bound head tail merged =>
        cases head
        cases tail
        rw [member_bindings] at merged
        cases merged
        rw [member_instance]
        exact List.getElem_mem bound

/-! ## ZF sets -/

mutual
/-- **The ZF set a term denotes**: a set denotes the set of what its members denote. -/
def zfOf : Pattern → ZFSet.{0}
  | .collection .hashSet values none => zfOfList values
  | _ => ∅

/-- The ZF set of what the terms of a list denote. -/
def zfOfList : List Pattern → ZFSet.{0}
  | [] => ∅
  | value :: values => insert (zfOf value) (zfOfList values)
end

theorem zfOf_set (values : List Pattern) : zfOf (set values) = zfOfList values := by
  simp only [set, zfOf]

theorem mem_zfOfList {set : ZFSet.{0}} : ∀ {values : List Pattern},
    set ∈ zfOfList values ↔ ∃ value ∈ values, zfOf value = set
  | [] => by simp [zfOfList]
  | value :: values => by
    rw [zfOfList, ZFSet.mem_insert_iff, mem_zfOfList]
    constructor
    · rintro (rfl | ⟨other, member, rfl⟩)
      · exact ⟨value, List.mem_cons_self, rfl⟩
      · exact ⟨other, List.mem_cons_of_mem _ member, rfl⟩
    · rintro ⟨other, member, rfl⟩
      rcases List.mem_cons.mp member with rfl | member
      · exact Or.inl rfl
      · exact Or.inr ⟨other, member, rfl⟩

/-- **A term and its canonical form denote the same ZF set.** -/
theorem zfOf_sortBags {term : Pattern} (holds : Hereditary language sort term) :
    zfOf (BagForms.sortBags term) = zfOf term := by
  induction holds with
  | atom _ => rfl
  | @members values _ same =>
    apply ZFSet.ext
    intro element
    rw [sortBags_set_values, zfOf_set, zfOf_set, mem_zfOfList, mem_zfOfList]
    constructor
    · rintro ⟨value, member, rfl⟩
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp ((arrange_mem value).mp member)
      exact ⟨original, originalMember, (same original originalMember).symm⟩
    · rintro ⟨value, member, rfl⟩
      exact ⟨BagForms.sortBags value, (arrange_mem _).mpr (List.mem_map_of_mem member), same value member⟩

theorem arrange_of_canonical {values : List Pattern} (canonical : BagForms.sortBags (set values) = set values) :
    arrange .hashSet values = values := by
  have fixed : values.map BagForms.sortBags = values := by
    conv_rhs => rw [← List.map_id values]
    exact List.map_congr_left (member_canonical canonical)
  have := canonical
  rw [sortBags_set_values] at this
  simpa [set, fixed] using this

/-- **Canonical sets with no atoms that denote the same ZF set are equal.** -/
theorem zfOf_injective (pure : ∀ label, ¬ AtomOf language sort label) {first : Pattern}
    (firstHolds : Hereditary language sort first) :
    ∀ {second : Pattern}, Hereditary language sort second → BagForms.sortBags first = first →
      BagForms.sortBags second = second → zfOf first = zfOf second → first = second := by
  induction firstHolds with
  | atom atom => exact absurd atom (pure _)
  | @members values _ ih =>
    intro second secondHolds firstCanonical secondCanonical same
    rcases secondHolds.cases with ⟨label, -, atom⟩ | ⟨others, rfl, othersHold⟩
    · exact absurd atom (pure _)
    · have firstMembers := member_canonical firstCanonical
      have secondMembers := member_canonical secondCanonical
      rw [zfOf_set, zfOf_set] at same
      have members : ∀ value, value ∈ values ↔ value ∈ others := by
        intro value
        constructor
        · intro member
          obtain ⟨other, otherMember, equal⟩ := mem_zfOfList.mp (same ▸ mem_zfOfList.mpr ⟨value, member, rfl⟩)
          rw [ih value member (othersHold other otherMember) (firstMembers value member)
            (secondMembers other otherMember) equal.symm]
          exact otherMember
        · intro member
          obtain ⟨original, originalMember, equal⟩ :=
            mem_zfOfList.mp (same.symm ▸ mem_zfOfList.mpr ⟨value, member, rfl⟩)
          rw [← ih original originalMember (othersHold value member) (firstMembers original originalMember)
            (secondMembers value member) equal]
          exact originalMember
      rw [← arrange_of_canonical firstCanonical, ← arrange_of_canonical secondCanonical,
        arrange_eq_of_presents (kind := .hashSet) members]

/-- **Hereditary terms with no atoms are equivalent exactly when they denote the same ZF set.** -/
theorem equivalent_iff_zfOf (lang : HereditaryLanguage language carrier)
    (pure : ∀ label, ¬ AtomOf language carrier.category label) {first second : Pattern}
    (firstHolds : Hereditary language carrier.category first)
    (secondHolds : Hereditary language carrier.category second) :
    ObjectEquivalent relEnv language .syntax first second ↔ zfOf first = zfOf second := by
  have canonical := hereditary_canonical (relEnv := relEnv) lang
  rw [canonical.equivalent_iff ((hereditary_iff _).mpr firstHolds) ((hereditary_iff _).mpr secondHolds)]
  constructor
  · intro same
    rw [← zfOf_sortBags firstHolds, ← zfOf_sortBags secondHolds, same]
  · intro same
    refine zfOf_injective pure firstHolds.sortBags secondHolds.sortBags ?_ ?_ ?_
    · rw [BagForms.sortBags_eq_canon, Mettapedia.OSLF.MeTTaIL.CanonicalBags.canon_idempotent]
    · rw [BagForms.sortBags_eq_canon, Mettapedia.OSLF.MeTTaIL.CanonicalBags.canon_idempotent]
    · rw [zfOf_sortBags firstHolds, zfOf_sortBags secondHolds, same]

abbrev Membership := referenceStructure RelationEnv.empty membership

theorem membership_equivalent {first second : Pattern} (firstHolds : Hereditary membership hfRule.category first)
    (secondHolds : Hereditary membership hfRule.category second) :
    ObjectEquivalent relEnv membership .syntax first second ↔ zfOf first = zfOf second :=
  equivalent_iff_zfOf membership_hereditary membership_pure firstHolds secondHolds

/-- **A hereditary term steps to another exactly when the second denotes a member of the first.** -/
theorem member_step_iff {first second : Pattern} (firstHolds : Hereditary membership hfRule.category first)
    (secondHolds : Hereditary membership hfRule.category second) :
    (referenceStructure relEnv membership).step first .any second ↔ zfOf second ∈ zfOf first := by
  have canonical := hereditary_canonical (relEnv := relEnv) membership_hereditary
  constructor
  · rintro ⟨-, -, redex, contractum, witness, before, -, valid, -, after, -⟩
    have redexHolds : Hereditary membership hfRule.category redex :=
      (hereditary_iff _).mp (canonical.invariant ((hereditary_iff _).mpr firstHolds) before)
    rcases redexHolds.cases with ⟨label, -, atom⟩ | ⟨values, rfl, valuesHold⟩
    · exact absurd atom (membership_pure _)
    · have member := member_of_step valid
      have contractumHolds := valuesHold contractum member
      rw [(membership_equivalent firstHolds redexHolds).mp before, zfOf_set,
        ← (membership_equivalent contractumHolds secondHolds).mp after]
      exact mem_zfOfList.mpr ⟨contractum, member, rfl⟩
  · intro member
    rcases firstHolds.cases with ⟨label, -, atom⟩ | ⟨values, rfl, valuesHold⟩
    · exact absurd atom (membership_pure _)
    · rw [zfOf_set] at member
      obtain ⟨value, valueMember, same⟩ := mem_zfOfList.mp member
      obtain ⟨index, bound, rfl⟩ := List.getElem_of_mem valueMember
      exact ⟨(firstHolds.typed membership_hereditary.setCarrier).2,
        (secondHolds.typed membership_hereditary.setCarrier).2,
        set values, values[index], _, Relation.EqvGen.refl _, (firstHolds.typed membership_hereditary.setCarrier).2,
        member_fires values index bound, ((valuesHold _ valueMember).typed membership_hereditary.setCarrier).2,
        (membership_equivalent (valuesHold _ valueMember) secondHolds).mpr same, rfl⟩

/-- Everything a hereditary term steps to is hereditary. -/
theorem step_hereditary {first second : Pattern} (firstHolds : Hereditary membership hfRule.category first)
    (step : (referenceStructure relEnv membership).step first .any second) :
    Hereditary membership hfRule.category second := by
  have canonical := hereditary_canonical (relEnv := relEnv) membership_hereditary
  obtain ⟨-, -, redex, contractum, witness, before, -, valid, -, after, -⟩ := step
  have redexHolds : Hereditary membership hfRule.category redex :=
    (hereditary_iff _).mp (canonical.invariant ((hereditary_iff _).mpr firstHolds) before)
  rcases redexHolds.cases with ⟨label, -, atom⟩ | ⟨values, rfl, valuesHold⟩
  · exact absurd atom (membership_pure _)
  · exact (hereditary_iff _).mp
      (canonical.invariant ((hereditary_iff _).mpr (valuesHold contractum (member_of_step valid))) after)

/-- **`◇φ` holds at a set when `φ` holds at something denoting a member.** -/
theorem possibly_iff {n : ℕ} {env : Env Pattern n} {formula : Formula n} {term : Pattern}
    (holds : Hereditary membership hfRule.category term) :
    (referenceStructure relEnv membership).sat env (.possibly .any formula) term ↔
      ∃ member, Hereditary membership hfRule.category member ∧ zfOf member ∈ zfOf term ∧
        (referenceStructure relEnv membership).sat env formula member := by
  constructor
  · rintro ⟨member, step, holdsThere⟩
    have memberHolds := step_hereditary holds step
    exact ⟨member, memberHolds, (member_step_iff holds memberHolds).mp step, holdsThere⟩
  · rintro ⟨member, memberHolds, isMember, holdsThere⟩
    exact ⟨member, (member_step_iff holds memberHolds).mpr isMember, holdsThere⟩

/-- **`□φ` holds at a set when `φ` holds at everything denoting a member.** -/
theorem necessarily_iff {n : ℕ} {env : Env Pattern n} {formula : Formula n} {term : Pattern}
    (holds : Hereditary membership hfRule.category term) :
    (referenceStructure relEnv membership).sat env (.necessarily .any formula) term ↔
      ∀ member, Hereditary membership hfRule.category member → zfOf member ∈ zfOf term →
        (referenceStructure relEnv membership).sat env formula member := by
  constructor
  · intro every member memberHolds isMember
    exact every member ((member_step_iff holds memberHolds).mpr isMember)
  · intro every member step
    have memberHolds := step_hereditary holds step
    exact every member memberHolds ((member_step_iff holds memberHolds).mp step)

/-- **Transport from the extensional side**: hereditary terms that denote the same ZF set satisfy the same closed
formulas, so every native type of the language holds alike at them. -/
theorem transport_zfOf (formula : Formula 0) {first second : Pattern}
    (firstHolds : Hereditary membership hfRule.category first)
    (secondHolds : Hereditary membership hfRule.category second) (same : zfOf first = zfOf second) :
    (referenceStructure relEnv membership).sat Env.closed formula first ↔
      (referenceStructure relEnv membership).sat Env.closed formula second :=
  sat_respects_equivalent relEnv membership formula (firstHolds.typed membership_hereditary.setCarrier).2
    (secondHolds.typed membership_hereditary.setCarrier).2 ((membership_equivalent firstHolds secondHolds).mpr same)

/-- **Extensional equality is indiscernibility by native types**: two hereditary terms satisfy the same closed
formulas exactly when they denote the same ZF set. -/
theorem indiscernible_iff_zfOf {first second : Pattern} (firstHolds : Hereditary membership hfRule.category first)
    (secondHolds : Hereditary membership hfRule.category second) :
    (∀ formula : Formula 0, (referenceStructure relEnv membership).sat Env.closed formula first ↔
      (referenceStructure relEnv membership).sat Env.closed formula second) ↔ zfOf first = zfOf second := by
  refine ⟨fun same => ?_, fun same formula => transport_zfOf formula firstHolds secondHolds same⟩
  have atSecond : (referenceStructure relEnv membership).sat Env.closed (.is second) second :=
    ⟨(secondHolds.typed membership_hereditary.setCarrier).2.2, Relation.EqvGen.refl _⟩
  obtain ⟨-, equivalent⟩ := (same (.is second)).mpr atSecond
  exact (membership_equivalent firstHolds secondHolds).mp equivalent

/-! ## The front door -/

def zero : Pattern := set []
def one : Pattern := set [zero]
def two : Pattern := set [zero, one]
def three : Pattern := set [zero, one, two]

abbrev membershipForms : CanonicalForms RelationEnv.empty membership 2 := flatForms membership_flat 2

theorem three_members_answer :
    ask RelationEnv.empty [] membership 2 (.atLeast 3 .forward .any .top) three none 4 (some membershipForms) =
      .proved (.canonicalRegion 4) := by
  decide +kernel

theorem three_not_four_answer :
    ask RelationEnv.empty [] membership 2 (.atLeast 4 .forward .any .top) three none 4 (some membershipForms) =
      .refuted (.canonicalRegion 4) := by
  decide +kernel

theorem zero_mem_two_answer :
    ask RelationEnv.empty [] membership 2 (.possibly .any (.is zero)) two none 4 (some membershipForms) =
      .proved (.exploration 4) := by
  decide +kernel

theorem three_not_mem_self_answer :
    ask RelationEnv.empty [] membership 2 (.possibly .any (.is three)) three none 4 (some membershipForms) =
      .refuted (.canonicalRegion 4) := by
  decide +kernel

theorem three_wellFounded_answer :
    ask RelationEnv.empty [] membership 2 (.mu (.necessarily .any (.var 0))) three none 4 (some membershipForms) =
      .proved (.canonicalRegion 4) := by
  decide +kernel

theorem extensional_answer :
    ask RelationEnv.empty [] membership 2 (.is one) (set [zero, zero]) none 4 (some membershipForms) =
      .proved (.canonicalRegion 4) := by
  decide +kernel

theorem three_rank_answer :
    ask RelationEnv.empty [] membership 2 (.possibly .any (.possibly .any (.possibly .any .top))) three none 4
      (some membershipForms) = .proved (.exploration 4) := by
  decide +kernel

theorem two_rank_answer :
    ask RelationEnv.empty [] membership 2 (.possibly .any (.possibly .any (.possibly .any .top))) two none 4
      (some membershipForms) = .refuted (.canonicalRegion 4) := by
  decide +kernel

/-- **Without these canonical forms the front door cannot refute that `3 ∈ 3`.** -/
theorem three_not_mem_self_open :
    ask RelationEnv.empty [] membership 2 (.possibly .any (.is three)) three none 4 = .unknown 4 := by
  decide +kernel

theorem zero_holds : Hereditary membership hfRule.category zero := (hereditary_iff _).mp (by decide)
theorem two_holds : Hereditary membership hfRule.category two := (hereditary_iff _).mp (by decide)
theorem three_holds : Hereditary membership hfRule.category three := (hereditary_iff _).mp (by decide)

/-- **Read through ZF sets, the front door's verdicts are facts of set theory**: `0 ∈ 2` and `3 ∉ 3`, and
every descent from `3` ends. -/
theorem membership_verdicts :
    zfOf zero ∈ zfOf two ∧ zfOf three ∉ zfOf three ∧
      Membership.sat Env.closed (.mu (.necessarily .any (.var 0))) three := by
  refine ⟨?_, fun member => ?_, ask_proved three_wellFounded_answer⟩
  · obtain ⟨element, elementHolds, isMember, -, named⟩ := (possibly_iff two_holds).mp (ask_proved zero_mem_two_answer)
    rwa [(membership_equivalent elementHolds zero_holds).mp named] at isMember
  · exact ask_refuted three_not_mem_self_answer ((possibly_iff three_holds).mpr
      ⟨three, three_holds, member, (three_holds.typed membership_hereditary.setCarrier).2.2, Relation.EqvGen.refl _⟩)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

import Mettapedia.OSLF.NativeTypes.GeneratedLogic.TwoLevelSetRules

/-!
# Set rules nested at any depth

A set rule's element patterns may themselves be set patterns, to any depth (`NestedElement`): metavariables and closed
canonical terms, and set patterns of element patterns of their own, with or without a rest. Under the set laws every set
inside a presentation may hold copies of its members, so a rule can fire at presentations the canonical form does not
show. Canonical regions still decide such languages. The copies are bounded depth by depth (`bounds`, outermost first):
a set pattern at a depth has at most that depth's bound element patterns, counting its rest.

- **The listed presentations** (`nestedPresentations bounds`): a canonical term itself, and, for a set, each member
  written between once and the outermost bound times, each copy a listed presentation of the member under the
  remaining bounds. Each presents the term (`nestedPresentations_class`). One bound at every depth is the uniform
  case (`List.replicate depth bound`).
- **A match moves to a listed presentation**, with like captures (`nested_transfer`), by induction on the element
  pattern: a set pattern's elements move to listed presentations of their members, and the match is regrouped by
  classes (`regroup`).
- **Coherence** (`nested_coherent`, `nestedForms`): a step from any presentation of a canonical hereditary set is
  matched, with the same labels and up to canonical form, by a step listed at one of these presentations. Rules may
  have premises that transfer between alike captures (`PremisesTransfer`, `nested_coherent_with`).

Flat and two-level set rules are depths one and two, which `HereditarySets` and `TwoLevelSetRules` also decide with
finer bounds on the copies at each level.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec (MatchRel MatchBagRel matchPattern_iff_matchRel)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (canon Same arrange arrange_mem canon_idempotent arrange_eq_of_presents)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (matchPatternForRule matchPatternForRule_eq_syntactic)

variable {language : LanguageDef} {sort : String}

/-! ## Nested element patterns and their presentations -/

/-- **Element patterns of nested set rules, under bounds by depth**: metavariables and closed hereditary canonical
terms under any bounds, and set patterns whose element patterns, counting the rest, are at most the outermost bound,
each an element pattern under the remaining bounds. -/
inductive NestedElement (language : LanguageDef) (sort : String) : List ℕ → Pattern → Prop
  | var (bounds : List ℕ) (name : String) : NestedElement language sort bounds (.fvar name)
  | closed (bounds : List ℕ) {pattern : Pattern} : Hereditary language sort pattern →
      BagForms.sortBags pattern = pattern → NestedElement language sort bounds pattern
  | set {bound : ℕ} {bounds : List ℕ} {elements : List Pattern} {inner : Option String} :
      elements.length + inner.toList.length ≤ bound →
      (∀ element ∈ elements, NestedElement language sort bounds element) →
      NestedElement language sort (bound :: bounds) (.collection .hashSet elements inner)

/-- **The presentations listed for nested set rules, under bounds by depth**: a canonical term itself, and, for a set,
each member written between once and the outermost bound times, each copy a listed presentation of the member under
the remaining bounds. -/
def nestedPresentations : List ℕ → Pattern → List Pattern
  | [], value => [value]
  | bound :: bounds, value => value :: match value with
    | .collection .hashSet values none =>
      (chooseGroups (values.map fun member => nestedGroups bound (nestedPresentations bounds member))).map
        fun members => .collection .hashSet members none
    | _ => []

theorem self_mem_nestedPresentations (bounds : List ℕ) (value : Pattern) : value ∈ nestedPresentations bounds value := by
  cases bounds <;> simp [nestedPresentations]

theorem mem_listsOf_inv {items : List Pattern} : ∀ {n : ℕ} {members : List Pattern}, members ∈ listsOf items n →
    members.length = n ∧ ∀ member ∈ members, member ∈ items
  | 0, members, listed => by
    simp only [listsOf, List.mem_singleton] at listed
    subst listed
    exact ⟨rfl, fun _ member => absurd member List.not_mem_nil⟩
  | n + 1, members, listed => by
    simp only [listsOf, List.mem_flatMap, List.mem_map] at listed
    obtain ⟨item, itemMember, tail, tailListed, rfl⟩ := listed
    obtain ⟨length, inside⟩ := mem_listsOf_inv tailListed
    refine ⟨by rw [List.length_cons, length], fun member member' => ?_⟩
    rcases List.mem_cons.mp member' with rfl | inTail
    · exact itemMember
    · exact inside member inTail

theorem mem_nestedGroups_inv {bound : ℕ} {presentations group : List Pattern}
    (listed : group ∈ nestedGroups bound presentations) :
    group ≠ [] ∧ ∀ member ∈ group, member ∈ presentations := by
  obtain ⟨n, -, inLists⟩ := List.mem_flatMap.mp listed
  obtain ⟨length, inside⟩ := mem_listsOf_inv inLists
  exact ⟨fun empty => (by rw [empty] at length; cases length), inside⟩

theorem mem_chooseGroups_inv : ∀ {choices : List (List (List Pattern))} {picked : List Pattern},
    picked ∈ chooseGroups choices →
      ∃ groups : List (List Pattern), List.Forall₂ (· ∈ ·) groups choices ∧ picked = groups.flatten
  | [], picked, listed => by
    simp only [chooseGroups, List.mem_singleton] at listed
    exact ⟨[], .nil, listed⟩
  | _ :: _, picked, listed => by
    simp only [chooseGroups, List.mem_flatMap, List.mem_map] at listed
    obtain ⟨group, groupMember, tail, tailListed, rfl⟩ := listed
    obtain ⟨tailGroups, related, rfl⟩ := mem_chooseGroups_inv tailListed
    exact ⟨group :: tailGroups, .cons groupMember related, by rw [List.flatten_cons]⟩

/-- **A listed presentation presents the term**: its canonical form is the term. -/
theorem nestedPresentations_class : ∀ {bounds : List ℕ} {value shown : Pattern}, BagForms.sortBags value = value →
    shown ∈ nestedPresentations bounds value → BagForms.sortBags shown = value
  | [], value, shown, canonical, listed => by
    simp only [nestedPresentations, List.mem_singleton] at listed
    subst listed
    exact canonical
  | _ :: _, value, shown, canonical, listed => by
    rcases List.mem_cons.mp listed with rfl | listed
    · exact canonical
    · split at listed
      · rename_i values listed
        obtain ⟨members, chosen, rfl⟩ := List.mem_map.mp listed
        have canonicalSet : BagForms.sortBags (set values) = set values := canonical
        have valuesCanonical := member_canonical canonicalSet
        have valuesArranged : arrange .hashSet (values.map BagForms.sortBags) = values := by
          have arranged := canonicalSet
          rw [sortBags_set_values] at arranged
          simpa [set] using arranged
        obtain ⟨groups, related, rfl⟩ := mem_chooseGroups_inv chosen
        rw [List.forall₂_map_right_iff] at related
        have memberClass : ∀ member ∈ groups.flatten, BagForms.sortBags member ∈ values := by
          intro member inside
          obtain ⟨group, groupMember, memberInGroup⟩ := List.mem_flatten.mp inside
          obtain ⟨value', valueMember, groupListed⟩ := exists_right_of_forall₂ related group groupMember
          rw [nestedPresentations_class (valuesCanonical value' valueMember)
            ((mem_nestedGroups_inv groupListed).2 member memberInGroup)]
          exact valueMember
        have valueShown : ∀ value' ∈ values, ∃ member ∈ groups.flatten, BagForms.sortBags member = value' := by
          intro value' valueMember
          obtain ⟨group, groupMember, groupListed⟩ := exists_left_of_forall₂ related value' valueMember
          obtain ⟨nonempty, inside⟩ := mem_nestedGroups_inv groupListed
          obtain ⟨member, memberInGroup⟩ := List.exists_mem_of_ne_nil group nonempty
          exact ⟨member, List.mem_flatten.mpr ⟨group, groupMember, memberInGroup⟩,
            nestedPresentations_class (valuesCanonical value' valueMember) (inside member memberInGroup)⟩
        change BagForms.sortBags (set groups.flatten) = set values
        rw [sortBags_set_values]
        congr 1
        refine (arrange_eq_of_presents (kind := .hashSet) fun other => ?_).trans valuesArranged
        simp only [List.mem_map]
        constructor
        · rintro ⟨member, memberIn, rfl⟩
          exact ⟨BagForms.sortBags member, memberClass member memberIn,
            valuesCanonical _ (memberClass member memberIn)⟩
        · rintro ⟨value', valueMember, rfl⟩
          obtain ⟨member, memberIn, memberIs⟩ := valueShown value' valueMember
          exact ⟨member, memberIn, by rw [memberIs, valuesCanonical value' valueMember]⟩
      · exact absurd listed List.not_mem_nil

/-! ## Moving a match to a listed presentation -/

theorem patternNames_sublist : ∀ {patterns : List Pattern} {pattern : Pattern}, pattern ∈ patterns →
    (patternNames pattern).Sublist (patternNamesList patterns)
  | _ :: _, _, .head _ => List.sublist_append_left _ _
  | _ :: _, _, .tail _ member => (patternNames_sublist member).trans (List.sublist_append_right _ _)

/-- **A nested element pattern with distinct names captures distinct names.** -/
theorem nested_captures_distinct {bounds : List ℕ} {pattern : Pattern}
    (element : NestedElement language sort bounds pattern) :
    ∀ {term : Pattern} {captured : Bindings}, MatchRel pattern term captured → (patternNames pattern).Nodup →
      (captured.map Prod.fst).Nodup := by
  induction element with
  | var bounds name =>
    intro term captured matched _
    cases matched
    exact List.nodup_singleton _
  | closed bounds holds canonical =>
    intro term captured matched _
    exact flat_captures_distinct (rest := none) (.inr ⟨holds, canonical⟩) matched
  | set short each recurse =>
    intro term captured matched distinct
    cases matched with
    | collection _ bag =>
      exact bag_nodup bag (fun other member _ _ matched' names => recurse other member matched' names)
        (by simpa only [patternNames] using distinct)

/-- **A match of a nested element pattern moves to a listed presentation of the term's canonical form**, with like
captures. -/
theorem nested_transfer {bounds : List ℕ} {pattern : Pattern} (element : NestedElement language sort bounds pattern) :
    ∀ {term : Pattern} {bindings : Bindings}, Hereditary language sort term → MatchRel pattern term bindings →
      (patternNames pattern).Nodup →
      ∃ partner ∈ nestedPresentations bounds (BagForms.sortBags term), ∃ bindings',
        MatchRel pattern partner bindings' ∧ BagForms.BindingsSame bindings bindings' := by
  induction element with
  | var bounds name =>
    intro term bindings _ matched _
    cases matched
    refine ⟨BagForms.sortBags term, self_mem_nestedPresentations _ _, [(name, BagForms.sortBags term)], .fvar,
      .cons ⟨rfl, ?_⟩ .nil⟩
    change canon term = canon (BagForms.sortBags term)
    rw [BagForms.sortBags_eq_canon, canon_idempotent]
  | closed bounds holds canonical =>
    intro term bindings termHolds matched _
    obtain ⟨same, rfl⟩ := closed_match holds canonical termHolds matched
    refine ⟨BagForms.sortBags term, self_mem_nestedPresentations _ _, [], ?_, .nil⟩
    rw [same]
    exact match_self holds
  | @set bound bounds elements inner short each recurse =>
    intro term bindings termHolds matched distinct
    rcases termHolds.cases with ⟨label, rfl, -⟩ | ⟨terms, rfl, termsHold⟩
    · cases matched
    · cases matched with
      | collection _ bag =>
        have names : (inner.toList ++ patternNamesList elements).Nodup := by
          simpa only [patternNames] using distinct
        obtain ⟨grouped, groupedListed, bindings', bag', same⟩ :=
          regroup (nestedPresentations bounds) nestedPresentations_class
            (fun _ => self_mem_nestedPresentations _ _) bag
            (fun other member _ _ held matchedOther =>
              recurse other member held matchedOther
                (names.sublist ((patternNames_sublist member).trans (List.sublist_append_right _ _))))
            (fun other member _ _ matchedOther names' => nested_captures_distinct (each other member) matchedOther names')
            termsHold names short
        refine ⟨.collection .hashSet grouped none, ?_, bindings', .collection (by decide) bag', same⟩
        rw [sortBags_set_values]
        simp only [set, nestedPresentations]
        exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨grouped, groupedListed, rfl⟩)

/-! ## Coherence -/

/-- **Premises that transfer between alike captures**: whenever they hold from some captures, they hold from any
captures alike to them, to alike results, and neither derivation takes a premise step. -/
def PremisesTransfer (relEnv : RelationEnv) (language : LanguageDef) (premises : List Premise) : Prop :=
  ∀ {sites : Pattern} {initial initial' final : Bindings} {witnesses : List Witness},
    BagForms.BindingsSame initial initial' → PremisesValid relEnv language sites initial premises witnesses final →
      premiseStepsList witnesses = [] ∧ ∃ witnesses' final',
        PremisesValid relEnv language sites initial' premises witnesses' final' ∧
          BagForms.BindingsSame final final' ∧ premiseStepsList witnesses' = []

/-- No premises transfer. -/
theorem premisesTransfer_nil {relEnv : RelationEnv} : PremisesTransfer relEnv language [] := by
  intro sites initial initial' final witnesses same valid
  cases valid
  exact ⟨rfl, [], initial', .nil _, same, rfl⟩

/-- **Guards transfer**: relation queries with no arguments read no capture, hold whatever the captures, and take no
step. -/
theorem premisesTransfer_guards {relEnv : RelationEnv} : ∀ {premises : List Premise},
    premises.all BagForms.guard = true → PremisesTransfer relEnv language premises
  | [], _ => premisesTransfer_nil
  | premise :: premises, guarded => by
    simp only [List.all_cons, Bool.and_eq_true] at guarded
    obtain ⟨isGuard, restGuards⟩ := guarded
    intro same valid
    cases valid with
    | cons head tail =>
      cases premise with
      | relationQuery relation arguments =>
        cases arguments with
        | cons _ _ => simp [BagForms.guard] at isGuard
        | nil =>
          cases head with
          | base _ member =>
            obtain ⟨rfl, holds⟩ := BagForms.guard_result member
            obtain ⟨noSteps, witnesses', final', valid', sameFinal, noSteps'⟩ :=
              premisesTransfer_guards restGuards same tail
            exact ⟨by simpa [premiseStepsList, premiseSteps] using noSteps, .base _ :: witnesses', final',
              .cons (.base rfl (holds _)) valid', sameFinal, by simpa [premiseStepsList, premiseSteps] using noSteps'⟩
          | step endpoints _ _ _ => simp [stepEndpoints] at endpoints
      | freshness _ => simp [BagForms.guard] at isGuard
      | congruence _ _ => simp [BagForms.guard] at isGuard
      | scopedStep _ => simp [BagForms.guard] at isGuard
      | forAll _ _ _ => simp [BagForms.guard] at isGuard

/-- **A nested set language with premises, under bounds by depth**: a hereditary set language whose rules' left sides
are nested element patterns under the bounds, with distinct names, and whose rules' premises transfer between alike
captures. -/
structure NestedSetLanguageWith (relEnv : RelationEnv) (language : LanguageDef) (carrier : GrammarRule)
    (bounds : List ℕ) : Prop where
  hereditary : HereditaryLanguage language carrier
  rules : ∀ rule ∈ language.rewrites, NestedElement language carrier.category bounds rule.left ∧
    (patternNames rule.left).Nodup ∧ PremisesTransfer relEnv language rule.premises

/-- **A nested set language, under bounds by depth**: a hereditary set language whose rules' left sides are nested
element patterns under the bounds, with distinct names, and whose rules have no premises. -/
structure NestedSetLanguage (language : LanguageDef) (carrier : GrammarRule) (bounds : List ℕ) : Prop where
  hereditary : HereditaryLanguage language carrier
  rules : ∀ rule ∈ language.rewrites, NestedElement language carrier.category bounds rule.left ∧
    (patternNames rule.left).Nodup ∧ rule.premises = []

variable {relEnv : RelationEnv} {carrier : GrammarRule} {bounds : List ℕ}

/-- A nested set language without premises is one with premises that transfer. -/
theorem NestedSetLanguage.withPremises (lang : NestedSetLanguage language carrier bounds) :
    NestedSetLanguageWith relEnv language carrier bounds where
  hereditary := lang.hereditary
  rules rule member := by
    obtain ⟨element, distinct, noPremises⟩ := lang.rules rule member
    exact ⟨element, distinct, noPremises ▸ premisesTransfer_nil⟩

/-- **Coherence for nested set languages with premises**: a step from any presentation of a canonical hereditary set
is matched, with the same labels and up to canonical form, by a step listed at a presentation whose sets hold each
member between once and their depth's bound times. -/
theorem nested_coherent_with (lang : NestedSetLanguageWith relEnv language carrier bounds) (fuel : ℕ) :
    Coherent relEnv language fuel BagForms.sortBags (hereditary language carrier.category)
      (nestedPresentations bounds) := by
  intro state redex witness contractum _ admitted canonState complete before _ valid
  have canonical := hereditary_canonical (relEnv := relEnv) lang.hereditary
  have redexHolds : Hereditary language carrier.category redex :=
    (hereditary_iff _).mp (canonical.invariant admitted before)
  have redexCanon : BagForms.sortBags redex = state := ((canonical.same admitted before).symm).trans canonState
  cases valid with
  | @rule _ index rule initial final witnesses found matched premises =>
    obtain ⟨element, distinct, transfers⟩ := lang.rules rule (List.mem_of_getElem? found)
    rw [matchPatternForRule_eq_syntactic] at matched
    obtain ⟨partner, listed, bindings', matched', same⟩ :=
      nested_transfer element redexHolds (matchPattern_iff_matchRel.mp matched) distinct
    obtain ⟨noSteps, witnesses', final', premises', sameFinal, noSteps'⟩ := transfers same premises
    rw [redexCanon] at listed
    have matchedFinal : bindings' ∈ matchPatternForRule language rule partner := by
      rw [matchPatternForRule_eq_syntactic]
      exact matchPattern_iff_matchRel.mpr matched'
    have fired := StepValid.rule (relEnv := relEnv) found matchedFinal premises'
    refine ⟨(.rule index bindings' witnesses', applyBindingsScoped (captureSites rule) final' 0 rule.right),
      mem_listedAt.mpr ⟨_, listed, mem_stepsAt_of_enough (enoughAt_iff.mp complete _ listed) fired⟩,
      fun label => BagForms.admits_rule label index _ _ (noSteps.trans noSteps'.symm), ?_⟩
    rw [BagForms.sortBags_eq_canon]
    exact (BagForms.applyBindingsScoped_same (captureSites rule) sameFinal 0 rule.right).symm

/-- **Coherence for nested set languages.** -/
theorem nested_coherent (lang : NestedSetLanguage language carrier bounds) (fuel : ℕ) :
    Coherent relEnv language fuel BagForms.sortBags (hereditary language carrier.category)
      (nestedPresentations bounds) :=
  nested_coherent_with lang.withPremises fuel

/-- **Canonical forms for a nested set language with premises**, for the front door. -/
def nestedFormsWith (lang : NestedSetLanguageWith relEnv language carrier bounds) (fuel : ℕ) :
    CanonicalForms relEnv language fuel :=
  .ofCoherent (hereditary_canonical lang.hereditary) (nested_coherent_with lang fuel)

/-- **Canonical forms for a nested set language**, for the front door. -/
def nestedForms (lang : NestedSetLanguage language carrier bounds) (fuel : ℕ) :
    CanonicalForms relEnv language fuel :=
  .ofCoherent (hereditary_canonical lang.hereditary) (nested_coherent lang fuel)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

import Mettapedia.OSLF.NativeTypes.GeneratedLogic.NestedSetRules

/-!
# Set rules with canonical captures, and their premises

The listed presentations of `NestedSetRules` group copies by member, so a rest captures its members only up to their
order. Premises that compare captured values, such as relation queries, can tell two presentations of one set apart.
This variant lists presentations at which every capture is canonical:

- **The listed presentations** (`capturePresentations`): a canonical term itself, and, for a set, a list of at most the
  outermost bound partners, each a listed presentation of a member under the remaining bounds, followed by the
  canonical form of some of its members, kept when they present the set (`capturePresentations_class`).
- **A match moves to a listed presentation with canonical captures** (`capture_transfer`): each element's match moves
  to a partner, by induction on the element pattern, and the rest captures the canonical set of the remaining members.
- **Premises that hold at canonical captures** (`PremisesCanon`) then hold at the moved captures, which are the
  canonical forms of the original ones (`eq_canonBindings_of_same`). Relation queries over metavariables do, in a
  relation environment that respects canonical forms (`premisesCanon_queries`), and so do guards.
- **Coherence** (`capture_coherent`, `captureForms`): a step from any presentation of a canonical hereditary set is
  matched, with the same labels and up to canonical form, by a step listed at one of these presentations.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec (MatchRel MatchBagRel matchPattern_iff_matchRel)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (canon Same arrange arrange_mem canon_idempotent arrange_eq_of_presents
  canon_collection)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (matchPatternForRule matchPatternForRule_eq_syntactic)
open Mettapedia.GSLT.LanguageDef.WellSorted (isObjectPattern isObjectPatternList)
open Mettapedia.GSLT.LanguageDef.BagNormalForm (isObjectPatternList_iff)

variable {language : LanguageDef} {sort : String}

/-! ## Canonical captures -/

/-- **Every captured value is canonical.** -/
def CanonicalValues (bindings : Bindings) : Prop := ∀ entry ∈ bindings, BagForms.sortBags entry.2 = entry.2

/-- **Canonical captures alike to some captures are their canonical forms.** -/
theorem eq_canonBindings_of_same : ∀ {bindings bindings' : Bindings}, BagForms.BindingsSame bindings bindings' →
    CanonicalValues bindings' → bindings' = BagForms.canonBindings bindings
  | [], [], .nil, _ => rfl
  | ⟨name, value⟩ :: entries, ⟨name', value'⟩ :: entries', .cons heads tail, canonical => by
    have headCanon : canon value' = value' := by
      rw [← BagForms.sortBags_eq_canon]
      exact canonical _ List.mem_cons_self
    have rest := eq_canonBindings_of_same tail fun entry member => canonical entry (List.mem_cons_of_mem _ member)
    obtain ⟨sameName, sameValue⟩ := heads
    simp only at sameName
    subst sameName
    simp only [BagForms.canonBindings, List.map_cons] at rest ⊢
    rw [← rest]
    have same : canon value = canon value' := sameValue
    rw [same, headCanon]

theorem sortBags_idem (term : Pattern) : BagForms.sortBags (BagForms.sortBags term) = BagForms.sortBags term := by
  rw [BagForms.sortBags_eq_canon, canon_idempotent]

/-! ## The listed presentations -/

/-- Lists of at most a length over the listed items. -/
def listsUpTo (items : List Pattern) (bound : ℕ) : List (List Pattern) :=
  (List.range (bound + 1)).flatMap (listsOf items)

theorem mem_listsUpTo {items members : List Pattern} {bound : ℕ} (short : members.length ≤ bound)
    (inside : ∀ member ∈ members, member ∈ items) : members ∈ listsUpTo items bound :=
  List.mem_flatMap.mpr ⟨members.length, List.mem_range.mpr (by omega), mem_listsOf members inside⟩

/-- **The presentations listed for set rules with canonical captures, under bounds by depth**: a canonical term
itself, and, for a set, at most the outermost bound partners, each a listed presentation of a member under the
remaining bounds, followed by the canonical form of some of its members, when they present the set. -/
def capturePresentations : List ℕ → Pattern → List Pattern
  | [], value => [value]
  | bound :: bounds, value => value :: match value with
    | .collection .hashSet values none =>
      ((listsUpTo (values.flatMap (capturePresentations bounds)) bound).flatMap fun partners =>
        values.sublists.map fun sub => Pattern.collection .hashSet (partners ++ arrange .hashSet sub) none).filter
          fun shown => decide (BagForms.sortBags shown = value)
    | _ => []

theorem self_mem_capturePresentations (bounds : List ℕ) (value : Pattern) :
    value ∈ capturePresentations bounds value := by
  cases bounds <;> simp [capturePresentations]

/-- **A listed presentation presents the term.** -/
theorem capturePresentations_class {bounds : List ℕ} {value shown : Pattern} (canonical : BagForms.sortBags value = value)
    (listed : shown ∈ capturePresentations bounds value) : BagForms.sortBags shown = value := by
  cases bounds with
  | nil =>
    simp only [capturePresentations, List.mem_singleton] at listed
    subst listed
    exact canonical
  | cons bound bounds =>
    rcases List.mem_cons.mp listed with rfl | listed
    · exact canonical
    · split at listed
      · exact of_decide_eq_true (List.mem_filter.mp listed).2
      · exact absurd listed List.not_mem_nil

/-! ## Moving a match to a listed presentation with canonical captures -/

mutual
/-- The rest metavariables of a pattern's collections. -/
def restNames : Pattern → List String
  | .collection _ elements rest => rest.toList ++ restNamesList elements
  | _ => []

/-- The rest metavariables of the collections of the patterns of a list. -/
def restNamesList : List Pattern → List String
  | [] => []
  | pattern :: patterns => restNames pattern ++ restNamesList patterns
end

theorem restNames_sublist : ∀ {patterns : List Pattern} {pattern : Pattern}, pattern ∈ patterns →
    (restNames pattern).Sublist (restNamesList patterns)
  | _ :: _, _, .head _ => List.sublist_append_left _ _
  | _ :: _, _, .tail _ member => (restNames_sublist member).trans (List.sublist_append_right _ _)

/-- **A match of a nested element pattern moves to a listed presentation of the term's canonical form**, with captures
alike to the original ones, each the presentation `pick` chooses for its name and class. The choice must keep each
class, be listed at the bounds of every held term of the class, and leave the rests' captures canonical; it holds of
the held terms (`extra`) under their bounds, and descends from a set to its members. -/
theorem capture_transfer_with (extra : List ℕ → Pattern → Prop)
    (descend : ∀ {bound : ℕ} {bounds : List ℕ} {values : List Pattern}, extra (bound :: bounds) (set values) →
      ∀ value ∈ values, extra bounds value)
    (pick : String → Pattern → Pattern)
    (pickClass : ∀ name value, BagForms.sortBags value = value → BagForms.sortBags (pick name value) = value)
    (picked : ∀ {bounds : List ℕ} {name : String} {term : Pattern}, IsObject term → extra bounds term →
      pick name (BagForms.sortBags term) ∈ capturePresentations bounds (BagForms.sortBags term))
    {bounds : List ℕ} {pattern : Pattern} (element : NestedElement language sort bounds pattern) :
    ∀ {term : Pattern} {bindings : Bindings}, IsObject term → extra bounds term →
      MatchRel pattern term bindings → (patternNames pattern).Nodup →
      (∀ name ∈ restNames pattern, ∀ value, pick name value = value) →
      ∃ partner ∈ capturePresentations bounds (BagForms.sortBags term), ∃ bindings',
        MatchRel pattern partner bindings' ∧ BagForms.BindingsSame bindings bindings' ∧
          ∀ entry ∈ bindings', entry.2 = pick entry.1 (BagForms.sortBags entry.2) := by
  induction element with
  | var bounds name =>
    intro term bindings termHolds termExtra matched _ _
    cases matched
    have kept : BagForms.sortBags (pick name (BagForms.sortBags term)) = BagForms.sortBags term :=
      pickClass name _ (sortBags_idem term)
    refine ⟨pick name (BagForms.sortBags term), picked termHolds termExtra, [(name, pick name (BagForms.sortBags term))],
      .fvar, .cons ⟨rfl, ?_⟩ .nil, fun entry member => ?_⟩
    · change canon term = canon (pick name (BagForms.sortBags term))
      rw [← BagForms.sortBags_eq_canon, kept]
    · rw [List.mem_singleton.mp member]
      simp only
      rw [kept]
  | closed bounds holds canonical =>
    intro term bindings termHolds _ matched _ _
    obtain ⟨same, rfl⟩ := closed_match_object holds canonical termHolds matched
    refine ⟨BagForms.sortBags term, self_mem_capturePresentations _ _, [], ?_, .nil,
      fun _ member => absurd member List.not_mem_nil⟩
    rw [same]
    exact match_self holds
  | @set bound bounds elements inner short each recurse =>
    intro term bindings termObject termExtra matched distinct restsKept
    · cases matched with
      | @collection _ _ _ terms rest _ _ bag =>
        have parts : rest.isNone = true ∧ isObjectPatternList terms = true := by
          simpa [IsObject, isObjectPattern] using termObject
        obtain rfl : rest = none := Option.isNone_iff_eq_none.mp parts.1
        have termsHold : ∀ value ∈ terms, IsObject value := fun value member =>
          isObjectPatternList_iff.mp parts.2 value member
        rw [show Pattern.collection .hashSet terms none = set terms from rfl] at termExtra ⊢
        have names : (inner.toList ++ patternNamesList elements).Nodup := by
          simpa only [patternNames] using distinct
        obtain ⟨partners, matchedTerms, remaining, length, partnersListed, split, noRemaining, transfer⟩ :=
          bag_transfer_with (capturePresentations bounds) (fun value => IsObject value ∧ extra bounds value)
            (fun entry => entry.2 = pick entry.1 (BagForms.sortBags entry.2)) bag
            (fun other member _ _ held matchedOther =>
              recurse other member held.1 held.2 matchedOther
                (names.sublist ((patternNames_sublist member).trans (List.sublist_append_right _ _)))
                fun name inOther => restsKept name (by
                  simp only [restNames]
                  exact List.mem_append_right _ ((restNames_sublist member).subset inOther)))
            (fun other member _ _ matchedOther names' => nested_captures_distinct (each other member) matchedOther names')
            (fun value member => ⟨termsHold value member, descend termExtra value member⟩) names
        let values := arrange .hashSet (terms.map BagForms.sortBags)
        let sub := values.filter fun value => decide (value ∈ remaining.map BagForms.sortBags)
        let extras := arrange .hashSet sub
        have termClass : ∀ term ∈ terms, BagForms.sortBags term ∈ values :=
          fun term member => (arrange_mem _).mpr (List.mem_map_of_mem member)
        have extrasMembers : ∀ value, value ∈ extras ↔ value ∈ remaining.map BagForms.sortBags := by
          intro value
          rw [arrange_mem, List.mem_filter, decide_eq_true_eq]
          constructor
          · exact fun both => both.2
          · intro inRemaining
            obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp inRemaining
            exact ⟨termClass original (split.symm.subset (List.mem_append_right _ originalMember)), inRemaining⟩
        have extrasCanonical : ∀ extra ∈ extras, BagForms.sortBags extra = extra := by
          intro extra member
          obtain ⟨original, -, rfl⟩ := List.mem_map.mp ((extrasMembers extra).mp member)
          exact sortBags_idem original
        have extrasMap : extras.map canon = extras := by
          conv_rhs => rw [← List.map_id extras]
          exact List.map_congr_left fun extra member => by
            rw [← BagForms.sortBags_eq_canon]
            exact extrasCanonical extra member
        have extrasSame : Same (.collection .hashSet remaining none) (.collection .hashSet extras none) := by
          change canon _ = canon _
          rw [canon_collection, canon_collection, extrasMap]
          congr 1
          apply arrange_eq_of_presents
          intro other
          rw [extrasMembers, ← BagForms.sortBags_eq_canon]
        have extrasSet : BagForms.sortBags (.collection .hashSet extras none) = .collection .hashSet extras none := by
          rw [BagForms.sortBags_eq_canon, canon_collection, extrasMap]
          congr 1
          exact arrange_eq_of_presents (kind := .hashSet) fun other => arrange_mem other
        have noExtras : inner = none → extras = [] := by
          intro none
          have empty : sub = [] := List.filter_eq_nil_iff.mpr fun value _ => by simp [noRemaining none]
          simp only [extras, empty]
          rfl
        have restGood : ∀ name, inner = some name →
            (Pattern.collection .hashSet extras none) =
              pick name (BagForms.sortBags (.collection .hashSet extras none)) := by
          intro name isRest
          rw [extrasSet, restsKept name (by simp [restNames, isRest])]
        obtain ⟨bindings', bag', sameBindings, goodValues⟩ := transfer extras noExtras extrasSame restGood
        refine ⟨.collection .hashSet (partners ++ extras) none, ?_, bindings', .collection (by decide) bag', sameBindings,
          goodValues⟩
        rw [sortBags_set_values]
        simp only [set, capturePresentations]
        refine List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨?_, ?_⟩)
        · refine List.mem_flatMap.mpr ⟨partners, mem_listsUpTo ?_ fun partner member => ?_,
            List.mem_map.mpr ⟨sub, List.mem_sublists.mpr List.filter_sublist, rfl⟩⟩
          · rw [length]
            omega
          · obtain ⟨term, termMember, listed⟩ := exists_right_of_forall₂ partnersListed partner member
            exact List.mem_flatMap.mpr ⟨BagForms.sortBags term,
              termClass term (split.symm.subset (List.mem_append_left _ termMember)), listed⟩
        · refine decide_eq_true ?_
          rw [show Pattern.collection .hashSet (partners ++ extras) none = set (partners ++ extras) from rfl,
            sortBags_set_values]
          show set _ = set _
          congr 1
          apply arrange_eq_of_presents
          intro other
          simp only [List.map_append, List.mem_append]
          constructor
          · rintro (inPartners | inExtras)
            · obtain ⟨partner, partnerMember, rfl⟩ := List.mem_map.mp inPartners
              obtain ⟨term, termMember, listed⟩ := exists_right_of_forall₂ partnersListed partner partnerMember
              rw [capturePresentations_class (sortBags_idem term) listed]
              exact List.mem_map_of_mem (split.symm.subset (List.mem_append_left _ termMember))
            · obtain ⟨extra, extraMember, rfl⟩ := List.mem_map.mp inExtras
              rw [extrasCanonical extra extraMember]
              obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp ((extrasMembers extra).mp extraMember)
              exact List.mem_map_of_mem (split.symm.subset (List.mem_append_right _ originalMember))
          · intro inTerms
            obtain ⟨term, termMember, rfl⟩ := List.mem_map.mp inTerms
            rcases List.mem_append.mp (split.subset termMember) with inMatched | inRemaining
            · obtain ⟨partner, partnerMember, listed⟩ := exists_left_of_forall₂ partnersListed term inMatched
              exact Or.inl (List.mem_map.mpr ⟨partner, partnerMember, capturePresentations_class (sortBags_idem term) listed⟩)
            · have inExtras := (extrasMembers (BagForms.sortBags term)).mpr (List.mem_map_of_mem inRemaining)
              exact Or.inr (List.mem_map.mpr ⟨_, inExtras, extrasCanonical _ inExtras⟩)

/-- **A match of a nested element pattern moves to a listed presentation of the term's canonical form, with canonical
captures alike to the original ones.** -/
theorem capture_transfer {bounds : List ℕ} {pattern : Pattern} (element : NestedElement language sort bounds pattern) :
    ∀ {term : Pattern} {bindings : Bindings}, Hereditary language sort term → MatchRel pattern term bindings →
      (patternNames pattern).Nodup →
      ∃ partner ∈ capturePresentations bounds (BagForms.sortBags term), ∃ bindings',
        MatchRel pattern partner bindings' ∧ BagForms.BindingsSame bindings bindings' ∧ CanonicalValues bindings' := by
  intro term bindings termHolds matched distinct
  obtain ⟨partner, listed, bindings', matched', same, kept⟩ :=
    capture_transfer_with (fun _ _ => True) (fun _ _ _ => trivial) (fun _ value => value) (fun _ _ canonical => canonical)
      (fun _ _ => self_mem_capturePresentations _ _) element termHolds.object trivial matched distinct (fun _ _ _ => rfl)
  exact ⟨partner, listed, bindings', matched', same, fun entry member => (kept entry member).symm⟩

/-! ## Premises at canonical captures -/

/-- **Premises that hold at canonical captures**: whenever they hold from some captures, they hold from their canonical
forms, to the canonical forms of the results, and neither derivation takes a premise step. -/
def PremisesCanon (relEnv : RelationEnv) (language : LanguageDef) (premises : List Premise) : Prop :=
  ∀ {sites : Pattern} {initial final : Bindings} {witnesses : List Witness},
    PremisesValid relEnv language sites initial premises witnesses final →
      premiseStepsList witnesses = [] ∧ ∃ witnesses',
        PremisesValid relEnv language sites (BagForms.canonBindings initial) premises witnesses'
          (BagForms.canonBindings final) ∧ premiseStepsList witnesses' = []

/-- **Relation queries over metavariables hold at canonical captures**, in a relation environment that respects
canonical forms; guards are such queries. -/
theorem premisesCanon_queries {relEnv : RelationEnv} (respects : BagForms.RespectsCanon relEnv) {premises : List Premise}
    (queried : premises.all BagForms.query = true) : PremisesCanon relEnv language premises :=
  fun valid => BagForms.queries_canon respects premises queried valid

/-- **A premise that holds at canonical captures**: whenever it holds from some captures, it holds from their
canonical forms, to the canonical form of the result, and neither derivation takes a premise step. -/
def PremiseCanon (relEnv : RelationEnv) (language : LanguageDef) (premise : Premise) : Prop :=
  ∀ {sites : Pattern} {initial result : Bindings} {witness : Witness},
    PremiseValid relEnv language sites initial premise witness result →
      premiseSteps witness = [] ∧ ∃ witness',
        PremiseValid relEnv language sites (BagForms.canonBindings initial) premise witness'
          (BagForms.canonBindings result) ∧ premiseSteps witness' = []

/-- **Premises each of which holds at canonical captures hold there together.** -/
theorem premisesCanon_of_each {relEnv : RelationEnv} : ∀ {premises : List Premise},
    (∀ premise ∈ premises, PremiseCanon relEnv language premise) → PremisesCanon relEnv language premises
  | [], _ => fun valid => by
    cases valid
    exact ⟨rfl, [], .nil _, rfl⟩
  | premise :: premises, each => fun valid => by
    cases valid with
    | cons head tail =>
      obtain ⟨headSteps, witness', head', headSteps'⟩ := each premise List.mem_cons_self head
      obtain ⟨tailSteps, witnesses', tail', tailSteps'⟩ :=
        premisesCanon_of_each (fun other member => each other (List.mem_cons_of_mem _ member)) tail
      exact ⟨by simp [premiseStepsList, headSteps, tailSteps], witness' :: witnesses', .cons head' tail',
        by simp [premiseStepsList, headSteps', tailSteps']⟩

/-- **A relation query over metavariables holds at canonical captures**, in a relation environment that respects
canonical forms. -/
theorem premiseCanon_query {relEnv : RelationEnv} (respects : BagForms.RespectsCanon relEnv) {relation : String}
    {arguments : List Pattern} (metavariables : arguments.all BagForms.isMetavariable = true) :
    PremiseCanon relEnv language (.relationQuery relation arguments) := by
  intro sites initial result witness valid
  cases valid with
  | base _ member =>
    exact ⟨rfl, .base _, .base rfl (BagForms.query_canon respects metavariables member), rfl⟩
  | step endpoints _ _ _ => simp [stepEndpoints] at endpoints

theorem canonBindings_bindParameter (bindings : Bindings) (parameter : String) (element : Pattern) :
    BagForms.canonBindings (bindParameter bindings parameter element) =
      bindParameter (BagForms.canonBindings bindings) parameter (canon element) := by
  simp only [BagForms.canonBindings, bindParameter, List.map_cons]
  congr 1
  rw [List.filter_map]
  rfl

/-- The bodies of a quantified premise hold at each element, without premise steps. -/
theorem forAll_each {relEnv : RelationEnv} {sites : Pattern} {bindings : Bindings} {parameter : String}
    {body : Premise} (bodyCanon : PremiseCanon relEnv language body) : ∀ {elements : List Pattern}
    {bodies : List Witness}, ForAllValid relEnv language sites bindings parameter body elements bodies →
      premiseStepsList bodies = [] ∧ ∀ element ∈ elements, ∃ witness result,
        PremiseValid relEnv language sites (BagForms.canonBindings (bindParameter bindings parameter element)) body
          witness result ∧ premiseSteps witness = []
  | [], [], .nil => ⟨rfl, fun _ member => absurd member List.not_mem_nil⟩
  | _ :: _, _ :: _, .cons head tail => by
    obtain ⟨headSteps, witness', head', headSteps'⟩ := bodyCanon head
    obtain ⟨tailSteps, tailEach⟩ := forAll_each bodyCanon tail
    refine ⟨by simp [premiseStepsList, headSteps, tailSteps], fun element member => ?_⟩
    rcases List.mem_cons.mp member with rfl | inTail
    · exact ⟨witness', _, head', headSteps'⟩
    · exact tailEach element inTail

/-- Quantified bodies built at the elements of a list. -/
theorem forAllValid_of_each {relEnv : RelationEnv} {sites : Pattern} {bindings : Bindings} {parameter : String}
    {body : Premise} : ∀ {elements : List Pattern}, (∀ element ∈ elements, ∃ witness result,
      PremiseValid relEnv language sites (bindParameter bindings parameter element) body witness result ∧
        premiseSteps witness = []) →
      ∃ bodies, ForAllValid relEnv language sites bindings parameter body elements bodies ∧ premiseStepsList bodies = []
  | [], _ => ⟨[], .nil, rfl⟩
  | element :: elements, each => by
    obtain ⟨witness, result, valid, steps⟩ := each element List.mem_cons_self
    obtain ⟨bodies, rest, restSteps⟩ := forAllValid_of_each fun other member => each other (List.mem_cons_of_mem _ member)
    exact ⟨witness :: bodies, .cons valid rest, by simp [premiseStepsList, steps, restSteps]⟩

/-- **A universally quantified premise holds at canonical captures** when its body does: the canonical form of the
quantified collection holds the canonical forms of its elements. -/
theorem premiseCanon_forAll {relEnv : RelationEnv} {collection parameter : String} {body : Premise}
    (bodyCanon : PremiseCanon relEnv language body) :
    PremiseCanon relEnv language (.forAll collection parameter body) := by
  intro sites initial result witness valid
  cases valid with
  | base base _ => simp [isBase] at base
  | step endpoints _ _ _ => simp [stepEndpoints] at endpoints
  | @forAll _ _ _ _ _ kind elements bodies found bodiesValid =>
    obtain ⟨steps, each⟩ := forAll_each bodyCanon bodiesValid
    have found' : (BagForms.canonBindings initial).lookup collection =
        some (.collection kind (arrange kind (elements.map canon)) none) := by
      rw [BagForms.lookup_canonBindings, found]
      simp only [Option.map_some]
      rw [canon_collection]
    obtain ⟨bodies', valid', steps'⟩ := forAllValid_of_each (relEnv := relEnv) (sites := sites)
      (bindings := BagForms.canonBindings initial) (parameter := parameter) (body := body)
      (elements := arrange kind (elements.map canon)) fun element' member => by
        obtain ⟨element, elementMember, rfl⟩ := List.mem_map.mp ((arrange_mem element').mp member)
        obtain ⟨witness, result', bodyValid, bodySteps⟩ := each element elementMember
        rw [canonBindings_bindParameter] at bodyValid
        exact ⟨witness, result', bodyValid, bodySteps⟩
    exact ⟨by simpa [premiseSteps] using steps, .forAll bodies', .forAll found' valid',
      by simpa [premiseSteps] using steps'⟩

/-! ## Coherence -/

/-- **A set language with canonical captures, under bounds by depth**: a hereditary set language whose rules' left
sides are nested element patterns under the bounds, with distinct names, and whose rules' premises hold at canonical
captures. -/
structure CaptureSetLanguage (relEnv : RelationEnv) (language : LanguageDef) (carrier : GrammarRule)
    (bounds : List ℕ) : Prop where
  hereditary : HereditaryLanguage language carrier
  rules : ∀ rule ∈ language.rewrites, NestedElement language carrier.category bounds rule.left ∧
    (patternNames rule.left).Nodup ∧ PremisesCanon relEnv language rule.premises

variable {relEnv : RelationEnv} {carrier : GrammarRule} {bounds : List ℕ}

/-- **Coherence for set languages with canonical captures**: a step from any presentation of a canonical hereditary
set is matched, with the same labels and up to canonical form, by a step listed at a presentation at which every
capture is canonical. -/
theorem capture_coherent (lang : CaptureSetLanguage relEnv language carrier bounds) (fuel : ℕ) :
    Coherent relEnv language fuel BagForms.sortBags (hereditary language carrier.category)
      (capturePresentations bounds) := by
  intro state redex witness contractum _ admitted canonState complete before _ valid
  have canonical := hereditary_canonical (relEnv := relEnv) lang.hereditary
  have redexHolds : Hereditary language carrier.category redex :=
    (hereditary_iff _).mp (canonical.invariant admitted before)
  have redexCanon : BagForms.sortBags redex = state := ((canonical.same admitted before).symm).trans canonState
  cases valid with
  | @rule _ index rule initial final witnesses found matched premises =>
    obtain ⟨element, distinct, holdsCanon⟩ := lang.rules rule (List.mem_of_getElem? found)
    rw [matchPatternForRule_eq_syntactic] at matched
    obtain ⟨partner, listed, bindings', matched', same, canonicalValues⟩ :=
      capture_transfer element redexHolds (matchPattern_iff_matchRel.mp matched) distinct
    have bindingsIs := eq_canonBindings_of_same same canonicalValues
    obtain ⟨noSteps, witnesses', premises', noSteps'⟩ := holdsCanon premises
    rw [← bindingsIs] at premises'
    rw [redexCanon] at listed
    have matchedFinal : bindings' ∈ matchPatternForRule language rule partner := by
      rw [matchPatternForRule_eq_syntactic]
      exact matchPattern_iff_matchRel.mpr matched'
    have fired := StepValid.rule (relEnv := relEnv) found matchedFinal premises'
    refine ⟨(.rule index bindings' witnesses',
      applyBindingsScoped (captureSites rule) (BagForms.canonBindings final) 0 rule.right),
      mem_listedAt.mpr ⟨_, listed, mem_stepsAt_of_enough (enoughAt_iff.mp complete _ listed) fired⟩,
      fun label => BagForms.admits_rule label index _ _ (noSteps.trans noSteps'.symm), ?_⟩
    rw [BagForms.sortBags_eq_canon]
    exact BagForms.applyBindingsScoped_same (captureSites rule) (BagForms.bindingsSame_canon final) 0 rule.right

/-- **Canonical forms for a set language with canonical captures**, for the front door. -/
def captureForms (lang : CaptureSetLanguage relEnv language carrier bounds) (fuel : ℕ) :
    CanonicalForms relEnv language fuel :=
  .ofCoherent (hereditary_canonical lang.hereditary) (capture_coherent lang fuel)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

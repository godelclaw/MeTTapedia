import Mettapedia.OSLF.Framework.HerbrandBridge
import Mettapedia.OSLF.Framework.BackwardNarrowingGround
import Mettapedia.GSLT.Poly.FirstOrderLanguage
import Mettapedia.OSLF.MeTTaIL.ScopedPattern

/-!
# Sorts through the Herbrand bridge

A first-order grammar with distinct labels (`Grammar`) sorts the Herbrand terms of its language
(`sortingOf`): a constant or a symbol has the category of its constructor, and an argument position
the base sort of its parameter. The well-sorted Herbrand terms are the images of the closed trees of
the grammar's first-order signature (`herbrandOf_sorted`, `exists_herbrandOf`), and so exactly the
encodings of the well-sorted states of the compiled plan (`sorted_iff`).

The backward box over the well-sorted states of a language is the backward box over well-sorted
Herbrand terms for root steps (`pastBox_iff`). The sorted root checker decides it, splitting open
premises by sort (`pastBox_proved`, `pastBox_refuted`), and the compiled plan has the same backward
box (`compiled_pastBox_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.HerbrandBridge

open Mettapedia.Logic.LP
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.Framework.BackwardNarrowing (Sorting WellSorted Splitting herbrandRootSpan rootPastBox
  PastBox Instance)
open Mettapedia.GSLT.Poly.FirstOrderLanguage (baseSort? FirstOrderRule signature toPattern)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.GeneralCanonicalAgreement (RootProfile)
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (gsltSpan)
open Mettapedia.OSLF.Framework.BackwardSearch (between box_between_transfer)

/-! ## The sorting of a first-order grammar -/

/-- **The grammar profile**: every constructor is first order, and labels are distinct. -/
structure Grammar (language : LanguageDef) : Prop where
  firstOrder : ∀ rule ∈ language.terms, FirstOrderRule rule
  labels : (language.terms.map (·.label)).Nodup

/-- The grammar profile, decided. -/
def grammarCheck (language : LanguageDef) : Bool :=
  language.terms.all (fun rule => rule.params.all fun parameter => (baseSort? parameter).isSome) &&
    decide (language.terms.map (·.label)).Nodup

theorem Grammar.of_check {language : LanguageDef} (checked : grammarCheck language = true) : Grammar language where
  firstOrder rule member parameter inside :=
    List.all_eq_true.mp (List.all_eq_true.mp (Bool.and_eq_true_iff.mp checked).1 rule member) parameter inside
  labels := of_decide_eq_true (Bool.and_eq_true_iff.mp checked).2

/-- The first-order constructor of a label at an arity. -/
def ruleOf (language : LanguageDef) (label : String) (count : ℕ) : Option GrammarRule :=
  (language.terms.find? (·.label == label)).filter fun rule =>
    rule.params.length == count && rule.params.all fun parameter => (baseSort? parameter).isSome

theorem ruleOf_some {language : LanguageDef} {label : String} {count : ℕ} {rule : GrammarRule}
    (found : ruleOf language label count = some rule) :
    rule ∈ language.terms ∧ rule.label = label ∧ rule.params.length = count ∧ FirstOrderRule rule := by
  obtain ⟨found, kept⟩ := Option.filter_eq_some_iff.mp found
  obtain ⟨length, firstOrder⟩ := Bool.and_eq_true_iff.mp kept
  exact ⟨List.mem_of_find?_eq_some found, by simpa using List.find?_some found, beq_iff_eq.mp length,
    fun parameter inside => List.all_eq_true.mp firstOrder parameter inside⟩

theorem ruleOf_rule {language : LanguageDef} (labels : (language.terms.map (·.label)).Nodup)
    {rule : GrammarRule} (member : rule ∈ language.terms) (firstOrder : FirstOrderRule rule) :
    ruleOf language rule.label rule.params.length = some rule := by
  obtain ⟨found, foundIs⟩ : ∃ found, language.terms.find? (·.label == rule.label) = some found := by
    cases read : language.terms.find? (·.label == rule.label) with
    | none => exact absurd (List.find?_eq_none.mp read rule member) (by simp)
    | some found => exact ⟨found, rfl⟩
  have same : found = rule := List.inj_on_of_nodup_map labels (List.mem_of_find?_eq_some foundIs) member
    (by simpa using List.find?_some foundIs)
  subst same
  unfold ruleOf
  rw [foundIs]
  exact Option.filter_eq_some_iff.mpr ⟨rfl, by simpa [FirstOrderRule] using firstOrder⟩

/-- **The sorting of a first-order grammar.** -/
def sortingOf (language : LanguageDef) : Sorting String (String × ℕ) String Prod.snd where
  constant label := (ruleOf language label 0).map (·.category)
  symbol symbol := if symbol.2 = 0 then none else (ruleOf language symbol.1 symbol.2).map (·.category)
  argument symbol position :=
    ((ruleOf language symbol.1 symbol.2).bind fun rule => rule.params[position.1]?.bind baseSort?).getD ""
  constantsOf sort := (language.terms.filter fun rule => rule.params.isEmpty && rule.category == sort).map (·.label)
  symbolsOf sort := (language.terms.filter fun rule => !rule.params.isEmpty && rule.category == sort).map
    fun rule => (rule.label, rule.params.length)
  constants_complete label sort found := by
    obtain ⟨rule, ruleFound, rfl⟩ := Option.map_eq_some_iff.mp found
    obtain ⟨member, rfl, empty, _⟩ := ruleOf_some ruleFound
    exact List.mem_map.mpr ⟨rule, List.mem_filter.mpr ⟨member, by simp [List.length_eq_zero_iff.mp empty]⟩, rfl⟩
  symbols_complete symbol sort found := by
    obtain ⟨label, count⟩ := symbol
    simp only at found
    split_ifs at found with zero
    obtain ⟨rule, ruleFound, rfl⟩ := Option.map_eq_some_iff.mp found
    obtain ⟨member, rfl, rfl, _⟩ := ruleOf_some ruleFound
    refine List.mem_map.mpr ⟨rule, List.mem_filter.mpr ⟨member, ?_⟩, rfl⟩
    simpa [List.isEmpty_iff, ← List.length_eq_zero_iff] using zero

/-! ## Herbrand images of the grammar's closed trees -/

variable {language : LanguageDef}

/-- A closed tree of the grammar's first-order signature. -/
abbrev Tree (language : LanguageDef) (sort : String) :=
  Mettapedia.OSLF.SortedConstructors.Term (signature language) sort

/-- The Herbrand term of a closed tree. -/
def herbrandOf : {sort : String} → Tree language sort → Term Labels
  | _, .node rule arguments =>
      if rule.1.params.length = 0 then .const rule.1.label
      else .app (rule.1.label, rule.1.params.length) fun position => herbrandOf (arguments position)

theorem herbrandOf_cast {first second : String} (same : first = second) (tree : Tree language first) :
    herbrandOf (same ▸ tree) = herbrandOf tree := by
  subst same
  rfl

theorem decode_herbrandOf : {sort : String} → (tree : Tree language sort) → decode (herbrandOf tree) = toPattern tree
  | _, .node rule arguments => by
    unfold herbrandOf
    split_ifs with empty
    · simp only [decode, toPattern]
      exact congrArg _ (List.eq_nil_of_length_eq_zero (by simpa using empty)).symm
    · simp only [decode, toPattern]
      exact congrArg _ (List.ofFn_inj.mpr (funext fun position => decode_herbrandOf (arguments position)))

theorem herbrandOf_canonical : {sort : String} → (tree : Tree language sort) → Canonical (herbrandOf tree)
  | _, .node rule arguments => by
    unfold herbrandOf
    split_ifs with empty
    · trivial
    · exact ⟨Nat.pos_of_ne_zero empty, fun position => herbrandOf_canonical (arguments position)⟩

theorem encode_toPattern {sort : String} (tree : Tree language sort) :
    encode [] (toPattern tree) = some (herbrandOf tree) := by
  rw [← decode_herbrandOf]
  exact encode_decode _ (herbrandOf_canonical tree)

theorem argument_input (rule : Mettapedia.GSLT.Poly.FirstOrderLanguage.FirstOrderConstructor language)
    (found : ruleOf language rule.1.label rule.1.params.length = some rule.1) (position : Fin rule.1.params.length) :
    (sortingOf language).argument (rule.1.label, rule.1.params.length) position =
      (signature language).input rule position := by
  simp only [sortingOf, found, Option.bind_some, List.getElem?_eq_getElem position.2]
  have found := Mettapedia.GSLT.Poly.FirstOrderLanguage.baseSort?_input rule position
  rw [List.get_eq_getElem] at found
  rw [found]
  rfl

/-- **The Herbrand term of a closed tree is well-sorted at its sort.** -/
theorem herbrandOf_sorted (labels : (language.terms.map (·.label)).Nodup) :
    {sort : String} → (tree : Tree language sort) → WellSorted (sortingOf language) (herbrandOf tree) sort
  | _, .node rule arguments => by
    have found := ruleOf_rule labels rule.2.1 rule.2.2
    unfold herbrandOf
    split_ifs with empty
    · show (ruleOf language rule.1.label 0).map (·.category) = some rule.1.category
      rw [← empty, found]
      rfl
    · refine ⟨?_, fun position => ?_⟩
      · show (if rule.1.params.length = 0 then none else _) = some rule.1.category
        rw [if_neg empty, found]
        rfl
      · show WellSorted _ (herbrandOf (arguments position)) _
        rw [argument_input rule found position]
        exact herbrandOf_sorted labels (arguments position)

/-- **Every well-sorted Herbrand term is the image of a closed tree.** -/
theorem exists_herbrandOf :
    (term : Term Labels) → (sort : String) → WellSorted (sortingOf language) term sort →
      ∃ tree : Tree language sort, herbrandOf tree = term
  | .var _, _, sorted => sorted.elim
  | .const label, sort, sorted => by
    obtain ⟨rule, ruleFound, rfl⟩ := Option.map_eq_some_iff.mp sorted
    obtain ⟨member, rfl, empty, firstOrder⟩ := ruleOf_some ruleFound
    refine ⟨.node (signature := signature language) ⟨rule, member, firstOrder⟩
      fun position => absurd position.2 (by simp [empty]), ?_⟩
    simp [herbrandOf, empty]
  | .app (label, count) arguments, sort, ⟨sortedSymbol, sortedArguments⟩ => by
    have recursive := fun position => exists_herbrandOf (arguments position) _ (sortedArguments position)
    change (if count = 0 then none else _) = some sort at sortedSymbol
    split_ifs at sortedSymbol with zero
    obtain ⟨rule, found, rfl⟩ := Option.map_eq_some_iff.mp sortedSymbol
    obtain ⟨member, rfl, rfl, firstOrder⟩ := ruleOf_some found
    let constructor : Mettapedia.GSLT.Poly.FirstOrderLanguage.FirstOrderConstructor language :=
      ⟨rule, member, firstOrder⟩
    have children : ∀ position : Fin rule.params.length,
        ∃ child : Tree language ((signature language).input constructor position),
          herbrandOf child = arguments position := by
      intro position
      obtain ⟨child, image⟩ := recursive position
      have same := argument_input constructor found position
      exact ⟨same ▸ child, (herbrandOf_cast same child).trans image⟩
    choose child image using children
    refine ⟨.node (signature := signature language) constructor child, ?_⟩
    rw [herbrandOf, if_neg (show ¬ constructor.1.params.length = 0 from zero)]
    exact congrArg _ (funext image)

theorem wellSorted_canonical {term : Term Labels} {sort : String}
    (sorted : WellSorted (sortingOf language) term sort) : Canonical term := by
  obtain ⟨tree, rfl⟩ := exists_herbrandOf term sort sorted
  exact herbrandOf_canonical tree

/-! ## Well-sorted states are the well-sorted encodings -/

theorem toPattern_metadata : {sort : String} → (tree : Tree language sort) →
    (toPattern tree).hasCanonicalBinderMetadata = true
  | _, .node _ arguments => by
    simp only [toPattern, Pattern.hasCanonicalBinderMetadata]
    have pointwise : ∀ patterns : List Pattern, (∀ pattern ∈ patterns, pattern.hasCanonicalBinderMetadata = true) →
        Pattern.hasCanonicalBinderMetadataList patterns = true := by
      intro patterns each
      induction patterns with
      | nil => rfl
      | cons pattern patterns ih =>
        simp only [Pattern.hasCanonicalBinderMetadataList, Bool.and_eq_true]
        exact ⟨each pattern List.mem_cons_self, ih fun other member => each other (List.mem_cons_of_mem _ member)⟩
    apply pointwise
    intro pattern member
    obtain ⟨position, rfl⟩ := List.mem_ofFn.mp member
    exact toPattern_metadata (arguments position)

theorem toPattern_scoped : {sort : String} → (tree : Tree language sort) → (toPattern tree).isWellScopedAt 0 = true
  | _, .node _ arguments => by
    simp only [toPattern, Pattern.isWellScopedAt]
    rw [Mettapedia.OSLF.MeTTaIL.ScopedPattern.isWellScopedListAt_eq_true_iff]
    intro pattern member
    obtain ⟨position, rfl⟩ := List.mem_ofFn.mp member
    exact toPattern_scoped (arguments position)

/-- **A ground pattern is a well-sorted state exactly when its encoding is well-sorted.** -/
theorem sorted_iff (grammar : Grammar language) {state : Pattern} {encoded : Term Labels}
    (read : encode [] state = some encoded) (sort : String) :
    Sorted language (.base sort) state ↔ WellSorted (sortingOf language) encoded sort := by
  constructor
  · rintro ⟨typed, _, objects, _⟩
    obtain ⟨tree, rfl⟩ :=
      Mettapedia.GSLT.Poly.FirstOrderLanguage.exists_toPattern grammar.firstOrder _ sort typed objects
    rw [encode_toPattern, Option.some.injEq] at read
    exact read ▸ herbrandOf_sorted grammar.labels tree
  · intro sorted
    obtain ⟨tree, rfl⟩ := exists_herbrandOf encoded sort sorted
    obtain rfl : state = toPattern tree := (decode_encode state read).symm.trans (decode_herbrandOf tree)
    exact ⟨Mettapedia.GSLT.Poly.FirstOrderLanguage.toPattern_hasType tree, toPattern_metadata tree,
      Mettapedia.GSLT.Poly.FirstOrderLanguage.toPattern_isObjectPattern tree, toPattern_scoped tree⟩

/-- Every well-sorted state is first order. -/
theorem sorted_encode (grammar : Grammar language) {state : Pattern} {sort : String}
    (sorted : Sorted language (.base sort) state) :
    ∃ encoded, encode [] state = some encoded ∧ WellSorted (sortingOf language) encoded sort := by
  obtain ⟨tree, rfl⟩ :=
    Mettapedia.GSLT.Poly.FirstOrderLanguage.exists_toPattern grammar.firstOrder _ sort sorted.1 sorted.2.2.1
  exact ⟨_, encode_toPattern tree, herbrandOf_sorted grammar.labels tree⟩

/-! ## The backward box over well-sorted states -/

variable {sort : String}

/-- **The backward box over the well-sorted states of a language is the backward box over
well-sorted Herbrand terms**, for root steps. -/
theorem pastBox_iff (grammar : Grammar language) (profile : Profile language) {state : Pattern}
    {encoded : Term Labels} (read : encode [] state = some encoded) (stateSorted : Sorted language (.base sort) state)
    (property : Pattern → Prop) :
    derivedBox (between (languageSpan language) (Sorted language (.base sort))) property state ↔
      derivedBox (herbrandRootSpan (encodeRules language) (Splitting.sorted (sortingOf language) sort).counted)
        (fun term => property (decode term)) encoded := by
  constructor
  · rintro holds ⟨⟨previous, target⟩, ⟨herbrand, member, substitution, leftSide, rightSide⟩, previousSorted, _⟩ ends
    change target = encoded at ends
    subst ends
    have previousRead := encode_decode previous (wellSorted_canonical previousSorted)
    obtain ⟨next, nextRead, step⟩ := step_backward profile previousRead member leftSide
    rw [rightSide] at nextRead
    obtain rfl : next = state := encode_injective nextRead read
    exact holds ⟨⟨(decode previous, next), step⟩, (sorted_iff grammar previousRead sort).mpr previousSorted,
      stateSorted⟩ rfl
  · rintro holds ⟨⟨⟨previous, target⟩, step⟩, previousSorted, _⟩ ends
    change target = state at ends
    subst ends
    obtain ⟨previousEncoded, previousRead, previousWellSorted⟩ := sorted_encode grammar previousSorted
    obtain ⟨targetEncoded, targetRead, herbrand, member, substitution, leftSide, rightSide⟩ :=
      step_forward profile previousRead step
    obtain rfl : encoded = targetEncoded := Option.some.inj (read.symm.trans targetRead)
    change property previous
    rw [← decode_encode previous previousRead]
    exact holds ⟨(previousEncoded, encoded), ⟨herbrand, member, substitution, leftSide, rightSide⟩,
      previousWellSorted, (sorted_iff grammar read sort).mp stateSorted⟩ rfl

/-- **The compiled plan has the backward box of the language** over well-sorted states. -/
theorem compiled_pastBox_iff (rootProfile : RootProfile language (.base sort)) (property : Pattern → Prop)
    (state : Pattern) :
    derivedBox (between (gsltSpan (compiled language (.base sort))) (Sorted language (.base sort))) property state ↔
      derivedBox (between (languageSpan language) (Sorted language (.base sort))) property state :=
  box_between_transfer _ (fun _ _ sourceSorted _ => compiled_steps_agree rootProfile sourceSorted) property state

variable (language) in
/-- **Check the backward box over well-sorted states**: every well-sorted predecessor of the state
is an instance of one of the types, splitting open premises by sort up to the allowance. -/
def pastBox (types : List Pattern) (sort : String) (allowance : ℕ) (state : Pattern) : PastBox :=
  match encode [] state with
  | some encoded =>
      rootPastBox (encodeRules language) (Splitting.sorted (sortingOf language) sort) (encodeGoals types) encoded
        allowance
  | none => .unknown

variable {types : List Pattern}

theorem goal_decode (goalsChecked : goalsCheck types = true) {term : Term Labels}
    (sorted : WellSorted (sortingOf language) term sort) :
    Goal types (decode term) ↔ ∃ goal ∈ encodeGoals types, Instance goal term :=
  goal_iff goalsChecked (encode_decode term (wellSorted_canonical sorted))

theorem pastBox_proved (grammar : Grammar language) (profile : Profile language)
    (goalsChecked : goalsCheck types = true) {state : Pattern} (stateSorted : Sorted language (.base sort) state)
    {allowance : ℕ} (read : pastBox language types sort allowance state = .proved) :
    derivedBox (between (languageSpan language) (Sorted language (.base sort))) (Goal types) state := by
  unfold pastBox at read
  split at read
  · rename_i encoded stateRead
    have checked := BackwardNarrowing.rootPastBox_proved (encode_ground stateRead)
      ((sorted_iff grammar stateRead sort).mp stateSorted) read
    exact (pastBox_iff grammar profile stateRead stateSorted _).mpr fun event ends =>
      (goal_decode goalsChecked event.2.2.1).mpr (checked event ends)
  · cases read

theorem pastBox_refuted (grammar : Grammar language) (profile : Profile language)
    (goalsChecked : goalsCheck types = true) {state : Pattern} (stateSorted : Sorted language (.base sort) state)
    {allowance : ℕ} (read : pastBox language types sort allowance state = .refuted) :
    ¬ derivedBox (between (languageSpan language) (Sorted language (.base sort))) (Goal types) state := by
  unfold pastBox at read
  split at read
  · rename_i encoded stateRead
    intro holds
    apply BackwardNarrowing.rootPastBox_refuted (encode_ground stateRead)
      ((sorted_iff grammar stateRead sort).mp stateSorted) read
    intro event ends
    exact (goal_decode goalsChecked event.2.2.1).mp
      ((pastBox_iff grammar profile stateRead stateSorted _).mp holds event ends)
  · cases read

end Mettapedia.OSLF.Framework.HerbrandBridge

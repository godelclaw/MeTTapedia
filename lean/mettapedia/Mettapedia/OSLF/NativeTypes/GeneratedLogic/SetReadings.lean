import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Readings
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.BagCanonicalForms

/-!
# Three readings of a set language

A rule `{x, ...rest} ⇒ ...` asks what remains of a set once `x` is matched. Under the set laws the
equation `{x} ∪ rest = S` has every solution between `S ∖ {x}` and `S`, and three readings choose among them:
- **consume** (`consumeStructure`): the smallest. The rules fire at the canonical form, where each member is
  written once, so a member a rule matches leaves the set.
- **keep** (`keepStructure`): the largest. The rules fire where every member is written more often than any
  rule matches (`saturate`, `setWidth`), so a matched member stays.
- **either** (`eitherStructure`): all of them. This is the language's own semantics, modulo its laws: a set may
  be presented with a member copied, and a rule may consume the copy.

Consume and keep are decided by closed regions of their readings (`Readings`). Either is the reference
semantics; two lemmas about least fixed points prove its verdicts here (`reaches_of_step`,
`not_eventually`).

**Separating them** (`pool`, with the rule `{A, ...rest} ⇒ {B, ...rest}`), from `{A}`:

| reading | some run reaches `{B}` | every run reaches `{B}` |
|---|---|---|
| consume | yes | yes |
| keep | no | no |
| either | yes | no |
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.GSLT.LanguageDef.EquationSemantics (DerivedInstance SortedAt CollectionCarrierRule)
open Mettapedia.GSLT.LanguageDef.WellSorted (FreeTypeContext checkHasType checkHasType_sound)

/-! ## Saturation -/

mutual
  /-- Every member of every set written `copies` times. -/
  def saturate (copies : ℕ) : Pattern → Pattern
    | .bvar index => .bvar index
    | .fvar name => .fvar name
    | .apply label arguments => .apply label (saturateList copies arguments)
    | .lambda binder body => .lambda binder (saturate copies body)
    | .multiLambda arity binders body => .multiLambda arity binders (saturate copies body)
    | .subst body replacement => .subst (saturate copies body) (saturate copies replacement)
    | .collection kind elements rest =>
        if kind = .hashSet then
          .collection kind ((saturateList copies elements).flatMap (List.replicate copies)) rest
        else
          .collection kind (saturateList copies elements) rest

  def saturateList (copies : ℕ) : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns => saturate copies pattern :: saturateList copies patterns
end

mutual
  /-- The most members a set pattern inside the pattern names. -/
  def setPatternWidth : Pattern → ℕ
    | .bvar _ | .fvar _ => 0
    | .apply _ arguments => setPatternWidthList arguments
    | .lambda _ body | .multiLambda _ _ body => setPatternWidth body
    | .subst body replacement => max (setPatternWidth body) (setPatternWidth replacement)
    | .collection kind elements _ =>
        max (if kind = .hashSet then elements.length else 0) (setPatternWidthList elements)

  def setPatternWidthList : List Pattern → ℕ
    | [] => 0
    | pattern :: patterns => max (setPatternWidth pattern) (setPatternWidthList patterns)
end

/-- The most members a set pattern on the left of a rule names. -/
def setWidth (language : LanguageDef) : ℕ :=
  (language.rewrites.map fun rule => setPatternWidth rule.left).foldl max 0

/-! ## The readings -/

variable (relEnv : RelationEnv) (language : LanguageDef)

/-- **Consume**: the rules fire at the canonical form, where each member of a set is written once; a member a
rule matches leaves the set. -/
abbrev consumeStructure : NativeStructure Pattern :=
  readingStructure relEnv language id BagForms.sortBags

/-- **Keep**: the rules fire where every member of a set is written more often than any rule matches; a matched
member stays. -/
abbrev keepStructure : NativeStructure Pattern :=
  readingStructure relEnv language (saturate (setWidth language + 1)) BagForms.sortBags

/-- **Either**: the language's own semantics, modulo its laws; a set may be presented with a member copied, and a
rule may consume the copy. -/
abbrev eitherStructure : NativeStructure Pattern := referenceStructure relEnv language

/-! ## Two lemmas about least fixed points -/

/-- Some run reaches `target`. -/
def reaches (target : Pattern) : Formula 0 := .mu (.or (.is target) (.possibly .any (.var 0)))

/-- Every run reaches `target`. -/
def eventually (target : Pattern) : Formula 0 :=
  .mu (.or (.is target) (.and (.possibly .any .top) (.necessarily .any (.var 0))))

section FixedPoints

variable {Carrier : Type} (S : NativeStructure Carrier)

/-- **A step to a state named `target` reaches it.** -/
theorem reaches_of_step {target : Pattern} {start middle : Carrier} (step : S.step start .any middle)
    (named : S.named middle target) : S.sat Env.closed (reaches target) start := by
  intro closed prefixed
  have middleIn : middle ∈ closed := prefixed middle (Or.inl named)
  exact prefixed start (Or.inr ⟨middle, step, middleIn⟩)

/-- **A run that avoids `target` forever refutes that every run reaches it**: states none of which is named
`target`, each with a step to another of them. -/
theorem not_eventually {target : Pattern} (avoid : Set Carrier) (notTarget : ∀ state ∈ avoid, ¬ S.named state target)
    (continues : ∀ state ∈ avoid, ∃ next ∈ avoid, S.step state .any next) {start : Carrier} (inside : start ∈ avoid) :
    ¬ S.sat Env.closed (eventually target) start := by
  intro holds
  refine holds avoidᶜ (fun state body member => ?_) inside
  rcases body with named | ⟨-, every⟩
  · exact notTarget state member named
  · obtain ⟨next, nextIn, step⟩ := continues state member
    exact every next step nextIn

end FixedPoints

/-! ## A set language -/

def token (label : String) : Pattern := .apply label []
def set (items : List Pattern) : Pattern := .collection .hashSet items none

def atomRule (label : String) : GrammarRule :=
  { label := label, category := "Atom", params := [], syntaxPattern := [.terminal label] }

/-- A set carrier of atoms. -/
def poolRule : GrammarRule :=
  { label := "Pool", category := "Pool", params := [.simple "members" (.collection .hashSet (.base "Atom"))],
    syntaxPattern := [.terminal "{", .op (.sep "members" "," none), .terminal "}"] }

def restOccurrences (path : List ℕ) : RuleBindingSpec :=
  { dependencies := [("rest", [])],
    occurrences := [{ name := "rest", site := .left, path := path, arguments := [] },
      { name := "rest", site := .right, path := path, arguments := [] }] }

/-- `{A, ...rest} ⇒ {B, ...rest}`. -/
def useA : RewriteRule :=
  { name := "UseA", typeContext := [("rest", .collection .hashSet (.base "Atom"))], premises := [],
    left := .collection .hashSet [token "A"] (some "rest"),
    right := .collection .hashSet [token "B"] (some "rest"), bindings := some (restOccurrences [1]) }

def pool : LanguageDef :=
  { name := "SetReadings.Pool", types := [⟨"Atom", .ast⟩, ⟨"Pool", .ast⟩],
    terms := [atomRule "A", atomRule "B", poolRule], equations := [], rewrites := [useA] }

theorem pool_no_equations : pool.equations = [] := rfl

theorem pool_no_algebra : pool.hasAlgebraDeclarations = false := by decide

def onlyA : Pattern := set [token "A"]
def onlyB : Pattern := set [token "B"]
def bothAB : Pattern := set [token "A", token "B"]

/-! ## Consume -/

abbrev Consume := consumeStructure RelationEnv.empty pool

theorem consume_reaches_answer :
    decideReading RelationEnv.empty pool 2 id BagForms.sortBags (reaches onlyB) onlyA 3 = some true := by
  decide +kernel

theorem consume_eventually_answer :
    decideReading RelationEnv.empty pool 2 id BagForms.sortBags (eventually onlyB) onlyA 3 = some true := by
  decide +kernel

theorem onlyA_canonical : BagForms.sortBags onlyA = onlyA := by decide +kernel

/-- **Consume: every run from `{A}` reaches `{B}`**, and so some run does. -/
theorem consume_verdicts : Consume.sat Env.closed (reaches onlyB) onlyA ∧ Consume.sat Env.closed (eventually onlyB) onlyA := by
  constructor
  · have decided := (decideReading_sound (by decide) consume_reaches_answer).mp rfl
    rwa [onlyA_canonical] at decided
  · have decided := (decideReading_sound (by decide) consume_eventually_answer).mp rfl
    rwa [onlyA_canonical] at decided

/-! ## Keep -/

abbrev Keep := keepStructure RelationEnv.empty pool

theorem pool_width : setWidth pool = 1 := by decide +kernel

theorem keep_reaches_answer :
    decideReading RelationEnv.empty pool 2 (saturate (setWidth pool + 1)) BagForms.sortBags (reaches onlyB) onlyA 3 =
      some false := by
  decide +kernel

theorem keep_eventually_answer :
    decideReading RelationEnv.empty pool 2 (saturate (setWidth pool + 1)) BagForms.sortBags (eventually onlyB) onlyA 3 =
      some false := by
  decide +kernel

/-- **Keep: no run from `{A}` reaches `{B}`**: the `A` is never removed. -/
theorem keep_verdicts : ¬ Keep.sat Env.closed (reaches onlyB) onlyA ∧ ¬ Keep.sat Env.closed (eventually onlyB) onlyA := by
  constructor
  · intro holds
    have decided := (decideReading_sound (by decide) keep_reaches_answer).mpr
    rw [onlyA_canonical] at decided
    exact Bool.false_ne_true (decided holds)
  · intro holds
    have decided := (decideReading_sound (by decide) keep_eventually_answer).mpr
    rw [onlyA_canonical] at decided
    exact Bool.false_ne_true (decided holds)

/-! ## Either -/

abbrev Either := eitherStructure RelationEnv.empty pool

theorem poolCarrier : CollectionCarrierRule pool poolRule .hashSet :=
  ⟨by simp [pool], "members", .base "Atom", rfl⟩

theorem sorted_of_check {pattern : Pattern}
    (checked : checkHasType pool FreeTypeContext.empty [] pattern (.base "Pool") = true) :
    SortedAt pool pattern poolRule.category :=
  ⟨_, _, checkHasType_sound checked⟩

/-- One law step between object sets, at the root. -/
theorem lawStep {source target : Pattern} (sourceObject : IsObject source) (targetObject : IsObject target)
    (law : DerivedInstance pool source target) : ObjectEquivalent RelationEnv.empty pool source target :=
  Relation.EqvGen.rel _ _ ⟨sourceObject, targetObject, .inContext .hole (Or.inr law)⟩

theorem onlyA_twice : ObjectEquivalent RelationEnv.empty pool onlyA (set [token "A", token "A"]) :=
  Relation.EqvGen.symm _ _ (lawStep (by decide) (by decide)
    (.setDedup_of_sorted (sorted_of_check (by decide +kernel))))

theorem bothAB_twice : ObjectEquivalent RelationEnv.empty pool bothAB (set [token "A", token "A", token "B"]) :=
  Relation.EqvGen.symm _ _ (lawStep (by decide) (by decide)
    (.setDedup_of_sorted (sorted_of_check (by decide +kernel))))

theorem ba_bothAB : ObjectEquivalent RelationEnv.empty pool (set [token "B", token "A"]) bothAB :=
  lawStep (by decide) (by decide) (.setPerm_of_sorted (sorted_of_check (by decide +kernel)) (List.Perm.swap _ _ _))

theorem bab_bothAB : ObjectEquivalent RelationEnv.empty pool (set [token "B", token "A", token "B"]) bothAB := by
  have toBBA : ObjectEquivalent RelationEnv.empty pool (set [token "B", token "A", token "B"])
      (set [token "B", token "B", token "A"]) :=
    lawStep (by decide) (by decide)
      (.setPerm_of_sorted (sorted_of_check (by decide +kernel)) ((List.Perm.swap _ _ _).cons _))
  have toBA : ObjectEquivalent RelationEnv.empty pool (set [token "B", token "B", token "A"]) (set [token "B", token "A"]) :=
    lawStep (by decide) (by decide) (.setDedup_of_sorted (sorted_of_check (by decide +kernel)))
  exact toBBA.trans _ _ _ (toBA.trans _ _ _ ba_bothAB)

/-- A listed step to a target is a step. -/
theorem fires_of_listed {source target : Pattern}
    (listed : ((stepsAt RelationEnv.empty pool 2 source).any fun entry => entry.2 == target) = true) :
    ∃ witness, StepValid RelationEnv.empty pool source witness target := by
  obtain ⟨⟨witness, contractum⟩, member, same⟩ := List.any_eq_true.mp listed
  obtain rfl : contractum = target := by simpa using same
  exact ⟨witness, stepValid_of_mem_stepsAt RelationEnv.empty pool member⟩

theorem fires_onlyA_twice :
    ∃ witness, StepValid RelationEnv.empty pool (set [token "A", token "A"]) witness (set [token "B", token "A"]) :=
  fires_of_listed (by decide +kernel)

theorem fires_bothAB_twice : ∃ witness, StepValid RelationEnv.empty pool (set [token "A", token "A", token "B"]) witness
    (set [token "B", token "A", token "B"]) :=
  fires_of_listed (by decide +kernel)

theorem fires_onlyA : ∃ witness, StepValid RelationEnv.empty pool onlyA witness onlyB :=
  fires_of_listed (by decide +kernel)

/-- The canonical form is invariant under the set laws, here. -/
theorem canon_same {first second : Pattern} (equivalent : ObjectEquivalent RelationEnv.empty pool first second) :
    BagForms.sortBags first = BagForms.sortBags second := by
  rw [BagForms.sortBags_eq_canon]
  exact BagForms.canon_eq_of_equivalent pool_no_equations pool_no_algebra equivalent

theorem onlyA_state : IsState onlyA := by decide
theorem onlyB_state : IsState onlyB := by decide
theorem bothAB_state : IsState bothAB := by decide
theorem aa_state : IsState (set [token "A", token "A"]) := by decide
theorem ba_state : IsState (set [token "B", token "A"]) := by decide
theorem aab_state : IsState (set [token "A", token "A", token "B"]) := by decide
theorem bab_state : IsState (set [token "B", token "A", token "B"]) := by decide

/-- **Either: some run from `{A}` reaches `{B}`, but not every run does**: a member may be copied and a copy
consumed, which leaves `{A, B}`, from which the same happens again. -/
theorem either_verdicts : Either.sat Env.closed (reaches onlyB) onlyA ∧ ¬ Either.sat Env.closed (eventually onlyB) onlyA := by
  constructor
  · obtain ⟨witness, fires⟩ := fires_onlyA
    exact reaches_of_step Either ⟨onlyA_state, onlyB_state, onlyA, onlyB, witness, Relation.EqvGen.refl _, onlyA_state,
      fires, onlyB_state, Relation.EqvGen.refl _, rfl⟩ ⟨onlyB_state.2, Relation.EqvGen.refl _⟩
  · let avoid : Set Pattern := fun state => IsState state ∧
      (ObjectEquivalent RelationEnv.empty pool state onlyA ∨ ObjectEquivalent RelationEnv.empty pool state bothAB)
    refine not_eventually Either avoid ?_ ?_ ⟨onlyA_state, Or.inl (Relation.EqvGen.refl _)⟩
    · rintro state ⟨-, sameA | sameAB⟩ ⟨-, named⟩
      · exact absurd ((canon_same sameA).symm.trans (canon_same named)) (by decide +kernel)
      · exact absurd ((canon_same sameAB).symm.trans (canon_same named)) (by decide +kernel)
    · rintro state ⟨stateIs, sameA | sameAB⟩
      · obtain ⟨witness, fires⟩ := fires_onlyA_twice
        exact ⟨bothAB, ⟨bothAB_state, Or.inr (Relation.EqvGen.refl _)⟩, stateIs, bothAB_state,
          set [token "A", token "A"], set [token "B", token "A"], witness,
          Relation.EqvGen.trans _ _ _ sameA onlyA_twice, aa_state, fires, ba_state, ba_bothAB, rfl⟩
      · obtain ⟨witness, fires⟩ := fires_bothAB_twice
        exact ⟨bothAB, ⟨bothAB_state, Or.inr (Relation.EqvGen.refl _)⟩, stateIs, bothAB_state,
          set [token "A", token "A", token "B"], set [token "B", token "A", token "B"], witness,
          Relation.EqvGen.trans _ _ _ sameAB bothAB_twice, aab_state, fires, bab_state, bab_bothAB, rfl⟩

/-! ## Keep only adds members -/

section KeepAddsMembers

open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec (MatchRel MatchBagRel matchPattern_iff_matchRel mergeBindings_subsumed_right)
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (matchPatternForRule_eq_syntactic)
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars liftBVars_zero)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (arrange arrange_mem arrange_eq_of_presents)

/-- A rule that rewrites a set at the root and puts its rest back, with no premises:
`{p…, ...rest} ⇒ {q…, ...rest}`. -/
def keepsRest (rule : RewriteRule) : Bool :=
  match rule.left, rule.right with
  | .collection .hashSet _ (some rest), .collection .hashSet _ (some rest') => rest == rest' && rule.premises.isEmpty
  | _, _ => false

/-- The members of a set. -/
def members : Pattern → List Pattern
  | .collection .hashSet elements _ => elements
  | _ => []

theorem keepsRest_shape {rule : RewriteRule} (keeps : keepsRest rule = true) :
    ∃ patterns results rest, rule.left = .collection .hashSet patterns (some rest) ∧
      rule.right = .collection .hashSet results (some rest) ∧ rule.premises = [] := by
  unfold keepsRest at keeps
  split at keeps
  · rename_i patterns rest results rest' leftIs rightIs
    simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at keeps
    obtain ⟨rfl, none⟩ := keeps
    exact ⟨patterns, results, rest, leftIs, rightIs, none⟩
  · cases keeps

theorem le_foldl_max : ∀ (values : List ℕ) (init : ℕ),
    init ≤ values.foldl max init ∧ ∀ value ∈ values, value ≤ values.foldl max init
  | [], init => ⟨le_refl _, fun _ member => nomatch member⟩
  | head :: tail, init => by
    obtain ⟨initLe, each⟩ := le_foldl_max tail (max init head)
    refine ⟨le_trans (le_max_left _ _) initLe, fun value member => ?_⟩
    rcases List.mem_cons.mp member with rfl | inTail
    · exact le_trans (le_max_right _ _) initLe
    · exact each value inTail

theorem width_le {language : LanguageDef} {rule : RewriteRule} (member : rule ∈ language.rewrites) :
    setPatternWidth rule.left ≤ setWidth language :=
  (le_foldl_max _ 0).2 _ (List.mem_map_of_mem member)

theorem count_le_eraseIdx : ∀ (list : List Pattern) (index : ℕ) (value : Pattern),
    list.count value ≤ (list.eraseIdx index).count value + 1
  | [], _, _ => by simp
  | head :: tail, 0, value => by
    simp only [List.eraseIdx_cons_zero, List.count_cons]
    split <;> omega
  | head :: tail, index + 1, value => by
    simp only [List.eraseIdx_cons_succ, List.count_cons]
    have := count_le_eraseIdx tail index value
    split <;> omega

/-- **What a set pattern leaves in its rest**: every value, except at most one copy per pattern member. -/
theorem matchBag_rest : ∀ {patterns : List Pattern} {rest : String} {kind : CollType} {values : List Pattern}
    {bindings : Bindings}, MatchBagRel patterns (some rest) kind values bindings →
    ∃ residual, bindings.find? (·.1 == rest) = some (rest, .collection kind residual none) ∧
      ∀ value, values.count value ≤ residual.count value + patterns.length
  | [], rest, kind, values, bindings, matched => by
    cases matched
    exact ⟨values, by simp, fun value => by simp⟩
  | _ :: _, _, _, values, _, matched => by
    cases matched with
    | cons index _ _ tail merged =>
      obtain ⟨residual, found, counted⟩ := matchBag_rest tail
      refine ⟨residual, mergeBindings_subsumed_right merged found, fun value => ?_⟩
      have erased := count_le_eraseIdx values index value
      have later := counted value
      simp only [List.length_cons]
      omega

theorem count_flatMap_replicate (copies : ℕ) {value : Pattern} : ∀ {list : List Pattern}, value ∈ list →
    copies ≤ (list.flatMap (List.replicate copies)).count value
  | _ :: _, member => by
    rw [List.flatMap_cons, List.count_append]
    rcases List.mem_cons.mp member with rfl | inTail
    · rw [List.count_replicate_self]
      omega
    · have := count_flatMap_replicate copies inTail
      omega

theorem saturateList_eq_map (copies : ℕ) : ∀ patterns : List Pattern,
    saturateList copies patterns = patterns.map (saturate copies)
  | [] => rfl
  | pattern :: patterns => by simp [saturateList, saturateList_eq_map copies patterns]

/-- **Canonical forms undo saturation.** -/
theorem sortBags_saturate {copies : ℕ} (positive : 0 < copies) (pattern : Pattern) :
    BagForms.sortBags (saturate copies pattern) = BagForms.sortBags pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [saturate, BagForms.sortBags]
  | hfvar name => simp [saturate, BagForms.sortBags]
  | happly label arguments recurse =>
    simp only [saturate, BagForms.sortBags, saturateList_eq_map, BagForms.sortBagsList_eq_map, List.map_map]
    congr 1
    exact List.map_congr_left recurse
  | hlambda binder body recurse => simp [saturate, BagForms.sortBags, recurse]
  | hmultiLambda arity binders body recurse => simp [saturate, BagForms.sortBags, recurse]
  | hsubst body replacement bodyRecurse replacementRecurse =>
    simp [saturate, BagForms.sortBags, bodyRecurse, replacementRecurse]
  | hcollection kind elements rest recurse =>
    by_cases isSet : kind = .hashSet
    · subst isSet
      simp only [saturate, if_true, BagForms.sortBags, saturateList_eq_map, BagForms.sortBagsList_eq_map]
      congr 1
      apply arrange_eq_of_presents
      intro value
      simp only [List.mem_map, List.mem_flatMap, List.mem_replicate]
      constructor
      · rintro ⟨copy, ⟨saturated, ⟨element, member, rfl⟩, -, rfl⟩, rfl⟩
        exact ⟨element, member, (recurse element member).symm⟩
      · rintro ⟨element, member, rfl⟩
        exact ⟨saturate copies element, ⟨saturate copies element, ⟨element, member, rfl⟩, positive.ne', rfl⟩,
          recurse element member⟩
    · simp only [saturate, isSet, if_false, BagForms.sortBags, saturateList_eq_map, BagForms.sortBagsList_eq_map,
        List.map_map]
      congr 2
      exact List.map_congr_left recurse

theorem restSplice_keeps {lhs : Pattern} {bindings : Bindings} {rest : String} {residual : List Pattern}
    (found : bindings.find? (·.1 == rest) = some (rest, .collection .hashSet residual none)) :
    restSplice lhs bindings 0 .hashSet (some rest) = (residual, none) := by
  have identity : liftBVars 0 0 = id := funext fun pattern => liftBVars_zero pattern 0
  simp only [restSplice, found, beq_self_eq_true, if_true]
  split
  · simp only [Nat.zero_sub, identity, List.map_id]
  · rfl

variable {relEnv : RelationEnv} {language : LanguageDef}

/-- **Keep only adds members**: in a language whose rules rewrite a set at the root and put its rest back, a
step of the keep reading from a set leads to a set with every member of the source, in canonical form. -/
theorem keep_keeps_members (rules : language.rewrites.all keepsRest = true) {elements : List Pattern}
    {label : StepLabel} {target : Pattern}
    (step : (keepStructure relEnv language).step (.collection .hashSet elements none) label target) :
    (∃ results, target = .collection .hashSet results none) ∧
      ∀ element ∈ elements, BagForms.sortBags element ∈ members target := by
  obtain ⟨-, -, witness, contractum, valid, -, reached⟩ := step
  subst reached
  cases valid with
  | @rule _ index rule initial final witnesses found matched premises =>
    obtain ⟨patterns, results, rest, leftIs, rightIs, noPremises⟩ :=
      keepsRest_shape (List.all_eq_true.mp rules rule (List.mem_of_getElem? found))
    rw [noPremises] at premises
    cases premises
    rw [matchPatternForRule_eq_syntactic, leftIs] at matched
    have related := matchPattern_iff_matchRel.mp matched
    simp only [saturate, if_true, saturateList_eq_map] at related
    cases related with
    | collection _ bag =>
      obtain ⟨residual, bound, counted⟩ := matchBag_rest bag
      have wide : patterns.length < setWidth language + 1 := by
        have := width_le (List.mem_of_getElem? found)
        rw [leftIs] at this
        simp only [setPatternWidth, if_true] at this
        omega
      rw [rightIs]
      simp only [applyBindingsScoped, restSplice_keeps bound, BagForms.sortBags]
      refine ⟨⟨_, rfl⟩, fun element member => ?_⟩
      have many := count_flatMap_replicate (setWidth language + 1)
        (List.mem_map_of_mem (f := saturate (setWidth language + 1)) member)
      have kept : saturate (setWidth language + 1) element ∈ residual := by
        have := counted (saturate (setWidth language + 1) element)
        exact List.count_pos_iff.mp (by omega)
      show BagForms.sortBags element ∈ arrange .hashSet (BagForms.sortBagsList _)
      rw [arrange_mem, BagForms.sortBagsList_eq_map, ← sortBags_saturate (Nat.succ_pos _) element]
      exact List.mem_map_of_mem (List.mem_append_right _ kept)

/-- **Along every run of the keep reading, a canonical set keeps its members.** -/
theorem keep_runs_keep_members (rules : language.rewrites.all keepsRest = true) {start target : Pattern}
    (run : Relation.ReflTransGen (fun source next => ∃ label, (keepStructure relEnv language).step source label next)
      start target)
    {elements : List Pattern} (isSet : start = .collection .hashSet elements none)
    (canonical : ∀ element ∈ elements, BagForms.sortBags element = element) :
    ∀ element ∈ elements, element ∈ members target := by
  have invariant : (∃ results, target = .collection .hashSet results none) ∧ ∀ element ∈ elements, element ∈ members target := by
    induction run with
    | refl => exact ⟨⟨elements, isSet⟩, fun element member => by rw [isSet]; exact member⟩
    | tail _ step previous =>
      obtain ⟨label, step⟩ := step
      obtain ⟨⟨results, rfl⟩, inside⟩ := previous
      obtain ⟨shape, kept⟩ := keep_keeps_members rules step
      refine ⟨shape, fun element member => ?_⟩
      have := kept element (inside element member)
      rwa [canonical element member] at this
  exact invariant.2

theorem pool_keepsRest : pool.rewrites.all keepsRest = true := by decide

/-- **Under keep, no run from `{A}` ever loses the `A`**, by the general theorem rather than by a region. -/
theorem keep_never_drops_A {target : Pattern}
    (run : Relation.ReflTransGen (fun source next => ∃ label, Keep.step source label next) onlyA target) :
    token "A" ∈ members target := by
  refine keep_runs_keep_members pool_keepsRest run rfl (fun element member => ?_) _ (by simp)
  rw [List.mem_singleton.mp member]
  decide +kernel

end KeepAddsMembers

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

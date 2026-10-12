import Mettapedia.OSLF.NativeTypes.Generation.Checking
import Mettapedia.OSLF.Framework.SortedInstrumentCongruenceLogic
import Mathlib.Tactic.FinCases

open Mettapedia.OSLF.Framework

/-!
# Generated structural observation and its instrument index

Two authored inert constructors have identical reduction behavior, but the
generated constructor questions distinguish them. The declaration-derived
instrument system observes those questions as actual labelled interactions.
Its finite structural fragment is adequate without negation. This refutes a
universal necessity claim, not a general expressiveness/checkability tradeoff.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Structural.ObservationControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Generation
open Mettapedia.OSLF.NativeTypes.Structural
open GeneralOccurrenceFrontier

def language : LanguageDef where
  name := "InertObservations"
  types := [TypeDecl.plain "Value"]
  terms := [
    {label := "First", category := "Value", params := [], syntaxPattern := []},
    {label := "Second", category := "Value", params := [], syntaxPattern := []}]
  equations := []
  rewrites := []

def carrier : TypeExpr := .base "Value"
def first : Pattern := .apply "First" []
def second : Pattern := .apply "Second" []
def snapshot : GeneralExecutionAdmission.Snapshot := ⟨language, [], ⟨[], []⟩⟩
def languageFragment : LanguageFragment :=
  {operational := {includeDerivedEquations := false}}
def logicFragment : ConnectiveFragment :=
  {core := {top := true, conj := true, structural := true, modal := false, possibility := false}}
def chosen := selectedSnapshot snapshot languageFragment
def vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.CubeVertex chosen.language :=
  (fun _ => .star, fun _ => .star)
def generated := generate snapshot languageFragment logicFragment vertex

private def runtimePlan : GeneralExecutionAdmission.Plan :=
  ⟨snapshot, languageFragment.operational, [], [], []⟩

private theorem generated_plan : generated.plan = runtimePlan := by
  cbv

theorem generated_fragment_has_no_negation : generated.logicFragment.admits .negation = false := rfl

/-- The claim ranges over every source, target, carrier and binding context.
No authored reduction can be hidden by a limited probe budget. -/
theorem whole_language_has_no_authored_steps (bound : List TypeExpr) (expected : TypeExpr)
    (source target : Pattern) :
    ¬ (GeneralOccurrenceSemantics.gslt generated.plan bound expected).Step source target := by
  rw [generated_plan]
  rintro ⟨representative, receipt, _, valid, _⟩
  have declared := valid.1.1
  change _ ∈ ([] : List (GeneralExecutionAdmission.RulePlan × Nat)) at declared
  cases declared

theorem whole_language_bare_bisimilar (bound : List TypeExpr) (expected : TypeExpr)
    (source target : Pattern) :
    (GeneralOccurrenceSemantics.gslt generated.plan bound expected).Bisimilar source target := by
  refine ⟨fun _ _ => True, ⟨?_, ?_⟩, trivial⟩
  · intro left right related next step
    exact False.elim (whole_language_has_no_authored_steps bound expected left next step)
  · intro left right related next step
    exact False.elim (whole_language_has_no_authored_steps bound expected right next step)

theorem generated_equations_are_equality (bound : List TypeExpr) (expected : TypeExpr)
    (source target : Pattern) :
    Relation.EqvGen (GeneralOccurrenceSemantics.Equation generated.plan bound expected)
      source target ↔ source = target := by
  constructor
  · intro equivalent
    induction equivalent with
    | rel left right equation =>
        obtain ⟨receipt, completed, _⟩ := equation
        have declared := completed.job.1
        rw [generated_plan] at declared
        change _ ∈ ([] : List (GeneralExecutionAdmission.EquationPlan × Nat)) at declared
        cases declared
    | refl term => rfl
    | symm left right _ same => exact same.symm
    | trans left middle right _ _ before after => exact before.trans after
  · intro same
    subst target
    exact .refl _

private theorem first_typed : HasType language snapshot.free [] first carrier := by
  apply checkHasType_sound
  cbv

private theorem second_typed : HasType language snapshot.free [] second carrier := by
  apply checkHasType_sound
  cbv

private theorem first_formed :
    Formed generated.snapshot.language generated.atomSort generated.logicFragment carrier (.root 0) := by
  apply (generated_formation_iff generated carrier (.root 0)).mp
  cbv

private theorem nullary_root_exact (index : Nat) (declaration : GrammarRule)
    (found : language.terms[index]? = some declaration) (noArguments : declaration.params = [])
    (term : Pattern) :
    Holds language snapshot.free [] (fun _ => Eq) (fun _ _ _ => False)
      (.base declaration.category) (.root index) term ↔
      term = .apply declaration.label [] := by
  rw [holds_root_exact found]
  constructor
  · rintro ⟨member, value, equal⟩
    cases value with
    | ordinary arguments ordinary typed =>
        have arity := typed.length_eq
        rw [noArguments] at arity
        have empty : arguments = [] := by simpa using arity
        simpa only [ConstructorValue.pattern, empty] using equal
    | collection name kind sort elements rest shape typed =>
        rw [noArguments] at shape
        cases shape
  · intro same
    subst term
    refine ⟨?_, .ordinary [] ?_ ?_, rfl⟩
    · exact (mem_structuralFormers_iff language ⟨index, declaration⟩).mpr found
    · rintro ⟨name, kind, sort, shape⟩
      rw [noArguments] at shape
      cases shape
    · rw [noArguments]
      exact .nil

theorem generated_structural_separation :
    Holds generated.snapshot.language generated.snapshot.free []
      (fun expected => Relation.EqvGen (GeneralOccurrenceSemantics.Equation generated.plan [] expected))
      (fun _ _ _ => False) carrier (.root 0) first ∧
    ¬ Holds generated.snapshot.language generated.snapshot.free []
      (fun expected => Relation.EqvGen (GeneralOccurrenceSemantics.Equation generated.plan [] expected))
      (fun _ _ _ => False) carrier (.root 0) second := by
  have equationFamily :
      (fun expected => Relation.EqvGen (GeneralOccurrenceSemantics.Equation generated.plan [] expected)) =
        (fun (_ : TypeExpr) => (Eq : Pattern → Pattern → Prop)) := by
    funext expected left right
    exact propext (generated_equations_are_equality [] expected left right)
  rw [equationFamily]
  change Holds language snapshot.free [] (fun _ => Eq) (fun _ _ _ => False) carrier (.root 0) first ∧
    ¬ Holds language snapshot.free [] (fun _ => Eq) (fun _ _ _ => False) carrier (.root 0) second
  have exactQuestion := nullary_root_exact 0 (language.terms[0]'(by decide)) rfl rfl
  exact ⟨(exactQuestion first).mpr rfl,
    fun holds => (by decide +kernel : second ≠ first) ((exactQuestion second).mp holds)⟩

theorem generated_first_question_executes :
    (generated.checkFormula [] carrier first (.root 0) 12).result = .decided true := by
  cbv

theorem generated_second_question_refutes_first_shape :
    (generated.checkFormula [] carrier second (.root 0) 12).result = .decided false := by
  cbv

namespace Instrument

open Mettapedia.OSLF.SortedConstructors
open SortedInstrumentCongruence

/-- Constructor indices and arities are read from the authored declaration
list. This particular language has one carrier and nullary declarations. -/
def signature : Signature where
  Srt := Unit
  Constructor := Fin language.terms.length
  arity constructor := language.terms[constructor].params.length
  input _ _ := ()
  output _ := ()

def declaration (constructor : signature.Constructor) : GrammarRule :=
  language.terms[constructor.val]'constructor.isLt

private theorem arity_zero (constructor : signature.Constructor) : signature.arity constructor = 0 := by
  change Fin 2 at constructor
  fin_cases constructor <;> rfl

private theorem category_value (constructor : signature.Constructor) :
    (declaration constructor).category = "Value" := by
  change Fin 2 at constructor
  fin_cases constructor <;> rfl

private theorem parameters_empty (constructor : signature.Constructor) :
    (declaration constructor).params = [] := by
  change Fin 2 at constructor
  fin_cases constructor <;> rfl

def head {sort : signature.Srt} : Term signature sort → signature.Constructor
  | .node constructor _ => constructor

/-- Every closed sorted term is the actual nullary native constructor. -/
def native {sort : signature.Srt} (term : Term signature sort) : Pattern :=
  .apply (declaration (head term)).label []

theorem native_typed {sort : signature.Srt} (term : Term signature sort) :
    HasType language snapshot.free [] (native term) carrier := by
  cases term with
  | node constructor arguments =>
      change Fin 2 at constructor
      fin_cases constructor
      · exact first_typed
      · exact second_typed

private theorem native_first_or_second {sort : signature.Srt} (term : Term signature sort) :
    native term = first ∨ native term = second := by
  cases term with
  | node constructor arguments =>
      change Fin 2 at constructor
      fin_cases constructor
      · exact Or.inl rfl
      · exact Or.inr rfl

private theorem label_injective (left right : signature.Constructor)
    (same : (declaration left).label = (declaration right).label) : left = right := by
  change Fin 2 at left right
  fin_cases left <;> fin_cases right <;> simp_all [declaration, language] <;> rfl

theorem native_injective {sort : signature.Srt} {left right : Term signature sort}
    (same : native left = native right) : left = right := by
  cases left with
  | node first arguments =>
      cases right with
      | node second other =>
          have heads : first = second := label_injective first second
            (Pattern.apply.inj same).1
          subst second
          congr 1
          funext position
          have impossible := position.isLt
          have empty := arity_zero first
          omega

def readout {sort : signature.Srt} (term : Term signature sort)
    (formula : Mettapedia.OSLF.NativeTypes.Structural.Formula) : Option Bool :=
  let request := generated.request [] carrier (native term)
  Mettapedia.OSLF.NativeTypes.Structural.readGeneratedFormula request
    (generated.execute [] carrier (native term) 12) 12 formula

private theorem lookup_parameters_empty (index : Nat) (rule : GrammarRule)
    (found : language.terms[index]? = some rule) : rule.params = [] := by
  cases index with
  | zero => cases found; rfl
  | succ next =>
      cases next with
      | zero => cases found; rfl
      | succ next => simp [language] at found

private theorem root_readout_conclusive {sort : signature.Srt} (term : Term signature sort)
    (index : Nat) (rule : GrammarRule) (found : language.terms[index]? = some rule) :
    ∃ answer, readout term (.root index) = some answer := by
  cases index with
  | zero =>
      cases found
      unfold readout
      rcases native_first_or_second term with isFirst | isSecond
      · rw [isFirst]; exact ⟨true, by cbv⟩
      · rw [isSecond]; exact ⟨false, by cbv⟩
  | succ next =>
      cases next with
      | zero =>
          cases found
          unfold readout
          rcases native_first_or_second term with isFirst | isSecond
          · rw [isFirst]; exact ⟨false, by cbv⟩
          · rw [isSecond]; exact ⟨true, by cbv⟩
      | succ next => simp [language] at found

/-- The finite fragment is actually checked for every formed question and
every closed term. Root checks execute the same certified engine; conjunction
recurses on those delivered answers. -/
theorem formed_readout_conclusive {expected : TypeExpr}
    {formula : Mettapedia.OSLF.NativeTypes.Structural.Formula}
    (formed : Mettapedia.OSLF.NativeTypes.Structural.Formed generated.snapshot.language generated.atomSort
      generated.logicFragment expected formula) {sort : signature.Srt} (term : Term signature sort) :
    ∃ answer, readout term formula = some answer := by
  change Mettapedia.OSLF.NativeTypes.Structural.Formed language generated.atomSort logicFragment expected formula at formed
  induction formed with
  | top => exact ⟨true, rfl⟩
  | bottom expected enabled => cases enabled
  | atom index enabled sort => cases enabled
  | conj enabled first second ihFirst ihSecond =>
      obtain ⟨left, before⟩ := ihFirst
      obtain ⟨right, after⟩ := ihSecond
      refine ⟨left && right, ?_⟩
      change readBinary Bool.and (readout term _) (readout term _) = some (left && right)
      rw [before, after]
      rfl
  | disj enabled first second => cases enabled
  | imp enabled first second => cases enabled
  | neg enabled inner => cases enabled
  | root index rule enabled found expected => exact root_readout_conclusive term index rule found
  | split index rule firstParam secondParam enabled found expected arity firstType secondType first second =>
      rw [lookup_parameters_empty index rule found] at arity
      cases arity
  | spatial index rule shape enabled found expected spatial first second =>
      simp only [spatialShape?, lookup_parameters_empty index rule found] at spatial
      cases spatial

theorem generated_check_conclusive {sort : signature.Srt} (term : Term signature sort)
    (formula : Mettapedia.OSLF.NativeTypes.Structural.Formula)
    (formed : Mettapedia.OSLF.NativeTypes.Structural.Formed generated.snapshot.language generated.atomSort
      generated.logicFragment carrier formula) :
    ∃ answer, (generated.checkFormula [] carrier (native term) formula 12).result = .decided answer := by
  obtain ⟨answer, observed⟩ := formed_readout_conclusive formed term
  have admitted : generated.equationAdmission = some true := by cbv
  have sourceAdmitted : sourceAdmission (generated.request [] carrier (native term)) = true := by
    rcases native_first_or_second term with isFirst | isSecond
    · rw [isFirst]; cbv
    · rw [isSecond]; cbv
  have formedCheck := (generated_formation_iff generated carrier formula).mpr formed
  cases elaborated : generated.elaborate carrier formula with
  | error reason => rw [elaborated] at formedCheck; cases formedCheck
  | ok judgment =>
      refine ⟨answer, ?_⟩
      simp only [Generated.checkFormula, elaborated, admitted, formulaReadout, sourceAdmitted, if_true]
      exact congrArg (fun result => match result with
        | some value => CheckResult.decided value
        | none => CheckResult.unknown) observed

def equations : Congruence signature := Congruence.equality signature

/-- Authored labels read the original generated reduction semantics; the
whole-language no-step theorem discharges its equation-respect laws. -/
def base : BaseSystem equations where
  Atom := Empty
  observes observation := observation.elim
  observes_resp observation := observation.elim
  Label := Unit
  act _ {_} {_} left right :=
    (GeneralOccurrenceSemantics.gslt generated.plan [] carrier).Step (native left) (native right)
  act_resp_left _ authored :=
    False.elim (whole_language_has_no_authored_steps [] carrier _ _ authored)
  act_resp_right authored _ :=
    False.elim (whole_language_has_no_authored_steps [] carrier _ _ authored)

def opened (_ : signature.Constructor) : Prop := True

def generatedMeaning (formula : Mettapedia.OSLF.NativeTypes.Structural.Formula)
    {sort : signature.Srt} (term : Term signature sort) : Prop :=
  Mettapedia.OSLF.NativeTypes.Structural.Holds generated.snapshot.language generated.snapshot.free []
    (fun expected => Relation.EqvGen (GeneralOccurrenceSemantics.Equation generated.plan [] expected))
    (fun _ _ _ => False) carrier formula (native term)

def GeneratedEquivalent {sort : signature.Srt} (left right : Term signature sort) : Prop :=
  ∀ formula, Mettapedia.OSLF.NativeTypes.Structural.Formed generated.snapshot.language generated.atomSort
    generated.logicFragment carrier formula →
      (generatedMeaning formula left ↔ generatedMeaning formula right)

private theorem root_formed (constructor : signature.Constructor) :
    Mettapedia.OSLF.NativeTypes.Structural.Formed generated.snapshot.language generated.atomSort
      generated.logicFragment carrier (.root constructor.val) := by
  apply Mettapedia.OSLF.NativeTypes.Structural.Formed.root constructor.val (declaration constructor)
  · rfl
  · exact List.getElem?_eq_getElem constructor.isLt
  · exact congrArg TypeExpr.base (category_value constructor).symm

private theorem generated_root_exact (constructor : signature.Constructor)
    {sort : signature.Srt} (term : Term signature sort) :
    generatedMeaning (.root constructor.val) term ↔
      native term = .apply (declaration constructor).label [] := by
  unfold generatedMeaning
  have equationFamily :
      (fun expected => Relation.EqvGen (GeneralOccurrenceSemantics.Equation generated.plan [] expected)) =
        (fun (_ : TypeExpr) => (Eq : Pattern → Pattern → Prop)) := by
    funext expected left right
    exact propext (generated_equations_are_equality [] expected left right)
  rw [equationFamily]
  change Mettapedia.OSLF.NativeTypes.Structural.Holds language snapshot.free [] (fun _ => Eq)
    (fun _ _ _ => False) carrier (.root constructor.val) (native term) ↔ _
  have result := nullary_root_exact constructor.val (declaration constructor)
    (List.getElem?_eq_getElem constructor.isLt) (parameters_empty constructor) (native term)
  simpa only [category_value, carrier] using result

/-- For every closed term of the generated finite language, its generated
root question characterizes it. Negation and modal flags are unnecessary
for this particular observation index. -/
theorem generated_equivalence_exact {sort : signature.Srt} (left right : Term signature sort) :
    GeneratedEquivalent left right ↔ left = right := by
  constructor
  · intro sameQuestions
    have own := (generated_root_exact (head left) left).mpr rfl
    have transferred := (sameQuestions (.root (head left).val) (root_formed (head left))).mp own
    have same := (generated_root_exact (head left) right).mp transferred
    exact native_injective same.symm
  · intro same
    subst right
    intro formula formed
    exact Iff.rfl

/-- The reused instrument theorem identifies the correct relation: authored
steps extended by constructor ask/get/build observations. -/
theorem instrument_full_logic_adequate {sort : signature.Srt}
    (left right : Term signature sort) :
    LogicallyEquivalent base opened left right ↔ Bisimilar base opened (.term left) (.term right) :=
  logicallyEquivalent_iff_bisimilar base opened left right

theorem negation_free_generated_adequacy {sort : signature.Srt}
    (left right : Term signature sort) :
    GeneratedEquivalent left right ↔ Bisimilar base opened (.term left) (.term right) := by
  rw [generated_equivalence_exact]
  exact (bisimilar_iff_rel (base := base) (fun _ => trivial) left right).symm

def closed (constructor : signature.Constructor) : Term signature () :=
  .node constructor fun position => by
    have below := position.isLt
    have empty := arity_zero constructor
    omega

def firstConstructor : signature.Constructor := ⟨0, by decide⟩
def secondConstructor : signature.Constructor := ⟨1, by decide⟩

/-- Opening the first constructor is a real step of the instrument extension,
even though neither value has an authored reduction. -/
theorem actual_instrument_ask :
    Act base opened (.ask firstConstructor) (.term (closed firstConstructor))
      (.bundle firstConstructor (fun position => by
        have below := position.isLt
        have empty := arity_zero firstConstructor
        omega)) :=
  .ask firstConstructor trivial (equations.refl _)

theorem second_cannot_answer_first_instrument :
    ¬ ∃ next, Act base opened (.ask firstConstructor) (.term (closed secondConstructor)) next := by
  rintro ⟨next, asks⟩
  obtain ⟨_, value, arguments, same, _, equation⟩ := Act.ask_inv asks
  have source : closed secondConstructor = value := State.term_injective same
  have values := congrArg native (source.trans equation)
  change second = first at values
  exact (by decide +kernel : second ≠ first) values

theorem observer_index_strictly_changes_equivalence :
    (GeneralOccurrenceSemantics.gslt generated.plan [] carrier).Bisimilar first second ∧
      ¬ Bisimilar base opened (.term (closed firstConstructor)) (.term (closed secondConstructor)) := by
  refine ⟨whole_language_bare_bisimilar [] carrier first second, ?_⟩
  intro related
  have same := (bisimilar_iff_rel (base := base) (fun _ => trivial) _ _).mp related
  have values := congrArg native same
  change first = second at values
  exact (by decide +kernel : first ≠ second) values

/-- The adequate fragment is genuinely discriminating on two different
values. Its lack of negation does not make the adequacy theorem vacuous. -/
theorem universal_negation_necessity_refuted :
    generated.logicFragment.admits .negation = false ∧
    (∀ left right : Term signature (), GeneratedEquivalent left right ↔
      Bisimilar base opened (.term left) (.term right)) ∧
    ¬ GeneratedEquivalent (closed firstConstructor) (closed secondConstructor) := by
  refine ⟨generated_fragment_has_no_negation, negation_free_generated_adequacy, ?_⟩
  intro equivalent
  exact observer_index_strictly_changes_equivalence.2
    ((negation_free_generated_adequacy _ _).mp equivalent)

end Instrument

end Mettapedia.OSLF.NativeTypes.Structural.ObservationControls

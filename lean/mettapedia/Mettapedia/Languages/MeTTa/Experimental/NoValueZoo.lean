import Mettapedia.Languages.MeTTa.MeTTaZero
import Mettapedia.TypeTheory.Authority
import Mettapedia.GSLT.LanguageDef.CertificateGSLTConstructibleDuality
import Mettapedia.Logic.TheoryModel.OpenDeclarations

/-!
# The no-value zoo

"No value" is not one thing.  Thirteen kinds of it occur in a MeTTa language with typed
judgments and declared types, each in its own carrier and with its own laws:

* **zero answers**: the empty answer bag of a query or evaluation; the unit of answer
  union and absorbing for continuation (`zeroAnswers_add`, `zeroAnswers_bind`);
* **the unit datum** `()`: one answer, the empty tuple, which is also what reifying zero
  answers produces (`reify_nil`);
* **an empty collection**: one answer, a list with nothing in it;
* **an error value**: an answer `(Error subject message)`; it is one answer, and a
  continuation receives it like any other (`singleton_bind`);
* **an inert call**: an evaluation that retained its subject because nothing interprets
  it (`evaluate_headOfNil`);
* **`None`**: the absent case of an option value, an ordinary answer;
* **the datum `Empty`**: an ordinary symbol returned as an answer;
* **neither**: the evidence status in which no lane accepted; the bottom of the
  knowledge order, refined by any arriving evidence (`neither_knowledge_bottom`);
* **undetermined**: a judgment outside the authority's fragment; no budget changes it
  (`Outcome.budget_does_not_resolve_outside`), a stronger authority can;
* **incomplete**: a judgment stopped at a resource frontier; more budget can decide it,
  a change of authority cannot (`Outcome.authority_does_not_resolve_incomplete`);
* **refuted**: a checked negative verdict, which no refinement turns into established
  evidence;
* **a closed type with no constructors**: its declaration entails that it is empty;
* **an open declared type with no constructors**: its inhabitation is undetermined
  (`Logic.TheoryModel.OpenDeclarations`).

**Non-collapse.**  Each kind has a witness on its own carrier, the answer bags being
produced by MeTTa Zero evaluation and query (`Kind.witness`), and an observation of
that carrier that holds of its witness and of no other (`Kind.observation_witness_iff`).
Hence every two kinds are told apart by an observation (`Kind.separated`), and the
witnesses are pairwise distinct (`Kind.witness_injective`).  Five of the answer kinds
(zero answers, the unit datum, an empty collection, the datum `Empty` and an error
value) are the kinds of `Languages.FiniteChoice.Emptiness`, separated there by contexts
of a small expression language; the inert call and `None` are added here, and the
judgment, evidence and declaration kinds live on other carriers.

**Collapses and their quirks.**  A view that identifies two kinds forces one behaviour
on both:

* HE's sentinel reading deletes the datum `Empty` from answers, identifying it with zero
  answers (`heView_collapses`); an identity function then cannot return `Empty`
  (`heView_identity_quirk`), the instance on MeTTa Zero evaluation of
  `Languages.FiniteChoice.Emptiness.positional_breaks_definitional_replacement`;
* an evaluator without inert retention identifies an uninterpreted call with zero
  answers (`withoutRetention_collapses`): a misspelt call vanishes;
* MeTTa Zero's grounding boundary reads an empty grounded result as declining, so
  evaluation never yields zero answers (`evaluateOne_ne_zero`) and an operation that
  answers nothing is retained inert (`groundedNothing_retained`); a two-channel boundary
  separates declining from answering nothing and changes nothing else
  (`evaluateTwoChannel_eq_of_declines`, `evaluateTwoChannel_eq_of_answers`,
  `evaluateTwoChannel_answers_zero`);
* a null test on lookups identifies an absent key with a key bound to `None`
  (`nullTest_collapses`);
* reading verdicts as Booleans with `false` for no verdict, as a SQL `WHERE`, an IEEE
  comparison or truthiness do, identifies refuted, undetermined and incomplete
  (`toBool_collapses`); a claim with no verdict then passes neither the filter nor its
  negation (`toBool_excluded_middle_iff`), and `NOT IN` over a column with an unknown
  entry filters out a row whose present values all differ (`sqlNotIn_unknown`);
* a universe in which every type has a designated inhabitant hosts no model of the
  closed empty type and adds inhabitation to an open one
  (`OpenDeclarations.modelsIn_pointedUniverse_closedDecl_empty`,
  `OpenDeclarations.not_hostsFaithfully_pointedUniverse_openDecl_empty`);
* HE normalizes the completed alternatives of every evaluation, dropping `Empty` when
  anything else arrived and error values when anything succeeded (`heNormalize`).  An
  error beside a success is erased, so the normal form cannot report it
  (`heNormalize_collapses`), and adding a succeeding equation for a head erases the
  error its other equation produced (`sibling_equation_erases_error`).  The rule is not
  monotone in the alternatives (`heNormalize_not_monotone`), so no producer that emits as
  alternatives arrive computes it (`no_streaming_heNormalize`): every level buffers its
  completed set.  A retention policy keeps every value and error occurrence; success-only is an
  explicit observation (`withoutErrors`), monotone (`withoutErrors_monotone`), and equal
  to HE's normal form where something succeeded and no `Empty` arrived
  (`heNormalize_eq_withoutErrors`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Experimental.NoValueZoo

open Mettapedia.Languages.MeTTa.MeTTaZero
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.TypeTheory.AuthorityTheory
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.Logic.TheoryModel

/-! ## Atoms and the reference evaluator -/

/-- A symbol. -/
def sym (name : String) : Pattern := .apply name []

/-- The datum `Empty`. -/
def emptyAtom : Pattern := sym "Empty"

/-- The absent option value `None`. -/
def noneAtom : Pattern := sym "None"

/-- The empty list. -/
def nilAtom : Pattern := sym "Nil"

/-- Reify a list of answers as one tuple. -/
def reify (answers : List Pattern) : Pattern :=
  .collection .vec answers none

/-- The unit datum `()`, the empty tuple. -/
def unitAtom : Pattern := reify []

/-- Reifying zero answers gives the unit datum. -/
theorem reify_nil : reify [] = unitAtom :=
  rfl

/-- An error value: the failing subject and a message. -/
def errorAtom (subject : Pattern) (message : String) : Pattern :=
  .apply "Error" [subject, sym message]

/-- An application of `Error`. -/
def IsErrorAtom (answer : Pattern) : Prop :=
  ∃ arguments, answer = .apply "Error" arguments

/-- A stored equation. -/
def equation (left right : Pattern) : Pattern :=
  .apply "=" [left, right]

/-- The reference evaluator: the structural model with no grounded operation. -/
abbrev reference : Model :=
  structuralModel fun _ => 0

/-- `(head-of Nil)`, interpreted by no equation. -/
def headOfNil : Pattern := .apply "head-of" [nilAtom]

/-- `(head-or-none Nil)`, interpreted as `None`. -/
def headOrNoneNil : Pattern := .apply "head-or-none" [nilAtom]

/-- `(checked-head Nil)`, interpreted as an error value. -/
def checkedHeadNil : Pattern := .apply "checked-head" [nilAtom]

/-- `(empty-of Nil)`, interpreted as the datum `Empty`. -/
def emptyOfNil : Pattern := .apply "empty-of" [nilAtom]

/-- `(done Nil)`, interpreted as the unit datum. -/
def doneNil : Pattern := .apply "done" [nilAtom]

/-- `(tail-of (cons z Nil))`, interpreted by the tail equation as the empty list. -/
def tailOfSingleton : Pattern := .apply "tail-of" [.apply "cons" [sym "z", nilAtom]]

def noneSpace : Multiset Pattern := {equation headOrNoneNil noneAtom}

def errorSpace : Multiset Pattern := {equation checkedHeadNil (errorAtom checkedHeadNil "empty-list")}

def emptySpace : Multiset Pattern := {equation emptyOfNil emptyAtom}

def unitSpace : Multiset Pattern := {equation doneNil unitAtom}

/-- The tail equation `(= (tail-of (cons $h $t)) $t)`. -/
def tailSpace : Multiset Pattern :=
  {equation (.apply "tail-of" [.apply "cons" [.fvar "h", .fvar "t"]]) (.fvar "t")}

/-- A space binding the key `k1` to `None`. -/
def entry (key value : Pattern) : Pattern := .apply "entry" [key, value]

def mapSpace : Multiset Pattern := {entry (sym "k1") noneAtom}

/-- Looking a key up: the values bound to it. -/
def lookup (key : Pattern) : Multiset Pattern :=
  query reference mapSpace (entry key (.fvar "v")) (.fvar "v")

/-- The lookup as a call. -/
def lookupCall (key : Pattern) : Pattern :=
  .apply "match" [sym "&self", entry key (.fvar "v"), .fvar "v"]

theorem evaluate_headOfNil : evaluateOne reference (0 : Multiset Pattern) headOfNil = {headOfNil} :=
  rfl

theorem evaluate_headOrNoneNil : evaluateOne reference noneSpace headOrNoneNil = {noneAtom} := by
  simp [reference, evaluateOne, interpretedResults, equationResults, queryAll, query, structuralModel,
    matchPattern, matchArgs, mergeBindings, viewEquation?, noneSpace, equation, headOrNoneNil,
    noneAtom, nilAtom, sym, applyBindings, allAtomsVariable]

theorem evaluate_checkedHeadNil :
    evaluateOne reference errorSpace checkedHeadNil = {errorAtom checkedHeadNil "empty-list"} := by
  simp [reference, evaluateOne, interpretedResults, equationResults, queryAll, query, structuralModel,
    matchPattern, matchArgs, mergeBindings, viewEquation?, errorSpace, equation, checkedHeadNil,
    errorAtom, nilAtom, sym, applyBindings, allAtomsVariable]

theorem evaluate_emptyOfNil : evaluateOne reference emptySpace emptyOfNil = {emptyAtom} := by
  simp [reference, evaluateOne, interpretedResults, equationResults, queryAll, query, structuralModel,
    matchPattern, matchArgs, mergeBindings, viewEquation?, emptySpace, equation, emptyOfNil,
    emptyAtom, nilAtom, sym, applyBindings, allAtomsVariable]

theorem evaluate_doneNil : evaluateOne reference unitSpace doneNil = {unitAtom} := by
  simp [reference, evaluateOne, interpretedResults, equationResults, queryAll, query, structuralModel,
    matchPattern, matchArgs, mergeBindings, viewEquation?, unitSpace, equation, doneNil,
    unitAtom, reify, nilAtom, sym, applyBindings, allAtomsVariable]

theorem evaluate_tailOfSingleton : evaluateOne reference tailSpace tailOfSingleton = {nilAtom} := by
  simp [reference, evaluateOne, interpretedResults, equationResults, queryAll, query, structuralModel,
    matchPattern, matchArgs, mergeBindings, viewEquation?, tailSpace, equation, tailOfSingleton,
    nilAtom, sym, applyBindings, allAtomsVariable]

theorem lookup_bound : lookup (sym "k1") = {noneAtom} := by
  simp [lookup, reference, query, structuralModel, matchPattern, matchArgs, mergeBindings, mapSpace, entry,
    noneAtom, sym, applyBindings]

theorem lookup_absent : lookup (sym "k2") = 0 := by
  simp [lookup, reference, query, structuralModel, matchPattern, matchArgs, mergeBindings, mapSpace, entry,
    noneAtom, sym]

/-! ## The kinds and their witnesses -/

/-- The thirteen kinds of no-value. -/
inductive Kind where
  | zeroAnswers
  | unitDatum
  | emptyCollection
  | errorValue
  | inertCall
  | noneValue
  | emptyDatum
  | neither
  | undetermined
  | incomplete
  | refuted
  | closedEmptyType
  | openDeclaredType
  deriving DecidableEq, Repr

/-- Judgment outcomes, with their evidence forgotten. -/
abbrev Verdict := Outcome Unit Unit Unit Unit

/-- Where a no-value lives. -/
inductive Witness where
  /-- An evaluation or query: its subject and its answer bag. -/
  | answers (subject : Pattern) (bag : Multiset Pattern)
  /-- The joint status of a positive and a negative evidence lane. -/
  | evidence (status : FourVerdict)
  /-- A judgment outcome. -/
  | verdict (outcome : Verdict)
  /-- The status of a declared type. -/
  | declaration (status : OpenDeclarations.Status String)

/-- The witness of each kind; answer bags are computed by the reference evaluator. -/
def Kind.witness : Kind → Witness
  | .zeroAnswers => .answers (lookupCall (sym "k2")) (lookup (sym "k2"))
  | .unitDatum => .answers doneNil (evaluateOne reference unitSpace doneNil)
  | .emptyCollection => .answers tailOfSingleton (evaluateOne reference tailSpace tailOfSingleton)
  | .errorValue => .answers checkedHeadNil (evaluateOne reference errorSpace checkedHeadNil)
  | .inertCall => .answers headOfNil (evaluateOne reference (0 : Multiset Pattern) headOfNil)
  | .noneValue => .answers headOrNoneNil (evaluateOne reference noneSpace headOrNoneNil)
  | .emptyDatum => .answers emptyOfNil (evaluateOne reference emptySpace emptyOfNil)
  | .neither => .evidence (fourOfLanes false false)
  | .undetermined => .verdict (.outsideFragment ())
  | .incomplete => .verdict (.incomplete ())
  | .refuted => .verdict (.refuted ())
  | .closedEmptyType => .declaration (.closed ∅)
  | .openDeclaredType => .declaration (.declared ∅)

/-! ## Observations -/

/-- No answer. -/
def NoAnswer : Witness → Prop
  | .answers _ bag => bag = 0
  | _ => False

/-- The answer is the reification of zero answers, the unit datum. -/
def UnitAnswer : Witness → Prop
  | .answers _ bag => bag = {reify []}
  | _ => False

/-- The answer is the empty list. -/
def EmptyCollectionAnswer : Witness → Prop
  | .answers _ bag => bag = {nilAtom}
  | _ => False

/-- An error value among the answers. -/
def ErrorAnswer : Witness → Prop
  | .answers _ bag => ∃ answer ∈ bag, IsErrorAtom answer
  | _ => False

/-- Evaluation retained its subject. -/
def RetainedSubject : Witness → Prop
  | .answers subject bag => bag = {subject}
  | _ => False

/-- The option protocol reads the answer as absent. -/
def OptionAbsent : Witness → Prop
  | .answers _ bag => bag = {noneAtom}
  | _ => False

/-- HE's sentinel protocol would delete an answer. -/
def SentinelAnswer : Witness → Prop
  | .answers _ bag => emptyAtom ∈ bag
  | _ => False

/-- The bottom of the knowledge order: every status refines it. -/
def KnowledgeBottom : Witness → Prop
  | .evidence status => ∀ other, FourVerdict.knowledgeLE status other = true
  | _ => False

/-- No verdict, and no budget changes it. -/
def BudgetStableGap : Witness → Prop
  | .verdict outcome =>
      outcome.asBool = none ∧ ∀ later, Outcome.BudgetRefines outcome later → later = outcome
  | _ => False

/-- No verdict, but more budget can give one. -/
def BudgetResolvableGap : Witness → Prop
  | .verdict outcome =>
      outcome.asBool = none ∧ ∃ later, Outcome.BudgetRefines outcome later ∧ later.asBool ≠ none
  | _ => False

/-- A checked negative verdict. -/
def CheckedNegative : Witness → Prop
  | .verdict outcome => outcome.asBool = some false
  | _ => False

/-- The declaration entails that the type is empty. -/
def EntailsEmpty : Witness → Prop
  | .declaration status =>
      Entails (OpenDeclarations.Sat (V := ℕ)) status.theory .isEmpty
  | _ => False

/-- The declaration leaves inhabitation undetermined. -/
def InhabitationOpen : Witness → Prop
  | .declaration status =>
      ¬ Entails (OpenDeclarations.Sat (V := ℕ)) status.theory .inhabited ∧
        ¬ Entails (OpenDeclarations.Sat (V := ℕ)) status.theory .isEmpty
  | _ => False

/-- The observation characteristic of each kind. -/
def Kind.observation : Kind → Witness → Prop
  | .zeroAnswers => NoAnswer
  | .unitDatum => UnitAnswer
  | .emptyCollection => EmptyCollectionAnswer
  | .errorValue => ErrorAnswer
  | .inertCall => RetainedSubject
  | .noneValue => OptionAbsent
  | .emptyDatum => SentinelAnswer
  | .neither => KnowledgeBottom
  | .undetermined => BudgetStableGap
  | .incomplete => BudgetResolvableGap
  | .refuted => CheckedNegative
  | .closedEmptyType => EntailsEmpty
  | .openDeclaredType => InhabitationOpen

/-! ## Each observation picks out its kind -/

/-! ### The witnesses, computed -/

theorem witness_zeroAnswers :
    Kind.zeroAnswers.witness = .answers (lookupCall (sym "k2")) 0 := by
  simp only [Kind.witness, lookup_absent]

theorem witness_unitDatum : Kind.unitDatum.witness = .answers doneNil {unitAtom} := by
  simp only [Kind.witness, evaluate_doneNil]

theorem witness_emptyCollection :
    Kind.emptyCollection.witness = .answers tailOfSingleton {nilAtom} := by
  simp only [Kind.witness, evaluate_tailOfSingleton]

theorem witness_errorValue :
    Kind.errorValue.witness = .answers checkedHeadNil {errorAtom checkedHeadNil "empty-list"} := by
  simp only [Kind.witness, evaluate_checkedHeadNil]

theorem witness_inertCall : Kind.inertCall.witness = .answers headOfNil {headOfNil} := by
  simp only [Kind.witness, evaluate_headOfNil]

theorem witness_noneValue : Kind.noneValue.witness = .answers headOrNoneNil {noneAtom} := by
  simp only [Kind.witness, evaluate_headOrNoneNil]

theorem witness_emptyDatum : Kind.emptyDatum.witness = .answers emptyOfNil {emptyAtom} := by
  simp only [Kind.witness, evaluate_emptyOfNil]

theorem witness_neither : Kind.neither.witness = .evidence (fourOfLanes false false) := rfl

theorem witness_undetermined : Kind.undetermined.witness = .verdict (.outsideFragment ()) := rfl

theorem witness_incomplete : Kind.incomplete.witness = .verdict (.incomplete ()) := rfl

theorem witness_refuted : Kind.refuted.witness = .verdict (.refuted ()) := rfl

theorem witness_closedEmptyType : Kind.closedEmptyType.witness = .declaration (.closed ∅) := rfl

theorem witness_openDeclaredType :
    Kind.openDeclaredType.witness = .declaration (.declared ∅) := rfl

theorem not_isErrorAtom_apply (head : String) (arguments : List Pattern) (different : head ≠ "Error") :
    ¬ IsErrorAtom (.apply head arguments) := by
  rintro ⟨arguments', equal⟩
  simp only [Pattern.apply.injEq] at equal
  exact different equal.1

theorem isErrorAtom_errorAtom (subject : Pattern) (message : String) :
    IsErrorAtom (errorAtom subject message) :=
  ⟨_, rfl⟩

theorem not_isErrorAtom_unitAtom : ¬ IsErrorAtom unitAtom := by
  rintro ⟨arguments, equal⟩
  cases equal

/-! ### Each observation picks out its kind -/

theorem noAnswer_iff (k : Kind) : NoAnswer k.witness ↔ k = .zeroAnswers := by
  cases k <;> simp [witness_zeroAnswers, witness_unitDatum, witness_emptyCollection,
    witness_errorValue, witness_inertCall, witness_noneValue, witness_emptyDatum, witness_neither, witness_undetermined, witness_incomplete, witness_refuted,
    witness_closedEmptyType, witness_openDeclaredType, NoAnswer]

theorem errorAnswer_iff (k : Kind) : ErrorAnswer k.witness ↔ k = .errorValue := by
  cases k <;> simp only [witness_zeroAnswers, witness_unitDatum, witness_emptyCollection,
    witness_errorValue, witness_inertCall,
    witness_noneValue, witness_emptyDatum, witness_neither, witness_undetermined,
    witness_incomplete, witness_refuted, witness_closedEmptyType, witness_openDeclaredType,
    ErrorAnswer, Multiset.mem_singleton, exists_eq_left, Multiset.notMem_zero, false_and,
    exists_false, reduceCtorEq, iff_false, iff_true]
  · exact not_isErrorAtom_unitAtom
  · exact not_isErrorAtom_apply "Nil" _ (by decide)
  · exact isErrorAtom_errorAtom _ _
  · exact not_isErrorAtom_apply "head-of" _ (by decide)
  · exact not_isErrorAtom_apply "None" _ (by decide)
  · exact not_isErrorAtom_apply "Empty" _ (by decide)

theorem unitAnswer_iff (k : Kind) : UnitAnswer k.witness ↔ k = .unitDatum := by
  cases k <;> simp [witness_zeroAnswers, witness_unitDatum, witness_emptyCollection,
    witness_errorValue, witness_inertCall, witness_noneValue, witness_emptyDatum, witness_neither,
    witness_undetermined, witness_incomplete, witness_refuted, witness_closedEmptyType,
    witness_openDeclaredType, UnitAnswer, unitAtom, reify, errorAtom, headOfNil, noneAtom,
    emptyAtom, nilAtom, sym]

theorem emptyCollectionAnswer_iff (k : Kind) :
    EmptyCollectionAnswer k.witness ↔ k = .emptyCollection := by
  cases k <;> simp [witness_zeroAnswers, witness_unitDatum, witness_emptyCollection,
    witness_errorValue, witness_inertCall, witness_noneValue, witness_emptyDatum, witness_neither,
    witness_undetermined, witness_incomplete, witness_refuted, witness_closedEmptyType,
    witness_openDeclaredType, EmptyCollectionAnswer, unitAtom, reify, errorAtom, headOfNil,
    noneAtom, emptyAtom, nilAtom, sym]

theorem retainedSubject_iff (k : Kind) : RetainedSubject k.witness ↔ k = .inertCall := by
  cases k <;> simp [witness_zeroAnswers, witness_unitDatum, witness_emptyCollection,
    witness_errorValue, witness_inertCall, witness_noneValue, witness_emptyDatum, witness_neither, witness_undetermined, witness_incomplete, witness_refuted,
    witness_closedEmptyType, witness_openDeclaredType, RetainedSubject, errorAtom, checkedHeadNil,
    noneAtom, headOrNoneNil, emptyAtom, emptyOfNil, unitAtom, reify, doneNil, nilAtom,
    tailOfSingleton, sym]

theorem optionAbsent_iff (k : Kind) : OptionAbsent k.witness ↔ k = .noneValue := by
  cases k <;> simp [witness_zeroAnswers, witness_unitDatum, witness_emptyCollection,
    witness_errorValue, witness_inertCall, witness_noneValue, witness_emptyDatum, witness_neither, witness_undetermined, witness_incomplete, witness_refuted,
    witness_closedEmptyType, witness_openDeclaredType, OptionAbsent, errorAtom, headOfNil,
    noneAtom, emptyAtom, unitAtom, reify, nilAtom, sym]

theorem sentinelAnswer_iff (k : Kind) : SentinelAnswer k.witness ↔ k = .emptyDatum := by
  cases k <;> simp [witness_zeroAnswers, witness_unitDatum, witness_emptyCollection,
    witness_errorValue, witness_inertCall, witness_noneValue, witness_emptyDatum, witness_neither, witness_undetermined, witness_incomplete, witness_refuted,
    witness_closedEmptyType, witness_openDeclaredType, SentinelAnswer, errorAtom, headOfNil,
    noneAtom, emptyAtom, unitAtom, reify, nilAtom, sym]

/-- **Neither is the bottom of the knowledge order.** -/
theorem neither_knowledge_bottom (other : FourVerdict) :
    FourVerdict.knowledgeLE (fourOfLanes false false) other = true := by
  cases other <;> rfl

theorem knowledgeBottom_iff (k : Kind) : KnowledgeBottom k.witness ↔ k = .neither := by
  cases k <;> simp only [witness_zeroAnswers, witness_unitDatum, witness_emptyCollection,
    witness_errorValue, witness_inertCall,
    witness_noneValue, witness_emptyDatum, witness_neither, witness_undetermined,
    witness_incomplete, witness_refuted, witness_closedEmptyType, witness_openDeclaredType,
    KnowledgeBottom, reduceCtorEq, iff_true]
  exact neither_knowledge_bottom

theorem budgetStableGap_iff (k : Kind) : BudgetStableGap k.witness ↔ k = .undetermined := by
  cases k <;> simp only [witness_zeroAnswers, witness_unitDatum, witness_emptyCollection,
    witness_errorValue, witness_inertCall,
    witness_noneValue, witness_emptyDatum, witness_neither, witness_undetermined,
    witness_incomplete, witness_refuted, witness_closedEmptyType, witness_openDeclaredType,
    BudgetStableGap, reduceCtorEq, iff_false, iff_true, not_and]
  · exact ⟨rfl, fun later refinement => Outcome.budget_does_not_resolve_outside () later refinement⟩
  · intro _ stable
    have resolved := stable (.established ()) (.incompleteEstablished () ())
    cases resolved
  · intro decided
    cases decided

theorem budgetResolvableGap_iff (k : Kind) : BudgetResolvableGap k.witness ↔ k = .incomplete := by
  cases k <;> simp only [witness_zeroAnswers, witness_unitDatum, witness_emptyCollection,
    witness_errorValue, witness_inertCall,
    witness_noneValue, witness_emptyDatum, witness_neither, witness_undetermined,
    witness_incomplete, witness_refuted, witness_closedEmptyType, witness_openDeclaredType,
    BudgetResolvableGap, reduceCtorEq, iff_false, iff_true, not_and, not_exists]
  · intro _ later refinement
    rw [Outcome.budget_does_not_resolve_outside () later refinement]
    exact fun decided => decided rfl
  · exact ⟨rfl, .established (), .incompleteEstablished () (), by simp [Outcome.asBool]⟩
  · intro decided
    cases decided

theorem checkedNegative_iff (k : Kind) : CheckedNegative k.witness ↔ k = .refuted := by
  cases k <;> simp [witness_zeroAnswers, witness_unitDatum, witness_emptyCollection,
    witness_errorValue, witness_inertCall, witness_noneValue, witness_emptyDatum, witness_neither, witness_undetermined, witness_incomplete, witness_refuted,
    witness_closedEmptyType, witness_openDeclaredType, CheckedNegative, Outcome.asBool]

theorem entailsEmpty_iff (k : Kind) : EntailsEmpty k.witness ↔ k = .closedEmptyType := by
  cases k <;> simp only [witness_zeroAnswers, witness_unitDatum, witness_emptyCollection,
    witness_errorValue, witness_inertCall,
    witness_noneValue, witness_emptyDatum, witness_neither, witness_undetermined,
    witness_incomplete, witness_refuted, witness_closedEmptyType, witness_openDeclaredType,
    EntailsEmpty, reduceCtorEq, iff_false, iff_true]
  · exact OpenDeclarations.closedDecl_empty_entails_isEmpty
  · exact (OpenDeclarations.openDecl_empty_undetermined (N := String) (0 : ℕ)).2

theorem inhabitationOpen_iff (k : Kind) : InhabitationOpen k.witness ↔ k = .openDeclaredType := by
  cases k <;> simp only [witness_zeroAnswers, witness_unitDatum, witness_emptyCollection,
    witness_errorValue, witness_inertCall,
    witness_noneValue, witness_emptyDatum, witness_neither, witness_undetermined,
    witness_incomplete, witness_refuted, witness_closedEmptyType, witness_openDeclaredType,
    InhabitationOpen, reduceCtorEq, iff_false, iff_true, not_and, not_not]
  · intro _
    exact OpenDeclarations.closedDecl_empty_entails_isEmpty
  · exact OpenDeclarations.openDecl_empty_undetermined (N := String) (0 : ℕ)

/-- **Each observation holds of its own kind's witness and of no other.** -/
theorem Kind.observation_witness_iff (k k' : Kind) : k.observation k'.witness ↔ k' = k := by
  cases k
  · exact noAnswer_iff k'
  · exact unitAnswer_iff k'
  · exact emptyCollectionAnswer_iff k'
  · exact errorAnswer_iff k'
  · exact retainedSubject_iff k'
  · exact optionAbsent_iff k'
  · exact sentinelAnswer_iff k'
  · exact knowledgeBottom_iff k'
  · exact budgetStableGap_iff k'
  · exact budgetResolvableGap_iff k'
  · exact checkedNegative_iff k'
  · exact entailsEmpty_iff k'
  · exact inhabitationOpen_iff k'

/-- **Non-collapse: every two kinds are told apart by an observation.** -/
theorem Kind.separated {k k' : Kind} (different : k ≠ k') :
    ∃ observe : Witness → Prop, observe k.witness ∧ ¬ observe k'.witness :=
  ⟨k.observation, (k.observation_witness_iff k).mpr rfl,
    fun holds => different ((k.observation_witness_iff k').mp holds).symm⟩

theorem Kind.witness_injective : Function.Injective Kind.witness := by
  intro k k' equal
  have holds : k.observation k'.witness := equal ▸ (k.observation_witness_iff k).mpr rfl
  exact ((k.observation_witness_iff k').mp holds).symm

/-! ## Laws of the answer face -/

/-- Zero answers is the unit of answer union. -/
theorem zeroAnswers_add (bag : Multiset Pattern) : 0 + bag = bag :=
  zero_add bag

/-- A continuation of zero answers has zero answers. -/
theorem zeroAnswers_bind (continuation : Pattern → Multiset Pattern) :
    (0 : Multiset Pattern).bind continuation = 0 :=
  Multiset.zero_bind _

/-- One answer, an error value included, is passed to the continuation. -/
theorem singleton_bind (answer : Pattern) (continuation : Pattern → Multiset Pattern) :
    ({answer} : Multiset Pattern).bind continuation = continuation answer :=
  Multiset.singleton_bind _ _

/-! ## Collapses -/

/-- HE's sentinel reading: the datum `Empty` is deleted from answers. -/
def heView (bag : Multiset Pattern) : Multiset Pattern :=
  bag.filter (· ≠ emptyAtom)

/-- **HE's sentinel reading identifies the datum `Empty` with zero answers.** -/
theorem heView_collapses :
    heView (evaluateOne reference emptySpace emptyOfNil) = heView (lookup (sym "k2")) := by
  rw [evaluate_emptyOfNil, lookup_absent]
  simp [heView]

/-- The identity function `(= (myid $x) $x)`. -/
def identitySpace : Multiset Pattern := {equation (.apply "myid" [.fvar "x"]) (.fvar "x")}

theorem evaluate_myid (argument : Pattern) (ground : argument = emptyAtom ∨ argument = noneAtom) :
    evaluateOne reference identitySpace (.apply "myid" [argument]) = {argument} := by
  rcases ground with rfl | rfl <;>
    simp [reference, evaluateOne, interpretedResults, equationResults, queryAll, query, structuralModel,
      matchPattern, matchArgs, mergeBindings, viewEquation?, identitySpace, equation, emptyAtom,
      noneAtom, sym, applyBindings, allAtomsVariable]

/-- **Under the sentinel reading the identity function cannot return `Empty`**, while it
returns `None`. -/
theorem heView_identity_quirk :
    heView (evaluateOne reference identitySpace (.apply "myid" [emptyAtom])) = 0 ∧
      heView (evaluateOne reference identitySpace (.apply "myid" [noneAtom])) = {noneAtom} := by
  rw [evaluate_myid _ (Or.inl rfl), evaluate_myid _ (Or.inr rfl)]
  constructor
  · simp [heView]
  · rw [heView, Multiset.filter_singleton, if_pos]
    simp [noneAtom, emptyAtom, sym]

/-- Evaluation without inert retention: only what interprets the subject. -/
def withoutRetention (model : Model) (space : model.Space) (subject : Pattern) : Multiset Pattern :=
  interpretedResults model space subject

/-- **Without inert retention an uninterpreted call has zero answers**, where the
reference evaluator retains it. -/
theorem withoutRetention_collapses :
    withoutRetention reference (0 : Multiset Pattern) headOfNil = 0 ∧ evaluateOne reference (0 : Multiset Pattern) headOfNil = {headOfNil} :=
  ⟨rfl, rfl⟩

/-- **MeTTa Zero evaluation never yields zero answers.** -/
theorem evaluateOne_ne_zero (model : Model) (space : model.Space) (subject : Pattern) :
    evaluateOne model space subject ≠ 0 := by
  unfold evaluateOne
  dsimp only
  split
  · exact Multiset.singleton_ne_zero _
  · assumption

/-- An operation that answers nothing: `(nothing)`. -/
def nothingCall : Pattern := .apply "nothing" []

/-- **A grounded operation answering nothing is retained inert.** -/
theorem groundedNothing_retained :
    evaluateOne (structuralModel fun _ => 0) (0 : Multiset Pattern) nothingCall = {nothingCall} :=
  rfl

/-- What a grounded operation does with a subject: decline it, or answer it with a bag,
possibly empty. -/
inductive GroundAnswer where
  | declines
  | answers (bag : Multiset Pattern)

/-- One-step evaluation with a two-channel grounding boundary. -/
def evaluateTwoChannel (model : Model) (space : model.Space) (ground : Pattern → GroundAnswer)
    (subject : Pattern) : Multiset Pattern :=
  match ground subject with
  | .answers bag => equationResults model space subject + bag
  | .declines =>
      if equationResults model space subject = 0 then {subject}
      else equationResults model space subject

/-- Where the operation declines, the two-channel evaluator agrees with MeTTa Zero's. -/
theorem evaluateTwoChannel_eq_of_declines (model : Model) (space : model.Space)
    (ground : Pattern → GroundAnswer) (subject : Pattern) (declines : ground subject = .declines)
    (noGround : model.groundApply subject = 0) :
    evaluateTwoChannel model space ground subject = evaluateOne model space subject := by
  simp only [evaluateTwoChannel, declines, evaluateOne, interpretedResults, noGround, add_zero]

/-- Where the operation answers a nonempty bag, they agree too. -/
theorem evaluateTwoChannel_eq_of_answers (model : Model) (space : model.Space)
    (ground : Pattern → GroundAnswer) (subject : Pattern) {bag : Multiset Pattern}
    (answers : ground subject = .answers bag) (nonempty : bag ≠ 0)
    (grounded : model.groundApply subject = bag) :
    evaluateTwoChannel model space ground subject = evaluateOne model space subject := by
  have nonzero : equationResults model space subject + bag ≠ 0 := by
    intro zero
    exact nonempty (add_eq_zero.mp zero).2
  simp only [evaluateTwoChannel, answers, evaluateOne, interpretedResults, grounded,
    if_neg nonzero]

/-- **They differ exactly where the operation answers nothing**: zero answers instead of
retention. -/
theorem evaluateTwoChannel_answers_zero (model : Model) (space : model.Space)
    (ground : Pattern → GroundAnswer) (subject : Pattern) (answers : ground subject = .answers 0)
    (uninterpreted : equationResults model space subject = 0) (grounded : model.groundApply subject = 0) :
    evaluateTwoChannel model space ground subject = 0 ∧
      evaluateOne model space subject = {subject} := by
  constructor
  · simp only [evaluateTwoChannel, answers, uninterpreted, add_zero]
  · simp only [evaluateOne, interpretedResults, uninterpreted, grounded, add_zero, if_true]

/-- A null test on lookups: no value, or the value `None`. -/
def nullTest (bag : Multiset Pattern) : Prop :=
  bag = 0 ∨ bag = {noneAtom}

/-- **A null test identifies an absent key with a key bound to `None`.** -/
theorem nullTest_collapses :
    nullTest (lookup (sym "k2")) ∧ nullTest (lookup (sym "k1")) ∧
      lookup (sym "k2") ≠ lookup (sym "k1") := by
  rw [lookup_absent, lookup_bound]
  exact ⟨Or.inl rfl, Or.inr rfl, (Multiset.singleton_ne_zero _).symm⟩

/-- A verdict read as a Boolean, with `false` for no verdict. -/
def toBool (outcome : Verdict) : Bool :=
  outcome.asBool.getD false

/-- The outcome of the negated claim: established and refuted exchange. -/
def negate : Verdict → Verdict
  | .established evidence => .refuted evidence
  | .refuted obstruction => .established obstruction
  | .outsideFragment reason => .outsideFragment reason
  | .incomplete receipt => .incomplete receipt

/-- **Reading verdicts as Booleans identifies refuted, undetermined and incomplete.** -/
theorem toBool_collapses :
    toBool (.refuted ()) = toBool (.outsideFragment ()) ∧
      toBool (.outsideFragment ()) = toBool (.incomplete ()) :=
  ⟨rfl, rfl⟩

/-- **A claim passes the filter or its negation exactly when it has a verdict.** -/
theorem toBool_excluded_middle_iff (outcome : Verdict) :
    (toBool outcome = true ∨ toBool (negate outcome) = true) ↔ outcome.asBool.isSome := by
  cases outcome <;> simp [toBool, negate, Outcome.asBool]

/-- Strong Kleene conjunction. -/
def kleeneAnd : Option Bool → Option Bool → Option Bool
  | some false, _ => some false
  | _, some false => some false
  | some true, some true => some true
  | _, _ => none

/-- SQL inequality with an unknown entry. -/
def sqlNe (x : ℕ) : Option ℕ → Option Bool
  | some y => some (decide (x ≠ y))
  | none => none

/-- SQL `x NOT IN column`. -/
def sqlNotIn (x : ℕ) (column : List (Option ℕ)) : Option Bool :=
  column.foldr (fun entry rest => kleeneAnd (sqlNe x entry) rest) (some true)

/-- **`NOT IN` over a column with an unknown entry has no verdict, and the filter drops
the row**, although every present value differs; with the missing entry absent instead,
the test is decided. -/
theorem sqlNotIn_unknown :
    sqlNotIn 2 [some 1, none] = none ∧ (sqlNotIn 2 [some 1, none]).getD false = false ∧
      sqlNotIn 2 [some 1] = some true := by
  decide

/-! ## HE's completed-set normalization

HE normalizes the alternatives of every evaluated expression before they reach the
caller: the datum `Empty` is dropped when anything else arrived, and error values are
dropped when anything succeeded.  Each rule is conditional on what else arrived, so it
identifies kinds the zoo keeps apart, and it is not monotone in the alternatives: a later
success erases an earlier error.  A producer that emits alternatives as they arrive
cannot compute it; every level must buffer its completed set.  A retention policy keeps every value
and error occurrence, and a success-only view is an explicit, monotone observation. -/

/-- A Boolean test for an error value. -/
def isErrorB : Pattern → Bool
  | .apply head _ => head == "Error"
  | _ => false

theorem isErrorB_iff (answer : Pattern) : isErrorB answer = true ↔ IsErrorAtom answer := by
  cases answer with
  | apply head arguments =>
      simp only [isErrorB, beq_iff_eq, IsErrorAtom, Pattern.apply.injEq]
      exact ⟨fun equal => ⟨arguments, equal, rfl⟩, fun ⟨_, equal, _⟩ => equal⟩
  | _ => simp [isErrorB, IsErrorAtom]

/-- An alternative succeeded: it is neither `Empty` nor an error value. -/
def isSuccessB (answer : Pattern) : Bool :=
  answer != emptyAtom && !isErrorB answer

/-- HE's first rule: `Empty` is dropped when anything else arrived. -/
def dropEmptyIfOther (bag : Multiset Pattern) : Multiset Pattern :=
  if bag.filter (· ≠ emptyAtom) = 0 then bag else bag.filter (· ≠ emptyAtom)

/-- HE's second rule: error values are dropped when anything succeeded. -/
def dropErrorsIfSuccess (bag : Multiset Pattern) : Multiset Pattern :=
  if bag.filter (fun answer => isSuccessB answer = true) = 0 then bag
  else bag.filter (fun answer => isErrorB answer = false)

/-- HE's normalization of the completed alternatives of one evaluation. -/
def heNormalize (bag : Multiset Pattern) : Multiset Pattern :=
  dropErrorsIfSuccess (dropEmptyIfOther bag)

/-- The answer `True`. -/
def trueAtom : Pattern := sym "True"

/-- An error alternative, as an ill-formed call reports it. -/
def arityError : Pattern := errorAtom (.apply "f" []) "IncorrectNumberOfArguments"

theorem isErrorB_arityError : isErrorB arityError = true := rfl

theorem isErrorB_trueAtom : isErrorB trueAtom = false := rfl

theorem trueAtom_ne_emptyAtom : trueAtom ≠ emptyAtom := by
  simp [trueAtom, emptyAtom, sym]

theorem arityError_ne_emptyAtom : arityError ≠ emptyAtom := by
  simp [arityError, errorAtom, emptyAtom, sym]

theorem arityError_ne_trueAtom : arityError ≠ trueAtom := by
  simp [arityError, errorAtom, trueAtom, sym]

theorem isSuccessB_trueAtom : isSuccessB trueAtom = true := by
  simp [isSuccessB, trueAtom_ne_emptyAtom, isErrorB_trueAtom]

theorem isSuccessB_arityError : isSuccessB arityError = false := by
  simp [isSuccessB, isErrorB_arityError]

/-- **An error alternative beside a success is erased.** -/
theorem heNormalize_error_beside_success :
    heNormalize {arityError, trueAtom} = {trueAtom} := by
  simp [heNormalize, dropEmptyIfOther, dropErrorsIfSuccess, arityError_ne_emptyAtom,
    trueAtom_ne_emptyAtom, isSuccessB_trueAtom, isSuccessB_arityError, isErrorB_arityError,
    isErrorB_trueAtom]

/-- Alone, the error alternative is kept. -/
theorem heNormalize_error_alone : heNormalize {arityError} = {arityError} := by
  simp [heNormalize, dropEmptyIfOther, dropErrorsIfSuccess, Multiset.filter_singleton,
    arityError_ne_emptyAtom, isSuccessB_arityError]

theorem heNormalize_success_alone : heNormalize {trueAtom} = {trueAtom} := by
  simp [heNormalize, dropEmptyIfOther, dropErrorsIfSuccess, Multiset.filter_singleton,
    trueAtom_ne_emptyAtom, isSuccessB_trueAtom, isErrorB_trueAtom]

/-- **The kinds collapse**: with and without the error alternative, the same normal
form, so no observation of the normal form can report the error. -/
theorem heNormalize_collapses :
    heNormalize {arityError, trueAtom} = heNormalize {trueAtom} := by
  rw [heNormalize_error_beside_success, heNormalize_success_alone]

/-- The datum `Empty` beside an answer is erased too. -/
theorem heNormalize_empty_beside_answer :
    heNormalize {emptyAtom, trueAtom} = {trueAtom} := by
  simp [heNormalize, dropEmptyIfOther, dropErrorsIfSuccess, trueAtom_ne_emptyAtom,
    isSuccessB_trueAtom, isErrorB_trueAtom]

/-- **HE's normalization is not monotone**: one more alternative can remove one that
was there. -/
theorem heNormalize_not_monotone :
    ¬ ∀ bag bag' : Multiset Pattern, bag ≤ bag' → heNormalize bag ≤ heNormalize bag' := by
  intro monotone
  have extended : ({arityError} : Multiset Pattern) ≤ {arityError, trueAtom} := by
    rw [Multiset.insert_eq_cons, ← Multiset.cons_zero]
    exact Multiset.cons_le_cons _ (Multiset.zero_le _)
  have image := monotone _ _ extended
  rw [heNormalize_error_alone, heNormalize_error_beside_success, Multiset.singleton_le,
    Multiset.mem_singleton] at image
  exact arityError_ne_trueAtom image

/-- **No streaming producer computes it**: an emission that only grows as alternatives
arrive cannot agree with HE's normalization on every completed set, so each level must
buffer its alternatives until they are complete. -/
theorem no_streaming_heNormalize (emit : Multiset Pattern → Multiset Pattern)
    (monotone : ∀ bag bag', bag ≤ bag' → emit bag ≤ emit bag') :
    ¬ ∀ bag, emit bag = heNormalize bag := by
  intro agrees
  apply heNormalize_not_monotone
  intro bag bag' included
  rw [← agrees bag, ← agrees bag']
  exact monotone bag bag' included

/-- An explicit success-only observation: the alternatives that are not error
values.  The datum `Empty` is data and stays. -/
def withoutErrors (bag : Multiset Pattern) : Multiset Pattern :=
  bag.filter (fun answer => isErrorB answer = false)

/-- **The explicit observation is monotone**, so it can be taken as alternatives arrive. -/
theorem withoutErrors_monotone {bag bag' : Multiset Pattern} (included : bag ≤ bag') :
    withoutErrors bag ≤ withoutErrors bag' :=
  Multiset.filter_le_filter _ included

/-- Where something succeeded and no `Empty` arrived, HE's normal form is the explicit
observation of the completed set. -/
theorem heNormalize_eq_withoutErrors {bag : Multiset Pattern} (noEmpty : emptyAtom ∉ bag)
    (success : bag.filter (fun answer => isSuccessB answer = true) ≠ 0) :
    heNormalize bag = withoutErrors bag := by
  have kept : dropEmptyIfOther bag = bag := by
    unfold dropEmptyIfOther
    split_ifs
    · rfl
    · exact Multiset.filter_eq_self.mpr fun answer member equal => noEmpty (equal ▸ member)
  unfold heNormalize
  rw [kept]
  unfold dropErrorsIfSuccess
  rw [if_neg success]
  rfl

/-! ### The same collapse across programs

Adding an equation for a head can erase an error alternative that its other equation
produced: the error vanishes from the normal form, while the evaluation itself still
has it. -/

/-- `(f)`, defined by an equation whose right side reports an error. -/
def fCall : Pattern := .apply "f" []

def failingSpace : Multiset Pattern := {equation fCall arityError}

/-- The same program with a second, succeeding equation for `(f)`. -/
def siblingSpace : Multiset Pattern := {equation fCall trueAtom, equation fCall arityError}

theorem evaluate_failing : evaluateOne reference failingSpace fCall = {arityError} := by
  simp [reference, evaluateOne, interpretedResults, equationResults, queryAll, query, structuralModel,
    matchPattern, matchArgs, viewEquation?, failingSpace, equation, fCall, arityError, errorAtom,
    sym, applyBindings, allAtomsVariable]

theorem evaluate_sibling :
    evaluateOne reference siblingSpace fCall = {trueAtom, arityError} := by
  simp [reference, evaluateOne, interpretedResults, equationResults, queryAll, query, structuralModel,
    matchPattern, matchArgs, viewEquation?, siblingSpace, equation, fCall, arityError, errorAtom,
    trueAtom, sym, applyBindings, allAtomsVariable]

/-- **Adding a succeeding equation erases the error under HE's normalization**, while
the evaluation keeps both alternatives. -/
theorem sibling_equation_erases_error :
    heNormalize (evaluateOne reference failingSpace fCall) = {arityError} ∧
      heNormalize (evaluateOne reference siblingSpace fCall) = {trueAtom} ∧
      arityError ∈ evaluateOne reference siblingSpace fCall := by
  have swap : ({trueAtom, arityError} : Multiset Pattern) = {arityError, trueAtom} := by
    simp only [Multiset.insert_eq_cons]
    exact Multiset.cons_swap _ _ _
  rw [evaluate_failing, evaluate_sibling, swap]
  exact ⟨heNormalize_error_alone, heNormalize_error_beside_success, by simp⟩

end Mettapedia.Languages.MeTTa.Experimental.NoValueZoo

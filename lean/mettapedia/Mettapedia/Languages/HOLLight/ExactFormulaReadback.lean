import Mettapedia.Languages.HOLLight.RegisteredReplayModels
import Mettapedia.Languages.OpenTheory.ReverseTranslation
import Mettapedia.Logic.HOL.ImpredicativeConnectives

/-!
# Executable exact reading of cached source formulas

The checker compares a cached conclusion with the reverse translation of a
typed formula. Its accepted fragment consists of variables, ordinary source
symbols, application, abstraction and primitive equality. An uninterpreted
equality symbol is refused: reversing it would change its meaning.
Source Boolean definitions remain ordinary provenance-bearing symbols.

Accepted comparisons produce the existing `Translates` evidence and retain
membership in the actual theorem cache. No semantic validity is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.ExactFormulaReadback

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open ReverseTranslation ProofExecution
universe w

private theorem and_accepted {first second : Bool} (accepted : (first && second) = true) :
    first = true ∧ second = true := by
  simpa only [Bool.and_eq_true] using accepted

/-- The fragment on which reverse translation is an exact syntactic inverse. -/
def readable : {context : HOL.Ctx AtomicTy} → {type : HOL.Ty AtomicTy} →
    HOL.Term Symbol context type → Bool
  | _, _, .var _ => true
  | _, _, .const (.variable ..) => true
  | _, _, .const (.constant constant annotation _) => (equalityOperand? constant annotation).isNone
  | _, _, .app function argument => readable function && readable argument
  | _, _, .lam body => readable body
  | _, _, .eq left right => readable left && readable right
  | _, _, _ => false

private theorem constant_unrecognized {context : HOL.Ctx AtomicTy}
    {constant : Const} {annotation : Ty} {type : HOL.Ty AtomicTy}
    {typed : annotation.toHOL = type}
    (accepted : readable (.const (.constant constant annotation typed) : HOL.Term Symbol context type) = true) :
    equalityOperand? constant annotation = none := by
  cases recognized : equalityOperand? constant annotation with
  | none => rfl
  | some operand => simp [readable,recognized] at accepted

private theorem equality_head_none {context : HOL.Ctx AtomicTy} :
    ∀ {type : HOL.Ty AtomicTy} (term : HOL.Term Symbol context type), readable term = true →
      (reverseTermOpen term).equalityHeadOperand? = none
  | _, .var _, _ => rfl
  | _, .const (.constant ..), _ => rfl
  | _, .const (.variable ..), _ => rfl
  | _, .app (.const (.constant _ _ typed)) _, accepted =>
      constant_unrecognized (typed := typed) (and_accepted accepted).1
  | _, .app (.const (.variable ..)) _, _ => rfl
  | _, .app (.var _) _, _ => rfl
  | _, .app (.app _ _) _, _ => rfl
  | _, .app (.lam _) _, _ => rfl
  | _, .lam _, _ => rfl
  | _, .eq _ _, _ => rfl
  | _, .top, accepted => by cases accepted
  | _, .bot, accepted => by cases accepted
  | _, .and _ _, accepted => by cases accepted
  | _, .or _ _, accepted => by cases accepted
  | _, .imp _ _, accepted => by cases accepted
  | _, .not _, accepted => by cases accepted
  | _, .all _, accepted => by cases accepted
  | _, .ex _, accepted => by cases accepted

theorem readable_translates :
    ∀ {context : HOL.Ctx AtomicTy} {type : HOL.Ty AtomicTy}
      (term : HOL.Term Symbol context type), readable term = true →
        Translates context (reverseTermOpen term) type term
  | _, _, .var index, _ => .bound index
  | _, _, .const (.variable _ typed), _ => .free typed
  | _, _, .const (.constant _ _ typed), accepted => .constant (constant_unrecognized accepted) typed
  | _, _, .app function argument, accepted =>
      .app (equality_head_none function (and_accepted accepted).1)
        (readable_translates function (and_accepted accepted).1)
        (readable_translates argument (and_accepted accepted).2)
  | _, _, .lam (σ := domain) body, accepted => by
      rw [reverseTermOpen_lam]
      exact .abs (toHOL_reverseTy domain) (readable_translates body accepted)
  | _, _, .eq (τ := type) left right, accepted =>
      .equalityApp (equalityOperand?_equality (reverseTy type)) (toHOL_reverseTy type)
        (readable_translates left (and_accepted accepted).1)
        (readable_translates right (and_accepted accepted).2)
  | _, _, .top, accepted => by cases accepted
  | _, _, .bot, accepted => by cases accepted
  | _, _, .and _ _, accepted => by cases accepted
  | _, _, .or _ _, accepted => by cases accepted
  | _, _, .imp _ _, accepted => by cases accepted
  | _, _, .not _, accepted => by cases accepted
  | _, _, .all _, accepted => by cases accepted
  | _, _, .ex _, accepted => by cases accepted

def matchesB (fact : Theorem) (formula : HOL.ClosedFormula Symbol) : Bool :=
  readable formula && DBTerm.same fact.sequent.concl.term (reverseTermOpen formula) &&
    (fact.sequent.hyp.card == 0)

theorem matches_sound {fact : Theorem} {formula : HOL.ClosedFormula Symbol}
    (accepted : matchesB fact formula = true) :
    fact.sequent.hyp = ∅ ∧ Translates [] fact.sequent.concl.term .prop formula := by
  simp only [matchesB, Bool.and_eq_true, beq_iff_eq, Finset.card_eq_zero] at accepted
  refine ⟨accepted.2,?_⟩
  rw [(DBTerm.same_eq_true_iff _ _).mp accepted.1.2]
  exact readable_translates formula accepted.1.1

structure ReadFact (state : Registered.State) (formula : HOL.ClosedFormula Symbol) where
  fact : Theorem
  known : fact ∈ state.cache
  closed : fact.sequent.hyp = ∅
  translated : Translates [] fact.sequent.concl.term .prop formula

def read? (state : Registered.State) (index : Nat) (formula : HOL.ClosedFormula Symbol) :
    Option (ReadFact state formula) :=
  match present : state.cache[index]? with
  | none => none
  | some fact =>
      if accepted : matchesB fact formula = true then
        some ⟨fact,Array.mem_of_getElem? present,(matches_sound accepted).1,(matches_sound accepted).2⟩
      else none

/-- Reading an existing cache entry retains its original hypotheses and
translation; no new theorem is minted by this operation. -/
theorem read_models {initial : DefinitionAdapters.TheoryContext} {policy : AxiomPolicy}
    {state : Registered.State}
    (frame : RegisteredReplayModels.Frame.{w} initial policy state.context state.cache)
    (other : TypeFamilySemantics.OperatorFamilies.{w}) (assignment : TypeFamilySemantics.Assignment.{w})
    (formula : HOL.ClosedFormula Symbol) (read : ReadFact state formula) :
    (frame.model other assignment).models formula := by
  apply frame.cached_models_of_translation other assignment read.known read.translated
  intro hypothesis member
  simp [read.closed,translatedHypotheses] at member

/-! ## Logical bodies lowered by the source exporter -/

/-- Logical constructors may be lowered by reverse translation. Ordinary
symbols remain literal; an uninterpreted primitive-equality symbol is refused. -/
def symbolsReadable : {context : HOL.Ctx AtomicTy} → {type : HOL.Ty AtomicTy} →
    HOL.Term Symbol context type → Bool
  | _, _, .var _ => true
  | _, _, .const (.variable ..) => true
  | _, _, .const (.constant constant annotation _) => (equalityOperand? constant annotation).isNone
  | _, _, .app function argument => symbolsReadable function && symbolsReadable argument
  | _, _, .lam body => symbolsReadable body
  | _, _, .top | _, _, .bot => true
  | _, _, .and left right | _, _, .or left right | _, _, .imp left right | _, _, .eq left right =>
      symbolsReadable left && symbolsReadable right
  | _, _, .not body | _, _, .all body | _, _, .ex body => symbolsReadable body

theorem symbolsReadable_free : ∀ {context : HOL.Ctx AtomicTy} {type : HOL.Ty AtomicTy}
    (term : HOL.Term Symbol context type), symbolsReadable term = true → EqualitySymbolFree term
  | _, _, .var _, _ => fun _ => .var
  | _, _, .const (.variable sourceVar typed), _ => fun operand =>
      Symbol.noConstOccurrence_const _ _ (sigma_variable_ne_equalitySymbol sourceVar typed operand)
  | _, _, .const (.constant constant annotation typed), accepted => by
      intro operand
      apply Symbol.noConstOccurrence_const _ _
      intro same
      have raw := congrArg (fun entry : Sigma Symbol => reverseSymbol entry.2) same
      obtain ⟨constantSame, annotationSame⟩ := DBTerm.const.inj raw
      subst constant
      subst annotation
      simp [symbolsReadable, equalityOperand?_equality] at accepted
  | _, _, .app function argument, accepted => fun operand =>
      .app (symbolsReadable_free function (and_accepted accepted).1 operand)
        (symbolsReadable_free argument (and_accepted accepted).2 operand)
  | _, _, .lam body, accepted => fun operand => .lam (symbolsReadable_free body accepted operand)
  | _, _, .top, _ => fun _ => .top
  | _, _, .bot, _ => fun _ => .bot
  | _, _, .and left right, accepted => fun operand =>
      .and (symbolsReadable_free left (and_accepted accepted).1 operand)
        (symbolsReadable_free right (and_accepted accepted).2 operand)
  | _, _, .or left right, accepted => fun operand =>
      .or (symbolsReadable_free left (and_accepted accepted).1 operand)
        (symbolsReadable_free right (and_accepted accepted).2 operand)
  | _, _, .imp left right, accepted => fun operand =>
      .imp (symbolsReadable_free left (and_accepted accepted).1 operand)
        (symbolsReadable_free right (and_accepted accepted).2 operand)
  | _, _, .not body, accepted => fun operand => .not (symbolsReadable_free body accepted operand)
  | _, _, .eq left right, accepted => fun operand =>
      .eq (symbolsReadable_free left (and_accepted accepted).1 operand)
        (symbolsReadable_free right (and_accepted accepted).2 operand)
  | _, _, .all body, accepted => fun operand => .all (symbolsReadable_free body accepted operand)
  | _, _, .ex body, accepted => fun operand => .ex (symbolsReadable_free body accepted operand)

def meaningMatchesB (fact : Theorem) (formula : HOL.ClosedFormula Symbol) : Bool :=
  symbolsReadable formula && DBTerm.same fact.sequent.concl.term (reverseTermOpen formula) &&
    (fact.sequent.hyp.card == 0)

/-- The intermediate source reading and its proof to the requested logical
formula are derived from structural comparison and the proved round trip. -/
theorem meaningMatches_sound {fact : Theorem} {formula : HOL.ClosedFormula Symbol}
    (accepted : meaningMatchesB fact formula = true) :
    fact.sequent.hyp = ∅ ∧ ∃ actual : HOL.ClosedFormula Symbol,
      Translates [] fact.sequent.concl.term .prop actual ∧ HOL.ExtDerivation Symbol [actual] formula := by
  simp only [meaningMatchesB, Bool.and_eq_true, beq_iff_eq, Finset.card_eq_zero] at accepted
  obtain ⟨actual, translated, proof, _⟩ := exists_translates_reverseTermOpen_derivable formula
    (symbolsReadable_free formula accepted.1.1)
  exact ⟨accepted.2, actual, (DBTerm.same_eq_true_iff _ _).mp accepted.1.2 ▸ translated, proof⟩

structure ReadMeaning (state : Registered.State) (formula : HOL.ClosedFormula Symbol) where
  fact : Theorem
  known : fact ∈ state.cache
  closed : fact.sequent.hyp = ∅
  interpretation : ∃ actual : HOL.ClosedFormula Symbol,
    Translates [] fact.sequent.concl.term .prop actual ∧ HOL.ExtDerivation Symbol [actual] formula

def readMeaning? (state : Registered.State) (index : Nat) (formula : HOL.ClosedFormula Symbol) :
    Option (ReadMeaning state formula) :=
  match present : state.cache[index]? with
  | none => none
  | some fact =>
      if accepted : meaningMatchesB fact formula = true then
        some ⟨fact, Array.mem_of_getElem? present, (meaningMatches_sound accepted).1, (meaningMatches_sound accepted).2⟩
      else none

theorem readMeaning_models {initial : DefinitionAdapters.TheoryContext} {policy : AxiomPolicy}
    {state : Registered.State}
    (frame : RegisteredReplayModels.Frame.{w} initial policy state.context state.cache)
    (other : TypeFamilySemantics.OperatorFamilies.{w}) (assignment : TypeFamilySemantics.Assignment.{w})
    (formula : HOL.ClosedFormula Symbol) (read : ReadMeaning state formula) :
    (frame.model other assignment).models formula := by
  obtain ⟨actual, translated, derives⟩ := read.interpretation
  have input : (frame.model other assignment).models actual := by
    apply frame.cached_models_of_translation other assignment read.known translated
    intro hypothesis member
    simp [read.closed, translatedHypotheses] at member
  have implication := HOL.Soundness.extTheorem_sound (HOL.ExtDerivation.impI derives)
    (frame.model other assignment)
    (HOL.HenkinModel.functionsRespectEqv_of_fullDomains _ (frame.model_fullDomains other assignment))
  exact implication input

/-- Read the actual equation emitted for a generated typed body. Logical
expansion is an explicit part of that exporter, and its denotation is proved. -/
def readEquation? {type : HOL.Ty AtomicTy} (state : Registered.State) (index : Nat)
    (installed body : HOL.ClosedTerm Symbol type) :
    Option (ReadMeaning state (.eq installed (HOL.ImpredicativeConnectives.expand body))) :=
  readMeaning? state index (.eq installed (HOL.ImpredicativeConnectives.expand body))

theorem readEquation_denote {initial : DefinitionAdapters.TheoryContext} {policy : AxiomPolicy}
    {state : Registered.State}
    (frame : RegisteredReplayModels.Frame.{w} initial policy state.context state.cache)
    (other : TypeFamilySemantics.OperatorFamilies.{w}) (assignment : TypeFamilySemantics.Assignment.{w})
    {type : HOL.Ty AtomicTy} (installed body : HOL.ClosedTerm Symbol type)
    (read : ReadMeaning state (.eq installed (HOL.ImpredicativeConnectives.expand body))) :
    (frame.model other assignment).denote installed (fun index => nomatch index) =
      (frame.model other assignment).denote body (fun index => nomatch index) := by
  let values : (frame.model other assignment).Valuation [] := fun index => nomatch index
  change (frame.model other assignment).denote installed values = (frame.model other assignment).denote body values
  have atValues : (frame.model other assignment).models (.eq installed (HOL.ImpredicativeConnectives.expand body)) ↔
      ((frame.model other assignment).denote (.eq installed (HOL.ImpredicativeConnectives.expand body)) values).down := by
    unfold HOL.HenkinModel.models HOL.PreModel.models
    exact Iff.of_eq (congrArg ULift.down ((frame.model other assignment).denote_closed_valuation_eq _ _ _))
  have meaning := atValues.mp (readMeaning_models frame other assignment _ read)
  have equal := ((frame.model other assignment).eqv_iff_eq_of_fullDomains
    (frame.model_fullDomains other assignment) _ _).mp meaning
  exact equal.trans (HOL.ImpredicativeConnectives.denote_expand _ body values)

#print axioms readable_translates
#print axioms matches_sound
#print axioms read_models
#print axioms symbolsReadable_free
#print axioms meaningMatches_sound
#print axioms readMeaning_models
#print axioms readEquation_denote

end Mettapedia.Languages.HOLLight.ExactFormulaReadback

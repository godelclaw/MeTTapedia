import Mettapedia.TypeTheory.RetractionDependentDescent
import Mettapedia.OSLF.Framework.RhoGeneratedScopeSubstitution

/-!
# Dependent access through an actual rho quotation

Complete dependent consumers of processes descend to quoted names exactly
when they agree on the actual quotation fibres. The name eta equation
supplies the reconstruction; no process beta equation is assumed.

Native predicates have the same precise boundary. Their quotation image
admits an origin satisfying the predicate and retains that origin in its
receipt. Reflecting a particular supplied origin additionally requires
compatibility with all processes quoting to the same name.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.RhoQuotationDependentAccess

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open BindingSubstitutionAlgebra BindingConstructorPredicates FreeBindingTerms
open RhoGeneratedScopeSubstitution

open Mettapedia.TypeTheory

universe u

variable {context : Ctx sig}

abbrev Compatible (family : Name context → Type u)
    (consumer : (process : Process context) → family (quote process)) : Prop :=
  RetractionDependentDescent.Compatible quote family consumer

def descend (family : Name context → Type u)
    (consumer : (process : Process context) → family (quote process)) :
    (name : Name context) → family name :=
  RetractionDependentDescent.descend quote drop quote_drop family consumer

theorem descend_beta (family : Name context → Type u)
    (consumer : (process : Process context) → family (quote process))
    (compatible : Compatible family consumer) (process : Process context) :
    descend family consumer (quote process) = consumer process :=
  RetractionDependentDescent.descend_beta quote drop quote_drop family consumer compatible process

def sectionsEquiv (family : Name context → Type u) :
    {consumer : ((process : Process context) → family (quote process)) //
      Compatible family consumer} ≃ ((name : Name context) → family name) :=
  RetractionDependentDescent.sectionsEquiv quote drop quote_drop family

theorem unique_descent (family : Name context → Type u)
    (consumer : (process : Process context) → family (quote process))
    (nameConsumer : (name : Name context) → family name)
    (agrees : (fun process => nameConsumer (quote process)) = consumer) :
    nameConsumer = descend family consumer :=
  RetractionDependentDescent.unique_descent quote drop quote_drop family consumer nameConsumer agrees

theorem descent_exists_iff (family : Name context → Type u)
    (consumer : (process : Process context) → family (quote process)) :
    (∃ nameConsumer : (name : Name context) → family name,
      (fun process => nameConsumer (quote process)) = consumer) ↔
        Compatible family consumer :=
  RetractionDependentDescent.descent_exists_iff quote drop quote_drop family consumer

/-- A native dependent action descends through quotation using the actual
substitution map on both sorts. Chosen process origins need not coincide. -/
theorem descend_substitution {source target : Ctx sig}
    (env : Environment sig (TermQ rhoSourceE) source target)
    (family : Name source → Type u) (nextFamily : Name target → Type u)
    (action : (name : Name source) → family name →
      nextFamily (model.substitution.substitute env name))
    (consumer : (process : Process source) → family (quote process))
    (nextConsumer : (process : Process target) → nextFamily (quote process))
    (nextCompatible : Compatible nextFamily nextConsumer)
    (consumer_natural : ∀ process,
      HEq (action (quote process) (consumer process))
        (nextConsumer (model.substitution.substitute env process))) (name : Name source) :
    HEq (action name (descend family consumer name))
      (descend nextFamily nextConsumer (model.substitution.substitute env name)) :=
  RetractionDependentDescent.descend_commutes quote drop quote_drop family
    quote drop quote_drop nextFamily (model.substitution.substitute env)
    (model.substitution.substitute env) (fun process => (substitute_quote env process).symm)
    action consumer nextConsumer nextCompatible consumer_natural name

def quoteInputs (predicate : Predicate model Srt.pr) :
    Arguments model (sig.arity Op.quo) := .cons predicate .nil

def quoted (predicate : Predicate model Srt.pr) : Predicate model Srt.nm :=
  image model Op.quo (quoteInputs predicate)

abbrev QuotationReceipt (predicate : Predicate model Srt.pr)
    (name : Name context) := Receipt model Op.quo (quoteInputs predicate) name

def QuotationReceipt.origin {predicate : Predicate model Srt.pr}
    {name : Name context} (receipt : QuotationReceipt predicate name) : Process context :=
  match receipt.arguments with
  | .cons process .nil => process

theorem QuotationReceipt.origin_admitted {predicate : Predicate model Srt.pr}
    {name : Name context} (receipt : QuotationReceipt predicate name) :
    predicate.holds (QuotationReceipt.origin receipt) :=
  match receipt with
  | ⟨.cons _ .nil, admitted, _⟩ => admitted.1

theorem QuotationReceipt.origin_quotes {predicate : Predicate model Srt.pr}
    {name : Name context} (receipt : QuotationReceipt predicate name) :
    quote (QuotationReceipt.origin receipt) = name :=
  match receipt with
  | ⟨.cons process .nil, _, output⟩ => (quote_operation process).trans output

def receiptOf (predicate : Predicate model Srt.pr) (process : Process context)
    (admitted : predicate.holds process) : QuotationReceipt predicate (quote process) where
  arguments := .cons process .nil
  admitted := ⟨admitted, by trivial⟩
  output := (quote_operation process).symm

theorem quoted_iff (predicate : Predicate model Srt.pr) (name : Name context) :
    (quoted predicate).holds name ↔
      ∃ process : Process context, predicate.holds process ∧ quote process = name := by
  constructor
  · rintro ⟨receipt⟩
    exact ⟨(QuotationReceipt.origin receipt), QuotationReceipt.origin_admitted receipt, QuotationReceipt.origin_quotes receipt⟩
  · rintro ⟨process, admitted, rfl⟩
    exact ⟨receiptOf predicate process admitted⟩

theorem QuotationReceipt.substitute_origin {source target : Ctx sig}
    {predicate : Predicate model Srt.pr} {name : Name source}
    (env : Environment sig (TermQ rhoSourceE) source target)
    (receipt : QuotationReceipt predicate name) :
    QuotationReceipt.origin (receipt.substitute env) =
      model.substitution.substitute env (QuotationReceipt.origin receipt) :=
  match receipt with
  | ⟨.cons _ .nil, _, _⟩ => rfl

def PredicateCompatible (predicate : Predicate model Srt.pr) : Prop :=
  ∀ {context : Ctx sig} (first second : Process context),
    quote first = quote second → (predicate.holds first ↔ predicate.holds second)

def namePredicate (predicate : Predicate model Srt.pr) : Predicate model Srt.nm where
  holds := fun name => predicate.holds (drop name)
  substitute := by
    intro source target env name admitted
    rw [← substitute_drop]
    exact predicate.substitute env (drop name) admitted

theorem quoted_reflects_origin_iff (predicate : Predicate model Srt.pr) :
    (∀ {context : Ctx sig} (process : Process context),
      (quoted predicate).holds (quote process) ↔ predicate.holds process) ↔
        PredicateCompatible predicate := by
  constructor
  · intro reflects context first second same
    rw [← reflects first, ← reflects second, same]
  · intro compatible context process
    constructor
    · intro member
      obtain ⟨origin, admitted, same⟩ := (quoted_iff predicate _).mp member
      exact (compatible origin process same).mp admitted
    · intro admitted
      exact ⟨receiptOf predicate process admitted⟩

theorem namePredicate_readout (predicate : Predicate model Srt.pr)
    (compatible : PredicateCompatible predicate) (process : Process context) :
    (namePredicate predicate).holds (quote process) ↔ predicate.holds process :=
  compatible (drop (quote process)) process (quote_drop _)

theorem quoted_eq_namePredicate (predicate : Predicate model Srt.pr)
    (compatible : PredicateCompatible predicate) (name : Name context) :
    (quoted predicate).holds name ↔ (namePredicate predicate).holds name := by
  rw [← quote_drop name]
  exact ((quoted_reflects_origin_iff predicate).mpr compatible _).trans
    (namePredicate_readout predicate compatible _).symm

end Mettapedia.OSLF.Framework.RhoQuotationDependentAccess

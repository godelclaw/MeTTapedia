import Mettapedia.Logic.HOL.BetaNormalization
import Mettapedia.Languages.MM0.HOLKernelLogicalOperations
import Mettapedia.Languages.MM0.HOLKernelTermReadbackCoherence

/-!
# Curried logical functions in the maintained native HOL profile

The checked operation profile identifies the seven native function constants
and the stored constructor definitions relating their applications to the
primitive Boolean forms. Their intrinsic readings are ordinary typed HOL
lambdas. Primitive constructors retain their existing reading; the two
presentations agree through explicit beta-conversion evidence.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelLogicalFunctionReadback
open Mettapedia.Logic.HOL
open Kernel HOLKernelSyntax HOLKernelTermReadback HOLKernelLogicalOperations
universe u
variable {Const : Ty Unit → Type u} {gamma : Ctx Unit}

def value (operator : Operator) (domain : Ty Unit) : Decoded Const gamma :=
  match operator with
  | .equality => ⟨domain ⇒ domain ⇒ .prop,
      .lam (.lam (.eq (.var (.vs .vz)) (.var .vz)))⟩
  | .conjunction => ⟨.prop ⇒ .prop ⇒ .prop,
      .lam (.lam (.and (.var (.vs .vz)) (.var .vz)))⟩
  | .disjunction => ⟨.prop ⇒ .prop ⇒ .prop,
      .lam (.lam (.or (.var (.vs .vz)) (.var .vz)))⟩
  | .implication => ⟨.prop ⇒ .prop ⇒ .prop,
      .lam (.lam (.imp (.var (.vs .vz)) (.var .vz)))⟩
  | .negation => ⟨.prop ⇒ .prop, .lam (.not (.var .vz))⟩
  | .universal => ⟨(domain ⇒ .prop) ⇒ .prop,
      .lam (.all (.app (.var (.vs .vz)) (.var .vz)))⟩
  | .existential => ⟨(domain ⇒ .prop) ⇒ .prop,
      .lam (.ex (.app (.var (.vs .vz)) (.var .vz)))⟩

variable {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
variable {theorems : TheoremSignature} {signature : Signature sorts terms}

def atoms (profile : Profile sorts terms definitions theorems signature) :
    {gamma : Ctx Unit} → Preterm → Option (Decoded Const gamma)
  | _, .term index =>
      if index = profile.reference .conjunction then some (value .conjunction .prop)
      else if index = profile.reference .disjunction then some (value .disjunction .prop)
      else if index = profile.reference .implication then some (value .implication .prop)
      else if index = profile.reference .negation then some (value .negation .prop)
      else none
  | _, .app (.term index) typeCode =>
      match readType signature.symbol typeCode with
      | none => none
      | some domain =>
          if index = profile.reference .equality then some (value .equality domain)
          else if index = profile.reference .universal then some (value .universal domain)
          else if index = profile.reference .existential then some (value .existential domain)
          else none
  | _, _ => none

def reader (profile : Profile sorts terms definitions theorems signature)
    (constants : Nat → Option (NamedElaboration.SomeConst Const)) (parameters : Nat) : TermReader Const :=
  readTermWith (atoms profile) signature.symbol constants parameters


theorem reader_encode (profile : Profile sorts terms definitions theorems signature)
    (constants : Nat → Option (NamedElaboration.SomeConst Const))
    (indices : ∀ {type}, Const type → Nat) (parameters : Nat)
    (lookup : ∀ {type} (constant : Const type), constants (indices constant) = some ⟨type, constant⟩)
    (bounded : ∀ {type} (constant : Const type), indices constant < parameters)
    {type : Ty Unit} (source : Term Const gamma type)
    (names : Names gamma) (depth : Nat) (scope : InScope parameters names depth) :
    reader profile constants parameters names
      (encodeTerm signature.symbol (fun _ : Unit => Preterm.var 0)
        (fun {_} symbol => Preterm.var (indices symbol)) (fun value => parameters + value)
        names.nameOf depth source) = some ⟨type, source⟩ :=
  readTermWith_encode (atoms profile) signature.symbol signature.symbol_injective constants indices parameters
    lookup bounded source names depth scope

theorem readHead_operator (profile : Profile sorts terms definitions theorems signature) (operator : Operator) :
    readHead signature.symbol (profile.reference operator) = none := by
  cases found : readHead signature.symbol (profile.reference operator) with
  | none => rfl
  | some constructor =>
      exact False.elim (profile.reference_ne_symbol operator constructor
        (readHead_sound signature.symbol _ _ found).symm)

theorem reader_nullary (profile : Profile sorts terms definitions theorems signature)
    (constants : Nat → Option (NamedElaboration.SomeConst Const)) (parameters : Nat)
    (names : Names gamma) (operator : Operator)
    (nullary : operator ∈ [.conjunction, .disjunction, .implication, .negation]) :
    reader profile constants parameters names (.term (profile.reference operator)) = some (value operator .prop) := by
  cases operator <;> simp_all [reader, readTermWith, readHead_operator, atoms, profile.reference_injective.eq_iff]

theorem reader_parameterized (profile : Profile sorts terms definitions theorems signature)
    (constants : Nat → Option (NamedElaboration.SomeConst Const)) (parameters : Nat)
    (names : Names gamma) (operator : Operator)
    (parameterized : operator ∈ [.equality, .universal, .existential])
    (typeCode : Preterm) (domain : Ty Unit) (typeRead : readType signature.symbol typeCode = some domain) :
    reader profile constants parameters names (.app (.term (profile.reference operator)) typeCode) =
      some (value operator domain) := by
  cases operator <;> simp_all [reader, readTermWith, readHead_operator, atoms, profile.reference_injective.eq_iff]

open ContextualTrinity BetaNormalization

theorem conjunction_reduces (first second : Formula Const gamma) :
    ReducesStar (.app (.app (value .conjunction .prop).term first) second) (.and first second) := by
  have firstStep : BetaStep (.app (.app (value .conjunction .prop).term first) second)
      (.app (.lam (.and (weaken first) (.var .vz))) second) := by
    simpa [value, instantiate, subst, Subst.lift, Subst.single, weaken] using
      (BetaStep.appFun second (BetaStep.beta (.lam (.and (.var (.vs .vz)) (.var .vz))) first))
  have secondStep : BetaStep (.app (.lam (.and (weaken first) (.var .vz))) second) (.and first second) := by
    have step := BetaStep.beta (.and (weaken first) (.var .vz)) second
    change BetaStep _ (.and (instantiate second (weaken first)) second) at step
    simpa only [instantiate_weaken] using step
  exact .head ⟨firstStep⟩ (.single ⟨secondStep⟩)

theorem disjunction_reduces (first second : Formula Const gamma) :
    ReducesStar (.app (.app (value .disjunction .prop).term first) second) (.or first second) := by
  have firstStep : BetaStep (.app (.app (value .disjunction .prop).term first) second)
      (.app (.lam (.or (weaken first) (.var .vz))) second) := by
    simpa [value, instantiate, subst, Subst.lift, Subst.single, weaken] using
      (BetaStep.appFun second (BetaStep.beta (.lam (.or (.var (.vs .vz)) (.var .vz))) first))
  have secondStep : BetaStep (.app (.lam (.or (weaken first) (.var .vz))) second) (.or first second) := by
    have step := BetaStep.beta (.or (weaken first) (.var .vz)) second
    change BetaStep _ (.or (instantiate second (weaken first)) second) at step
    simpa only [instantiate_weaken] using step
  exact .head ⟨firstStep⟩ (.single ⟨secondStep⟩)

theorem implication_reduces (first second : Formula Const gamma) :
    ReducesStar (.app (.app (value .implication .prop).term first) second) (.imp first second) := by
  have firstStep : BetaStep (.app (.app (value .implication .prop).term first) second)
      (.app (.lam (.imp (weaken first) (.var .vz))) second) := by
    simpa [value, instantiate, subst, Subst.lift, Subst.single, weaken] using
      (BetaStep.appFun second (BetaStep.beta (.lam (.imp (.var (.vs .vz)) (.var .vz))) first))
  have secondStep : BetaStep (.app (.lam (.imp (weaken first) (.var .vz))) second) (.imp first second) := by
    have step := BetaStep.beta (.imp (weaken first) (.var .vz)) second
    change BetaStep _ (.imp (instantiate second (weaken first)) second) at step
    simpa only [instantiate_weaken] using step
  exact .head ⟨firstStep⟩ (.single ⟨secondStep⟩)

theorem equality_reduces {domain : Ty Unit} (first second : Term Const gamma domain) :
    ReducesStar (.app (.app (value .equality domain).term first) second) (.eq first second) := by
  have firstStep : BetaStep (.app (.app (value .equality domain).term first) second)
      (.app (.lam (.eq (weaken first) (.var .vz))) second) := by
    simpa [value, instantiate, subst, Subst.lift, Subst.single, weaken] using
      (BetaStep.appFun second (BetaStep.beta (.lam (.eq (.var (.vs .vz)) (.var .vz))) first))
  have secondStep : BetaStep (.app (.lam (.eq (weaken first) (.var .vz))) second) (.eq first second) := by
    have step := BetaStep.beta (.eq (weaken first) (.var .vz)) second
    change BetaStep _ (.eq (instantiate second (weaken first)) second) at step
    simpa only [instantiate_weaken] using step
  exact .head ⟨firstStep⟩ (.single ⟨secondStep⟩)

theorem negation_reduces (body : Formula Const gamma) :
    ReducesStar (.app (value .negation .prop).term body) (.not body) := by
  have step : BetaStep (.app (value .negation .prop).term body) (.not body) := by
    simpa [value, instantiate, subst, Subst.single] using
      (BetaStep.beta (.not (.var .vz)) body)
  exact .single ⟨step⟩

theorem universal_reduces {domain : Ty Unit} (body : Formula Const (domain :: gamma)) :
    ReducesStar (.app (value .universal domain).term (.lam body)) (.all body) := by
  have firstStep : BetaStep (.app (value .universal domain).term (.lam body))
      (.all (.app (weaken (.lam body)) (.var .vz))) := by
    simpa [value, instantiate, subst, Subst.lift, Subst.single, weaken] using
      (BetaStep.beta (.all (.app (.var (.vs .vz)) (.var .vz))) (.lam body))
  have bodyStep : BetaStep (.app (weaken (.lam body)) (.var .vz)) body := by
    simpa only [weaken, rename, instantiate_vz_rename_lift_weaken] using
      (BetaStep.beta (rename (Rename.lift Rename.weaken) body) (.var .vz))
  exact .head ⟨firstStep⟩ (.single ⟨.all bodyStep⟩)

theorem existential_reduces {domain : Ty Unit} (body : Formula Const (domain :: gamma)) :
    ReducesStar (.app (value .existential domain).term (.lam body)) (.ex body) := by
  have firstStep : BetaStep (.app (value .existential domain).term (.lam body))
      (.ex (.app (weaken (.lam body)) (.var .vz))) := by
    simpa [value, instantiate, subst, Subst.lift, Subst.single, weaken] using
      (BetaStep.beta (.ex (.app (.var (.vs .vz)) (.var .vz))) (.lam body))
  have bodyStep : BetaStep (.app (weaken (.lam body)) (.var .vz)) body := by
    simpa only [weaken, rename, instantiate_vz_rename_lift_weaken] using
      (BetaStep.beta (rename (Rename.lift Rename.weaken) body) (.var .vz))
  exact .head ⟨firstStep⟩ (.single ⟨.ex bodyStep⟩)

#print axioms reader_nullary
#print axioms reader_parameterized
#print axioms universal_reduces
#print axioms reader
end Mettapedia.Languages.MM0.HOLKernelLogicalFunctionReadback

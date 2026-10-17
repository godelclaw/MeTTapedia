import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.SourceModel
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.BindingObservations
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSubstitutionReadout

/-!
# Open native expressions over the actual authored binding model

The language installation determines all structural operations and every
source-event projection. Contexts, types, terms, predicates and substitutions
use the common dependent interpreter. The ambient modal signature uses the
curried focus carrier; the existing raw local signature remains separate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.Interpretation

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.NativeTypes.Semantics Classifier
open CurriedBindingLanguage

variable (installed : Joined.Installed)

abbrev language := NativeCubeProfile.language installed.indexed.operational
abbrev worlds := Worlds (language installed)
abbrev symbols := SourceInjection.symbols installed.indexed
abbrev signature := SourceModel.signature installed
noncomputable abbrev model := SourceModel.model installed (BindingObservations.observations installed)

theorem realization : SignatureRealization (model installed) (signature installed) :=
  SourceModel.realization installed (BindingObservations.observations installed)

/-- Every independently derived judgment has an interpretation, including
context and substitution equations and predicate entailment. -/
theorem sound {judgment : Judgment (symbols installed)}
    (tree : Derivation (signature installed) judgment) : Interprets (model installed) judgment :=
  SourceModel.sound installed (BindingObservations.observations installed) tree

def check (certificate : Certificates.Refinement.Certificate (signature installed))
    (judgment : Judgment (symbols installed)) : NativeLogic.CheckResult :=
  SourceModel.check installed certificate judgment

/-- The executable checker accepts exactly the permitted independent
native derivations that erase to the supplied certificate. -/
theorem check_exact (certificate : Certificates.Refinement.Certificate (signature installed))
    (judgment : Judgment (symbols installed)) :
    check installed certificate judgment = .accepted ↔
      installed.indexed.operational.logic.permits judgment ∧
      NativeLogic.CertificatePermitted installed.indexed.operational.logic certificate ∧
      ∃ tree : Derivation (signature installed) judgment,
        Certificates.Refinement.erase tree = certificate :=
  NativeLogic.check_exact _ _ _

theorem check_sound (certificate : Certificates.Refinement.Certificate (signature installed))
    (judgment : Judgment (symbols installed))
    (accepted : check installed certificate judgment = .accepted) :
    Interprets (model installed) judgment :=
  SourceModel.check_sound installed (BindingObservations.observations installed) certificate judgment accepted

theorem type_substitution {n m : Nat} (type : TypeExpr (symbols installed) n)
    (source : Scope (worlds installed) m) (target : Scope (worlds installed) n)
    (mapping : Substitution (symbols installed) n m) (arrow : source.1 ⟶ target.1)
    (mappingRead : (model installed).evaluateSubstitution source target mapping = some arrow)
    (meaning : NativeLocalTypeFormers.NativeType target.1)
    (read : (model installed).evaluateType target type = some meaning) :
    (model installed).evaluateType source (type.substitute mapping) = some (meaning.reindex arrow) :=
  ModelData.evaluateType_substitute _ (NativeLocalTypeOperations.products_substitution _)
    type source target mapping (ModelSubstitution.ofEvaluated _ _ _ _ _ mappingRead) meaning read

theorem term_substitution {n m : Nat} (term : TermExpr (symbols installed) n)
    (source : Scope (worlds installed) m) (target : Scope (worlds installed) n)
    (mapping : Substitution (symbols installed) n m) (arrow : source.1 ⟶ target.1)
    (mappingRead : (model installed).evaluateSubstitution source target mapping = some arrow)
    (meaning : NativeValue target.1)
    (read : (model installed).evaluateTerm target term = some meaning) :
    (model installed).evaluateTerm source (term.substitute mapping) = some (meaning.substitute arrow) :=
  ModelData.evaluateTerm_substitute _ (NativeLocalTypeOperations.products_substitution _)
    term source target mapping (ModelSubstitution.ofEvaluated _ _ _ _ _ mappingRead) meaning read

theorem predicate_substitution {n m : Nat} (predicate : PropExpr (symbols installed) n)
    (source : Scope (worlds installed) m) (target : Scope (worlds installed) n)
    (mapping : Substitution (symbols installed) n m) (arrow : source.1 ⟶ target.1)
    (mappingRead : (model installed).evaluateSubstitution source target mapping = some arrow)
    (meaning : Subfunctor target.1)
    (read : (model installed).evaluatePredicate target predicate = some meaning) :
    (model installed).evaluatePredicate source (predicate.substitute mapping) =
      some (meaning.preimage arrow) :=
  ModelData.evaluatePredicate_substitute _ (NativeLocalTypeOperations.products_substitution _)
    predicate source target mapping (ModelSubstitution.ofEvaluated _ _ _ _ _ mappingRead) meaning read

theorem context_extension {n : Nat} (context : ContextExpr (symbols installed) n)
    (type : TypeExpr (symbols installed) n) (scope : Scope (worlds installed) n)
    (meaning : NativeLocalTypeFormers.NativeType scope.1)
    (contextRead : (model installed).evaluateContext context = some scope)
    (typeRead : (model installed).evaluateType scope type = some meaning) :
    (model installed).evaluateContext (.snoc context type) = some (scope.snoc meaning) :=
  (model installed).evaluateContext_snoc context type scope meaning contextRead typeRead

theorem context_assumption {n : Nat} (context : ContextExpr (symbols installed) n)
    (predicate : PropExpr (symbols installed) n) (scope : Scope (worlds installed) n)
    (meaning : Subfunctor scope.1)
    (contextRead : (model installed).evaluateContext context = some scope)
    (predicateRead : (model installed).evaluatePredicate scope predicate = some meaning) :
    (model installed).evaluateContext (.assume context predicate) = some (scope.assume meaning) :=
  (model installed).evaluateContext_assume context predicate scope meaning contextRead predicateRead

noncomputable abbrev requests (index : installed.Index) := ContinuationSemantics.requests
  (AuthoredClassifiers.operational installed.indexed) (AuthoredClassifiers.algebra installed.indexed)
  installed.indexed.classifierVertex (CurriedInterfaces.interface installed.indexed index)

/-- The exact full-family meaning of an authored indexed modal operation. -/
def NativeMeaning (index : installed.Index)
    (world : (worlds installed)ᵒᵖ)
    (focus : (AuthoredClassifiers.operational installed.indexed
      (CurriedInterfaces.interface installed.indexed index).focus).obj world)
    (parameters : (requests installed index).parameters.1.obj world) : Prop :=
  (focus, parameters) ∈ (ResponseSemantics.meaning (requests installed index)
    (BindingObservations.observations installed index)).obj world

/-- Source membership quantifies over every future request and retains a
complete selected source frame, its captures and its actual target. -/
theorem native_meaning_source (index : installed.Index) (world : (worlds installed)ᵒᵖ)
    (focus : (AuthoredClassifiers.operational installed.indexed
      (CurriedInterfaces.interface installed.indexed index).focus).obj world)
    (parameters : (requests installed index).parameters.1.obj world) :
    NativeMeaning installed index world focus parameters ↔
      ResponseSemantics.SourceMeaning (requests installed index)
        (BindingObservations.observations installed index) world focus parameters :=
  ResponseSemantics.meaning_exact _ _ _ _ _

/-- Operational context substitution preserves the actual native membership. -/
theorem native_meaning_restrict (index : installed.Index)
    {world future : (worlds installed)ᵒᵖ} (restriction : world ⟶ future)
    {focus : (AuthoredClassifiers.operational installed.indexed
      (CurriedInterfaces.interface installed.indexed index).focus).obj world}
    {parameters : (requests installed index).parameters.1.obj world}
    (member : NativeMeaning installed index world focus parameters) :
    NativeMeaning installed index future
      ((AuthoredClassifiers.operational installed.indexed
        (CurriedInterfaces.interface installed.indexed index).focus).map restriction focus)
      ((requests installed index).parameters.1.map restriction parameters) :=
  (ResponseSemantics.meaning (requests installed index) (BindingObservations.observations installed index)).map
    restriction member


/-- The generated primitive itself evaluates in the full source model. -/
theorem modal_evaluates (index : installed.Index) :
    (model installed).evaluateTerm (requests installed index).parameters
      (.primitive (installed.modalSymbol index) TermExpr.var) =
      some ⟨CertifiedProjection.certifiedAt (AuthoredClassifiers.operational installed.indexed)
        (CurriedInterfaces.interface installed.indexed index).focus
        (CurriedInterfaces.interface installed.indexed index).resultSort
        (requests installed index).parameters.1,
        ResponseSemantics.former (requests installed index) (BindingObservations.observations installed index)⟩ :=
  SourceModel.modal_evaluates installed (BindingObservations.observations installed) index

/-- Membership of the actual interpreted primitive, rather than only a
separately named predicate, has the independent all-future source meaning. -/
theorem modal_membership_source (index : installed.Index) (world : (worlds installed)ᵒᵖ)
    (focus : (AuthoredClassifiers.operational installed.indexed
      (CurriedInterfaces.interface installed.indexed index).focus).obj world)
    (parameters : (requests installed index).parameters.1.obj world) :
    Code.Member (.operational focus)
      (CertifiedProjection.certifiedAtEquiv (AuthoredClassifiers.operational installed.indexed)
        (CurriedInterfaces.interface installed.indexed index).focus
        (CurriedInterfaces.interface installed.indexed index).resultSort
        (requests installed index).parameters.1 ⟨world, parameters⟩
        (((model installed).termValue (installed.modalSymbol index)).val ⟨world, parameters⟩)).val ↔
      ResponseSemantics.SourceMeaning (requests installed index)
        (BindingObservations.observations installed index) world focus parameters :=
  ModalModel.modal_meaning (AuthoredClassifiers.operational installed.indexed)
    (AuthoredClassifiers.algebra installed.indexed) installed.indexed.classifierVertex
    (CurriedInterfaces.interface installed.indexed) (BindingObservations.observations installed)
    index world focus parameters

theorem substitution_identity {n : Nat} (scope : Scope (worlds installed) n) :
    (model installed).evaluateSubstitution scope scope TermExpr.var = some (𝟙 scope.1) :=
  (model installed).evaluateSubstitution_identity scope

theorem substitution_composition {n m k : Nat}
    (firstScope : Scope (worlds installed) n) (middleScope : Scope (worlds installed) m)
    (lastScope : Scope (worlds installed) k)
    (first : Substitution (symbols installed) m n) (second : Substitution (symbols installed) n k)
    (firstArrow : firstScope.1 ⟶ middleScope.1) (secondArrow : lastScope.1 ⟶ firstScope.1)
    (firstRead : (model installed).evaluateSubstitution firstScope middleScope first = some firstArrow)
    (secondRead : (model installed).evaluateSubstitution lastScope firstScope second = some secondArrow) :
    (model installed).evaluateSubstitution lastScope middleScope (composeSubstitution first second) =
      some (secondArrow ≫ firstArrow) :=
  (model installed).evaluateSubstitution_composition (NativeLocalTypeOperations.products_substitution _)
    firstScope middleScope lastScope first second firstArrow secondArrow firstRead secondRead

theorem type_renaming {n m : Nat} (type : TypeExpr (symbols installed) n)
    (source : Scope (worlds installed) m) (target : Scope (worlds installed) n)
    (mapping : Renaming n m) (represented : ModelRenaming source target mapping)
    (meaning : NativeLocalTypeFormers.NativeType target.1)
    (read : (model installed).evaluateType target type = some meaning) :
    (model installed).evaluateType source (type.rename mapping) = some (meaning.reindex represented.arrow) :=
  (model installed).evaluateType_rename (NativeLocalTypeOperations.products_substitution _)
    type source target mapping represented meaning read

theorem type_weakening {n : Nat} (type : TypeExpr (symbols installed) n)
    (scope : Scope (worlds installed) n) (extra meaning : NativeLocalTypeFormers.NativeType scope.1)
    (read : (model installed).evaluateType scope type = some meaning) :
    (model installed).evaluateType (scope.snoc extra) (type.rename Fin.succ) =
      some (meaning.reindex (DisplayedPresheafComprehension.totalProjection extra.decoded)) :=
  type_renaming installed type (scope.snoc extra) scope Fin.succ
    (ModelRenaming.weaken scope extra) meaning read

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.Interpretation

import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.ModalModel
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.AuthoredClassifiers
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.CurriedInterfaces
import Mettapedia.OSLF.NativeTypes.Modal.NativeBindingModalDiagram
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSignatureSumModel

/-!
# Original programs, contextual response classifiers and their explicit injection

The original binding constructor and event model remains on the left. Its
operational values inject naturally into the classifier carrier. Modal results
classify the ambient curried focus; local raw-focus declarations retain their
separate existing signature. Both use the same original native grammar.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.SourceModel

open _root_.CategoryTheory Opposite
open Mettapedia.OSLF.NativeTypes.Semantics
open Presheaf CubeEnrichment CubeNativeDeclarations Classifier
open Mettapedia.TypeTheory Calculi.NativeDependent.Refinement
open NativeLocalTypeFormers ContextualLocalUniverses ContextualModelTelescopes
open Mettapedia.OSLF.NativeTypes.Modal
open CurriedBindingLanguage

variable (installed : Joined.Installed)

noncomputable section

abbrev indexed := installed.indexed
abbrev operational := installed.indexed.operational
abbrev language := NativeCubeProfile.language (operational installed)
abbrev D := Pipeline.classifierSignature (operational installed)
abbrev interfaces := CurriedInterfaces.interface (indexed installed)

abbrev ready := (NativeOperationalProfile.check_exact _).mp installed.semantic.operationalMeaning

def sourceDiagram : CurriedNativeModalModel.Diagram
    (BindingPipeline.plan (operational installed).generated) (operational installed).modal :=
  NativeBindingModalDiagram.diagram installed.semantic.freeEmpty (ready installed)
    (operational installed).nativeMeaning_admitted (operational installed).distinctLabels
    (AuthoredBindingNativeModel.header_decoded (operational installed)) installed.semantic.modalMeanings

def source : ModelData (operational installed).symbols (Worlds (language installed)) :=
  CurriedNativeModalModel.model (operational installed).declarations
    (operational installed).nativeMeaning_admitted (sourceDiagram installed)

theorem source_realization : SignatureRealization (source installed) (operational installed).signature :=
  CurriedNativeModalModel.realization (operational installed).declarations
    (operational installed).nativeMeaning_admitted (sourceDiagram installed)

variable (observed : ∀ index : installed.Index, ResponseSemantics.Observations
  (AuthoredClassifiers.operational (indexed installed)) (interfaces installed index))

abbrev modal := ModalModel.model
  (AuthoredClassifiers.operational (indexed installed)) (AuthoredClassifiers.algebra (indexed installed))
  (indexed installed).classifierVertex (interfaces installed) observed

abbrev coreSignature := SignatureSum.signature (operational installed).signature
  (Declarations.signature (indexed installed).classifierVertex (interfaces installed))

abbrev core := SignatureSum.model (source installed) (modal installed observed)

theorem core_realization : SignatureRealization (core installed observed) (coreSignature installed) :=
  SignatureSum.realization (source installed) (modal installed observed)
    (operational installed).signature
    (Declarations.signature (indexed installed).classifierVertex (interfaces installed))
    (source_realization installed)
    (ModalModel.realization (AuthoredClassifiers.operational (indexed installed))
      (AuthoredClassifiers.algebra (indexed installed)) (indexed installed).classifierVertex
      (interfaces installed) observed)

/-- Only the classifier carrier of a modal result changes from local focus
to its earned ambient function carrier. All parameter and origin slots stay. -/
def signature : Signature (SourceInjection.symbols (indexed installed)) where
  typeRank := (SignatureSum.sumRanks (SignatureSum.ranks (coreSignature installed))
    (SourceInjection.extraRanks (indexed installed))).typeRank
  termRank := (SignatureSum.sumRanks (SignatureSum.ranks (coreSignature installed))
    (SourceInjection.extraRanks (indexed installed))).termRank
  predicateRank := (SignatureSum.sumRanks (SignatureSum.ranks (coreSignature installed))
    (SourceInjection.extraRanks (indexed installed))).predicateRank
  typeParameters symbol := match symbol with
    | .inl symbol => SignatureSum.contextLeft ((coreSignature installed).typeParameters symbol)
    | .inr impossible => nomatch impossible
  termParameters symbol := match symbol with
    | .inl symbol => SignatureSum.contextLeft ((coreSignature installed).termParameters symbol)
    | .inr carrier => SourceInjection.injectionContext (indexed installed) carrier
  predicateParameters symbol := match symbol with
    | .inl symbol => SignatureSum.contextLeft ((coreSignature installed).predicateParameters symbol)
    | .inr impossible => nomatch impossible
  termResult symbol := match symbol with
    | .inl symbol => SignatureSum.typeLeft ((coreSignature installed).termResult symbol)
    | .inr carrier => SourceInjection.codeType (indexed installed) carrier 1
  typeParameters_before := by
    intro symbol
    cases symbol with
    | inl symbol =>
        apply (SignatureSum.contextLeft_before _ _ _ _).mpr
        exact (coreSignature installed).typeParameters_before symbol
    | inr impossible => exact nomatch impossible
  termParameters_before := by
    intro symbol
    cases symbol with
    | inl symbol =>
        apply (SignatureSum.contextLeft_before _ _ _ _).mpr
        exact (coreSignature installed).termParameters_before symbol
    | inr carrier =>
        refine ⟨True.intro, ?_⟩
        apply (SignatureSum.typeLeft_before _ _ _ _).mpr
        apply (SignatureSum.typeLeft_signature_before (operational installed).signature
          (Declarations.signature (indexed installed).classifierVertex (interfaces installed)) _ _).mpr
        exact (((SourceInjection.carriers (indexed installed)).formed carrier).before_judgment
          ((SourceInjection.carriers (indexed installed)).before carrier)).2
  predicateParameters_before := by
    intro symbol
    cases symbol with
    | inl symbol =>
        apply (SignatureSum.contextLeft_before _ _ _ _).mpr
        exact (coreSignature installed).predicateParameters_before symbol
    | inr impossible => exact nomatch impossible
  termResult_before := by
    intro symbol
    cases symbol with
    | inl symbol =>
        apply (SignatureSum.typeLeft_before _ _ _ _).mpr
        exact (coreSignature installed).termResult_before symbol
    | inr carrier =>
        refine ⟨?_, fun position => Fin.elim0 position⟩
        change 0 < 4
        decide


/-- The change of focus carrier does not change any declaration rank. -/
theorem typeRank_preserved (symbol : (SourceInjection.symbols (indexed installed)).TypeSymbol) :
    (signature installed).typeRank symbol = (SourceInjection.signature (indexed installed)).typeRank symbol := by
  rcases symbol with ((source | (classifier | impossible)) | impossible)
  · rfl
  · rfl
  · cases impossible
  · cases impossible

theorem termRank_preserved (symbol : (SourceInjection.symbols (indexed installed)).TermSymbol) :
    (signature installed).termRank symbol = (SourceInjection.signature (indexed installed)).termRank symbol := by
  rcases symbol with ((source | (classifier | index)) | injection) <;> rfl

theorem predicateRank_preserved (symbol : (SourceInjection.symbols (indexed installed)).PredicateSymbol) :
    (signature installed).predicateRank symbol = (SourceInjection.signature (indexed installed)).predicateRank symbol := by
  rcases symbol with ((source | (classifier | impossible)) | impossible)
  · rfl
  · rfl
  · cases impossible
  · cases impossible

/-- All generated open parameter contexts, including the target continuation,
are exactly the existing contexts. The result classifier is compared separately. -/
theorem typeHeader_preserved (symbol : (SourceInjection.symbols (indexed installed)).TypeSymbol) :
    (signature installed).typeParameters symbol =
      (SourceInjection.signature (indexed installed)).typeParameters symbol := by
  rcases symbol with ((source | (classifier | impossible)) | impossible)
  · rfl
  · rfl
  · cases impossible
  · cases impossible

theorem termHeader_preserved (symbol : (SourceInjection.symbols (indexed installed)).TermSymbol) :
    (signature installed).termParameters symbol =
      (SourceInjection.signature (indexed installed)).termParameters symbol := by
  rcases symbol with ((source | (classifier | index)) | injection) <;> rfl

theorem predicateHeader_preserved (symbol : (SourceInjection.symbols (indexed installed)).PredicateSymbol) :
    (signature installed).predicateParameters symbol =
      (SourceInjection.signature (indexed installed)).predicateParameters symbol := by
  rcases symbol with ((source | (classifier | impossible)) | impossible)
  · rfl
  · rfl
  · cases impossible
  · cases impossible

theorem source_result_preserved (symbol : (operational installed).symbols.TermSymbol) :
    (signature installed).termResult (.inl (.inl symbol)) =
      (SourceInjection.signature (indexed installed)).termResult (.inl (.inl symbol)) := rfl

theorem classifier_result_preserved (symbol : (CubeNativeDeclarations.symbols (D installed)).TermSymbol) :
    (signature installed).termResult (.inl (.inr (.inl symbol))) =
      (SourceInjection.signature (indexed installed)).termResult (.inl (.inr (.inl symbol))) := rfl

theorem injection_result_preserved (carrier : (D installed).Carrier) :
    (signature installed).termResult (.inr carrier) =
      (SourceInjection.signature (indexed installed)).termResult (.inr carrier) := rfl

/-- An empty local binder prefix needs no currying, so this modal result also
coincides. No equality is asserted for a nonempty prefix. -/
theorem modal_result_empty_prefix (index : installed.Index)
    (empty : (CurriedInterfaces.header (indexed installed) index).focusBinders = []) :
    (signature installed).termResult (.inl (.inr (.inr index))) =
      (SourceInjection.signature (indexed installed)).termResult (.inl (.inr (.inr index))) := by
  have focus := congrArg Interface.focus
    (CurriedInterfaces.empty_prefix (indexed installed) index empty)
  change (SignatureSum.typeLeft (SignatureSum.typeRight (SignatureSum.typeLeft
    (certifiedCode (interfaces installed index).focus (interfaces installed index).resultSort
      (arity (D := D installed) (interfaces installed index))))) :
      TypeExpr (SourceInjection.symbols (indexed installed)) _) = _
  rw [focus]
  rfl

abbrev injectionScope (carrier : (D installed).Carrier) := carrierScope [carrier]

def sourceName (carrier : (D installed).Carrier) :
    (injectionScope installed carrier).1 ⟶ meaning carrier :=
  (carrierScopeProductIso [carrier]).hom ≫
    {app := fun _ => TypeCat.ofHom Prod.fst, naturality := by intros; rfl}

def injectionName (carrier : (D installed).Carrier) :
    (injectionScope installed carrier).1 ⟶
      Classifier.Carrier.presheaf (AuthoredClassifiers.operational (indexed installed)) carrier :=
  sourceName installed carrier ≫
    Classifier.Carrier.injection (AuthoredClassifiers.operational (indexed installed)) carrier

def injections : ModelData (SourceInjection.injectionSymbols (indexed installed)) (Worlds (language installed)) where
  typeParameters impossible := nomatch impossible
  typeFamily impossible := nomatch impossible
  termParameters := injectionScope installed
  termType carrier := Classifier.Families.codeAt (AuthoredClassifiers.operational (indexed installed)) carrier
    (injectionScope installed carrier).1
  termValue carrier := Classifier.Families.codeSection (AuthoredClassifiers.operational (indexed installed)) carrier
    (injectionName installed carrier)
  predicateParameters impossible := nomatch impossible
  predicateValue impossible := nomatch impossible

def model : ModelData (SourceInjection.symbols (indexed installed)) (Worlds (language installed)) :=
  SignatureSum.model (core installed observed) (injections installed)

theorem source_type_read {n : Nat} (scope : Scope (Worlds (language installed)) n)
    (expression : TypeExpr (operational installed).symbols n) :
    (model installed observed).evaluateType scope
      (SignatureSum.typeLeft (SignatureSum.typeLeft expression)) =
      (source installed).evaluateType scope expression := by
  exact (SignatureSum.evaluateType_left (core installed observed) (injections installed)
    (SignatureSum.typeLeft expression) scope).trans
    (SignatureSum.evaluateType_left (source installed) (modal installed observed) expression scope)

theorem source_term_read {n : Nat} (scope : Scope (Worlds (language installed)) n)
    (expression : TermExpr (operational installed).symbols n) :
    (model installed observed).evaluateTerm scope
      (SignatureSum.termLeft (SignatureSum.termLeft expression)) =
      (source installed).evaluateTerm scope expression := by
  exact (SignatureSum.evaluateTerm_left (core installed observed) (injections installed)
    (SignatureSum.termLeft expression) scope).trans
    (SignatureSum.evaluateTerm_left (source installed) (modal installed observed) expression scope)


theorem source_predicate_read {n : Nat} (scope : Scope (Worlds (language installed)) n)
    (expression : PropExpr (operational installed).symbols n) :
    (model installed observed).evaluatePredicate scope
      (SignatureSum.propLeft (SignatureSum.propLeft expression)) =
      (source installed).evaluatePredicate scope expression :=
  (SignatureSum.evaluatePredicate_left (core installed observed) (injections installed)
    (SignatureSum.propLeft expression) scope).trans
    (SignatureSum.evaluatePredicate_left (source installed) (modal installed observed) expression scope)

theorem source_context_read {n : Nat} (context : ContextExpr (operational installed).symbols n) :
    (model installed observed).evaluateContext
      (SignatureSum.contextLeft (SignatureSum.contextLeft context)) =
      (source installed).evaluateContext context :=
  (SignatureSum.evaluateContext_left (core installed observed) (injections installed)
    (SignatureSum.contextLeft context)).trans
    (SignatureSum.evaluateContext_left (source installed) (modal installed observed) context)

theorem classifier_type_read {n : Nat} (scope : Scope (Worlds (language installed)) n)
    (expression : TypeExpr (CubeNativeDeclarations.symbols (D installed)) n) :
    (model installed observed).evaluateType scope
      (SignatureSum.typeLeft (SignatureSum.typeRight (SignatureSum.typeLeft expression))) =
      (AuthoredClassifiers.model (indexed installed)).evaluateType scope expression := by
  refine (SignatureSum.evaluateType_left (core installed observed) (injections installed)
    (SignatureSum.typeRight (SignatureSum.typeLeft expression)) scope).trans ?_
  refine (SignatureSum.evaluateType_right (source installed) (modal installed observed)
    (SignatureSum.typeLeft expression) scope).trans ?_
  exact SignatureSum.evaluateType_left _ _ expression scope

theorem source_carrier_read {n : Nat} (scope : Scope (Worlds (language installed)) n)
    (carrier : (D installed).Carrier) :
    (model installed observed).evaluateType scope
      ((SourceInjection.sourceType (indexed installed) carrier).rename (Fin.elim0 : Renaming 0 n)) =
      some (carrierNativeType scope.1 carrier) := by
  rw [← SignatureSum.typeLeft_rename, ← SignatureSum.typeLeft_rename]
  change (model installed observed).evaluateType scope
    (SignatureSum.typeLeft (SignatureSum.typeLeft
      ((NativeModalSignature.authoredType (BindingPipeline.plan (operational installed).generated)
        (operational installed).declarations (operational installed).modal carrier 0).rename Fin.elim0))) = _
  rw [NativeModalSignature.authoredType_rename]
  exact (source_type_read installed observed scope _).trans
    (CurriedNativeModalModel.carrier_read (operational installed).declarations
      (operational installed).nativeMeaning_admitted (sourceDiagram installed) scope carrier)

theorem code_read {n : Nat} (scope : Scope (Worlds (language installed)) n) (carrier : (D installed).Carrier) :
    (model installed observed).evaluateType scope (SourceInjection.codeType (indexed installed) carrier n) =
      some (Classifier.Families.codeAt (AuthoredClassifiers.operational (indexed installed)) carrier scope.1) :=
  (classifier_type_read installed observed scope (CubeNativeDeclarations.codeType carrier n)).trans
    (Classifier.Realization.code_read (AuthoredClassifiers.operational (indexed installed))
      (AuthoredClassifiers.algebra (indexed installed)) (indexed installed).classifierVertex scope carrier)

theorem injection_context_read (carrier : (D installed).Carrier) :
    (model installed observed).evaluateContext (SourceInjection.injectionContext (indexed installed) carrier) =
      some (injectionScope installed carrier) := by
  apply (model installed observed).evaluateContext_snoc .nil
    (SourceInjection.sourceType (indexed installed) carrier) Families.emptyScope
    (carrierNativeType Families.emptyScope.1 carrier) rfl
  exact (source_type_read installed observed Families.emptyScope
    (NativeModalSignature.authoredType (BindingPipeline.plan (operational installed).generated)
      (operational installed).declarations (operational installed).modal carrier 0)).trans
    (CurriedNativeModalModel.carrier_read (operational installed).declarations
      (operational installed).nativeMeaning_admitted (sourceDiagram installed) Families.emptyScope carrier)

theorem realization : SignatureRealization (model installed observed) (signature installed) where
  typeHeader symbol := by
    cases symbol with
    | inl symbol =>
        exact (SignatureSum.evaluateContext_left (core installed observed) (injections installed) _).trans
          ((core_realization installed observed).typeHeader symbol)
    | inr impossible => exact nomatch impossible
  termHeader symbol := by
    cases symbol with
    | inl symbol =>
        exact (SignatureSum.evaluateContext_left (core installed observed) (injections installed) _).trans
          ((core_realization installed observed).termHeader symbol)
    | inr carrier => exact injection_context_read installed observed carrier
  predicateHeader symbol := by
    cases symbol with
    | inl symbol =>
        exact (SignatureSum.evaluateContext_left (core installed observed) (injections installed) _).trans
          ((core_realization installed observed).predicateHeader symbol)
    | inr impossible => exact nomatch impossible
  termResult symbol := by
    cases symbol with
    | inl symbol =>
        exact (SignatureSum.evaluateType_left (core installed observed) (injections installed) _ _).trans
          ((core_realization installed observed).termResult symbol)
    | inr carrier => exact code_read installed observed _ carrier


/-- The modal primitive of the full source language evaluates at its computed
open context to the actual response classifier and its kind evidence. -/
theorem modal_evaluates (index : installed.Index) :
    (model installed observed).evaluateTerm
      (ContinuationSemantics.parameterScope (AuthoredClassifiers.operational (indexed installed))
        (AuthoredClassifiers.algebra (indexed installed)) (indexed installed).classifierVertex
        (interfaces installed index))
      (.primitive (.inl (.inr (.inr index))) TermExpr.var) =
        some ⟨Classifier.CertifiedProjection.certifiedAt
          (AuthoredClassifiers.operational (indexed installed))
          (interfaces installed index).focus (interfaces installed index).resultSort
          (ContinuationSemantics.parameterScope (AuthoredClassifiers.operational (indexed installed))
            (AuthoredClassifiers.algebra (indexed installed)) (indexed installed).classifierVertex
            (interfaces installed index)).1,
          ResponseSemantics.former
            (ContinuationSemantics.requests (AuthoredClassifiers.operational (indexed installed))
              (AuthoredClassifiers.algebra (indexed installed)) (indexed installed).classifierVertex
              (interfaces installed index)) (observed index)⟩ := by
  let scope := ContinuationSemantics.parameterScope (AuthoredClassifiers.operational (indexed installed))
    (AuthoredClassifiers.algebra (indexed installed)) (indexed installed).classifierVertex
    (interfaces installed index)
  exact (SignatureSum.evaluateTerm_left (core installed observed) (injections installed)
    (SignatureSum.termRight (.primitive (.inr index) TermExpr.var)) scope).trans
    ((SignatureSum.evaluateTerm_right (source installed) (modal installed observed)
      (.primitive (.inr index) TermExpr.var) scope).trans
      (ModalModel.modal_evaluates (AuthoredClassifiers.operational (indexed installed))
        (AuthoredClassifiers.algebra (indexed installed)) (indexed installed).classifierVertex
        (interfaces installed) observed index))

theorem sound {judgment : Judgment (SourceInjection.symbols (indexed installed))}
    (tree : Derivation (signature installed) judgment) : Interprets (model installed observed) judgment :=
  tree.native_sound (model installed observed) (realization installed observed)

def check (certificate : Certificates.Refinement.Certificate (signature installed))
    (judgment : Judgment (SourceInjection.symbols (indexed installed))) : NativeLogic.CheckResult :=
  NativeLogic.check (operational installed).logic certificate judgment

theorem check_sound (certificate : Certificates.Refinement.Certificate (signature installed))
    (judgment : Judgment (SourceInjection.symbols (indexed installed)))
    (accepted : check installed certificate judgment = .accepted) :
    Interprets (model installed observed) judgment := by
  obtain ⟨_, _, derivation, _⟩ :=
    (NativeLogic.check_exact (operational installed).logic certificate judgment).mp accepted
  exact sound installed observed derivation

theorem injection_exact (carrier : (D installed).Carrier) (world : (Worlds (language installed))ᵒᵖ)
    (value : (injectionScope installed carrier).1.obj world) :
    (injectionName installed carrier).app world value =
      .operational ((sourceName installed carrier).app world value) := rfl

end
end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.SourceModel

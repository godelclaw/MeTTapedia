import Mettapedia.Languages.MeTTa.PrimeCandidates.StagedReflective.LanguageOperationSyntax

/-!
# The selected language routes and their compiled Data actions

Finite language-operation signatures already provide an independent candidate
grammar, a syntax-directed decoder, dependent typing, and free-path semantics.
This module identifies the strongest true reflection principle for that
grammar.

Raw syntax is not isomorphic to free paths: explicit identities and differently
parenthesized compositions give distinct terms with the same decoded program.
Instead, recognized terms are quotiented by equality of their recovered
endpoint-indexed path.  That quotient is exactly equivalent to decoded free
programs, and every interpretation insensitive to the choice of surface
spelling factors uniquely through it.

This is a selected-fragment initial-factorization theorem.  It does not claim
that every authored GSLT-IL relation is functional or that every future
language operation belongs to a finite signature.
-/

open Mettapedia.TypeTheory.Calculi.StagedScopedReflective
namespace Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageOperationFactorization

open _root_.CategoryTheory
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Syntax
open Mettapedia.GSLT.LanguageDef.FiniteLanguageOperationSignature
open Mettapedia.Languages.MeTTa.PrimeCandidates.StagedReflectiveInstances

universe u


/-! ## The represented operational and structural action -/

namespace CurrentExecution

open Mettapedia.Languages.MeTTa.PrimeCandidates.DataFibration
open Mettapedia.Languages.MeTTa.PrimeCandidates.DataFibration.FibreTranslation
open Mettapedia.Languages.MeTTa.PrimeCandidates.DataFibration.ValidatedLanguageData
open Mettapedia.Languages.MeTTa.PrimeCandidates.InternalDataTransport
open Mettapedia.Languages.MeTTa.Experimental.StagedReflective
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageOperationSyntax

/-- The two semantic readings and executable Data action determined by one
represented candidate route.  The source and target remain intrinsic indices. -/
structure CompiledAction where
  source : Language
  target : Language
  program : Program source target
  operationalRoute : operationStage source ⟶ operationStage target
  structuralRoute :
    currentLanguagePresentation source ⟶ currentLanguagePresentation target
  run : AllData (fibre (currentLanguagePresentation source)) →
    AllData (fibre (currentLanguagePresentation target))
  operational_eq : operationalRoute = gsltInterpretation.map program
  structural_eq : structuralRoute = structuralInterpretation.map program
  run_eq : run = runProgram program

/-- Interpret one decoded free program simultaneously in the operational
diagram, the structural language category, and the internal Data action. -/
def actionOfDecoded (decoded : currentOperationSignature.DecodedProgram) :
    CompiledAction :=
  { source := decoded.source
    target := decoded.target
    program := decoded.program
    operationalRoute := gsltInterpretation.map decoded.program
    structuralRoute := structuralInterpretation.map decoded.program
    run := runProgram decoded.program
    operational_eq := rfl
    structural_eq := rfl
    run_eq := rfl }

/-- A recognized authored spelling acts only through its independently
decoded endpoint-indexed program. -/
def actionOfRecognized (operation : RecognizedOperation) : CompiledAction :=
  actionOfDecoded operation.decoded

/-- Exact program equality implies equality of operational transport,
structural transport, and executable Data action together. -/
theorem action_respects (first second : RecognizedOperation)
    (same : Mettapedia.GSLT.LanguageDef.FiniteLanguageOperationSignature.Signature.SameProgram
      currentOperationSignature first second) :
    actionOfRecognized first = actionOfRecognized second := by
  exact congrArg actionOfDecoded same

/-- Compiled execution descends to the exact spelling quotient. -/
def quotientAction :
    Mettapedia.GSLT.LanguageDef.FiniteLanguageOperationSignature.Signature.OperationQuotient
        currentOperationSignature →
      CompiledAction :=
  Quotient.lift actionOfRecognized action_respects

@[simp] theorem quotientAction_mk (operation : RecognizedOperation) :
    quotientAction
        (Quotient.mk
          (Mettapedia.GSLT.LanguageDef.FiniteLanguageOperationSignature.Signature.recognizedSetoid
            currentOperationSignature)
          operation) =
      actionOfRecognized operation :=
  rfl

/-- Canonicalization does not change either interpretation or execution. -/
theorem canonical_action_agrees (operation : RecognizedOperation) :
    actionOfRecognized
        (Mettapedia.GSLT.LanguageDef.FiniteLanguageOperationSignature.Signature.canonical
          currentOperationSignature operation.decoded) =
      actionOfRecognized operation := by
  unfold actionOfRecognized
  rw [Mettapedia.GSLT.LanguageDef.FiniteLanguageOperationSignature.Signature.canonical_decoded]

end CurrentExecution

/-! ## A concrete many-spellings/one-program control -/

namespace CurrentCanary

open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageOperationSyntax

/-- The canonical spelling of the Zero identity. -/
def canonicalIdentityTerm : ScopedTerm 0 :=
  identityTerm .zero

/-- A distinct spelling which explicitly composes the Zero identity with
itself. -/
def expandedIdentityTerm : ScopedTerm 0 :=
  composeTerm .zero .zero .zero canonicalIdentityTerm canonicalIdentityTerm

def identityDecoded : currentOperationSignature.DecodedProgram :=
  { source := .zero
    target := .zero
    program := identityProgram .zero }

theorem canonicalIdentity_decodes :
    decodeProgram? canonicalIdentityTerm = some identityDecoded := by
  exact decodeProgram_encodeProgram (identityProgram .zero)

theorem expandedIdentity_decodes :
    decodeProgram? expandedIdentityTerm = some identityDecoded := by
  change currentOperationSignature.decodeProgram?
      (currentOperationSignature.composeTerm .zero .zero .zero
        (currentOperationSignature.encodeProgram
          (currentOperationSignature.identityProgram .zero))
        (currentOperationSignature.encodeProgram
          (currentOperationSignature.identityProgram .zero))) =
    some
      { source := .zero
        target := .zero
        program := Quiver.Path.comp
          (currentOperationSignature.identityProgram .zero)
          (currentOperationSignature.identityProgram .zero) }
  exact Mettapedia.GSLT.LanguageDef.FiniteLanguageOperationSignature.Signature.decodeProgram_compose_encode
    currentOperationSignature
    (currentOperationSignature.identityProgram .zero)
    (currentOperationSignature.identityProgram .zero)

/-- The two accepted terms are syntactically distinct. -/
theorem identity_spellings_distinct :
    canonicalIdentityTerm ≠ expandedIdentityTerm := by
  decide

/-- A non-operation is rejected by normalization rather than assigned a
synthetic route. -/
theorem routeType_is_not_normalized :
    Mettapedia.GSLT.LanguageDef.FiniteLanguageOperationSignature.Signature.normalize?
      currentOperationSignature (.const routeTypeName) = none := by
  simp [Mettapedia.GSLT.LanguageDef.FiniteLanguageOperationSignature.Signature.normalize?,
    Mettapedia.GSLT.LanguageDef.FiniteLanguageOperationSignature.Signature.decodeProgram?,
    Mettapedia.GSLT.LanguageDef.FiniteLanguageOperationSignature.Signature.decodeRouteName?,
    Mettapedia.GSLT.LanguageDef.FiniteLanguageOperationSignature.Signature.decodeIndex?,
    routeNameEmbedding, routeTypeName, promoteName]

def canonicalIdentityOperation : RecognizedOperation where
  term := canonicalIdentityTerm
  decoded := identityDecoded
  recognized := canonicalIdentity_decodes

def expandedIdentityOperation : RecognizedOperation where
  term := expandedIdentityTerm
  decoded := identityDecoded
  recognized := expandedIdentity_decodes

/-- Distinct surface terms become equal exactly at the categorical quotient,
not by pretending their raw syntax was identical. -/
theorem distinct_spellings_same_quotient :
    canonicalIdentityOperation.term ≠ expandedIdentityOperation.term ∧
      Quotient.mk
          (Mettapedia.GSLT.LanguageDef.FiniteLanguageOperationSignature.Signature.recognizedSetoid
            currentOperationSignature)
          canonicalIdentityOperation =
        Quotient.mk
          (Mettapedia.GSLT.LanguageDef.FiniteLanguageOperationSignature.Signature.recognizedSetoid
            currentOperationSignature)
          expandedIdentityOperation := by
  exact ⟨identity_spellings_distinct, Quotient.sound rfl⟩

end CurrentCanary

#print axioms Signature.operationQuotientEquiv
#print axioms Signature.encodeProgram_injective
#print axioms Signature.InvariantInterpretation.existsUnique_factor
#print axioms CurrentExecution.action_respects
#print axioms CurrentExecution.canonical_action_agrees
#print axioms CurrentCanary.distinct_spellings_same_quotient
#print axioms CurrentCanary.routeType_is_not_normalized

end Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageOperationFactorization

import Mettapedia.OSLF.NativeTypes.Generation.AuthoredControls
import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeDisplay

/-!
# Original language consumers of one generated native interface

The same installation, native checker, retained fair search and operational
executor serve all presentations. Structural and dependent certificates are
checked in the actual shared cube-enriched signature. Logical falsehood
formation and failed membership remain distinct from proving negation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.AuthoredPipeline.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.NativeTypes.Certificates
open Mettapedia.OSLF.NativeTypes.Semantics.Presheaf

/-- Structural graphs use full native predicate equality. Removing a required
logical feature refuses the certificate, rather than refuting the type. -/
def structuralVocabulary (language : LanguageDef) (enabled : NativeLogic.Fragment) :
    Option NativeLogic.CheckResult := do
  let logic := {BindingPipeline.Controls.fullLogic with native := enabled}
  let installed ← (generateLanguage language .star BindingPipeline.Controls.fragment logic).toOption
  let constructor ← (List.finRange installed.operational.declarations.headers.length).head?
  let certificate := Certificates.Refinement.erase (installed.structuralEvidence constructor)
  return installed.check certificate certificate.root.conclusion

#guard structuralVocabulary BindingPipeline.Controls.originalLambda NativeLogic.full == some .accepted
#guard structuralVocabulary BindingPipeline.Controls.originalLambda
    ⟨NativeLogic.full.enabled.filter (· != .functions)⟩ == some .vocabularyRefused
#guard structuralVocabulary BindingPipeline.Controls.originalLambda
    ⟨NativeLogic.full.enabled.filter (· != .universal)⟩ == some .vocabularyRefused

def checkGeneratedEvidence (language : LanguageDef) : Bool :=
  match generateLanguage language with
  | .error _ => false
  | .ok installed =>
      let structural := (List.finRange installed.operational.declarations.headers.length).all fun constructor =>
        let tree := installed.structuralEvidence constructor
        let certificate := Certificates.Refinement.erase tree
        installed.check certificate certificate.root.conclusion == .accepted
      let responses := (List.finRange installed.operational.modal.length).all fun index =>
        let tree := installed.responseEvidence index
        let certificate := Certificates.Refinement.erase tree
        installed.check certificate certificate.root.conclusion == .accepted
      let cube := installed.formerList.all fun former =>
        let tree := installed.cubeDerivation
          (CubeNativeDeclarations.primitiveFormation installed.vertex (.formation former))
        let certificate := Certificates.Refinement.erase tree
        installed.check certificate certificate.root.conclusion == .accepted
      structural && responses && cube

#guard checkGeneratedEvidence BindingPipeline.Controls.originalLambda
#guard checkGeneratedEvidence BindingPipeline.Controls.originalMachine
#guard checkGeneratedEvidence BindingPipeline.Controls.originalLetCase

def searchStructural (language : LanguageDef) : Bool :=
  match generateLanguage language with
  | .error _ => false
  | .ok installed =>
      let prepared := installed.prepare
      (List.finRange installed.operational.declarations.headers.length).all fun constructor =>
        let certificate := Certificates.Refinement.erase (installed.structuralEvidence constructor)
        (prepared.search certificate.root.conclusion prepared.seeds.length).found.isSome

#guard searchStructural BindingPipeline.Controls.originalLambda
#guard searchStructural BindingPipeline.Controls.originalMachine
#guard searchStructural BindingPipeline.Controls.originalLetCase

def nativeAnswers (language : LanguageDef) :
    Option (BindingPipeline.Installed.NativeAnswer × BindingPipeline.Installed.NativeAnswer ×
      NativeLogic.CheckResult) := do
  let installed ← (generateLanguage language).toOption
  let prepared := installed.prepare
  let empty := deriveList (D := installed.signature) .contextNil .nil
  let truth := deriveList (.truthIntroduction .nil) (.cons empty .nil)
  let certificate := Certificates.Refinement.erase truth
  return (prepared.query (.entails .nil .truth) 0,
    prepared.query (.entails .nil .truth) prepared.seeds.length,
    installed.check certificate (.entails .nil .falsehood))

#guard nativeAnswers BindingPipeline.Controls.originalLambda == some (.unknown, .proved, .certificateRejected)
#guard nativeAnswers BindingPipeline.Controls.originalMachine == some (.unknown, .proved, .certificateRejected)
#guard nativeAnswers BindingPipeline.Controls.originalLetCase == some (.unknown, .proved, .certificateRejected)

def main : IO Unit := do
  for language in [BindingPipeline.Controls.originalLambda, BindingPipeline.Controls.originalMachine,
      BindingPipeline.Controls.originalLetCase] do
    match generateLanguage language with
    | .error reason => IO.println ("Generation refused: " ++ reprStr reason)
    | .ok installed =>
        IO.println installed.renderGenerated
        IO.println ("Generated evidence checked=" ++ toString (checkGeneratedEvidence language) ++
          "; structural judgments discovered=" ++ toString (searchStructural language) ++
          "; unknown/proof/bad-certificate=" ++ reprStr (nativeAnswers language))
  IO.println (BindingPipeline.Controls.renderExecution BindingPipeline.Controls.originalLambda
    BindingPipeline.Controls.lambdaSource 2000)
  IO.println (BindingPipeline.Controls.renderExecution BindingPipeline.Controls.originalMachine
    BindingPipeline.Controls.machineSource 500)
  IO.println (BindingPipeline.Controls.renderExecution BindingPipeline.Controls.originalLetCase
    BindingPipeline.Controls.letCaseSource 2000)
  IO.println (BindingPipeline.Controls.renderExecution BindingPipeline.Controls.originalMachine
    BindingPipeline.Controls.stoppedMachine 500)

#eval main

end Mettapedia.OSLF.NativeTypes.Generation.AuthoredPipeline.Controls

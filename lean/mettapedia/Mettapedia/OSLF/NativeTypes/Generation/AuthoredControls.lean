import Mettapedia.OSLF.NativeTypes.Generation.AuthoredPipeline
import Mettapedia.OSLF.NativeTypes.Generation.BindingControls

/-!
# Original presentations through the cube-enriched native generator

The same entry point receives the original language definitions. Independent
language, vocabulary and cube choices affect the generated signature or its
ordinary certificate checking. Source declaration indices survive selection.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.AuthoredPipeline.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Semantics.Presheaf
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.NativeTypes.Certificates

def generateLanguage (language : LanguageDef) (kind : HSort := .star)
    (fragment : LanguageFragment := BindingPipeline.Controls.fragment)
    (logic : BindingPipeline.Logic := BindingPipeline.Controls.fullLogic) : Except Issue Installed :=
  AuthoredPipeline.generate (BindingPipeline.Controls.snapshot language) fragment logic
    (fun _ => kind, fun _ => kind)

def counts (language : LanguageDef) : Option (Nat × Nat) :=
  match generateLanguage language with
  | .error _ => none
  | .ok installed => some (installed.operational.declarations.headers.length,
      installed.operational.modal.length)

#guard (counts BindingPipeline.Controls.originalLambda).isSome
#guard (counts BindingPipeline.Controls.originalMachine).isSome
#guard (counts BindingPipeline.Controls.originalLetCase).isSome

def unusedConstructor : GrammarRule :=
  {label := "UnusedConstant", category := "Term", params := [], syntaxPattern := []}

def languageWithUnusedConstructor : LanguageDef :=
  {BindingPipeline.Controls.originalLambda with
    terms := unusedConstructor :: BindingPipeline.Controls.originalLambda.terms}

def selectedConstructors : LanguageFragment :=
  {BindingPipeline.Controls.fragment with
    constructorIndices := some (List.range' 1 BindingPipeline.Controls.originalLambda.terms.length)}

def selectedOrigins : Option (List Nat) :=
  match generateLanguage languageWithUnusedConstructor .star selectedConstructors with
  | .error _ => none
  | .ok installed => some ((List.finRange installed.operational.declarations.headers.length).map
      fun constructor => (installed.operational.constructorOrigin constructor).2)

#guard selectedOrigins == some (List.range' 1 BindingPipeline.Controls.originalLambda.terms.length)
#guard counts languageWithUnusedConstructor != counts BindingPipeline.Controls.originalLambda

def closedConstructorKind (language : LanguageDef) (vertexKind requested : HSort) : Option Bool :=
  match generateLanguage language vertexKind with
  | .error _ => none
  | .ok installed =>
      match (List.finRange installed.operational.declarations.headers.length).head? with
      | none => none
      | some constructor =>
          let declaration : NativeCubeProfile.Former installed.operational := .inl constructor
          let code : CubeNativeKindEncoding.PureCode
              ((NativeCubeProfile.signature installed.operational).output declaration) :=
            @CubeEnrichment.Code.former (NativeCubeProfile.signature installed.operational)
              (fun _ => Empty) declaration (fun _ => .sort .star)
          match installed.cubeFormation? code requested with
          | none => some false
          | some (term, certificate) => some (installed.check certificate
              (installed.cubeJudgment code requested term) == .accepted)

-- Lambda's first constructor binds one argument; a star constant has kind box.
#guard closedConstructorKind BindingPipeline.Controls.originalLambda .box .box == some true
#guard closedConstructorKind BindingPipeline.Controls.originalLambda .star .box == some false
#guard closedConstructorKind BindingPipeline.Controls.originalLambda .star .star == some false

def vocabularyResult (language : LanguageDef) (permitTruth : Bool) : Option NativeLogic.CheckResult :=
  let logic := {BindingPipeline.Controls.fullLogic with
    native := ⟨if permitTruth then NativeLogic.full.enabled
      else NativeLogic.full.enabled.filter (· != .truth)⟩}
  match generateLanguage language .star BindingPipeline.Controls.fragment logic with
  | .error _ => none
  | .ok installed =>
      let empty := deriveList (D := installed.signature) .contextNil .nil
      let tree := deriveList (.truthIntroduction .nil) (.cons empty .nil)
      some (installed.check (Certificates.Refinement.erase tree) (.entails .nil .truth))

#guard vocabularyResult BindingPipeline.Controls.originalLambda true == some .accepted
#guard vocabularyResult BindingPipeline.Controls.originalLambda false == some .vocabularyRefused

def runTargets (language : LanguageDef) (source : BindingPipeline.Installed.Source) (budget : Nat) :
    Option (List Pattern × Bool) :=
  match generateLanguage language with
  | .error _ => none
  | .ok installed =>
      let state := installed.operational.resume source budget (installed.operational.begin source)
      some ((installed.operational.receipts state).map (·.target),
        Mettapedia.OSLF.MeTTaIL.GeneralPremise.Scheduler.complete state)

#guard runTargets BindingPipeline.Controls.originalLambda BindingPipeline.Controls.lambdaSource 2000 ==
  some ([Mettapedia.OSLF.MeTTaIL.StructuralDescent.Controls.nestedTarget], true)
#guard (runTargets BindingPipeline.Controls.originalMachine BindingPipeline.Controls.machineSource 500).map Prod.fst ==
  some Mettapedia.OSLF.MeTTaIL.StructuralDescent.Controls.partrecTargets
#guard (runTargets BindingPipeline.Controls.originalLetCase BindingPipeline.Controls.letCaseSource 2000).map Prod.snd ==
  some true

end Mettapedia.OSLF.NativeTypes.Generation.AuthoredPipeline.Controls

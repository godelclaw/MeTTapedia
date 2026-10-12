import Mettapedia.OSLF.NativeTypes.Generation.BindingNativeSearch
import Mettapedia.OSLF.NativeTypes.Generation.BindingControls

/-!
# Runnable selected native proof-search controls

Generated headers are discovered by searching the computed finite priority
prefix. The same interface handles all three original presentations. A
logical formation judgment is distinct from an inhabitance claim; formation
of falsehood never certifies falsehood itself.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.BindingPipeline.Controls

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.NativeTypes.Certificates

def searchedHeaders (language : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef) : Bool :=
  match installLanguage language with
  | .error _ => false
  | .ok installed =>
      let prepared := installed.prepareNativeSearch
      (List.finRange installed.declarations.headers.length).all fun constructor =>
        (prepared.search
          (.type (installed.signature.termParameters (.inl constructor))
            (installed.signature.termResult (.inl constructor)))
          installed.rawSeeds.length).found.isSome

#guard searchedHeaders originalLambda
#guard searchedHeaders originalMachine
#guard searchedHeaders originalLetCase

def nativeAnswers (language : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef) :
    Option (Installed.NativeAnswer × Installed.NativeAnswer × Installed.NativeAnswer) :=
  match installLanguage language with
  | .error _ => none
  | .ok installed => some
      (installed.queryNative (.context .nil) 0,
       installed.queryNative (.context .nil) 1,
       installed.queryNative (.entails .nil .truth) installed.rawSeeds.length)

#guard nativeAnswers originalLambda == some (.unknown, .proved, .proved)
#guard nativeAnswers originalMachine == some (.unknown, .proved, .proved)
#guard nativeAnswers originalLetCase == some (.unknown, .proved, .proved)

def withoutFalsehood (language : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef) :
    Except GenerationIssue Installed :=
  BindingPipeline.generate (snapshot language) fragment
    {fullLogic with native := ⟨NativeLogic.full.enabled.filter (· != .falsehood)⟩}
    (fun _ => .star, fun _ => .star)

def logicControl (language : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef) :
    Option (Installed.NativeAnswer × Installed.NativeAnswer) := do
  let full ← (installLanguage language).toOption
  let selected ← (withoutFalsehood language).toOption
  return (full.queryNative (.predicate .nil .falsehood) full.rawSeeds.length,
    selected.queryNative (.predicate .nil .falsehood) selected.rawSeeds.length)

#guard logicControl originalLambda == some (.proved, .vocabularyRefused)
#guard logicControl originalMachine == some (.proved, .vocabularyRefused)
#guard logicControl originalLetCase == some (.proved, .vocabularyRefused)

def wrongCertificate (language : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef) :
    Option NativeLogic.CheckResult := do
  let installed ← (installLanguage language).toOption
  let empty := NativeModalSignature.emptyFormed (plan installed.generated) installed.declarations installed.modal
  let truthCertificate := Certificates.Refinement.erase
    (deriveList (.truthIntroduction .nil) (.cons empty .nil))
  return installed.check truthCertificate (.entails .nil .falsehood)

#guard wrongCertificate originalLambda == some .certificateRejected
#guard wrongCertificate originalMachine == some .certificateRejected
#guard wrongCertificate originalLetCase == some .certificateRejected

def resumedNative (language : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef) : Bool :=
  match installLanguage language with
  | .error _ => false
  | .ok installed =>
      let judgment : Judgment installed.symbols := .entails .nil .truth
      let direct := installed.searchNative judgment installed.rawSeeds.length
      let split := installed.resumeNative judgment (installed.rawSeeds.length - 1)
        (installed.searchNative judgment 1)
      direct.cursor == split.cursor && direct.found.isSome == split.found.isSome

#guard resumedNative originalLambda
#guard resumedNative originalMachine
#guard resumedNative originalLetCase

def nativeMain : IO Unit := do
  for language in [originalLambda, originalMachine, originalLetCase] do
    IO.println (language.name ++ ": every generated result header discovered=" ++
      toString (searchedHeaders language) ++ "; native results=" ++ reprStr (nativeAnswers language) ++
      "; logic selection=" ++ reprStr (logicControl language) ++
      "; rejected false certificate=" ++ reprStr (wrongCertificate language))

#eval nativeMain

end Mettapedia.OSLF.NativeTypes.Generation.BindingPipeline.Controls

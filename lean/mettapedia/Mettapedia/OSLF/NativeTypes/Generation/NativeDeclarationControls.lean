import Mettapedia.OSLF.NativeTypes.Generation.NativeDeclarations
import Mettapedia.OSLF.NativeTypes.Instances.LetCase.Language
import Mettapedia.OSLF.Syntax.LambdaAuthoredFullRuleProfile
import Mettapedia.Languages.PartrecMachine.LanguageDef

/-!
# Executable declaration and dependent-header controls

All three authored presentations pass through one installer. Its output
contains complete ordered parameter types, including function-valued binding
parameters, and executable native certificates for every generated header.
These controls exercise declaration generation; operational execution and
semantic comparison are verified by their separate general laws.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.NativeSignature.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax

def headersChecked (language : LanguageDef) : Bool :=
  match install? language with
  | none => false
  | some installed =>
      (List.finRange installed.headers.length).all fun constructor =>
        installed.check (installed.parameterCertificate constructor)
          (.context (installed.signature.termParameters constructor)) &&
        installed.check (installed.resultCertificate constructor)
          (.type (installed.signature.termParameters constructor)
            (installed.signature.termResult constructor))

theorem installed_headers_checked (language : LanguageDef) (installed : Installation language)
    (generated : install? language = some installed) : headersChecked language = true := by
  simp only [headersChecked, generated]
  apply List.all_eq_true.mpr
  intro constructor _
  rw [installed.parameterCertificate_checked, installed.resultCertificate_checked]
  rfl

def renderCarrier {language : LanguageDef} : Carrier language → String
  | .sort position => language.types[position.val].name
  | .function domain codomain => "(" ++ renderCarrier domain ++ " -> " ++ renderCarrier codomain ++ ")"

def render (language : LanguageDef) : String :=
  match install? language with
  | none => "Native declarations refused: an undeclared or unsupported parameter/result carrier."
  | some installed =>
      "Language " ++ language.name ++ "\n" ++
      String.intercalate "\n" ((List.finRange installed.headers.length).map fun constructor =>
        let header := installed.headers[constructor]
        "  #" ++ toString header.origin.val ++ " " ++ language.terms[header.origin.val].label ++
          " : " ++ String.intercalate " * " (header.parameters.map renderCarrier) ++
          " -> " ++ renderCarrier (Carrier.sort header.result) ++
          "; graph : inputs * result -> Prop; header certificates checked")

/-- Declaration decoding retains repeated headers. This is not an admission
claim for the entire language, whose validator separately checks labels. -/
def duplicateLanguage : LanguageDef where
  name := "DuplicateConstructorOrigins"
  types := ["Value"]
  terms :=
    [{ label := "One", category := "Value", params := [], syntaxPattern := [] },
     { label := "One", category := "Value", params := [], syntaxPattern := [] }]
  equations := []
  rewrites := []

def origins (language : LanguageDef) : Option (List Nat) :=
  (install? language).map fun installed => installed.headers.map (fun header => header.origin.val)

theorem duplicate_origins_retained : origins duplicateLanguage = some [0, 1] := by decide

def undeclaredLanguage : LanguageDef where
  name := "UndeclaredParameter"
  types := ["Value"]
  terms := [{ label := "Broken", category := "Value", params := [.simple "x" (.base "Other")], syntaxPattern := [] }]
  equations := []
  rewrites := []

theorem undeclared_parameter_refused : (install? undeclaredLanguage).isSome = false := by decide

#guard headersChecked Mettapedia.Languages.PartrecMachine.partrecMachine
#guard headersChecked Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.language
#guard headersChecked Mettapedia.OSLF.NativeTypes.Instances.LetCase.language
#guard origins duplicateLanguage == some [0, 1]
#guard !(install? undeclaredLanguage).isSome

def main : IO Unit := do
  IO.println (render Mettapedia.Languages.PartrecMachine.partrecMachine)
  IO.println (render Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.language)
  IO.println (render Mettapedia.OSLF.NativeTypes.Instances.LetCase.language)

#eval main

end Mettapedia.OSLF.NativeTypes.Generation.NativeSignature.Controls

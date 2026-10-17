import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeFixedPoints
import Mettapedia.OSLF.NativeTypes.Generation.AuthoredControls
import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneCertificateControls

/-!
# Native fixed-point outputs from the original authored installations

The same installed entry point consumes the first generated authored sort
of each original presentation. The operator, its quantified monotonicity
witness and both returned predicate typing certificates are ordinary native
syntax and finite derivation trees. A damaged witness is rejected; disabled
functions or universal propositions are reported as vocabulary refusals.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.AuthoredFixedPointControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.NativeTypes.Certificates
open Mettapedia.OSLF.NativeTypes.Semantics.Presheaf
open NativeMonotoneCertificateControls

variable (installed : AuthoredPipeline.Installed)

def domain (position : Fin (BindingPipeline.plan installed.operational.generated).snapshot.language.types.length) :
    TypeExpr installed.symbols 0 :=
  SignatureSum.typeLeft (SignatureSum.typeLeft
    (NativeModalSignature.authoredType (BindingPipeline.plan installed.operational.generated)
      installed.operational.declarations installed.operational.modal (.sort position) 0))

def domainFormed (position : Fin (BindingPipeline.plan installed.operational.generated).snapshot.language.types.length) :
    Derivation installed.signature (.type .nil (domain installed position)) :=
  installed.operationalDerivation
    (NativeModalSignature.authoredFormed (BindingPipeline.plan installed.operational.generated)
      installed.operational.declarations installed.operational.modal (.sort position) .nil
      (NativeModalSignature.emptyFormed (BindingPipeline.plan installed.operational.generated)
        installed.operational.declarations installed.operational.modal))

def formed : Derivation installed.signature (.context .nil) := deriveList .contextNil .nil

def operator (position : Fin (BindingPipeline.plan installed.operational.generated).snapshot.language.types.length) :
    TermExpr installed.symbols 0 :=
  constantOperator (domain installed position) (truthPredicate (domain installed position))

def operatorCertificate
    (position : Fin (BindingPipeline.plan installed.operational.generated).snapshot.language.types.length) :
    Certificates.Refinement.Certificate installed.signature :=
  Certificates.Refinement.erase
    (constantTyping .nil (domain installed position) (truthPredicate (domain installed position))
      (formed installed) (domainFormed installed position)
      (truthPredicateTyping .nil (domain installed position) (formed installed) (domainFormed installed position)))

def monotonicityCertificate
    (position : Fin (BindingPipeline.plan installed.operational.generated).snapshot.language.types.length) :
    Certificates.Refinement.Certificate installed.signature :=
  Certificates.Refinement.erase
    (constantMonotonicity .nil (domain installed position) (truthPredicate (domain installed position))
      (formed installed) (domainFormed installed position)
      (truthPredicateTyping .nil (domain installed position) (formed installed) (domainFormed installed position)))

def run (position : Fin (BindingPipeline.plan installed.operational.generated).snapshot.language.types.length)
    (malformed : Bool) : Except NativeLogic.CheckResult Bool :=
  match installed.fixedPointPredicates .nil (domain installed position) (operator installed position)
      (Certificates.Refinement.erase (formed installed))
      (Certificates.Refinement.erase (domainFormed installed position))
      (operatorCertificate installed position)
      (if malformed then wrongMonotonicity .nil (formed installed)
        else monotonicityCertificate installed position) with
  | .error reason => .error reason
  | .ok output => .ok
      ((installed.check output.leastCertificate
        (.term .nil output.leastCode (FixedPointSyntax.predicateType (domain installed position))) == .accepted) &&
       (installed.check output.greatestCertificate
        (.term .nil output.greatestCode (FixedPointSyntax.predicateType (domain installed position))) == .accepted))

def exercise (language : LanguageDef) (malformed : Bool := false)
    (disabled : List NativeLogic.Feature := []) : Option (Except NativeLogic.CheckResult Bool) :=
  let logic := {BindingPipeline.Controls.fullLogic with
    native := ⟨NativeLogic.full.enabled.filter (fun feature => !disabled.contains feature)⟩}
  match AuthoredPipeline.Controls.generateLanguage language .star BindingPipeline.Controls.fragment logic with
  | .error _ => none
  | .ok installed =>
      match (List.finRange (BindingPipeline.plan installed.operational.generated).snapshot.language.types.length).head? with
      | none => none
      | some position => some (run installed position malformed)

def main : IO Unit := do
  let cases : List (Bool × List NativeLogic.Feature × Except NativeLogic.CheckResult Bool) :=
    [(false, [], .ok true), (true, [], .error .certificateRejected),
      (false, [.functions], .error .vocabularyRefused),
      (false, [.universal], .error .vocabularyRefused)]
  for language in [BindingPipeline.Controls.originalLambda,
      BindingPipeline.Controls.originalMachine, BindingPipeline.Controls.originalLetCase] do
    for (malformed, disabled, expected) in cases do
      let answer := exercise language malformed disabled
      unless answer == some expected do
        throw (IO.userError ("Native fixed-point control failed for " ++ language.name ++
          "; malformed=" ++ toString malformed ++ "; disabled=" ++ reprStr disabled))
  IO.println "Authored native fixed-point controls: 12 passed"

#eval main

end Mettapedia.OSLF.NativeTypes.Generation.AuthoredFixedPointControls

import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorJudgmentReplay
import Mettapedia.Logic.DerivationList
import Lean.Elab.Tactic

/-!
# Producing finite annotated certificates from existing source proofs

These elaborator commands are untrusted certificate producers. They inspect
existing constructor proofs and emit finite rule data. Structural proof recursion,
projections and definitionally reflexive casts are unfolded before extraction.
The ordinary source
checker independently validates the result. Declared roots require explicit
schema citations; this producer handles the surrounding derivations and
context formation without inventing those citations.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies
namespace Programs.Annotated.JudgmentReplay.Producer

open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Annotated

def assemble (profile : ComputationProfiles.Selection) {statement : CStatement Tower.Head}
    (code : Checking.Code Tower.Head (decoder profile).Code statement)
    (children : List (Certificate profile)) : Certificate profile :=
  Logic.Derivation.fromChildren statement ⟨statement, code⟩ children

open Lean Meta Elab Tactic

private def codeFamily (profile : Expr) : MetaM Expr := do
  let provider ← mkAppM ``decoder #[profile]
  mkAppM ``Checking.RootDecoder.Code #[provider]

private def expose (fuel : Nat) (proof : Expr) : MetaM Expr := do
  match fuel with
  | 0 => throwError "Source proof unfolding exhausted its supplied traversal fuel"
  | fuel + 1 =>
      let value ← withTransparency .all (whnf proof)
      if let .proj structureName index parent := value then
        let exposed ← expose fuel parent
        return ← expose fuel (.proj structureName index exposed)
      let .const name levels := value.getAppFn | throwError "Expected a source constructor; got {value}"
      let info ← getConstInfo name
      if let .ctorInfo _ := info then
        return value
      else if let .recInfo recursor := info then
        let arguments := value.getAppArgs
        let major := recursor.getMajorIdx
        unless major < arguments.size do
          throwError "Source recursor {name} has no supplied major premise"
        let premiseType ← withTransparency .all (whnf (← inferType arguments[major]!))
        if premiseType.isAppOfArity ``Eq 3 then
          let sides := premiseType.getAppArgs
          if ← withTransparency .all (isDefEq sides[1]! sides[2]!) then
            let reflexive ← mkEqRefl sides[1]!
            return ← expose fuel (mkAppN value.getAppFn (arguments.set! major reflexive))
        let premise ← expose fuel arguments[major]!
        expose fuel (mkAppN value.getAppFn (arguments.set! major premise))
      else if let some body := info.value? (allowOpaque := true) then
        expose fuel (mkAppN (body.instantiateLevelParams info.levelParams levels) value.getAppArgs)
      else
        throwError "Cannot expose source constructor through {name}: {← inferType value}"

private def constructor (fuel : Nat) (proof : Expr) (expected : Name) : MetaM (ConstructorVal × Array Expr) := do
  let value ← expose fuel proof
  let .const name _ := value.getAppFn | throwError "Expected a source constructor; got {value}"
  let .ctorInfo ctor ← getConstInfo name | throwError "Expected a source constructor; got {name}"
  unless ctor.induct == expected do
    throwError "Expected a constructor of {expected}; got {name}"
  return (ctor, value.getAppArgs)

private def derivation (fuel : Nat) (profile : Expr) (proof : Expr) : MetaM Expr := do
  match fuel with
  | 0 => throwError "Annotated certificate producer exhausted its supplied traversal fuel"
  | fuel + 1 =>
      let (info, args) ← constructor fuel proof ``CDerivable
      let .str _ ruleName := info.name | throwError "Unexpected source constructor name {info.name}"
      if ruleName == "root" then
        throwError "Declared root admission requires an explicit annotated schema citation"
      let mut fields : Array Expr := #[]
      let mut children : List Expr := []
      for argument in args.extract info.numParams args.size do
        if ← isProof argument then
          let type ← whnf (← inferType argument)
          if type.getAppFn.constName? == some ``CDerivable then
            children := children ++ [← derivation fuel profile argument]
        else
          fields := fields.push argument
      let code := mkAppN (mkConst (``Checking.Code ++ Name.mkSimple ruleName))
        (#[mkConst ``Tower.Head, ← codeFamily profile] ++ fields)
      let certificateType ← mkAppM ``Certificate #[profile]
      mkAppM ``assemble #[profile, code, ← mkListLit certificateType children]

private def context (fuel : Nat) (profile : Expr) (proof : Expr) : MetaM Expr := do
  match fuel with
  | 0 => throwError "Annotated context producer exhausted its supplied traversal fuel"
  | fuel + 1 =>
      let (info, args) ← constructor fuel proof ``CCtxFormed
      if info.name == ``CCtxFormed.nil then
        return mkAppN (mkConst ``Checking.ContextCode.nil)
          #[mkConst ``Tower.Head, ← mkAppM ``Witness #[profile]]
      else
        let prior ← context fuel profile (args[args.size - 2]!)
        let (_, typed) ← constructor fuel (args[args.size - 1]!) ``Exists
        let level := typed[typed.size - 2]!
        let (_, pair) ← constructor fuel (typed[typed.size - 1]!) ``And
        let domain ← derivation fuel profile (pair[pair.size - 1]!)
        mkAppM ``Checking.ContextCode.snoc #[prior, level, domain]

syntax (name := annotatedCertificate) "annotated_certificate " num term : tactic
syntax (name := annotatedContextCertificate) "annotated_context_certificate " num term : tactic

elab_rules : tactic
  | `(tactic| annotated_certificate $fuel:num $source:term) => withMainContext do
      let proof ← elabTerm source none
      let type ← whnf (← inferType proof)
      unless type.getAppFn.constName? == some ``CDerivable do throwError "Expected an annotated source judgment"
      let sourcePackage := type.getAppArgs[2]!
      let package ← withTransparency .all (whnf sourcePackage)
      let goal ← getMainGoal
      let expected ← goal.getType
      let mut profile ← mkFreshExprMVar (mkConst ``ComputationProfiles.Selection)
      let required ← mkAppM ``Certificate #[profile]
      unless ← isDefEq expected required do throwError "Expected an annotated Certificate goal"
      profile ← instantiateMVars profile
      let requiredPackage ← mkAppM ``church #[profile]
      unless ← withTransparency .all (isDefEq package requiredPackage) do throwError "Source profile mismatch"
      let result ← derivation fuel.getNat profile proof
      closeMainGoal `annotated_certificate result
  | `(tactic| annotated_context_certificate $fuel:num $source:term) => withMainContext do
      let proof ← elabTerm source none
      let goal ← getMainGoal
      let expected ← goal.getType
      let profile ← mkFreshExprMVar (mkConst ``ComputationProfiles.Selection)
      let arity ← mkFreshExprMVar (mkConst ``Nat)
      let required ← mkAppM ``ContextCertificate #[profile, arity]
      unless ← isDefEq expected required do throwError "Expected an annotated ContextCertificate goal"
      let result ← context fuel.getNat (← instantiateMVars profile) proof
      closeMainGoal `annotated_context_certificate result

end Programs.Annotated.JudgmentReplay.Producer
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies

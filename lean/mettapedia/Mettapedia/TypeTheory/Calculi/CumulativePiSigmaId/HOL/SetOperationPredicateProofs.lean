import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.SetOperationSignature
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLPredicateEqualityOperations
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLImpredicativeProofCompilation

/-!
# Constructive equality proofs in the common material signature

The six named operations receive the predicate-equality reading and the
constructed native proof-operation algebra. A successful proof compilation is
typed at its exact expanded conclusion. Union and powerset congruence compile
to distinct, explicitly displayed native programs, retaining their named heads.

The constructive algebra has no extensionality operations. The controls compare
an accepted reflexivity proof with a refused propositional-extensionality proof
of the same conclusion. Refusing that presentation does not refute its conclusion.
This module supplies typing; the material proof denotation is a further join.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.SetOperationPredicateProofs
open Presentation Presentation.FormationSensitive FormationSensitiveHOLInterface
open Mettapedia.Logic HOL.Embedding.ZFSetHenkinInterpretation
open SetOperationSignature (proofName)

def signature : LogicalSignature Unit Symbol :=
  HOLPredicateEqualitySignature.signature SetOperationSignature.signature

theorem fresh : SetOperationSignature.rules.constantType proofName = none := by decide

def operations : HOLNativeGenericProofCompiler.Operations signature proofName :=
  HOLPredicateEqualityOperations.operations SetOperationSignature.signature proofName fresh

def compile {Γ : HOL.Ctx Unit} {Δ : List (HOL.Formula Symbol Γ)} {φ : HOL.Formula Symbol Γ}
    (source : HOL.ProofSyntax Symbol Δ φ) {n : Nat} (objects : Sub Tower.Head Γ.length n)
    (hypotheses : Fin (Δ.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n) :
    Option (Tower.Tm n) :=
  HOLImpredicativeProofCompilation.compileExpanded signature proofName operations source objects hypotheses

theorem compile_substitute {Γ : HOL.Ctx Unit} {Δ : List (HOL.Formula Symbol Γ)} {φ : HOL.Formula Symbol Γ}
    (source : HOL.ProofSyntax Symbol Δ φ) {n m : Nat} (objects : Sub Tower.Head Γ.length n)
    (hypotheses : Fin (Δ.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n)
    (sigma : Sub Tower.Head n m) :
    compile source (fun index => subst sigma (objects index))
        (fun index => subst sigma (hypotheses index)) =
      (compile source objects hypotheses).map (subst sigma) :=
  HOLNativeGenericProofCompiler.compile_substitute signature proofName operations
    (HOLPredicateEqualityOperations.natural SetOperationSignature.signature)
    (HOL.ImpredicativeConnectives.expandProof source) objects hypotheses sigma

theorem compile_typed {Γ : HOL.Ctx Unit} {Δ : List (HOL.Formula Symbol Γ)} {φ : HOL.Formula Symbol Γ}
    (source : HOL.ProofSyntax Symbol Δ φ) {n : Nat} {target : Tower.Ctx n}
    {objects : Sub Tower.Head Γ.length n}
    {hypotheses : Fin (Δ.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n}
    {out : Tower.Tm n}
    (objectTyped : HOLNativeGenericProofCompiler.GenericTyping.Objects signature target objects)
    (hypothesisTyped : HOLNativeGenericProofCompiler.GenericTyping.Hypotheses signature operations target objects hypotheses)
    (success : compile source objects hypotheses = some out) :
    Typing operations.target target out (FormationSensitiveHOLGenericProofFamily.proof proofName
      (subst objects (HOLImpredicativeRepresentation.translate signature φ))) :=
  HOLImpredicativeProofCompilation.compileExpanded_typed signature proofName operations source
    objectTyped hypothesisTyped success

def operationConclusion (operation : Symbol mapping) : HOL.ClosedFormula Symbol :=
  .all (.all (.imp (.eq (.var (.vs .vz)) (.var .vz))
    (.eq (.app (.const operation) (.var (.vs .vz))) (.app (.const operation) (.var .vz)))))

def operationProof (operation : Symbol mapping) : HOL.ProofSyntax Symbol [] (operationConclusion operation) :=
  .allI (.allI (.impI (.eqAppArg (.const operation) (.hyp 0))))

def operationProgram (operation : Symbol mapping) : Tower.Tm 0 :=
  .lam (.lam (.lam (HOLPredicateEqualityDerived.congruence SetOperationSignature.signature set
    (.const (SetOperationSignature.symbolName operation)) (.var 2) (.var 0))))

theorem operation_compiles (operation : Symbol mapping) :
    compile (operationProof operation) Fin.elim0 Fin.elim0 = some (operationProgram operation) := rfl

theorem operation_typed (operation : Symbol mapping) :
    Typing operations.target .nil (operationProgram operation)
      (FormationSensitiveHOLGenericProofFamily.proof proofName
        (HOLImpredicativeRepresentation.translate signature (operationConclusion operation))) :=
  HOLImpredicativeProofCompilation.compileExpanded_closed_typed signature proofName operations
    (operationProof operation) (operation_compiles operation)

theorem union_typed : Typing operations.target .nil (operationProgram .union)
    (FormationSensitiveHOLGenericProofFamily.proof proofName
      (HOLImpredicativeRepresentation.translate signature (operationConclusion .union))) :=
  HOLImpredicativeProofCompilation.compileExpanded_closed_typed signature proofName operations
    (operationProof .union) (operation_compiles .union)

theorem power_typed : Typing operations.target .nil (operationProgram .power)
    (FormationSensitiveHOLGenericProofFamily.proof proofName
      (HOLImpredicativeRepresentation.translate signature (operationConclusion .power))) :=
  operation_typed .power

theorem union_and_power_programs_distinct : operationProgram .union ≠ operationProgram .power := by decide

def extensionalTruth : HOL.ProofSyntax Symbol [] (HOL.Term.eq .top .top : HOL.ClosedFormula Symbol) :=
  .eqPropI (.impI (.hyp 0)) (.impI (.hyp 0))

def reflexiveTruth : HOL.ProofSyntax Symbol [] (HOL.Term.eq .top .top : HOL.ClosedFormula Symbol) :=
  .eqRefl .top

theorem extensionalTruth_refused : compile extensionalTruth (n := 0) Fin.elim0 Fin.elim0 = none := rfl

theorem reflexiveTruth_compiles : compile reflexiveTruth (n := 0) Fin.elim0 Fin.elim0 =
    some HOLPredicateEqualityDerived.reflTerm := rfl

theorem reflexiveTruth_typed : Typing operations.target .nil HOLPredicateEqualityDerived.reflTerm
    (FormationSensitiveHOLGenericProofFamily.proof proofName
      (HOLImpredicativeRepresentation.translate signature (HOL.Term.eq .top .top : HOL.ClosedFormula Symbol))) :=
  HOLImpredicativeProofCompilation.compileExpanded_closed_typed signature proofName operations
    reflexiveTruth reflexiveTruth_compiles

#print axioms compile_typed
#print axioms operation_typed
#print axioms union_and_power_programs_distinct
#print axioms extensionalTruth_refused
#print axioms reflexiveTruth_typed
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.SetOperationPredicateProofs

import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalAnnotatedElaboration
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalAnnotatedTransport
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalPredicateControls
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorAnnotatedPrograms

/-!
# Annotation-sensitive agreement and refusal controls

Two source programs are typed at the same natural type and have the same
unannotated erasure. Their retained lambda domains yield different literal
HOL terms. Both terms have explicit beta proofs to the same zero, so their
relationship is proved equality rather than a syntactic identification.
The reader also refuses a malformed domain and a non-function application.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading.AnnotatedControls

open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Annotated NativeNaturalVectorFamilies

def operations := Controls.operations
abbrev number := operations.number
abbrev Const := HOL.NaturalRecursionProofControls.Const

def natural {n : Nat} : CTm Tower.Head n := .const natName
def zero {n : Nat} : CTm Tower.Head n := .const zeroName
def functions {n : Nat} : CTm Tower.Head n := .pi natural natural
def operators {n : Nat} : CTm Tower.Head n := .pi functions functions
def first : CTm Tower.Head 0 := .app (.lam functions zero) (.lam natural (.var 0))
def second : CTm Tower.Head 0 := .app (.lam operators zero) (.lam functions (.var 0))

def firstCode : HOL.ClosedTerm Const number :=
  .app (.lam (HOL.weaken operations.zero)) (.lam (.var (.vz : HOL.Var [number] number)))
def secondCode : HOL.ClosedTerm Const number :=
  .app (.lam (HOL.weaken operations.zero))
    (.lam (.var (.vz : HOL.Var [.arr number number] (.arr number number))))

theorem first_reading : AnnotatedReads operations (Γ := []) first firstCode := by
  apply AnnotatedReads.application
  · exact .abstraction (.product .natural .natural) .zero
  · exact .abstraction .natural (AnnotatedReads.var (Γ := [number]) .vz)

theorem first_read : AnnotatedReading.infer? operations [] first = some ⟨number, firstCode⟩ :=
  AnnotatedReading.infer?_complete first_reading

/-- Run the reader on the source; existence follows from its independently
constructed structural derivation. -/
def checkedFirst : AnnotatedReading.Result operations [] first :=
  (AnnotatedReading.read? operations [] first).get
    (by rw [AnnotatedReading.read?_complete first_reading]; rfl)

theorem checkedFirst_agrees : checkedFirst.val = ⟨number, firstCode⟩ :=
  AnnotatedReading.coherent checkedFirst.property first_reading

theorem second_read : AnnotatedReading.infer? operations [] second = some ⟨number, secondCode⟩ := by
  apply AnnotatedReading.infer?_complete
  apply AnnotatedReads.application
  · exact .abstraction (.product (.product .natural .natural) (.product .natural .natural)) .zero
  · exact .abstraction (.product .natural .natural)
      (AnnotatedReads.var (Γ := [.arr number number]) .vz)

theorem same_erasure : first.erase = second.erase := rfl

theorem different_annotations : first ≠ second := by
  intro same
  cases same

theorem different_codes : firstCode ≠ secondCode := by
  intro same
  have erased := congrArg HOL.CheckableFragment.erase same
  cases erased

def first_beta : HOL.ProofSyntax Const [] (.eq firstCode operations.zero) := by
  apply HOL.ProofSyntax.castIndices rfl ?_
    (.beta (.lam (.var (.vz : HOL.Var [number] number))) (HOL.weaken operations.zero))
  simp [firstCode, HOL.instantiate_weaken]

def second_beta : HOL.ProofSyntax Const [] (.eq secondCode operations.zero) := by
  apply HOL.ProofSyntax.castIndices rfl ?_
    (.beta (.lam (.var (.vz : HOL.Var [.arr number number] (.arr number number))))
      (HOL.weaken operations.zero))
  simp [secondCode, HOL.instantiate_weaken]

def codes_equal : HOL.ProofSyntax Const [] (.eq firstCode secondCode) :=
  .eqTrans first_beta (.eqSymm second_beta)

/-- Both paths meet at the same annotated source zero. Its target agreement
is derived by the reader, while the two outer codes remain different. -/
def composed_codes_equal : HOL.ProofSyntax Const [] (.eq firstCode secondCode) :=
  AnnotatedReading.compose (operations := operations) (Γ := []) (middle := (zero : CTm Tower.Head 0))
    AnnotatedReads.zero AnnotatedReads.zero first_beta (.eqSymm second_beta)

theorem composed_codes_free : composed_codes_equal.FunctionExtensionalityFree := by
  unfold composed_codes_equal
  apply AnnotatedReading.compose_free
  · simp [first_beta, HOL.ProofSyntax.FunctionExtensionalityFree]
  · simp [second_beta, HOL.ProofSyntax.FunctionExtensionalityFree]

theorem bad_domain_refused :
    AnnotatedReading.infer? operations [] (.lam zero (.var 0)) = none := by
  simp [AnnotatedReading.infer?, AnnotatedReading.read?, AnnotatedPredicateReading.Reader.read?, lexicalReading, zero, natName, zeroName,
    operations, Controls.operations, HOL.NaturalRecursionProofControls.number]

theorem nonfunction_refused :
    AnnotatedReading.infer? operations [] (.app zero zero) = none := by
  simp [AnnotatedReading.infer?, AnnotatedReading.read?, AnnotatedPredicateReading.Reader.read?, lexicalReading, zero, natName, zeroName,
    operations, Controls.operations, HOL.NaturalRecursionProofControls.number]

theorem first_unique {candidate : HOL.ClosedTerm Const number}
    (other : AnnotatedReads operations (Γ := []) first candidate) : candidate = firstCode :=
  AnnotatedReading.term_unique other (AnnotatedReading.infer?_sound _ _ _ _ _ first_read)

theorem original_zero_read :
    AnnotatedReading.infer? operations operations.parameters (liftTm natZeroIotaLeft) =
      some ⟨operations.result, operations.zeroLeft⟩ :=
  AnnotatedReading.infer?_complete
    (AnnotatedReads.of_lamFree operations.zeroLeft_reads (by decide +kernel))

theorem original_successor_read :
    AnnotatedReading.infer? operations operations.successorParameters (liftTm natSuccIotaRight) =
      some ⟨operations.result, operations.successorRight⟩ :=
  AnnotatedReading.infer?_complete
    (AnnotatedReads.of_lamFree operations.successorRight_reads (by decide +kernel))

theorem original_type_read :
    AnnotatedReading.infer? operations [] (liftTm natEliminateType) =
      some ⟨.arr operations.eliminatorType .prop, operations.eliminatorCode⟩ :=
  AnnotatedReading.infer?_complete
    (AnnotatedReads.of_lamFree operations.eliminatorCode_reads (by decide +kernel))

theorem original_zero_weakened :
    AnnotatedReading.infer? operations operations.successorParameters
      ((liftTm natZeroIotaLeft).rename wk) = some ⟨operations.result, HOL.weaken operations.zeroLeft⟩ :=
  AnnotatedReading.infer?_rename original_zero_read HOL.Rename.weaken wk (fun _ => rfl)

def identitySource : CTm Tower.Head 0 := .lam natural (.var 0)
def identityCode : HOL.ClosedTerm Const (.arr number number) := .lam (.var .vz)

theorem function_application_read : AnnotatedReading.infer? operations [.arr number number]
    (.app (.var 0) zero) =
      some ⟨number, HOL.Term.app (.var .vz) (HOL.weaken operations.zero)⟩ := by
  apply AnnotatedReading.infer?_complete
  exact .application (AnnotatedReads.var (Γ := [.arr number number]) .vz) .zero

theorem identity_substitution_read {type} (index : HOL.Var [.arr number number] type) :
    AnnotatedReading.infer? operations []
      (CTm.subst0 identitySource (FormationSensitiveHOLInterface.variableIndex index)) =
        some ⟨type, HOL.Subst.single identityCode index⟩ := by
  cases index with
  | vz =>
      apply AnnotatedReading.infer?_complete
      exact .abstraction .natural (AnnotatedReads.var (Γ := [number]) .vz)
  | vs impossible => cases impossible

theorem function_substitution_read :
    AnnotatedReading.infer? operations []
      (CTm.inst0 identitySource (.app (.var 0) zero)) =
        some ⟨number, .app identityCode operations.zero⟩ := by
  have after := AnnotatedReading.infer?_substitute function_application_read
    (HOL.Subst.single identityCode) (CTm.subst0 identitySource) identity_substitution_read
  have cancel : HOL.subst (HOL.Subst.single identityCode) (HOL.weaken operations.zero) = operations.zero :=
    HOL.instantiate_weaken identityCode operations.zero
  simpa only [CTm.inst0, HOL.subst, HOL.Subst.single, cancel] using after

variable (enabled : Programs.ComputationProfiles.Selection) {n : Nat} {Γ : CCtx Tower.Head n}

theorem natural_formed : CTyped (Programs.Annotated.church enabled) Γ natural
    (.head (.sort Tower.zero)) := Programs.Annotated.Functions.natural_typed enabled

theorem functions_formed : CTyped (Programs.Annotated.church enabled) Γ functions
    (.head (.sort Tower.zero)) := by
  apply CDerivable.cumul
    (.piForm (natural_formed enabled) (.sort _) (natural_formed enabled) (.sort _) (.sorts _ _))
  intro valuation
  simp [Mettapedia.TypeTheory.UniverseLevel.LevelExpr.eval, Tower.zero]

theorem operators_formed : CTyped (Programs.Annotated.church enabled) Γ operators
    (.head (.sort Tower.zero)) := by
  apply CDerivable.cumul
    (.piForm (functions_formed enabled) (.sort _) (functions_formed enabled) (.sort _) (.sorts _ _))
  intro valuation
  simp [Mettapedia.TypeTheory.UniverseLevel.LevelExpr.eval, Tower.zero]

theorem first_typed : CTyped (Programs.Annotated.church enabled) .nil first natural := by
  have identity : CTyped (Programs.Annotated.church enabled) .nil (.lam natural (.var 0)) functions :=
    .lamIntro (natural_formed enabled) (.sort _) (functions_formed enabled) (.sort _) (.var 0)
  have functionType : CTyped (Programs.Annotated.church enabled) .nil (.pi functions natural)
      (.head (.sort (.max Tower.zero Tower.zero))) :=
    .piForm (functions_formed enabled) (.sort _) (natural_formed enabled) (.sort _) (.sorts _ _)
  have discard : CTyped (Programs.Annotated.church enabled) .nil (.lam functions zero) (.pi functions natural) :=
    .lamIntro (functions_formed enabled) (.sort _) functionType (.sort _)
      (Programs.Annotated.Functions.zero_typed enabled)
  exact .appElim discard identity

theorem second_typed : CTyped (Programs.Annotated.church enabled) .nil second natural := by
  have identity : CTyped (Programs.Annotated.church enabled) .nil (.lam functions (.var 0)) operators :=
    .lamIntro (functions_formed enabled) (.sort _) (operators_formed enabled) (.sort _) (.var 0)
  have functionType : CTyped (Programs.Annotated.church enabled) .nil (.pi operators natural)
      (.head (.sort (.max Tower.zero Tower.zero))) :=
    .piForm (operators_formed enabled) (.sort _) (natural_formed enabled) (.sort _) (.sorts _ _)
  have discard : CTyped (Programs.Annotated.church enabled) .nil (.lam operators zero) (.pi operators natural) :=
    .lamIntro (operators_formed enabled) (.sort _) functionType (.sort _)
      (Programs.Annotated.Functions.zero_typed enabled)
  exact .appElim discard identity

#print axioms first_read
#print axioms checkedFirst_agrees
#print axioms second_read
#print axioms different_codes
#print axioms codes_equal
#print axioms composed_codes_free
#print axioms first_typed
#print axioms second_typed
#print axioms first_unique
#print axioms original_zero_read
#print axioms original_type_read
#print axioms function_substitution_read

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading.AnnotatedControls

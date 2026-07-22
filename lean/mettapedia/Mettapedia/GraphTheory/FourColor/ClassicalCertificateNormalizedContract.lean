import Mettapedia.GraphTheory.FourColor.ClassicalCertificateNormalizedConfiguration

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateNormalizedContract

open ClassicalCertificateConfiguration
open ClassicalCertificateNormalizedConfiguration

/-- Read the node successor of the distinguished pointer from a finite
pointed code.  Ill-sized external data uses zero; normalized programs never
take that branch. -/
def pointerNode (code : PointedCode) : Nat :=
  if hcode : code.WellSized then
    ((code.decode hcode).node.toFin (code.decode hcode).pointer).val
  else 0

/-- Read the face successor of the distinguished pointer from a finite
pointed code. -/
def pointerFace (code : PointedCode) : Nat :=
  if hcode : code.WellSized then
    ((code.decode hcode).face.toFin (code.decode hcode).pointer).val
  else 0

@[simp] theorem pointerNode_materialize (state : RawPointedHypermap) :
    pointerNode (PointedCode.materialize state) =
      (state.node.toFin state.pointer).val := by
  unfold pointerNode
  split
  · next hcode =>
      have hproof : hcode = PointedCode.materialize_wellSized state :=
        Subsingleton.elim _ _
      subst hcode
      rw [PointedCode.decode_materialize]
  · next hcode =>
      exact (hcode (PointedCode.materialize_wellSized state)).elim

@[simp] theorem pointerFace_materialize (state : RawPointedHypermap) :
    pointerFace (PointedCode.materialize state) =
      (state.face.toFin state.pointer).val := by
  unfold pointerFace
  split
  · next hcode =>
      have hproof : hcode = PointedCode.materialize_wellSized state :=
        Subsingleton.elim _ _
      subst hcode
      rw [PointedCode.decode_materialize]
  · next hcode =>
      exact (hcode (PointedCode.materialize_wellSized state)).elim

/-- Array-normalized pointed state together with the classical off-ring edge
transversal accumulated by a configuration program. -/
structure Compilation where
  code : PointedCode
  transversal : List Nat
  deriving DecidableEq, Repr

private def shiftDarts (amount : Nat) (darts : List Nat) : List Nat :=
  darts.map (· + amount)

/-- Efficient right-to-left interpretation of both the pointed map and its
contract transversal. -/
def compile : ConfigurationProgram → Compilation
  | [] => ⟨PointedCode.materialize pointedSeed, []⟩
  | step :: rest =>
      let previous := compile rest
      match step with
      | .rotate amount =>
          ⟨applyNormalizedStep (.rotate amount) previous.code,
            previous.transversal⟩
      | .yellow =>
          let next := applyNormalizedStep .yellow previous.code
          if rest.isEmpty then ⟨next, []⟩
          else
            ⟨next,
              (pointerNode previous.code + 4) ::
                shiftDarts 4 previous.transversal⟩
      | .hexagon =>
          let next := applyNormalizedStep .hexagon previous.code
          ⟨next,
            pointerFace next ::
              (pointerNode previous.code + 6) ::
              (previous.code.pointer + 6) ::
              shiftDarts 6 previous.transversal⟩

/-- The normalized joint interpreter is exactly the materialization of the
original function-valued contract compilation, including its transversal. -/
theorem compile_eq_materialize (program : ConfigurationProgram) :
    (compile program).code =
        PointedCode.materialize (compileContractTransversal program).state ∧
      (compile program).transversal =
        (compileContractTransversal program).transversal := by
  induction program with
  | nil => constructor <;> rfl
  | cons step rest ih =>
      rcases ih with ⟨hcode, htransversal⟩
      cases step with
      | rotate amount =>
          simp [compile, compileContractTransversal, hcode, htransversal,
            applyNormalizedStep_materialize, applyConfigurationStep]
      | yellow =>
          by_cases hempty : rest = []
          · subst rest
            simp [compile, compileContractTransversal,
              applyNormalizedStep_materialize, applyConfigurationStep]
          · simp [compile, compileContractTransversal, hcode, htransversal,
              applyNormalizedStep_materialize, applyConfigurationStep,
              shiftDarts, hempty]
            all_goals rfl
      | hexagon =>
          simp [compile, compileContractTransversal, hcode, htransversal,
            applyNormalizedStep_materialize, applyConfigurationStep,
            shiftDarts]
          constructor <;> rfl

theorem compile_code_eq_materialize (program : ConfigurationProgram) :
    (compile program).code =
      PointedCode.materialize (compileConfigurationProgram program) := by
  rw [(compile_eq_materialize program).1,
    compileContractTransversal_state]

theorem compile_transversal_eq (program : ConfigurationProgram) :
    (compile program).transversal =
      (compileContractTransversal program).transversal :=
  (compile_eq_materialize program).2

/-- Read the canonical outer ring through the finite pointed decoding. -/
def forwardRing (code : PointedCode) : List Nat :=
  if hcode : code.WellSized then (code.decode hcode).forwardRing else []

@[simp] theorem forwardRing_materialize (state : RawPointedHypermap) :
    forwardRing (PointedCode.materialize state) = state.forwardRing := by
  unfold forwardRing
  split
  · next hcode =>
      have hproof : hcode = PointedCode.materialize_wellSized state :=
        Subsingleton.elim _ _
      subst hcode
      rw [PointedCode.decode_materialize]
  · next hcode =>
      exact (hcode (PointedCode.materialize_wellSized state)).elim

/-- Efficient canonical boundary extraction for a configuration. -/
def configurationForwardRing (configuration : Configuration) : List Nat :=
  forwardRing (compile configuration.program).code

theorem configurationForwardRing_eq (configuration : Configuration) :
    configurationForwardRing configuration =
      configuration.compile.forwardRing := by
  rw [configurationForwardRing, compile_code_eq_materialize,
    forwardRing_materialize]
  rfl

/-- Efficient decoding of the selected contract annotations. -/
def contractDarts (configuration : Configuration) : List Nat :=
  selectContract configuration.contractReferences
    (compile configuration.program).transversal

theorem contractDarts_eq (configuration : Configuration) :
    contractDarts configuration = configuration.contractDarts := by
  simp [contractDarts, Configuration.contractDarts,
    compile_transversal_eq]

end ClassicalCertificateNormalizedContract

end Mettapedia.GraphTheory.FourColor

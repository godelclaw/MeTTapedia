import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfiguration

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateNormalizedConfiguration

open ClassicalCertificateConfiguration

/-- Array-valued pointed hypermap data.  Normalizing through this finite form
between construction steps prevents the original function tables from growing
into deeply nested reduction terms. -/
structure PointedCode where
  dartCount : Nat
  edge : Array Nat
  node : Array Nat
  face : Array Nat
  pointer : Nat
  deriving DecidableEq, Repr

namespace PointedCode

/-- Exact sizing conditions needed to decode a pointed array certificate. -/
def WellSized (code : PointedCode) : Prop :=
  code.edge.size = code.dartCount ∧
    code.node.size = code.dartCount ∧
    code.face.size = code.dartCount ∧
    code.pointer < code.dartCount

instance (code : PointedCode) : Decidable code.WellSized := by
  unfold WellSized
  infer_instance

/-- Materialize a function-valued pointed map as finite arrays. -/
def materialize (state : RawPointedHypermap) : PointedCode where
  dartCount := state.dartCount
  edge := Array.ofFn state.edge
  node := Array.ofFn state.node
  face := Array.ofFn state.face
  pointer := state.pointer.val

theorem materialize_wellSized (state : RawPointedHypermap) :
    (materialize state).WellSized := by
  simp [WellSized, materialize]

/-- Decode a well-sized pointed array certificate. -/
def decode (code : PointedCode) (hcode : code.WellSized) :
    RawPointedHypermap where
  dartCount := code.dartCount
  edge := fun dart => HypermapCode.lookup code.edge dart.val
  node := fun dart => HypermapCode.lookup code.node dart.val
  face := fun dart => HypermapCode.lookup code.face dart.val
  pointer := ⟨code.pointer, hcode.2.2.2⟩

/-- Materialization followed by decoding recovers the pointed map exactly. -/
theorem decode_materialize (state : RawPointedHypermap) :
    (materialize state).decode (materialize_wellSized state) = state := by
  cases state with
  | mk dartCount edge node face pointer =>
      simp [decode, materialize, HypermapCode.lookup]

/-- Forget the pointer while retaining the materialized hypermap. -/
def pointee (code : PointedCode) : HypermapCode where
  dartCount := code.dartCount
  edge := code.edge
  node := code.node
  face := code.face

theorem pointee_materialize (state : RawPointedHypermap) :
    (materialize state).pointee =
      HypermapCode.materialize state.pointee := by
  rfl

end PointedCode

/-- Apply one construction instruction after replacing the input by its finite
array normal form.  Ill-sized external data is left unchanged. -/
def applyNormalizedStep (step : ConfigurationStep) (code : PointedCode) :
    PointedCode :=
  if hcode : code.WellSized then
    PointedCode.materialize
      (applyConfigurationStep step (code.decode hcode))
  else
    code

theorem applyNormalizedStep_materialize (step : ConfigurationStep)
    (state : RawPointedHypermap) :
    applyNormalizedStep step (PointedCode.materialize state) =
      PointedCode.materialize (applyConfigurationStep step state) := by
  simp only [applyNormalizedStep, dif_pos (PointedCode.materialize_wellSized state)]
  rw [PointedCode.decode_materialize]

/-- Efficient right-to-left interpretation of a configuration program. -/
def compileNormalized : ConfigurationProgram → PointedCode
  | [] => PointedCode.materialize pointedSeed
  | step :: rest => applyNormalizedStep step (compileNormalized rest)

/-- Normalization changes the representation of intermediate states, not the
meaning of a configuration program. -/
theorem compileNormalized_eq_materialize (program : ConfigurationProgram) :
    compileNormalized program =
      PointedCode.materialize (compileConfigurationProgram program) := by
  induction program with
  | nil => rfl
  | cons step rest ih =>
      rw [compileNormalized, ih, applyNormalizedStep_materialize,
        compileConfigurationProgram]

/-- The efficient interpreter exports exactly the original compiled map. -/
theorem compileNormalized_pointee (configuration : Configuration) :
    (compileNormalized configuration.program).pointee =
      HypermapCode.materialize configuration.compile.pointee := by
  rw [compileNormalized_eq_materialize]
  exact PointedCode.pointee_materialize configuration.compile

end ClassicalCertificateNormalizedConfiguration

end Mettapedia.GraphTheory.FourColor

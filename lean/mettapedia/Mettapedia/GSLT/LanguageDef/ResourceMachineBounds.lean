import Mettapedia.GSLT.LanguageDef.ResourceExecution
import Mettapedia.Computability.StackMachineMicroSpace

/-!
# Resource bounds derived from the executed machines

An executed polynomial translator already bounds its output length: every
additional output cell must have been pushed by an actual command. The
constant is computed from the machine's command syntax, rather than assumed
to be one cell per macrostep. This supplies the size obligation of an
operational translation directly from its execution proof.

The same argument bounds both transition-state peaks and the refined peak
including primitive mutations inside each command. It does not estimate
native allocation. All internal alphabets of the resource interface are
finite; these cell bounds do not silently count arbitrary terms as bits.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ResourceTranslation

open SemanticEvidence ProofSystems Turing Polynomial
open Mettapedia.Computability
open StackMachineSpaceGrowth

namespace MachineBounds

variable {Input Output Γ Δ : Type}
    {inputEncoding : Input → List Γ} {outputEncoding : Output → List Δ}
    {transform : Input → Output}

/-- Output storage is charged by the original executed clock and the syntactic
push bound of its machine, including all sequential pushes in a macrostep. -/
theorem output_length (implementation :
    TM2ComputableInPolyTime inputEncoding outputEncoding transform) (input : Input) :
    (outputEncoding (transform input)).length ≤ (inputEncoding input).length +
      machinePushBound implementation.tm *
        implementation.time.eval (inputEncoding input).length := by
  simpa only [List.length_map] using
    StackMachineSpaceGrowth.output_length_le implementation.tm (implementation.outputsFun input)

/-- The storage polynomial is obtained from the implemented clock, not a
second unconnected size assertion. -/
theorem output_polynomial (implementation :
    TM2ComputableInPolyTime inputEncoding outputEncoding transform) :
    PolyBoundedBy (fun input => (outputEncoding (transform input)).length)
      (fun input => (inputEncoding input).length) := by
  refine ⟨X + C (machinePushBound implementation.tm) * implementation.time, ?_⟩
  intro input
  simpa only [eval_add, eval_X, eval_mul, eval_C] using output_length implementation input

/-- The complete execution peak includes temporary stacks that are empty at
halt, not merely the final output footprint. -/
theorem peak_le (implementation :
    TM2ComputableInPolyTime inputEncoding outputEncoding transform) (input : Input) :
    ExecutionSpace.runPeak implementation.tm (implementation.outputsFun input) ≤
      (inputEncoding input).length + machinePushBound implementation.tm *
        implementation.time.eval (inputEncoding input).length := by
  simpa only [List.length_map] using
    StackMachineSpaceGrowth.runPeak_le implementation.tm (implementation.outputsFun input)

theorem peak_polynomial (implementation :
    TM2ComputableInPolyTime inputEncoding outputEncoding transform) :
    PolyBoundedBy
      (fun input => ExecutionSpace.runPeak implementation.tm (implementation.outputsFun input))
      (fun input => (inputEncoding input).length) := by
  refine ⟨X + C (machinePushBound implementation.tm) * implementation.time, ?_⟩
  intro input
  simpa only [eval_add, eval_X, eval_mul, eval_C] using peak_le implementation input

/-- The polynomial bound also covers temporary cells released before the next
transition, by following the command's original primitive mutations. -/
theorem microPeak_polynomial (implementation :
    TM2ComputableInPolyTime inputEncoding outputEncoding transform) :
    PolyBoundedBy
      (fun input => StackMachineMicroSpace.runPeak implementation.tm (implementation.outputsFun input))
      (fun input => (inputEncoding input).length) := by
  refine ⟨X + C (machinePushBound implementation.tm) * implementation.time, ?_⟩
  intro input
  simpa only [eval_add, eval_X, eval_mul, eval_C, List.length_map] using
    StackMachineMicroSpace.runPeak_le implementation.tm (implementation.outputsFun input)

end MachineBounds

namespace OperationalTranslation

variable {SK TK Γ Δ : Type} [Fintype Γ] [Fintype Δ]
    {S : TheoryFamily SK} {T : TheoryFamily TK}
    {SA : AuthorityContract S} {TA : AuthorityContract T}
    {se : Computability.Encoding (Packet SA) Γ}
    {te : Computability.Encoding (Packet TA) Δ}

/-- Qualify an authored translation from its actual machine. Output size is
derived from that execution, with no separately supplied polynomial bound. -/
def ofRealization (translation : Translation SA TA)
    (implementation : TM2ComputableInPolyTime se.encode te.encode translation.packet)
    (finiteAlphabet : ∀ key, Finite (implementation.tm.Γ key)) :
    OperationalTranslation SA TA se te where
  toTranslation := translation
  outputBound := MachineBounds.output_polynomial implementation
  realization := implementation
  finiteAlphabet := finiteAlphabet

theorem output_le_executed_work (translation : OperationalTranslation SA TA se te)
    (packet : Packet SA) :
    (te.encode (translation.packet packet)).length ≤ (se.encode packet).length +
      machinePushBound translation.realization.tm *
        translation.realization.time.eval (se.encode packet).length :=
  MachineBounds.output_length translation.realization packet

theorem polynomial_peak (translation : OperationalTranslation SA TA se te) :
    PolyBoundedBy
      (fun packet => ExecutionSpace.runPeak translation.realization.tm (translation.execution packet))
      (fun packet => (se.encode packet).length) :=
  MachineBounds.peak_polynomial translation.realization

end OperationalTranslation

namespace CheckerExecution

variable {Kind Γ : Type} [Fintype Γ]
    {theory : TheoryFamily Kind} {authority : AuthorityContract theory}
    {encoding : Computability.Encoding (Packet authority) Γ}

theorem peak_le_executed_work (implementation : CheckerExecution authority encoding)
    (packet : Packet authority) :
    implementation.peak packet ≤ (encoding.encode packet).length +
      machinePushBound implementation.tm * implementation.time packet := by
  simpa only [peak, List.length_map] using
    StackMachineSpaceGrowth.runPeak_le implementation.tm (implementation.outputs packet)

/-- Polynomial checking time bounds the original machine's peak stack cells,
with no additional memory assumption. This does not bound discovery time. -/
theorem peak_polynomial (implementation : CheckerExecution authority encoding)
    (timeBound : PolyBoundedBy implementation.time
      (fun packet => (encoding.encode packet).length)) :
    PolyBoundedBy implementation.peak (fun packet => (encoding.encode packet).length) := by
  exact (PolyBoundedBy.refl _ |>.add
    ((PolyBoundedBy.const (machinePushBound implementation.tm) _).mul timeBound)).of_le
      (peak_le_executed_work implementation)

/-- Refined checker peak follows operations within commands as well as the
states at transition boundaries. -/
def microPeak (implementation : CheckerExecution authority encoding)
    (packet : Packet authority) : Nat :=
  StackMachineMicroSpace.runPeak implementation.tm (implementation.outputs packet)

theorem transition_peak_le_microPeak (implementation : CheckerExecution authority encoding)
    (packet : Packet authority) : implementation.peak packet ≤ implementation.microPeak packet :=
  StackMachineMicroSpace.transition_peak_le implementation.tm
    (implementation.outputs packet).steps _

theorem microPeak_le_executed_work (implementation : CheckerExecution authority encoding)
    (packet : Packet authority) :
    implementation.microPeak packet ≤ (encoding.encode packet).length +
      machinePushBound implementation.tm * implementation.time packet := by
  simpa only [microPeak, List.length_map] using
    StackMachineMicroSpace.runPeak_le implementation.tm (implementation.outputs packet)

theorem microPeak_polynomial (implementation : CheckerExecution authority encoding)
    (timeBound : PolyBoundedBy implementation.time
      (fun packet => (encoding.encode packet).length)) :
    PolyBoundedBy implementation.microPeak (fun packet => (encoding.encode packet).length) := by
  exact (PolyBoundedBy.refl _ |>.add
    ((PolyBoundedBy.const (machinePushBound implementation.tm) _).mul timeBound)).of_le
      (microPeak_le_executed_work implementation)

end CheckerExecution

end Mettapedia.GSLT.LanguageDef.ResourceTranslation

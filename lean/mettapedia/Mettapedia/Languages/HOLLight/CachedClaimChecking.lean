import Mettapedia.Languages.HOLLight.ClaimCheckingMachine
import Mettapedia.Computability.FramedFieldSelection

/-!
# Executed cached source-claim checking

The original source-root table, theorem table, query and source pattern are
physical input. The machine follows both references, retains the independent
source pattern, and checks the selected theorem's actual claim. Missing rows,
invalid source scope and a changed claim produce completed Boolean refusal.
Logical validity of the stored theorem is a separate chronological invariant.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.CachedClaimChecking
open Turing
open Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.Languages.OpenTheory Mettapedia.Languages.OpenTheory.SyntaxEncoding
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.SharedReferenceExecution
open ArgumentRenderingMachine
open Mettapedia.GSLT.LanguageDef.InferenceChecker
abbrev Alphabet := Binary.Alphabet

def fields (roots : Array Nat) (values : Array Theorem) (query : Nat) (goal : Pattern) : Fin 4 → List Alphabet :=
  ![ChainedCache.sourceFields theoremCodec roots values query 0,
    ChainedCache.sourceFields theoremCodec roots values query 1,
    ChainedCache.sourceFields theoremCodec roots values query 2, patternWire goal]
def inputWire (roots : Array Nat) (values : Array Theorem) (query : Nat) (goal : Pattern) :=
  Indexed.argumentWire (fields roots values query goal)
def response (roots : Array Nat) (values : Array Theorem) (query : Nat) :=
  EncodedTable.decodedOutput theoremCodec (ChainedCache.selected roots values query)

theorem input_framing (roots : Array Nat) (values : Array Theorem) (query : Nat) (goal : Pattern) :
    inputWire roots values query goal = ChainedCache.sourcePacket theoremCodec roots values query ++
      (patternWire goal).map some ++ [none] := by
  simp [inputWire, fields, ChainedCache.sourcePacket, ChainedCache.sourceFields,
    Indexed.argumentWire, Indexed.frame, List.finRange_succ, List.append_assoc]

theorem input_length (roots : Array Nat) (values : Array Theorem) (query : Nat) (goal : Pattern) :
    (inputWire roots values query goal).length =
      (ChainedCache.sourcePacket theoremCodec roots values query).length + (patternWire goal).length + 1 := by
  rw [input_framing]
  simp [Nat.add_assoc]

theorem response_length (roots : Array Nat) (values : Array Theorem) (query : Nat) :
    (response roots values query).length ≤ (table (EncodedTable.rows theoremCodec values)).length := by
  cases root : roots[query]? with
  | none =>
    simp only [response, ChainedCache.selected, root, Option.bind_none, EncodedTable.decodedOutput,
      Triples.Recovery.decodedResponse]
    have bound := output_lookup_length_le_table [] (EncodedTable.rows theoremCodec values)
    have positive : 1 ≤ (output (lookup [] (EncodedTable.rows theoremCodec values))).length := by
      cases lookup [] (EncodedTable.rows theoremCodec values) <;> simp [output]
    exact positive.trans bound
  | some physical =>
    have stored := output_lookup_length_le_table (naturalKey physical) (EncodedTable.rows theoremCodec values)
    rw [EncodedTable.lookup_rows] at stored
    have recovered : (EncodedTable.decodedOutput theoremCodec values[physical]?).length ≤
        (output (values[physical]?.map (EncodedTable.value theoremCodec))).length := by
      cases found : values[physical]? with
      | none => simp [EncodedTable.decodedOutput, Triples.Recovery.decodedResponse, output]
      | some selected =>
        simp only [EncodedTable.decodedOutput, Option.map_some, Triples.Recovery.decodedResponse,
          Triples.Recovery.result, output, field, List.length_cons, List.length_append,
          List.length_nil, List.length_map]
        rw [EncodedTable.encoded_length]
        omega
    simpa only [response, ChainedCache.selected, root, Option.bind_some] using recovered.trans stored

def cacheIndices : List (Fin 4) := [0,1,2]
abbrev selection := FramedFieldSelection.machine (Γ := Alphabet) cacheIndices
local instance : Fintype (selection.Γ selection.k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited (selection.Γ selection.k₁) := inferInstanceAs (Inhabited (Option Alphabet))
def lookupMachine : FinTM2 := StackMachineComposition.machine selection ChainedCache.machine (Equiv.refl (Option Alphabet))

theorem selection_exact (roots : Array Nat) (values : Array Theorem) (query : Nat) (goal : Pattern) :
    Indexed.frame (cacheIndices.map (fields roots values query goal)) =
      ChainedCache.sourcePacket theoremCodec roots values query := by
  simp [cacheIndices, fields, ChainedCache.sourcePacket, ChainedCache.sourceFields,
    Indexed.argumentWire, Indexed.frame, List.finRange_succ]

noncomputable def lookupOutputs (roots : Array Nat) (values : Array Theorem) (query : Nat) (goal : Pattern) :
    TM2OutputsInTime lookupMachine (inputWire roots values query goal) (some (response roots values query))
      (440 * ((inputWire roots values query goal).length + 1)^2) := by
  have selected := FramedFieldSelection.outputs cacheIndices (fields roots values query goal)
  rw [selection_exact] at selected
  have joined := StackMachineComposition.outputs selection ChainedCache.machine (Equiv.refl (Option Alphabet))
    (inputWire roots values query goal) (ChainedCache.sourcePacket theoremCodec roots values query)
    (response roots values query) _ _ selected (by
      change TM2OutputsInTime ChainedCache.machine ((ChainedCache.sourcePacket theoremCodec roots values query).map id) _ _
      simpa only [List.map_id, response] using ChainedCache.outputs theoremCodec roots values query)
  apply WordEqualityMachine.within joined
  have parts := input_length roots values query goal
  have square := Nat.pow_le_pow_left (show (ChainedCache.sourcePacket theoremCodec roots values query).length + 1 ≤
      (inputWire roots values query goal).length + 1 by omega) 2
  change 36 * ((inputWire roots values query goal).length + 1) +
    2 * (ChainedCache.sourcePacket theoremCodec roots values query).length + 2 +
    400 * ((ChainedCache.sourcePacket theoremCodec roots values query).length + 1)^2 ≤ _
  nlinarith

local instance : Inhabited (lookupMachine.Γ lookupMachine.k₀) := inferInstanceAs (Inhabited (Option Alphabet))
local instance : Fintype (lookupMachine.Γ lookupMachine.k₁) := inferInstanceAs (Fintype Alphabet)
local instance : Inhabited (lookupMachine.Γ lookupMachine.k₁) := inferInstanceAs (Inhabited Alphabet)
def retainedMachine : FinTM2 := RetainedWordExecution.WithOutput.Framed.machine lookupMachine
  (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)
def retainedFields (roots : Array Nat) (values : Array Theorem) (query : Nat) (goal : Pattern) : Fin 5 → List Alphabet :=
  ![fields roots values query goal 0, fields roots values query goal 1,
    fields roots values query goal 2, patternWire goal, response roots values query]
def retainedWire (roots : Array Nat) (values : Array Theorem) (query : Nat) (goal : Pattern) :=
  Indexed.argumentWire (retainedFields roots values query goal)

theorem retained_framing (roots : Array Nat) (values : Array Theorem) (query : Nat) (goal : Pattern) :
    retainedWire roots values query goal = inputWire roots values query goal ++
      (response roots values query).map some ++ [none] := by
  simp [retainedWire, retainedFields, inputWire, fields, Indexed.argumentWire, Indexed.frame,
    List.finRange_succ, List.append_assoc]

theorem packet_parts (roots : Array Nat) (values : Array Theorem) (query : Nat) (goal : Pattern) :
    (response roots values query).length + (patternWire goal).length + 1 ≤ (inputWire roots values query goal).length := by
  have decoded := response_length roots values query
  have cache := ChainedCache.sourcePacket_length theoremCodec roots values query
  have original := input_length roots values query goal
  omega

noncomputable def retainedOutputs (roots : Array Nat) (values : Array Theorem) (query : Nat) (goal : Pattern) :
    TM2OutputsInTime retainedMachine (inputWire roots values query goal) (some (retainedWire roots values query goal))
      (510 * ((inputWire roots values query goal).length + 1)^2) := by
  have saved := RetainedWordExecution.WithOutput.Framed.outputs lookupMachine
    (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet) (inputWire roots values query goal)
    (response roots values query) _ (lookupOutputs roots values query goal)
  have framing : RetainedWordExecution.WithOutput.Framed.outputWord lookupMachine
      (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet) (inputWire roots values query goal)
      (response roots values query) = retainedWire roots values query goal := by
    change (inputWire roots values query goal).map id ++ (response roots values query).map some ++ [none] = _
    rw [List.map_id, retained_framing]
  rw [framing] at saved
  apply WordEqualityMachine.within saved
  have bound := packet_parts roots values query goal
  nlinarith

def reverseIndices : List (Fin 2) := [1,0]
abbrev reverseMachine := FramedFieldSelection.machine (Γ := Alphabet) reverseIndices
local instance : Fintype (reverseMachine.Γ reverseMachine.k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited (reverseMachine.Γ reverseMachine.k₁) := inferInstanceAs (Inhabited (Option Alphabet))
def successMachine : FinTM2 := StackMachineComposition.machine reverseMachine ClaimCheckingMachine.machine
  (Equiv.refl (Option Alphabet))
def reverseFields (goal : Pattern) (out : Theorem) : Fin 2 → List Alphabet :=
  ![encodeWith theoremCodec out, patternWire goal]
def reverseWire (goal : Pattern) (out : Theorem) := Indexed.argumentWire (reverseFields goal out)

theorem reverse_exact (goal : Pattern) (out : Theorem) :
    Indexed.frame (reverseIndices.map (reverseFields goal out)) = ClaimCheckingMachine.inputWire goal out := by
  simp [reverseIndices, reverseFields, ClaimCheckingMachine.inputWire, ClaimCheckingMachine.fields,
    Indexed.argumentWire, List.finRange_succ]

theorem reverse_length (goal : Pattern) (out : Theorem) :
    (reverseWire goal out).length = (ClaimCheckingMachine.inputWire goal out).length := by
  simp only [reverseWire, reverseFields, ClaimCheckingMachine.inputWire, ClaimCheckingMachine.fields,
    Indexed.argumentWire_length, List.finRange_succ, List.finRange_zero, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Matrix.cons_val_zero, Matrix.cons_val_succ]
  omega

noncomputable def successOutputs (goal : Pattern) (out : Theorem) :
    TM2OutputsInTime successMachine (reverseWire goal out) (some [ClaimCheckingMachine.result goal out])
      ((ClaimCheckingMachine.coefficient + 30) * ((reverseWire goal out).length + 1)^3) := by
  have selected := FramedFieldSelection.outputs reverseIndices (reverseFields goal out)
  rw [reverse_exact] at selected
  have joined := StackMachineComposition.outputs reverseMachine ClaimCheckingMachine.machine
    (Equiv.refl (Option Alphabet)) (reverseWire goal out) (ClaimCheckingMachine.inputWire goal out)
    [ClaimCheckingMachine.result goal out] _ _ selected (by
      change TM2OutputsInTime ClaimCheckingMachine.machine ((ClaimCheckingMachine.inputWire goal out).map id) _ _
      simpa only [List.map_id] using ClaimCheckingMachine.outputs goal out)
  apply WordEqualityMachine.within joined
  have clock := ClaimCheckingMachine.clock_polynomial goal out
  have length := reverse_length goal out
  have cube : (reverseWire goal out).length + 1 ≤ ((reverseWire goal out).length + 1)^3 :=
    le_self_pow (by omega) (by decide)
  change 28 * ((reverseWire goal out).length + 1) + 2 * (ClaimCheckingMachine.inputWire goal out).length + 2 +
    ClaimCheckingMachine.clock goal out ≤ _
  rw [← length] at clock ⊢
  nlinarith

def accept (symbol : Option Alphabet) : Bool := symbol == some 1
local instance : Inhabited (successMachine.Γ successMachine.k₀) := inferInstanceAs (Inhabited (Option Alphabet))
local instance : Fintype (successMachine.Γ successMachine.k₁) := inferInstanceAs (Fintype Bool)
local instance : Inhabited (successMachine.Γ successMachine.k₁) := inferInstanceAs (Inhabited Bool)
def guardedMachine : FinTM2 := StackMachineComposition.Dispatch.machine successMachine accept [false]
def guardedWire (roots : Array Nat) (values : Array Theorem) (query : Nat) (goal : Pattern) :=
  Indexed.frame [response roots values query, patternWire goal]
def result (roots : Array Nat) (values : Array Theorem) (query : Nat) (goal : Pattern) : Bool :=
  (ChainedCache.selected roots values query).any (ClaimCheckingMachine.result goal)

theorem success_framing (roots : Array Nat) (values : Array Theorem) (query : Nat) (goal : Pattern)
    (out : Theorem) (found : ChainedCache.selected roots values query = some out) :
    guardedWire roots values query goal = some (1 : Alphabet) :: reverseWire goal out := by
  simp [guardedWire, response, found, EncodedTable.decodedOutput, Triples.Recovery.decodedResponse,
    Triples.Recovery.result, reverseWire, reverseFields, Indexed.argumentWire, Indexed.frame, List.finRange_succ]

theorem reverse_bound (roots : Array Nat) (values : Array Theorem) (query : Nat) (goal : Pattern)
    (out : Theorem) (found : ChainedCache.selected roots values query = some out) :
    (reverseWire goal out).length ≤ (inputWire roots values query goal).length := by
  have bound := packet_parts roots values query goal
  have exactLength : (reverseWire goal out).length =
      (response roots values query).length + (patternWire goal).length + 1 := by
    simp [reverseWire, reverseFields, Indexed.argumentWire_length, List.finRange_succ,
      response, found, EncodedTable.decodedOutput, Triples.Recovery.decodedResponse,
      Triples.Recovery.result, Nat.add_assoc]
    omega
  omega

noncomputable def guardedOutputs (roots : Array Nat) (values : Array Theorem) (query : Nat) (goal : Pattern) :
    TM2OutputsInTime guardedMachine (guardedWire roots values query goal)
      (some [result roots values query goal])
      ((ClaimCheckingMachine.coefficient + 50) * ((inputWire roots values query goal).length + 1)^3) := by
  have cube : (inputWire roots values query goal).length + 1 ≤ ((inputWire roots values query goal).length + 1)^3 :=
    le_self_pow (by omega) (by decide)
  cases found : ChainedCache.selected roots values query with
  | none =>
    have refused := StackMachineComposition.Dispatch.outputs_refused successMachine accept [false]
      (some (0 : Alphabet)) (none :: (patternWire goal).map some ++ [none]) (by decide)
    have framing : guardedWire roots values query goal =
        some (0 : Alphabet) :: (none :: (patternWire goal).map some ++ [none]) := by
      simp [guardedWire, response, found, EncodedTable.decodedOutput, Triples.Recovery.decodedResponse,
        Indexed.frame]
    rw [← framing] at refused
    change TM2OutputsInTime guardedMachine _ _ _ at refused
    have resultEq : result roots values query goal = false := by simp [result, found]
    rw [resultEq]
    apply WordEqualityMachine.within refused
    have bound := input_length roots values query goal
    simp only [List.length_append, List.length_cons, List.length_nil, List.length_map]
    nlinarith
  | some out =>
    have accepted := StackMachineComposition.Dispatch.outputs_success successMachine accept [false]
      (some (1 : Alphabet)) (reverseWire goal out) [ClaimCheckingMachine.result goal out]
      _ (by decide) (successOutputs goal out)
    rw [← success_framing roots values query goal out found] at accepted
    have resultEq : result roots values query goal = ClaimCheckingMachine.result goal out := by simp [result, found]
    rw [resultEq]
    apply WordEqualityMachine.within accepted
    have bound := Nat.pow_le_pow_left (Nat.add_le_add_right (reverse_bound roots values query goal out found) 1) 3
    have multiplied := Nat.mul_le_mul_left (ClaimCheckingMachine.coefficient + 30) bound
    nlinarith

def guardIndices : List (Fin 5) := [4,3]
abbrev guardSelection := FramedFieldSelection.machine (Γ := Alphabet) guardIndices
local instance : Fintype (guardSelection.Γ guardSelection.k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited (guardSelection.Γ guardSelection.k₁) := inferInstanceAs (Inhabited (Option Alphabet))
def checkMachine : FinTM2 := StackMachineComposition.machine guardSelection guardedMachine
  (Equiv.refl (Option Alphabet))

theorem guard_selection_exact (roots : Array Nat) (values : Array Theorem) (query : Nat) (goal : Pattern) :
    Indexed.frame (guardIndices.map (retainedFields roots values query goal)) = guardedWire roots values query goal := by
  simp [guardIndices, retainedFields, guardedWire]

theorem retained_length (roots : Array Nat) (values : Array Theorem) (query : Nat) (goal : Pattern) :
    (retainedWire roots values query goal).length ≤ 2 * (inputWire roots values query goal).length + 1 := by
  rw [retained_framing]
  simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
  have bound := packet_parts roots values query goal
  omega

theorem guarded_length (roots : Array Nat) (values : Array Theorem) (query : Nat) (goal : Pattern) :
    (guardedWire roots values query goal).length ≤ (inputWire roots values query goal).length + 1 := by
  have bound := packet_parts roots values query goal
  simp only [guardedWire, Indexed.frame_length, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, List.length_cons, List.length_nil]
  omega

noncomputable def checkOutputs (roots : Array Nat) (values : Array Theorem) (query : Nat) (goal : Pattern) :
    TM2OutputsInTime checkMachine (retainedWire roots values query goal) (some [result roots values query goal])
      ((ClaimCheckingMachine.coefficient + 120) * ((inputWire roots values query goal).length + 1)^3) := by
  have selected := FramedFieldSelection.outputs guardIndices (retainedFields roots values query goal)
  rw [guard_selection_exact] at selected
  have joined := StackMachineComposition.outputs guardSelection guardedMachine (Equiv.refl (Option Alphabet))
    (retainedWire roots values query goal) (guardedWire roots values query goal) [result roots values query goal]
    _ _ selected (by
      change TM2OutputsInTime guardedMachine ((guardedWire roots values query goal).map id) _ _
      simpa only [List.map_id] using guardedOutputs roots values query goal)
  apply WordEqualityMachine.within joined
  have retained := retained_length roots values query goal
  have guarded := guarded_length roots values query goal
  have cube : (inputWire roots values query goal).length + 1 ≤ ((inputWire roots values query goal).length + 1)^3 :=
    le_self_pow (by omega) (by decide)
  change 28 * ((retainedWire roots values query goal).length + 1) + 2 * (guardedWire roots values query goal).length + 2 +
    (ClaimCheckingMachine.coefficient + 50) * ((inputWire roots values query goal).length + 1)^3 ≤ _
  nlinarith

local instance : Fintype (retainedMachine.Γ retainedMachine.k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited (retainedMachine.Γ retainedMachine.k₁) := inferInstanceAs (Inhabited (Option Alphabet))
def machine : FinTM2 := StackMachineComposition.machine retainedMachine checkMachine (Equiv.refl (Option Alphabet))
def coefficient : Nat := ClaimCheckingMachine.coefficient + 1000

/-- A single cubic clock charges both complete cache tables, source rendering,
claim comparison, physical retention, transfers and every admitted refusal. -/
noncomputable def outputs (roots : Array Nat) (values : Array Theorem) (query : Nat) (goal : Pattern) :
    TM2OutputsInTime machine (inputWire roots values query goal) (some [result roots values query goal])
      (coefficient * ((inputWire roots values query goal).length + 1)^3) := by
  have joined := StackMachineComposition.outputs retainedMachine checkMachine (Equiv.refl (Option Alphabet))
    (inputWire roots values query goal) (retainedWire roots values query goal) [result roots values query goal]
    _ _ (retainedOutputs roots values query goal) (by
      change TM2OutputsInTime checkMachine ((retainedWire roots values query goal).map id) _ _
      simpa only [List.map_id] using checkOutputs roots values query goal)
  apply WordEqualityMachine.within joined
  have retained := retained_length roots values query goal
  have cube : (inputWire roots values query goal).length + 1 ≤ ((inputWire roots values query goal).length + 1)^3 :=
    le_self_pow (by omega) (by decide)
  have square : ((inputWire roots values query goal).length + 1)^2 ≤ ((inputWire roots values query goal).length + 1)^3 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  unfold coefficient
  nlinarith

theorem result_accepted_iff (roots : Array Nat) (values : Array Theorem) (query : Nat) (goal : Pattern) :
    result roots values query goal = true ↔ ∃ out,
      ChainedCache.selected roots values query = some out ∧
      argumentValidAt 0 goal = true ∧ out.sequent.hyp = ∅ ∧
        out.sequent.concl = InferenceCompiler.compileClaim goal := by
  cases found : ChainedCache.selected roots values query <;>
    simp [result, found, ClaimCheckingMachine.result, InferenceCompiler.hasClaim]

abbrev Input := (Array Nat × Array Theorem) × (Nat × Pattern)
def encodeInput (input : Input) := inputWire input.1.1 input.1.2 input.2.1 input.2.2
def evaluate (input : Input) := result input.1.1 input.1.2 input.2.1 input.2.2

noncomputable def realization : TM2ComputableInPolyTime encodeInput
    (fun accepted : Bool => [accepted]) evaluate where
  tm := machine
  inputAlphabet := Equiv.refl (Option Alphabet)
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C coefficient * (Polynomial.X + Polynomial.C 1)^3
  outputsFun input := by
    change TM2OutputsInTime machine ((encodeInput input).map id)
      (some ([evaluate input].map id)) _
    simp only [List.map_id, encodeInput, evaluate, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X]
    exact outputs input.1.1 input.1.2 input.2.1 input.2.2

theorem run_readout (roots : Array Nat) (values : Array Theorem) (query : Nat) (goal : Pattern)
    {word : List Bool} (finished : TM2Outputs machine (inputWire roots values query goal) (some word)) :
    word = [result roots values query goal] :=
  StackMachineComposition.outputs_unique finished (outputs roots values query goal).toEvalsTo

theorem run_accepted (roots : Array Nat) (values : Array Theorem) (query : Nat) (goal : Pattern)
    (finished : TM2Outputs machine (inputWire roots values query goal) (some [true])) :
    ∃ out, ChainedCache.selected roots values query = some out ∧
      argumentValidAt 0 goal = true ∧ out.sequent.hyp = ∅ ∧
        out.sequent.concl = InferenceCompiler.compileClaim goal := by
  apply (result_accepted_iff roots values query goal).mp
  exact (List.cons.inj (run_readout roots values query goal finished)).1.symm

theorem missing_root_refused (roots : Array Nat) (values : Array Theorem) (query : Nat) (goal : Pattern)
    (missing : roots[query]? = none) : result roots values query goal = false := by
  simp [result, ChainedCache.selected, missing]

theorem missing_target_refused (roots : Array Nat) (values : Array Theorem) (query physical : Nat) (goal : Pattern)
    (root : roots[query]? = some physical) (missing : values[physical]? = none) :
    result roots values query goal = false := by
  simp [result, ChainedCache.selected, root, missing]

theorem changed_claim_refused (roots : Array Nat) (values : Array Theorem) (query : Nat) (goal : Pattern)
    (out : Theorem) (found : ChainedCache.selected roots values query = some out)
    (different : out.sequent.concl ≠ InferenceCompiler.compileClaim goal) : result roots values query goal = false := by
  simp [result, found, ClaimCheckingMachine.changed_claim_refusal goal out different]

theorem repeated_root (roots : Array Nat) (values : Array Theorem) (left right : Nat) (goal : Pattern)
    (same : roots[left]? = roots[right]?) : result roots values left goal = result roots values right goal := by
  simp only [result, ChainedCache.selected, same]

namespace Controls
def goal : Pattern := .apply "p" []
def original : Theorem := ClaimCheckingMachine.Controls.taggedClaim goal
def conditional : Theorem := ClaimCheckingMachine.Controls.conditionalClaim goal

theorem reordered_acceptance : result #[1,0] #[conditional, original] 0 goal = true := by
  change ClaimCheckingMachine.result goal original = true
  exact ClaimCheckingMachine.Controls.exact_claim goal (by decide)

theorem conditional_refusal : result #[1,0] #[conditional, original] 1 goal = false := by
  change ClaimCheckingMachine.result goal conditional = false
  exact ClaimCheckingMachine.Controls.conditional_claim_refused goal

theorem repeated_acceptance : result #[0,0] #[original] 1 goal = true := by
  change ClaimCheckingMachine.result goal original = true
  exact ClaimCheckingMachine.Controls.exact_claim goal (by decide)

theorem future_root_refusal : result #[0] #[original] 1 goal = false := by
  apply missing_root_refused
  rfl

theorem future_target_refusal : result #[1] #[original] 0 goal = false := by
  apply missing_target_refused (physical := 1) <;> rfl

theorem invalid_scope_refusal :
    result #[0] #[ClaimCheckingMachine.Controls.taggedClaim (.bvar 0)] 0 (.bvar 0) = false := by
  change ClaimCheckingMachine.result (.bvar 0) (ClaimCheckingMachine.Controls.taggedClaim (.bvar 0)) = false
  exact ClaimCheckingMachine.Controls.open_bound_refused

end Controls
end Mettapedia.Languages.HOLLight.CachedClaimChecking

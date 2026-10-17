import Mettapedia.Languages.HOLLight.CachedClaimChecking

/-!
# Executed saved-premise branch of the direct calculus-to-HOL compiler

The complete root table, theorem table, requested source judgment and query
are physical input. Actual cached claim checking controls the original root
lookup. Successful output retains the original physical address; refusal
drains the packet and emits the original absent-reference response. The
comparison with the compiler's saved-premise branch uses its original builder,
without copying or unfolding the saved derivation.

The domain is the original codec image. Validity of the retained theorem and
the checked chronological prefix belongs to the enclosing compiler invariant.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.SharedPremiseExecution
open Turing Polynomial
open Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.Languages.OpenTheory Mettapedia.Languages.OpenTheory.SyntaxEncoding
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.SharedReferenceExecution
open ArgumentRenderingMachine
abbrev Alphabet := Binary.Alphabet

abbrev inputWire := CachedClaimChecking.inputWire
abbrev fields := CachedClaimChecking.fields

def rootSelector : Indexed.Template Alphabet 4 := [.inr 0, .inr 1]
local instance : Fintype ((Indexed.machine rootSelector).Γ (Indexed.machine rootSelector).k₁) :=
  inferInstanceAs (Fintype Alphabet)
local instance : Inhabited ((Indexed.machine rootSelector).Γ (Indexed.machine rootSelector).k₁) :=
  inferInstanceAs (Inhabited Alphabet)
def rootMachine : FinTM2 := StackMachineComposition.machine (Indexed.machine rootSelector)
  Mettapedia.GSLT.LanguageDef.SharedReferenceExecution.machine (Equiv.refl Alphabet)

theorem root_selector_exact (roots : Array Nat) (values : Array Theorem) (query : Nat) (goal : Pattern) :
    Indexed.instantiate rootSelector (fields roots values query goal) = referencePacket roots query := by
  simp [rootSelector, CachedClaimChecking.fields, ChainedCache.sourceFields, referencePacket, packet]

theorem reference_length (roots : Array Nat) (values : Array Theorem) (query : Nat) (goal : Pattern) :
    (referencePacket roots query).length ≤ (inputWire roots values query goal).length := by
  have cached := ChainedCache.sourcePacket_length theoremCodec roots values query
  have input := CachedClaimChecking.input_length roots values query goal
  change (CachedClaimChecking.inputWire roots values query goal).length = _ at input
  change (referencePacket roots query).length ≤ (CachedClaimChecking.inputWire roots values query goal).length
  omega

noncomputable def rootOutputs (roots : Array Nat) (values : Array Theorem) (query : Nat) (goal : Pattern) :
    TM2OutputsInTime rootMachine (inputWire roots values query goal) (some (physicalOutput roots[query]?))
      (40 * ((inputWire roots values query goal).length + 1)^2) := by
  have selected := Indexed.outputs rootSelector (fields roots values query goal)
  rw [root_selector_exact] at selected
  have joined := StackMachineComposition.outputs (Indexed.machine rootSelector)
    Mettapedia.GSLT.LanguageDef.SharedReferenceExecution.machine (Equiv.refl Alphabet)
    (inputWire roots values query goal) (referencePacket roots query) (physicalOutput roots[query]?)
    _ _ selected (by
      change TM2OutputsInTime Mettapedia.GSLT.LanguageDef.SharedReferenceExecution.machine
        ((referencePacket roots query).map id) _ _
      simpa only [List.map_id] using referenceOutputs roots query)
  apply WordEqualityMachine.within joined
  have bound := reference_length roots values query goal
  have square := Nat.pow_le_pow_left bound 2
  change 12 * ((inputWire roots values query goal).length + 1) + 2 * (referencePacket roots query).length + 2 +
    (4 * (referencePacket roots query).length^2 + 20 * (referencePacket roots query).length + 20) ≤ _
  nlinarith

local instance : Inhabited (CachedClaimChecking.machine.Γ CachedClaimChecking.machine.k₀) :=
  inferInstanceAs (Inhabited (Option Alphabet))
local instance : Fintype (CachedClaimChecking.machine.Γ CachedClaimChecking.machine.k₁) := inferInstanceAs (Fintype Bool)
local instance : Inhabited (CachedClaimChecking.machine.Γ CachedClaimChecking.machine.k₁) := inferInstanceAs (Inhabited Bool)
def savedMachine : FinTM2 := RetainedWordExecution.machine CachedClaimChecking.machine (fun accepted => accepted)
def tagged (roots : Array Nat) (values : Array Theorem) (query : Nat) (goal : Pattern) : List (Option Alphabet ⊕ Bool) :=
  .inr (CachedClaimChecking.result roots values query goal) :: (inputWire roots values query goal).map Sum.inl

noncomputable def savedOutputs (roots : Array Nat) (values : Array Theorem) (query : Nat) (goal : Pattern) :
    TM2OutputsInTime savedMachine (inputWire roots values query goal) (some (tagged roots values query goal))
      ((CachedClaimChecking.coefficient + 10) * ((inputWire roots values query goal).length + 1)^3) := by
  have saved := RetainedWordExecution.outputs CachedClaimChecking.machine (fun accepted => accepted)
    (inputWire roots values query goal) (CachedClaimChecking.result roots values query goal) [] _
    (CachedClaimChecking.outputs roots values query goal)
  apply WordEqualityMachine.within saved
  have cube : (inputWire roots values query goal).length + 1 ≤ ((inputWire roots values query goal).length + 1)^3 :=
    le_self_pow (by omega) (by decide)
  simp only [inputWire, List.length_nil] at *
  nlinarith

local instance : Fintype (savedMachine.Γ savedMachine.k₁) := inferInstanceAs (Fintype (Option Alphabet ⊕ Bool))
local instance : Inhabited (savedMachine.Γ savedMachine.k₁) := inferInstanceAs (Inhabited (Option Alphabet ⊕ Bool))
def testedMachine : FinTM2 := StackMachineComposition.machine savedMachine
  (WordHomomorphismMachine.machine SourceQuantifierEmission.project) (Equiv.refl (Option Alphabet ⊕ Bool))

theorem tagged_project (roots : Array Nat) (values : Array Theorem) (query : Nat) (goal : Pattern) :
    (tagged roots values query goal).flatMap SourceQuantifierEmission.project =
      SourceQuantifierEmission.status (CachedClaimChecking.result roots values query goal) :: inputWire roots values query goal := by
  simp only [tagged, List.flatMap_cons, SourceQuantifierEmission.project, List.singleton_append, List.flatMap_map]
  congr 1
  induction inputWire roots values query goal with
  | nil => rfl
  | cons symbol rest ih => simp [ih]

noncomputable def testedOutputs (roots : Array Nat) (values : Array Theorem) (query : Nat) (goal : Pattern) :
    TM2OutputsInTime testedMachine (inputWire roots values query goal)
      (some (SourceQuantifierEmission.status (CachedClaimChecking.result roots values query goal) :: inputWire roots values query goal))
      ((CachedClaimChecking.coefficient + 30) * ((inputWire roots values query goal).length + 1)^3) := by
  have projected := WordHomomorphismMachine.outputs SourceQuantifierEmission.project (tagged roots values query goal)
  rw [tagged_project] at projected
  have joined := StackMachineComposition.outputs savedMachine
    (WordHomomorphismMachine.machine SourceQuantifierEmission.project) (Equiv.refl (Option Alphabet ⊕ Bool))
    (inputWire roots values query goal) (tagged roots values query goal)
    (SourceQuantifierEmission.status (CachedClaimChecking.result roots values query goal) :: inputWire roots values query goal)
    _ _ (savedOutputs roots values query goal) (by
      change TM2OutputsInTime (WordHomomorphismMachine.machine SourceQuantifierEmission.project)
        ((tagged roots values query goal).map id) _ _
      simpa only [List.map_id] using projected)
  apply WordEqualityMachine.within joined
  simp only [tagged, List.length_cons, List.length_map]
  have cube : (inputWire roots values query goal).length + 1 ≤ ((inputWire roots values query goal).length + 1)^3 :=
    le_self_pow (by omega) (by decide)
  nlinarith

local instance : Inhabited (rootMachine.Γ rootMachine.k₀) := inferInstanceAs (Inhabited (Option Alphabet))
local instance : Fintype (rootMachine.Γ rootMachine.k₁) := inferInstanceAs (Fintype Alphabet)
local instance : Inhabited (rootMachine.Γ rootMachine.k₁) := inferInstanceAs (Inhabited Alphabet)
def guardedMachine : FinTM2 := StackMachineComposition.Dispatch.machine rootMachine SourceQuantifierEmission.accept [(0 : Alphabet)]
def result (roots : Array Nat) (values : Array Theorem) (query : Nat) (goal : Pattern) : Option Nat :=
  if CachedClaimChecking.result roots values query goal then roots[query]? else none

noncomputable def guardedOutputs (roots : Array Nat) (values : Array Theorem) (query : Nat) (goal : Pattern) :
    TM2OutputsInTime guardedMachine
      (SourceQuantifierEmission.status (CachedClaimChecking.result roots values query goal) :: inputWire roots values query goal)
      (some (physicalOutput (result roots values query goal)))
      (50 * ((inputWire roots values query goal).length + 1)^2) := by
  cases checked : CachedClaimChecking.result roots values query goal with
  | false =>
    have refused := StackMachineComposition.Dispatch.outputs_refused rootMachine SourceQuantifierEmission.accept [(0 : Alphabet)]
      (some (0 : Alphabet)) (inputWire roots values query goal) (by decide)
    have run : TM2OutputsInTime guardedMachine
        (SourceQuantifierEmission.status false :: inputWire roots values query goal)
        (some (physicalOutput (result roots values query goal))) ((inputWire roots values query goal).length + 2) := by
      simpa [guardedMachine, result, checked, SourceQuantifierEmission.status, AdmittedArgumentRendering.status,
        physicalOutput, output] using refused
    exact WordEqualityMachine.within run (by nlinarith)
  | true =>
    have accepted := StackMachineComposition.Dispatch.outputs_success rootMachine SourceQuantifierEmission.accept [(0 : Alphabet)]
      (some (1 : Alphabet)) (inputWire roots values query goal) (physicalOutput roots[query]?)
      _ (by decide) (rootOutputs roots values query goal)
    have run : TM2OutputsInTime guardedMachine
        (SourceQuantifierEmission.status true :: inputWire roots values query goal)
        (some (physicalOutput (result roots values query goal)))
        (40 * ((inputWire roots values query goal).length + 1)^2 + 1) := by
      simpa [guardedMachine, result, checked, SourceQuantifierEmission.status, AdmittedArgumentRendering.status] using accepted
    exact WordEqualityMachine.within run (by
      have positive : 1 ≤ ((inputWire roots values query goal).length + 1)^2 := by
        nlinarith [Nat.zero_le (inputWire roots values query goal).length]
      nlinarith)

local instance : Fintype (testedMachine.Γ testedMachine.k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited (testedMachine.Γ testedMachine.k₁) := inferInstanceAs (Inhabited (Option Alphabet))
def machine : FinTM2 := StackMachineComposition.machine testedMachine guardedMachine (Equiv.refl (Option Alphabet))
def coefficient : Nat := CachedClaimChecking.coefficient + 1000

noncomputable def outputs (roots : Array Nat) (values : Array Theorem) (query : Nat) (goal : Pattern) :
    TM2OutputsInTime machine (inputWire roots values query goal) (some (physicalOutput (result roots values query goal)))
      (coefficient * ((inputWire roots values query goal).length + 1)^3) := by
  have joined := StackMachineComposition.outputs testedMachine guardedMachine (Equiv.refl (Option Alphabet))
    (inputWire roots values query goal)
    (SourceQuantifierEmission.status (CachedClaimChecking.result roots values query goal) :: inputWire roots values query goal)
    (physicalOutput (result roots values query goal)) _ _ (testedOutputs roots values query goal) (by
      change TM2OutputsInTime guardedMachine
        ((SourceQuantifierEmission.status (CachedClaimChecking.result roots values query goal) :: inputWire roots values query goal).map id) _ _
      simpa only [List.map_id] using guardedOutputs roots values query goal)
  apply WordEqualityMachine.within joined
  simp only [List.length_cons]
  have cube : (inputWire roots values query goal).length + 1 ≤ ((inputWire roots values query goal).length + 1)^3 :=
    le_self_pow (by omega) (by decide)
  have square : ((inputWire roots values query goal).length + 1)^2 ≤ ((inputWire roots values query goal).length + 1)^3 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  unfold coefficient
  nlinarith

/-- With the original admitted source scope, this is exactly the compiler's
saved-premise branch and returns its original unchanged builder and address. -/
theorem compiler_premise (definition : ValidatedCalculusLanguageDef) (emitRule : InferenceCompiler.RuleEmitter)
    (roots : Array Nat) (origin : ProofExecution.Origin) (goal : Pattern) (state : ProofExecution.State)
    (query : Nat) (valid : argumentValidAt 0 goal = true) :
    InferenceCompiler.compileOpenWith definition emitRule roots.toList origin goal (.premise query) state =
      (result roots state.cache query goal).map (fun root => (state, root)) := by
  cases root : roots[query]? with
  | none => simp [InferenceCompiler.compileOpenWith, result, CachedClaimChecking.result, ChainedCache.selected,
      Array.getElem?_toList, root]
  | some physical =>
    cases found : state.cache[physical]? with
    | none => simp [InferenceCompiler.compileOpenWith, result, CachedClaimChecking.result, ChainedCache.selected,
        Array.getElem?_toList, root, found]
    | some out =>
      simp [InferenceCompiler.compileOpenWith, result, CachedClaimChecking.result, ChainedCache.selected,
        ClaimCheckingMachine.result, Array.getElem?_toList, root, found, valid]

theorem physicalOutput_injective : Function.Injective physicalOutput := by
  intro first second same
  cases first with
  | none =>
    cases second with
    | none => rfl
    | some second => simp [physicalOutput, output] at same
  | some first =>
    cases second with
    | none => simp [physicalOutput, output] at same
    | some second =>
      have tail : field (naturalKey first) ++ [2] = field (naturalKey second) ++ [2] :=
        (List.cons.inj same).2
      rw [field_naturalKey, field_naturalKey] at tail
      have parsed := congrArg Binary.readNatural tail
      have firstRead := Binary.readNatural_natural first []
      have secondRead := Binary.readNatural_natural second []
      simp only [List.append_nil] at firstRead secondRead
      rw [firstRead, secondRead] at parsed
      exact congrArg some (congrArg Prod.fst (Option.some.inj parsed))

abbrev Input := CachedClaimChecking.Input
def encodeInput (input : Input) := inputWire input.1.1 input.1.2 input.2.1 input.2.2
def evaluate (input : Input) := result input.1.1 input.1.2 input.2.1 input.2.2

/-- A single fixed finite machine returns the physical address or refusal in
cubic time on every source-pattern and table codec image. -/
noncomputable def realization : TM2ComputableInPolyTime encodeInput physicalOutput evaluate where
  tm := machine
  inputAlphabet := Equiv.refl (Option Alphabet)
  outputAlphabet := Equiv.refl Alphabet
  time := Polynomial.C coefficient * (Polynomial.X + Polynomial.C 1)^3
  outputsFun input := by
    change TM2OutputsInTime machine ((encodeInput input).map id)
      (some ((physicalOutput (evaluate input)).map id)) _
    simp only [List.map_id, encodeInput, evaluate, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X]
    exact outputs input.1.1 input.1.2 input.2.1 input.2.2

theorem run_readout (roots : Array Nat) (values : Array Theorem) (query : Nat) (goal : Pattern)
    {word : List Alphabet} (finished : TM2Outputs machine (inputWire roots values query goal) (some word)) :
    word = physicalOutput (result roots values query goal) :=
  StackMachineComposition.outputs_unique finished (outputs roots values query goal).toEvalsTo

/-- This address is from the original ordered root table, and the original
stored theorem has exactly the admitted requested claim and no hypotheses. -/
theorem result_some_iff (roots : Array Nat) (values : Array Theorem) (query physical : Nat) (goal : Pattern) :
    result roots values query goal = some physical ↔ roots[query]? = some physical ∧ ∃ out,
      values[physical]? = some out ∧ argumentValidAt 0 goal = true ∧
      out.sequent.hyp = ∅ ∧ out.sequent.concl = InferenceCompiler.compileClaim goal := by
  cases checked : CachedClaimChecking.result roots values query goal with
  | false =>
    simp only [result, checked, Bool.false_eq_true, ↓reduceIte, reduceCtorEq, false_iff]
    rintro ⟨root, out, found, valid, hypotheses, conclusion⟩
    have accepted := (CachedClaimChecking.result_accepted_iff roots values query goal).mpr
      ⟨out, by simp [ChainedCache.selected, root, found], valid, hypotheses, conclusion⟩
    simp [checked] at accepted
  | true =>
    have accepted := (CachedClaimChecking.result_accepted_iff roots values query goal).mp checked
    simp only [result, checked, ↓reduceIte]
    constructor
    · intro root
      obtain ⟨out, selected, valid, hypotheses, conclusion⟩ := accepted
      exact ⟨root, out, by simpa [ChainedCache.selected, root] using selected, valid, hypotheses, conclusion⟩
    · exact fun fact => fact.1

theorem run_accepted (roots : Array Nat) (values : Array Theorem) (query physical : Nat) (goal : Pattern)
    (finished : TM2Outputs machine (inputWire roots values query goal) (some (physicalOutput (some physical)))) :
    roots[query]? = some physical ∧ ∃ out, values[physical]? = some out ∧
      argumentValidAt 0 goal = true ∧ out.sequent.hyp = ∅ ∧
      out.sequent.concl = InferenceCompiler.compileClaim goal := by
  apply (result_some_iff roots values query physical goal).mp
  exact physicalOutput_injective (run_readout roots values query goal finished).symm

/-- Completed machine execution agrees with the actual saved-premise branch;
the original compiler builder and physical sharing are retained. -/
theorem run_compiler_premise (definition : ValidatedCalculusLanguageDef) (emitRule : InferenceCompiler.RuleEmitter)
    (roots : Array Nat) (origin : ProofExecution.Origin) (goal : Pattern) (state : ProofExecution.State)
    (query : Nat) (valid : argumentValidAt 0 goal = true) (address : Option Nat)
    (finished : TM2Outputs machine (inputWire roots state.cache query goal) (some (physicalOutput address))) :
    InferenceCompiler.compileOpenWith definition emitRule roots.toList origin goal (.premise query) state =
      address.map (fun root => (state, root)) := by
  rw [compiler_premise definition emitRule roots origin goal state query valid]
  have same : address = result roots state.cache query goal :=
    physicalOutput_injective (run_readout roots state.cache query goal finished)
  rw [same]

/-- The enclosing prefix is independently checked by the original HOL replay.
The machine's selected address then gives a checked certificate for the actual
stored claim; the cached theorem's provenance tags alone would not suffice. -/
theorem run_kernel_checked (definition : CalculusLanguageDef) (roots : Array Nat)
    (state : ProofExecution.State) (query physical : Nat) (goal : Pattern)
    (priorReplay : GraphExpansion.BuildChecked
      (InferenceHosting.policy (FirstOrder.InferenceTranslation.inferenceRules definition)) [] state)
    (finished : TM2Outputs machine (inputWire roots state.cache query goal) (some (physicalOutput (some physical)))) :
    argumentValidAt 0 goal = true ∧ ∃ out,
      (ProofSystem.checker (InferenceHosting.policy (FirstOrder.InferenceTranslation.inferenceRules definition))).check
        out (state.receipts.toList, physical) = true ∧
      out.sequent.hyp = ∅ ∧ out.sequent.concl = InferenceCompiler.compileClaim goal := by
  obtain ⟨_, out, found, valid, hypotheses, conclusion⟩ := run_accepted roots state.cache query physical goal finished
  refine ⟨valid, out, ?_, hypotheses, conclusion⟩
  apply (ProofSystem.checker_check_iff _ _ _).mpr
  exact ⟨state.cache, priorReplay, found⟩

/-- In a checked compiled prefix, saved-premise machine acceptance reflects
to an original source derivation. No relation between a provenance tag and a
source claim is assumed. -/
theorem run_source_derivation (definition : ValidatedCalculusLanguageDef)
    (firstOrder : Mettapedia.Languages.MM0.Translation.CalculusSimulation.FirstOrderCalculus definition.1)
    (roots : Array Nat) (state : ProofExecution.State) (query physical : Nat) (goal : Pattern)
    (priorReplay : GraphExpansion.BuildChecked
      (InferenceHosting.policy (FirstOrder.InferenceTranslation.inferenceRules definition.1)) [] state)
    (finished : TM2Outputs machine (inputWire roots state.cache query goal) (some (physicalOutput (some physical)))) :
    Nonempty (InferenceChecker.Derivation definition goal) := by
  obtain ⟨valid, out, checked, hypotheses, conclusion⟩ := run_kernel_checked definition.1 roots state query physical goal priorReplay finished
  have source := (InferenceCompiler.graph_checked_iff definition firstOrder valid).mpr
    ⟨out, (state.receipts.toList, physical), checked, hypotheses, conclusion⟩
  obtain ⟨proof, accepted⟩ := source
  obtain ⟨derivation, _⟩ := InferenceChecker.checkRaw_exists_derivation_with_exact_erasure accepted
  exact ⟨derivation⟩

theorem missing_root_refused (roots : Array Nat) (values : Array Theorem) (query : Nat) (goal : Pattern)
    (missing : roots[query]? = none) : result roots values query goal = none := by
  simp [result, missing]

theorem missing_target_refused (roots : Array Nat) (values : Array Theorem) (query physical : Nat) (goal : Pattern)
    (root : roots[query]? = some physical) (missing : values[physical]? = none) :
    result roots values query goal = none := by
  rw [result, CachedClaimChecking.missing_target_refused roots values query physical goal root missing]
  rfl

theorem changed_claim_refused (roots : Array Nat) (values : Array Theorem) (query : Nat) (goal : Pattern)
    (out : Theorem) (found : ChainedCache.selected roots values query = some out)
    (different : out.sequent.concl ≠ InferenceCompiler.compileClaim goal) : result roots values query goal = none := by
  rw [result, CachedClaimChecking.changed_claim_refused roots values query goal out found different]
  rfl

theorem invalid_scope_refused (roots : Array Nat) (values : Array Theorem) (query : Nat) (goal : Pattern)
    (invalid : argumentValidAt 0 goal = false) : result roots values query goal = none := by
  cases selected : ChainedCache.selected roots values query <;>
    simp [result, CachedClaimChecking.result, selected, ClaimCheckingMachine.result, invalid]

theorem repeated_root (roots : Array Nat) (values : Array Theorem) (left right : Nat) (goal : Pattern)
    (same : roots[left]? = roots[right]?) : result roots values left goal = result roots values right goal := by
  simp only [result, CachedClaimChecking.result, ChainedCache.selected, same]

namespace Controls
def goal : Pattern := CachedClaimChecking.Controls.goal
def original : Theorem := CachedClaimChecking.Controls.original
def conditional : Theorem := CachedClaimChecking.Controls.conditional

theorem original_physical_root : result #[1,0] #[conditional, original] 0 goal = some 1 := by
  simp [result, goal, original, conditional, CachedClaimChecking.Controls.reordered_acceptance]
theorem repeated_physical_root : result #[0,0] #[original] 1 goal = some 0 := by
  simp [result, goal, original, CachedClaimChecking.Controls.repeated_acceptance]
theorem conditional_refused : result #[1,0] #[conditional, original] 1 goal = none := by
  simp [result, goal, original, conditional, CachedClaimChecking.Controls.conditional_refusal]
theorem future_source_refused : result #[0] #[original] 1 goal = none := by
  simp [result, goal, original, CachedClaimChecking.Controls.future_root_refusal]
theorem future_physical_refused : result #[1] #[original] 0 goal = none := by
  simp [result, goal, original, CachedClaimChecking.Controls.future_target_refusal]
theorem source_scope_refused : result #[0] #[original] 0 (.bvar 0) = none := by
  apply invalid_scope_refused
  rfl
end Controls

end Mettapedia.Languages.HOLLight.SharedPremiseExecution

import Mettapedia.GSLT.LanguageDef.ResourceTranslation
import Mettapedia.Computability.ExecutionSpace

/-!
# Executed search, translation and checking pipelines

Checking has a per-packet execution bound, with no imposed polynomial bound.
This admits computing checkers as well as explicit replay. An exact operational
translation followed by a target checker implements the source checker, on
accepted and refused packets alike. The composite pays the physical handoff.

Search contributes a witnessed producer run. No terminating search procedure
for all goals, completeness, or efficient reverse proof search is assumed.
The final theorem composes discovery and verification in one actual machine.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ResourceTranslation

open SemanticEvidence HeterogeneousTheory ProofSystems Turing
open Mettapedia.Computability

/-- An implemented checker with an input-dependent clock. The clock bounds the
machine's original run; it is not an independently declared cost account. -/
structure CheckerExecution {Kind Γ : Type} [Fintype Γ]
    {theory : TheoryFamily Kind} (authority : AuthorityContract theory)
    (encoding : Computability.Encoding (Packet authority) Γ)
    extends TM2ComputableAux Γ Bool where
  time : Packet authority → Nat
  outputs : ∀ p, TM2OutputsInTime tm
    ((encoding.encode p).map inputAlphabet.symm)
    (some ([checkPacket authority p].map outputAlphabet.symm)) (time p)
  finiteAlphabet : ∀ key, Finite (tm.Γ key)

namespace CheckerExecution

variable {SK TK Γ Δ : Type} [Fintype Γ] [Fintype Δ]
    {S : TheoryFamily SK} {T : TheoryFamily TK}
    {SA : AuthorityContract S} {TA : AuthorityContract T}
    {se : Computability.Encoding (Packet SA) Γ}
    {te : Computability.Encoding (Packet TA) Δ}

set_option backward.isDefEq.respectTransparency false in
/-- Execute a packet translation and then the original target checker. Exact
replay is required here because the result implements source refusals too. -/
noncomputable def via [Inhabited Δ]
    (f : OperationalTranslation SA TA se te) (exactReplay : f.toTranslation.Exact)
    (target : CheckerExecution TA te) : CheckerExecution SA se := by
  letI : Fintype (f.realization.tm.Γ f.realization.tm.k₁) :=
    Fintype.ofEquiv Δ f.realization.outputAlphabet.symm
  letI : Inhabited (f.realization.tm.Γ f.realization.tm.k₁) :=
    ⟨f.realization.outputAlphabet.symm default⟩
  let bridge := f.realization.outputAlphabet.trans target.inputAlphabet.symm
  refine
    { tm := StackMachineComposition.machine f.realization.tm target.tm bridge
      inputAlphabet := f.realization.inputAlphabet
      outputAlphabet := target.outputAlphabet
      time := fun p => f.realization.time.eval (se.encode p).length +
        2 * (te.encode (f.packet p)).length + 2 + target.time (f.packet p)
      outputs := ?_
      finiteAlphabet := ?_ }
  · intro p
    have targetRun := target.outputs (f.packet p)
    have handoff : ((te.encode (f.packet p)).map f.realization.outputAlphabet.symm).map
        bridge = (te.encode (f.packet p)).map target.inputAlphabet.symm := by
      simp [bridge, List.map_map, Function.comp_def]
    rw [← handoff] at targetRun
    have joined := StackMachineComposition.outputs f.realization.tm target.tm bridge
      ((se.encode p).map f.realization.inputAlphabet.symm)
      ((te.encode (f.packet p)).map f.realization.outputAlphabet.symm)
      ([checkPacket TA (f.packet p)].map target.outputAlphabet.symm)
      _ _ (f.execution p) targetRun
    rw [exactReplay p] at joined
    convert joined using 1 <;> first | rfl | simp only [List.length_map]
  · intro key
    change Finite (StackMachineComposition.Alphabet f.realization.tm target.tm key)
    cases key with
    | none => exact f.finiteAlphabet _
    | some key => cases key with
      | inl key => exact f.finiteAlphabet key
      | inr key => exact target.finiteAlphabet key

/-- The realized source clock records translation, transfer and target checking
as separate summands. -/
theorem via_time [Inhabited Δ]
    (f : OperationalTranslation SA TA se te) (exactReplay : f.toTranslation.Exact)
    (target : CheckerExecution TA te) (p : Packet SA) :
    (via f exactReplay target).time p =
      f.realization.time.eval (se.encode p).length +
        2 * (te.encode (f.packet p)).length + 2 + target.time (f.packet p) := rfl

/-- Polynomial target checking is inherited only after including the executed
translation and intermediate packet length in the bound. -/
theorem via_polynomial [Inhabited Δ]
    (f : OperationalTranslation SA TA se te) (exactReplay : f.toTranslation.Exact)
    (target : CheckerExecution TA te)
    (targetBound : PolyBoundedBy target.time (fun p => (te.encode p).length)) :
    PolyBoundedBy (via f exactReplay target).time (fun p => (se.encode p).length) := by
  have translationBound : PolyBoundedBy
      (fun p => f.realization.time.eval (se.encode p).length)
      (fun p => (se.encode p).length) := ⟨f.realization.time, fun _ => le_rfl⟩
  exact ((translationBound.add ((PolyBoundedBy.const 2 _).mul f.outputBound)).add
    (PolyBoundedBy.const 2 _)).add ((targetBound.comp f.packet).trans f.outputBound)

/-- Peak stack storage is measured along this checker execution. -/
def peak (implementation : CheckerExecution SA se) (p : Packet SA) : Nat :=
  ExecutionSpace.runPeak implementation.tm (implementation.outputs p)

theorem peak_positive (implementation : CheckerExecution SA se) (p : Packet SA) :
    0 < implementation.peak p := by
  have outputStored := ExecutionSpace.output_length_le_runPeak implementation.tm
    (implementation.outputs p)
  change 1 ≤ _ at outputStored
  exact outputStored

/-- Executed acceptance inherits the independently authored meaning. -/
theorem accepted_meaning (implementation : CheckerExecution SA se)
    (p : Packet SA)
    (run : TM2Outputs implementation.tm
      ((se.encode p).map implementation.inputAlphabet.symm)
      (some ([true].map implementation.outputAlphabet.symm))) :
    S.Meaning p.1 p.2.1 := by
  have same := StackMachineComposition.outputs_unique run
    (implementation.outputs p).toTM2Outputs
  have accepted : checkPacket SA p = true := by
    simpa using (List.map_injective_iff.mpr implementation.outputAlphabet.symm.injective) same
  exact S.scope_sound _ _ ((SA.scopeAuthority _).sound _ _ accepted)

end CheckerExecution

namespace SearchExecution

variable {Kind Γ : Type} [Fintype Γ] [Inhabited Γ]
    {theory : TheoryFamily Kind} {authority : AuthorityContract theory}
    {encoding : Computability.Encoding (Packet authority) Γ}

/-- A producer's successful run, with discovery work charged independently of
certificate length and checker work. Negative goals need no terminating run. -/
noncomputable def searchThenCheck (producer : FinTM2)
    (producerOutput : producer.Γ producer.k₁ ≃ Γ)
    (checker : CheckerExecution authority encoding) : FinTM2 := by
  letI : Fintype (producer.Γ producer.k₁) := Fintype.ofEquiv Γ producerOutput.symm
  letI : Inhabited (producer.Γ producer.k₁) := ⟨producerOutput.symm default⟩
  exact StackMachineComposition.machine producer checker.tm
    (producerOutput.trans checker.inputAlphabet.symm)

set_option backward.isDefEq.respectTransparency false in
/-- One physical machine performs discovery and checking. The producer can be
partial: only this run is required. Invalid candidates produce `false` with the
same accounting theorem; a search timeout is not a proof of non-theoremhood. -/
noncomputable def searchThenCheck_outputs (producer : FinTM2)
    (producerOutput : producer.Γ producer.k₁ ≃ Γ)
    (checker : CheckerExecution authority encoding)
    (input : List (producer.Γ producer.k₀)) (p : Packet authority) (discovery : Nat)
    (produced : TM2OutputsInTime producer input
      (some ((encoding.encode p).map producerOutput.symm)) discovery) :
    TM2OutputsInTime (searchThenCheck producer producerOutput checker) input
      (some ([checkPacket authority p].map checker.outputAlphabet.symm))
      (discovery + 2 * (encoding.encode p).length + 2 + checker.time p) := by
  letI : Fintype (producer.Γ producer.k₁) := Fintype.ofEquiv Γ producerOutput.symm
  letI : Inhabited (producer.Γ producer.k₁) := ⟨producerOutput.symm default⟩
  let bridge := producerOutput.trans checker.inputAlphabet.symm
  have checked := checker.outputs p
  have handoff : ((encoding.encode p).map producerOutput.symm).map bridge =
      (encoding.encode p).map checker.inputAlphabet.symm := by
    simp [bridge, List.map_map, Function.comp_def]
  rw [← handoff] at checked
  have joined := StackMachineComposition.outputs producer checker.tm bridge input
    ((encoding.encode p).map producerOutput.symm)
    ([checkPacket authority p].map checker.outputAlphabet.symm) _ _ produced checked
  convert joined using 1 <;> first | rfl | simp only [List.length_map]

end SearchExecution

end Mettapedia.GSLT.LanguageDef.ResourceTranslation

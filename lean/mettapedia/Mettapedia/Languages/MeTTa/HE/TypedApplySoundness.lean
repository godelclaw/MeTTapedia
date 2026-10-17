import Mettapedia.Languages.MeTTa.HE.TypedApplyMachine
import Mettapedia.Languages.MeTTa.HE.EvalSpec
import Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution

/-!
# Per-position execution evidence and admitted sequential arguments

The typed-apply invariant supplies actual callback occurrences or substitution
reads at each position. It does not alone construct a sequential binding chain
or source meaning. `MachineArgChain` retains independently admitted first-success
heads and their actual output occurrences, threading each reached binding record
into the next head. Its source theorem preserves the selected readout frame.
General all-candidate HE and foreign callbacks need their own admission theorem.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open FirstSuccessSourceExecution Spec.Eval

/-- Extract the actual callback provenance; independent existential input
records at different positions do not assert sequential evaluation. -/
theorem applyComplete_args_provenance
    (space : Space) (dispatch : HE.GroundedDispatch) (fuel : Nat)
    (st : TypedApplyState)
    (provenance : ProvenanceInvariant
      (fun a t b => evalAtom space dispatch a t b fuel)
      (fun b a => Bindings.applyDefault b a) st)
    (i : Nat) (present : i < st.evArgs.length) (original : i < st.origArgs.length) :
    (∃ env, st.evArgs[i] = Bindings.applyDefault env st.origArgs[i]) ∨
    (∃ env expected output,
      (st.evArgs[i], output) ∈ evalAtom space dispatch
        (Bindings.applyDefault env st.origArgs[i]) expected env fuel) := by
  obtain ⟨env, evidence⟩ := provenance.2 i present original
  rcases evidence with read | ⟨expected, output, evaluated⟩
  · exact Or.inl ⟨env, read⟩
  · exact Or.inr ⟨env, expected, output, evaluated⟩

/-- Completed argument storage has the authored arity and the actual
per-position callback/read provenance. No source adequacy is inferred. -/
theorem emission_provenance
    (space : Space) (dispatch : HE.GroundedDispatch) (fuel : Nat)
    (st : TypedApplyState)
    (provenance : ProvenanceInvariant
      (fun a t b => evalAtom space dispatch a t b fuel)
      (fun b a => Bindings.applyDefault b a) st)
    (done : st.idx ≥ st.origArgs.length) (bounded : st.idx ≤ st.origArgs.length) :
    st.evArgs.length = st.origArgs.length ∧
    ∀ i (present : i < st.evArgs.length) (original : i < st.origArgs.length),
      (∃ env, st.evArgs[i] = Bindings.applyDefault env st.origArgs[i]) ∨
      (∃ env expected output,
        (st.evArgs[i], output) ∈ evalAtom space dispatch
          (Bindings.applyDefault env st.origArgs[i]) expected env fuel) := by
  exact ⟨by have := provenance.1; omega,
    fun i present original => applyComplete_args_provenance space dispatch fuel st
      provenance i present original⟩

/-! The following two constructors retain the historical judgment algebra.
They consume historical evidence explicitly and make no executable adequacy claim. -/

/-- For a single argument: EvalAtom derivation + nil tail = InterpretArgs. -/
theorem single_arg_interpretArgs
    (space : Space) (dispatch : GroundedDispatch)
    (arg argType : Atom) (env : Bindings)
    (headResult : ResultPair)
    (h_head : EvalAtom space dispatch arg argType env headResult)
    (h_ok : isEmptyOrError headResult.1 = false ∨ headResult.1 = arg) :
    InterpretArgs space dispatch [arg] [argType] env
      (argumentPacket [headResult.1], headResult.2) := by
  exact .cons_ok arg [] argType [] env headResult (argumentPacket [], headResult.2)
    h_head h_ok (.nil) (by
      simp)

/-- For a single argument with changed error: propagates directly. -/
theorem single_arg_error_interpretArgs
    (space : Space) (dispatch : GroundedDispatch)
    (arg argType : Atom) (env : Bindings)
    (headResult : ResultPair)
    (h_head : EvalAtom space dispatch arg argType env headResult)
    (h_err : isEmptyOrError headResult.1 = true)
    (h_changed : headResult.1 ≠ arg) :
    InterpretArgs space dispatch [arg] [argType] env headResult :=
  .head_changed_error arg [] argType [] env headResult h_head h_err h_changed

/-- Sequential first-success admission. Each head is a constructed derivation
of the existing grammar, with an actual physical result occurrence. The tail
starts from that occurrence's record, not another existential input record. -/
inductive MachineArgChain (space : Space) (fuel : Nat)
    (comparison : SourceBindingComparison := .records) :
    List Atom → List Atom → Bindings → ResultPair → (live : List Atom := []) → Prop where
  | nil {live : List Atom} (bindings : Bindings) :
      MachineArgChain space fuel comparison (live := live) [] [] bindings
        (argumentPacket [], bindings)
  | head_changed_error {live : List Atom} (a : Atom) (as : List Atom) (t : Atom) (ts : List Atom)
      (bindings : Bindings) (head : ResultPair)
      (admitted : ∃ depth ≤ fuel, ∃ results,
        AtomDerivation (comparison := comparison) space (as ++ ts ++ live)
          a t bindings depth results ∧ head ∈ results)
      (error : isEmptyOrError head.1 = true) (changed : head.1 ≠ a) :
      MachineArgChain space fuel comparison (live := live) (a :: as) (t :: ts) bindings head
  | cons_tail_error {live : List Atom} (a : Atom) (as : List Atom) (t : Atom) (ts : List Atom)
      (bindings : Bindings) (head tail : ResultPair)
      (admitted : ∃ depth ≤ fuel, ∃ results,
        AtomDerivation (comparison := comparison) space (as ++ ts ++ live)
          a t bindings depth results ∧ head ∈ results)
      (safe : isEmptyOrError head.1 = false ∨ head.1 = a)
      (rest : MachineArgChain space fuel comparison (live := head.1 :: live) as ts head.2 tail)
      (error : argumentsSucceeded tail.1 = false) :
      MachineArgChain space fuel comparison (live := live) (a :: as) (t :: ts) bindings tail
  | cons_ok {live : List Atom} (a : Atom) (as : List Atom) (t : Atom) (ts : List Atom)
      (bindings : Bindings) (head tail : ResultPair)
      (admitted : ∃ depth ≤ fuel, ∃ results,
        AtomDerivation (comparison := comparison) space (as ++ ts ++ live)
          a t bindings depth results ∧ head ∈ results)
      (safe : isEmptyOrError head.1 = false ∨ head.1 = a)
      (rest : MachineArgChain space fuel comparison (live := head.1 :: live) as ts head.2 tail)
      (success : argumentsSucceeded tail.1 = true) :
      MachineArgChain space fuel comparison (live := live) (a :: as) (t :: ts) bindings
        (argumentPacket (head.1 :: argumentValues tail.1), tail.2)

private theorem clean_source {value original : Atom}
    (safe : isEmptyOrError value = false ∨ value = original) :
    ¬Spec.Eval.IsEmptyOrErrorRel value ∨ value = original := by
  rcases safe with clean | same
  · exact Or.inl (fun error => by
      have := (Spec.Type.Conformance.isEmptyOrErrorRel_iff_isEmptyOrError value).mp error
      simp [clean] at this)
  · exact Or.inr same

/-- The independently constructed head and tail derivations retain the exact
selected source frame at every continuation. No universal evaluator transport
or source meaning is an admission field. -/
theorem machineArgChain_to_interpretArgs
    {space : Space} {fuel : Nat} {comparison : SourceBindingComparison}
    {args types : List Atom} {bindings : Bindings} {result : ResultPair} {live : List Atom}
    (chain : MachineArgChain space fuel comparison (live := live) args types bindings result)
    (sourceInput : BindingFrame)
    (related : comparison.FrameRelated bindings sourceInput) :
    ∃ sourceOutput,
      InterpretArgsRel space noHost live args types sourceInput (result.1, sourceOutput) ∧
      comparison.FrameRelated result.2 sourceOutput := by
  induction chain generalizing sourceInput with
  | nil bindings => exact ⟨sourceInput, .nil sourceInput, related⟩
  | head_changed_error a as t ts bindings head admitted error changed =>
      obtain ⟨depth, _, results, derived, member⟩ := admitted
      obtain ⟨output, evaluated, connected⟩ := derived.sound head member [] sourceInput related
      exact ⟨output, .headChangedError a as t ts sourceInput (head.1, output) evaluated
        ((Spec.Type.Conformance.isEmptyOrErrorRel_iff_isEmptyOrError head.1).mpr error)
        changed, connected⟩
  | cons_tail_error a as t ts bindings head tail admitted safe rest error ih =>
      obtain ⟨depth, _, results, derived, member⟩ := admitted
      obtain ⟨headOutput, evaluated, headRelated⟩ := derived.sound head member [] sourceInput related
      obtain ⟨tailOutput, interpreted, tailRelated⟩ := ih headOutput headRelated
      refine ⟨tailOutput, .tailError a as t ts sourceInput (head.1, headOutput)
        (tail.1, tailOutput) evaluated (clean_source safe) interpreted ?_, tailRelated⟩
      intro values same
      rw [same] at error
      simp at error
  | cons_ok a as t ts bindings head tail admitted safe rest success ih =>
      obtain ⟨depth, _, results, derived, member⟩ := admitted
      obtain ⟨headOutput, evaluated, headRelated⟩ := derived.sound head member [] sourceInput related
      obtain ⟨tailOutput, interpreted, tailRelated⟩ := ih headOutput headRelated
      exact ⟨tailOutput, .success a as t ts sourceInput (head.1, headOutput)
        (tail.1, tailOutput) evaluated (clean_source safe) interpreted
        (argumentsSucceeded_iff.mp success), tailRelated⟩

/-- Every actual row of the existing recursive argument admission constructs
its sequential chain. The head occurrences and reached records are extracted
from the actual flat-map, including duplicate rows. -/
theorem FirstSuccessSourceExecution.ArgsDerivation.machineArgChain
    {space : Space} {comparison : SourceBindingComparison} {live : List Atom}
    {args types : List Atom} {bindings : Bindings} {depth : Nat} {rows : ArgumentResults}
    (derived : ArgsDerivation (comparison := comparison) space live args types bindings depth rows)
    (row : List Atom × Bindings) (member : row ∈ rows) (fuel : Nat) (enough : depth ≤ fuel) :
    MachineArgChain space fuel comparison (live := live) args types bindings
      (argumentPacket row.1, row.2) := by
  cases derived with
  | nil live bindings depth =>
      obtain rfl := List.mem_singleton.mp member
      exact .nil bindings
  | cons live a t as ts bindings depth heads tails head safe tail =>
      obtain ⟨selected, selectedMember, restMember⟩ := List.mem_flatMap.mp member
      obtain ⟨rest, present, rfl⟩ := List.mem_map.mp restMember
      have tailChain := (tail selected selectedMember).machineArgChain rest present fuel (by omega)
      simpa only [argumentValues_packet] using MachineArgChain.cons_ok a as t ts bindings
        selected (argumentPacket rest.1, rest.2)
        ⟨depth, by omega, heads, head, selectedMember⟩
        ((safe selected selectedMember).symm) tailChain (by simp)
termination_by depth

namespace TypedApplySourceControls

/-- A raw head can contain an error-shaped expression without becoming a
changed failure; the exact record is threaded through both positions. -/
theorem raw_pair_chain (space : Space) (bindings : Bindings) (left right : Atom)
    (live : List Atom) :
    MachineArgChain space 3 (comparison := .records) (live := live) [left, right] [Atom.atomType, Atom.atomType]
      bindings (argumentPacket [left, right], bindings) := by
  have first : AtomDerivation (comparison := .records) space ([right] ++ [Atom.atomType] ++ live)
      left Atom.atomType bindings 1 [(left, bindings)] := .leaf _ _ _ _ 0 ((FirstSuccessLeafEvaluation.leaf_gate left Atom.atomType).mpr (Or.inr (by simp)))
  have second : AtomDerivation (comparison := .records) space ([] ++ [] ++ left :: live)
      right Atom.atomType bindings 1 [(right, bindings)] := .leaf _ _ _ _ 0 ((FirstSuccessLeafEvaluation.leaf_gate right Atom.atomType).mpr (Or.inr (by simp)))
  exact .cons_ok left [right] Atom.atomType [Atom.atomType] bindings (left, bindings)
    (argumentPacket [right], bindings) ⟨1, by omega, _, first, by simp⟩ (Or.inr rfl)
    (.cons_ok right [] Atom.atomType [] bindings (right, bindings) (argumentPacket [], bindings)
      ⟨1, by omega, _, second, by simp⟩ (Or.inr rfl) (.nil bindings) (by simp)) (by simp)

theorem empty_chain_cannot_change_record (space : Space) (fuel : Nat)
    (comparison : SourceBindingComparison) (input output : Bindings) (live : List Atom)
    (different : output ≠ input) :
    ¬MachineArgChain space fuel comparison (live := live) [] [] input
      (argumentPacket [], output) := by
  intro derived
  cases derived
  exact different rfl

end TypedApplySourceControls
end Mettapedia.Languages.MeTTa.HE

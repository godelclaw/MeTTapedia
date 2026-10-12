import Mettapedia.Languages.MeTTa.HE.TypedApplyMachine
import Mettapedia.Languages.MeTTa.HE.Correctness

/-!
# Per-position HE evidence and sequential argument chains

Instantiating the typed-apply provenance invariant with `evalAtom` gives
per-position evidence. Each position has either a substitution equality or
an `EvalAtom` derivation. The equality branch is not itself an evaluation
derivation, and the separate existential environments do not establish a
sequential binding chain.

An explicit `MachineArgChain` does supply that chain. Its conversion to
`InterpretArgs` is proved by induction, lifting each computation witness
with `evalAtom_sound`. This file does not construct that chain from every
typed-apply machine execution or establish native interpreter refinement.
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-! ## Provenance to EvalAtom Bridge -/

/-- A single provenance witness for position i, instantiated with evalAtom,
    yields an EvalAtom derivation for that argument.

    The premise here is an actual `evalAtom` result; a substitution equality
    alone does not supply it. -/
theorem provenance_to_evalAtom
    (space : Space) (dispatch : GroundedDispatch)
    (origArg argType evArg : Atom) (env evalEnv : Bindings) (fuel : Nat)
    (h_mem : (evArg, evalEnv) ∈ evalAtom space dispatch
               (Bindings.applyDefault env origArg) argType env fuel) :
    EvalAtom space dispatch (Bindings.applyDefault env origArg) argType env (evArg, evalEnv) :=
  evalAtom_sound space dispatch _ _ _ fuel _ h_mem

/-- At completion, if ProvenanceInvariant holds with eval1 = evalAtom,
    every evaluated arg at position i has either:
    (a) a fast-path justification (was not evaluated, just substituted), or
    (b) an EvalAtom derivation from Correctness.lean's soundness.

    This is the per-position spec bridge. -/
theorem applyComplete_args_sound
    (space : Space) (dispatch : GroundedDispatch) (fuel : Nat)
    (st : TypedApplyState)
    (h_prov : ProvenanceInvariant
      (fun a t b => evalAtom space dispatch a t b fuel)
      (fun b a => Bindings.applyDefault b a)
      st)
    (i : Nat) (hi : i < st.evArgs.length) (ho : i < st.origArgs.length) :
    -- Either fast-path (substitution only)...
    (∃ env, st.evArgs[i] = Bindings.applyDefault env st.origArgs[i]) ∨
    -- ...or has an EvalAtom derivation
    (∃ env argType evalEnv,
      EvalAtom space dispatch
        (Bindings.applyDefault env st.origArgs[i]) argType env
        (st.evArgs[i], evalEnv)) := by
  obtain ⟨_, h_pos⟩ := h_prov
  obtain ⟨env, h_or⟩ := h_pos i hi ho
  rcases h_or with h_fast | ⟨argType, evalEnv, h_mem⟩
  · exact Or.inl ⟨env, h_fast⟩
  · exact Or.inr ⟨env, argType, evalEnv,
      evalAtom_sound space dispatch _ _ _ fuel _ h_mem⟩

/-! ## Per-position evidence at a completed argument state -/

/-- The given completed state has the original argument count, and each
    retained argument has a substitution equality or evaluation derivation.
    These premises do not characterize all emitted calls or construct a
    sequential `InterpretArgs` witness. -/
theorem emission_sound
    (space : Space) (dispatch : GroundedDispatch) (fuel : Nat)
    (st : TypedApplyState)
    (h_prov : ProvenanceInvariant
      (fun a t b => evalAtom space dispatch a t b fuel)
      (fun b a => Bindings.applyDefault b a)
      st)
    (h_done : st.idx ≥ st.origArgs.length)
    (h_wf : st.idx ≤ st.origArgs.length) :
    -- Structure
    st.evArgs.length = st.origArgs.length
    -- Per-position soundness
    ∧ (∀ i (hi : i < st.evArgs.length) (ho : i < st.origArgs.length),
        (∃ env, st.evArgs[i] = Bindings.applyDefault env st.origArgs[i]) ∨
        (∃ env argType evalEnv,
          EvalAtom space dispatch
            (Bindings.applyDefault env st.origArgs[i]) argType env
            (st.evArgs[i], evalEnv))) := by
  have h_len := h_prov.1
  exact ⟨by omega,
         fun i hi ho => applyComplete_args_sound space dispatch fuel st h_prov i hi ho⟩

/-! ## InterpretArgs Assembly

To build a full InterpretArgs derivation tree from per-position EvalAtom
derivations, we need to show the binding chain is consistent: env at
position i+1 is the output bindings from evaluating position i.

The `ProvenanceInvariant` has existential environments per position; it does
not supply this sequential witness. The results below construct a single
argument judgment or consume an explicit `MachineArgChain`. They do not prove
that every typed-apply emission supplies that chain. In particular, the
argument judgment returns tagged argument data, whereas the typed-apply
component emits a call containing its operator. -/

/-- Single-arg soundness: if typedApplyDirect with one arg and evalAtom
    produces a call-term result, that result has a valid EvalAtom derivation
    for the argument. -/
theorem single_arg_sound
    (space : Space) (dispatch : GroundedDispatch) (fuel : Nat)
    (_head arg argType : Atom) (env : Bindings)
    (evArg : Atom) (resultEnv : Bindings)
    (h_eval : (evArg, resultEnv) ∈ evalAtom space dispatch
                (Bindings.applyDefault env arg) argType env fuel) :
    EvalAtom space dispatch (Bindings.applyDefault env arg) argType env (evArg, resultEnv) :=
  evalAtom_sound space dispatch _ _ _ fuel _ h_eval

/-! ## InterpretArgs from EvalAtom: direct construction for known shapes

For a single-arg application where the arg evaluates successfully (not
a changed error), we can construct the InterpretArgs derivation directly.

InterpretArgs.cons_ok requires:
- h_head : EvalAtom ... a t b headResult
- h_head_ok : isEmptyOrError headResult.1 = false ∨ headResult.1 = a
- h_tail : InterpretArgs ... [] [] headResult.2 (argumentPacket [], headResult.2)
- h_tail_ok : argumentsSucceeded (argumentPacket []) = true -/

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

/-! ## Reachability-Indexed Env-Chain Witness

`MachineArgChain` explicitly threads the resulting env of one argument
into the next, mirroring `InterpretArgs`' structure. It uses plain
`EvalAtom` (not the private Sync types from Correctness.lean).

This is the missing bridge: ProvenanceInvariant has existential envs
per position, but InterpretArgs needs the chain. MachineArgChain IS
the chain. -/

/-- A left-to-right env-threading chain for evaluated arguments.
    Mirrors `InterpretArgsAligned` from Correctness.lean but uses
    the public `EvalAtom` relation.

    Each constructor says: "I evaluated arg `a` at type `t` with
    bindings `b`, got `headResult`, and the tail was evaluated
    starting from `headResult.2`." -/
inductive MachineArgChain (space : Space) (dispatch : GroundedDispatch) (fuel : Nat) :
    List Atom → List Atom → Bindings → ResultPair → Prop where
  /-- Base: no arguments left → tagged empty list with current bindings. -/
  | nil (b : Bindings) :
      MachineArgChain space dispatch fuel [] [] b (argumentPacket [], b)
  /-- Head evaluates to changed error → propagate immediately. -/
  | head_changed_error (a : Atom) (as : List Atom) (t : Atom) (ts : List Atom)
      (b : Bindings) (headResult : ResultPair)
      (h_head : ∃ f ≤ fuel, headResult ∈ evalAtom space dispatch a t b f)
      (h_err : isEmptyOrError headResult.1 = true)
      (h_changed : headResult.1 ≠ a) :
      MachineArgChain space dispatch fuel (a :: as) (t :: ts) b headResult
  /-- Head ok, tail evaluates to error → propagate tail error. -/
  | cons_tail_error (a : Atom) (as : List Atom) (t : Atom) (ts : List Atom)
      (b : Bindings) (headResult tailResult : ResultPair)
      (h_head : ∃ f ≤ fuel, headResult ∈ evalAtom space dispatch a t b f)
      (h_head_ok : isEmptyOrError headResult.1 = false ∨ headResult.1 = a)
      (h_tail : MachineArgChain space dispatch fuel as ts headResult.2 tailResult)
      (h_tail_err : argumentsSucceeded tailResult.1 = false) :
      MachineArgChain space dispatch fuel (a :: as) (t :: ts) b tailResult
  /-- Head ok, tail ok → combine into expression. -/
  | cons_ok (a : Atom) (as : List Atom) (t : Atom) (ts : List Atom)
      (b : Bindings) (headResult tailResult : ResultPair)
      (h_head : ∃ f ≤ fuel, headResult ∈ evalAtom space dispatch a t b f)
      (h_head_ok : isEmptyOrError headResult.1 = false ∨ headResult.1 = a)
      (h_tail : MachineArgChain space dispatch fuel as ts headResult.2 tailResult)
      (h_tail_ok : argumentsSucceeded tailResult.1 = true) :
      MachineArgChain space dispatch fuel (a :: as) (t :: ts) b
        (argumentPacket (headResult.1 :: argumentValues tailResult.1), tailResult.2)

/-! ## MachineArgChain → InterpretArgs Conversion -/

/-- Convert a MachineArgChain to an InterpretArgs derivation.
    Each `evalAtom` membership witness is lifted to an `EvalAtom`
    derivation via `evalAtom_sound`. -/
theorem machineArgChain_to_interpretArgs
    (space : Space) (dispatch : GroundedDispatch) (fuel : Nat)
    (args types : List Atom) (b : Bindings) (r : ResultPair)
    (h : MachineArgChain space dispatch fuel args types b r) :
    InterpretArgs space dispatch args types b r := by
  induction h with
  | nil b => exact .nil
  | head_changed_error a as t ts b headResult h_head h_err h_changed =>
    obtain ⟨f, _, hf⟩ := h_head
    exact .head_changed_error a as t ts b headResult
      (evalAtom_sound space dispatch a t b f headResult hf) h_err h_changed
  | cons_tail_error a as t ts b headResult tailResult h_head h_ok _ h_tail_err ih =>
    obtain ⟨f, _, hf⟩ := h_head
    exact .cons_tail_error a as t ts b headResult tailResult
      (evalAtom_sound space dispatch a t b f headResult hf) h_ok ih h_tail_err
  | cons_ok a as t ts b headResult tailResult h_head h_ok _ h_tail_ok ih =>
    obtain ⟨f, _, hf⟩ := h_head
    exact .cons_ok a as t ts b headResult tailResult
      (evalAtom_sound space dispatch a t b f headResult hf) h_ok ih h_tail_ok

end Mettapedia.Languages.MeTTa.HE

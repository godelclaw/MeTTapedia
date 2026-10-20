import Mettapedia.Languages.MeTTa.PeTTa.TypedCallLowering

/-!
# Arity admission before PeTTa call protocols

A complete call consumes every domain of its selected arrow. A partial call
may consume a prefix. The old dispatch used the prefix test for both kinds,
so a longer declaration could execute a complete predicate again.

This module proves the admission filter against an independent judgment and
composes complete-call admission with the existing typed-call lowering. The
equality holds for effectful, nondeterministic, failing and suspended
services. Partial admission is covered separately; its runtime protocol is
not identified with the complete-call protocol. The counterexample observes
body executions, including their multiplicity.

Callability determines the call kind before this boundary. Source lookup,
declaration canonicalization and the SWI/C implementations have executable
conformance tests; this is not a proof of their memory representations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.CallArityDispatch

open CallGuardOptimization TypedCallLowering
open Mettapedia.Machines.OrderedProtocol

inductive Kind where
  | complete
  | underApplied
  deriving DecidableEq, Repr

inductive Applicable (supplied : Nat) : Kind → Signature → Prop where
  | complete {signature : Signature} (allDomains : signature.domains.length = supplied) :
      Applicable supplied .complete signature
  | underApplied {signature : Signature} (within : supplied ≤ signature.domains.length) :
      Applicable supplied .underApplied signature

theorem applicable_iff (supplied : Nat) (kind : Kind) (signature : Signature) :
    Applicable supplied kind signature ↔
      match kind with
      | .complete => signature.domains.length = supplied
      | .underApplied => supplied ≤ signature.domains.length := by
  cases kind <;> constructor
  · intro h; cases h; assumption
  · exact Applicable.complete
  · intro h; cases h; assumption
  · exact Applicable.underApplied

instance (supplied : Nat) (kind : Kind) (signature : Signature) :
    Decidable (Applicable supplied kind signature) := by
  cases kind with
  | complete =>
      exact decidable_of_iff (signature.domains.length = supplied)
        (applicable_iff supplied .complete signature).symm
  | underApplied =>
      exact decidable_of_iff (supplied ≤ signature.domains.length)
        (applicable_iff supplied .underApplied signature).symm

def eligible (kind : Kind) (supplied : Nat) (signature : Signature) : Bool :=
  match kind with
  | .complete => signature.domains.length == supplied
  | .underApplied => decide (supplied ≤ signature.domains.length)

theorem eligible_iff (kind : Kind) (supplied : Nat) (signature : Signature) :
    eligible kind supplied signature = true ↔ Applicable supplied kind signature := by
  rw [applicable_iff]
  cases kind <;> simp [eligible]

/-- Any positional argument derivation consumes the entire domain list.
This does not assume which type judgments or evaluation demands are used. -/
theorem argument_derivation_requires_complete {Value : Type}
    (checks : Value → OSLFCore.Atom → Prop) (values : List Value)
    (signature : Signature) (derivation : List.Forall₂ checks values signature.domains) :
    Applicable values.length .complete signature :=
  .complete derivation.length_eq.symm

theorem wrong_arity_has_no_argument_derivation {Value : Type}
    (checks : Value → OSLFCore.Atom → Prop) (values : List Value)
    (signature : Signature) (wrongArity : signature.domains.length ≠ values.length) :
    ¬ List.Forall₂ checks values signature.domains := by
  intro derivation
  exact wrongArity derivation.length_eq.symm

def select (kind : Kind) (supplied : Nat) (family : List Signature) : List Signature :=
  family.filter (eligible kind supplied)

theorem mem_select (kind : Kind) (supplied : Nat) (signature : Signature)
    (family : List Signature) :
    signature ∈ select kind supplied family ↔
      signature ∈ family ∧ Applicable supplied kind signature := by
  simp [select, eligible_iff]

theorem complete_has_all_domains {supplied : Nat} {signature : Signature}
    {family : List Signature} (selected : signature ∈ select .complete supplied family) :
    signature.domains.length = supplied :=
  (applicable_iff supplied .complete signature).mp ((mem_select ..).mp selected).2

theorem irrelevant_declaration (supplied : Nat) (before after : List Signature)
    (signature : Signature) (wrongArity : signature.domains.length ≠ supplied) :
    select .complete supplied (before ++ signature :: after) =
      select .complete supplied (before ++ after) := by
  simp [select, eligible, wrongArity]

/-- Filtering removes inapplicable occurrences only. It neither sorts the
family nor collapses multiplicities of retained occurrences. -/
theorem occurrence_count (kind : Kind) (supplied : Nat) (signature : Signature)
    (family : List Signature) :
    (select kind supplied family).count signature =
      if eligible kind supplied signature then family.count signature else 0 := by
  by_cases admitted : eligible kind supplied signature = true
  · simp [select, admitted]
  · rw [if_neg admitted]
    apply List.count_eq_zero.mpr
    intro member
    exact admitted ((List.mem_filter.mp member).2)

variable {State World Fault Pause Result : Type}

/-- The source enumerates applicable declarations, composing each complete
protocol with the pending source tail. It never invokes the compiler. -/
def sourceDispatch (services : Services State World Fault Pause Result)
    (held : Bool) (supplied : Nat) :
    List Signature → Kernel State World Fault Pause Result
  | [] => alternatives []
  | signature :: rest =>
      if Applicable supplied .complete signature then
        choice (sourceCall services held signature)
          (sourceDispatch services held supplied rest)
      else sourceDispatch services held supplied rest

def compileDispatch (held : Bool) (supplied : Nat)
    (family : List Signature) : List (List Action) :=
  (select .complete supplied family).map (compileCall held)

/-- Exact equality retains all answer occurrences, world effects and
terminal continuations; it is stronger than equality of answer sets. -/
theorem compileDispatch_exact (services : Services State World Fault Pause Result)
    (held : Bool) (supplied : Nat) (family : List Signature) :
    alternatives ((compileDispatch held supplied family).map (execute services)) =
      sourceDispatch services held supplied family := by
  induction family with
  | nil => rfl
  | cons signature rest ih =>
      by_cases applies : Applicable supplied .complete signature
      · have admitted : eligible .complete supplied signature = true :=
          (eligible_iff ..).mpr applies
        simpa [compileDispatch, select, List.filter_cons, admitted, sourceDispatch,
          applies, alternatives, compileCall_exact] using
          congrArg (choice (sourceCall services held signature)) ih
      · have rejected : eligible .complete supplied signature = false := by
          cases result : eligible .complete supplied signature
          · rfl
          · exact False.elim (applies ((eligible_iff ..).mp result))
        simpa [compileDispatch, select, List.filter_cons, rejected, sourceDispatch,
          applies] using ih

/-- A mismatched declaration cannot add observable execution to a complete
call, even when the underlying services have effects or multiple answers. -/
theorem irrelevant_execution (services : Services State World Fault Pause Result)
    (held : Bool) (supplied : Nat) (before after : List Signature)
    (signature : Signature) (wrongArity : signature.domains.length ≠ supplied) :
    alternatives ((compileDispatch held supplied
        (before ++ signature :: after)).map (execute services)) =
      alternatives ((compileDispatch held supplied
        (before ++ after)).map (execute services)) := by
  simp only [compileDispatch, irrelevant_declaration supplied before after signature wrongArity]

namespace Counterexample

open OSLFCore (Atom)

def unary : Signature := ⟨[.symbol "Number"], .symbol "%Undefined%"⟩
def binary : Signature := ⟨[.symbol "Number", .symbol "Number"], .symbol "%Undefined%"⟩

/-- The old compiler accepted any arrow with at least the supplied domains. -/
def legacySelect (supplied : Nat) (family : List Signature) : List Signature :=
  family.filter (fun signature => decide (supplied ≤ signature.domains.length))

/-- The old argument traversal stops when the actual arguments end, even if
the arrow still has unconsumed domains, then calls the complete predicate. -/
def legacyCompileCall (held : Bool) (supplied : Nat) (signature : Signature) : List Action :=
  .activate signature ::
    (compileArguments 1 (signature.domains.take supplied) ++ [.body held] ++
      (if demand signature.codomain == .checked then [.guardResult] else []) ++ [.publish])

theorem legacy_lowering_agrees_on_applicable_complete_calls
    (held : Bool) (supplied : Nat) (signature : Signature)
    (applicable : Applicable supplied .complete signature) :
    legacyCompileCall held supplied signature = compileCall held signature := by
  have lengthEq := (applicable_iff supplied .complete signature).mp applicable
  simp [legacyCompileCall, compileCall, ← lengthEq]

theorem old_selects_an_inapplicable_declaration :
    binary ∈ legacySelect 1 [unary, binary] ∧ ¬ Applicable 1 .complete binary := by
  simp [legacySelect, unary, binary, applicable_iff]

/-- One selected body has this many real equation derivations. Each body
execution advances an effect counter, and traversal demands every answer. -/
def body (copies : Nat) : Kernel Unit Nat Unit Unit Nat :=
  match copies with
  | 0 => alternatives []
  | copies + 1 => choice
      (fun state success pending _ _ _ world => success state pending (world + 1))
      (body copies)

def services (copies : Nat) : Services Unit Nat Unit Unit Nat
  | .body _ => body copies
  | _ => done

def observe (copies : Nat) (family : List Signature) : Nat :=
  alternatives ((family.map (compileCall false)).map (execute (services copies)))
    () (fun _ pending world => pending world) id id (fun _ => id) (fun _ => id) 0

def observeLegacy (copies supplied : Nat) (family : List Signature) : Nat :=
  alternatives ((family.map (legacyCompileCall false supplied)).map (execute (services copies)))
    () (fun _ pending world => pending world) id id (fun _ => id) (fun _ => id) 0

theorem old_repeats_the_body_and_its_effect :
    observeLegacy 1 1 (legacySelect 1 [unary, binary]) = 2 ∧
      observe 1 (select .complete 1 [unary, binary]) = 1 := by decide

theorem old_violates_irrelevant_declaration_invariance :
    observeLegacy 1 1 (legacySelect 1 [unary]) ≠
      observeLegacy 1 1 (legacySelect 1 [unary, binary]) := by decide

theorem old_protocol_disagrees_with_source :
    alternatives (((legacySelect 1 [unary, binary]).map (legacyCompileCall false 1)).map
      (execute (services 1))) ≠ sourceDispatch (services 1) false 1 [unary, binary] := by
  intro same
  have corrected := compileDispatch_exact (services 1) false 1 [unary, binary]
  have effect := congrArg
    (fun protocol : Kernel Unit Nat Unit Unit Nat =>
      protocol () (fun _ pending world => pending world) id id
        (fun _ => id) (fun _ => id) 0)
    (same.trans corrected.symm)
  change observeLegacy 1 1 (legacySelect 1 [unary, binary]) =
    observe 1 (select .complete 1 [unary, binary]) at effect
  rw [old_repeats_the_body_and_its_effect.1,
    old_repeats_the_body_and_its_effect.2] at effect
  exact (by decide : (2 : Nat) ≠ 1) effect

theorem corrected_dispatch_preserves_two_real_derivations :
    observe 2 (select .complete 1 [unary, binary]) = 2 ∧
      observeLegacy 2 1 (legacySelect 1 [unary, binary]) = 4 := by decide

theorem partial_application_still_admits_the_longer_arrow :
    Applicable 1 .underApplied binary ∧ binary ∈ select .underApplied 1 [binary] := by
  simp [applicable_iff, mem_select, binary]

end Counterexample
end Mettapedia.Languages.MeTTa.PeTTa.CallArityDispatch

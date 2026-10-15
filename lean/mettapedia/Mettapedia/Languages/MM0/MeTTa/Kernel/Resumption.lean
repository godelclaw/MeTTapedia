import Mettapedia.Languages.MM0.MeTTa.Kernel.Proof
import Mettapedia.Languages.MeTTa.PeTTa.Resumption

/-!
# Resumption of the actual authored MM0 proof checker

The source program, tables, request configuration and logical witness judgment
are the existing ones. This connects that whole-checker correspondence to the
configuration resumption law. A pause retains the original invocation; an
eventual answer earns the same exact claim judgment as uninterrupted execution.

This is a theorem about the retained PeTTa source machine. Native Prime
translation and a native dependent proof representation require their own
correspondence; these results do not silently assert either of them.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.Proof

open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Kernel (Context Preterm ProofWitness)
open Presentation.ComputationalTyping (signatureOf)
open ProofResults (resultValue)

/-- Any finite prefix budget may be used. The remaining computation, or the
already terminal answer, yields precisely the original MM0 checking judgment. -/
theorem checks_iff_resumed_source (tables : Tables) (context : Context)
    (witness : ProofWitness) (before : Effects.State) (ready : Ready tables before)
    (claim : Preterm) (first : Nat) :
    ProofWitness.Checks (signatureOf tables.entries)
      (Unfolding.definitionSignature tables.bodies) (theoremSignature tables.declarations)
      context tables.values witness claim ↔
      ∃ after second, resume program second
        (run program first (requestConfiguration before tables context witness)) =
          .complete after [resultValue (some claim)] [] [] := by
  rw [checks_iff_source_returns tables context witness before ready claim]
  constructor
  · rintro ⟨after, fuel, finished⟩
    refine ⟨after, fuel, ?_⟩
    rw [resume_run, Nat.add_comm]
    exact completed_run_more_fuel program fuel first _ after _ [] [] finished
  · rintro ⟨after, second, finished⟩
    rw [resume_run] at finished
    exact ⟨after, first + second, finished⟩

/-- A genuinely paused checker, not a claimed result, continues under its
original program and invocation indices. Completion reconstructs admission. -/
theorem paused_completion_checks (tables : Tables) (context : Context)
    (witness : ProofWitness) (before : Effects.State) (ready : Ready tables before)
    (first : Nat)
    (paused : PausedExecution program (requestConfiguration before tables context witness) first)
    (after : Effects.State) (claim : Preterm) (second : Nat)
    (completed : paused.continueWith second =
      .complete after [resultValue (some claim)] [] []) :
    ProofWitness.Checks (signatureOf tables.entries)
      (Unfolding.definitionSignature tables.bodies) (theoremSignature tables.declarations)
      context tables.values witness claim := by
  apply (checks_iff_source_returns tables context witness before ready claim).mpr
  exact ⟨after, first + second, paused.continueWith_eq_run second ▸ completed⟩

/-- The resumed answer also has a path in the independently declared GSLT.
Its endpoints include the original tables, context, witness and exact claim. -/
theorem paused_completion_path (tables : Tables) (context : Context)
    (witness : ProofWitness) (before : Effects.State)
    (first : Nat)
    (paused : PausedExecution program (requestConfiguration before tables context witness) first)
    (after : Effects.State) (claim : Preterm) (second : Nat)
    (completed : paused.continueWith second =
      .complete after [resultValue (some claim)] [] []) :
    (Eval.theory program).MultiStep (requestConfiguration before tables context witness)
      (finished after [resultValue (some claim)] [] []) := by
  apply completed_run_has_path program (first + second)
  exact paused.continueWith_eq_run second ▸ completed

/-- The existing declaration-aware certificate checker and a split execution
of the real authored program admit the same claim. Signature and store
authorization are displayed exactly as in the original correspondence. -/
theorem certificate_accepted_iff_resumed_source (theory : Kernel.Theory)
    (tables : Tables) (terms : tables.entries = theory.terms)
    (definitions : tables.bodies = theory.definitions)
    (theorems : tables.declarations = theory.theorems)
    (context : Context) (witness : ProofWitness) (before : Effects.State)
    (ready : Ready tables before) (claim : Preterm) (first : Nat) :
    (∃ fuel, Mettapedia.GSLT.LanguageDef.InferenceComputedLeaves.check
      Presentation.Calculus.kernelCalculus (Presentation.Calculus.family theory).evaluate
      (Presentation.Calculus.derivesJ context tables.values claim)
      (Presentation.Calculus.Witness.translate theory fuel context tables.values witness) = true) ↔
      ∃ after second, resume program second
        (run program first (requestConfiguration before tables context witness)) =
          .complete after [resultValue (some claim)] [] [] := by
  rw [certificate_accepted_iff_petta_judgment theory tables terms definitions theorems
    context witness before ready claim]
  have original := checks_iff_petta_judgment tables context witness before ready claim
  exact original.symm.trans
    (checks_iff_resumed_source tables context witness before ready claim first)

end Mettapedia.Languages.MM0.MeTTa.Proof

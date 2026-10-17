import Mathlib.Computability.PartrecCode

/-!
# The whole partial-recursive graph has finite, effectively checked evidence

This module takes an ACTUAL finite `Nat.Partrec.Code` as input. It wraps the
existing bounded evaluator, rather than accepting an opaque semantic predicate
as the implementation of a universal checker. The universal theorem is about
graphs of partial recursive functions. An effectively presented judgment system
is included after its recognizer/validator has been encoded by such a code.

The evaluation bound is NOT a time budget: `evaln` bounds values encountered by
its particular evaluation scheme. There is no polynomial claim in the bit size
of that bound. `OriginalMachineTrace` is the separate supplied-run interface.

This is an arithmetic/Lean-side evidence construction. The direct HOL/MM0
realizations, source-admission compiler and declaration-history joins are NOT
implemented by these small wrapper lemmas. They remain explicit obligations.
-/

set_option autoImplicit false
namespace Mettapedia.Computability.UniversalEffectiveEvidence

abbrev Code := Nat.Partrec.Code

/-- This verifier terminates for every finite code, input and supplied bound.
Acceptance refers to the supplied output, not to mere evaluator termination. -/
def check (code : Code) (input output bound : Nat) : Bool :=
  decide (output ∈ Nat.Partrec.Code.evaln bound code input)

/-- The bounded evaluator is the existing primitive-recursive interpreter.
This theorem is about the evaluator, not a bound on its running time. -/
theorem bounded_evaluator_primitive_recursive :
    Primrec (fun value : (Nat × Code) × Nat =>
      Nat.Partrec.Code.evaln value.1.1 value.1.2 value.2) :=
  Nat.Partrec.Code.primrec_evaln

theorem check_sound (code : Code) (input output bound : Nat)
    (accepted : check code input output bound = true) :
    output ∈ Nat.Partrec.Code.eval code input :=
  Nat.Partrec.Code.evaln_sound (of_decide_eq_true accepted)

/-- No global halting decision or checker-totality proof is needed to validate
one terminating computation. The finite witness exists exactly for results. -/
theorem graph_iff_evidence (code : Code) (input output : Nat) :
    output ∈ Nat.Partrec.Code.eval code input ↔
      ∃ bound, check code input output bound = true := by
  constructor
  · intro computed
    obtain ⟨bound, bounded⟩ := Nat.Partrec.Code.evaln_complete.mp computed
    exact ⟨bound, decide_eq_true bounded⟩
  · rintro ⟨bound, accepted⟩
    exact check_sound code input output bound accepted

/-- Increasing this evaluator's bound preserves an observed result; this does
not identify the two evaluation costs or authorize reuse under another code. -/
theorem check_mono (code : Code) (input output first second : Nat)
    (increased : first ≤ second) (accepted : check code input output first = true) :
    check code input output second = true :=
  decide_eq_true (Nat.Partrec.Code.evaln_mono increased (of_decide_eq_true accepted))

/-- Every partial recursive function has a finite-code checking presentation.
`exists_code` supplies mathematical existence. This is NOT an executable
compiler from arbitrary Lean functions or an automatic synthesis procedure. -/
theorem every_partial_recursive_graph {function : Nat →. Nat}
    (effective : Nat.Partrec function) :
    ∃ code : Code, ∀ input output,
      output ∈ function input ↔ ∃ bound, check code input output bound = true := by
  obtain ⟨code, implementation⟩ := Nat.Partrec.Code.exists_code.mp effective
  refine ⟨code, ?_⟩
  intro input output
  rw [← implementation]
  exact graph_iff_evidence code input output

/-- A countable/r.e. declaration family is accessed by an enumeration index
and finite evaluation evidence, not by trusting membership in an infinite set.
The resulting raw declaration still has to pass its source admission checker. -/
def declarationMember (enumerator : Code) (declaration : Nat)
    (witness : Nat × Nat) : Bool :=
  check enumerator witness.1 declaration witness.2

theorem declaration_member_iff (enumerator : Code) (declaration : Nat) :
    (∃ witness, declarationMember enumerator declaration witness = true) ↔
      ∃ index, declaration ∈ Nat.Partrec.Code.eval enumerator index := by
  constructor
  · rintro ⟨⟨index, bound⟩, accepted⟩
    exact ⟨index, check_sound enumerator index declaration bound accepted⟩
  · rintro ⟨index, enumerated⟩
    obtain ⟨bound, accepted⟩ :=
      (graph_iff_evidence enumerator index declaration).mp enumerated
    exact ⟨(index, bound), accepted⟩

end Mettapedia.Computability.UniversalEffectiveEvidence

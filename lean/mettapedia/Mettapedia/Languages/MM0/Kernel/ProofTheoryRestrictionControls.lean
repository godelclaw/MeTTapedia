import Mettapedia.Languages.MM0.Kernel.ProofTheoryRestriction

/-!
# Used and unused theorem entries in actual MM0 proof checking

A two-step witness uses two declarations and retains its ordered child proof.
The controls change the unused declaration, the used child declaration and
the theorem policy independently. A local hypothesis is retained as an
assumption rather than reported as an imported theorem dependency.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.Kernel.ProofTheoryRestrictionControls
open ProofWitness

private def terms : TermSignature
  | 0 | 1 => some ⟨[], 0, ∅⟩
  | _ => none

private def theorems : TheoremSignature
  | 10 => some ⟨[], [], .term 0⟩
  | 11 => some ⟨[], [.term 0], .term 1⟩
  | 12 => some ⟨[], [], .term 1⟩
  | _ => none

private def proof : ProofWitness := .theoremApp 11 [] [.theoremApp 10 [] []]
private def policy (index : Nat) : Bool := index != 12

theorem exact_references : theoremReferences proof = [11, 10] := by decide +kernel

theorem original_accepted : check terms (fun _ => none) theorems [] [] proof (.term 1) = true := by decide +kernel

theorem restricted_accepted :
    check terms (fun _ => none) (restrictedTheorems policy theorems) [] [] proof (.term 1) = true :=
  (restricted_check_iff policy proof (.term 1)).mpr
    ⟨original_accepted, by intro index member; simp only [exact_references, List.mem_cons, List.not_mem_nil,
      or_false] at member; rcases member with rfl | rfl <;> rfl⟩

theorem changed_conclusion_refused :
    check terms (fun _ => none) theorems [] [] proof (.term 0) = false := by decide +kernel

theorem denied_child_refused :
    check terms (fun _ => none) (restrictedTheorems (fun index => index != 10) theorems)
      [] [] proof (.term 1) = false :=
  disallowed_reference_refused (fun index => index != 10) proof (.term 1) (index := 10)
    (by simp [exact_references]) rfl

private def changedUnused (index : Nat) : Option TheoremDecl :=
  if index = 12 then some ⟨[], [], .term 0⟩ else theorems index

theorem unused_change_preserves :
    check terms (fun _ => none) changedUnused [] [] proof (.term 1) = true :=
  (check_iff_of_theorem_agreement changedUnused proof (.term 1) (by
    intro index member
    simp only [exact_references, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl)).mpr original_accepted

private def changedUsed (index : Nat) : Option TheoremDecl :=
  if index = 10 then some ⟨[], [], .term 1⟩ else theorems index

theorem used_change_refused :
    check terms (fun _ => none) changedUsed [] [] proof (.term 1) = false := by decide +kernel

private def fromAssumption : ProofWitness := .theoremApp 11 [] [.hyp 0]

theorem local_assumption_retained :
    theoremReferences fromAssumption = [11] ∧
      check terms (fun _ => none) (restrictedTheorems (fun index => index == 11) theorems)
        [] [.term 0] fromAssumption (.term 1) = true ∧
      check terms (fun _ => none) theorems [] [] fromAssumption (.term 1) = false := by decide +kernel

#print axioms original_accepted
#print axioms restricted_accepted
#print axioms denied_child_refused
#print axioms unused_change_preserves
#print axioms used_change_refused
#print axioms local_assumption_retained
end Mettapedia.Languages.MM0.Kernel.ProofTheoryRestrictionControls

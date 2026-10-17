import Mettapedia.Logic.InferenceBasisCompiler
import Mettapedia.Logic.InferenceBasisControls

/-!
# Compiling one irredundant basis into another

The source uses zero and successor. The target uses one, predecessor and
add-two. Zero expands to predecessor(one); successor expands to
predecessor(add-two(the supplied premise)). The templates are concrete,
computable certificates replayed by independently defined rule checkers.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.InferenceBasisCompiler.Controls

open InferenceBasis.Controls (Operation family first second)

def localCheck : Operation → List Nat → Nat → Bool
  | .zero, premises, result => decide (premises = [] ∧ result = 0)
  | .one, premises, result => decide (premises = [] ∧ result = 1)
  | .successor, [n], result => decide (result = n + 1)
  | .predecessor, [n], result => decide (n = result + 1)
  | .addTwo, [n], result => decide (result = n + 2)
  | _, _, _ => false

theorem localCheck_exact (operation : Operation) (premises : List Nat) (result : Nat) :
    localCheck operation premises result = true ↔ family operation premises result := by
  cases operation <;> cases premises with
  | nil => simp [localCheck, family]
  | cons first rest => cases rest <;> simp [localCheck, family, eq_comm]

def rules (basis : Finset Operation) (premises : List Nat) (result : Nat) : Prop :=
  ∃ operation ∈ basis, family operation premises result

def target : RuleWitness (rules second) where
  W := Operation
  isInstance operation premises result := decide (operation ∈ second) && localCheck operation premises result
  sound operation premises result accepted := by
    have parts := Bool.and_eq_true_iff.mp accepted
    exact ⟨operation, of_decide_eq_true parts.1, (localCheck_exact _ _ _).mp parts.2⟩
  complete premises result instanceRule := by
    obtain ⟨operation, member, ruleInstance⟩ := instanceRule
    exact ⟨operation, by simp [member, (localCheck_exact _ _ _).mpr ruleInstance]⟩

def source : RuleWitness (rules first) where
  W := Bool
  isInstance witness premises result := localCheck (if witness then .successor else .zero) premises result
  sound witness premises result accepted := by
    cases witness
    · exact ⟨.zero, by simp [first], (localCheck_exact _ _ _).mp accepted⟩
    · exact ⟨.successor, by simp [first], (localCheck_exact _ _ _).mp accepted⟩
  complete premises result instanceRule := by
    obtain ⟨operation, member, ruleInstance⟩ := instanceRule
    have cases : operation = .zero ∨ operation = .successor := by simpa [first] using member
    rcases cases with rfl | rfl
    · exact ⟨false, (localCheck_exact _ _ _).mpr ruleInstance⟩
    · exact ⟨true, (localCheck_exact _ _ _).mpr ruleInstance⟩

def zeroTemplate (n result : Nat) : Derivation Nat (Fin n ⊕ Operation) :=
  .node result (.inr .predecessor) 1 (fun _ =>
    .node 1 (.inr .one) 0 Fin.elim0)

def successorTemplate {n : Nat} (premises : Fin (n + 1) → Nat) (result : Nat) :
    Derivation Nat (Fin (n + 1) ⊕ Operation) :=
  .node result (.inr .predecessor) 1 (fun _ =>
    .node (premises 0 + 2) (.inr .addTwo) 1 (fun _ =>
      .node (premises 0) (.inl 0) 0 Fin.elim0))

def template (n : Nat) (witness : Bool) (premises : Fin n → Nat) (result : Nat) :
    Derivation Nat (Fin n ⊕ Operation) :=
  if witness then
    match n with
    | 0 => zeroTemplate 0 result
    | _ + 1 => successorTemplate premises result
  else zeroTemplate n result

theorem template_concl (n : Nat) (witness : Bool) (premises : Fin n → Nat) (result : Nat) :
    (template n witness premises result).concl = result := by
  cases witness <;> cases n <;> rfl

theorem template_valid (n : Nat) (witness : Bool) (premises : Fin n → Nat) (result : Nat)
    (accepted : source.isInstance witness (List.ofFn premises) result = true) :
    (template n witness premises result).valid (openWitness target premises) = true := by
  cases witness with
  | false =>
      have resultZero : result = 0 := by simpa [source, localCheck] using (of_decide_eq_true accepted).2
      subst result
      simp [template, zeroTemplate, Derivation.valid, Derivation.concl, openWitness, target,
        localCheck, second]
  | true =>
      obtain ⟨value, ps, same⟩ := (localCheck_exact .successor _ _).mp accepted
      have length := congrArg List.length ps
      simp only [List.length_ofFn, List.length_singleton] at length
      subst n
      have valueEq : premises 0 = value := by
        have head := congrArg (fun xs => xs[0]?) ps
        simpa using head
      subst result
      simp [template, successorTemplate, Derivation.valid, Derivation.concl, openWitness,
        target, localCheck, second, valueEq]

def compiler : Compiler source target where
  template := template
  template_valid := template_valid
  template_concl n witness premises result _ := template_concl n witness premises result

def sourceProof : Nat → Derivation Nat Bool
  | 0 => .node 0 false 0 Fin.elim0
  | n + 1 => .node (n + 1) true 1 (fun _ => sourceProof n)

theorem sourceProof_concl (n : Nat) : (sourceProof n).concl = n := by cases n <;> rfl

theorem sourceProof_valid (n : Nat) : (sourceProof n).valid source = true := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
      change (source.isInstance true [(sourceProof n).concl] (n + 1) &&
        ([(sourceProof n).valid source]).all id) = true
      rw [sourceProof_concl]
      apply Bool.and_eq_true_iff.mpr
      exact ⟨by simp [source, localCheck], by simpa using ih⟩

theorem every_number_compiles (n : Nat) :
    (compiler.compile (sourceProof n)).valid target = true ∧
      (compiler.compile (sourceProof n)).concl = n := by
  have compiled := compiler.compile_correct _ (sourceProof_valid n)
  exact ⟨compiled.1, compiled.2.trans (sourceProof_concl n)⟩

theorem sourceProof_nodes (n : Nat) : nodes (sourceProof n) = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change 1 + (nodes (sourceProof n) + 0) = n + 1 + 1
      omega

/-- This concrete compiler doubles the tree-node count. This is not a byte
bound or a runtime theorem; the payloads remain the original natural numbers. -/
theorem compiled_nodes (n : Nat) : nodes (compiler.compile (sourceProof n)) = 2 * (n + 1) := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
      change 1 + ((1 + (nodes (compiler.compile (sourceProof n)) + 0)) + 0) = 2 * (n + 1 + 1)
      omega

theorem concrete_two_accepted :
    (compiler.compile (sourceProof 2)).valid target = true := by decide +kernel

theorem bad_source_claim_rejected :
    (Derivation.node 1 false 0 Fin.elim0).valid source = false := by decide +kernel

theorem bad_target_predecessor_rejected :
    (Derivation.node 2 Operation.predecessor 1 (fun _ =>
      Derivation.node 1 Operation.one 0 Fin.elim0)).valid target = false := by decide +kernel

end Mettapedia.Logic.InferenceBasisCompiler.Controls

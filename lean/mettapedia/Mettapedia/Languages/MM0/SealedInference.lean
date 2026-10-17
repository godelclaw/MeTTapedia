import Mettapedia.Languages.MM0.Kernel.BorrowedProofCursor
import Mettapedia.Languages.MM0.Kernel.DefinitionFreeConversion
import Mettapedia.Languages.MeTTa.Seal.NativeContract

/-!
# MM0 inference under the shared native seal policy

The issuing policy is indexed by the actual MM0 scope: signatures,
definitions, context and hypotheses. A reached theorem capsule therefore
has a derivation in that scope and a replayable graph of native local rules.
The policy does not authorize arbitrary untrusted helper equations.

This is a source-level consequence of private minting and checked rule
admission. Native expression ownership, conversion-handle authentication,
failure-atomic publication and binary decoding remain separate implementation
obligations. Changing a scope requires an explicit admission or transport law.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.SealedInference

open Kernel Kernel.BorrowedProofCursor
open Mettapedia.Languages.MeTTa
open Mettapedia.Logic.DerivationGraph

theorem capsule_has_original (scope : Scope)
    {kernel brand identity principal : Nat}
    {initial final : Seal.NativeContract.Config Preterm} {claim : Preterm}
    (start : Seal.KernelStart (Rules scope) kernel brand initial.erase)
    (reached : Seal.NativeContract.Reach
      (Seal.kernelPolicy (Rules scope) kernel brand) initial final)
    (held : Seal.NativeContract.Value.box identity brand (.data claim) ∈ final.holds principal) :
    Kernel.Derives scope.signature scope.definitions scope.theorems scope.context
      scope.hypotheses claim :=
  (derives_iff_original scope claim).mp
    (Seal.NativeContract.lcf_original (Rules scope) start reached held)

theorem capsule_has_graph (scope : Scope)
    {kernel brand identity principal : Nat}
    {initial final : Seal.NativeContract.Config Preterm} {claim : Preterm}
    (start : Seal.KernelStart (Rules scope) kernel brand initial.erase)
    (reached : Seal.NativeContract.Reach
      (Seal.kernelPolicy (Rules scope) kernel brand) initial final)
    (held : Seal.NativeContract.Value.box identity brand (.data claim) ∈ final.holds principal) :
    ∃ (nodes : List (Node Preterm Witness Nat)) (cache : Array Preterm) (root : Nat),
      replay (interface scope) nodes = some cache ∧ cache[root]? = some claim :=
  (original_iff_graph scope claim).mp (capsule_has_original scope start reached held)

theorem source_impossible_excludes_capsule (scope : Scope)
    {kernel brand identity principal : Nat}
    {initial final : Seal.NativeContract.Config Preterm} {claim : Preterm}
    (start : Seal.KernelStart (Rules scope) kernel brand initial.erase)
    (reached : Seal.NativeContract.Reach
      (Seal.kernelPolicy (Rules scope) kernel brand) initial final)
    (impossible : ¬ Kernel.Derives scope.signature scope.definitions scope.theorems scope.context
      scope.hypotheses claim) :
    Seal.NativeContract.Value.box identity brand (.data claim) ∉ final.holds principal :=
  fun held => impossible (capsule_has_original scope start reached held)

namespace WritableEndpoints

/-- The former boundary accepted caller-supplied endpoints after checking
only that the existing proof had the supplied left endpoint. -/
structure SubmittedConversion where
  left : Preterm
  right : Preterm
  sort : Nat

def applyUnchecked (proofConclusion : Preterm) (conversion : SubmittedConversion) :
    Option Preterm :=
  if proofConclusion = conversion.left then some conversion.right else none

def scope : Scope where
  signature := fun name => if name < 2 then some ⟨[], 0, ∅⟩ else none
  definitions := fun _ => none
  theorems := fun _ => none
  context := []
  hypotheses := [.term 0]

theorem genuine_hypothesis_checks :
    ProofWitness.check scope.signature scope.definitions scope.theorems scope.context
      scope.hypotheses (.hyp 0) (.term 0) = true := by decide +kernel

theorem original_only_hypothesis {claim : Preterm}
    (derived : Kernel.Derives scope.signature scope.definitions scope.theorems
      scope.context scope.hypotheses claim) : claim = .term 0 := by
  apply Mettapedia.Logic.Derives.least (fun expression => expression = .term 0)
    _ ((derives_iff_original scope claim).mpr derived)
  intro premises conclusion rule earlier
  cases rule with
  | hypothesis found =>
      simpa [scope] using List.mem_of_getElem? found
  | theoremApp known _ => simp [scope] at known
  | @conversion left right sort converted =>
      have same := converted.eq_of_no_definitions (fun _ => rfl)
      exact same ▸ earlier left (by simp)

/-- Both endpoint constants are well typed, but their writable pair can
forge a conclusion that the original source rules cannot derive. -/
theorem writable_pair_forges :
    Preterm.infer scope.signature scope.context (.term 0) = some ([], 0) ∧
    Preterm.infer scope.signature scope.context (.term 1) = some ([], 0) ∧
    applyUnchecked (.term 0) ⟨.term 0, .term 1, 0⟩ = some (.term 1) ∧
    ¬ Kernel.Derives scope.signature scope.definitions scope.theorems scope.context
      scope.hypotheses (.term 1) := by
  refine ⟨by decide +kernel, by decide +kernel, rfl, ?_⟩
  intro derived
  have impossible := original_only_hypothesis derived
  cases impossible

theorem corrected_policy_excludes_forgery
    {kernel brand identity principal : Nat}
    {initial final : Seal.NativeContract.Config Preterm}
    (start : Seal.KernelStart (Rules scope) kernel brand initial.erase)
    (reached : Seal.NativeContract.Reach
      (Seal.kernelPolicy (Rules scope) kernel brand) initial final) :
    Seal.NativeContract.Value.box identity brand (.data (.term 1)) ∉ final.holds principal :=
  source_impossible_excludes_capsule scope start reached writable_pair_forges.2.2.2

end WritableEndpoints

#print axioms capsule_has_original
#print axioms capsule_has_graph
#print axioms source_impossible_excludes_capsule
#print axioms WritableEndpoints.writable_pair_forges
#print axioms WritableEndpoints.corrected_policy_excludes_forgery

end Mettapedia.Languages.MM0.SealedInference

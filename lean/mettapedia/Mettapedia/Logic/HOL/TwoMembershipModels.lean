import Mettapedia.Logic.HOL.ContextualTrinity
import Mettapedia.Logic.HOL.Semantics.StandardTransport
import Mettapedia.TypeTheory.MaterialSets.Hypersets.CodedFamilies

/-!
# Host membership and hyperset membership on the extensional face of the HOL kernel

One HOL signature has a single constant `mem : ι ⇒ ι ⇒ prop`. Three standard
models interpret it:

* the host model: well-founded sets with their own membership
  (`hostModel`);
* the hyperset model: anti-founded sets with theirs (`hypersetModel`);
* the code model: the host's sets that code hypersets, with the interpreted
  membership `codeMem` read through the decoder (`codeModel`). Its carrier is
  host data and its host membership is irreflexive, but its interpreted
  membership is the hyperset one.

The sentence `∃x. mem x x` separates the memberships: it is false in the host
model (`host_refutes_selfMember`) and true in the hyperset model and in the code
model (`hyperset_satisfies_selfMember`, `code_satisfies_selfMember`). The code
model and the hyperset model satisfy exactly the same closed formulas
(`code_models_iff_hyperset`): the decoder transports the interpreted membership,
so no HOL sentence sees that the code carrier is made of host sets.

On the kernel side (`ContextualTrinity`), each model is an extensional face of
the same operational and intensional faces. A retained proof is sound in every
one of them, so the kernel proves neither `∃x. mem x x` nor its negation
(`selfMember_independent`). Which membership is meant is a choice of
extensional face, invisible to proofs; what the proofs fix is what all the
faces share.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.TwoMembershipModels

open Mettapedia.TypeTheory.MaterialSets.Hypersets
open Mettapedia.Logic.HOL.StandardTransport

/-- One base type of sets. -/
abbrev ι : Ty Unit := .base ()

/-- The signature of membership. `mem a b` reads `a ∈ b`. -/
inductive MembershipConst : Ty Unit → Type where
  | mem : MembershipConst (ι ⇒ ι ⇒ .prop)

/-- Interpret membership in a carrier with a membership relation. -/
def interpret {Carrier : Type 1} (member : Carrier → Carrier → Prop) :
    {τ : Ty Unit} → MembershipConst τ → Ty.denote.{0, 0} (fun _ : Unit => Carrier) τ
  | _, .mem => fun element collection => ULift.up (member element collection)

/-- Well-founded host sets with host membership. -/
noncomputable def hostModel : HenkinModel.{0, 0, 0} Unit MembershipConst :=
  HenkinModel.standard (fun _ => ZFSet.{0}) (interpret (fun element collection => element ∈ collection))

/-- Hypersets with their membership. -/
noncomputable def hypersetModel : HenkinModel.{0, 0, 0} Unit MembershipConst :=
  HenkinModel.standard (fun _ => HSet.{0}) (interpret (fun element collection => element ∈ collection))

/-- Host codes of hypersets, with the interpreted membership. -/
noncomputable def codeModel : HenkinModel.{0, 0, 2} Unit MembershipConst :=
  HenkinModel.standard (fun _ => CodedFamilies.Code.{0})
    (fun {τ} constant => match τ, constant with
      | _, .mem => fun element collection =>
          ULift.up (codeMem collection.1 element.1))

/-- `∃x. x ∈ x`. -/
def selfMember : ClosedFormula MembershipConst :=
  .ex (.app (.app (.const .mem) (.var .vz)) (.var .vz))

theorem host_refutes_selfMember : ¬ HenkinModel.models hostModel selfMember := by
  rintro ⟨element, _, member⟩
  exact ZFSet.mem_irrefl element member

theorem hyperset_satisfies_selfMember : HenkinModel.models hypersetModel selfMember :=
  ⟨HSet.quineAtom, trivial, HSet.quineAtom_mem_self⟩

theorem code_satisfies_selfMember : HenkinModel.models codeModel selfMember :=
  ⟨CodedFamilies.encode HSet.quineAtom, trivial, CodedFamilies.quine_codeMem_self⟩

/-- The witness of self-membership in the code model is not a host
self-member. -/
theorem code_witness_not_host_selfMember :
    (CodedFamilies.encode HSet.quineAtom.{0}).1 ∉ (CodedFamilies.encode HSet.quineAtom.{0}).1 :=
  CodedFamilies.hostCode_not_mem_self _

/-- **The code model and the hyperset model satisfy the same closed
formulas.** The decoder carries the interpreted membership to hyperset
membership. -/
theorem code_models_iff_hyperset (formula : ClosedFormula MembershipConst) :
    HenkinModel.models codeModel formula ↔ HenkinModel.models hypersetModel formula := by
  apply models_transport hypersetModel codeModel
    (HenkinModel.fullDomains_standard _ _) (HenkinModel.fullDomains_standard _ _)
    (fun _ => CodedFamilies.carrierEquiv.symm)
  intro τ constant
  cases constant
  funext element collection
  apply ULift.ext
  rfl

/-- Both standard models respect extensional equality. -/
theorem hostModel_respects : hostModel.FunctionsRespectEqv :=
  HenkinModel.functionsRespectEqv_of_fullDomains _ (HenkinModel.fullDomains_standard _ _)

theorem hypersetModel_respects : hypersetModel.FunctionsRespectEqv :=
  HenkinModel.functionsRespectEqv_of_fullDomains _ (HenkinModel.fullDomains_standard _ _)

/-- A retained proof of a closed sentence holds in a model of the trinity's
extensional face. -/
theorem proof_models {M : HenkinModel.{0, 0, 0} Unit MembershipConst}
    (respects : M.FunctionsRespectEqv) {sentence : ClosedFormula MembershipConst}
    (proof : ProofSyntax MembershipConst [] sentence) : HenkinModel.models M sentence :=
  Soundness.extDerivation_sound proof.erase respects (fun index => nomatch index)
    (fun _ member => nomatch member)

/-- **The kernel proves neither `∃x. x ∈ x` nor its negation.** -/
theorem selfMember_independent :
    IsEmpty (ProofSyntax MembershipConst [] selfMember) ∧
      IsEmpty (ProofSyntax MembershipConst [] (.not selfMember)) :=
  ⟨⟨fun proof => host_refutes_selfMember (proof_models hostModel_respects proof)⟩,
    ⟨fun proof => (proof_models hypersetModel_respects proof) hyperset_satisfies_selfMember⟩⟩

/-- The same independence through the trinity: no element of the intensional
face at the empty context proves either sentence, because soundness into the
host face and into the hyperset face would disagree. -/
theorem no_logic_element_decides_selfMember
    (proved : ContextualTrinity.ProvedSequent (Const := MembershipConst) []) :
    proved.1 ≠ ([], selfMember) ∧ proved.1 ≠ ([], .not selfMember) := by
  obtain ⟨⟨hypotheses, conclusion⟩, proof⟩ := proved
  constructor
  · intro same
    cases same
    exact selfMember_independent.1.false proof
  · intro same
    cases same
    exact selfMember_independent.2.false proof

#print axioms code_models_iff_hyperset
#print axioms selfMember_independent
#print axioms no_logic_element_decides_selfMember

end Mettapedia.Logic.HOL.TwoMembershipModels

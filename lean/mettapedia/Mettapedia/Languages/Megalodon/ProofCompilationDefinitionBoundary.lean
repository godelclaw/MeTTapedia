import Mettapedia.Languages.Megalodon.ProofJudgment
import Mettapedia.Languages.Megalodon.ProofCompilation
import Mettapedia.Languages.Megalodon.RetainedDefinitionControls

/-!
# Definition-unfolding boundary of retained proof compilation

A typed self-referential definition does not guarantee that its reflexivity
proof compiles into an accepted native proof. The actual compiled program is
rejected at every budget because argument unfolding exhausts that budget.
The corresponding program is accepted with the same name declared opaque.

This separates source derivability from native definition policy. It does not
refute a compiler theorem for an admitted terminating or opaque profile, and
it concerns definition unfolding rather than cyclic material membership.
-/

set_option autoImplicit false

open Mettapedia.Logic.HOL
open Mettapedia.Languages.Megalodon
open MathdataKernel HenkinTermInterpretation RetainedDefinitionControls

namespace Mettapedia.Languages.Megalodon.ProofCompilationDefinitionBoundary

/-- Acceptance of compiled source reflexivity forces the native argument's
delta phase to finish at the same budget. This is a necessary condition on
the admitted fragment, derived from the actual Boolean checker. -/
theorem compiled_reflexivity_requires_delta {environment : Environment}
    {gamma : Ctx Base} {type : Ty Base} {fuel depth : Nat} {hypotheses : List Tm}
    (term : Term (Constant environment) gamma type)
    (functional : Tp → Tp → Pf) (propositional : Pf)
    (accepted : checkProof environment fuel depth (gamma.map reifyType) hypotheses
      (ProofCompilation.compile functional propositional
        (.eqRefl term : ProofSyntax (Constant environment)
          ([] : List (Formula (Constant environment) gamma)) (.eq term term)))
      (HOLTermEncoding.native (.eq term term)) = true) :
    ∃ expanded, deltaNormalize environment fuel (HOLTermEncoding.native term) = some expanded := by
  obtain ⟨normal, _, derived⟩ :=
    (ProofJudgment.check_iff environment fuel ⟨depth, gamma.map reifyType, hypotheses⟩ _ _).mp accepted
  change ProofJudgment.Proves environment fuel ⟨depth, gamma.map reifyType, hypotheses⟩
    (.termApp (RelationEqualityProofs.reflexivity (reifyType type))
      (HOLTermEncoding.native term)) normal at derived
  cases derived with
  | termApp _ _ expanded _ => exact ⟨_, expanded⟩

def loopReflexivity : Pf :=
  .termApp (RelationEqualityProofs.reflexivity .prop) (.named "loop")

theorem cyclic_argument_rejected (fuel : Nat) :
    inferProof Cyclic.environment fuel 0 [] [] loopReflexivity = none := by
  cases computed : inferProof Cyclic.environment fuel 0 [] [] loopReflexivity with
  | none => rfl
  | some output =>
      have derived := ProofJudgment.proves_of_infer (context := ⟨0, [], []⟩) computed
      change ProofJudgment.Proves Cyclic.environment fuel ⟨0, [], []⟩
        (.termApp (RelationEqualityProofs.reflexivity .prop) (.named "loop")) output at derived
      cases derived with
      | termApp _ _ expanded _ =>
          rw [Cyclic.all_fuels_exhausted] at expanded
          cases expanded

def opaqueEnvironment : Environment := {terms := [⟨"loop", .prop, none⟩]}

theorem opaque_argument_accepted :
    inferProof opaqueEnvironment 32 0 [] [] loopReflexivity =
      some (RelationEqualityProofs.equality .prop (.named "loop") (.named "loop")) := by
  apply (ProofJudgment.Proves.infer (context := ⟨0, [], []⟩))
  refine .termApp (normalized := .named "loop")
    (ProofJudgment.proves_of_infer (context := ⟨0, [], []⟩)
    (RelationEqualityProofs.reflexivity_infers opaqueEnvironment 0 .prop rfl [] [])) ?_ ?_ ?_
  · rfl
  · simp [deltaNormalize, opaqueEnvironment, Environment.lookupTerm?, lookupTermList?]
  · simp [MathdataKernel.normalize, deltaNormalize, opaqueEnvironment, Environment.lookupTerm?,
      lookupTermList?, RelationEqualityProofs.equality, RelationEqualityProofs.relationType,
      RelationEqualityProofs.relationApply, Tm.instantiate, Tm.instantiateAt, Tm.shift,
      Tm.normalize, Tm.normalizeOne]

def sourceReflexivity : ProofSyntax (Constant Cyclic.environment)
    ([] : List (ClosedFormula (Constant Cyclic.environment)))
    (.eq (.const Cyclic.loop) (.const Cyclic.loop)) := .eqRefl (.const Cyclic.loop)

theorem compiled_cyclic_rejected (functional : Tp → Tp → Pf) (propositional : Pf) (fuel : Nat) :
    inferProof Cyclic.environment fuel 0 [] []
      (ProofCompilation.compile functional propositional sourceReflexivity) = none := by
  change inferProof Cyclic.environment fuel 0 [] [] loopReflexivity = none
  exact cyclic_argument_rejected fuel

theorem checked_source_reflexivity :
    Nonempty (ProofSyntax (Constant Cyclic.environment)
      ([] : List (ClosedFormula (Constant Cyclic.environment)))
      (.eq (.const Cyclic.loop) (.const Cyclic.loop))) := ⟨sourceReflexivity⟩

#print axioms cyclic_argument_rejected
#print axioms compiled_reflexivity_requires_delta
#print axioms opaque_argument_accepted
#print axioms checked_source_reflexivity
#print axioms compiled_cyclic_rejected

end Mettapedia.Languages.Megalodon.ProofCompilationDefinitionBoundary

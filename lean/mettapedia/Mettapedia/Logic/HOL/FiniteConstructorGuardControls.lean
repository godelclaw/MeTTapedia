import Mettapedia.Logic.HOL.FiniteConstructorGuardProofs
import Mettapedia.Logic.HOL.FiniteConstructorEncodingControls

/-!
# Positive and separating controls for constructor-image predicates

The generated predicate accepts an encoded Boolean tuple, distinguishes its
constructor occurrence, and refuses a well-typed payload outside the image.
An empty constructor signature produces the false predicate.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.FiniteConstructorEncoding.GuardControls

open Controls

theorem full : model.FullDomains := HenkinModel.fullDomains_standard _ _

def packed : ClosedTerm Constants (payloadType signature) := encode signature ⟨0, by decide⟩ fields

theorem packed_accepted : (model.denote (validGuard signature packed) values).down := by
  apply (validGuard_denote model full signature packed values).mpr
  exact ⟨⟨⟨0, by decide⟩, denoteArguments model _ fields values⟩, generated_denotation.symm⟩

theorem wrong_constructor_refused :
    ¬ (model.denote (constructorGuard signature ⟨1, by decide⟩ packed) values).down := by
  intro accepted
  obtain ⟨data, same⟩ := (constructorGuard_denote model full signature ⟨1, by decide⟩ packed values).mp accepted
  have images := generated_denotation.symm.trans same
  have source := TypeTheory.FiniteConstructorEncoding.encode_injective _ _ images
  have impossible := congrArg (fun item => item.1.val) source
  change (0 : Nat) = 1 at impossible
  cases impossible

theorem unused_guard_refused : ¬ (model.denote (validGuard signature unused) values).down :=
  fun accepted => unused_refused ((validGuard_denote model full signature unused values).mp accepted)

theorem empty_signature_refused :
    ¬ (model.denote (validGuard [] (Term.bot : ClosedFormula Constants)) values).down := by
  exact id

def membershipProof : ProofSyntax Constants [] (.app (predicate signature) packed) :=
  predicate_intro signature ⟨0, by decide⟩ fields

theorem membershipProof_free : membershipProof.FunctionExtensionalityFree :=
  predicate_intro_free signature ⟨0, by decide⟩ fields

#print axioms packed_accepted
#print axioms wrong_constructor_refused
#print axioms unused_guard_refused
#print axioms membershipProof

end Mettapedia.Logic.HOL.FiniteConstructorEncoding.GuardControls

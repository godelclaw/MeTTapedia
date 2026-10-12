import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.DeclaredBindingTraceSemantics
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLProofCarryingPairTraceSemantics
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLIdentityEquality
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeRegularity
import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.Presentation

/-!
# Declared bindings consuming the retained HOL proof compiler

The source program binds the compiler's actual dependent pair and returns its
proof component. Its family mentions the value component of that same pair.
The identity-indexed companion returns reflexivity at the proof it receives.
Neither program replaces the compiled proof by an acceptance Boolean.

Origins and instance identifiers use the existing declaration-entry algebra.
The retained source value contains the original assumptions and proof syntax;
the term interpretation does not claim to recover them from a set value.
The concrete semantic instance is the existing uniform-List trace model.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.DeclaredBindingProofConsumption

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Mettapedia.Logic
open HOLNativeGenericProofCompiler HOLImpredicativeProofCompilation
open PrivateIdentityContexts (Name Frame)

universe u
variable {Γ : HOL.Ctx HOL.UniformListInduction.BaseSort}
  {Δ : List (HOL.Formula HOL.UniformListInduction.Symbol Γ)}
  {σ : HOL.Ty HOL.UniformListInduction.BaseSort}

abbrev signature := FormationSensitiveHOLLeibnizInterface.signature
abbrev rules := UniformList.operations.target

/-- Declaration extension does not alter the universe relations; the actual
uniform-List host discharges regularity from the cumulative presentation. -/
theorem universeRegularity : FormationSensitive.UniverseRegularity rules where
  head_target := FormationSensitive.towerUniverseRegularity.head_target
  join_target := FormationSensitive.towerUniverseRegularity.join_target
  cumulative_target := FormationSensitive.towerUniverseRegularity.cumulative_target
  universe_typed := FormationSensitive.towerUniverseRegularity.universe_typed

abbrev Packed {predicate : HOL.Term HOL.UniformListInduction.Symbol Γ (.arr σ .prop)}
    (value : HOL.ProofCarryingPipeline.Value predicate Δ) {n : Nat}
    (objects : Sub Tower.Head Γ.length n)
    (hypotheses : Fin (Δ.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n) :=
  HOLProofCarryingPairs.pack signature UniformList.proofName UniformList.operations
    uniformList_total value objects hypotheses

def witnessFamily (predicate : HOL.Term HOL.UniformListInduction.Symbol Γ (.arr σ .prop))
    {n : Nat} (objects : Sub Tower.Head Γ.length n) : Tower.Tm (n + 1) :=
  inst0 (.fst (.var 0)) (rename (liftRen wk)
    (HOLProofCarryingPairs.family signature UniformList.proofName predicate objects))

def proofConsumer {predicate : HOL.Term HOL.UniformListInduction.Symbol Γ (.arr σ .prop)}
    (value : HOL.ProofCarryingPipeline.Value predicate Δ) {n : Nat}
    (context : PrivateIdentityContexts.Context Tower.Head n)
    (objects : Sub Tower.Head Γ.length n)
    (hypotheses : Fin (Δ.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n) :
    DeclaredBindingDependent.Source Tower.Head n :=
  .whereBinding (context.frame.freshName "certified")
    (.core (Packed value objects hypotheses)) (.result (.core (.snd (.var 0))))

def indexedProofConsumer {predicate : HOL.Term HOL.UniformListInduction.Symbol Γ (.arr σ .prop)}
    (value : HOL.ProofCarryingPipeline.Value predicate Δ) {n : Nat}
    (context : PrivateIdentityContexts.Context Tower.Head n)
    (objects : Sub Tower.Head Γ.length n)
    (hypotheses : Fin (Δ.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n) :
    DeclaredBindingDependent.Source Tower.Head n :=
  .whereBinding (context.frame.freshName "certified")
    (.core (Packed value objects hypotheses)) (.result (.core (.refl (.snd (.var 0)))))

def exactProofIndex (predicate : HOL.Term HOL.UniformListInduction.Symbol Γ (.arr σ .prop))
    {n : Nat} (objects : Sub Tower.Head Γ.length n) : Tower.Tm (n + 1) :=
  .id (witnessFamily predicate objects) (.snd (.var 0)) (.snd (.var 0))

def exactPairFamily (predicate : HOL.Term HOL.UniformListInduction.Symbol Γ (.arr σ .prop))
    {n : Nat} (objects : Sub Tower.Head Γ.length n) : Tower.Tm (n + 1) :=
  .sigma (witnessFamily predicate objects)
    (.id (rename wk (witnessFamily predicate objects)) (.var 0)
      (rename wk (.snd (.var 0))))

def exactPairConsumer {predicate : HOL.Term HOL.UniformListInduction.Symbol Γ (.arr σ .prop)}
    (value : HOL.ProofCarryingPipeline.Value predicate Δ) {n : Nat}
    (context : PrivateIdentityContexts.Context Tower.Head n)
    (objects : Sub Tower.Head Γ.length n)
    (hypotheses : Fin (Δ.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n) :
    DeclaredBindingDependent.Source Tower.Head n :=
  .whereBinding (context.frame.freshName "certified")
    (.core (Packed value objects hypotheses))
    (.result (.core (.pair (.snd (.var 0)) (.refl (.snd (.var 0))))))

private theorem body_typed (predicate : HOL.Term HOL.UniformListInduction.Symbol Γ (.arr σ .prop))
    {n : Nat} {target : Tower.Ctx n} {objects : Sub Tower.Head Γ.length n} :
    FormationSensitive.Typing rules
      (.snoc target (HOLProofCarryingPairs.pairType signature UniformList.proofName predicate objects))
      (.snd (.var 0)) (witnessFamily predicate objects) :=
  .sndElim (.var 0)

theorem proofConsumer_typed
    {predicate : HOL.Term HOL.UniformListInduction.Symbol Γ (.arr σ .prop)}
    (value : HOL.ProofCarryingPipeline.Value predicate Δ) {n : Nat}
    (context : PrivateIdentityContexts.Context Tower.Head n)
    (formed : PrivateIdentityContexts.WellFormed rules context)
    {objects : Sub Tower.Head Γ.length n}
    {hypotheses : Fin (Δ.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n}
    (objectTyped : GenericTyping.Objects signature context.erase objects)
    (hypothesisTyped : GenericTyping.Hypotheses signature UniformList.operations
      context.erase objects hypotheses) :
    DeclaredBindingDependent.Typing rules context (proofConsumer value context objects hypotheses)
      (inst0 (Packed value objects hypotheses) (witnessFamily predicate objects)) := by
  have domainFormed := HOLProofCarryingPairs.pairType_formed signature UniformList.proofName
    UniformList.operations predicate objectTyped
  have domainUniverse := UniformList.operations.sourceMorphism.isUniverse
    (LevelTower.IsUniverse.sort (.max Tower.zero Tower.zero))
  have extended : FormationSensitive.ContextFormation rules
      (.snoc context.erase (HOLProofCarryingPairs.pairType signature UniformList.proofName
        predicate objects)) := .snoc formed.erase domainFormed domainUniverse
  obtain ⟨level, universeWitness, bodyFormed⟩ :=
    (body_typed (objects := objects) predicate).regularity universeRegularity extended
  change LevelTower.IsUniverse level at universeWitness
  cases universeWitness with
  | sort level =>
    have productFormed := FormationSensitive.Typing.piForm domainFormed domainUniverse
      bodyFormed (LevelTower.IsUniverse.sort level) (LevelTower.Join.sorts _ _)
    exact .whereBinding (context.frame.freshName_fresh "certified") productFormed
      (LevelTower.IsUniverse.sort _) (.core (HOLProofCarryingPairs.pack_typed signature
        UniformList.proofName UniformList.operations uniformList_total value objectTyped hypothesisTyped))
      (.result (.core (body_typed predicate)))

theorem indexedProofConsumer_typed
    {predicate : HOL.Term HOL.UniformListInduction.Symbol Γ (.arr σ .prop)}
    (value : HOL.ProofCarryingPipeline.Value predicate Δ) {n : Nat}
    (context : PrivateIdentityContexts.Context Tower.Head n)
    (formed : PrivateIdentityContexts.WellFormed rules context)
    {objects : Sub Tower.Head Γ.length n}
    {hypotheses : Fin (Δ.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n}
    (objectTyped : GenericTyping.Objects signature context.erase objects)
    (hypothesisTyped : GenericTyping.Hypotheses signature UniformList.operations
      context.erase objects hypotheses) :
    DeclaredBindingDependent.Typing rules context (indexedProofConsumer value context objects hypotheses)
      (inst0 (Packed value objects hypotheses) (exactProofIndex predicate objects)) := by
  have domainFormed := HOLProofCarryingPairs.pairType_formed signature UniformList.proofName
    UniformList.operations predicate objectTyped
  have domainUniverse := UniformList.operations.sourceMorphism.isUniverse
    (LevelTower.IsUniverse.sort (.max Tower.zero Tower.zero))
  have extended : FormationSensitive.ContextFormation rules
      (.snoc context.erase (HOLProofCarryingPairs.pairType signature UniformList.proofName
        predicate objects)) := .snoc formed.erase domainFormed domainUniverse
  have evidenceTyped := body_typed (target := context.erase) (objects := objects) predicate
  obtain ⟨level, universeWitness, bodyFormed⟩ := evidenceTyped.regularity universeRegularity extended
  change LevelTower.IsUniverse level at universeWitness
  cases universeWitness with
  | sort level =>
    have indexedFormed := FormationSensitive.Typing.idForm bodyFormed
      (LevelTower.IsUniverse.sort level) evidenceTyped evidenceTyped
    have productFormed := FormationSensitive.Typing.piForm domainFormed domainUniverse
      indexedFormed (LevelTower.IsUniverse.sort level) (LevelTower.Join.sorts _ _)
    exact .whereBinding (context.frame.freshName_fresh "certified") productFormed
      (LevelTower.IsUniverse.sort _) (.core (HOLProofCarryingPairs.pack_typed signature
        UniformList.proofName UniformList.operations uniformList_total value objectTyped hypothesisTyped))
      (.result (.core (.reflIntro evidenceTyped)))

/-- The source consumer itself returns the Sigma whose second component is
identity at the exact first proof. Its formation uses no proof erasure rule. -/
theorem exactPairConsumer_typed
    {predicate : HOL.Term HOL.UniformListInduction.Symbol Γ (.arr σ .prop)}
    (value : HOL.ProofCarryingPipeline.Value predicate Δ) {n : Nat}
    (context : PrivateIdentityContexts.Context Tower.Head n)
    (formed : PrivateIdentityContexts.WellFormed rules context)
    {objects : Sub Tower.Head Γ.length n}
    {hypotheses : Fin (Δ.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n}
    (objectTyped : GenericTyping.Objects signature context.erase objects)
    (hypothesisTyped : GenericTyping.Hypotheses signature UniformList.operations
      context.erase objects hypotheses) :
    DeclaredBindingDependent.Typing rules context (exactPairConsumer value context objects hypotheses)
      (inst0 (Packed value objects hypotheses) (exactPairFamily predicate objects)) := by
  have domainFormed := HOLProofCarryingPairs.pairType_formed signature UniformList.proofName
    UniformList.operations predicate objectTyped
  have domainUniverse := UniformList.operations.sourceMorphism.isUniverse
    (LevelTower.IsUniverse.sort (.max Tower.zero Tower.zero))
  have extended : FormationSensitive.ContextFormation rules
      (.snoc context.erase (HOLProofCarryingPairs.pairType signature UniformList.proofName
        predicate objects)) := .snoc formed.erase domainFormed domainUniverse
  have evidenceTyped := body_typed (target := context.erase) (objects := objects) predicate
  obtain ⟨level, universeWitness, familyFormed⟩ := evidenceTyped.regularity universeRegularity extended
  change LevelTower.IsUniverse level at universeWitness
  cases universeWitness with
  | sort level =>
    have newest : FormationSensitive.Typing rules
        (.snoc (.snoc context.erase (HOLProofCarryingPairs.pairType signature UniformList.proofName
          predicate objects)) (witnessFamily predicate objects))
        (.var 0) (rename wk (witnessFamily predicate objects)) := .var 0
    have identityFormed := FormationSensitive.Typing.idForm familyFormed.weaken
      (LevelTower.IsUniverse.sort level) newest evidenceTyped.weaken
    have resultFormed := FormationSensitive.Typing.sigmaForm familyFormed
      (LevelTower.IsUniverse.sort level) identityFormed (LevelTower.IsUniverse.sort level)
      (LevelTower.Join.sorts _ _)
    have reflexive : FormationSensitive.Typing rules
        (.snoc context.erase (HOLProofCarryingPairs.pairType signature UniformList.proofName
          predicate objects)) (.refl (.snd (.var 0)))
        (inst0 (.snd (.var 0))
          (.id (rename wk (witnessFamily predicate objects)) (.var 0)
            (rename wk (.snd (.var 0))))) := by
      change FormationSensitive.Typing rules _ (.refl (.snd (.var 0)))
        (.id (inst0 (.snd (.var 0)) (rename wk (witnessFamily predicate objects)))
          (.snd (.var 0)) (inst0 (.snd (.var 0)) (rename wk (.snd (.var 0)))))
      rw [inst0_rename_wk, inst0_rename_wk]
      exact .reflIntro evidenceTyped
    have resultTyped := FormationSensitive.Typing.pairIntro resultFormed
      (LevelTower.IsUniverse.sort (.max level level)) evidenceTyped reflexive
    have productFormed := FormationSensitive.Typing.piForm domainFormed domainUniverse
      resultFormed (LevelTower.IsUniverse.sort (.max level level)) (LevelTower.Join.sorts _ _)
    exact .whereBinding (context.frame.freshName_fresh "certified") productFormed
      (LevelTower.IsUniverse.sort _) (.core (HOLProofCarryingPairs.pack_typed signature
        UniformList.proofName UniformList.operations uniformList_total value objectTyped hypothesisTyped))
      (.result (.core resultTyped))

theorem exactPairConsumer_beta
    {predicate : HOL.Term HOL.UniformListInduction.Symbol Γ (.arr σ .prop)}
    (value : HOL.ProofCarryingPipeline.Value predicate Δ) {n : Nat}
    (context : PrivateIdentityContexts.Context Tower.Head n)
    (objects : Sub Tower.Head Γ.length n)
    (hypotheses : Fin (Δ.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n) :
    Step rules.headEq (DeclaredBindingDependent.translate
      (exactPairConsumer value context objects hypotheses))
      (.pair (.snd (Packed value objects hypotheses))
        (.refl (.snd (Packed value objects hypotheses)))) rules.computation := by
  simpa only [exactPairConsumer, DeclaredBindingDependent.translate, inst0, subst,
    subst0, Fin.cases_zero] using
    (Step.betaPi (headEq := rules.headEq) (root := rules.computation)
      (.pair (.snd (.var 0)) (.refl (.snd (.var 0)))) (Packed value objects hypotheses))

/-- The complete actual proof survives the authored binding's beta reduction. -/
theorem proofConsumer_beta
    {predicate : HOL.Term HOL.UniformListInduction.Symbol Γ (.arr σ .prop)}
    (value : HOL.ProofCarryingPipeline.Value predicate Δ) {n : Nat}
    (context : PrivateIdentityContexts.Context Tower.Head n)
    (objects : Sub Tower.Head Γ.length n)
    (hypotheses : Fin (Δ.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n) :
    Step rules.headEq (DeclaredBindingDependent.translate
      (proofConsumer value context objects hypotheses))
      (.snd (Packed value objects hypotheses)) rules.computation := by
  simpa only [proofConsumer, DeclaredBindingDependent.translate, inst0, subst,
    subst0, Fin.cases_zero] using
    (Step.betaPi (headEq := rules.headEq) (root := rules.computation)
      (.snd (.var 0)) (Packed value objects hypotheses))

theorem consumed_proof_is_compiler_output
    {predicate : HOL.Term HOL.UniformListInduction.Symbol Γ (.arr σ .prop)}
    (value : HOL.ProofCarryingPipeline.Value predicate Δ) {n : Nat}
    (objects : Sub Tower.Head Γ.length n)
    (hypotheses : Fin (Δ.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n) :
    Step rules.headEq (.snd (Packed value objects hypotheses))
      (translateProof signature UniformList.proofName UniformList.operations uniformList_total
        value.evidence objects hypotheses) rules.computation := .betaSigmaSnd _ _

structure RetainedInput (Origin : Type) (predicate : HOL.Term HOL.UniformListInduction.Symbol Γ (.arr σ .prop))
    (assumptions : List (HOL.Formula HOL.UniformListInduction.Symbol Γ)) where
  declaration : Mettapedia.GSLT.LanguageDef.ModuleAlgebra.Entry Origin String
    (HOL.ProofCarryingPipeline.Value predicate assumptions)
  instanceId : Nat

def receipts {Origin : Type}
    {predicate : HOL.Term HOL.UniformListInduction.Symbol Γ (.arr σ .prop)}
    (retained : RetainedInput Origin predicate Δ) {n : Nat}
    (context : PrivateIdentityContexts.Context Tower.Head n)
    (objects : Sub Tower.Head Γ.length n)
    (hypotheses : Fin (Δ.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n) :
    List (Nat × List Nat) :=
  (DeclaredBindingDependent.bindingOccurrences
    (proofConsumer retained.declaration.body context objects hypotheses)).map
      (fun path => (retained.instanceId, path))

theorem receipts_exact {Origin : Type}
    {predicate : HOL.Term HOL.UniformListInduction.Symbol Γ (.arr σ .prop)}
    (retained : RetainedInput Origin predicate Δ) {n : Nat}
    (context : PrivateIdentityContexts.Context Tower.Head n)
    (objects : Sub Tower.Head Γ.length n)
    (hypotheses : Fin (Δ.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n) :
    receipts retained context objects hypotheses = [(retained.instanceId, [])] := rfl

/-- Changing an environment substitutes into both the object and the actual
proof argument. Source assumptions and the declaration's origin stay retained. -/
theorem packed_substitution
    {predicate : HOL.Term HOL.UniformListInduction.Symbol Γ (.arr σ .prop)}
    (value : HOL.ProofCarryingPipeline.Value predicate Δ) {n m : Nat}
    (objects : Sub Tower.Head Γ.length n)
    (hypotheses : Fin (Δ.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n)
    (substitution : Sub Tower.Head n m) :
    subst substitution (Packed value objects hypotheses) =
      Packed value (fun i => subst substitution (objects i))
        (fun i => subst substitution (hypotheses i)) :=
  HOLProofCarryingPairs.pack_substitute signature UniformList.proofName UniformList.operations
    uniformList_total uniformList_natural value objects hypotheses substitution

/-- Source context transport and substitution into the retained proof
compiler commute in the same diagram, at arbitrary dependent substitutions. -/
theorem consumer_substitution
    {predicate : HOL.Term HOL.UniformListInduction.Symbol Γ (.arr σ .prop)}
    (value : HOL.ProofCarryingPipeline.Value predicate Δ) {n m : Nat}
    (source : PrivateIdentityContexts.Context Tower.Head n)
    (target : PrivateIdentityContexts.Context Tower.Head m)
    (objects : Sub Tower.Head Γ.length n)
    (hypotheses : Fin (Δ.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n)
    (substitution : Sub Tower.Head n m) :
    DeclaredBindingDependent.translate
      (DeclaredBindingDependent.substituteInto target.frame substitution
        (proofConsumer value source objects hypotheses)) =
      DeclaredBindingDependent.translate
        (proofConsumer value target (fun i => subst substitution (objects i))
          (fun i => subst substitution (hypotheses i))) := by
  rw [DeclaredBindingDependent.substitution_square]
  change Tm.app (.lam (.snd (.var 0))) (subst substitution (Packed value objects hypotheses)) = _
  rw [packed_substitution]
  rfl

/-- The source declaration cannot be reconstructed from a material term:
independent origins can produce the very same computed proof consumer. -/
theorem origin_not_recoverable {Origin : Type}
    {predicate : HOL.Term HOL.UniformListInduction.Symbol Γ (.arr σ .prop)}
    (first second : Origin) (different : first ≠ second)
    (value : HOL.ProofCarryingPipeline.Value predicate Δ) {n : Nat}
    (context : PrivateIdentityContexts.Context Tower.Head n)
    (objects : Sub Tower.Head Γ.length n)
    (hypotheses : Fin (Δ.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n) :
    ¬ ∃ recover : Tower.Tm n → Origin,
      ∀ input : RetainedInput Origin predicate Δ,
        recover (DeclaredBindingDependent.translate
          (proofConsumer input.declaration.body context objects hypotheses)) =
          input.declaration.origin := by
  rintro ⟨recover, law⟩
  have left := law ⟨⟨first, "consumer", value⟩, 0⟩
  have right := law ⟨⟨second, "consumer", value⟩, 1⟩
  exact different (left.symm.trans right)

theorem receipts_not_recoverable
    {predicate : HOL.Term HOL.UniformListInduction.Symbol Γ (.arr σ .prop)}
    (value : HOL.ProofCarryingPipeline.Value predicate Δ) {n : Nat}
    (context : PrivateIdentityContexts.Context Tower.Head n)
    (objects : Sub Tower.Head Γ.length n)
    (hypotheses : Fin (Δ.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n) :
    ¬ ∃ recover : Tower.Tm n → List (Nat × List Nat),
      ∀ input : RetainedInput Nat predicate Δ,
        recover (DeclaredBindingDependent.translate
          (proofConsumer input.declaration.body context objects hypotheses)) =
          receipts input context objects hypotheses := by
  rintro ⟨recover, law⟩
  have left := law ⟨⟨0, "consumer", value⟩, 0⟩
  have right := law ⟨⟨0, "consumer", value⟩, 1⟩
  have impossible : ([(0, [])] : List (Nat × List Nat)) = [(1, [])] := left.symm.trans right
  cases (List.cons.inj impossible).1

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.DeclaredBindingProofConsumption

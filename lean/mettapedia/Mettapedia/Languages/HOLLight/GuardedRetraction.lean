import Mettapedia.Logic.HOL.GuardedRetraction
import Mettapedia.Languages.HOLLight.RetainedCompilation
import Mettapedia.Languages.HOLLight.InferenceOnlyReplay

/-!
# Native HOL Light blocks for guarded retractions

The existing retained-compilation operations compose actual primitive graphs
for the guarded injectivity rule and a functional representation of Boolean
values. The blocks work under any axiom policy and specialize to the empty
policy. No datatype retraction law is inserted by this logical construction.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.HOLLight.GuardedRetraction
open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open RetainedCompilation ReverseTranslation
open SourceSubstitution GraphExpansion
local infixr:60 " ⇒ " => HOL.Ty.arr

variable {policy : AxiomPolicy} [DecidablePred policy]
variable {Γ : HOL.Ctx AtomicTy} {names : Naming Γ}
variable {σ τ : HOL.Ty AtomicTy} {Δ : List (HOL.Formula Symbol Γ)}

def reflectEquality (encode : HOL.Term Symbol Γ (σ ⇒ τ)) (decode : HOL.Term Symbol Γ (τ ⇒ σ))
    (valid : HOL.Term Symbol Γ (σ ⇒ .prop)) (first second : HOL.Term Symbol Γ σ)
    (retraction : Compiled policy names Δ (HOL.GuardedRetraction.law encode decode valid))
    (firstValid : Compiled policy names Δ (.app valid first))
    (secondValid : Compiled policy names Δ (.app valid second))
    (same : Compiled policy names Δ (.eq (.app encode first) (.app encode second)))
    (origin : ProofExecution.Origin) : Compiled policy names Δ (.eq first second) := by
  have firstLaw : Compiled policy names Δ
      (.imp (.app valid first) (.eq (.app decode (.app encode first)) first)) := by
    simpa only [HOL.GuardedRetraction.law, HOL.GuardedRetraction.instantiate_law] using
      Compiled.specialize first retraction origin
  have secondLaw : Compiled policy names Δ
      (.imp (.app valid second) (.eq (.app decode (.app encode second)) second)) := by
    simpa only [HOL.GuardedRetraction.law, HOL.GuardedRetraction.instantiate_law] using
      Compiled.specialize second retraction origin
  exact Compiled.transitive (Compiled.symmetric (Compiled.modusPonens firstLaw firstValid origin) origin)
    (Compiled.transitive (Compiled.argumentCongruence decode same origin)
      (Compiled.modusPonens secondLaw secondValid origin) origin) origin

def point (encode : HOL.Term Symbol Γ (σ ⇒ τ)) (decode : HOL.Term Symbol Γ (τ ⇒ σ))
    (valid : HOL.Term Symbol Γ (σ ⇒ .prop)) (first second : HOL.Term Symbol Γ σ)
    (names : Naming Γ) (origin : ProofExecution.Origin) :
    Compiled policy names [] (HOL.GuardedRetraction.consequence encode decode valid first second) := by
  let assumptions := [.eq (.app encode first) (.app encode second), .app valid second,
    .app valid first, HOL.GuardedRetraction.law encode decode valid]
  have same : Compiled policy names assumptions (.eq first second) :=
    reflectEquality encode decode valid first second
      (Compiled.hypothesis ⟨3, by simp [assumptions]⟩ origin)
      (Compiled.hypothesis ⟨2, by simp [assumptions]⟩ origin)
      (Compiled.hypothesis ⟨1, by simp [assumptions]⟩ origin)
      (Compiled.hypothesis ⟨0, by simp [assumptions]⟩ origin) origin
  exact Compiled.discharge (Compiled.discharge (Compiled.discharge
    (Compiled.discharge same origin) origin) origin) origin

def compiledRule (policy : AxiomPolicy) [DecidablePred policy] (σ τ : HOL.Ty AtomicTy)
    (origin : ProofExecution.Origin) :
    Compiled policy Naming.empty [] (HOL.GuardedRetraction.rule σ τ) := by
  refine Compiled.universalIntro (Compiled.universalIntro (Compiled.universalIntro
    (Compiled.universalIntro (Compiled.universalIntro ?_ origin) origin) origin) origin) origin
  exact point (.var (.vs (.vs (.vs (.vs .vz))))) (.var (.vs (.vs (.vs .vz))))
    (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz) _ origin

def roundtrip (value : HOL.Term Symbol Γ σ) (origin : ProofExecution.Origin) :
    Compiled policy names Δ
      (.eq (.app HOL.GuardedRetraction.evaluateTrue
        (.app HOL.GuardedRetraction.constantEmbedding value)) value) := by
  have decodeBeta : Compiled policy names Δ
      (.eq (.app HOL.GuardedRetraction.evaluateTrue (.app HOL.GuardedRetraction.constantEmbedding value))
        (.app (.app HOL.GuardedRetraction.constantEmbedding value) .top)) := by
    simpa only [HOL.GuardedRetraction.evaluateTrue, HOL.instantiate, HOL.subst, HOL.Subst.single] using
      Compiled.betaRule (.app HOL.GuardedRetraction.constantEmbedding value) (.app (.var .vz) .top) origin
  have encodeBeta : Compiled policy names Δ
      (.eq (.app HOL.GuardedRetraction.constantEmbedding value) (.lam (HOL.weaken value))) := by
    simpa only [HOL.GuardedRetraction.constantEmbedding, HOL.instantiate, HOL.subst,
      HOL.Subst.single, HOL.Subst.lift, HOL.weaken] using
      Compiled.betaRule value (.lam (.var (.vs .vz))) origin
  have readBeta : Compiled policy names Δ (.eq (.app (.lam (HOL.weaken value)) .top) value) := by
    simpa only [HOL.instantiate_weaken] using Compiled.betaRule .top (HOL.weaken value) origin
  exact Compiled.transitive decodeBeta
    (Compiled.transitive (Compiled.functionCongruence .top encodeBeta origin) readBeta origin) origin

def functionalLaw (policy : AxiomPolicy) [DecidablePred policy]
    (names : Naming Γ) (Δ : List (HOL.Formula Symbol Γ)) (σ : HOL.Ty AtomicTy)
    (origin : ProofExecution.Origin) :
    Compiled policy names Δ (HOL.GuardedRetraction.law
      (HOL.GuardedRetraction.constantEmbedding (σ := σ)) HOL.GuardedRetraction.evaluateTrue
      HOL.GuardedRetraction.allValid) := by
  refine Compiled.universalIntro (Compiled.discharge ?_ origin) origin
  exact roundtrip (.var .vz) origin

local instance : DecidablePred emptyAxiomPolicy := fun _ => isFalse id

def layer : AtomicTy := ⟨.var (Name.global "DatatypeLayer"), rfl, rfl⟩
def carrier : AtomicTy := ⟨.var (Name.global "DatatypeCarrier"), rfl, rfl⟩

def schema := compiledRule emptyAxiomPolicy (.base layer) (.base carrier) ("guarded-retraction", 0)
def functionalRetraction := functionalLaw emptyAxiomPolicy Naming.empty [] .prop ("functional-retraction", 0)

/-- Native type instantiation retains the original proof graph as a premise
and appends the kernel's actual INST_TYPE inference. -/
def instantiateTypes (proof : CheckedProof policy) (entries : List (Ty × Ty))
    (origin : ProofExecution.Origin) : CheckedProof policy := by
  let result := substituteTheorem (typeOnlySubstitution entries) proof.result
  exact CheckedProof.unary proof result
    (primitiveBlock (.inference (.instType entries proof.result)) result origin)
    (primitiveBlock_checked (.inference (.instType entries proof.result)) result origin
      ((RuleRequest.check_eq_some_iff policy _ _).mpr
        (substituteTheorem_semantics (typeOnlySubstitution entries) proof.result))) origin

def functionalSchemaInstance := instantiateTypes schema.proof
  [(Ty.bool, .var (Name.global "DatatypeLayer")),
   (Ty.function Ty.bool Ty.bool, .var (Name.global "DatatypeCarrier"))]
  ("guarded-retraction-type-instance", 0)

theorem schema_accepted : (ProofSystem.checker emptyAxiomPolicy).check
    schema.proof.result schema.proof.certificate = true := schema.proof.accepted

theorem functional_retraction_accepted : (ProofSystem.checker emptyAxiomPolicy).check
    functionalRetraction.proof.result functionalRetraction.proof.certificate = true :=
  functionalRetraction.proof.accepted

theorem functional_schema_instance_accepted : (ProofSystem.checker emptyAxiomPolicy).check
    functionalSchemaInstance.result functionalSchemaInstance.certificate = true := functionalSchemaInstance.accepted

set_option maxRecDepth 8192 in
theorem schema_axioms_empty : schema.proof.result.axioms = ∅ := by decide +kernel

set_option maxRecDepth 8192 in
theorem functional_retraction_axioms_empty : functionalRetraction.proof.result.axioms = ∅ := by decide +kernel

set_option maxRecDepth 8192 in
theorem functional_schema_instance_axioms_empty : functionalSchemaInstance.result.axioms = ∅ := by decide +kernel

set_option maxRecDepth 8192 in
theorem schema_only_inferences : InferenceOnlyReplay.inferenceOnly schema.proof.certificate.1 = true :=
  InferenceOnlyReplay.inference_only_of_empty_acceptance _ _ schema_accepted

set_option maxRecDepth 8192 in
theorem functional_retraction_only_inferences :
    InferenceOnlyReplay.inferenceOnly functionalRetraction.proof.certificate.1 = true :=
  InferenceOnlyReplay.inference_only_of_empty_acceptance _ _ functional_retraction_accepted

set_option maxRecDepth 8192 in
theorem schema_policy (selected : AxiomPolicy) [DecidablePred selected] :
    (ProofSystem.checker selected).check schema.proof.result schema.proof.certificate = true := by
  rw [← InferenceOnlyReplay.checker emptyAxiomPolicy selected _ _ schema_only_inferences]
  exact schema_accepted

def verdicts : List (String × Bool) :=
  [("guarded retraction rule checks with no admitted axioms",
    (ProofSystem.checker emptyAxiomPolicy).check schema.proof.result schema.proof.certificate),
   ("functional representation retraction checks with no admitted axioms",
    (ProofSystem.checker emptyAxiomPolicy).check functionalRetraction.proof.result functionalRetraction.proof.certificate),
   ("guarded retraction graph retains inference nodes only",
    InferenceOnlyReplay.inferenceOnly schema.proof.certificate.1),
   ("guarded retraction native function-type instance checks",
    (ProofSystem.checker emptyAxiomPolicy).check functionalSchemaInstance.result functionalSchemaInstance.certificate)]

#print axioms schema_accepted
#print axioms schema_axioms_empty
#print axioms functional_retraction_accepted
#print axioms functional_retraction_axioms_empty
#print axioms schema_only_inferences
#print axioms schema_policy
#print axioms functional_schema_instance_accepted
end Mettapedia.Languages.HOLLight.GuardedRetraction

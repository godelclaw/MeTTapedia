import Mettapedia.Languages.Megalodon.SourceDefinitionInvariant
import Mettapedia.Languages.Megalodon.ProofJudgment

/-!
# Protected polymorphic regions throughout proof inference

Scope follows from actual term synthesis. Protected proof payloads and an
admitted environment then preserve both scope and protected type regions
through all eight inference rules, including open-context generalization.
This is an invariant of successful checking, not an assumption on its result.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.SourceScopeInvariant
open MathdataKernel ProofJudgment

theorem inferTerm_scoped {environment : Environment} {typeDepth : Nat} {context : List Tp}
    {body : Tm} {type : Tp} (typed : inferTerm environment typeDepth context body = some type) :
    Scoped context.length body := by
  induction body generalizing typeDepth context type with
  | db index => exact (List.getElem?_eq_some_iff.mp typed).1
  | named | prim => trivial
  | app function argument ihf iha =>
      cases first : inferTerm environment typeDepth context function with
      | none => simp [inferTerm, first] at typed
      | some firstType =>
          cases firstType <;> simp only [inferTerm, first] at typed
          all_goals try contradiction
          cases second : inferTerm environment typeDepth context argument with
          | none => simp [second] at typed
          | some secondType => exact ⟨ihf first, iha second⟩
  | lam domain body ih | all domain body ih =>
      by_cases formed : domain.plainWellFormed typeDepth = true
      · cases inferred : inferTerm environment typeDepth (domain :: context) body with
        | none => simp [inferTerm, formed, inferred] at typed
        | some result => exact ih inferred
      · simp [inferTerm, formed] at typed
  | imp domain codomain ihd ihc =>
      cases first : inferTerm environment typeDepth context domain with
      | none => simp [inferTerm, first] at typed
      | some firstType =>
          cases firstType <;> simp only [inferTerm, first] at typed
          all_goals try contradiction
          cases second : inferTerm environment typeDepth context codomain with
          | none => simp [second] at typed
          | some secondType => exact ⟨ihd first, ihc second⟩
  | typeApp body argument ih =>
      by_cases formed : argument.plainWellFormed typeDepth = true
      · cases inferred : inferTerm environment typeDepth context body with
        | none => simp [inferTerm, formed, inferred] at typed
        | some result => exact ih inferred
      · simp [inferTerm, formed] at typed
  | typeLam body ih =>
      cases inferred : inferTerm environment (typeDepth + 1) (context.map (Tp.shift 0 1)) body with
      | none => simp [inferTerm, inferred] at typed
      | some result => simpa [Scoped] using ih inferred
  | typeAll => simp [inferTerm] at typed

def Known (environment : Environment) : Prop :=
  ∀ name proposition, environment.lookupKnown? name = some proposition →
    Scoped 0 proposition ∧ Protected proposition

def ContextSafe (context : Context) : Prop :=
  ∀ proposition ∈ context.hypotheses,
    Scoped context.terms.length proposition ∧ Protected proposition

def ProofPayload : Pf → Prop
  | .hyp _ | .known _ | .gpa _ => True
  | .termApp proof argument => ProofPayload proof ∧ Protected argument
  | .proofApp function argument => ProofPayload function ∧ ProofPayload argument
  | .termLam _ proof | .typeApp proof _ | .typeLam proof => ProofPayload proof
  | .proofLam proposition proof => Protected proposition ∧ ProofPayload proof

instance proofPayloadDecidable : (proof : Pf) → Decidable (ProofPayload proof)
  | .hyp _ | .known _ | .gpa _ => isTrue trivial
  | .termApp proof argument =>
      haveI := proofPayloadDecidable proof
      inferInstanceAs (Decidable (ProofPayload proof ∧ Protected argument))
  | .proofApp function argument =>
      haveI := proofPayloadDecidable function
      haveI := proofPayloadDecidable argument
      inferInstanceAs (Decidable (ProofPayload function ∧ ProofPayload argument))
  | .termLam _ proof | .typeApp proof _ | .typeLam proof => proofPayloadDecidable proof
  | .proofLam proposition proof =>
      haveI := proofPayloadDecidable proof
      inferInstanceAs (Decidable (Protected proposition ∧ ProofPayload proof))

theorem ContextSafe.termBinder {context : Context} (safe : ContextSafe context) (type : Tp) :
    ContextSafe (context.termBinder type) := by
  intro proposition member
  change proposition ∈ context.hypotheses.map (Tm.shift 0 1) at member
  obtain ⟨source, sourceMember, same⟩ := List.mem_map.mp member
  subst proposition
  obtain ⟨scope, protectedBody⟩ := safe source sourceMember
  exact ⟨scoped_shift scope 0 1, protected_shift protectedBody 0 1⟩

theorem ContextSafe.proofBinder {context : Context} (safe : ContextSafe context) {proposition : Tm}
    (scope : Scoped context.terms.length proposition) (protectedBody : Protected proposition) :
    ContextSafe (context.proofBinder proposition) := by
  intro body member
  rcases List.mem_cons.mp member with rfl | member
  · exact ⟨scope, protectedBody⟩
  · exact safe body member

theorem ContextSafe.typeBinder (context : Context) : ContextSafe context.typeBinder := by
  intro proposition member
  cases member

theorem proof_invariants {environment : Environment} (definitions : Definitions environment)
    (known : Known environment) {fuel : Nat} {context : Context} {proof : Pf} {proposition : Tm}
    (derivation : Proves environment fuel context proof proposition) (safeContext : ContextSafe context)
    (payload : ProofPayload proof) : Scoped context.terms.length proposition ∧ Protected proposition := by
  induction derivation with
  | hyp found => exact safeContext _ (List.mem_of_getElem? found)
  | known found normalized =>
      obtain ⟨scope, safe⟩ := known _ _ found
      obtain ⟨ns, np⟩ := full_normalize_invariants definitions fuel normalized
      exact ⟨ns _ (scoped_mono scope (Nat.zero_le _)), np safe⟩
  | termApp _ typed unfolded normalized ih =>
      obtain ⟨bodyScope, bodySafe⟩ := ih safeContext payload.1
      simp only [Scoped] at bodyScope
      simp only [Protected] at bodySafe
      obtain ⟨ascope, asafe⟩ := delta_invariants environment definitions fuel _ _ unfolded
      have argumentScope := ascope _ (inferTerm_scoped typed)
      have argumentSafe := asafe payload.2
      have substitutedScope := scoped_instantiate argumentScope 0 bodyScope
      have substitutedSafe := protected_instantiate bodySafe argumentSafe 0
      obtain ⟨ns, np⟩ := full_normalize_invariants definitions fuel normalized
      exact ⟨ns _ substitutedScope, np substitutedSafe⟩
  | proofApp _ _ ihf _ =>
      obtain ⟨scope, safe⟩ := ihf safeContext payload.1
      exact ⟨scope.2, safe.2⟩
  | termLam _ _ ih => exact ih (safeContext.termBinder _) payload
  | proofLam typed normalized _ ih =>
      obtain ⟨ns, np⟩ := full_normalize_invariants definitions fuel normalized
      have scope := ns _ (inferTerm_scoped typed)
      have safe := np payload.1
      obtain ⟨bodyScope, bodySafe⟩ := ih (safeContext.proofBinder scope safe) payload.2
      exact ⟨⟨scope, bodyScope⟩, safe, bodySafe⟩
  | typeApp _ ih =>
      obtain ⟨scope, safe⟩ := ih safeContext payload
      exact ⟨(scoped_typeInstantiate _ _ _ _).mpr scope, protected_typeInstantiate safe.2 _ _⟩
  | typeLam terms _ _ ih =>
      obtain ⟨scope, safe⟩ := ih (ContextSafe.typeBinder _) payload
      exact ⟨by simpa [terms, Context.typeBinder, Scoped] using scope, scope, safe⟩

/-- This statement is about the actual executable checker, uniformly in the
selected profile inventory and the supplied finite normalization bound. -/
theorem inferProof_invariants {environment : Environment} (definitions : Definitions environment)
    (known : Known environment) {fuel : Nat} {context : Context} {proof : Pf} {proposition : Tm}
    (safeContext : ContextSafe context) (payload : ProofPayload proof)
    (accepted : inferProof environment fuel context.typeDepth context.terms context.hypotheses proof = some proposition) :
    Scoped context.terms.length proposition ∧ Protected proposition :=
  proof_invariants definitions known (proves_of_infer accepted) safeContext payload

end Mettapedia.Languages.Megalodon.SourceScopeInvariant

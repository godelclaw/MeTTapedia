import Mettapedia.Languages.Megalodon.DeltaNormalInvariant
import Mettapedia.Languages.Megalodon.SourceProofInvariant

/-!
# Native inference and the publication proof algorithm

This reference follows the mathematical control flow of `extr_propofpf`:
term application uses publication substitution and beta/eta normalization,
without a redundant delta pass. A common explicit finite bound makes its
resource observation comparable to the Lean native checker. The theorem
compares independent operations on the admitted source fragment. It does not
verify OCaml execution, exception delivery, source parsing or hash admission.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.PublicationProofRefinement
open MathdataKernel ProofJudgment SourceScopeInvariant DeltaNormalInvariant

def normalize (environment : Environment) (fuel : Nat) (body : Tm) : Option Tm :=
  (deltaNormalize environment fuel body).bind (SourcePublicationNormalization.normalize fuel)

def infer (environment : Environment) (fuel : Nat) : Nat → List Tp → List Tm → Pf → Option Tm
  | _, _, hypotheses, .hyp index => hypotheses[index]?
  | _, _, _, .gpa _ => none
  | _, _, _, .known name => do normalize environment fuel (← environment.lookupKnown? name)
  | depth, terms, hypotheses, .termApp proof argument => do
      let .all domain body ← infer environment fuel depth terms hypotheses proof | none
      let actual ← inferTerm environment depth terms argument
      if actual != domain then none else
      let expanded ← deltaNormalize environment fuel argument
      SourcePublicationNormalization.normalize fuel (SourceTermFragment.publicationSubstitute 0 expanded body)
  | depth, terms, hypotheses, .proofApp function argument => do
      let .imp domain codomain ← infer environment fuel depth terms hypotheses function | none
      let actual ← infer environment fuel depth terms hypotheses argument
      if actual = domain then some codomain else none
  | depth, terms, hypotheses, .termLam type proof => do
      if !type.plainWellFormed depth then none else
      return .all type (← infer environment fuel depth (type :: terms) (hypotheses.map (Tm.shift 0 1)) proof)
  | depth, terms, hypotheses, .proofLam proposition proof => do
      if (← inferTerm environment depth terms proposition) != .prop then none
      let normal ← normalize environment fuel proposition
      return .imp normal (← infer environment fuel depth terms (normal :: hypotheses) proof)
  | depth, terms, hypotheses, .typeApp proof type => do
      let .typeAll body ← infer environment fuel depth terms hypotheses proof | none
      some (Tm.typeInstantiate type body)
  | depth, terms, hypotheses, .typeLam proof =>
      if terms.isEmpty && hypotheses.isEmpty then
        return .typeAll (← infer environment fuel (depth + 1) [] [] proof)
      else none

private theorem contextNormal_termBinder {environment : Environment} {context : Context}
    (normal : ContextNormal environment context) (type : Tp) : ContextNormal environment (context.termBinder type) := by
  intro proposition member
  change proposition ∈ context.hypotheses.map (Tm.shift 0 1) at member
  obtain ⟨source, sourceMember, same⟩ := List.mem_map.mp member
  subst proposition
  simpa only [Normal, NativeSupport.termSupport_shift] using normal source sourceMember

theorem infer_agrees {environment : Environment} (definitions : Definitions environment) (known : Known environment)
    (fuel : Nat) {context : Context} {proof : Pf} (safeContext : ContextSafe context)
    (normalContext : ContextNormal environment context) (payload : ProofPayload proof) :
    infer environment fuel context.typeDepth context.terms context.hypotheses proof =
      inferProof environment fuel context.typeDepth context.terms context.hypotheses proof := by
  induction proof generalizing context with
  | hyp | gpa => rfl
  | known name =>
      cases found : environment.lookupKnown? name with
      | none => simp [infer, inferProof, found]
      | some proposition =>
          simp only [infer, inferProof, found]
          exact SourcePublicationNormalization.expanded_normalize_agrees definitions fuel (known name proposition found).2
  | termApp proof argument ih =>
      have earlier := ih safeContext normalContext payload.1
      simp only [infer, inferProof, earlier]
      cases parent : inferProof environment fuel context.typeDepth context.terms context.hypotheses proof with
      | none => rfl
      | some proposition =>
          cases proposition <;> try rfl
          rename_i domain body
          cases typed : inferTerm environment context.typeDepth context.terms argument with
          | none => rfl
          | some actual =>
              by_cases same : actual = domain
              · subst actual
                simp only [Bind.bind, Option.bind, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
                cases expanded : deltaNormalize environment fuel argument with
                | none => rfl
                | some normal =>
                    have derived := proves_of_infer (context := context) parent
                    have safeBody : Protected body := (proof_invariants definitions known derived safeContext payload.1).2
                    have normalResult := inferred_normal derived normalContext
                    have normalBody : Normal environment body := normalResult
                    have safeArgument := (delta_invariants environment definitions fuel argument normal expanded).2 payload.2
                    have correspondence := SourcePublicationNormalization.normalize_agrees fuel
                      (protected_instantiate safeBody safeArgument 0)
                    simp only [publication_substitution_agrees safeBody]
                    exact correspondence.trans (application_normalization environment fuel normalBody expanded).symm
              · simp [same]
  | proofApp function argument ihf iha =>
      simp only [infer, inferProof, ihf safeContext normalContext payload.1,
        iha safeContext normalContext payload.2]
      rfl
  | termLam type proof ih =>
      have earlier := ih (safeContext.termBinder type) (contextNormal_termBinder normalContext type) payload
      simpa only [infer, inferProof, Context.termBinder] using congrArg
        (fun (result : Option Tm) => if !type.plainWellFormed context.typeDepth then none else do return Tm.all type (← result)) earlier
  | proofLam proposition proof ih =>
      have normalization : normalize environment fuel proposition = MathdataKernel.normalize environment fuel proposition :=
        SourcePublicationNormalization.expanded_normalize_agrees definitions fuel payload.1
      simp only [infer, inferProof, normalization]
      cases typed : inferTerm environment context.typeDepth context.terms proposition with
      | none => rfl
      | some type =>
          by_cases isProp : type = .prop
          · subst type
            simp only [Bind.bind, Option.bind, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
            cases normalized : MathdataKernel.normalize environment fuel proposition with
            | none => rfl
            | some normal =>
                obtain ⟨scope, safe⟩ := full_normalize_invariants definitions fuel normalized
                have nextSafe := safeContext.proofBinder (scope _ (inferTerm_scoped typed)) (safe payload.1)
                have nextNormal : ContextNormal environment (context.proofBinder normal) := by
                  intro body member
                  rcases List.mem_cons.mp member with rfl | old
                  · exact normalize_result normalized
                  · exact normalContext body old
                exact congrArg (fun (result : Option Tm) => do return Tm.imp normal (← result)) (ih nextSafe nextNormal payload.2)
          · simp [isProp]
  | typeApp proof type ih => simp only [infer, inferProof, ih safeContext normalContext payload]; rfl
  | typeLam proof ih =>
      have nextNormal : ContextNormal environment context.typeBinder := by intro body member; cases member
      have earlier := ih (ContextSafe.typeBinder context) nextNormal payload
      simpa only [infer, inferProof, Context.typeBinder] using congrArg
        (fun (result : Option Tm) => if context.terms.isEmpty && context.hypotheses.isEmpty then do return Tm.typeAll (← result) else none) earlier

/-- At the closed entry point both context invariants follow from emptiness.
The remaining premises are executable admission checks on selected data. -/
theorem closed_infer_agrees {environment : Environment} (definitions : Definitions environment)
    (known : Known environment) (fuel : Nat) {proof : Pf} (payload : ProofPayload proof) :
    infer environment fuel 0 [] [] proof = inferProof environment fuel 0 [] [] proof :=
  infer_agrees definitions known fuel (context := ⟨0, [], []⟩)
    (by intro body member; cases member) (by intro body member; cases member) payload

def check (environment : Environment) (fuel depth : Nat) (terms : List Tp)
    (hypotheses : List Tm) (proof : Pf) (proposition : Tm) : Bool :=
  match normalize environment fuel proposition, infer environment fuel depth terms hypotheses proof with
  | some expected, some actual => decide (actual = expected)
  | _, _ => false

theorem closed_check_agrees {environment : Environment} (definitions : Definitions environment)
    (known : Known environment) (fuel : Nat) {proof : Pf} {proposition : Tm}
    (payload : ProofPayload proof) (safeClaim : Protected proposition) :
    check environment fuel 0 [] [] proof proposition = checkProof environment fuel 0 [] [] proof proposition := by
  have normal := SourcePublicationNormalization.expanded_normalize_agrees definitions fuel safeClaim
  have inferred := closed_infer_agrees definitions known fuel payload
  unfold check
  rw [inferred]
  change normalize environment fuel proposition = MathdataKernel.normalize environment fuel proposition at normal
  rw [normal]
  cases normalized : MathdataKernel.normalize environment fuel proposition <;>
    cases derived : inferProof environment fuel 0 [] [] proof <;>
    simp [checkProof, checkNormalizedProof, normalized, derived]

end Mettapedia.Languages.Megalodon.PublicationProofRefinement

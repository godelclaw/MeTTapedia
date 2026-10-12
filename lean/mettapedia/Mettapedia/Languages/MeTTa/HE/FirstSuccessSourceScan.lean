import Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceApplicability

/-!
# Constructed first-success scan through actual qualified callbacks

Visited nonfunction, wrong-arity and closed incompatible return candidates
construct independent rejection replies. A successful wildcard-domain callback
constructs a selected reply from its actual ordered binding output. Every
unvisited suffix remains unresolved.
The source strategy, retained native scan and independent candidate judgment
then agree on the selected arrow. Earlier rejection blocks cannot add branches
after that success. The source's repeated raw type paths remain occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceScan

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type Spec.Eval FirstSuccessSourceApplicability

theorem applicable_lengths {space : Space} {arguments domains : List Atom}
    {incoming outgoing : Bindings}
    (applicable : ArgumentsApplicableRel space arguments domains incoming outgoing) :
    arguments.length = domains.length := by
  induction applicable with
  | nil => rfl
  | cons _ _ _ ih => simp only [List.length_cons, ih]

theorem wrong_arity_excludes_success (space : Space) (operator returned expected : Atom)
    (arguments domains : List Atom) (incoming outgoing : Bindings)
    (different : arguments.length ≠ domains.length) :
    ¬ApplicationSuccessRel space (.expression (operator :: arguments))
      (.expression (.symbol "->" :: (domains ++ [returned]))) expected incoming outgoing := by
  intro success
  cases success with
  | mk shape arrow argumentsApplicable _ =>
      obtain ⟨rfl, rfl⟩ := List.cons.inj (Atom.expression.inj shape)
      have sameDomains := FunctionTypeRel.unique arrow (show FunctionTypeRel
        (.expression (.symbol "->" :: (domains ++ [returned]))) domains returned from rfl)
      exact different (sameDomains.1 ▸ applicable_lengths argumentsApplicable)

/-- An inspected prefix is earned by grammar and arity facts, not by a
callback-soundness field assumed for every candidate. -/
inductive RejectedPrefix (operator expected : Atom) (arguments : List Atom) :
    List Atom → List NativeSelectedTypeScan.Candidate → Prop where
  | nil : RejectedPrefix operator expected arguments [] []
  | nonFunction {candidate candidates replies} :
      (¬∃ domains returned, FunctionTypeRel candidate domains returned) →
      RejectedPrefix operator expected arguments candidates replies →
      RejectedPrefix operator expected arguments (candidate :: candidates)
        (⟨candidate, .nonFunction⟩ :: replies)
  | wrongArity {domains : List Atom} {returned : Atom} {candidates replies} :
      arguments.length ≠ domains.length →
      RejectedPrefix operator expected arguments candidates replies →
      RejectedPrefix operator expected arguments
        (.expression (.symbol "->" :: (domains ++ [returned])) :: candidates)
        (⟨.expression (.symbol "->" :: (domains ++ [returned])),
          .error [mkError (.expression (operator :: arguments)) .incorrectNumberOfArguments]⟩ :: replies)
  | badReturn {domains : List Atom} {returned : Atom} {candidates replies} :
      List.Forall₂ (fun _ domain => WildcardDomain domain) arguments domains →
      Spec.Type.Presentation.TypeSubst.typeVars expected = [] →
      Spec.Type.Presentation.TypeSubst.typeVars returned = [] →
      (¬ClosedTypeFits expected returned) →
      RejectedPrefix operator expected arguments candidates replies →
      RejectedPrefix operator expected arguments
        (.expression (.symbol "->" :: (domains ++ [returned])) :: candidates)
        (⟨.expression (.symbol "->" :: (domains ++ [returned])),
          .error [mkError (.expression (operator :: arguments)) (.badType expected returned)]⟩ :: replies)

theorem rejected_prefix_sourceTypes {operator expected : Atom} {arguments candidates : List Atom}
    {replies : List NativeSelectedTypeScan.Candidate}
    (visited : RejectedPrefix operator expected arguments candidates replies) :
    NativeSelectedTypeScan.sourceTypes replies = candidates := by
  induction visited <;> simp_all [NativeSelectedTypeScan.sourceTypes]

theorem rejected_prefix_retains_selected
    {operator expected : Atom} {arguments candidates : List Atom}
    {replies : List NativeSelectedTypeScan.Candidate}
    (visited : RejectedPrefix operator expected arguments candidates replies)
    (space : Space) (incoming : Bindings) (fuel : Nat) (suffix : List Atom)
    (policy : SelectedTypePolicy) (alternatives : List Bindings)
    (selected : FirstSuccessRecursiveStrategy.select space (.expression (operator :: arguments))
      expected incoming (fuel + 1) suffix = .selected policy alternatives) :
    FirstSuccessRecursiveStrategy.select space (.expression (operator :: arguments))
      expected incoming (fuel + 1) (candidates ++ suffix) = .selected policy alternatives := by
  induction visited with
  | nil => exact selected
  | nonFunction notFunction _ ih =>
      simp only [List.cons_append, FirstSuccessRecursiveStrategy.select,
        (FirstSuccessRecursiveStrategy.readPolicy_none_iff _).mpr notFunction,
        FirstSuccessRecursiveStrategy.noteNonFunction, ih]
  | @wrongArity domains returned candidates replies different _ ih =>
      obtain ⟨parsedPolicy, parsed, _⟩ := FirstSuccessRecursiveStrategy.readPolicy_complete
        (show FunctionTypeRel (.expression (.symbol "->" :: (domains ++ [returned])))
          domains returned from rfl)
      simp only [List.cons_append, FirstSuccessRecursiveStrategy.select, parsed,
        source_wrong_arity space operator returned expected arguments domains incoming fuel different,
        ih, FirstSuccessRecursiveStrategy.noteErrors]
  | @badReturn domains returned candidates replies wildcards expectedClosed returnedClosed incompatible _ ih =>
      obtain ⟨parsedPolicy, parsed, _⟩ := FirstSuccessRecursiveStrategy.readPolicy_complete
        (show FunctionTypeRel (.expression (.symbol "->" :: (domains ++ [returned])))
          domains returned from rfl)
      simp only [List.cons_append, FirstSuccessRecursiveStrategy.select, parsed,
        wildcard_applicability_failure space operator expected returned arguments domains incoming fuel
          wildcards expectedClosed returnedClosed incompatible,
        ih, FirstSuccessRecursiveStrategy.noteErrors]

theorem rejected_prefix_independent
    {operator expected : Atom} {arguments candidates : List Atom}
    {replies : List NativeSelectedTypeScan.Candidate}
    (visited : RejectedPrefix operator expected arguments candidates replies)
    (space : Space) (incoming : Bindings) (suffix : List NativeSelectedTypeScan.Candidate)
    (outcome : FunctionCandidateScanOutcome)
    (selected : NativeSelectedTypeScan.RepliesRel PublishedCandidateApplicabilityRel
      space (.expression (operator :: arguments)) expected incoming suffix outcome) :
    ∃ complete, NativeSelectedTypeScan.RepliesRel PublishedCandidateApplicabilityRel
      space (.expression (operator :: arguments)) expected incoming (replies ++ suffix) complete ∧
      (∀ policy output, outcome = .success policy output → complete = outcome) := by
  induction visited with
  | nil => exact ⟨outcome, selected, fun _ _ _ => rfl⟩
  | nonFunction notFunction _ ih =>
      obtain ⟨tailOutcome, tailRelated, tailSelected⟩ := ih
      refine ⟨NativeSelectedTypeScan.noteNonFunction tailOutcome,
        .nonFunction notFunction tailRelated, ?_⟩
      intro policy output success
      rw [tailSelected policy output success, success]
      rfl
  | @wrongArity domains returned candidates replies different _ ih =>
      obtain ⟨tailOutcome, tailRelated, tailSelected⟩ := ih
      refine ⟨NativeSelectedTypeScan.noteErrors
        [mkError (.expression (operator :: arguments)) .incorrectNumberOfArguments] tailOutcome,
        .failed rfl ?_ (.error (independent_wrong_arity space operator returned expected
          arguments domains incoming different)) (by simp) tailRelated, ?_⟩
      · intro policy output successful
        cases successful with
        | success _ applicable =>
            cases applicable with
            | success derivation =>
                exact wrong_arity_excludes_success space operator returned expected
                  arguments domains incoming output different derivation
      · intro policy output success
        rw [tailSelected policy output success, success]
        rfl

  | @badReturn domains returned candidates replies wildcards expectedClosed returnedClosed incompatible _ ih =>
      obtain ⟨tailOutcome, tailRelated, tailSelected⟩ := ih
      refine ⟨NativeSelectedTypeScan.noteErrors
        [mkError (.expression (operator :: arguments)) (.badType expected returned)] tailOutcome,
        .failed rfl ?_ (.error (independent_bad_return space operator expected returned
          arguments domains incoming wildcards expectedClosed returnedClosed incompatible)) (by simp)
          tailRelated, ?_⟩
      · intro policy output successful
        cases successful with
        | success _ applicable =>
            cases applicable with
            | success derivation =>
                exact closed_return_excludes_success space operator expected returned arguments domains
                  incoming output expectedClosed returnedClosed incompatible derivation
      · intro policy output success
        rw [tailSelected policy output success, success]
        rfl

/-- The actual callback's selected policy and each of its ordered binding
occurrences construct a native replay and the independent first-success scan. -/
theorem raw_selected_replay (space : Space) (operator returned : Atom)
    (arguments : List Atom) (incoming : Bindings) (fuel : Nat) (suffix : List Atom) :
    ∃ policy, policy.argumentTypes = List.replicate arguments.length Atom.atomType ∧
      policy.returnType = returned ∧
      FirstSuccessRecursiveStrategy.select space (.expression (operator :: arguments))
        Atom.undefinedType incoming (fuel + 1)
        (policy.functionType :: suffix) =
          .selected policy (List.replicate (pathCount space arguments) incoming) ∧
      NativeSelectedTypeScan.RepliesRel PublishedCandidateApplicabilityRel
        space (.expression (operator :: arguments)) Atom.undefinedType incoming
        (⟨policy.functionType, .success policy incoming⟩ :: NativeSelectedTypeScan.unresolved suffix)
        (.success policy incoming) := by
  let candidate := Atom.expression (.symbol "->" ::
    (List.replicate arguments.length Atom.atomType ++ [returned]))
  obtain ⟨policy, parsed, sameCandidate, domains, returnType⟩ :=
    FirstSuccessRecursiveStrategy.readPolicy_complete
      (show FunctionTypeRel candidate (List.replicate arguments.length Atom.atomType) returned from rfl)
  refine ⟨policy, domains, returnType, ?_, ?_⟩
  · rw [sameCandidate]
    simp only [FirstSuccessRecursiveStrategy.select, parsed, candidate,
      source_raw_applicability]
  · have application : ApplicationSuccessRel space (.expression (operator :: arguments))
        policy.functionType Atom.undefinedType incoming incoming := by
      rw [sameCandidate]
      exact source_raw_applicability_sound space operator returned arguments incoming incoming
        (by simp [pathCount_positive space arguments |>.ne'])
    have published : PublishedCandidateApplicabilityRel space (.expression (operator :: arguments))
        policy.functionType Atom.undefinedType incoming (.success policy incoming) := by
      cases policy with
      | mk functionType argumentTypes returnType isFunction =>
          exact .success isFunction (.success application)
    exact .selected policy.isFunction published

/-- An arbitrary earned rejection prefix and unvisited suffix connect the
actual source callback's complete binding occurrence list to the independent
first-success scan. Nothing inspects the suffix after the selected arrow. -/
theorem raw_prefix_selected
    {operator : Atom} {arguments candidates : List Atom}
    {replies : List NativeSelectedTypeScan.Candidate}
    (visited : RejectedPrefix operator Atom.undefinedType arguments candidates replies)
    (space : Space) (returned : Atom) (incoming : Bindings) (fuel : Nat) (suffix : List Atom) :
    ∃ policy, policy.argumentTypes = List.replicate arguments.length Atom.atomType ∧
      policy.returnType = returned ∧
      FirstSuccessRecursiveStrategy.select space (.expression (operator :: arguments))
        Atom.undefinedType incoming (fuel + 1)
        (candidates ++ policy.functionType :: suffix) =
          .selected policy (List.replicate (pathCount space arguments) incoming) ∧
      FunctionCandidateScanRel PublishedCandidateApplicabilityRel
        space (.expression (operator :: arguments)) Atom.undefinedType incoming
        (candidates ++ policy.functionType :: suffix) (.success policy incoming) := by
  obtain ⟨policy, domains, resultType, selected, independent⟩ :=
    raw_selected_replay space operator returned arguments incoming fuel suffix
  refine ⟨policy, domains, resultType,
    rejected_prefix_retains_selected visited space incoming fuel _ _ _ selected, ?_⟩
  obtain ⟨outcome, completed, firstSuccess⟩ :=
    rejected_prefix_independent visited space incoming _ _ independent
  have exactOutcome := firstSuccess policy incoming rfl
  subst outcome
  have scan := NativeSelectedTypeScan.replies_to_specification completed
  have orderedSources : NativeSelectedTypeScan.sourceTypes
      (replies ++ ⟨policy.functionType, .success policy incoming⟩ ::
        NativeSelectedTypeScan.unresolved suffix) =
        candidates ++ policy.functionType :: suffix := by
    simp only [NativeSelectedTypeScan.sourceTypes, List.map_append, List.map_cons]
    rw [show replies.map NativeSelectedTypeScan.Candidate.source = candidates from
      rejected_prefix_sourceTypes visited,
      show (NativeSelectedTypeScan.unresolved suffix).map
        NativeSelectedTypeScan.Candidate.source = suffix from
        NativeSelectedTypeScan.sourceTypes_unresolved suffix]
  rw [orderedSources] at scan
  exact scan

/-- A checked wildcard argument policy and closed return projection select
one coherent arrow after an independently rejected prefix. The callback's
complete occurrence list and the independent scan remain distinct outputs. -/
theorem wildcard_prefix_selected
    {operator expected : Atom} {arguments candidates : List Atom}
    {replies : List NativeSelectedTypeScan.Candidate}
    (visited : RejectedPrefix operator expected arguments candidates replies)
    (space : Space) (returned : Atom) (domains : List Atom) (incoming : Bindings)
    (fuel : Nat) (suffix : List Atom)
    (wildcards : List.Forall₂ (fun _ domain => WildcardDomain domain) arguments domains)
    (expectedClosed : Spec.Type.Presentation.TypeSubst.typeVars expected = [])
    (returnedClosed : Spec.Type.Presentation.TypeSubst.typeVars returned = [])
    (fits : ClosedTypeFits expected returned)
    (enough : sizeOf expected + sizeOf returned + 2 ≤ fuel) :
    ∃ policy, policy.argumentTypes = domains ∧ policy.returnType = returned ∧
      FirstSuccessRecursiveStrategy.select space (.expression (operator :: arguments))
        expected incoming (fuel + 1) (candidates ++ policy.functionType :: suffix) =
          .selected policy (List.replicate (pathCount space arguments) incoming) ∧
      FunctionCandidateScanRel PublishedCandidateApplicabilityRel
        space (.expression (operator :: arguments)) expected incoming
        (candidates ++ policy.functionType :: suffix) (.success policy incoming) := by
  let candidate := Atom.expression (.symbol "->" :: (domains ++ [returned]))
  obtain ⟨policy, parsed, sameCandidate, argumentTypes, returnType⟩ :=
    FirstSuccessRecursiveStrategy.readPolicy_complete (show FunctionTypeRel candidate domains returned from rfl)
  have selected : FirstSuccessRecursiveStrategy.select space (.expression (operator :: arguments))
      expected incoming (fuel + 1) (policy.functionType :: suffix) =
        .selected policy (List.replicate (pathCount space arguments) incoming) := by
    rw [sameCandidate]
    simp only [FirstSuccessRecursiveStrategy.select, parsed, candidate,
      wildcard_applicability_success space operator expected returned arguments domains incoming fuel
        wildcards expectedClosed returnedClosed fits enough]
  have application : ApplicationSuccessRel space (.expression (operator :: arguments))
      policy.functionType expected incoming incoming := by
    rw [sameCandidate]
    exact independent_wildcard_application space operator expected returned arguments domains incoming
      wildcards expectedClosed returnedClosed fits
  have one : NativeSelectedTypeScan.RepliesRel PublishedCandidateApplicabilityRel
      space (.expression (operator :: arguments)) expected incoming
      (⟨policy.functionType, .success policy incoming⟩ :: NativeSelectedTypeScan.unresolved suffix)
      (.success policy incoming) := .selected policy.isFunction (.success policy.isFunction (.success application))
  obtain ⟨complete, related, retained⟩ := rejected_prefix_independent visited space incoming _ _ one
  rw [retained policy incoming rfl] at related
  have scan := NativeSelectedTypeScan.replies_to_specification related
  have sourceTypes : NativeSelectedTypeScan.sourceTypes
      (replies ++ (⟨policy.functionType, .success policy incoming⟩ :: NativeSelectedTypeScan.unresolved suffix)) =
      candidates ++ policy.functionType :: suffix := by
    simp only [NativeSelectedTypeScan.sourceTypes, List.map_append, List.map_cons]
    rw [show replies.map NativeSelectedTypeScan.Candidate.source = candidates from
      rejected_prefix_sourceTypes visited,
      show (NativeSelectedTypeScan.unresolved suffix).map NativeSelectedTypeScan.Candidate.source =
        suffix from NativeSelectedTypeScan.sourceTypes_unresolved suffix]
  rw [sourceTypes] at scan
  exact ⟨policy, argumentTypes, returnType,
    rejected_prefix_retains_selected visited space incoming fuel _ _ _ selected, scan⟩

end Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceScan

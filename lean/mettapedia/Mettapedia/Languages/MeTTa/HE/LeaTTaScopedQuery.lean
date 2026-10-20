import Mettapedia.Languages.MeTTa.HE.LeaTTaBindingMaterialization
import Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationExactConformance
import Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal
import Mettapedia.Languages.MeTTa.HE.LeaTTaMinimalControlReturn
open Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory
open Mettapedia.Languages.MeTTa.HE.BindingComposition
open Mettapedia.Languages.MeTTa.HE.MatchSizeTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.ModelTransport

/-!
# Independent query derivations for the actual LeaTTa work-item generator

The existing executable `queryOpItemsOfRule` supplies matching, merge, loop
filtering, instantiation and continuation handling. Its actual freshening is
proved hygienic against the complete projected binding support and retained
stack scope. Pattern representation and logical binding correspondence are
constructed here rather than required as caller-supplied correspondence laws.

The scope view contains names only; it is not a representation of the whole
interpreter state. The complete scan preserves physical declaration positions, freshening
counters and local branch ordinals through the actual static, added and
imported candidate tables. Its full spawned list enters the existing retained
machine with the original world and callers. No native C implementation
refinement or universal source grammar is claimed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaScopedQuery

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open LeaTTaBridge LeaTTaTypeConformance LeaTTaSpecConformance
open Spec.Match.Merge Spec.Eval.Steps

def liveScope (previous : Metta.Minimal.Stack) : List Atom :=
  (Metta.Minimal.liveStackVars previous).map Atom.var

theorem liveScope_name_mem {previous : Metta.Minimal.Stack} {atom : Atom} {name : String}
    (member : atom ∈ liveScope previous) (occurrence : name ∈ (encodeModelAtom atom).vars) :
    name ∈ Metta.Minimal.liveStackVars previous := by
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  have equal : name = original := by
    simpa only [encodeModelAtom, Metta.Atom.vars, List.mem_singleton] using occurrence
  subst name
  exact originalMember

theorem actual_scope_covers (previous : Metta.Minimal.Stack) (query : Atom)
    (incoming : Metta.Bindings) (image : LeaBindingsHEImage incoming) :
    ∀ name, QueryVisibleName (liveScope previous) query (QueryBindingProjection.project incoming) name →
      name ∈ Metta.Minimal.queryOpAvoid previous (encodeModelAtom query) incoming := by
  intro name visible
  have member := (EquationScope.mem_visibleNames_iff _ _ _ name).mpr visible
  simp only [EquationScope.visibleNames, List.mem_append, List.mem_flatMap] at member
  simp only [Metta.Minimal.queryOpAvoid, List.mem_append]
  rcases member with (queryName | liveName) | bindingName
  · exact Or.inl (Or.inr queryName)
  · obtain ⟨atom, atomMember, occurrence⟩ := liveName
    exact Or.inr (liveScope_name_mem atomMember occurrence)
  · exact Or.inl (Or.inl (QueryBindingProjection.binding_name_mem image bindingName))

def freshRule (previous : Metta.Minimal.Stack) (query : Atom) (incoming : Metta.Bindings)
    (counter : Nat) (lhs rhs : Atom) : Atom × Atom :=
  LeaTTaTypePresentationExactConformance.EquationFreshening.freshRule
    (Metta.Minimal.queryOpAvoid previous (encodeModelAtom query) incoming) counter lhs rhs

theorem freshRule_alphaVariant (previous : Metta.Minimal.Stack) (query : Atom)
    (incoming : Metta.Bindings) (image : LeaBindingsHEImage incoming) (counter : Nat) (lhs rhs : Atom) :
    AlphaVariantRel (liveScope previous) query (QueryBindingProjection.project incoming) lhs rhs
      (freshRule previous query incoming counter lhs rhs).1
      (freshRule previous query incoming counter lhs rhs).2 :=
  LeaTTaTypePresentationExactConformance.EquationFreshening.freshRule_alphaVariant_of_covers
    _ _ _ _ _ _ _
    (actual_scope_covers previous query incoming image)

/-- Each emitted item carries the exact stored row, fresh rule and reached
binding state that generated it. Equal declarations at other positions do not
justify this occurrence. -/
theorem queryOpItemsOfRule_occurrence_sound
    {space : Space} {previous : Metta.Minimal.Stack} {query lhs rhs : Atom}
    {incoming : Metta.Bindings} {counter position : Nat} {item : Metta.Minimal.Item}
    (stored : space.atoms[position]? = some (.expression [.symbol "=", lhs, rhs]))
    (image : LeaBindingsHEImage incoming) (runtime : LeaRuntimeBindingInvariant incoming)
    (member : item ∈ Metta.Minimal.queryOpItemsOfRule previous (encodeModelAtom query)
      incoming counter (encodeModelAtom lhs, encodeModelAtom rhs)) :
    ∃ emitted output merged freshPattern freshRhs matched,
      EquationQueryOccurrenceRel space (liveScope previous) query
        (QueryBindingProjection.project incoming) position lhs rhs freshPattern freshRhs
        matched emitted output ∧
      item = Metta.Minimal.evalResult previous (encodeModelAtom emitted) merged ∧
      ScopedEquationQuery.BindingInvariant (QueryBindingProjection.project merged) merged ∧
      ScopedEquationQuery.BindingInvariant output merged ∧
      emitted = decodeModelAtom (Metta.instantiate merged (encodeModelAtom freshRhs)) := by
  obtain ⟨matched, matchedMember, merged, mergedMember, loopFree, itemEq⟩ :=
    (mem_queryOpItemsOfRule_iff _ _ _ _ _ _).mp member
  let fresh := freshRule previous query incoming counter lhs rhs
  have translation := LeaTTaTypePresentationExactConformance.EquationFreshening.freshRule_translation
    (Metta.Minimal.queryOpAvoid previous (encodeModelAtom query) incoming) counter lhs rhs
  have patternTranslation := congrArg Prod.fst translation
  have rhsTranslation := congrArg Prod.snd translation
  simp only at patternTranslation rhsTranslation
  change encodeModelAtom fresh.1 = _ at patternTranslation
  change encodeModelAtom fresh.2 = _ at rhsTranslation
  rw [← patternTranslation] at matchedMember
  obtain ⟨specMatched, output, matchDerivation, mergeDerivation, next, observation⟩ :=
    queryOp_hit_observational_sound (rhs := encodeModelAtom fresh.2)
      (QueryBindingProjection.paired incoming image runtime).semantic matchedMember mergedMember loopFree
  have matchedImage : LeaBindingsHEImage matched :=
    leaMatchAtoms_result_heImage (leaAtomHEImage_encodeModelAtom fresh.1)
      (leaAtomHEImage_encodeModelAtom query) matchedMember
  have mergedImage : LeaBindingsHEImage merged :=
    leaMerge_result_image image matchedImage mergedMember
  have emittedImage : LeaAtomHEImage (Metta.instantiate merged (encodeModelAtom fresh.2)) :=
    instantiate_heImage mergedImage _ (leaAtomHEImage_encodeModelAtom fresh.2)
  let emitted := decodeModelAtom (Metta.instantiate merged (encodeModelAtom fresh.2))
  have projected := QueryBindingProjection.paired merged mergedImage next.runtime
  have satisfied : HEBindingSatisfied (leaClassSolution merged) output :=
    (next.solutionTheory (leaClassSolution merged)).mpr next.runtime.canonical.1
  refine ⟨emitted, output, merged, fresh.1, fresh.2, specMatched, ?_, ?_,
    projected, ⟨next, mergedImage⟩, rfl⟩
  · refine ⟨stored, ⟨freshRule_alphaVariant _ _ _ image _ _ _, matchDerivation⟩,
      (mergeDerivation.logicalMerge
        ⟨_, specTypeBindingSatisfied_of_heBindingSatisfied satisfied⟩).comm, ?_⟩
    intro valuation outputSatisfied
    unfold HEAtomEquationSatisfied
    rw [encodeModelAtom_decodeModelAtom_of_heImage emittedImage]
    exact observation valuation outputSatisfied
  · rw [itemEq, ← rhsTranslation]
    rw [encodeModelAtom_decodeModelAtom_of_heImage emittedImage]

/-- A returned work item constructs its independent equation-query derivation,
exact executable continuation and next representable, paired binding state. -/
private theorem queryOpItemsOfRule_sound_witness {space : Space} {previous : Metta.Minimal.Stack}
    {query lhs rhs : Atom} {incoming : Metta.Bindings} {counter : Nat} {item : Metta.Minimal.Item}
    (stored : .expression [.symbol "=", lhs, rhs] ∈ space.atoms)
    (image : LeaBindingsHEImage incoming) (runtime : LeaRuntimeBindingInvariant incoming)
    (member : item ∈ Metta.Minimal.queryOpItemsOfRule previous (encodeModelAtom query)
      incoming counter (encodeModelAtom lhs, encodeModelAtom rhs)) :
    ∃ emitted output merged,
      EquationQueryCandidateRel space (liveScope previous) query
          (QueryBindingProjection.project incoming) emitted output ∧
        item = Metta.Minimal.evalResult previous (encodeModelAtom emitted) merged ∧
        ScopedEquationQuery.BindingInvariant (QueryBindingProjection.project merged) merged ∧
        (∀ valuation,
          HEBindingSatisfied valuation output ↔
            HEBindingSatisfied valuation (QueryBindingProjection.project merged)) ∧
        ScopedEquationQuery.BindingInvariant output merged ∧
        ∃ rawRhs,
          EquationQueryCandidateRel space (liveScope previous) query
            (QueryBindingProjection.project incoming) rawRhs output ∧
          emitted = decodeModelAtom (Metta.instantiate merged (encodeModelAtom rawRhs)) := by
  obtain ⟨position, storedAt⟩ := List.mem_iff_getElem?.mp stored
  obtain ⟨emitted, output, merged, pattern, rawRhs, matched, occurrence, itemEq,
    projected, paired, emittedEq⟩ :=
    queryOpItemsOfRule_occurrence_sound storedAt image runtime member
  refine ⟨emitted, output, merged, occurrence.candidate, itemEq, projected, ?_,
    paired, rawRhs, ?_, emittedEq⟩
  · intro valuation
    exact (paired.semantic.solutionTheory valuation).trans
      (projected.semantic.solutionTheory valuation).symm
  · refine ⟨pattern, rawRhs, matched,
      ⟨lhs, rhs, stored, occurrence.selected⟩,
      occurrence.result.1, ?_⟩
    intro valuation satisfied
    rfl

theorem queryOpItemsOfRule_sound {space : Space} {previous : Metta.Minimal.Stack}
    {query lhs rhs : Atom} {incoming : Metta.Bindings} {counter : Nat} {item : Metta.Minimal.Item}
    (stored : .expression [.symbol "=", lhs, rhs] ∈ space.atoms)
    (image : LeaBindingsHEImage incoming) (runtime : LeaRuntimeBindingInvariant incoming)
    (member : item ∈ Metta.Minimal.queryOpItemsOfRule previous (encodeModelAtom query)
      incoming counter (encodeModelAtom lhs, encodeModelAtom rhs)) :
    ∃ emitted output merged,
      EquationQueryCandidateRel space (liveScope previous) query
          (QueryBindingProjection.project incoming) emitted output ∧
        item = Metta.Minimal.evalResult previous (encodeModelAtom emitted) merged ∧
        ScopedEquationQuery.BindingInvariant (QueryBindingProjection.project merged) merged ∧
        (∀ valuation,
          HEBindingSatisfied valuation output ↔
            HEBindingSatisfied valuation (QueryBindingProjection.project merged)) ∧
        ScopedEquationQuery.BindingInvariant output merged := by
  obtain ⟨emitted, output, merged, candidate, itemEq, projected, theory, actual, _⟩ :=
    queryOpItemsOfRule_sound_witness stored image runtime member
  exact ⟨emitted, output, merged, candidate, itemEq, projected, theory, actual⟩

/-- An actual equation hit earns its independent producer materialization
under the actual output frame. Only the equation producer resolves this raw
RHS; raw callbacks and the general completion judgment are unchanged.

The saved continuation and native frame remain those of the original item.
Residual representatives are compared by alpha observation, while invocation
requires its own local query guards and completion derivation. -/
theorem queryOpItemsOfRule_producer_materialization
    {space : Space} {previous : Metta.Minimal.Stack} {query lhs rhs : Atom}
    {incoming : Metta.Bindings} {counter : Nat} {item : Metta.Minimal.Item}
    (stored : .expression [.symbol "=", lhs, rhs] ∈ space.atoms)
    (image : LeaBindingsHEImage incoming) (runtime : LeaRuntimeBindingInvariant incoming)
    (member : item ∈ Metta.Minimal.queryOpItemsOfRule previous (encodeModelAtom query)
      incoming counter (encodeModelAtom lhs, encodeModelAtom rhs)) :
    ∃ rawRhs normalized emitted output merged,
      EquationQueryCandidateRel space (liveScope previous) query
        (QueryBindingProjection.project incoming) rawRhs output ∧
      ScopedEquationQuery.BindingInvariant output merged ∧
      ScopedEquationQuery.BindingInvariant (QueryBindingProjection.project merged) merged ∧
      item = Metta.Minimal.evalResult previous (encodeModelAtom emitted) merged ∧
      emitted = decodeModelAtom (Metta.instantiate merged (encodeModelAtom rawRhs)) ∧
      Spec.Type.Presentation.BindingTheory.BindingMaterializationRel output rawRhs normalized ∧
      Spec.Type.Presentation.Alpha.ObservedTypeAlphaRel normalized emitted ∧
      (Spec.Eval.Minimal.IsFunction normalized ↔ Spec.Eval.Minimal.IsFunction emitted) ∧
      (∀ body, normalized = .expression [.symbol "function", body] →
        ∃ actualBody, emitted = .expression [.symbol "function", actualBody] ∧
          Spec.Type.Presentation.Alpha.ObservedTypeAlphaRel body actualBody) ∧
      (∀ dispatch typing caller result,
        ¬Spec.Eval.Minimal.HostCall dispatch query →
        Spec.Eval.Minimal.embeddedInstruction query = false →
        Spec.Eval.Minimal.CoreInvocationResultRel space dispatch (liveScope previous)
          normalized output result (typing := typing) (caller := some query) →
        Spec.Eval.Minimal.CoreInvocationRel space dispatch (liveScope previous)
          query (QueryBindingProjection.project incoming) result (typing := typing) (caller := caller)) ∧
      ((∀ tail, normalized ≠ .expression (.symbol "function" :: tail)) →
        (∀ dispatch typing caller,
          ¬Spec.Eval.Minimal.HostCall dispatch query →
          Spec.Eval.Minimal.embeddedInstruction query = false →
          Spec.Eval.Minimal.CoreInvocationRel space dispatch (liveScope previous)
            query (QueryBindingProjection.project incoming) (normalized, output)
            (typing := typing) (caller := caller)) ∧
        item = Metta.Minimal.finItem previous (encodeModelAtom emitted) merged) := by
  obtain ⟨emitted, output, merged, _, itemEq, projected, _, paired, rawRhs, candidate, emittedEq⟩ :=
    queryOpItemsOfRule_sound_witness stored image runtime member
  obtain ⟨normalized, materialized, alpha⟩ :=
    QueryBindingProjection.exists_binding_materialization paired.semantic rawRhs
  rw [← emittedEq] at alpha
  have invoke : ∀ dispatch typing caller result,
      ¬Spec.Eval.Minimal.HostCall dispatch query →
      Spec.Eval.Minimal.embeddedInstruction query = false →
      Spec.Eval.Minimal.CoreInvocationResultRel space dispatch (liveScope previous)
        normalized output result (typing := typing) (caller := some query) →
      Spec.Eval.Minimal.CoreInvocationRel space dispatch (liveScope previous)
        query (QueryBindingProjection.project incoming) result (typing := typing) (caller := caller) := by
    intro dispatch typing caller result notHost notEmbedded completed
    exact .equation space query rawRhs normalized (QueryBindingProjection.project incoming)
      output result notHost notEmbedded candidate (.historical _ _) materialized completed
  refine ⟨rawRhs, normalized, emitted, output, merged, candidate, paired, projected,
    itemEq, emittedEq, materialized, alpha,
    Spec.Eval.Minimal.isFunction_of_observedTypeAlpha_iff alpha,
    fun _ shape => Spec.Eval.Minimal.functionBody_of_observedTypeAlpha alpha shape, invoke, ?_⟩
  intro raw
  refine ⟨?_, ?_⟩
  · intro dispatch typing caller notHost notEmbedded
    exact invoke dispatch typing caller (normalized, output) notHost notEmbedded
      (.raw space normalized output (fun ⟨body, shape⟩ => raw [body] shape))
  have actualRaw : ∀ tail, encodeModelAtom emitted ≠ .expr (.sym "function" :: tail) := by
    intro tail shape
    have decoded := congrArg decodeModelAtom shape
    have actualHead : ∃ values, emitted = .expression (.symbol "function" :: values) :=
      ⟨decodeModelAtoms tail, by simpa only [decodeModelAtom_encodeModelAtom,
        decodeModelAtom, decodeModelAtoms] using decoded⟩
    obtain ⟨sourceTail, sourceHead⟩ :=
      (Spec.Eval.Minimal.functionHead_of_observedTypeAlpha_iff alpha).mpr actualHead
    exact raw sourceTail sourceHead
  exact itemEq.trans (LeaTTaMinimalControlExecution.evalResult_raw_of_not_function_head
    previous (encodeModelAtom emitted) merged actualRaw)

/-- Any legal independent fresh variant of the same physical raw equation
produces an actual query work item. Its original saved continuation is passed
to `evalResult`, and its native bindings are retained rather than merged a
second time. The runtime fresh counter is independent of the physical row
position. Function completion and subsequent typed evaluation are separate.

Private names are compared by the constructed permutation and valuation
reindexing. Neither equality of raw binding records nor a count of semantic
derivations is asserted. -/
private theorem queryOpItemsOfRule_occurrence_arbitrary_alpha_witness
    {space : Space} {previous : Metta.Minimal.Stack}
    {query lhs rhs sourcePattern sourceRhs emitted : Atom}
    {incoming : Metta.Bindings} {matched output : Bindings} {counter position : Nat}
    (image : LeaBindingsHEImage incoming) (runtime : LeaRuntimeBindingInvariant incoming)
    (source : EquationQueryOccurrenceRel space (liveScope previous) query
      (QueryBindingProjection.project incoming) position lhs rhs sourcePattern sourceRhs
      matched emitted output) :
    ∃ permutation : Equiv.Perm String, ∃ actualEmitted targetMatched targetOutput nativeMatched merged item,
      (∀ name, QueryVisibleName (liveScope previous) query
        (QueryBindingProjection.project incoming) name → permutation name = name) ∧
      nativeMatched ∈ Metta.matchAtoms
        (encodeModelAtom (freshRule previous query incoming counter lhs rhs).1)
        (encodeModelAtom query) ∧
      merged ∈ Metta.Bindings.merge incoming nativeMatched ∧
      merged.hasLoop = false ∧
      item ∈ Metta.Minimal.queryOpItemsOfRule previous (encodeModelAtom query) incoming counter
        (encodeModelAtom lhs, encodeModelAtom rhs) ∧
      item = Metta.Minimal.evalResult previous (encodeModelAtom actualEmitted) merged ∧
      EquationQueryOccurrenceRel space (liveScope previous) query
        (QueryBindingProjection.project incoming) position lhs rhs
        (freshRule previous query incoming counter lhs rhs).1
        (freshRule previous query incoming counter lhs rhs).2
        targetMatched actualEmitted targetOutput ∧
      ScopedEquationQuery.BindingInvariant (QueryBindingProjection.project merged) merged ∧
      (∀ valuation,
        HEBindingSatisfied valuation (QueryBindingProjection.project merged) ↔
          HEBindingSatisfied (valuation ∘ permutation) output) ∧
      actualEmitted = decodeModelAtom (Metta.instantiate merged
        (encodeModelAtom (freshRule previous query incoming counter lhs rhs).2)) ∧
      ∀ valuation, HEBindingSatisfied valuation (QueryBindingProjection.project merged) →
        HEAtomEquationSatisfied valuation actualEmitted
          (Spec.Type.RuntimeRefinement.renameTypeVars permutation emitted) := by
  let paired := QueryBindingProjection.paired incoming image runtime
  obtain ⟨permutation, targetMatched, targetOutput, fixed, _, _, target, theory,
    targetNonvariable⟩ :=
    EquationFreshening.occurrence_alpha_transport paired.semantic.specAssignmentsNonVariable source
      (freshRule_alphaVariant previous query incoming image counter lhs rhs)
  let fresh := freshRule previous query incoming counter lhs rhs
  have disjoint : VarsDisjoint query fresh.1 := by
    intro name queryName freshName
    have avoided := LeaTTaTypePresentationExactConformance.EquationFreshening.freshRule_variables_avoid
      (Metta.Minimal.queryOpAvoid previous (encodeModelAtom query) incoming)
      counter lhs rhs name (List.mem_append_left _ freshName)
    exact avoided (by simp only [Metta.Minimal.queryOpAvoid, List.mem_append]; tauto)
  obtain ⟨sourceModel, sourceSatisfied⟩ := target.result.1.he_model
  have common := (target.result.1.he_solutions sourceModel).mp sourceSatisfied
  obtain ⟨callerFirst, callerFirstMerge, callerFirstSatisfied, _callerFirstShape⟩ :=
    Spec.Match.Completeness.exists_specMerge_of_solution
      common.2 paired.semantic.specAssignmentsNonVariable
      common.1 (Spec.Match.ModelTheory.specMatch_assignmentsNonVariable target.selected.2)
  have callerFirstTheory (valuation : String → Metta.Atom) :
      HEBindingSatisfied valuation targetOutput ↔ HEBindingSatisfied valuation callerFirst := by
    rw [target.result.1.he_solutions,
      Spec.Match.SolutionTheory.mergeRel_solution_iff callerFirstMerge, and_comm]
  obtain ⟨nativeMatched, merged, matchMember, mergeMember, loopFree, callerFirstEquivalent⟩ :=
    queryOp_hit_exists_of_spec paired.semantic.solutionTheory runtime.noFloat
      runtime.assignmentsNonVariable runtime.equalitiesIrreflexive disjoint
      target.selected.2 callerFirstMerge ⟨sourceModel, callerFirstSatisfied⟩
  have equivalent : LeaBindingSolutionTheoryEquiv targetOutput merged :=
    fun valuation => (callerFirstTheory valuation).trans (callerFirstEquivalent valuation)
  have matchedImage : LeaBindingsHEImage nativeMatched :=
    leaMatchAtoms_result_heImage (leaAtomHEImage_encodeModelAtom fresh.1)
      (leaAtomHEImage_encodeModelAtom query) matchMember
  have mergedImage := leaMerge_result_image image matchedImage mergeMember
  have mergedRuntime := runtime.merge_matchOutput
    (encodeModelAtom_noFloat fresh.1) (encodeModelAtom_noFloat query)
    matchMember mergeMember loopFree
  let actualEmitted := decodeModelAtom (Metta.instantiate merged (encodeModelAtom fresh.2))
  let item := Metta.Minimal.evalResult previous (encodeModelAtom actualEmitted) merged
  have emittedImage := instantiate_heImage mergedImage _ (leaAtomHEImage_encodeModelAtom fresh.2)
  have emittedTranslation : encodeModelAtom actualEmitted =
      Metta.instantiate merged (encodeModelAtom fresh.2) :=
    encodeModelAtom_decodeModelAtom_of_heImage emittedImage
  have projected := QueryBindingProjection.paired merged mergedImage mergedRuntime
  have projectedTheory (valuation : String → Metta.Atom) :
      HEBindingSatisfied valuation (QueryBindingProjection.project merged) ↔
        HEBindingSatisfied valuation targetOutput :=
    (projected.semantic.solutionTheory valuation).trans (equivalent valuation).symm
  have observation (valuation : String → Metta.Atom)
      (satisfied : HEBindingSatisfied valuation targetOutput) :
      HEAtomEquationSatisfied valuation actualEmitted
        (Spec.Type.RuntimeRefinement.renameTypeVars permutation emitted) := by
    unfold HEAtomEquationSatisfied
    rw [emittedTranslation]
    exact (anchored_observable_inert equivalent satisfied (encodeModelAtom fresh.2)).trans
      (target.result.2 valuation satisfied).symm
  have translation := LeaTTaTypePresentationExactConformance.EquationFreshening.freshRule_translation
    (Metta.Minimal.queryOpAvoid previous (encodeModelAtom query) incoming) counter lhs rhs
  have patternTranslation := congrArg Prod.fst translation
  have rhsTranslation := congrArg Prod.snd translation
  change encodeModelAtom fresh.1 = _ at patternTranslation
  change encodeModelAtom fresh.2 = _ at rhsTranslation
  have member : item ∈ Metta.Minimal.queryOpItemsOfRule previous (encodeModelAtom query)
      incoming counter (encodeModelAtom lhs, encodeModelAtom rhs) := by
    apply (mem_queryOpItemsOfRule_iff _ _ _ _ _ _).mpr
    refine ⟨nativeMatched, ?_, merged, mergeMember, loopFree, ?_⟩
    · simpa only [← patternTranslation] using matchMember
    · change Metta.Minimal.evalResult previous (encodeModelAtom actualEmitted) merged = _
      rw [emittedTranslation, rhsTranslation]
  refine ⟨permutation, actualEmitted, targetMatched, targetOutput, nativeMatched, merged, item,
    fixed, matchMember, mergeMember, loopFree, member, rfl,
    ⟨target.stored, target.selected,
      ⟨target.result.1, ?_⟩⟩,
    projected, (fun valuation => (projectedTheory valuation).trans (theory valuation)), rfl,
    fun valuation satisfied => observation valuation ((projectedTheory valuation).mp satisfied)⟩
  intro valuation satisfied
  exact (observation valuation satisfied).trans (target.result.2 valuation satisfied)

/-- Arbitrary legal variants realize the actual query continuation, retaining
the physical occurrence, native bindings and complete reindexed theory. -/
theorem queryOpItemsOfRule_occurrence_arbitrary_alpha_complete
    {space : Space} {previous : Metta.Minimal.Stack}
    {query lhs rhs sourcePattern sourceRhs emitted : Atom}
    {incoming : Metta.Bindings} {matched output : Bindings} {counter position : Nat}
    (image : LeaBindingsHEImage incoming) (runtime : LeaRuntimeBindingInvariant incoming)
    (source : EquationQueryOccurrenceRel space (liveScope previous) query
      (QueryBindingProjection.project incoming) position lhs rhs sourcePattern sourceRhs
      matched emitted output) :
    ∃ permutation : Equiv.Perm String, ∃ actualEmitted targetMatched targetOutput nativeMatched merged item,
      (∀ name, QueryVisibleName (liveScope previous) query
        (QueryBindingProjection.project incoming) name → permutation name = name) ∧
      nativeMatched ∈ Metta.matchAtoms
        (encodeModelAtom (freshRule previous query incoming counter lhs rhs).1)
        (encodeModelAtom query) ∧
      merged ∈ Metta.Bindings.merge incoming nativeMatched ∧
      merged.hasLoop = false ∧
      item ∈ Metta.Minimal.queryOpItemsOfRule previous (encodeModelAtom query) incoming counter
        (encodeModelAtom lhs, encodeModelAtom rhs) ∧
      item = Metta.Minimal.evalResult previous (encodeModelAtom actualEmitted) merged ∧
      EquationQueryOccurrenceRel space (liveScope previous) query
        (QueryBindingProjection.project incoming) position lhs rhs
        (freshRule previous query incoming counter lhs rhs).1
        (freshRule previous query incoming counter lhs rhs).2
        targetMatched actualEmitted targetOutput ∧
      ScopedEquationQuery.BindingInvariant (QueryBindingProjection.project merged) merged ∧
      (∀ valuation,
        HEBindingSatisfied valuation (QueryBindingProjection.project merged) ↔
          HEBindingSatisfied (valuation ∘ permutation) output) ∧
      ∀ valuation, HEBindingSatisfied valuation (QueryBindingProjection.project merged) →
        HEAtomEquationSatisfied valuation actualEmitted
          (Spec.Type.RuntimeRefinement.renameTypeVars permutation emitted) := by
  obtain ⟨permutation, actualEmitted, targetMatched, targetOutput, nativeMatched, merged, item,
    fixed, matchMember, mergeMember, loopFree, member, itemEq, occurrence, paired, theory, _, observed⟩ :=
    queryOpItemsOfRule_occurrence_arbitrary_alpha_witness (counter := counter) image runtime source
  exact ⟨permutation, actualEmitted, targetMatched, targetOutput, nativeMatched, merged, item,
    fixed, matchMember, mergeMember, loopFree, member, itemEq, occurrence, paired, theory, observed⟩

/-- The actual continuation dispatches the materialized source observation.
This strengthens model equality only at the reachable native instantiation
boundary, using the existing canonical-model and idempotence theorems. It
does not identify raw source syntax with already instantiated syntax. -/
theorem queryOpItemsOfRule_occurrence_materialized_complete
    {space : Space} {previous : Metta.Minimal.Stack}
    {query lhs rhs sourcePattern sourceRhs emitted : Atom}
    {incoming : Metta.Bindings} {matched output : Bindings} {counter position : Nat}
    (image : LeaBindingsHEImage incoming) (runtime : LeaRuntimeBindingInvariant incoming)
    (source : EquationQueryOccurrenceRel space (liveScope previous) query
      (QueryBindingProjection.project incoming) position lhs rhs sourcePattern sourceRhs
      matched emitted output) :
    ∃ permutation : Equiv.Perm String, ∃ actualEmitted merged item,
      (∀ name, QueryVisibleName (liveScope previous) query
        (QueryBindingProjection.project incoming) name → permutation name = name) ∧
      item ∈ Metta.Minimal.queryOpItemsOfRule previous (encodeModelAtom query) incoming counter
        (encodeModelAtom lhs, encodeModelAtom rhs) ∧
      item = Metta.Minimal.evalResult previous (encodeModelAtom actualEmitted) merged ∧
      item = Metta.Minimal.evalResult previous
        (Metta.instantiate merged (encodeModelAtom
          (Spec.Type.RuntimeRefinement.renameTypeVars permutation emitted))) merged ∧
      ScopedEquationQuery.BindingInvariant (QueryBindingProjection.project merged) merged ∧
      (∀ valuation, HEBindingSatisfied valuation (QueryBindingProjection.project merged) ↔
        HEBindingSatisfied (valuation ∘ permutation) output) ∧
      ∀ environment state,
        Metta.Minimal.evalOp environment state previous (encodeModelAtom actualEmitted) merged =
          Metta.Minimal.evalOp environment state previous
            (encodeModelAtom (Spec.Type.RuntimeRefinement.renameTypeVars permutation emitted)) merged := by
  obtain ⟨permutation, actualEmitted, _, _, nativeMatched, merged, item,
    fixed, matchMember, mergeMember, _, member, itemEq, _, paired, theory, emittedEq, observed⟩ :=
    queryOpItemsOfRule_occurrence_arbitrary_alpha_witness (counter := counter) image runtime source
  have matchedImage : LeaBindingsHEImage nativeMatched :=
    leaMatchAtoms_result_heImage
      (leaAtomHEImage_encodeModelAtom (freshRule previous query incoming counter lhs rhs).1)
      (leaAtomHEImage_encodeModelAtom query) matchMember
  have mergedImage := leaMerge_result_image image matchedImage mergeMember
  have emittedImage := instantiate_heImage mergedImage _
    (leaAtomHEImage_encodeModelAtom (freshRule previous query incoming counter lhs rhs).2)
  have sameMaterialized := paired.semantic.materializes_observation observed
  have fixedEmission : Metta.instantiate merged (encodeModelAtom actualEmitted) =
      encodeModelAtom actualEmitted := by
    rw [emittedEq, encodeModelAtom_decodeModelAtom_of_heImage emittedImage]
    have inert := instantiate_semantically_inert paired.semantic.runtime.canonical.1
      (encodeModelAtom (freshRule previous query incoming counter lhs rhs).2)
    simpa only [applyClassSolution_lea_eq_instantiate] using inert
  refine ⟨permutation, actualEmitted, merged, item, fixed, member, itemEq, ?_, paired, theory, ?_⟩
  · rw [← sameMaterialized, fixedEmission]
    exact itemEq
  · intro environment state
    exact paired.semantic.evalOp_observation environment state previous observed

/-- The same actual occurrence has an independently normal finite binding
presentation. Its materialized source emission and actual entry value agree
up to residual-variable renaming. This compares shapes after materialization;
it does not transfer raw dispatch from an unresolved source emission. -/
theorem queryOpItemsOfRule_occurrence_normal_presentation_complete
    {space : Space} {previous : Metta.Minimal.Stack}
    {query lhs rhs sourcePattern sourceRhs emitted : Atom}
    {incoming : Metta.Bindings} {matched output : Bindings} {counter position : Nat}
    (image : LeaBindingsHEImage incoming) (runtime : LeaRuntimeBindingInvariant incoming)
    (source : EquationQueryOccurrenceRel space (liveScope previous) query
      (QueryBindingProjection.project incoming) position lhs rhs sourcePattern sourceRhs
      matched emitted output) :
    ∃ permutation : Equiv.Perm String,
    ∃ presentation : Spec.Type.Presentation.TypeSubst, ∃ value merged item,
      (∀ name, QueryVisibleName (liveScope previous) query
        (QueryBindingProjection.project incoming) name → permutation name = name) ∧
      item ∈ Metta.Minimal.queryOpItemsOfRule previous (encodeModelAtom query) incoming counter
        (encodeModelAtom lhs, encodeModelAtom rhs) ∧
      item = Metta.Minimal.evalResult previous (encodeModelAtom value) merged ∧
      ScopedEquationQuery.BindingInvariant (QueryBindingProjection.project merged) merged ∧
      presentation.Normal ∧
      (∀ valuation, Spec.Type.Presentation.Theory.TypeSubstSatisfied valuation presentation ↔
        Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation (QueryBindingProjection.project merged)) ∧
      (∀ valuation, HEBindingSatisfied valuation (QueryBindingProjection.project merged) ↔
        HEBindingSatisfied (valuation ∘ permutation) output) ∧
      Spec.Type.Presentation.Alpha.ObservedTypeAlphaRel
        (presentation.apply (Spec.Type.RuntimeRefinement.renameTypeVars permutation emitted)) value ∧
      (Spec.Eval.Minimal.IsFunction
        (presentation.apply (Spec.Type.RuntimeRefinement.renameTypeVars permutation emitted)) ↔
          Spec.Eval.Minimal.IsFunction value) ∧
      ((∃ tail, presentation.apply (Spec.Type.RuntimeRefinement.renameTypeVars permutation emitted) =
          .expression (.symbol "function" :: tail)) ↔
        ∃ tail, value = .expression (.symbol "function" :: tail)) ∧
      Spec.Eval.Minimal.embeddedInstruction
          (presentation.apply (Spec.Type.RuntimeRefinement.renameTypeVars permutation emitted)) =
        Spec.Eval.Minimal.embeddedInstruction value ∧
      (∀ body, presentation.apply (Spec.Type.RuntimeRefinement.renameTypeVars permutation emitted) =
          .expression [.symbol "function", body] →
        ∃ actualBody, value = .expression [.symbol "function", actualBody] ∧
          Spec.Type.Presentation.Alpha.ObservedTypeAlphaRel body actualBody) ∧
      ((∀ tail, presentation.apply (Spec.Type.RuntimeRefinement.renameTypeVars permutation emitted) ≠
          .expression (.symbol "function" :: tail)) →
        (∀ dispatch typing caller,
          Spec.Eval.Minimal.CoreInvocationResultRel space dispatch (liveScope previous)
            (presentation.apply (Spec.Type.RuntimeRefinement.renameTypeVars permutation emitted))
            (QueryBindingProjection.project merged)
            (presentation.apply (Spec.Type.RuntimeRefinement.renameTypeVars permutation emitted),
              QueryBindingProjection.project merged) (typing := typing) (caller := caller)) ∧
        item = Metta.Minimal.finItem previous (encodeModelAtom value) merged) ∧
      Spec.Type.Presentation.BindingTheory.EquationListPresentationRel
        (Spec.Type.Presentation.BindingTheory.bindingAtomEquations (QueryBindingProjection.project merged))
        [] presentation ∧
      Spec.Type.Presentation.BindingTheory.BindingMaterializationRel
        (QueryBindingProjection.project merged)
        (Spec.Type.RuntimeRefinement.renameTypeVars permutation emitted)
        (presentation.apply (Spec.Type.RuntimeRefinement.renameTypeVars permutation emitted)) := by
  obtain ⟨permutation, actualEmitted, merged, item,
    fixed, member, _, materializedItem, paired, theory, _⟩ :=
    queryOpItemsOfRule_occurrence_materialized_complete (counter := counter) image runtime source
  obtain ⟨presentation, fold⟩ :=
    Spec.Type.Presentation.BindingTheory.exists_binding_presentation
      (QueryBindingProjection.binding_theory_satisfiable paired.semantic)
  have normal := fold.bindingTheory.1
  have exactTheory := fold.bindingTheory.2
  have alpha := QueryBindingProjection.normal_materialization_alpha paired.semantic normal exactTheory
  let renamed := Spec.Type.RuntimeRefinement.renameTypeVars permutation emitted
  let materialized := Metta.instantiate merged (encodeModelAtom renamed)
  let value := decodeModelAtom materialized
  have valueImage : LeaAtomHEImage materialized :=
    instantiate_heImage paired.image _ (leaAtomHEImage_encodeModelAtom renamed)
  have entry : item = Metta.Minimal.evalResult previous (encodeModelAtom value) merged := by
    change item = Metta.Minimal.evalResult previous
      (encodeModelAtom (decodeModelAtom materialized)) merged
    rw [encodeModelAtom_decodeModelAtom_of_heImage valueImage]
    exact materializedItem
  have observed := alpha renamed
  have functionHead := Spec.Eval.Minimal.functionHead_of_observedTypeAlpha_iff observed
  refine ⟨permutation, presentation, value, merged, item, fixed, member, entry,
    paired, normal, exactTheory, theory, observed,
    Spec.Eval.Minimal.isFunction_of_observedTypeAlpha_iff observed,
    functionHead, Spec.Eval.Minimal.embeddedInstruction_of_observedTypeAlpha observed,
    fun _ body => Spec.Eval.Minimal.functionBody_of_observedTypeAlpha observed body,
    ?_, fold, ⟨presentation, fold, rfl⟩⟩
  intro raw
  refine ⟨?_, ?_⟩
  · intro dispatch typing caller
    exact .raw space _ _ (fun ⟨body, function⟩ => raw [body] function)
  have actualRaw : ∀ tail, encodeModelAtom value ≠ .expr (.sym "function" :: tail) := by
    intro tail function
    have decoded := congrArg decodeModelAtom function
    have valueHead : ∃ values, value = .expression (.symbol "function" :: values) :=
      ⟨decodeModelAtoms tail, by simpa only [decodeModelAtom_encodeModelAtom,
        decodeModelAtom, decodeModelAtoms] using decoded⟩
    obtain ⟨sourceTail, sourceHead⟩ := functionHead.mpr valueHead
    exact raw sourceTail sourceHead
  exact entry.trans (LeaTTaMinimalControlExecution.evalResult_raw_of_not_function_head
    previous (encodeModelAtom value) merged actualRaw)

/-! ## Source occurrences through the complete retained query scan -/

open Metta.Minimal
open LeaTTaMinimalControlExecution LeaTTaMinimalControlExecution.Retained
open Spec.Eval.Minimal Spec.Type.Presentation Spec.Type.RuntimeRefinement
open Spec.Type.Presentation.BindingTheory
open Mettapedia.GSLT.Distinction.ProductiveBlocks

structure RuleOccurrence where
  position : Nat
  lhs : Atom
  rhs : Atom
  deriving Repr, DecidableEq

def RuleOccurrence.native (rule : RuleOccurrence) : Metta.Atom × Metta.Atom :=
  (encodeModelAtom rule.lhs, encodeModelAtom rule.rhs)

def storedRules (offset : Nat) : List Atom → List RuleOccurrence
  | [] => []
  | atom :: atoms =>
    match atom with
    | .expression [.symbol "=", lhs, rhs] =>
      ⟨offset, lhs, rhs⟩ :: storedRules (offset + 1) atoms
    | _ => storedRules (offset + 1) atoms

theorem storedRules_native (offset : Nat) (atoms : List Atom) :
    (storedRules offset atoms).map RuleOccurrence.native =
      extractRules (encodeModelAtoms atoms) := by
  induction atoms generalizing offset with
  | nil => rfl
  | cons atom atoms ih =>
    cases atom with
    | symbol name => simpa [storedRules, extractRules, encodeModelAtoms, encodeModelAtom] using ih (offset+1)
    | var name => simpa [storedRules, extractRules, encodeModelAtoms, encodeModelAtom] using ih (offset+1)
    | grounded value => simpa [storedRules, extractRules, encodeModelAtoms, encodeModelAtom] using ih (offset+1)
    | expression entries =>
      cases entries with
      | nil => simpa [storedRules, extractRules, encodeModelAtoms, encodeModelAtom] using ih (offset+1)
      | cons head tail =>
        cases head <;> cases tail <;> simp_all [storedRules, extractRules, encodeModelAtoms, encodeModelAtom]
        all_goals rename_i a b c
        all_goals cases c <;> simp_all
        all_goals rename_i rest
        all_goals cases rest <;> simp_all
        all_goals split <;> simp_all [RuleOccurrence.native]

theorem storedRules_stored {offset : Nat} {atoms : List Atom} {rule : RuleOccurrence}
    (member : rule ∈ storedRules offset atoms) :
    offset ≤ rule.position ∧
      atoms[rule.position - offset]? = some (.expression [.symbol "=", rule.lhs, rule.rhs]) := by
  induction atoms generalizing offset with
  | nil => simp [storedRules] at member
  | cons atom atoms ih =>
    simp only [storedRules] at member
    split at member
    · rename_i lhs rhs
      rcases List.mem_cons.mp member with same | later
      · subst rule
        simp
      · obtain ⟨bound, stored⟩ := ih later
        have index : rule.position - offset = (rule.position - (offset + 1)) + 1 := by omega
        exact ⟨by omega, by simpa [index] using stored⟩
    · obtain ⟨bound, stored⟩ := ih member
      have index : rule.position - offset = (rule.position - (offset + 1)) + 1 := by omega
      exact ⟨by omega, by simpa [index] using stored⟩

/-- Runtime-added rules use the actual head filter, retaining every physical row. -/
def dynamicCandidate (query : Metta.Atom) (rule : Metta.Atom × Metta.Atom) : Bool :=
  match headKey rule.1, headKey query with
  | some left, some right => left == right
  | none, _ => true
  | _, _ => false

def candidateRules (atoms added imported : List Atom) (query : Atom) : List RuleOccurrence :=
  let base := storedRules 0 atoms
  (match headKey (encodeModelAtom query) with
    | some key => base.filter (fun rule => headKey rule.native.1 == some key)
    | none => []) ++
  base.filter (fun rule => (headKey rule.native.1).isNone) ++
  (storedRules atoms.length (added ++ imported)).filter
    (fun rule => dynamicCandidate (encodeModelAtom query) rule.native)

theorem dynamicCandidates_extract (atoms : List Metta.Atom) (query : Metta.Atom) :
    (extractRules atoms).filter (dynamicCandidate query) =
      atoms.filterMap (fun atom => match atom with
        | .expr [.sym "=", lhs, rhs] =>
          match headKey lhs, headKey query with
          | some left, some right => if left == right then some (lhs, rhs) else none
          | none, _ => some (lhs, rhs)
          | _, _ => none
        | _ => none) := by
  simp only [extractRules, List.filter_filterMap]
  apply List.filterMap_congr
  intro atom _
  split
  · rename_i lhs rhs _
    simp only [Option.filter, dynamicCandidate]
    have choose (left right : Option String) :
        (if (match left, right with
          | some a, some b => a == b
          | none, _ => true
          | _, _ => false) then some (lhs, rhs) else none) =
        (match left, right with
          | some a, some b => if a == b then some (lhs, rhs) else none
          | none, _ => some (lhs, rhs)
          | _, _ => none) := by
      cases left <;> cases right <;> rfl
    exact choose (headKey lhs) (headKey query)
  · split <;> simp_all

theorem candidateRules_native (atoms added imported : List Atom) (query : Atom)
    (grounded : Metta.GroundingTable) (world : World)
    (extra : world.selfExtra = encodeModelAtoms added)
    (imports : world.selfImports = encodeModelAtoms imported) :
    (candidateRules atoms added imported query).map RuleOccurrence.native =
      candidatesW (MinEnv.ofAtomsGT (encodeModelAtoms atoms) grounded) world (encodeModelAtom query) := by
  unfold candidateRules candidatesW MinEnv.candidates
  rw [extra, imports]
  simp only [List.map_append]
  have filtered (offset : Nat) (source : List Atom) (predicate : (Metta.Atom × Metta.Atom) → Bool) :
      ((storedRules offset source).filter (fun rule => predicate rule.native)).map RuleOccurrence.native =
        (extractRules (encodeModelAtoms source)).filter predicate := by
    change ((storedRules offset source).filter (predicate ∘ RuleOccurrence.native)).map RuleOccurrence.native = _
    rw [← List.filter_map, storedRules_native]
  rw [filtered 0 atoms (fun pair => (headKey pair.1).isNone),
    filtered atoms.length (added ++ imported) (dynamicCandidate (encodeModelAtom query))]
  rw [dynamicCandidates_extract]
  have appendAtoms : encodeModelAtoms (added ++ imported) = encodeModelAtoms added ++ encodeModelAtoms imported := by
    simp only [encodeModelAtoms_eq_map, List.map_append]
  rw [appendAtoms]
  cases key : headKey (encodeModelAtom query) with
  | none => simp only [List.map_nil, Metta.ofAtomsGT_varRules]; rfl
  | some value =>
    simp only [Metta.ruleIndex_getD, Metta.ofAtomsGT_varRules]
    rw [filtered 0 atoms (fun pair => headKey pair.1 == some value)]
    rfl

theorem candidateRules_stored {atoms added imported : List Atom} {query : Atom}
    {rule : RuleOccurrence} (member : rule ∈ candidateRules atoms added imported query) :
    (atoms ++ added ++ imported)[rule.position]? =
      some (.expression [.symbol "=", rule.lhs, rule.rhs]) := by
  have source : rule ∈ storedRules 0 atoms ∨ rule ∈ storedRules atoms.length (added ++ imported) := by
    simp only [candidateRules, List.mem_append, List.mem_filter] at member
    rcases member with (selected | unkeyed) | dynamic
    · cases key : headKey (encodeModelAtom query) <;> simp only [key] at selected
      · simp at selected
      · exact Or.inl (List.mem_filter.mp selected).1
    · exact Or.inl unkeyed.1
    · exact Or.inr dynamic.1
  rcases source with first | second
  · obtain ⟨_, stored⟩ := storedRules_stored first
    simp only [Nat.sub_zero] at stored
    rw [List.append_assoc, List.getElem?_append_left (List.getElem?_eq_some_iff.mp stored).1]
    exact stored
  · obtain ⟨bound, stored⟩ := storedRules_stored second
    rw [List.append_assoc, List.getElem?_append_right bound]
    exact stored

/-- The source row, actual freshening counter and branch ordinal accompany
one work item. Neither equal values nor equal declaration bodies identify
these physical occurrences. -/
structure QueryOccurrence where
  rule : RuleOccurrence
  counter : Nat
  branch : Nat
  item : Item

def ruleWork (previous : Stack) (query : Atom) (incoming : Metta.Bindings)
    (counter : Nat) (rule : RuleOccurrence) : List QueryOccurrence :=
  (Metta.Minimal.queryOpItemsOfRule previous (encodeModelAtom query) incoming counter rule.native).zipIdx.map
    (fun pair => ⟨rule, counter, pair.2, pair.1⟩)

def queryWork (previous : Stack) (query : Atom) (incoming : Metta.Bindings) :
    Nat → List RuleOccurrence → List QueryOccurrence
  | _, [] => []
  | counter, rule :: rules =>
    ruleWork previous query incoming counter rule ++ queryWork previous query incoming (counter + 1) rules

theorem ruleWork_items (previous : Stack) (query : Atom) (incoming : Metta.Bindings)
    (counter : Nat) (rule : RuleOccurrence) :
    (ruleWork previous query incoming counter rule).map QueryOccurrence.item =
      Metta.Minimal.queryOpItemsOfRule previous (encodeModelAtom query) incoming counter rule.native := by
  simp only [ruleWork, List.map_map]
  exact List.zipIdx_map_fst 0 _

/-- Erasing only occurrence metadata gives the complete actual fold, with
its counter advanced even across candidates that produced no work. -/
theorem queryWork_fold (previous : Stack) (query : Atom) (incoming : Metta.Bindings)
    (rules : List RuleOccurrence) (accumulated : List Item) (state : St) :
    (rules.map RuleOccurrence.native).foldl
      (Metta.Minimal.queryOpFoldStep previous (encodeModelAtom query) incoming) (accumulated, state) =
      (accumulated ++ (queryWork previous query incoming state.counter rules).map QueryOccurrence.item,
       {state with counter := state.counter + rules.length}) := by
  induction rules generalizing accumulated state with
  | nil => simp [queryWork]
  | cons rule rules ih =>
    simp only [List.map_cons, List.foldl_cons, Metta.Minimal.queryOpFoldStep]
    rw [freshenRuleAvoiding_counter, ih]
    simp only [queryWork, List.map_append, ruleWork_items, List.length_cons]
    simp only [List.append_assoc, Prod.mk.injEq, true_and, St.mk.injEq, and_true]
    omega

theorem queryWork_member {previous : Stack} {query : Atom} {incoming : Metta.Bindings}
    {counter : Nat} {rules : List RuleOccurrence} {occurrence : QueryOccurrence}
    (member : occurrence ∈ queryWork previous query incoming counter rules) :
    ∃ before after, rules = before ++ occurrence.rule :: after ∧
      occurrence.counter = counter + before.length ∧
      (Metta.Minimal.queryOpItemsOfRule previous (encodeModelAtom query)
        incoming occurrence.counter occurrence.rule.native)[occurrence.branch]? = some occurrence.item := by
  induction rules generalizing counter with
  | nil => simp [queryWork] at member
  | cons rule rules ih =>
    rcases List.mem_append.mp member with first | later
    · obtain ⟨⟨item, branch⟩, native, rfl⟩ := List.mem_map.mp first
      exact ⟨[], rules, rfl, by simp, List.mk_mem_zipIdx_iff_getElem?.mp native⟩
    · obtain ⟨before, after, list, count, item⟩ := ih later
      exact ⟨rule :: before, after, by simp [list], by simp only [List.length_cons]; omega, item⟩

/-- An actual local branch remains at its own occurrence in the whole scan. -/
theorem queryWork_of_branch (previous : Stack) (query : Atom) (incoming : Metta.Bindings)
    (counter : Nat) (before after : List RuleOccurrence) (rule : RuleOccurrence)
    (branch : Nat) (item : Item)
    (selected : (Metta.Minimal.queryOpItemsOfRule previous (encodeModelAtom query) incoming
      (counter + before.length) rule.native)[branch]? = some item) :
    (⟨rule, counter + before.length, branch, item⟩ : QueryOccurrence) ∈
      queryWork previous query incoming counter (before ++ rule :: after) := by
  induction before generalizing counter with
  | nil =>
    apply List.mem_append_left
    apply List.mem_map.mpr
    exact ⟨(item, branch), List.mk_mem_zipIdx_iff_getElem?.mpr selected, rfl⟩
  | cons head before ih =>
    apply List.mem_append_right
    have index : counter + (head :: before).length = (counter + 1) + before.length := by
      simp only [List.length_cons]
      omega
    rw [index] at selected ⊢
    exact ih (counter + 1) selected

/-- Any admitted source derivation for a candidate occurrence has a real
branch in the full scan, with only its private fresh names transported. This
uses the independent match/merge completeness theorem, not result equality. -/
theorem queryWork_occurrence_complete
    {atoms added imported : List Atom} {previous : Stack} {query : Atom}
    {incoming : Metta.Bindings} {counter : Nat} {rule : RuleOccurrence}
    {sourcePattern sourceRhs emitted : Atom} {matched output : Bindings}
    (image : LeaBindingsHEImage incoming) (runtime : LeaRuntimeBindingInvariant incoming)
    (candidate : rule ∈ candidateRules atoms added imported query)
    (source : EquationQueryOccurrenceRel (Space.ofList (atoms ++ added ++ imported))
      (liveScope previous) query (QueryBindingProjection.project incoming) rule.position
      rule.lhs rule.rhs sourcePattern sourceRhs matched emitted output) :
    ∃ occurrence ∈ queryWork previous query incoming counter (candidateRules atoms added imported query),
      occurrence.rule = rule ∧ ∃ permutation : Equiv.Perm String, ∃ actualEmitted merged,
      (∀ name, QueryVisibleName (liveScope previous) query
        (QueryBindingProjection.project incoming) name → permutation name = name) ∧
      occurrence.item = evalResult previous (encodeModelAtom actualEmitted) merged ∧
      ScopedEquationQuery.BindingInvariant (QueryBindingProjection.project merged) merged ∧
      (∀ valuation, HEBindingSatisfied valuation (QueryBindingProjection.project merged) ↔
        HEBindingSatisfied (valuation ∘ permutation) output) ∧
      ∀ valuation, HEBindingSatisfied valuation (QueryBindingProjection.project merged) →
        HEAtomEquationSatisfied valuation actualEmitted
          (Spec.Type.RuntimeRefinement.renameTypeVars permutation emitted) := by
  obtain ⟨before, after, listed⟩ := List.mem_iff_append.mp candidate
  obtain ⟨permutation, actualEmitted, targetMatched, targetOutput, nativeMatched, merged, item,
    fixed, _, _, _, member, itemEq, _, paired, theory, observed⟩ :=
    queryOpItemsOfRule_occurrence_arbitrary_alpha_complete
      (counter := counter + before.length) image runtime source
  obtain ⟨branch, selected⟩ := List.mem_iff_getElem?.mp member
  refine ⟨⟨rule, counter + before.length, branch, item⟩, ?_, rfl,
    permutation, actualEmitted, merged, fixed, itemEq, paired, theory, observed⟩
  rw [listed]
  exact queryWork_of_branch previous query incoming counter before after rule branch item selected

/-- Every entry in the complete scan has an independent judgment tied to its
original physical source position and exact native branch item. -/
theorem queryWork_sound {atoms added imported : List Atom} {previous : Stack}
    {query : Atom} {incoming : Metta.Bindings} {counter : Nat} {occurrence : QueryOccurrence}
    (image : LeaBindingsHEImage incoming) (runtime : LeaRuntimeBindingInvariant incoming)
    (member : occurrence ∈ queryWork previous query incoming counter
      (candidateRules atoms added imported query)) :
    ∃ emitted output merged freshPattern freshRhs matched,
      EquationQueryOccurrenceRel (Space.ofList (atoms ++ added ++ imported))
        (liveScope previous) query (QueryBindingProjection.project incoming)
        occurrence.rule.position occurrence.rule.lhs occurrence.rule.rhs freshPattern freshRhs
        matched emitted output ∧
      occurrence.item = evalResult previous (encodeModelAtom emitted) merged ∧
      ScopedEquationQuery.BindingInvariant (QueryBindingProjection.project merged) merged ∧
      ScopedEquationQuery.BindingInvariant output merged ∧
      emitted = decodeModelAtom (Metta.instantiate merged (encodeModelAtom freshRhs)) := by
  obtain ⟨before, after, list, _, native⟩ := queryWork_member member
  have ruleMember : occurrence.rule ∈ candidateRules atoms added imported query := by simp [list]
  exact queryOpItemsOfRule_occurrence_sound (candidateRules_stored ruleMember) image runtime
    (List.mem_of_getElem? native)

/-- The full native query is this occurrence list unless no item survived;
that case retains the native NotReducible marker and the advanced counter. -/
theorem queryWork_queryOp (atoms added imported : List Atom) (previous : Stack)
    (query : Atom) (incoming : Metta.Bindings) (grounded : Metta.GroundingTable) (state : St)
    (extra : state.world.selfExtra = encodeModelAtoms added)
    (imports : state.world.selfImports = encodeModelAtoms imported)
    (notVariable : isVariableHeaded (encodeModelAtom query) = false) :
    let rules := candidateRules atoms added imported query
    let work := queryWork previous query incoming state.counter rules
    queryOp (MinEnv.ofAtomsGT (encodeModelAtoms atoms) grounded) state previous (encodeModelAtom query) incoming =
      ((if work.isEmpty then [finItem previous notReducibleA incoming] else work.map QueryOccurrence.item),
        {state with counter := state.counter + rules.length}) := by
  intro rules work
  unfold queryOp
  rw [notVariable]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [← candidateRules_native atoms added imported query grounded state.world extra imports]
  rw [queryWork_fold]
  simp only [List.nil_append, List.isEmpty_map]
  change (if work.isEmpty then (_, _) else (_, _)) = _
  split <;> simp_all [rules, work]

/-- Local dispatch conditions select the existing query handler after actual
operand materialization. The grounding table is consulted on the same world-
resolved operands as the native interpreter. -/
theorem evalOp_query (environment : MinEnv) (state : St) (previous : Stack)
    (argument query : Metta.Atom) (incoming : Metta.Bindings)
    (materialized : Metta.instantiate incoming argument = query)
    (ordinary : isEmbeddedOp query = false)
    (host : ∀ name args, query = .expr (.sym name :: args) →
      Metta.callGrounded environment.gt name
        (args.map (fun atom => resolveStates state.world (subTokens state.world atom))) =
          .noReduce) :
    evalOp environment state previous argument incoming = queryOp environment state previous query incoming := by
  simp only [evalOp, materialized]
  split
  · rename_i _ name args
    rw [host name args rfl]
    simp [ordinary]
  · simp [ordinary]

/-- A single existing eval instruction hands every query result to the
retained queue. A stored caller, prior publications and the whole world are
kept; only the native gensym counter advances during the scan. -/
theorem queryWork_retained
    (atoms added imported : List Atom) (previous : Stack) (scope : List String)
    (argument query : Atom) (incoming : Metta.Bindings)
    (grounded : Metta.GroundingTable) (state : St)
    (extra : state.world.selfExtra = encodeModelAtoms added)
    (imports : state.world.selfImports = encodeModelAtoms imported)
    (materialized : Metta.instantiate incoming (encodeModelAtom argument) = encodeModelAtom query)
    (ordinary : isEmbeddedOp (encodeModelAtom query) = false)
    (notVariable : isVariableHeaded (encodeModelAtom query) = false)
    (host : ∀ name args, encodeModelAtom query = .expr (.sym name :: args) →
      Metta.callGrounded grounded name
        (args.map (fun atom => resolveStates state.world (subTokens state.world atom))) = .noReduce)
    (fuel : Nat) (queued : List Item) (completed : List (Metta.Atom × Metta.Bindings))
    (receipts : List Receipt) :
    let environment := MinEnv.ofAtomsGT (encodeModelAtoms atoms) grounded
    let rules := candidateRules atoms added imported query
    let work := queryWork previous query incoming state.counter rules
    let spawned := if work.isEmpty then [finItem previous notReducibleA incoming] else work.map QueryOccurrence.item
    let nextState := {state with counter := state.counter + rules.length}
    let instruction : Item := ⟨{atom := .expr [.sym "eval", encodeModelAtom argument], vars := scope} :: previous, incoming⟩
    let before : Configuration := ⟨fuel + 1, state, instruction :: queued, completed, receipts⟩
    let after : Configuration :=
      ⟨fuel, nextState, spawned.filter (fun item => !isFinal item) ++ queued,
        completed ++ finals spawned, receipts ++ [⟨state, instruction, spawned, nextState⟩]⟩
    (machine environment).run 1 before =
      ((finals spawned).filter (fun pair => pair.1 != emptyA), .exhausted after) ∧
      Receipt.Valid environment ⟨state, instruction, spawned, nextState⟩ := by
  intro environment rules work spawned nextState instruction before after
  have step (depth : Nat) : interpretStack1 environment depth state instruction = (spawned, nextState) := by
    rw [step_eval, evalOp_query environment state previous (encodeModelAtom argument)
      (encodeModelAtom query) incoming materialized ordinary host]
    exact queryWork_queryOp atoms added imported previous query incoming grounded state extra imports notVariable
  constructor
  · rw [run_succ_ready environment before instruction queued rfl fuel rfl (by rfl) 0]
    simp only [Machine.run, emitted, advance, before, step, List.append_nil]
    rfl
  · exact ⟨by rfl, step⟩

namespace RetainedQueryControls

def query : Atom := .expression [.symbol "ask", .symbol "A"]
def body : Atom := .expression [.symbol "unify", .var "local", .var "argument",
  .expression [.symbol "cons-atom", .symbol "return",
    .expression [.expression [.symbol "pair", .var "local", .var "local"]]],
  .expression [.symbol "return", .symbol "refused"]]
def equation : Atom := .expression [.symbol "=",
  .expression [.symbol "ask", .var "argument"], .expression [.symbol "function", body]]
def atoms : List Atom := [.symbol "declaration", equation, equation]
def added : List Atom := [equation]
def imported : List Atom := [equation]
def environment : MinEnv := MinEnv.ofAtomsGT (encodeModelAtoms atoms) Metta.Builtins.table
def state : St := {St.init with world := {St.init.world with
  selfExtra := encodeModelAtoms added, selfImports := encodeModelAtoms imported}}
def incoming : Metta.Bindings := [.val "caller" (.sym "kept")]
def work := queryWork [] query incoming state.counter (candidateRules atoms added imported query)
def loaded : Configuration := ⟨40, state,
  [⟨atomToStack (.expr [.sym "eval", encodeModelAtom query]) [], incoming⟩], [], []⟩

#guard (candidateRules atoms added imported query).map RuleOccurrence.position == [1, 2, 3, 4]
#guard work.map (fun occurrence => (occurrence.rule.position, occurrence.counter, occurrence.branch)) ==
  [(1,0,0), (2,1,0), (3,2,0), (4,3,0)]
#guard work.length == 4
#guard ((machine environment).run 40 loaded).1.map Prod.fst ==
  List.replicate 4 (.expr [.sym "pair", .sym "A", .sym "A"])
#guard (((machine environment).run 40 loaded).1.all
  (fun result => Metta.instantiate result.2 (.var "caller") == .sym "kept"))
#guard ((machine environment).run 4 loaded).1.isEmpty
#guard ((machine environment).run 5 loaded).1.map Prod.fst == [.expr [.sym "pair", .sym "A", .sym "A"]]
#guard ((machine environment).run 6 loaded).1.map Prod.fst == [.expr [.sym "pair", .sym "A", .sym "A"]]
#guard ((machine environment).continueRun 30 ((machine environment).run 4 loaded)).1 ==
  ((machine environment).run 34 loaded).1
#guard (queryOp environment state [] (.var "unknown") incoming).1.length == 1
#guard (queryOp environment state [] (.var "unknown") incoming).2.counter == state.counter
#guard (queryOp environment state [] (.expr [.sym "missing"]) incoming).1.map (fun item => (finalPair item).1) ==
  [notReducibleA]
#guard (queryOp environment state [] (.expr [.sym "missing"]) incoming).2.counter == 0
#guard (queryOp environment state [] (.expr [.sym "ask", .sym "A", .sym "B"]) incoming).1.map
  (fun item => (finalPair item).1) == [notReducibleA]
#guard (queryOp environment state [] (.expr [.sym "ask", .sym "A", .sym "B"]) incoming).2.counter == 4
#guard match ((machine environment).run 1 loaded).2 with
  | .exhausted after => after.pending.length == 4 && after.completed.isEmpty &&
      after.receipts.length == 1 && after.runtime.counter == 4
  | _ => false
#guard match ((machine environment).run 5 loaded).2 with
  | .exhausted after => after.pending.length == 3 && after.completed.length == 1
  | _ => false

private theorem incoming_image : LeaBindingsHEImage incoming := by
  intro key value member
  have same : key = "caller" ∧ value = .sym "kept" := by simpa [incoming] using member
  obtain ⟨rfl, rfl⟩ := same
  exact leaAtomHEImage_sym "kept"

private theorem incoming_runtime : LeaRuntimeBindingInvariant incoming := by
  apply leaRuntimeBindingInvariant_empty.merge (right := incoming)
  · intro key value member
    have same : key = "caller" ∧ value = .sym "kept" := by simpa [incoming] using member
    obtain ⟨rfl, rfl⟩ := same
    simp [MettaAtomNoFloat]
  · change incoming ∈ Metta.Bindings.merge [] incoming
    change incoming ∈ [incoming]
    exact List.mem_singleton_self _
  · exact Metta.Bindings.hasLoop_singleton_val_of_not_mem _ _ (by simp [Metta.Atom.vars])

/-- The full occurrence theorem applies to every physical result, including
all repeated static, added and imported declarations. -/
theorem every_repeated_declaration_has_source (occurrence : QueryOccurrence)
    (member : occurrence ∈ work) :
    ∃ emitted output merged freshPattern freshRhs matched,
      EquationQueryOccurrenceRel (Space.ofList (atoms ++ added ++ imported)) [] query
        (QueryBindingProjection.project incoming) occurrence.rule.position occurrence.rule.lhs
        occurrence.rule.rhs freshPattern freshRhs matched emitted output ∧
      occurrence.item = evalResult [] (encodeModelAtom emitted) merged ∧
      ScopedEquationQuery.BindingInvariant (QueryBindingProjection.project merged) merged ∧
      ScopedEquationQuery.BindingInvariant output merged ∧
      emitted = decodeModelAtom (Metta.instantiate merged (encodeModelAtom freshRhs)) :=
  queryWork_sound incoming_image incoming_runtime member

end RetainedQueryControls

end Mettapedia.Languages.MeTTa.HE.LeaTTaScopedQuery

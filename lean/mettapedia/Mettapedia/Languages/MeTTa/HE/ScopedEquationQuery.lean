import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory
import Mettapedia.Languages.MeTTa.HE.RecursiveScope
import Mettapedia.Languages.MeTTa.HE.Spec.Match.Completeness

/-!
# Scoped equation-query execution and independent soundness

Rule selection uses the actual LeaTTa freshener, matcher, binding merger and
instantiator. The avoidance set retains both the independent binding
presentation and the native binding record. Hits carry their ordered source
position and native binding state. The soundness theorem constructs an
independent equation-query derivation and the next paired binding invariant.

This is an explicit-scope query profile. It does not silently replace the
older fuelled HE evaluator or assert equality with CeTTa's native evaluator.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.ScopedEquationQuery

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open LeaTTaBridge LeaTTaTypeConformance LeaTTaSpecConformance
open Spec.Match.Merge Spec.Eval.Steps

structure Hit where
  value : Atom
  bindings : Metta.Bindings
  deriving Repr

def avoidNames (live : List Atom) (query : Atom)
    (specIncoming : Bindings) (incoming : Metta.Bindings) : List String :=
  EquationScope.visibleNames live query specIncoming ++ incoming.vars

def freshRule (live : List Atom) (query : Atom) (specIncoming : Bindings)
    (incoming : Metta.Bindings) (counter : Nat) (lhs rhs : Atom) : Atom × Atom :=
  EquationFreshening.freshRule (avoidNames live query specIncoming incoming) counter lhs rhs

/-- Execute one complete stored-rule candidate, retaining native bindings. -/
def ruleResults (live : List Atom) (query : Atom) (specIncoming : Bindings)
    (incoming : Metta.Bindings) (counter : Nat) (lhs rhs : Atom) : List Hit :=
  let fresh := freshRule live query specIncoming incoming counter lhs rhs
  (Metta.matchAtoms (toLeaTTaAtom fresh.1) (toLeaTTaAtom query)).flatMap fun matched =>
    (Metta.Bindings.merge incoming matched).filterMap fun merged =>
      if merged.hasLoop then none
      else some ⟨fromLeaTTaAtom (Metta.instantiate merged (toLeaTTaAtom fresh.2)), merged⟩

/-- Both semantic and exact-image invariants used by the query boundary. -/
structure BindingInvariant (spec : Bindings) (native : Metta.Bindings) : Prop where
  semantic : LeaQueryOpBindingInvariant spec native
  image : LeaBindingsHEImage native

theorem bindingInvariant_empty : BindingInvariant Bindings.empty Metta.Bindings.empty :=
  ⟨leaQueryOpBindingInvariant_empty, leaBindingsHEImage_empty⟩

theorem freshRule_alphaVariant (live : List Atom) (query : Atom) (specIncoming : Bindings)
    (incoming : Metta.Bindings) (counter : Nat) (lhs rhs : Atom) :
    AlphaVariantRel live query specIncoming lhs rhs
      (freshRule live query specIncoming incoming counter lhs rhs).1
      (freshRule live query specIncoming incoming counter lhs rhs).2 :=
  EquationFreshening.freshRule_alphaVariant_of_covers live query lhs rhs specIncoming counter _
    (fun name visible => List.mem_append_left _
      ((EquationScope.mem_visibleNames_iff live query specIncoming name).mpr visible))

theorem freshRule_varsDisjoint (live : List Atom) (query : Atom) (specIncoming : Bindings)
    (incoming : Metta.Bindings) (counter : Nat) (lhs rhs : Atom) :
    VarsDisjoint query (freshRule live query specIncoming incoming counter lhs rhs).1 := by
  intro name queryMember patternMember
  have avoided := EquationFreshening.freshRule_variables_avoid
    (avoidNames live query specIncoming incoming) counter lhs rhs name
    (List.mem_append_left _ patternMember)
  apply avoided
  simp only [avoidNames, EquationScope.visibleNames, List.mem_append]
  exact Or.inl (Or.inl (Or.inl queryMember))

/-- Matching the chosen hygienic rule is complete for the independent match
judgment. This law concerns matching, before ambient merge and filtering. -/
theorem match_nonempty_iff (live : List Atom) (query : Atom) (specIncoming : Bindings)
    (incoming : Metta.Bindings) (counter : Nat) (lhs rhs : Atom) :
    Metta.matchAtoms
        (toLeaTTaAtom (freshRule live query specIncoming incoming counter lhs rhs).1)
        (toLeaTTaAtom query) ≠ [] ↔
      ∃ matched, MatchRel equalityGroundedSemantic query
        (freshRule live query specIncoming incoming counter lhs rhs).1 matched := by
  constructor
  · intro nonempty
    obtain ⟨nativeMatched, member⟩ := List.exists_mem_of_ne_nil _ nonempty
    obtain ⟨matched, derivation, _⟩ := leaMatch_observational_sound member
    exact ⟨matched, derivation⟩
  · rintro ⟨matched, derivation⟩ empty
    obtain ⟨nativeMatched, member, _⟩ := specMatch_observational_complete derivation
      (freshRule_varsDisjoint live query specIncoming incoming counter lhs rhs)
    simp [empty] at member

/-- Empty matching is an independent semantic rejection for the chosen rule. -/
theorem match_empty_iff (live : List Atom) (query : Atom) (specIncoming : Bindings)
    (incoming : Metta.Bindings) (counter : Nat) (lhs rhs : Atom) :
    Metta.matchAtoms
        (toLeaTTaAtom (freshRule live query specIncoming incoming counter lhs rhs).1)
        (toLeaTTaAtom query) = [] ↔
      ∀ matched, ¬MatchRel equalityGroundedSemantic query
        (freshRule live query specIncoming incoming counter lhs rhs).1 matched := by
  simpa only [not_not, not_exists] using
    (not_congr (match_nonempty_iff live query specIncoming incoming counter lhs rhs))

/-- A returned hit exposes the actual match, merge and loop-filter decisions. -/
theorem ruleResults_witness {live : List Atom} {query lhs rhs : Atom}
    {specIncoming : Bindings} {incoming : Metta.Bindings} {counter : Nat} {hit : Hit}
    (member : hit ∈ ruleResults live query specIncoming incoming counter lhs rhs) :
    ∃ matched merged,
      matched ∈ Metta.matchAtoms
        (toLeaTTaAtom (freshRule live query specIncoming incoming counter lhs rhs).1)
        (toLeaTTaAtom query) ∧
      merged ∈ Metta.Bindings.merge incoming matched ∧
      merged.hasLoop = false ∧
      hit = ⟨fromLeaTTaAtom (Metta.instantiate merged
        (toLeaTTaAtom (freshRule live query specIncoming incoming counter lhs rhs).2)), merged⟩ := by
  simp only [ruleResults, List.mem_flatMap, List.mem_filterMap] at member
  obtain ⟨matched, matchMember, merged, mergeMember, emitted⟩ := member
  split at emitted
  · simp at emitted
  · rename_i ordinary
    exact ⟨matched, merged, matchMember, mergeMember,
      by simpa using ordinary, by simpa using emitted.symm⟩

/-- Replay the actual native match, merge and loop-filter decisions without
losing the instantiated RHS or its returned bindings. -/
theorem ruleResults_of_match_merge {live : List Atom} {query lhs rhs : Atom}
    {specIncoming : Bindings} {incoming matched merged : Metta.Bindings} {counter : Nat}
    (matchMember : matched ∈ Metta.matchAtoms
      (toLeaTTaAtom (freshRule live query specIncoming incoming counter lhs rhs).1)
      (toLeaTTaAtom query))
    (mergeMember : merged ∈ Metta.Bindings.merge incoming matched)
    (loopFree : merged.hasLoop = false) :
    (⟨fromLeaTTaAtom (Metta.instantiate merged
      (toLeaTTaAtom (freshRule live query specIncoming incoming counter lhs rhs).2)), merged⟩ : Hit) ∈
      ruleResults live query specIncoming incoming counter lhs rhs := by
  unfold ruleResults
  exact List.mem_flatMap.mpr ⟨matched, matchMember,
    List.mem_filterMap.mpr ⟨merged, mergeMember, by simp [loopFree]⟩⟩

/-- The concrete matcher and merge preserve representable binding payloads,
independently of the stronger paired logical invariant. -/
theorem ruleResults_bindingsImage {live : List Atom} {query lhs rhs : Atom}
    {specIncoming : Bindings} {incoming : Metta.Bindings} {counter : Nat} {hit : Hit}
    (incomingImage : LeaBindingsHEImage incoming)
    (member : hit ∈ ruleResults live query specIncoming incoming counter lhs rhs) :
    LeaBindingsHEImage hit.bindings := by
  obtain ⟨matched, merged, matchedMember, mergedMember, _, rfl⟩ := ruleResults_witness member
  apply leaMerge_result_image incomingImage _ mergedMember
  exact leaMatchAtoms_result_heImage
    (leaAtomHEImage_toLeaTTaAtom (freshRule live query specIncoming incoming counter lhs rhs).1)
    (leaAtomHEImage_toLeaTTaAtom query) matchedMember

/-- The semantic witnesses are constructed from the actual native match and
merge that emitted this hit, retaining the exact freshened pair. -/
theorem ruleResults_sound_witness {live : List Atom} {query lhs rhs : Atom}
    {specIncoming : Bindings} {incoming : Metta.Bindings} {counter : Nat} {hit : Hit}
    (invariant : BindingInvariant specIncoming incoming)
    (member : hit ∈ ruleResults live query specIncoming incoming counter lhs rhs) :
    ∃ nativeMatched specMatched specOutput,
      nativeMatched ∈ Metta.matchAtoms
        (toLeaTTaAtom (freshRule live query specIncoming incoming counter lhs rhs).1)
        (toLeaTTaAtom query) ∧
      hit.bindings ∈ Metta.Bindings.merge incoming nativeMatched ∧
      hit.bindings.hasLoop = false ∧
      hit.value = fromLeaTTaAtom (Metta.instantiate hit.bindings
        (toLeaTTaAtom (freshRule live query specIncoming incoming counter lhs rhs).2)) ∧
      EquationRuleInstanceRel live query specIncoming lhs rhs
        (freshRule live query specIncoming incoming counter lhs rhs).1
        (freshRule live query specIncoming incoming counter lhs rhs).2 specMatched ∧
      EquationQueryResultRel specIncoming specMatched
        (freshRule live query specIncoming incoming counter lhs rhs).2 hit.value specOutput ∧
      BindingInvariant specOutput hit.bindings := by
  obtain ⟨matched, merged, matchMember, mergeMember, loopFree, rfl⟩ := ruleResults_witness member
  let fresh := freshRule live query specIncoming incoming counter lhs rhs
  obtain ⟨specMatched, specOutput, matchDerivation, mergeDerivation, next, observation⟩ :=
    queryOp_hit_observational_sound invariant.semantic matchMember mergeMember loopFree
  have matchedImage : LeaBindingsHEImage matched :=
    leaMatchAtoms_result_heImage (leaAtomHEImage_toLeaTTaAtom fresh.1)
      (leaAtomHEImage_toLeaTTaAtom query) matchMember
  have mergedImage : LeaBindingsHEImage merged :=
    leaMerge_result_image invariant.image matchedImage mergeMember
  have emittedImage : LeaAtomHEImage (Metta.instantiate merged (toLeaTTaAtom fresh.2)) :=
    instantiate_heImage mergedImage _ (leaAtomHEImage_toLeaTTaAtom fresh.2)
  have satisfied : HEBindingSatisfied (leaClassSolution merged) specOutput :=
    (next.solutionTheory (leaClassSolution merged)).mpr next.runtime.canonical.1
  obtain ⟨swapped, reversed, swappedShape, _swappedModel, theory⟩ :=
    Spec.Match.Completeness.exists_swapped_specMerge_of_satisfied mergeDerivation
      invariant.semantic.specAssignmentsNonVariable
      (specMatch_assignmentsNonVariable matchDerivation) ⟨leaClassSolution merged, satisfied⟩
  have swappedSatisfied := (theory (leaClassSolution merged)).mp satisfied
  have nextSwapped : LeaQueryOpBindingInvariant swapped merged :=
    ⟨fun valuation => (theory valuation).symm.trans (next.solutionTheory valuation),
      swappedShape, next.runtime⟩
  refine ⟨matched, specMatched, swapped, matchMember, mergeMember, loopFree, rfl,
    ⟨freshRule_alphaVariant live query specIncoming incoming counter lhs rhs, matchDerivation⟩,
    ⟨reversed.logicalMerge ⟨_,
      specTypeBindingSatisfied_of_heBindingSatisfied swappedSatisfied⟩, ?_⟩,
      ⟨nextSwapped, mergedImage⟩⟩
  intro valuation outputSatisfied
  unfold HEAtomEquationSatisfied
  rw [toLeaTTaAtom_fromLeaTTaAtom_of_heImage emittedImage]
  exact observation valuation ((theory valuation).mpr outputSatisfied)

/-- Every hit from an admitted paired state constructs the independent
query derivation and the paired invariant needed by its continuation. -/
theorem ruleResults_sound {space : Space} {live : List Atom} {query lhs rhs : Atom}
    {specIncoming : Bindings} {incoming : Metta.Bindings} {counter : Nat} {hit : Hit}
    (stored : .expression [.symbol "=", lhs, rhs] ∈ space.atoms)
    (invariant : BindingInvariant specIncoming incoming)
    (member : hit ∈ ruleResults live query specIncoming incoming counter lhs rhs) :
    ∃ specOutput,
      EquationQueryCandidateRel space live query specIncoming hit.value specOutput ∧
        BindingInvariant specOutput hit.bindings := by
  obtain ⟨_, specMatched, specOutput, _, _, _, _, selected, result, next⟩ :=
    ruleResults_sound_witness invariant member
  exact ⟨specOutput,
    ⟨_, _, specMatched, ⟨lhs, rhs, stored, selected⟩, result⟩, next⟩

structure LocatedHit where
  position : Nat
  lhs : Atom
  rhs : Atom
  result : Hit
  deriving Repr

/-- Ordered full-space query; non-rule atoms retain their source positions. -/
def queryResults (space : Space) (live : List Atom) (query : Atom) (specIncoming : Bindings)
    (incoming : Metta.Bindings) (counter : Nat) : List LocatedHit :=
  space.atoms.zipIdx.flatMap fun (atom, position) =>
    match atom with
    | .expression [.symbol "=", lhs, rhs] =>
        (ruleResults live query specIncoming incoming (counter + position) lhs rhs).map
          fun hit => ⟨position, lhs, rhs, hit⟩
    | _ => []

/-- Source positions and raw rule identities come from the stored space,
while returned hits come from that exact candidate's execution. -/
theorem queryResults_witness {space : Space} {live : List Atom} {query : Atom}
    {specIncoming : Bindings} {incoming : Metta.Bindings} {counter : Nat} {hit : LocatedHit}
    (member : hit ∈ queryResults space live query specIncoming incoming counter) :
    (.expression [.symbol "=", hit.lhs, hit.rhs], hit.position) ∈ space.atoms.zipIdx ∧
      hit.result ∈ ruleResults live query specIncoming incoming
        (counter + hit.position) hit.lhs hit.rhs := by
  simp only [queryResults, List.mem_flatMap] at member
  obtain ⟨⟨atom, position⟩, source, candidate⟩ := member
  split at candidate
  · rename_i lhs rhs
    obtain ⟨result, executed, rfl⟩ := List.mem_map.mp candidate
    subst_vars
    exact ⟨source, executed⟩
  · simp at candidate

/-- Exact completeness of the finite source-row enumeration for its actual
per-rule executions. Non-rule offsets are counted before matching. -/
theorem queryResults_mem_iff (space : Space) (live : List Atom) (query : Atom)
    (specIncoming : Bindings) (incoming : Metta.Bindings) (counter : Nat) (hit : LocatedHit) :
    hit ∈ queryResults space live query specIncoming incoming counter ↔
      space.atoms[hit.position]? = some (.expression [.symbol "=", hit.lhs, hit.rhs]) ∧
      hit.result ∈ ruleResults live query specIncoming incoming
        (counter + hit.position) hit.lhs hit.rhs := by
  constructor
  · intro member
    obtain ⟨stored, executed⟩ := queryResults_witness member
    exact ⟨List.mem_zipIdx_iff_getElem?.mp stored, executed⟩
  · rintro ⟨stored, executed⟩
    apply List.mem_flatMap.mpr
    refine ⟨(.expression [.symbol "=", hit.lhs, hit.rhs], hit.position),
      List.mem_zipIdx_iff_getElem?.mpr stored, ?_⟩
    change hit ∈ (ruleResults live query specIncoming incoming
      (counter + hit.position) hit.lhs hit.rhs).map
      (fun result => ⟨hit.position, hit.lhs, hit.rhs, result⟩)
    exact List.mem_map.mpr ⟨hit.result, executed, by cases hit; rfl⟩

/-- A semantic occurrence using this query's actual fresh pair supplies a
native match. This is before ambient merge and loop filtering, so it does not
claim that every such match survives as a returned hit. -/
theorem occurrence_match_nonempty {space : Space} {live : List Atom} {query lhs rhs : Atom}
    {specIncoming output matched : Bindings} {incoming : Metta.Bindings}
    {counter position : Nat} {emitted : Atom}
    (occurrence : EquationQueryOccurrenceRel space live query specIncoming position lhs rhs
      (freshRule live query specIncoming incoming (counter + position) lhs rhs).1
      (freshRule live query specIncoming incoming (counter + position) lhs rhs).2
      matched emitted output) :
    Metta.matchAtoms
      (toLeaTTaAtom (freshRule live query specIncoming incoming (counter + position) lhs rhs).1)
      (toLeaTTaAtom query) ≠ [] :=
  (match_nonempty_iff live query specIncoming incoming (counter + position) lhs rhs).mpr
    ⟨matched, occurrence.selected.2⟩

/-- Completeness for a physical occurrence using the query's chosen fresh
pair. The actual hit has the same binding solution theory and an equivalent
emitted value under every model of the source output. Neither raw binding-list
equality nor a count of all semantic derivations is asserted. -/
theorem occurrence_observational_complete {space : Space} {live : List Atom}
    {query lhs rhs emitted : Atom} {specIncoming matched output : Bindings}
    {incoming : Metta.Bindings} {counter position : Nat}
    (invariant : BindingInvariant specIncoming incoming)
    (occurrence : EquationQueryOccurrenceRel space live query specIncoming position lhs rhs
      (freshRule live query specIncoming incoming (counter + position) lhs rhs).1
      (freshRule live query specIncoming incoming (counter + position) lhs rhs).2
      matched emitted output) :
    ∃ result : Hit,
      (⟨position, lhs, rhs, result⟩ : LocatedHit) ∈
        queryResults space live query specIncoming incoming counter ∧
      LeaBindingSolutionTheoryEquiv output result.bindings ∧
      ∀ valuation, HEBindingSatisfied valuation output →
        HEAtomEquationSatisfied valuation result.value emitted := by
  let fresh := freshRule live query specIncoming incoming (counter + position) lhs rhs
  obtain ⟨sourceModel, sourceSatisfied⟩ := occurrence.result.1.he_model
  have common := (occurrence.result.1.he_solutions sourceModel).mp sourceSatisfied
  obtain ⟨callerFirst, callerFirstMerge, callerFirstSatisfied, _callerFirstShape⟩ :=
    Spec.Match.Completeness.exists_specMerge_of_solution
      common.2 invariant.semantic.specAssignmentsNonVariable
      common.1 (specMatch_assignmentsNonVariable occurrence.selected.2)
  have callerFirstModel : ∃ valuation, HEBindingSatisfied valuation callerFirst :=
    ⟨sourceModel, callerFirstSatisfied⟩
  have callerFirstTheory (valuation : String → Metta.Atom) :
      HEBindingSatisfied valuation output ↔ HEBindingSatisfied valuation callerFirst := by
    rw [occurrence.result.1.he_solutions,
      Spec.Match.SolutionTheory.mergeRel_solution_iff callerFirstMerge, and_comm]
  obtain ⟨nativeMatched, merged, matchMember, mergeMember, loopFree, callerFirstEquivalent⟩ :=
    queryOp_hit_exists_of_spec invariant.semantic.solutionTheory
      invariant.semantic.runtime.noFloat invariant.semantic.runtime.assignmentsNonVariable
      invariant.semantic.runtime.equalitiesIrreflexive
      (freshRule_varsDisjoint live query specIncoming incoming (counter + position) lhs rhs)
      occurrence.selected.2 callerFirstMerge callerFirstModel
  have equivalent : LeaBindingSolutionTheoryEquiv output merged :=
    fun valuation => (callerFirstTheory valuation).trans (callerFirstEquivalent valuation)
  let result : Hit := ⟨fromLeaTTaAtom (Metta.instantiate merged (toLeaTTaAtom fresh.2)), merged⟩
  have returned : result ∈ ruleResults live query specIncoming incoming (counter + position) lhs rhs :=
    ruleResults_of_match_merge matchMember mergeMember loopFree
  have matchedImage : LeaBindingsHEImage nativeMatched :=
    leaMatchAtoms_result_heImage (leaAtomHEImage_toLeaTTaAtom fresh.1)
      (leaAtomHEImage_toLeaTTaAtom query) matchMember
  have mergedImage := leaMerge_result_image invariant.image matchedImage mergeMember
  have emittedImage := instantiate_heImage mergedImage _ (leaAtomHEImage_toLeaTTaAtom fresh.2)
  refine ⟨result, (queryResults_mem_iff _ _ _ _ _ _ _).mpr ⟨occurrence.stored, returned⟩,
    equivalent, ?_⟩
  intro valuation satisfied
  have observed := anchored_observable_inert equivalent satisfied (toLeaTTaAtom fresh.2)
  have original := occurrence.result.2 valuation satisfied
  change applyClassSolution valuation (toLeaTTaAtom result.value) =
    applyClassSolution valuation (toLeaTTaAtom emitted)
  change applyClassSolution valuation (toLeaTTaAtom emitted) =
    applyClassSolution valuation (toLeaTTaAtom fresh.2) at original
  change applyClassSolution valuation
    (toLeaTTaAtom (fromLeaTTaAtom (Metta.instantiate merged (toLeaTTaAtom fresh.2)))) = _
  rw [toLeaTTaAtom_fromLeaTTaAtom_of_heImage emittedImage]
  exact observed.trans original.symm

/-- Every physical hit is justified by its own raw row and the same native
matching, merging and freshening execution. This is query soundness, before
`Minimal.CoreInvocationResultRel` and recursive RHS evaluation. -/
theorem queryResults_occurrence_sound {space : Space} {live : List Atom} {query : Atom}
    {specIncoming : Bindings} {incoming : Metta.Bindings} {counter : Nat} {hit : LocatedHit}
    (invariant : BindingInvariant specIncoming incoming)
    (member : hit ∈ queryResults space live query specIncoming incoming counter) :
    ∃ nativeMatched specMatched specOutput,
      nativeMatched ∈ Metta.matchAtoms
        (toLeaTTaAtom (freshRule live query specIncoming incoming
          (counter + hit.position) hit.lhs hit.rhs).1) (toLeaTTaAtom query) ∧
      hit.result.bindings ∈ Metta.Bindings.merge incoming nativeMatched ∧
      hit.result.bindings.hasLoop = false ∧
      hit.result.value = fromLeaTTaAtom (Metta.instantiate hit.result.bindings
        (toLeaTTaAtom (freshRule live query specIncoming incoming
          (counter + hit.position) hit.lhs hit.rhs).2)) ∧
      EquationQueryOccurrenceRel space live query specIncoming hit.position hit.lhs hit.rhs
        (freshRule live query specIncoming incoming (counter + hit.position) hit.lhs hit.rhs).1
        (freshRule live query specIncoming incoming (counter + hit.position) hit.lhs hit.rhs).2
        specMatched hit.result.value specOutput ∧
      BindingInvariant specOutput hit.result.bindings := by
  obtain ⟨source, executed⟩ := queryResults_witness member
  obtain ⟨nativeMatched, specMatched, specOutput, matched, merged, loopFree, emitted,
    selected, result, next⟩ := ruleResults_sound_witness invariant executed
  exact ⟨nativeMatched, specMatched, specOutput, matched, merged, loopFree, emitted,
    ⟨List.mem_zipIdx_iff_getElem?.mp source, selected, result⟩, next⟩

/-- Every complete-space query hit has independently justified semantics
and retains a valid paired binding state for subsequent evaluation. -/
theorem queryResults_sound {space : Space} {live : List Atom} {query : Atom}
    {specIncoming : Bindings} {incoming : Metta.Bindings} {counter : Nat} {hit : LocatedHit}
    (invariant : BindingInvariant specIncoming incoming)
    (member : hit ∈ queryResults space live query specIncoming incoming counter) :
    ∃ specOutput,
      EquationQueryCandidateRel space live query specIncoming hit.result.value specOutput ∧
        BindingInvariant specOutput hit.result.bindings := by
  obtain ⟨_, _, output, _, _, _, _, occurrence, next⟩ :=
    queryResults_occurrence_sound invariant member
  exact ⟨output, occurrence.candidate, next⟩

/-- Every legal independent alpha variant of a physical raw row is realized
by the scoped query, after a constructed caller-fixed private permutation.
The returned native hit retains a paired binding invariant for the transported
source output. Full binding theory is preserved under valuation reindexing,
not by equating records whose private variable spellings differ. -/
theorem occurrence_arbitrary_alpha_complete {space : Space} {live : List Atom}
    {query lhs rhs sourcePattern sourceRhs emitted : Atom}
    {specIncoming matched output : Bindings} {incoming : Metta.Bindings}
    {counter position : Nat}
    (invariant : BindingInvariant specIncoming incoming)
    (source : EquationQueryOccurrenceRel space live query specIncoming position lhs rhs
      sourcePattern sourceRhs matched emitted output) :
    ∃ permutation : Equiv.Perm String, ∃ targetMatched targetOutput result,
      (∀ name, QueryVisibleName live query specIncoming name → permutation name = name) ∧
      (⟨position, lhs, rhs, result⟩ : LocatedHit) ∈
        queryResults space live query specIncoming incoming counter ∧
      EquationQueryOccurrenceRel space live query specIncoming position lhs rhs
        (freshRule live query specIncoming incoming (counter + position) lhs rhs).1
        (freshRule live query specIncoming incoming (counter + position) lhs rhs).2
        targetMatched result.value targetOutput ∧
      BindingInvariant targetOutput result.bindings ∧
      (∀ valuation, HEBindingSatisfied valuation targetOutput ↔
        HEBindingSatisfied (valuation ∘ permutation) output) ∧
      ∀ valuation, HEBindingSatisfied valuation targetOutput →
        HEAtomEquationSatisfied valuation result.value (Spec.Type.RuntimeRefinement.renameTypeVars permutation emitted) := by
  obtain ⟨permutation, targetMatched, targetOutput, fixed, _, _, target, theory,
    targetNonvariable⟩ :=
    EquationFreshening.occurrence_alpha_transport invariant.semantic.specAssignmentsNonVariable source
      (freshRule_alphaVariant live query specIncoming incoming (counter + position) lhs rhs)
  obtain ⟨result, member, equivalent, observed⟩ :=
    occurrence_observational_complete invariant target
  have executed := (queryResults_mem_iff _ _ _ _ _ _ _).mp member |>.2
  obtain ⟨nativeMatched, merged, matchMember, mergeMember, loopFree, resultEq⟩ :=
    ruleResults_witness executed
  change result = _ at resultEq
  have runtime : LeaRuntimeBindingInvariant result.bindings := by
    rw [resultEq]
    exact LeaRuntimeBindingInvariant.merge_matchOutput invariant.semantic.runtime
      (toLeaTTaAtom_noFloat _) (toLeaTTaAtom_noFloat _) matchMember mergeMember loopFree
  have paired : BindingInvariant targetOutput result.bindings :=
    ⟨⟨equivalent, targetNonvariable, runtime⟩, ruleResults_bindingsImage invariant.image executed⟩
  refine ⟨permutation, targetMatched, targetOutput, result, fixed, member,
    ⟨target.stored, target.selected,
      ⟨target.result.1, ?_⟩⟩,
    paired, theory, observed⟩
  intro valuation satisfied
  exact (observed valuation satisfied).trans (target.result.2 valuation satisfied)

end Mettapedia.Languages.MeTTa.HE.ScopedEquationQuery

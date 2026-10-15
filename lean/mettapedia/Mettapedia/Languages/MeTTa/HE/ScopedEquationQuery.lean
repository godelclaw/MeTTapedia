import Mettapedia.Languages.MeTTa.HE.RecursiveScope

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
  refine ⟨specOutput, ?_, ⟨next, mergedImage⟩⟩
  refine ⟨fresh.1, fresh.2, specMatched, ?_, mergeDerivation,
    semanticLoopFree_of_satisfied_nonvariable satisfied next.specAssignmentsNonVariable,
    ⟨leaClassSolution merged, satisfied⟩, ?_⟩
  · exact ⟨lhs, rhs, stored,
      freshRule_alphaVariant live query specIncoming incoming counter lhs rhs, matchDerivation⟩
  · intro valuation outputSatisfied
    unfold HEAtomEquationSatisfied
    rw [toLeaTTaAtom_fromLeaTTaAtom_of_heImage emittedImage]
    exact observation valuation outputSatisfied

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

/-- Every complete-space query hit has independently justified semantics
and retains a valid paired binding state for subsequent evaluation. -/
theorem queryResults_sound {space : Space} {live : List Atom} {query : Atom}
    {specIncoming : Bindings} {incoming : Metta.Bindings} {counter : Nat} {hit : LocatedHit}
    (invariant : BindingInvariant specIncoming incoming)
    (member : hit ∈ queryResults space live query specIncoming incoming counter) :
    ∃ specOutput,
      EquationQueryCandidateRel space live query specIncoming hit.result.value specOutput ∧
        BindingInvariant specOutput hit.result.bindings := by
  obtain ⟨source, executed⟩ := queryResults_witness member
  have stored : .expression [.symbol "=", hit.lhs, hit.rhs] ∈ space.atoms := by
    have mapped : Atom.expression [.symbol "=", hit.lhs, hit.rhs] ∈
        space.atoms.zipIdx.map Prod.fst :=
      List.mem_map.mpr ⟨(Atom.expression [.symbol "=", hit.lhs, hit.rhs], hit.position), source, rfl⟩
    simpa using mapped
  exact ruleResults_sound stored invariant executed

end Mettapedia.Languages.MeTTa.HE.ScopedEquationQuery

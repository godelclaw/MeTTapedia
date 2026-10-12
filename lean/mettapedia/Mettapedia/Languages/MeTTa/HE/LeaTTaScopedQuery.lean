import Mettapedia.Languages.MeTTa.HE.QueryBindingProjection

/-!
# Independent query derivations for the actual LeaTTa work-item generator

The existing executable `queryOpItemsOfRule` supplies matching, merge, loop
filtering, instantiation and continuation handling. Its actual freshening is
proved hygienic against the complete projected binding support and retained
stack scope. Pattern representation and logical binding correspondence are
constructed here rather than required as caller-supplied correspondence laws.

The scope view contains names only; it is not a representation of the whole
interpreter state. The result covers one stored equation candidate, before
recursive interpretation, type selection or native C implementation refinement.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaScopedQuery

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open LeaTTaBridge LeaTTaTypeConformance LeaTTaSpecConformance
open Spec.Match.Merge Spec.Eval.Steps

def liveScope (previous : Metta.Minimal.Stack) : List Atom :=
  (Metta.Minimal.liveStackVars previous).map Atom.var

theorem liveScope_name_mem {previous : Metta.Minimal.Stack} {atom : Atom} {name : String}
    (member : atom ∈ liveScope previous) (occurrence : name ∈ (toLeaTTaAtom atom).vars) :
    name ∈ Metta.Minimal.liveStackVars previous := by
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  have equal : name = original := by
    simpa only [toLeaTTaAtom, Metta.Atom.vars, List.mem_singleton] using occurrence
  subst name
  exact originalMember

theorem actual_scope_covers (previous : Metta.Minimal.Stack) (query : Atom)
    (incoming : Metta.Bindings) (image : LeaBindingsHEImage incoming) :
    ∀ name, QueryVisibleName (liveScope previous) query (QueryBindingProjection.project incoming) name →
      name ∈ Metta.Minimal.queryOpAvoid previous (toLeaTTaAtom query) incoming := by
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
  EquationFreshening.freshRule
    (Metta.Minimal.queryOpAvoid previous (toLeaTTaAtom query) incoming) counter lhs rhs

theorem freshRule_alphaVariant (previous : Metta.Minimal.Stack) (query : Atom)
    (incoming : Metta.Bindings) (image : LeaBindingsHEImage incoming) (counter : Nat) (lhs rhs : Atom) :
    AlphaVariantRel (liveScope previous) query (QueryBindingProjection.project incoming) lhs rhs
      (freshRule previous query incoming counter lhs rhs).1
      (freshRule previous query incoming counter lhs rhs).2 :=
  EquationFreshening.freshRule_alphaVariant_of_covers _ _ _ _ _ _ _
    (actual_scope_covers previous query incoming image)

/-- A returned work item constructs its independent equation-query derivation,
exact executable continuation and next representable, paired binding state. -/
theorem queryOpItemsOfRule_sound {space : Space} {previous : Metta.Minimal.Stack}
    {query lhs rhs : Atom} {incoming : Metta.Bindings} {counter : Nat} {item : Metta.Minimal.Item}
    (stored : .expression [.symbol "=", lhs, rhs] ∈ space.atoms)
    (image : LeaBindingsHEImage incoming) (runtime : LeaRuntimeBindingInvariant incoming)
    (member : item ∈ Metta.Minimal.queryOpItemsOfRule previous (toLeaTTaAtom query)
      incoming counter (toLeaTTaAtom lhs, toLeaTTaAtom rhs)) :
    ∃ emitted output merged,
      EquationQueryCandidateRel space (liveScope previous) query
          (QueryBindingProjection.project incoming) emitted output ∧
        item = Metta.Minimal.evalResult previous (toLeaTTaAtom emitted) merged ∧
        ScopedEquationQuery.BindingInvariant (QueryBindingProjection.project merged) merged ∧
        ∀ valuation,
          HEBindingSatisfied valuation output ↔
            HEBindingSatisfied valuation (QueryBindingProjection.project merged) := by
  obtain ⟨matched, matchedMember, merged, mergedMember, loopFree, itemEq⟩ :=
    (mem_queryOpItemsOfRule_iff _ _ _ _ _ _).mp member
  let fresh := freshRule previous query incoming counter lhs rhs
  have translation := EquationFreshening.freshRule_translation
    (Metta.Minimal.queryOpAvoid previous (toLeaTTaAtom query) incoming) counter lhs rhs
  have patternTranslation := congrArg Prod.fst translation
  have rhsTranslation := congrArg Prod.snd translation
  simp only at patternTranslation rhsTranslation
  change toLeaTTaAtom fresh.1 = _ at patternTranslation
  change toLeaTTaAtom fresh.2 = _ at rhsTranslation
  rw [← patternTranslation] at matchedMember
  obtain ⟨specMatched, output, matchDerivation, mergeDerivation, next, observation⟩ :=
    queryOp_hit_observational_sound (rhs := toLeaTTaAtom fresh.2)
      (QueryBindingProjection.paired incoming image runtime).semantic matchedMember mergedMember loopFree
  have matchedImage : LeaBindingsHEImage matched :=
    leaMatchAtoms_result_heImage (leaAtomHEImage_toLeaTTaAtom fresh.1)
      (leaAtomHEImage_toLeaTTaAtom query) matchedMember
  have mergedImage : LeaBindingsHEImage merged :=
    leaMerge_result_image image matchedImage mergedMember
  have emittedImage : LeaAtomHEImage (Metta.instantiate merged (toLeaTTaAtom fresh.2)) :=
    instantiate_heImage mergedImage _ (leaAtomHEImage_toLeaTTaAtom fresh.2)
  let emitted := fromLeaTTaAtom (Metta.instantiate merged (toLeaTTaAtom fresh.2))
  have projectedNext := QueryBindingProjection.paired merged mergedImage next.runtime
  have satisfied : HEBindingSatisfied (leaClassSolution merged) output :=
    (next.solutionTheory (leaClassSolution merged)).mpr next.runtime.canonical.1
  refine ⟨emitted, output, merged, ?_, ?_, projectedNext, ?_⟩
  · refine ⟨fresh.1, fresh.2, specMatched, ?_, mergeDerivation,
      semanticLoopFree_of_satisfied_nonvariable satisfied next.specAssignmentsNonVariable,
      ⟨leaClassSolution merged, satisfied⟩, ?_⟩
    · exact ⟨lhs, rhs, stored, freshRule_alphaVariant _ _ _ image _ _ _, matchDerivation⟩
    · intro valuation outputSatisfied
      unfold HEAtomEquationSatisfied
      rw [toLeaTTaAtom_fromLeaTTaAtom_of_heImage emittedImage]
      exact observation valuation outputSatisfied
  · rw [itemEq, ← rhsTranslation]
    rw [toLeaTTaAtom_fromLeaTTaAtom_of_heImage emittedImage]
  · intro valuation
    exact (next.solutionTheory valuation).trans (projectedNext.semantic.solutionTheory valuation).symm

end Mettapedia.Languages.MeTTa.HE.LeaTTaScopedQuery

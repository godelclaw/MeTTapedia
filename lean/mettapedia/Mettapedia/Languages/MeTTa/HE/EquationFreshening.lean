import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory
import Mettapedia.Languages.MeTTa.HE.EquationScope
import Mettapedia.Languages.MeTTa.HE.Spec.Match.Completeness
import Mettapedia.Languages.MeTTa.HE.Spec.Eval
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ScopeObservation
open Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory
open Mettapedia.Languages.MeTTa.HE.BindingComposition
open Mettapedia.Languages.MeTTa.HE.MatchSizeTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.ModelTransport

/-!
# Scoped equation instances and source alpha transport

Independent HE equation instances admit one permutation fixing the complete
caller-visible scope. Logical transport preserves their entire constraint
theory, including incoming variable-valued aliases. The structural HE
freshener realizes `AlphaVariantRel` without an atom-depth or evaluation-fuel
bound. Implementation fresheners are optional downstream realizations of
this source contract.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.EquationFreshening

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory
open Spec.Type.Presentation Spec.Type.Presentation.Exact
open Spec.Type.RuntimeRefinement
open Spec.Eval.Steps

/-- Reindexing a valuation by a caller-fixed name function leaves its query
observation unchanged, including names at arbitrary finite depth. -/
theorem query_observation_reindex {live : List Atom} {query : Atom} {incoming : Bindings}
    (rename : String → String)
    (fixed : ∀ name, QueryVisibleName live query incoming name → rename name = name)
    (valuation : String → Metta.Atom) :
    applyClassSolution (valuation ∘ rename) (encodeModelAtom query) =
      applyClassSolution valuation (encodeModelAtom query) := by
  apply Spec.Match.ModelTheory.applyClassSolution_congr_of_eq_on_vars
  intro name member
  have visible : QueryVisibleName live query incoming name :=
    Or.inl (Spec.Match.ModelTheory.atomOccurs_iff_mem_translated_vars.mpr member)
  simp only [Function.comp_apply, fixed name visible]

/-- All incoming value constraints and equality edges survive a caller-fixed
valuation reindexing. The generic finite-support observation law is reused. -/
theorem incoming_satisfaction_reindex {live : List Atom} {query : Atom} {incoming : Bindings}
    (rename : String → String)
    (fixed : ∀ name, QueryVisibleName live query incoming name → rename name = name)
    (valuation : String → Metta.Atom) :
    HEBindingSatisfied (valuation ∘ rename) incoming ↔ HEBindingSatisfied valuation incoming := by
  apply Spec.Match.ModelTheory.bindingSatisfied_congr_of_eq_on_support
  intro name member
  have listed : name ∈ EquationScope.bindingNames incoming := by
    apply List.mem_toFinset.mp
    rw [EquationScope.bindingNames_toFinset]
    exact member
  have visible : QueryVisibleName live query incoming name :=
    (EquationScope.mem_visibleNames_iff live query incoming name).mp
      (by simp only [EquationScope.visibleNames, List.mem_append]; tauto)
  simp only [Function.comp_apply, fixed name visible]

/-- Source fresh-instance transport uses logical conjunction rather than an
operational merge representation. It accepts arbitrary incoming aliases and
preserves the whole output theory under one caller-fixed permutation. -/
theorem occurrence_alpha_transport_logical
    {space : Space} {live : List Atom} {query lhs rhs sourcePattern sourceRhs
      targetPattern targetRhs emitted : Atom}
    {incoming matched output : Bindings} {position : Nat}
    (source : EquationQueryOccurrenceRel space live query incoming position lhs rhs
      sourcePattern sourceRhs matched emitted output)
    (targetVariant : AlphaVariantRel live query incoming lhs rhs targetPattern targetRhs) :
    ∃ permutation : Equiv.Perm String, ∃ targetMatched targetOutput,
      (∀ name, QueryVisibleName live query incoming name → permutation name = name) ∧
      targetPattern = renameTypeVars permutation sourcePattern ∧
      targetRhs = renameTypeVars permutation sourceRhs ∧
      EquationQueryOccurrenceRel space live query incoming position lhs rhs
        targetPattern targetRhs targetMatched (renameTypeVars permutation emitted) targetOutput ∧
      (∀ valuation, HEBindingSatisfied valuation targetOutput ↔
        HEBindingSatisfied (valuation ∘ permutation) output) ∧
      targetOutput = ⟨targetMatched.assignments ++ incoming.assignments,
        targetMatched.equalities ++ incoming.equalities⟩ := by
  obtain ⟨permutation, fixed, patternEquation, rhsEquation⟩ :=
    alphaVariants_public_fixed_permutation source.selected.1 targetVariant
  have inverseFixed : ∀ name, QueryVisibleName live query incoming name →
      permutation.symm name = name := by
    intro name visible
    apply permutation.injective
    simp only [Equiv.apply_symm_apply, fixed name visible]
  obtain ⟨sourceModel, sourceSatisfied⟩ := source.result.1.he_model
  let targetModel : String → Metta.Atom := sourceModel ∘ permutation.symm
  have modelRoundTrip : targetModel ∘ permutation = sourceModel := by
    funext name
    simp only [targetModel, Function.comp_apply, Equiv.symm_apply_apply]
  have sourceParts := (source.result.1.he_solutions sourceModel).mp sourceSatisfied
  have targetIncoming : HEBindingSatisfied targetModel incoming :=
    (incoming_satisfaction_reindex permutation.symm inverseFixed sourceModel).mpr sourceParts.2
  have targetEquation : HEAtomEquationSatisfied targetModel query targetPattern := by
    unfold HEAtomEquationSatisfied
    rw [patternEquation, applyClassSolution_renameTypeVars, modelRoundTrip]
    exact (query_observation_reindex permutation.symm inverseFixed sourceModel).trans
      ((Spec.Match.SolutionTheory.matchRel_solution_iff source.selected.2 sourceModel).mp sourceParts.1)
  obtain ⟨targetMatched, targetMatch, targetMatchedSatisfied⟩ :=
    Spec.Match.Completeness.exists_specMatch_of_solution targetEquation
  let targetOutput : Bindings :=
    ⟨targetMatched.assignments ++ incoming.assignments,
      targetMatched.equalities ++ incoming.equalities⟩
  have targetMerge : Spec.Bindings.ScopeObservation.LogicalMergeRel targetMatched incoming targetOutput :=
    Spec.Bindings.ScopeObservation.LogicalMergeRel.append_of_common_model
      ⟨_,specTypeBindingSatisfied_of_heBindingSatisfied targetMatchedSatisfied,
        specTypeBindingSatisfied_of_heBindingSatisfied targetIncoming⟩
  have theory (valuation : String → Metta.Atom) :
      HEBindingSatisfied valuation targetOutput ↔
        HEBindingSatisfied (valuation ∘ permutation) output := by
    rw [targetMerge.he_solutions,
      Spec.Match.SolutionTheory.matchRel_solution_iff targetMatch,
      source.result.1.he_solutions,
      Spec.Match.SolutionTheory.matchRel_solution_iff source.selected.2,
      incoming_satisfaction_reindex permutation fixed,
      query_observation_reindex permutation fixed,
      patternEquation, applyClassSolution_renameTypeVars]
  refine ⟨permutation, targetMatched, targetOutput, fixed, patternEquation, rhsEquation,
    ⟨source.stored, ⟨targetVariant, targetMatch⟩,
      ⟨targetMerge, ?_⟩⟩, theory, rfl⟩
  intro valuation satisfied
  unfold HEAtomEquationSatisfied
  rw [rhsEquation, applyClassSolution_renameTypeVars, applyClassSolution_renameTypeVars]
  exact source.result.2 (valuation ∘ permutation) ((theory valuation).mp satisfied)

/-- The existing no-variable-assignment specialization is obtained from the
general logical transport. Its stronger output invariant is preserved. -/
theorem occurrence_alpha_transport
    {space : Space} {live : List Atom} {query lhs rhs sourcePattern sourceRhs
      targetPattern targetRhs emitted : Atom}
    {incoming matched output : Bindings} {position : Nat}
    (incomingNonvariable : HEAssignmentsNonVariable incoming)
    (source : EquationQueryOccurrenceRel space live query incoming position lhs rhs
      sourcePattern sourceRhs matched emitted output)
    (targetVariant : AlphaVariantRel live query incoming lhs rhs targetPattern targetRhs) :
    ∃ permutation : Equiv.Perm String, ∃ targetMatched targetOutput,
      (∀ name, QueryVisibleName live query incoming name → permutation name = name) ∧
      targetPattern = renameTypeVars permutation sourcePattern ∧
      targetRhs = renameTypeVars permutation sourceRhs ∧
      EquationQueryOccurrenceRel space live query incoming position lhs rhs
        targetPattern targetRhs targetMatched (renameTypeVars permutation emitted) targetOutput ∧
      (∀ valuation, HEBindingSatisfied valuation targetOutput ↔
        HEBindingSatisfied (valuation ∘ permutation) output) ∧
      HEAssignmentsNonVariable targetOutput := by
  obtain ⟨permutation,targetMatched,_,fixed,patternEquation,rhsEquation,selected,theory,rfl⟩ :=
    occurrence_alpha_transport_logical source targetVariant
  refine ⟨permutation,targetMatched,_,fixed,patternEquation,rhsEquation,selected,theory,?_⟩
  intro key target member
  rcases List.mem_append.mp member with matched | old
  · exact Spec.Match.ModelTheory.specMatch_assignmentsNonVariable selected.selected.2 key target matched
  · exact incomingNonvariable key target old

/-- A no-unifier certificate for one legal fresh instance rules out every
other instance of the same stored row, including with alias-bearing callers.
This supplies the negative leaf needed by complete source frontiers. -/
theorem row_miss_of_instance
    {space : Space} {live : List Atom} {query lhs rhs pattern body : Atom}
    {incoming : Bindings} {position : Nat}
    (stored : space.atoms[position]? = some (.expression [.symbol "=",lhs,rhs]))
    (variant : AlphaVariantRel live query incoming lhs rhs pattern body)
    (absent : ∀ matched output,
      ¬(Spec.Match.Merge.MatchRel Spec.Match.Merge.equalityGroundedSemantic query pattern matched ∧
        Spec.Bindings.ScopeObservation.LogicalMergeRel matched incoming output)) :
    EquationRowResultsRel live query incoming position (.expression [.symbol "=",lhs,rhs]) [] := by
  apply EquationRowResultsRel.miss position lhs rhs pattern body variant
  intro otherPattern otherBody otherInstance matched output viable
  have source : EquationQueryOccurrenceRel space live query incoming position lhs rhs
      otherPattern otherBody matched otherBody output :=
    ⟨stored,⟨otherInstance,viable.1⟩,viable.2,fun _ _ => rfl⟩
  obtain ⟨_,targetMatched,targetOutput,_,_,_,selected,_,_⟩ :=
    occurrence_alpha_transport_logical source variant
  exact absent targetMatched targetOutput ⟨selected.selected.2,selected.result.1⟩



/-! ## The retained evaluator's freshener

The retained HE evaluator renames each stored rule apart from every name visible
at the call (`equationScope`). Its instance is a legal independent alpha variant
at the same physical row, so every independent occurrence of that row transports
to the evaluator's own instance names. -/

mutual

private theorem atomVariables_eq_typeVars : ∀ atom : Atom,
    atomVariables atom = TypeSubst.typeVars atom
  | .var _ => by simp [atomVariables, TypeSubst.typeVars]
  | .symbol _ => by simp [atomVariables, TypeSubst.typeVars]
  | .grounded _ => by simp [atomVariables, TypeSubst.typeVars]
  | .expression atoms => by
      simp only [atomVariables, TypeSubst.typeVars]
      exact atomListVariables_eq_typeVarsList atoms

private theorem atomListVariables_eq_typeVarsList : ∀ atoms : List Atom,
    atomListVariables atoms = TypeSubst.typeVarsList atoms
  | [] => by simp [atomListVariables, TypeSubst.typeVarsList]
  | atom :: atoms => by
      simp only [atomListVariables, TypeSubst.typeVarsList]
      rw [atomVariables_eq_typeVars atom, atomListVariables_eq_typeVarsList atoms]

end

mutual

private theorem renameAtom_eq_renameTypeVars (rename : String → String) : ∀ atom : Atom,
    renameAtom rename atom = renameTypeVars rename atom
  | .var _ => by simp [renameAtom, renameTypeVars]
  | .symbol _ => by simp [renameAtom, renameTypeVars]
  | .grounded _ => by simp [renameAtom, renameTypeVars]
  | .expression atoms => by
      simp only [renameAtom, renameTypeVars]
      exact congrArg Atom.expression (renameAtomList_eq_renameTypeVars rename atoms)

private theorem renameAtomList_eq_renameTypeVars (rename : String → String) :
    ∀ atoms : List Atom, renameAtomList rename atoms = atoms.map (renameTypeVars rename)
  | [] => by simp [renameAtomList]
  | atom :: atoms => by
      simp only [renameAtomList, List.map_cons]
      rw [renameAtom_eq_renameTypeVars rename atom, renameAtomList_eq_renameTypeVars rename atoms]

end

/-- The structural variable scan has exactly the independent occurrence support. -/
theorem atomOccurs_iff_mem_atomVariables {atom : Atom} {name : String} :
    Spec.Match.Merge.AtomOccurs atom name ↔ name ∈ atomVariables atom := by
  rw [Spec.Match.ModelTheory.atomOccurs_iff_mem_translated_vars, encodeModelAtom_vars_eq_typeVars,
    atomVariables_eq_typeVars]

/-- Every name visible to the independent query judgment is in the call scope of
the retained evaluator. -/
theorem equationScope_visible {live : List Atom} {query type_ : Atom} {incoming : Bindings}
    {name : String} (visible : QueryVisibleName live query incoming name) :
    name ∈ equationScope live query type_ incoming := by
  simp only [equationScope, atomListVariables_eq_flatMap, Bindings.names, List.mem_append,
    List.mem_flatMap, List.mem_cons]
  rcases visible with queryOccurs | ⟨atom, member, occurs⟩ | ⟨value, member⟩ |
      ⟨key, value, member, occurs⟩ | ⟨left, right, member, endpoint⟩
  · exact Or.inl (Or.inl (Or.inr (atomOccurs_iff_mem_atomVariables.mp queryOccurs)))
  · exact Or.inl (Or.inl (Or.inl ⟨atom, member, atomOccurs_iff_mem_atomVariables.mp occurs⟩))
  · exact Or.inr (Or.inl ⟨(name, value), member, Or.inl rfl⟩)
  · exact Or.inr (Or.inl ⟨(key, value), member, Or.inr (atomOccurs_iff_mem_atomVariables.mp occurs)⟩)
  · exact Or.inr (Or.inr ⟨(left, right), member, by
      rcases endpoint with rfl | rfl <;> simp⟩)

/-- A covering list for a call contains every name visible to the independent
judgment when nothing else is retained. -/
theorem coversCall_visible {avoid : List String} {query : Atom} {incoming : Bindings}
    {name : String} (covers : CoversCall avoid query incoming)
    (visible : QueryVisibleName [] query incoming name) : name ∈ avoid := by
  apply covers
  rcases visible with queryOccurs | ⟨_, member, _⟩ | ⟨value, member⟩ |
      ⟨key, value, member, occurs⟩ | ⟨left, right, member, endpoint⟩
  · exact Or.inl (atomOccurs_iff_mem_atomVariables.mp queryOccurs)
  · simp at member
  · exact Or.inr (List.mem_append_left _ (List.mem_flatMap.mpr ⟨(name, value), member, by simp⟩))
  · exact Or.inr (List.mem_append_left _ (List.mem_flatMap.mpr ⟨(key, value), member,
      List.mem_cons_of_mem _ (atomOccurs_iff_mem_atomVariables.mp occurs)⟩))
  · exact Or.inr (List.mem_append_right _ (List.mem_flatMap.mpr ⟨(left, right), member, by
      rcases endpoint with rfl | rfl <;> simp⟩))

/-- The retained freshener realizes the independent alpha-variant judgment for
any avoidance list containing the visible scope. -/
theorem freshenEquationAvoiding_alphaVariant (live : List Atom) (query lhs rhs : Atom)
    (incoming : Bindings) (avoid : List String) (counter : Nat)
    (covers : ∀ name, QueryVisibleName live query incoming name → name ∈ avoid) :
    AlphaVariantRel live query incoming lhs rhs
      (freshenEquationAvoiding avoid counter lhs rhs).1
      (freshenEquationAvoiding avoid counter lhs rhs).2 := by
  let ruleVariables := (atomVariables lhs ++ atomVariables rhs).eraseDups
  refine ⟨instanceName avoid ruleVariables counter, instanceName_injective avoid ruleVariables counter,
    ?_, ?_, ?_⟩
  · simp only [freshenEquationAvoiding, renameAtom_eq_renameTypeVars]
    exact rename_alpha _ lhs
  · simp only [freshenEquationAvoiding, renameAtom_eq_renameTypeVars]
    exact rename_alpha _ rhs
  · intro name _ visible
    exact instanceName_not_mem avoid ruleVariables counter name (covers _ visible)

/-- One independent HE rule instance uses the existing structural freshener.
Its spelling is a representation choice; source coverage ranges over every
legal alpha variant. -/
def freshRule (avoid : List String) (counter : Nat) (lhs rhs : Atom) : Atom × Atom :=
  freshenEquationAvoiding avoid counter lhs rhs

/-- Both sides of the structural source instance avoid the full caller scope. -/
theorem freshRule_variables_avoid (avoid : List String) (counter : Nat) (lhs rhs : Atom) :
    ∀ name ∈ (encodeModelAtom (freshRule avoid counter lhs rhs).1).vars ++
        (encodeModelAtom (freshRule avoid counter lhs rhs).2).vars,
      name ∉ avoid := by
  intro name member
  rw [encodeModelAtom_vars_eq_typeVars, encodeModelAtom_vars_eq_typeVars] at member
  simp only [freshRule, freshenEquationAvoiding, renameAtom_eq_renameTypeVars,
    Spec.Type.Presentation.ScopeObservation.typeVars_renameTypeVars, List.mem_append] at member
  rcases member with member | member
  all_goals
    obtain ⟨original, _occurs, rfl⟩ := List.mem_map.mp member
    exact instanceName_not_mem _ _ _ _

/-- Any finite avoidance list covering the complete caller scope yields a
lawful source equation instance, independently of a runtime freshener. -/
theorem freshRule_alphaVariant_of_covers (live : List Atom) (query lhs rhs : Atom)
    (incoming : Bindings) (counter : Nat) (avoid : List String)
    (covers : ∀ name, QueryVisibleName live query incoming name → name ∈ avoid) :
    AlphaVariantRel live query incoming lhs rhs
      (freshRule avoid counter lhs rhs).1 (freshRule avoid counter lhs rhs).2 :=
  freshenEquationAvoiding_alphaVariant live query lhs rhs incoming avoid counter covers

theorem freshRule_alphaVariant (live : List Atom) (query lhs rhs : Atom)
    (incoming : Bindings) (counter : Nat) :
    AlphaVariantRel live query incoming lhs rhs
      (freshRule (EquationScope.visibleNames live query incoming) counter lhs rhs).1
      (freshRule (EquationScope.visibleNames live query incoming) counter lhs rhs).2 :=
  freshRule_alphaVariant_of_covers live query lhs rhs incoming counter _
    (fun name visible => (EquationScope.mem_visibleNames_iff live query incoming name).mpr visible)

/-- Every finite space has a complete source query frontier. Each physical
row is classified using one fresh instance; alpha transport earns coverage
of all other legal instances. This concerns selection only, not termination
of the selected equation bodies. Incoming aliases need no normalization. -/
theorem equationFrontier_exists (space : Space) (live : List Atom) (query : Atom)
    (incoming : Bindings) :
    ∃ results, EquationFrontierRel space live query incoming results := by
  classical
  have rowComplete (row : Atom × Nat) (member : row ∈ space.atoms.zipIdx) :
      ∃ results, EquationRowResultsRel live query incoming row.2 row.1 results := by
    have stored := List.mem_zipIdx_iff_getElem?.mp member
    by_cases equation : ∃ left right, row.1 = .expression [.symbol "=",left,right]
    · obtain ⟨left,right,shape⟩ := equation
      rw [shape] at stored ⊢
      let chosen := freshenEquationAvoiding (EquationScope.visibleNames live query incoming)
        row.2 left right
      have variant : AlphaVariantRel live query incoming left right chosen.1 chosen.2 :=
        freshenEquationAvoiding_alphaVariant live query left right incoming _ row.2
          (fun name visible => (EquationScope.mem_visibleNames_iff live query incoming name).mpr visible)
      by_cases viable : ∃ matched output,
          Spec.Match.Merge.MatchRel Spec.Match.Merge.equalityGroundedSemantic query chosen.1 matched ∧
          Spec.Bindings.ScopeObservation.LogicalMergeRel matched incoming output
      · obtain ⟨matched,output,matching,merged⟩ := viable
        exact ⟨_,.hit row.2 left right chosen.1 chosen.2 matched output variant matching merged⟩
      · exact ⟨[],row_miss_of_instance stored variant (by
          intro matched output both
          exact viable ⟨matched,output,both⟩)⟩
    · refine ⟨[],.irrelevant row.2 row.1 ?_⟩
      intro left right shape
      exact equation ⟨left,right,shape⟩
  have collect : ∀ rows : List (Atom × Nat),
      (∀ row ∈ rows, row ∈ space.atoms.zipIdx) →
      ∃ blocks, List.Forall₂ (fun row block =>
        EquationRowResultsRel live query incoming row.2 row.1 block) rows blocks := by
    intro rows
    induction rows with
    | nil => exact fun _ => ⟨[],.nil⟩
    | cons row rows ih =>
        intro included
        obtain ⟨block,classified⟩ := rowComplete row (included row (by simp))
        obtain ⟨blocks,rest⟩ := ih (fun item member => included item (List.mem_cons_of_mem _ member))
        exact ⟨block :: blocks,.cons classified rest⟩
  obtain ⟨blocks,completed⟩ := collect _ (fun _ member => member)
  exact ⟨blocks.flatten,.completed completed⟩

/-- Complete coverage preserves the entire principal binding theory and
the selected RHS observation, not only the existence of a matching row.
Representatives may differ by one permutation fixing the caller's scope. -/
theorem frontier_covers_readout
    {space : Space} {live : List Atom} {query lhs rhs sourcePattern sourceRhs emitted : Atom}
    {incoming matched output : Bindings} {position : Nat} {results : List EquationWork}
    (completed : EquationFrontierRel space live query incoming results)
    (source : EquationQueryOccurrenceRel space live query incoming position lhs rhs
      sourcePattern sourceRhs matched emitted output) :
    ∃ work ∈ results, work.position = position ∧ ∃ permutation : Equiv.Perm String,
      (∀ name, QueryVisibleName live query incoming name → permutation name = name) ∧
      work.pattern = renameTypeVars permutation sourcePattern ∧
      work.body = renameTypeVars permutation sourceRhs ∧
      (∀ valuation, HEBindingSatisfied valuation work.bindings ↔
        HEBindingSatisfied (valuation ∘ permutation) output) ∧
      (∀ valuation, HEBindingSatisfied valuation work.bindings →
        HEAtomEquationSatisfied valuation work.body (renameTypeVars permutation emitted)) := by
  obtain ⟨work,present,positionEquation⟩ := completed.covers source
  obtain ⟨workMatch,actual⟩ := completed.occurrence present
  have atPosition : EquationQueryOccurrenceRel space live query incoming position
      work.left work.right work.pattern work.body workMatch work.body work.bindings := by
    simpa only [positionEquation] using actual
  obtain ⟨leftEquation,rightEquation⟩ := source.raw_rule_unique atPosition
  have variant : AlphaVariantRel live query incoming lhs rhs work.pattern work.body := by
    rw [leftEquation,rightEquation]
    exact actual.selected.1
  obtain ⟨permutation,targetMatch,targetOutput,fixed,patternEquation,rhsEquation,selected,theory,_⟩ :=
    occurrence_alpha_transport_logical source variant
  have sameTheory (valuation : String → Metta.Atom) :
      HEBindingSatisfied valuation work.bindings ↔ HEBindingSatisfied valuation targetOutput := by
    rw [actual.result.1.he_solutions,selected.result.1.he_solutions,
      Spec.Match.SolutionTheory.matchRel_solution_iff actual.selected.2,
      Spec.Match.SolutionTheory.matchRel_solution_iff selected.selected.2]
  refine ⟨work,present,positionEquation,permutation,fixed,patternEquation,rhsEquation,
    fun valuation => (sameTheory valuation).trans (theory valuation),?_⟩
  intro valuation satisfied
  exact (selected.result.2 valuation ((sameTheory valuation).mp satisfied)).symm

/-- Every hit of the retained evaluator's equation query comes from a stored row
whose instance is a legal independent alpha variant for the call's visible
scope, and whose renamed left-hand side matched by the HE declarative matcher. -/
theorem queryEquationsAvoiding_instance {live : List Atom} {query : Atom} {incoming : Bindings}
    {avoid : List String} {space : Space} {fuel : Nat} {rhs : Atom} {qb : Bindings}
    (covers : ∀ name, QueryVisibleName live query incoming name → name ∈ avoid)
    (hit : (rhs, qb) ∈ queryEquationsAvoiding avoid space query fuel) :
    ∃ position lhs rhs0,
      space.atoms[position]? = some (.expression [.symbol "=", lhs, rhs0]) ∧
      AlphaVariantRel live query incoming lhs rhs0
        (freshenEquationAvoiding avoid position lhs rhs0).1
        (freshenEquationAvoiding avoid position lhs rhs0).2 ∧
      rhs = (freshenEquationAvoiding avoid position lhs rhs0).2 ∧
      DeclMatchSpec.MatchRel query (freshenEquationAvoiding avoid position lhs rhs0).1 qb ∧
      qb.hasLoop = false := by
  obtain ⟨lhs, rhs0, position, stored, emitted, matched, loopFree⟩ :=
    queryEquationsAvoiding_matchAtoms_witness hit
  rw [List.mem_zipIdx_iff_getElem?] at stored
  exact ⟨position, lhs, rhs0, stored,
    freshenEquationAvoiding_alphaVariant live query lhs rhs0 incoming avoid position covers,
    emitted, DeclMatchSpec.matchAtoms_sound matched, loopFree⟩

/-- The retained evaluator's own query at a call with retained atoms `live`,
expected type `type_` and incoming record `incoming` produces legal independent
instances. -/
theorem retained_query_instance {live : List Atom} {query type_ : Atom} {incoming : Bindings}
    {space : Space} {fuel : Nat} {rhs : Atom} {qb : Bindings}
    (hit : (rhs, qb) ∈ queryEquationsAvoiding (equationScope live query type_ incoming) space
      query fuel) :
    ∃ position lhs rhs0,
      space.atoms[position]? = some (.expression [.symbol "=", lhs, rhs0]) ∧
      AlphaVariantRel live query incoming lhs rhs0
        (freshenEquationAvoiding (equationScope live query type_ incoming) position lhs rhs0).1
        (freshenEquationAvoiding (equationScope live query type_ incoming) position lhs rhs0).2 ∧
      rhs = (freshenEquationAvoiding (equationScope live query type_ incoming) position lhs rhs0).2 ∧
      DeclMatchSpec.MatchRel query
        (freshenEquationAvoiding (equationScope live query type_ incoming) position lhs rhs0).1 qb ∧
      qb.hasLoop = false :=
  queryEquationsAvoiding_instance (fun _ visible => equationScope_visible visible) hit

/-- Any independent occurrence at a stored row transports to the retained
evaluator's own instance names for the same call, with every visible name fixed. -/
theorem occurrence_transports_to_retained_instance
    {space : Space} {live : List Atom} {query type_ lhs rhs sourcePattern sourceRhs emitted : Atom}
    {incoming matched output : Bindings} {position : Nat}
    (source : EquationQueryOccurrenceRel space live query incoming position lhs rhs
      sourcePattern sourceRhs matched emitted output) :
    ∃ permutation : Equiv.Perm String, ∃ targetMatched targetOutput,
      (∀ name, QueryVisibleName live query incoming name → permutation name = name) ∧
      EquationQueryOccurrenceRel space live query incoming position lhs rhs
        (freshenEquationAvoiding (equationScope live query type_ incoming) position lhs rhs).1
        (freshenEquationAvoiding (equationScope live query type_ incoming) position lhs rhs).2
        targetMatched (renameTypeVars permutation emitted) targetOutput ∧
      (∀ valuation, HEBindingSatisfied valuation targetOutput ↔
        HEBindingSatisfied (valuation ∘ permutation) output) := by
  obtain ⟨permutation, targetMatched, targetOutput, fixed, _, _, occurrence, theory, _⟩ :=
    occurrence_alpha_transport_logical source
      (freshenEquationAvoiding_alphaVariant live query lhs rhs incoming
        (equationScope live query type_ incoming) position
        (fun _ visible => equationScope_visible visible))
  exact ⟨permutation, targetMatched, targetOutput, fixed, occurrence, theory⟩


/-! ## Call-site signature instances

An invocation instantiates each returned signature by one injective map that
avoids the protected scope and every earlier instance of the same query. The
executable list is therefore an ordered alpha-variant list of the literal
annotation list; repeated variables of one signature stay correlated. -/

/-- The executable binding-name scan is the independent binding support. -/
theorem bindings_names_eq_specBindingVars (bindings : Bindings) :
    bindings.names = Spec.Bindings.ScopeObservation.specBindingVars bindings := by
  simp only [Bindings.names, Spec.Bindings.ScopeObservation.specBindingVars,
    atomVariables_eq_typeVars]

theorem instantiateTypeSignature_variant {avoid scope : List String} (position : Nat)
    (signature : Atom) (protects : ∀ name ∈ avoid, name ∈ scope) :
    TypeCandidateAlphaVariantRel avoid signature
      (instantiateTypeSignature scope position signature) :=
  ⟨instanceName scope (atomVariables signature).eraseDups position,
    instanceName_injective _ _ _, renameAtom_eq_renameTypeVars _ _,
    fun name _ member => instanceName_not_mem _ _ _ name (protects _ member)⟩

theorem instantiateTypeSignatures_variants {avoid scope : List String} (position : Nat)
    (signatures : List Atom) (protects : ∀ name ∈ avoid, name ∈ scope) :
    ArgumentAlphaVariantsRel avoid signatures
      (instantiateTypeSignatures scope position signatures) := by
  induction signatures generalizing avoid scope position with
  | nil => exact .nil avoid
  | cons signature rest ih =>
      simp only [instantiateTypeSignatures]
      refine .cons (instantiateTypeSignature_variant position signature protects)
        (ih (position + 1) ?_)
      intro name member
      rcases List.mem_append.mp member with old | new
      · exact List.mem_append_right _ (protects name old)
      · exact List.mem_append_left _ (by rwa [atomVariables_eq_typeVars])

/-- The executable invocation query is an ordered alpha-variant list of the
literal annotation list. Its instances avoid the protected scope, every reached
binding name and the variables of the subject and of its demand, hence every
avoidance list contained in those names. -/
theorem getAtomTypesScoped_variants {avoid : List String} (scope : List String) (space : Space)
    (bindings : Bindings) (subject expected : Atom)
    (protects : ∀ name ∈ avoid, name ∈ scope ++ Spec.Bindings.ScopeObservation.specBindingVars bindings ++
      TypeSubst.typeVars subject ++ TypeSubst.typeVars expected) :
    ArgumentAlphaVariantsRel avoid
      (getAtomTypes space subject) (getAtomTypesScoped scope space bindings subject expected) :=
  instantiateTypeSignatures_variants 0 _ fun name member => by
    simpa only [bindings_names_eq_specBindingVars, atomVariables_eq_typeVars] using
      protects name member

/-- Service-level bridge: given the literal lookup derivation, the worker's
invocation query answers the scoped source lookup for every protected scope
that the worker retains. -/
theorem getAtomTypesScoped_scopedTypeLookup {protectedScope : List String} (scope : List String)
    (space : Space) (bindings : Bindings) (subject expected : Atom)
    (raw : Spec.Type.StorageTypesRel space subject (getAtomTypes space subject))
    (retained : ∀ name ∈ protectedScope, name ∈ scope) :
    Spec.Eval.scopedTypeLookup protectedScope space bindings subject expected
      (getAtomTypesScoped scope space bindings subject expected) := by
  refine ⟨getAtomTypes space subject, raw,
    getAtomTypesScoped_variants scope space bindings subject expected ?_⟩
  intro name member
  simp only [Spec.Eval.invocationTypeScope, List.nil_append, TypeSubst.typeVarsList,
    List.append_nil, List.mem_append] at member ⊢
  rcases member with (kept | subjectName | expectedName) | bound
  · exact Or.inl (Or.inl (Or.inl (retained name kept)))
  · exact Or.inl (Or.inr subjectName)
  · exact Or.inr expectedName
  · exact Or.inl (Or.inl (Or.inr bound))

/-- Negative control: instantiation renames schematic signatures, so the
executable query is not the literal annotation list in general. -/
example : getAtomTypesScoped [] (Space.ofList
      [.expression [.symbol ":", .symbol "ident", .expression [.symbol "->", .var "t", .var "t"]]])
      Bindings.empty (.symbol "ident") (.symbol "%Undefined%") ≠
    [.expression [.symbol "->", .var "t", .var "t"]] := by decide

namespace LogicalTransportControls

def incoming : Bindings := ⟨[("left",.var "right")],[]⟩
def query : Atom := .symbol "Value"
def context : Space := Space.ofList [.expression [.symbol "=",.var "private",.var "private"]]

private theorem source_instance : AlphaVariantRel [] query incoming
    (.var "private") (.var "private") (.var "private") (.var "private") := by
  refine ⟨id,Function.injective_id,.variable _,.variable _,?_⟩
  intro name occurs
  rcases occurs with occurs | occurs <;> cases occurs
  all_goals simp [QueryVisibleName,query,incoming,
    ← Spec.Match.Merge.mem_vars_iff_atomOccurs,Mettapedia.Languages.MeTTa.SubstitutionAlgebra.vars]

/-- The source caller really contains a bare alias, outside the old input
invariant. This is not an empty or normalized special case. -/
theorem caller_is_not_nonvariable : ¬HEAssignmentsNonVariable incoming := by
  intro normalized
  exact normalized "left" "right" (by simp [incoming])

private theorem source_occurrence : ∃ matched output,
    EquationQueryOccurrenceRel context [] query incoming 0 (.var "private") (.var "private")
      (.var "private") (.var "private") matched (.var "private") output := by
  let valuation : String → Metta.Atom := fun _ => .sym "Value"
  obtain ⟨matched,matching,satisfied⟩ := Spec.Match.Completeness.exists_specMatch_of_solution
    (show HEAtomEquationSatisfied valuation query (.var "private") by
      simp [HEAtomEquationSatisfied,valuation,query,encodeModelAtom,applyClassSolution])
  have callerModel : HEBindingSatisfied valuation incoming := by
    simp [HEBindingSatisfied,incoming,valuation,applyClassSolution,encodeModelAtom]
  have merged := Spec.Bindings.ScopeObservation.LogicalMergeRel.append_of_common_model
    ⟨_,specTypeBindingSatisfied_of_heBindingSatisfied satisfied,
      specTypeBindingSatisfied_of_heBindingSatisfied callerModel⟩
  exact ⟨matched,_,rfl,⟨source_instance,matching⟩,merged,fun _ _ => rfl⟩

def target : Atom × Atom := freshenEquationAvoiding
  (EquationScope.visibleNames [] query incoming) 0 (.var "private") (.var "private")

private theorem target_instance : AlphaVariantRel [] query incoming
    (.var "private") (.var "private") target.1 target.2 :=
  freshenEquationAvoiding_alphaVariant [] query _ _ incoming _ 0
    (fun name visible => (EquationScope.mem_visibleNames_iff [] query incoming name).mpr visible)

theorem fresh_instance_is_distinct : target.1 ≠ .var "private" := by decide +kernel

/-- Actual distinct fresh instances preserve the complete source theory
with the caller's bare alias and every visible name fixed. -/
theorem aliased_caller_transports :
    ∃ sourceMatched sourceOutput, ∃ permutation : Equiv.Perm String, ∃ matched output,
      EquationQueryOccurrenceRel context [] query incoming 0 (.var "private") (.var "private")
        (.var "private") (.var "private") sourceMatched (.var "private") sourceOutput ∧
      (∀ name, QueryVisibleName [] query incoming name → permutation name = name) ∧
      EquationQueryOccurrenceRel context [] query incoming 0 (.var "private") (.var "private")
        target.1 target.2 matched (renameTypeVars permutation (.var "private")) output ∧
      (∀ valuation, HEBindingSatisfied valuation output ↔
        HEBindingSatisfied (valuation ∘ permutation) sourceOutput) := by
  obtain ⟨matched,output,source⟩ := source_occurrence
  obtain ⟨permutation,targetMatched,targetOutput,fixed,_,_,selected,theory,_⟩ :=
    occurrence_alpha_transport_logical source target_instance
  exact ⟨matched,output,permutation,targetMatched,targetOutput,source,fixed,selected,theory⟩

/-- A name occurring only inside a caller alias remains protected. Reusing
it for the rule's private variable would capture that caller relation. -/
theorem alias_value_cannot_be_a_private_instance :
    ¬AlphaVariantRel [] query incoming (.var "private") (.var "private")
      (.var "right") (.var "right") := by
  rintro ⟨rename,_,renamed,_,fresh⟩
  have same : rename "private" = "right" := by
    simpa only [renameTypeVars,Atom.var.injEq] using (alphaRename_eq renamed).symm
  have outside := fresh "private" (Or.inl (.var "private"))
  rw [same] at outside
  apply outside
  simp [QueryVisibleName,incoming,query,
    ← Spec.Match.Merge.mem_vars_iff_atomOccurs,Mettapedia.Languages.MeTTa.SubstitutionAlgebra.vars]

end LogicalTransportControls

end Mettapedia.Languages.MeTTa.HE.EquationFreshening

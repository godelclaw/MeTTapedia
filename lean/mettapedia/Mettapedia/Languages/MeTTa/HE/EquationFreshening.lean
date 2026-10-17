import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory
import Mettapedia.Languages.MeTTa.HE.EquationScope
import Mettapedia.Languages.MeTTa.HE.Spec.Match.Completeness
import Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationExactConformance
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ScopeObservation
import MettaHyperonFull.Proofs.CaptureAvoidingFreshening

/-!
# Equation freshening realizes independent alpha variation

Both branches of LeaTTa's actual rule freshener are simultaneous, injective
renamings. The collision branch avoids the complete finite caller scope;
the normal branch retains its existing spelling when that spelling is fresh.
The structural HE adapter realizes `AlphaVariantRel` without an atom-depth
or evaluation-fuel bound.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.EquationFreshening

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open LeaTTaBridge LeaTTaTypeConformance LeaTTaTypePresentationExactConformance
open Spec.Type.Presentation Spec.Type.Presentation.Exact
open Spec.Type.RuntimeRefinement
open Spec.Eval.Steps

private theorem mapped_lookup (names : List String) (rename : String → String)
    (name : String) (member : name ∈ names) :
    Metta.Subst.lookup (names.map fun candidate =>
      (candidate, Metta.Atom.var (rename candidate))) name =
        some (.var (rename name)) := by
  induction names with
  | nil => simp at member
  | cons head tail ih =>
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · simp [Metta.Subst.lookup]
    · by_cases equal : name = head
      · subst name
        simp [Metta.Subst.lookup]
      · simpa [Metta.Subst.lookup, equal] using ih member

private theorem mapped_apply (names : List String) (rename : String → String)
    (atom : Metta.Atom) (covers : ∀ name ∈ atom.vars, name ∈ names) :
    Metta.Subst.apply (names.map fun name => (name, Metta.Atom.var (rename name))) atom =
      Metta.Minimal.renameAllVars rename atom := by
  cases atom with
  | sym name => simp [Metta.Subst.apply, Metta.Minimal.renameAllVars]
  | gnd value => simp [Metta.Subst.apply, Metta.Minimal.renameAllVars]
  | var name =>
      have member : name ∈ names := covers name (by simp [Metta.Atom.vars])
      simp [Metta.Subst.apply, Metta.Minimal.renameAllVars,
        mapped_lookup names rename name member]
  | expr atoms =>
      simp only [Metta.Subst.apply, Metta.Minimal.renameAllVars]
      congr 1
      apply List.map_congr_left
      intro atom member
      apply mapped_apply names rename atom
      intro name occurrence
      apply covers name
      simp only [Metta.Atom.vars, List.mem_flatten]
      exact ⟨atom.vars, List.mem_map.mpr ⟨atom, member, rfl⟩, occurrence⟩
termination_by atom.size
decreasing_by
  subst_vars
  have bound : atom.size ≤ (atoms.map Metta.Atom.size).sum :=
    List.le_sum_of_mem (List.mem_map.mpr ⟨atom, member, rfl⟩)
  simp only [Metta.Atom.size]
  omega

/-- The ordinary counter freshener is one total simultaneous renaming. -/
theorem legacy_is_total_renaming (counter : Nat) (lhs rhs : Metta.Atom) :
    Metta.Minimal.freshenRule counter lhs rhs =
      (Metta.Minimal.renameAllVars (fun name => name ++ "#" ++ toString counter) lhs,
        Metta.Minimal.renameAllVars (fun name => name ++ "#" ++ toString counter) rhs) := by
  have left := mapped_apply (lhs.vars ++ rhs.vars)
    (fun name => name ++ "#" ++ toString counter) lhs
    (fun name member => List.mem_append_left _ member)
  have right := mapped_apply (lhs.vars ++ rhs.vars)
    (fun name => name ++ "#" ++ toString counter) rhs
    (fun name member => List.mem_append_right _ member)
  unfold Metta.Minimal.freshenRule
  split
  · rename_i empty
    simp only [empty, List.map_nil, Metta.Subst.apply_nil] at left right
    exact congrArg₂ Prod.mk left right
  · exact congrArg₂ Prod.mk left right

/-- The name function selected by the runtime's collision test. -/
def ruleRename (avoid : List String) (counter : Nat) (lhs rhs : Metta.Atom) : String → String :=
  if ∃ name ∈ (Metta.Minimal.freshenRule counter lhs rhs).1.vars ++
      (Metta.Minimal.freshenRule counter lhs rhs).2.vars, name ∈ avoid
  then Metta.Minimal.captureAvoidingName avoid counter
  else fun name => name ++ "#" ++ toString counter

theorem ruleRename_injective (avoid : List String) (counter : Nat) (lhs rhs : Metta.Atom) :
    Function.Injective (ruleRename avoid counter lhs rhs) := by
  unfold ruleRename
  split
  · exact Metta.Minimal.captureAvoidingName_injective avoid counter
  · intro left right equal
    have suffixEqual : left ++ ("#" ++ toString counter) =
        right ++ ("#" ++ toString counter) := by
      simpa [String.append_assoc] using equal
    exact (String.append_left_inj ("#" ++ toString counter)).mp suffixEqual

/-- The actual freshener, including its counter, realizes the selected map. -/
theorem runtime_freshening (avoid : List String) (counter : Nat) (lhs rhs : Metta.Atom) :
    Metta.Minimal.freshenRuleAvoiding counter avoid lhs rhs =
      ((Metta.Minimal.renameAllVars (ruleRename avoid counter lhs rhs) lhs,
        Metta.Minimal.renameAllVars (ruleRename avoid counter lhs rhs) rhs), counter + 1) := by
  unfold Metta.Minimal.freshenRuleAvoiding ruleRename
  dsimp only
  split
  · rfl
  · rw [legacy_is_total_renaming]



/-- Read the actual runtime's freshened HE equation back into HE syntax. -/
def freshRule (avoid : List String) (counter : Nat) (lhs rhs : Atom) : Atom × Atom :=
  let native := (Metta.Minimal.freshenRuleAvoiding counter avoid
    (toLeaTTaAtom lhs) (toLeaTTaAtom rhs)).1
  (fromLeaTTaAtom native.1, fromLeaTTaAtom native.2)

theorem freshRule_eq_renamed (avoid : List String) (counter : Nat) (lhs rhs : Atom) :
    freshRule avoid counter lhs rhs =
      (renameTypeVars (ruleRename avoid counter (toLeaTTaAtom lhs) (toLeaTTaAtom rhs)) lhs,
        renameTypeVars (ruleRename avoid counter (toLeaTTaAtom lhs) (toLeaTTaAtom rhs)) rhs) := by
  simp only [freshRule, runtime_freshening]
  rw [← toLeaTTaAtom_renameTypeVars, ← toLeaTTaAtom_renameTypeVars,
    fromLeaTTaAtom_toLeaTTaAtom, fromLeaTTaAtom_toLeaTTaAtom]

/-- Readback preserves the actual native freshened rule exactly. -/
theorem freshRule_translation (avoid : List String) (counter : Nat) (lhs rhs : Atom) :
    (toLeaTTaAtom (freshRule avoid counter lhs rhs).1,
      toLeaTTaAtom (freshRule avoid counter lhs rhs).2) =
      (Metta.Minimal.freshenRuleAvoiding counter avoid (toLeaTTaAtom lhs) (toLeaTTaAtom rhs)).1 := by
  rw [freshRule_eq_renamed, runtime_freshening]
  simp only [toLeaTTaAtom_renameTypeVars]

/-- Neither side of the returned equation contains an avoided variable. -/
theorem freshRule_variables_avoid (avoid : List String) (counter : Nat) (lhs rhs : Atom) :
    ∀ name ∈ (toLeaTTaAtom (freshRule avoid counter lhs rhs).1).vars ++
        (toLeaTTaAtom (freshRule avoid counter lhs rhs).2).vars,
      name ∉ avoid := by
  have nativeFresh := Metta.Minimal.freshenRuleAvoiding_vars_fresh counter avoid
    (toLeaTTaAtom lhs) (toLeaTTaAtom rhs)
  have translation := freshRule_translation avoid counter lhs rhs
  have left := congrArg Prod.fst translation
  have right := congrArg Prod.snd translation
  simp only at left right
  intro name member
  rw [left, right] at member
  exact nativeFresh name member

/-- Any finite avoidance list containing the complete caller scope suffices.
Additional native or retained names do not weaken hygiene. -/
theorem freshRule_alphaVariant_of_covers (live : List Atom) (query lhs rhs : Atom)
    (incoming : Bindings) (counter : Nat) (avoid : List String)
    (covers : ∀ name, QueryVisibleName live query incoming name → name ∈ avoid) :
    AlphaVariantRel live query incoming lhs rhs
      (freshRule avoid counter lhs rhs).1
      (freshRule avoid counter lhs rhs).2 := by
  let rename := ruleRename avoid counter (toLeaTTaAtom lhs) (toLeaTTaAtom rhs)
  rw [freshRule_eq_renamed]
  refine ⟨rename, ruleRename_injective _ _ _ _, rename_alpha _ _, rename_alpha _ _, ?_⟩
  intro name occurs visible
  have renamedOccurs : rename name ∈
      (toLeaTTaAtom (renameTypeVars rename lhs)).vars ++
        (toLeaTTaAtom (renameTypeVars rename rhs)).vars := by
    rw [toLeaTTaAtom_vars_eq_typeVars, toLeaTTaAtom_vars_eq_typeVars,
      Spec.Type.Presentation.ScopeObservation.typeVars_renameTypeVars,
      Spec.Type.Presentation.ScopeObservation.typeVars_renameTypeVars]
    rcases occurs with left | right
    · apply List.mem_append_left
      apply List.mem_map_of_mem
      rw [← toLeaTTaAtom_vars_eq_typeVars]
      exact Spec.Match.ModelTheory.atomOccurs_iff_mem_translated_vars.mp left
    · apply List.mem_append_right
      apply List.mem_map_of_mem
      rw [← toLeaTTaAtom_vars_eq_typeVars]
      exact Spec.Match.ModelTheory.atomOccurs_iff_mem_translated_vars.mp right
  have fresh := Metta.Minimal.freshenRuleAvoiding_vars_fresh counter avoid
    (toLeaTTaAtom lhs) (toLeaTTaAtom rhs)
  rw [runtime_freshening] at fresh
  simp only [toLeaTTaAtom_renameTypeVars] at renamedOccurs
  exact fresh (rename name) renamedOccurs (covers (rename name) visible)

/-- Complete caller scope and the actual freshener construct a hygienic
alpha variant of both equation sides, at arbitrary nesting depth. -/
theorem freshRule_alphaVariant (live : List Atom) (query lhs rhs : Atom)
    (incoming : Bindings) (counter : Nat) :
    AlphaVariantRel live query incoming lhs rhs
      (freshRule (EquationScope.visibleNames live query incoming) counter lhs rhs).1
      (freshRule (EquationScope.visibleNames live query incoming) counter lhs rhs).2 :=
  freshRule_alphaVariant_of_covers live query lhs rhs incoming counter _
    (fun name visible => (EquationScope.mem_visibleNames_iff live query incoming name).mpr visible)



/-- Two legal fresh variants of both sides admit one constructed permutation
fixing the entire caller-visible scope. The finite extension is shared with
the existing private-candidate theory, applied to the pair of equation sides. -/
theorem alphaVariants_public_fixed_permutation
    {live : List Atom} {query lhs rhs leftPattern leftRhs rightPattern rightRhs : Atom}
    {incoming : Bindings}
    (left : AlphaVariantRel live query incoming lhs rhs leftPattern leftRhs)
    (right : AlphaVariantRel live query incoming lhs rhs rightPattern rightRhs) :
    ∃ permutation : Equiv.Perm String,
      (∀ name, QueryVisibleName live query incoming name → permutation name = name) ∧
      rightPattern = renameTypeVars permutation leftPattern ∧
      rightRhs = renameTypeVars permutation leftRhs := by
  let scope := EquationScope.visibleNames live query incoming
  have lift {pattern body : Atom}
      (variant : AlphaVariantRel live query incoming lhs rhs pattern body) :
      Spec.Type.Presentation.Exact.TypeCandidateAlphaVariantRel scope
        (.expression [lhs, rhs]) (.expression [pattern, body]) := by
    obtain ⟨rename, injective, patternRenamed, bodyRenamed, fresh⟩ := variant
    refine ⟨rename, injective, ?_, ?_⟩
    · rw [alphaRename_eq patternRenamed, alphaRename_eq bodyRenamed]
      simp only [renameTypeVars, List.map_cons, List.map_nil]
    · intro name member visible
      have occurrence : Spec.Match.Merge.AtomOccurs lhs name ∨ Spec.Match.Merge.AtomOccurs rhs name := by
        have translated : name ∈ (toLeaTTaAtom lhs).vars ∨ name ∈ (toLeaTTaAtom rhs).vars := by
          simpa only [TypeSubst.typeVars, TypeSubst.typeVarsList, List.mem_append,
            List.not_mem_nil, or_false, toLeaTTaAtom_vars_eq_typeVars] using member
        exact translated.imp Spec.Match.ModelTheory.atomOccurs_iff_mem_translated_vars.mpr
          Spec.Match.ModelTheory.atomOccurs_iff_mem_translated_vars.mpr
      exact fresh name occurrence
        ((EquationScope.mem_visibleNames_iff live query incoming (rename name)).mp visible)
  have siblings : Spec.Type.Presentation.ScopeObservation.PrivateCandidateAlphaRel scope
      (.expression [leftPattern, leftRhs]) (.expression [rightPattern, rightRhs]) :=
    ⟨.expression [lhs, rhs], lift left, lift right⟩
  obtain ⟨permutation, fixed, equation⟩ := siblings.exists_public_fixed_permutation
  refine ⟨permutation, ?_, ?_⟩
  · intro name visible
    exact fixed name ((EquationScope.mem_visibleNames_iff live query incoming name).mpr visible)
  · simpa only [renameTypeVars, List.map_cons, List.map_nil, Atom.expression.injEq,
      List.cons.injEq, and_true] using equation



/-- Reindexing a valuation by a caller-fixed name function leaves its query
observation unchanged, including names at arbitrary finite depth. -/
theorem query_observation_reindex {live : List Atom} {query : Atom} {incoming : Bindings}
    (rename : String → String)
    (fixed : ∀ name, QueryVisibleName live query incoming name → rename name = name)
    (valuation : String → Metta.Atom) :
    applyClassSolution (valuation ∘ rename) (toLeaTTaAtom query) =
      applyClassSolution valuation (toLeaTTaAtom query) := by
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

/-- An independent occurrence transports to any other legal fresh pair of
that same physical raw rule. The complete output theory is preserved under
the constructed permutation's valuation reindexing. It fixes the query,
incoming bindings and every retained live name; private spellings may change.

Normalized incoming assignments are the condition used by the existing
semantic merge-existence theorem, not an assumed evaluator correspondence. -/
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
  obtain ⟨targetOutput, targetMerge, targetSatisfied, targetNonvariable⟩ :=
    Spec.Match.Completeness.exists_specMerge_of_solution targetMatchedSatisfied
      (LeaTTaSpecConformance.specMatch_assignmentsNonVariable targetMatch)
      targetIncoming incomingNonvariable
  have theory (valuation : String → Metta.Atom) :
      HEBindingSatisfied valuation targetOutput ↔
        HEBindingSatisfied (valuation ∘ permutation) output := by
    rw [Spec.Match.SolutionTheory.mergeRel_solution_iff targetMerge,
      Spec.Match.SolutionTheory.matchRel_solution_iff targetMatch,
      source.result.1.he_solutions,
      Spec.Match.SolutionTheory.matchRel_solution_iff source.selected.2,
      incoming_satisfaction_reindex permutation fixed,
      query_observation_reindex permutation fixed,
      patternEquation, applyClassSolution_renameTypeVars]
  refine ⟨permutation, targetMatched, targetOutput, fixed, patternEquation, rhsEquation,
    ⟨source.stored, ⟨targetVariant, targetMatch⟩,
      ⟨targetMerge.logicalMerge ⟨_,
        specTypeBindingSatisfied_of_heBindingSatisfied targetSatisfied⟩, ?_⟩⟩,
      theory, targetNonvariable⟩
  intro valuation satisfied
  unfold HEAtomEquationSatisfied
  rw [rhsEquation, applyClassSolution_renameTypeVars, applyClassSolution_renameTypeVars]
  exact source.result.2 (valuation ∘ permutation) ((theory valuation).mp satisfied)

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
  rw [Spec.Match.ModelTheory.atomOccurs_iff_mem_translated_vars, toLeaTTaAtom_vars_eq_typeVars,
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
    (incomingNonvariable : HEAssignmentsNonVariable incoming)
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
    occurrence_alpha_transport incomingNonvariable source
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
    (raw : Spec.Type.TypesOfRel space subject (getAtomTypes space subject))
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

end Mettapedia.Languages.MeTTa.HE.EquationFreshening

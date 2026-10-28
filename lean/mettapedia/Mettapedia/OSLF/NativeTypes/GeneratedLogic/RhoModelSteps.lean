import Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoModelEquality

/-!
# ρ's runtime model: its rules fire where the plan fires

The model language (`RhoModel.language`) reads ρ's rules as the plan reads them: at a closed process sorted in the
plan's sorting, matching syntactically, substituting by ρ's reflective substitution. Its steps are the plan's
firings, up to the order of a bag's members:

- **A firing of the plan at the root of a bag is a COMM of the model** (`rootFiring_step`): an input and an output on
  one channel, the residue in order, and the reflective substitution, which on well-sorted bodies is ρ's semantic
  substitution.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoModel

open Mettapedia.OSLF.MeTTaIL Syntax Match MatchSpec
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.DerivedContexts (OneHoleContext)
open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep (StepAt PremisesAt PremiseAt)
open Mettapedia.OSLF.MeTTaIL.Complete.RhoPresented (rules_zipIdx rule_at bare_rule)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.ReflectionExtension (rhoReflectionProfile)
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution (applyBindingsForRuleUsing)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep (rhoBasePremises rho_input_wellSorted_inv
  rho_output_wellSorted_inv)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalStepperCompleteness (commBindingsAt apply_commBindingsAt
  rho_parallel_wellSorted_inv)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalTyping (procListWellSorted_iff_forall_mem)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus (semanticCommSubst)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep (rhoParCong_no_substitutionPresentation)
open Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence GeneralTypedSites

/-- One step of the model's rules, at a bounded depth of contexts. -/
abbrev Step (fuel : ℕ) : Pattern → Pattern → Prop := StepAt interpretation rhoBasePremises language fuel

/-! ## COMM matched syntactically -/

theorem comm_rule_mem : rhoCommRewrite ∈ language.rewrites := by simp [rewrites_eq]

theorem parCong_rule_mem : rhoParCongRewrite ∈ language.rewrites := by simp [rewrites_eq]

/-- **COMM matches an input and an output on one channel, at any two positions.** -/
theorem comm_matches {elements : List Pattern} {inputIndex outputIndex : ℕ}
    (inputBound : inputIndex < elements.length) (outputBound : outputIndex < (elements.eraseIdx inputIndex).length)
    {channel body payload : Pattern} {binder : Option String}
    (inputEq : elements[inputIndex] = .apply "PInput" [channel, .lambda binder body])
    (outputEq : (elements.eraseIdx inputIndex)[outputIndex] = .apply "POutput" [channel, payload]) :
    commBindingsAt elements inputIndex outputIndex channel body payload ∈
      matchPattern rhoCommRewrite.left (.collection .hashBag elements none) := by
  rw [matchPattern_iff_matchRel]
  apply MatchRel.collection (by decide)
  refine MatchBagRel.cons (hb := [("p", body), ("n", channel)])
    (restB := [("rest", .collection .hashBag ((elements.eraseIdx inputIndex).eraseIdx outputIndex) none),
      ("q", payload), ("n", channel)]) inputIndex inputBound ?_ ?_ ?_
  · rw [inputEq]
    exact .apply (.cons .fvar (.cons (.lambda .fvar) .nil rfl) rfl) rfl
  · refine MatchBagRel.cons (hb := [("q", payload), ("n", channel)])
      (restB := [("rest", .collection .hashBag ((elements.eraseIdx inputIndex).eraseIdx outputIndex) none)])
      outputIndex outputBound ?_ .nilRest ?_
    · rw [outputEq]
      exact .apply (.cons .fvar (.cons .fvar .nil rfl) rfl) rfl
    · simp [mergeBindings]
  · simp [commBindingsAt, mergeBindings]


/-! ## A root firing is a COMM -/

theorem sorted_of_plan {term : Pattern}
    (typed : OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
      (GeneralPlanEnvironment.environment plan).free [] proc term) : sorted term = true :=
  sorted_iff.mpr ((GeneralPlanEnvironment.typing_iff plan [] proc term).mp typed)

theorem plan_of_sorted {term : Pattern} (typed : sorted term = true) :
    OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
      (GeneralPlanEnvironment.environment plan).free [] proc term :=
  (GeneralPlanEnvironment.typing_iff plan [] proc term).mpr (sorted_iff.mp typed)

/-- **A firing of the plan at the root of a sealed bag is a COMM of the model**, with the same target. -/
theorem rootFiring_step {source : Pattern} {index : ℕ} {trace : List GeneralScopedMatchMachine.BagChoice}
    {captured completed : ScopedRuleMatching.Assignment} {history : List GeneralPremise.Event} {target : Pattern}
    (safe : sealed source = true)
    (fired : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] proc source index trace captured
      completed history target) :
    Step 1 source target := by
  cases fired with
  | @fire _ _ _ _ _ rule spec _ _ _ _ ruleFound specFound _ sourceSorted matched _ premises reduct _ =>
    have zero : index = 0 := by
      rw [Complete.RhoPresented.rewrites_eq] at ruleFound
      cases index with
      | zero => rfl
      | succ => simp at ruleFound
    subst zero
    obtain ⟨_, rfl, rfl⟩ := rule_at (declaration := GeneralRho.declaration) (by rw [rules_zipIdx]; exact .head _)
      ruleFound specFound
    have typed := Complete.RhoReference.procWellSorted_of_sorted sourceSorted
    have noPremises : GeneralRho.comm.premises = [] := rfl
    rw [noPremises] at premises
    cases premises
    obtain ⟨elements, inputIndex, outputIndex, channel, display, body, payload, rfl, inputAt, outputAt,
      _, capturedEq, _, _, _, residueSafe⟩ := GeneralRho.DepthOne.traced_comm_inv matched
    rw [capturedEq] at reduct
    obtain ⟨_, elementsTyped⟩ := rho_parallel_wellSorted_inv typed
    have inputTyped := procListWellSorted_iff_forall_mem.mp elementsTyped _ (List.mem_of_getElem? inputAt)
    obtain ⟨rfl, _, bodyTyped⟩ := rho_input_wellSorted_inv inputTyped
    have outputTyped := procListWellSorted_iff_forall_mem.mp elementsTyped _
      (List.mem_of_mem_eraseIdx (List.mem_of_getElem? outputAt))
    obtain ⟨_, payloadTyped⟩ := rho_output_wellSorted_inv outputTyped
    have semantic := GeneralRho.reflective_reduct_semantic (channel := channel) bodyTyped payloadTyped residueSafe
    have localTarget := Option.some.inj (reduct.symm.trans semantic)
    subst localTarget
    obtain ⟨inputBound, inputEq⟩ := List.getElem?_eq_some_iff.mp inputAt
    obtain ⟨outputBound, outputEq⟩ := List.getElem?_eq_some_iff.mp outputAt
    refine StepAt.rule (rule := rhoCommRewrite)
      (initialBindings := commBindingsAt elements inputIndex outputIndex channel body payload)
      (finalBindings := commBindingsAt elements inputIndex outputIndex channel body payload)
      comm_rule_mem ?_ (PremisesAt.nil _) ?_
    · show _ ∈ (if carrier (.collection .hashBag elements none) then _ else [])
      rw [if_pos (by simp [carrier, sorted_of_plan sourceSorted, safe])]
      exact comm_matches inputBound outputBound inputEq outputEq
    · exact apply_commBindingsAt bodyTyped payloadTyped elements inputIndex outputIndex channel


/-! ## A firing inside a bag is a congruence -/

/-- A member of a sorted bag is sorted. -/
theorem sorted_member {elements : List Pattern} {member : Pattern}
    (typed : sorted (.collection .hashBag elements none) = true) (found : member ∈ elements) : sorted member = true := by
  have rho := Complete.RhoReference.procWellSorted_of_sorted (plan_of_sorted typed)
  obtain ⟨_, elementsTyped⟩ := rho_parallel_wellSorted_inv rho
  have memberTyped := procListWellSorted_iff_forall_mem.mp elementsTyped _ found
  exact sorted_of_plan ((GeneralPlanEnvironment.typing_iff plan [] proc _).mpr
    (GeneralRho.derived_process_open memberTyped))

/-- A member of a sealed bag is sealed. -/
theorem sealed_member {elements : List Pattern} {member : Pattern}
    (safe : sealed (.collection .hashBag elements none) = true) (found : member ∈ elements) : sealed member = true := by
  simp only [sealed, ScopedPattern.binderSafeAt] at safe ⊢
  induction elements with
  | nil => cases found
  | cons head tail ih =>
    simp only [ScopedPattern.binderSafeListAt, Bool.and_eq_true] at safe
    rcases List.mem_cons.mp found with rfl | found
    · exact safe.1
    · exact ih safe.2 found

/-- A member of a bag of ρ's carrier is in it. -/
theorem carrier_member {elements : List Pattern} {member : Pattern}
    (admitted : carrier (.collection .hashBag elements none) = true) (found : member ∈ elements) :
    carrier member = true := by
  simp only [carrier, Bool.and_eq_true] at admitted ⊢
  exact ⟨sorted_member admitted.1 found, sealed_member admitted.2 found⟩

/-- **ParCong steps a member of a bag**, writing its step in front. -/
theorem parCong_step {elements : List Pattern} {index : ℕ} (bound : index < elements.length) {fuel : ℕ}
    {target : Pattern} (typed : carrier (.collection .hashBag elements none) = true)
    (step : Step fuel elements[index] target) :
    Step (fuel + 1) (.collection .hashBag elements none) (.collection .hashBag (target :: elements.eraseIdx index) none) := by
  refine StepAt.rule (rule := rhoParCongRewrite)
    (initialBindings := [("rest", .collection .hashBag (elements.eraseIdx index) none), ("S", elements[index])])
    (finalBindings := [("T", target), ("rest", .collection .hashBag (elements.eraseIdx index) none),
      ("S", elements[index])])
    parCong_rule_mem ?_ ?_ ?_
  · show _ ∈ (if carrier (.collection .hashBag elements none) then _ else [])
    rw [if_pos typed, matchPattern_iff_matchRel]
    exact .collection (by decide) (.cons index bound .fvar .nilRest rfl)
  · refine PremisesAt.cons (PremiseAt.congruence (candidate := target) (premiseBindings := [("T", target)]) ?_ ?_ rfl)
      (PremisesAt.nil _)
    · simpa [applyBindings] using step
    · simp [matchPattern]
  · show applyBindingsForRuleUsing rhoReflectionProfile rhoParCongRewrite _ = _
    rw [applyBindingsForRuleUsing, rhoParCong_no_substitutionPresentation, applyRuleBindings,
      applyBindingsScoped_zero_of_binderFree _ _ _ (by decide)]
    simp [rhoParCongRewrite, applyBindings]

/-- **Every firing of the plan is a step of the model**, up to the order of a bag's members: a firing at the root is a
COMM, one inside a member of a bag is ParCong around the member's step. -/
theorem licensed_step {bound : List TypeExpr} {expected : TypeExpr} {source : Pattern} {site : SiteData}
    (licensed : Licensed (GeneralPlanEnvironment.environment plan).language plan.snapshot.free
      plan.permissions.sites bound expected source site) :
    bound = [] → expected = proc → carrier source = true →
      ∀ {index : ℕ} {trace : List GeneralScopedMatchMachine.BagChoice}
        {captured completed : ScopedRuleMatching.Assignment} {history : List GeneralPremise.Event} {localTarget : Pattern},
        GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) site.focusBound site.focusType site.focus index
          trace captured completed history localTarget →
        ∃ target fuel, Step fuel source target ∧ Relation.EqvGen Move target (site.context.fill localTarget) := by
  induction licensed with
  | here _ _ _ =>
    intro closed procType admitted _ _ _ _ _ _ fired
    subst closed procType
    exact ⟨_, 1, rootFiring_step (Bool.and_eq_true_iff.mp admitted).2 fired, .refl _⟩
  | application _ _ _ _ _ _ _ permitted _ _ =>
    intro _ _ _
    change GeneralRho.Standard.sites.allConstructorArguments = true ∨ _ ∈ GeneralRho.Standard.sites.constructorArguments
      at permitted
    simp [GeneralRho.Standard.sites] at permitted
  | lambda enabled _ _ =>
    intro _ _ _
    change GeneralRho.Standard.sites.underLambda = true at enabled
    simp [GeneralRho.Standard.sites] at enabled
  | multiLambda enabled _ _ =>
    intro _ _ _
    change GeneralRho.Standard.sites.underMultiLambda = true at enabled
    simp [GeneralRho.Standard.sites] at enabled
  | directCollection _ _ _ _ _ _ =>
    intro _ procType
    cases procType
  | @authoredCollection bound rule declarationIndex parameterName kind elements index element elementType inner
      declared shape permitted elementsTyped objects selected _ ih =>
    intro closed _ typed _ _ _ _ _ _ fired
    obtain ⟨_, rfl, rfl⟩ := bare_rule (List.fst_mem_of_mem_zipIdx declared)
      ((GrammarRule.bareParams_cons_iff _ _ _).mp shape).2
    obtain ⟨bound', elementEq⟩ := List.getElem?_eq_some_iff.mp selected
    subst elementEq
    obtain ⟨target, fuel, step, related⟩ := ih closed rfl (carrier_member typed (List.getElem_mem bound')) fired
    refine ⟨_, fuel + 1, parCong_step bound' typed step, ?_⟩
    have inside := equiv_fill (.collection .hashBag [] .hole (elements.eraseIdx index) none) related
    simp only [OneHoleContext.fill, List.nil_append] at inside
    refine .trans _ _ _ inside (bag_perm ?_)
    rw [eraseIdx_eq index]
    exact List.perm_middle.symm

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoModel

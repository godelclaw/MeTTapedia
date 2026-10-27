import Mettapedia.OSLF.MeTTaIL.ReferenceStepExecution
import Mathlib.Data.List.Sections

/-!
# Executing the reference relation through a presentation

Under a presented internal boundary policy (`InternalBoundaryPolicy.presented present`), a premise steps
a listed presentation of its child, its target is matched against a listed presentation of the step's
result, and a relation's answers are matched at listed presentations of their values. Freshness and
quantified premises read their captures as they are.

`presentedStepsAt present fuel source` lists the steps of `source` under that policy, with their
witnesses, every derivation at most `fuel` rule layers deep, as `stepsAt` does for the literal policy.

- **Sound**: every listed pair is a valid witness and its target (`stepValid_of_mem_presentedStepsAt`).
- **Complete**: every valid witness is listed once the fuel reaches its depth
  (`mem_presentedStepsAt_of_stepValid`), and every one is listed when the fuel is enough
  (`presentedEnough`, `mem_presentedStepsAt_of_enough`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.ReferenceStep

open Syntax Match Engine ContextualStep ReflectiveCanonical ReflectiveSubstitution

variable (relEnv : RelationEnv) (language : LanguageDef) (present : Pattern → List Pattern)

/-! ## The executor -/

/-- The bindings a freshness or relation premise produces through a presentation. -/
def presentedBaseStep (bindings : Bindings) : Premise → List Bindings
  | .relationQuery relation arguments => presentedQueryStep present relEnv language bindings relation arguments
  | premise => premiseStepWithEnv relEnv language bindings premise

/-- Evaluate a premise through a presentation, with a given recursive stepper for presented children. -/
def presentedPremiseAt (recursive : Pattern → List (Witness × Pattern)) (sites : Pattern) :
    Bindings → Premise → List (Witness × Bindings)
  | bindings, .forAll collection parameter body =>
      match bindings.lookup collection with
      | some (.collection _ elements none) =>
          (elements.foldr
            (fun element rest =>
              (presentedPremiseAt recursive sites (bindParameter bindings parameter element) body).flatMap
                fun entry => rest.map (entry.1 :: ·))
            [[]]).map fun bodies => (.forAll bodies, bindings)
      | _ => []
  | bindings, premise =>
      if isBase premise = true then
        (presentedBaseStep relEnv language present bindings premise).map fun result => (.base result, result)
      else
        match stepEndpoints premise with
        | none => []
        | some (source, target) =>
            (present (applyBindingsScoped sites bindings (stepDepth sites premise) source)).flatMap fun redex =>
              (recursive redex).flatMap fun entry =>
                (present entry.2).flatMap fun candidate =>
                  (matchPattern target candidate).filterMap fun matched =>
                    (mergeBindings bindings matched).map fun result =>
                      (.premiseStep entry.1 candidate matched result, result)

/-- Evaluate a list of premises through a presentation. -/
def presentedPremisesAt (recursive : Pattern → List (Witness × Pattern)) (sites : Pattern) :
    Bindings → List Premise → List (List Witness × Bindings)
  | bindings, [] => [([], bindings)]
  | bindings, premise :: premises =>
      (presentedPremiseAt relEnv language present recursive sites bindings premise).flatMap fun entry =>
        (presentedPremisesAt recursive sites entry.2 premises).map fun rest => (entry.1 :: rest.1, rest.2)

/-- **The steps of a term through a presentation**, with their witnesses, derivations at most `fuel` rule
layers deep. -/
def presentedStepsAt : ℕ → Pattern → List (Witness × Pattern)
  | 0, _ => []
  | fuel + 1, source =>
      (List.range language.rewrites.length).flatMap fun index =>
        match language.rewrites[index]? with
        | none => []
        | some rule =>
            (matchPatternForRule language rule source).flatMap fun initial =>
              (presentedPremisesAt relEnv language present (presentedStepsAt fuel) (captureSites rule) initial
                rule.premises).map fun entry =>
                  (.rule index initial entry.1, applyBindingsScoped (captureSites rule) entry.2 0 rule.right)

/-! ## Soundness -/

variable {relEnv language present}

theorem presentedPremiseValid_of_base {sites : Pattern} {bindings result : Bindings} {premise : Premise}
    (base : isBase premise = true) (member : result ∈ presentedBaseStep relEnv language present bindings premise) :
    PremiseValid relEnv language sites bindings premise (.base result) result (.presented present) := by
  cases premise with
  | freshness condition => exact .presentedFreshness member
  | relationQuery relation arguments => exact .presentedQuery member
  | _ => simp [isBase] at base

/-- **Every listed premise witness is valid**, when the recursive stepper lists only valid steps. -/
theorem presentedPremiseValid_of_mem {recursive : Pattern → List (Witness × Pattern)}
    (recursiveSound : ∀ {source witness target}, (witness, target) ∈ recursive source →
      StepValid relEnv language source witness target (.presented present)) :
    ∀ (premise : Premise) {sites : Pattern} {bindings result : Bindings} {witness : Witness},
      (witness, result) ∈ presentedPremiseAt relEnv language present recursive sites bindings premise →
        PremiseValid relEnv language sites bindings premise witness result (.presented present)
  | .forAll collection parameter body, sites, bindings, result, witness, member => by
    simp only [presentedPremiseAt] at member
    split at member
    · rename_i kind elements found
      obtain ⟨bodies, bodiesMember, pairEq⟩ := List.mem_map.mp member
      simp only [Prod.mk.injEq] at pairEq
      obtain ⟨rfl, rfl⟩ := pairEq
      have related := (mem_foldr_choices_iff _ elements bodies).mp bodiesMember
      refine .presentedForAll found ?_
      clear bodiesMember member found
      induction related with
      | nil => exact .presentedNil
      | cons head _ tailValid =>
        obtain ⟨other, chosen⟩ := head
        exact .presentedCons (presentedPremiseValid_of_mem recursiveSound body chosen) tailValid
    · simp at member
  | .freshness condition, sites, bindings, result, witness, member => by
    simp only [presentedPremiseAt, isBase, ↓reduceIte, List.mem_map, Prod.mk.injEq] at member
    obtain ⟨produced, producedMember, rfl, rfl⟩ := member
    exact presentedPremiseValid_of_base rfl producedMember
  | .relationQuery relation arguments, sites, bindings, result, witness, member => by
    simp only [presentedPremiseAt, isBase, ↓reduceIte, List.mem_map, Prod.mk.injEq] at member
    obtain ⟨produced, producedMember, rfl, rfl⟩ := member
    exact presentedPremiseValid_of_base rfl producedMember
  | .congruence source target, sites, bindings, result, witness, member => by
    simp only [presentedPremiseAt, isBase, Bool.false_eq_true, ↓reduceIte, stepEndpoints, List.mem_flatMap,
      List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq] at member
    obtain ⟨redex, redexMember, ⟨step, contractum⟩, stepMember, candidate, candidateMember, matched, matchedMember,
      merged, mergedEq, rfl, rfl⟩ := member
    exact .presentedStep rfl redexMember (recursiveSound stepMember) candidateMember matchedMember mergedEq
  | .scopedStep premise, sites, bindings, result, witness, member => by
    simp only [presentedPremiseAt, isBase, Bool.false_eq_true, ↓reduceIte, stepEndpoints, List.mem_flatMap,
      List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq] at member
    obtain ⟨redex, redexMember, ⟨step, contractum⟩, stepMember, candidate, candidateMember, matched, matchedMember,
      merged, mergedEq, rfl, rfl⟩ := member
    exact .presentedStep rfl redexMember (recursiveSound stepMember) candidateMember matchedMember mergedEq

theorem presentedPremisesValid_of_mem {recursive : Pattern → List (Witness × Pattern)}
    (recursiveSound : ∀ {source witness target}, (witness, target) ∈ recursive source →
      StepValid relEnv language source witness target (.presented present)) {sites : Pattern} :
    ∀ {premises : List Premise} {bindings final : Bindings} {witnesses : List Witness},
      (witnesses, final) ∈ presentedPremisesAt relEnv language present recursive sites bindings premises →
        PremisesValid relEnv language sites bindings premises witnesses final (.presented present)
  | [], bindings, final, witnesses, member => by
    simp only [presentedPremisesAt, List.mem_singleton, Prod.mk.injEq] at member
    obtain ⟨rfl, rfl⟩ := member
    exact .presentedNil _
  | premise :: premises, bindings, final, witnesses, member => by
    simp only [presentedPremisesAt, List.mem_flatMap, List.mem_map, Prod.mk.injEq] at member
    obtain ⟨⟨witness, middle⟩, headMember, ⟨rest, restFinal⟩, restMember, rfl, rfl⟩ := member
    exact .presentedCons (presentedPremiseValid_of_mem recursiveSound premise headMember)
      (presentedPremisesValid_of_mem recursiveSound restMember)

/-- **Sound**: every listed step comes with a valid witness. -/
theorem stepValid_of_mem_presentedStepsAt : ∀ {fuel : ℕ} {source target : Pattern} {witness : Witness},
    (witness, target) ∈ presentedStepsAt relEnv language present fuel source →
      StepValid relEnv language source witness target (.presented present)
  | 0, _, _, _, member => by simp [presentedStepsAt] at member
  | fuel + 1, source, target, witness, member => by
    simp only [presentedStepsAt, List.mem_flatMap, List.mem_range] at member
    obtain ⟨index, _, rest⟩ := member
    split at rest
    · simp at rest
    · rename_i rule found
      simp only [List.mem_flatMap, List.mem_map, Prod.mk.injEq] at rest
      obtain ⟨initial, matched, ⟨witnesses, final⟩, premisesMember, rfl, rfl⟩ := rest
      exact .presentedRule found matched
        (presentedPremisesValid_of_mem (stepValid_of_mem_presentedStepsAt (fuel := fuel)) premisesMember)

/-! ## Completeness -/

theorem presentedForall₂_of_forAllValid {sites : Pattern} {bindings : Bindings} {parameter : String}
    {body : Premise} {bound : ℕ} {choices : Pattern → List (Witness × Bindings)}
    (listed : ∀ {element : Pattern} {witness : Witness} {result : Bindings},
      PremiseValid relEnv language sites (bindParameter bindings parameter element) body witness result
          (.presented present) →
        witness.depth ≤ bound → (witness, result) ∈ choices element) :
    ∀ {elements : List Pattern} {bodies : List Witness},
      ForAllValid relEnv language sites bindings parameter body elements bodies (.presented present) →
      (∀ witness ∈ bodies, witness.depth ≤ bound) →
        List.Forall₂ (fun element choice => ∃ other, (choice, other) ∈ choices element) elements bodies
  | [], [], _, _ => .nil
  | [], _ :: _, valid, _ => by cases valid
  | _ :: _, [], valid, _ => by cases valid
  | element :: elements, witness :: witnesses, valid, bounded => by
    cases valid with
    | presentedCons head tail =>
      exact .cons ⟨_, listed head (bounded witness List.mem_cons_self)⟩
        (presentedForall₂_of_forAllValid listed tail (fun other member => bounded other (List.mem_cons_of_mem _ member)))

/-- **Every valid premise witness is listed**, when the recursive stepper lists every valid step no deeper
than the witness. -/
theorem mem_presentedPremiseAt_of_valid {recursive : Pattern → List (Witness × Pattern)} {bound : ℕ}
    (recursiveComplete : ∀ {source witness target}, StepValid relEnv language source witness target (.presented present) →
      witness.depth ≤ bound → (witness, target) ∈ recursive source) :
    ∀ (premise : Premise) {sites : Pattern} {bindings result : Bindings} {witness : Witness},
      PremiseValid relEnv language sites bindings premise witness result (.presented present) → witness.depth ≤ bound →
        (witness, result) ∈ presentedPremiseAt relEnv language present recursive sites bindings premise
  | .forAll collection parameter body, sites, bindings, result, witness, valid, bounded => by
    cases valid with
    | presentedStep endpoints _ _ _ _ _ => simp [stepEndpoints] at endpoints
    | @presentedForAll _ _ _ _ _ _ kind elements bodies found bodiesValid =>
      simp only [presentedPremiseAt, found]
      refine List.mem_map.mpr ⟨bodies, ?_, rfl⟩
      apply (mem_foldr_choices_iff _ elements bodies).mpr
      exact presentedForall₂_of_forAllValid
        (fun bodyValid bodyBounded => mem_presentedPremiseAt_of_valid recursiveComplete body bodyValid bodyBounded)
        bodiesValid (Witness.depthList_le_iff.mp bounded)
  | .freshness condition, sites, bindings, result, witness, valid, _ => by
    cases valid with
    | presentedFreshness member =>
      simp only [presentedPremiseAt, isBase, ↓reduceIte, List.mem_map, Prod.mk.injEq]
      exact ⟨_, member, rfl, rfl⟩
    | presentedStep endpoints _ _ _ _ _ => simp [stepEndpoints] at endpoints
  | .relationQuery relation arguments, sites, bindings, result, witness, valid, _ => by
    cases valid with
    | presentedQuery member =>
      simp only [presentedPremiseAt, isBase, ↓reduceIte, List.mem_map, Prod.mk.injEq]
      exact ⟨_, member, rfl, rfl⟩
    | presentedStep endpoints _ _ _ _ _ => simp [stepEndpoints] at endpoints
  | .congruence source target, sites, bindings, result, witness, valid, bounded => by
    cases valid with
    | presentedStep endpoints redexMember stepped candidateMember matchedMember merged =>
      simp only [stepEndpoints, Option.some.injEq, Prod.mk.injEq] at endpoints
      obtain ⟨rfl, rfl⟩ := endpoints
      simp only [presentedPremiseAt, isBase, Bool.false_eq_true, ↓reduceIte, stepEndpoints, List.mem_flatMap,
        List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq]
      exact ⟨_, redexMember, _, recursiveComplete stepped bounded, _, candidateMember, _, matchedMember, _, merged, rfl,
        rfl⟩
  | .scopedStep premise, sites, bindings, result, witness, valid, bounded => by
    cases valid with
    | presentedStep endpoints redexMember stepped candidateMember matchedMember merged =>
      simp only [stepEndpoints, Option.some.injEq, Prod.mk.injEq] at endpoints
      obtain ⟨rfl, rfl⟩ := endpoints
      simp only [presentedPremiseAt, isBase, Bool.false_eq_true, ↓reduceIte, stepEndpoints, List.mem_flatMap,
        List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq]
      exact ⟨_, redexMember, _, recursiveComplete stepped bounded, _, candidateMember, _, matchedMember, _, merged, rfl,
        rfl⟩

theorem mem_presentedPremisesAt_of_valid {recursive : Pattern → List (Witness × Pattern)} {bound : ℕ}
    (recursiveComplete : ∀ {source witness target}, StepValid relEnv language source witness target (.presented present) →
      witness.depth ≤ bound → (witness, target) ∈ recursive source) {sites : Pattern} :
    ∀ {premises : List Premise} {bindings final : Bindings} {witnesses : List Witness},
      PremisesValid relEnv language sites bindings premises witnesses final (.presented present) →
      (∀ witness ∈ witnesses, witness.depth ≤ bound) →
        (witnesses, final) ∈ presentedPremisesAt relEnv language present recursive sites bindings premises
  | [], _, _, _, valid, _ => by
    cases valid
    simp [presentedPremisesAt]
  | premise :: premises, _, _, _, valid, bounded => by
    cases valid with
    | @presentedCons _ _ _ _ _ _ _ witness witnesses first rest =>
      simp only [presentedPremisesAt, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
      exact ⟨_, mem_presentedPremiseAt_of_valid recursiveComplete premise first (bounded witness List.mem_cons_self),
        _, mem_presentedPremisesAt_of_valid recursiveComplete rest
          (fun other member => bounded other (List.mem_cons_of_mem _ member)), rfl, rfl⟩

/-- **Complete**: a valid witness is listed once the fuel reaches its depth. -/
theorem mem_presentedStepsAt_of_stepValid : ∀ {fuel : ℕ} {source target : Pattern} {witness : Witness},
    StepValid relEnv language source witness target (.presented present) → witness.depth ≤ fuel →
      (witness, target) ∈ presentedStepsAt relEnv language present fuel source
  | fuel, source, target, witness, valid, bounded => by
    cases valid with
    | @presentedRule _ _ index rule initial final witnesses found matched premises =>
      simp only [Witness.depth] at bounded
      obtain ⟨smaller, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by omega⟩
      have premisesBounded : ∀ witness ∈ witnesses, witness.depth ≤ smaller :=
        Witness.depthList_le_iff.mp (by omega)
      have indexBound : index < language.rewrites.length := by
        by_contra outside
        rw [List.getElem?_eq_none (by omega)] at found
        cases found
      simp only [presentedStepsAt, List.mem_flatMap, List.mem_range]
      refine ⟨index, indexBound, ?_⟩
      simp only [found, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
      exact ⟨initial, matched, (witnesses, final),
        mem_presentedPremisesAt_of_valid (fun valid bounded => mem_presentedStepsAt_of_stepValid valid bounded)
          premises premisesBounded, rfl, rfl⟩

/-! ## Complete listings -/

variable (relEnv language present)

/-- Whether a premise's presented step source is completely listed by `check`. -/
def presentedPremiseEnough (check : Pattern → Bool) (sites : Pattern) : Bindings → Premise → Bool
  | bindings, .forAll collection parameter body =>
      match bindings.lookup collection with
      | some (.collection _ elements none) =>
          elements.all fun element =>
            presentedPremiseEnough check sites (bindParameter bindings parameter element) body
      | _ => true
  | bindings, premise =>
      if isBase premise = true then true
      else
        match stepEndpoints premise with
        | none => true
        | some (source, _) =>
            (present (applyBindingsScoped sites bindings (stepDepth sites premise) source)).all check

/-- Whether every premise's presented step source is completely listed, under every bindings the listing
produces for the premises before it. -/
def presentedPremisesEnough (recursive : Pattern → List (Witness × Pattern)) (check : Pattern → Bool)
    (sites : Pattern) : Bindings → List Premise → Bool
  | _, [] => true
  | bindings, premise :: premises =>
      presentedPremiseEnough present check sites bindings premise &&
        (presentedPremiseAt relEnv language present recursive sites bindings premise).all fun entry =>
          presentedPremisesEnough recursive check sites entry.2 premises

/-- **The fuel is enough for a term through a presentation**: every derivation of a step from it fits in the
fuel. -/
def presentedEnough : ℕ → Pattern → Bool
  | 0, source => language.rewrites.all fun rule => (matchPatternForRule language rule source).isEmpty
  | fuel + 1, source => language.rewrites.all fun rule =>
      (matchPatternForRule language rule source).all fun initial =>
        presentedPremisesEnough relEnv language present (presentedStepsAt relEnv language present fuel)
          (presentedEnough fuel) (captureSites rule) initial rule.premises

variable {relEnv language present}

theorem presentedDepthList_le_of_forAllValid {check : Pattern → Bool} {bound : ℕ} {sites : Pattern}
    {bindings : Bindings} {parameter : String} {body : Premise}
    (bodyBound : ∀ {bindings' : Bindings} {result : Bindings} {witness : Witness},
      presentedPremiseEnough present check sites bindings' body = true →
        PremiseValid relEnv language sites bindings' body witness result (.presented present) → witness.depth ≤ bound) :
    ∀ {elements : List Pattern} {bodies : List Witness},
      (∀ element ∈ elements,
        presentedPremiseEnough present check sites (bindParameter bindings parameter element) body = true) →
        ForAllValid relEnv language sites bindings parameter body elements bodies (.presented present) →
          ∀ witness ∈ bodies, witness.depth ≤ bound
  | [], [], _, _ => by simp
  | [], _ :: _, _, valid => by cases valid
  | _ :: _, [], _, valid => by cases valid
  | element :: elements, witness :: witnesses, checked, valid => by
    cases valid with
    | presentedCons head tail =>
      intro other member
      rcases List.mem_cons.mp member with rfl | member
      · exact bodyBound (checked element List.mem_cons_self) head
      · exact presentedDepthList_le_of_forAllValid bodyBound
          (fun element' inside => checked element' (List.mem_cons_of_mem _ inside)) tail other member

theorem presentedDepth_le_of_premiseEnough {check : Pattern → Bool} {bound : ℕ}
    (checkBound : ∀ {source witness target}, check source = true →
      StepValid relEnv language source witness target (.presented present) → witness.depth ≤ bound) :
    ∀ (premise : Premise) {sites : Pattern} {bindings result : Bindings} {witness : Witness},
      presentedPremiseEnough present check sites bindings premise = true →
        PremiseValid relEnv language sites bindings premise witness result (.presented present) → witness.depth ≤ bound
  | .forAll collection parameter body, sites, bindings, result, witness, checked, valid => by
    cases valid with
    | presentedStep endpoints _ _ _ _ _ => simp [stepEndpoints] at endpoints
    | @presentedForAll _ _ _ _ _ _ kind elements bodies found bodiesValid =>
      simp only [presentedPremiseEnough, found, List.all_eq_true] at checked
      simp only [Witness.depth]
      exact Witness.depthList_le_iff.mpr (presentedDepthList_le_of_forAllValid
        (fun bodyChecked bodyValid => presentedDepth_le_of_premiseEnough checkBound body bodyChecked bodyValid)
        checked bodiesValid)
  | .freshness _, _, _, _, _, _, valid => by
    cases valid with
    | presentedFreshness _ => simp [Witness.depth]
    | presentedStep endpoints _ _ _ _ _ => simp [stepEndpoints] at endpoints
  | .relationQuery _ _, _, _, _, _, _, valid => by
    cases valid with
    | presentedQuery _ => simp [Witness.depth]
    | presentedStep endpoints _ _ _ _ _ => simp [stepEndpoints] at endpoints
  | .congruence source target, sites, bindings, result, witness, checked, valid => by
    cases valid with
    | presentedStep endpoints redexMember stepped _ _ _ =>
      simp only [stepEndpoints, Option.some.injEq, Prod.mk.injEq] at endpoints
      obtain ⟨rfl, rfl⟩ := endpoints
      simp only [presentedPremiseEnough, isBase, Bool.false_eq_true, ↓reduceIte, stepEndpoints, List.all_eq_true] at checked
      simp only [Witness.depth]
      exact checkBound (checked _ redexMember) stepped
  | .scopedStep premise, sites, bindings, result, witness, checked, valid => by
    cases valid with
    | presentedStep endpoints redexMember stepped _ _ _ =>
      simp only [stepEndpoints, Option.some.injEq, Prod.mk.injEq] at endpoints
      obtain ⟨rfl, rfl⟩ := endpoints
      simp only [presentedPremiseEnough, isBase, Bool.false_eq_true, ↓reduceIte, stepEndpoints, List.all_eq_true] at checked
      simp only [Witness.depth]
      exact checkBound (checked _ redexMember) stepped

theorem presentedDepth_le_of_premisesEnough {recursive : Pattern → List (Witness × Pattern)}
    {check : Pattern → Bool} {bound : ℕ}
    (recursiveComplete : ∀ {source witness target}, StepValid relEnv language source witness target (.presented present) →
      witness.depth ≤ bound → (witness, target) ∈ recursive source)
    (checkBound : ∀ {source witness target}, check source = true →
      StepValid relEnv language source witness target (.presented present) → witness.depth ≤ bound) {sites : Pattern} :
    ∀ {premises : List Premise} {bindings final : Bindings} {witnesses : List Witness},
      presentedPremisesEnough relEnv language present recursive check sites bindings premises = true →
        PremisesValid relEnv language sites bindings premises witnesses final (.presented present) →
          ∀ witness ∈ witnesses, witness.depth ≤ bound
  | [], _, _, _, _, valid => by
    cases valid
    simp
  | premise :: premises, bindings, final, _, checked, valid => by
    cases valid with
    | @presentedCons _ _ _ middle _ _ _ witness witnesses first rest =>
      simp only [presentedPremisesEnough, Bool.and_eq_true, List.all_eq_true] at checked
      have firstBound := presentedDepth_le_of_premiseEnough checkBound premise checked.1 first
      have listed := mem_presentedPremiseAt_of_valid recursiveComplete premise first firstBound
      have restBound := presentedDepth_le_of_premisesEnough recursiveComplete checkBound (checked.2 _ listed) rest
      intro other member
      rcases List.mem_cons.mp member with rfl | member
      · exact firstBound
      · exact restBound other member

/-- **When the fuel is enough, no derivation is cut off.** -/
theorem presentedDepth_le_of_enough : ∀ {fuel : ℕ} {source target : Pattern} {witness : Witness},
    presentedEnough relEnv language present fuel source = true →
      StepValid relEnv language source witness target (.presented present) → witness.depth ≤ fuel
  | 0, source, target, witness, checked, valid => by
    cases valid with
    | @presentedRule _ _ index rule initial final witnesses found matched premises =>
      simp only [presentedEnough, List.all_eq_true, List.isEmpty_iff] at checked
      rw [checked rule (List.mem_of_getElem? found)] at matched
      cases matched
  | fuel + 1, source, target, witness, checked, valid => by
    cases valid with
    | @presentedRule _ _ index rule initial final witnesses found matched premises =>
      simp only [presentedEnough, List.all_eq_true] at checked
      have premisesBound := presentedDepth_le_of_premisesEnough
        (fun valid bounded => mem_presentedStepsAt_of_stepValid valid bounded)
        (fun checked valid => presentedDepth_le_of_enough checked valid)
        (checked rule (List.mem_of_getElem? found) initial matched) premises
      simp only [Witness.depth]
      have := Witness.depthList_le_iff.mpr premisesBound
      omega

/-- **When the fuel is enough, the listing holds every step.** -/
theorem mem_presentedStepsAt_of_enough {fuel : ℕ} {source target : Pattern} {witness : Witness}
    (checked : presentedEnough relEnv language present fuel source = true)
    (valid : StepValid relEnv language source witness target (.presented present)) :
    (witness, target) ∈ presentedStepsAt relEnv language present fuel source :=
  mem_presentedStepsAt_of_stepValid valid (presentedDepth_le_of_enough checked valid)

/-! ## Rules without premises -/

/-- **Rules without premises step alike under every presented policy**: a presentation reads only the
boundaries of premises. -/
theorem stepValid_presented_iff_of_premises_nil (noPremises : ∀ rule ∈ language.rewrites, rule.premises = [])
    {source target : Pattern} {witness : Witness} :
    StepValid relEnv language source witness target (.presented present) ↔
      StepValid relEnv language source witness target := by
  constructor
  · intro valid
    cases valid with
    | presentedRule found matched premises =>
      have none := noPremises _ (List.mem_of_getElem? found)
      rw [none] at premises
      cases premises
      exact .rule found matched (by rw [none]; exact .nil _)
  · intro valid
    cases valid with
    | rule found matched premises =>
      have none := noPremises _ (List.mem_of_getElem? found)
      rw [none] at premises
      cases premises
      exact .presentedRule found matched (by rw [none]; exact .presentedNil _)

/-- **Rules without premises step alike under every equational policy**: a theory reads only the boundaries of
premises. -/
theorem stepValid_equational_iff_of_premises_nil {theory : Setoid Pattern}
    (noPremises : ∀ rule ∈ language.rewrites, rule.premises = []) {source target : Pattern} {witness : Witness} :
    StepValid relEnv language source witness target (.equational theory) ↔
      StepValid relEnv language source witness target := by
  constructor
  · intro valid
    cases valid with
    | equationalRule found matched premises =>
      have none := noPremises _ (List.mem_of_getElem? found)
      rw [none] at premises
      cases premises
      exact .rule found matched (by rw [none]; exact .nil _)
  · intro valid
    cases valid with
    | rule found matched premises =>
      have none := noPremises _ (List.mem_of_getElem? found)
      rw [none] at premises
      cases premises
      exact .equationalRule found matched (by rw [none]; exact .equationalNil _)

/-! ## Listed presentations are equivalent presentations -/

theorem forall₂_related_of_mem_sections {theory : Setoid Pattern}
    (related : ∀ term shown, shown ∈ present term → theory.r term shown) :
    ∀ {tuple presented : List Pattern}, presented ∈ List.sections (tuple.map present) → List.Forall₂ theory.r tuple presented
  | [], presented, member => by
    rw [List.map_nil, List.sections, List.mem_singleton] at member
    subst member
    exact .nil
  | value :: values, presented, member => by
    have chosen := List.mem_sections.mp member
    rw [List.map_cons] at chosen
    cases chosen with
    | cons head tail =>
      exact .cons (related _ _ head) (forall₂_related_of_mem_sections related (List.mem_sections.mpr tail))

mutual
/-- **A step through listed presentations is a step modulo a theory** that relates each term to its listed
presentations: each listed presentation of a child is an equivalent presentation of it. -/
theorem stepValid_equational_of_presented {theory : Setoid Pattern}
    (related : ∀ term shown, shown ∈ present term → theory.r term shown) :
    ∀ (witness : Witness) {source target : Pattern},
      StepValid relEnv language source witness target (.presented present) →
        StepValid relEnv language source witness target (.equational theory)
  | .rule _ _ witnesses, _, _, valid => by
    cases valid with
    | presentedRule found matched premises =>
      exact .equationalRule found matched (premisesValid_equational_of_presented related witnesses premises)
  | .base _, _, _, valid => by cases valid
  | .premiseStep _ _ _ _, _, _, valid => by cases valid
  | .forAll _, _, _, valid => by cases valid

theorem premiseValid_equational_of_presented {theory : Setoid Pattern}
    (related : ∀ term shown, shown ∈ present term → theory.r term shown) :
    ∀ (witness : Witness) {sites : Pattern} {initial final : Bindings} {premise : Premise},
      PremiseValid relEnv language sites initial premise witness final (.presented present) →
        PremiseValid relEnv language sites initial premise witness final (.equational theory)
  | .base _, _, _, _, _, valid => by
    cases valid with
    | presentedFreshness member => exact .equationalFreshness member
    | presentedQuery member =>
      simp only [presentedQueryStep, List.mem_flatMap, List.mem_filterMap] at member
      obtain ⟨tuple, provided, presented, chosen, extension, matched, merged⟩ := member
      exact .equationalQuery ⟨tuple, provided, presented, forall₂_related_of_mem_sections related chosen, extension,
        matched, merged⟩
  | .premiseStep step candidate _ _, _, _, _, _, valid => by
    cases valid with
    | presentedStep endpoints redexMember stepped candidateMember matched merged =>
      exact .equationalStep endpoints (related _ _ redexMember)
        (stepValid_equational_of_presented related step stepped) (related _ _ candidateMember)
        (PresentedMatch.of_literal theory matched) merged
  | .forAll bodies, _, _, _, _, valid => by
    cases valid with
    | presentedForAll selected body =>
      exact .equationalForAll selected (forAllValid_equational_of_presented related bodies body)
  | .rule _ _ _, _, _, _, _, valid => by cases valid

theorem premisesValid_equational_of_presented {theory : Setoid Pattern}
    (related : ∀ term shown, shown ∈ present term → theory.r term shown) :
    ∀ (witnesses : List Witness) {sites : Pattern} {initial final : Bindings} {premises : List Premise},
      PremisesValid relEnv language sites initial premises witnesses final (.presented present) →
        PremisesValid relEnv language sites initial premises witnesses final (.equational theory)
  | [], _, _, _, _, valid => by
    cases valid
    exact .equationalNil _
  | witness :: witnesses, _, _, _, _, valid => by
    cases valid with
    | presentedCons first rest =>
      exact .equationalCons (premiseValid_equational_of_presented related witness first)
        (premisesValid_equational_of_presented related witnesses rest)

theorem forAllValid_equational_of_presented {theory : Setoid Pattern}
    (related : ∀ term shown, shown ∈ present term → theory.r term shown) :
    ∀ (witnesses : List Witness) {sites : Pattern} {bindings : Bindings} {parameter : String}
      {body : Premise} {elements : List Pattern},
      ForAllValid relEnv language sites bindings parameter body elements witnesses (.presented present) →
        ForAllValid relEnv language sites bindings parameter body elements witnesses (.equational theory)
  | [], _, _, _, _, _, valid => by
    cases valid
    exact .equationalNil
  | witness :: witnesses, _, _, _, _, _, valid => by
    cases valid with
    | presentedCons first rest =>
      exact .equationalCons (premiseValid_equational_of_presented related witness first)
        (forAllValid_equational_of_presented related witnesses rest)
end

/-! ## Checking a witness through presentations -/

variable (relEnv language present)

mutual
/-- **Check a step witness through presentations** at a source, computing its target. A step premise's witness does not
name the listed presentation of the child it stepped; each is tried. -/
def checkPresentedStep (source : Pattern) : Witness → Option Pattern
  | .rule index initial witnesses =>
      match language.rewrites[index]? with
      | none => none
      | some rule =>
          if initial ∈ matchPatternForRule language rule source then
            (checkPresentedPremises (captureSites rule) initial rule.premises witnesses).map
              (fun final => applyBindingsScoped (captureSites rule) final 0 rule.right)
          else none
  | _ => none

/-- Check the witnesses of a list of premises through presentations. -/
def checkPresentedPremises (sites : Pattern) (bindings : Bindings) : List Premise → List Witness → Option Bindings
  | [], [] => some bindings
  | premise :: premises, witness :: witnesses =>
      match checkPresentedPremise sites bindings premise witness with
      | none => none
      | some middle => checkPresentedPremises sites middle premises witnesses
  | _, _ => none

/-- Check a premise witness through presentations. -/
def checkPresentedPremise (sites : Pattern) (bindings : Bindings) : Premise → Witness → Option Bindings
  | premise, .base result =>
      if isBase premise = true ∧ result ∈ presentedBaseStep relEnv language present bindings premise then some result
      else none
  | premise, .premiseStep step candidate matched result =>
      match stepEndpoints premise with
      | none => none
      | some (source, target) =>
          if ((present (applyBindingsScoped sites bindings (stepDepth sites premise) source)).any fun redex =>
                match checkPresentedStep redex step with
                | some contractum => decide (candidate ∈ present contractum)
                | none => false) = true ∧
              matched ∈ matchPattern target candidate ∧ mergeBindings bindings matched = some result then
            some result
          else none
  | .forAll collection parameter body, .forAll bodies =>
      match bindings.lookup collection with
      | some (.collection _ elements none) =>
          if checkPresentedForAll sites bindings parameter body elements bodies = true then some bindings else none
      | _ => none
  | _, _ => none

/-- Check the evidence for a quantified body at each element, through presentations. -/
def checkPresentedForAll (sites : Pattern) (bindings : Bindings) (parameter : String) (body : Premise) :
    List Pattern → List Witness → Bool
  | [], [] => true
  | element :: elements, witness :: witnesses =>
      (checkPresentedPremise sites (bindParameter bindings parameter element) body witness).isSome &&
        checkPresentedForAll sites bindings parameter body elements witnesses
  | _, _ => false
end

variable {relEnv language present}

mutual
/-- **A checked witness through presentations is valid.** -/
theorem stepValid_of_checkPresentedStep : ∀ (witness : Witness) {source target : Pattern},
    checkPresentedStep relEnv language present source witness = some target →
      StepValid relEnv language source witness target (.presented present)
  | .rule index initial witnesses, source, target, checked => by
    simp only [checkPresentedStep] at checked
    split at checked
    · cases checked
    · rename_i rule found
      split at checked
      · rename_i matched
        obtain ⟨final, premisesChecked, rfl⟩ := Option.map_eq_some_iff.mp checked
        exact .presentedRule found matched (premisesValid_of_checkPresentedPremises witnesses premisesChecked)
      · cases checked
  | .base _, _, _, checked => by simp [checkPresentedStep] at checked
  | .premiseStep _ _ _ _, _, _, checked => by simp [checkPresentedStep] at checked
  | .forAll _, _, _, checked => by simp [checkPresentedStep] at checked

theorem premisesValid_of_checkPresentedPremises : ∀ (witnesses : List Witness) {sites : Pattern}
    {bindings final : Bindings} {premises : List Premise},
    checkPresentedPremises relEnv language present sites bindings premises witnesses = some final →
      PremisesValid relEnv language sites bindings premises witnesses final (.presented present)
  | [], _, _, _, [], checked => by
    simp only [checkPresentedPremises, Option.some.injEq] at checked
    subst checked
    exact .presentedNil _
  | [], _, _, _, _ :: _, checked => by simp [checkPresentedPremises] at checked
  | _ :: _, _, _, _, [], checked => by simp [checkPresentedPremises] at checked
  | witness :: witnesses, sites, bindings, final, premise :: premises, checked => by
    simp only [checkPresentedPremises] at checked
    split at checked
    · cases checked
    · rename_i middle headChecked
      exact .presentedCons (premiseValid_of_checkPresentedPremise witness headChecked)
        (premisesValid_of_checkPresentedPremises witnesses checked)

theorem premiseValid_of_checkPresentedPremise : ∀ (witness : Witness) {sites : Pattern} {bindings result : Bindings}
    {premise : Premise}, checkPresentedPremise relEnv language present sites bindings premise witness = some result →
      PremiseValid relEnv language sites bindings premise witness result (.presented present)
  | .base produced, sites, bindings, result, premise, checked => by
    simp only [checkPresentedPremise] at checked
    split at checked
    · rename_i holds
      cases checked
      exact presentedPremiseValid_of_base holds.1 holds.2
    · cases checked
  | .premiseStep step candidate matched produced, sites, bindings, result, premise, checked => by
    simp only [checkPresentedPremise] at checked
    split at checked
    · cases checked
    · rename_i source target endpoints
      split at checked
      · rename_i holds
        cases checked
        obtain ⟨tried, matchedMember, merged⟩ := holds
        obtain ⟨redex, redexMember, succeeded⟩ := List.any_eq_true.mp tried
        split at succeeded
        · rename_i contractum stepped
          exact .presentedStep endpoints redexMember (stepValid_of_checkPresentedStep step stepped)
            (of_decide_eq_true succeeded) matchedMember merged
        · cases succeeded
      · cases checked
  | .forAll bodies, sites, bindings, result, premise, checked => by
    cases premise with
    | forAll collection parameter body =>
      simp only [checkPresentedPremise] at checked
      split at checked
      · rename_i kind elements found
        split at checked
        · rename_i bodiesChecked
          cases checked
          exact .presentedForAll found (forAllValid_of_checkPresentedForAll bodies bodiesChecked)
        · cases checked
      · cases checked
    | _ => simp [checkPresentedPremise] at checked
  | .rule _ _ _, _, _, _, premise, checked => by
    cases premise <;> simp [checkPresentedPremise] at checked

theorem forAllValid_of_checkPresentedForAll : ∀ (witnesses : List Witness) {sites : Pattern} {bindings : Bindings}
    {parameter : String} {body : Premise} {elements : List Pattern},
    checkPresentedForAll relEnv language present sites bindings parameter body elements witnesses = true →
      ForAllValid relEnv language sites bindings parameter body elements witnesses (.presented present)
  | [], _, _, _, _, [], _ => .presentedNil
  | [], _, _, _, _, _ :: _, checked => by simp [checkPresentedForAll] at checked
  | _ :: _, _, _, _, _, [], checked => by simp [checkPresentedForAll] at checked
  | witness :: witnesses, sites, bindings, parameter, body, element :: elements, checked => by
    simp only [checkPresentedForAll, Bool.and_eq_true, Option.isSome_iff_exists] at checked
    obtain ⟨⟨result, headChecked⟩, rest⟩ := checked
    exact .presentedCons (premiseValid_of_checkPresentedPremise witness headChecked)
      (forAllValid_of_checkPresentedForAll witnesses rest)
end

end Mettapedia.OSLF.MeTTaIL.ReferenceStep

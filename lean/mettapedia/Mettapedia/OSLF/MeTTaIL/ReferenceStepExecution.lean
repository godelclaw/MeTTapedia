import Mettapedia.OSLF.MeTTaIL.ReferenceStep

/-!
# Executing the reference step relation

`stepsAt fuel source` lists steps of `source` together with their witnesses, every derivation at most
`fuel` rule layers deep. Premise evaluation takes the recursive stepper as an argument
(`premiseAtUsing`), as the least contextual relation's compiler does, so a step premise at one layer
uses the steps one layer down.

- **Sound**: every listed pair is a valid witness and its target (`stepValid_of_mem_stepsAt`).
- **Complete**: every valid witness is listed once the fuel reaches its depth
  (`mem_stepsAt_of_stepValid`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.ReferenceStep

open Syntax Match Engine ContextualStep ReflectiveCanonical ReflectiveSubstitution

/-! ## Depth of a witness -/

mutual
/-- The number of rule layers in a witness. -/
def Witness.depth : Witness → ℕ
  | .base _ => 0
  | .premiseStep step _ _ _ => step.depth
  | .rule _ _ premises => Witness.depthList premises + 1
  | .forAll bodies => Witness.depthList bodies

/-- The largest depth in a list of witnesses. -/
def Witness.depthList : List Witness → ℕ
  | [] => 0
  | witness :: witnesses => max witness.depth (Witness.depthList witnesses)
end

variable (relEnv : RelationEnv) (language : LanguageDef)

/-! ## The executor -/

/-- Evaluate a premise with a given recursive stepper, listing the witnesses and the bindings they
produce. -/
def premiseAtUsing (recursive : Pattern → List (Witness × Pattern)) (sites : Pattern) :
    Bindings → Premise → List (Witness × Bindings)
  | bindings, .forAll collection parameter body =>
      match bindings.lookup collection with
      | some (.collection _ elements none) =>
          (elements.foldr
            (fun element rest =>
              (premiseAtUsing recursive sites (bindParameter bindings parameter element) body).flatMap
                fun entry => rest.map (entry.1 :: ·))
            [[]]).map fun bodies => (.forAll bodies, bindings)
      | _ => []
  | bindings, premise =>
      if isBase premise = true then
        (premiseStepWithEnv relEnv language bindings premise).map fun result => (.base result, result)
      else
        match stepEndpoints premise with
        | none => []
        | some (source, target) =>
            (recursive (applyBindingsScoped sites bindings (stepDepth sites premise) source)).flatMap
              fun entry =>
                (matchPattern target entry.2).filterMap fun matched =>
                  (mergeBindings bindings matched).map fun result =>
                    (.premiseStep entry.1 entry.2 matched result, result)

/-- Evaluate a list of premises with a given recursive stepper. -/
def premisesAtUsing (recursive : Pattern → List (Witness × Pattern)) (sites : Pattern) :
    Bindings → List Premise → List (List Witness × Bindings)
  | bindings, [] => [([], bindings)]
  | bindings, premise :: premises =>
      (premiseAtUsing relEnv language recursive sites bindings premise).flatMap fun entry =>
        (premisesAtUsing recursive sites entry.2 premises).map fun rest => (entry.1 :: rest.1, rest.2)

/-- **The steps of a term with their witnesses**, derivations at most `fuel` rule layers deep. -/
def stepsAt : ℕ → Pattern → List (Witness × Pattern)
  | 0, _ => []
  | fuel + 1, source =>
      (List.range language.rewrites.length).flatMap fun index =>
        match language.rewrites[index]? with
        | none => []
        | some rule =>
            (matchPatternForRule language rule source).flatMap fun initial =>
              (premisesAtUsing relEnv language (stepsAt fuel) (captureSites rule) initial rule.premises).map
                fun entry =>
                  (.rule index initial entry.1, applyBindingsScoped (captureSites rule) entry.2 0 rule.right)

/-! ## One witness per element -/

/-- The lists built by choosing one entry per element are the element-wise choices. -/
theorem mem_foldr_choices_iff {α β γ : Type} (choices : α → List (β × γ)) :
    ∀ (elements : List α) (picked : List β),
      picked ∈ elements.foldr (fun element rest => (choices element).flatMap fun entry => rest.map (entry.1 :: ·))
          [[]] ↔
        List.Forall₂ (fun element choice => ∃ other, (choice, other) ∈ choices element) elements picked
  | [], picked => by
    simp only [List.foldr_nil, List.mem_singleton]
    constructor
    · rintro rfl
      exact .nil
    · intro related
      cases related
      rfl
  | element :: elements, picked => by
    simp only [List.foldr_cons, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨⟨choice, other⟩, chosen, rest, restMember, rfl⟩
      exact .cons ⟨other, chosen⟩ ((mem_foldr_choices_iff choices elements rest).mp restMember)
    · intro related
      cases related with
      | cons head tail =>
        obtain ⟨other, chosen⟩ := head
        exact ⟨(_, other), chosen, _, (mem_foldr_choices_iff choices elements _).mpr tail, rfl⟩

theorem Witness.depthList_le_iff {bound : ℕ} : ∀ {witnesses : List Witness},
    Witness.depthList witnesses ≤ bound ↔ ∀ witness ∈ witnesses, witness.depth ≤ bound
  | [] => by simp [Witness.depthList]
  | witness :: witnesses => by
    simp only [Witness.depthList, max_le_iff, List.mem_cons, forall_eq_or_imp, Witness.depthList_le_iff]

/-! ## Soundness -/

/-- **Every listed premise witness is valid**, when the recursive stepper lists only valid steps. -/
theorem premiseValid_of_mem_premiseAtUsing {recursive : Pattern → List (Witness × Pattern)}
    (recursiveSound : ∀ {source witness target}, (witness, target) ∈ recursive source →
      StepValid relEnv language source witness target) :
    ∀ (premise : Premise) {sites : Pattern} {bindings result : Bindings} {witness : Witness},
      (witness, result) ∈ premiseAtUsing relEnv language recursive sites bindings premise →
        PremiseValid relEnv language sites bindings premise witness result
  | .forAll collection parameter body, sites, bindings, result, witness, member => by
    simp only [premiseAtUsing] at member
    split at member
    · rename_i kind elements found
      obtain ⟨bodies, bodiesMember, pairEq⟩ := List.mem_map.mp member
      simp only [Prod.mk.injEq] at pairEq
      obtain ⟨rfl, rfl⟩ := pairEq
      have related := (mem_foldr_choices_iff _ elements bodies).mp bodiesMember
      refine .forAll found ?_
      clear bodiesMember member found
      induction related with
      | nil => exact .nil
      | cons head _ tailValid =>
        obtain ⟨other, chosen⟩ := head
        exact .cons (premiseValid_of_mem_premiseAtUsing recursiveSound body chosen) tailValid
    · simp at member
  | .freshness condition, sites, bindings, result, witness, member => by
    simp only [premiseAtUsing, isBase, ↓reduceIte, List.mem_map, Prod.mk.injEq] at member
    obtain ⟨produced, producedMember, rfl, rfl⟩ := member
    exact .base rfl producedMember
  | .relationQuery relation arguments, sites, bindings, result, witness, member => by
    simp only [premiseAtUsing, isBase, ↓reduceIte, List.mem_map, Prod.mk.injEq] at member
    obtain ⟨produced, producedMember, rfl, rfl⟩ := member
    exact .base rfl producedMember
  | .congruence source target, sites, bindings, result, witness, member => by
    simp only [premiseAtUsing, isBase, Bool.false_eq_true, ↓reduceIte, stepEndpoints, List.mem_flatMap,
      List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq] at member
    obtain ⟨⟨step, candidate⟩, stepMember, matched, matchedMember, merged, mergedEq, rfl, rfl⟩ := member
    exact .step rfl (recursiveSound stepMember) matchedMember mergedEq
  | .scopedStep premise, sites, bindings, result, witness, member => by
    simp only [premiseAtUsing, isBase, Bool.false_eq_true, ↓reduceIte, stepEndpoints, List.mem_flatMap,
      List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq] at member
    obtain ⟨⟨step, candidate⟩, stepMember, matched, matchedMember, merged, mergedEq, rfl, rfl⟩ := member
    exact .step rfl (recursiveSound stepMember) matchedMember mergedEq

theorem premisesValid_of_mem_premisesAtUsing {recursive : Pattern → List (Witness × Pattern)}
    (recursiveSound : ∀ {source witness target}, (witness, target) ∈ recursive source →
      StepValid relEnv language source witness target) {sites : Pattern} :
    ∀ {premises : List Premise} {bindings final : Bindings} {witnesses : List Witness},
      (witnesses, final) ∈ premisesAtUsing relEnv language recursive sites bindings premises →
        PremisesValid relEnv language sites bindings premises witnesses final
  | [], bindings, final, witnesses, member => by
    simp only [premisesAtUsing, List.mem_singleton, Prod.mk.injEq] at member
    obtain ⟨rfl, rfl⟩ := member
    exact .nil _
  | premise :: premises, bindings, final, witnesses, member => by
    simp only [premisesAtUsing, List.mem_flatMap, List.mem_map, Prod.mk.injEq] at member
    obtain ⟨⟨witness, middle⟩, headMember, ⟨rest, restFinal⟩, restMember, rfl, rfl⟩ := member
    exact .cons (premiseValid_of_mem_premiseAtUsing relEnv language recursiveSound premise headMember)
      (premisesValid_of_mem_premisesAtUsing recursiveSound restMember)

/-- **Sound**: every listed step comes with a valid witness. -/
theorem stepValid_of_mem_stepsAt : ∀ {fuel : ℕ} {source target : Pattern} {witness : Witness},
    (witness, target) ∈ stepsAt relEnv language fuel source → StepValid relEnv language source witness target
  | 0, _, _, _, member => by simp [stepsAt] at member
  | fuel + 1, source, target, witness, member => by
    simp only [stepsAt, List.mem_flatMap, List.mem_range] at member
    obtain ⟨index, _, rest⟩ := member
    split at rest
    · simp at rest
    · rename_i rule found
      simp only [List.mem_flatMap, List.mem_map, Prod.mk.injEq] at rest
      obtain ⟨initial, matched, ⟨witnesses, final⟩, premisesMember, rfl, rfl⟩ := rest
      exact .rule found matched
        (premisesValid_of_mem_premisesAtUsing relEnv language (stepValid_of_mem_stepsAt (fuel := fuel)) premisesMember)

/-! ## Completeness -/

/-- Valid evidence at each element, every body witness listed by `listed`, gives the element-wise
choices. -/
theorem forall₂_of_forAllValid {sites : Pattern} {bindings : Bindings} {parameter : String} {body : Premise}
    {bound : ℕ} {choices : Pattern → List (Witness × Bindings)}
    (listed : ∀ {element : Pattern} {witness : Witness} {result : Bindings},
      PremiseValid relEnv language sites (bindParameter bindings parameter element) body witness result →
        witness.depth ≤ bound → (witness, result) ∈ choices element) :
    ∀ {elements : List Pattern} {bodies : List Witness},
      ForAllValid relEnv language sites bindings parameter body elements bodies →
      (∀ witness ∈ bodies, witness.depth ≤ bound) →
        List.Forall₂ (fun element choice => ∃ other, (choice, other) ∈ choices element) elements bodies
  | [], [], _, _ => .nil
  | [], _ :: _, valid, _ => by cases valid
  | _ :: _, [], valid, _ => by cases valid
  | element :: elements, witness :: witnesses, valid, bounded => by
    cases valid with
    | cons head tail =>
      exact .cons ⟨_, listed head (bounded witness List.mem_cons_self)⟩
        (forall₂_of_forAllValid listed tail (fun other member => bounded other (List.mem_cons_of_mem _ member)))

/-- **Every valid premise witness is listed**, when the recursive stepper lists every valid step no
deeper than the witness. -/
theorem mem_premiseAtUsing_of_premiseValid {recursive : Pattern → List (Witness × Pattern)} {bound : ℕ}
    (recursiveComplete : ∀ {source witness target}, StepValid relEnv language source witness target →
      witness.depth ≤ bound → (witness, target) ∈ recursive source) :
    ∀ (premise : Premise) {sites : Pattern} {bindings result : Bindings} {witness : Witness},
      PremiseValid relEnv language sites bindings premise witness result → witness.depth ≤ bound →
        (witness, result) ∈ premiseAtUsing relEnv language recursive sites bindings premise
  | .forAll collection parameter body, sites, bindings, result, witness, valid, bounded => by
    cases valid with
    | base baseCase _ => simp [isBase] at baseCase
    | step endpoints _ _ _ => simp [stepEndpoints] at endpoints
    | @forAll _ _ _ _ _ kind elements bodies found bodiesValid =>
      simp only [premiseAtUsing, found]
      refine List.mem_map.mpr ⟨bodies, ?_, rfl⟩
      apply (mem_foldr_choices_iff _ elements bodies).mpr
      exact forall₂_of_forAllValid relEnv language
        (fun bodyValid bodyBounded => mem_premiseAtUsing_of_premiseValid recursiveComplete body bodyValid bodyBounded)
        bodiesValid (Witness.depthList_le_iff.mp bounded)
  | .freshness condition, sites, bindings, result, witness, valid, _ => by
    cases valid with
    | base _ member =>
      simp only [premiseAtUsing, isBase, ↓reduceIte, List.mem_map, Prod.mk.injEq]
      exact ⟨_, member, rfl, rfl⟩
    | step endpoints _ _ _ => simp [stepEndpoints] at endpoints
  | .relationQuery relation arguments, sites, bindings, result, witness, valid, _ => by
    cases valid with
    | base _ member =>
      simp only [premiseAtUsing, isBase, ↓reduceIte, List.mem_map, Prod.mk.injEq]
      exact ⟨_, member, rfl, rfl⟩
    | step endpoints _ _ _ => simp [stepEndpoints] at endpoints
  | .congruence source target, sites, bindings, result, witness, valid, bounded => by
    cases valid with
    | base baseCase _ => simp [isBase] at baseCase
    | step endpoints stepped matchedMember merged =>
      simp only [stepEndpoints, Option.some.injEq, Prod.mk.injEq] at endpoints
      obtain ⟨rfl, rfl⟩ := endpoints
      simp only [premiseAtUsing, isBase, Bool.false_eq_true, ↓reduceIte, stepEndpoints, List.mem_flatMap,
        List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq]
      exact ⟨_, recursiveComplete stepped bounded, _, matchedMember, _, merged, rfl, rfl⟩
  | .scopedStep premise, sites, bindings, result, witness, valid, bounded => by
    cases valid with
    | base baseCase _ => simp [isBase] at baseCase
    | step endpoints stepped matchedMember merged =>
      simp only [stepEndpoints, Option.some.injEq, Prod.mk.injEq] at endpoints
      obtain ⟨rfl, rfl⟩ := endpoints
      simp only [premiseAtUsing, isBase, Bool.false_eq_true, ↓reduceIte, stepEndpoints, List.mem_flatMap,
        List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq]
      exact ⟨_, recursiveComplete stepped bounded, _, matchedMember, _, merged, rfl, rfl⟩

theorem mem_premisesAtUsing_of_premisesValid {recursive : Pattern → List (Witness × Pattern)} {bound : ℕ}
    (recursiveComplete : ∀ {source witness target}, StepValid relEnv language source witness target →
      witness.depth ≤ bound → (witness, target) ∈ recursive source) {sites : Pattern} :
    ∀ {premises : List Premise} {bindings final : Bindings} {witnesses : List Witness},
      PremisesValid relEnv language sites bindings premises witnesses final →
      (∀ witness ∈ witnesses, witness.depth ≤ bound) →
        (witnesses, final) ∈ premisesAtUsing relEnv language recursive sites bindings premises
  | [], _, _, _, valid, _ => by
    cases valid
    simp [premisesAtUsing]
  | premise :: premises, _, _, _, valid, bounded => by
    cases valid with
    | @cons _ _ _ _ _ _ witness witnesses first rest =>
      simp only [premisesAtUsing, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
      exact ⟨_, mem_premiseAtUsing_of_premiseValid relEnv language recursiveComplete premise first
          (bounded witness List.mem_cons_self),
        _, mem_premisesAtUsing_of_premisesValid recursiveComplete rest
          (fun other member => bounded other (List.mem_cons_of_mem _ member)), rfl, rfl⟩

/-- **Complete**: a valid witness is listed once the fuel reaches its depth. -/
theorem mem_stepsAt_of_stepValid : ∀ {fuel : ℕ} {source target : Pattern} {witness : Witness},
    StepValid relEnv language source witness target → witness.depth ≤ fuel →
      (witness, target) ∈ stepsAt relEnv language fuel source
  | fuel, source, target, witness, valid, bounded => by
    cases valid with
    | @rule _ index rule initial final witnesses found matched premises =>
      simp only [Witness.depth] at bounded
      obtain ⟨smaller, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by omega⟩
      have premisesBounded : ∀ witness ∈ witnesses, witness.depth ≤ smaller :=
        Witness.depthList_le_iff.mp (by omega)
      have indexBound : index < language.rewrites.length := by
        by_contra outside
        rw [List.getElem?_eq_none (by omega)] at found
        cases found
      simp only [stepsAt, List.mem_flatMap, List.mem_range]
      refine ⟨index, indexBound, ?_⟩
      simp only [found, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
      exact ⟨initial, matched, (witnesses, final),
        mem_premisesAtUsing_of_premisesValid relEnv language
          (fun valid bounded => mem_stepsAt_of_stepValid valid bounded) premises premisesBounded, rfl, rfl⟩

/-- **The reference relation is the union of the executor's layers.** -/
theorem step_iff_exists_mem_stepsAt {source target : Pattern} :
    Step relEnv language source target ↔ ∃ fuel witness, (witness, target) ∈ stepsAt relEnv language fuel source := by
  constructor
  · rintro ⟨witness, valid⟩
    exact ⟨witness.depth, witness, mem_stepsAt_of_stepValid relEnv language valid le_rfl⟩
  · rintro ⟨fuel, witness, member⟩
    exact ⟨witness, stepValid_of_mem_stepsAt relEnv language member⟩

/-! ## Complete listings

The listing at a fuel holds every step whose derivation fits in the fuel. It holds every step outright
when the fuel is **enough** (`enough`): at no fuel no rule may match, and with more fuel the step
premises of every rule that matches are enough one layer down, under every bindings the listing
produces for the premises before them. Then no derivation is cut off (`depth_le_of_enough`), and the
listing is the term's complete set of successors (`step_iff_mem_of_enough`). -/

/-- Whether a premise's step source is completely listed by `check`. -/
def premiseEnoughUsing (check : Pattern → Bool) (sites : Pattern) : Bindings → Premise → Bool
  | bindings, .forAll collection parameter body =>
      match bindings.lookup collection with
      | some (.collection _ elements none) =>
          elements.all fun element => premiseEnoughUsing check sites (bindParameter bindings parameter element) body
      | _ => true
  | bindings, premise =>
      if isBase premise = true then true
      else
        match stepEndpoints premise with
        | none => true
        | some (source, _) => check (applyBindingsScoped sites bindings (stepDepth sites premise) source)

/-- Whether every premise's step source is completely listed, under every bindings the listing produces
for the premises before it. -/
def premisesEnoughUsing (recursive : Pattern → List (Witness × Pattern)) (check : Pattern → Bool) (sites : Pattern) :
    Bindings → List Premise → Bool
  | _, [] => true
  | bindings, premise :: premises =>
      premiseEnoughUsing check sites bindings premise &&
        (premiseAtUsing relEnv language recursive sites bindings premise).all fun entry =>
          premisesEnoughUsing recursive check sites entry.2 premises

/-- **The fuel is enough for a term**: every derivation of a step from it fits in the fuel. -/
def enough : ℕ → Pattern → Bool
  | 0, source => language.rewrites.all fun rule => (matchPatternForRule language rule source).isEmpty
  | fuel + 1, source => language.rewrites.all fun rule =>
      (matchPatternForRule language rule source).all fun initial =>
        premisesEnoughUsing relEnv language (stepsAt relEnv language fuel) (enough fuel) (captureSites rule) initial
          rule.premises

variable {relEnv language}

theorem depthList_le_of_forAllValid {check : Pattern → Bool} {bound : ℕ} {sites : Pattern} {bindings : Bindings}
    {parameter : String} {body : Premise}
    (bodyBound : ∀ {bindings' : Bindings} {result : Bindings} {witness : Witness},
      premiseEnoughUsing check sites bindings' body = true →
        PremiseValid relEnv language sites bindings' body witness result → witness.depth ≤ bound) :
    ∀ {elements : List Pattern} {bodies : List Witness},
      (∀ element ∈ elements, premiseEnoughUsing check sites (bindParameter bindings parameter element) body = true) →
        ForAllValid relEnv language sites bindings parameter body elements bodies → ∀ witness ∈ bodies, witness.depth ≤ bound
  | [], [], _, _ => by simp
  | [], _ :: _, _, valid => by cases valid
  | _ :: _, [], _, valid => by cases valid
  | element :: elements, witness :: witnesses, checked, valid => by
    cases valid with
    | cons head tail =>
      intro other member
      rcases List.mem_cons.mp member with rfl | member
      · exact bodyBound (checked element List.mem_cons_self) head
      · exact depthList_le_of_forAllValid bodyBound
          (fun element' inside => checked element' (List.mem_cons_of_mem _ inside)) tail other member

theorem depth_le_of_premiseEnough {check : Pattern → Bool} {bound : ℕ}
    (checkBound : ∀ {source witness target}, check source = true → StepValid relEnv language source witness target →
      witness.depth ≤ bound) :
    ∀ (premise : Premise) {sites : Pattern} {bindings result : Bindings} {witness : Witness},
      premiseEnoughUsing check sites bindings premise = true →
        PremiseValid relEnv language sites bindings premise witness result → witness.depth ≤ bound
  | .forAll collection parameter body, sites, bindings, result, witness, checked, valid => by
    cases valid with
    | base baseCase _ => simp [isBase] at baseCase
    | step endpoints _ _ _ => simp [stepEndpoints] at endpoints
    | @forAll _ _ _ _ _ kind elements bodies found bodiesValid =>
      simp only [premiseEnoughUsing, found, List.all_eq_true] at checked
      simp only [Witness.depth]
      exact Witness.depthList_le_iff.mpr (depthList_le_of_forAllValid
        (fun bodyChecked bodyValid => depth_le_of_premiseEnough checkBound body bodyChecked bodyValid) checked bodiesValid)
  | .freshness _, _, _, _, _, _, valid => by
    cases valid with
    | base _ _ => simp [Witness.depth]
    | step endpoints _ _ _ => simp [stepEndpoints] at endpoints
  | .relationQuery _ _, _, _, _, _, _, valid => by
    cases valid with
    | base _ _ => simp [Witness.depth]
    | step endpoints _ _ _ => simp [stepEndpoints] at endpoints
  | .congruence source target, sites, bindings, result, witness, checked, valid => by
    cases valid with
    | base baseCase _ => simp [isBase] at baseCase
    | step endpoints stepped _ _ =>
      simp only [stepEndpoints, Option.some.injEq, Prod.mk.injEq] at endpoints
      obtain ⟨rfl, rfl⟩ := endpoints
      simp only [premiseEnoughUsing, isBase, Bool.false_eq_true, ↓reduceIte, stepEndpoints] at checked
      simp only [Witness.depth]
      exact checkBound checked stepped
  | .scopedStep premise, sites, bindings, result, witness, checked, valid => by
    cases valid with
    | base baseCase _ => simp [isBase] at baseCase
    | step endpoints stepped _ _ =>
      simp only [stepEndpoints, Option.some.injEq, Prod.mk.injEq] at endpoints
      obtain ⟨rfl, rfl⟩ := endpoints
      simp only [premiseEnoughUsing, isBase, Bool.false_eq_true, ↓reduceIte, stepEndpoints] at checked
      simp only [Witness.depth]
      exact checkBound checked stepped

theorem depth_le_of_premisesEnough {recursive : Pattern → List (Witness × Pattern)} {check : Pattern → Bool}
    {bound : ℕ}
    (recursiveComplete : ∀ {source witness target}, StepValid relEnv language source witness target →
      witness.depth ≤ bound → (witness, target) ∈ recursive source)
    (checkBound : ∀ {source witness target}, check source = true → StepValid relEnv language source witness target →
      witness.depth ≤ bound) {sites : Pattern} :
    ∀ {premises : List Premise} {bindings final : Bindings} {witnesses : List Witness},
      premisesEnoughUsing relEnv language recursive check sites bindings premises = true →
        PremisesValid relEnv language sites bindings premises witnesses final → ∀ witness ∈ witnesses, witness.depth ≤ bound
  | [], _, _, _, _, valid => by
    cases valid
    simp
  | premise :: premises, bindings, final, _, checked, valid => by
    cases valid with
    | @cons _ _ middle _ _ _ witness witnesses first rest =>
      simp only [premisesEnoughUsing, Bool.and_eq_true, List.all_eq_true] at checked
      have firstBound := depth_le_of_premiseEnough checkBound premise checked.1 first
      have listed := mem_premiseAtUsing_of_premiseValid relEnv language recursiveComplete premise first firstBound
      have restBound := depth_le_of_premisesEnough recursiveComplete checkBound (checked.2 _ listed) rest
      intro other member
      rcases List.mem_cons.mp member with rfl | member
      · exact firstBound
      · exact restBound other member

/-- **When the fuel is enough, no derivation is cut off.** -/
theorem depth_le_of_enough : ∀ {fuel : ℕ} {source target : Pattern} {witness : Witness},
    enough relEnv language fuel source = true → StepValid relEnv language source witness target → witness.depth ≤ fuel
  | 0, source, target, witness, checked, valid => by
    cases valid with
    | @rule _ index rule initial final witnesses found matched premises =>
      simp only [enough, List.all_eq_true, List.isEmpty_iff] at checked
      rw [checked rule (List.mem_of_getElem? found)] at matched
      cases matched
  | fuel + 1, source, target, witness, checked, valid => by
    cases valid with
    | @rule _ index rule initial final witnesses found matched premises =>
      simp only [enough, List.all_eq_true] at checked
      have premisesBound := depth_le_of_premisesEnough
        (fun valid bounded => mem_stepsAt_of_stepValid relEnv language valid bounded)
        (fun checked valid => depth_le_of_enough checked valid)
        (checked rule (List.mem_of_getElem? found) initial matched) premises
      simp only [Witness.depth]
      have := Witness.depthList_le_iff.mpr premisesBound
      omega

/-- **When the fuel is enough, the listing holds every step.** -/
theorem mem_stepsAt_of_enough {fuel : ℕ} {source target : Pattern} {witness : Witness}
    (checked : enough relEnv language fuel source = true) (valid : StepValid relEnv language source witness target) :
    (witness, target) ∈ stepsAt relEnv language fuel source :=
  mem_stepsAt_of_stepValid relEnv language valid (depth_le_of_enough checked valid)

/-- **A complete set of successors**: when the fuel is enough, the term steps exactly to the listed
targets. -/
theorem step_iff_mem_of_enough {fuel : ℕ} {source target : Pattern}
    (checked : enough relEnv language fuel source = true) :
    Step relEnv language source target ↔ target ∈ (stepsAt relEnv language fuel source).map (·.2) := by
  constructor
  · rintro ⟨witness, valid⟩
    exact List.mem_map.mpr ⟨(witness, target), mem_stepsAt_of_enough checked valid, rfl⟩
  · intro listed
    obtain ⟨⟨witness, _⟩, member, rfl⟩ := List.mem_map.mp listed
    exact ⟨witness, stepValid_of_mem_stepsAt relEnv language member⟩

end Mettapedia.OSLF.MeTTaIL.ReferenceStep

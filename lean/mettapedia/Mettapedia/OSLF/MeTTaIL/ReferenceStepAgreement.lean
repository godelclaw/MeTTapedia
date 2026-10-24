import Mettapedia.OSLF.MeTTaIL.ReferenceStep

/-!
# The least contextual relation is the reference relation on aligned languages

`ContextualStep` instantiates premise sources without shifting and reads capture depths from a rule's
left side only, and it never satisfies a quantified premise or a premise with local binders. The
reference relation shifts every value to the depth where it is used (`ReferenceStep`). The two agree
exactly when shifting changes nothing (`contextualStep_iff_step`). A language is aligned
(`ReferenceProfile`) when each of its rules has
- no quantified premise and no premise with local binders;
- no compound step source with a metavariable deeper than its capture depth;
- no metavariable bound by a premise used in the right side deeper than where the premise bound it.

The instantiation lemmas behind it:
- a step source that is a metavariable is stepped where it was captured, so its instantiation is the
  plain one (`applyBindingsScoped_inPlace_fvar`);
- a pattern whose metavariables sit no deeper than their capture depths is instantiated plainly
  (`applyBindingsScoped_eq_applyBindings_of_notDeeper`);
- adding binding sites after the left side changes nothing where the added names are used no deeper
  than they were bound (`applyBindingsScoped_sites_eq`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.ReferenceStep

open Syntax Match Engine ContextualStep ReflectiveCanonical ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars liftBVars_zero)

/-! ## Instantiation lemmas -/

/-- **A metavariable source is stepped where it was captured**, so it is instantiated without a shift. -/
theorem applyBindingsScoped_inPlace_fvar (sites : Pattern) (bindings : Bindings) (x : String) :
    applyBindingsScoped sites bindings (inPlaceDepth sites (.fvar x)) (.fvar x) = applyBindings bindings (.fvar x) := by
  simp only [applyBindingsScoped, applyBindings, inPlaceDepth]
  cases bindings.find? (fun entry => entry.1 == x) with
  | none => rfl
  | some entry =>
    cases captureDepth x 0 sites with
    | none => rfl
    | some depth => simp only [Option.getD_some, Nat.sub_self, liftBVars_zero]

mutual
/-- Every metavariable of a pattern sits no deeper than its capture depth in `sites`. -/
def notDeeper (sites : Pattern) : ℕ → Pattern → Bool
  | d, .fvar x =>
      match captureDepth x 0 sites with
      | some c => decide (d ≤ c)
      | none => true
  | _, .bvar _ => true
  | d, .apply _ arguments => notDeeperList sites d arguments
  | d, .lambda _ body => notDeeper sites (d + 1) body
  | d, .multiLambda n _ body => notDeeper sites (d + n) body
  | d, .subst body replacement => notDeeper sites (d + 1) body && notDeeper sites d replacement
  | d, .collection _ elements rest =>
      notDeeperList sites d elements &&
        (match rest with
          | some restVar =>
              match captureDepth restVar 0 sites with
              | some c => decide (d ≤ c)
              | none => true
          | none => true)

def notDeeperList (sites : Pattern) : ℕ → List Pattern → Bool
  | _, [] => true
  | d, pattern :: patterns => notDeeper sites d pattern && notDeeperList sites d patterns
end

mutual
/-- **A pattern no deeper than its capture depths is instantiated plainly.** -/
theorem applyBindingsScoped_eq_applyBindings_of_notDeeper (sites : Pattern) (bindings : Bindings) :
    ∀ (d : ℕ) (pattern : Pattern), notDeeper sites d pattern = true →
      applyBindingsScoped sites bindings d pattern = applyBindings bindings pattern
  | d, .fvar x, shallow => by
    simp only [applyBindingsScoped, applyBindings]
    cases bindings.find? (fun entry => entry.1 == x) with
    | none => rfl
    | some entry =>
      cases captured : captureDepth x 0 sites with
      | none => rfl
      | some depth =>
        simp only [notDeeper, captured, decide_eq_true_eq] at shallow
        simp only [Nat.sub_eq_zero_of_le shallow, liftBVars_zero]
  | _, .bvar _, _ => by simp only [applyBindingsScoped, applyBindings]
  | d, .apply _ arguments, shallow => by
    simp only [notDeeper] at shallow
    simp only [applyBindingsScoped, applyBindings,
      applyBindingsScopedList_eq_applyBindingsMap_of_notDeeper sites bindings d arguments shallow]
  | d, .lambda _ body, shallow => by
    simp only [notDeeper] at shallow
    simp only [applyBindingsScoped, applyBindings,
      applyBindingsScoped_eq_applyBindings_of_notDeeper sites bindings (d + 1) body shallow]
  | d, .multiLambda n _ body, shallow => by
    simp only [notDeeper] at shallow
    simp only [applyBindingsScoped, applyBindings,
      applyBindingsScoped_eq_applyBindings_of_notDeeper sites bindings (d + n) body shallow]
  | d, .subst body replacement, shallow => by
    simp only [notDeeper, Bool.and_eq_true] at shallow
    simp only [applyBindingsScoped, applyBindings,
      applyBindingsScoped_eq_applyBindings_of_notDeeper sites bindings (d + 1) body shallow.1,
      applyBindingsScoped_eq_applyBindings_of_notDeeper sites bindings d replacement shallow.2]
  | d, .collection kind elements rest, shallow => by
    simp only [notDeeper, Bool.and_eq_true] at shallow
    rw [applyBindings.eq_def]
    simp only [applyBindingsScoped,
      applyBindingsScopedList_eq_applyBindingsMap_of_notDeeper sites bindings d elements shallow.1]
    cases rest with
    | none => simp [restSplice]
    | some restVar =>
      simp only [restSplice]
      cases found : bindings.find? (fun entry => entry.1 == restVar) with
      | none => simp
      | some entry =>
        obtain ⟨entryName, entryValue⟩ := entry
        cases entryValue with
        | collection boundKind boundElements boundRest =>
          cases boundRest with
          | some _ => simp
          | none =>
            by_cases sameKind : boundKind = kind
            · subst sameKind
              cases captured : captureDepth restVar 0 sites with
              | none => simp
              | some depth =>
                have noShift : d - depth = 0 := by
                  simp only [captured, decide_eq_true_eq] at shallow
                  exact Nat.sub_eq_zero_of_le shallow.2
                simp [noShift, map_liftBVars_zero]
            · simp [sameKind]
        | _ => simp

theorem applyBindingsScopedList_eq_applyBindingsMap_of_notDeeper (sites : Pattern) (bindings : Bindings) :
    ∀ (d : ℕ) (patterns : List Pattern), notDeeperList sites d patterns = true →
      applyBindingsScopedList sites bindings d patterns = patterns.map (applyBindings bindings)
  | _, [], _ => rfl
  | d, pattern :: patterns, shallow => by
    simp only [notDeeperList, Bool.and_eq_true] at shallow
    simp only [applyBindingsScopedList, List.map_cons,
      applyBindingsScoped_eq_applyBindings_of_notDeeper sites bindings d pattern shallow.1,
      applyBindingsScopedList_eq_applyBindingsMap_of_notDeeper sites bindings d patterns shallow.2]
end

/-! ## The sites a rule adds after its left side -/

/-- The binding sites a rule adds after its left side. -/
def extraSites (rule : RewriteRule) : List Pattern :=
  (rule.premises.foldl (fun sites premise => sites ++ premiseSites sites premise) [rule.left]).tail

theorem foldl_sites_head (lhs : Pattern) :
    ∀ (premises : List Premise) (rest : List Pattern), ∃ tail,
      premises.foldl (fun sites premise => sites ++ premiseSites sites premise) (lhs :: rest) = lhs :: tail
  | [], rest => ⟨rest, rfl⟩
  | premise :: premises, rest => by
    simp only [List.foldl_cons, List.cons_append]
    exact foldl_sites_head lhs premises _

/-- **A rule's capture sites are its left side, then the sites its premises add.** -/
theorem captureSites_eq (rule : RewriteRule) : captureSites rule = .apply "" (rule.left :: extraSites rule) := by
  obtain ⟨tail, folded⟩ := foldl_sites_head rule.left rule.premises []
  simp only [captureSites, captureSitesOf, extraSites, folded, List.tail_cons]

theorem captureDepth_sites (lhs : Pattern) (extra : List Pattern) (name : String) :
    captureDepth name 0 (.apply "" (lhs :: extra)) = (captureDepth name 0 lhs).or (captureDepthList name 0 extra) := by
  simp only [captureDepth, captureDepthList]
  cases captureDepth name 0 lhs <;> rfl

mutual
/-- Every metavariable that the left side does not bind, but the extra sites do, occurs no deeper than
the extra sites bind it. -/
def extraNotDeeper (lhs : Pattern) (extra : List Pattern) : ℕ → Pattern → Bool
  | d, .fvar x =>
      match captureDepth x 0 lhs with
      | some _ => true
      | none =>
          match captureDepthList x 0 extra with
          | some c => decide (d ≤ c)
          | none => true
  | _, .bvar _ => true
  | d, .apply _ arguments => extraNotDeeperList lhs extra d arguments
  | d, .lambda _ body => extraNotDeeper lhs extra (d + 1) body
  | d, .multiLambda n _ body => extraNotDeeper lhs extra (d + n) body
  | d, .subst body replacement => extraNotDeeper lhs extra (d + 1) body && extraNotDeeper lhs extra d replacement
  | d, .collection _ elements rest =>
      extraNotDeeperList lhs extra d elements &&
        (match rest with
          | some restVar =>
              match captureDepth restVar 0 lhs with
              | some _ => true
              | none =>
                  match captureDepthList restVar 0 extra with
                  | some c => decide (d ≤ c)
                  | none => true
          | none => true)

def extraNotDeeperList (lhs : Pattern) (extra : List Pattern) : ℕ → List Pattern → Bool
  | _, [] => true
  | d, pattern :: patterns => extraNotDeeper lhs extra d pattern && extraNotDeeperList lhs extra d patterns
end

/-- The shift the scoped instantiation applies is unchanged by extra sites where they bind no deeper
than the use. -/
theorem shift_sites_eq (lhs : Pattern) (extra : List Pattern) (name : String) (d : ℕ) (value : Pattern)
    (shallow : (match captureDepth name 0 lhs with
      | some _ => true
      | none => match captureDepthList name 0 extra with
        | some c => decide (d ≤ c)
        | none => true) = true) :
    (match captureDepth name 0 (.apply "" (lhs :: extra)) with
      | some dc => liftBVars 0 (d - dc) value
      | none => value) =
    (match captureDepth name 0 lhs with
      | some dc => liftBVars 0 (d - dc) value
      | none => value) := by
  rw [captureDepth_sites]
  cases lhsDepth : captureDepth name 0 lhs with
  | some depth => rfl
  | none =>
    simp only [lhsDepth] at shallow
    cases extraDepth : captureDepthList name 0 extra with
    | none => rfl
    | some depth =>
      simp only [extraDepth, decide_eq_true_eq] at shallow
      simp only [Option.none_or, Nat.sub_eq_zero_of_le shallow, liftBVars_zero]

mutual
/-- **Extra binding sites change nothing where their names are used no deeper than they were bound.** -/
theorem applyBindingsScoped_sites_eq (lhs : Pattern) (extra : List Pattern) (bindings : Bindings) :
    ∀ (d : ℕ) (pattern : Pattern), extraNotDeeper lhs extra d pattern = true →
      applyBindingsScoped (.apply "" (lhs :: extra)) bindings d pattern = applyBindingsScoped lhs bindings d pattern
  | d, .fvar x, shallow => by
    simp only [applyBindingsScoped]
    cases bindings.find? (fun entry => entry.1 == x) with
    | none => rfl
    | some entry =>
      simp only [extraNotDeeper] at shallow
      exact shift_sites_eq lhs extra x d entry.2 shallow
  | _, .bvar _, _ => by simp only [applyBindingsScoped]
  | d, .apply _ arguments, shallow => by
    simp only [extraNotDeeper] at shallow
    simp only [applyBindingsScoped, applyBindingsScopedList_sites_eq lhs extra bindings d arguments shallow]
  | d, .lambda _ body, shallow => by
    simp only [extraNotDeeper] at shallow
    simp only [applyBindingsScoped, applyBindingsScoped_sites_eq lhs extra bindings (d + 1) body shallow]
  | d, .multiLambda n _ body, shallow => by
    simp only [extraNotDeeper] at shallow
    simp only [applyBindingsScoped, applyBindingsScoped_sites_eq lhs extra bindings (d + n) body shallow]
  | d, .subst body replacement, shallow => by
    simp only [extraNotDeeper, Bool.and_eq_true] at shallow
    simp only [applyBindingsScoped, applyBindingsScoped_sites_eq lhs extra bindings (d + 1) body shallow.1,
      applyBindingsScoped_sites_eq lhs extra bindings d replacement shallow.2]
  | d, .collection kind elements rest, shallow => by
    simp only [extraNotDeeper, Bool.and_eq_true] at shallow
    simp only [applyBindingsScoped, applyBindingsScopedList_sites_eq lhs extra bindings d elements shallow.1]
    cases rest with
    | none => simp [restSplice]
    | some restVar =>
      simp only [restSplice]
      cases found : bindings.find? (fun entry => entry.1 == restVar) with
      | none => rfl
      | some entry =>
        obtain ⟨entryName, entryValue⟩ := entry
        cases entryValue with
        | collection boundKind boundElements boundRest =>
          cases boundRest with
          | some _ => rfl
          | none =>
            by_cases sameKind : boundKind = kind
            · subst sameKind
              simp only [beq_self_eq_true, ↓reduceIte]
              rw [captureDepth_sites]
              cases lhsDepth : captureDepth restVar 0 lhs with
              | some depth => rfl
              | none =>
                have shallowRest := shallow.2
                simp only [lhsDepth] at shallowRest
                cases extraDepth : captureDepthList restVar 0 extra with
                | none => rfl
                | some depth =>
                  simp only [extraDepth, decide_eq_true_eq] at shallowRest
                  simp [Nat.sub_eq_zero_of_le shallowRest, map_liftBVars_zero]
            · simp [sameKind]
        | _ => rfl

theorem applyBindingsScopedList_sites_eq (lhs : Pattern) (extra : List Pattern) (bindings : Bindings) :
    ∀ (d : ℕ) (patterns : List Pattern), extraNotDeeperList lhs extra d patterns = true →
      applyBindingsScopedList (.apply "" (lhs :: extra)) bindings d patterns =
        applyBindingsScopedList lhs bindings d patterns
  | _, [], _ => rfl
  | d, pattern :: patterns, shallow => by
    simp only [extraNotDeeperList, Bool.and_eq_true] at shallow
    simp only [applyBindingsScopedList, applyBindingsScoped_sites_eq lhs extra bindings d pattern shallow.1,
      applyBindingsScopedList_sites_eq lhs extra bindings d patterns shallow.2]
end

/-! ## Aligned languages -/

/-- A step source that both relations instantiate alike: a metavariable, or a pattern no deeper than
its capture depths. -/
def sourceAligned (sites : Pattern) : Pattern → Bool
  | .fvar _ => true
  | source => notDeeper sites 0 source

/-- A premise that both relations interpret alike. -/
def premiseAligned (sites : Pattern) : Premise → Bool
  | .forAll _ _ _ => false
  | .scopedStep premise => premise.binders.isEmpty && sourceAligned sites premise.source
  | .congruence source _ => sourceAligned sites source
  | _ => true

/-- **A rule that both relations interpret alike**: its premises are aligned, and the names its
premises bind are used in its right side no deeper than they were bound. -/
def ruleAligned (rule : RewriteRule) : Bool :=
  rule.premises.all (premiseAligned (captureSites rule)) && extraNotDeeper rule.left (extraSites rule) 0 rule.right

/-- **An aligned language**: every rule is aligned. -/
def ReferenceProfile (language : LanguageDef) : Prop := ∀ rule ∈ language.rewrites, ruleAligned rule = true

theorem inPlaceDepth_of_not_fvar (sites : Pattern) {source : Pattern} (notVar : ∀ x, source ≠ .fvar x) :
    inPlaceDepth sites source = 0 := by
  cases source with
  | fvar x => exact absurd rfl (notVar x)
  | _ => rfl

theorem sourceAligned_of_not_fvar {sites source : Pattern} (notVar : ∀ x, source ≠ .fvar x)
    (aligned : sourceAligned sites source = true) : notDeeper sites 0 source = true := by
  cases source with
  | fvar x => exact absurd rfl (notVar x)
  | _ => exact aligned

/-- An aligned source is instantiated plainly at its in-place depth. -/
theorem instantiate_inPlace (sites : Pattern) (bindings : Bindings) {source : Pattern}
    (aligned : sourceAligned sites source = true) :
    applyBindingsScoped sites bindings (inPlaceDepth sites source) source = applyBindings bindings source := by
  by_cases isVar : ∃ x, source = .fvar x
  · obtain ⟨x, rfl⟩ := isVar
    exact applyBindingsScoped_inPlace_fvar sites bindings x
  · have notVar : ∀ x, source ≠ .fvar x := fun x equal => isVar ⟨x, equal⟩
    rw [inPlaceDepth_of_not_fvar sites notVar]
    exact applyBindingsScoped_eq_applyBindings_of_notDeeper sites bindings 0 source
      (sourceAligned_of_not_fvar notVar aligned)

/-- **An aligned step premise's source is instantiated plainly.** -/
theorem instantiate_source (sites : Pattern) (bindings : Bindings) {premise : Premise} {source target : Pattern}
    (aligned : premiseAligned sites premise = true) (endpoints : stepEndpoints premise = some (source, target)) :
    applyBindingsScoped sites bindings (stepDepth sites premise) source = applyBindings bindings source := by
  cases premise with
  | congruence premiseSource premiseTarget =>
    simp only [stepEndpoints, Option.some.injEq, Prod.mk.injEq] at endpoints
    obtain ⟨rfl, rfl⟩ := endpoints
    exact instantiate_inPlace sites bindings aligned
  | scopedStep scopedPremise =>
    simp only [stepEndpoints, Option.some.injEq, Prod.mk.injEq] at endpoints
    obtain ⟨rfl, rfl⟩ := endpoints
    simp only [premiseAligned, Bool.and_eq_true, List.isEmpty_iff] at aligned
    simp only [stepDepth, aligned.1, List.length_nil, Nat.zero_max]
    exact instantiate_inPlace sites bindings aligned.2
  | freshness _ => simp [stepEndpoints] at endpoints
  | relationQuery _ _ => simp [stepEndpoints] at endpoints
  | forAll _ _ _ => simp [stepEndpoints] at endpoints

/-- **An aligned rule's right side is instantiated as the least contextual relation does.** -/
theorem instantiate_right (language : LanguageDef) {rule : RewriteRule} (bindings : Bindings)
    (aligned : ruleAligned rule = true) :
    applyBindingsScoped (captureSites rule) bindings 0 rule.right = applyBindingsForRule language rule bindings := by
  simp only [ruleAligned, Bool.and_eq_true] at aligned
  rw [captureSites_eq, applyBindingsScoped_sites_eq rule.left (extraSites rule) bindings 0 rule.right aligned.2,
    applyBindingsForRule_eq_syntactic]
  rfl

/-! ## Agreement -/

variable (relEnv : RelationEnv) (language : LanguageDef)

mutual
/-- **On an aligned language, a derivation of bounded depth has a witness.** -/
theorem stepValid_of_stepAt (profile : ReferenceProfile language) : ∀ {fuel : ℕ} {source target : Pattern},
    StepAt (engineBasePremises relEnv) language fuel source target →
      ∃ witness, StepValid relEnv language source witness target
  | 0, _, _, step => by cases step
  | fuel + 1, _, _, step => by
    cases step with
    | @rule _ _ _ rule _ _ member matched premises targetEq =>
      have ruleOk := profile rule member
      have premisesAligned : ∀ premise ∈ rule.premises, premiseAligned (captureSites rule) premise = true := by
        simp only [ruleAligned, Bool.and_eq_true, List.all_eq_true] at ruleOk
        exact ruleOk.1
      obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
      obtain ⟨witnesses, valid⟩ := premisesValid_of_premisesAt profile premisesAligned premises
      subst targetEq
      rw [← instantiate_right language _ ruleOk]
      exact ⟨.rule index _ witnesses, StepValid.rule found matched valid⟩
termination_by fuel => (fuel, 0)

/-- **On an aligned language, premise derivations of bounded depth have witnesses**, at any binding
sites the premises are aligned with. -/
theorem premisesValid_of_premisesAt (profile : ReferenceProfile language) {fuel : ℕ} {sites : Pattern} :
    ∀ {premises : List Premise} {initial final : Bindings},
      (∀ premise ∈ premises, premiseAligned sites premise = true) →
      PremisesAt (engineBasePremises relEnv) language fuel initial premises final →
        ∃ witnesses, PremisesValid relEnv language sites initial premises witnesses final
  | [], _, _, _, evidence => by
    cases evidence
    exact ⟨[], .nil _⟩
  | premise :: premises, _, _, aligned, evidence => by
    cases evidence with
    | cons first rest =>
      obtain ⟨witness, valid⟩ := premiseValid_of_premiseAt profile (aligned premise List.mem_cons_self) first
      obtain ⟨witnesses, restValid⟩ :=
        premisesValid_of_premisesAt profile (fun other member => aligned other (List.mem_cons_of_mem _ member)) rest
      exact ⟨witness :: witnesses, .cons valid restValid⟩
termination_by premises => (fuel, 2 + premises.length)

/-- **On an aligned language, a premise derivation of bounded depth has a witness.** -/
theorem premiseValid_of_premiseAt (profile : ReferenceProfile language) {fuel : ℕ} {sites : Pattern}
    {initial final : Bindings} {premise : Premise} (aligned : premiseAligned sites premise = true)
    (evidence : PremiseAt (engineBasePremises relEnv) language fuel initial premise final) :
    ∃ witness, PremiseValid relEnv language sites initial premise witness final := by
  cases evidence with
  | freshness member => exact ⟨.base _, .base rfl member⟩
  | relationQuery member => exact ⟨.base _, .base rfl member⟩
  | forAll member => simp [engineBasePremises, premiseStepWithEnv] at member
  | congruence stepped matchedMember merged =>
    rw [← instantiate_source sites initial aligned rfl] at stepped
    obtain ⟨witness, valid⟩ := stepValid_of_stepAt profile stepped
    exact ⟨.premiseStep witness _ _ _, .step rfl valid matchedMember merged⟩
  | scopedRoot empty stepped matchedMember merged =>
    rw [← instantiate_source sites initial aligned rfl] at stepped
    obtain ⟨witness, valid⟩ := stepValid_of_stepAt profile stepped
    exact ⟨.premiseStep witness _ _ _, .step rfl valid matchedMember merged⟩
termination_by (fuel, 1)
end

mutual
/-- **On an aligned language, a witness is a derivation of bounded depth.** -/
theorem stepAt_of_stepValid (profile : ReferenceProfile language) : ∀ (witness : Witness) {source target : Pattern},
    StepValid relEnv language source witness target →
      ∃ fuel, StepAt (engineBasePremises relEnv) language fuel source target
  | .rule _ _ witnesses, _, _, valid => by
    cases valid with
    | @rule _ _ rule _ _ _ found matched premises =>
      have member := List.mem_of_getElem? found
      have ruleOk := profile rule member
      have premisesAligned : ∀ premise ∈ rule.premises, premiseAligned (captureSites rule) premise = true := by
        simp only [ruleAligned, Bool.and_eq_true, List.all_eq_true] at ruleOk
        exact ruleOk.1
      obtain ⟨fuel, evidence⟩ := premisesAt_of_premisesValid profile witnesses premisesAligned premises
      rw [instantiate_right language _ ruleOk]
      exact ⟨fuel + 1, .rule member matched evidence rfl⟩
  | .base _, _, _, valid => by cases valid
  | .premiseStep _ _ _ _, _, _, valid => by cases valid
  | .forAll _, _, _, valid => by cases valid

theorem premisesAt_of_premisesValid (profile : ReferenceProfile language) : ∀ (witnesses : List Witness)
    {sites : Pattern} {initial final : Bindings} {premises : List Premise},
    (∀ premise ∈ premises, premiseAligned sites premise = true) →
    PremisesValid relEnv language sites initial premises witnesses final →
      ∃ fuel, PremisesAt (engineBasePremises relEnv) language fuel initial premises final
  | [], _, _, _, _, _, valid => by
    cases valid
    exact ⟨0, .nil _⟩
  | witness :: witnesses, _, _, _, _, aligned, valid => by
    cases valid with
    | cons first rest =>
      obtain ⟨headFuel, head⟩ := premiseAt_of_premiseValid profile witness (aligned _ List.mem_cons_self) first
      obtain ⟨tailFuel, tail⟩ := premisesAt_of_premisesValid profile witnesses
        (fun premise member => aligned premise (List.mem_cons_of_mem _ member)) rest
      exact ⟨max headFuel tailFuel, .cons (head.mono_fuel (le_max_left _ _)) (tail.mono_fuel (le_max_right _ _))⟩

theorem premiseAt_of_premiseValid (profile : ReferenceProfile language) : ∀ (witness : Witness)
    {sites : Pattern} {initial final : Bindings} {premise : Premise},
    premiseAligned sites premise = true → PremiseValid relEnv language sites initial premise witness final →
      ∃ fuel, PremiseAt (engineBasePremises relEnv) language fuel initial premise final
  | .base _, _, _, _, premise, _, valid => by
    cases valid with
    | base baseCase member =>
      cases premise with
      | freshness condition => exact ⟨0, .freshness member⟩
      | relationQuery relation arguments => exact ⟨0, .relationQuery member⟩
      | congruence _ _ => simp [isBase] at baseCase
      | scopedStep _ => simp [isBase] at baseCase
      | forAll _ _ _ => simp [isBase] at baseCase
  | .premiseStep step _ _ _, sites, initial, _, premise, aligned, valid => by
    cases valid with
    | step endpoints stepped matchedMember merged =>
      rw [instantiate_source sites initial aligned endpoints] at stepped
      obtain ⟨fuel, evidence⟩ := stepAt_of_stepValid profile step stepped
      cases premise with
      | congruence premiseSource premiseTarget =>
        simp only [stepEndpoints, Option.some.injEq, Prod.mk.injEq] at endpoints
        obtain ⟨rfl, rfl⟩ := endpoints
        exact ⟨fuel, .congruence evidence matchedMember merged⟩
      | scopedStep scopedPremise =>
        simp only [stepEndpoints, Option.some.injEq, Prod.mk.injEq] at endpoints
        obtain ⟨rfl, rfl⟩ := endpoints
        simp only [premiseAligned, Bool.and_eq_true, List.isEmpty_iff] at aligned
        exact ⟨fuel, .scopedRoot aligned.1 evidence matchedMember merged⟩
      | freshness _ => simp [stepEndpoints] at endpoints
      | relationQuery _ _ => simp [stepEndpoints] at endpoints
      | forAll _ _ _ => simp [stepEndpoints] at endpoints
  | .rule _ _ _, _, _, _, _, _, valid => by cases valid
  | .forAll _, _, _, _, premise, aligned, valid => by
    cases valid
    simp [premiseAligned] at aligned
end

/-- **On an aligned language the least contextual relation is the reference relation.** -/
theorem contextualStep_iff_step (profile : ReferenceProfile language) {source target : Pattern} :
    ContextualStep.Step (engineBasePremises relEnv) language source target ↔ Step relEnv language source target := by
  constructor
  · rintro ⟨_, evidence⟩
    exact stepValid_of_stepAt relEnv language profile evidence
  · rintro ⟨witness, valid⟩
    exact stepAt_of_stepValid relEnv language profile witness valid

end Mettapedia.OSLF.MeTTaIL.ReferenceStep

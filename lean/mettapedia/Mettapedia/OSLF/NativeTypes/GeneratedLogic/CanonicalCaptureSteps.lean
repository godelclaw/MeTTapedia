import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalCaptureFreshness

/-!
# Step premises at set rules

A rule may step a member it captures: `{x, ...rest} ⇒ {y, ...rest} if x ⇒ y`. The premise steps the member as captured,
in the presentation the rule matched, and a member's step may fire only at some presentation of the member, one that
writes a copy of one of its own members. So the captures cannot all be canonical: the member the premise steps is
captured at a presentation listed for it, and the presentations of a state are listed to the state's height.

- **Heights** (`height_sortBags`): canonical forms keep the height of every term.
- **Larger bounds list more** (`BoundsLe`, `NestedElement.mono`, `capturePresentations_mono`).
- **Captured values are hereditary** (`captures_hereditary`).
- **A member step** (`MemberStep`): a rule's one premise steps, in place, a metavariable its left side captures as an
  element to a metavariable it does not capture.
- **The listed presentations** (`stepPresentations width depth`): the presentations of `capturePresentations` under
  `width` copies at each of the state's height and the rules' `depth` levels.
- **Every step is listed** (`step_listed`), by induction on the step's witness: a step from a hereditary presentation
  is matched, with the same labels and up to canonical form, by a step from a listed presentation of its canonical
  form. A member step's premise is matched first, at the member, and the match moves to a listed presentation that
  captures the member at the presentation where its matched step fires, and every other value canonically
  (`capture_transfer_with`).
- **Coherence** (`step_coherent`, `stepForms`): the front door's canonical forms for such set languages.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec (MatchRel MatchBagRel matchPattern_iff_matchRel)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (canon Same arrange arrange_mem canon_idempotent canon_apply canon_collection)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (matchPatternForRule matchPatternForRule_eq_syntactic)

variable {language : LanguageDef} {sort : String}

/-! ## Heights -/

theorem heightList_le : ∀ {values : List Pattern} {bound : ℕ}, (∀ value ∈ values, height value ≤ bound) →
    heightList values ≤ bound
  | [], _, _ => Nat.zero_le _
  | value :: values, _, each => by
    rw [heightList]
    exact max_le (each value List.mem_cons_self) (heightList_le fun other member => each other (List.mem_cons_of_mem _ member))

theorem heightList_congr {first second : List Pattern} (same : ∀ value, value ∈ first ↔ value ∈ second) :
    heightList first = heightList second :=
  le_antisymm (heightList_le fun value member => height_le_heightList ((same value).mp member))
    (heightList_le fun value member => height_le_heightList ((same value).mpr member))

theorem heightList_map {f : Pattern → Pattern} : ∀ {values : List Pattern},
    (∀ value ∈ values, height (f value) = height value) → heightList (values.map f) = heightList values
  | [], _ => rfl
  | value :: values, keeps => by
    rw [List.map_cons, heightList, heightList, keeps value List.mem_cons_self,
      heightList_map fun other member => keeps other (List.mem_cons_of_mem _ member)]

theorem height_set (values : List Pattern) : height (set values) = heightList values + 1 := by
  rw [set, height]

theorem height_lt_of_mem_set {values : List Pattern} {value : Pattern} (member : value ∈ values) :
    height value < height (set values) := by
  rw [height_set]
  exact Nat.lt_succ_of_le (height_le_heightList member)

/-- **Canonical forms keep the height** of every term. -/
theorem height_canon (term : Pattern) : height (canon term) = height term := by
  induction term using Pattern.inductionOn with
  | hbvar => simp [canon, height]
  | hfvar => simp [canon, height]
  | happly label arguments _ =>
    rw [canon_apply]
    simp [height]
  | hlambda => simp [canon, height]
  | hmultiLambda => simp [canon, height]
  | hsubst => simp [canon, height]
  | hcollection kind elements rest recurse =>
    rw [canon_collection, height, height, heightList_congr fun value => arrange_mem value, heightList_map recurse]

theorem height_sortBags (term : Pattern) : height (BagForms.sortBags term) = height term := by
  rw [BagForms.sortBags_eq_canon]
  exact height_canon term

/-! ## Larger bounds list more -/

/-- **Bounds at least as large, depth by depth, and at least as deep.** -/
def BoundsLe : List ℕ → List ℕ → Prop
  | [], _ => True
  | _ :: _, [] => False
  | bound :: bounds, bound' :: bounds' => bound ≤ bound' ∧ BoundsLe bounds bounds'

/-- One width at as many depths as some bounds have, each at least the width, is below them. -/
theorem boundsLe_replicate {width : ℕ} : ∀ {depth : ℕ} {bounds : List ℕ}, depth ≤ bounds.length →
    (∀ bound ∈ bounds, width ≤ bound) → BoundsLe (List.replicate depth width) bounds
  | 0, _, _, _ => trivial
  | _ + 1, [], deep, _ => absurd deep (by simp)
  | _ + 1, bound :: bounds, deep, wide =>
    ⟨wide bound List.mem_cons_self,
      boundsLe_replicate (by simpa using deep) fun other member => wide other (List.mem_cons_of_mem _ member)⟩

theorem NestedElement.mono {bounds : List ℕ} {pattern : Pattern} (element : NestedElement language sort bounds pattern) :
    ∀ {bounds' : List ℕ}, BoundsLe bounds bounds' → NestedElement language sort bounds' pattern := by
  induction element with
  | var _ name => exact fun _ => .var _ name
  | closed _ holds canonical => exact fun _ => .closed _ holds canonical
  | set short _ recurse =>
    intro bounds' larger
    match bounds', larger with
    | _ :: _, ⟨wider, deeper⟩ => exact .set (short.trans wider) fun element member => recurse element member deeper

theorem mem_listsUpTo_inv {items members : List Pattern} {bound : ℕ} (listed : members ∈ listsUpTo items bound) :
    members.length ≤ bound ∧ ∀ member ∈ members, member ∈ items := by
  obtain ⟨length, lengthMember, inside⟩ := List.mem_flatMap.mp listed
  obtain ⟨same, each⟩ := mem_listsOf_inv inside
  rw [same]
  exact ⟨Nat.lt_succ_iff.mp (List.mem_range.mp lengthMember), each⟩

/-- What a presentation listed under bounds with an outermost bound is. -/
theorem mem_capturePresentations_cons {bound : ℕ} {bounds : List ℕ} {value shown : Pattern} :
    shown ∈ capturePresentations (bound :: bounds) value ↔ shown = value ∨ ∃ values,
      value = .collection .hashSet values none ∧
        shown ∈ ((listsUpTo (values.flatMap (capturePresentations bounds)) bound).flatMap fun partners =>
          values.sublists.map fun sub => Pattern.collection .hashSet (partners ++ arrange .hashSet sub) none).filter
            fun shown => decide (BagForms.sortBags shown = value) := by
  constructor
  · intro listed
    rcases List.mem_cons.mp listed with rfl | listed
    · exact Or.inl rfl
    · right
      split at listed
      · exact ⟨_, rfl, listed⟩
      · exact absurd listed List.not_mem_nil
  · rintro (rfl | ⟨values, rfl, listed⟩)
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ listed

/-- **Larger bounds list more presentations.** -/
theorem capturePresentations_mono : ∀ {bounds bounds' : List ℕ}, BoundsLe bounds bounds' → ∀ {value shown : Pattern},
    shown ∈ capturePresentations bounds value → shown ∈ capturePresentations bounds' value
  | [], _, _, _, _, listed => by
    rw [capturePresentations, List.mem_singleton] at listed
    subst listed
    exact self_mem_capturePresentations _ _
  | _ :: _, [], larger, _, _, _ => larger.elim
  | _ :: _, _ :: _, ⟨wider, deeper⟩, value, shown, listed => by
    rcases mem_capturePresentations_cons.mp listed with rfl | ⟨values, rfl, listed⟩
    · exact self_mem_capturePresentations _ _
    · refine mem_capturePresentations_cons.mpr (Or.inr ⟨values, rfl, ?_⟩)
      obtain ⟨inLists, presents⟩ := List.mem_filter.mp listed
      obtain ⟨partners, partnersListed, shownMember⟩ := List.mem_flatMap.mp inLists
      obtain ⟨short, inside⟩ := mem_listsUpTo_inv partnersListed
      refine List.mem_filter.mpr ⟨List.mem_flatMap.mpr ⟨partners, mem_listsUpTo (short.trans wider)
        fun partner member => ?_, shownMember⟩, presents⟩
      obtain ⟨original, originalMember, partnerListed⟩ := List.mem_flatMap.mp (inside partner member)
      exact List.mem_flatMap.mpr ⟨original, originalMember, capturePresentations_mono deeper partnerListed⟩

/-! ## Captured values are hereditary -/

theorem bag_captures_hereditary : ∀ {patterns : List Pattern} {rest : Option String} {terms : List Pattern}
    {bindings : Bindings}, MatchBagRel patterns rest .hashSet terms bindings →
    (∀ pattern ∈ patterns, ∀ {term : Pattern} {captured : Bindings}, Hereditary language sort term →
      MatchRel pattern term captured → ∀ entry ∈ captured, Hereditary language sort entry.2) →
    (∀ term ∈ terms, Hereditary language sort term) → ∀ entry ∈ bindings, Hereditary language sort entry.2
  | _, _, _, _, .nilNoRest, _, _, _, member => absurd member List.not_mem_nil
  | _, _, _, _, .nilRest, _, termsHold, entry, member => by
    rw [List.mem_singleton.mp member]
    exact .members termsHold
  | pattern :: _, _, _, _, .cons _ bound head tail merged, each, termsHold, entry, member => by
    rcases mem_of_mergeBindings _ _ merged entry member with inHead | inTail
    · exact each pattern List.mem_cons_self (termsHold _ (List.getElem_mem bound)) head entry inHead
    · exact bag_captures_hereditary tail (fun other inOther => each other (List.mem_cons_of_mem _ inOther))
        (fun other inOther => termsHold other (List.mem_of_mem_eraseIdx inOther)) entry inTail

/-- **A nested element pattern's match at a hereditary term captures hereditary values.** -/
theorem captures_hereditary {bounds : List ℕ} {pattern : Pattern} (element : NestedElement language sort bounds pattern) :
    ∀ {term : Pattern} {bindings : Bindings}, Hereditary language sort term → MatchRel pattern term bindings →
      ∀ entry ∈ bindings, Hereditary language sort entry.2 := by
  induction element with
  | var _ name =>
    intro term bindings termHolds matched entry member
    cases matched
    rw [List.mem_singleton.mp member]
    exact termHolds
  | closed _ holds canonical =>
    intro term bindings termHolds matched entry member
    obtain ⟨-, rfl⟩ := closed_match holds canonical termHolds matched
    exact absurd member List.not_mem_nil
  | set _ _ recurse =>
    intro term bindings termHolds matched
    rcases termHolds.cases with ⟨label, rfl, -⟩ | ⟨terms, rfl, termsHold⟩
    · cases matched
    · cases matched with
      | collection _ bag =>
        exact bag_captures_hereditary bag (fun other member _ _ held matchedOther => recurse other member held matchedOther)
          termsHold

/-! ## Member steps -/

/-- **A rule whose one premise steps a member it captures**: the premise steps, in place, a metavariable the left side
captures as an element and not as a rest, to a metavariable the left side does not capture.
`{x, ...rest} ⇒ {y, ...rest} if x ⇒ y` is one. -/
structure MemberStep (rule : RewriteRule) (premise : Premise) (source target : String) : Prop where
  premises : rule.premises = [premise]
  endpoints : stepEndpoints premise = some (.fvar source, .fvar target)
  inPlace : stepDepth (captureSites rule) premise = 0
  element : source ∉ restNames rule.left
  fresh : target ∉ patternNames rule.left

/-- **A set language whose rules' premises hold at canonical captures or step a member**, its left sides nested
element patterns with at most `width` elements and rest at each of `depth` levels, with distinct names. -/
structure StepSetLanguage (relEnv : RelationEnv) (language : LanguageDef) (carrier : GrammarRule) (width depth : ℕ) :
    Prop where
  hereditary : HereditaryLanguage language carrier
  rules : ∀ rule ∈ language.rewrites, NestedElement language carrier.category (List.replicate depth width) rule.left ∧
    (patternNames rule.left).Nodup ∧
      (PremisesCanon relEnv language rule.premises ∨ ∃ premise source target, MemberStep rule premise source target)

/-- **The presentations listed to a state's height**: `width` copies at each of the state's height and the rules'
`depth` levels. -/
def stepPresentations (width depth : ℕ) (state : Pattern) : List Pattern :=
  capturePresentations (List.replicate (height state + depth) width) state

theorem isBase_of_endpoints {premise : Premise} {endpoints : Pattern × Pattern}
    (stepping : stepEndpoints premise = some endpoints) : isBase premise = false := by
  cases premise <;> simp_all [stepEndpoints, isBase]

theorem applyBindings_fvar_of_find? {bindings : Bindings} {name : String} {entry : String × Pattern}
    (found : bindings.find? (·.1 == name) = some entry) : applyBindings bindings (.fvar name) = entry.2 := by
  rw [BagForms.applyBindings_var]
  simp [Bindings.lookup, found]

theorem applyBindings_fvar_of_find?_none {bindings : Bindings} {name : String}
    (missing : bindings.find? (·.1 == name) = none) : applyBindings bindings (.fvar name) = .fvar name := by
  rw [BagForms.applyBindings_var]
  simp [Bindings.lookup, missing]

variable {relEnv : RelationEnv}

/-- **A member step fires at a moved match**: at captures alike to the original ones, where the member's step is
matched with the same labels and up to canonical form, the rule steps with the same labels to a contractum with the
same canonical form. -/
theorem memberStep_at {rule : RewriteRule} {premise : Premise} {source target : String}
    (step : MemberStep rule premise source target) {index : ℕ} (found : language.rewrites[index]? = some rule)
    {redex partner : Pattern} {initial initial' final matchedTarget : Bindings} {candidate candidate' : Pattern}
    {child child' : Witness} (matched : MatchRel rule.left redex initial) (matched' : MatchRel rule.left partner initial')
    (same : BagForms.BindingsSame initial initial') (targetMatched : matchedTarget ∈ matchPattern (.fvar target) candidate)
    (merged : mergeBindings initial matchedTarget = some final)
    (stepped : StepValid relEnv language (applyBindings initial' (.fvar source)) child' candidate')
    (sameCandidate : canon candidate' = canon candidate) (agree : ∀ label : StepLabel, label.admits child = label.admits child') :
    ∃ witness' contractum', StepValid relEnv language partner witness' contractum' ∧
      (∀ label : StepLabel,
        label.admits (.rule index initial [.premiseStep child candidate matchedTarget final]) = label.admits witness') ∧
      canon contractum' = canon (applyBindingsScoped (captureSites rule) final 0 rule.right) := by
  have targetIs : matchedTarget = [(target, candidate)] := by
    have := matchPattern_iff_matchRel.mp targetMatched
    cases this
    rfl
  subst targetIs
  obtain ⟨result, result', mergedAgain, merged', resultSame⟩ :=
    mergeBindings_disjoint [(target, candidate)] [(target, candidate')] initial initial' same
      (.cons ⟨rfl, sameCandidate.symm⟩ .nil)
      (fun captured member other otherMember sameName => step.fresh (by
        have named := captured_names matched captured member
        rw [List.mem_singleton.mp otherMember] at sameName
        rw [sameName] at named
        exact named))
      (List.nodup_singleton _)
  rw [merged] at mergedAgain
  cases mergedAgain
  have premiseValid : PremiseValid relEnv language (captureSites rule) initial' premise
      (.premiseStep child' candidate' [(target, candidate')] result') result' := by
    refine .step step.endpoints ?_ (matchPattern_iff_matchRel.mpr .fvar) merged'
    rw [step.inPlace, applyBindingsScoped_fvar_zero]
    exact stepped
  have premisesValid : PremisesValid relEnv language (captureSites rule) initial' rule.premises
      [.premiseStep child' candidate' [(target, candidate')] result'] result' := by
    rw [step.premises]
    exact .cons premiseValid (.nil _)
  have matchedFinal : initial' ∈ matchPatternForRule language rule partner := by
    rw [matchPatternForRule_eq_syntactic]
    exact matchPattern_iff_matchRel.mpr matched'
  refine ⟨_, _, .rule found matchedFinal premisesValid, fun label => ?_,
    (BagForms.applyBindingsScoped_same (captureSites rule) resultSame 0 rule.right).symm⟩
  cases label <;> simp [StepLabel.admits, ruleOf, premiseStepsList, premiseSteps, agree]

variable {carrier : GrammarRule} {width depth : ℕ}

/-- **Every step from a hereditary presentation is listed**, below a bound on the size of its witness. -/
theorem step_listed_below (lang : StepSetLanguage relEnv language carrier width depth) :
    ∀ (bound : ℕ) (witness : Witness), sizeOf witness < bound → ∀ {redex contractum : Pattern},
      StepValid relEnv language redex witness contractum → Hereditary language carrier.category redex →
      ∃ shown ∈ stepPresentations width depth (BagForms.sortBags redex), ∃ witness' contractum',
        StepValid relEnv language shown witness' contractum' ∧
          (∀ label : StepLabel, label.admits witness = label.admits witness') ∧ canon contractum' = canon contractum
  | 0, _, small, _, _, _, _ => absurd small (Nat.not_lt_zero _)
  | bound + 1, _, small, redex, _, valid, redexHolds => by
    cases valid with
    | @rule _ index rule initial final witnesses found matched premises =>
      obtain ⟨element, distinct, shape⟩ := lang.rules rule (List.mem_of_getElem? found)
      have wide : ∀ value ∈ List.replicate (height (BagForms.sortBags redex) + depth) width, width ≤ value :=
        fun value member => (List.eq_of_mem_replicate member).ge
      have element' := element.mono (boundsLe_replicate (by simp) wide)
      rw [matchPatternForRule_eq_syntactic] at matched
      have matchedRel := matchPattern_iff_matchRel.mp matched
      rcases shape with holdsCanon | ⟨premise, source, target, step⟩
      · obtain ⟨partner, listed, bindings', matched', same, canonicalValues⟩ :=
          capture_transfer element' redexHolds matchedRel distinct
        have bindingsIs := eq_canonBindings_of_same same canonicalValues
        obtain ⟨noSteps, witnesses', premises', noSteps'⟩ := holdsCanon premises
        rw [← bindingsIs] at premises'
        have matchedFinal : bindings' ∈ matchPatternForRule language rule partner := by
          rw [matchPatternForRule_eq_syntactic]
          exact matchPattern_iff_matchRel.mpr matched'
        exact ⟨partner, listed, .rule index bindings' witnesses',
          applyBindingsScoped (captureSites rule) (BagForms.canonBindings final) 0 rule.right,
          .rule found matchedFinal premises',
          fun label => BagForms.admits_rule label index _ _ (noSteps.trans noSteps'.symm),
          BagForms.applyBindingsScoped_same (captureSites rule) (BagForms.bindingsSame_canon final) 0 rule.right⟩
      · rw [step.premises] at premises
        cases premises with
        | cons head tail =>
          cases tail
          cases head with
          | base isBaseTrue _ =>
            rw [isBase_of_endpoints step.endpoints] at isBaseTrue
            cases isBaseTrue
          | forAll _ _ =>
            have endpoints := step.endpoints
            simp [stepEndpoints] at endpoints
          | @step _ _ matchedTarget _ _ childSource childTarget candidate child endpoints stepped targetMatched merged =>
            rw [step.endpoints] at endpoints
            cases endpoints
            rw [step.inPlace, applyBindingsScoped_fvar_zero] at stepped
            have childSmall : sizeOf child < bound := by
              simp only [Witness.rule.sizeOf_spec, Witness.premiseStep.sizeOf_spec, List.cons.sizeOf_spec,
                List.nil.sizeOf_spec] at small
              omega
            cases found? : initial.find? (·.1 == source) with
            | none =>
              obtain ⟨partner, listed, bindings', matched', same, -⟩ :=
                capture_transfer element' redexHolds matchedRel distinct
              have missing : bindings'.find? (·.1 == source) = none := by
                rcases BagForms.find?_same same source with ⟨-, missing⟩ | ⟨_, _, present, -⟩
                · exact missing
                · rw [found?] at present
                  cases present
              rw [applyBindings_fvar_of_find?_none found?] at stepped
              obtain ⟨witness', contractum', fired, agree, sameContractum⟩ :=
                memberStep_at step found matchedRel matched' same targetMatched merged
                  (by rw [applyBindings_fvar_of_find?_none missing]; exact stepped) rfl (fun _ => rfl)
              exact ⟨partner, listed, witness', contractum', fired, agree, sameContractum⟩
            | some entry =>
              rw [applyBindings_fvar_of_find? found?] at stepped
              have childHolds : Hereditary language carrier.category entry.2 :=
                captures_hereditary element' redexHolds matchedRel entry (List.mem_of_find?_eq_some found?)
              obtain ⟨shownChild, listedChild, child', candidate', stepped', agree, sameCandidate⟩ :=
                step_listed_below lang bound child childSmall stepped childHolds
              have childClass : BagForms.sortBags shownChild = BagForms.sortBags entry.2 :=
                capturePresentations_class (sortBags_idem entry.2) listedChild
              let pick : String → Pattern → Pattern := fun name value =>
                if name = source ∧ value = BagForms.sortBags entry.2 then shownChild else value
              have pickClass : ∀ name value, BagForms.sortBags value = value →
                  BagForms.sortBags (pick name value) = value := by
                intro name value canonical
                by_cases chosen : name = source ∧ value = BagForms.sortBags entry.2
                · simp only [pick, if_pos chosen]
                  rw [childClass, chosen.2]
                · simp only [pick, if_neg chosen]
                  exact canonical
              let extra : List ℕ → Pattern → Prop := fun bounds term =>
                height term + depth ≤ bounds.length ∧ ∀ bound ∈ bounds, width ≤ bound
              have picked : ∀ {bounds : List ℕ} {name : String} {term : Pattern},
                  IsObject term → extra bounds term →
                  pick name (BagForms.sortBags term) ∈ capturePresentations bounds (BagForms.sortBags term) := by
                intro bounds name term termHolds termExtra
                by_cases chosen : name = source ∧ BagForms.sortBags term = BagForms.sortBags entry.2
                · simp only [pick, if_pos chosen]
                  rw [chosen.2]
                  refine capturePresentations_mono (boundsLe_replicate ?_ termExtra.2) listedChild
                  have heights : height (BagForms.sortBags entry.2) = height term := by
                    rw [← chosen.2, height_sortBags]
                  rw [heights]
                  exact termExtra.1
                · simp only [pick, if_neg chosen]
                  exact self_mem_capturePresentations _ _
              have descend : ∀ {bound : ℕ} {bounds : List ℕ} {values : List Pattern}, extra (bound :: bounds) (set values) →
                  ∀ value ∈ values, extra bounds value := by
                intro bound bounds values holds value member
                have below := height_lt_of_mem_set member
                refine ⟨?_, fun other inBounds => holds.2 other (List.mem_cons_of_mem _ inBounds)⟩
                have := holds.1
                simp only [List.length_cons] at this
                omega
              have topExtra : extra (List.replicate (height (BagForms.sortBags redex) + depth) width) redex :=
                ⟨by rw [List.length_replicate, height_sortBags], wide⟩
              obtain ⟨partner, listed, bindings', matched', same, kept⟩ :=
                capture_transfer_with extra descend pick pickClass picked element' redexHolds.object topExtra matchedRel distinct
                  fun name isRest value => by
                    have other : name ≠ source := fun same' => step.element (same' ▸ isRest)
                    simp [pick, other]
              have movedChild : applyBindings bindings' (.fvar source) = shownChild := by
                rcases BagForms.find?_same same source with ⟨missing, -⟩ | ⟨first, second, present, present', -, sameValue⟩
                · rw [found?] at missing
                  cases missing
                · rw [found?] at present
                  cases present
                  rw [applyBindings_fvar_of_find? present', kept second (List.mem_of_find?_eq_some present')]
                  have named : second.1 = source := by simpa using List.find?_some present'
                  have sameClass : BagForms.sortBags second.2 = BagForms.sortBags entry.2 := by
                    rw [BagForms.sortBags_eq_canon]
                    exact sameValue.symm
                  simp [pick, named, sameClass]
              obtain ⟨witness', contractum', fired, agree', sameContractum⟩ :=
                memberStep_at step found matchedRel matched' same targetMatched merged
                  (by rw [movedChild]; exact stepped') sameCandidate agree
              exact ⟨partner, listed, witness', contractum', fired, agree', sameContractum⟩

/-- **Every step from a hereditary presentation is listed** at a presentation of its canonical form, to the state's
height, with the same labels and up to canonical form. -/
theorem step_listed (lang : StepSetLanguage relEnv language carrier width depth) {redex contractum : Pattern}
    {witness : Witness} (valid : StepValid relEnv language redex witness contractum)
    (redexHolds : Hereditary language carrier.category redex) :
    ∃ shown ∈ stepPresentations width depth (BagForms.sortBags redex), ∃ witness' contractum',
      StepValid relEnv language shown witness' contractum' ∧
        (∀ label : StepLabel, label.admits witness = label.admits witness') ∧ canon contractum' = canon contractum :=
  step_listed_below lang (sizeOf witness + 1) witness (Nat.lt_succ_self _) valid redexHolds

/-- **Coherence for set languages with member steps**: a step from any presentation of a canonical hereditary set is
matched, with the same labels and up to canonical form, by a step listed at a presentation to the state's height. -/
theorem step_coherent (lang : StepSetLanguage relEnv language carrier width depth) (fuel : ℕ) :
    Coherent relEnv language fuel BagForms.sortBags (hereditary language carrier.category)
      (stepPresentations width depth) := by
  intro state redex witness contractum _ admitted canonState complete before _ valid
  have canonical := hereditary_canonical (relEnv := relEnv) lang.hereditary
  have redexHolds : Hereditary language carrier.category redex :=
    (hereditary_iff _).mp (canonical.invariant admitted before)
  have redexCanon : BagForms.sortBags redex = state := ((canonical.same admitted before).symm).trans canonState
  obtain ⟨shown, listed, witness', contractum', fired, agree, same⟩ := step_listed lang valid redexHolds
  rw [redexCanon] at listed
  refine ⟨(witness', contractum'),
    mem_listedAt.mpr ⟨shown, listed, mem_stepsAt_of_enough (enoughAt_iff.mp complete _ listed) fired⟩, agree, ?_⟩
  rw [BagForms.sortBags_eq_canon]
  exact same

/-- **Canonical forms for a set language with member steps**, for the front door. -/
def stepForms (lang : StepSetLanguage relEnv language carrier width depth) (fuel : ℕ) :
    CanonicalForms relEnv language fuel :=
  .ofCoherent (hereditary_canonical lang.hereditary) (step_coherent lang fuel)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

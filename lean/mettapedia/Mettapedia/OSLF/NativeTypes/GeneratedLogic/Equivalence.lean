import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Finite

/-!
# The equivalence native types induce

Native types tell two elements apart when some closed formula holds at one and fails at the other.
Which equivalence remains depends on the formers allowed.

- **All of Φ(L).** A language's states are equivalent exactly when they are equal modulo the language's
  equations (`agree_iff_objectEquivalent`), since a singleton type names each state. The same holds
  for the formulas the language generates, at well-sorted states (`generated_agree_iff_objectEquivalent`).
- **The behavioural fragment** (`Formula.behavioural`): steps forward and backward under labels, with
  `∧`, `∨`, μ and ν. It is closed under the dual, so it has negation for closed formulas.
  - Forward-backward bisimilar elements satisfy the same behavioural formulas, in every structure
    (`sat_of_bisimilar`), with the fixed points handled as in `Invariance`.
  - Conversely, on a structure with finitely many successors and predecessors under each label,
    elements that agree on every closed behavioural formula are bisimilar
    (`behaviourallyEquivalent_iff_bisimilar`). This is the Hennessy–Milner argument: a finite
    conjunction of distinguishing formulas under a modality.
- **Between the two.** Bisimilarity identifies elements that equality modulo the equations separates.
  Past steps separate elements that forward bisimilarity identifies. Both are in `EquivalenceControls`.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax

universe u

namespace Formula

/-- **The behavioural fragment**: steps forward and backward, with `∧`, `∨`, μ and ν. -/
def behavioural : {n : ℕ} → Formula n → Bool
  | _, .top | _, .bot | _, .var _ => true
  | _, .and left right | _, .or left right => behavioural left && behavioural right
  | _, .mu inner | _, .nu inner => behavioural inner
  | _, .possibly _ formula | _, .necessarily _ formula | _, .sometimeBefore _ formula
  | _, .alwaysBefore _ formula => behavioural formula
  | _, _ => false

theorem behavioural_dual : ∀ {n : ℕ} (formula : Formula n), (dual formula).behavioural = formula.behavioural
  | _, .top | _, .bot | _, .var _ | _, .empty _ | _, .nonEmpty _ | _, .bound _ | _, .notBound _
  | _, .typed _ | _, .untyped _ | _, .is _ | _, .isNot _ | _, .mapsAll _ _ | _, .mapsSome _ _
  | _, .split _ _ _ | _, .everySplit _ _ _ | _, .single _ _ | _, .everySingle _ _ | _, .body _
  | _, .everyBody _ | _, .multiBody _ _ | _, .everyMultiBody _ _ | _, .someOf _ _ | _, .everyOf _ _
  | _, .built _ _ | _, .everyBuilt _ _ | _, .atLeast _ _ _ _ | _, .allButFewer _ _ _ _ => by
    simp [dual, behavioural]
  | _, .and left right | _, .or left right => by
    simp only [dual, behavioural, behavioural_dual left, behavioural_dual right]
  | _, .mu inner | _, .nu inner => by simp only [dual, behavioural, behavioural_dual inner]
  | _, .possibly _ formula | _, .necessarily _ formula | _, .sometimeBefore _ formula
  | _, .alwaysBefore _ formula => by simp only [dual, behavioural, behavioural_dual formula]

/-- A finite conjunction. -/
def conj {n : ℕ} (formulas : List (Formula n)) : Formula n := formulas.foldr .and .top

theorem behavioural_conj {n : ℕ} : ∀ formulas : List (Formula n), (∀ formula ∈ formulas, formula.behavioural = true) →
    (conj formulas).behavioural = true
  | [], _ => rfl
  | formula :: formulas, every => by
    simp only [conj, List.foldr_cons, behavioural, Bool.and_eq_true]
    exact ⟨every formula (List.mem_cons_self ..),
      behavioural_conj formulas fun other member => every other (List.mem_cons_of_mem _ member)⟩

end Formula

namespace NativeStructure

variable {Carrier : Type u} (S : NativeStructure Carrier)

theorem sat_conj {n : ℕ} (env : Env Carrier n) (element : Carrier) :
    ∀ formulas : List (Formula n), S.sat env (Formula.conj formulas) element ↔ ∀ formula ∈ formulas, S.sat env formula element
  | [] => by simp [Formula.conj, sat]
  | formula :: formulas => by
    simp only [Formula.conj, List.foldr_cons, sat, List.mem_cons, forall_eq_or_imp]
    exact and_congr Iff.rfl (sat_conj env element formulas)

/-! ## Bisimulation -/

/-- **A forward-backward bisimulation**: related elements match each other's steps under every label,
forward and backward, into related elements. -/
structure Bisimulation (relation : Carrier → Carrier → Prop) : Prop where
  forth : ∀ {first second label next}, relation first second → S.step first label next →
    ∃ next', S.step second label next' ∧ relation next next'
  back : ∀ {first second label next'}, relation first second → S.step second label next' →
    ∃ next, S.step first label next ∧ relation next next'
  pastForth : ∀ {first second label previous}, relation first second → S.step previous label first →
    ∃ previous', S.step previous' label second ∧ relation previous previous'
  pastBack : ∀ {first second label previous'}, relation first second → S.step previous' label second →
    ∃ previous, S.step previous label first ∧ relation previous previous'

/-- **Bisimilarity**: related by some forward-backward bisimulation. -/
def Bisimilar (first second : Carrier) : Prop := ∃ relation, S.Bisimulation relation ∧ relation first second

theorem bisimulation_bisimilar : S.Bisimulation S.Bisimilar where
  forth := by
    rintro first second label next ⟨relation, bisimulation, related⟩ step
    obtain ⟨next', step', relatedNext⟩ := bisimulation.forth related step
    exact ⟨next', step', relation, bisimulation, relatedNext⟩
  back := by
    rintro first second label next' ⟨relation, bisimulation, related⟩ step
    obtain ⟨next, step', relatedNext⟩ := bisimulation.back related step
    exact ⟨next, step', relation, bisimulation, relatedNext⟩
  pastForth := by
    rintro first second label previous ⟨relation, bisimulation, related⟩ step
    obtain ⟨previous', step', relatedPrevious⟩ := bisimulation.pastForth related step
    exact ⟨previous', step', relation, bisimulation, relatedPrevious⟩
  pastBack := by
    rintro first second label previous' ⟨relation, bisimulation, related⟩ step
    obtain ⟨previous, step', relatedPrevious⟩ := bisimulation.pastBack related step
    exact ⟨previous, step', relation, bisimulation, relatedPrevious⟩

/-- **Bisimilarity is an equivalence.** -/
theorem bisimilar_equivalence : Equivalence S.Bisimilar where
  refl element := ⟨Eq, {
    forth := fun related step => ⟨_, related ▸ step, rfl⟩
    back := fun related step => ⟨_, related ▸ step, rfl⟩
    pastForth := fun related step => ⟨_, related ▸ step, rfl⟩
    pastBack := fun related step => ⟨_, related ▸ step, rfl⟩ }, rfl⟩
  symm := by
    rintro first second ⟨relation, bisimulation, related⟩
    refine ⟨fun left right => relation right left, ⟨?_, ?_, ?_, ?_⟩, related⟩
    · intro first second label next related step
      exact bisimulation.back related step
    · intro first second label next' related step
      exact bisimulation.forth related step
    · intro first second label previous related step
      exact bisimulation.pastBack related step
    · intro first second label previous' related step
      exact bisimulation.pastForth related step
  trans := by
    rintro first second third ⟨relation, bisimulation, related⟩ ⟨relation', bisimulation', related'⟩
    refine ⟨fun left right => ∃ middle, relation left middle ∧ relation' middle right, ⟨?_, ?_, ?_, ?_⟩,
      second, related, related'⟩
    · rintro first third label next ⟨middle, left, right⟩ step
      obtain ⟨next', step', relatedNext⟩ := bisimulation.forth left step
      obtain ⟨next'', step'', relatedNext'⟩ := bisimulation'.forth right step'
      exact ⟨next'', step'', next', relatedNext, relatedNext'⟩
    · rintro first third label next'' ⟨middle, left, right⟩ step
      obtain ⟨next', step', relatedNext'⟩ := bisimulation'.back right step
      obtain ⟨next, stepFirst, relatedNext⟩ := bisimulation.back left step'
      exact ⟨next, stepFirst, next', relatedNext, relatedNext'⟩
    · rintro first third label previous ⟨middle, left, right⟩ step
      obtain ⟨previous', step', relatedPrevious⟩ := bisimulation.pastForth left step
      obtain ⟨previous'', step'', relatedPrevious'⟩ := bisimulation'.pastForth right step'
      exact ⟨previous'', step'', previous', relatedPrevious, relatedPrevious'⟩
    · rintro first third label previous'' ⟨middle, left, right⟩ step
      obtain ⟨previous', step', relatedPrevious'⟩ := bisimulation'.pastBack right step
      obtain ⟨previous, stepFirst, relatedPrevious⟩ := bisimulation.pastBack left step'
      exact ⟨previous, stepFirst, previous', relatedPrevious, relatedPrevious'⟩

/-! ## Bisimilar elements satisfy the same behavioural formulas -/

variable {S}

/-- **Behavioural formulas hold alike at bisimilar elements**, in environments closed under
bisimilarity. -/
theorem sat_of_bisimilar : ∀ {n : ℕ} (formula : Formula n), formula.behavioural = true →
    ∀ {env : Env Carrier n}, env.Respects S.Bisimilar → ∀ {first second : Carrier}, S.Bisimilar first second →
      S.sat env formula first → S.sat env formula second
  | _, .top, _, _, _, _, _, _, _ => trivial
  | _, .bot, _, _, _, _, _, _, holds => holds
  | _, .and left right, behavioural, _, respects, _, _, related, holds => by
    simp only [Formula.behavioural, Bool.and_eq_true] at behavioural
    exact ⟨sat_of_bisimilar left behavioural.1 respects related holds.1,
      sat_of_bisimilar right behavioural.2 respects related holds.2⟩
  | _, .or left right, behavioural, _, respects, _, _, related, holds => by
    simp only [Formula.behavioural, Bool.and_eq_true] at behavioural
    exact holds.imp (sat_of_bisimilar left behavioural.1 respects related)
      (sat_of_bisimilar right behavioural.2 respects related)
  | _, .var index, _, _, respects, first, second, related, holds => respects index first second related holds
  | _, .mu inner, behavioural, env, respects, first, second, related, holds => by
    intro closed closedHolds
    let interior : Set Carrier := {element | ∀ other, S.Bisimilar element other → other ∈ closed}
    have interiorRespects : ∀ a b, S.Bisimilar a b → a ∈ interior → b ∈ interior :=
      fun a b ab member other bOther => member other ((S.bisimilar_equivalence).trans ab bOther)
    have inside : interior ⊆ closed := fun element member => member element (S.bisimilar_equivalence.refl element)
    have interiorHolds := holds interior fun element elementHolds other related' =>
      closedHolds other (S.sat_mono inner (env.extend_sub inside) other
        (sat_of_bisimilar inner behavioural (respects.extend interiorRespects) related' elementHolds))
    exact interiorHolds second related
  | _, .nu inner, behavioural, env, respects, first, second, related, holds => by
    obtain ⟨invariant, member, preserved⟩ := holds
    let closure : Set Carrier := {element | ∃ origin ∈ invariant, S.Bisimilar origin element}
    have closureRespects : ∀ a b, S.Bisimilar a b → a ∈ closure → b ∈ closure := by
      rintro a b ab ⟨origin, originMember, originA⟩
      exact ⟨origin, originMember, S.bisimilar_equivalence.trans originA ab⟩
    have contains : invariant ⊆ closure :=
      fun element member => ⟨element, member, S.bisimilar_equivalence.refl element⟩
    refine ⟨closure, ⟨first, member, related⟩, ?_⟩
    rintro element ⟨origin, originMember, originRelated⟩
    exact sat_of_bisimilar inner behavioural (respects.extend closureRespects) originRelated
      (S.sat_mono inner (env.extend_sub contains) origin (preserved origin originMember))
  | _, .possibly _ formula, behavioural, _, respects, _, _, related, holds => by
    obtain ⟨next, step, nextHolds⟩ := holds
    obtain ⟨next', step', relatedNext⟩ := S.bisimulation_bisimilar.forth related step
    exact ⟨next', step', sat_of_bisimilar formula behavioural respects relatedNext nextHolds⟩
  | _, .necessarily _ formula, behavioural, _, respects, _, _, related, holds => fun next' step' => by
    obtain ⟨next, step, relatedNext⟩ := S.bisimulation_bisimilar.back related step'
    exact sat_of_bisimilar formula behavioural respects relatedNext (holds next step)
  | _, .sometimeBefore _ formula, behavioural, _, respects, _, _, related, holds => by
    obtain ⟨previous, step, previousHolds⟩ := holds
    obtain ⟨previous', step', relatedPrevious⟩ := S.bisimulation_bisimilar.pastForth related step
    exact ⟨previous', step', sat_of_bisimilar formula behavioural respects relatedPrevious previousHolds⟩
  | _, .alwaysBefore _ formula, behavioural, _, respects, _, _, related, holds => fun previous' step' => by
    obtain ⟨previous, step, relatedPrevious⟩ := S.bisimulation_bisimilar.pastBack related step'
    exact sat_of_bisimilar formula behavioural respects relatedPrevious (holds previous step)
  | _, .built _ _, behavioural, _, _, _, _, _, _ | _, .everyBuilt _ _, behavioural, _, _, _, _, _, _
  | _, .split _ _ _, behavioural, _, _, _, _, _, _ | _, .everySplit _ _ _, behavioural, _, _, _, _, _, _
  | _, .empty _, behavioural, _, _, _, _, _, _ | _, .nonEmpty _, behavioural, _, _, _, _, _, _
  | _, .single _ _, behavioural, _, _, _, _, _, _ | _, .everySingle _ _, behavioural, _, _, _, _, _, _
  | _, .body _, behavioural, _, _, _, _, _, _ | _, .everyBody _, behavioural, _, _, _, _, _, _
  | _, .multiBody _ _, behavioural, _, _, _, _, _, _ | _, .everyMultiBody _ _, behavioural, _, _, _, _, _, _
  | _, .bound _, behavioural, _, _, _, _, _, _ | _, .notBound _, behavioural, _, _, _, _, _, _
  | _, .typed _, behavioural, _, _, _, _, _, _ | _, .untyped _, behavioural, _, _, _, _, _, _
  | _, .is _, behavioural, _, _, _, _, _, _ | _, .isNot _, behavioural, _, _, _, _, _, _
  | _, .mapsAll _ _, behavioural, _, _, _, _, _, _ | _, .mapsSome _ _, behavioural, _, _, _, _, _, _
  | _, .someOf _ _, behavioural, _, _, _, _, _, _ | _, .everyOf _ _, behavioural, _, _, _, _, _, _ => by
    simp [Formula.behavioural] at behavioural

/-! ## Separating formulas -/

variable (S)

/-- **Agreement on the closed formulas of a fragment.** -/
def AgreeOn (fragment : Formula 0 → Bool) (first second : Carrier) : Prop :=
  ∀ formula : Formula 0, fragment formula = true →
    (S.sat Env.closed formula first ↔ S.sat Env.closed formula second)

/-- **Finitely many successors and predecessors under each label.** -/
structure ImageFinite : Prop where
  successors : ∀ element label, ∃ list : List Carrier, ∀ next, S.step element label next ↔ next ∈ list
  predecessors : ∀ element label, ∃ list : List Carrier, ∀ previous, S.step previous label element ↔ previous ∈ list

end NativeStructure

/-- **A fragment closed under the dual**, with truth and finite conjunctions. -/
structure FragmentClosed (fragment : Formula 0 → Bool) : Prop where
  dual : ∀ formula, fragment formula.dual = fragment formula
  top : fragment .top = true
  conj : ∀ formulas : List (Formula 0), (∀ formula ∈ formulas, fragment formula = true) →
    fragment (Formula.conj formulas) = true

namespace NativeStructure

variable {Carrier : Type u} {S : NativeStructure Carrier} {fragment : Formula 0 → Bool}

theorem AgreeOn.symm {first second : Carrier} (agree : S.AgreeOn fragment first second) :
    S.AgreeOn fragment second first :=
  fun formula inFragment => (agree formula inFragment).symm

theorem AgreeOn.refl (element : Carrier) : S.AgreeOn fragment element element := fun _ _ => Iff.rfl

/-- Elements that disagree are told apart by a closed formula of the fragment that holds at the first. -/
theorem distinguish (closed : FragmentClosed fragment) {first second : Carrier}
    (differ : ¬ S.AgreeOn fragment first second) :
    ∃ formula : Formula 0, fragment formula = true ∧ S.sat Env.closed formula first ∧
      ¬ S.sat Env.closed formula second := by
  simp only [AgreeOn, not_forall] at differ
  obtain ⟨formula, inFragment, disagree⟩ := differ
  by_cases holds : S.sat Env.closed formula first
  · exact ⟨formula, inFragment, holds, fun holds' => disagree ⟨fun _ => holds', fun _ => holds⟩⟩
  · refine ⟨formula.dual, (closed.dual formula).trans inFragment, (S.sat_dual_closed formula first).mpr holds,
      fun dualHolds => ?_⟩
    have fails := (S.sat_dual_closed formula second).mp dualHolds
    exact disagree ⟨fun holds' => absurd holds' holds, fun holds' => absurd holds' fails⟩

variable (S) in
open Classical in
/-- A formula of the fragment that holds at the first element and fails at the second, when they
disagree. -/
noncomputable def separator (closed : FragmentClosed fragment) (first second : Carrier) : Formula 0 :=
  if differ : S.AgreeOn fragment first second then .top else Classical.choose (distinguish closed differ)

theorem separator_fragment (closed : FragmentClosed fragment) (first second : Carrier) :
    fragment (S.separator closed first second) = true := by
  unfold separator
  split
  · exact closed.top
  · rename_i differ
    exact (Classical.choose_spec (distinguish closed differ)).1

theorem separator_holds (closed : FragmentClosed fragment) (first second : Carrier) :
    S.sat Env.closed (S.separator closed first second) first := by
  unfold separator
  split
  · trivial
  · rename_i differ
    exact (Classical.choose_spec (distinguish closed differ)).2.1

theorem separator_fails (closed : FragmentClosed fragment) {first second : Carrier}
    (differ : ¬ S.AgreeOn fragment first second) : ¬ S.sat Env.closed (S.separator closed first second) second := by
  unfold separator
  rw [dif_neg differ]
  exact (Classical.choose_spec (distinguish closed differ)).2.2

/-- The conjunction of the separators from an element to each of a list holds at the element. -/
theorem separators_hold (closed : FragmentClosed fragment) (first : Carrier) (others : List Carrier) :
    S.sat Env.closed (Formula.conj (others.map (S.separator closed first))) first := by
  refine (S.sat_conj _ _ _).mpr fun formula member => ?_
  obtain ⟨other, -, rfl⟩ := List.mem_map.mp member
  exact separator_holds closed first other

theorem separators_fragment (closed : FragmentClosed fragment) (first : Carrier) (others : List Carrier) :
    fragment (Formula.conj (others.map (S.separator closed first))) = true :=
  closed.conj _ fun formula member => by
    obtain ⟨other, -, rfl⟩ := List.mem_map.mp member
    exact separator_fragment closed first other

/-- **The Hennessy–Milner step**, for any relation with finitely many successors that a former of the
fragment reads existentially: what the first element reaches is matched by something the second
reaches that agrees with it. Otherwise the conjunction of the separators from the first's successor to
each of the second's, under the former, holds at the first and fails at the second. -/
theorem match_of_agree (closed : FragmentClosed fragment) {relation : Carrier → Carrier → Prop}
    (finite : ∀ element, ∃ list : List Carrier, ∀ other, relation element other ↔ other ∈ list)
    {former : Formula 0 → Formula 0} (formerIn : ∀ formula, fragment formula = true → fragment (former formula) = true)
    (reads : ∀ formula element, S.sat Env.closed (former formula) element ↔
      ∃ other, relation element other ∧ S.sat Env.closed formula other)
    {first second next : Carrier} (agree : S.AgreeOn fragment first second) (related : relation first next) :
    ∃ next', relation second next' ∧ S.AgreeOn fragment next next' := by
  by_contra none
  push Not at none
  obtain ⟨list, listed⟩ := finite second
  let witness := former (Formula.conj (list.map (S.separator closed next)))
  have atFirst : S.sat Env.closed witness first :=
    (reads _ first).mpr ⟨next, related, separators_hold closed next list⟩
  obtain ⟨next', related', conjunction⟩ :=
    (reads _ second).mp ((agree witness (formerIn _ (separators_fragment closed next list))).mp atFirst)
  exact separator_fails closed (none next' related')
    ((S.sat_conj _ _ _).mp conjunction _ (List.mem_map.mpr ⟨next', (listed next').mp related', rfl⟩))

/-! ## Agreement on behavioural formulas is bisimilarity, for finitely branching structures -/

/-- The behavioural fragment, closed under the dual. -/
theorem behavioural_closed : FragmentClosed fun formula => formula.behavioural where
  dual := Formula.behavioural_dual
  top := rfl
  conj := Formula.behavioural_conj

variable (S) in
/-- **Agreement on every closed behavioural formula.** -/
abbrev BehaviourallyEquivalent : Carrier → Carrier → Prop := S.AgreeOn fun formula => formula.behavioural

/-- On a finitely branching structure, agreement on behavioural formulas is a bisimulation. -/
theorem bisimulation_behaviourallyEquivalent (finite : S.ImageFinite) : S.Bisimulation S.BehaviourallyEquivalent where
  forth := fun {_ _ label _} agree step =>
    match_of_agree behavioural_closed (relation := fun element next => S.step element label next)
      (fun element => finite.successors element label) (former := .possibly label) (fun _ inFragment => inFragment)
      (fun _ _ => Iff.rfl) agree step
  back := fun {_ _ label _} agree step => by
    obtain ⟨next, step', related⟩ := match_of_agree behavioural_closed
      (relation := fun element next => S.step element label next) (fun element => finite.successors element label)
      (former := .possibly label) (fun _ inFragment => inFragment) (fun _ _ => Iff.rfl) agree.symm step
    exact ⟨next, step', related.symm⟩
  pastForth := fun {_ _ label _} agree step =>
    match_of_agree behavioural_closed (relation := fun element previous => S.step previous label element)
      (fun element => finite.predecessors element label) (former := .sometimeBefore label)
      (fun _ inFragment => inFragment) (fun _ _ => Iff.rfl) agree step
  pastBack := fun {_ _ label _} agree step => by
    obtain ⟨previous, step', related⟩ := match_of_agree behavioural_closed
      (relation := fun element previous => S.step previous label element)
      (fun element => finite.predecessors element label) (former := .sometimeBefore label)
      (fun _ inFragment => inFragment) (fun _ _ => Iff.rfl) agree.symm step
    exact ⟨previous, step', related.symm⟩

/-- **The behavioural fragment induces bisimilarity**, on a structure with finitely many successors and
predecessors under each label. -/
theorem behaviourallyEquivalent_iff_bisimilar (finite : S.ImageFinite) {first second : Carrier} :
    S.BehaviourallyEquivalent first second ↔ S.Bisimilar first second :=
  ⟨fun agree => ⟨_, bisimulation_behaviourallyEquivalent finite, agree⟩,
    fun related formula behavioural =>
      ⟨sat_of_bisimilar formula behavioural (Env.respects_closed _) related,
        sat_of_bisimilar formula behavioural (Env.respects_closed _) (S.bisimilar_equivalence.symm related)⟩⟩

end NativeStructure

/-- **A finite structure is finitely branching.** -/
theorem FiniteStructure.imageFinite {Carrier : Type u} (F : FiniteStructure Carrier) : F.native.ImageFinite where
  successors element label := ⟨F.elements.filter (F.step element label ·), fun next => by
    simp [FiniteStructure.native, F.complete next]⟩
  predecessors element label := ⟨F.elements.filter (F.step · label element), fun previous => by
    simp [FiniteStructure.native, F.complete previous]⟩

/-! ## All of Φ(L) induces equality modulo the equations -/

open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.GSLT.LanguageDef.WellSorted (OpenPatternWellSorted FreeTypeContext)

/-- **A language's states agree on every closed formula exactly when they are equal modulo its
equations.** -/
theorem agree_iff_objectEquivalent (relEnv : RelationEnv) (language : LanguageDef) {first second : Pattern}
    (firstState : IsState first) (secondState : IsState second) :
    (∀ formula : Formula 0, (referenceStructure relEnv language).sat Env.closed formula first ↔
      (referenceStructure relEnv language).sat Env.closed formula second) ↔
        ObjectEquivalent relEnv language first second := by
  constructor
  · intro agree
    obtain ⟨-, equivalent⟩ := (agree (.is first)).mp ⟨firstState.2, Relation.EqvGen.refl _⟩
    exact ObjectEquivalent.equivalence.symm equivalent
  · intro equivalent formula
    exact sat_respects_equivalent relEnv language formula firstState secondState equivalent

/-- **The same for the formulas the language generates**, at well-sorted states: the singleton type of
a well-sorted state is generated. -/
theorem generated_agree_iff_objectEquivalent (relEnv : RelationEnv) (language : LanguageDef) {first second : Pattern}
    (firstState : IsState first) (secondState : IsState second)
    (wellSorted : ∃ type, OpenPatternWellSorted language FreeTypeContext.empty [] type first) :
    (∀ formula : Formula 0, GeneratedBy language formula →
      ((referenceStructure relEnv language).sat Env.closed formula first ↔
        (referenceStructure relEnv language).sat Env.closed formula second)) ↔
        ObjectEquivalent relEnv language first second := by
  constructor
  · intro agree
    obtain ⟨-, equivalent⟩ := (agree (.is first) wellSorted).mp ⟨firstState.2, Relation.EqvGen.refl _⟩
    exact ObjectEquivalent.equivalence.symm equivalent
  · intro equivalent formula _
    exact sat_respects_equivalent relEnv language formula firstState secondState equivalent

end Mettapedia.OSLF.NativeTypes.GeneratedLogic

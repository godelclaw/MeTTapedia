import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Equivalence
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Invariance

/-!
# Forward bisimilarity over a class of labels, and the formulas that characterize it

`Equivalence` characterizes forward-backward bisimilarity under every label, which needs finitely many predecessors
as well as successors. Some languages have one without the other: in ρ an output with an arbitrary payload steps to
the inert process, so the inert process has infinitely many predecessors even up to the equations. And a calculus is
often compared only under some labels, such as the contexts of a class.

- **The forward formulas over admitted labels** (`Formula.forwardOn`): `⊤`, `⊥`, `∧`, `∨`, and the step modalities
  forward under admitted labels. The fragment is closed under the dual.
- **Forward bisimilarity over admitted labels** (`ForwardBisimilar`): related elements match each other's steps under
  every admitted label, forward only.
- **Forward-bisimilar elements satisfy the same forward formulas**, in every structure (`sat_of_forwardBisimilar`).
- **Conversely, on a region closed under the admitted steps, with finitely many successors up to an equivalence the
  formulas respect, elements that agree on the forward formulas are forward bisimilar**
  (`agree_iff_forwardBisimilar`). Neither predecessors nor the non-admitted labels need be finite.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax

universe u

namespace Formula

/-- **The forward formulas over admitted labels**: steps forward under admitted labels, with `⊤`, `⊥`, `∧`, `∨`. -/
def forwardOn (admitted : StepLabel → Bool) : {n : ℕ} → Formula n → Bool
  | _, .top | _, .bot => true
  | _, .and left right | _, .or left right => forwardOn admitted left && forwardOn admitted right
  | _, .possibly label formula | _, .necessarily label formula => admitted label && forwardOn admitted formula
  | _, _ => false

theorem forwardOn_dual (admitted : StepLabel → Bool) :
    ∀ {n : ℕ} (formula : Formula n), (dual formula).forwardOn admitted = formula.forwardOn admitted
  | _, .top | _, .bot | _, .var _ | _, .empty _ | _, .nonEmpty _ | _, .bound _ | _, .notBound _
  | _, .typed _ | _, .untyped _ | _, .is _ | _, .isNot _ | _, .mapsAll _ _ | _, .mapsSome _ _
  | _, .inRelation _ | _, .notInRelation _
  | _, .split _ _ _ | _, .everySplit _ _ _ | _, .single _ _ | _, .everySingle _ _ | _, .body _
  | _, .everyBody _ | _, .multiBody _ _ | _, .everyMultiBody _ _ | _, .someOf _ _ | _, .everyOf _ _
  | _, .built _ _ | _, .everyBuilt _ _ | _, .atLeast _ _ _ _ | _, .allButFewer _ _ _ _
  | _, .mu _ | _, .nu _ | _, .sometimeBefore _ _ | _, .alwaysBefore _ _ => by
    simp [dual, forwardOn]
  | _, .and left right | _, .or left right => by
    simp only [dual, forwardOn, forwardOn_dual admitted left, forwardOn_dual admitted right]
  | _, .possibly _ formula | _, .necessarily _ formula => by
    simp only [dual, forwardOn, forwardOn_dual admitted formula]

theorem forwardOn_conj (admitted : StepLabel → Bool) {n : ℕ} :
    ∀ formulas : List (Formula n), (∀ formula ∈ formulas, formula.forwardOn admitted = true) →
      (conj formulas).forwardOn admitted = true
  | [], _ => rfl
  | formula :: formulas, every => by
    simp only [conj, List.foldr_cons, forwardOn, Bool.and_eq_true]
    exact ⟨every formula (List.mem_cons_self ..),
      forwardOn_conj admitted formulas fun other member => every other (List.mem_cons_of_mem _ member)⟩

end Formula

/-- The forward formulas over admitted labels, closed under the dual. -/
theorem forwardOn_closed (admitted : StepLabel → Bool) : FragmentClosed (Formula.forwardOn admitted) where
  dual := Formula.forwardOn_dual admitted
  top := rfl
  conj := Formula.forwardOn_conj admitted

namespace NativeStructure

variable {Carrier : Type u} (S : NativeStructure Carrier) (admitted : StepLabel → Bool)

/-- **A forward bisimulation over admitted labels**: related elements match each other's steps under every admitted
label, into related elements. -/
structure ForwardBisimulation (relation : Carrier → Carrier → Prop) : Prop where
  forth : ∀ {first second label next}, relation first second → admitted label = true → S.step first label next →
    ∃ next', S.step second label next' ∧ relation next next'
  back : ∀ {first second label next'}, relation first second → admitted label = true → S.step second label next' →
    ∃ next, S.step first label next ∧ relation next next'

/-- **Forward bisimilarity over admitted labels.** -/
def ForwardBisimilar (first second : Carrier) : Prop :=
  ∃ relation, S.ForwardBisimulation admitted relation ∧ relation first second

/-- **Finitely many successors up to an equivalence**, under each admitted label, at the elements of a region: a list
of successors that every successor is equivalent to one of. -/
def FiniteUpTo (region : Carrier → Prop) (equivalent : Carrier → Carrier → Prop) : Prop :=
  ∀ element, region element → ∀ label, admitted label = true →
    ∃ list : List Carrier, (∀ listed ∈ list, S.step element label listed) ∧
      ∀ next, S.step element label next → ∃ listed ∈ list, equivalent next listed

/-- **A region closed under the admitted steps.** -/
def ClosedUnder (region : Carrier → Prop) : Prop :=
  ∀ ⦃element label next⦄, region element → admitted label = true → S.step element label next → region next

variable {S admitted}

/-- **Forward-bisimilar elements satisfy the same forward formulas**, in every structure. -/
theorem sat_of_forwardBisimulation {relation : Carrier → Carrier → Prop}
    (bisimulation : S.ForwardBisimulation admitted relation) :
    ∀ {n : ℕ} (formula : Formula n) (env : Env Carrier n), formula.forwardOn admitted = true →
      ∀ {first second : Carrier}, relation first second → S.sat env formula first → S.sat env formula second
  | _, .top, _, _, _, _, _, _ => trivial
  | _, .bot, _, _, _, _, _, holds => holds
  | _, .and left right, env, inFragment, _, _, related, holds => by
    simp only [Formula.forwardOn, Bool.and_eq_true] at inFragment
    exact ⟨sat_of_forwardBisimulation bisimulation left env inFragment.1 related holds.1,
      sat_of_forwardBisimulation bisimulation right env inFragment.2 related holds.2⟩
  | _, .or left right, env, inFragment, _, _, related, holds => by
    simp only [Formula.forwardOn, Bool.and_eq_true] at inFragment
    exact holds.imp (sat_of_forwardBisimulation bisimulation left env inFragment.1 related)
      (sat_of_forwardBisimulation bisimulation right env inFragment.2 related)
  | _, .possibly label formula, env, inFragment, _, _, related, holds => by
    simp only [Formula.forwardOn, Bool.and_eq_true] at inFragment
    obtain ⟨next, step, nextHolds⟩ := holds
    obtain ⟨next', step', relatedNext⟩ := bisimulation.forth related inFragment.1 step
    exact ⟨next', step', sat_of_forwardBisimulation bisimulation formula env inFragment.2 relatedNext nextHolds⟩
  | _, .necessarily label formula, env, inFragment, _, _, related, holds => by
    simp only [Formula.forwardOn, Bool.and_eq_true] at inFragment
    intro next' step'
    obtain ⟨next, step, relatedNext⟩ := bisimulation.back related inFragment.1 step'
    exact sat_of_forwardBisimulation bisimulation formula env inFragment.2 relatedNext (holds next step)
  | _, .var _, _, inFragment, _, _, _, _ | _, .empty _, _, inFragment, _, _, _, _
  | _, .nonEmpty _, _, inFragment, _, _, _, _ | _, .bound _, _, inFragment, _, _, _, _
  | _, .notBound _, _, inFragment, _, _, _, _ | _, .typed _, _, inFragment, _, _, _, _
  | _, .untyped _, _, inFragment, _, _, _, _ | _, .is _, _, inFragment, _, _, _, _
  | _, .isNot _, _, inFragment, _, _, _, _ | _, .mapsAll _ _, _, inFragment, _, _, _, _
  | _, .mapsSome _ _, _, inFragment, _, _, _, _ | _, .inRelation _, _, inFragment, _, _, _, _
  | _, .notInRelation _, _, inFragment, _, _, _, _ | _, .split _ _ _, _, inFragment, _, _, _, _
  | _, .everySplit _ _ _, _, inFragment, _, _, _, _ | _, .single _ _, _, inFragment, _, _, _, _
  | _, .everySingle _ _, _, inFragment, _, _, _, _ | _, .body _, _, inFragment, _, _, _, _
  | _, .everyBody _, _, inFragment, _, _, _, _ | _, .multiBody _ _, _, inFragment, _, _, _, _
  | _, .everyMultiBody _ _, _, inFragment, _, _, _, _ | _, .someOf _ _, _, inFragment, _, _, _, _
  | _, .everyOf _ _, _, inFragment, _, _, _, _ | _, .built _ _, _, inFragment, _, _, _, _
  | _, .everyBuilt _ _, _, inFragment, _, _, _, _ | _, .atLeast _ _ _ _, _, inFragment, _, _, _, _
  | _, .allButFewer _ _ _ _, _, inFragment, _, _, _, _ | _, .mu _, _, inFragment, _, _, _, _
  | _, .nu _, _, inFragment, _, _, _, _ | _, .sometimeBefore _ _, _, inFragment, _, _, _, _
  | _, .alwaysBefore _ _, _, inFragment, _, _, _, _ => by cases inFragment

/-- **Forward-bisimilar elements agree on the forward formulas.** -/
theorem agree_of_forwardBisimilar {first second : Carrier} (related : S.ForwardBisimilar admitted first second) :
    S.AgreeOn (Formula.forwardOn admitted) first second := by
  obtain ⟨relation, bisimulation, related⟩ := related
  have inverse : S.ForwardBisimulation admitted (fun first second => relation second first) :=
    ⟨fun related admits step => bisimulation.back related admits step,
      fun related admits step => bisimulation.forth related admits step⟩
  exact fun formula inFragment =>
    ⟨sat_of_forwardBisimulation bisimulation formula Env.closed inFragment related,
      sat_of_forwardBisimulation inverse formula Env.closed inFragment related⟩

/-- **The Hennessy–Milner step up to an equivalence**: what the first element reaches under an admitted label is
matched by something the second reaches that agrees with it. Otherwise the conjunction of the separators from the
first's successor to each listed successor of the second, under the label, holds at the first and fails at the
second. -/
theorem match_upTo {region : Carrier → Prop} {equivalent : Carrier → Carrier → Prop} (saturated : S.Saturated equivalent)
    (finite : S.FiniteUpTo admitted region equivalent) {first second next : Carrier} {label : StepLabel}
    (secondIn : region second) (admits : admitted label = true)
    (agree : S.AgreeOn (Formula.forwardOn admitted) first second) (step : S.step first label next) :
    ∃ next', S.step second label next' ∧ S.AgreeOn (Formula.forwardOn admitted) next next' := by
  have closed := forwardOn_closed admitted
  obtain ⟨list, listedSteps, covers⟩ := finite second secondIn label admits
  by_contra none
  push Not at none
  let separators := Formula.conj (list.map (S.separator closed next))
  have inFragment : (Formula.possibly label separators).forwardOn admitted = true := by
    simp only [Formula.forwardOn, admits, Bool.true_and]
    exact separators_fragment closed next list
  have atFirst : S.sat Env.closed (.possibly label separators) first :=
    ⟨next, step, separators_hold closed next list⟩
  obtain ⟨next', step', conjunction⟩ := (agree _ inFragment).mp atFirst
  obtain ⟨listed, member, same⟩ := covers next' step'
  have atListed : S.sat Env.closed separators listed :=
    sat_congr saturated separators (Env.respects_closed _) same conjunction
  exact separator_fails closed (none listed (listedSteps listed member))
    ((S.sat_conj _ _ _).mp atListed _ (List.mem_map.mpr ⟨listed, member, rfl⟩))

/-- **Agreement on the forward formulas, within a closed region, is a forward bisimulation**, with finitely many
successors up to an equivalence the formulas respect. -/
theorem forwardBisimulation_agree {region : Carrier → Prop} {equivalent : Carrier → Carrier → Prop}
    (saturated : S.Saturated equivalent) (finite : S.FiniteUpTo admitted region equivalent)
    (closedUnder : S.ClosedUnder admitted region) :
    S.ForwardBisimulation admitted fun first second =>
      region first ∧ region second ∧ S.AgreeOn (Formula.forwardOn admitted) first second where
  forth := by
    rintro first second label next ⟨firstIn, secondIn, agree⟩ admits step
    obtain ⟨next', step', agreeNext⟩ := match_upTo saturated finite secondIn admits agree step
    exact ⟨next', step', closedUnder firstIn admits step, closedUnder secondIn admits step', agreeNext⟩
  back := by
    rintro first second label next' ⟨firstIn, secondIn, agree⟩ admits step'
    obtain ⟨next, step, agreeNext⟩ := match_upTo saturated finite firstIn admits agree.symm step'
    exact ⟨next, step, closedUnder firstIn admits step, closedUnder secondIn admits step', agreeNext.symm⟩

/-- **The forward formulas over admitted labels characterize forward bisimilarity over them**, on a region closed
under the admitted steps with finitely many successors up to an equivalence the formulas respect. -/
theorem agree_iff_forwardBisimilar {region : Carrier → Prop} {equivalent : Carrier → Carrier → Prop}
    (saturated : S.Saturated equivalent) (finite : S.FiniteUpTo admitted region equivalent)
    (closedUnder : S.ClosedUnder admitted region) {first second : Carrier} (firstIn : region first)
    (secondIn : region second) :
    S.AgreeOn (Formula.forwardOn admitted) first second ↔ S.ForwardBisimilar admitted first second :=
  ⟨fun agree => ⟨_, forwardBisimulation_agree saturated finite closedUnder, firstIn, secondIn, agree⟩,
    agree_of_forwardBisimilar⟩

end NativeStructure

end Mettapedia.OSLF.NativeTypes.GeneratedLogic

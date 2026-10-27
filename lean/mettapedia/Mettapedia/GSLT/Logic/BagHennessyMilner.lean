import Mettapedia.GSLT.Logic.BagSaturated
import Mathlib.Data.Set.Finite.Basic

/-!
# Hennessy–Milner for parallel contexts

In a calculus whose composition is parallel, an agent is a bag and a context the bag beside it (`BagRelativePushout`).
The modal formulas over contexts (`Formula`) say what an agent does when the environment adds a context: some or every
reaction of the composite leads to a formula. A class of admissible contexts fixes which environments are considered.

- **Saturated bisimilarity on admissible contexts** (`SaturatedBisimilarIn`): in every admissible context each reaction
  of either side is matched by a reaction of the other, and the results are again related. With every context
  admissible it is the saturated bisimilarity of the context category (`saturatedBisimilarIn_iff`), so least labels
  characterize it (`BagSaturated.semiSaturated_iff_saturated`).
- **Saturated bisimilar agents satisfy the same formulas over admissible contexts** (`holds_iff_of_saturated`).
- **When an agent in a context has finitely many reactions, the converse holds** (`saturated_of_agree`): agents that no
  formula over admissible contexts tells apart are saturated bisimilar (`saturatedBisimilarIn_iff_agree`). A reaction
  left unmatched is told apart by some reaction in the context leading to the conjunction of formulas that separate its
  result from each result of the other side.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.BagHennessyMilner

open CategoryTheory
open Mettapedia.GSLT.RedexRelativeCongruence (ReactionRule)
open Mettapedia.GSLT.BagRelativePushout
open Mettapedia.GSLT.SemiSaturated (Reacts)

universe u

variable {α : Type u} [DecidableEq α]

/-- **Modal formulas over parallel contexts**: the connectives, and some or every reaction of the agent beside a
context. -/
inductive Formula (α : Type u) where
  | top
  | bot
  | and (left right : Formula α)
  | or (left right : Formula α)
  | possibly (context : List α) (inner : Formula α)
  | necessarily (context : List α) (inner : Formula α)

namespace Formula

variable (rules : ReactionRule (Obj α) → Prop)

/-- **What a formula says of an agent**: a reaction of the agent beside the context, to an agent with the inner formula,
for the possibility, and every such reaction for the necessity. -/
def Holds : Formula α → Multiset α → Prop
  | .top, _ => True
  | .bot, _ => False
  | .and left right, agent => left.Holds agent ∧ right.Holds agent
  | .or left right, agent => left.Holds agent ∨ right.Holds agent
  | .possibly context inner, agent =>
    ∃ next, Reacts rules (bag agent ≫ bag (context : Multiset α)) (bag next) ∧ inner.Holds next
  | .necessarily context inner, agent =>
    ∀ next, Reacts rules (bag agent ≫ bag (context : Multiset α)) (bag next) → inner.Holds next

/-- **Every context of the formula is admissible.** -/
def Within (admissible : Multiset α → Prop) : Formula α → Prop
  | .top | .bot => True
  | .and left right | .or left right => left.Within admissible ∧ right.Within admissible
  | .possibly context inner | .necessarily context inner => admissible context ∧ inner.Within admissible

/-- The dual: each former exchanged with its dual. -/
def dual : Formula α → Formula α
  | .top => .bot
  | .bot => .top
  | .and left right => .or left.dual right.dual
  | .or left right => .and left.dual right.dual
  | .possibly context inner => .necessarily context inner.dual
  | .necessarily context inner => .possibly context inner.dual

variable {rules}

/-- **The dual is the negation.** -/
theorem holds_dual : ∀ (formula : Formula α) (agent : Multiset α),
    formula.dual.Holds rules agent ↔ ¬ formula.Holds rules agent
  | .top, _ => by simp [dual, Holds]
  | .bot, _ => by simp [dual, Holds]
  | .and left right, agent => by
    simp only [dual, Holds, holds_dual left agent, holds_dual right agent, not_and_or]
  | .or left right, agent => by
    simp only [dual, Holds, holds_dual left agent, holds_dual right agent, not_or]
  | .possibly context inner, agent => by
    simp only [dual, Holds, fun next => holds_dual inner next, not_exists, not_and]
  | .necessarily context inner, agent => by
    simp only [dual, Holds, fun next => holds_dual inner next, not_forall, exists_prop]

omit [DecidableEq α] in
theorem within_dual {admissible : Multiset α → Prop} :
    ∀ {formula : Formula α}, formula.Within admissible → formula.dual.Within admissible
  | .top, _ | .bot, _ => trivial
  | .and _ _, within | .or _ _, within => ⟨within_dual within.1, within_dual within.2⟩
  | .possibly _ _, within | .necessarily _ _, within => ⟨within.1, within_dual within.2⟩

/-- The conjunction of a list of formulas. -/
def conj : List (Formula α) → Formula α
  | [] => .top
  | formula :: formulas => .and formula (conj formulas)

theorem holds_conj : ∀ {formulas : List (Formula α)} {agent : Multiset α},
    (conj formulas).Holds rules agent ↔ ∀ formula ∈ formulas, formula.Holds rules agent
  | [], _ => by simp [conj, Holds]
  | _ :: _, _ => by
    simp only [conj, Holds, holds_conj, List.mem_cons, forall_eq_or_imp]

omit [DecidableEq α] in
theorem within_conj {admissible : Multiset α → Prop} :
    ∀ {formulas : List (Formula α)}, (∀ formula ∈ formulas, formula.Within admissible) →
      (conj formulas).Within admissible
  | [], _ => trivial
  | formula :: _, within =>
    ⟨within formula List.mem_cons_self, within_conj fun other member => within other (List.mem_cons_of_mem _ member)⟩

end Formula

open Formula

variable (rules : ReactionRule (Obj α) → Prop) (admissible : Multiset α → Prop)

/-- **A saturated bisimulation on admissible contexts**: in every admissible context, a reaction of either side is
matched by a reaction of the other, to related agents. -/
def IsSaturatedIn (relation : Multiset α → Multiset α → Prop) : Prop :=
  ∀ ⦃first second⦄, relation first second → ∀ context, admissible context →
    (∀ next, Reacts rules (bag first ≫ bag context) (bag next) →
      ∃ matched, Reacts rules (bag second ≫ bag context) (bag matched) ∧ relation next matched) ∧
    (∀ next, Reacts rules (bag second ≫ bag context) (bag next) →
      ∃ matched, Reacts rules (bag first ≫ bag context) (bag matched) ∧ relation matched next)

/-- **Saturated bisimilarity on admissible contexts.** -/
def SaturatedBisimilarIn (first second : Multiset α) : Prop :=
  ∃ relation, IsSaturatedIn rules admissible relation ∧ relation first second

/-- **The agents no formula over admissible contexts tells apart.** -/
def Agree (first second : Multiset α) : Prop :=
  ∀ formula : Formula α, formula.Within admissible → (formula.Holds rules first ↔ formula.Holds rules second)

/-- **Finitely many reactions**: an agent beside an admissible context reacts to finitely many agents. -/
def ImageFinite : Prop :=
  ∀ agent context, admissible context → {next | Reacts rules (bag agent ≫ bag context) (bag next)}.Finite

variable {rules admissible}

/-- **Saturated bisimilar agents satisfy the same formulas over admissible contexts.** -/
theorem holds_iff_of_saturated {relation : Multiset α → Multiset α → Prop}
    (saturated : IsSaturatedIn rules admissible relation) :
    ∀ (formula : Formula α), formula.Within admissible → ∀ {first second}, relation first second →
      (formula.Holds rules first ↔ formula.Holds rules second)
  | .top, _, _, _, _ => Iff.rfl
  | .bot, _, _, _, _ => Iff.rfl
  | .and left right, within, _, _, related =>
    and_congr (holds_iff_of_saturated saturated left within.1 related)
      (holds_iff_of_saturated saturated right within.2 related)
  | .or left right, within, _, _, related =>
    or_congr (holds_iff_of_saturated saturated left within.1 related)
      (holds_iff_of_saturated saturated right within.2 related)
  | .possibly context inner, within, _, _, related => by
    obtain ⟨forth, back⟩ := saturated related context within.1
    constructor
    · rintro ⟨next, reacts, holds⟩
      obtain ⟨matched, matchedReacts, nextRelated⟩ := forth next reacts
      exact ⟨matched, matchedReacts, (holds_iff_of_saturated saturated inner within.2 nextRelated).mp holds⟩
    · rintro ⟨next, reacts, holds⟩
      obtain ⟨matched, matchedReacts, nextRelated⟩ := back next reacts
      exact ⟨matched, matchedReacts, (holds_iff_of_saturated saturated inner within.2 nextRelated).mpr holds⟩
  | .necessarily context inner, within, _, _, related => by
    obtain ⟨forth, back⟩ := saturated related context within.1
    constructor
    · intro every next reacts
      obtain ⟨matched, matchedReacts, nextRelated⟩ := back next reacts
      exact (holds_iff_of_saturated saturated inner within.2 nextRelated).mp (every matched matchedReacts)
    · intro every next reacts
      obtain ⟨matched, matchedReacts, nextRelated⟩ := forth next reacts
      exact (holds_iff_of_saturated saturated inner within.2 nextRelated).mpr (every matched matchedReacts)

/-- A formula over admissible contexts that holds at one agent and fails at another, when they disagree. -/
theorem separates_of_not_agree {first second : Multiset α} (differ : ¬ Agree rules admissible first second) :
    ∃ formula : Formula α, formula.Within admissible ∧ formula.Holds rules first ∧ ¬ formula.Holds rules second := by
  have found : ∃ formula : Formula α, formula.Within admissible ∧
      ¬ (formula.Holds rules first ↔ formula.Holds rules second) := by
    by_contra none
    exact differ fun formula within => by_contra fun differs => none ⟨formula, within, differs⟩
  obtain ⟨formula, within, differs⟩ := found
  by_cases holds : formula.Holds rules first
  · exact ⟨formula, within, holds, fun other => differs ⟨fun _ => other, fun _ => holds⟩⟩
  · refine ⟨formula.dual, within_dual within, (holds_dual formula first).mpr holds, fun dualHolds => ?_⟩
    have secondFails := (holds_dual formula second).mp dualHolds
    exact differs ⟨fun inside => (holds inside).elim, fun inside => (secondFails inside).elim⟩

/-- **An unmatched reaction is told apart**: if no reaction of `second` beside the context agrees with `next`, a formula
over admissible contexts holds at `first` and fails at `second`. -/
theorem told_apart (finite : ImageFinite rules admissible) {first second next : Multiset α} {context : Multiset α}
    (contextAdmissible : admissible context) (reacts : Reacts rules (bag first ≫ bag context) (bag next))
    (unmatched : ∀ matched, Reacts rules (bag second ≫ bag context) (bag matched) →
      ¬ Agree rules admissible next matched) :
    ∃ formula : Formula α, formula.Within admissible ∧ formula.Holds rules first ∧ ¬ formula.Holds rules second := by
  classical
  have results : {next | Reacts rules (bag second ≫ bag context) (bag next)}.Finite :=
    finite second context contextAdmissible
  have separates : ∀ result : results.toFinset, ∃ formula : Formula α, formula.Within admissible ∧
      formula.Holds rules next ∧ ¬ formula.Holds rules result.1 := fun result =>
    separates_of_not_agree (unmatched result.1 ((Set.Finite.mem_toFinset results).mp result.2))
  choose separating within holds fails using separates
  obtain ⟨list, rfl⟩ := Quotient.exists_rep context
  refine ⟨.possibly list (conj (results.toFinset.attach.toList.map separating)),
    ⟨contextAdmissible, within_conj fun formula member => ?_⟩, ⟨next, reacts, holds_conj.mpr fun formula member => ?_⟩,
    ?_⟩
  · obtain ⟨result, -, rfl⟩ := List.mem_map.mp member
    exact within result
  · obtain ⟨result, -, rfl⟩ := List.mem_map.mp member
    exact holds result
  · rintro ⟨matched, matchedReacts, matchedHolds⟩
    have member : matched ∈ results.toFinset := (Set.Finite.mem_toFinset results).mpr matchedReacts
    exact fails ⟨matched, member⟩ (holds_conj.mp matchedHolds _
      (List.mem_map.mpr ⟨⟨matched, member⟩, Finset.mem_toList.mpr (Finset.mem_attach _ _), rfl⟩))

/-- **Agreement on the formulas is a saturated bisimulation**, when reactions are finitely many. -/
theorem isSaturatedIn_agree (finite : ImageFinite rules admissible) :
    IsSaturatedIn rules admissible (Agree rules admissible) := by
  intro first second agree context contextAdmissible
  constructor
  · intro next reacts
    by_contra unmatched
    obtain ⟨formula, within, holds, fails⟩ := told_apart finite contextAdmissible reacts
      fun matched matchedReacts same => unmatched ⟨matched, matchedReacts, same⟩
    exact fails ((agree formula within).mp holds)
  · intro next reacts
    by_contra unmatched
    obtain ⟨formula, within, holds, fails⟩ := told_apart finite contextAdmissible reacts
      fun matched matchedReacts same => unmatched ⟨matched, matchedReacts, fun formula within =>
        (same formula within).symm⟩
    exact fails ((agree formula within).mpr holds)

/-- **Agents no formula tells apart are saturated bisimilar**, when reactions are finitely many. -/
theorem saturated_of_agree (finite : ImageFinite rules admissible) {first second : Multiset α}
    (agree : Agree rules admissible first second) : SaturatedBisimilarIn rules admissible first second :=
  ⟨_, isSaturatedIn_agree finite, agree⟩

/-- **Hennessy–Milner for parallel contexts**: with finitely many reactions, agents are saturated bisimilar on admissible
contexts exactly when no formula over admissible contexts tells them apart. -/
theorem saturatedBisimilarIn_iff_agree (finite : ImageFinite rules admissible) {first second : Multiset α} :
    SaturatedBisimilarIn rules admissible first second ↔ Agree rules admissible first second :=
  ⟨fun ⟨_, saturated, related⟩ formula within => holds_iff_of_saturated saturated formula within related,
    saturated_of_agree finite⟩

/-- **With every context admissible, it is the saturated bisimilarity of the context category.** -/
theorem saturatedBisimilarIn_iff {first second : Multiset α} :
    SaturatedBisimilarIn rules (fun _ => True) first second ↔
      SemiSaturated.SaturatedBisimilar rules (bag first) (bag second) := by
  constructor
  · rintro ⟨relation, saturated, related⟩
    refine ⟨fun _ left right => relation (BagSaturated.coordinates left) (BagSaturated.coordinates right), ?_, related⟩
    intro interface left right holds outer context
    obtain ⟨forth, back⟩ := saturated holds (BagSaturated.coordinates context) trivial
    constructor
    · intro next reacts
      obtain ⟨matched, matchedReacts, nextRelated⟩ := forth (BagSaturated.coordinates next) reacts
      exact ⟨bag matched, matchedReacts, nextRelated⟩
    · intro next reacts
      obtain ⟨matched, matchedReacts, nextRelated⟩ := back (BagSaturated.coordinates next) reacts
      exact ⟨bag matched, matchedReacts, nextRelated⟩
  · rintro ⟨relation, saturated, related⟩
    refine ⟨fun left right => relation (Obj α) (bag left) (bag right), ?_, related⟩
    intro first second holds context _
    obtain ⟨forth, back⟩ := saturated (bag first) (bag second) holds (bag context)
    constructor
    · intro next reacts
      obtain ⟨matched, matchedReacts, nextRelated⟩ := forth (bag next) reacts
      exact ⟨BagSaturated.coordinates matched, matchedReacts, nextRelated⟩
    · intro next reacts
      obtain ⟨matched, matchedReacts, nextRelated⟩ := back (bag next) reacts
      exact ⟨BagSaturated.coordinates matched, matchedReacts, nextRelated⟩

end Mettapedia.GSLT.BagHennessyMilner

import Mettapedia.GSLT.Logic.InterfaceModalLogic

/-!
# Complete modal observations at actual reaction interfaces

The formula grammar retains both interfaces of every context arrow and
allows conjunctions indexed at the level of the actual agent arrows. Its
diamonds use the independently constructed idem-pushout firing relation.
Logical equivalence is exactly interface-indexed IPO bisimilarity, with no
branching hypothesis. The existing finitary grammar embeds with its actual
satisfaction preserved; finitary completeness requires a separate cover.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.InterfaceInfinitaryModalLogic

open _root_.CategoryTheory RedexRelativeCongruence

universe u v

variable {C : Type u} [Category.{v} C] {origin : C}

inductive Formula (C : Type u) [Category.{v} C] : C → Type (max u (v + 1)) where
  | conj {interface} {Index : Type v} (parts : Index → Formula C interface) : Formula C interface
  | neg {interface} (inner : Formula C interface) : Formula C interface
  | diamond {first last} (label : first ⟶ last) (inner : Formula C last) : Formula C first

def Formula.top {interface : C} : Formula C interface :=
  .conj (Index := PEmpty.{v + 1}) (fun index => index.elim)

def Formula.pair {interface : C} (first second : Formula C interface) : Formula C interface :=
  .conj (fun index : ULift.{v} Bool => if index.down then first else second)

def Holds (rules : ReactionRule origin → Prop) :
    {interface : C} → Formula C interface → (origin ⟶ interface) → Prop
  | _, .conj parts, agent => ∀ index, Holds rules (parts index) agent
  | _, .neg inner, agent => ¬ Holds rules inner agent
  | _, .diamond label inner, agent =>
      ∃ target, ActIPO rules label agent target ∧ Holds rules inner target

variable (rules : ReactionRule origin → Prop)

theorem holds_top {interface : C} (agent : origin ⟶ interface) :
    Holds rules Formula.top agent := fun index => index.elim

theorem holds_pair {interface : C} (first second : Formula C interface)
    (agent : origin ⟶ interface) :
    Holds rules (first.pair second) agent ↔ Holds rules first agent ∧ Holds rules second agent := by
  constructor
  · intro holds
    exact ⟨holds ⟨true⟩, holds ⟨false⟩⟩
  · rintro ⟨firstHolds, secondHolds⟩ ⟨index⟩
    cases index
    · exact secondHolds
    · exact firstHolds

def LogicallyEquivalent {interface : C} (first second : origin ⟶ interface) : Prop :=
  ∀ formula : Formula C interface, Holds rules formula first ↔ Holds rules formula second

theorem logicallyEquivalent_refl {interface : C} (agent : origin ⟶ interface) :
    LogicallyEquivalent rules agent agent := fun _ => Iff.rfl

theorem logicallyEquivalent_symm {interface : C} {first second : origin ⟶ interface}
    (related : LogicallyEquivalent rules first second) : LogicallyEquivalent rules second first :=
  fun formula => (related formula).symm

theorem logicallyEquivalent_trans {interface : C} {first middle last : origin ⟶ interface}
    (before : LogicallyEquivalent rules first middle) (after : LogicallyEquivalent rules middle last) :
    LogicallyEquivalent rules first last := fun formula => (before formula).trans (after formula)

theorem holds_iff_of_bisimulation
    (relation : (interface : C) → (origin ⟶ interface) → (origin ⟶ interface) → Prop)
    (bisimulation : IsIPOBisimulation rules relation) {interface : C}
    (formula : Formula C interface) :
    ∀ (first second : origin ⟶ interface), relation interface first second →
      (Holds rules formula first ↔ Holds rules formula second) := by
  induction formula with
  | conj parts readings =>
      intro first second related
      exact forall_congr' (fun index => readings index first second related)
  | neg inner reading =>
      intro first second related
      exact not_congr (reading first second related)
  | diamond label inner reading =>
      intro first second related
      constructor
      · rintro ⟨next, firing, holds⟩
        obtain ⟨matched, actual, successors⟩ := (bisimulation first second related).1 label next firing
        exact ⟨matched, actual, (reading next matched successors).mp holds⟩
      · rintro ⟨next, firing, holds⟩
        obtain ⟨matched, actual, successors⟩ := (bisimulation first second related).2 label next firing
        exact ⟨matched, actual, (reading matched next successors).mpr holds⟩

theorem logicallyEquivalent_of_ipoBisimilar {interface : C} {first second : origin ⟶ interface}
    (related : IPOBisimilar rules first second) : LogicallyEquivalent rules first second := by
  obtain ⟨relation, bisimulation, pair⟩ := related
  exact fun formula => holds_iff_of_bisimulation rules relation bisimulation formula first second pair

theorem exists_separating_formula {interface : C} {first second : origin ⟶ interface}
    (different : ¬ LogicallyEquivalent rules first second) :
    ∃ formula : Formula C interface, Holds rules formula first ∧ ¬ Holds rules formula second := by
  obtain ⟨formula, disagreement⟩ := not_forall.mp different
  by_cases firstHolds : Holds rules formula first
  · exact ⟨formula, firstHolds, fun secondHolds =>
      disagreement ⟨fun _ => secondHolds, fun _ => firstHolds⟩⟩
  · exact ⟨.neg formula, firstHolds, fun secondFails =>
      disagreement ⟨fun holds => absurd holds firstHolds, fun holds => absurd holds secondFails⟩⟩

/-- A conjunction over the actual successors earns the matching step without a finite cover. -/
theorem exists_matching_step {interface nextInterface : C}
    {first second : origin ⟶ interface} (equivalent : LogicallyEquivalent rules first second)
    (label : interface ⟶ nextInterface) {next : origin ⟶ nextInterface}
    (firing : ActIPO rules label first next) :
    ∃ matched, ActIPO rules label second matched ∧ LogicallyEquivalent rules next matched := by
  classical
  by_contra noMatch
  have separators : ∀ candidate : {target : origin ⟶ nextInterface // ActIPO rules label second target},
      ∃ formula : Formula C nextInterface,
        Holds rules formula next ∧ ¬ Holds rules formula candidate.val := by
    intro candidate
    exact exists_separating_formula rules
      (fun related => noMatch ⟨candidate.val, candidate.property, related⟩)
  choose separator holdsNext failsCandidate using separators
  let bundle : Formula C nextInterface := .conj separator
  have firstHolds : Holds rules (.diamond label bundle) first :=
    ⟨next, firing, holdsNext⟩
  obtain ⟨matched, actual, allHolds⟩ := (equivalent (.diamond label bundle)).mp firstHolds
  exact failsCandidate ⟨matched, actual⟩ (allHolds ⟨matched, actual⟩)

theorem logicallyEquivalent_isBisimulation :
    IsIPOBisimulation rules (fun _ first second => LogicallyEquivalent rules first second) := by
  intro interface first second related
  constructor
  · intro nextInterface label next firing
    exact exists_matching_step rules related label firing
  · intro nextInterface label next firing
    obtain ⟨matched, actual, successors⟩ :=
      exists_matching_step rules (logicallyEquivalent_symm rules related) label firing
    exact ⟨matched, actual, logicallyEquivalent_symm rules successors⟩

/-- Adequacy concerns the actual least-context labelled system, at every interface. -/
theorem logicallyEquivalent_iff_ipoBisimilar {interface : C} (first second : origin ⟶ interface) :
    LogicallyEquivalent rules first second ↔ IPOBisimilar rules first second :=
  ⟨fun related => ⟨_, logicallyEquivalent_isBisimulation rules, related⟩,
    logicallyEquivalent_of_ipoBisimilar rules⟩

def ofFinitary : {interface : C} → InterfaceModalLogic.Formula C interface → Formula C interface
  | _, .top => .top
  | _, .conj first second => (ofFinitary first).pair (ofFinitary second)
  | _, .neg inner => .neg (ofFinitary inner)
  | _, .diamond label inner => .diamond label (ofFinitary inner)

theorem holds_ofFinitary {interface : C} (formula : InterfaceModalLogic.Formula C interface) :
    ∀ agent : origin ⟶ interface,
      Holds rules (ofFinitary formula) agent ↔ InterfaceModalLogic.Holds rules formula agent := by
  induction formula with
  | top => intro agent; exact ⟨fun _ => trivial, fun _ => holds_top rules agent⟩
  | conj first second firstRead secondRead =>
      intro agent
      exact (holds_pair rules _ _ agent).trans (and_congr (firstRead agent) (secondRead agent))
  | neg inner reading => intro agent; exact not_congr (reading agent)
  | diamond label inner reading =>
      intro agent
      exact exists_congr (fun next => and_congr Iff.rfl (reading next))

theorem finitary_logicallyEquivalent_of_complete {interface : C} {first second : origin ⟶ interface}
    (related : LogicallyEquivalent rules first second) :
    InterfaceModalLogic.LogicallyEquivalent rules first second :=
  fun formula => (holds_ofFinitary rules formula first).symm.trans
    ((related (ofFinitary formula)).trans (holds_ofFinitary rules formula second))

end Mettapedia.GSLT.InterfaceInfinitaryModalLogic

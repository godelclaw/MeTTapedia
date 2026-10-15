import Mettapedia.GSLT.Logic.InterfaceInfinitaryModalLogic
import Mathlib.Data.Set.Finite.Basic

/-!
# Finitary adequacy with explicit covers of actual reaction successors

Finite covers are families at the actual result interface. A cover relation
needs only to preserve the independently defined finitary readings; it need
not be installed as an equation relation. Equality and already earned IPO
bisimilarity provide two sufficient instances. Complete infinitary and
finitary readings therefore agree under the stated cover hypothesis.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.InterfaceModalLogic

open _root_.CategoryTheory RedexRelativeCongruence

universe u v

variable {C : Type u} [Category.{v} C] {origin : C}
  (rules : ReactionRule origin → Prop)

def ImageFiniteUpTo
    (relation : (interface : C) → (origin ⟶ interface) → (origin ⟶ interface) → Prop) : Prop :=
  ∀ {first last : C} (label : first ⟶ last) (agent : origin ⟶ first),
    ∃ representatives : Set (origin ⟶ last), representatives.Finite ∧
      ∀ {target}, ActIPO rules label agent target →
        ∃ representative ∈ representatives, relation last target representative

/-- The original finite-successor contract, on the actual result-agent set. -/
def ImageFinite : Prop :=
  ∀ {first last : C} (label : first ⟶ last) (agent : origin ⟶ first),
    Set.Finite {target | ActIPO rules label agent target}

def ImageFiniteBisimilar : Prop := ImageFiniteUpTo rules (fun _ => IPOBisimilar rules)

/-- The independently formed equality-cover condition recovers the original contract. -/
theorem imageFinite_iff_equality_cover :
    ImageFinite rules ↔ ImageFiniteUpTo rules (fun _ first second => first = second) := by
  constructor
  · intro finite first last label agent
    exact ⟨{target | ActIPO rules label agent target}, finite label agent,
      fun actual => ⟨_, actual, rfl⟩⟩
  · intro finite first last label agent
    obtain ⟨representatives, hFinite, covered⟩ := finite label agent
    apply hFinite.subset
    intro target actual
    obtain ⟨representative, member, same⟩ := covered actual
    exact same ▸ member

theorem imageFinite_of_finite_agents
    (finite : ∀ interface : C, Finite (origin ⟶ interface)) : ImageFinite rules := by
  intro first last label agent
  let _ := finite last
  exact Set.toFinite _

theorem imageFiniteBisimilar_of_imageFinite (finite : ImageFinite rules) :
    ImageFiniteBisimilar rules := by
  have cover : ImageFiniteUpTo rules (fun _ first second => first = second) :=
    (imageFinite_iff_equality_cover rules).mp finite
  intro first last label agent
  obtain ⟨representatives, hFinite, covered⟩ := cover label agent
  refine ⟨representatives, hFinite, ?_⟩
  intro target firing
  obtain ⟨representative, member, same⟩ := covered firing
  refine ⟨representative, member, ?_⟩
  subst representative
  exact ipoBisimilar_refl rules target

theorem exists_separating_formula {interface : C} {first second : origin ⟶ interface}
    (different : ¬ LogicallyEquivalent rules first second) :
    ∃ formula : Formula C interface, Holds rules formula first ∧ ¬ Holds rules formula second := by
  obtain ⟨formula, disagreement⟩ := not_forall.mp different
  by_cases firstHolds : Holds rules formula first
  · exact ⟨formula, firstHolds, fun secondHolds =>
      disagreement ⟨fun _ => secondHolds, fun _ => firstHolds⟩⟩
  · exact ⟨.neg formula, firstHolds, fun secondFails =>
      disagreement ⟨fun holds => absurd holds firstHolds, fun holds => absurd holds secondFails⟩⟩

/-- The complete cover argument retains the changing result interface. -/
theorem exists_matching_step_of_finite_cover
    {cover : (interface : C) → (origin ⟶ interface) → (origin ⟶ interface) → Prop}
    (respect : ∀ {interface} (formula : Formula C interface) {first second},
      cover interface first second → (Holds rules formula first ↔ Holds rules formula second))
    (finite : ImageFiniteUpTo rules cover)
    {interface nextInterface : C} {first second : origin ⟶ interface}
    (equivalent : LogicallyEquivalent rules first second) (label : interface ⟶ nextInterface)
    {next : origin ⟶ nextInterface} (firing : ActIPO rules label first next) :
    ∃ matched, ActIPO rules label second matched ∧ LogicallyEquivalent rules next matched := by
  classical
  by_contra noMatch
  have unmatched : ∀ target, ActIPO rules label second target →
      ¬ LogicallyEquivalent rules next target :=
    fun target actual related => noMatch ⟨target, actual, related⟩
  have separators : ∀ candidate : origin ⟶ nextInterface,
      ∃ formula : Formula C nextInterface,
        Holds rules formula next ∧
          ((∃ target, ActIPO rules label second target ∧ cover nextInterface target candidate) →
            ¬ Holds rules formula candidate) := by
    intro candidate
    by_cases reachable : ∃ target,
        ActIPO rules label second target ∧ cover nextInterface target candidate
    · obtain ⟨target, actual, related⟩ := reachable
      have different : ¬ LogicallyEquivalent rules next candidate := by
        intro matching
        exact unmatched target actual (fun formula =>
          (matching formula).trans (respect formula related).symm)
      obtain ⟨formula, holds, fails⟩ := exists_separating_formula rules different
      exact ⟨formula, holds, fun _ => fails⟩
    · exact ⟨.top, trivial, fun reached => absurd reached reachable⟩
  choose separator holdsNext failsCandidate using separators
  obtain ⟨representatives, hFinite, covered⟩ := finite label second
  obtain ⟨finiteRepresentatives, same⟩ := hFinite.exists_finset_coe
  let bundle := Formula.conjList (finiteRepresentatives.toList.map separator)
  have firstHolds : Holds rules (.diamond label bundle) first := by
    refine ⟨next, firing, ?_⟩
    rw [holds_conjList]
    intro formula member
    obtain ⟨candidate, _, rfl⟩ := List.mem_map.mp member
    exact holdsNext candidate
  obtain ⟨matched, actual, allHolds⟩ := (equivalent (.diamond label bundle)).mp firstHolds
  obtain ⟨representative, member, related⟩ := covered actual
  have representativeHolds : Holds rules (separator representative) representative := by
    apply (respect _ related).mp
    apply (holds_conjList rules _ matched).mp allHolds
    apply List.mem_map.mpr
    refine ⟨representative, ?_, rfl⟩
    rw [Finset.mem_toList]
    exact Finset.mem_coe.mp (same.symm ▸ member)
  exact failsCandidate representative ⟨matched, actual, related⟩ representativeHolds

theorem logicallyEquivalent_isBisimulation_of_finite_cover
    {cover : (interface : C) → (origin ⟶ interface) → (origin ⟶ interface) → Prop}
    (respect : ∀ {interface} (formula : Formula C interface) {first second},
      cover interface first second → (Holds rules formula first ↔ Holds rules formula second))
    (finite : ImageFiniteUpTo rules cover) :
    IsIPOBisimulation rules (fun _ first second => LogicallyEquivalent rules first second) := by
  intro interface first second related
  constructor
  · intro nextInterface label next firing
    exact exists_matching_step_of_finite_cover rules respect finite related label firing
  · intro nextInterface label next firing
    obtain ⟨matched, actual, successors⟩ := exists_matching_step_of_finite_cover rules respect finite
      (logicallyEquivalent_symm rules related) label firing
    exact ⟨matched, actual, logicallyEquivalent_symm rules successors⟩

theorem logicallyEquivalent_iff_ipoBisimilar_of_behavioral_cover
    (finite : ImageFiniteBisimilar rules) {interface : C} (first second : origin ⟶ interface) :
    LogicallyEquivalent rules first second ↔ IPOBisimilar rules first second :=
  ⟨fun related => ⟨_, logicallyEquivalent_isBisimulation_of_finite_cover rules
      (fun {_} formula {_ _} related => logicallyEquivalent_of_ipoBisimilar rules related formula)
      finite, related⟩,
    logicallyEquivalent_of_ipoBisimilar rules⟩

theorem logicallyEquivalent_iff_ipoBisimilar (finite : ImageFinite rules)
    {interface : C} (first second : origin ⟶ interface) :
    LogicallyEquivalent rules first second ↔ IPOBisimilar rules first second :=
  logicallyEquivalent_iff_ipoBisimilar_of_behavioral_cover rules
    (imageFiniteBisimilar_of_imageFinite rules finite) first second

theorem ipoBisimilar_iff_logicallyEquivalent (finite : ImageFinite rules)
    {interface : C} (first second : origin ⟶ interface) :
    IPOBisimilar rules first second ↔ LogicallyEquivalent rules first second :=
  (logicallyEquivalent_iff_ipoBisimilar rules finite first second).symm

theorem finitary_iff_complete (finite : ImageFiniteBisimilar rules)
    {interface : C} (first second : origin ⟶ interface) :
    LogicallyEquivalent rules first second ↔
      InterfaceInfinitaryModalLogic.LogicallyEquivalent rules first second :=
  (logicallyEquivalent_iff_ipoBisimilar_of_behavioral_cover rules finite first second).trans
    (InterfaceInfinitaryModalLogic.logicallyEquivalent_iff_ipoBisimilar rules first second).symm

end Mettapedia.GSLT.InterfaceModalLogic

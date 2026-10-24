import Mettapedia.OSLF.Syntax.FiniteBranchingGSOSFinalBialgebra
import Mettapedia.TypeTheory.MaterialSets.Hypersets.Streams

/-!
# Finite-branching behaviour interpreted by labelled hypersets

Each small state carrier and its complete labelled successors define a
labelled graph. Its hyperset decoration is natural in coalgebra morphisms.
Consequently the direct material interpretation agrees with observing in
the independently constructed final action-tree coalgebra and then decorating.

When the label interpretation is injective, equality of material readings
is exactly the existing labelled bisimilarity, hence exactly equality of
final observations. Constructor compatibility is inherited from the actual
GSOS lifting. These statements retain successor sets, not edge multiplicity.
All graph nodes and labels live in the stated small universe; no terminality
claim about unrestricted powerset coalgebras is used.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.FiniteBranching.HypersetSemantics

open _root_.CategoryTheory Mettapedia.CategoryTheory
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open Mettapedia.OSLF.DeterministicGSOS (Signature)

universe u

variable {S : Signature.{u}} {Actions : S.Srt → Type u}

abbrev Coalgebra := Endofunctor.Coalgebra (behaviourFunctor S Actions)

/-- The graph uses the coalgebra's actual successor membership. -/
def edge (object : Coalgebra (S := S) (Actions := Actions))
    (base : PUnit.{u + 1}) (sort : S.Srt)
    (source : object.V base sort) (action : Actions sort) (target : object.V base sort) : Prop :=
  target ∈ object.str base sort source action

def readout (object : Coalgebra (S := S) (Actions := Actions))
    (labels : (sort : S.Srt) → Actions sort → HSet.{u})
    (base : PUnit.{u + 1}) (sort : S.Srt) (state : object.V base sort) : HSet.{u} :=
  HSet.decorateLabelled (edge object base sort) (labels sort) state

theorem readout_members (object : Coalgebra (S := S) (Actions := Actions))
    (labels : (sort : S.Srt) → Actions sort → HSet.{u})
    (base : PUnit.{u + 1}) (sort : S.Srt) (state : object.V base sort) (value : HSet.{u}) :
    value ∈ readout object labels base sort state ↔
      ∃ action next, next ∈ object.str base sort state action ∧
        value = HSet.kpair (labels sort action) (readout object labels base sort next) :=
  HSet.mem_decorateLabelled

/-- Coalgebra morphisms preserve the whole material observation, even when
they identify states. Their successor-image law supplies the reverse direction. -/
theorem readout_natural {source target : Coalgebra (S := S) (Actions := Actions)}
    (mapping : source ⟶ target) (labels : (sort : S.Srt) → Actions sort → HSet.{u})
    (base : PUnit.{u + 1}) (sort : S.Srt) (state : source.V base sort) :
    readout target labels base sort (mapping.f base sort state) =
      readout source labels base sort state := by
  have square (state : source.V base sort) (action : Actions sort) :
      FinitePowerset.map (mapping.f base sort) (source.str base sort state action) =
        target.str base sort (mapping.f base sort state) action :=
    congrArg (fun arrow => arrow base sort state action) mapping.h
  have decorates : HSet.IsLabelledDecoration (edge source base sort) (labels sort)
      (fun state => readout target labels base sort (mapping.f base sort state)) := by
    intro current value
    rw [readout_members]
    constructor
    · rintro ⟨action, next, member, same⟩
      rw [← square current action] at member
      obtain ⟨original, originalMember, rfl⟩ := (FinitePowerset.mem_map _ _ _).mp member
      exact ⟨action, original, originalMember, same⟩
    · rintro ⟨action, next, member, same⟩
      refine ⟨action, mapping.f base sort next, ?_, same⟩
      rw [← square current action]
      exact (FinitePowerset.mem_map _ _ _).mpr ⟨next, member, rfl⟩
  exact congrFun decorates.eq_decorateLabelled state

/-- Direct graph decoration factors through the actual final observation. -/
theorem readout_observe (object : Coalgebra (S := S) (Actions := Actions))
    (labels : (sort : S.Srt) → Actions sort → HSet.{u})
    (base : PUnit.{u + 1}) (sort : S.Srt) (state : object.V base sort) :
    readout (FinalSemantics.finalObject S Actions) labels base sort
        ((FinalSemantics.observe S Actions object).f base sort state) =
      readout object labels base sort state :=
  readout_natural (FinalSemantics.observe S Actions object) labels base sort state

theorem readout_eq_of_bisimilar {left right : Coalgebra (S := S) (Actions := Actions)}
    (labels : (sort : S.Srt) → Actions sort → HSet.{u})
    (base : PUnit.{u + 1}) (sort : S.Srt)
    {first : left.V base sort} {second : right.V base sort}
    (related : Bisimulation.Bisimilar left right base sort first second) :
    readout left labels base sort first = readout right labels base sort second := by
  obtain ⟨relation, admitted, held⟩ := related
  apply HSet.decorateLabelled_eq_of_labelledBisimilar
  refine ⟨relation base sort, ?_, held⟩
  intro first second matched
  constructor
  · intro action next member
    obtain ⟨other, present, matchedNext⟩ := (admitted base sort first second matched action).1 next member
    exact ⟨action, other, present, rfl, matchedNext⟩
  · intro action next member
    obtain ⟨other, present, matchedNext⟩ := (admitted base sort first second matched action).2 next member
    exact ⟨action, other, present, rfl, matchedNext⟩

/-- Equality of material observations supplies a bisimulation when action
labels retain their distinctions. No such reflection is assumed. -/
theorem readout_kernel_admitted
    (left right : Coalgebra (S := S) (Actions := Actions))
    (labels : (sort : S.Srt) → Actions sort → HSet.{u})
    (faithful : ∀ sort, Function.Injective (labels sort)) :
    Bisimulation.Admitted left right (fun base sort first second =>
      readout left labels base sort first = readout right labels base sort second) := by
  intro base sort first second same action
  constructor
  · intro next member
    have observed : HSet.kpair (labels sort action) (readout left labels base sort next) ∈
        readout right labels base sort second := by
      rw [← same, readout_members]
      exact ⟨action, next, member, rfl⟩
    obtain ⟨otherAction, other, present, equal⟩ := (readout_members _ _ _ _ _ _).mp observed
    obtain ⟨labelEq, stateEq⟩ := HSet.kpair_inj.mp equal
    have actionEq := faithful sort labelEq
    subst otherAction
    exact ⟨other, present, stateEq⟩
  · intro next member
    have observed : HSet.kpair (labels sort action) (readout right labels base sort next) ∈
        readout left labels base sort first := by
      rw [same, readout_members]
      exact ⟨action, next, member, rfl⟩
    obtain ⟨otherAction, other, present, equal⟩ := (readout_members _ _ _ _ _ _).mp observed
    obtain ⟨labelEq, stateEq⟩ := HSet.kpair_inj.mp equal
    have actionEq := faithful sort labelEq
    subst otherAction
    exact ⟨other, present, stateEq.symm⟩

theorem readout_eq_iff_bisimilar
    (left right : Coalgebra (S := S) (Actions := Actions))
    (labels : (sort : S.Srt) → Actions sort → HSet.{u})
    (faithful : ∀ sort, Function.Injective (labels sort))
    (base : PUnit.{u + 1}) (sort : S.Srt) (first : left.V base sort) (second : right.V base sort) :
    readout left labels base sort first = readout right labels base sort second ↔
      Bisimulation.Bisimilar left right base sort first second :=
  ⟨fun same => ⟨_, readout_kernel_admitted left right labels faithful, same⟩,
    readout_eq_of_bisimilar labels base sort⟩

/-- The material and final-tree readings identify exactly the same states. -/
theorem readout_eq_iff_observe_eq
    (left right : Coalgebra (S := S) (Actions := Actions))
    (labels : (sort : S.Srt) → Actions sort → HSet.{u})
    (faithful : ∀ sort, Function.Injective (labels sort))
    (base : PUnit.{u + 1}) (sort : S.Srt) (first : left.V base sort) (second : right.V base sort) :
    readout left labels base sort first = readout right labels base sort second ↔
      (FinalSemantics.observe S Actions left).f base sort first =
        (FinalSemantics.observe S Actions right).f base sort second :=
  (readout_eq_iff_bisimilar left right labels faithful base sort first second).trans
    (FinalSemantics.kernel_iff_bisimilar S Actions left right base sort first second).symm

/-- The unique compatible initial-to-final semantics has this exact material reading. -/
theorem initial_final_readout (law : Law S Actions)
    (labels : (sort : S.Srt) → Actions sort → HSet.{u})
    (base : PUnit.{u + 1}) (sort : S.Srt) (term : S.ClosedTerm sort) :
    readout (FinalSemantics.finalObject S Actions) labels base sort
        ((FinalBialgebra.semantics law).f.f base sort term) =
      readout (FinalBialgebra.closedOperational law) labels base sort term :=
  readout_natural (FinalBialgebra.semantics law).f labels base sort term

end Mettapedia.OSLF.FiniteBranching.HypersetSemantics

import Mettapedia.Cybernetics.HierarchicalComplexity.Finite

/-!
# Hierarchical rank under changes of observation

Observation postcomposes each supplied schedule readout and reclassifies it.
Occurrence families and leaves remain intact. Rank can decrease; preserving
Commons admissibility additionally needs control of child-rank homogeneity.
Classification of arbitrary schedule families is a classical construction.
-/

namespace Mettapedia.Cybernetics.HierarchicalComplexity

universe u v w z
variable {I : Type u} {A : Type v} {B : Type w} {C : Type z}

variable (q : A → B)

namespace Organization

noncomputable def classify (f : ScheduleSemantics I A) : Organization I A := by
  classical
  exact if h : IsChain f then .chain f h
    else .coordination f ((isCoordination_iff_not_isChain f).mpr h)

@[simp] theorem semantics_classify (f : ScheduleSemantics I A) : (classify f).semantics = f := by
  unfold classify; split <;> rfl

theorem semantics_injective : Function.Injective (semantics : Organization I A → _) := by
  intro first second same
  cases first <;> cases second <;> simp only [semantics] at same
  all_goals cases same
  all_goals first | rfl | exact False.elim (IsChain.not_coordination (by assumption) (by assumption))

noncomputable def observe (o : Organization I A) : Organization I B :=
  classify (q ∘ o.semantics)

@[simp] theorem semantics_observe (o : Organization I A) :
    (observe q o).semantics = q ∘ o.semantics := semantics_classify _

theorem observe_as_chain (o : Organization I A) (h : IsChain (q ∘ o.semantics)) :
    observe q o = .chain (q ∘ o.semantics) h := semantics_injective (semantics_observe q o)

@[simp] theorem observe_chain (f : ScheduleSemantics I A) (h : IsChain f) :
    observe q (.chain f h) = .chain (q ∘ f) (fun i j => congrArg q (h i j)) :=
  semantics_injective (semantics_observe q (.chain f h))

theorem observe_coordination (f : ScheduleSemantics I A)
    (h : IsCoordination f) (observed : IsCoordination (q ∘ f)) :
    observe q (.coordination f h) = .coordination (q ∘ f) observed :=
  semantics_injective (semantics_observe q (.coordination f h))

theorem observe_coordination_of_injective (injective : Function.Injective q)
    (f : ScheduleSemantics I A) (h : IsCoordination f) :
    IsCoordination (q ∘ f) := by
  obtain ⟨first, second, different⟩ := h
  exact ⟨first, second, fun same => different (injective same)⟩

theorem coordination_of_observed (f : ScheduleSemantics I A)
    (h : IsCoordination (q ∘ f)) : IsCoordination f := by
  obtain ⟨first, second, different⟩ := h
  exact ⟨first, second, fun same => different (congrArg q same)⟩

theorem chain_observed_iff (injective : Function.Injective q)
    (f : ScheduleSemantics I A) : IsChain (q ∘ f) ↔ IsChain f :=
  ⟨fun h i j => injective (h i j), fun h i j => congrArg q (h i j)⟩

theorem observe_coordination_injective (injective : Function.Injective q)
    (f : ScheduleSemantics I A) (h : IsCoordination f) :
    observe q (.coordination f h) = .coordination (q ∘ f) (observe_coordination_of_injective q injective f h) :=
  observe_coordination q f h _

@[simp] theorem observe_id (o : Organization I A) : observe id o = o :=
  semantics_injective (semantics_observe id o)

theorem observe_comp (r : B → C) (o : Organization I A) :
    observe r (observe q o) = observe (r ∘ q) o := by
  apply semantics_injective
  simp only [semantics_observe, Function.comp_assoc]

end Organization

namespace Action

noncomputable def observe : Action.{u,v} A → Action.{u,w} B :=
  Action.rec .simple (fun I two _ o children => .compound I two children (o.observe q))

@[simp] theorem observe_simple : observe q (.simple : Action.{u,v} A) = .simple := rfl

@[simp] theorem observe_compound (two : HasAtLeastTwo I)
    (child : I → Action.{u,v} A) (o : Organization I A) :
    observe q (.compound I two child o) =
      .compound I two (fun i => observe q (child i)) (o.observe q) := rfl

@[simp] theorem observe_id (a : Action.{u,v} A) : observe id a = a := by
  induction a <;> simp_all only [observe_simple, observe_compound, Organization.observe_id]

theorem observe_comp (r : B → C) (a : Action.{u,v} A) :
    observe r (observe q a) = observe (r ∘ q) a := by
  induction a <;> simp_all only [observe_simple, observe_compound, Organization.observe_comp]

theorem rank_observe_le (a : Action.{u,v} A) : rank (observe q a) ≤ rank a := by
  induction a with
  | simple => exact le_rfl
  | compound I two child o ih =>
      have below : childSup (fun i => observe q (child i)) ≤ childSup child :=
        Ordinal.iSup_le fun i => (ih i).trans (Ordinal.le_iSup (fun j => rank (child j)) i)
      cases o with
      | chain f h =>
          rw [observe_compound, Organization.observe_chain]
          exact below
      | coordination f h =>
          change rank (.compound I two _ (Organization.observe q (.coordination f h))) ≤ _
          rw [rank_coordination]
          cases Organization.observe q (.coordination f h) with
          | chain _ _ => exact below.trans (Order.le_succ _)
          | coordination _ _ => exact Order.succ_le_succ below

theorem rank_observe_of_injective (injective : Function.Injective q)
    (a : Action.{u,v} A) : rank (observe q a) = rank a := by
  induction a with
  | simple => rfl
  | compound I two child o ih =>
      cases o with
      | chain f h =>
          rw [observe_compound, Organization.observe_chain]
          change (⨆ i, rank (observe q (child i))) = ⨆ i, rank (child i)
          simp only [ih]
      | coordination f h =>
          simp only [observe_compound, Organization.observe_coordination_injective q injective,
            rank_coordination, ih]

theorem rank_observe_comp_le (r : B → C) (a : Action.{u,v} A) :
    rank (observe (r ∘ q) a) ≤ rank (observe q a) := by
  rw [← observe_comp]
  exact rank_observe_le r _

/-- The interpretation retains the entire occurrence-indexed family of leaves. -/
noncomputable def observedLeavesEquiv (a : Action.{u,v} A) :
    SimpleLeaves (observe q a) ≃ SimpleLeaves a := by
  induction a with
  | simple => exact Equiv.refl _
  | compound I two child o ih => exact Equiv.sigmaCongrRight ih

theorem simpleLeafCardinal_observe (a : Action.{u,v} A) :
    simpleLeafCardinal (observe q a) = simpleLeafCardinal a :=
  Cardinal.mk_congr (observedLeavesEquiv q a)

theorem finitelyBranching_observe (a : Action.{u,v} A) :
    FinitelyBranching (observe q a) ↔ FinitelyBranching a := by
  induction a <;> simp_all only [observe_simple, observe_compound,
    finitelyBranching_simple, finitelyBranching_compound]

theorem commonsAdmissible_observe_iff (injective : Function.Injective q)
    (a : Action.{u,v} A) : CommonsAdmissible (observe q a) ↔ CommonsAdmissible a := by
  induction a with
  | simple => rfl
  | compound I two child o ih =>
      cases o <;> simp only [observe_compound, Organization.observe_chain,
        Organization.observe_coordination_injective q injective, CommonsAdmissible,
        ih, rank_observe_of_injective q injective]

end Action

namespace Finite.Action

/-- Finite Commons actions transport when the observer preserves distinctions. -/
noncomputable def observe (injective : Function.Injective q)
    (a : Finite.Action.{u,v} A) : Finite.Action.{u,w} B where
  toAmbient := a.toAmbient.observe q
  finitelyBranching := (Action.finitelyBranching_observe q _).mpr a.finitelyBranching
  commonsAdmissible := (Action.commonsAdmissible_observe_iff q injective _).mpr a.commonsAdmissible

theorem order_observe (injective : Function.Injective q)
    (a : Finite.Action.{u,v} A) : (observe q injective a).order = a.order := by
  exact (order_eq_iff _ _).mpr
    ((Action.rank_observe_of_injective q injective a.toAmbient).trans a.rank_eq_natCast_order)

theorem simpleLeafCount_observe (injective : Function.Injective q)
    (a : Finite.Action.{u,v} A) : (observe q injective a).simpleLeafCount = a.simpleLeafCount :=
  Nat.card_congr (Action.observedLeavesEquiv q a.toAmbient)

end Finite.Action

namespace ObserverControls
open LimitCanary

/-- False selects an erased distinction; true selects a retained one. -/
def contrast (retained : Bool) : ScheduleSemantics (Fin 2) (Fin 3) :=
  fun schedule => if schedule 0 = 0 then 0 else if retained then 2 else 1

theorem contrast_sensitive (retained : Bool) : IsCoordination (contrast retained) := by
  cases retained <;> exact ⟨Equiv.refl _, Equiv.swap 0 1, by decide⟩

def coarse (x : Fin 3) : Bool := x == 2

def leafPair (retained : Bool) : Action.{0,0} (Fin 3) :=
  .compound (Fin 2) binary_hasAtLeastTwo (fun _ => .simple)
    (.coordination (contrast retained) (contrast_sensitive retained))

theorem erased_chain : IsChain (coarse ∘ contrast false) := by
  intro i j
  simp only [Function.comp_apply, contrast, coarse]
  split_ifs <;> simp_all

theorem retained_coordination : IsCoordination (coarse ∘ contrast true) :=
  ⟨Equiv.refl _, Equiv.swap 0 1, by decide⟩

theorem leafPair_rank (retained : Bool) : (leafPair retained).rank = 1 := by
  simp [leafPair, Action.rank_coordination, Action.rank_simple, ciSup_const, Order.succ_eq_add_one]

theorem observed_pair_ranks : (Action.observe coarse (leafPair false)).rank = 0 ∧
    (Action.observe coarse (leafPair true)).rank = 1 := by
  constructor
  · rw [leafPair, Action.observe_compound,
      Organization.observe_as_chain coarse (.coordination _ (contrast_sensitive false)) erased_chain]
    change (⨆ _ : Fin 2, (0 : Ordinal)) = 0
    exact ciSup_const
  · simp only [leafPair, Action.observe_compound,
      Organization.observe_coordination coarse _ (contrast_sensitive true) retained_coordination,
      Action.rank_coordination, Action.observe_simple, Action.rank_simple, ciSup_const,
      Order.succ_eq_add_one, zero_add]

theorem strict_rank_drop : (leafPair false).rank = 1 ∧
    (Action.observe coarse (leafPair false)).rank = 0 := ⟨leafPair_rank _, observed_pair_ranks.1⟩

def parent : Action.{0,0} (Fin 3) :=
  .compound (Fin 2) binary_hasAtLeastTwo (fun i => leafPair (i == 1))
    (.coordination (contrast true) (contrast_sensitive true))

theorem coarsening_breaks_admissibility : parent.CommonsAdmissible ∧
    ¬ (Action.observe coarse parent).CommonsAdmissible := by
  constructor
  · exact ⟨fun _ => ⟨fun _ => trivial, fun _ _ => rfl⟩,
      fun _ _ => (leafPair_rank _).trans (leafPair_rank _).symm⟩
  · intro admissible
    simp only [parent, Action.observe_compound,
      Organization.observe_coordination coarse _ (contrast_sensitive true) retained_coordination,
      Action.CommonsAdmissible] at admissible
    have unequal := admissible.2 (0 : Fin 2) (1 : Fin 2)
    simp only [show ((0 : Fin 2) == 1) = false from rfl, show ((1 : Fin 2) == 1) = true from rfl,
      observed_pair_ranks.1, observed_pair_ranks.2] at unequal
    exact zero_ne_one unequal

end ObserverControls
end Mettapedia.Cybernetics.HierarchicalComplexity

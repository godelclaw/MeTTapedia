import Mettapedia.GSLT.OpenEnded.DisjunctiveBubbles
import Mathlib.Logic.Relation

/-!
# The principal requests: a sub-fibration closed under conjunction

Every request determines its sufficiency upset (`DisjunctiveBubbles`), so the
space of requests is the lattice `UpperSet B` of upper sets of the bubble
order (for a finite bubble order, its upper powerdomain). Over it sits the
generic sufficiency family: pairs of a request and a bubble sufficient for it
(`Total`). Its projection to the request is a fibration (`proj_fibration`)
whose lifts are cartesian (`lift_cartesian`), and whose fiber over a request
is that request's upset (`fiber_eq`).

The requests with a least sufficient bubble are the principal points
(`Principal`, `mem_principal_iff`). They form a sub-fibration with these
properties:

* **Localized.** Being principal is a property of one fiber
  (`mem_principal_iff`); over the principal requests the projection is again a
  fibration (`principal_fibration`), with a monotone section choosing the
  least bubble (`leastBubble_isLeast`, `leastBubble_monotone`). The total space
  over the principal requests is the order of pairs `a ≤ b` of bubbles
  (`principalTotalIso`): the arrow order of the bubble order itself.
* **Closed under conjunction, not disjunction.** Both of two principal
  requests, and all of any family, are principal (`principal_sup`,
  `principal_sSup`); either of two principal requests is principal only for
  comparable bubbles (`principal_inf_iff`).
* **Proper, and generating.** Whenever two bubbles are incomparable there is
  a request that is not principal (`principal_proper`). Every request is the
  disjunction (meet) of the principal requests it implies
  (`eq_sInf_principal`).
* **Where it is used.** Over the principal requests the least bubble is a
  canonical choice; for requests given by Horn clauses it is the Horn closure,
  computed by forward chaining under any fair schedule
  (`SufficientBubbles.isLeast_hornClosure`,
  `ChaoticIteration.fair_firing_computes_hornClosure`).

Observers. An observer is a set of observations, and its upset is the join of
theirs, so more observations always make a more demanding request
(`observerUpset_mono`). Having a least bubble is neither monotone nor antitone
in the observer (`principal_neither_monotone_nor_antitone`). Over sets of
generators, an observer has a least bubble exactly when it is equivalent to a
set of point requirements "retain `g`" (`principal_iff_atomic`). For
reachability observers, a saturated observer, whose observed targets are
reachable through observed targets, has the least carrier "source plus
targets" (`isLeast_saturated`); the full reachability observer is saturated
(`cone_saturated`); in the diamond, observing `d` alone is not saturated
(`diamond_single_not_saturated`), and observing `b` and `d` is
(`diamond_through_b_isLeast`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.OpenEnded.CarveOut

open Set
open Mettapedia.GSLT.OpenEnded.DisjunctiveBubbles

universe u v

theorem Ici_le_Ici_iff {B : Type u} [PartialOrder B] {a b : B} :
    UpperSet.Ici a ≤ UpperSet.Ici b ↔ a ≤ b := by
  rw [UpperSet.le_Ici, UpperSet.mem_Ici_iff]

/-! ## The generic sufficiency fibration -/

section Fibration

variable {B : Type u} [PartialOrder B]

/-- A request, given by its upset, with a bubble sufficient for it. -/
def Total (B : Type u) [PartialOrder B] : Type u :=
  {p : UpperSet B × B // p.2 ∈ p.1}

instance : PartialOrder (Total B) :=
  Subtype.partialOrder _

/-- The request of a pair. -/
def proj : Total B →o UpperSet B :=
  ⟨fun e => e.1.1, fun _ _ le => le.1⟩

/-- The bubble of a pair. -/
def bubbleOf (e : Total B) : B :=
  e.1.2

/-- Weakening the request keeps the bubble sufficient. -/
def lift (e : Total B) (U : UpperSet B) (le : U ≤ proj e) : Total B :=
  ⟨(U, e.1.2), UpperSet.coe_subset_coe.mpr le e.2⟩

theorem proj_lift (e : Total B) (U : UpperSet B) (le : U ≤ proj e) : proj (lift e U le) = U :=
  rfl

theorem lift_le (e : Total B) (U : UpperSet B) (le : U ≤ proj e) : lift e U le ≤ e :=
  ⟨le, le_rfl⟩

/-- **The projection to the request is a fibration.** -/
theorem proj_fibration : Relation.Fibration (· ≤ ·) (· ≤ ·) (proj : Total B → UpperSet B) :=
  fun e U le => ⟨lift e U le, lift_le e U le, rfl⟩

/-- **Its lifts are cartesian.** -/
theorem lift_cartesian (e : Total B) (U : UpperSet B) (le : U ≤ proj e) {e' : Total B}
    (below : e' ≤ e) (over : proj e' ≤ U) : e' ≤ lift e U le :=
  ⟨over, below.2⟩

/-- **The fiber over a request is its upset.** -/
theorem fiber_eq (U : UpperSet B) : bubbleOf '' (proj ⁻¹' {U}) = (U : Set B) := by
  ext b
  constructor
  · rintro ⟨e, over, rfl⟩
    have same : e.1.1 = U := over
    exact same ▸ e.2
  · intro member
    exact ⟨⟨(U, b), member⟩, rfl, rfl⟩

/-! ## The principal requests -/

/-- The requests with a least sufficient bubble. -/
def Principal : Set (UpperSet B) :=
  range UpperSet.Ici

/-- **Being principal is a property of one fiber.** -/
theorem mem_principal_iff (U : UpperSet B) : U ∈ Principal ↔ ∃ m, IsLeast (U : Set B) m := by
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨m, UpperSet.mem_Ici_iff.mpr le_rfl, fun _ member => UpperSet.mem_Ici_iff.mp member⟩
  · rintro ⟨m, member, lower⟩
    refine ⟨m, SetLike.ext fun x => ?_⟩
    rw [UpperSet.mem_Ici_iff]
    exact ⟨fun le => U.upper le member, fun inU => lower inU⟩

/-- The least bubble of a principal request. -/
noncomputable def leastBubble (U : (Principal : Set (UpperSet B))) : B :=
  Classical.choose U.2

theorem Ici_leastBubble (U : (Principal : Set (UpperSet B))) : UpperSet.Ici (leastBubble U) = U.1 :=
  Classical.choose_spec U.2

theorem leastBubble_isLeast (U : (Principal : Set (UpperSet B))) :
    IsLeast (U.1 : Set B) (leastBubble U) := by
  rw [← Ici_leastBubble U]
  exact ⟨UpperSet.mem_Ici_iff.mpr le_rfl, fun _ member => UpperSet.mem_Ici_iff.mp member⟩

/-- **The least-bubble section is monotone.** -/
theorem leastBubble_monotone : Monotone (leastBubble (B := B)) := by
  intro U V le
  have le' : UpperSet.Ici (leastBubble U) ≤ UpperSet.Ici (leastBubble V) := by
    rw [Ici_leastBubble, Ici_leastBubble]
    exact le
  exact Ici_le_Ici_iff.mp le'

theorem leastBubble_Ici (a : B) : leastBubble ⟨UpperSet.Ici a, a, rfl⟩ = a :=
  UpperSet.Ici_injective (Ici_leastBubble ⟨UpperSet.Ici a, a, rfl⟩)

/-- The pairs over principal requests. -/
def PrincipalTotal (B : Type u) [PartialOrder B] : Type u :=
  {e : Total B // proj e ∈ (Principal : Set (UpperSet B))}

instance : PartialOrder (PrincipalTotal B) :=
  Subtype.partialOrder _

/-- The request of a pair over a principal request. -/
def principalProj (e : PrincipalTotal B) : (Principal : Set (UpperSet B)) :=
  ⟨proj e.1, e.2⟩

/-- **Over the principal requests the projection is again a fibration.** -/
theorem principal_fibration : Relation.Fibration (· ≤ ·) (· ≤ ·) (principalProj : PrincipalTotal B → _) := by
  intro e U le
  exact ⟨⟨lift e.1 U.1 le, U.2⟩, lift_le e.1 U.1 le, rfl⟩

/-- **Over the principal requests the total space is the arrow order of the
bubbles.** -/
noncomputable def principalTotalIso : PrincipalTotal B ≃o {p : B × B // p.1 ≤ p.2} where
  toFun e := ⟨(leastBubble (principalProj e), e.1.1.2),
    (leastBubble_isLeast (principalProj e)).2 e.1.2⟩
  invFun p := ⟨⟨(UpperSet.Ici p.1.1, p.1.2), UpperSet.mem_Ici_iff.mpr p.2⟩, p.1.1, rfl⟩
  left_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    change (UpperSet.Ici (leastBubble (principalProj e)), e.1.1.2) = e.1.1
    rw [Ici_leastBubble]
    rfl
  right_inv p := by
    apply Subtype.ext
    change (leastBubble ⟨UpperSet.Ici p.1.1, p.1.1, rfl⟩, p.1.2) = p.1
    rw [leastBubble_Ici]
  map_rel_iff' := by
    intro e e'
    change (leastBubble (principalProj e) ≤ leastBubble (principalProj e') ∧ e.1.1.2 ≤ e'.1.1.2) ↔
      (e.1.1.1 ≤ e'.1.1.1 ∧ e.1.1.2 ≤ e'.1.1.2)
    have requests : leastBubble (principalProj e) ≤ leastBubble (principalProj e') ↔
        e.1.1.1 ≤ e'.1.1.1 := by
      rw [← Ici_le_Ici_iff, Ici_leastBubble, Ici_leastBubble]
      rfl
    rw [requests]

/-- **Either of two principal requests is principal only for comparable
bubbles.** -/
theorem principal_inf_iff (a b : B) :
    UpperSet.Ici a ⊓ UpperSet.Ici b ∈ (Principal : Set (UpperSet B)) ↔ a ≤ b ∨ b ≤ a := by
  rw [← inf_Ici_principal_iff]
  exact ⟨fun ⟨c, same⟩ => ⟨c, same.symm⟩, fun ⟨c, same⟩ => ⟨c, same.symm⟩⟩

/-- **The principal requests are proper**: incomparable bubbles give a request
that is not principal. -/
theorem principal_proper {a b : B} (notAB : ¬ a ≤ b) (notBA : ¬ b ≤ a) :
    UpperSet.Ici a ⊓ UpperSet.Ici b ∉ (Principal : Set (UpperSet B)) := by
  rw [principal_inf_iff]
  rintro (le | le)
  · exact notAB le
  · exact notBA le

/-- **Every request is the disjunction of the principal requests it
implies.** -/
theorem eq_sInf_principal (U : UpperSet B) :
    sInf {V | V ∈ (Principal : Set (UpperSet B)) ∧ U ≤ V} = U := by
  apply SetLike.ext
  intro x
  rw [← SetLike.mem_coe, UpperSet.coe_sInf, mem_iUnion₂]
  constructor
  · rintro ⟨_, ⟨⟨b, rfl⟩, le⟩, member⟩
    exact U.upper (UpperSet.mem_Ici_iff.mp member) (UpperSet.le_Ici.mp le)
  · intro member
    exact ⟨UpperSet.Ici x, ⟨⟨x, rfl⟩, UpperSet.le_Ici.mpr member⟩, UpperSet.mem_Ici_iff.mpr le_rfl⟩

end Fibration

/-! ## Conjunction stays principal -/

section Conjunction

/-- **Both of two principal requests is principal.** -/
theorem principal_sup {B : Type u} [SemilatticeSup B] {U V : UpperSet B}
    (principalU : U ∈ (Principal : Set (UpperSet B))) (principalV : V ∈ (Principal : Set (UpperSet B))) :
    U ⊔ V ∈ (Principal : Set (UpperSet B)) := by
  obtain ⟨a, rfl⟩ := principalU
  obtain ⟨b, rfl⟩ := principalV
  exact ⟨a ⊔ b, (sup_Ici a b).symm⟩

/-- **All of any family of principal requests is principal.** -/
theorem principal_sSup {B : Type u} [CompleteLattice B] {S : Set (UpperSet B)}
    (included : S ⊆ (Principal : Set (UpperSet B))) : sSup S ∈ (Principal : Set (UpperSet B)) := by
  have image : S = UpperSet.Ici '' {a | UpperSet.Ici a ∈ S} := by
    ext U
    constructor
    · intro member
      obtain ⟨a, rfl⟩ := included member
      exact ⟨a, member, rfl⟩
    · rintro ⟨a, member, rfl⟩
      exact member
  refine ⟨sSup {a | UpperSet.Ici a ∈ S}, ?_⟩
  rw [UpperSet.Ici_sSup]
  conv_rhs => rw [image]
  rw [sSup_image]

end Conjunction

/-! ## Observers -/

section Observers

variable {B : Type u} [PartialOrder B] {Obs : Type v}

/-- The upset of an observer: every observation must be met. -/
def observerUpset (upsetOf : Obs → UpperSet B) (O : Set Obs) : UpperSet B :=
  ⨆ o ∈ O, upsetOf o

/-- **More observations make a more demanding request.** -/
theorem observerUpset_mono (upsetOf : Obs → UpperSet B) : Monotone (observerUpset upsetOf) :=
  fun _ _ included => biSup_mono included

end Observers

/-- **Having a least bubble is neither monotone nor antitone in the
observer.** Adding the observation "retain `true`" to the choice "retain `true`
or retain `false`" creates a least bubble; adding the choice to the trivial
observation destroys one. -/
theorem principal_neither_monotone_nor_antitone :
    (UpperSet.Ici ({true} : Set Bool) ⊓ UpperSet.Ici {false} ∉ (Principal : Set (UpperSet (Set Bool))) ∧
      UpperSet.Ici ({true} : Set Bool) ⊔ (UpperSet.Ici {true} ⊓ UpperSet.Ici {false}) ∈
        (Principal : Set (UpperSet (Set Bool)))) ∧
    (UpperSet.Ici (∅ : Set Bool) ∈ (Principal : Set (UpperSet (Set Bool))) ∧
      UpperSet.Ici (∅ : Set Bool) ⊔ (UpperSet.Ici {true} ⊓ UpperSet.Ici {false}) ∉
        (Principal : Set (UpperSet (Set Bool)))) := by
  have notTF : ¬ ({true} : Set Bool) ⊆ {false} := fun inside => by
    have := inside (mem_singleton true)
    cases this
  have notFT : ¬ ({false} : Set Bool) ⊆ {true} := fun inside => by
    have := inside (mem_singleton false)
    cases this
  have choice := principal_proper notTF notFT
  refine ⟨⟨choice, ?_⟩, ⟨⟨∅, rfl⟩, ?_⟩⟩
  · rw [sup_inf_self]
    exact ⟨{true}, rfl⟩
  · have bottom : UpperSet.Ici (∅ : Set Bool) = ⊥ := UpperSet.Ici_bot
    rw [bottom, bot_sup_eq]
    exact choice

/-- **An observer over generators has a least bubble exactly when it is a set
of point requirements.** -/
theorem principal_iff_atomic {G : Type u} (U : UpperSet (Set G)) :
    U ∈ (Principal : Set (UpperSet (Set G))) ↔
      ∃ A : Set G, U = ⨆ g ∈ A, UpperSet.Ici ({g} : Set G) := by
  constructor
  · rintro ⟨m, rfl⟩
    refine ⟨m, ?_⟩
    rw [← UpperSet.Ici_iSup₂]
    congr 1
    rw [iSup_eq_iUnion]
    simp only [iSup_eq_iUnion]
    exact (biUnion_of_singleton m).symm
  · rintro ⟨A, rfl⟩
    refine ⟨⨆ g ∈ A, ({g} : Set G), ?_⟩
    exact UpperSet.Ici_iSup₂ _

/-! ## Reachability observers -/

section Reachability

open Mettapedia.GSLT
open CarrierBubbles

variable {S : GSLT}

/-- Reachability within a carrier is monotone in the carrier. -/
theorem reachWithin_mono {B B' : Set S.Term} (included : B ⊆ B') {t t' : S.Term}
    (path : ReachWithin B t t') : ReachWithin B' t t' := by
  induction path with
  | refl member => exact .refl (included member)
  | step member step _ ih => exact .step (included member) step ih

/-- Every observed target is reachable from the source inside the carrier. -/
def ObservesTargets (s : S.Term) (T : Set S.Term) (B : Set S.Term) : Prop :=
  ∀ t ∈ T, ReachWithin B s t

/-- The observed targets are reachable through observed targets. -/
def Saturated (s : S.Term) (T : Set S.Term) : Prop :=
  ∀ t ∈ T, ReachWithin (insert s T) s t

/-- **A saturated observer has the least carrier "source plus targets".** -/
theorem isLeast_saturated {s : S.Term} {T : Set S.Term} (nonempty : T.Nonempty)
    (saturated : Saturated s T) : IsLeast {B | ObservesTargets s T B} (insert s T) := by
  refine ⟨saturated, fun B observes => ?_⟩
  obtain ⟨t, memberT⟩ := nonempty
  intro x member
  rcases member with rfl | inT
  · exact (observes t memberT).source_mem
  · exact (observes x inT).target_mem

/-- **The full reachability observer is saturated.** -/
theorem cone_saturated (s : S.Term) : Saturated s (cone S {s}) := by
  intro t member
  have sufficient := (reachSufficient_iff {s} (cone S {s})).mpr subset_rfl
  obtain ⟨source, same, path⟩ := member
  rw [mem_singleton_iff] at same
  subst same
  exact reachWithin_mono (subset_insert _ _) ((sufficient source rfl t).mp path)

end Reachability

section Diamond

open CarrierBubbles Node

/-- **Observing `d` alone is not saturated.** -/
theorem diamond_single_not_saturated : ¬ Saturated (S := diamond) a {d} := by
  intro saturated
  obtain ⟨_, _, middle⟩ := single_needs (saturated d (mem_singleton d))
  rcases middle with inB | inC
  · rcases inB with absurd | absurd <;> cases absurd
  · rcases inC with absurd | absurd <;> cases absurd

/-- **Observing `b` and `d` is saturated, with least carrier `{a, b, d}`.** -/
theorem diamond_through_b_isLeast :
    IsLeast {B | ObservesTargets (S := diamond) a {b, d} B} {a, b, d} := by
  refine isLeast_saturated ⟨b, Or.inl rfl⟩ ?_
  intro t member
  rcases member with rfl | rfl
  · exact .step (Or.inl rfl) (show DiamondStep a b from .ab) (.refl (Or.inr (Or.inl rfl)))
  · exact .step (Or.inl rfl) (show DiamondStep a b from .ab)
      (.step (Or.inr (Or.inl rfl)) (show DiamondStep b d from .bd) (.refl (Or.inr (Or.inr rfl))))

end Diamond

#print axioms proj_fibration
#print axioms lift_cartesian
#print axioms fiber_eq
#print axioms mem_principal_iff
#print axioms leastBubble_isLeast
#print axioms leastBubble_monotone
#print axioms principal_fibration
#print axioms principalTotalIso
#print axioms principal_inf_iff
#print axioms principal_proper
#print axioms eq_sInf_principal
#print axioms principal_sup
#print axioms principal_sSup
#print axioms observerUpset_mono
#print axioms principal_neither_monotone_nor_antitone
#print axioms principal_iff_atomic
#print axioms isLeast_saturated
#print axioms cone_saturated
#print axioms diamond_single_not_saturated
#print axioms diamond_through_b_isLeast

end Mettapedia.GSLT.OpenEnded.CarveOut

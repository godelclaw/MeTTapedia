import Mettapedia.GSLT.Causality.FactStoreSaturation
import Mettapedia.Languages.MeTTa.WeightedAnswerAlgebra
import Mathlib.Data.Set.Semiring
import Mathlib.Data.ENat.Basic
import Mathlib.Order.OrderIsoNat

/-!
# Fact stores annotated in a semiring: one store for sets, bags and provenance

A fact store over a commutative semiring `K` gives every atom an annotation in `K`. Keep-only rules
derive annotations: a firing contributes its weight times the product of its reads' annotations, and
the contributions to an atom add up (`kStep`). Iterating from nothing gives the stages of the store
(`kStage`). Booleans give sets of facts, the natural numbers count derivations, other semirings give
provenance, cost or evidence (Green, Karvounarakis and Tannen, *Provenance semirings*, PODS 2007).

## One store, related by homomorphisms

* **A semiring homomorphism commutes with every stage** (`map_kStage`): changing the annotation after
  saturating equals saturating with the changed annotations.
* **The set store is the support of the derivation counts.** Over the natural numbers, with unit
  seeds and weights, an atom is in the set store's closure (`saturation` of `FactStoreSaturation`)
  exactly when some stage gives it a nonzero count (`mem_saturation_iff_count`). Through the support
  homomorphism `ℕ → Presence` the same holds for the two-element semiring of sets
  (`mem_saturation_iff_presence`).

## When saturation terminates

* **Finitely many atoms and finitely many annotations suffice** (`kStage_eventually_fixed`): over any
  canonically ordered commutative semiring the stages only grow (`kStage_monotone`), so they stop in a
  finite one, at a fixed point of the rules. Idempotence is not what is needed: counts saturating at a
  bound are finite and not idempotent.
* **Counting derivations of a recursive rule never stops** (`Controls.nat_stage`,
  `Controls.nat_never_fixed`). Over the completed naturals the rule has a least fixed point, the
  supremum `⊤` (`Controls.enat_fixed_point_top`): ω-continuity gives the fixed point, not termination.
* **Idempotence alone does not stop it either** (`Controls.lengths_never_fixed`): over sets of
  derivation lengths, an idempotent semiring with infinite ascending chains, the stages grow forever.
* **Sets stop at once** (`Controls.presence_stage`).

## When retraction by counting is exact

Counting maintenance keeps, for every atom, the number of one-step derivations from the current store
(`supportCount`), positive exactly when the atom is seeded or supported (`supportCount_pos_iff`).
Retracting a seed removes atoms whose count reaches zero until none does (`retractStage`).

* **Retraction never removes a derivable atom** (`saturation_subset_retractStage`).
* **For acyclic rules it is exact** (`retraction_exact_of_ranked`): when every read of a rule has a
  smaller rank than every atom it produces, a store in which every atom keeps a support lies inside the
  closure (`subset_saturation_of_ranked`), and retraction ends at the closure of the remaining seeds.
* **For a cycle it is not** (`Controls.counting_retraction_inexact_on_cycle`): two atoms that each
  derive the other keep each other's count positive after their seed is withdrawn, while the closure
  of no seeds is empty. Delete-and-rederive, or derivation identity, is needed there.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ResourceInteraction

open Mettapedia.Languages.MeTTa.WeightedAnswerAlgebra (Presence supportOfCount)

universe uRes uRule uK uL

namespace System

variable {R : Type uRes} [DecidableEq R] (S : System.{uRes, uRule} R)

/-! ## The annotated store -/

section Annotated

variable {K : Type uK} [CommSemiring K]

/-- What one firing of an instance contributes: its weight times the product of the annotations of
its reads. -/
def firingValue (weight : S.Entry → K) (f : R → K) (entry : S.Entry) : K :=
  weight entry * ((S.read entry.2).map f).prod

/-- **The annotated immediate-consequence step**: an atom's seed plus, for every catalogued instance,
the firing's contribution as many times as the instance produces the atom. -/
def kStep (catalogue : List S.Entry) (seed : R → K) (weight : S.Entry → K) (f : R → K) : R → K :=
  fun r => seed r +
    (catalogue.map fun entry => ((S.produce entry.2).count r : K) * S.firingValue weight f entry).sum

/-- The stages of the annotated store, from nothing. -/
def kStage (catalogue : List S.Entry) (seed : R → K) (weight : S.Entry → K) (n : ℕ) : R → K :=
  (S.kStep catalogue seed weight)^[n] 0

theorem kStage_zero (catalogue : List S.Entry) (seed : R → K) (weight : S.Entry → K) :
    S.kStage catalogue seed weight 0 = 0 := rfl

theorem kStage_succ (catalogue : List S.Entry) (seed : R → K) (weight : S.Entry → K) (n : ℕ) :
    S.kStage catalogue seed weight (n + 1) =
      S.kStep catalogue seed weight (S.kStage catalogue seed weight n) :=
  Function.iterate_succ_apply' _ _ _

/-- **A semiring homomorphism commutes with one step.** -/
theorem map_kStep {L : Type uL} [CommSemiring L] (φ : K →+* L) (catalogue : List S.Entry)
    (seed : R → K) (weight : S.Entry → K) (f : R → K) :
    (fun r => φ (S.kStep catalogue seed weight f r)) =
      S.kStep catalogue (φ ∘ seed) (φ ∘ weight) (φ ∘ f) := by
  funext r
  simp [kStep, firingValue, map_list_sum, List.map_map, map_multiset_prod, Multiset.map_map,
    Function.comp_def]

/-- **A semiring homomorphism commutes with every stage**: annotating differently after saturating is
saturating with the changed annotations. -/
theorem map_kStage {L : Type uL} [CommSemiring L] (φ : K →+* L) (catalogue : List S.Entry)
    (seed : R → K) (weight : S.Entry → K) (n : ℕ) :
    (fun r => φ (S.kStage catalogue seed weight n r)) =
      S.kStage catalogue (φ ∘ seed) (φ ∘ weight) n := by
  induction n with
  | zero => funext r; simp [kStage_zero]
  | succ n ih =>
      rw [kStage_succ, kStage_succ, map_kStep, ← ih]
      rfl

end Annotated

/-! ## Canonically ordered annotations: the stages grow, and stop when finite -/

section Ordered

variable {K : Type uK} [CommSemiring K] [PartialOrder K] [CanonicallyOrderedAdd K]
  [IsOrderedAddMonoid K]

omit [DecidableEq R] [IsOrderedAddMonoid K] in
theorem prod_map_mono (reads : Multiset R) {f g : R → K} (le : f ≤ g) :
    (reads.map f).prod ≤ (reads.map g).prod := by
  induction reads using Multiset.induction_on with
  | empty => simp
  | cons a reads ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons]
      exact mul_le_mul' (le a) ih

/-- **The step is monotone.** -/
theorem kStep_mono (catalogue : List S.Entry) (seed : R → K) (weight : S.Entry → K) {f g : R → K}
    (le : f ≤ g) : S.kStep catalogue seed weight f ≤ S.kStep catalogue seed weight g := by
  intro r
  exact add_le_add le_rfl (List.sum_le_sum fun entry _ =>
    mul_le_mul' le_rfl (mul_le_mul' le_rfl (prod_map_mono _ le)))

/-- **The stages only grow.** -/
theorem kStage_monotone (catalogue : List S.Entry) (seed : R → K) (weight : S.Entry → K) :
    Monotone (S.kStage catalogue seed weight) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero => exact fun r => zero_le
  | succ n ih =>
      rw [kStage_succ, kStage_succ (n := n + 1)]
      exact S.kStep_mono catalogue seed weight ih

/-- **With finitely many atoms and annotations the stages stop, at a fixed point of the rules.** -/
theorem kStage_eventually_fixed [Finite K] [Finite R] (catalogue : List S.Entry) (seed : R → K)
    (weight : S.Entry → K) :
    ∃ N, (∀ n, N ≤ n → S.kStage catalogue seed weight n = S.kStage catalogue seed weight N) ∧
      S.kStep catalogue seed weight (S.kStage catalogue seed weight N) =
        S.kStage catalogue seed weight N := by
  have : WellFoundedGT (R → K) := Finite.to_wellFoundedGT
  obtain ⟨N, stable⟩ := WellFoundedGT.monotone_chain_condition
    ⟨S.kStage catalogue seed weight, S.kStage_monotone catalogue seed weight⟩
  refine ⟨N, fun n le => (stable n le).symm, ?_⟩
  rw [← kStage_succ]
  exact (stable (N + 1) (Nat.le_succ N)).symm

end Ordered

/-! ## The set store is the support of the derivation counts -/

section Support

theorem nat_list_sum_ne_zero_iff (l : List ℕ) : l.sum ≠ 0 ↔ ∃ x ∈ l, x ≠ 0 := by
  rw [Ne, List.sum_eq_zero_iff]
  simp only [not_forall, exists_prop]

theorem nat_add_ne_zero_iff (a b : ℕ) : a + b ≠ 0 ↔ a ≠ 0 ∨ b ≠ 0 := by
  omega

/-- The derivation counts with unit seeds on a set of atoms and unit weights. -/
noncomputable def countStage (catalogue : List S.Entry) (seed : Set R) (n : ℕ) : R → ℕ :=
  open Classical in S.kStage catalogue (fun r => if r ∈ seed then 1 else 0) (fun _ => 1) n

theorem countStage_succ_ne_zero_iff (catalogue : List S.Entry) (seed : Set R) (n : ℕ) (r : R) :
    S.countStage catalogue seed (n + 1) r ≠ 0 ↔
      r ∈ seed ∨ ∃ entry ∈ catalogue, r ∈ S.produce entry.2 ∧
        ∀ a ∈ S.read entry.2, S.countStage catalogue seed n a ≠ 0 := by
  classical
  unfold countStage
  rw [kStage_succ]
  simp only [kStep, firingValue, one_mul, nat_add_ne_zero_iff, nat_list_sum_ne_zero_iff,
    List.mem_map, Nat.cast_id]
  apply or_congr
  · by_cases h : r ∈ seed <;> simp [h]
  · constructor
    · rintro ⟨_, ⟨entry, member, rfl⟩, nonzero⟩
      refine ⟨entry, member, ?_, ?_⟩
      · exact Multiset.count_ne_zero.mp (left_ne_zero_of_mul nonzero)
      · intro a inRead
        have prodNonzero := right_ne_zero_of_mul nonzero
        rw [Ne, Multiset.prod_eq_zero_iff] at prodNonzero
        exact fun zero => prodNonzero (Multiset.mem_map.mpr ⟨a, inRead, zero⟩)
    · rintro ⟨entry, member, produced, reads⟩
      refine ⟨_, ⟨entry, member, rfl⟩, mul_ne_zero (Multiset.count_ne_zero.mpr produced) ?_⟩
      rw [Ne, Multiset.prod_eq_zero_iff]
      intro zeroIn
      obtain ⟨a, inRead, zero⟩ := Multiset.mem_map.mp zeroIn
      exact reads a inRead zero

theorem countStage_monotone (catalogue : List S.Entry) (seed : Set R) :
    Monotone (S.countStage catalogue seed) := by
  classical
  exact S.kStage_monotone catalogue _ _

/-- **An atom is in the set store's closure exactly when some stage counts a derivation of it.** -/
theorem mem_saturation_iff_count (catalogue : List S.Entry) (seed : Set R) (r : R) :
    r ∈ S.saturation {entry | entry ∈ catalogue} seed ↔ ∃ n, S.countStage catalogue seed n r ≠ 0 := by
  have least := S.saturation_isLeast {entry | entry ∈ catalogue} seed
  constructor
  · intro member
    let U : Set R := {r | ∃ n, S.countStage catalogue seed n r ≠ 0}
    have closed : seed ≤ U ∧ ∀ entry : {entry | entry ∈ catalogue}, S.setRule entry.1.2 U ≤ U := by
      refine ⟨fun r seeded => ⟨1, (S.countStage_succ_ne_zero_iff catalogue seed 0 r).mpr
        (Or.inl seeded)⟩, ?_⟩
      rintro ⟨entry, inCatalogue⟩ r ⟨readsIn, produced⟩
      choose stage hstage using readsIn
      let N := ((S.read entry.2).attach.map fun a => stage a.1 a.2).sup
      have atN : ∀ a ∈ S.read entry.2, S.countStage catalogue seed N a ≠ 0 := by
        intro a inRead
        have le : stage a inRead ≤ N :=
          Multiset.le_sup (Multiset.mem_map.mpr ⟨⟨a, inRead⟩, Multiset.mem_attach _ _, rfl⟩)
        exact fun zero => hstage a inRead
          (Nat.eq_zero_of_le_zero (zero ▸ S.countStage_monotone catalogue seed le a))
      exact ⟨N + 1, (S.countStage_succ_ne_zero_iff catalogue seed N r).mpr
        (Or.inr ⟨entry, inCatalogue, produced, atN⟩)⟩
    exact least.2 closed member
  · rintro ⟨n, nonzero⟩
    induction n generalizing r with
    | zero => exact absurd rfl nonzero
    | succ n ih =>
        rcases (S.countStage_succ_ne_zero_iff catalogue seed n r).mp nonzero with seeded |
          ⟨entry, member, produced, reads⟩
        · exact least.1.1 seeded
        · exact least.1.2 ⟨entry, member⟩ ⟨fun a inRead => ih a (reads a inRead), produced⟩

/-- **Through the support homomorphism, the same holds for the two-element semiring of sets.** -/
theorem mem_saturation_iff_presence (catalogue : List S.Entry) (seed : Set R) (r : R) :
    r ∈ S.saturation {entry | entry ∈ catalogue} seed ↔
      ∃ n, (S.kStage catalogue (supportOfCount ∘ fun r => open Classical in
        if r ∈ seed then 1 else 0) (supportOfCount ∘ fun _ => 1) n r).present = true := by
  rw [mem_saturation_iff_count]
  apply exists_congr
  intro n
  have mapped := congrFun (S.map_kStage supportOfCount catalogue
    (open Classical in fun r => if r ∈ seed then 1 else 0) (fun _ => 1) n) r
  rw [← mapped]
  show _ ↔ decide (_ ≠ 0) = true
  simp [countStage]

end Support

/-! ## Retraction by counting -/

section Retraction

/-- The atoms seeded or produced by a catalogued instance whose reads are all in `X`. -/
def supported (catalogue : List S.Entry) (seed X : Set R) : Set R :=
  seed ∪ {r | ∃ entry ∈ catalogue, r ∈ S.produce entry.2 ∧ ∀ a ∈ S.read entry.2, a ∈ X}

omit [DecidableEq R] in
theorem supported_mono (catalogue : List S.Entry) (seed : Set R) {X Y : Set R} (le : X ⊆ Y) :
    S.supported catalogue seed X ⊆ S.supported catalogue seed Y := by
  rintro r (seeded | ⟨entry, member, produced, reads⟩)
  · exact Or.inl seeded
  · exact Or.inr ⟨entry, member, produced, fun a inRead => le (reads a inRead)⟩

/-- **The count counting maintenance keeps**: the seed plus the number of one-step derivations from
`X`. -/
noncomputable def supportCount (catalogue : List S.Entry) (seed X : Set R) (r : R) : ℕ :=
  open Classical in
  (if r ∈ seed then 1 else 0) +
    ((catalogue.filter fun entry => ∀ a ∈ S.read entry.2, a ∈ X).map
      fun entry => (S.produce entry.2).count r).sum

/-- **The count is positive exactly when the atom is seeded or supported.** -/
theorem supportCount_pos_iff (catalogue : List S.Entry) (seed X : Set R) (r : R) :
    S.supportCount catalogue seed X r ≠ 0 ↔ r ∈ S.supported catalogue seed X := by
  classical
  simp only [supportCount, supported, nat_add_ne_zero_iff, nat_list_sum_ne_zero_iff, List.mem_map,
    List.mem_filter, Set.mem_union, Set.mem_ofPred_eq]
  apply or_congr
  · by_cases h : r ∈ seed <;> simp [h]
  · constructor
    · rintro ⟨_, ⟨entry, ⟨member, reads⟩, rfl⟩, nonzero⟩
      exact ⟨entry, member, Multiset.count_ne_zero.mp nonzero, by simpa using reads⟩
    · rintro ⟨entry, member, produced, reads⟩
      exact ⟨_, ⟨entry, ⟨member, by simpa using reads⟩, rfl⟩, Multiset.count_ne_zero.mpr produced⟩

/-- **One round of retraction**: drop every atom whose count is zero. -/
def retractStep (catalogue : List S.Entry) (seed X : Set R) : Set R :=
  X ∩ S.supported catalogue seed X

/-- The rounds of retraction from the old store. -/
def retractStage (catalogue : List S.Entry) (seed old : Set R) (k : ℕ) : Set R :=
  (S.retractStep catalogue seed)^[k] old

omit [DecidableEq R] in
theorem retractStage_succ (catalogue : List S.Entry) (seed old : Set R) (k : ℕ) :
    S.retractStage catalogue seed old (k + 1) =
      S.retractStep catalogue seed (S.retractStage catalogue seed old k) :=
  Function.iterate_succ_apply' _ _ _

omit [DecidableEq R] in
theorem retractStage_antitone (catalogue : List S.Entry) (seed old : Set R) :
    Antitone (S.retractStage catalogue seed old) := by
  apply antitone_nat_of_succ_le
  intro k
  rw [retractStage_succ]
  exact Set.inter_subset_left

omit [DecidableEq R] in
/-- The closure is closed under support: everything in it keeps a support in it. -/
theorem saturation_subset_supported (catalogue : List S.Entry) (seed : Set R) :
    S.saturation {entry | entry ∈ catalogue} seed ⊆
      S.supported catalogue seed (S.saturation {entry | entry ∈ catalogue} seed) := by
  have least := S.saturation_isLeast {entry | entry ∈ catalogue} seed
  apply least.2
  refine ⟨fun r seeded => Or.inl seeded, ?_⟩
  rintro ⟨entry, member⟩ r ⟨reads, produced⟩
  refine Or.inr ⟨entry, member, produced, fun a inRead => ?_⟩
  rcases reads a inRead with seeded | ⟨other, otherIn, otherProduced, otherReads⟩
  · exact least.1.1 seeded
  · exact least.1.2 ⟨other, otherIn⟩ ⟨otherReads, otherProduced⟩

omit [DecidableEq R] in
/-- **Retraction never removes a derivable atom**: the closure of the remaining seeds stays inside every
round, when it was inside the old store. -/
theorem saturation_subset_retractStage (catalogue : List S.Entry) (seed old : Set R)
    (inside : S.saturation {entry | entry ∈ catalogue} seed ⊆ old) (k : ℕ) :
    S.saturation {entry | entry ∈ catalogue} seed ⊆ S.retractStage catalogue seed old k := by
  induction k with
  | zero => exact inside
  | succ k ih =>
      rw [retractStage_succ]
      exact Set.subset_inter ih ((S.saturation_subset_supported catalogue seed).trans
        (S.supported_mono catalogue seed ih))

/-- A rank that strictly increases from every read of a catalogued instance to everything it
produces. -/
def Ranked (catalogue : List S.Entry) (rank : R → ℕ) : Prop :=
  ∀ entry ∈ catalogue, ∀ r ∈ S.produce entry.2, ∀ a ∈ S.read entry.2, rank a < rank r

omit [DecidableEq R] in
/-- **For acyclic rules, a store in which every atom keeps a support lies inside the closure.** -/
theorem subset_saturation_of_ranked (catalogue : List S.Entry) (seed : Set R) {rank : R → ℕ}
    (ranked : S.Ranked catalogue rank) {X : Set R} (keeps : X ⊆ S.supported catalogue seed X) :
    X ⊆ S.saturation {entry | entry ∈ catalogue} seed := by
  have least := S.saturation_isLeast {entry | entry ∈ catalogue} seed
  suffices ∀ n, ∀ r ∈ X, rank r = n → r ∈ S.saturation {entry | entry ∈ catalogue} seed from
    fun r member => this _ r member rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro r member hr
      rcases keeps member with seeded | ⟨entry, inCatalogue, produced, reads⟩
      · exact least.1.1 seeded
      · refine least.1.2 ⟨entry, inCatalogue⟩ ⟨fun a inRead => ?_, produced⟩
        exact ih (rank a) (hr ▸ ranked entry inCatalogue r produced a inRead) a (reads a inRead) rfl

omit [DecidableEq R] in
/-- **For acyclic rules, retraction by counting is exact**: from any old store containing the closure
of the remaining seeds, the rounds end at that closure. -/
theorem retraction_exact_of_ranked [Finite R] (catalogue : List S.Entry) (seed old : Set R)
    {rank : R → ℕ} (ranked : S.Ranked catalogue rank)
    (inside : S.saturation {entry | entry ∈ catalogue} seed ⊆ old) :
    ∃ K, ∀ k, K ≤ k →
      S.retractStage catalogue seed old k = S.saturation {entry | entry ∈ catalogue} seed := by
  have : WellFoundedLT (Set R) := Finite.to_wellFoundedLT
  obtain ⟨K, stable⟩ := WellFoundedLT.antitone_chain_condition
    (S.retractStage_antitone catalogue seed old)
  have keeps : S.retractStage catalogue seed old K ⊆
      S.supported catalogue seed (S.retractStage catalogue seed old K) := by
    have fixed := stable (K + 1) (Nat.le_succ K)
    rw [retractStage_succ] at fixed
    intro r member
    rw [fixed] at member
    exact member.2
  have atK : S.retractStage catalogue seed old K = S.saturation {entry | entry ∈ catalogue} seed :=
    Set.Subset.antisymm (S.subset_saturation_of_ranked catalogue seed ranked keeps)
      (S.saturation_subset_retractStage catalogue seed old inside K)
  exact ⟨K, fun k le => (stable k le).symm.trans atK⟩

end Retraction

end System

/-! ## Controls -/

namespace SemiringControls

open _root_.Mettapedia.GSLT.Causality.ResourceInteraction.System

/-- One atom and one rule that reads it and produces it. -/
def selfFeeding : System Unit where
  Site := Unit
  Instance := fun _ => Unit
  consume := fun _ => 0
  read := fun _ => {()}
  produce := fun _ => {()}

def selfCatalogue : List selfFeeding.Entry := [⟨(), ()⟩]

theorem selfFeeding_kStep {K : Type uK} [CommSemiring K] (seed : Unit → K) (weight : selfFeeding.Entry → K)
    (f : Unit → K) :
    selfFeeding.kStep selfCatalogue seed weight f () = seed () + weight ⟨(), ()⟩ * f () := by
  simp [kStep, firingValue, selfCatalogue, selfFeeding]

/-- **Counting derivations of a recursive rule never stops**: stage `n` counts `n`. -/
theorem nat_stage (n : ℕ) : selfFeeding.kStage selfCatalogue (fun _ => (1 : ℕ)) (fun _ => 1) n () = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [kStage_succ, selfFeeding_kStep, ih]
      omega

theorem nat_never_fixed (N : ℕ) :
    selfFeeding.kStage selfCatalogue (fun _ => (1 : ℕ)) (fun _ => 1) (N + 1) ≠
      selfFeeding.kStage selfCatalogue (fun _ => (1 : ℕ)) (fun _ => 1) N := by
  intro same
  have := congrFun same ()
  rw [nat_stage, nat_stage] at this
  omega

/-- **Over the completed naturals the only fixed point of the rule is the supremum `⊤`.** -/
theorem enat_fixed_point_top (f : Unit → ℕ∞)
    (fixed : selfFeeding.kStep selfCatalogue (fun _ => 1) (fun _ => 1) f = f) : f () = ⊤ := by
  have atUnit := congrFun fixed ()
  rw [selfFeeding_kStep, one_mul] at atUnit
  by_contra notTop
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp notTop
  rw [← hm] at atUnit
  have castEq : ((1 + m : ℕ) : ℕ∞) = (m : ℕ∞) := by
    push_cast
    exact atUnit
  have := Nat.cast_injective castEq
  omega

/-- **Sets stop at once**: from the first stage on, the atom is present. -/
theorem presence_stage (n : ℕ) :
    (selfFeeding.kStage selfCatalogue (supportOfCount ∘ fun _ => (1 : ℕ)) (supportOfCount ∘ fun _ => 1)
      (n + 1) ()).present = true := by
  have mapped := congrFun (selfFeeding.map_kStage supportOfCount selfCatalogue (fun _ => (1 : ℕ))
    (fun _ => 1) (n + 1)) ()
  rw [← mapped, nat_stage]
  simp [supportOfCount]

/-- Sets of derivation lengths: an idempotent semiring with infinite ascending chains. -/
abbrev Lengths := SetSemiring (Multiplicative ℕ)

/-- One more step of derivation. -/
def oneStep : Lengths := Set.up {Multiplicative.ofAdd 1}

theorem lengths_stage (n : ℕ) :
    (selfFeeding.kStage selfCatalogue (fun _ => (1 : Lengths)) (fun _ => oneStep) n ()).down =
      {x | Multiplicative.toAdd x < n} := by
  induction n with
  | zero =>
      simp [kStage_zero]
  | succ n ih =>
      rw [kStage_succ, selfFeeding_kStep, SetSemiring.down_add, SetSemiring.down_mul, ih,
        SetSemiring.down_one]
      ext x
      simp only [oneStep, SetSemiring.down_up, Set.mem_union, Set.mem_one, Set.mem_mul,
        Set.mem_singleton_iff, Set.mem_ofPred_eq, exists_eq_left]
      constructor
      · rintro (rfl | ⟨y, lt, rfl⟩)
        · simp
        · simp only [toAdd_mul, toAdd_ofAdd]
          omega
      · intro lt
        rcases Nat.eq_zero_or_pos (Multiplicative.toAdd x) with zero | pos
        · left
          exact Multiplicative.toAdd.injective (by simpa using zero)
        · right
          refine ⟨Multiplicative.ofAdd (Multiplicative.toAdd x - 1), by simp; omega, ?_⟩
          apply Multiplicative.toAdd.injective
          simp only [toAdd_mul, toAdd_ofAdd]
          omega

/-- **Idempotence alone does not stop saturation**: over sets of derivation lengths the stages grow
forever. -/
theorem lengths_never_fixed (N : ℕ) :
    selfFeeding.kStage selfCatalogue (fun _ => (1 : Lengths)) (fun _ => oneStep) (N + 1) ≠
      selfFeeding.kStage selfCatalogue (fun _ => (1 : Lengths)) (fun _ => oneStep) N := by
  intro same
  have downs := congrArg SetSemiring.down (congrFun same ())
  rw [lengths_stage, lengths_stage] at downs
  have member : Multiplicative.ofAdd N ∈ {x : Multiplicative ℕ | Multiplicative.toAdd x < N + 1} := by
    simp
  rw [downs] at member
  simp at member

/-- Two atoms, each derived from the other. -/
def cycle : System Bool where
  Site := Unit
  Instance := fun _ => Bool
  consume := fun _ => 0
  read := fun (b : Bool) => {!b}
  produce := fun (b : Bool) => {b}

def cycleCatalogue : List cycle.Entry := [⟨(), true⟩, ⟨(), false⟩]

/-- **Retraction by counting is not exact on a cycle**: after the seed is withdrawn, both atoms keep a
positive count in every round, while the closure of no seeds is empty. -/
theorem counting_retraction_inexact_on_cycle :
    (∀ b, cycle.supportCount cycleCatalogue ∅ Set.univ b ≠ 0) ∧
      (∀ k, cycle.retractStage cycleCatalogue ∅ Set.univ k = Set.univ) ∧
      cycle.saturation {entry | entry ∈ cycleCatalogue} ∅ = ∅ := by
  have supportedAll : cycle.supported cycleCatalogue ∅ Set.univ = Set.univ := by
    ext b
    simp only [supported, Set.empty_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    refine ⟨⟨(), b⟩, ?_, by simp [cycle], fun _ _ => trivial⟩
    cases b <;> simp [cycleCatalogue]
  refine ⟨fun b => (cycle.supportCount_pos_iff cycleCatalogue ∅ Set.univ b).mpr (by
    rw [supportedAll]; exact Set.mem_univ b), fun k => ?_, ?_⟩
  · induction k with
    | zero => rfl
    | succ k ih => rw [retractStage_succ, ih, retractStep, supportedAll, Set.inter_univ]
  · have least := cycle.saturation_isLeast {entry | entry ∈ cycleCatalogue} ∅
    apply Set.eq_empty_of_subset_empty
    apply least.2
    refine ⟨le_rfl, ?_⟩
    intro entry r member
    obtain ⟨reads, -⟩ := member
    exact absurd (reads (!entry.1.2) (by simp [cycle])) (Set.notMem_empty _)

end SemiringControls

end Mettapedia.GSLT.Causality.ResourceInteraction

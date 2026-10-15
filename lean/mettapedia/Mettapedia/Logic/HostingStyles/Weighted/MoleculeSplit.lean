import Mettapedia.Logic.HostingStyles.Weighted.MoleculeMultiplicity
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Sym.Card

/-!
# Constant-part splits and the two readings of `k!`

Meredith, *Collision and Scattering for Process Molecules*, Definition `def:split`
and the factor `k!` in Definition `def:mu`.

A split of the constant part assigns each occurrence of each atom to one of `k`
components. Variables of the pattern are renamed, not chosen, so the count is
the constant-part count. `Nat.multichoose k c` is that number for one atom.
The paper's binomial `(c + k - 1).choose (k - 1)` agrees when `k ≥ 1`. At
`k = 0` the binomial, read with subtraction in `ℕ`, is not the multichoose.

The factor `k!` counts orderings of message occurrences as data. Two orderings
of equal messages are two candidates. Identifying those orderings leaves the
product of the `T_a`. The collision site, two equal singleton messages and one
role, is the smallest site at which the two readings differ: `2` against `1`.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.Weighted

universe u

open scoped BigOperators

variable {Atom : Type u} [DecidableEq Atom]

/-- Ways to give a total of `n` indistinguishable occurrences to `k` components. -/
abbrev countVector (k n : ℕ) := {v : Fin k → ℕ // ∑ i : Fin k, v i = n}

/-- **Positive.** One component receiving the one occurrence. -/
def oneCount : countVector 1 1 :=
  ⟨fun _ => 1, by rw [sum_fin1]⟩

/-- **Positive.** That component's count is `1`. -/
theorem oneCount_value : oneCount.1 0 = 1 :=
  rfl

/-- **Negative.** A component count of `2` does not sum to `1`. -/
theorem two_not_oneCount (v : countVector 1 1) : v.1 0 ≠ 2 := by
  intro h
  have hv := v.2
  rw [sum_fin1, h] at hv
  exact absurd hv (by decide)

/-- Occurrence counts with a fixed sum are the multisets of that cardinality.
`Sym.equivNatSumOfFintype` is that bijection. Rewriting `n` in
`∑ i, Multiset.count i ↑s = n` is ill-typed: `↑s` has type `Sym (Fin k) n`. -/
noncomputable def countVectorEquiv (k n : ℕ) : countVector k n ≃ Sym (Fin k) n :=
  (Sym.equivNatSumOfFintype (Fin k) n).symm

/-- **Positive.** The one-component vector is the singleton multiset of that component. -/
theorem oneCount_equiv_count :
    Multiset.count (0 : Fin 1) (countVectorEquiv 1 1 oneCount : Multiset (Fin 1)) = 1 := by
  rw [countVectorEquiv, Sym.coe_equivNatSumOfFintype_symm_apply, sum_fin1, oneCount_value,
    one_nsmul, Multiset.count_singleton_self]

/-- **Negative.** That multiset is not empty. -/
theorem oneCount_equiv_ne_zero :
    (countVectorEquiv 1 1 oneCount : Multiset (Fin 1)) ≠ 0 := by
  intro h
  have hc := congrArg (Multiset.count (0 : Fin 1)) h
  rw [oneCount_equiv_count, Multiset.count_zero] at hc
  exact Nat.one_ne_zero hc

noncomputable instance countVectorFintype (k n : ℕ) : Fintype (countVector k n) :=
  Fintype.ofEquiv _ (countVectorEquiv k n).symm

theorem countVector_card (k n : ℕ) : Fintype.card (countVector k n) = Nat.multichoose k n := by
  rw [Fintype.card_congr (countVectorEquiv k n)]
  exact Sym.card_sym_fin_eq_multichoose k n

/-- A split of a constant multiset into `k` components. The components are
multisets of atoms and they sum to the constant part. -/
structure ConstSplit (Atom : Type u) [DecidableEq Atom] (k : ℕ) (constant : Message Atom) where
  component : Fin k → Message Atom
  partsSum : ∑ i : Fin k, component i = constant

theorem ConstSplit.ext_eq {k : ℕ} {constant : Message Atom}
    {s₁ s₂ : ConstSplit Atom k constant} (h : s₁.component = s₂.component) : s₁ = s₂ := by
  cases s₁
  cases s₂
  cases h
  rfl

/-- **Positive.** The singleton constant is already one component. -/
def singletonSplit : ConstSplit Unit 1 ({()} : Message Unit) where
  component := fun _ => {()}
  partsSum := by
    rw [sum_fin1]

/-- **Positive.** That component is the singleton. -/
theorem singletonSplit_component : singletonSplit.component 0 = {()} :=
  rfl

/-- **Negative.** The empty multiset is not a split of the singleton. -/
theorem empty_not_split (s : ConstSplit Unit 1 ({()} : Message Unit)) : s.component 0 ≠ 0 := by
  intro h
  have hs := s.partsSum
  rw [sum_fin1, h] at hs
  exact message_singleton_ne_zero () hs.symm

/-- Distributing each atom of the constant part among the components. -/
def constSplitEquiv (k : ℕ) (constant : Message Atom) :
    ConstSplit Atom k constant ≃
      ∀ a : constant.toFinset, countVector k (Multiset.count (a : Atom) constant) where
  toFun s a :=
    ⟨fun i => Multiset.count (a : Atom) (s.component i), by
      have h :=
        Multiset.count_sum' (s := (Finset.univ : Finset (Fin k))) (a := (a : Atom))
          (f := s.component)
      rw [s.partsSum] at h
      exact h.symm⟩
  invFun family :=
    { component := fun i =>
        countsToMultiset constant.toFinset fun b =>
          if h : b ∈ constant.toFinset then (family ⟨b, h⟩).1 i else 0
      partsSum := by
        refine (Multiset.ext).mpr ?_
        intro b
        rw [Multiset.count_sum']
        by_cases hb : b ∈ constant.toFinset
        · rw [Finset.sum_congr rfl fun i _ => by
            rw [count_countsToMultiset, if_pos hb, dif_pos hb]]
          exact (family ⟨b, hb⟩).2
        · rw [Finset.sum_congr rfl fun i _ => by rw [count_countsToMultiset, if_neg hb],
            Finset.sum_const_zero]
          exact (Multiset.count_eq_zero.mpr fun hmem =>
            hb (Multiset.mem_toFinset.mpr hmem)).symm }
  left_inv s := by
    apply ConstSplit.ext_eq
    funext i
    have hsub : (s.component i).toFinset ⊆ constant.toFinset := by
      intro b hb
      have hmem : b ∈ ∑ j : Fin k, s.component j := by
        rw [Multiset.mem_sum]
        exact ⟨i, Finset.mem_univ i, Multiset.mem_toFinset.mp hb⟩
      rw [s.partsSum] at hmem
      exact Multiset.mem_toFinset.mpr hmem
    refine (countsToMultiset_congr ?_).trans (countsToMultiset_recover (s.component i) hsub)
    intro b hb
    rw [dif_pos hb]
  right_inv family := by
    funext a
    refine Subtype.ext ?_
    funext i
    change Multiset.count (a : Atom)
        (countsToMultiset constant.toFinset fun b =>
          if h : b ∈ constant.toFinset then (family ⟨b, h⟩).1 i else 0) =
      (family a).1 i
    rw [count_countsToMultiset, if_pos a.2, dif_pos a.2]

/-- **Positive.** The singleton split records one occurrence in its only component. -/
theorem constSplitEquiv_singleton :
    ((constSplitEquiv 1 ({()} : Message Unit) singletonSplit) ⟨(), by
      rw [Multiset.toFinset_singleton]; exact Finset.mem_singleton_self ()⟩).1 0 = 1 := by
  show Multiset.count () (singletonSplit.component 0) = 1
  rw [singletonSplit, message_singleton_count]

/-- **Negative.** It does not record two occurrences. -/
theorem constSplitEquiv_singleton_ne_two :
    ((constSplitEquiv 1 ({()} : Message Unit) singletonSplit) ⟨(), by
      rw [Multiset.toFinset_singleton]; exact Finset.mem_singleton_self ()⟩).1 0 ≠ 2 := by
  rw [constSplitEquiv_singleton]
  decide

noncomputable instance constSplitFintype (k : ℕ) (constant : Message Atom) :
    Fintype (ConstSplit Atom k constant) :=
  Fintype.ofEquiv _ (constSplitEquiv k constant).symm

/-- The number of constant-part splits: for each atom, `Nat.multichoose k c_a`
ways to give its `c_a` occurrences to `k` components. -/
def constSplitCount (k : ℕ) (constant : Message Atom) : ℕ :=
  ∏ a ∈ constant.toFinset, Nat.multichoose k (Multiset.count a constant)

/-- **Positive.** One occurrence and one component has one split. -/
theorem constSplitCount_singleton : constSplitCount 1 ({()} : Message Unit) = 1 := by
  rw [constSplitCount, Multiset.toFinset_singleton, Finset.prod_singleton,
    message_singleton_count, Nat.multichoose_one]

/-- **Negative.** Zero components cannot receive an occurrence. -/
theorem constSplitCount_zero_singleton : constSplitCount 0 ({()} : Message Unit) = 0 := by
  rw [constSplitCount, Multiset.toFinset_singleton, Finset.prod_singleton,
    message_singleton_count]
  exact Nat.multichoose_zero_succ 0

theorem constSplit_card (k : ℕ) (constant : Message Atom) :
    Fintype.card (ConstSplit Atom k constant) = constSplitCount k constant := by
  rw [Fintype.card_congr (constSplitEquiv k constant), Fintype.card_pi]
  rw [← Finset.prod_subtype constant.toFinset (fun _ => Iff.rfl)
    fun a => Fintype.card (countVector k (Multiset.count a constant))]
  rw [constSplitCount]
  exact Finset.prod_congr rfl fun a _ => countVector_card k (Multiset.count a constant)

/-- The binomial written in `def:split`. Subtraction is the subtraction of `ℕ`. -/
def paperBinomial (c k : ℕ) : ℕ := (c + k - 1).choose (k - 1)

/-- **Positive.** One occurrence and two components is the binomial `2`. -/
theorem paperBinomial_one_two : paperBinomial 1 2 = 2 := by
  decide

/-- **Negative.** At `k = 0` the binomial is `1` and `Nat.multichoose` is `0`. -/
theorem paperBinomial_zero_ne_multichoose : paperBinomial 1 0 ≠ Nat.multichoose 0 1 := by
  rw [paperBinomial, Nat.multichoose_zero_succ]
  decide

/-- For `k ≥ 1` the paper's binomial is `Nat.multichoose k c`. -/
theorem multichoose_paper (k c : ℕ) (hk : 0 < k) :
    Nat.multichoose k c = paperBinomial c k := by
  rw [Nat.multichoose_eq, paperBinomial]
  have hcomm : k + c - 1 = c + k - 1 := by rw [Nat.add_comm]
  rw [hcomm]
  have hassoc : c + k - 1 = c + (k - 1) := Nat.add_sub_assoc hk c
  have hc : c ≤ c + k - 1 := by
    rw [hassoc]
    exact Nat.le_add_right _ _
  rw [← Nat.choose_symm hc]
  have hsub : c + k - 1 - c = k - 1 := by
    rw [hassoc, Nat.add_sub_cancel_left]
  rw [hsub]

/-- For `k ≥ 1` the constant-part split count is the paper's product of binomials. -/
theorem constSplitCount_paper (k : ℕ) (hk : 0 < k) (constant : Message Atom) :
    constSplitCount k constant =
      ∏ a ∈ constant.toFinset, paperBinomial (Multiset.count a constant) k := by
  rw [constSplitCount]
  exact Finset.prod_congr rfl fun a _ => multichoose_paper k (Multiset.count a constant) hk

/-- The product of the `T_a`, without the factor `k!`. -/
def orderingBlindCount {Role : Type*} [Fintype Role] [DecidableEq Role] {k : ℕ}
    (messages : Fin k → Message Atom) (outcome : Role → Message Atom) : ℕ :=
  ∏ a ∈ atomSupport messages outcome,
    Fintype.card (MarginMatrix Role k (fun i => Multiset.count a (messages i))
      (fun role => Multiset.count a (outcome role)))

theorem fibreMultiplicity_eq_factorial_blind {Role : Type*} [Fintype Role] [DecidableEq Role]
    {k : ℕ} (messages : Fin k → Message Atom) (outcome : Role → Message Atom) :
    fibreMultiplicity messages outcome =
      Nat.factorial k * orderingBlindCount messages outcome :=
  rfl

/-- **Positive.** At the collision margins the matrices contribute `1`. -/
theorem collision_blind_one :
    orderingBlindCount collisionMessages collisionOutcome = 1 := by
  have h := collision_mu_eq_twoBodyMultiplicity
  rw [fibreMultiplicity_eq_factorial_blind, twoBodyMultiplicity_eq] at h
  have hfact : Nat.factorial 2 = 2 := by decide
  rw [hfact] at h
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) h

/-- **Negative.** The blind count is not the paper's `μ` at that site. -/
theorem collision_blind_ne_mu :
    orderingBlindCount collisionMessages collisionOutcome ≠
      fibreMultiplicity collisionMessages collisionOutcome := by
  rw [collision_blind_one, collision_mu_eq_twoBodyMultiplicity, twoBodyMultiplicity_eq]
  decide

/-- Below two messages, `k! = 1`, so the two readings agree at every site. -/
theorem factorial_below_two (k : ℕ) (hk : k < 2) : Nat.factorial k = 1 := by
  cases k with
  | zero => rfl
  | succ k =>
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (Nat.lt_of_succ_lt_succ hk))
    subst hk0
    rfl

theorem readings_agree_below_two {Role : Type*} [Fintype Role] [DecidableEq Role] {k : ℕ}
    (hk : k < 2) (messages : Fin k → Message Atom) (outcome : Role → Message Atom) :
    fibreMultiplicity messages outcome = orderingBlindCount messages outcome := by
  rw [fibreMultiplicity_eq_factorial_blind, factorial_below_two k hk, Nat.one_mul]

/-- A candidate at the collision site for an ordering `σ`. The two messages are
equal, and the parts do not depend on `σ`. -/
def collisionCandidate (σ : Equiv.Perm (Fin 2)) : Candidate Unit Unit 2 collisionMessages where
  ordering := σ
  part := fun _ _ => {()}
  rowSum := fun _ => by
    rw [sum_unit, collisionMessages]

/-- **Positive.** The reflected ordering is a collision candidate. -/
theorem collisionCandidate_refl_ordering :
    (collisionCandidate (Equiv.refl (Fin 2))).ordering = Equiv.refl (Fin 2) :=
  rfl

/-- **Negative.** The swapped ordering is not the reflected one. -/
theorem collisionCandidate_swap_ne_refl :
    (collisionCandidate (Equiv.swap 0 1)).ordering ≠ Equiv.refl (Fin 2) := by
  intro h
  have h0 :
      (collisionCandidate (Equiv.swap (0 : Fin 2) 1)).ordering (0 : Fin 2) =
        Equiv.refl (Fin 2) (0 : Fin 2) :=
    congrArg (fun σ : Equiv.Perm (Fin 2) => σ (0 : Fin 2)) h
  unfold collisionCandidate at h0
  rw [Equiv.swap_apply_left, Equiv.refl_apply] at h0
  exact absurd h0 (by decide : (1 : Fin 2) ≠ 0)

theorem collision_messages_eq : collisionMessages 0 = collisionMessages 1 :=
  rfl

theorem collisionCandidate_outcome (σ : Equiv.Perm (Fin 2)) :
    (collisionCandidate σ).outcome = collisionOutcome := by
  funext role
  cases role
  rw [Candidate.outcome, sum_fin2, collisionCandidate, collisionOutcome, two_nsmul]

/-- The paper's `k!` counts orderings as data: equal messages still give two
candidates, one for each ordering. -/
theorem paper_orderings_distinct :
    collisionCandidate (Equiv.refl (Fin 2)) ≠ collisionCandidate (Equiv.swap 0 1) := by
  intro h
  have hord := congrArg Candidate.ordering h
  exact collisionCandidate_swap_ne_refl (hord.symm)

/-- At the collision site the paper's count is `2` and the ordering-blind count
is `1`. No site with fewer than two messages separates the readings. -/
theorem collision_readings_separate :
    fibreMultiplicity collisionMessages collisionOutcome = 2 ∧
      orderingBlindCount collisionMessages collisionOutcome = 1 ∧
      ∀ k : ℕ, k < 2 → Nat.factorial k = 1 :=
  ⟨collision_mu_eq_twoBodyMultiplicity.trans twoBodyMultiplicity_eq, collision_blind_one,
    factorial_below_two⟩

end Mettapedia.Logic.HostingStyles.Weighted

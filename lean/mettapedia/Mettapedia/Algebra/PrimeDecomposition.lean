import Mettapedia.Algebra.CanonicalFactorization
import Mathlib.Algebra.GroupWithZero.WithZero
import Mathlib.Algebra.Order.Group.Multiset
import Mathlib.Data.ENat.Basic

/-!
# Zero-free unique decomposition

A reduced commutative monoid has no units other than one. Well-founded proper
factorization gives existence; cancellation and primality of irreducibles give
uniqueness. Primality is a genuine hypothesis: the numerical monoid generated
by two and three has incompatible decompositions of six.

`WithZero` connects these notions to Mathlib without changing the public
carrier. Canonical factor sets classify associates, while reducedness makes
associated elements literally equal. The free multiset model satisfies the
hypotheses; self-absorption obstructs well-foundedness. No particular process
calculus is claimed to satisfy the abstract hypotheses here.

For process-algebra motivation, see Luttik and van Oostrom, *Decomposition
orders* (2005), and Milner and Moller, *Unique decomposition of processes* (1993).
-/

namespace Mettapedia.Algebra

universe u

variable {M : Type u} [CommMonoid M]

/-- A reduced monoid has no unit other than the identity. -/
def Reduced (M : Type u) [CommMonoid M] : Prop := ∀ a b : M, a * b = 1 → a = 1

/-- **Irreducible**: not the identity, and not a product of two non-identities. -/
def Irred (p : M) : Prop := p ≠ 1 ∧ ∀ a b : M, p = a * b → a = 1 ∨ b = 1

/-- **Prime**: not the identity, and dividing a product means dividing a factor. -/
def PrimeElt (p : M) : Prop := p ≠ 1 ∧ ∀ a b : M, p ∣ a * b → p ∣ a ∨ p ∣ b

/-- A **decomposition** of `a`: a multiset of irreducibles whose product is `a`. -/
def IsDecomposition (s : Multiset M) (a : M) : Prop := (∀ p ∈ s, Irred p) ∧ s.prod = a

/-- Proper factorization: `a` is `b` times a nonidentity factor. -/
def ProperFactor (b a : M) : Prop := ∃ c : M, a = b * c ∧ c ≠ 1

/-! ## Comparison with Mathlib -/

/-- **Reducedness is `Subsingleton Mˣ`.** -/
theorem reduced_iff_subsingleton_units : Reduced M ↔ Subsingleton Mˣ := by
  constructor
  · intro h
    exact Subsingleton.units_of_isUnit fun a unit =>
      let ⟨b, equal⟩ := unit.exists_right_inv; h a b equal
  · intro _ a b hab
    exact isUnit_iff_eq_one.mp (IsUnit.of_mul_eq_one b hab)

/-- Irreducibility agrees with Mathlib when units are unique. -/
theorem irred_iff_irreducible [Subsingleton Mˣ] {p : M} : Irred p ↔ Irreducible p := by
  simp only [Irred, irreducible_iff, isUnit_iff_eq_one]

theorem withZero_reduced (hred : Reduced M) : Reduced (WithZero M) := by
  simpa only [Reduced, WithZero.forall, zero_mul, mul_zero, zero_ne_one, false_implies,
    true_and, implies_true, forall_const, ← WithZero.coe_mul, ← WithZero.coe_one,
    WithZero.coe_inj, WithZero.zero_ne_coe] using hred

theorem withZero_coe_dvd (a b : M) : (a : WithZero M) ∣ (b : WithZero M) ↔ a ∣ b := by
  simp only [dvd_def, WithZero.exists, mul_zero, WithZero.coe_ne_zero,
    false_or, ← WithZero.coe_mul, WithZero.coe_inj]

theorem primeElt_coe (hred : Reduced M) {p : M} (prime : PrimeElt p) : Prime (p : WithZero M) := by
  have := (reduced_iff_subsingleton_units (M := WithZero M)).mp (withZero_reduced hred)
  refine ⟨WithZero.coe_ne_zero, fun unit => prime.1 (WithZero.coe_injective (isUnit_iff_eq_one.mp unit)), ?_⟩
  simpa only [WithZero.forall, zero_mul, mul_zero, dvd_zero, true_or, or_true, implies_true,
    true_and, ← WithZero.coe_mul, withZero_coe_dvd] using prime.2

theorem withZero_cancellation [IsCancelMul M] : IsCancelMulZero (WithZero M) := by
  have : IsLeftCancelMulZero (WithZero M) := ⟨by
    intro a nonzero
    induction a using WithZero.recZeroCoe with
    | zero => exact (nonzero rfl).elim
    | coe a => exact Option.map_injective (mul_right_injective a)⟩
  exact IsLeftCancelMulZero.to_isCancelMulZero

theorem withZero_map_prod (s : Multiset M) :
    (s.map (fun p : M => (p : WithZero M))).prod = (s.prod : WithZero M) := by
  simpa only [WithZero.coeMonoidHom_apply] using
    (map_multiset_prod (WithZero.coeMonoidHom : M →* WithZero M) s).symm

/-- Well-founded proper factorization produces a finite decomposition. -/
theorem exists_decomposition (hwf : WellFounded (ProperFactor (M := M)))
    (_hred : Reduced M) : ∀ a : M, ∃ s : Multiset M, IsDecomposition s a := by
  intro a
  induction a using hwf.induction with
  | _ a ih =>
      by_cases ha : a = 1
      · exact ⟨0, by simp, by simp [ha]⟩
      · by_cases hirr : ∀ b c : M, a = b * c → b = 1 ∨ c = 1
        · exact ⟨{a}, by simpa using (show Irred a from ⟨ha, hirr⟩), by simp⟩
        · push Not at hirr
          obtain ⟨b, c, hbc, hb, hc⟩ := hirr
          obtain ⟨sb, hsb⟩ := ih b ⟨c, hbc, hc⟩
          obtain ⟨sc, hsc⟩ := ih c ⟨b, by rw [hbc, mul_comm], hb⟩
          refine ⟨sb + sc, ?_, ?_⟩
          · intro p hp
            exact (Multiset.mem_add.mp hp).elim (hsb.1 p) (hsc.1 p)
          · rw [Multiset.prod_add, hsb.2, hsc.2, hbc]

/-- The original existence and primality hypotheses realize Mathlib's factorization interface. -/
theorem withZero_factorization [IsCancelMul M]
    (wf : WellFounded (ProperFactor (M := M))) (reduced : Reduced M)
    (prime : ∀ p : M, Irred p → PrimeElt p) : UniqueFactorizationMonoid (WithZero M) := by
  have := withZero_cancellation (M := M)
  apply UniqueFactorizationMonoid.of_exists_prime_factors
  intro x nonzero
  induction x using WithZero.recZeroCoe with
  | zero => exact (nonzero rfl).elim
  | coe a =>
      obtain ⟨s, hs, product⟩ := exists_decomposition wf reduced a
      refine ⟨s.map (fun p : M => (p : WithZero M)), ?_, ?_⟩
      · simpa only [Multiset.forall_mem_map_iff] using
          (fun p hp => primeElt_coe reduced (prime p (hs p hp)))
      · apply Associated.of_eq
        rw [withZero_map_prod, product]

/-- A prime dividing a product of a multiset divides one of its members. -/
theorem prime_dvd_multiset_prod (hred : Reduced M) {p : M} (hp : PrimeElt p) : ∀ (s : Multiset M), p ∣ s.prod
    → ∃ q ∈ s, p ∣ q := by
  intro s
  simpa only [withZero_map_prod, Multiset.mem_map, exists_exists_and_eq_and, withZero_coe_dvd] using
    (primeElt_coe hred hp).exists_mem_multiset_dvd (s := s.map (fun p : M => (p : WithZero M)))

/-- In a reduced monoid a prime dividing an irreducible is that irreducible. -/
theorem eq_of_prime_dvd_irred {p q : M} (hp : PrimeElt p) (hq : Irred q) (h : p ∣ q) : p = q := by
  obtain ⟨c, hc⟩ := h
  rcases hq.2 p c hc with h1 | h1
  · exact absurd h1 hp.1
  · rw [hc, h1, mul_one]

/-- Primality and cancellation determine the irreducible multiset. -/
theorem decomposition_unique [IsCancelMul M] [DecidableEq M] (hred : Reduced M) (hprime : ∀ p : M, Irred p →
    PrimeElt p) : ∀ (s t : Multiset M) (a : M), IsDecomposition s a → IsDecomposition t a → s = t := by
  intro s t a hs ht
  have := withZero_cancellation (M := M)
  have : Subsingleton (WithZero M)ˣ := reduced_iff_subsingleton_units.mp (withZero_reduced hred)
  have primes (u : Multiset M) (hu : ∀ p ∈ u, Irred p) :
      ∀ q ∈ u.map (fun p : M => (p : WithZero M)), Prime q := by
    simpa only [Multiset.forall_mem_map_iff] using (fun p hp => primeElt_coe hred (hprime p (hu p hp)))
  apply Multiset.map_injective WithZero.coe_injective
  simpa only [associated_eq_eq, Multiset.rel_eq] using
    prime_factors_unique (primes s hs.1) (primes t ht.1)
      (Associated.of_eq (by rw [withZero_map_prod, withZero_map_prod, hs.2, ht.2]))

/-- Existence and uniqueness under their respective hypotheses. -/
theorem existsUnique_decomposition [IsCancelMul M] [DecidableEq M]
    (hwf : WellFounded (ProperFactor (M := M))) (hred : Reduced M)
    (hprime : ∀ p : M, Irred p → PrimeElt p) (a : M) :
    ∃! s : Multiset M, IsDecomposition s a := by
  obtain ⟨s, hs⟩ := exists_decomposition hwf hred a
  exact ⟨s, hs, fun t ht => decomposition_unique hred hprime t s a ht hs⟩

section Canonical

variable [UniqueFactorizationMonoid (WithZero M)] [Subsingleton (WithZero M)ˣ]
local notation "FactorSet" => Associates.FactorSet (WithZero M)
local notation "Factors" => Multiset {p : Associates (WithZero M) // Irreducible p}

/-- Finite factors of a nonzero embedded element, with the standard associate classes. -/
noncomputable def finiteFactors (a : M) : Factors :=
  ((Associates.mk (a : WithZero M)).factors).untop
    (fun equal => WithZero.coe_ne_zero (Associates.mk_eq_zero.mp
      (Associates.factors_eq_top_iff_zero.mp equal)))

omit [Subsingleton (WithZero M)ˣ] in
@[simp] theorem coe_finiteFactors (a : M) :
    ((finiteFactors a : Multiset _) : FactorSet) = (Associates.mk (a : WithZero M)).factors := WithTop.coe_untop _ _

/-- Exact canonical factors for the zero-free carrier. -/
noncomputable def finiteFactorEquiv : M ≃* Multiplicative Factors := by
  let e := (associatesEquivOfUniqueUnits (α := WithZero M)).symm.trans
    (CanonicalFactorization.factorSetEquiv (R := WithZero M))
  let restricted := e.toEquiv.subtypeEquiv (p := fun x => x ≠ 0)
    (q := fun x => Multiplicative.toAdd x ≠ ⊤) (fun x => by
      change x ≠ 0 ↔ (Associates.mk x).factors ≠ ⊤
      exact (not_congr (Associates.factors_eq_top_iff_zero.trans Associates.mk_eq_zero)).symm)
  let finite : M ≃ Factors := (Equiv.withBotSubtypeNe (α := M)).symm.trans
    (restricted.trans (Equiv.withTopSubtypeNe (α := Factors)))
  refine { finite with map_mul' := ?_ }
  intro a b
  change finiteFactors (a*b) = finiteFactors a + finiteFactors b
  apply WithTop.coe_injective (α := Factors)
  simp only [WithTop.coe_add, coe_finiteFactors, WithZero.coe_mul,
    ← Associates.mk_mul_mk, Associates.factors_mul]

omit [Subsingleton (WithZero M)ˣ] in
/-- Divisibility is inclusion of the full factor multiset, not just its support. -/
theorem finiteFactors_dvd_iff (a b : M) : finiteFactors a ≤ finiteFactors b ↔ a ∣ b := by
  rw [← WithTop.coe_le_coe, coe_finiteFactors, coe_finiteFactors, Associates.factors_le]
  change (Associates.mk (a : WithZero M)) ∣ (Associates.mk (b : WithZero M)) ↔ a ∣ b
  rw [Associates.mk_dvd_mk, withZero_coe_dvd]

noncomputable def factorCount (a : M) : ℕ := (finiteFactors a).card

theorem factorCount_mul (a b : M) : factorCount (a*b) = factorCount a + factorCount b := by
  exact (congrArg (fun x => (Multiplicative.toAdd x).card)
    ((finiteFactorEquiv (M := M)).map_mul a b)).trans (Multiset.card_add _ _)

theorem factorCount_eq_zero (a : M) : factorCount a = 0 ↔ a = 1 := by
  rw [factorCount, Multiset.card_eq_zero]
  exact (finiteFactorEquiv (M := M)).map_eq_one_iff

theorem properFactor_count_lt {b a : M} (factor : ProperFactor b a) : factorCount b < factorCount a := by
  obtain ⟨c, rfl, nonunit⟩ := factor
  rw [factorCount_mul]
  exact Nat.lt_add_of_pos_right (Nat.pos_of_ne_zero (mt (factorCount_eq_zero c).mp nonunit))

end Canonical

/-! ## Models and separating examples -/

/-- A nonidentity absorbed factor gives a self-loop in proper factorization. -/
theorem not_wellFounded_of_self_absorbing {p q : M} (hq : q ≠ 1) (h : p = p * q) :
    ¬ WellFounded (ProperFactor (M := M)) :=
  fun hwf => hwf.irrefl.irrefl p ⟨q, h, hq⟩

/-- Multisets of generators, written multiplicatively. -/
abbrev FreeCM (σ : Type u) := Multiplicative (Multiset σ)

variable {σ : Type u}

theorem freeCM_toAdd_mul (a b : FreeCM σ) : Multiplicative.toAdd (a * b) = Multiplicative.toAdd a +
    Multiplicative.toAdd b := rfl

theorem freeCM_eq_one_iff {a : FreeCM σ} : a = 1 ↔ Multiplicative.toAdd a = 0 :=
  Multiplicative.toAdd.injective.eq_iff.symm

/-- Divisibility is multiset containment. -/
theorem freeCM_dvd_iff {p a : FreeCM σ} : p ∣ a ↔ Multiplicative.toAdd p ≤ Multiplicative.toAdd a :=
  Multiset.le_iff_exists_add.symm

/-- Nothing but the empty multiset is invertible. -/
theorem freeCM_reduced : Reduced (FreeCM σ) := by
  intro a b equal
  exact freeCM_eq_one_iff.mpr
    (le_antisymm (freeCM_dvd_iff.mp ⟨b, equal.symm⟩) (Multiset.zero_le _))

/-- Factorization terminates, because a proper factor is strictly smaller. -/
theorem freeCM_wellFounded : WellFounded (ProperFactor (M := FreeCM σ)) := by
  refine Subrelation.wf ?_ (measure (fun a : FreeCM σ => (Multiplicative.toAdd a).card)).wf
  rintro b a ⟨c, rfl, nonunit⟩
  have positive := Multiset.card_pos.mpr (mt freeCM_eq_one_iff.mpr nonunit)
  change (Multiplicative.toAdd b).card < (Multiplicative.toAdd (b*c)).card
  rw [freeCM_toAdd_mul, Multiset.card_add]
  exact Nat.lt_add_of_pos_right positive

/-- The irreducibles are exactly the generators. -/
theorem freeCM_irred_iff [DecidableEq σ] {p : FreeCM σ} : Irred p ↔ (Multiplicative.toAdd p).card = 1 := by
  constructor
  · rintro ⟨nonunit, split⟩
    obtain ⟨x, member⟩ := Multiset.exists_mem_of_ne_zero (mt freeCM_eq_one_iff.mpr nonunit)
    obtain ⟨s, parts⟩ := Multiset.exists_cons_of_mem member
    have factor := split (Multiplicative.ofAdd ({x} : Multiset σ)) (Multiplicative.ofAdd s)
      (Multiplicative.toAdd.injective parts)
    change ({x} : Multiset σ) = 0 ∨ s = 0 at factor
    simp [parts, factor.resolve_left (Multiset.singleton_ne_zero _)]
  · intro cardinal
    refine ⟨fun equal => ?_, fun a b equal => ?_⟩
    · simp [equal] at cardinal
    · have sum := congrArg (fun p : FreeCM σ => (Multiplicative.toAdd p).card) equal
      simp only [freeCM_toAdd_mul, Multiset.card_add, cardinal] at sum
      simp only [freeCM_eq_one_iff, ← Multiset.card_eq_zero]
      omega

/-- A singleton generator dividing a sum occurs in one summand. -/
theorem freeCM_prime_of_card_one {p : FreeCM σ} (hcard : (Multiplicative.toAdd p).card = 1) : PrimeElt p := by
  obtain ⟨x, hx⟩ := Multiset.card_eq_one.mp hcard
  refine ⟨fun h => by rw [freeCM_eq_one_iff, hx] at h; simp at h, ?_⟩
  intro a b
  simp only [freeCM_dvd_iff, hx, freeCM_toAdd_mul, Multiset.singleton_le, Multiset.mem_add, imp_self]

/-- The free model discharges every hypothesis of unique decomposition. -/
theorem freeCM_existsUnique_decomposition [DecidableEq σ] (a : FreeCM σ) : ∃! s : Multiset (FreeCM σ),
    IsDecomposition s a :=
  existsUnique_decomposition freeCM_wellFounded freeCM_reduced
    (fun _ hp => freeCM_prime_of_card_one (freeCM_irred_iff.mp hp)) a

/-- Infinity absorbs one more factor. -/
theorem enat_top_self_absorbing : (Multiplicative.ofAdd (⊤ : ℕ∞)) = Multiplicative.ofAdd (⊤ : ℕ∞) *
    Multiplicative.ofAdd (1 : ℕ∞) :=
  congrArg Multiplicative.ofAdd (by simp : (⊤ : ℕ∞) = ⊤ + 1)

/-- The absorbing infinite element refutes well-foundedness. -/
theorem enat_not_wellFounded : ¬ WellFounded (ProperFactor (M := Multiplicative ℕ∞)) :=
  not_wellFounded_of_self_absorbing
    (q := Multiplicative.ofAdd (1 : ℕ∞))
    (fun h => (one_ne_zero : (1 : ℕ∞) ≠ 0) (congrArg Multiplicative.toAdd h))
    enat_top_self_absorbing

namespace Num23

/-- The numerical monoid generated by two and three: every natural but one. -/
def Carrier : Type := {n : ℕ // n ≠ 1}

private def additiveCarrier : AddSubmonoid ℕ where
  carrier := {n | n ≠ 1}
  zero_mem' := by decide
  add_mem' := by intro a b ha hb; change a ≠ 1 at ha; change b ≠ 1 at hb; change a+b ≠ 1; omega

instance : CommMonoid Carrier := inferInstanceAs (CommMonoid (Multiplicative additiveCarrier))

@[simp] theorem val_mul (a b : Carrier) : (a * b).1 = a.1 + b.1 := rfl
@[simp] theorem val_one : (1 : Carrier).1 = 0 := rfl

theorem eq_one_iff {a : Carrier} : a = 1 ↔ a.1 = 0 := Subtype.val_injective.eq_iff.symm

theorem ne_one_val (a : Carrier) : a.1 ≠ 1 := a.2

instance : DecidableEq Carrier := inferInstanceAs (DecidableEq (Multiplicative additiveCarrier))
instance : IsCancelMul Carrier := inferInstanceAs (IsCancelMul (Multiplicative additiveCarrier))

/-- The two hypotheses that are discharged elsewhere hold here. -/
theorem reduced : Reduced Carrier := by
  intro a b h
  exact eq_one_iff.mpr ((Nat.add_eq_zero_iff.mp (congrArg Subtype.val h)).1)

theorem wellFounded : WellFounded (ProperFactor (M := Carrier)) := by
  refine Subrelation.wf ?_ (measure (fun a : Carrier => a.1)).wf
  rintro b a ⟨c, rfl, nonunit⟩
  have positive : c.1 ≠ 0 := mt eq_one_iff.mpr nonunit
  change b.1 < b.1 + c.1
  omega

def two : Carrier := ⟨2, by omega⟩
def three : Carrier := ⟨3, by omega⟩
def four : Carrier := ⟨4, by omega⟩
def six : Carrier := ⟨6, by omega⟩

@[simp] theorem val_two : two.1 = 2 := rfl
@[simp] theorem val_three : three.1 = 3 := rfl
@[simp] theorem val_four : four.1 = 4 := rfl
@[simp] theorem val_six : six.1 = 6 := rfl

private theorem small_irred (a : Carrier) (low : 2 ≤ a.1) (high : a.1 ≤ 3) : Irred a := by
  refine ⟨fun h => by have := eq_one_iff.mp h; omega, ?_⟩
  intro b c equal
  have value := congrArg Subtype.val equal
  have hb := b.2; have hc := c.2
  simp only [val_mul] at value
  simp only [eq_one_iff]
  omega

theorem two_irred : Irred two := small_irred two (by decide) (by decide)
theorem three_irred : Irred three := small_irred three (by decide) (by decide)

theorem two_dvd_six : two ∣ three * three := ⟨four, Subtype.ext (by decide)⟩

theorem three_not_multiple_of_two : ∀ c : Carrier, three ≠ two * c := by
  intro c hc
  have hv := congrArg Subtype.val hc
  rw [val_mul, val_two, val_three] at hv
  exact ne_one_val c (by omega)

/-- Irreducibility does not imply primality in this reduced cancellative monoid. -/
theorem two_not_prime : ¬ PrimeElt two := by
  rintro ⟨-, hp⟩
  rcases hp three three two_dvd_six with ⟨c, hc⟩ | ⟨c, hc⟩
  all_goals exact three_not_multiple_of_two c hc

theorem decomposition_twos : IsDecomposition {two, two, two} six :=
  ⟨by simpa using two_irred, Subtype.ext (by decide)⟩

theorem decomposition_threes : IsDecomposition {three, three} six :=
  ⟨by simpa using three_irred, Subtype.ext (by decide)⟩

/-- The distinct factorizations of six refute uniqueness without primality. -/
theorem decomposition_not_unique :
    ∃ s t : Multiset Carrier, IsDecomposition s six ∧ IsDecomposition t six ∧ s ≠ t :=
  ⟨{two, two, two}, {three, three}, decomposition_twos, decomposition_threes, by
    intro h
    have hcard := congrArg Multiset.card h
    simp at hcard⟩

end Num23

end Mettapedia.Algebra

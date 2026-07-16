import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Weighted twisted Burnside identity

Let a finite group act on a finite set, let `twist` be an equivariant
permutation of that set, and let a rational weight be constant on group
orbits.  This module compares the weighted fixed-point sum of the induced
permutation on the orbit quotient with the average, over group elements, of
the corresponding twisted fixed-point sums upstairs.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace WeightedOrbitBurnside

variable {G X : Type*} [Group G] [Fintype G] [MulAction G X]
  [Fintype X] [DecidableEq X]

abbrev OrbitQuotient := Quotient (MulAction.orbitRel G X)

noncomputable instance orbitQuotientFintype :
    Fintype (OrbitQuotient (G := G) (X := X)) :=
  Fintype.ofFinite _

noncomputable instance orbitQuotientDecidableEq :
    DecidableEq (OrbitQuotient (G := G) (X := X)) :=
  Classical.decEq _

noncomputable instance orbitFintype (x : X) :
    Fintype (MulAction.orbit G x) :=
  Fintype.ofFinite _

abbrev Transporter (G : Type*) [Group G] [MulAction G X]
    (source target : X) :=
  { g : G // g • source = target }

noncomputable def stabilizerEquivTransporter
    {source target : X} (sameOrbit : MulAction.orbitRel G X target source) :
    MulAction.stabilizer G source ≃ Transporter G source target := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at sameOrbit
  let mover : G := Classical.choose sameOrbit
  have hmover : mover • source = target := Classical.choose_spec sameOrbit
  exact
    { toFun := fun stabilizerElement =>
        ⟨mover * stabilizerElement.1, by
          rw [mul_smul, stabilizerElement.2, hmover]⟩
      invFun := fun transporterElement =>
        ⟨mover⁻¹ * transporterElement.1, by
          change (mover⁻¹ * transporterElement.1) • source = source
          rw [mul_smul, transporterElement.2, ← hmover, inv_smul_smul]⟩
      left_inv := by
        intro stabilizerElement
        apply Subtype.ext
        simp
      right_inv := by
        intro transporterElement
        apply Subtype.ext
        simp }

theorem card_transporter
    {source target : X} (sameOrbit : MulAction.orbitRel G X target source) :
    Fintype.card (Transporter G source target) =
      Fintype.card (MulAction.stabilizer G source) := by
  exact Fintype.card_congr (stabilizerEquivTransporter sameOrbit).symm

variable (twist : X ≃ X)
  (twist_equivariant : ∀ (g : G) (x : X), twist (g • x) = g • twist x)

theorem stabilizer_twist
    (twist_equivariant : ∀ (g : G) (x : X), twist (g • x) = g • twist x)
    (x : X) :
    MulAction.stabilizer G (twist x) = MulAction.stabilizer G x := by
  ext g
  simp only [MulAction.mem_stabilizer_iff]
  constructor
  · intro hfixed
    apply twist.injective
    rw [twist_equivariant, hfixed]
  · intro hfixed
    rw [← twist_equivariant, hfixed]

theorem twist_respects_orbit
    (twist_equivariant : ∀ (g : G) (x : X), twist (g • x) = g • twist x)
    {left right : X} (sameOrbit : MulAction.orbitRel G X left right) :
    MulAction.orbitRel G X (twist left) (twist right) := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at sameOrbit ⊢
  rcases sameOrbit with ⟨g, hg⟩
  refine ⟨g, ?_⟩
  rw [← twist_equivariant]
  exact congrArg twist hg

def quotientTwist : OrbitQuotient (G := G) (X := X) →
    OrbitQuotient (G := G) (X := X) :=
  Quotient.map twist (fun _ _ sameOrbit =>
    twist_respects_orbit twist twist_equivariant sameOrbit)

@[simp] theorem quotientTwist_mk (x : X) :
    quotientTwist twist twist_equivariant (Quotient.mk _ x) =
      Quotient.mk _ (twist x) :=
  rfl

variable (weight : X → ℚ)
  (weight_invariant : ∀ (g : G) (x : X), weight (g • x) = weight x)

def quotientWeight : OrbitQuotient (G := G) (X := X) → ℚ :=
  Quotient.lift weight (by
    intro left right sameOrbit
    change MulAction.orbitRel G X left right at sameOrbit
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at sameOrbit
    rcases sameOrbit with ⟨g, hg⟩
    rw [← hg, weight_invariant])

@[simp] theorem quotientWeight_mk (x : X) :
    quotientWeight weight weight_invariant (Quotient.mk _ x) = weight x :=
  rfl

def quotientFixedWeightSum : ℚ :=
  Finset.univ.sum fun orbit : OrbitQuotient (G := G) (X := X) =>
    if quotientTwist twist twist_equivariant orbit = orbit then
      quotientWeight weight weight_invariant orbit
    else 0

def labeledTwistedWeightSum : ℚ :=
  Finset.univ.sum fun g : G => Finset.univ.sum fun x : X =>
    if g • twist x = x then weight x else 0

/-! The orbitwise cardinal calculation used by the weighted identity. -/

theorem transporter_card_on_fixed_orbit
    (orbit : OrbitQuotient (G := G) (X := X))
    (horbit : quotientTwist twist twist_equivariant orbit = orbit)
    (x : MulAction.orbit G orbit.out) :
    Fintype.card (Transporter G (twist x.1) x.1) =
      Fintype.card (MulAction.stabilizer G orbit.out) := by
  have htwistOrbit :
      MulAction.orbitRel G X x.1 (twist x.1) := by
    have hx : (Quotient.mk _ x.1 : OrbitQuotient (G := G) (X := X)) = orbit := by
      exact (Quotient.sound x.2).trans (Quotient.out_eq' orbit)
    apply Quotient.eq''.mp
    calc
      (Quotient.mk _ x.1 : OrbitQuotient (G := G) (X := X)) = orbit := hx
      _ = quotientTwist twist twist_equivariant orbit := horbit.symm
      _ = Quotient.mk _ (twist x.1) :=
        (congrArg (quotientTwist twist twist_equivariant) hx.symm).trans
          (quotientTwist_mk twist twist_equivariant x.1)
  calc
    Fintype.card (Transporter G (twist x.1) x.1) =
        Fintype.card (MulAction.stabilizer G (twist x.1)) :=
      card_transporter htwistOrbit
    _ = Fintype.card (MulAction.stabilizer G x.1) := by
      exact Fintype.card_congr (Equiv.setCongr (by
        simpa using congrArg SetLike.coe
          (stabilizer_twist twist twist_equivariant x.1)))
    _ = Fintype.card (MulAction.stabilizer G orbit.out) := by
      have hxrel : MulAction.orbitRel G X x.1 orbit.out := x.2
      exact Fintype.card_congr
        (MulAction.stabilizerEquivStabilizerOfOrbitRel hxrel).toEquiv

theorem transporter_is_empty_off_fixed_orbit
    (orbit : OrbitQuotient (G := G) (X := X))
    (horbit : quotientTwist twist twist_equivariant orbit ≠ orbit)
    (x : MulAction.orbit G orbit.out) :
    IsEmpty (Transporter G (twist x.1) x.1) := by
  refine ⟨fun transporterElement => horbit ?_⟩
  have hx : (Quotient.mk _ x.1 : OrbitQuotient (G := G) (X := X)) = orbit := by
    exact (Quotient.sound x.2).trans (Quotient.out_eq' orbit)
  rw [← hx, quotientTwist_mk]
  exact Quotient.sound
    (by
      change MulAction.orbitRel G X (twist x.1) x.1
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      exact ⟨transporterElement.1⁻¹,
        inv_smul_eq_iff.mpr transporterElement.2.symm⟩)

theorem sum_indicator_eq_card_transporter_mul
    (source target : X) (value : ℚ) :
    (Finset.univ.sum fun g : G =>
      if g • source = target then value else 0) =
      Fintype.card (Transporter G source target) * value := by
  classical
  simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul]
  congr 1
  exact_mod_cast
    (Fintype.card_subtype (fun g : G => g • source = target)).symm

theorem orbit_twisted_sum_of_fixed
    (orbit : OrbitQuotient (G := G) (X := X))
    (horbit : quotientTwist twist twist_equivariant orbit = orbit) :
    (Finset.univ.sum fun x : MulAction.orbit G orbit.out =>
      Finset.univ.sum fun g : G =>
        if g • twist x.1 = x.1 then weight x.1 else 0) =
      Fintype.card G * quotientWeight weight weight_invariant orbit := by
  classical
  simp_rw [sum_indicator_eq_card_transporter_mul]
  have hweight (x : MulAction.orbit G orbit.out) :
      weight x.1 = quotientWeight weight weight_invariant orbit := by
    rw [← quotientWeight_mk weight weight_invariant x.1]
    congr 1
    exact (Quotient.sound x.2).trans (Quotient.out_eq' orbit)
  simp_rw [transporter_card_on_fixed_orbit twist twist_equivariant orbit horbit,
    hweight]
  rw [Finset.sum_const, nsmul_eq_mul]
  change (Fintype.card (MulAction.orbit G orbit.out) : ℚ) *
      ((Fintype.card (MulAction.stabilizer G orbit.out) : ℚ) *
        quotientWeight weight weight_invariant orbit) = _
  rw [← mul_assoc, ← Nat.cast_mul,
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group]

theorem orbit_twisted_sum_of_not_fixed
    (orbit : OrbitQuotient (G := G) (X := X))
    (horbit : quotientTwist twist twist_equivariant orbit ≠ orbit) :
    (Finset.univ.sum fun x : MulAction.orbit G orbit.out =>
      Finset.univ.sum fun g : G =>
        if g • twist x.1 = x.1 then weight x.1 else 0) = 0 := by
  classical
  simp_rw [sum_indicator_eq_card_transporter_mul]
  have hempty (x : MulAction.orbit G orbit.out) :
      Fintype.card (Transporter G (twist x.1) x.1) = 0 := by
    letI := transporter_is_empty_off_fixed_orbit twist twist_equivariant orbit horbit x
    exact Fintype.card_eq_zero
  simp [hempty]

/-- Weighted twisted Burnside identity.  The right side is the trace of the
induced signed permutation on the orbit quotient; the left side is the sum of
twisted labeled traces before division by the group order. -/
theorem labeledTwistedWeightSum_eq_card_mul_quotientFixedWeightSum :
    labeledTwistedWeightSum (G := G) twist weight =
      Fintype.card G *
        quotientFixedWeightSum (G := G) twist twist_equivariant weight
          weight_invariant := by
  classical
  unfold labeledTwistedWeightSum quotientFixedWeightSum
  rw [Finset.sum_comm]
  let decompose := MulAction.selfEquivSigmaOrbits G X
  let upstairs : X → ℚ := fun x =>
    Finset.univ.sum fun g : G =>
      if g • twist x = x then weight x else 0
  let decomposed :
      (Sigma fun orbit : OrbitQuotient (G := G) (X := X) =>
        MulAction.orbit G orbit.out) → ℚ := fun entry =>
    Finset.univ.sum fun g : G =>
      if g • twist entry.2.1 = entry.2.1 then weight entry.2.1 else 0
  rw [Fintype.sum_equiv decompose upstairs decomposed (fun _ => rfl)]
  rw [Fintype.sum_sigma, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro orbit _
  by_cases horbit : quotientTwist twist twist_equivariant orbit = orbit
  · rw [if_pos horbit]
    exact orbit_twisted_sum_of_fixed twist twist_equivariant weight
      weight_invariant orbit horbit
  · rw [if_neg horbit, mul_zero]
    exact orbit_twisted_sum_of_not_fixed twist twist_equivariant weight orbit horbit

end WeightedOrbitBurnside
end YangMills
end QuantumTheory
end Mettapedia

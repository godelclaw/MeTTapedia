import Mettapedia.QuantumTheory.YangMills.SupportGrowth

/-!
# Support-growth recurrence regression checks

Pins the coarsen-then-thicken uniform envelope, its `b = 2` instantiation,
the thicken-only linear envelope with its tightness witness, and the
dichotomy theorem.  Axiom audits are guarded so any future `sorry` or extra
axiom fails the build.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace SupportGrowthRegression

theorem good_uniform_bound_regression
    {r : ℕ → ℝ} {b A : ℝ} (hb : 1 < b) (hA : 0 ≤ A)
    (hrec : ∀ j, r (j + 1) ≤ r j / b + A) :
    ∀ J, r J ≤ r 0 / b ^ J + A * b / (b - 1) :=
  good_support_recurrence_uniform_bound hb hA hrec

theorem good_uniform_bound_two_regression
    {r : ℕ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hrec : ∀ j, r (j + 1) ≤ r j / 2 + A) :
    ∀ J, r J ≤ r 0 / 2 ^ J + 2 * A :=
  good_support_recurrence_uniform_bound_two hA hrec

theorem bad_linear_bound_regression
    {r : ℕ → ℝ} {A : ℝ}
    (hrec : ∀ j, r (j + 1) ≤ r j + A) :
    ∀ J : ℕ, r J ≤ r 0 + A * J :=
  bad_support_recurrence_linear_bound hrec

theorem bad_envelope_tight_regression (r0 A : ℝ) (j : ℕ) :
    badSupportEnvelope r0 A (j + 1) = badSupportEnvelope r0 A j + A :=
  badSupportEnvelope_step r0 A j

theorem bad_envelope_unbounded_regression
    {r0 A : ℝ} (hA : 0 < A) (M : ℝ) :
    ∃ J : ℕ, M < badSupportEnvelope r0 A J :=
  badSupportEnvelope_unbounded hA M

theorem dichotomy_regression
    {b A r0 : ℝ} (hb : 1 < b) (hA : 0 < A) (hr0 : 0 ≤ r0) :
    (∀ r : ℕ → ℝ, r 0 = r0 →
      (∀ j, r (j + 1) ≤ r j / b + A) →
      ∀ J, r J ≤ r0 + A * b / (b - 1)) ∧
    (∀ M : ℝ, ∃ J : ℕ, M < badSupportEnvelope r0 A J) :=
  support_growth_dichotomy hb hA hr0

/--
info: 'Mettapedia.QuantumTheory.YangMills.good_support_recurrence_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms good_support_recurrence_uniform_bound

/--
info: 'Mettapedia.QuantumTheory.YangMills.bad_support_recurrence_linear_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms bad_support_recurrence_linear_bound

/--
info: 'Mettapedia.QuantumTheory.YangMills.support_growth_dichotomy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms support_growth_dichotomy

end SupportGrowthRegression
end YangMills
end QuantumTheory
end Mettapedia

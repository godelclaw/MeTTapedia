import ProbabilityTheory.Cox.ProductRuleDerivation
import Mettapedia.ProbabilityTheory.Common.OrderedCombination

/-!
# Cox regraduation: positive powers and calibration

The operation-indexed carrier retains the given conjunction on `(0,1]`.
Reversing its probability order makes negative logarithms additive ordered
representations. Canonical representation uniqueness then determines all
multiplicative scales up to a positive power, on precisely that domain.
Agreement at one interior value fixes the power. Normalization at certainty
alone does not: identity and squaring both represent ordinary multiplication,
but squaring fails the ordinary complement equation.
-/

noncomputable section
namespace Mettapedia.ProbabilityTheory.Cox.Regraduation

open _root_.ProbabilityTheory.Cox _root_.ProbabilityTheory.Cox.CoxFullAxioms
open KnuthSkilling KnuthSkillingMonoidBase KnuthSkilling.Additive
open Mettapedia.ProbabilityTheory.OrderedCombination

/-- Valid values retain the conjunction whose multiplication they carry. -/
@[ext] structure CoxScale (C : CoxFullAxioms) where
  val : ℝ
  valid : val ∈ Set.Ioc 0 1

namespace CoxScale
variable {C : CoxFullAxioms}

instance : Monoid (CoxScale C) where
  one := ⟨1, by simp⟩
  mul x y := ⟨C.F x.val y.val,
    C.F_range _ _ x.valid.1 x.valid.2 y.valid.1 y.valid.2⟩
  mul_assoc x y z := CoxScale.ext (C.F_assoc x.val y.val z.val)
  one_mul x := CoxScale.ext (C.F_one_left x.val)
  mul_one x := CoxScale.ext (C.F_one_right x.val)

instance : KnuthSkillingMonoidBase (CoxScale C) where
  toLinearOrder := LinearOrder.lift' (β := ℝᵒᵈ) (fun x => OrderDual.toDual x.val)
    (fun _ _ h => CoxScale.ext h)
  op := (· * ·)
  op_assoc := mul_assoc
  ident := 1
  op_ident_left := one_mul
  op_ident_right := mul_one
  op_strictMono_left z _ _ h := C.F_strictMono_left z.val z.valid.1 z.valid.2 h
  op_strictMono_right z _ _ h := C.F_strictMono_right z.val z.valid.1 z.valid.2 h

@[simp] theorem val_one : (1 : CoxScale C).val = 1 := rfl
@[simp] theorem val_mul (x y : CoxScale C) : (x * y).val = C.F x.val y.val := rfl

/-- Each multiplicative scale gives a canonical additive representation. -/
def logRepresentation (g : MultiplicativeRepresentation C) :
    NormalizedRepresentationResult (CoxScale C) where
  Θ x := -Real.log (g.g x.val)
  order_preserving x y := by
    change y.val ≤ x.val ↔ -Real.log (g.g x.val) ≤ -Real.log (g.g y.val)
    rw [neg_le_neg_iff, Real.log_le_log_iff (g.g_pos _ y.valid.1 y.valid.2)
      (g.g_pos _ x.valid.1 x.valid.2)]
    exact (g.g_strictMonoOn.le_iff_le y.valid x.valid).symm
  additive x y := by
    change -Real.log (g.g (C.F x.val y.val)) = _
    rw [g.g_multiplicative _ _ x.valid.1 x.valid.2 y.valid.1 y.valid.2,
      Real.log_mul (ne_of_gt (g.g_pos _ x.valid.1 x.valid.2))
        (ne_of_gt (g.g_pos _ y.valid.1 y.valid.2)), neg_add]
  ident_zero := by
    change -Real.log (g.g 1) = 0
    rw [g_one_eq_one C g, Real.log_one, neg_zero]

/-- The supplied conjunction action and its logarithmic observation commute. -/
theorem observe_step (g : MultiplicativeRepresentation C) (x s : CoxScale C) :
    (logRepresentation g).Θ (rightRegular (MulOpposite.op x) s) =
      (logRepresentation g).Θ s + (logRepresentation g).Θ x :=
  (logRepresentation g).additive s x

/-- Normalized multiplicative representations differ by a positive power. -/
theorem positive_power (g₁ g₂ : MultiplicativeRepresentation C) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ Set.Ioc (0 : ℝ) 1, g₂.g x = (g₁.g x) ^ c := by
  let a : CoxScale C := ⟨1 / 2, by norm_num⟩
  obtain ⟨c, hc, h⟩ := KnuthSkilling.Additive.Axioms.OpIsAddition.representation_unique_up_to_scale
    (CoxScale C) (logRepresentation g₁).Θ (logRepresentation g₂).Θ
    (logRepresentation g₁).order_preserving (logRepresentation g₂).order_preserving
    (logRepresentation g₁).ident_zero (logRepresentation g₂).ident_zero
    (logRepresentation g₁).additive (logRepresentation g₂).additive a (by change (1 / 2 : ℝ) < 1; norm_num)
  refine ⟨c, hc, fun x hx => ?_⟩
  have heq := h ⟨x, hx⟩
  change -Real.log (g₂.g x) = c * -Real.log (g₁.g x) at heq
  have hlog : Real.log (g₂.g x) = Real.log (g₁.g x) * c := by linarith
  rw [Real.rpow_def_of_pos (g₁.g_pos x hx.1 hx.2), ← hlog,
    Real.exp_log (g₂.g_pos x hx.1 hx.2)]

/-- An interior calibration, unlike certainty normalization, fixes the scale. -/
theorem interior_calibration_unique (g₁ g₂ : MultiplicativeRepresentation C)
    {a : ℝ} (ha : a ∈ Set.Ioo 0 1) (hanchor : g₁.g a = g₂.g a) :
    ∀ x ∈ Set.Ioc (0 : ℝ) 1, g₁.g x = g₂.g x := by
  let anchor : CoxScale C := ⟨a, ha.1, ha.2.le⟩
  have heq := calibrated_unique (logRepresentation g₁) (logRepresentation g₂)
    anchor (by exact ha.2) (by change -Real.log (g₁.g a) = -Real.log (g₂.g a); rw [hanchor])
  intro x hx
  have h := congrFun heq ⟨x, hx⟩
  change -Real.log (g₁.g x) = -Real.log (g₂.g x) at h
  exact Real.log_injOn_pos (g₁.g_pos x hx.1 hx.2) (g₂.g_pos x hx.1 hx.2) (neg_injective h)

end CoxScale

/-- A second scale for ordinary multiplication, with the same value at certainty. -/
def squareRepresentation : MultiplicativeRepresentation standard_productRule_satisfies_cox where
  g x := x ^ 2
  g_pos x hx _ := pow_pos hx 2
  g_strictMonoOn := by
    intro x hx y hy hxy
    nlinarith [hx.1, hy.1]
  g_continuousOn := (continuous_id.pow 2).continuousOn
  g_multiplicative x y _ _ _ _ := mul_pow x y 2

/-- Certainty normalization alone admits distinct scales. -/
theorem identity_square_distinct :
    standard_productRule_multRep.g 1 = squareRepresentation.g 1 ∧
      standard_productRule_multRep.g (1 / 2) ≠ squareRepresentation.g (1 / 2) := by
  norm_num [standard_productRule_multRep, squareRepresentation]

/-- Product regraduation does not automatically preserve the ordinary complement. -/
theorem square_fails_complement :
    squareRepresentation.g (1 - (1 / 2)) ≠ 1 - squareRepresentation.g (1 / 2) := by
  norm_num [squareRepresentation]

end Mettapedia.ProbabilityTheory.Cox.Regraduation

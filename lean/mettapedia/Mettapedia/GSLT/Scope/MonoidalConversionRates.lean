import Mettapedia.GSLT.Scope.ConversionPotentials

/-!
# Monoidal common measures need admitted multiplication of exchanges

If multiplying an edge on the left yields an admitted edge with the same
rate, this action extends to every reversible path. Connectedness from the
monoid unit then proves that the normalized common measure is a monoid
homomorphism. The edge action is explicit; compatibility of numeric rates
without the required edges cannot supply this conclusion.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Scope.ConversionRates.Graph

universe uToken uEdge

noncomputable section

variable {Token : Type uToken} [Monoid Token] (G : Graph.{uToken, uEdge} Token)

structure LeftCompatible where
  multiply : ∀ left : Token, ∀ {source target : Token},
    G.Edge source target → G.Edge (left * source) (left * target)
  rate_multiply : ∀ (left : Token) {source target : Token} (edge : G.Edge source target),
    G.rate (multiply left edge) = G.rate edge

def LeftCompatible.walk (admission : G.LeftCompatible) (left : Token) :
    {source target : Token} → G.Walk source target → G.Walk (left * source) (left * target)
  | _, _, .nil token => .nil (left * token)
  | _, _, .forward edge rest => .forward (admission.multiply left edge) (walk admission left rest)
  | _, _, .backward edge rest => .backward (admission.multiply left edge) (walk admission left rest)

theorem LeftCompatible.walk_yield (admission : G.LeftCompatible) (left : Token)
    {source target : Token} (path : G.Walk source target) :
    G.yield (LeftCompatible.walk G admission left path) = G.yield path := by
  induction path with
  | nil => rfl
  | forward edge rest ih => rw [LeftCompatible.walk, yield, yield, admission.rate_multiply, ih]
  | backward edge rest ih => rw [LeftCompatible.walk, yield, yield, admission.rate_multiply, ih]

def normalized (valuation : G.Valuation) : G.Valuation :=
  Valuation.rescale G valuation (valuation.price 1)⁻¹ (inv_pos.mpr (valuation.positive 1))

theorem normalized_unit (valuation : G.Valuation) : (normalized G valuation).price 1 = 1 :=
  inv_mul_cancel₀ (valuation.positive 1).ne'

theorem normalized_mul (admission : G.LeftCompatible)
    (connected : ∀ token : Token, Trunc (G.Walk 1 token)) (valuation : G.Valuation)
    (left right : Token) :
    (normalized G valuation).price (left * right) =
      (normalized G valuation).price left * (normalized G valuation).price right := by
  let chosen := normalized G valuation
  have unit : chosen.price 1 = 1 := normalized_unit G valuation
  induction connected right using Trunc.induction_on with
  | h path =>
      have first := Valuation.yield_ratio G chosen path
      have multiplied := Valuation.yield_ratio G chosen (LeftCompatible.walk G admission left path)
      rw [LeftCompatible.walk_yield G admission, mul_one] at multiplied
      have ratio : chosen.price left / chosen.price (left * right) =
          chosen.price 1 / chosen.price right := multiplied.symm.trans first
      have cross := (div_eq_div_iff (chosen.positive (left * right)).ne'
        (chosen.positive right).ne').mp ratio
      rw [unit, one_mul] at cross
      exact cross.symm

def normalizedHom (admission : G.LeftCompatible)
    (connected : ∀ token : Token, Trunc (G.Walk 1 token)) (valuation : G.Valuation) : Token →* ℝ where
  toFun := (normalized G valuation).price
  map_one' := normalized_unit G valuation
  map_mul' := normalized_mul G admission connected valuation

theorem normalized_unique (connected : ∀ token : Token, Trunc (G.Walk 1 token))
    (first second : G.Valuation) : normalized G first = normalized G second :=
  Valuation.unique_at_root G connected _ _
    ((normalized_unit G first).trans (normalized_unit G second).symm)

end

end Mettapedia.GSLT.Scope.ConversionRates.Graph

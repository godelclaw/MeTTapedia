import Mettapedia.GSLT.Scope.ConversionRates

/-!
# Log potentials and uniqueness of a virtual token

The common measure and its logarithmic potential are mutually inverse
constructions. On a connected conversion graph, two positive common measures
differ by one positive global scale. Fixing the price of the root fixes that
scale. The result uses all reversible paths, including variable-length paths
and repeated edges.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Scope.ConversionRates.Graph

universe uToken uEdge

noncomputable section

variable {Token : Type uToken} (G : Graph.{uToken, uEdge} Token)

theorem Valuation.ext {first second : G.Valuation}
    (prices : first.price = second.price) : first = second := by
  cases first
  cases second
  cases prices
  rfl

structure Potential where
  value : Token → ℝ
  respects : ∀ {source target : Token} (edge : G.Edge source target),
    Real.log (G.rate edge) = value source - value target

theorem Potential.ext {first second : G.Potential}
    (values : first.value = second.value) : first = second := by
  cases first
  cases second
  cases values
  rfl

def Valuation.toPotential (valuation : G.Valuation) : G.Potential where
  value token := Real.log (valuation.price token)
  respects {source target} edge := by
    rw [valuation.respects edge,
      Real.log_div (valuation.positive source).ne' (valuation.positive target).ne']

def Potential.toValuation (potential : G.Potential) : G.Valuation where
  price token := Real.exp (potential.value token)
  positive token := Real.exp_pos _
  respects edge := by
    have exponentiated := congrArg Real.exp (potential.respects edge)
    rwa [Real.exp_log (G.positive edge), Real.exp_sub] at exponentiated

theorem valuation_log_exp (valuation : G.Valuation) :
    Potential.toValuation G (Valuation.toPotential G valuation) = valuation := by
  apply Valuation.ext G
  funext token
  exact Real.exp_log (valuation.positive token)

theorem potential_exp_log (potential : G.Potential) :
    Valuation.toPotential G (Potential.toValuation G potential) = potential := by
  apply Potential.ext G
  funext token
  exact Real.log_exp _

def valuationPotentialEquiv : G.Valuation ≃ G.Potential where
  toFun := Valuation.toPotential G
  invFun := Potential.toValuation G
  left_inv := valuation_log_exp G
  right_inv := potential_exp_log G

variable {root : Token}

theorem noArbitrage_iff_potential
    (connected : ∀ token : Token, Trunc (G.Walk root token)) :
    G.NoArbitrage ↔ Nonempty G.Potential := by
  rw [G.noArbitrage_iff_valuation connected]
  exact ⟨fun ⟨valuation⟩ => ⟨Valuation.toPotential G valuation⟩,
    fun ⟨potential⟩ => ⟨Potential.toValuation G potential⟩⟩

def Valuation.rescale (valuation : G.Valuation) (scale : ℝ) (positive : 0 < scale) : G.Valuation where
  price token := scale * valuation.price token
  positive token := mul_pos positive (valuation.positive token)
  respects {source target} edge := by
    rw [mul_div_mul_left _ _ positive.ne']
    exact valuation.respects edge

theorem Valuation.unique_scale
    (connected : ∀ token : Token, Trunc (G.Walk root token))
    (first second : G.Valuation) (token : Token) :
    second.price token = (second.price root / first.price root) * first.price token := by
  induction connected token using Trunc.induction_on with
  | h walk =>
      have ratio : second.price root / second.price token =
          first.price root / first.price token :=
        (Valuation.yield_ratio G second walk).symm.trans (Valuation.yield_ratio G first walk)
      have cross := (div_eq_div_iff (second.positive token).ne' (first.positive token).ne').mp ratio
      field_simp [(first.positive root).ne']
      simpa only [mul_comm] using cross.symm

theorem Valuation.unique_at_root
    (connected : ∀ token : Token, Trunc (G.Walk root token))
    (first second : G.Valuation) (sameRoot : first.price root = second.price root) :
    first = second := by
  apply Valuation.ext G
  funext token
  rw [Valuation.unique_scale G connected first second token, ← sameRoot,
    div_self (first.positive root).ne', one_mul]

theorem reconstructed_root_is_one (noArbitrage : G.NoArbitrage)
    (connected : ∀ token : Token, Trunc (G.Walk root token)) :
    (G.valuationOfNoArbitrage noArbitrage connected).price root = 1 := by
  change (G.rootAmount noArbitrage connected root)⁻¹ = 1
  unfold rootAmount
  induction connected root using Trunc.induction_on with
  | h loop =>
      change (G.views.transport loop (1 : ℝ))⁻¹ = 1
      rw [G.transport_yield, noArbitrage loop, one_mul, inv_one]

end

end Mettapedia.GSLT.Scope.ConversionRates.Graph

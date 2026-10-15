import Mettapedia.GSLT.Scope.Holonomy
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Reversible conversion rates and their common measure

Positive rates act on amounts by multiplication. Walks use declared edges in
either orientation, with inverse rates in the reverse orientation. Their
yield is the actual product of these rates. The existing view-system holonomy
construction reconstructs a positive common measure on a connected graph
exactly when every closed walk has yield one.

Connectedness is a truncated walk from a root. No finite graph or selected
spanning tree is required. A common measure prices conversions; permission
to execute an exchange remains separate.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Scope.ConversionRates

universe uToken uEdge

structure Graph (Token : Type uToken) where
  Edge : Token → Token → Type uEdge
  rate : ∀ {source target : Token}, Edge source target → ℝ
  positive : ∀ {source target : Token} (edge : Edge source target), 0 < rate edge

namespace Graph

noncomputable section

variable {Token : Type uToken} (G : Graph.{uToken, uEdge} Token)

def exchangeEquiv {source target : Token} (edge : G.Edge source target) : ℝ ≃ ℝ where
  toFun amount := amount * G.rate edge
  invFun amount := amount / G.rate edge
  left_inv amount := mul_div_cancel_right₀ amount (G.positive edge).ne'
  right_inv amount := div_mul_cancel₀ amount (G.positive edge).ne'

abbrev views : ViewSystem.{uToken, uEdge, 0} Token where
  View _ := ℝ
  Edge := G.Edge
  translate := G.exchangeEquiv

abbrev Walk (source target : Token) := G.views.Walk source target

def yield : {source target : Token} → G.Walk source target → ℝ
  | _, _, .nil _ => 1
  | _, _, .forward edge rest => G.rate edge * yield rest
  | _, _, .backward edge rest => (G.rate edge)⁻¹ * yield rest

theorem yield_positive {source target : Token} (walk : G.Walk source target) :
    0 < G.yield walk := by
  induction walk with
  | nil => exact zero_lt_one
  | forward edge rest ih => exact mul_pos (G.positive edge) ih
  | backward edge rest ih => exact mul_pos (inv_pos.mpr (G.positive edge)) ih

theorem transport_yield {source target : Token} (walk : G.Walk source target) (amount : ℝ) :
    G.views.transport walk amount = amount * G.yield walk := by
  induction walk generalizing amount with
  | nil => exact (mul_one amount).symm
  | forward edge rest ih =>
      change G.views.transport rest (amount * G.rate edge) = _
      rw [ih]
      exact mul_assoc amount (G.rate edge) (G.yield rest)
  | backward edge rest ih =>
      change G.views.transport rest (amount / G.rate edge) = _
      rw [ih, div_eq_mul_inv, mul_assoc]
      rfl

def NoArbitrage : Prop := ∀ {token : Token} (loop : G.Walk token token), G.yield loop = 1

theorem noArbitrage_iff_holonomy : G.NoArbitrage ↔ G.views.TrivialHolonomy := by
  constructor
  · intro noArbitrage token loop amount
    exact (G.transport_yield loop amount).trans (by rw [noArbitrage loop, mul_one])
  · intro trivial token loop
    have fixed : (G.views.transport loop (1 : ℝ) : ℝ) = 1 := trivial loop (1 : ℝ)
    simpa only [G.transport_yield, one_mul] using fixed

structure Valuation where
  price : Token → ℝ
  positive : ∀ token, 0 < price token
  respects : ∀ {source target : Token} (edge : G.Edge source target),
    G.rate edge = price source / price target

theorem Valuation.yield_ratio (valuation : G.Valuation)
    {source target : Token} (walk : G.Walk source target) :
    G.yield walk = valuation.price source / valuation.price target := by
  induction walk with
  | nil token => exact (div_self (valuation.positive token).ne').symm
  | @forward first middle last edge rest ih =>
      rw [yield, valuation.respects edge, ih]
      field_simp [(valuation.positive first).ne', (valuation.positive middle).ne',
        (valuation.positive last).ne']
  | @backward first middle last edge rest ih =>
      rw [yield, valuation.respects edge, ih]
      field_simp [(valuation.positive first).ne', (valuation.positive middle).ne',
        (valuation.positive last).ne']

theorem Valuation.noArbitrage (valuation : G.Valuation) : G.NoArbitrage := by
  intro token loop
  rw [Valuation.yield_ratio G valuation loop, div_self (valuation.positive token).ne']

variable {root : Token}

def rootAmount (noArbitrage : G.NoArbitrage)
    (connected : ∀ token : Token, Trunc (G.Walk root token)) (token : Token) : ℝ :=
  ViewSystem.liftTransport
    ((ViewSystem.trivialHolonomy_iff_pathIndependent G.views).mp
      (G.noArbitrage_iff_holonomy.mp noArbitrage)) (connected token) (1 : ℝ)

theorem rootAmount_positive (noArbitrage : G.NoArbitrage)
    (connected : ∀ token : Token, Trunc (G.Walk root token)) (token : Token) :
    0 < G.rootAmount noArbitrage connected token := by
  unfold rootAmount
  induction connected token using Trunc.induction_on with
  | h walk =>
      change (0 : ℝ) < (G.views.transport walk (1 : ℝ) : ℝ)
      rw [G.transport_yield, one_mul]
      exact G.yield_positive walk

theorem rootAmount_edge (noArbitrage : G.NoArbitrage)
    (connected : ∀ token : Token, Trunc (G.Walk root token))
    {source target : Token} (edge : G.Edge source target) :
    G.rootAmount noArbitrage connected source * G.rate edge =
      G.rootAmount noArbitrage connected target := by
  exact (ViewSystem.gluingOfTrivialHolonomy
    (G.noArbitrage_iff_holonomy.mp noArbitrage) connected).compatible edge (1 : ℝ)

def valuationOfNoArbitrage (noArbitrage : G.NoArbitrage)
    (connected : ∀ token : Token, Trunc (G.Walk root token)) : G.Valuation where
  price token := (G.rootAmount noArbitrage connected token)⁻¹
  positive token := inv_pos.mpr (G.rootAmount_positive noArbitrage connected token)
  respects {source target} edge := by
    have sourceNonzero := (G.rootAmount_positive noArbitrage connected source).ne'
    have targetNonzero := (G.rootAmount_positive noArbitrage connected target).ne'
    have comparison := G.rootAmount_edge noArbitrage connected edge
    field_simp
    simpa only [mul_comm] using comparison

theorem noArbitrage_iff_valuation
    (connected : ∀ token : Token, Trunc (G.Walk root token)) :
    G.NoArbitrage ↔ Nonempty G.Valuation :=
  ⟨fun noArbitrage => ⟨G.valuationOfNoArbitrage noArbitrage connected⟩,
    fun ⟨valuation⟩ => Valuation.noArbitrage G valuation⟩

end

end Graph

end Mettapedia.GSLT.Scope.ConversionRates

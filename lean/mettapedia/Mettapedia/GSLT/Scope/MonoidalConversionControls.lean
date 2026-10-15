import Mettapedia.GSLT.Scope.MonoidalConversionRates

/-!
# Multiplicative prices and their edge-admission separator

On additive natural signatures, powers of two give a nonconstant monoidal
common measure. The rate is independently written as an integer power of the
signature difference. In contrast, successor-sized prices give a perfectly
consistent common measure, but their normalized prices are not monoidal and
their graph has no rate-preserving multiplication action.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Scope.ConversionRates.MonoidalControls

open Graph

noncomputable section

abbrev Signature := Multiplicative Nat

def growthRate {source target : Signature} (_edge : PUnit.{1}) : ℝ :=
  (2 : ℝ) ^ ((source.toAdd : ℤ) - (target.toAdd : ℤ))

abbrev growth : Graph Signature where
  Edge _ _ := PUnit.{1}
  rate {source target} edge := growthRate (source := source) (target := target) edge
  positive {source target} _ := zpow_pos (by norm_num : (0 : ℝ) < 2)
    ((source.toAdd : ℤ) - (target.toAdd : ℤ))

def growthValue : growth.Valuation where
  price token := (2 : ℝ) ^ token.toAdd
  positive token := pow_pos (by norm_num) _
  respects {source target} edge := by
    change (2 : ℝ) ^ ((source.toAdd : ℤ) - (target.toAdd : ℤ)) =
      (2 : ℝ) ^ source.toAdd / (2 : ℝ) ^ target.toAdd
    rw [zpow_sub₀ (by norm_num), zpow_natCast, zpow_natCast]

def growthConnected (token : Signature) : Trunc (growth.Walk 1 token) :=
  Trunc.mk (.forward PUnit.unit (.nil token))

def growthAdmission : growth.LeftCompatible where
  multiply _left {_source _target} _edge := PUnit.unit
  rate_multiply left {source target} _ := by
    change (2 : ℝ) ^ (((left.toAdd + source.toAdd : Nat) : ℤ) -
      ((left.toAdd + target.toAdd : Nat) : ℤ)) =
        (2 : ℝ) ^ ((source.toAdd : ℤ) - (target.toAdd : ℤ))
    rw [Nat.cast_add, Nat.cast_add]
    congr 1
    omega

theorem constructed_hom_has_price_eight :
    normalizedHom growth growthAdmission growthConnected growthValue (Multiplicative.ofAdd 3) = 8 := by
  norm_num [normalizedHom, normalized, Valuation.rescale, growthValue]

theorem constructed_hom_multiplies_actual_signatures (first second : Signature) :
    normalizedHom growth growthAdmission growthConnected growthValue (first * second) =
      normalizedHom growth growthAdmission growthConnected growthValue first *
      normalizedHom growth growthAdmission growthConnected growthValue second :=
  (normalizedHom growth growthAdmission growthConnected growthValue).map_mul first second

def sizePrice (token : Signature) : ℝ := (token.toAdd : ℝ) + 1

abbrev sizeGraph : Graph Signature where
  Edge _ _ := PUnit.{1}
  rate {source target} _ := sizePrice source / sizePrice target
  positive _ := div_pos (by unfold sizePrice; positivity) (by unfold sizePrice; positivity)

def sizeValue : sizeGraph.Valuation where
  price := sizePrice
  positive _ := by unfold sizePrice; positivity
  respects _ := rfl

theorem common_measure_does_not_imply_monoidal_price :
    (normalized sizeGraph sizeValue).price (Multiplicative.ofAdd 2) ≠
      (normalized sizeGraph sizeValue).price (Multiplicative.ofAdd 1) *
      (normalized sizeGraph sizeValue).price (Multiplicative.ofAdd 1) := by
  norm_num [normalized, Valuation.rescale, sizeValue, sizePrice]

theorem no_multiplication_admission_for_size_rates : ¬ Nonempty sizeGraph.LeftCompatible := by
  rintro ⟨admission⟩
  have sameRate := admission.rate_multiply (Multiplicative.ofAdd 1)
    (source := (1 : Signature)) (target := Multiplicative.ofAdd 1) PUnit.unit
  norm_num [sizePrice] at sameRate

end

end Mettapedia.GSLT.Scope.ConversionRates.MonoidalControls

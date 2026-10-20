import Mettapedia.PLN.Evidence.BinaryEvidenceSemiring
import Mettapedia.PLN.WorldModel.EvidenceSpaces
import Mettapedia.PLN.Evidence.EvidentialLedger

/-!
# Identical count coordinates with distinct multiplication regimes

Paired-sample counts and tensor counts have the same additive coordinates.
Their multiplicative units and products differ. The coordinate correspondence
is therefore an additive equivalence, not a semiring equivalence. Embedding
sample counts into extended nonnegative binary counts preserves revision;
embedding tensor counts also preserves their coordinatewise product.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.Evidence.CountRegimes

open scoped ENNReal
open Mettapedia.PLN.WorldModel.EvidenceSpaces
open Mettapedia.PLN.Evidence.EvidentialLedger

/-- Retain both natural-number coordinates and their additive operation. -/
def sampleTensorAddEquiv : Evidence ℕ ≃+ BinEvNat where
  toFun counts := ⟨counts.pos, counts.neg⟩
  invFun counts := ⟨counts.pos, counts.neg⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Tensor counts embed into the existing binary tensor semiring. -/
noncomputable def tensorEmbedding : BinEvNat →+* BinaryEvidence where
  toFun := BinEvNat.toBinaryEvidence
  map_zero' := BinEvNat.toBinaryEvidence_zero
  map_one' := BinEvNat.toBinaryEvidence_one
  map_add' := BinEvNat.toBinaryEvidence_add
  map_mul' := BinEvNat.toBinaryEvidence_mul

/-- Sample-count revision is retained without changing its multiplication
into tensor fusion. Both count coordinates are preserved exactly. -/
noncomputable def sampleEmbedding : Evidence ℕ →+ BinaryEvidence :=
  tensorEmbedding.toAddMonoidHom.comp sampleTensorAddEquiv.toAddMonoidHom

@[simp] theorem sampleEmbedding_pos (counts : Evidence ℕ) :
    (sampleEmbedding counts).pos = (counts.pos : ℝ≥0∞) := rfl

@[simp] theorem sampleEmbedding_neg (counts : Evidence ℕ) :
    (sampleEmbedding counts).neg = (counts.neg : ℝ≥0∞) := rfl

/-- The additive correspondence agrees with the established coefficient map
on paired-sample counts, after exposing the binary count coordinates. -/
theorem sampleEmbedding_toPaired (counts : Evidence ℕ) :
    toPaired (sampleEmbedding counts) = Evidence.map (Nat.castRingHom ℝ≥0∞) counts := rfl

theorem sampleEmbedding_injective : Function.Injective sampleEmbedding := by
  intro first second same
  apply Evidence.ext
  · have positive := congrArg BinaryEvidence.pos same
    simp only [sampleEmbedding_pos] at positive
    exact_mod_cast positive
  · have negative := congrArg BinaryEvidence.neg same
    simp only [sampleEmbedding_neg] at negative
    exact_mod_cast negative

theorem sampleEmbedding_total (counts : Evidence ℕ) :
    (sampleEmbedding counts).total = (counts.total : ℝ≥0∞) := by
  simp [BinaryEvidence.total, Evidence.total]

theorem sampleEmbedding_finite (counts : Evidence ℕ) : (sampleEmbedding counts).total ≠ ⊤ := by
  rw [sampleEmbedding_total]
  exact ENNReal.natCast_ne_top _

/-- The sample product's unit is one positive sample; the tensor product's
unit has one count in each coordinate. The additive map retains this difference. -/
theorem sample_unit_is_not_tensor_unit : sampleEmbedding (1 : Evidence ℕ) ≠ 1 := by
  intro same
  have negative := congrArg BinaryEvidence.neg same
  have tensorOne : (1 : BinaryEvidence).neg = 1 := rfl
  rw [sampleEmbedding_neg, Evidence.one_neg, Nat.cast_zero, tensorOne] at negative
  exact zero_ne_one negative

theorem sample_product_is_not_tensor_product :
    sampleEmbedding ((⟨1, 1⟩ : Evidence ℕ) * ⟨1, 1⟩) ≠
      sampleEmbedding ⟨1, 1⟩ * sampleEmbedding ⟨1, 1⟩ := by
  intro same
  have negative := congrArg BinaryEvidence.neg same
  norm_num [sampleEmbedding_neg, Evidence.mul_neg, BinaryEvidence.tensor_def] at negative

/-- No semiring interpretation can preserve all these same count coordinates.
A consumer of polynomial products must choose its multiplication regime. -/
theorem no_coordinate_preserving_semiring_map :
    ¬ ∃ interpretation : Evidence ℕ →+* BinaryEvidence,
      ∀ counts, interpretation counts = sampleEmbedding counts := by
  rintro ⟨interpretation, coordinates⟩
  apply sample_unit_is_not_tensor_unit
  rw [← coordinates 1, map_one]

end Mettapedia.PLN.Evidence.CountRegimes

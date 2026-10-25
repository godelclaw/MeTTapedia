import Mettapedia.Computability.PNP.FiniteUniformRecovery
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Rat.Cast.Order
import Mettapedia.ProbabilityTheory.FiniteEventMass

/-!
# Uniform finite-sample densities

These rational cardinality ratios realize constant-weight finite events.
Nondeceptive samples complement deceptive samples; realizability places
nondeceptive samples inside exact recovery. Nonempty domains justify the
normalization and strict-positivity statements.
-/

namespace Mettapedia.Computability.PNP.EncodedFamily

universe u v

variable {Input : Type u} {Output : Type v}
variable [Fintype Input] [DecidableEq Output]
variable (H : EncodedFamily Input Output)

/-- Samples outside the deceptive set. -/
abbrev NondeceptiveSamples (target : Input → Output) (m : ℕ) :=
  { sample : PointSample Input m // ¬ H.IsDeceptiveSample target sample }

noncomputable instance nondeceptiveSamplesFintype
    (target : Input → Output) (m : ℕ) :
    Fintype (H.NondeceptiveSamples target m) :=
  Fintype.ofFinite _

/-- Samples on which the chosen ERM predictor exactly matches the target. -/
abbrev ExactRecoverySamples [Nonempty H.Code] (target : Input → Output) (m : ℕ) :=
  { sample : PointSample Input m //
      H.empiricalRiskPredictor (labeledByTarget target sample) = target }

noncomputable instance exactRecoverySamplesFintype [Nonempty H.Code]
    (target : Input → Output) (m : ℕ) :
    Fintype (H.ExactRecoverySamples target m) :=
  Fintype.ofFinite _

/-- Uniform density of deceptive samples, expressed as a rational cardinality
ratio on the finite point-sample space. -/
noncomputable def deceptiveRate
    (target : Input → Output) (m : ℕ) : ℚ :=
  Fintype.card (H.DeceptiveSamples target m) / Fintype.card (PointSample Input m)

/-- Uniform density of non-deceptive samples. -/
noncomputable def nondeceptiveRate
    (target : Input → Output) (m : ℕ) : ℚ :=
  Fintype.card (H.NondeceptiveSamples target m) / Fintype.card (PointSample Input m)

/-- Uniform density of exact ERM recovery samples. -/
noncomputable def exactRecoveryRate [Nonempty H.Code]
    (target : Input → Output) (m : ℕ) : ℚ :=
  Fintype.card (H.ExactRecoverySamples target m) / Fintype.card (PointSample Input m)

omit [DecidableEq Output] in
theorem card_nondeceptiveSamples
    (target : Input → Output) (m : ℕ) :
    Fintype.card (H.NondeceptiveSamples target m) =
      Fintype.card (PointSample Input m) -
        Fintype.card (H.DeceptiveSamples target m) := by
  classical
  simpa only [NondeceptiveSamples, DeceptiveSamples] using
    (Fintype.card_subtype_compl
      (p := fun sample : PointSample Input m => H.IsDeceptiveSample target sample))

theorem deceptiveRate_le
    [Nonempty Input]
    (target : Input → Output) (m : ℕ) :
    H.deceptiveRate target m ≤
      (((Fintype.card H.Code : ℚ) * ((Fintype.card Input : ℚ) - 1) ^ m) /
        Fintype.card (PointSample Input m)) := by
  unfold deceptiveRate
  apply div_le_div_of_nonneg_right _ (by positivity)
  have bound := Nat.cast_le (α := ℚ).mpr (H.card_deceptiveSamples_le target m)
  simpa only [Nat.cast_mul, Nat.cast_pow,
    Nat.cast_sub (Nat.succ_le_of_lt Fintype.card_pos), Nat.cast_one] using bound

theorem deceptiveRate_le_bound
    [Nonempty Input]
    (target : Input → Output) (m : ℕ) :
    H.deceptiveRate target m ≤
      (((Fintype.card H.Code : ℚ) * ((Fintype.card Input : ℚ) - 1) ^ m) /
        ((Fintype.card Input : ℚ) ^ m)) := by
  simpa [card_pointSample Input m, Nat.cast_pow] using H.deceptiveRate_le target m

omit [DecidableEq Output] in
theorem nondeceptiveRate_eq_one_sub_deceptiveRate
    [Nonempty Input]
    (target : Input → Output) (m : ℕ) :
    H.nondeceptiveRate target m = 1 - H.deceptiveRate target m := by
  have count : (Fintype.card (H.NondeceptiveSamples target m) : ℚ) =
      (Fintype.card (PointSample Input m) : ℚ) - Fintype.card (H.DeceptiveSamples target m) := by
    rw [H.card_nondeceptiveSamples, Nat.cast_sub (Fintype.card_subtype_le _)]
  have positive : (0 : ℚ) < Fintype.card (PointSample Input m) := by exact_mod_cast Fintype.card_pos
  simp only [nondeceptiveRate, deceptiveRate, count, sub_div, div_self positive.ne']

theorem card_nondeceptiveSamples_le_exactRecoverySamples
    [Nonempty H.Code]
    (target : Input → Output) (m : ℕ)
    (htarget : ∃ c : H.Code, H.decode c = target) :
    Fintype.card (H.NondeceptiveSamples target m) ≤
      Fintype.card (H.ExactRecoverySamples target m) := by
  exact Fintype.card_le_of_embedding
    ⟨fun sample => ⟨sample.1, H.empiricalRiskPredictor_eq_target_of_not_deceptive
      target sample.1 htarget sample.2⟩,
      fun _ _ same => Subtype.ext (congrArg (fun s : H.ExactRecoverySamples target m => s.1) same)⟩

theorem exactRecoveryRate_ge_nondeceptiveRate
    [Nonempty H.Code]
    (target : Input → Output) (m : ℕ)
    (htarget : ∃ c : H.Code, H.decode c = target) :
    H.nondeceptiveRate target m ≤ H.exactRecoveryRate target m := by
  unfold nondeceptiveRate exactRecoveryRate
  refine div_le_div_of_nonneg_right ?_ ?_
  · exact_mod_cast
      H.card_nondeceptiveSamples_le_exactRecoverySamples target m htarget
  · positivity

theorem exactRecoveryRate_ge_one_sub_deceptiveRate
    [Nonempty Input] [Nonempty H.Code]
    (target : Input → Output) (m : ℕ)
    (htarget : ∃ c : H.Code, H.decode c = target) :
    1 - H.deceptiveRate target m ≤ H.exactRecoveryRate target m := by
  rw [← H.nondeceptiveRate_eq_one_sub_deceptiveRate target m]
  exact H.exactRecoveryRate_ge_nondeceptiveRate target m htarget

theorem exactRecoveryRate_pos_of_bound_lt
    [Nonempty Input] [Nonempty H.Code]
    (target : Input → Output) (m : ℕ)
    (htarget : ∃ c : H.Code, H.decode c = target)
    (hbound :
      Fintype.card H.Code * (Fintype.card Input - 1) ^ m <
        Fintype.card Input ^ m) :
    0 < H.exactRecoveryRate target m := by
  obtain ⟨sample, exactness⟩ := H.exists_sample_empiricalRiskPredictor_eq_target_of_bound_lt
    target m htarget hbound
  apply div_pos
  · exact_mod_cast Fintype.card_pos_iff.mpr ⟨(⟨sample, exactness⟩ : H.ExactRecoverySamples target m)⟩
  · exact_mod_cast Fintype.card_pos (α := PointSample Input m)

omit [DecidableEq Output] in
/-- The uniform density agrees with an independently weighted finite event. -/
theorem deceptiveRate_eq_eventMass (target : Input → Output) (m : Nat)
    [DecidablePred (H.IsDeceptiveSample target (m := m))] :
    H.deceptiveRate target m = Mettapedia.ProbabilityTheory.FiniteEventMass.mass
      (fun _ : PointSample Input m => (Fintype.card (PointSample Input m) : ℚ)⁻¹)
      (fun sample => decide (H.IsDeceptiveSample target sample)) := by
  classical
  rw [Mettapedia.ProbabilityTheory.FiniteEventMass.mass_subtype
    (subtypeFintype := H.deceptiveSamplesFintype target m)]
  simp [deceptiveRate, div_eq_mul_inv, nsmul_eq_mul]

end Mettapedia.Computability.PNP.EncodedFamily

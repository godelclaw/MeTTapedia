import Mettapedia.Computability.PNP.ABVisibleInvariantSurjectivityObstructionBoolZ
import Mettapedia.Computability.PNP.ABVisibleInvariantSurjectivityObstructionSurjectivity

/-!
# P vs NP crux: route wrappers for AB-invariance obstruction

This module repackages the raw AB-invariance and hidden-`z` obstructions for the
canonical shared-AB data records used by the crux route.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section RouteWrappers

variable {Z : Type*} {r k : ℕ} {Index : Type*}

section

variable [Inhabited Z] [Nontrivial Z]

theorem SharedABAffineFeatureTargetData.not_surjective_predict_of_nontrivial
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : SharedABAffineFeatureTargetData (Z := Z) (r := r) (k := k) (Index := Index) G) :
    ¬ Function.Surjective G.predict := by
  exact
    not_surjective_predict_of_abVisibleInvariant_of_nontrivial
      (Z := Z) (k := k) h.invariant

theorem SharedABSparseThresholdTargetData.not_surjective_predict_of_nontrivial
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : SharedABSparseThresholdTargetData (Z := Z) (r := r) (k := k) (Index := Index) G) :
    ¬ Function.Surjective G.predict := by
  exact
    not_surjective_predict_of_abVisibleInvariant_of_nontrivial
      (Z := Z) (k := k) h.invariant

theorem SharedABDecisionListTargetData.not_surjective_predict_of_nontrivial
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : SharedABDecisionListTargetData (Z := Z) (r := r) (k := k) (Index := Index) G) :
    ¬ Function.Surjective G.predict := by
  exact
    not_surjective_predict_of_abVisibleInvariant_of_nontrivial
      (Z := Z) (k := k) h.invariant

theorem CanonicalABDecisionListCandidateData.not_surjective_predict_of_nontrivial
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : CanonicalABDecisionListCandidateData (Z := Z) (k := k) (Index := Index) G) :
    ¬ Function.Surjective G.predict := by
  exact
    not_surjective_predict_of_abVisibleInvariant_of_nontrivial
      (Z := Z) (k := k) h.invariant

omit [Inhabited Z] in
theorem canonicalABDecisionList_not_surjective_of_nontrivial
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G) :
    ¬ Function.Surjective G.predict := by
  exact
    not_surjective_predict_of_abVisibleInvariant_of_nontrivial
      (Z := Z) (k := k) hinv

omit [Inhabited Z] in
theorem canonicalABCodeFamily_not_surjective_of_nontrivial
    (codes : Index → SharedAffineDecisionListCode (k + k)) :
    ¬ Function.Surjective
        (canonicalABCodeFamily (Z := Z) (k := k) codes).predict := by
  exact
    not_surjective_predict_of_abVisibleInvariant_of_nontrivial
      (Z := Z) (k := k)
      (canonicalABCodeFamily_invariant (Z := Z) (k := k) codes)

end

section BoolTargetWrappers

variable {k : ℕ} {Index : Type*}

theorem CanonicalABDecisionListCandidateData.not_exists_predict_eq_boolZProjectionRule
    {G : ExactVisibleSwitchedFamily Bool k Index}
    (h : CanonicalABDecisionListCandidateData (Z := Bool) (k := k) (Index := Index) G) :
    ¬ ∃ i, G.predict i = boolZProjectionRule (k := k) := by
  exact not_exists_predict_eq_boolZProjectionRule_of_abVisibleInvariant
    (k := k) h.invariant

theorem canonicalABCodeFamily_not_exists_predict_eq_boolZProjectionRule
    (codes : Index → SharedAffineDecisionListCode (k + k)) :
    ¬ ∃ i,
        (canonicalABCodeFamily (Z := Bool) (k := k) codes).predict i =
          boolZProjectionRule (k := k) := by
  exact not_exists_predict_eq_boolZProjectionRule_of_abVisibleInvariant
    (k := k)
    (canonicalABCodeFamily_invariant (Z := Bool) (k := k) codes)

theorem CanonicalABDecisionListCandidateData.exists_pos_mass_disagreement_boolZProjectionRule
    {G : ExactVisibleSwitchedFamily Bool k Index}
    (h : CanonicalABDecisionListCandidateData (Z := Bool) (k := k) (Index := Index) G)
    {μ : PMF (ExactVisiblePostSwitchSurface Bool k)}
    (i : Index)
    (hfalse : μ ⟨false, default, default⟩ ≠ 0)
    (htrue : μ ⟨true, default, default⟩ ≠ 0) :
    ∃ x, μ x ≠ 0 ∧ G.predict i x ≠ boolZProjectionRule (k := k) x := by
  exact
    exists_pos_mass_disagreement_of_abVisibleInvariant_predict_boolZProjectionRule
      (k := k) h.invariant (μ := μ) i hfalse htrue

theorem canonicalABCodeFamily_exists_pos_mass_disagreement_boolZProjectionRule
    (codes : Index → SharedAffineDecisionListCode (k + k))
    {μ : PMF (ExactVisiblePostSwitchSurface Bool k)}
    (i : Index)
    (hfalse : μ ⟨false, default, default⟩ ≠ 0)
    (htrue : μ ⟨true, default, default⟩ ≠ 0) :
    ∃ x, μ x ≠ 0 ∧
      (canonicalABCodeFamily (Z := Bool) (k := k) codes).predict i x ≠
        boolZProjectionRule (k := k) x := by
  exact
    exists_pos_mass_disagreement_of_abVisibleInvariant_predict_boolZProjectionRule
      (k := k)
      (canonicalABCodeFamily_invariant (Z := Bool) (k := k) codes)
      (μ := μ) i hfalse htrue

theorem CanonicalABDecisionListCandidateData.agreementMass_lt_one_boolZProjectionRule
    {G : ExactVisibleSwitchedFamily Bool k Index}
    (h : CanonicalABDecisionListCandidateData (Z := Bool) (k := k) (Index := Index) G)
    {μ : PMF (ExactVisiblePostSwitchSurface Bool k)}
    (i : Index)
    (hfalse : μ ⟨false, default, default⟩ ≠ 0)
    (htrue : μ ⟨true, default, default⟩ ≠ 0) :
    agreementMass μ (boolZProjectionRule (k := k)) (G.predict i) < 1 := by
  exact
    agreementMass_lt_one_of_abVisibleInvariant_predict_boolZProjectionRule
      (k := k) h.invariant (μ := μ) i hfalse htrue

theorem canonicalABCodeFamily_agreementMass_lt_one_boolZProjectionRule
    (codes : Index → SharedAffineDecisionListCode (k + k))
    {μ : PMF (ExactVisiblePostSwitchSurface Bool k)}
    (i : Index)
    (hfalse : μ ⟨false, default, default⟩ ≠ 0)
    (htrue : μ ⟨true, default, default⟩ ≠ 0) :
    agreementMass μ (boolZProjectionRule (k := k))
      ((canonicalABCodeFamily (Z := Bool) (k := k) codes).predict i) < 1 := by
  exact
    agreementMass_lt_one_of_abVisibleInvariant_predict_boolZProjectionRule
      (k := k)
      (canonicalABCodeFamily_invariant (Z := Bool) (k := k) codes)
      (μ := μ) i hfalse htrue

theorem CanonicalABDecisionListCandidateData.not_exists_agreementMass_eq_one_boolZProjectionRule
    {G : ExactVisibleSwitchedFamily Bool k Index}
    (h : CanonicalABDecisionListCandidateData (Z := Bool) (k := k) (Index := Index) G)
    {μ : PMF (ExactVisiblePostSwitchSurface Bool k)}
    (hfalse : μ ⟨false, default, default⟩ ≠ 0)
    (htrue : μ ⟨true, default, default⟩ ≠ 0) :
    ¬ ∃ i, agreementMass μ (boolZProjectionRule (k := k)) (G.predict i) = 1 := by
  exact
    not_exists_agreementMass_eq_one_boolZProjectionRule_of_abVisibleInvariant
      (k := k) h.invariant (μ := μ) hfalse htrue

theorem canonicalABCodeFamily_not_exists_agreementMass_eq_one_boolZProjectionRule
    (codes : Index → SharedAffineDecisionListCode (k + k))
    {μ : PMF (ExactVisiblePostSwitchSurface Bool k)}
    (hfalse : μ ⟨false, default, default⟩ ≠ 0)
    (htrue : μ ⟨true, default, default⟩ ≠ 0) :
    ¬ ∃ i, agreementMass μ (boolZProjectionRule (k := k))
      ((canonicalABCodeFamily (Z := Bool) (k := k) codes).predict i) = 1 := by
  exact
    not_exists_agreementMass_eq_one_boolZProjectionRule_of_abVisibleInvariant
      (k := k)
      (canonicalABCodeFamily_invariant (Z := Bool) (k := k) codes)
      (μ := μ) hfalse htrue

end BoolTargetWrappers

section

variable [Inhabited Z] [Fintype Z] [Nontrivial Z]

theorem SharedABAffineFeatureRecoveryData.not_surjective_predict_of_nontrivial
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedABAffineFeatureRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_nontrivial

theorem SharedABSparseThresholdRecoveryData.not_surjective_predict_of_nontrivial
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedABSparseThresholdRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_nontrivial

theorem SharedABDecisionListRecoveryData.not_surjective_predict_of_nontrivial
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {features : Fin r → AffineColumnCode (k + k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedABDecisionListRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index)
        μ features G q) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_nontrivial

theorem SharedExactABAffineFeatureERMRecoveryData.not_surjective_predict_of_nontrivial
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactABAffineFeatureERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_nontrivial

theorem SharedExactABSparseThresholdERMRecoveryData.not_surjective_predict_of_nontrivial
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactABSparseThresholdERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_nontrivial

theorem SharedExactABERMRecoveryData.not_surjective_predict_of_nontrivial
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactABERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_nontrivial

end

end RouteWrappers

end Mettapedia.Computability.PNP

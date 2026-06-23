import Mettapedia.Computability.PNP.WeightedFeatureFiberMarginBalanced

/-!
# Weighted feature-fiber margin: majority sum forms

Single-sum correct and incorrect mass formulas for classifiers over visible fibers.
-/

namespace Mettapedia.Computability.PNP

section

variable {α U : Type*} [Fintype α] [DecidableEq U] [Fintype U]

/-- The correct mass can be written as a single sum over visible fibers, where
each fiber contributes its `true` mass or `false` mass according to the
classifier's prediction on that fiber. -/
theorem weightedCorrectMass_eq_sum_if_weightedFeatureFiberMass
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool) :
    weightedCorrectMass u y w h =
      ∑ v : U,
        if h v = true
          then weightedFeatureFiberTrueMass u y w v
          else weightedFeatureFiberFalseMass u y w v := by
  classical
  rw [weightedCorrectMass_eq_sum_predictedTrue_trueMass_add_sum_predictedFalse_falseMass]
  have hsum :
      ∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = true),
          (if h v = true
            then weightedFeatureFiberTrueMass u y w v
            else weightedFeatureFiberFalseMass u y w v) +
        ∑ v ∈ (Finset.univ : Finset U).filter (fun v => ¬ h v = true),
          (if h v = true
            then weightedFeatureFiberTrueMass u y w v
            else weightedFeatureFiberFalseMass u y w v) =
        ∑ v : U,
          if h v = true
            then weightedFeatureFiberTrueMass u y w v
            else weightedFeatureFiberFalseMass u y w v := by
    simpa using
      (Finset.sum_filter_add_sum_filter_not
        (s := (Finset.univ : Finset U))
        (p := fun v => h v = true)
        (f := fun v =>
          if h v = true
            then weightedFeatureFiberTrueMass u y w v
            else weightedFeatureFiberFalseMass u y w v))
  calc
    ∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = true),
        weightedFeatureFiberTrueMass u y w v +
      ∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = false),
        weightedFeatureFiberFalseMass u y w v
        =
      ∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = true),
          (if h v = true
            then weightedFeatureFiberTrueMass u y w v
            else weightedFeatureFiberFalseMass u y w v) +
        ∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = false),
          (if h v = true
            then weightedFeatureFiberTrueMass u y w v
            else weightedFeatureFiberFalseMass u y w v) := by
            congr 1
            · refine Finset.sum_congr rfl ?_
              intro v hv
              have hvtrue : h v = true := (Finset.mem_filter.mp hv).2
              simp [hvtrue]
            · refine Finset.sum_congr rfl ?_
              intro v hv
              have hvfalse : h v = false := (Finset.mem_filter.mp hv).2
              simp [hvfalse]
    _ = ∑ v : U,
          if h v = true
            then weightedFeatureFiberTrueMass u y w v
            else weightedFeatureFiberFalseMass u y w v := by
          simpa using hsum

/-- The incorrect mass has the analogous one-sum form over visible fibers. -/
theorem weightedIncorrectMass_eq_sum_if_weightedFeatureFiberMass
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool) :
    weightedIncorrectMass u y w h =
      ∑ v : U,
        if h v = true
          then weightedFeatureFiberFalseMass u y w v
          else weightedFeatureFiberTrueMass u y w v := by
  classical
  rw [weightedIncorrectMass_eq_sum_predictedTrue_falseMass_add_sum_predictedFalse_trueMass]
  have hsum :
      ∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = true),
          (if h v = true
            then weightedFeatureFiberFalseMass u y w v
            else weightedFeatureFiberTrueMass u y w v) +
        ∑ v ∈ (Finset.univ : Finset U).filter (fun v => ¬ h v = true),
          (if h v = true
            then weightedFeatureFiberFalseMass u y w v
            else weightedFeatureFiberTrueMass u y w v) =
        ∑ v : U,
          if h v = true
            then weightedFeatureFiberFalseMass u y w v
            else weightedFeatureFiberTrueMass u y w v := by
    simpa using
      (Finset.sum_filter_add_sum_filter_not
        (s := (Finset.univ : Finset U))
        (p := fun v => h v = true)
        (f := fun v =>
          if h v = true
            then weightedFeatureFiberFalseMass u y w v
            else weightedFeatureFiberTrueMass u y w v))
  calc
    ∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = true),
        weightedFeatureFiberFalseMass u y w v +
      ∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = false),
        weightedFeatureFiberTrueMass u y w v
        =
      ∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = true),
          (if h v = true
            then weightedFeatureFiberFalseMass u y w v
            else weightedFeatureFiberTrueMass u y w v) +
        ∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = false),
          (if h v = true
            then weightedFeatureFiberFalseMass u y w v
            else weightedFeatureFiberTrueMass u y w v) := by
            congr 1
            · refine Finset.sum_congr rfl ?_
              intro v hv
              have hvtrue : h v = true := (Finset.mem_filter.mp hv).2
              simp [hvtrue]
            · refine Finset.sum_congr rfl ?_
              intro v hv
              have hvfalse : h v = false := (Finset.mem_filter.mp hv).2
              simp [hvfalse]
    _ = ∑ v : U,
          if h v = true
            then weightedFeatureFiberFalseMass u y w v
            else weightedFeatureFiberTrueMass u y w v := by
          simpa using hsum

end

end Mettapedia.Computability.PNP

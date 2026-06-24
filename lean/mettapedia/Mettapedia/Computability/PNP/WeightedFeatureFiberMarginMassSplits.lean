import Mettapedia.Computability.PNP.WeightedFeatureFiberMarginCore

/-!
# Weighted feature-fiber margin: mass splits

Correct and incorrect weighted mass decompositions over predicted true and false visible fibers.
-/

namespace Mettapedia.Computability.PNP

section

variable {α U : Type*} [Fintype α] [DecidableEq U] [Fintype U]

/-- The correct mass splits into the `true`-labeled mass on fibers predicted
`true` and the `false`-labeled mass on fibers predicted `false`. -/
theorem weightedCorrectMass_eq_sum_predictedTrue_trueMass_add_sum_predictedFalse_falseMass
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool) :
    weightedCorrectMass u y w h =
      (∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = true),
        weightedFeatureFiberTrueMass u y w v) +
      ∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = false),
        weightedFeatureFiberFalseMass u y w v := by
  classical
  have htrue :
      ∑ x ∈ (Finset.univ : Finset α) with y x = true ∧ h (u x) = true, w x =
        ∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = true),
          weightedFeatureFiberTrueMass u y w v := by
    calc
      ∑ x ∈ (Finset.univ : Finset α) with y x = true ∧ h (u x) = true, w x
          =
        ∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = true),
          ∑ x ∈ ((Finset.univ : Finset α).filter (fun x => y x = true)) with u x = v, w x := by
            simpa [Finset.filter_filter, and_left_comm, and_assoc] using
              (Finset.sum_fiberwise_eq_sum_filter
                ((Finset.univ : Finset α).filter (fun x => y x = true))
                ((Finset.univ : Finset U).filter (fun v => h v = true))
                u w).symm
      _ =
        ∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = true),
          weightedFeatureFiberTrueMass u y w v := by
            refine Finset.sum_congr rfl ?_
            intro v hv
            simpa [Finset.filter_filter, and_comm, and_left_comm, and_assoc] using
              (weightedFeatureFiberTrueMass_eq_sum_filter u y w v).symm
  have hfalse :
      ∑ x ∈ (Finset.univ : Finset α) with y x = false ∧ h (u x) = false, w x =
        ∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = false),
          weightedFeatureFiberFalseMass u y w v := by
    calc
      ∑ x ∈ (Finset.univ : Finset α) with y x = false ∧ h (u x) = false, w x
          =
        ∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = false),
          ∑ x ∈ ((Finset.univ : Finset α).filter (fun x => y x = false)) with u x = v, w x := by
            simpa [Finset.filter_filter, and_left_comm, and_assoc] using
              (Finset.sum_fiberwise_eq_sum_filter
                ((Finset.univ : Finset α).filter (fun x => y x = false))
                ((Finset.univ : Finset U).filter (fun v => h v = false))
                u w).symm
      _ =
        ∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = false),
          weightedFeatureFiberFalseMass u y w v := by
            refine Finset.sum_congr rfl ?_
            intro v hv
            simpa [Finset.filter_filter, and_comm, and_left_comm, and_assoc] using
              (weightedFeatureFiberFalseMass_eq_sum_filter u y w v).symm
  have hfilter :
      weightedCorrectMass u y w h =
        ∑ x ∈ (Finset.univ : Finset α) with h (u x) = y x, w x := by
    unfold weightedCorrectMass Correct
    change ∑ x : {x : α // h (u x) = y x}, w x.1 =
      ∑ x ∈ (Finset.univ : Finset α) with h (u x) = y x, w x
    rw [← Finset.subtype_univ (fun x : α => h (u x) = y x)]
    exact
      (Finset.sum_subtype_eq_sum_filter
        (s := (Finset.univ : Finset α))
        (p := fun x => h (u x) = y x)
        (f := w))
  have hsplit :
      ∑ x ∈ (Finset.univ : Finset α) with h (u x) = y x, w x =
        (∑ x ∈ (Finset.univ : Finset α) with y x = true ∧ h (u x) = true, w x) +
        ∑ x ∈ (Finset.univ : Finset α) with y x = false ∧ h (u x) = false, w x := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset α).filter (fun x => h (u x) = y x))
      (p := fun x => y x = true)]
    have h1 :
        ∑ x ∈ ((Finset.univ : Finset α).filter (fun x => h (u x) = y x)) with y x = true, w x =
          ∑ x ∈ (Finset.univ : Finset α) with y x = true ∧ h (u x) = true, w x := by
      have hpred :
          (fun x : α => h (u x) = y x ∧ y x = true) =
            (fun x : α => y x = true ∧ h (u x) = true) := by
        funext x
        by_cases hy : y x <;> simp [hy]
      simp [Finset.filter_filter, hpred]
    have h2 :
        ∑ x ∈ ((Finset.univ : Finset α).filter (fun x => h (u x) = y x)) with ¬ y x = true, w x =
          ∑ x ∈ (Finset.univ : Finset α) with y x = false ∧ h (u x) = false, w x := by
      rw [Finset.filter_filter]
      have hpred :
          (fun x : α => h (u x) = y x ∧ y x = false) =
            (fun x : α => y x = false ∧ h (u x) = false) := by
        funext x
        by_cases hy : y x <;> simp [hy]
      simp [hpred]
    rw [h1, h2]
  rw [hfilter, hsplit, htrue, hfalse]

/-- The incorrect mass splits into the `false`-labeled mass on fibers predicted
`true` and the `true`-labeled mass on fibers predicted `false`. -/
theorem weightedIncorrectMass_eq_sum_predictedTrue_falseMass_add_sum_predictedFalse_trueMass
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool) :
    weightedIncorrectMass u y w h =
      (∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = true),
        weightedFeatureFiberFalseMass u y w v) +
      ∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = false),
        weightedFeatureFiberTrueMass u y w v := by
  classical
  have htrue :
      ∑ x ∈ (Finset.univ : Finset α) with y x = false ∧ h (u x) = true, w x =
        ∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = true),
          weightedFeatureFiberFalseMass u y w v := by
    calc
      ∑ x ∈ (Finset.univ : Finset α) with y x = false ∧ h (u x) = true, w x
          =
        ∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = true),
          ∑ x ∈ ((Finset.univ : Finset α).filter (fun x => y x = false)) with u x = v, w x := by
            simpa [Finset.filter_filter, and_left_comm, and_assoc] using
              (Finset.sum_fiberwise_eq_sum_filter
                ((Finset.univ : Finset α).filter (fun x => y x = false))
                ((Finset.univ : Finset U).filter (fun v => h v = true))
                u w).symm
      _ =
        ∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = true),
          weightedFeatureFiberFalseMass u y w v := by
            refine Finset.sum_congr rfl ?_
            intro v hv
            simpa [Finset.filter_filter, and_comm, and_left_comm, and_assoc] using
              (weightedFeatureFiberFalseMass_eq_sum_filter u y w v).symm
  have hfalse :
      ∑ x ∈ (Finset.univ : Finset α) with y x = true ∧ h (u x) = false, w x =
        ∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = false),
          weightedFeatureFiberTrueMass u y w v := by
    calc
      ∑ x ∈ (Finset.univ : Finset α) with y x = true ∧ h (u x) = false, w x
          =
        ∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = false),
          ∑ x ∈ ((Finset.univ : Finset α).filter (fun x => y x = true)) with u x = v, w x := by
            simpa [Finset.filter_filter, and_left_comm, and_assoc] using
              (Finset.sum_fiberwise_eq_sum_filter
                ((Finset.univ : Finset α).filter (fun x => y x = true))
                ((Finset.univ : Finset U).filter (fun v => h v = false))
                u w).symm
      _ =
        ∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = false),
          weightedFeatureFiberTrueMass u y w v := by
            refine Finset.sum_congr rfl ?_
            intro v hv
            simpa [Finset.filter_filter, and_comm, and_left_comm, and_assoc] using
              (weightedFeatureFiberTrueMass_eq_sum_filter u y w v).symm
  have hfilter :
      weightedIncorrectMass u y w h =
        ∑ x ∈ (Finset.univ : Finset α) with ¬ h (u x) = y x, w x := by
    unfold weightedIncorrectMass Incorrect
    change ∑ x : {x : α // ¬ h (u x) = y x}, w x.1 =
      ∑ x ∈ (Finset.univ : Finset α) with ¬ h (u x) = y x, w x
    rw [← Finset.subtype_univ (fun x : α => ¬ h (u x) = y x)]
    exact
      (Finset.sum_subtype_eq_sum_filter
        (s := (Finset.univ : Finset α))
        (p := fun x => ¬ h (u x) = y x)
        (f := w))
  have hsplit :
      ∑ x ∈ (Finset.univ : Finset α) with ¬ h (u x) = y x, w x =
        (∑ x ∈ (Finset.univ : Finset α) with y x = false ∧ h (u x) = true, w x) +
        ∑ x ∈ (Finset.univ : Finset α) with y x = true ∧ h (u x) = false, w x := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset α).filter (fun x => ¬ h (u x) = y x))
      (p := fun x => y x = false)]
    have h1 :
        ∑ x ∈ ((Finset.univ : Finset α).filter (fun x => ¬ h (u x) = y x)) with y x = false, w x =
          ∑ x ∈ (Finset.univ : Finset α) with y x = false ∧ h (u x) = true, w x := by
      have hpred :
          (fun x : α => ¬ h (u x) = y x ∧ y x = false) =
            (fun x : α => y x = false ∧ h (u x) = true) := by
        funext x
        by_cases hy : y x <;> simp [hy]
      simp [Finset.filter_filter, hpred]
    have h2 :
        ∑ x ∈ ((Finset.univ : Finset α).filter (fun x => ¬ h (u x) = y x)) with ¬ y x = false, w x =
          ∑ x ∈ (Finset.univ : Finset α) with y x = true ∧ h (u x) = false, w x := by
      rw [Finset.filter_filter]
      have hpred :
          (fun x : α => ¬ h (u x) = y x ∧ y x = true) =
            (fun x : α => y x = true ∧ h (u x) = false) := by
        funext x
        by_cases hy : y x <;> simp [hy]
      simp [hpred]
    rw [h1, h2]
  rw [hfilter, hsplit, htrue, hfalse]

end

end Mettapedia.Computability.PNP

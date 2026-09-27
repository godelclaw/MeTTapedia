import Mettapedia.GraphTheory.FourColor.GoertzelV24CurvatureScope
import Mettapedia.GraphTheory.FourColor.GoertzelV24FaceOrbitIncidence

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FaceOrbitPartitionBridge

open GoertzelV24CurvatureScope
open GoertzelV24FaceOrbitIncidence

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

section PermutationOrbits

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Classify a dart orbit as either a nontrivial cycle factor or a fixed
point. This is the decomposition underlying `Equiv.Perm.partition`. -/
def permOrbitClassify (sigma : Equiv.Perm D) (dart : D) :
    sigma.cycleFactorsFinset ⊕ Function.fixedPoints sigma :=
  if hfixed : sigma dart = dart then
    Sum.inr ⟨dart, hfixed⟩
  else
    Sum.inl ⟨sigma.cycleOf dart,
      Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr
        (Equiv.Perm.mem_support.mpr hfixed)⟩

theorem permOrbitClassify_eq_of_sameCycle (sigma : Equiv.Perm D)
    {left right : D} (hsame : sigma.SameCycle left right) :
    permOrbitClassify sigma left = permOrbitClassify sigma right := by
  by_cases hleft : sigma left = left
  · have hright : sigma right = right := hsame.apply_eq_self_iff.mp hleft
    simp only [permOrbitClassify, dif_pos hleft, dif_pos hright]
    congr 2
    exact hsame.eq_of_left hleft
  · have hright : sigma right ≠ right :=
      fun h => hleft (hsame.apply_eq_self_iff.mpr h)
    simp only [permOrbitClassify, dif_neg hleft, dif_neg hright]
    congr 2
    exact hsame.cycleOf_eq

/-- The quotient by a permutation's cycle relation is canonically the sum
of its nontrivial cycle factors and its fixed points. -/
noncomputable def permOrbitEquivCycleFactorsSumFixedPoints
    (sigma : Equiv.Perm D) :
    Quotient (Equiv.Perm.SameCycle.setoid sigma) ≃
      sigma.cycleFactorsFinset ⊕ Function.fixedPoints sigma :=
  Equiv.ofBijective
    (Quotient.lift (permOrbitClassify sigma)
      (fun _ _ => permOrbitClassify_eq_of_sameCycle sigma))
    ⟨by
      intro left right heq
      induction left, right using Quotient.inductionOn₂ with
      | _ left right =>
          apply Quotient.sound
          simp only [Quotient.lift_mk] at heq
          change permOrbitClassify sigma left =
            permOrbitClassify sigma right at heq
          by_cases hleft : sigma left = left
          · by_cases hright : sigma right = right
            · simp only [permOrbitClassify, dif_pos hleft,
                dif_pos hright] at heq
              exact (congrArg Subtype.val (Sum.inr.inj heq)).sameCycle sigma
            · simp [permOrbitClassify, hleft, hright] at heq
          · by_cases hright : sigma right = right
            · simp [permOrbitClassify, hleft, hright] at heq
            · apply (Equiv.Perm.sameCycle_iff_cycleOf_eq_of_mem_support
                  (Equiv.Perm.mem_support.mpr hleft)
                  (Equiv.Perm.mem_support.mpr hright)).mpr
              simp only [permOrbitClassify, dif_neg hleft,
                dif_neg hright] at heq
              exact congrArg Subtype.val (Sum.inl.inj heq),
    by
      intro target
      rcases target with factor | fixed
      · obtain ⟨dart, hdart⟩ :=
          (Equiv.Perm.mem_cycleFactorsFinset_iff.mp factor.2).1.nonempty_support
        refine ⟨Quotient.mk _ dart, ?_⟩
        have hdartSigma : dart ∈ sigma.support :=
          Equiv.Perm.mem_cycleFactorsFinset_support_le factor.2 hdart
        simp only [Quotient.lift_mk]
        unfold permOrbitClassify
        rw [dif_neg (Equiv.Perm.mem_support.mp hdartSigma)]
        congr 2
        exact (Equiv.Perm.eq_cycleOf_of_mem_cycleFactorsFinset_iff
          sigma factor factor.2 dart).mpr hdart |>.symm
      · refine ⟨Quotient.mk _ fixed.1, ?_⟩
        simp only [Quotient.lift_mk]
        unfold permOrbitClassify
        rw [dif_pos (Function.mem_fixedPoints_iff.mp fixed.2)]⟩

noncomputable local instance permOrbitFintype (sigma : Equiv.Perm D) :
    Fintype (Quotient (Equiv.Perm.SameCycle.setoid sigma)) :=
  Fintype.ofFinite _

/-- Counting cycle-relation classes agrees with the number of parts in the
permutation partition, including singleton fixed-point cycles. -/
theorem card_permOrbit_eq_card_partition_parts (sigma : Equiv.Perm D) :
    Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid sigma)) =
      sigma.partition.parts.card := by
  classical
  have hfixed : Fintype.card (Function.fixedPoints sigma) =
      Fintype.card D - sigma.support.card := by
    rw [sigma.card_fixedPoints, sigma.sum_cycleType]
  calc
    Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid sigma)) =
        Fintype.card
          (sigma.cycleFactorsFinset ⊕ Function.fixedPoints sigma) :=
      Fintype.card_congr (permOrbitEquivCycleFactorsSumFixedPoints sigma)
    _ = sigma.cycleFactorsFinset.card +
        Fintype.card (Function.fixedPoints sigma) := by
      rw [Fintype.card_sum, Fintype.card_coe]
    _ = sigma.cycleType.card +
        (Fintype.card D - sigma.support.card) := by
      rw [hfixed, Equiv.Perm.cycleType_def, Multiset.card_map]
      rfl
    _ = sigma.partition.parts.card := by
      rw [Equiv.Perm.parts_partition, Multiset.card_add,
        Multiset.card_replicate]

end PermutationOrbits

/-- The quotient-face count is exactly the all-cycle count already used by
the curvature API. -/
theorem card_orbitFace_eq_faceCycleLengths_card (RS : RotationSystem V E) :
    Fintype.card (OrbitFace RS) = (faceCycleLengths RS).card := by
  exact card_permOrbit_eq_card_partition_parts RS.phi

end GoertzelV24FaceOrbitPartitionBridge

end Mettapedia.GraphTheory.FourColor

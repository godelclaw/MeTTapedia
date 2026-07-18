import Mettapedia.GraphTheory.FourColor.GoertzelV24ThreeEdgeCutCap
import Mettapedia.GraphTheory.FourColor.GoertzelV24ComplementaryRegionBoundaryOrder
import Mathlib.GroupTheory.Perm.Cycle.Type

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ThreeEdgeCutCapOrder

open GoertzelV24ComplementaryRegionBoundaryOrder
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RotationCutDartDecomposition

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Every fixed-point-free permutation of three points is a relabeling of
the standard positive three-cycle. -/
theorem exists_reindex_finRotate_three
    (cycle : Equiv.Perm (Fin 3))
    (hfree : ∀ point, cycle point ≠ point) :
    ∃ reindex : Equiv.Perm (Fin 3),
      reindex.permCongr (finRotate 3) = cycle := by
  have hsupport : cycle.support = Finset.univ := by
    ext point
    simp [hfree point]
  have hcycle : cycle.IsCycle := by
    exact (card_support_eq_three_iff.mp (by
      rw [hsupport]
      simp)).isCycle
  have hrotate : (finRotate 3).IsCycle :=
    isCycle_finRotate_of_le (by omega)
  have hsupportCard : (finRotate 3).support.card = cycle.support.card := by
    rw [hsupport, support_finRotate_of_le (by omega)]
  rcases (_root_.isConj_iff.mp
      (hrotate.isConj hcycle hsupportCard)) with ⟨reindex, hconj⟩
  refine ⟨reindex, ?_⟩
  apply Equiv.ext
  intro point
  have hpoint := DFunLike.congr_fun hconj point
  simpa [Equiv.permCongr_apply, Equiv.Perm.mul_apply] using hpoint

end

end GoertzelV24ThreeEdgeCutCapOrder

open GoertzelV24ThreeEdgeCutCapOrder
open GoertzelV24ComplementaryRegionBoundaryOrder
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RotationCutDartDecomposition

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

namespace RotationSystem

namespace ThreeEdgeCutSideData

noncomputable section

variable {RS : RotationSystem V E}
  (data : Mettapedia.GraphTheory.FourColor.RotationSystem.ThreeEdgeCutSideData RS)

/-- Relabel the ordered cut positions without changing its edge support. -/
def reindex (index : Equiv.Perm (Fin 3)) :
    Mettapedia.GraphTheory.FourColor.RotationSystem.ThreeEdgeCutSideData RS where
  side := data.side
  crossing := data.crossing ∘ index
  crossing_injective := data.crossing_injective.comp index.injective
  boundary_eq := by
    rw [data.boundary_eq]
    ext edge
    simp only [orderedCut, Finset.mem_image, Finset.mem_univ, true_and,
      Function.comp_apply]
    constructor
    · rintro ⟨step, rfl⟩
      exact ⟨index.symm step, by simp⟩
    · rintro ⟨step, rfl⟩
      exact ⟨index step, rfl⟩
  outer_mem := data.outer_mem

@[simp]
theorem reindex_side (index : Equiv.Perm (Fin 3)) :
    (data.reindex index).side = data.side :=
  rfl

@[simp]
theorem reindex_crossing (index : Equiv.Perm (Fin 3)) (step : Fin 3) :
    (data.reindex index).crossing step = data.crossing (index step) :=
  rfl

@[simp]
theorem reindex_keep (index : Equiv.Perm (Fin 3)) :
    (data.reindex index).keep = data.keep :=
  rfl

/-- Reindexing the cut transports the canonical boundary-dart enumeration
by the same permutation. -/
theorem crossingBoundaryDartEquiv_reindex
    (index : Equiv.Perm (Fin 3)) :
    (data.reindex index).crossingBoundaryDartEquiv =
      index.trans data.crossingBoundaryDartEquiv := by
  apply Equiv.ext
  intro step
  apply boundaryDart_eq_of_edgeOf_eq RS (data.reindex index).keep
  rw [(data.reindex index).crossingBoundaryDartEquiv_edgeOf]
  change data.crossing (index step) =
    RS.edgeOf (data.crossingBoundaryDartEquiv (index step)).1.1
  rw [data.crossingBoundaryDartEquiv_edgeOf]

/-- The cyclic matching on retained boundary darts induced by rotation at
the cap vertex. -/
def capBoundaryCycle : Equiv.Perm (BoundaryDart RS data.keep) :=
  data.crossingBoundaryDartEquiv.permCongr (finRotate 3)

/-- A two-sided ambient face cannot return a retained boundary dart to
itself through the retained side. -/
theorem retainedRegionBoundarySuccessor_ne_of_twoSided
    (htwoSided : OrbitFacesTwoSided RS)
    (root : BoundaryDart RS data.keep) :
    retainedRegionBoundarySuccessor RS data.keep root ≠ root := by
  intro hfixed
  apply htwoSided root.1.1
  apply Quotient.sound
  have hface := retainedRegionBoundarySuccessor_sameAmbientFace_alpha
    RS data.keep root
  rw [hfixed] at hface
  exact hface.symm

/-- The inverse retained boundary order is fixed-point-free as well. -/
theorem retainedRegionBoundarySuccessor_inv_ne_of_twoSided
    (htwoSided : OrbitFacesTwoSided RS)
    (root : BoundaryDart RS data.keep) :
    (retainedRegionBoundarySuccessor RS data.keep)⁻¹ root ≠ root := by
  intro hfixed
  apply data.retainedRegionBoundarySuccessor_ne_of_twoSided htwoSided root
  have htransport := congrArg
    (retainedRegionBoundarySuccessor RS data.keep) hfixed
  simpa using htransport.symm

/-- A relabeling of the three cut edges whose cap-vertex rotation is the
inverse of the computed retained boundary order. -/
def planarReindex (htwoSided : OrbitFacesTwoSided RS) :
    Equiv.Perm (Fin 3) :=
  Classical.choose (exists_reindex_finRotate_three
    ((data.crossingBoundaryDartEquiv).symm.permCongr
      ((retainedRegionBoundarySuccessor RS data.keep)⁻¹))
    (by
      intro step hfixed
      apply data.retainedRegionBoundarySuccessor_inv_ne_of_twoSided
        htwoSided (data.crossingBoundaryDartEquiv step)
      have htransport := congrArg data.crossingBoundaryDartEquiv hfixed
      simpa [Equiv.permCongr_apply] using htransport))

/-- The side data with cap spokes in planar boundary order. -/
def planarOrdered (htwoSided : OrbitFacesTwoSided RS) :
    Mettapedia.GraphTheory.FourColor.RotationSystem.ThreeEdgeCutSideData RS :=
  data.reindex (data.planarReindex htwoSided)

/-- The planar reindexing makes cap rotation exactly cancel the retained
boundary successor. -/
theorem planarOrdered_capBoundaryCycle
    (htwoSided : OrbitFacesTwoSided RS) :
    (data.planarOrdered htwoSided).capBoundaryCycle =
      (retainedRegionBoundarySuccessor RS data.keep)⁻¹ := by
  let target : Equiv.Perm (Fin 3) :=
    (data.crossingBoundaryDartEquiv).symm.permCongr
      ((retainedRegionBoundarySuccessor RS data.keep)⁻¹)
  have hchosen :
      (data.planarReindex htwoSided).permCongr (finRotate 3) = target :=
    Classical.choose_spec (exists_reindex_finRotate_three target
      (by
        intro step hfixed
        apply data.retainedRegionBoundarySuccessor_inv_ne_of_twoSided
          htwoSided (data.crossingBoundaryDartEquiv step)
        have htransport := congrArg data.crossingBoundaryDartEquiv hfixed
        simpa [target, Equiv.permCongr_apply] using htransport))
  unfold capBoundaryCycle planarOrdered
  rw [data.crossingBoundaryDartEquiv_reindex]
  apply Equiv.ext
  intro boundary
  change data.crossingBoundaryDartEquiv
      ((data.planarReindex htwoSided)
        (finRotate 3
          ((data.planarReindex htwoSided).symm
            (data.crossingBoundaryDartEquiv.symm boundary)))) =
    (retainedRegionBoundarySuccessor RS data.keep)⁻¹ boundary
  have hpoint := DFunLike.congr_fun hchosen
    (data.crossingBoundaryDartEquiv.symm boundary)
  simpa [target, Equiv.permCongr_apply] using
    congrArg data.crossingBoundaryDartEquiv hpoint

end

end ThreeEdgeCutSideData

end RotationSystem

end Mettapedia.GraphTheory.FourColor

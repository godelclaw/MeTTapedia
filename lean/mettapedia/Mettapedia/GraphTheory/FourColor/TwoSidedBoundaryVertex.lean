import Mettapedia.GraphTheory.FourColor.TwoSidedBoundaryJoint
import Mettapedia.GraphTheory.FourColor.GoertzelV24CompositeSeamCubic
import Mettapedia.GraphTheory.FourColor.OpenTangleBoundaryView
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitCountCongr

/-! # Vertex geometry under boundary reindexing

Changing port coordinates retains the actual vertex fibres and rotations.
The tube seam-shift reduction consumes these two transport laws.
-/

namespace Mettapedia.GraphTheory.FourColor.TwoSidedBoundaryReindex

open GoertzelV24OpenTangleComposition SerialTangleSmallCutTransfer
open GoertzelV24CompositeSeamCubic
open TwoSidedOpenTangleData GoertzelV24OrbitCountCongr

noncomputable section
variable {V I L R L' R' : Type*}
  [Fintype I] [DecidableEq I] [Fintype L] [DecidableEq L]
  [Fintype R] [DecidableEq R] [Fintype L'] [DecidableEq L']
  [Fintype R'] [DecidableEq R'] [DecidableEq V]
  (T : TwoSidedOpenTangleData V I L R) (e : L' ⊕ R' ≃ L ⊕ R)

omit [DecidableEq I] [DecidableEq L] [DecidableEq R] [DecidableEq L'] [DecidableEq R'] in
theorem cubic_reindex (h : OpenIsCubic (asOpen T)) :
    OpenIsCubic (asOpen (reindex T e)) := by
  intro v
  let f := (darts e).subtypeEquiv (fun d => show
      d ∈ openDartsAt (asOpen (reindex T e)) v ↔
        darts e d ∈ openDartsAt (asOpen T) v by
    simp only [openDartsAt, Finset.mem_filter, Finset.mem_univ, true_and,
      asOpen_vertOf, vert_reindex])
  have hc := Fintype.card_congr f
  have hc' : (openDartsAt (asOpen (reindex T e)) v).card =
      (openDartsAt (asOpen T) v).card := by
    simpa only [Fintype.card_coe] using hc
  exact hc'.trans (h v)

omit [DecidableEq V] in
theorem rotationCyclic_reindex (h : OpenRotationCyclic (asOpen T)) :
    OpenRotationCyclic (asOpen (reindex T e)) := by
  intro d f hv
  have hh : T.vertOf (darts e d) = T.vertOf (darts e f) := by
    simpa only [asOpen_vertOf, vert_reindex] using hv
  have hs := h (darts e d) (darts e f) (by simpa only [asOpen_vertOf] using hh)
  change Equiv.Perm.SameCycle
    (((darts e).trans T.rho).trans (darts e).symm) d f
  simpa only [Equiv.symm_symm, Equiv.symm_apply_apply] using
    (sameCycle_conjEquiv_iff (darts e).symm T.rho (darts e d) (darts e f)).mpr hs

end
end Mettapedia.GraphTheory.FourColor.TwoSidedBoundaryReindex

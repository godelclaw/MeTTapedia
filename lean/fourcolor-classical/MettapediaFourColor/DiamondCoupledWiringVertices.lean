import MettapediaFourColor.DiamondCoupledWiringRotation
import Mettapedia.GraphTheory.FourColor.GoertzelV24CompositeSeamCubic

/-! # Cubic vertices and their rotations in the coupled wiring

Every exterior vertex retains all its darts and their cyclic order.
The six inserted darts form exactly two cubic vertices.
-/

namespace FourColor.DiamondCoupledWiring.Rotation
open Mettapedia.GraphTheory.FourColor
open GoertzelV24OpenTangleComposition GoertzelV24CompositeSeamCubic
open GoertzelV24FaceDualConnectedness

noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
  (O : OpenTangleData V I (Fin 8)) (hs : Separated O)

theorem cubic (ho : OpenIsCubic O) : (closed O hs).IsCubic := by
  rintro (v | j)
  · have hc : ((closed O hs).dartsAt (.inl v)).card = (openDartsAt O v).card := by
      refine (Finset.card_bij (fun d _ => Sum.inl d) ?_ ?_ ?_).symm
      · intro d hd
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, congrArg Sum.inl (Finset.mem_filter.mp hd).2⟩
      · intro d _ e _ he
        exact Sum.inl.inj he
      · rintro (d | k) hd
        · exact ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            Sum.inl.inj (Finset.mem_filter.mp hd).2⟩, rfl⟩
        · have hh := (Finset.mem_filter.mp hd).2
          cases hh
    exact hc.trans (ho v)
  · have hc : ((closed O hs).dartsAt (.inr j)).card =
        (Finset.univ.filter (fun k : Fin 6 => coreVertex k = j)).card := by
      refine (Finset.card_bij (fun d _ => Sum.inr d) ?_ ?_ ?_).symm
      · intro d hd
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, congrArg Sum.inr (Finset.mem_filter.mp hd).2⟩
      · intro d _ e _ he
        exact Sum.inr.inj he
      · rintro (d | k) hd
        · have hh := (Finset.mem_filter.mp hd).2
          cases hh
        · exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            Sum.inr.inj (Finset.mem_filter.mp hd).2⟩, rfl⟩
    rw [hc]
    fin_cases j <;> decide

theorem rotation_cyclic (ho : OpenRotationCyclic O) : VertexRotationCyclic (closed O hs) := by
  rintro (d | i) (e | j) he
  · exact sameCycle_sumCongr_inl O.rho coreRotation (ho d e (Sum.inl.inj he))
  · cases he
  · cases he
  · have hcore : ∀ i j, coreVertex i = coreVertex j → coreRotation.SameCycle i j := by decide
    exact sameCycle_sumCongr_inr O.rho coreRotation (hcore i j (Sum.inr.inj he))

end
end FourColor.DiamondCoupledWiring.Rotation

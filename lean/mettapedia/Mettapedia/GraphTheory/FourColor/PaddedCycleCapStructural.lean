import Mettapedia.GraphTheory.FourColor.PaddedCycleCapGeometry
import Mettapedia.GraphTheory.FourColor.OpenTangleInternalReplacement

/-! # Internal connectivity and bridge-freedom of padded caps

The three concentric cycles have no single-edge cuts. At least two radial
edges join each consecutive pair, so a cut of size at most one is constant
on the entire literal cap.
-/

namespace Mettapedia.GraphTheory.FourColor.PaddedCycleCap

open GoertzelV24OpenTangleComposition GoertzelV24CompositeSeamMultigraph
open GoertzelV24BoundaryEssentialGluing Multigraph BoundarySmallCutProfile
open SmallCutConnectedBridgeless SmallCutReplacementCore OpenTangleCutDartSum

noncomputable section
attribute [local instance] Classical.propDecidable

variable (m : ℕ) [NeZero m] (hm : 2 ≤ m)

def vertexNext : Equiv.Perm (Vertex m) where
  toFun v := (if v.2 = 0 ∨ v.2 = 3 ∨ v.2 = 7 then v.1+1 else v.1,
    ![0,2,3,1,5,6,7,4] v.2)
  invFun v := (if v.2 = 0 ∨ v.2 = 1 ∨ v.2 = 4 then v.1-1 else v.1,
    ![0,3,1,2,7,4,5,6] v.2)
  left_inv := by rintro ⟨i,v⟩; fin_cases v <;> simp
  right_inv := by rintro ⟨i,v⟩; fin_cases v <;> simp

theorem cap_cutSize (s : Vertex m → Bool) :
    cutSize (sideMultigraph (openCap m hm)) s =
      ∑ i : Fin m, ∑ e : Fin 11,
        bit (s (vertexOf m (.inl (i,e,false)))) (s (vertexOf m (.inl (i,e,true)))) := by
  have h := twice_cutSize (openCap m hm) s
  conv at h =>
    rhs
    simp only [Interior, Fintype.sum_prod_type, Fintype.sum_bool,
      openCap, SerialTangleSmallCutTransfer.asOpen, tangle, alpha,
      Equiv.coe_fn_mk, flip, Bool.not_true, Bool.not_false]
  have he (i : Fin m) (e : Fin 11) :
      bit (s (vertexOf m (.inl (i,e,true)))) (s (vertexOf m (.inl (i,e,false)))) =
      bit (s (vertexOf m (.inl (i,e,false)))) (s (vertexOf m (.inl (i,e,true)))) :=
    bit_symm _ _
  simp only [he, Finset.sum_add_distrib] at h
  omega

def radialCut (s : Vertex m → Bool) : ℕ :=
  ∑ i : Fin m, (bit (s (i,0)) (s (i,1)) + bit (s (i,2)) (s (i,4)) +
    bit (s (i,3)) (s (i,6)))

theorem cap_cut_decomposition (s : Vertex m → Bool) :
    cutSize (sideMultigraph (openCap m hm)) s =
      cutSize (permutationGraph (vertexNext m)) s + radialCut m s := by
  rw [cap_cutSize]
  change (∑ i : Fin m, ∑ e : Fin 11,
    bit (s (vertexOf m (.inl (i,e,false)))) (s (vertexOf m (.inl (i,e,true))))) =
    (∑ v : Vertex m, bit (s v) (s (vertexNext m v))) + radialCut m s
  rw [Fintype.sum_prod_type]
  unfold radialCut
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp [Fin.sum_univ_succ, vertexOf, position, vertexNext]
  omega

private def cycleTag : Fin 8 → Fin 8 := ![0,1,1,1,4,4,4,4]

private theorem cycle_constant (s : Vertex m → Bool)
    (hs : cutSize (permutationGraph (vertexNext m)) s ≤ 1) :
    ∀ i v, s (i,v) = s (0,cycleTag v) := by
  have h := permutation_small_cut (vertexNext m) s hs
  have h0 (i : Fin m) : s (i,0) = s (i+1,0) := by simpa [vertexNext] using h (i,0)
  have h1 (i : Fin m) : s (i,1) = s (i,2) := by simpa [vertexNext] using h (i,1)
  have h2 (i : Fin m) : s (i,2) = s (i,3) := by simpa [vertexNext] using h (i,2)
  have h3 (i : Fin m) : s (i,3) = s (i+1,1) := by simpa [vertexNext] using h (i,3)
  have h4 (i : Fin m) : s (i,4) = s (i,5) := by simpa [vertexNext] using h (i,4)
  have h5 (i : Fin m) : s (i,5) = s (i,6) := by simpa [vertexNext] using h (i,5)
  have h6 (i : Fin m) : s (i,6) = s (i,7) := by simpa [vertexNext] using h (i,6)
  have h7 (i : Fin m) : s (i,7) = s (i+1,4) := by simpa [vertexNext] using h (i,7)
  have hu := CyclicColourAvoidance.constant_of_next (fun i => s (i,0)) (fun i => (h0 i).symm)
  have hv := CyclicColourAvoidance.constant_of_next (fun i => s (i,1))
    (fun i => ((h1 i).trans ((h2 i).trans (h3 i))).symm)
  have hw := CyclicColourAvoidance.constant_of_next (fun i => s (i,4))
    (fun i => ((h4 i).trans ((h5 i).trans ((h6 i).trans (h7 i)))).symm)
  intro i v
  fin_cases v
  · exact hu i
  · exact hv i
  · exact (h1 i).symm.trans (hv i)
  · exact ((h1 i).trans (h2 i)).symm.trans (hv i)
  · exact hw i
  · exact (h4 i).symm.trans (hw i)
  · exact ((h4 i).trans (h5 i)).symm.trans (hw i)
  · exact ((h4 i).trans ((h5 i).trans (h6 i))).symm.trans (hw i)

private theorem cap_constant (s : Vertex m → Bool)
    (hs : cutSize (sideMultigraph (openCap m hm)) s ≤ 1) :
    ∀ v, s v = s (0,0) := by
  rw [cap_cut_decomposition] at hs
  have hp : cutSize (permutationGraph (vertexNext m)) s ≤ 1 := by omega
  have hr : radialCut m s ≤ 1 := by omega
  have hc := cycle_constant m s hp
  have hrval : radialCut m s =
      m * (bit (s (0,0)) (s (0,1)) + 2 * bit (s (0,1)) (s (0,4))) := by
    unfold radialCut
    have he (i : Fin m) :
        bit (s (i,0)) (s (i,1)) + bit (s (i,2)) (s (i,4)) + bit (s (i,3)) (s (i,6)) =
        bit (s (0,0)) (s (0,1)) + 2 * bit (s (0,1)) (s (0,4)) := by
      rw [hc i 0, hc i 1, hc i 2, hc i 4, hc i 3, hc i 6]
      simp [cycleTag, two_mul, add_assoc]
    simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [hrval] at hr
  have hroots : s (0,0) = s (0,1) ∧ s (0,1) = s (0,4) := by
    cases hu : s (0,0) <;> cases hv : s (0,1) <;> cases hw : s (0,4) <;>
      simp [hu,hv,hw,bit] at hr ⊢ <;> omega
  rintro ⟨i,v⟩
  rw [hc]
  fin_cases v <;> dsimp [cycleTag] <;>
    first | rfl | exact hroots.1.symm | exact (hroots.1.trans hroots.2).symm

theorem cap_connected_bridgeless :
    (sideMultigraph (openCap m hm)).Connected ∧
      (sideMultigraph (openCap m hm)).Bridgeless := by
  apply (no_small_cut_iff _).mp
  rintro ⟨s, ⟨u,hu⟩, ⟨v,hv⟩, hs⟩
  have h := (cap_constant m hm s hs u).trans (cap_constant m hm s hs v).symm
  simp only [hu,hv,Bool.true_eq_false] at h

end
end Mettapedia.GraphTheory.FourColor.PaddedCycleCap

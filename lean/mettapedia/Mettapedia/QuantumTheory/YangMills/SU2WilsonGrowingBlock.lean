import Mettapedia.QuantumTheory.YangMills.SU2WilsonEffectiveInteraction

/-!
# A spatial response estimate inside blocks of growing size

The separator mesh is the whole torus side. Every unheld link lies in the
same cell, whose size grows with the volume. The separated boundary patches
therefore do not belong to distinct bounded-size cells. The strong-coupling
estimate still has a constant prefactor and decays with their separation.
-/
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Filter
open scoped Topology Classical
namespace Mettapedia.QuantumTheory.YangMills.SU2WilsonGrowingBlock
open SU2WilsonAssembly SU2WilsonBlockPilot SU2WilsonEffectiveInteraction
open StrongCouplingCrossing WilsonDyadicGeometry WilsonDyadicProjection
open WilsonPinnedIntegral WilsonBoundaryChanges WilsonSeparatedBoundaryResponse

abbrev side (N : ℕ) := volumeIndex N + 3
def boundary (N : ℕ) : Finset (AssemblyLink N) := retainedSet (side N)

/-- Original Wilson integral over precisely the unheld links of the growing block. -/
def logPartition (N : ℕ) (β : ℝ) (b : FullField N) : ℝ :=
  Real.log (∫ i : {l : AssemblyLink N // l ∉ boundary N} → SU2,
    fullDensity N β (fill (boundary N) b i))

theorem logPartition_eq_boundary (N : ℕ) (β : ℝ) (b : FullField N) :
    logPartition N β b = boundaryLogPartition (volume : Measure SU2)
      (SU2BoundaryResponse.model (volumeIndex N) univ)
      (SU2BoundaryResponse.model_continuous (volumeIndex N) univ) β (boundary N) b :=
  (boundaryLogPartition_eq_interior (volume : Measure SU2)
    (SU2BoundaryResponse.model (volumeIndex N) univ)
    (SU2BoundaryResponse.model_continuous (volumeIndex N) univ) β (boundary N) b).symm

def mixedChange (N : ℕ) (β : ℝ) (b a c : FullField N) : ℝ :=
  let S := SU2BoundaryResponse.firstPatch N
  let T := SU2BoundaryResponse.secondPatch N
  logPartition N β (replace T c (replace S a b)) + logPartition N β b -
    logPartition N β (replace S a b) - logPartition N β (replace T c b)

theorem mixedChange_eq_response (N : ℕ) (β : ℝ) (b a c : FullField N) :
    mixedChange N β b a c = SU2BoundaryResponse.response β (volumeIndex N) univ
      (boundary N) (SU2BoundaryResponse.firstPatch N) (SU2BoundaryResponse.secondPatch N) b a c := by
  unfold mixedChange
  simp_rw [logPartition_eq_boundary]
  rfl

/-- All original sites, hence all interior links, have the same mesh cell. -/
theorem one_cell (N : ℕ) (x : Site 4 (volumeIndex N)) : cell (side N) x = 0 := by
  funext i
  exact Nat.div_eq_of_lt (x i).val_lt

/-- There are actual integrated link variables at every volume. -/
theorem interior_nonempty (N : ℕ) :
    ∃ l : AssemblyLink N, l ∉ boundary N := by
  refine ⟨((fun _ => 1), 0), ?_⟩
  intro h
  obtain ⟨i, _, hi⟩ := (mem_filter.mp h).2
  have hv : (1 : ZMod (side N)).val = 1 := by
    rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by dsimp [side, volumeIndex]; omega)]
  change side N ∣ (1 : ZMod (side N)).val at hi
  rw [hv] at hi
  have hle := Nat.le_of_dvd (by norm_num : 0 < 1) hi
  dsimp [side, volumeIndex] at hle
  omega

/-- Both changed singleton patches are genuinely retained boundary variables. -/
theorem patches_on_boundary (N : ℕ) :
    SU2BoundaryResponse.firstPatch N ∪ SU2BoundaryResponse.secondPatch N ⊆ boundary N :=
  (SU2BoundaryResponse.growing_patches_on_face N).trans (heldFace_subset_separator _ _)

/-- The growing block retains a whole microscopic three-dimensional face. -/
theorem boundary_card_lower (N : ℕ) : (side N)^3 ≤ (boundary N).card :=
  SU2WilsonSeparatorComparison.retained_face_card _ _ le_rfl

/-- Genuine spatial decay across one increasingly large integrated block;
the prefactor and rate are independent of its side length. -/
theorem mixedChange_decay {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 4) :
    ∃ κ > 0, ∀ (N : ℕ) (b a c : FullField N),
      |mixedChange N β b a c| ≤
        3 * Real.exp (512*β + 1536 + 2*κ) * Real.exp (-κ * ((N : ℝ) + 3)) := by
  obtain ⟨κ, hκ, h⟩ := SU2BoundaryResponse.growing_family_bound hβ hβ0
  refine ⟨κ, hκ, ?_⟩
  intro N b a c
  rw [mixedChange_eq_response]
  exact h N univ (boundary N) b a c

theorem tendsto_mixedChange {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 4)
    (b a c : ∀ N, FullField N) :
    Tendsto (fun N => mixedChange N β (b N) (a N) (c N)) atTop (𝓝 0) := by
  simp_rw [mixedChange_eq_response]
  exact SU2BoundaryResponse.tendsto_growing_response hβ hβ0 (fun _ => univ) boundary b a c

#print axioms logPartition_eq_boundary
#print axioms one_cell
#print axioms interior_nonempty
#print axioms boundary_card_lower
#print axioms mixedChange_decay
#print axioms tendsto_mixedChange
end Mettapedia.QuantumTheory.YangMills.SU2WilsonGrowingBlock

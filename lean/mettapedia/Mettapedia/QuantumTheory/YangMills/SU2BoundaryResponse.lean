import Mettapedia.QuantumTheory.YangMills.SU2WilsonBlockIntegration
import Mettapedia.QuantumTheory.YangMills.WilsonSeparatedBoundaryResponse

/-!
# Spatial decay of the genuine SU(2) boundary free energy

The gauge group is the matrix group SU(2), the reference law is normalized
Haar, and the plaquette energy is `1 - Re(trace U_p)/2`. Arbitrary plaquette
masks and fixed boundary values are allowed. The bound is uniform in volume
on the explicit SC4 coupling interval. Its prefactor depends only on the
sizes of the two changed patches.
-/
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Filter
open scoped Topology Classical
open Mettapedia.Combinatorics.PolymerGas

namespace Mettapedia.QuantumTheory.YangMills.SU2BoundaryResponse
open SU2WilsonBlockPilot StrongCouplingCrossing InhomogeneousWilsonCrossing
open WilsonLocalResponse WilsonPatchGeometry WilsonBoundaryChanges
open WilsonSeparatedBoundaryResponse

/-- The original SU(2) Wilson plaquette, with its two reversed links. -/
def plaquetteEnergy : C((Fin 4 → SU2), ℝ) :=
  ⟨fun v => SU2WilsonBlockIntegration.potential (StrongCouplingTwist.holonomy v), by
    apply SU2WilsonBlockIntegration.potential.continuous.comp
    unfold StrongCouplingTwist.holonomy
    fun_prop⟩

/-- Each selected plaquette appears once; omitted factors are exactly one. -/
abbrev model (n : ℕ) (active : Finset (Plaquette 4 n)) : Model 4 SU2 :=
  ({ n := n
     φ := fun _ => plaquetteEnergy
     measurable := fun _ => plaquetteEnergy.continuous.measurable
     nonneg := fun _ _ => (SU2WilsonBlockIntegration.potential_bounds _).1
     le_two := fun _ _ => (SU2WilsonBlockIntegration.potential_bounds _).2 } : Model 4 SU2).masked active

theorem model_continuous (n : ℕ) (active : Finset (Plaquette 4 n)) :
    ∀ p, Continuous ((model n active).φ p) := by
  intro p
  dsimp only [model, Model.masked]
  split_ifs
  · exact plaquetteEnergy.continuous
  · exact continuous_const

/-- Four original boundary partition functions on the same SU(2) lattice. -/
def response (β : ℝ) (n : ℕ) (active : Finset (Plaquette 4 n))
    (held S T : Finset (Link 4 n)) (b a c : Link 4 n → SU2) : ℝ :=
  boundaryResponse (volume : Measure SU2) (model n active) (model_continuous n active)
    β held S T b a c

private theorem exp_ratio (a b c t : ℝ) :
    (3 * Real.exp a * Real.exp b * Real.exp c * Real.exp t) /
      (Real.exp (-a) * Real.exp (-b)) = 3 * Real.exp (2*a + 2*b + c + t) := by
  rw [show 2*a + 2*b + c + t = a + b + c + t + a + b by ring]
  simp only [Real.exp_neg, Real.exp_add, div_mul_eq_div_div, div_inv_eq_mul]
  ring

/-- An explicit patch-size prefactor and spatial decay for the genuine SU(2)
Wilson action. Neither the decay rate nor the prefactor grows with the rest
of the lattice. -/
theorem uniform_boundary_response {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 4) :
    ∃ κ > 0, ∀ (n : ℕ) (active : Finset (Plaquette 4 n))
      (held S T : Finset (Link 4 n)) (b a c : Link 4 n → SU2),
      (collar S).Nonempty → (collar T).Nonempty → 1 < polymerDist S T →
      |response β n active held S T b a c| ≤
        3 * Real.exp ((256 * β + 768) * (S.card + T.card) + 2 * κ) *
          Real.exp (-κ * polymerDist S T) := by
  obtain ⟨κ, hκ, hc⟩ := boundaryResponse_clustering 4 (volume : Measure SU2)
    (1 : SU2) hβ hβ0
  refine ⟨κ, hκ, ?_⟩
  intro n active held S T b a c hS hT hsep
  have h := hc (model n active) (model_continuous n active) held S T b a c hS
    (disjoint_incident_of_separation hsep)
  change |response β n active held S T b a c| ≤ _ at h
  rw [show -2 * β * ((incident S).card : ℝ) = -(2 * β * (incident S).card) by ring,
    show -2 * β * ((incident T).card : ℝ) = -(2 * β * (incident T).card) by ring,
    exp_ratio] at h
  apply h.trans
  rw [mul_assoc 3, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 3)
  apply Real.exp_le_exp.mpr
  have hqS : ((incident S).card : ℝ) ≤ S.card * 64 := by
    exact_mod_cast WilsonPatchGeometry.card_incident_le S
  have hqT : ((incident T).card : ℝ) ≤ T.card * 64 := by
    exact_mod_cast WilsonPatchGeometry.card_incident_le T
  have hsS : ((collar S).card : ℝ) ≤ S.card * 256 := by
    exact_mod_cast card_collar_le S
  have hsT : ((collar T).card : ℝ) ≤ T.card * 256 := by
    exact_mod_cast card_collar_le T
  have hd := separation_collar hS hT
  nlinarith

/-- Displacements grow while the side length remains larger than twice their
radius; hence the estimate is tested away from torus wrap-around. -/
def displacement (r : ℕ) : Fin 4 → ℤ := fun i => if i = 0 then (r + 3 : ℕ) else 0

abbrev familyVolume (r : ℕ) : ℕ := 4*r + 5

def firstPatch (r : ℕ) : Finset (Link 4 (familyVolume r)) :=
  CalibrationSeparation.firstSupport 0 (familyVolume r) (displacement r)

def secondPatch (r : ℕ) : Finset (Link 4 (familyVolume r)) :=
  CalibrationSeparation.secondSupport 0 (familyVolume r) (displacement r)

theorem growing_separation (r : ℕ) :
    (r : ℝ) + 3 ≤ polymerDist (firstPatch r) (secondPatch r) := by
  have hr : CalibrationSeparation.radius (displacement r) ≤ r + 3 := by
    apply Finset.sup_le
    intro i _
    by_cases h : i = 0
    · simp only [displacement, h, ↓reduceIte]
      exact le_rfl
    · simp [displacement, h]
  have h := CalibrationSeparation.abs_coordinate_le_support_dist
    (n := familyVolume r) (0 : Fin 4) (displacement r) (by dsimp [familyVolume]; omega) 0
  simpa [displacement, firstPatch, secondPatch,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (r : ℝ) + 3)] using h

/-- On singleton patches the prefactor is constant along the entire growing
family. All other boundary values and plaquette masks may vary with volume. -/
theorem growing_family_bound {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 4) :
    ∃ κ > 0, ∀ (r : ℕ) (active : Finset (Plaquette 4 (familyVolume r)))
      (held : Finset (Link 4 (familyVolume r))) (b a c : Link 4 (familyVolume r) → SU2),
      |response β (familyVolume r) active held (firstPatch r) (secondPatch r) b a c| ≤
        3 * Real.exp (512 * β + 1536 + 2 * κ) * Real.exp (-κ * ((r : ℝ) + 3)) := by
  obtain ⟨κ, hκ, hc⟩ := uniform_boundary_response hβ hβ0
  refine ⟨κ, hκ, ?_⟩
  intro r active held b a c
  have hS : (collar (firstPatch r)).Nonempty := singleton_zero_collar_nonempty _
  have hT : (collar (secondPatch r)).Nonempty := singleton_zero_collar_nonempty _
  have hd := growing_separation r
  have h := hc (familyVolume r) active held (firstPatch r) (secondPatch r) b a c hS hT
    (by have := Nat.cast_nonneg (α := ℝ) r; linarith)
  have hcard : (256 * β + 768) * ((firstPatch r).card + (secondPatch r).card : ℝ) + 2 * κ =
      512 * β + 1536 + 2 * κ := by
    simp only [firstPatch, secondPatch, CalibrationSeparation.card_firstSupport,
      CalibrationSeparation.card_secondSupport, Nat.cast_one]
    ring
  rw [hcard] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  nlinarith

/-- The actual mixed boundary free energy tends to zero on the growing
family, for arbitrary volume-dependent masks and prescribed boundary data. -/
theorem tendsto_growing_response {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 4)
    (active : ∀ r, Finset (Plaquette 4 (familyVolume r)))
    (held : ∀ r, Finset (Link 4 (familyVolume r)))
    (b a c : ∀ r, Link 4 (familyVolume r) → SU2) :
    Tendsto (fun r => response β (familyVolume r) (active r) (held r)
      (firstPatch r) (secondPatch r) (b r) (a r) (c r)) atTop (𝓝 0) := by
  obtain ⟨κ, hκ, hc⟩ := growing_family_bound hβ hβ0
  have ht : Tendsto (fun r : ℕ => κ * ((r : ℝ) + 3)) atTop atTop :=
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).const_mul_atTop hκ
  have he : Tendsto (fun r : ℕ => Real.exp (-κ * ((r : ℝ) + 3))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp ht
  have hb := he.const_mul (3 * Real.exp (512 * β + 1536 + 2 * κ))
  rw [mul_zero] at hb
  apply squeeze_zero_norm (fun r => ?_) hb
  simpa only [Real.norm_eq_abs] using hc r (active r) (held r) (b r) (a r) (c r)

/-- A genuine codimension-one fixed face containing both growing patches;
links normal to the face remain integrated. -/
def heldFace (n : ℕ) : Finset (Link 4 n) :=
  univ.filter (fun l => l.2 ≠ 1 ∧ l.1 1 = 0)

theorem growing_patches_on_face (r : ℕ) :
    firstPatch r ∪ secondPatch r ⊆ heldFace (familyVolume r) := by
  intro l hl
  simp only [firstPatch, secondPatch, CalibrationSeparation.firstSupport,
    CalibrationSeparation.secondSupport, mem_union, mem_singleton] at hl
  rcases hl with rfl | rfl <;>
    simp [heldFace, CalibrationSeparation.displacementSite, displacement]

theorem normal_link_not_held (n : ℕ) :
    ((0 : Site 4 n), (1 : Fin 4)) ∉ heldFace n := by simp [heldFace]

#print axioms uniform_boundary_response
#print axioms growing_separation
#print axioms growing_family_bound
#print axioms tendsto_growing_response
end Mettapedia.QuantumTheory.YangMills.SU2BoundaryResponse

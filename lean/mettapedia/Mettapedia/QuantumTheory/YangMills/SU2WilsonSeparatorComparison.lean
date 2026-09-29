import Mettapedia.QuantumTheory.YangMills.SU2WilsonAssembly
import Mettapedia.QuantumTheory.YangMills.WilsonDyadicProjection

/-!
# Comparing two separators on the same SU(2) Wilson model

The mesh-four separator is a strict subset of the mesh-two separator. The
discarded links are actual shared interfaces, not independent copies.
Both choices have the same strong-coupling spatial response estimate.
Exact retained boundary data grow with the microscopic area of a face.
-/
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory
open scoped Topology Classical
open Mettapedia.Combinatorics.PolymerGas
namespace Mettapedia.QuantumTheory.YangMills.SU2WilsonSeparatorComparison
open StrongCouplingCrossing SU2WilsonAssembly WilsonDyadicGeometry
open WilsonDyadicProjection WilsonDyadicLocality WilsonPatchGeometry

/-- A fine separator link that becomes an interior interface at the next level. -/
def seamLink (N : ℕ) : AssemblyLink N := (![2, 1, 1, 1], 1)

theorem seamLink_retained_two (N : ℕ) : Retained 2 (seamLink N) := by
  refine ⟨0, by change (0 : Fin 4) ≠ 1; decide, ?_⟩
  change 2 ∣ ((2 : ℕ) : ZMod (volumeIndex N + 3)).val
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by dsimp [volumeIndex]; omega)]

theorem seamLink_not_retained_four (N : ℕ) : ¬Retained 4 (seamLink N) := by
  have h1 : (1 : ZMod (volumeIndex N + 3)).val = 1 := by
    rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by dsimp [volumeIndex]; omega)]
  have h2 : (2 : ZMod (volumeIndex N + 3)).val = 2 := by
    change ((2 : ℕ) : ZMod (volumeIndex N + 3)).val = 2
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by dsimp [volumeIndex]; omega)]
  rintro ⟨i, hi, hd⟩
  fin_cases i <;> simp_all [seamLink]

/-- The second stage genuinely integrates variables retained by the first. -/
theorem separators_strict (N : ℕ) :
    (retainedSet 4 : Finset (AssemblyLink N)) ⊂ retainedSet 2 := by
  apply ssubset_iff_subset_ne.mpr
  constructor
  · intro l hl
    exact mem_filter.mpr ⟨mem_univ _, coarse_retained_fine l (mem_filter.mp hl).2⟩
  · intro heq
    have h : seamLink N ∈ (retainedSet 4 : Finset (AssemblyLink N)) := by
      rw [heq]
      exact mem_filter.mpr ⟨mem_univ _, seamLink_retained_two N⟩
    exact seamLink_not_retained_four N (mem_filter.mp h).2

/-- One microscopic face of a block, with one tangential orientation. -/
def faceLink (n s : ℕ) (q : Fin 3 → Fin s) : Link 4 n :=
  (![0, (q 0 : ℕ), (q 1 : ℕ), (q 2 : ℕ)], 1)

theorem faceLink_retained (n s : ℕ) (q : Fin 3 → Fin s) : Retained s (faceLink n s q) := by
  refine ⟨0, by change (0 : Fin 4) ≠ 1; decide, ?_⟩
  simp [faceLink]

theorem faceLink_injective (n s : ℕ) (hs : s ≤ n + 3) :
    Function.Injective (faceLink n s) := by
  intro q r h
  have hv (k : Fin s) : ((k : ℕ) : ZMod (n+3)).val = k := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (lt_of_lt_of_le k.isLt hs)]
  have he (i : Fin 4) := congrArg (fun l : Link 4 n => (l.1 i).val) h
  funext i
  apply Fin.ext
  fin_cases i
  · simpa [faceLink, hv] using he 1
  · simpa [faceLink, hv] using he 2
  · simpa [faceLink, hv] using he 3

/-- Even one face retains at least `s^3` distinct microscopic SU(2) link coordinates.
This lower bound must be addressed by any proposed fixed-size coarse encoding. -/
theorem retained_face_card (n s : ℕ) (hs : s ≤ n + 3) :
    s^3 ≤ (retainedSet s : Finset (Link 4 n)).card := by
  have hi := faceLink_injective n s hs
  have hsub : univ.image (faceLink n s) ⊆ (retainedSet s : Finset (Link 4 n)) := by
    intro l hl
    obtain ⟨q, _, rfl⟩ := mem_image.mp hl
    exact mem_filter.mpr ⟨mem_univ _, faceLink_retained n s q⟩
  have hc := card_le_card hsub
  rw [card_image_of_injective _ hi] at hc
  simpa using hc

/-- Mesh two has a three-link collar in the original lattice metric. -/
theorem fine_collar (N : ℕ) (S : Finset (AssemblyLink N))
    {l : AssemblyLink N} (hl : l ∈ dependencyBoundary 2 S) :
    ∃ a ∈ S, dist l a ≤ 3 := by
  have h := dependencyBoundary_radius (by norm_num : 0 < 2) S hl
  obtain ⟨a, ha, hd⟩ := h
  refine ⟨a, ha, ?_⟩
  norm_num at hd
  exact hd

/-- Mesh four integrates more variables and has a five-link collar in the same
original metric. Its generated interactions are retained exactly. -/
theorem coarse_collar (N : ℕ) (S : Finset (AssemblyLink N))
    {l : AssemblyLink N} (hl : l ∈ dependencyBoundary 4 S) :
    ∃ a ∈ S, dist l a ≤ 5 := by
  have h := dependencyBoundary_radius (by norm_num : 0 < 4) S hl
  obtain ⟨a, ha, hd⟩ := h
  refine ⟨a, ha, ?_⟩
  norm_num at hd
  exact hd

/-- One rate works simultaneously for both separators, every volume and all
boundary assignments, on the same full Wilson plaquette model. -/
theorem both_separators_response {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 4) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (N s : ℕ) (S T : Finset (AssemblyLink N))
      (b a c : FullField N),
      (collar S).Nonempty → (collar T).Nonempty → 1 < polymerDist S T →
      |SU2BoundaryResponse.response β (volumeIndex N) univ (retainedSet s) S T b a c| ≤
        3 * Real.exp ((256*β + 768) * (S.card + T.card) + 2*κ) *
          Real.exp (-κ * polymerDist S T) := by
  obtain ⟨κ, hκ, h⟩ := SU2BoundaryResponse.uniform_boundary_response hβ hβ0
  exact ⟨κ, hκ, fun N s S T b a c => h (volumeIndex N) univ (retainedSet s) S T b a c⟩

#print axioms separators_strict
#print axioms retained_face_card
#print axioms both_separators_response
end Mettapedia.QuantumTheory.YangMills.SU2WilsonSeparatorComparison

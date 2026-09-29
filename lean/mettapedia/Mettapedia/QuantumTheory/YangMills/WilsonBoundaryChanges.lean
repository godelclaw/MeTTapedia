import Mettapedia.QuantumTheory.YangMills.WilsonLocalResponse
import Mettapedia.QuantumTheory.YangMills.WilsonPatchGeometry

/-!
# Local factors for actual changes of Wilson boundary data

A change on a patch of fixed links is represented exactly by a density factor
on the incident-plaquette collar. Its upper and lower bounds depend on the
number of incident plaquettes, not the volume. Separated changes compose
multiplicatively, so their mixed boundary free energy is the local response
controlled by strong-coupling clustering.
-/
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory
open scoped Topology
open Mettapedia.Combinatorics.PolymerGas

namespace Mettapedia.QuantumTheory.YangMills.WilsonBoundaryChanges
open StrongCouplingCrossing InhomogeneousWilsonCrossing WilsonPatchGeometry WilsonLocalResponse
open WilsonBlockElimination WilsonBoundaryResponse

variable {E : Type*} [TopologicalSpace E] [CompactSpace E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] {d n : ℕ}

/-- Replace boundary values only on the specified patch. -/
def replace (S : Finset (Link d n)) (new old : Link d n → E) : Link d n → E :=
  fun l => if l ∈ S then new l else old l

/-- The original local energy at a plaquette after fixing the chosen links. -/
def pinnedPotential (M : Model d E) (held : Finset (Link d M.n))
    (b : Link d M.n → E) (p : Plaquette d M.n) (ω : Link d M.n → E) : ℝ :=
  potential ((M.pinned held b).φ p) p ω

theorem continuous_pinnedPotential (M : Model d E) (hφ : ∀ p, Continuous (M.φ p))
    (held : Finset (Link d M.n)) (b : Link d M.n → E) (p : Plaquette d M.n) :
    Continuous (pinnedPotential M held b p) :=
  (continuous_pinned M hφ held b p).comp (continuous_pi fun _ => continuous_apply _)

theorem pinnedPotential_eq_of_agree (M : Model d E) (held : Finset (Link d M.n))
    (b b' : Link d M.n → E) (p : Plaquette d M.n)
    (h : ∀ l ∈ support p, b l = b' l) (ω : Link d M.n → E) :
    pinnedPotential M held b p ω = pinnedPotential M held b' p ω := by
  dsimp only [pinnedPotential, potential, Model.pinned]
  apply congrArg (M.φ p)
  funext i
  rw [h _ (mem_image.mpr ⟨i, mem_univ _, rfl⟩)]

theorem pinnedPotential_local (M : Model d E) (held : Finset (Link d M.n))
    (b : Link d M.n → E) (p : Plaquette d M.n) (ω ω' : Link d M.n → E)
    (h : ∀ l ∈ support p, ω l = ω' l) :
    pinnedPotential M held b p ω = pinnedPotential M held b p ω' := by
  unfold pinnedPotential potential
  congr 1
  funext i
  exact h _ (mem_image.mpr ⟨i, mem_univ _, rfl⟩)

theorem unchanged_off_incident (M : Model d E) (held S : Finset (Link d M.n))
    (b new : Link d M.n → E) (p : Plaquette d M.n) (hp : p ∉ incident S)
    (ω : Link d M.n → E) :
    pinnedPotential M held (replace S new b) p ω = pinnedPotential M held b p ω := by
  apply pinnedPotential_eq_of_agree
  intro l hl
  have hnot : l ∉ S := fun hS => hp (mem_incident.mpr ⟨l, hS, hl⟩)
  simp [replace, hnot]

/-- The complete energy change; the sum only removes terms proved unchanged. -/
def energyChange (M : Model d E) (hφ : ∀ p, Continuous (M.φ p))
    (held S : Finset (Link d M.n)) (b new : Link d M.n → E) :
    C(Link d M.n → E, ℝ) :=
  ⟨fun ω => ∑ p ∈ incident S, (pinnedPotential M held (replace S new b) p ω -
    pinnedPotential M held b p ω), continuous_finsetSum _ fun p _ =>
      (continuous_pinnedPotential M hφ held _ p).sub
        (continuous_pinnedPotential M hφ held _ p)⟩

theorem energyChange_eq_full (M : Model d E) (hφ : ∀ p, Continuous (M.φ p))
    (held S : Finset (Link d M.n)) (b new : Link d M.n → E) (ω : Link d M.n → E) :
    energyChange M hφ held S b new ω =
      (∑ p, pinnedPotential M held (replace S new b) p ω) -
        ∑ p, pinnedPotential M held b p ω := by
  rw [← sum_sub_distrib]
  exact sum_subset (subset_univ _) (fun p _ hp => by
    rw [unchanged_off_incident M held S b new p hp, sub_self])

/-- The actual Radon--Nikodym factor for this change of boundary values. -/
def changeFactor (M : Model d E) (hφ : ∀ p, Continuous (M.φ p)) (β : ℝ)
    (held S : Finset (Link d M.n)) (b new : Link d M.n → E) :
    C(Link d M.n → E, ℝ) :=
  ⟨fun ω => Real.exp (-β * energyChange M hφ held S b new ω), by fun_prop⟩

theorem changeFactor_pos (M : Model d E) (hφ : ∀ p, Continuous (M.φ p)) (β : ℝ)
    (held S : Finset (Link d M.n)) (b new : Link d M.n → E) (ω : Link d M.n → E) :
    0 < changeFactor M hφ β held S b new ω := Real.exp_pos _

theorem realDensity_pinned_eq_exp (M : Model d E) (hφ : ∀ p, Continuous (M.φ p)) (β : ℝ)
    (held : Finset (Link d M.n)) (b : Link d M.n → E) (ω : Link d M.n → E) :
    realDensity (M.pinned held b) (continuous_pinned M hφ held b) β ω =
      Real.exp (-β * ∑ p, pinnedPotential M held b p ω) := by
  simp only [realDensity, ContinuousMap.coe_mk, pinnedPotential]
  rw [mul_sum, Real.exp_sum]

/-- Exact equality of the two original fixed-boundary densities. -/
theorem density_changed (M : Model d E) (hφ : ∀ p, Continuous (M.φ p)) (β : ℝ)
    (held S : Finset (Link d M.n)) (b new : Link d M.n → E) :
    realDensity (M.pinned held (replace S new b)) (continuous_pinned M hφ held _) β =
      realDensity (M.pinned held b) (continuous_pinned M hφ held b) β *
        changeFactor M hφ β held S b new := by
  ext ω
  change realDensity (M.pinned held (replace S new b))
      (continuous_pinned M hφ held _) β ω =
    realDensity (M.pinned held b) (continuous_pinned M hφ held b) β ω *
      Real.exp (-β * energyChange M hφ held S b new ω)
  rw [realDensity_pinned_eq_exp M hφ β held (replace S new b) ω,
    realDensity_pinned_eq_exp M hφ β held b ω, energyChange_eq_full, ← Real.exp_add]
  congr 1
  ring

/-- A response factor depends only on the actual incident-plaquette collar. -/
theorem changeFactor_local (M : Model d E) (hφ : ∀ p, Continuous (M.φ p)) (β : ℝ)
    (held S : Finset (Link d M.n)) (b new : Link d M.n → E)
    (ω ω' : Link d M.n → E) (h : ∀ l ∈ collar S, ω l = ω' l) :
    changeFactor M hφ β held S b new ω = changeFactor M hφ β held S b new ω' := by
  apply congrArg (fun t => Real.exp (-β * t))
  apply sum_congr rfl
  intro p hp
  have hp' : ∀ l ∈ support p, ω l = ω' l := fun l hl =>
    h l (mem_biUnion.mpr ⟨p, hp, hl⟩)
  rw [pinnedPotential_local M held _ p ω ω' hp', pinnedPotential_local M held b p ω ω' hp']

theorem energyChange_bounds (M : Model d E) (hφ : ∀ p, Continuous (M.φ p))
    (held S : Finset (Link d M.n)) (b new : Link d M.n → E) (ω : Link d M.n → E) :
    -(2 * (incident S).card : ℝ) ≤ energyChange M hφ held S b new ω ∧
      energyChange M hφ held S b new ω ≤ 2 * (incident S).card := by
  have hlo (p : Plaquette d M.n) : -2 ≤
      pinnedPotential M held (replace S new b) p ω - pinnedPotential M held b p ω := by
    have := (M.pinned held (replace S new b)).nonneg p (fun i => ω (linkAt p i))
    have := (M.pinned held b).le_two p (fun i => ω (linkAt p i))
    change -2 ≤ potential ((M.pinned held (replace S new b)).φ p) p ω -
      potential ((M.pinned held b).φ p) p ω
    unfold potential
    linarith
  have hhi (p : Plaquette d M.n) :
      pinnedPotential M held (replace S new b) p ω - pinnedPotential M held b p ω ≤ 2 := by
    have := (M.pinned held (replace S new b)).le_two p (fun i => ω (linkAt p i))
    have := (M.pinned held b).nonneg p (fun i => ω (linkAt p i))
    change potential ((M.pinned held (replace S new b)).φ p) p ω -
      potential ((M.pinned held b).φ p) p ω ≤ 2
    unfold potential
    linarith
  constructor
  · simpa [energyChange, mul_comm] using sum_le_sum (s := incident S) (fun p _ => hlo p)
  · simpa [energyChange, mul_comm] using sum_le_sum (s := incident S) (fun p _ => hhi p)

/-- The normalization cost depends only on the changed patch. -/
theorem changeFactor_bounds (M : Model d E) (hφ : ∀ p, Continuous (M.φ p))
    {β : ℝ} (hβ : 0 ≤ β) (held S : Finset (Link d M.n))
    (b new : Link d M.n → E) (ω : Link d M.n → E) :
    Real.exp (-2 * β * (incident S).card) ≤ changeFactor M hφ β held S b new ω ∧
      changeFactor M hφ β held S b new ω ≤ Real.exp (2 * β * (incident S).card) := by
  obtain ⟨hl, hu⟩ := energyChange_bounds M hφ held S b new ω
  constructor <;> apply Real.exp_le_exp.mpr <;> nlinarith

#print axioms density_changed
#print axioms changeFactor_local
#print axioms changeFactor_bounds

end Mettapedia.QuantumTheory.YangMills.WilsonBoundaryChanges

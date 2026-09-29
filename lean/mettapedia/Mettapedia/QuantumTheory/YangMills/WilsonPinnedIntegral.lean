import Mettapedia.QuantumTheory.YangMills.WilsonSeparatedBoundaryResponse

/-!
# Fixed-boundary integrals without dummy variables

Replacing held coordinates inside the plaquette potentials is exactly
integration over the complementary link variables. The unused held-coordinate
probability factors integrate to one. This identifies the boundary response
with the original interior-only partition function.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Finset
open scoped Topology Classical

namespace Mettapedia.QuantumTheory.YangMills.WilsonPinnedIntegral
open StrongCouplingCrossing InhomogeneousWilsonCrossing WilsonLocalResponse
open WilsonSeparatedBoundaryResponse WilsonBoundaryResponse

variable {X E : Type*} [Fintype X] [DecidableEq X] [MeasurableSpace E]

/-- Assemble prescribed boundary values with the remaining interior variables. -/
def fill (held : Finset X) (b : X → E) (i : {x // x ∉ held} → E) : X → E :=
  fun x => if h : x ∈ held then b x else i ⟨x, h⟩

def pin (held : Finset X) (b ω : X → E) : X → E :=
  fun x => if x ∈ held then b x else ω x

/-- Exact equality of the two integration conventions, for an arbitrary
integrand and any probability law on each link. -/
theorem integral_pin (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (held : Finset X) (b : X → E) (F : (X → E) → ℝ) :
    (∫ ω, F (pin held b ω) ∂Measure.pi (fun _ : X => ν₀)) =
      ∫ i, F (fill held b i) ∂Measure.pi (fun _ : {x // x ∉ held} => ν₀) := by
  letI : Fintype {x : X // x ∈ held} := Subtype.fintype (fun x => x ∈ held)
  have h := (measurePreserving_piEquivPiSubtypeProd (fun _ : X => ν₀)
    (fun x => x ∈ held)).symm.integral_comp' (fun ω => F (pin held b ω))
  rw [← h]
  have heq : (fun p : (held → E) × ({x // x ∉ held} → E) =>
      F (pin held b ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : X => E)
        (fun x => x ∈ held)).symm p))) = fun p => F (fill held b p.2) := by
    funext p
    apply congrArg F
    funext x
    by_cases hx : x ∈ held <;>
      simp [pin, fill, MeasurableEquiv.piEquivPiSubtypeProd,
        Equiv.piEquivPiSubtypeProd_symm_apply, hx]
  rw [heq]
  simpa using (integral_fun_snd
    (μ := Measure.pi (fun _ : {x : X // x ∈ held} => ν₀))
    (ν := Measure.pi (fun _ : {x // x ∉ held} => ν₀))
    (fun i => F (fill held b i)))

section Continuous
variable [TopologicalSpace E] [CompactSpace E] [BorelSpace E] [SecondCountableTopology E]
  {d : ℕ}

theorem realDensity_pinned_apply (M : Model d E) (hφ : ∀ p, Continuous (M.φ p))
    (β : ℝ) (held : Finset (Link d M.n)) (b ω : Link d M.n → E) :
    realDensity (M.pinned held b) (continuous_pinned M hφ held b) β ω =
      realDensity M hφ β (pin held b ω) := rfl

/-- The partition function used in the spatial response theorem is exactly
the partition function integrating only the unheld links. -/
theorem boundaryLogPartition_eq_interior (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (M : Model d E) (hφ : ∀ p, Continuous (M.φ p)) (β : ℝ)
    (held : Finset (Link d M.n)) (b : Link d M.n → E) :
    boundaryLogPartition ν₀ M hφ β held b =
      Real.log (∫ i, realDensity M hφ β (fill held b i)
        ∂Measure.pi (fun _ : {l : Link d M.n // l ∉ held} => ν₀)) := by
  unfold boundaryLogPartition logPartition
  simp_rw [realDensity_pinned_apply M hφ β held b]
  rw [integral_pin]

end Continuous
#print axioms integral_pin
#print axioms boundaryLogPartition_eq_interior
end Mettapedia.QuantumTheory.YangMills.WilsonPinnedIntegral

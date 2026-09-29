import Mettapedia.QuantumTheory.YangMills.SU2BoundaryResponse
import Mettapedia.QuantumTheory.YangMills.WilsonDyadicGeometry
import Mettapedia.QuantumTheory.YangMills.WilsonEliminationRoutes

/-!
# Exact two-level SU(2) Wilson block assembly

The periodic four-dimensional lattice has side `4(N+2)`. Fine blocks have
side two, and coarse blocks have side four. First integrate links interior
to fine blocks; then integrate the fine separator links that are interior
to coarse blocks. The remaining variables are the coarse separator links.

Every elementary plaquette occurs once in the original Wilson product.
The two marginalizations retain the entire induced boundary density and
all marked-observable remainders. No Wilson-form truncation is made.
-/
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory
open scoped Topology Classical

namespace Mettapedia.QuantumTheory.YangMills.SU2WilsonAssembly
open StrongCouplingCrossing SU2WilsonBlockPilot WilsonDyadicGeometry
open WilsonBlockElimination CompactTransferGap
open Mettapedia.GSLT.Ultrainfinite

abbrev volumeIndex (N : ℕ) := 4*N + 5
abbrev AssemblyLink (N : ℕ) := Link 4 (volumeIndex N)
abbrev AssemblyPlaquette (N : ℕ) := Plaquette 4 (volumeIndex N)
abbrev FullField (N : ℕ) := AssemblyLink N → SU2

abbrev FineLink (N : ℕ) := {l : AssemblyLink N // Retained 2 l}
abbrev InternalLink (N : ℕ) := {l : AssemblyLink N // ¬Retained 2 l}
abbrev CoarseLink (N : ℕ) := {l : FineLink N // Retained 4 l.val}
abbrev InterfaceLink (N : ℕ) := {l : FineLink N // ¬Retained 4 l.val}

abbrev FineField (N : ℕ) := FineLink N → SU2
abbrev InternalField (N : ℕ) := InternalLink N → SU2
abbrev CoarseField (N : ℕ) := CoarseLink N → SU2
abbrev InterfaceField (N : ℕ) := InterfaceLink N → SU2
abbrev SplitField (N : ℕ) := (CoarseField N × InterfaceField N) × InternalField N

/-- Reassemble the fine boundary and its complementary interior links. -/
def assembleFine (N : ℕ) (p : FineField N × InternalField N) : FullField N :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : AssemblyLink N => SU2) (Retained 2)).symm p

/-- Reassemble coarse boundaries with the actual shared fine interfaces. -/
def assembleCoarse (N : ℕ) (p : CoarseField N × InterfaceField N) : FineField N :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : FineLink N => SU2)
    (fun l => Retained 4 l.val)).symm p

/-- Each original link has exactly one source coordinate in this nested split. -/
def assemble (N : ℕ) (p : SplitField N) : FullField N :=
  assembleFine N (assembleCoarse N p.1, p.2)

theorem continuous_assembleFine (N : ℕ) : Continuous (assembleFine N) := by
  apply continuous_pi
  intro l
  change Continuous (fun p : FineField N × InternalField N =>
    if h : Retained 2 l then p.1 ⟨l, h⟩ else p.2 ⟨l, h⟩)
  split_ifs <;> fun_prop

theorem continuous_assembleCoarse (N : ℕ) : Continuous (assembleCoarse N) := by
  apply continuous_pi
  intro l
  change Continuous (fun p : CoarseField N × InterfaceField N =>
    if h : Retained 4 l.val then p.1 ⟨l, h⟩ else p.2 ⟨l, h⟩)
  split_ifs <;> fun_prop

theorem continuous_assemble (N : ℕ) : Continuous (assemble N) :=
  (continuous_assembleFine N).comp
    (((continuous_assembleCoarse N).comp continuous_fst).prodMk continuous_snd)

theorem integral_assembleFine (N : ℕ) (F : FullField N → ℝ) :
    (∫ p : FineField N × InternalField N, F (assembleFine N p) ∂volume.prod volume) =
      ∫ ω : FullField N, F ω :=
  (volume_preserving_piEquivPiSubtypeProd (fun _ : AssemblyLink N => SU2) (Retained 2)).symm.integral_comp' F

theorem integral_assembleCoarse (N : ℕ) (F : FineField N → ℝ) :
    (∫ p : CoarseField N × InterfaceField N, F (assembleCoarse N p) ∂volume.prod volume) =
      ∫ ω : FineField N, F ω :=
  (volume_preserving_piEquivPiSubtypeProd (fun _ : FineLink N => SU2)
    (fun l => Retained 4 l.val)).symm.integral_comp' F

/-- The nested split preserves the original product Haar integral. -/
theorem integral_assemble (N : ℕ) (F : C(FullField N, ℝ)) :
    (∫ p : SplitField N, F (assemble N p) ∂(volume.prod volume).prod volume) =
      ∫ ω : FullField N, F ω := by
  rw [integral_prod (fun p : SplitField N => F (assemble N p))
    (IntegralKernel.integrable_continuous_fun _
    (F.continuous.comp (continuous_assemble N)))]
  change (∫ p : CoarseField N × InterfaceField N,
    (∫ j : InternalField N, F (assembleFine N (assembleCoarse N p, j)))
      ∂volume.prod volume) = _
  rw [integral_assembleCoarse N (fun b => ∫ j : InternalField N, F (assembleFine N (b, j)))]
  rw [← integral_prod (fun p : FineField N × InternalField N => F (assembleFine N p))
    (IntegralKernel.integrable_continuous_fun _
    (F.continuous.comp (continuous_assembleFine N)))]
  exact integral_assembleFine N F

/-- The original SU(2) density, with every torus plaquette included exactly once. -/
def fullDensity (N : ℕ) (β : ℝ) : C(FullField N, ℝ) :=
  WilsonLocalResponse.realDensity (SU2BoundaryResponse.model (volumeIndex N) univ)
    (SU2BoundaryResponse.model_continuous (volumeIndex N) univ) β

theorem fullDensity_pos (N : ℕ) (β : ℝ) (ω : FullField N) : 0 < fullDensity N β ω :=
  WilsonLocalResponse.realDensity_pos (SU2BoundaryResponse.model (volumeIndex N) univ)
    (SU2BoundaryResponse.model_continuous (volumeIndex N) univ) β ω

/-- All original plaquette factors in the coordinates of the two eliminations. -/
def density (N : ℕ) (β : ℝ) : C(SplitField N, ℝ) :=
  ⟨fun p => fullDensity N β (assemble N p),
    (fullDensity N β).continuous.comp (continuous_assemble N)⟩

theorem density_pos (N : ℕ) (β : ℝ) (p : SplitField N) : 0 < density N β p :=
  fullDensity_pos N β _

/-- The first effective density retains the fine interfaces. -/
def firstDensity (N : ℕ) (β : ℝ) : C(CoarseField N × InterfaceField N, ℝ) :=
  marginal (volume : Measure (InternalField N)) (density N β)

/-- The second effective density retains every generated coarse interaction. -/
def secondDensity (N : ℕ) (β : ℝ) : C(CoarseField N, ℝ) :=
  marginal (volume : Measure (InterfaceField N)) (firstDensity N β)

theorem secondDensity_staged (N : ℕ) (β : ℝ) :
    secondDensity N β = marginal
      ((volume : Measure (InterfaceField N)).prod (volume : Measure (InternalField N)))
      (reassociate (density N β)) :=
  marginal_staged _ _ _

/-- Staged elimination gives exactly the original full Wilson partition function. -/
theorem partition_staged (N : ℕ) (β : ℝ) :
    (∫ b : CoarseField N, secondDensity N β b) = ∫ ω : FullField N, fullDensity N β ω := by
  rw [secondDensity, integral_marginal, firstDensity, integral_marginal]
  exact integral_assemble N (fullDensity N β)

/-- Exact two-step GSLT route, using the already proved admissible operators. -/
def route (N : ℕ) (β : ℝ) : Route WilsonEliminationRoutes.Step
    (WilsonEliminationRoutes.source (volume.prod volume) volume (density N β) (density_pos N β))
    (WilsonEliminationRoutes.target volume volume (firstDensity N β)
      (marginal_pos volume (density N β) (density_pos N β))) :=
  .cons (WilsonEliminationRoutes.elimination (volume.prod volume) volume
      (density N β) (density_pos N β))
    (.cons (WilsonEliminationRoutes.elimination volume volume (firstDensity N β)
      (marginal_pos volume (density N β) (density_pos N β))) (.refl _))

def splitObservable (N : ℕ) (F : C(FullField N, ℝ)) : C(SplitField N, ℝ) :=
  ⟨fun p => F (assemble N p), F.continuous.comp (continuous_assemble N)⟩

theorem expectation_split (N : ℕ) (β : ℝ) (F : C(FullField N, ℝ)) :
    expectation ((volume.prod volume).prod volume) (density N β) (splitObservable N F) =
      expectation (volume : Measure (FullField N)) (fullDensity N β) F := by
  unfold expectation
  change (∫ p, (fullDensity N β * F) (assemble N p) ∂(volume.prod volume).prod volume) /
    (∫ p, fullDensity N β (assemble N p) ∂(volume.prod volume).prod volume) = _
  rw [integral_assemble, integral_assemble]
  rfl

/-- Every continuous mark is transported from the original Wilson law through
both genuine elimination stages. -/
theorem expectation_route (N : ℕ) (β : ℝ) (F : C(FullField N, ℝ)) :
    expectation (volume : Measure (CoarseField N)) (secondDensity N β)
      (WilsonEliminationRoutes.action (route N β) (splitObservable N F)) =
      expectation (volume : Measure (FullField N)) (fullDensity N β) F := by
  exact (WilsonEliminationRoutes.expectation_action (route N β) (splitObservable N F)).trans
    (expectation_split N β F)

/-- Exact covariance transport retains the entire composed remainder on the
coarse boundary. It holds at every real coupling. -/
theorem covariance_route (N : ℕ) (β : ℝ) (F G : C(FullField N, ℝ)) :
    covariance (volume : Measure (FullField N)) (fullDensity N β) F G =
      covariance (volume : Measure (CoarseField N)) (secondDensity N β)
        (WilsonEliminationRoutes.action (route N β) (splitObservable N F))
        (WilsonEliminationRoutes.action (route N β) (splitObservable N G)) +
      expectation (volume : Measure (CoarseField N)) (secondDensity N β)
        (WilsonEliminationRoutes.remainder (route N β) (splitObservable N F) (splitObservable N G)) := by
  have h := WilsonEliminationRoutes.covariance_action (route N β)
    (splitObservable N F) (splitObservable N G)
  have hmul : splitObservable N F * splitObservable N G = splitObservable N (F * G) := rfl
  have hs : covariance ((volume.prod volume).prod volume) (density N β)
      (splitObservable N F) (splitObservable N G) =
    covariance (volume : Measure (FullField N)) (fullDensity N β) F G := by
    simp only [covariance, hmul, expectation_split]
  exact hs.symm.trans h

/-- Explicit local Wilson marks on each actual elementary plaquette. -/
def plaquetteObservable (N : ℕ) (p : AssemblyPlaquette N) : C(FullField N, ℝ) :=
  ⟨fun ω => SU2BoundaryResponse.plaquetteEnergy (fun i => ω (linkAt p i)),
    SU2BoundaryResponse.plaquetteEnergy.continuous.comp
      (continuous_pi fun _ => continuous_apply _)⟩

theorem plaquetteObservable_bounds (N : ℕ) (p : AssemblyPlaquette N) (ω : FullField N) :
    0 ≤ plaquetteObservable N p ω ∧ plaquetteObservable N p ω ≤ 2 :=
  SU2WilsonBlockIntegration.potential_bounds _

#print axioms integral_assemble
#print axioms secondDensity_staged
#print axioms partition_staged
#print axioms expectation_route
#print axioms covariance_route
end Mettapedia.QuantumTheory.YangMills.SU2WilsonAssembly

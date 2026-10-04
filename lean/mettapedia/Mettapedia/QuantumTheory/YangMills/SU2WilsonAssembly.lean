import Mettapedia.QuantumTheory.YangMills.WilsonConditionalProjection
import Mettapedia.QuantumTheory.YangMills.SU2BoundaryResponse
import Mettapedia.QuantumTheory.YangMills.WilsonDyadicGeometry
import Mettapedia.QuantumTheory.YangMills.WilsonMaxwellBlock
import Mettapedia.QuantumTheory.YangMills.WilsonEliminationRoutes
import Mettapedia.QuantumTheory.YangMills.WilsonProjectionComposition

/-!
# Exact SU(2) Wilson assembly and Haar rescaling

The periodic four-dimensional lattice has side `4(N+2)`. Fine blocks have
side two, and coarse blocks have side four. First integrate links interior
to fine blocks; then integrate the fine separator links that are interior
to coarse blocks. The remaining variables are the coarse separator links.

Every elementary plaquette occurs once in the original Wilson product.
The two marginalizations retain the entire induced boundary density and
all marked-observable remainders. No Wilson-form truncation is made.

The separate scale-two map replaces each disjoint ordered link pair by its
product. Its positive generated density, gauge invariance and conditional
observables are explicit. A small local-interaction state carries the full
density and vacuum term; nonlinear extraction reconstructs the next density
exactly and contracts its support-cardinality norm. The Wilson action enters
the invariant radius at a positive volume-independent threshold.
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

/-- The first Haar elimination, integrating the fine block interiors. -/
def firstRoute (N : ℕ) (β : ℝ) : Route WilsonEliminationRoutes.Step
    (WilsonEliminationRoutes.source (volume.prod volume) volume (density N β) (density_pos N β))
    (WilsonEliminationRoutes.target (volume.prod volume) volume (density N β) (density_pos N β)) :=
  .cons (WilsonEliminationRoutes.elimination (volume.prod volume) volume
    (density N β) (density_pos N β)) (.refl _)

/-- The second Haar elimination uses the complete generated first density. -/
def secondRoute (N : ℕ) (β : ℝ) : Route WilsonEliminationRoutes.Step
    (WilsonEliminationRoutes.source volume volume (firstDensity N β)
      (marginal_pos volume (density N β) (density_pos N β)))
    (WilsonEliminationRoutes.target volume volume (firstDensity N β)
      (marginal_pos volume (density N β) (density_pos N β))) :=
  .cons (WilsonEliminationRoutes.elimination volume volume (firstDensity N β)
    (marginal_pos volume (density N β) (density_pos N β))) (.refl _)

/-- Exact two-step GSLT route, using the proved weighted integral operators. -/
def route (N : ℕ) (β : ℝ) : Route WilsonEliminationRoutes.Step
    (WilsonEliminationRoutes.source (volume.prod volume) volume (density N β) (density_pos N β))
    (WilsonEliminationRoutes.target volume volume (firstDensity N β)
      (marginal_pos volume (density N β) (density_pos N β))) :=
  .cons (WilsonEliminationRoutes.elimination (volume.prod volume) volume
      (density N β) (density_pos N β))
    (.cons (WilsonEliminationRoutes.elimination volume volume (firstDensity N β)
      (marginal_pos volume (density N β) (density_pos N β))) (.refl _))

theorem route_eq_append (N : ℕ) (β : ℝ) :
    route N β = (firstRoute N β).append (secondRoute N β) := rfl

def splitObservable (N : ℕ) (F : C(FullField N, ℝ)) : C(SplitField N, ℝ) :=
  ⟨fun p => F (assemble N p), F.continuous.comp (continuous_assemble N)⟩

/-- Actual initial weighted state and raw moments of the local marks. -/
def initialResponseState (N : ℕ) (β : ℝ) (F : AssemblyLink N → C(FullField N, ℝ)) :
    WilsonEliminationRoutes.BoundaryState (AssemblyLink N) :=
  ⟨WilsonEliminationRoutes.source (volume.prod volume) volume (density N β) (density_pos N β),
    WilsonEliminationRoutes.ResponseData.initial (fun l ↦ splitObservable N (F l))⟩

/-- The first generated density and all three orders of projected moments. -/
def firstResponseState (N : ℕ) (β : ℝ) (F : AssemblyLink N → C(FullField N, ℝ)) :
    WilsonEliminationRoutes.BoundaryState (AssemblyLink N) :=
  ⟨_, (initialResponseState N β F).2.transport (firstRoute N β)⟩

/-- The second generated density, retaining moments from the first step. -/
def secondResponseState (N : ℕ) (β : ℝ) (F : AssemblyLink N → C(FullField N, ℝ)) :
    WilsonEliminationRoutes.BoundaryState (AssemblyLink N) :=
  ⟨_, (firstResponseState N β F).2.transport (secondRoute N β)⟩

theorem initialResponse_transition (N : ℕ) (β : ℝ)
    (F : AssemblyLink N → C(FullField N, ℝ)) :
    WilsonEliminationRoutes.HaarTransition (AssemblyLink N)
      (initialResponseState N β F) (firstResponseState N β F) :=
  .integrate (volume.prod volume) volume (density N β) (density_pos N β) _

theorem firstResponse_transition (N : ℕ) (β : ℝ)
    (F : AssemblyLink N → C(FullField N, ℝ)) :
    WilsonEliminationRoutes.HaarTransition (AssemblyLink N)
      (firstResponseState N β F) (secondResponseState N β F) :=
  .integrate volume volume (firstDensity N β)
    (marginal_pos volume (density N β) (density_pos N β)) _

/-- Direct and staged transport agree for the complete boundary moment data. -/
theorem secondResponseState_data (N : ℕ) (β : ℝ)
    (F : AssemblyLink N → C(FullField N, ℝ)) :
    (secondResponseState N β F).2 =
      (initialResponseState N β F).2.transport (route N β) := rfl

/-- Both boundary states retain the original partition normalization. -/
theorem responseState_partitions (N : ℕ) (β : ℝ)
    (F : AssemblyLink N → C(FullField N, ℝ)) :
    (firstResponseState N β F).1.partition = (initialResponseState N β F).1.partition ∧
    (secondResponseState N β F).1.partition = (initialResponseState N β F).1.partition := by
  constructor
  · exact integral_marginal (volume.prod volume) volume (density N β)
  · change (∫ b, marginal volume (marginal volume (density N β)) b ∂volume) = _
    rw [integral_marginal, integral_marginal]
    rfl

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

open WilsonConditionalProjection.PairedHaar SU2BoundaryResponse WilsonLocalResponse
open Mettapedia.Combinatorics.PolymerGas

def wilsonInteraction (n : ℕ) (β : ℝ) : Finset (Link 4 n) → C(Link 4 n → SU2, ℝ) :=
  regroupInteraction support (fun p : Plaquette 4 n ↦ (-β) • plaquetteTrace p)

theorem wilsonInteraction_local (n : ℕ) (β : ℝ) (S : Finset (Link 4 n)) :
    DependsOn S (wilsonInteraction n β S) := by
  apply regroupInteraction_local
  intro p U V h
  exact congrArg (fun x : ℝ ↦ -β * x) (plaquetteTrace_local p U V h)

theorem wilsonInteraction_centered (n : ℕ) (β : ℝ) (S : Finset (Link 4 n)) :
    (∫ U, wilsonInteraction n β S U) = 0 := by
  simp only [wilsonInteraction, regroupInteraction, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply, smul_eq_mul]
  have hi (p : Plaquette 4 n) : Integrable (fun U ↦ -β * plaquetteTrace p U) volume :=
    CompactTransferGap.IntegralKernel.integrable_continuous_fun _
      (continuous_const.mul (plaquetteTrace p).continuous)
  rw [integral_finsetSum _ (fun p _ ↦ hi p)]
  simp only [integral_const_mul, integral_plaquetteTrace_zero, mul_zero, sum_const_zero]

theorem sum_wilsonInteraction (n : ℕ) (β : ℝ) :
    (∑ S, wilsonInteraction n β S) = ∑ p : Plaquette 4 n, (-β) • plaquetteTrace p :=
  sum_regroupInteraction _ _

theorem wilsonInteraction_norm_le (n : ℕ) (β a : ℝ) (ha : 0 ≤ a) :
    interactionNorm a (wilsonInteraction n β) ≤ 64 * |β| * Real.exp (4 * a) := by
  apply interactionNorm_le _ _ (by positivity)
  intro l
  refine (interactionRow_regroup_le support (fun p : Plaquette 4 n ↦ (-β) • plaquetteTrace p) a l).trans ?_
  calc
    _ ≤ ∑ p ∈ univ.filter (fun p : Plaquette 4 n ↦ l ∈ support p), Real.exp (4*a) * |β| := by
      apply sum_le_sum
      intro p _
      have hnorm : ‖(-β) • plaquetteTrace p‖ ≤ |β| := by
        rw [norm_smul, Real.norm_eq_abs, abs_neg]
        exact (mul_le_mul_of_nonneg_left (norm_plaquetteTrace_le p) (abs_nonneg β)).trans_eq (mul_one _)
      have he : Real.exp (a * (support p).card) ≤ Real.exp (4*a) := by
        apply Real.exp_le_exp.mpr
        have hc : ((support p).card : ℝ) ≤ 4 := by exact_mod_cast card_support_le p
        nlinarith
      exact mul_le_mul he hnorm (norm_nonneg _) (Real.exp_pos _).le
    _ ≤ 64 * |β| * Real.exp (4*a) := by
      simp only [sum_const, nsmul_eq_mul]
      have hc : (((univ : Finset (Plaquette 4 n)).filter (fun p ↦ l ∈ support p)).card : ℝ) ≤ 64 := by
        exact_mod_cast card_incident_le 4 n l
      nlinarith [mul_le_mul_of_nonneg_right hc (show 0 ≤ Real.exp (4*a) * |β| by positivity)]

set_option maxHeartbeats 800000 in
/-- Spatial incidence before regrouping, so a designated plaquette remains
an individual source in the exact generated logarithm. -/
theorem wilsonPlaquette_spatial_row_le (n : ℕ) (β a η : ℝ) (ha : 0 ≤ a) (hη : 0 ≤ η)
    (l : Link 4 n) :
    (∑ p ∈ univ.filter (fun p : Plaquette 4 n => l ∈ support p),
      Real.exp (a*(support p).card+η*treeLength (support p)) * ‖(-β) • plaquetteTrace p‖) ≤
        64 * |β| * Real.exp (4*a+4*η) := by
  calc
    _ ≤ ∑ p ∈ univ.filter (fun p : Plaquette 4 n => l ∈ support p), Real.exp (4*a+4*η) * |β| := by
      apply sum_le_sum
      intro p _
      have hn : ‖(-β) • plaquetteTrace p‖ ≤ |β| := by
        rw [norm_smul, Real.norm_eq_abs, abs_neg]
        exact (mul_le_mul_of_nonneg_left (norm_plaquetteTrace_le p) (abs_nonneg β)).trans_eq (mul_one _)
      have he : Real.exp (a * (support p).card + η * treeLength (support p)) ≤ Real.exp (4*a+4*η) := by
        apply Real.exp_le_exp.mpr
        have hc : ((support p).card : ℝ) ≤ 4 := by exact_mod_cast card_support_le p
        have ht := treeLength_support_le p
        nlinarith
      exact mul_le_mul he hn (norm_nonneg _) (Real.exp_pos _).le
    _ ≤ _ := by
      simp only [sum_const, nsmul_eq_mul]
      have hc : (((univ : Finset (Plaquette 4 n)).filter (fun p => l ∈ support p)).card : ℝ) ≤ 64 := by
        exact_mod_cast card_incident_le 4 n l
      nlinarith [mul_le_mul_of_nonneg_right hc (show 0 ≤ Real.exp (4*a+4*η) * |β| by positivity)]


theorem wilsonInteraction_spatial_norm_le (n : ℕ) (β a η : ℝ) (ha : 0 ≤ a) (hη : 0 ≤ η) :
    spatialInteractionNorm a η (wilsonInteraction n β) ≤ 64 * |β| * Real.exp (4*a + 4*η) := by
  apply spatialInteractionNorm_le _ _ _ (by positivity)
  intro l
  exact (weightedInteractionRow_regroup_le support
    (fun p : Plaquette 4 n => (-β) • plaquetteTrace p)
    (fun S => Real.exp (a * S.card + η * treeLength S)) (fun _ => (Real.exp_pos _).le) l).trans
      (wilsonPlaquette_spatial_row_le n β a η ha hη l)

theorem wilsonInteraction_spatial_entry (a η ρ : ℝ) (ha : 0 ≤ a) (hη : 0 ≤ η)
    (n : ℕ) (β : ℝ) (hβ : |β| ≤ ρ / (64 * Real.exp (4*a+4*η))) :
    spatialInteractionNorm a η (wilsonInteraction n β) ≤ ρ := by
  have hp : 0 < 64 * Real.exp (4*a+4*η) := by positivity
  have hh := (le_div_iff₀ hp).mp hβ
  exact (wilsonInteraction_spatial_norm_le n β a η ha hη).trans (by nlinarith)

theorem wilsonInteraction_entry (a ρ : ℝ) (ha : 0 ≤ a)
    (n : ℕ) (β : ℝ) (hβ : |β| ≤ ρ / (64 * Real.exp (4*a))) :
    interactionNorm a (wilsonInteraction n β) ≤ ρ := by
  have hp : 0 < 64 * Real.exp (4*a) := by positivity
  have hh := (le_div_iff₀ hp).mp hβ
  exact (wilsonInteraction_norm_le n β a ha).trans (by nlinarith)

theorem realDensity_eq_wilsonInteraction (n : ℕ) (β : ℝ) (U : Link 4 n → SU2) :
    realDensity (model n univ) (model_continuous n univ) β U =
      Real.exp (-β * Fintype.card (Plaquette 4 n) + (∑ S, wilsonInteraction n β S) U) := by
  rw [sum_wilsonInteraction]
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  change (∏ p, Real.exp (-β * potential ((model n univ).φ p) p U)) = _
  rw [← Real.exp_sum]
  apply congrArg Real.exp
  have he (p : Plaquette 4 n) : potential ((model n univ).φ p) p U = 1 + plaquetteTrace p U := by
    simp only [mem_univ, ↓reduceIte,
      potential, plaquetteEnergy, ContinuousMap.coe_mk, plaquetteTrace,
      SU2WilsonBlockIntegration.traceScore_eq_potential_sub_one]
    ring
  simp_rw [he, mul_add, mul_one]
  simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul]
  ring

namespace ScaleTwo
open WilsonMaxwellBlock
open PairedLinks Mettapedia.Combinatorics.PolymerGas

/-- These are different lattices, with periods `2(n+3)` and `n+3`. -/
abbrev FineConfig (n : ℕ) := Link 4 (doubleIndex n) → SU2
abbrev CoarseConfig (n : ℕ) := Link 4 n → SU2
abbrev Fluctuation (n : ℕ) := CoarseConfig n × (UnusedLink 4 n → SU2)

/-- Keep the first link in each pair as a fluctuation and solve for the
second from its prescribed coarse product. All other links are retained
as independent fluctuation coordinates. -/
def chart (n : ℕ) : (CoarseConfig n × Fluctuation n) ≃ᵐ FineConfig n :=
  PairedLinks.chart (blockIndexEquiv 4 n)

@[simp] theorem chart_first (n : ℕ) (p : CoarseConfig n × Fluctuation n) (l : Link 4 n) :
    chart n p (blockEdge l 0) = p.2.1 l := by
  exact (congrArg (chart n p) (blockIndexEquiv_first l).symm).trans
    (PairedLinks.chart_first (E := SU2) (blockIndexEquiv 4 n) p l)

@[simp] theorem chart_second (n : ℕ) (p : CoarseConfig n × Fluctuation n) (l : Link 4 n) :
    chart n p (blockEdge l 1) = (p.2.1 l)⁻¹ * p.1 l := by
  exact (congrArg (chart n p) (blockIndexEquiv_second l).symm).trans
    (PairedLinks.chart_second (E := SU2) (blockIndexEquiv 4 n) p l)

@[simp] theorem chart_unused (n : ℕ) (p : CoarseConfig n × Fluctuation n) (l : UnusedLink 4 n) :
    chart n p l.val = p.2.2 l := by
  exact (congrArg (chart n p) (blockIndexEquiv_unused l).symm).trans
    (PairedLinks.chart_unused (E := SU2) (blockIndexEquiv 4 n) p l)

theorem paired_block_eq (n : ℕ) (U : FineConfig n) :
    PairedLinks.block (blockIndexEquiv 4 n) U = blockField (d := 4) (n := n) U := by
  funext l
  change U (blockIndexEquiv 4 n (.inl (.inl l))) *
    U (blockIndexEquiv 4 n (.inl (.inr l))) = _
  rw [blockIndexEquiv_first, blockIndexEquiv_second]
  rfl

@[simp] theorem block_chart (n : ℕ) (p : CoarseConfig n × Fluctuation n) :
    blockField (d := 4) (n := n) (E := SU2) (chart n p) = p.1 := by
  rw [← paired_block_eq]
  exact PairedLinks.block_chart (E := SU2) (blockIndexEquiv 4 n) p


/-- Correct a fine curve to the identity coarse fiber using the existing Haar chart. -/
def identityFiberCurve (n : ℕ) (U : ℝ → FineConfig n) (t : ℝ) : FineConfig n :=
  chart n (1, (fun l => U t (blockEdge l 0), fun l => U t l.val))

@[simp] theorem block_identityFiberCurve (n : ℕ) (U : ℝ → FineConfig n) (t : ℝ) :
    blockField (identityFiberCurve n U t) = 1 := by
  exact block_chart n _

theorem identityFiberCurve_zero {n : ℕ} (U : ℝ → FineConfig n) (hzero : ∀ l, U 0 l = 1) :
    identityFiberCurve n U 0 = 1 := by
  funext l
  obtain ⟨r, rfl⟩ := (blockIndexEquiv 4 n).surjective l
  rcases r with (r | r) | r <;>
    simp only [blockIndexEquiv_first, blockIndexEquiv_second, blockIndexEquiv_unused,
      identityFiberCurve, chart_first, chart_second, chart_unused, hzero, Pi.one_apply, inv_one, mul_one]

open scoped Matrix.Norms.Elementwise in
/-- The kernel of Q is exactly the derivative constraint of the true Haar fiber,
for tangent data realized by differentiable SU(2) paths. -/
theorem hasDerivAt_identityFiberCurve {n : ℕ} (U : ℝ → FineConfig n)
    (A : Link 4 (doubleIndex n) → Matrix (Fin 2) (Fin 2) ℂ)
    (hzero : ∀ l, U 0 l = 1)
    (hderiv : ∀ l, HasDerivAt (fun t => (U t l).val) (A l) 0)
    (hQ : linearBlock A = 0) (l : Link 4 (doubleIndex n)) :
    HasDerivAt (fun t => (identityFiberCurve n U t l).val) (A l) 0 := by
  obtain ⟨r, rfl⟩ := (blockIndexEquiv 4 n).surjective l
  rcases r with (r | r) | r
  · simpa only [identityFiberCurve, blockIndexEquiv_first, chart_first] using hderiv (blockEdge r 0)
  · have h := (hderiv (blockEdge r 0)).star
    have hpair : A (blockEdge r 0) + A (blockEdge r 1) = 0 := congrFun hQ r
    have he : star (A (blockEdge r 0)) = A (blockEdge r 1) := by
      rw [tangent_star_eq_neg (hzero _) (hderiv _)]
      exact (eq_neg_of_add_eq_zero_right hpair).symm
    rw [he] at h
    simp only [identityFiberCurve, blockIndexEquiv_second, chart_second, Pi.one_apply, mul_one,
      ← Matrix.star_eq_inv, Matrix.specialUnitaryGroup.coe_star]
    convert h using 1 <;> rfl
  · simpa only [identityFiberCurve, blockIndexEquiv_unused, chart_unused] using hderiv r.val


theorem measurePreserving_chart (n : ℕ) :
    MeasurePreserving (chart n)
      ((volume : Measure (CoarseConfig n)).prod (volume : Measure (Fluctuation n)))
      (volume : Measure (FineConfig n)) := by
  change MeasurePreserving (PairedLinks.chart (E := SU2) (blockIndexEquiv 4 n))
    ((Measure.pi fun _ : Link 4 n ↦ (volume : Measure SU2)).prod
      ((Measure.pi fun _ : Link 4 n ↦ (volume : Measure SU2)).prod
        (Measure.pi fun _ : UnusedLink 4 n ↦ (volume : Measure SU2))))
    (Measure.pi fun _ : Link 4 (doubleIndex n) ↦ (volume : Measure SU2))
  exact PairedLinks.measurePreserving_chart (volume : Measure SU2) (blockIndexEquiv 4 n)

theorem measurePreserving_blockField (n : ℕ) :
    MeasurePreserving (blockField (d := 4) (n := n) (E := SU2))
      (volume : Measure (FineConfig n)) (volume : Measure (CoarseConfig n)) :=
  PairedLinks.measurePreserving_block (volume : Measure SU2) (blockIndexEquiv 4 n)

/-- Every elementary plaquette of the fine torus appears in this weight. -/
def fineDensity (n : ℕ) (β : ℝ) : C(FineConfig n, ℝ) :=
  WilsonLocalResponse.realDensity (SU2BoundaryResponse.model (doubleIndex n) univ)
    (SU2BoundaryResponse.model_continuous (doubleIndex n) univ) β

theorem fineDensity_pos (n : ℕ) (β : ℝ) : ∀ U, 0 < fineDensity n β U :=
  WilsonLocalResponse.realDensity_pos (SU2BoundaryResponse.model (doubleIndex n) univ)
    (SU2BoundaryResponse.model_continuous (doubleIndex n) univ) β

section QuadraticDensity
open Filter
open scoped Matrix.Norms.Elementwise
variable {n : ℕ}

theorem neg_log_fineDensity (n : ℕ) (β : ℝ) (U : FineConfig n) :
    -Real.log (fineDensity n β U) = β * ∑ p : Plaquette 4 (doubleIndex n),
      SU2WilsonBlockIntegration.potential (holonomy (fun i => U (linkAt p i))) := by
  simp only [fineDensity, WilsonLocalResponse.realDensity, model,
    InhomogeneousWilsonCrossing.Model.masked, potential, plaquetteEnergy,
    ContinuousMap.coe_mk, Finset.mem_univ, ↓reduceIte]
  rw [← Real.exp_sum, Real.log_exp]
  simp only [← Finset.mul_sum]
  ring

theorem tendsto_fineDensity_quadratic (β : ℝ) (U : ℝ → FineConfig n)
    (A : Link 4 (doubleIndex n) → Fin 3 → ℝ) (hzero : ∀ l, U 0 l = 1)
    (hderiv : ∀ l, HasDerivAt (fun t => (U t l).val) (pauliTangent (A l)) 0) :
    Tendsto (fun t => -Real.log (fineDensity n β (U t)) / t^2) (𝓝[≠] 0)
      (𝓝 (β/2 * ∑ i : Fin 3, curlEnergy (fun l => A l i))) := by
  have hs := tendsto_finsetSum (Finset.univ : Finset (Plaquette 4 (doubleIndex n)))
    (fun p _ => tendsto_wilsonPlaquette_quadratic U A hzero hderiv p)
  have hm := (tendsto_const_nhds (x := β)).mul hs
  have he : (∑ p : Plaquette 4 (doubleIndex n), (1/2:ℝ) * ∑ i : Fin 3,
      (curl (fun l => A l i) p)^2) = (1/2:ℝ) * ∑ i : Fin 3, curlEnergy (fun l => A l i) := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    rfl
  rw [he] at hm
  convert hm using 1
  · funext t
    rw [neg_log_fineDensity, ← Finset.sum_div]
    ring
  · congr 1
    ring

/-- The actual fine Wilson density has the Maxwell leading term along the
nonlinear Haar chart at fixed identity coarse field. -/
theorem tendsto_identityFiberDensity_quadratic (β : ℝ) (U : ℝ → FineConfig n)
    (A : Link 4 (doubleIndex n) → Fin 3 → ℝ) (hzero : ∀ l, U 0 l = 1)
    (hderiv : ∀ l, HasDerivAt (fun t => (U t l).val) (pauliTangent (A l)) 0)
    (hQ : linearBlock (fun l => pauliTangent (A l)) = 0) :
    Tendsto (fun t => -Real.log (fineDensity n β (identityFiberCurve n U t)) / t^2) (𝓝[≠] 0)
      (𝓝 (β/2 * ∑ i : Fin 3, curlEnergy (fun l => A l i))) := by
  exact tendsto_fineDensity_quadratic β (identityFiberCurve n U) A
    (fun l => congrFun (identityFiberCurve_zero U hzero) l)
    (hasDerivAt_identityFiberCurve U (fun l => pauliTangent (A l)) hzero hderiv hQ)

end QuadraticDensity

/-- The full scale-two effective Wilson weight, without action extraction. -/
def coarseDensity (n : ℕ) (β : ℝ) : C(CoarseConfig n, ℝ) :=
  PairedLinks.blockedDensity (volume : Measure SU2) (blockIndexEquiv 4 n) (fineDensity n β)

theorem coarseDensity_pos (n : ℕ) (β : ℝ) : ∀ c, 0 < coarseDensity n β c :=
  PairedLinks.blockedDensity_pos (volume : Measure SU2) (blockIndexEquiv 4 n)
    (fineDensity n β) (fineDensity_pos n β)

section ConditionalQuadraticDensity
open Filter
open scoped Matrix.Norms.Elementwise
variable {n : ℕ}

theorem fineDensity_one (n : ℕ) (β : ℝ) : fineDensity n β 1 = 1 := by
  simp [fineDensity, WilsonLocalResponse.realDensity, model,
    InhomogeneousWilsonCrossing.Model.masked, potential, plaquetteEnergy,
    holonomy, SU2WilsonBlockIntegration.potential, specialUnitaryWilsonPotential,
    Matrix.trace, Fin.sum_univ_two]

/-- Subtracting the reference action removes the exact coarse normalizer.
The density here is relative to the fluctuation Haar measure. -/
theorem conditionalAction_sub_identity (n : ℕ) (β : ℝ) (U : FineConfig n) :
    -Real.log (fineDensity n β U / coarseDensity n β 1) +
      Real.log (fineDensity n β 1 / coarseDensity n β 1) =
      -Real.log (fineDensity n β U) := by
  rw [fineDensity_one, Real.log_div (fineDensity_pos n β U).ne' (coarseDensity_pos n β 1).ne',
    Real.log_div one_ne_zero (coarseDensity_pos n β 1).ne', Real.log_one]
  ring

/-- The centered action of the normalized conditional Haar law has the same
quadratic coefficient. No coordinate Jacobian or nonlinear error estimate is asserted. -/
theorem tendsto_conditionalAction_quadratic (β : ℝ) (U : ℝ → FineConfig n)
    (A : Link 4 (doubleIndex n) → Fin 3 → ℝ) (hzero : ∀ l, U 0 l = 1)
    (hderiv : ∀ l, HasDerivAt (fun t => (U t l).val) (pauliTangent (A l)) 0)
    (hQ : linearBlock (fun l => pauliTangent (A l)) = 0) :
    Tendsto (fun t => (-Real.log (fineDensity n β (identityFiberCurve n U t) /
      coarseDensity n β 1) + Real.log (fineDensity n β 1 / coarseDensity n β 1)) / t^2)
      (𝓝[≠] 0) (𝓝 (β/2 * ∑ i : Fin 3, curlEnergy (fun l => A l i))) := by
  simp_rw [conditionalAction_sub_identity]
  exact tendsto_identityFiberDensity_quadratic β U A hzero hderiv hQ

end ConditionalQuadraticDensity

def projected (n : ℕ) (β : ℝ) (F : C(FineConfig n, ℝ)) : C(CoarseConfig n, ℝ) :=
  PairedLinks.blockedProject (volume : Measure SU2) (blockIndexEquiv 4 n)
    (fineDensity n β) (fineDensity_pos n β) F

theorem partition_preserved (n : ℕ) (β : ℝ) :
    (∫ c, coarseDensity n β c) = ∫ U, fineDensity n β U :=
  PairedLinks.integral_blockedDensity (volume : Measure SU2) (blockIndexEquiv 4 n)
    (fineDensity n β)

theorem expectation_preserved (n : ℕ) (β : ℝ) (F : C(FineConfig n, ℝ)) :
    expectation volume (coarseDensity n β) (projected n β F) =
      expectation volume (fineDensity n β) F :=
  PairedLinks.expectation_blockedProject (volume : Measure SU2) (blockIndexEquiv 4 n)
    (fineDensity n β) (fineDensity_pos n β) F

/-- Coarse-product observables survive exactly and are not discarded by
elimination. Nonzero such observables therefore cannot have a strict
uniform projection factor in the sup norm. -/
theorem projected_blockObservable (n : ℕ) (β : ℝ) (F : C(CoarseConfig n, ℝ)) :
    projected n β (F.comp (PairedLinks.blockMap (blockIndexEquiv 4 n))) = F :=
  PairedLinks.blockedProject_lift (volume : Measure SU2) (blockIndexEquiv 4 n)
    (fineDensity n β) (fineDensity_pos n β) F

/-- The scale change has the same exact weighted route semantics as the
original-lattice integrations, with a genuinely different configuration space. -/
def integrationStep (n : ℕ) (β : ℝ) :
    WilsonEliminationRoutes.Step
      (WilsonProjectionComposition.coordinateState (volume : Measure SU2)
        (fineDensity n β) (fineDensity_pos n β))
      (WilsonProjectionComposition.coordinateState (volume : Measure SU2)
        (coarseDensity n β) (coarseDensity_pos n β)) :=
  WilsonProjectionComposition.blockedStep (volume : Measure SU2) (blockIndexEquiv 4 n)
    (fineDensity n β) (fineDensity_pos n β)

/-- The fluctuation coordinates transform at their original fine endpoints. -/
def fluctuationGauge (n : ℕ) (g : Site 4 (doubleIndex n) → SU2)
    (f : Fluctuation n) : Fluctuation n :=
  (fun l ↦ g (doubleSite l.1) * f.1 l * (g (doubleSite l.1 + StrongCouplingCrossing.step l.2))⁻¹,
   fun l ↦ g l.val.1 * f.2 l * (g (l.val.1 + StrongCouplingCrossing.step l.val.2))⁻¹)

theorem chart_gauge (n : ℕ) (g : Site 4 (doubleIndex n) → SU2)
    (c : CoarseConfig n) (f : Fluctuation n) :
    chart n (WilsonDyadicGeometry.gaugeAct (fun x ↦ g (doubleSite x)) c, fluctuationGauge n g f) =
      WilsonDyadicGeometry.gaugeAct g (chart n (c, f)) := by
  funext l
  obtain ⟨s, rfl⟩ := (blockIndexEquiv 4 n).surjective l
  rcases s with (i | i) | j
  · rw [blockIndexEquiv_first]
    rw [chart_first]
    dsimp only [WilsonDyadicGeometry.gaugeAct]
    rw [chart_first]
    simp only [blockEdge_zero, fluctuationGauge]
  · rw [blockIndexEquiv_second]
    rw [chart_second]
    dsimp only [WilsonDyadicGeometry.gaugeAct]
    rw [chart_second]
    simp only [fluctuationGauge, blockEdge_one, doubleSite_add, doubleSite_step, ← add_assoc]
    group
  · simp only [blockIndexEquiv_unused, WilsonDyadicGeometry.gaugeAct, chart_unused,
      fluctuationGauge]

theorem measurePreserving_fluctuationGauge (n : ℕ) (g : Site 4 (doubleIndex n) → SU2) :
    MeasurePreserving (fluctuationGauge n g) (volume : Measure (Fluctuation n)) volume := by
  have hfirst : MeasurePreserving
      (fun a : CoarseConfig n ↦ fun l ↦
        g (doubleSite l.1) * a l * (g (doubleSite l.1 + StrongCouplingCrossing.step l.2))⁻¹)
      (volume : Measure (CoarseConfig n)) volume := by
    exact measurePreserving_pi (fun _ ↦ (volume : Measure SU2)) (fun _ ↦ volume)
      (fun l ↦ (measurePreserving_mul_right volume _).comp (measurePreserving_mul_left volume _))
  have hunused : MeasurePreserving
      (fun a : UnusedLink 4 n → SU2 ↦ fun l ↦
        g l.val.1 * a l * (g (l.val.1 + StrongCouplingCrossing.step l.val.2))⁻¹)
      (volume : Measure (UnusedLink 4 n → SU2)) volume := by
    exact measurePreserving_pi (fun _ ↦ (volume : Measure SU2)) (fun _ ↦ volume)
      (fun l ↦ (measurePreserving_mul_right volume _).comp (measurePreserving_mul_left volume _))
  exact hfirst.prod hunused

theorem fineDensity_gauge (n : ℕ) (β : ℝ)
    (g : Site 4 (doubleIndex n) → SU2) (U : FineConfig n) :
    fineDensity n β (WilsonDyadicGeometry.gaugeAct g U) = fineDensity n β U := by
  apply Finset.prod_congr rfl
  intro p _
  have he := (specialUnitaryWilsonPotential (Fin 2)).conjugation_invariant
    (g p.1) (holonomy (fun i ↦ U (linkAt p i)))
  simp only [SU2BoundaryResponse.model, InhomogeneousWilsonCrossing.Model.masked,
    Finset.mem_univ, ↓reduceIte, StrongCouplingCrossing.potential,
    SU2BoundaryResponse.plaquetteEnergy, ContinuousMap.coe_mk,
    WilsonDyadicGeometry.holonomy_gaugeAct]
  exact congrArg (fun x : ℝ ↦ Real.exp (-β * x)) he

/-- Exact gauge transport for any continuous generated fine interaction,
not only for the initial Wilson product. -/
theorem blockedDensity_gauge_restriction (n : ℕ) (F : C(FineConfig n, ℝ))
    (g : Site 4 (doubleIndex n) → SU2)
    (hF : ∀ U, F (WilsonDyadicGeometry.gaugeAct g U) = F U) (c : CoarseConfig n) :
    blockedDensity (volume : Measure SU2) (blockIndexEquiv 4 n) F
      (WilsonDyadicGeometry.gaugeAct (fun x ↦ g (doubleSite x)) c) =
    blockedDensity (volume : Measure SU2) (blockIndexEquiv 4 n) F c := by
  let gc := WilsonDyadicGeometry.gaugeAct (fun x ↦ g (doubleSite x)) c
  let H : C(Fluctuation n, ℝ) :=
    ⟨fun f ↦ F (chart n (gc, f)), F.continuous.comp
      ((continuous_chart (E := SU2) (blockIndexEquiv 4 n)).comp
        (continuous_const.prodMk continuous_id))⟩
  have hm := measurePreserving_fluctuationGauge n g
  have hi := integral_map_of_stronglyMeasurable (μ := (volume : Measure (Fluctuation n)))
    hm.measurable H.continuous.stronglyMeasurable
  rw [hm.map_eq] at hi
  change (∫ f, H f) = ∫ f, F (chart n (c, f))
  rw [hi]
  apply integral_congr_ae
  filter_upwards [] with f
  change F (chart n (gc, fluctuationGauge n g f)) = _
  rw [chart_gauge, hF]

theorem blockedDensity_gauge (n : ℕ) (F : C(FineConfig n, ℝ))
    (hF : ∀ (g : Site 4 (doubleIndex n) → SU2) U,
      F (WilsonDyadicGeometry.gaugeAct g U) = F U)
    (g : Site 4 n → SU2) (c : CoarseConfig n) :
    blockedDensity (volume : Measure SU2) (blockIndexEquiv 4 n) F
      (WilsonDyadicGeometry.gaugeAct g c) =
    blockedDensity (volume : Measure SU2) (blockIndexEquiv 4 n) F c := by
  let gf : Site 4 (doubleIndex n) → SU2 :=
    Function.extend (doubleSite (d := 4) (n := n)) g (fun _ ↦ 1)
  have hg : (fun x ↦ gf (doubleSite x)) = g :=
    funext fun x ↦ doubleSite_injective.extend_apply g (fun _ ↦ 1) x
  have h := blockedDensity_gauge_restriction n F gf (hF gf) c
  rw [hg] at h
  exact h


/-- Gauge covariance and Haar invariance specialize to the Wilson density. -/
theorem coarseDensity_gauge_restriction (n : ℕ) (β : ℝ)
    (g : Site 4 (doubleIndex n) → SU2) (c : CoarseConfig n) :
    coarseDensity n β (WilsonDyadicGeometry.gaugeAct (fun x ↦ g (doubleSite x)) c) =
      coarseDensity n β c := by
  exact blockedDensity_gauge_restriction n (fineDensity n β) g (fineDensity_gauge n β g) c

theorem coarseDensity_gauge (n : ℕ) (β : ℝ)
    (g : Site 4 n → SU2) (c : CoarseConfig n) :
    coarseDensity n β (WilsonDyadicGeometry.gaugeAct g c) = coarseDensity n β c := by
  exact blockedDensity_gauge n (fineDensity n β) (fineDensity_gauge n β) g c


variable {n : ℕ}

open SU2BoundaryResponse

/-- Coarse rotations lift to the second half of each ordered path. -/
def liftPatch (S : Finset (Link 4 n)) : Finset (Link 4 (doubleIndex n)) :=
  S.image (fun l ↦ blockEdge l 1)

@[simp] theorem mem_liftPatch_second (S : Finset (Link 4 n)) (l : Link 4 n) :
    blockEdge l 1 ∈ liftPatch S ↔ l ∈ S := by
  constructor
  · rintro h
    obtain ⟨k, hk, he⟩ := mem_image.mp h
    have hkl := congrArg Prod.fst (@blockEdge_injective 4 n (k, 1) (l, 1) he)
    change k = l at hkl
    exact hkl ▸ hk
  · intro h
    exact mem_image.mpr ⟨l, h, rfl⟩

@[simp] theorem not_mem_liftPatch_first (S : Finset (Link 4 n)) (l : Link 4 n) :
    blockEdge l 0 ∉ liftPatch S := by
  rintro h
  obtain ⟨k, _, he⟩ := mem_image.mp h
  have hf := congrArg Prod.snd (@blockEdge_injective 4 n (k, 1) (l, 0) he)
  exact (by decide : (1 : Fin 2) ≠ 0) hf

@[simp] theorem not_mem_liftPatch_unused (S : Finset (Link 4 n)) (l : UnusedLink 4 n) :
    l.val ∉ liftPatch S := by
  rintro h
  obtain ⟨k, _, he⟩ := mem_image.mp h
  exact l.property ⟨.inr k, he⟩

@[simp] theorem card_liftPatch (S : Finset (Link 4 n)) : (liftPatch S).card = S.card := by
  apply card_image_of_injective
  intro l k h
  exact congrArg Prod.fst (@blockEdge_injective 4 n (l, 1) (k, 1) h)

def liftFrame (q : CoarseConfig n) (f : Fluctuation n) : FineConfig n :=
  fun l ↦ match (blockIndexEquiv 4 n).symm l with
    | .inl (.inr k) => (f.1 k)⁻¹ * q k
    | _ => 1

@[simp] theorem liftFrame_second (q : CoarseConfig n) (f : Fluctuation n) (l : Link 4 n) :
    liftFrame q f (blockEdge l 1) = (f.1 l)⁻¹ * q l := by
  rw [← blockIndexEquiv_second]
  simp only [liftFrame, Equiv.symm_apply_apply]

theorem continuous_liftFrame (q : CoarseConfig n) : Continuous (liftFrame q) := by
  apply continuous_pi
  intro l
  dsimp only [liftFrame]
  split <;> fun_prop

theorem chart_boundaryCurve (S : Finset (Link 4 n)) (q c : CoarseConfig n)
    (f : Fluctuation n) (t : ℝ) :
    chart n (boundaryCurve S q c t, f) =
      boundaryCurve (liftPatch S) (liftFrame q f) (chart n (c, f)) t := by
  funext l
  obtain ⟨s, rfl⟩ := (blockIndexEquiv 4 n).surjective l
  rcases s with (i | i) | j
  · rw [blockIndexEquiv_first, chart_first]
    simp only [boundaryCurve, not_mem_liftPatch_first, ↓reduceIte, chart_first]
  · rw [blockIndexEquiv_second, chart_second]
    simp only [boundaryCurve, mem_liftPatch_second, chart_second, liftFrame_second]
    by_cases h : i ∈ S
    · simp only [h, ↓reduceIte, rotationPerturbation]
      group
    · simp only [h, ↓reduceIte]
  · rw [blockIndexEquiv_unused, chart_unused]
    simp only [boundaryCurve, not_mem_liftPatch_unused, ↓reduceIte, chart_unused]


open WilsonConditionalProjection.PairedHaar SU2BoundaryResponse

theorem retainedSupport_plaquette (p : Plaquette 4 (doubleIndex n)) :
    retainedSupport (blockIndexEquiv 4 n) (support p) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro l hl
  obtain ⟨h0, h1⟩ := (mem_retainedSupport _ _ _).mp hl
  rw [blockIndexEquiv_first] at h0
  rw [blockIndexEquiv_second] at h1
  exact no_blockPair_in_support p l ⟨h0, h1⟩

theorem blocked_plaquetteTrace_eq_zero (p : Plaquette 4 (doubleIndex n)) :
    PairedLinks.blockedDensity (volume : Measure SU2) (blockIndexEquiv 4 n) (plaquetteTrace p) = 0 :=
  blockedDensity_eq_zero volume (blockIndexEquiv 4 n) (support p) (plaquetteTrace p)
    (plaquetteTrace_local p) (integral_plaquetteTrace_zero p) (retainedSupport_plaquette p)

def retainedWilsonObservable (p : Plaquette 4 n) : C(FineConfig n, ℝ) :=
  (plaquetteTrace p).comp (PairedLinks.blockMap (blockIndexEquiv 4 n))

@[simp] theorem projected_retainedWilsonObservable (β : ℝ) (p : Plaquette 4 n) :
    projected n β (retainedWilsonObservable p) = plaquetteTrace p :=
  projected_blockObservable n β (plaquetteTrace p)

theorem projected_retainedWilsonObservable_ne_zero (β : ℝ) (p : Plaquette 4 n) :
    projected n β (retainedWilsonObservable p) ≠ 0 := by
  intro h
  have he := congrArg (fun F : C(CoarseConfig n, ℝ) ↦ F (fun _ ↦ 1)) h
  rw [projected_retainedWilsonObservable, plaquetteTrace_one] at he
  norm_num at he

theorem integral_retainedWilsonObservable_zero (p : Plaquette 4 n) :
    (∫ U, retainedWilsonObservable p U) = 0 := by
  have hm := measurePreserving_blockField n
  have hi := integral_map_of_stronglyMeasurable (μ := (volume : Measure (FineConfig n)))
    hm.measurable (plaquetteTrace p).continuous.stronglyMeasurable
  rw [hm.map_eq] at hi
  exact hi.symm.trans (integral_plaquetteTrace_zero p)

def rectangleSupport (p : Plaquette 4 n) : Finset (Link 4 (doubleIndex n)) :=
  (support p).biUnion (fun l ↦ {blockEdge l 0, blockEdge l 1})

theorem retainedWilsonObservable_local (p : Plaquette 4 n) :
    WilsonLocalResponse.DependsOn (rectangleSupport p) (retainedWilsonObservable p) := by
  intro U V h
  apply plaquetteTrace_local p
  intro l hl
  change U (blockEdge l 0) * U (blockEdge l 1) = V (blockEdge l 0) * V (blockEdge l 1)
  rw [h _ (mem_biUnion.mpr ⟨l, hl, by simp⟩), h _ (mem_biUnion.mpr ⟨l, hl, by simp⟩)]

theorem plaquetteTrace_gauge (p : Plaquette 4 n) (g : Site 4 n → SU2) (U : CoarseConfig n) :
    plaquetteTrace p (WilsonDyadicGeometry.gaugeAct g U) = plaquetteTrace p U := by
  change SU2WilsonBlockIntegration.traceScore (holonomy (fun i ↦
    WilsonDyadicGeometry.gaugeAct g U (linkAt p i))) = _
  rw [holonomy_gaugeAct, SU2WilsonBlockIntegration.traceScore_eq_potential_sub_one]
  change _ = SU2WilsonBlockIntegration.traceScore _
  rw [SU2WilsonBlockIntegration.traceScore_eq_potential_sub_one]
  exact congrArg (fun x : ℝ ↦ x - 1)
    ((specialUnitaryWilsonPotential (Fin 2)).conjugation_invariant (g p.1) _)

theorem retainedWilsonObservable_gauge (p : Plaquette 4 n)
    (g : Site 4 (doubleIndex n) → SU2) (U : FineConfig n) :
    retainedWilsonObservable p (WilsonDyadicGeometry.gaugeAct g U) = retainedWilsonObservable p U := by
  change plaquetteTrace p (blockField (WilsonDyadicGeometry.gaugeAct g U)) = plaquetteTrace p (blockField U)
  rw [blockField_gaugeAct]
  exact plaquetteTrace_gauge p _ _

theorem blocked_wilsonInteraction_zero (n : ℕ) (β : ℝ) :
    blockedInteraction (volume : Measure SU2) (WilsonDyadicGeometry.blockIndexEquiv 4 n)
      (wilsonInteraction (WilsonDyadicGeometry.doubleIndex n) β) = 0 := by
  funext T
  unfold blockedInteraction regroupInteraction
  apply Finset.sum_eq_zero
  intro S _
  change (blockedDensityLinear (volume : Measure SU2) (WilsonDyadicGeometry.blockIndexEquiv 4 n))
    (∑ p ∈ univ.filter (fun p : Plaquette 4 (WilsonDyadicGeometry.doubleIndex n) ↦ support p = S),
      (-β) • plaquetteTrace p) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro p _
  rw [map_smul]
  change (-β) • WilsonBlockElimination.PairedLinks.blockedDensity
    (volume : Measure SU2) (WilsonDyadicGeometry.blockIndexEquiv 4 n) (plaquetteTrace p) = 0
  rw [blocked_plaquetteTrace_eq_zero, smul_zero]

/-! The dependency geometry for integration uses the independent fluctuation
coordinates. Both halves of a coarse link share one such coordinate. -/

abbrev FluctuationLink (n : ℕ) := Link 4 n ⊕ UnusedLink 4 n

instance fluctuationFintype (n : ℕ) : Fintype (FluctuationLink n) :=
  inferInstanceAs (Fintype (Link 4 n ⊕ UnusedLink 4 n))

instance fluctuationPseudoMetricSpace (n : ℕ) : PseudoMetricSpace (FluctuationLink n) :=
  PseudoMetricSpace.induced (fluctuationRepresentative (blockIndexEquiv 4 n)) inferInstance

def fluctuationPlaquetteSupport {n : ℕ} (p : Plaquette 4 (doubleIndex n)) : Finset (FluctuationLink n) :=
  fluctuationSupport (blockIndexEquiv 4 n) (support p)

theorem fluctuationPlaquetteSupport_nonempty {n : ℕ} (p : Plaquette 4 (doubleIndex n)) :
    (fluctuationPlaquetteSupport p).Nonempty := fluctuationSupport_nonempty _ (support_nonempty p)

theorem card_fluctuationPlaquetteSupport_le {n : ℕ} (p : Plaquette 4 (doubleIndex n)) :
    (fluctuationPlaquetteSupport p).card ≤ 4 := (card_fluctuationSupport_le _ _).trans (card_support_le p)

theorem dist_fluctuationRepresentative_le {n : ℕ} (x : Link 4 (doubleIndex n)) :
    dist x (fluctuationRepresentative (blockIndexEquiv 4 n) (fluctuationIndex (blockIndexEquiv 4 n) x)) ≤ 1 := by
  obtain ⟨s, rfl⟩ := (blockIndexEquiv 4 n).surjective x
  rcases s with (i | i) | j
  · change dist ((blockIndexEquiv 4 n) (.inl (.inl i)))
      (fluctuationRepresentative (blockIndexEquiv 4 n)
        (fluctuationIndex (blockIndexEquiv 4 n) ((blockIndexEquiv 4 n) (.inl (.inl i))))) ≤ 1
    rw [fluctuationIndex_first]
    simp only [fluctuationRepresentative, dist_self]
    norm_num
  · change dist ((blockIndexEquiv 4 n) (.inl (.inr i)))
      (fluctuationRepresentative (blockIndexEquiv 4 n)
        (fluctuationIndex (blockIndexEquiv 4 n) ((blockIndexEquiv 4 n) (.inl (.inr i))))) ≤ 1
    rw [fluctuationIndex_second]
    simp only [fluctuationRepresentative, blockIndexEquiv_first, blockIndexEquiv_second]
    rw [dist_comm]
    exact dist_blockEdge_halves_le i
  · change dist ((blockIndexEquiv 4 n) (.inr j))
      (fluctuationRepresentative (blockIndexEquiv 4 n)
        (fluctuationIndex (blockIndexEquiv 4 n) ((blockIndexEquiv 4 n) (.inr j)))) ≤ 1
    rw [fluctuationIndex_unused]
    simp only [fluctuationRepresentative, dist_self]
    norm_num

theorem diam_fluctuationPlaquetteSupport_le {n : ℕ} (p : Plaquette 4 (doubleIndex n)) :
    polymerDiam (fluctuationPlaquetteSupport p) ≤ 3 := by
  have h := diam_fluctuationSupport_le (blockIndexEquiv 4 n) (by norm_num : (0 : ℝ) ≤ 1)
    dist_fluctuationRepresentative_le (support p)
  exact h.trans (by linarith [diam_support_le p])

set_option maxHeartbeats 400000 in
theorem card_incident_fluctuationPlaquetteSupport_le (n : ℕ) (y : FluctuationLink n) :
    ((univ : Finset (Plaquette 4 (doubleIndex n))).filter
      (fun p ↦ y ∈ fluctuationPlaquetteSupport p)).card ≤ 128 := by
  have hD (x : Link 4 (doubleIndex n)) :
      ((univ : Finset (Plaquette 4 (doubleIndex n))).filter (fun p ↦ x ∈ support p)).card ≤ 64 := by
    exact card_incident_le 4 (doubleIndex n) x
  have hh := card_incident_fluctuationSupport_le (Pl := Plaquette 4 (doubleIndex n))
    (D := 64) (blockIndexEquiv 4 n) support hD y
  convert hh using 1
  congr 1
  unfold fluctuationPlaquetteSupport
  congr 1

/-! A pair of scale changes has independent coordinates from both fibers.
The representatives live on the original lattice, so separation is measured
before either elimination. -/

abbrev TwoFluctuationLink (n : ℕ) := FluctuationLink (doubleIndex n) ⊕ FluctuationLink n

instance twoFluctuationPseudoMetricSpace (n : ℕ) : PseudoMetricSpace (TwoFluctuationLink n) :=
  PseudoMetricSpace.induced
    (twoFluctuationRepresentative (blockIndexEquiv 4 (doubleIndex n)) (blockIndexEquiv 4 n)) inferInstance

theorem dist_second_outerRepresentative_le {n : ℕ} (i : Link 4 (doubleIndex n)) :
    dist ((blockIndexEquiv 4 (doubleIndex n)) (.inl (.inr i)))
      ((blockIndexEquiv 4 (doubleIndex n)) (.inl (.inl
        (fluctuationRepresentative (blockIndexEquiv 4 n) (fluctuationIndex (blockIndexEquiv 4 n) i))))) ≤ 3 := by
  simp only [blockIndexEquiv_first, blockIndexEquiv_second]
  let v := fluctuationRepresentative (blockIndexEquiv 4 n) (fluctuationIndex (blockIndexEquiv 4 n) i)
  change dist (blockEdge i 1) (blockEdge v 0) ≤ 3
  have ht := dist_triangle (blockEdge i 1) (blockEdge i 0) (blockEdge v 0)
  rw [dist_blockEdge_zero, dist_comm (blockEdge i 1) (blockEdge i 0)] at ht
  have hs : dist i v ≤ 1 := dist_fluctuationRepresentative_le i
  linarith [dist_blockEdge_halves_le i]

def twoFluctuationPlaquetteSupport {n : ℕ} (p : Plaquette 4 (doubleIndex (doubleIndex n))) :
    Finset (TwoFluctuationLink n) :=
  twoFluctuationSupport (blockIndexEquiv 4 (doubleIndex n)) (blockIndexEquiv 4 n) (support p)

theorem twoFluctuationPlaquetteSupport_nonempty {n : ℕ}
    (p : Plaquette 4 (doubleIndex (doubleIndex n))) : (twoFluctuationPlaquetteSupport p).Nonempty :=
  twoFluctuationSupport_nonempty _ _ (support_nonempty p)

theorem card_twoFluctuationPlaquetteSupport_le {n : ℕ}
    (p : Plaquette 4 (doubleIndex (doubleIndex n))) : (twoFluctuationPlaquetteSupport p).card ≤ 8 := by
  have h := card_twoFluctuationSupport_le (blockIndexEquiv 4 (doubleIndex n)) (blockIndexEquiv 4 n) (support p)
  have hc := card_support_le p
  change (twoFluctuationSupport _ _ _).card ≤ 8
  omega

theorem diam_twoFluctuationPlaquetteSupport_le {n : ℕ}
    (p : Plaquette 4 (doubleIndex (doubleIndex n))) : polymerDiam (twoFluctuationPlaquetteSupport p) ≤ 7 := by
  have h := diam_twoFluctuationSupport_le (blockIndexEquiv 4 (doubleIndex n)) (blockIndexEquiv 4 n)
    (by norm_num : (0 : ℝ) ≤ 3)
    (fun x => (dist_fluctuationRepresentative_le x).trans (by norm_num : (1 : ℝ) ≤ 3))
    dist_second_outerRepresentative_le (support p)
  exact h.trans (by linarith [diam_support_le p])

theorem dist_twoFluctuationSupport_ge_six {n : ℕ}
    (S T : Finset (Link 4 (doubleIndex (doubleIndex n)))) (hS : S.Nonempty) (hT : T.Nonempty) :
    polymerDist S T - 6 ≤ polymerDist
      (twoFluctuationSupport (blockIndexEquiv 4 (doubleIndex n)) (blockIndexEquiv 4 n) S)
      (twoFluctuationSupport (blockIndexEquiv 4 (doubleIndex n)) (blockIndexEquiv 4 n) T) := by
  simpa only [show (2 : ℝ)*3 = 6 by norm_num] using
    dist_twoFluctuationSupport_ge (blockIndexEquiv 4 (doubleIndex n)) (blockIndexEquiv 4 n)
      (fun x => (dist_fluctuationRepresentative_le x).trans (by norm_num : (1 : ℝ) ≤ 3))
      dist_second_outerRepresentative_le S T hS hT

set_option maxHeartbeats 400000 in
theorem card_incident_twoFluctuationPlaquetteSupport_le (n : ℕ) (y : TwoFluctuationLink n) :
    ((univ : Finset (Plaquette 4 (doubleIndex (doubleIndex n)))).filter
      (fun p => y ∈ twoFluctuationPlaquetteSupport p)).card ≤ 128 := by
  cases y with
  | inl y =>
    simp only [twoFluctuationPlaquetteSupport, mem_twoFluctuationSupport_inl]
    exact card_incident_fluctuationPlaquetteSupport_le (doubleIndex n) y
  | inr y =>
    simp only [twoFluctuationPlaquetteSupport, mem_twoFluctuationSupport_inr]
    cases y with
    | inl i =>
      let u := (blockIndexEquiv 4 (doubleIndex n)) (.inl (.inr ((blockIndexEquiv 4 n) (.inl (.inl i)))))
      let v := (blockIndexEquiv 4 (doubleIndex n)) (.inl (.inr ((blockIndexEquiv 4 n) (.inl (.inr i)))))
      have he : (univ.filter (fun p : Plaquette 4 (doubleIndex (doubleIndex n)) =>
          Sum.inl i ∈ fluctuationSupport (blockIndexEquiv 4 n)
            (coarseDependencySupport (blockIndexEquiv 4 (doubleIndex n)) (support p)))) =
          (univ.filter (fun p => u ∈ support p)) ∪ (univ.filter (fun p => v ∈ support p)) := by
        ext p
        simp [u, v]
      rw [he]
      have hu := card_incident_le 4 (doubleIndex (doubleIndex n)) u
      have hv := card_incident_le 4 (doubleIndex (doubleIndex n)) v
      have hh := card_union_le
        (univ.filter (fun p : Plaquette 4 (doubleIndex (doubleIndex n)) => u ∈ support p))
        (univ.filter (fun p : Plaquette 4 (doubleIndex (doubleIndex n)) => v ∈ support p))
      norm_num only at hu hv
      omega
    | inr j =>
      simp only [mem_fluctuationSupport_inr, mem_coarseDependencySupport]
      exact (card_incident_le 4 (doubleIndex (doubleIndex n))
        ((blockIndexEquiv 4 (doubleIndex n)) (.inl (.inr ((blockIndexEquiv 4 n) (.inr j)))))).trans (by norm_num)

set_option maxHeartbeats 400000 in
theorem degree_fluctuationPlaquetteGraph_le (n : ℕ) (p : Plaquette 4 (doubleIndex n)) :
    (plaquetteGraph (fluctuationPlaquetteSupport (n := n))).degree p ≤ 512 := by
  have hD (y : FluctuationLink n) :
      ((univ : Finset (Plaquette 4 (doubleIndex n))).filter
        (fun q ↦ y ∈ fluctuationPlaquetteSupport q)).card ≤ 128 :=
    card_incident_fluctuationPlaquetteSupport_le n y
  have hh := degree_plaquetteGraph_le_of_incidence (s := 4) (D := 128)
    (fluctuationPlaquetteSupport (n := n)) card_fluctuationPlaquetteSupport_le
    (fun y ↦ by
      convert hD y using 1
      congr 1
      ext q
      simp only [mem_filter]) p
  convert hh using 1
  congr 1
  exact Subsingleton.elim _ _



open StrongCouplingCrossing WilsonBlockElimination WilsonConditionalProjection.PairedHaar
open WilsonDyadicGeometry SU2WilsonBlockPilot
open Mettapedia.Combinatorics.PolymerGas
variable {n : ℕ} {P : Type*} [Fintype P] [DecidableEq P]
  (supp : P → Finset (Link 4 (doubleIndex n))) (Φ : P → C(FineConfig n, ℝ))

theorem clusterActivity_gauge
    (hΦ : ∀ p (g : Site 4 (doubleIndex n) → SU2) U, Φ p (gaugeAct g U) = Φ p U)
    (C : Finset P) (g : Site 4 n → SU2) (c : CoarseConfig n) :
    clusterActivity volume (blockIndexEquiv 4 n) supp Φ C (gaugeAct g c) =
      clusterActivity volume (blockIndexEquiv 4 n) supp Φ C c := by
  classical
  unfold clusterActivity
  split_ifs
  · apply blockedDensity_gauge
    intro gf U
    simp only [ContinuousMap.prod_apply, interactionFactor, ContinuousMap.coe_mk]
    apply prod_congr rfl
    intro p hp
    rw [hΦ]
  · rfl



theorem effectiveInteraction_gauge
    (Φ : Finset (Link 4 (doubleIndex n)) → C(FineConfig n, ℝ))
    (hsmall : interactionNorm 8 Φ ≤ 1/2)
    (hΦ : ∀ S (g : Site 4 (doubleIndex n) → SU2) U, Φ S (gaugeAct g U) = Φ S U)
    (T : Finset (Link 4 n)) (g : Site 4 n → SU2) (c : CoarseConfig n) :
    effectiveInteraction volume (blockIndexEquiv 4 n) Φ hsmall T (gaugeAct g c) =
      effectiveInteraction volume (blockIndexEquiv 4 n) Φ hsmall T c := by
  apply effectiveInteraction_eval_eq
  intro C
  exact clusterActivity_gauge (fun S : {S : Finset (Link 4 (doubleIndex n)) // S.Nonempty} ↦ S.val)
    (fun S ↦ Φ S.val) (fun S ↦ hΦ S.val) C g c

theorem wilsonInteraction_gauge (n : ℕ) (β : ℝ) (S : Finset (Link 4 n))
    (g : Site 4 n → SU2) (U : Link 4 n → SU2) :
    wilsonInteraction n β S (gaugeAct g U) = wilsonInteraction n β S U := by
  simp only [wilsonInteraction, regroupInteraction, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply, smul_eq_mul]
  apply sum_congr rfl
  intro p hp
  rw [plaquetteTrace_gauge]



open StrongCouplingCrossing WilsonBlockElimination WilsonConditionalProjection.PairedHaar
open WilsonDyadicGeometry SU2WilsonBlockPilot WilsonLocalResponse
open Mettapedia.GSLT.Ultrainfinite WilsonEliminationRoutes

/-- A full local interaction with a separate vacuum contribution. -/
structure InteractionState (n : ℕ) where
  terms : Finset (Link 4 n) → C(Link 4 n → SU2, ℝ)
  locality : ∀ S, DependsOn S (terms S)
  centered : ∀ S, (∫ U, terms S U) = 0
  empty : terms ∅ = 0
  gauge : ∀ S (g : Site 4 n → SU2) U, terms S (gaugeAct g U) = terms S U
  small : interactionNorm 8 terms ≤ 1/2
  vacuum : ℝ

namespace InteractionState
variable {n : ℕ}

def density (A : InteractionState n) : C(Link 4 n → SU2, ℝ) :=
  Real.exp A.vacuum • interactionDensity A.terms

@[simp] theorem density_apply (A : InteractionState n) (U : Link 4 n → SU2) :
    A.density U = Real.exp (A.vacuum + ∑ S, A.terms S U) := by
  simp only [density, ContinuousMap.smul_apply, smul_eq_mul, interactionDensity,
    ContinuousMap.coe_mk, Real.exp_add]

theorem density_pos (A : InteractionState n) (U : Link 4 n → SU2) : 0 < A.density U := by
  rw [density_apply]
  positivity

/-- Spatial polymer clustering for the complete generated law, including its
vacuum factor. The contraction radius needs no further reduction. -/
theorem covariance_spatial_le {η : ℝ} (hη : 0 ≤ η) {n : ℕ}
    (A : InteractionState n) (hA : spatialInteractionNorm 8 η A.terms ≤ 1/2)
    (S T : Finset (Link 4 n)) (hS : S.Nonempty) (F G : C(Link 4 n → SU2, ℝ))
    (hF : DependsOn S F) (hG : DependsOn T G) (B C : ℝ)
    (hB : ∀ U, |F U| ≤ B) (hC : ∀ U, |G U| ≤ C) :
    |covariance volume A.density F G| ≤
      3 * B * C * Real.exp (3 * S.card + 3 * T.card) * Real.exp (-η * polymerDist S T) := by
  rw [density, covariance_smul_density volume _ _ _ (Real.exp_pos A.vacuum).ne']
  exact covariance_interactionDensity_le A.terms volume hη A.locality A.empty hA S T hS F G hF hG B C hB hC


def block (A : InteractionState (doubleIndex n)) : InteractionState n where
  terms := effectiveInteraction volume (blockIndexEquiv 4 n) A.terms A.small
  locality := effectiveInteraction_local volume (blockIndexEquiv 4 n) A.terms A.small A.locality
  centered := effectiveInteraction_centered volume (blockIndexEquiv 4 n) A.terms A.small
  empty := effectiveInteraction_empty_eq_zero volume (blockIndexEquiv 4 n) A.terms A.small A.locality
  gauge := effectiveInteraction_gauge A.terms A.small A.gauge
  small := (effectiveInteraction_norm_le volume (blockIndexEquiv 4 n) A.terms A.small).trans (by
    have hq : 0 ≤ 4 * Real.exp (-2) := by positivity
    have h := mul_le_mul_of_nonneg_left A.small hq
    have hq1 := exp_reserve_lt_one
    linarith)
  vacuum := A.vacuum + effectiveVacuum volume (blockIndexEquiv 4 n) A.terms A.small

theorem norm_block_le (A : InteractionState (doubleIndex n)) :
    interactionNorm 8 A.block.terms ≤ (4 * Real.exp (-2)) * interactionNorm 8 A.terms := by
  simpa only [block] using effectiveInteraction_norm_le volume (blockIndexEquiv 4 n) A.terms A.small

theorem spatial_norm_block_le {η : ℝ} (hη : 0 ≤ η)
    (A : InteractionState (doubleIndex n)) (hA : spatialInteractionNorm 8 η A.terms ≤ 1/2) :
    spatialInteractionNorm 8 η A.block.terms ≤ (4 * Real.exp (-2)) * spatialInteractionNorm 8 η A.terms := by
  have hfirst (i : Link 4 n) : halfLink (blockIndexEquiv 4 n (.inl (.inl i))) = i :=
    halfLink_blockEdge i 0
  have hsecond (i : Link 4 n) : halfLink (blockIndexEquiv 4 n (.inl (.inr i))) = i :=
    halfLink_blockEdge i 1
  simpa only [block] using effectiveInteraction_spatial_norm_le (blockIndexEquiv 4 n) halfLink
    hfirst hsecond dist_halfLink_le volume hη A.terms A.small hA

theorem spatial_small_block {η : ℝ} (hη : 0 ≤ η)
    (A : InteractionState (doubleIndex n)) (hA : spatialInteractionNorm 8 η A.terms ≤ 1/2) :
    spatialInteractionNorm 8 η A.block.terms ≤ 1/2 := by
  have h := spatial_norm_block_le hη A hA
  have h' := mul_le_mul_of_nonneg_left hA (show 0 ≤ 4 * Real.exp (-2) by positivity)
  have hq := exp_reserve_lt_one
  linarith

theorem density_block (A : InteractionState (doubleIndex n)) :
    A.block.density = PairedLinks.blockedDensity volume (blockIndexEquiv 4 n) A.density := by
  ext c
  have he := effectiveInteraction_reconstruct volume (blockIndexEquiv 4 n)
    A.terms A.small A.locality A.empty c
  calc
    _ = Real.exp A.vacuum * Real.exp (effectiveVacuum volume (blockIndexEquiv 4 n) A.terms A.small +
        ∑ S, effectiveInteraction volume (blockIndexEquiv 4 n) A.terms A.small S c) := by
      rw [density_apply]
      simp only [block, add_assoc, Real.exp_add]
    _ = Real.exp A.vacuum * PairedLinks.blockedDensity volume (blockIndexEquiv 4 n)
        (interactionDensity A.terms) c := congrArg (Real.exp A.vacuum * ·) he.symm
    _ = _ := by
      change _ = ∫ f, Real.exp A.vacuum * interactionDensity A.terms (chart n (c, f))
      rw [integral_const_mul]
      rfl

theorem density_gauge (A : InteractionState n) (g : Site 4 n → SU2) (U : Link 4 n → SU2) :
    A.density (gaugeAct g U) = A.density U := by
  rw [density_apply, density_apply]
  congr 2
  exact sum_congr rfl (fun S _ ↦ A.gauge S g U)

abbrev weightedState (A : InteractionState n) : WilsonEliminationRoutes.State :=
  WilsonProjectionComposition.coordinateState (volume : Measure SU2) A.density A.density_pos

/-- The quantitative contraction is attached to the actual Haar integral. -/
def step (A : InteractionState (doubleIndex n)) : Step A.weightedState A.block.weightedState where
  project := PairedLinks.blockedProjectLinear volume (blockIndexEquiv 4 n) A.density A.density_pos
  expectation := fun F ↦ by
    change expectation volume A.block.density _ = expectation volume A.density F
    rw [density_block]
    exact PairedLinks.expectation_blockedProject volume (blockIndexEquiv 4 n) A.density A.density_pos F
  contract := fun F _ hF ↦ PairedLinks.abs_blockedProject_le volume (blockIndexEquiv 4 n)
    A.density A.density_pos F hF

end InteractionState


/-- A positive, volume-independent interval for the full nonlinear iteration. -/
def iterationBeta : ℝ := 1 / (128 * Real.exp 32)

theorem iterationBeta_pos : 0 < iterationBeta := by unfold iterationBeta; positivity

theorem wilsonInteraction_empty (n : ℕ) (β : ℝ) : wilsonInteraction n β ∅ = 0 := by
  ext U
  have he (W : Link 4 n → SU2) : wilsonInteraction n β ∅ W = wilsonInteraction n β ∅ U :=
    wilsonInteraction_local n β ∅ W U (by simp)
  have hi := wilsonInteraction_centered n β ∅
  simp_rw [he] at hi
  simpa using hi

def wilsonState (n : ℕ) (β : ℝ) (hβ : |β| ≤ iterationBeta) : InteractionState n where
  terms := wilsonInteraction n β
  locality := wilsonInteraction_local n β
  centered := wilsonInteraction_centered n β
  empty := wilsonInteraction_empty n β
  gauge := wilsonInteraction_gauge n β
  small := wilsonInteraction_entry 8 (1/2) (by norm_num) n β (by
    convert hβ using 1
    unfold iterationBeta
    norm_num
    ring)
  vacuum := -β * Fintype.card (Plaquette 4 n)

theorem wilsonState_density (n : ℕ) (β : ℝ) (hβ : |β| ≤ iterationBeta) :
    (wilsonState n β hβ).density =
      realDensity (SU2BoundaryResponse.model n univ) (SU2BoundaryResponse.model_continuous n univ) β := by
  ext U
  rw [InteractionState.density_apply, realDensity_eq_wilsonInteraction]
  simp only [wilsonState, ContinuousMap.sum_apply]


def strongIterationBeta : ℝ := min iterationBeta (StrongCouplingCrossing.beta0 4)

theorem strongIterationBeta_pos : 0 < strongIterationBeta :=
  lt_min iterationBeta_pos (StrongCouplingCrossing.beta0_pos 4)

theorem abs_le_iterationBeta {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ strongIterationBeta) :
    |β| ≤ iterationBeta := by
  rw [abs_of_nonneg hβ]
  exact hβ0.trans (min_le_left _ _)

/-- Spatial Wilson entry, with the rate fixed before the volume. -/

def spatialIterationBeta (η : ℝ) : ℝ := 1 / (128 * Real.exp (32+4*η))

theorem spatialIterationBeta_pos (η : ℝ) : 0 < spatialIterationBeta η := by unfold spatialIterationBeta; positivity

theorem spatialIterationBeta_le {η : ℝ} (hη : 0 ≤ η) : spatialIterationBeta η ≤ iterationBeta := by
  apply one_div_le_one_div_of_le (by positivity : 0 < 128 * Real.exp 32)
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  linarith

theorem wilsonState_spatial_small {η : ℝ} (hη : 0 ≤ η) (n : ℕ) (β : ℝ)
    (hβ : |β| ≤ iterationBeta) (hsp : |β| ≤ spatialIterationBeta η) :
    spatialInteractionNorm 8 η (wilsonState n β hβ).terms ≤ 1/2 := by
  apply wilsonInteraction_spatial_entry 8 η (1/2) (by norm_num) hη
  convert hsp using 1
  unfold spatialIterationBeta
  norm_num
  ring

theorem wilsonPlaquette_spatial_row_small {η β : ℝ} (hη : 0 ≤ η)
    (hβ : |β| ≤ spatialIterationBeta η) (n : ℕ) (l : Link 4 n) :
    (∑ p ∈ univ.filter (fun p : Plaquette 4 n => l ∈ support p),
      Real.exp (8*(support p).card+η*treeLength (support p)) * ‖(-β) • plaquetteTrace p‖) ≤ 1/2 := by
  apply (wilsonPlaquette_spatial_row_le n β 8 η (by norm_num) hη l).trans
  have h := (le_div_iff₀ (by positivity : 0 < 128*Real.exp (32+4*η))).mp hβ
  norm_num only at *
  nlinarith

set_option maxHeartbeats 1200000 in
set_option linter.defProp false in
-- Inferring this private proof's type preserves the finite-set instance
-- arguments of the generic positivity theorem without expensive conversions.
private def wilsonPlaquette_partition_pos (n : ℕ) (β : ℝ) (hβ : |β| ≤ iterationBeta) :=
  clusterActivity_partition_pos volume (blockIndexEquiv 4 n) support
    (fun p : Plaquette 4 (doubleIndex n) => (-β) • plaquetteTrace p) support_nonempty
    (R := 1/2) (by norm_num) le_rfl (by
      intro l
      have hb : |β| ≤ spatialIterationBeta 0 := by
        simpa [spatialIterationBeta, iterationBeta] using hβ
      simpa only [zero_mul, add_zero] using
        wilsonPlaquette_spatial_row_small (by norm_num) hb (doubleIndex n) l)

set_option maxHeartbeats 1200000 in
/-- The complete generated logarithm indexed by original plaquette labels.
Keeping these labels identifies which generated coefficients contain a source. -/
def plaquetteLogFamily (n : ℕ) (β : ℝ) (hβ : |β| ≤ iterationBeta) :
    Finset (Finset (Plaquette 4 (doubleIndex n))) → C(CoarseConfig n, ℝ) :=
  clusterLogFamily volume (blockIndexEquiv 4 n) support
    (fun p : Plaquette 4 (doubleIndex n) => (-β) • plaquetteTrace p)
    (wilsonPlaquette_partition_pos n β hβ)

theorem plaquetteLogFamily_local (n : ℕ) (β : ℝ) (hβ : |β| ≤ iterationBeta)
    (A : Finset (Finset (Plaquette 4 (doubleIndex n)))) :
    DependsOn (A.biUnion (clusterRetainedSupport (blockIndexEquiv 4 n) support))
      (plaquetteLogFamily n β hβ A) :=
  clusterLogFamily_local volume (blockIndexEquiv 4 n) support
    (fun p : Plaquette 4 (doubleIndex n) => (-β) • plaquetteTrace p)
    (fun p U V h => congrArg (fun x : ℝ => -β*x) (plaquetteTrace_local p U V h))
    (wilsonPlaquette_partition_pos n β hβ) A

theorem plaquetteLogCoefficient_local (n : ℕ) (β : ℝ) (hβ : |β| ≤ iterationBeta)
    (A : Finset (Finset (Plaquette 4 (doubleIndex n)))) :
    DependsOn (A.biUnion (clusterRetainedSupport (blockIndexEquiv 4 n) support))
      (SubsetExpansion.coefficient (A := C(CoarseConfig n, ℝ)) (plaquetteLogFamily n β hβ) A) :=
  coefficient_local _ _ (plaquetteLogFamily_local n β hβ) A

set_option maxHeartbeats 1200000 in
/-- Exact relation to the first Wilson marginal, including the vacuum factor. -/
theorem log_coarseDensity_eq_plaquetteLogFamily (n : ℕ) (β : ℝ)
    (hβ : |β| ≤ iterationBeta) (c : CoarseConfig n) :
    Real.log (coarseDensity n β c) =
      -β * Fintype.card (Plaquette 4 (doubleIndex n)) + plaquetteLogFamily n β hβ univ c := by
  let Φ := fun p : Plaquette 4 (doubleIndex n) => (-β) • plaquetteTrace p
  have hl := clusterLogFamily_univ volume (blockIndexEquiv 4 n) support Φ
    (wilsonPlaquette_partition_pos n β hβ) support_nonempty
    (fun p U V h => congrArg (fun x : ℝ => -β*x) (plaquetteTrace_local p U V h)) c
  change plaquetteLogFamily n β hβ univ c =
    Real.log (blockedDensity volume (blockIndexEquiv 4 n) (interactionDensity Φ) c) at hl
  rw [hl]
  have he : coarseDensity n β c = Real.exp (-β * Fintype.card (Plaquette 4 (doubleIndex n))) *
      blockedDensity volume (blockIndexEquiv 4 n) (interactionDensity Φ) c := by
    change (∫ f : Fluctuation n, fineDensity n β (chart n (c,f))) =
      Real.exp (-β * Fintype.card (Plaquette 4 (doubleIndex n))) *
        ∫ f : Fluctuation n, Real.exp (∑ p, -β * plaquetteTrace p (chart n (c,f)))
    simp_rw [fineDensity, realDensity_eq_wilsonInteraction, sum_wilsonInteraction]
    simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul, Real.exp_add]
    rw [integral_const_mul]
  rw [he, Real.log_mul (Real.exp_pos _).ne'
    (blockedDensity_pos volume (blockIndexEquiv 4 n) _ (interactionDensity_pos Φ) c).ne', Real.log_exp]

theorem log_coarseDensity_eq_sum_plaquetteCoefficients (n : ℕ) (β : ℝ)
    (hβ : |β| ≤ iterationBeta) (c : CoarseConfig n) :
    Real.log (coarseDensity n β c) = -β * Fintype.card (Plaquette 4 (doubleIndex n)) +
      ∑ A, SubsetExpansion.coefficient (plaquetteLogFamily n β hβ) A c := by
  rw [log_coarseDensity_eq_plaquetteLogFamily n β hβ c]
  congr 1
  have h := congrArg (fun F : C(CoarseConfig n, ℝ) => F c)
    (SubsetExpansion.zeta_coefficient (plaquetteLogFamily n β hβ) univ)
  simpa only [SubsetExpansion.zeta, powerset_univ, ContinuousMap.sum_apply] using h.symm

set_option maxHeartbeats 1200000 in
/-- Every generated logarithmic coefficient carrying a designated original
Wilson plaquette has a volume-uniform spatial budget, with its location retained. -/
theorem plaquetteLogFamily_marked_spatial_budget {η β : ℝ} (hη : 0 ≤ η)
    (hβ : |β| ≤ spatialIterationBeta η) (n : ℕ) (p : Plaquette 4 (doubleIndex n)) :
    ∑ A ∈ univ.filter (fun A : Finset (Finset (Plaquette 4 (doubleIndex n))) => p ∈ A.biUnion id),
      Real.exp (8*(A.biUnion (clusterRetainedSupport (blockIndexEquiv 4 n) support)).card +
        η*treeLength (A.biUnion (clusterRetainedSupport (blockIndexEquiv 4 n) support) ∪
          (support p).image halfLink)) *
        ‖SubsetExpansion.coefficient (plaquetteLogFamily n β (hβ.trans (spatialIterationBeta_le hη))) A‖ ≤
      2 * |β| * Real.exp (24+4*η) := by
  have h := clusterLogFamily_marked_spatial_budget (blockIndexEquiv 4 n) halfLink
    (fun i => halfLink_blockEdge i 0) (fun i => halfLink_blockEdge i 1) dist_halfLink_le volume support
    (fun p : Plaquette 4 (doubleIndex n) => (-β) • plaquetteTrace p)
    (wilsonPlaquette_partition_pos n β (hβ.trans (spatialIterationBeta_le hη))) hη support_nonempty
    (R := 1/2) (by norm_num) le_rfl (wilsonPlaquette_spatial_row_small hη hβ (doubleIndex n)) p
  apply h.trans
  have hc : ((support p).card : ℝ) ≤ 4 := by exact_mod_cast card_support_le p
  have ht := treeLength_support_le p
  have hn : ‖(-β) • plaquetteTrace p‖ ≤ |β| := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg]
    exact (mul_le_mul_of_nonneg_left (norm_plaquetteTrace_le p) (abs_nonneg β)).trans_eq (mul_one _)
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left hn (by norm_num)
  · exact Real.exp_le_exp.mpr (by nlinarith)
  · positivity
  · positivity


end ScaleTwo

#print axioms integral_assemble
#print axioms secondDensity_staged
#print axioms partition_staged
#print axioms expectation_route
#print axioms covariance_route
end Mettapedia.QuantumTheory.YangMills.SU2WilsonAssembly

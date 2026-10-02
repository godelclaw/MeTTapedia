import Mettapedia.QuantumTheory.YangMills.WilsonConditionalProjection
import Mettapedia.QuantumTheory.YangMills.SU2BoundaryResponse
import Mettapedia.QuantumTheory.YangMills.WilsonDyadicGeometry
import Mettapedia.QuantumTheory.YangMills.WilsonEliminationRoutes
import Mettapedia.QuantumTheory.YangMills.WilsonProjectionComposition

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

/-- The full scale-two effective Wilson weight, without action extraction. -/
def coarseDensity (n : ℕ) (β : ℝ) : C(CoarseConfig n, ℝ) :=
  PairedLinks.blockedDensity (volume : Measure SU2) (blockIndexEquiv 4 n) (fineDensity n β)

theorem coarseDensity_pos (n : ℕ) (β : ℝ) : ∀ c, 0 < coarseDensity n β c :=
  PairedLinks.blockedDensity_pos (volume : Measure SU2) (blockIndexEquiv 4 n)
    (fineDensity n β) (fineDensity_pos n β)

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


end ScaleTwo

#print axioms integral_assemble
#print axioms secondDensity_staged
#print axioms partition_staged
#print axioms expectation_route
#print axioms covariance_route
end Mettapedia.QuantumTheory.YangMills.SU2WilsonAssembly

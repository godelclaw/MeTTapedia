import Mettapedia.QuantumTheory.YangMills.SU2WilsonBlockIntegration
import Mettapedia.QuantumTheory.YangMills.WilsonSeparatedBoundaryResponse
import Mettapedia.QuantumTheory.YangMills.WilsonPinnedIntegral

/-!
# Spatial decay of the genuine SU(2) boundary free energy

The gauge group is the matrix group SU(2), the reference law is normalized
Haar, and the plaquette energy is `1 - Re(trace U_p)/2`. Arbitrary plaquette
masks and fixed boundary values are allowed. The bound is uniform in volume
on the explicit SC4 coupling interval. Its prefactor depends only on the
sizes of the two changed patches.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Finset MeasureTheory Filter
open scoped Topology Classical Matrix.Norms.Elementwise
open Mettapedia.Combinatorics.PolymerGas

namespace Mettapedia.QuantumTheory.YangMills.SU2BoundaryResponse
open SU2WilsonBlockPilot StrongCouplingCrossing InhomogeneousWilsonCrossing
open WilsonLocalResponse WilsonPatchGeometry WilsonBoundaryChanges
open WilsonSeparatedBoundaryResponse

/-- The original SU(2) Wilson plaquette, with its two reversed links. -/
def plaquetteEnergy : C((Fin 4 → SU2), ℝ) :=
  ⟨fun v => SU2WilsonBlockIntegration.potential (holonomy v), by
    apply SU2WilsonBlockIntegration.potential.continuous.comp
    unfold holonomy
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

/-! ## Actual boundary curves and their local action scores -/

variable {n : ℕ}

/-- Independently framed rotation directions on a patch of boundary links.
Every other boundary value is left fixed. -/
def boundaryCurve (S : Finset (Link 4 n)) (q b : Link 4 n → SU2) (t : ℝ) :
    Link 4 n → SU2 := fun l ↦ if l ∈ S then rotationPerturbation (q l) (b l) t else b l

@[simp] theorem boundaryCurve_zero (S : Finset (Link 4 n)) (q b : Link 4 n → SU2) :
    boundaryCurve S q b 0 = b := by
  funext l
  simp [boundaryCurve]

@[fun_prop] theorem continuous_boundaryCurve (S : Finset (Link 4 n))
    (q b : Link 4 n → SU2) : Continuous (boundaryCurve S q b) := by
  apply continuous_pi
  intro l
  by_cases hl : l ∈ S <;> simp only [boundaryCurve, hl, ↓reduceIte] <;> fun_prop

open scoped ContDiff in
theorem contDiff_boundaryCurve (S : Finset (Link 4 n)) (q b : Link 4 n → SU2) :
    ContDiff ℝ ∞ (fun t ↦ fun l ↦ (boundaryCurve S q b t l).val) := by
  apply contDiff_pi.mpr
  intro l
  by_cases hl : l ∈ S
  · simpa only [boundaryCurve, hl, ↓reduceIte] using contDiff_rotationPerturbation (q l) (b l)
  · simp only [boundaryCurve, hl, ↓reduceIte]
    exact contDiff_const

/-- The original four link values, with only held coordinates pinned. -/
def plaquetteValues (held : Finset (Link 4 n)) (b : Link 4 n → SU2)
    (p : Plaquette 4 n) (ω : Link 4 n → SU2) : Fin 4 → SU2 :=
  fun i ↦ WilsonPinnedIntegral.pin held b ω (linkAt p i)

theorem plaquetteValues_pin (held : Finset (Link 4 n)) (b : Link 4 n → SU2)
    (p : Plaquette 4 n) (ω : Link 4 n → SU2) :
    plaquetteValues held b p (WilsonPinnedIntegral.pin held b ω) = plaquetteValues held b p ω := by
  funext i
  exact congrFun (WilsonPinnedIntegral.pin_pin held b ω) (linkAt p i)

/-- A plaquette slot moves exactly when its link is both held and changed. -/
def movingSlots (held S : Finset (Link 4 n)) (p : Plaquette 4 n) : Finset (Fin 4) :=
  univ.filter (fun i ↦ linkAt p i ∈ held ∧ linkAt p i ∈ S)

theorem movingSlots_empty_of_not_incident (held S : Finset (Link 4 n))
    (p : Plaquette 4 n) (hp : p ∉ incident S) : movingSlots held S p = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro i hi
  have hS := ((mem_filter.mp hi).2).2
  exact hp (mem_incident.mpr ⟨linkAt p i, hS, mem_image.mpr ⟨i, mem_univ _, rfl⟩⟩)

theorem card_movingSlots_le (held S : Finset (Link 4 n)) (p : Plaquette 4 n) :
    (movingSlots held S p).card ≤ 4 := by
  simpa using card_le_card (subset_univ (movingSlots held S p))

theorem pinnedPotential_eq (active : Finset (Plaquette 4 n))
    (held : Finset (Link 4 n)) (b : Link 4 n → SU2) (p : Plaquette 4 n)
    (ω : Link 4 n → SU2) :
    pinnedPotential (model n active) held b p ω =
      if p ∈ active then SU2WilsonBlockIntegration.potential (holonomy (plaquetteValues held b p ω))
      else 0 := by
  by_cases hp : p ∈ active <;>
    simp [pinnedPotential, model, Model.masked, Model.pinned, StrongCouplingCrossing.potential,
      plaquetteEnergy, plaquetteValues, WilsonPinnedIntegral.pin, hp] <;> rfl

/-- The full original Wilson action before multiplication by beta. -/
def action (active : Finset (Plaquette 4 n)) (held : Finset (Link 4 n))
    (b : Link 4 n → SU2) : C(Link 4 n → SU2, ℝ) :=
  ⟨fun ω ↦ ∑ p, pinnedPotential (model n active) held b p ω,
    continuous_finsetSum _ fun p _ ↦
      continuous_pinnedPotential (model n active) (model_continuous n active) held b p⟩

def plaquetteScore (active : Finset (Plaquette 4 n)) (held S : Finset (Link 4 n))
    (q b : Link 4 n → SU2) (t : ℝ) (p : Plaquette 4 n) (ω : Link 4 n → SU2) : ℝ :=
  if p ∈ active then SU2WilsonBlockIntegration.holonomyScore
    (plaquetteValues held (boundaryCurve S q b t) p ω)
    (fun i ↦ rotationPerturbation (q (linkAt p i)) (b (linkAt p i)) (t + Real.pi / 2))
    (movingSlots held S p) else 0

theorem continuous_plaquetteValues_curve (held S : Finset (Link 4 n))
    (q b : Link 4 n → SU2) (p : Plaquette 4 n) :
    Continuous (fun z : ℝ × (Link 4 n → SU2) ↦
      plaquetteValues held (boundaryCurve S q b z.1) p z.2) := by
  apply continuous_pi
  intro i
  by_cases hi : linkAt p i ∈ held
  · simp only [plaquetteValues, WilsonPinnedIntegral.pin, hi, ↓reduceIte]
    exact ((continuous_apply (linkAt p i)).comp (continuous_boundaryCurve S q b)).comp
      continuous_fst
  · simp only [plaquetteValues, WilsonPinnedIntegral.pin, hi, ↓reduceIte]
    fun_prop

theorem continuous_plaquetteScore (active : Finset (Plaquette 4 n))
    (held S : Finset (Link 4 n)) (q b : Link 4 n → SU2) (p : Plaquette 4 n) :
    Continuous (fun z : ℝ × (Link 4 n → SU2) ↦ plaquetteScore active held S q b z.1 p z.2) := by
  by_cases hp : p ∈ active
  · simp only [plaquetteScore, hp, ↓reduceIte]
    have hu : Continuous (fun z : ℝ × (Link 4 n → SU2) ↦ fun i : Fin 4 ↦
        rotationPerturbation (q (linkAt p i)) (b (linkAt p i)) (z.1 + Real.pi / 2)) := by
      apply continuous_pi
      intro i
      exact (continuous_rotationPerturbation _ _).comp (continuous_fst.add continuous_const)
    simpa only [Function.comp_def] using
      (SU2WilsonBlockIntegration.continuous_holonomyScore (movingSlots held S p)).comp
        ((continuous_plaquetteValues_curve held S q b p).prodMk hu)
  · simp only [plaquetteScore, hp, ↓reduceIte]
    exact continuous_const

theorem hasDerivAt_plaquetteValues (held S : Finset (Link 4 n))
    (q b : Link 4 n → SU2) (t : ℝ) (p : Plaquette 4 n) (ω : Link 4 n → SU2) (i : Fin 4) :
    HasDerivAt (fun s ↦ (plaquetteValues held (boundaryCurve S q b s) p ω i).val)
      (if i ∈ movingSlots held S p then
        (rotationPerturbation (q (linkAt p i)) (b (linkAt p i)) (t + Real.pi / 2)).val else 0) t := by
  by_cases hh : linkAt p i ∈ held <;> by_cases hS : linkAt p i ∈ S
  · simpa [plaquetteValues, WilsonPinnedIntegral.pin, boundaryCurve, movingSlots, hh, hS] using
      hasDerivAt_rotationPerturbation (q (linkAt p i)) (b (linkAt p i)) t
  · simpa [plaquetteValues, WilsonPinnedIntegral.pin, boundaryCurve, movingSlots, hh, hS] using
      hasDerivAt_const_matrix (b (linkAt p i)).val t
  · simpa [plaquetteValues, WilsonPinnedIntegral.pin, boundaryCurve, movingSlots, hh, hS] using
      hasDerivAt_const_matrix (ω (linkAt p i)).val t
  · simpa [plaquetteValues, WilsonPinnedIntegral.pin, boundaryCurve, movingSlots, hh, hS] using
      hasDerivAt_const_matrix (ω (linkAt p i)).val t

/-- Sum only over incident plaquettes; all removed terms have zero derivative. -/
def score (active : Finset (Plaquette 4 n)) (held S : Finset (Link 4 n))
    (q b : Link 4 n → SU2) (t : ℝ) : C(Link 4 n → SU2, ℝ) :=
  ⟨fun ω ↦ ∑ p ∈ incident S, plaquetteScore active held S q b t p ω,
    continuous_finsetSum _ fun p _ ↦ by
      simpa only [Function.comp_def] using (continuous_plaquetteScore active held S q b p).comp
        (show Continuous (fun ω : Link 4 n → SU2 ↦ (t, ω)) from
          continuous_const.prodMk continuous_id)⟩

theorem continuous_score (active : Finset (Plaquette 4 n)) (held S : Finset (Link 4 n))
    (q b : Link 4 n → SU2) :
    Continuous (fun z : ℝ × (Link 4 n → SU2) ↦ score active held S q b z.1 z.2) :=
  continuous_finsetSum _ fun p _ ↦ continuous_plaquetteScore active held S q b p

theorem plaquetteScore_off_incident (active : Finset (Plaquette 4 n))
    (held S : Finset (Link 4 n)) (q b : Link 4 n → SU2) (t : ℝ) (p : Plaquette 4 n)
    (hp : p ∉ incident S) (ω : Link 4 n → SU2) : plaquetteScore active held S q b t p ω = 0 := by
  have hm := movingSlots_empty_of_not_incident held S p hp
  simp [plaquetteScore, hm, SU2WilsonBlockIntegration.holonomyScore]

theorem abs_plaquetteScore_le (active : Finset (Plaquette 4 n))
    (held S : Finset (Link 4 n)) (q b : Link 4 n → SU2) (t : ℝ) (p : Plaquette 4 n)
    (ω : Link 4 n → SU2) : |plaquetteScore active held S q b t p ω| ≤ 4 := by
  by_cases hp : p ∈ active
  · simp only [plaquetteScore, hp, ↓reduceIte]
    apply (SU2WilsonBlockIntegration.abs_holonomyScore_le _ _ _).trans
    have hc := card_movingSlots_le held S p
    exact_mod_cast hc
  · simp [plaquetteScore, hp]

/-- The local derivative bound depends on patch size, with no volume factor. -/
theorem abs_score_le (active : Finset (Plaquette 4 n)) (held S : Finset (Link 4 n))
    (q b : Link 4 n → SU2) (t : ℝ) (ω : Link 4 n → SU2) :
    |score active held S q b t ω| ≤ 256 * S.card := by
  have hsum : |score active held S q b t ω| ≤ 4 * (incident S).card := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_comm] using
      Finset.sum_le_sum (s := incident S) (fun p _ ↦ abs_plaquetteScore_le active held S q b t p ω)
  have hc : ((incident S).card : ℝ) ≤ S.card * 64 := by
    exact_mod_cast WilsonPatchGeometry.card_incident_le S
  nlinarith

theorem hasDerivAt_pinnedPotential (active : Finset (Plaquette 4 n))
    (held S : Finset (Link 4 n)) (q b : Link 4 n → SU2) (t : ℝ) (p : Plaquette 4 n)
    (ω : Link 4 n → SU2) :
    HasDerivAt (fun s ↦ pinnedPotential (model n active) held (boundaryCurve S q b s) p ω)
      (plaquetteScore active held S q b t p ω) t := by
  by_cases hp : p ∈ active
  · simp only [pinnedPotential_eq, hp, ↓reduceIte, plaquetteScore]
    apply SU2WilsonBlockIntegration.hasDerivAt_holonomy_potential
    exact hasDerivAt_plaquetteValues held S q b t p ω
  · simp only [pinnedPotential_eq, hp, ↓reduceIte, plaquetteScore]
    exact hasDerivAt_const _ _

theorem hasDerivAt_action (active : Finset (Plaquette 4 n)) (held S : Finset (Link 4 n))
    (q b : Link 4 n → SU2) (t : ℝ) (ω : Link 4 n → SU2) :
    HasDerivAt (fun s ↦ action active held (boundaryCurve S q b s) ω)
      (score active held S q b t ω) t := by
  apply (HasDerivAt.fun_sum (fun p _ ↦ hasDerivAt_pinnedPotential active held S q b t p ω)).congr_deriv
  exact (sum_subset (subset_univ (incident S)) (fun p _ hp ↦
    plaquetteScore_off_incident active held S q b t p hp ω)).symm

theorem score_local (active : Finset (Plaquette 4 n)) (held S : Finset (Link 4 n))
    (q b : Link 4 n → SU2) (t : ℝ) (ω ω' : Link 4 n → SU2)
    (h : ∀ l ∈ collar S, ω l = ω' l) :
    score active held S q b t ω = score active held S q b t ω' := by
  apply sum_congr rfl
  intro p hp
  unfold plaquetteScore
  congr 2
  funext i
  have hi : linkAt p i ∈ collar S :=
    mem_biUnion.mpr ⟨p, hp, mem_image.mpr ⟨i, mem_univ _, rfl⟩⟩
  simp only [plaquetteValues, WilsonPinnedIntegral.pin, h _ hi]

/-- Scores of the pinned action already ignore the held dummy coordinates. -/
theorem score_pin (active : Finset (Plaquette 4 n)) (held S : Finset (Link 4 n))
    (q b : Link 4 n → SU2) (ω : Link 4 n → SU2) :
    score active held S q b 0 (WilsonPinnedIntegral.pin held b ω) =
      score active held S q b 0 ω := by
  apply sum_congr rfl
  intro p _
  simp only [plaquetteScore, boundaryCurve_zero, plaquetteValues_pin]

/-- The action score on its actual incident-plaquette collar. -/
def localScore (active : Finset (Plaquette 4 n)) (held S : Finset (Link 4 n))
    (q b : Link 4 n → SU2) (t : ℝ) : C(collar S → SU2, ℝ) :=
  (score active held S q b t).comp (WilsonSeparatedBoundaryResponse.extend (1 : SU2) (collar S))

theorem localScore_reconstruct (active : Finset (Plaquette 4 n))
    (held S : Finset (Link 4 n)) (q b : Link 4 n → SU2) (t : ℝ) :
    localObservable (collar S) (localScore active held S q b t) =
      score active held S q b t := by
  ext ω
  simp only [localObservable, localScore, ContinuousMap.comp_apply,
    WilsonSeparatedBoundaryResponse.extend, ContinuousMap.coe_mk]
  apply score_local
  intro l hl
  simp [WilsonSeparatedBoundaryResponse.extend, extendConfiguration, restrictTo, hl]

theorem plaquetteScore_eq_of_agree (active : Finset (Plaquette 4 n))
    (held S : Finset (Link 4 n)) (q b b' : Link 4 n → SU2) (t : ℝ)
    (p : Plaquette 4 n) (h : ∀ l ∈ support p, b l = b' l) (ω : Link 4 n → SU2) :
    plaquetteScore active held S q b t p ω = plaquetteScore active held S q b' t p ω := by
  have hi (i : Fin 4) := h (linkAt p i) (mem_image.mpr ⟨i, mem_univ _, rfl⟩)
  have hv : plaquetteValues held (boundaryCurve S q b t) p ω =
      plaquetteValues held (boundaryCurve S q b' t) p ω := by
    funext i
    simp [plaquetteValues, WilsonPinnedIntegral.pin, boundaryCurve, hi i]
  have hu : (fun i ↦ rotationPerturbation (q (linkAt p i)) (b (linkAt p i))
      (t + Real.pi / 2)) = (fun i ↦ rotationPerturbation (q (linkAt p i))
        (b' (linkAt p i)) (t + Real.pi / 2)) := by
    funext i
    rw [hi i]
  unfold plaquetteScore
  rw [hv, hu]

/-- There is no contact interaction between plaquette-disjoint patches. -/
theorem score_other (active : Finset (Plaquette 4 n)) (held S T : Finset (Link 4 n))
    (q r b : Link 4 n → SU2) (s t : ℝ)
    (hST : Disjoint (incident S) (incident T)) :
    score active held S q (boundaryCurve T r b t) s = score active held S q b s := by
  ext ω
  apply sum_congr rfl
  intro p hp
  apply plaquetteScore_eq_of_agree
  intro l hl
  have hpT : p ∉ incident T := fun h ↦ disjoint_left.mp hST hp h
  have hlT : l ∉ T := fun h ↦ hpT (mem_incident.mpr ⟨l, h, hl⟩)
  simp [boundaryCurve, hlT]

theorem hasDerivAt_score_other (active : Finset (Plaquette 4 n))
    (held S T : Finset (Link 4 n)) (q r b : Link 4 n → SU2) (s t : ℝ)
    (hST : Disjoint (incident S) (incident T)) (ω : Link 4 n → SU2) :
    HasDerivAt (fun u ↦ score active held S q (boundaryCurve T r b u) s ω) 0 t := by
  simp_rw [score_other active held S T q r b s _ hST]
  exact hasDerivAt_const _ _

/-- Vanishing of the mixed derivative of the original Wilson action itself,
at every point on the two independent boundary curves. -/
theorem hasDerivAt_contact_zero (active : Finset (Plaquette 4 n))
    (held S T : Finset (Link 4 n)) (q r b : Link 4 n → SU2) (s t : ℝ)
    (hST : Disjoint (incident S) (incident T)) (ω : Link 4 n → SU2) :
    HasDerivAt (fun u ↦ deriv (fun v ↦ action active held
      (boundaryCurve S q (boundaryCurve T r b u) v) ω) s) 0 t := by
  have hd (u : ℝ) := (hasDerivAt_action active held S q (boundaryCurve T r b u) s ω).deriv
  simpa only [hd] using hasDerivAt_score_other active held S T q r b s t hST ω

/-! ## The contact derivative for arbitrary patch pairs -/

def plaquetteContact (active : Finset (Plaquette 4 n)) (held S T : Finset (Link 4 n))
    (q r b : Link 4 n → SU2) (t : ℝ) (p : Plaquette 4 n) (ω : Link 4 n → SU2) : ℝ :=
  if p ∈ active then SU2WilsonBlockIntegration.holonomyContact
    (plaquetteValues held (boundaryCurve T r b t) p ω)
    (fun i ↦ rotationPerturbation (q (linkAt p i))
      (boundaryCurve T r b t (linkAt p i)) (Real.pi / 2))
    (fun i ↦ rotationPerturbation (r (linkAt p i)) (b (linkAt p i)) (t + Real.pi / 2))
    (fun i ↦ rotationPerturbation (q (linkAt p i))
      (rotationPerturbation (r (linkAt p i)) (b (linkAt p i)) (t + Real.pi / 2)) (Real.pi / 2))
    (movingSlots held S p) (movingSlots held T p) else 0

theorem continuous_plaquetteScore_other (active : Finset (Plaquette 4 n))
    (held S T : Finset (Link 4 n)) (q r b : Link 4 n → SU2) (p : Plaquette 4 n) :
    Continuous (fun z : ℝ × (Link 4 n → SU2) ↦
      plaquetteScore active held S q (boundaryCurve T r b z.1) 0 p z.2) := by
  by_cases hp : p ∈ active
  · simp only [plaquetteScore, hp, ↓reduceIte, boundaryCurve_zero, zero_add]
    have hu : Continuous (fun z : ℝ × (Link 4 n → SU2) ↦ fun i : Fin 4 ↦
        rotationPerturbation (q (linkAt p i))
          (boundaryCurve T r b z.1 (linkAt p i)) (Real.pi / 2)) := by
      apply continuous_pi
      intro i
      simpa only [rotationPerturbation, Function.comp_def] using continuous_const.fun_mul
        (((continuous_apply (linkAt p i)).comp (continuous_boundaryCurve T r b)).comp continuous_fst)
    simpa only [Function.comp_def] using
      (SU2WilsonBlockIntegration.continuous_holonomyScore (movingSlots held S p)).comp
        ((continuous_plaquetteValues_curve held T r b p).prodMk hu)
  · simp only [plaquetteScore, hp, ↓reduceIte]
    exact continuous_const

theorem continuous_plaquetteContact (active : Finset (Plaquette 4 n))
    (held S T : Finset (Link 4 n)) (q r b : Link 4 n → SU2) (p : Plaquette 4 n) :
    Continuous (fun z : ℝ × (Link 4 n → SU2) ↦ plaquetteContact active held S T q r b z.1 p z.2) := by
  by_cases hp : p ∈ active
  · simp only [plaquetteContact, hp, ↓reduceIte]
    have hu : Continuous (fun z : ℝ × (Link 4 n → SU2) ↦ fun i : Fin 4 ↦
        rotationPerturbation (q (linkAt p i))
          (boundaryCurve T r b z.1 (linkAt p i)) (Real.pi / 2)) := by
      apply continuous_pi
      intro i
      simpa only [rotationPerturbation, Function.comp_def] using continuous_const.fun_mul
        (((continuous_apply (linkAt p i)).comp (continuous_boundaryCurve T r b)).comp continuous_fst)
    have hv : Continuous (fun z : ℝ × (Link 4 n → SU2) ↦ fun i : Fin 4 ↦
        rotationPerturbation (r (linkAt p i)) (b (linkAt p i)) (z.1 + Real.pi / 2)) := by
      apply continuous_pi
      intro i
      exact (continuous_rotationPerturbation _ _).comp (continuous_fst.add continuous_const)
    have hvu : Continuous (fun z : ℝ × (Link 4 n → SU2) ↦ fun i : Fin 4 ↦
        rotationPerturbation (q (linkAt p i))
          (rotationPerturbation (r (linkAt p i)) (b (linkAt p i)) (z.1 + Real.pi / 2)) (Real.pi / 2)) := by
      apply continuous_pi
      intro i
      simpa only [rotationPerturbation, Function.comp_def] using continuous_const.fun_mul
        ((continuous_apply i).comp hv)
    simpa only [Function.comp_def] using
      (SU2WilsonBlockIntegration.continuous_holonomyContact
        (movingSlots held S p) (movingSlots held T p)).comp
        (((continuous_plaquetteValues_curve held T r b p).prodMk hu).prodMk (hv.prodMk hvu))
  · simp only [plaquetteContact, hp, ↓reduceIte]
    exact continuous_const

/-- The mixed derivative of the original action, before taking an expectation. -/
def contact (active : Finset (Plaquette 4 n)) (held S T : Finset (Link 4 n))
    (q r b : Link 4 n → SU2) (t : ℝ) : C(Link 4 n → SU2, ℝ) :=
  ⟨fun ω ↦ ∑ p ∈ incident S, plaquetteContact active held S T q r b t p ω,
    continuous_finsetSum _ fun p _ ↦ by
      simpa only [Function.comp_def] using
        (continuous_plaquetteContact active held S T q r b p).comp
          (show Continuous (fun ω : Link 4 n → SU2 ↦ (t, ω)) from
            continuous_const.prodMk continuous_id)⟩

theorem continuous_score_other (active : Finset (Plaquette 4 n))
    (held S T : Finset (Link 4 n)) (q r b : Link 4 n → SU2) :
    Continuous (fun z : ℝ × (Link 4 n → SU2) ↦
      score active held S q (boundaryCurve T r b z.1) 0 z.2) :=
  continuous_finsetSum _ fun p _ ↦ continuous_plaquetteScore_other active held S T q r b p

theorem continuous_contact (active : Finset (Plaquette 4 n))
    (held S T : Finset (Link 4 n)) (q r b : Link 4 n → SU2) :
    Continuous (fun z : ℝ × (Link 4 n → SU2) ↦ contact active held S T q r b z.1 z.2) :=
  continuous_finsetSum _ fun p _ ↦ continuous_plaquetteContact active held S T q r b p

theorem hasDerivAt_plaquetteScore_other (active : Finset (Plaquette 4 n))
    (held S T : Finset (Link 4 n)) (q r b : Link 4 n → SU2) (t : ℝ)
    (p : Plaquette 4 n) (ω : Link 4 n → SU2) :
    HasDerivAt (fun s ↦ plaquetteScore active held S q (boundaryCurve T r b s) 0 p ω)
      (plaquetteContact active held S T q r b t p ω) t := by
  by_cases hp : p ∈ active
  · simp only [plaquetteScore, plaquetteContact, hp, ↓reduceIte, boundaryCurve_zero, zero_add]
    apply SU2WilsonBlockIntegration.hasDerivAt_holonomyScore
    · exact hasDerivAt_plaquetteValues held T r b t p ω
    · intro i hi
      have hh : linkAt p i ∈ held := ((mem_filter.mp hi).2).1
      by_cases hT : linkAt p i ∈ T
      · have h := hasDerivAt_su2_left_mul
          (rotationPerturbation (q (linkAt p i)) 1 (Real.pi / 2))
          (hasDerivAt_rotationPerturbation (r (linkAt p i)) (b (linkAt p i)) t)
        simpa [boundaryCurve, hT, movingSlots, hh, rotationPerturbation,
          Submonoid.coe_mul] using h
      · simpa [boundaryCurve, hT, movingSlots, hh] using
          hasDerivAt_const_matrix
            (rotationPerturbation (q (linkAt p i)) (b (linkAt p i)) (Real.pi / 2)).val t
  · simp only [plaquetteScore, plaquetteContact, hp, ↓reduceIte]
    exact hasDerivAt_const t 0

theorem hasDerivAt_score_contact (active : Finset (Plaquette 4 n))
    (held S T : Finset (Link 4 n)) (q r b : Link 4 n → SU2) (t : ℝ) (ω : Link 4 n → SU2) :
    HasDerivAt (fun s ↦ score active held S q (boundaryCurve T r b s) 0 ω)
      (contact active held S T q r b t ω) t :=
  HasDerivAt.fun_sum (fun p _ ↦ hasDerivAt_plaquetteScore_other active held S T q r b t p ω)

theorem hasDerivAt_action_contact (active : Finset (Plaquette 4 n))
    (held S T : Finset (Link 4 n)) (q r b : Link 4 n → SU2) (t : ℝ) (ω : Link 4 n → SU2) :
    HasDerivAt (fun u ↦ deriv (fun v ↦ action active held
      (boundaryCurve S q (boundaryCurve T r b u) v) ω) 0)
      (contact active held S T q r b t ω) t := by
  have hd (u : ℝ) := (hasDerivAt_action active held S q (boundaryCurve T r b u) 0 ω).deriv
  simpa only [hd] using hasDerivAt_score_contact active held S T q r b t ω

theorem abs_plaquetteContact_le (active : Finset (Plaquette 4 n))
    (held S T : Finset (Link 4 n)) (q r b : Link 4 n → SU2) (t : ℝ)
    (p : Plaquette 4 n) (ω : Link 4 n → SU2) : |plaquetteContact active held S T q r b t p ω| ≤ 16 := by
  by_cases hp : p ∈ active
  · simp only [plaquetteContact, hp, ↓reduceIte]
    apply (SU2WilsonBlockIntegration.abs_holonomyContact_le _ _ _ _ _ _).trans
    have hS : ((movingSlots held S p).card : ℝ) ≤ 4 := by exact_mod_cast card_movingSlots_le held S p
    have hT : ((movingSlots held T p).card : ℝ) ≤ 4 := by exact_mod_cast card_movingSlots_le held T p
    have hpos : (0 : ℝ) ≤ (movingSlots held S p).card := by positivity
    have hpos' : (0 : ℝ) ≤ (movingSlots held T p).card := by positivity
    nlinarith
  · simp [plaquetteContact, hp]

theorem abs_contact_le (active : Finset (Plaquette 4 n)) (held S T : Finset (Link 4 n))
    (q r b : Link 4 n → SU2) (t : ℝ) (ω : Link 4 n → SU2) :
    |contact active held S T q r b t ω| ≤ 1024 * S.card := by
  have hsum : |contact active held S T q r b t ω| ≤ 16 * (incident S).card := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_comm] using
      Finset.sum_le_sum (s := incident S)
        (fun p _ ↦ abs_plaquetteContact_le active held S T q r b t p ω)
  have hc : ((incident S).card : ℝ) ≤ S.card * 64 := by
    exact_mod_cast WilsonPatchGeometry.card_incident_le S
  nlinarith

theorem contact_pin (active : Finset (Plaquette 4 n)) (held S T : Finset (Link 4 n))
    (q r b : Link 4 n → SU2) (ω : Link 4 n → SU2) :
    contact active held S T q r b 0 (WilsonPinnedIntegral.pin held b ω) =
      contact active held S T q r b 0 ω := by
  apply sum_congr rfl
  intro p _
  simp only [plaquetteContact, boundaryCurve_zero, plaquetteValues_pin]

theorem contact_eq_zero (active : Finset (Plaquette 4 n)) (held S T : Finset (Link 4 n))
    (q r b : Link 4 n → SU2) (t : ℝ) (hST : Disjoint (incident S) (incident T)) :
    contact active held S T q r b t = 0 := by
  ext ω
  apply sum_eq_zero
  intro p hp
  have hpT : p ∉ incident T := fun h ↦ disjoint_left.mp hST hp h
  simp [plaquetteContact, movingSlots_empty_of_not_incident held T p hpT]

/-- The original pinned Wilson density; held dummy variables integrate to one. -/
abbrev boundaryDensity (β : ℝ) (active : Finset (Plaquette 4 n))
    (held : Finset (Link 4 n)) (b : Link 4 n → SU2) : C(Link 4 n → SU2, ℝ) :=
  realDensity ((model n active).pinned held b)
    (continuous_pinned (model n active) (model_continuous n active) held b) β

theorem boundaryDensity_eq_exp (β : ℝ) (active : Finset (Plaquette 4 n))
    (held : Finset (Link 4 n)) (b : Link 4 n → SU2) (ω : Link 4 n → SU2) :
    boundaryDensity β active held b ω = Real.exp (-β * action active held b ω) :=
  realDensity_pinned_eq_exp (model n active) (model_continuous n active) β held b ω

theorem continuous_action_curve (active : Finset (Plaquette 4 n))
    (held S : Finset (Link 4 n)) (q b : Link 4 n → SU2) :
    Continuous (fun z : ℝ × (Link 4 n → SU2) ↦
      action active held (boundaryCurve S q b z.1) z.2) := by
  apply continuous_finsetSum
  intro p _
  simp only [pinnedPotential_eq]
  by_cases hp : p ∈ active
  · simp only [hp, ↓reduceIte]
    apply plaquetteEnergy.continuous.comp
    exact continuous_plaquetteValues_curve held S q b p
  · simp only [hp, ↓reduceIte]
    exact continuous_const

theorem continuous_boundaryDensity_curve (β : ℝ) (active : Finset (Plaquette 4 n))
    (held S : Finset (Link 4 n)) (q b : Link 4 n → SU2) :
    Continuous (fun z : ℝ × (Link 4 n → SU2) ↦
      boundaryDensity β active held (boundaryCurve S q b z.1) z.2) := by
  simp_rw [boundaryDensity_eq_exp]
  exact (continuous_const.mul (continuous_action_curve active held S q b)).rexp

theorem hasDerivAt_boundaryDensity (β : ℝ) (active : Finset (Plaquette 4 n))
    (held S : Finset (Link 4 n)) (q b : Link 4 n → SU2) (t : ℝ)
    (ω : Link 4 n → SU2) :
    HasDerivAt (fun s ↦ boundaryDensity β active held (boundaryCurve S q b s) ω)
      (-β * (boundaryDensity β active held (boundaryCurve S q b t) ω *
        score active held S q b t ω)) t := by
  simp_rw [boundaryDensity_eq_exp]
  apply ((hasDerivAt_action active held S q b t ω).const_mul (-β)).exp.congr_deriv
  ring

/-- Differentiate the actual normalized-Haar partition function for any real
coupling and arbitrary background and patch rotation directions. -/
theorem hasDerivAt_boundaryLogPartition (β : ℝ) (active : Finset (Plaquette 4 n))
    (held S : Finset (Link 4 n)) (q b : Link 4 n → SU2) (t : ℝ) :
    HasDerivAt (fun s ↦ boundaryLogPartition (volume : Measure SU2)
      (model n active) (model_continuous n active) β held (boundaryCurve S q b s))
      (-β * WilsonBlockElimination.expectation (Measure.pi fun _ ↦ (volume : Measure SU2))
        (boundaryDensity β active held (boundaryCurve S q b t)) (score active held S q b t)) t := by
  exact WilsonBoundaryResponse.hasDerivAt_logPartition
    (Measure.pi fun _ : Link 4 n ↦ (volume : Measure SU2)) β _ _
    (continuous_boundaryDensity_curve β active held S q b) (continuous_score active held S q b)
    (hasDerivAt_boundaryDensity β active held S q b) t (fun ω ↦ by
      rw [boundaryDensity_eq_exp]
      exact Real.exp_pos _)

/-- The genuine iterated derivative of the original boundary log partition. -/
def mixedDerivative (β : ℝ) (active : Finset (Plaquette 4 n))
    (held S T : Finset (Link 4 n)) (q r b : Link 4 n → SU2) : ℝ :=
  deriv (fun t ↦ deriv (fun s ↦ boundaryLogPartition (volume : Measure SU2)
    (model n active) (model_continuous n active) β held
      (boundaryCurve S q (boundaryCurve T r b t) s)) 0) 0

/-- The exact Haar Hessian for every pair of patches, including the mixed
derivative of the original action when their incident plaquettes overlap. -/
theorem mixedDerivative_eq_covariance_sub_contact (β : ℝ) (active : Finset (Plaquette 4 n))
    (held S T : Finset (Link 4 n)) (q r b : Link 4 n → SU2) :
    mixedDerivative β active held S T q r b =
      β ^ 2 * WilsonBlockElimination.covariance (Measure.pi fun _ ↦ (volume : Measure SU2))
        (boundaryDensity β active held b) (score active held S q b 0) (score active held T r b 0) -
      β * WilsonBlockElimination.expectation (Measure.pi fun _ ↦ (volume : Measure SU2))
        (boundaryDensity β active held b) (contact active held S T q r b 0) := by
  have hd (t : ℝ) := (hasDerivAt_boundaryLogPartition β active held S q
    (boundaryCurve T r b t) 0).deriv
  simp only [boundaryCurve_zero] at hd
  unfold mixedDerivative
  simp_rw [hd]
  have h := WilsonBoundaryResponse.hasDerivAt_logPartitionScore
    (Measure.pi fun _ ↦ (volume : Measure SU2)) β
    (fun t ↦ boundaryDensity β active held (boundaryCurve T r b t))
    (fun t ↦ score active held S q (boundaryCurve T r b t) 0)
    (score active held T r b) (contact active held S T q r b)
    (continuous_boundaryDensity_curve β active held T r b)
    (continuous_score_other active held S T q r b)
    (continuous_score active held T r b) (continuous_contact active held S T q r b)
    (hasDerivAt_boundaryDensity β active held T r b)
    (hasDerivAt_score_contact active held S T q r b) 0
    (fun ω ↦ by
      simp only [boundaryCurve_zero]
      rw [boundaryDensity_eq_exp]
      exact Real.exp_pos _)
  simpa only [boundaryCurve_zero] using h.deriv

/-- The separated-patch identity follows from the full Haar Hessian and
vanishing of the original action's contact derivative. -/
theorem mixedDerivative_eq_covariance (β : ℝ) (active : Finset (Plaquette 4 n))
    (held S T : Finset (Link 4 n)) (q r b : Link 4 n → SU2)
    (hST : Disjoint (incident S) (incident T)) :
    mixedDerivative β active held S T q r b =
      β ^ 2 * WilsonBlockElimination.covariance (Measure.pi fun _ ↦ (volume : Measure SU2))
        (boundaryDensity β active held b) (score active held S q b 0) (score active held T r b 0) := by
  rw [mixedDerivative_eq_covariance_sub_contact,
    contact_eq_zero active held S T q r b 0 hST, WilsonBlockElimination.expectation_zero,
    mul_zero, sub_zero]

/-- The covariance of two original Wilson scores as a third patch moves.
Both score marks and the density follow their actual boundary curves. -/
def scoreCovariance (β : ℝ) (active : Finset (Plaquette 4 n))
    (held S T V : Finset (Link 4 n)) (q r u b : Link 4 n → SU2) (t : ℝ) : ℝ :=
  WilsonBlockElimination.covariance (Measure.pi fun _ ↦ (volume : Measure SU2))
    (boundaryDensity β active held (boundaryCurve V u b t))
    (score active held S q (boundaryCurve V u b t) 0)
    (score active held T r (boundaryCurve V u b t) 0)

/-- Covariance differentiation for actual Wilson score marks, with both
original action contacts retained. All derivative hypotheses are discharged
by the compact Haar plaquette calculus, for every real beta. -/
theorem hasDerivAt_scoreCovariance (β : ℝ) (active : Finset (Plaquette 4 n))
    (held S T V : Finset (Link 4 n)) (q r u b : Link 4 n → SU2) (t : ℝ) :
    HasDerivAt (scoreCovariance β active held S T V q r u b)
      (WilsonBlockElimination.covariance (Measure.pi fun _ ↦ (volume : Measure SU2))
          (boundaryDensity β active held (boundaryCurve V u b t))
          (contact active held S V q u b t) (score active held T r (boundaryCurve V u b t) 0) +
        WilsonBlockElimination.covariance (Measure.pi fun _ ↦ (volume : Measure SU2))
          (boundaryDensity β active held (boundaryCurve V u b t))
          (score active held S q (boundaryCurve V u b t) 0) (contact active held T V r u b t) -
        β * WilsonBlockElimination.thirdCumulant (Measure.pi fun _ ↦ (volume : Measure SU2))
          (boundaryDensity β active held (boundaryCurve V u b t))
          (score active held S q (boundaryCurve V u b t) 0)
          (score active held T r (boundaryCurve V u b t) 0) (score active held V u b t)) t :=
  WilsonBoundaryResponse.hasDerivAt_covariance
    (Measure.pi fun _ : Link 4 n ↦ (volume : Measure SU2)) β
    (fun s ↦ boundaryDensity β active held (boundaryCurve V u b s)) (score active held V u b)
    (fun s ↦ score active held S q (boundaryCurve V u b s) 0)
    (fun s ↦ score active held T r (boundaryCurve V u b s) 0)
    (contact active held S V q u b) (contact active held T V r u b)
    (continuous_boundaryDensity_curve β active held V u b) (continuous_score active held V u b)
    (continuous_score_other active held S V q u b) (continuous_score_other active held T V r u b)
    (continuous_contact active held S V q u b) (continuous_contact active held T V r u b)
    (hasDerivAt_boundaryDensity β active held V u b)
    (hasDerivAt_score_contact active held S V q u b)
    (hasDerivAt_score_contact active held T V r u b) t (fun ω ↦ by
      rw [boundaryDensity_eq_exp]
      exact Real.exp_pos _)

/-- The genuine iterated three-patch derivative of the original Haar log
partition function, with the third patch applied to the outer background. -/
def thirdDerivative (β : ℝ) (active : Finset (Plaquette 4 n))
    (held S T V : Finset (Link 4 n)) (q r u b : Link 4 n → SU2) : ℝ :=
  deriv (fun t ↦ mixedDerivative β active held S T q r (boundaryCurve V u b t)) 0

/-- Three plaquette-separated patches have a true third logarithmic response
equal to the third connected Wilson score, with its original sign and beta
power. This identity holds for every real coupling. -/
theorem thirdDerivative_eq_cumulant (β : ℝ) (active : Finset (Plaquette 4 n))
    (held S T V : Finset (Link 4 n)) (q r u b : Link 4 n → SU2)
    (hST : Disjoint (incident S) (incident T))
    (hSV : Disjoint (incident S) (incident V))
    (hTV : Disjoint (incident T) (incident V)) :
    thirdDerivative β active held S T V q r u b =
      -β ^ 3 * WilsonBlockElimination.thirdCumulant
        (Measure.pi fun _ ↦ (volume : Measure SU2)) (boundaryDensity β active held b)
        (score active held S q b 0) (score active held T r b 0) (score active held V u b 0) := by
  have ht (t : ℝ) : mixedDerivative β active held S T q r (boundaryCurve V u b t) =
      β ^ 2 * scoreCovariance β active held S T V q r u b t :=
    mixedDerivative_eq_covariance β active held S T q r (boundaryCurve V u b t) hST
  unfold thirdDerivative
  simp_rw [ht]
  have hd := (hasDerivAt_scoreCovariance β active held S T V q r u b 0).const_mul (β ^ 2)
  rw [hd.deriv]
  rw [contact_eq_zero active held S V q u b 0 hSV,
    contact_eq_zero active held T V r u b 0 hTV]
  simp only [boundaryCurve_zero, WilsonBlockElimination.covariance, zero_mul, mul_zero,
    WilsonBlockElimination.expectation_zero, sub_zero, zero_add]
  ring

/-- Strong-coupling decay of the true mixed derivative. The rate precedes all
volumes, pinning, plaquette masks, background fields and rotation directions.
The explicit prefactor contains no ambient-volume term. -/
theorem uniform_mixedDerivative {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 4) :
    ∃ κ > 0, ∀ (n : ℕ) (active : Finset (Plaquette 4 n))
      (held S T : Finset (Link 4 n)) (q r b : Link 4 n → SU2),
      (collar S).Nonempty → (collar T).Nonempty → 1 < polymerDist S T →
      |mixedDerivative β active held S T q r b| ≤
        3 * β ^ 2 * (256 * S.card) * (256 * T.card) *
          Real.exp (768 * (S.card + T.card) + 2 * κ) *
          Real.exp (-κ * polymerDist S T) := by
  obtain ⟨κ, hκ, hc⟩ := covariance_clustering 4 (volume : Measure SU2) (1 : SU2) hβ hβ0
  refine ⟨κ, hκ, ?_⟩
  intro n active held S T q r b hS hT hsep
  rw [mixedDerivative_eq_covariance β active held S T q r b
    (disjoint_incident_of_separation hsep), abs_mul, abs_of_nonneg (sq_nonneg β)]
  have h := hc ((model n active).pinned held b)
    (continuous_pinned (model n active) (model_continuous n active) held b)
    (collar S) (collar T) hS (localScore active held S q b 0) (localScore active held T r b 0)
    (256 * S.card) (256 * T.card)
    (fun v ↦ abs_score_le active held S q b 0 _)
    (fun v ↦ abs_score_le active held T r b 0 _)
  rw [localScore_reconstruct, localScore_reconstruct] at h
  apply (mul_le_mul_of_nonneg_left h (sq_nonneg β)).trans
  have he : Real.exp (3 * (collar S).card + 3 * (collar T).card) *
      Real.exp (-κ * polymerDist (collar S) (collar T)) ≤
      Real.exp (768 * (S.card + T.card) + 2 * κ) *
        Real.exp (-κ * polymerDist S T) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hsS : ((collar S).card : ℝ) ≤ S.card * 256 := by
      exact_mod_cast card_collar_le S
    have hsT : ((collar T).card : ℝ) ≤ T.card * 256 := by
      exact_mod_cast card_collar_le T
    have hd := separation_collar hS hT
    nlinarith
  have hp : 0 ≤ 3 * β ^ 2 * (256 * (S.card : ℝ)) * (256 * T.card) := by positivity
  simpa only [mul_assoc, mul_left_comm, mul_comm] using mul_le_mul_of_nonneg_left he hp

/-- An unconditional bound for the actual Haar Hessian, retaining contacts
for overlapping patches. It holds for every real coupling. -/
theorem abs_mixedDerivative_le (β : ℝ) (active : Finset (Plaquette 4 n))
    (held S T : Finset (Link 4 n)) (q r b : Link 4 n → SU2) :
    |mixedDerivative β active held S T q r b| ≤
      2 * β ^ 2 * (256 * S.card) * (256 * T.card) + |β| * (1024 * S.card) := by
  have hW : ∀ ω, 0 < boundaryDensity β active held b ω := fun ω ↦ by
    rw [boundaryDensity_eq_exp]
    exact Real.exp_pos _
  have hc := WilsonBlockElimination.abs_covariance_le
    (Measure.pi fun _ : Link 4 n ↦ (volume : Measure SU2))
    (boundaryDensity β active held b) (score active held S q b 0)
    (score active held T r b 0) hW (by positivity) (by positivity)
    (abs_score_le active held S q b 0) (abs_score_le active held T r b 0)
  have hj := WilsonBlockElimination.abs_expectation_le
    (Measure.pi fun _ : Link 4 n ↦ (volume : Measure SU2))
    (boundaryDensity β active held b) (contact active held S T q r b 0) hW
    (abs_contact_le active held S T q r b 0)
  rw [mixedDerivative_eq_covariance_sub_contact]
  apply (abs_sub _ _).trans
  simp only [abs_mul, abs_of_nonneg (sq_nonneg β)]
  exact (add_le_add (mul_le_mul_of_nonneg_left hc (sq_nonneg β))
    (mul_le_mul_of_nonneg_left hj (abs_nonneg β))).trans_eq (by ring)

/-- Actual iterated single-link derivatives along the two prescribed frame
fields. Links outside the held set still appear, with their actual response. -/
def responseArray (β : ℝ) (active : Finset (Plaquette 4 n))
    (held : Finset (Link 4 n)) (q r b : Link 4 n → SU2) : Link 4 n → Link 4 n → ℝ :=
  fun l m ↦ mixedDerivative β active held {l} {m} q r b

/-- The nearby-pair bound includes the diagonal action contact. -/
def nearResponseBound (β : ℝ) : ℝ := 2 * β ^ 2 * 256 ^ 2 + |β| * 1024

/-- One envelope covers nearby contacts and separated connected responses. -/
def responseEnvelopeBound (β κ : ℝ) : ℝ :=
  3 * β ^ 2 * 256 ^ 2 * Real.exp (1536 + 2 * κ) +
    nearResponseBound β * Real.exp κ

theorem responseEnvelopeBound_nonneg (β κ : ℝ) : 0 ≤ responseEnvelopeBound β κ := by
  unfold responseEnvelopeBound nearResponseBound
  positivity

/-- A single exponential envelope holds for all link pairs, including nearby
and coincident pairs. The rate precedes volume, boundary data and frames. -/
theorem uniform_responseArray_envelope {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 4) :
    ∃ κ > 0, ∀ (n : ℕ) (active : Finset (Plaquette 4 n))
      (held : Finset (Link 4 n)) (q r b : Link 4 n → SU2) (l m : Link 4 n),
      |responseArray β active held q r b l m| ≤
        responseEnvelopeBound β κ * Real.exp (-κ * dist l m) := by
  obtain ⟨κ, hκ, h⟩ := uniform_mixedDerivative hβ hβ0
  refine ⟨κ, hκ, ?_⟩
  intro n active held q r b l m
  have hnear : 0 ≤ nearResponseBound β := by unfold nearResponseBound; positivity
  have hfar : 0 ≤ 3 * β ^ 2 * 256 ^ 2 * Real.exp (1536 + 2 * κ) := by positivity
  by_cases hsep : 1 < dist l m
  · have hh := h n active held {l} {m} q r b (singleton_collar_nonempty l)
      (singleton_collar_nonempty m) (by simpa only [polymerDist_singletons] using hsep)
    have hbase : |responseArray β active held q r b l m| ≤
        (3 * β ^ 2 * 256 ^ 2 * Real.exp (1536 + 2 * κ)) *
          Real.exp (-κ * dist l m) := by
      simpa only [responseArray, card_singleton, Nat.cast_one, mul_one,
        one_add_one_eq_two, show (768 : ℝ) * 2 = 1536 by norm_num,
        polymerDist_singletons, pow_two, mul_assoc] using hh
    apply hbase.trans
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    exact le_add_of_nonneg_right (mul_nonneg hnear (Real.exp_pos _).le)
  · have hh := abs_mixedDerivative_le β active held {l} {m} q r b
    have hbase : |responseArray β active held q r b l m| ≤ nearResponseBound β := by
      simpa only [responseArray, nearResponseBound, card_singleton, Nat.cast_one,
        mul_one, pow_two, mul_assoc] using hh
    have he : 1 ≤ Real.exp κ * Real.exp (-κ * dist l m) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      have hd : dist l m ≤ 1 := le_of_not_gt hsep
      nlinarith
    apply hbase.trans
    have hp := mul_le_mul_of_nonneg_left he hnear
    dsimp only [responseEnvelopeBound]
    nlinarith [mul_nonneg hfar (Real.exp_pos (-κ * dist l m)).le]

/-- Total boundary influence is uniformly summable at strong coupling.
The same constants cover every volume, plaquette mask, held set, background
and choice of the two link rotation frames. -/
theorem uniform_weightedResponseSeminorm {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 4) :
    ∃ η > 0, ∃ C ≥ 0, ∀ (n : ℕ) (active : Finset (Plaquette 4 n))
      (held : Finset (Link 4 n)) (q r b : Link 4 n → SU2),
      WilsonBoundaryResponse.weightedResponseSeminorm η
        (responseArray β active held q r b) ≤ C := by
  obtain ⟨κ, hκ, h⟩ := uniform_responseArray_envelope hβ hβ0
  have hcount : 0 ≤ exponentialVolumeBound 4 (κ / 2) := by
    unfold exponentialVolumeBound
    positivity
  refine ⟨κ / 2, by positivity,
    responseEnvelopeBound β κ * exponentialVolumeBound 4 (κ / 2),
    mul_nonneg (responseEnvelopeBound_nonneg β κ) hcount, ?_⟩
  intro n active held q r b
  apply WilsonBoundaryResponse.weightedResponseSeminorm_le_of_envelope
    (κ / 2) κ _ (responseEnvelopeBound_nonneg β κ) hcount
    (h n active held q r b)
  intro l
  rw [show κ - κ / 2 = κ / 2 by ring]
  exact sum_exp_dist_le (by decide) (by positivity) l

/-- Third connected responses of the actual singleton Wilson scores, under
the original fixed-boundary Haar density. The three frames are independent. -/
def scoreThirdArray (β : ℝ) (active : Finset (Plaquette 4 n))
    (held : Finset (Link 4 n)) (q r u b : Link 4 n → SU2) :
    Link 4 n → Link 4 n → Link 4 n → ℝ := fun l m k ↦
  WilsonBlockElimination.thirdCumulant (Measure.pi fun _ ↦ (volume : Measure SU2))
    (boundaryDensity β active held b) (score active held {l} q b 0)
    (score active held {m} r b 0) (score active held {k} u b 0)

/-- Tree decay includes all triples, with no separation assumption. The
rate is chosen before the volume, pinned values, plaquette mask and frames. -/
theorem uniform_scoreThirdArray_envelope {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 4) :
    ∃ κ > 0, ∀ (n : ℕ) (active : Finset (Plaquette 4 n))
      (held : Finset (Link 4 n)) (q r u b : Link 4 n → SU2) (l m k : Link 4 n),
      |scoreThirdArray β active held q r u b l m k| ≤
        thirdCumulantEnvelope 256 κ *
          Real.exp (-(κ / 2) * WilsonBoundaryResponse.threeTreeLength l m k) := by
  obtain ⟨κ, hκ, hc⟩ := thirdCumulant_collar_clustering
    (volume : Measure SU2) (1 : SU2) hβ hβ0
  refine ⟨κ, hκ, ?_⟩
  intro n active held q r u b l m k
  exact hc ((model n active).pinned held b)
    (continuous_pinned (model n active) (model_continuous n active) held b)
    l m k (score active held {l} q b 0) (score active held {m} r b 0)
    (score active held {k} u b 0) 256 (by norm_num)
    (score_local active held {l} q b 0) (score_local active held {m} r b 0)
    (score_local active held {k} u b 0)
    (by simpa using abs_score_le active held {l} q b 0)
    (by simpa using abs_score_le active held {m} r b 0)
    (by simpa using abs_score_le active held {k} u b 0)

/-- A finite total third-response budget, uniform over every boundary datum
and every volume. The chosen exponent is one quarter of the clustering rate. -/
theorem uniform_weightedThirdSeminorm {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 4) :
    ∃ η > 0, ∃ C ≥ 0, ∀ (n : ℕ) (active : Finset (Plaquette 4 n))
      (held : Finset (Link 4 n)) (q r u b : Link 4 n → SU2),
      WilsonBoundaryResponse.weightedThirdSeminorm η
        (scoreThirdArray β active held q r u b) ≤ C := by
  obtain ⟨κ, hκ, hc⟩ := uniform_scoreThirdArray_envelope hβ hβ0
  have hM : 0 ≤ thirdCumulantEnvelope 256 κ := by
    unfold thirdCumulantEnvelope
    positivity
  have hV : 0 ≤ exponentialVolumeBound 4 (κ / 8) := by
    unfold exponentialVolumeBound
    positivity
  refine ⟨κ / 4, by positivity,
    thirdCumulantEnvelope 256 κ * (exponentialVolumeBound 4 (κ / 8)) ^ 2,
    by positivity, ?_⟩
  intro n active held q r u b
  apply WilsonBoundaryResponse.weightedThirdSeminorm_le_of_envelope
    (κ / 4) (κ / 2) (by linarith) _ hM hV (hc n active held q r u b)
  intro l
  rw [show (κ / 2 - κ / 4) / 2 = κ / 8 by ring]
  exact sum_exp_dist_le (by decide) (by positivity) l

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

/-- The patch-size prefactor is constant on the separated singleton family,
including arbitrary volume-dependent backgrounds and rotation directions. -/
theorem growing_mixedDerivative_bound {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 4) :
    ∃ κ > 0, ∀ (r : ℕ) (active : Finset (Plaquette 4 (familyVolume r)))
      (held : Finset (Link 4 (familyVolume r))) (q u b : Link 4 (familyVolume r) → SU2),
      |mixedDerivative β active held (firstPatch r) (secondPatch r) q u b| ≤
        3 * β ^ 2 * 256 ^ 2 * Real.exp (1536 + 2 * κ) *
          Real.exp (-κ * ((r : ℝ) + 3)) := by
  obtain ⟨κ, hκ, hc⟩ := uniform_mixedDerivative hβ hβ0
  refine ⟨κ, hκ, ?_⟩
  intro r active held q u b
  have hS : (collar (firstPatch r)).Nonempty := singleton_zero_collar_nonempty _
  have hT : (collar (secondPatch r)).Nonempty := singleton_zero_collar_nonempty _
  have hd := growing_separation r
  have h := hc (familyVolume r) active held (firstPatch r) (secondPatch r) q u b hS hT
    (by have := Nat.cast_nonneg (α := ℝ) r; linarith)
  have hcard : (firstPatch r).card = 1 ∧ (secondPatch r).card = 1 := by
    simp [firstPatch, secondPatch]
  rw [hcard.1, hcard.2] at h
  norm_num only [Nat.cast_one, mul_one, one_add_one_eq_two, mul_one, mul_add,
    show (768 : ℝ) * 2 = 1536 by norm_num] at h
  have he : Real.exp (-κ * polymerDist (firstPatch r) (secondPatch r)) ≤
      Real.exp (-κ * ((r : ℝ) + 3)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hp : 0 ≤ 3 * β ^ 2 * 256 ^ 2 * Real.exp (1536 + 2 * κ) := by positivity
  apply h.trans
  convert mul_le_mul_of_nonneg_left he hp using 1 <;> ring

theorem tendsto_growing_mixedDerivative {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 4)
    (active : ∀ r, Finset (Plaquette 4 (familyVolume r)))
    (held : ∀ r, Finset (Link 4 (familyVolume r)))
    (q u b : ∀ r, Link 4 (familyVolume r) → SU2) :
    Tendsto (fun r ↦ mixedDerivative β (active r) (held r)
      (firstPatch r) (secondPatch r) (q r) (u r) (b r)) atTop (𝓝 0) := by
  obtain ⟨κ, hκ, hc⟩ := growing_mixedDerivative_bound hβ hβ0
  have ht : Tendsto (fun r : ℕ ↦ κ * ((r : ℝ) + 3)) atTop atTop :=
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).const_mul_atTop hκ
  have he : Tendsto (fun r : ℕ ↦ Real.exp (-κ * ((r : ℝ) + 3))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp ht
  have hb := he.const_mul (3 * β ^ 2 * 256 ^ 2 * Real.exp (1536 + 2 * κ))
  rw [mul_zero] at hb
  apply squeeze_zero_norm (fun r ↦ ?_) hb
  simpa only [Real.norm_eq_abs] using hc r (active r) (held r) (q r) (u r) (b r)

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
#print axioms contDiff_boundaryCurve
#print axioms abs_score_le
#print axioms hasDerivAt_boundaryLogPartition
#print axioms hasDerivAt_contact_zero
#print axioms hasDerivAt_action_contact
#print axioms abs_contact_le
#print axioms contact_eq_zero
#print axioms mixedDerivative_eq_covariance_sub_contact
#print axioms mixedDerivative_eq_covariance
#print axioms uniform_mixedDerivative
#print axioms hasDerivAt_scoreCovariance
#print axioms thirdDerivative_eq_cumulant
#print axioms uniform_responseArray_envelope
#print axioms uniform_weightedResponseSeminorm
#print axioms tendsto_growing_mixedDerivative
#print axioms growing_separation
#print axioms growing_family_bound
#print axioms tendsto_growing_response
end Mettapedia.QuantumTheory.YangMills.SU2BoundaryResponse

import Mettapedia.GSLT.Causality.DoCalculus.BowArc
import Mettapedia.GSLT.Causality.DoCalculus.ForkArc
import Mettapedia.GSLT.Causality.DoCalculus.QueryCounts
import Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets

/-!
# The bow hedge as a credal interval

The two bow models share one observational joint. `P(Y = true, X = true)` and
`P(X = true)` are sums of that joint. From those two sums the interventional
value is the natural bound `[P(y, x), P(y, x) + 1 - P(x)]`, an `Interval`.
Every conditional table with that `(X, Y)` margin has its `do(X = true)` mass
inside the interval, and the two shipped models meet the endpoints.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Mettapedia.GSLT.Causality.DoCalculus

open Mettapedia.Logic.EvidenceStateInsufficiency
open Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets
open Mettapedia.ProbabilityTheory.BayesianNetworks
open BayesianNetwork
open DirectedGraph
open scoped BigOperators ENNReal

/-! ## Extended-nonnegative arithmetic for the natural bound -/

lemma mul_le_of_le_one_left {a b : ℝ≥0∞} (ha : a ≤ 1) : a * b ≤ b := by
  have h := IsOrderedMonoid.mul_le_mul_left a 1 ha b
  simpa using h

lemma mul_le_of_le_one_right {a b : ℝ≥0∞} (hb : b ≤ 1) : a * b ≤ a := by
  have h := IsOrderedMonoid.mul_le_mul_right b 1 hb a
  simpa using h

lemma enn_pair (a b c d : ℝ≥0∞) : (a + b) + (c + d) = (a + c) + (b + d) := by
  calc (a + b) + (c + d)
      = a + (b + (c + d)) := by rw [add_assoc]
    _ = a + ((b + c) + d) := by rw [← add_assoc b c d]
    _ = a + ((c + b) + d) := by rw [add_comm b c]
    _ = a + (c + (b + d)) := by rw [add_assoc c b d]
    _ = (a + c) + (b + d) := by rw [← add_assoc]

lemma le_one_left_of_add {a b : ℝ≥0∞} (h : a + b = 1) : a ≤ 1 :=
  (le_self_add (a := a) (b := b)).trans (le_of_eq h)

lemma pmf_bool_sum (p : PMF Bool) : p false + p true = 1 := by
  rw [← tsum_bool]
  exact p.tsum_coe

lemma natural_bound_toReal {atom doM treat : ℝ≥0∞}
    (hatom : atom ≤ doM) (hupper : doM ≤ atom + (1 - treat))
    (hdo : doM ≤ 1) (htreat : treat ≤ 1) :
    atom.toReal ≤ doM.toReal ∧ doM.toReal ≤ atom.toReal + 1 - treat.toReal := by
  have hatom_top : atom ≠ ∞ :=
    ne_top_of_le_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top hdo) hatom
  have hdo_top : doM ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hdo
  have hsub_top : 1 - treat ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have hsum_top : atom + (1 - treat) ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hatom_top, hsub_top⟩
  refine ⟨ENNReal.toReal_mono hdo_top hatom, ?_⟩
  calc doM.toReal
      ≤ (atom + (1 - treat)).toReal := ENNReal.toReal_mono hsum_top hupper
    _ = atom.toReal + (1 - treat).toReal := ENNReal.toReal_add hatom_top hsub_top
    _ = atom.toReal + (1 - treat.toReal) := by
        rw [ENNReal.toReal_sub_of_le htreat ENNReal.one_ne_top, ENNReal.toReal_one]
    _ = atom.toReal + 1 - treat.toReal := by rw [add_sub]

/-- The finite natural bound, written as two-point sums.
`px` and `py` are conditional rows; each relevant row sums to one. -/
lemma factor_natural_bound
    (pu : Bool → ℝ≥0∞) (px : Bool → Bool → ℝ≥0∞)
    (py : Bool → Bool → Bool → ℝ≥0∞)
    (hpu : pu false + pu true = 1)
    (hpxF : px false false + px false true = 1)
    (hpxT : px true false + px true true = 1)
    (hpyF : py false true false + py false true true = 1)
    (hpyT : py true true false + py true true true = 1) :
    pu false * (px false true * py false true true) +
        pu true * (px true true * py true true true) ≤
      pu false * py false true true + pu true * py true true true ∧
    pu false * py false true true + pu true * py true true true ≤
      (pu false * (px false true * py false true true) +
        pu true * (px true true * py true true true)) +
      (1 - (pu false * px false true + pu true * px true true)) ∧
    pu false * py false true true + pu true * py true true true ≤ 1 ∧
    pu false * px false true + pu true * px true true ≤ 1 := by
  have hpxFT : px false true ≤ 1 := by
    have hcomm : px false true + px false false = 1 := by rw [add_comm, hpxF]
    exact le_one_left_of_add hcomm
  have hpxTT : px true true ≤ 1 := by
    have hcomm : px true true + px true false = 1 := by rw [add_comm, hpxT]
    exact le_one_left_of_add hcomm
  have hpyFT : py false true true ≤ 1 := by
    have hcomm : py false true true + py false true false = 1 := by rw [add_comm, hpyF]
    exact le_one_left_of_add hcomm
  have hpyTT : py true true true ≤ 1 := by
    have hcomm : py true true true + py true true false = 1 := by rw [add_comm, hpyT]
    exact le_one_left_of_add hcomm
  let atom := pu false * (px false true * py false true true) +
    pu true * (px true true * py true true true)
  let doM := pu false * py false true true + pu true * py true true true
  let treat := pu false * px false true + pu true * px true true
  let cross := pu false * (px false false * py false true true) +
    pu true * (px true false * py true true true)
  let falseMarg := pu false * px false false + pu true * px true false
  have hlow : atom ≤ doM := by
    have hF : px false true * py false true true ≤ py false true true :=
      mul_le_of_le_one_left hpxFT
    have hT : px true true * py true true true ≤ py true true true :=
      mul_le_of_le_one_left hpxTT
    exact add_le_add
      (IsOrderedMonoid.mul_le_mul_right _ _ hF (pu false))
      (IsOrderedMonoid.mul_le_mul_right _ _ hT (pu true))
  have hsplitF : pu false * py false true true =
      pu false * (px false false * py false true true) +
        pu false * (px false true * py false true true) := by
    calc pu false * py false true true
        = pu false * ((px false false + px false true) * py false true true) := by
          rw [hpxF, one_mul]
      _ = pu false * (px false false * py false true true +
            px false true * py false true true) := by rw [add_mul]
      _ = pu false * (px false false * py false true true) +
            pu false * (px false true * py false true true) := by rw [mul_add]
  have hsplitT : pu true * py true true true =
      pu true * (px true false * py true true true) +
        pu true * (px true true * py true true true) := by
    calc pu true * py true true true
        = pu true * ((px true false + px true true) * py true true true) := by
          rw [hpxT, one_mul]
      _ = pu true * (px true false * py true true true +
            px true true * py true true true) := by rw [add_mul]
      _ = pu true * (px true false * py true true true) +
            pu true * (px true true * py true true true) := by rw [mul_add]
  have hdo_split : doM = atom + cross := by
    dsimp only [doM]
    calc pu false * py false true true + pu true * py true true true
        = (pu false * (px false false * py false true true) +
            pu false * (px false true * py false true true)) +
          (pu true * (px true false * py true true true) +
            pu true * (px true true * py true true true)) := by rw [hsplitF, hsplitT]
      _ = cross + atom := by rw [enn_pair]
      _ = atom + cross := by rw [add_comm]
  have hcrossF : pu false * (px false false * py false true true) ≤
      pu false * px false false := by
    exact IsOrderedMonoid.mul_le_mul_right _ _
      (mul_le_of_le_one_right hpyFT) (pu false)
  have hcrossT : pu true * (px true false * py true true true) ≤
      pu true * px true false := by
    exact IsOrderedMonoid.mul_le_mul_right _ _
      (mul_le_of_le_one_right hpyTT) (pu true)
  have hcross : cross ≤ falseMarg := add_le_add hcrossF hcrossT
  have hsum : treat + falseMarg = 1 := by
    calc treat + falseMarg
        = (pu false * px false true + pu true * px true true) +
            (pu false * px false false + pu true * px true false) := rfl
      _ = (pu false * px false true + pu false * px false false) +
            (pu true * px true true + pu true * px true false) := by
          rw [enn_pair]
      _ = pu false * (px false true + px false false) +
            pu true * (px true true + px true false) := by rw [mul_add, mul_add]
      _ = pu false * 1 + pu true * 1 := by
          rw [add_comm (px false true), hpxF, add_comm (px true true), hpxT]
      _ = pu false + pu true := by rw [mul_one, mul_one]
      _ = 1 := hpu
  have htreat : treat ≤ 1 :=
    (le_self_add (a := treat) (b := falseMarg)).trans (le_of_eq hsum)
  have hfalse : falseMarg = 1 - treat := by
    have hcomm : falseMarg + treat = 1 := by rw [add_comm, hsum]
    exact ENNReal.eq_sub_of_add_eq
      (ne_top_of_le_ne_top ENNReal.one_ne_top htreat) hcomm
  have hupper : doM ≤ atom + (1 - treat) := by
    calc doM = atom + cross := hdo_split
      _ ≤ atom + falseMarg :=
          IsOrderedAddMonoid.add_le_add_right cross falseMarg hcross atom
      _ = atom + (1 - treat) := by rw [hfalse]
  have hdo : doM ≤ 1 := by
    calc doM ≤ pu false + pu true :=
          add_le_add (mul_le_of_le_one_right hpyFT) (mul_le_of_le_one_right hpyTT)
      _ = 1 := hpu
  exact ⟨hlow, hupper, hdo, htreat⟩

lemma weighted_py_sum
    (puF puT pxF pxT pyFf pyFt pyTf pyTt : ℝ≥0∞)
    (hpyF : pyFf + pyFt = 1) (hpyT : pyTf + pyTt = 1) :
    (puF * (pxF * pyFf) + puT * (pxT * pyTf)) +
        (puF * (pxF * pyFt) + puT * (pxT * pyTt)) =
      puF * pxF + puT * pxT := by
  calc (puF * (pxF * pyFf) + puT * (pxT * pyTf)) +
        (puF * (pxF * pyFt) + puT * (pxT * pyTt))
      = (puF * (pxF * pyFf) + puF * (pxF * pyFt)) +
          (puT * (pxT * pyTf) + puT * (pxT * pyTt)) := by
        exact enn_pair _ _ _ _
    _ = puF * (pxF * pyFf + pxF * pyFt) +
          puT * (pxT * pyTf + pxT * pyTt) := by rw [mul_add, mul_add]
    _ = puF * (pxF * (pyFf + pyFt)) + puT * (pxT * (pyTf + pyTt)) := by
        rw [show pxF * pyFf + pxF * pyFt = pxF * (pyFf + pyFt) from (mul_add _ _ _).symm,
          show pxT * pyTf + pxT * pyTt = pxT * (pyTf + pyTt) from (mul_add _ _ _).symm]
    _ = puF * (pxF * 1) + puT * (pxT * 1) := by rw [hpyF, hpyT]
    _ = puF * pxF + puT * pxT := by rw [mul_one, mul_one]

/-! ## Bow factors of an arbitrary conditional table -/

lemma bow_parent_u_empty (v : Bow) :
    v ∈ (network (β := Bool) bowGraph bowAcyclic).parents Bow.u → False := by
  intro h
  cases v <;> simp [BayesianNetwork.parents, DirectedGraph.parents, bowGraph] at h

lemma bow_parent_x (v : Bow) :
    v ∈ (network (β := Bool) bowGraph bowAcyclic).parents Bow.x ↔ v = Bow.u := by
  cases v <;> simp [BayesianNetwork.parents, DirectedGraph.parents, bowGraph]

lemma bow_parent_y (v : Bow) :
    v ∈ (network (β := Bool) bowGraph bowAcyclic).parents Bow.y ↔
      v = Bow.u ∨ v = Bow.x := by
  cases v <;> simp [BayesianNetwork.parents, DirectedGraph.parents, bowGraph]

noncomputable def bowPU
    (cpt : (network (β := Bool) bowGraph bowAcyclic).DiscreteCPT) (u : Bool) : ℝ≥0∞ :=
  cpt.cpt Bow.u
    (DiscreteCPT.parentAssignOfConfig cpt (bowOf false false false) Bow.u) u

noncomputable def bowPX
    (cpt : (network (β := Bool) bowGraph bowAcyclic).DiscreteCPT) (u x : Bool) : ℝ≥0∞ :=
  cpt.cpt Bow.x
    (DiscreteCPT.parentAssignOfConfig cpt (bowOf u false false) Bow.x) x

noncomputable def bowPY
    (cpt : (network (β := Bool) bowGraph bowAcyclic).DiscreteCPT) (u x y : Bool) : ℝ≥0∞ :=
  cpt.cpt Bow.y
    (DiscreteCPT.parentAssignOfConfig cpt (bowOf u x false) Bow.y) y

lemma bow_pu_sum (cpt : (network (β := Bool) bowGraph bowAcyclic).DiscreteCPT) :
    bowPU cpt false + bowPU cpt true = 1 := by
  simpa [bowPU] using pmf_bool_sum (cpt.cpt Bow.u
    (DiscreteCPT.parentAssignOfConfig cpt (bowOf false false false) Bow.u))

lemma bow_px_sum (cpt : (network (β := Bool) bowGraph bowAcyclic).DiscreteCPT) (u : Bool) :
    bowPX cpt u false + bowPX cpt u true = 1 := by
  simpa [bowPX] using pmf_bool_sum (cpt.cpt Bow.x
    (DiscreteCPT.parentAssignOfConfig cpt (bowOf u false false) Bow.x))

lemma bow_py_sum (cpt : (network (β := Bool) bowGraph bowAcyclic).DiscreteCPT)
    (u x : Bool) : bowPY cpt u x false + bowPY cpt u x true = 1 := by
  simpa [bowPY] using pmf_bool_sum (cpt.cpt Bow.y
    (DiscreteCPT.parentAssignOfConfig cpt (bowOf u x false) Bow.y))

lemma bow_pu_invariant (cpt : (network (β := Bool) bowGraph bowAcyclic).DiscreteCPT)
    (f : Bow → Bool) : cpt.nodeProb f Bow.u = bowPU cpt (f Bow.u) := by
  unfold DiscreteCPT.nodeProb bowPU
  apply congr_arg (fun pa => cpt.cpt Bow.u pa (f Bow.u))
  funext v hv
  exact (bow_parent_u_empty v hv).elim

lemma bow_px_invariant (cpt : (network (β := Bool) bowGraph bowAcyclic).DiscreteCPT)
    (f : Bow → Bool) : cpt.nodeProb f Bow.x = bowPX cpt (f Bow.u) (f Bow.x) := by
  unfold DiscreteCPT.nodeProb bowPX
  apply congr_arg (fun pa => cpt.cpt Bow.x pa (f Bow.x))
  funext v hv
  have hv' : v = Bow.u := (bow_parent_x v).1 hv
  subst hv'
  rfl

lemma bow_py_invariant (cpt : (network (β := Bool) bowGraph bowAcyclic).DiscreteCPT)
    (f : Bow → Bool) :
    cpt.nodeProb f Bow.y = bowPY cpt (f Bow.u) (f Bow.x) (f Bow.y) := by
  unfold DiscreteCPT.nodeProb bowPY
  apply congr_arg (fun pa => cpt.cpt Bow.y pa (f Bow.y))
  funext v hv
  rcases (bow_parent_y v).1 hv with rfl | rfl
  · rfl
  · rfl

lemma bow_joint_bits (cpt : (network (β := Bool) bowGraph bowAcyclic).DiscreteCPT)
    (u x y : Bool) :
    cpt.jointWeight (bowOf u x y) =
      bowPU cpt u * (bowPX cpt u x * bowPY cpt u x y) := by
  unfold DiscreteCPT.jointWeight
  rw [prod_bow]
  rw [bow_pu_invariant cpt (bowOf u x y), bow_px_invariant cpt (bowOf u x y),
    bow_py_invariant cpt (bowOf u x y)]
  simp [bowOf]

lemma bow_trunc_bits (cpt : (network (β := Bool) bowGraph bowAcyclic).DiscreteCPT)
    (u x y : Bool) :
    truncatedWeight bowGraph bowAcyclic cpt doXTrue (bowOf u x y) =
      (if x = true then 1 else 0) * (bowPU cpt u * bowPY cpt u x y) := by
  unfold truncatedWeight
  rw [prod_bow]
  have hu : truncatedFactor bowGraph bowAcyclic cpt doXTrue (bowOf u x y) Bow.u =
      bowPU cpt u := by
    have hne : Bow.u ≠ Bow.x := by decide
    simp only [truncatedFactor, doXTrue, if_neg hne, cptAt_eq_nodeProb]
    exact bow_pu_invariant cpt (bowOf u x y)
  have hx : truncatedFactor bowGraph bowAcyclic cpt doXTrue (bowOf u x y) Bow.x =
      if x = true then 1 else 0 := by
    by_cases hxt : x = true
    · simp [truncatedFactor, doXTrue, bowOf, hxt]
    · simp [truncatedFactor, doXTrue, bowOf, hxt]
  have hy : truncatedFactor bowGraph bowAcyclic cpt doXTrue (bowOf u x y) Bow.y =
      bowPY cpt u x y := by
    have hne : Bow.y ≠ Bow.x := by decide
    simp only [truncatedFactor, doXTrue, if_neg hne, cptAt_eq_nodeProb]
    exact bow_py_invariant cpt (bowOf u x y)
  rw [hu, hx, hy]
  exact mul_left_comm _ _ _

/-- `P(X = x, Y = y)`, the sum of `jointWeight` over the matching configurations. -/
noncomputable def bowAtom
    (cpt : (network (β := Bool) bowGraph bowAcyclic).DiscreteCPT) (x y : Bool) : ℝ≥0∞ :=
  ∑ f, if f Bow.x = x ∧ f Bow.y = y then cpt.jointWeight f else 0

/-- `P(X = x)`, the sum of `jointWeight` over the matching configurations. -/
noncomputable def bowTreatMass
    (cpt : (network (β := Bool) bowGraph bowAcyclic).DiscreteCPT) (x : Bool) : ℝ≥0∞ :=
  ∑ f, if f Bow.x = x then cpt.jointWeight f else 0

lemma bow_config_atom (cpt : (network (β := Bool) bowGraph bowAcyclic).DiscreteCPT)
    (u x y x0 y0 : Bool) :
    (if (bowOf u x y) Bow.x = x0 ∧ (bowOf u x y) Bow.y = y0 then
        cpt.jointWeight (bowOf u x y) else 0) =
      if x = x0 ∧ y = y0 then
        bowPU cpt u * (bowPX cpt u x * bowPY cpt u x y) else 0 := by
  have hxproj : (bowOf u x y) Bow.x = x := rfl
  have hyproj : (bowOf u x y) Bow.y = y := rfl
  rw [hxproj, hyproj, bow_joint_bits]

lemma bow_config_do (cpt : (network (β := Bool) bowGraph bowAcyclic).DiscreteCPT)
    (u x y : Bool) :
    (if (bowOf u x y) Bow.y = true then
        truncatedWeight bowGraph bowAcyclic cpt doXTrue (bowOf u x y) else 0) =
      if y = true then
        (if x = true then 1 else 0) * (bowPU cpt u * bowPY cpt u x y) else 0 := by
  have hyproj : (bowOf u x y) Bow.y = y := rfl
  rw [hyproj, bow_trunc_bits]

lemma bow_atom_factor (cpt : (network (β := Bool) bowGraph bowAcyclic).DiscreteCPT)
    (x0 y0 : Bool) :
    bowAtom cpt x0 y0 =
      bowPU cpt false * (bowPX cpt false x0 * bowPY cpt false x0 y0) +
        bowPU cpt true * (bowPX cpt true x0 * bowPY cpt true x0 y0) := by
  unfold bowAtom
  rw [sum_bow]
  simp_rw [bow_config_atom]
  have hinner (bu bx : Bool) :
      (∑ byy, if bx = x0 ∧ byy = y0 then
          bowPU cpt bu * (bowPX cpt bu bx * bowPY cpt bu bx byy) else 0) =
        if bx = x0 then
          bowPU cpt bu * (bowPX cpt bu x0 * bowPY cpt bu x0 y0) else 0 := by
    rw [sum_bool]
    by_cases hx : bx = x0
    · subst hx
      cases y0 <;> simp
    · rw [if_neg hx]
      simp [hx]
  simp_rw [hinner]
  have hmid (bu : Bool) :
      (∑ bx, if bx = x0 then
          bowPU cpt bu * (bowPX cpt bu x0 * bowPY cpt bu x0 y0) else 0) =
        bowPU cpt bu * (bowPX cpt bu x0 * bowPY cpt bu x0 y0) := by
    rw [sum_bool]
    cases x0 <;> simp
  simp_rw [hmid, sum_bool]

lemma bow_do_factor (cpt : (network (β := Bool) bowGraph bowAcyclic).DiscreteCPT) :
    bowDoMass cpt true =
      bowPU cpt false * bowPY cpt false true true +
        bowPU cpt true * bowPY cpt true true true := by
  unfold bowDoMass
  rw [sum_bow]
  simp_rw [bow_config_do]
  have hinner (bu bx : Bool) :
      (∑ byy, if byy = true then
          (if bx = true then 1 else 0) * (bowPU cpt bu * bowPY cpt bu bx byy) else 0) =
        (if bx = true then 1 else 0) * (bowPU cpt bu * bowPY cpt bu bx true) := by
    rw [sum_bool]
    simp
  simp_rw [hinner]
  have hmid (bu : Bool) :
      (∑ bx, (if bx = true then 1 else 0) *
          (bowPU cpt bu * bowPY cpt bu bx true)) =
        bowPU cpt bu * bowPY cpt bu true true := by
    rw [sum_bool]
    simp
  simp_rw [hmid, sum_bool]

lemma bow_treat_eq_atoms (cpt : (network (β := Bool) bowGraph bowAcyclic).DiscreteCPT)
    (x : Bool) :
    bowTreatMass cpt x = bowAtom cpt x false + bowAtom cpt x true := by
  unfold bowTreatMass bowAtom
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun f _ => ?_
  cases hy : f Bow.y <;> by_cases hx : f Bow.x = x <;> simp [hx]

lemma bow_treat_factor (cpt : (network (β := Bool) bowGraph bowAcyclic).DiscreteCPT)
    (x0 : Bool) :
    bowTreatMass cpt x0 =
      bowPU cpt false * bowPX cpt false x0 + bowPU cpt true * bowPX cpt true x0 := by
  rw [bow_treat_eq_atoms, bow_atom_factor, bow_atom_factor]
  exact weighted_py_sum _ _ _ _ _ _ _ _
    (bow_py_sum cpt false x0) (bow_py_sum cpt true x0)

/-! ## The shared joint of the two shipped models -/

lemma bow_atom_tt : bowAtom bowCPT1 true true = (2 : ℝ≥0∞)⁻¹ := by
  unfold bowAtom
  rw [sum_bow]
  simp_rw [joint1_factor, bow_factor_support, bowOf, sum_bool]
  simp [fairBit_apply]

lemma bow_atom_tf : bowAtom bowCPT1 true false = 0 := by
  unfold bowAtom
  rw [sum_bow]
  simp_rw [joint1_factor, bow_factor_support, bowOf, sum_bool]
  simp

lemma bow_treat_half : bowTreatMass bowCPT1 true = (2 : ℝ≥0∞)⁻¹ := by
  unfold bowTreatMass
  rw [sum_bow]
  simp_rw [joint1_factor, bow_factor_support, bowOf, sum_bool]
  simp [fairBit_apply]

lemma bow_atom_agree (x y : Bool) : bowAtom bowCPT2 x y = bowAtom bowCPT1 x y := by
  unfold bowAtom
  refine Finset.sum_congr rfl fun f _ => ?_
  by_cases h : f Bow.x = x ∧ f Bow.y = y
  · simp [h, bow_joint_agree]
  · simp [h]

lemma bow_treat_agree (x : Bool) : bowTreatMass bowCPT2 x = bowTreatMass bowCPT1 x := by
  rw [bow_treat_eq_atoms, bow_treat_eq_atoms, bow_atom_agree, bow_atom_agree]

/-- Both models put mass `1/2` on `(X, Y) = (true, true)` and on `X = true`. -/
theorem bow_shared_joint :
    bowAtom bowCPT1 true true = (2 : ℝ≥0∞)⁻¹ ∧
      bowAtom bowCPT2 true true = (2 : ℝ≥0∞)⁻¹ ∧
      bowTreatMass bowCPT1 true = (2 : ℝ≥0∞)⁻¹ ∧
      bowTreatMass bowCPT2 true = (2 : ℝ≥0∞)⁻¹ := by
  refine ⟨bow_atom_tt, ?_, bow_treat_half, ?_⟩
  · rw [bow_atom_agree, bow_atom_tt]
  · rw [bow_treat_agree, bow_treat_half]

noncomputable def bowJointTrue : ℝ := (bowAtom bowCPT1 true true).toReal

noncomputable def bowTreatTrue : ℝ := (bowTreatMass bowCPT1 true).toReal

/-- Observational counts of `(Y | X = true)`. The positive cell is the
`(true, true)` atom and the negative cell is the `(true, false)` atom, which
the shared joint sets to zero, so the strength is the conditional probability. -/
def bowObsCounts : Counts := ⟨1, 0⟩

/-- Interventional counts of the copying model. Its strength is `bowDoMass`. -/
def bowModel1Counts : Counts := ⟨1, 0⟩

/-- Interventional counts of the latent-copy model. Its strength is `bowDoMass`. -/
def bowModel2Counts : Counts := ⟨1, 1⟩

theorem bow_observed_cells :
    bowJointTrue = 1 / 2 ∧ bowTreatTrue = 1 / 2 ∧ bowObsCounts = ⟨1, 0⟩ := by
  refine ⟨?_, ?_, rfl⟩
  · unfold bowJointTrue
    rw [bow_atom_tt]
    simp
  · unfold bowTreatTrue
    rw [bow_treat_half]
    simp

/-- `[P(y, x), P(y, x) + 1 - P(x)]`, read off the shared joint. -/
noncomputable def bowCredal : Interval where
  lower := bowJointTrue
  upper := bowJointTrue + 1 - bowTreatTrue
  valid := by
    rw [bow_observed_cells.1, bow_observed_cells.2.1]
    norm_num

theorem bow_credal_is_natural_bound :
    bowCredal.lower = (bowAtom bowCPT1 true true).toReal ∧
      bowCredal.upper =
        (bowAtom bowCPT1 true true).toReal + 1 - (bowTreatMass bowCPT1 true).toReal := by
  simp [bowCredal, bowJointTrue, bowTreatTrue]

theorem bow_credal_endpoints :
    bowCredal.lower = 1 / 2 ∧ bowCredal.upper = 1 := by
  have hcells := bow_observed_cells
  constructor
  · simp [bowCredal, hcells.1]
  · simp [bowCredal, hcells.1, hcells.2.1]

/-- A table with the shared `(X, Y)` margin has `P(Y = true | do(X = true))`
inside the natural bound. -/
theorem bow_margin_determines_bound
    (cpt : (network (β := Bool) bowGraph bowAcyclic).DiscreteCPT)
    (hm : ∀ x y, bowAtom cpt x y = bowAtom bowCPT1 x y) :
    bowCredal.lower ≤ (bowDoMass cpt true).toReal ∧
      (bowDoMass cpt true).toReal ≤ bowCredal.upper := by
  have hfac := factor_natural_bound (bowPU cpt) (bowPX cpt) (bowPY cpt)
    (bow_pu_sum cpt) (bow_px_sum cpt false) (bow_px_sum cpt true)
    (bow_py_sum cpt false true) (bow_py_sum cpt true true)
  have hatom := bow_atom_factor cpt true true
  have hdo := bow_do_factor cpt
  have htreat := bow_treat_factor cpt true
  rw [← hatom, ← hdo, ← htreat] at hfac
  have hreal := natural_bound_toReal hfac.1 hfac.2.1 hfac.2.2.1 hfac.2.2.2
  have htreat1 : bowTreatMass cpt true = bowTreatMass bowCPT1 true := by
    rw [bow_treat_eq_atoms, bow_treat_eq_atoms, hm true false, hm true true]
  rw [hm true true, htreat1] at hreal
  simpa [bowCredal, bowJointTrue, bowTreatTrue] using hreal

theorem bow_model_strengths :
    bowModel1Counts.strength = 1 ∧ bowModel2Counts.strength = 1 / 2 := by
  constructor <;> norm_num [bowModel1Counts, bowModel2Counts, Counts.strength, Counts.total]

theorem bow_models_share_observational_counts :
    (∀ f, bowCPT1.jointWeight f = bowCPT2.jointWeight f) ∧
      bowObsCounts = ⟨1, 0⟩ ∧
      bowModel1Counts.strength ≠ bowModel2Counts.strength := by
  refine ⟨bow_joint_agree, bow_observed_cells.2.2, ?_⟩
  rw [bow_model_strengths.1, bow_model_strengths.2]
  norm_num

/-- The two do-masses are the endpoints of the interval read off the joint. -/
theorem bow_models_meet_endpoints :
    bowDoMass bowCPT1 true = ENNReal.ofReal bowCredal.upper ∧
      bowDoMass bowCPT2 true = ENNReal.ofReal bowCredal.lower ∧
      bowCredal.lower ≤ (bowDoMass bowCPT1 true).toReal ∧
      (bowDoMass bowCPT1 true).toReal ≤ bowCredal.upper ∧
      bowCredal.lower ≤ (bowDoMass bowCPT2 true).toReal ∧
      (bowDoMass bowCPT2 true).toReal ≤ bowCredal.upper := by
  have hends := bow_credal_endpoints
  have hup : bowDoMass bowCPT1 true = ENNReal.ofReal bowCredal.upper := by
    rw [bow_do_model1, hends.2, ENNReal.ofReal_one]
  have hlow : bowDoMass bowCPT2 true = ENNReal.ofReal bowCredal.lower := by
    rw [bow_do_model2, hends.1]
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    simp [ENNReal.ofReal_one, one_div]
  refine ⟨hup, hlow, ?_, ?_, ?_, ?_⟩
  · rw [hup, ENNReal.toReal_ofReal (by norm_num [hends.2])]
    exact bowCredal.valid
  · rw [hup, ENNReal.toReal_ofReal (by norm_num [hends.2])]
  · rw [hlow, ENNReal.toReal_ofReal (by norm_num [hends.1])]
  · rw [hlow, ENNReal.toReal_ofReal (by norm_num [hends.1])]
    exact bowCredal.valid

theorem bow_models_inside_credal :
    bowCredal.lower ≤ (bowModel1Counts.strength : ℝ) ∧
      (bowModel1Counts.strength : ℝ) ≤ bowCredal.upper ∧
      bowCredal.lower ≤ (bowModel2Counts.strength : ℝ) ∧
      (bowModel2Counts.strength : ℝ) ≤ bowCredal.upper ∧
      bowDoMass bowCPT1 true = 1 ∧
      bowDoMass bowCPT2 true = (2 : ℝ≥0∞)⁻¹ := by
  have hlow := bow_credal_endpoints.1
  have hhigh := bow_credal_endpoints.2
  have hstr := bow_model_strengths
  refine ⟨?_, ?_, ?_, ?_, bow_do_model1, bow_do_model2⟩
  · rw [hlow, hstr.1]; norm_num
  · rw [hhigh, hstr.1]; norm_num
  · rw [hlow, hstr.2]; norm_num
  · rw [hhigh, hstr.2]; norm_num

/-- The observational state is the conditional read off the atoms, and each
interventional state is the corresponding do-mass. Pooling the observational
state alone cannot recover both models. -/
theorem bow_observational_pool_misses_a_model (pool : Counts → Counts) :
    (∀ f, bowCPT1.jointWeight f = bowCPT2.jointWeight f) ∧
      bowAtom bowCPT1 true false = 0 ∧
      bowAtom bowCPT1 true true = bowTreatMass bowCPT1 true ∧
      ENNReal.ofReal (bowObsCounts.strength : ℝ) =
        bowAtom bowCPT1 true true / bowTreatMass bowCPT1 true ∧
      ENNReal.ofReal (bowModel1Counts.strength : ℝ) = bowDoMass bowCPT1 true ∧
      ENNReal.ofReal (bowModel2Counts.strength : ℝ) = bowDoMass bowCPT2 true ∧
      (pool bowObsCounts ≠ bowModel1Counts ∨ pool bowObsCounts ≠ bowModel2Counts) := by
  refine ⟨bow_joint_agree, bow_atom_tf, ?_, ?_, ?_, ?_, ?_⟩
  · rw [bow_atom_tt, bow_treat_half]
  · have hstr : bowObsCounts.strength = 1 := by
      norm_num [bowObsCounts, Counts.strength, Counts.total]
    rw [hstr, bow_atom_tt, bow_treat_half]
    have hcast : ((1 : ℚ) : ℝ) = 1 := by norm_num
    rw [hcast, ENNReal.ofReal_one]
    exact (ENNReal.div_self
      (ENNReal.inv_ne_zero.mpr ENNReal.ofNat_ne_top)
      (ENNReal.inv_ne_top.mpr two_ne_zero)).symm
  · have hstr : bowModel1Counts.strength = 1 := bow_model_strengths.1
    rw [hstr, bow_do_model1]
    have hcast : ((1 : ℚ) : ℝ) = 1 := by norm_num
    rw [hcast, ENNReal.ofReal_one]
  · have hstr : bowModel2Counts.strength = 1 / 2 := bow_model_strengths.2
    rw [hstr, bow_do_model2]
    have hcast : ((1 / 2 : ℚ) : ℝ) = 1 / 2 := by norm_num
    rw [hcast, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    simp [ENNReal.ofReal_one, one_div]
  · by_cases hmatch : pool bowObsCounts = bowModel1Counts
    · refine Or.inr ?_
      intro hother
      have hne : bowModel1Counts ≠ bowModel2Counts := by decide
      exact hne (hmatch.symm.trans hother)
    · exact Or.inl hmatch

/-! ## Child bow: the same `(X, Y)` bound, with the child `D` summed out -/

lemma child_parent_u (v : ChildBow) :
    v ∈ (network (β := Bool) childBowGraph childBowAcyclic).parents ChildBow.u → False := by
  intro h
  cases v <;> simp [BayesianNetwork.parents, DirectedGraph.parents, childBowGraph] at h

lemma child_parent_x (v : ChildBow) :
    v ∈ (network (β := Bool) childBowGraph childBowAcyclic).parents ChildBow.x ↔
      v = ChildBow.u := by
  cases v <;> simp [BayesianNetwork.parents, DirectedGraph.parents, childBowGraph]

lemma child_parent_y (v : ChildBow) :
    v ∈ (network (β := Bool) childBowGraph childBowAcyclic).parents ChildBow.y ↔
      v = ChildBow.u ∨ v = ChildBow.x := by
  cases v <;> simp [BayesianNetwork.parents, DirectedGraph.parents, childBowGraph]

lemma child_parent_d (v : ChildBow) :
    v ∈ (network (β := Bool) childBowGraph childBowAcyclic).parents ChildBow.d ↔
      v = ChildBow.y := by
  cases v <;> simp [BayesianNetwork.parents, DirectedGraph.parents, childBowGraph]

noncomputable def childPU
    (cpt : (network (β := Bool) childBowGraph childBowAcyclic).DiscreteCPT)
    (u : Bool) : ℝ≥0∞ :=
  cpt.cpt ChildBow.u (DiscreteCPT.parentAssignOfConfig cpt
    (childBowOf false false false false) ChildBow.u) u

noncomputable def childPX
    (cpt : (network (β := Bool) childBowGraph childBowAcyclic).DiscreteCPT)
    (u x : Bool) : ℝ≥0∞ :=
  cpt.cpt ChildBow.x (DiscreteCPT.parentAssignOfConfig cpt
    (childBowOf u false false false) ChildBow.x) x

noncomputable def childPY
    (cpt : (network (β := Bool) childBowGraph childBowAcyclic).DiscreteCPT)
    (u x y : Bool) : ℝ≥0∞ :=
  cpt.cpt ChildBow.y (DiscreteCPT.parentAssignOfConfig cpt
    (childBowOf u x false false) ChildBow.y) y

noncomputable def childPD
    (cpt : (network (β := Bool) childBowGraph childBowAcyclic).DiscreteCPT)
    (y d : Bool) : ℝ≥0∞ :=
  cpt.cpt ChildBow.d (DiscreteCPT.parentAssignOfConfig cpt
    (childBowOf false false y false) ChildBow.d) d

lemma child_pu_sum
    (cpt : (network (β := Bool) childBowGraph childBowAcyclic).DiscreteCPT) :
    childPU cpt false + childPU cpt true = 1 := by
  simpa [childPU] using pmf_bool_sum (cpt.cpt ChildBow.u
    (DiscreteCPT.parentAssignOfConfig cpt (childBowOf false false false false) ChildBow.u))

lemma child_px_sum
    (cpt : (network (β := Bool) childBowGraph childBowAcyclic).DiscreteCPT) (u : Bool) :
    childPX cpt u false + childPX cpt u true = 1 := by
  simpa [childPX] using pmf_bool_sum (cpt.cpt ChildBow.x
    (DiscreteCPT.parentAssignOfConfig cpt (childBowOf u false false false) ChildBow.x))

lemma child_py_sum
    (cpt : (network (β := Bool) childBowGraph childBowAcyclic).DiscreteCPT)
    (u x : Bool) : childPY cpt u x false + childPY cpt u x true = 1 := by
  simpa [childPY] using pmf_bool_sum (cpt.cpt ChildBow.y
    (DiscreteCPT.parentAssignOfConfig cpt (childBowOf u x false false) ChildBow.y))

lemma child_pd_sum
    (cpt : (network (β := Bool) childBowGraph childBowAcyclic).DiscreteCPT) (y : Bool) :
    childPD cpt y false + childPD cpt y true = 1 := by
  simpa [childPD] using pmf_bool_sum (cpt.cpt ChildBow.d
    (DiscreteCPT.parentAssignOfConfig cpt (childBowOf false false y false) ChildBow.d))

lemma child_pu_invariant
    (cpt : (network (β := Bool) childBowGraph childBowAcyclic).DiscreteCPT)
    (f : ChildBow → Bool) : cpt.nodeProb f ChildBow.u = childPU cpt (f ChildBow.u) := by
  unfold DiscreteCPT.nodeProb childPU
  apply congr_arg (fun pa => cpt.cpt ChildBow.u pa (f ChildBow.u))
  funext v hv
  exact (child_parent_u v hv).elim

lemma child_px_invariant
    (cpt : (network (β := Bool) childBowGraph childBowAcyclic).DiscreteCPT)
    (f : ChildBow → Bool) :
    cpt.nodeProb f ChildBow.x = childPX cpt (f ChildBow.u) (f ChildBow.x) := by
  unfold DiscreteCPT.nodeProb childPX
  apply congr_arg (fun pa => cpt.cpt ChildBow.x pa (f ChildBow.x))
  funext v hv
  have hv' : v = ChildBow.u := (child_parent_x v).1 hv
  subst hv'
  rfl

lemma child_py_invariant
    (cpt : (network (β := Bool) childBowGraph childBowAcyclic).DiscreteCPT)
    (f : ChildBow → Bool) :
    cpt.nodeProb f ChildBow.y =
      childPY cpt (f ChildBow.u) (f ChildBow.x) (f ChildBow.y) := by
  unfold DiscreteCPT.nodeProb childPY
  apply congr_arg (fun pa => cpt.cpt ChildBow.y pa (f ChildBow.y))
  funext v hv
  rcases (child_parent_y v).1 hv with rfl | rfl
  · rfl
  · rfl

lemma child_pd_invariant
    (cpt : (network (β := Bool) childBowGraph childBowAcyclic).DiscreteCPT)
    (f : ChildBow → Bool) :
    cpt.nodeProb f ChildBow.d = childPD cpt (f ChildBow.y) (f ChildBow.d) := by
  unfold DiscreteCPT.nodeProb childPD
  apply congr_arg (fun pa => cpt.cpt ChildBow.d pa (f ChildBow.d))
  funext v hv
  have hv' : v = ChildBow.y := (child_parent_d v).1 hv
  subst hv'
  rfl

lemma child_joint_bits
    (cpt : (network (β := Bool) childBowGraph childBowAcyclic).DiscreteCPT)
    (u x y d : Bool) :
    cpt.jointWeight (childBowOf u x y d) =
      childPU cpt u * (childPX cpt u x *
        (childPY cpt u x y * childPD cpt y d)) := by
  unfold DiscreteCPT.jointWeight
  rw [prod_childBow]
  rw [child_pu_invariant cpt (childBowOf u x y d),
    child_px_invariant cpt (childBowOf u x y d),
    child_py_invariant cpt (childBowOf u x y d),
    child_pd_invariant cpt (childBowOf u x y d)]
  simp [childBowOf]

lemma child_trunc_bits
    (cpt : (network (β := Bool) childBowGraph childBowAcyclic).DiscreteCPT)
    (u x y d : Bool) :
    truncatedWeight childBowGraph childBowAcyclic cpt childBowDoX (childBowOf u x y d) =
      (if x = true then 1 else 0) *
        (childPU cpt u * (childPY cpt u x y * childPD cpt y d)) := by
  unfold truncatedWeight
  rw [prod_childBow]
  have hu : truncatedFactor childBowGraph childBowAcyclic cpt childBowDoX
      (childBowOf u x y d) ChildBow.u = childPU cpt u := by
    have hne : ChildBow.u ≠ ChildBow.x := by decide
    simp only [truncatedFactor, childBowDoX, if_neg hne, cptAt_eq_nodeProb]
    exact child_pu_invariant cpt (childBowOf u x y d)
  have hx : truncatedFactor childBowGraph childBowAcyclic cpt childBowDoX
      (childBowOf u x y d) ChildBow.x = if x = true then 1 else 0 := by
    by_cases hxt : x = true
    · simp [truncatedFactor, childBowDoX, childBowOf, hxt]
    · simp [truncatedFactor, childBowDoX, childBowOf, hxt]
  have hy : truncatedFactor childBowGraph childBowAcyclic cpt childBowDoX
      (childBowOf u x y d) ChildBow.y = childPY cpt u x y := by
    have hne : ChildBow.y ≠ ChildBow.x := by decide
    simp only [truncatedFactor, childBowDoX, if_neg hne, cptAt_eq_nodeProb]
    exact child_py_invariant cpt (childBowOf u x y d)
  have hd : truncatedFactor childBowGraph childBowAcyclic cpt childBowDoX
      (childBowOf u x y d) ChildBow.d = childPD cpt y d := by
    have hne : ChildBow.d ≠ ChildBow.x := by decide
    simp only [truncatedFactor, childBowDoX, if_neg hne, cptAt_eq_nodeProb]
    exact child_pd_invariant cpt (childBowOf u x y d)
  rw [hu, hx, hy, hd]
  exact mul_left_comm _ _ _

/-- `P(X = x, Y = y)` on the child bow, summing `jointWeight` over `U` and `D`. -/
noncomputable def childBowAtom
    (cpt : (network (β := Bool) childBowGraph childBowAcyclic).DiscreteCPT)
    (x y : Bool) : ℝ≥0∞ :=
  ∑ f, if f ChildBow.x = x ∧ f ChildBow.y = y then cpt.jointWeight f else 0

/-- `P(X = x)` on the child bow. -/
noncomputable def childBowTreatMass
    (cpt : (network (β := Bool) childBowGraph childBowAcyclic).DiscreteCPT)
    (x : Bool) : ℝ≥0∞ :=
  ∑ f, if f ChildBow.x = x then cpt.jointWeight f else 0

lemma child_config_atom
    (cpt : (network (β := Bool) childBowGraph childBowAcyclic).DiscreteCPT)
    (u x y d x0 y0 : Bool) :
    (if (childBowOf u x y d) ChildBow.x = x0 ∧
        (childBowOf u x y d) ChildBow.y = y0 then
        cpt.jointWeight (childBowOf u x y d) else 0) =
      if x = x0 ∧ y = y0 then
        childPU cpt u * (childPX cpt u x *
          (childPY cpt u x y * childPD cpt y d)) else 0 := by
  have hxproj : (childBowOf u x y d) ChildBow.x = x := rfl
  have hyproj : (childBowOf u x y d) ChildBow.y = y := rfl
  rw [hxproj, hyproj, child_joint_bits]

lemma child_config_do
    (cpt : (network (β := Bool) childBowGraph childBowAcyclic).DiscreteCPT)
    (u x y d : Bool) :
    (if (childBowOf u x y d) ChildBow.y = true then
        truncatedWeight childBowGraph childBowAcyclic cpt childBowDoX
          (childBowOf u x y d) else 0) =
      if y = true then
        (if x = true then 1 else 0) *
          (childPU cpt u * (childPY cpt u x y * childPD cpt y d)) else 0 := by
  have hyproj : (childBowOf u x y d) ChildBow.y = y := rfl
  rw [hyproj, child_trunc_bits]

lemma child_atom_factor
    (cpt : (network (β := Bool) childBowGraph childBowAcyclic).DiscreteCPT)
    (x0 y0 : Bool) :
    childBowAtom cpt x0 y0 =
      childPU cpt false * (childPX cpt false x0 * childPY cpt false x0 y0) +
        childPU cpt true * (childPX cpt true x0 * childPY cpt true x0 y0) := by
  unfold childBowAtom
  rw [sum_childBow]
  simp_rw [child_config_atom]
  have hd (bu bx byy : Bool) :
      (∑ bd, if bx = x0 ∧ byy = y0 then
          childPU cpt bu * (childPX cpt bu bx *
            (childPY cpt bu bx byy * childPD cpt byy bd)) else 0) =
        if bx = x0 ∧ byy = y0 then
          childPU cpt bu * (childPX cpt bu bx * childPY cpt bu bx byy) else 0 := by
    rw [sum_bool]
    by_cases hxy : bx = x0 ∧ byy = y0
    · rcases hxy with ⟨hx, hy⟩
      simp only [hx, hy]
      simp only [and_self, if_true]
      have hpd := child_pd_sum cpt y0
      have hmul (bd : Bool) :
          childPU cpt bu * (childPX cpt bu x0 *
              (childPY cpt bu x0 y0 * childPD cpt y0 bd)) =
            (childPU cpt bu * (childPX cpt bu x0 * childPY cpt bu x0 y0)) *
              childPD cpt y0 bd := by
        calc childPU cpt bu * (childPX cpt bu x0 *
              (childPY cpt bu x0 y0 * childPD cpt y0 bd))
            = childPU cpt bu * ((childPX cpt bu x0 * childPY cpt bu x0 y0) *
                childPD cpt y0 bd) := by
              congr 1
              rw [← mul_assoc]
          _ = (childPU cpt bu * (childPX cpt bu x0 * childPY cpt bu x0 y0)) *
                childPD cpt y0 bd := by rw [← mul_assoc]
      rw [hmul false, hmul true, ← mul_add, hpd, mul_one]
    · rw [if_neg hxy]
      simp [hxy]
  simp_rw [hd]
  have hy (bu bx : Bool) :
      (∑ byy, if bx = x0 ∧ byy = y0 then
          childPU cpt bu * (childPX cpt bu bx * childPY cpt bu bx byy) else 0) =
        if bx = x0 then
          childPU cpt bu * (childPX cpt bu x0 * childPY cpt bu x0 y0) else 0 := by
    rw [sum_bool]
    by_cases hx : bx = x0
    · subst hx
      cases y0 <;> simp
    · rw [if_neg hx]
      simp [hx]
  simp_rw [hy]
  have hmid (bu : Bool) :
      (∑ bx, if bx = x0 then
          childPU cpt bu * (childPX cpt bu x0 * childPY cpt bu x0 y0) else 0) =
        childPU cpt bu * (childPX cpt bu x0 * childPY cpt bu x0 y0) := by
    rw [sum_bool]
    cases x0 <;> simp
  simp_rw [hmid, sum_bool]

lemma child_do_factor
    (cpt : (network (β := Bool) childBowGraph childBowAcyclic).DiscreteCPT) :
    childBowDoMass cpt true =
      childPU cpt false * childPY cpt false true true +
        childPU cpt true * childPY cpt true true true := by
  unfold childBowDoMass
  rw [sum_childBow]
  simp_rw [child_config_do]
  have hd (bu bx byy : Bool) :
      (∑ bd, if byy = true then
          (if bx = true then 1 else 0) *
            (childPU cpt bu * (childPY cpt bu bx byy * childPD cpt byy bd)) else 0) =
        if byy = true then
          (if bx = true then 1 else 0) * (childPU cpt bu * childPY cpt bu bx byy) else 0 := by
    rw [sum_bool]
    by_cases hy : byy = true
    · subst hy
      simp only [if_true]
      have hpd := child_pd_sum cpt true
      have hmul (bd : Bool) :
          (if bx = true then 1 else 0) *
              (childPU cpt bu * (childPY cpt bu bx true * childPD cpt true bd)) =
            ((if bx = true then 1 else 0) *
              (childPU cpt bu * childPY cpt bu bx true)) * childPD cpt true bd := by
        calc (if bx = true then 1 else 0) *
              (childPU cpt bu * (childPY cpt bu bx true * childPD cpt true bd))
            = (if bx = true then 1 else 0) *
                ((childPU cpt bu * childPY cpt bu bx true) * childPD cpt true bd) := by
              congr 1
              rw [← mul_assoc]
          _ = ((if bx = true then 1 else 0) *
                (childPU cpt bu * childPY cpt bu bx true)) * childPD cpt true bd := by
              rw [← mul_assoc]
      rw [hmul false, hmul true, ← mul_add, hpd, mul_one]
    · rw [if_neg hy]
      simp [hy]
  simp_rw [hd]
  have hy (bu bx : Bool) :
      (∑ byy, if byy = true then
          (if bx = true then 1 else 0) * (childPU cpt bu * childPY cpt bu bx byy) else 0) =
        (if bx = true then 1 else 0) * (childPU cpt bu * childPY cpt bu bx true) := by
    rw [sum_bool]
    simp
  simp_rw [hy]
  have hmid (bu : Bool) :
      (∑ bx, (if bx = true then 1 else 0) *
          (childPU cpt bu * childPY cpt bu bx true)) =
        childPU cpt bu * childPY cpt bu true true := by
    rw [sum_bool]
    simp
  simp_rw [hmid, sum_bool]

lemma child_treat_eq_atoms
    (cpt : (network (β := Bool) childBowGraph childBowAcyclic).DiscreteCPT) (x : Bool) :
    childBowTreatMass cpt x = childBowAtom cpt x false + childBowAtom cpt x true := by
  unfold childBowTreatMass childBowAtom
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun f _ => ?_
  cases hy : f ChildBow.y <;> by_cases hx : f ChildBow.x = x <;> simp [hx]

lemma child_treat_factor
    (cpt : (network (β := Bool) childBowGraph childBowAcyclic).DiscreteCPT) (x0 : Bool) :
    childBowTreatMass cpt x0 =
      childPU cpt false * childPX cpt false x0 +
        childPU cpt true * childPX cpt true x0 := by
  rw [child_treat_eq_atoms, child_atom_factor, child_atom_factor]
  exact weighted_py_sum _ _ _ _ _ _ _ _
    (child_py_sum cpt false x0) (child_py_sum cpt true x0)

lemma child_bow_atom_tt : childBowAtom childBowCPT1 true true = (2 : ℝ≥0∞)⁻¹ := by
  unfold childBowAtom
  rw [sum_childBow]
  simp_rw [childBow_joint1, childBow_support1, childBowOf, sum_bool]
  simp [fairBit_apply]

lemma child_bow_atom_tf : childBowAtom childBowCPT1 true false = 0 := by
  unfold childBowAtom
  rw [sum_childBow]
  simp_rw [childBow_joint1, childBow_support1, childBowOf, sum_bool]
  simp

lemma child_bow_treat_half : childBowTreatMass childBowCPT1 true = (2 : ℝ≥0∞)⁻¹ := by
  unfold childBowTreatMass
  rw [sum_childBow]
  simp_rw [childBow_joint1, childBow_support1, childBowOf, sum_bool]
  simp [fairBit_apply]

lemma child_bow_atom_agree (x y : Bool) :
    childBowAtom childBowCPT2 x y = childBowAtom childBowCPT1 x y := by
  unfold childBowAtom
  refine Finset.sum_congr rfl fun f _ => ?_
  by_cases h : f ChildBow.x = x ∧ f ChildBow.y = y
  · simp [h, childBow_joint_agree]
  · simp [h]

lemma child_bow_treat_agree (x : Bool) :
    childBowTreatMass childBowCPT2 x = childBowTreatMass childBowCPT1 x := by
  rw [child_treat_eq_atoms, child_treat_eq_atoms, child_bow_atom_agree, child_bow_atom_agree]

theorem child_bow_shared_joint :
    childBowAtom childBowCPT1 true true = (2 : ℝ≥0∞)⁻¹ ∧
      childBowAtom childBowCPT2 true true = (2 : ℝ≥0∞)⁻¹ ∧
      childBowTreatMass childBowCPT1 true = (2 : ℝ≥0∞)⁻¹ ∧
      childBowTreatMass childBowCPT2 true = (2 : ℝ≥0∞)⁻¹ := by
  refine ⟨child_bow_atom_tt, ?_, child_bow_treat_half, ?_⟩
  · rw [child_bow_atom_agree, child_bow_atom_tt]
  · rw [child_bow_treat_agree, child_bow_treat_half]

noncomputable def childBowJointTrue : ℝ := (childBowAtom childBowCPT1 true true).toReal

noncomputable def childBowTreatTrue : ℝ := (childBowTreatMass childBowCPT1 true).toReal

def childBowObsCounts : Counts := ⟨1, 0⟩

def childBowModel1Counts : Counts := ⟨1, 0⟩

def childBowModel2Counts : Counts := ⟨1, 1⟩

noncomputable def childBowCredal : Interval where
  lower := childBowJointTrue
  upper := childBowJointTrue + 1 - childBowTreatTrue
  valid := by
    have hj : childBowJointTrue = 1 / 2 := by
      unfold childBowJointTrue
      rw [child_bow_atom_tt]
      simp
    have ht : childBowTreatTrue = 1 / 2 := by
      unfold childBowTreatTrue
      rw [child_bow_treat_half]
      simp
    rw [hj, ht]
    norm_num

theorem child_bow_credal_is_natural_bound :
    childBowCredal.lower = (childBowAtom childBowCPT1 true true).toReal ∧
      childBowCredal.upper =
        (childBowAtom childBowCPT1 true true).toReal + 1 -
          (childBowTreatMass childBowCPT1 true).toReal := by
  simp [childBowCredal, childBowJointTrue, childBowTreatTrue]

theorem child_bow_credal_endpoints :
    childBowCredal.lower = 1 / 2 ∧ childBowCredal.upper = 1 ∧
      childBowObsCounts = ⟨1, 0⟩ := by
  refine ⟨?_, ?_, rfl⟩
  · have hj : childBowJointTrue = 1 / 2 := by
      unfold childBowJointTrue
      rw [child_bow_atom_tt]
      simp
    simp [childBowCredal, hj]
  · have hj : childBowJointTrue = 1 / 2 := by
      unfold childBowJointTrue
      rw [child_bow_atom_tt]
      simp
    have ht : childBowTreatTrue = 1 / 2 := by
      unfold childBowTreatTrue
      rw [child_bow_treat_half]
      simp
    simp [childBowCredal, hj, ht]

theorem child_bow_margin_determines_bound
    (cpt : (network (β := Bool) childBowGraph childBowAcyclic).DiscreteCPT)
    (hm : ∀ x y, childBowAtom cpt x y = childBowAtom childBowCPT1 x y) :
    childBowCredal.lower ≤ (childBowDoMass cpt true).toReal ∧
      (childBowDoMass cpt true).toReal ≤ childBowCredal.upper := by
  have hfac := factor_natural_bound (childPU cpt) (childPX cpt) (childPY cpt)
    (child_pu_sum cpt) (child_px_sum cpt false) (child_px_sum cpt true)
    (child_py_sum cpt false true) (child_py_sum cpt true true)
  have hatom := child_atom_factor cpt true true
  have hdo := child_do_factor cpt
  have htreat := child_treat_factor cpt true
  rw [← hatom, ← hdo, ← htreat] at hfac
  have hreal := natural_bound_toReal hfac.1 hfac.2.1 hfac.2.2.1 hfac.2.2.2
  have htreat1 : childBowTreatMass cpt true = childBowTreatMass childBowCPT1 true := by
    rw [child_treat_eq_atoms, child_treat_eq_atoms, hm true false, hm true true]
  rw [hm true true, htreat1] at hreal
  simpa [childBowCredal, childBowJointTrue, childBowTreatTrue] using hreal

theorem child_bow_models_meet_endpoints :
    childBowDoMass childBowCPT1 true = ENNReal.ofReal childBowCredal.upper ∧
      childBowDoMass childBowCPT2 true = ENNReal.ofReal childBowCredal.lower ∧
      childBowCredal.lower ≤ (childBowDoMass childBowCPT1 true).toReal ∧
      (childBowDoMass childBowCPT1 true).toReal ≤ childBowCredal.upper ∧
      childBowCredal.lower ≤ (childBowDoMass childBowCPT2 true).toReal ∧
      (childBowDoMass childBowCPT2 true).toReal ≤ childBowCredal.upper := by
  have hlow_num : childBowCredal.lower = 1 / 2 := child_bow_credal_endpoints.1
  have hup_num : childBowCredal.upper = 1 := child_bow_credal_endpoints.2.1
  have hup : childBowDoMass childBowCPT1 true = ENNReal.ofReal childBowCredal.upper := by
    rw [childBow_do_model1, hup_num, ENNReal.ofReal_one]
  have hlow : childBowDoMass childBowCPT2 true = ENNReal.ofReal childBowCredal.lower := by
    rw [childBow_do_model2, hlow_num]
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    simp [ENNReal.ofReal_one, one_div]
  refine ⟨hup, hlow, ?_, ?_, ?_, ?_⟩
  · rw [hup, ENNReal.toReal_ofReal (by norm_num [hup_num])]
    exact childBowCredal.valid
  · rw [hup, ENNReal.toReal_ofReal (by norm_num [hup_num])]
  · rw [hlow, ENNReal.toReal_ofReal (by norm_num [hlow_num])]
  · rw [hlow, ENNReal.toReal_ofReal (by norm_num [hlow_num])]
    exact childBowCredal.valid

theorem child_bow_models_inside_credal :
    (∀ f, childBowCPT1.jointWeight f = childBowCPT2.jointWeight f) ∧
      childBowCredal.lower ≤ (childBowModel1Counts.strength : ℝ) ∧
      (childBowModel1Counts.strength : ℝ) ≤ childBowCredal.upper ∧
      childBowCredal.lower ≤ (childBowModel2Counts.strength : ℝ) ∧
      (childBowModel2Counts.strength : ℝ) ≤ childBowCredal.upper ∧
      childBowDoMass childBowCPT1 true = 1 ∧
      childBowDoMass childBowCPT2 true = (2 : ℝ≥0∞)⁻¹ := by
  have hlow := child_bow_credal_endpoints.1
  have hhigh := child_bow_credal_endpoints.2.1
  have hstr1 : childBowModel1Counts.strength = 1 := by
    norm_num [childBowModel1Counts, Counts.strength, Counts.total]
  have hstr2 : childBowModel2Counts.strength = 1 / 2 := by
    norm_num [childBowModel2Counts, Counts.strength, Counts.total]
  refine ⟨childBow_joint_agree, ?_, ?_, ?_, ?_, childBow_do_model1, childBow_do_model2⟩
  · rw [hlow, hstr1]; norm_num
  · rw [hhigh, hstr1]; norm_num
  · rw [hlow, hstr2]; norm_num
  · rw [hhigh, hstr2]; norm_num

theorem child_bow_observational_pool_misses_a_model (pool : Counts → Counts) :
    (∀ f, childBowCPT1.jointWeight f = childBowCPT2.jointWeight f) ∧
      childBowAtom childBowCPT1 true false = 0 ∧
      childBowAtom childBowCPT1 true true = childBowTreatMass childBowCPT1 true ∧
      ENNReal.ofReal (childBowObsCounts.strength : ℝ) =
        childBowAtom childBowCPT1 true true / childBowTreatMass childBowCPT1 true ∧
      ENNReal.ofReal (childBowModel1Counts.strength : ℝ) =
        childBowDoMass childBowCPT1 true ∧
      ENNReal.ofReal (childBowModel2Counts.strength : ℝ) =
        childBowDoMass childBowCPT2 true ∧
      (pool childBowObsCounts ≠ childBowModel1Counts ∨
        pool childBowObsCounts ≠ childBowModel2Counts) := by
  refine ⟨childBow_joint_agree, child_bow_atom_tf, ?_, ?_, ?_, ?_, ?_⟩
  · rw [child_bow_atom_tt, child_bow_treat_half]
  · have hstr : childBowObsCounts.strength = 1 := by
      norm_num [childBowObsCounts, Counts.strength, Counts.total]
    rw [hstr, child_bow_atom_tt, child_bow_treat_half]
    have hcast : ((1 : ℚ) : ℝ) = 1 := by norm_num
    rw [hcast, ENNReal.ofReal_one]
    exact (ENNReal.div_self
      (ENNReal.inv_ne_zero.mpr ENNReal.ofNat_ne_top)
      (ENNReal.inv_ne_top.mpr two_ne_zero)).symm
  · have hstr : childBowModel1Counts.strength = 1 := by
      norm_num [childBowModel1Counts, Counts.strength, Counts.total]
    rw [hstr, childBow_do_model1]
    have hcast : ((1 : ℚ) : ℝ) = 1 := by norm_num
    rw [hcast, ENNReal.ofReal_one]
  · have hstr : childBowModel2Counts.strength = 1 / 2 := by
      norm_num [childBowModel2Counts, Counts.strength, Counts.total]
    rw [hstr, childBow_do_model2]
    have hcast : ((1 / 2 : ℚ) : ℝ) = 1 / 2 := by norm_num
    rw [hcast, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    simp [ENNReal.ofReal_one, one_div]
  · by_cases hmatch : pool childBowObsCounts = childBowModel1Counts
    · refine Or.inr ?_
      intro hother
      have hne : childBowModel1Counts ≠ childBowModel2Counts := by decide
      exact hne (hmatch.symm.trans hother)
    · exact Or.inl hmatch

end Mettapedia.GSLT.Causality.DoCalculus

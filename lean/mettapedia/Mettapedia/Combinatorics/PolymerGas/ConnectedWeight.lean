import Mettapedia.Combinatorics.PolymerGas.ConnectedDecomposition
import Mettapedia.Combinatorics.PolymerGas.SupportRegrouping
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Summing exponentially weighted connected sets

The uniform connected-set count gives a geometric majorant for the sum over
all connected sets containing a specified vertex. Weighted neighbour sums
also give a degree-free connected-family majorant. Dobrushin removal bounds
control the full weighted logarithmic subset expansion, using the positive
negative-activity companion and every term of the convergent series.
-/

set_option autoImplicit false
noncomputable section

open Finset
open scoped Classical

namespace Mettapedia.Combinatorics.PolymerGas

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Summing the connected-set count costs at most twice its geometric ratio. -/
theorem sum_rootedConnected_pow_le {Δ : ℕ} (hdeg : ∀ v, G.degree v ≤ Δ)
    (root : V) {t : ℝ} (ht : 0 ≤ t)
    (hsmall : ((Δ + 1 : ℕ) : ℝ) ^ 2 * t ≤ 1 / 2) :
    ∑ C ∈ (univ : Finset (Finset V)).filter
        (fun C : Finset V => root ∈ C ∧ (G.induce (C : Set V)).Connected), t ^ C.card ≤
      2 * (((Δ + 1 : ℕ) : ℝ) ^ 2 * t) := by
  classical
  let I : Finset (Finset V) := univ.filter
    (fun C : Finset V => root ∈ C ∧ (G.induce (C : Set V)).Connected)
  have hcard : ∀ C ∈ I, 0 < C.card ∧ C.card ≤ Fintype.card V := by
    intro C hC
    exact ⟨card_pos.mpr ⟨root, (mem_filter.mp hC).2.1⟩, card_le_univ C⟩
  have hfibre : ∀ n, I.filter (fun C => C.card - 1 = n) = rootedConnectedSets G root (n + 1) := by
    intro n
    ext C
    simp only [I, rootedConnectedSets, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨⟨hr, hc⟩, hn⟩
      have hp : 0 < C.card := card_pos.mpr ⟨root, hr⟩
      exact ⟨hr, by omega, hc⟩
    · rintro ⟨hr, hn, hc⟩
      exact ⟨⟨hr, hc⟩, by omega⟩
  have hgroup :
      ∑ C ∈ I, t ^ C.card = ∑ n ∈ range (Fintype.card V),
        ∑ C ∈ rootedConnectedSets G root (n + 1), t ^ C.card := by
    rw [← sum_fiberwise_of_maps_to
      (s := I) (t := range (Fintype.card V)) (g := fun C => C.card - 1)
      (fun C hC => mem_range.mpr (by have := hcard C hC; omega)) (fun C => t ^ C.card)]
    simp_rw [hfibre]
  change ∑ C ∈ I, t ^ C.card ≤ _
  rw [hgroup]
  calc
    _ ≤ ∑ n ∈ range (Fintype.card V),
        (((Δ + 1 : ℕ) : ℝ) ^ 2 * t) ^ (n + 1) := by
      apply sum_le_sum
      intro n _
      calc
        _ = ((rootedConnectedSets G root (n + 1)).card : ℝ) * t ^ (n + 1) := by
          rw [show (∑ C ∈ rootedConnectedSets G root (n + 1), t ^ C.card) =
              ∑ _C ∈ rootedConnectedSets G root (n + 1), t ^ (n + 1) from
            sum_congr rfl (fun C hC => by rw [(mem_filter.mp hC).2.2.1])]
          simp
        _ ≤ (((Δ + 1) ^ (2 * (n + 1)) : ℕ) : ℝ) * t ^ (n + 1) := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg ht _)
          exact_mod_cast card_rootedConnectedSets_le G hdeg root (n + 1)
        _ = _ := by push_cast; rw [pow_mul, mul_pow]
    _ ≤ ∑ n ∈ range (Fintype.card V),
        (((Δ + 1 : ℕ) : ℝ) ^ 2 * t) * (1 / 2 : ℝ) ^ n := by
      apply sum_le_sum
      intro n _
      rw [pow_succ']
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hsmall _)
        (by positivity)
    _ = (((Δ + 1 : ℕ) : ℝ) ^ 2 * t) *
        ∑ n ∈ range (Fintype.card V), (1 / 2 : ℝ) ^ n := by rw [mul_sum]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (sum_geometric_two_le (Fintype.card V))
        (show 0 ≤ (((Δ + 1 : ℕ) : ℝ) ^ 2 * t) by positivity)
      nlinarith

/-- Connected vertex sets in a finite region containing a specified root. -/
def rootedFamily (Λ : Finset V) (p : V) : Finset (Finset V) :=
  Λ.powerset.filter (fun C => p ∈ C ∧ (G.induce (C : Set V)).Connected)

@[simp] theorem mem_rootedFamily {Λ C : Finset V} {p : V} :
    C ∈ rootedFamily G Λ p ↔ C ⊆ Λ ∧ p ∈ C ∧
      (G.induce (C : Set V)).Connected := by
  simp [rootedFamily]

def connectedWeight (w : V → ℝ) (Λ : Finset V) (p : V) : ℝ :=
  ∑ C ∈ rootedFamily G Λ p, ∏ v ∈ C, w v

theorem connectedWeight_nonneg {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    (Λ : Finset V) (p : V) : 0 ≤ connectedWeight G w Λ p :=
  sum_nonneg fun _ _ => prod_nonneg fun v _ => hw v

theorem connectedWeight_eq_zero_of_notMem {w : V → ℝ} {Λ : Finset V} {p : V}
    (hp : p ∉ Λ) : connectedWeight G w Λ p = 0 := by
  apply sum_eq_zero
  intro C hC
  exact (hp (((mem_rootedFamily G).mp hC).1 ((mem_rootedFamily G).mp hC).2.1)).elim

/-- Deleting the root bounds its connected-set sum by an exponential of
smaller rooted sums. No bound on the graph degree is required. -/
theorem connectedWeight_le_exp_neighbors {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    {Λ : Finset V} {p : V} (hp : p ∈ Λ) :
    connectedWeight G w Λ p ≤ w p * Real.exp
      (∑ q ∈ G.neighborFinset p, connectedWeight G w (Λ.erase p) q) := by
  let A : Finset (Finset V) := (G.neighborFinset p).biUnion
    (fun q => rootedFamily G (Λ.erase p) q)
  have hparts : ∀ C ∈ rootedFamily G Λ p,
      componentFamily G (C.erase p) ⊆ A := by
    intro C hC D hD
    obtain ⟨hsub, hpC, hconn⟩ := (mem_rootedFamily G).mp hC
    obtain ⟨q, hqD, hpq⟩ := componentFamily_erase_touches G hconn hpC hD
    apply mem_biUnion.mpr
    refine ⟨q, by simpa using hpq, (mem_rootedFamily G).mpr ⟨?_, hqD, ?_⟩⟩
    · intro v hv
      have hve : v ∈ C.erase p := by
        rw [← biUnion_componentFamily G (C.erase p)]
        exact mem_biUnion.mpr ⟨D, hD, hv⟩
      exact mem_erase.mpr ⟨(mem_erase.mp hve).1, hsub (mem_erase.mp hve).2⟩
    · exact (isComponentFamily_componentFamily G (C.erase p)).1 D hD
  have hinj : Set.InjOn (fun C : Finset V => componentFamily G (C.erase p))
      (rootedFamily G Λ p) := by
    intro C hC D hD he
    have he' : C.erase p = D.erase p := by
      simpa using congrArg (Finset.biUnion · id) he
    have hpC := ((mem_rootedFamily G).mp hC).2.1
    have hpD := ((mem_rootedFamily G).mp hD).2.1
    rw [← insert_erase hpC, ← insert_erase hpD, he']
  have hfactor : ∀ C ∈ rootedFamily G Λ p,
      (∏ v ∈ C, w v) = w p *
        ∏ D ∈ componentFamily G (C.erase p), ∏ v ∈ D, w v := by
    intro C hC
    have he := Finset.prod_biUnion (f := w)
      (isComponentFamily_componentFamily G (C.erase p)).2.1
    simp only [biUnion_componentFamily, id_eq] at he
    rw [← he]
    exact (mul_prod_erase C w ((mem_rootedFamily G).mp hC).2.1).symm
  have hsum : ∑ C ∈ rootedFamily G Λ p,
      ∏ D ∈ componentFamily G (C.erase p), ∏ v ∈ D, w v ≤
      ∑ Γ ∈ A.powerset, ∏ D ∈ Γ, ∏ v ∈ D, w v := by
    apply sum_le_sum_of_injOn (s := rootedFamily G Λ p) (t := A.powerset)
      (f := fun C => ∏ D ∈ componentFamily G (C.erase p), ∏ v ∈ D, w v)
      (g := fun Γ => ∏ D ∈ Γ, ∏ v ∈ D, w v)
      (fun C => componentFamily G (C.erase p)) hinj
    · intro Γ hΓ
      obtain ⟨C, hC, rfl⟩ := mem_image.mp hΓ
      exact mem_powerset.mpr (hparts C hC)
    · intro C hC
      exact le_rfl
    · intro Γ hΓ hnot
      exact prod_nonneg fun D _ => prod_nonneg fun v _ => hw v
  have htotal : ∑ D ∈ A, ∏ v ∈ D, w v ≤
      ∑ q ∈ G.neighborFinset p, connectedWeight G w (Λ.erase p) q := by
    calc
      _ ≤ ∑ D ∈ A, ∑ q ∈ G.neighborFinset p,
          if D ∈ rootedFamily G (Λ.erase p) q then ∏ v ∈ D, w v else 0 := by
        apply sum_le_sum
        intro D hD
        obtain ⟨q, hq, hDq⟩ := mem_biUnion.mp hD
        calc
          _ = if D ∈ rootedFamily G (Λ.erase p) q then ∏ v ∈ D, w v else 0 := by
            rw [if_pos hDq]
          _ ≤ _ := single_le_sum (s := G.neighborFinset p)
            (f := fun j => if D ∈ rootedFamily G (Λ.erase p) j then ∏ v ∈ D, w v else 0)
            (fun j _ => by split_ifs <;> first | positivity | exact prod_nonneg fun v _ => hw v) hq
      _ = _ := by
        rw [sum_comm]
        apply sum_congr rfl
        intro q hq
        rw [← sum_filter]
        change (∑ D ∈ A.filter (fun D => D ∈ rootedFamily G (Λ.erase p) q),
          ∏ v ∈ D, w v) = _
        have he : A.filter (fun D => D ∈ rootedFamily G (Λ.erase p) q) =
            rootedFamily G (Λ.erase p) q := by
          ext D
          simp only [mem_filter]
          constructor
          · exact And.right
          · intro hD
            exact ⟨mem_biUnion.mpr ⟨q, hq, hD⟩, hD⟩
        rw [he]
        rfl
  calc
    _ = w p * ∑ C ∈ rootedFamily G Λ p,
        ∏ D ∈ componentFamily G (C.erase p), ∏ v ∈ D, w v := by
      unfold connectedWeight
      rw [mul_sum]
      exact sum_congr rfl hfactor
    _ ≤ w p * ∑ Γ ∈ A.powerset, ∏ D ∈ Γ, ∏ v ∈ D, w v :=
      mul_le_mul_of_nonneg_left hsum (hw p)
    _ ≤ w p * Real.exp (∑ D ∈ A, ∏ v ∈ D, w v) := by
      apply mul_le_mul_of_nonneg_left _ (hw p)
      rw [← prod_one_add, Real.exp_sum]
      exact prod_le_prod (fun D _ => by
        have := prod_nonneg (fun v (_ : v ∈ D) => hw v)
        linarith) fun D _ => by linarith [Real.add_one_le_exp (∏ v ∈ D, w v)]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr htotal) (hw p)

/-- A weighted connected-set majorant, uniform in the finite region and with
no degree bound. Its smallness hypothesis is a weighted neighbourhood sum. -/
theorem connectedWeight_le_of_neighbor_sum {w a : V → ℝ}
    (hw : ∀ v, 0 ≤ w v)
    (ha : ∀ p, ∑ q ∈ G.neighborFinset p, w q * Real.exp (a q) ≤ a p)
    (Λ : Finset V) (p : V) :
    connectedWeight G w Λ p ≤ w p * Real.exp (a p) := by
  induction Λ using Finset.strongInductionOn generalizing p with
  | _ Λ ih =>
    by_cases hp : p ∈ Λ
    · calc
        _ ≤ w p * Real.exp
            (∑ q ∈ G.neighborFinset p, connectedWeight G w (Λ.erase p) q) :=
          connectedWeight_le_exp_neighbors G hw hp
        _ ≤ w p * Real.exp (∑ q ∈ G.neighborFinset p, w q * Real.exp (a q)) := by
          apply mul_le_mul_of_nonneg_left _ (hw p)
          apply Real.exp_le_exp.mpr
          exact sum_le_sum fun q _ => ih (Λ.erase p) (erase_ssubset hp) q
        _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (ha p)) (hw p)
    · rw [connectedWeight_eq_zero_of_notMem G hp]
      exact mul_nonneg (hw p) (Real.exp_pos _).le

#print axioms sum_rootedConnected_pow_le

end Mettapedia.Combinatorics.PolymerGas

/-! ## Absolute logarithmic coefficients -/

namespace Mettapedia.Combinatorics.PolymerGas
open SubsetExpansion
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def activatedLogPartition (a : V → ℝ) (Λ : Finset V) : Finset V → ℝ :=
  fun A => Real.log (partitionFunction G a (Λ ∩ A))

def negativeActivatedLogPartition (ρ : V → ℝ) (Λ : Finset V) : Finset V → ℝ :=
  -activatedLogPartition G (fun p => -ρ p) Λ

theorem activatedLogPartition_insert {a c : V → ℝ}
    (hD : DobrushinCondition G (fun p => (a p : ℂ)) c)
    {Λ : Finset V} {p : V} (hp : p ∉ Λ) :
    activatedLogPartition G a (insert p Λ) = activatedLogPartition G a Λ +
      fun A => Real.log (1 + (if p ∈ A then a p else 0) *
        Real.exp (activatedLogPartition G a Λ (A ∩ compatibleWith G Λ p) -
          activatedLogPartition G a Λ A)) := by
  funext A
  by_cases hpA : p ∈ A
  · have hi : insert p Λ ∩ A = insert p (Λ ∩ A) := by
      ext x
      simp only [mem_inter, mem_insert]
      constructor
      · rintro ⟨rfl | hx, hxA⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hx, hxA⟩
      · rintro (rfl | ⟨hx, hxA⟩)
        · exact ⟨Or.inl rfl, hpA⟩
        · exact ⟨Or.inr hx, hxA⟩
    have hc : Λ ∩ (A ∩ compatibleWith G Λ p) = compatibleWith G (Λ ∩ A) p := by
      ext x
      simp [compatibleWith, and_assoc, and_left_comm, and_comm]
    have hp' : p ∉ Λ ∩ A := fun h => hp (mem_inter.mp h).1
    have h0 := partitionFunction_pos_of_dobrushin hD (Λ ∩ A)
    have h1 := partitionFunction_pos_of_dobrushin hD (compatibleWith G (Λ ∩ A) p)
    have h2 := partitionFunction_pos_of_dobrushin hD (insert p (Λ ∩ A))
    rw [partitionFunction_insert (G := G) a hp'] at h2
    simp only [activatedLogPartition, Pi.add_apply, hi, hc, if_pos hpA]
    rw [partitionFunction_insert (G := G) a hp', Real.exp_sub, Real.exp_log h1, Real.exp_log h0]
    have he : 1 + a p * (partitionFunction G a (compatibleWith G (Λ ∩ A) p) /
        partitionFunction G a (Λ ∩ A)) =
        (partitionFunction G a (Λ ∩ A) + a p *
          partitionFunction G a (compatibleWith G (Λ ∩ A) p)) / partitionFunction G a (Λ ∩ A) := by
      field_simp
    rw [he, Real.log_div h2.ne' h0.ne']
    ring
  · have hi : insert p Λ ∩ A = Λ ∩ A := by
      ext x
      simp only [mem_inter, mem_insert]
      constructor
      · rintro ⟨rfl | hx, hxA⟩
        · exact (hpA hxA).elim
        · exact ⟨hx, hxA⟩
      · exact fun ⟨hx, hxA⟩ => ⟨Or.inr hx, hxA⟩
    simp [activatedLogPartition, hi, hpA]

theorem negativeActivatedLogPartition_insert {ρ c : V → ℝ}
    (hD : DobrushinCondition G (fun p => ((-ρ p : ℝ) : ℂ)) c)
    {Λ : Finset V} {p : V} (hp : p ∉ Λ) :
    negativeActivatedLogPartition G ρ (insert p Λ) = negativeActivatedLogPartition G ρ Λ +
      fun A => -Real.log (1 - (if p ∈ A then ρ p else 0) *
        Real.exp (negativeActivatedLogPartition G ρ Λ A -
          negativeActivatedLogPartition G ρ Λ (A ∩ compatibleWith G Λ p))) := by
  rw [negativeActivatedLogPartition, activatedLogPartition_insert G hD hp]
  funext A
  simp only [Pi.neg_apply, Pi.add_apply, negativeActivatedLogPartition, neg_add_rev,
    neg_sub_neg]
  by_cases h : p ∈ A <;> simp only [h, if_pos, if_false, neg_mul, sub_eq_add_neg,
    neg_zero, zero_mul, add_zero, Real.log_one, neg_zero] <;> ring

theorem negativeInsertion_lt_one {ρ c : V → ℝ} (hρ : ∀ p, 0 ≤ ρ p)
    (hD : DobrushinCondition G (fun p => ((-ρ p : ℝ) : ℂ)) c)
    (Λ : Finset V) (p : V) (A : Finset V) :
    (if p ∈ A then ρ p else 0) * Real.exp
      (negativeActivatedLogPartition G ρ Λ A -
        negativeActivatedLogPartition G ρ Λ (A ∩ compatibleWith G Λ p)) < 1 := by
  by_cases hpA : p ∈ A
  · have hc : Λ ∩ (A ∩ compatibleWith G Λ p) = compatibleWith G (Λ ∩ A) p := by
      ext x
      simp [compatibleWith, and_assoc, and_left_comm, and_comm]
    have h0 := partitionFunction_pos_of_dobrushin hD (Λ ∩ A)
    have h1 := partitionFunction_pos_of_dobrushin hD (compatibleWith G (Λ ∩ A) p)
    have hb := partitionFunction_abs_insertion_ratio_le hD (Λ ∩ A) p
    simp only [abs_div, abs_mul, abs_neg, abs_of_nonneg (hρ p), abs_of_pos h0,
      abs_of_pos h1] at hb
    simp only [if_pos hpA, negativeActivatedLogPartition, activatedLogPartition,
      Pi.neg_apply, neg_sub_neg, hc]
    rw [Real.exp_sub, Real.exp_log h1, Real.exp_log h0]
    have he := Real.exp_pos (-c p)
    rw [← mul_div_assoc]
    linarith
  · simp [hpA]

/-- Weighted absolute coefficients of the real polymer log partition are
dominated by the positive coefficients of its negative-activity companion.
The exponential and logarithmic comparisons include all powers. -/
theorem activatedLogPartition_majorizes (w : UnionWeight V) {a ρ c : V → ℝ}
    (hρ : ∀ p, 0 ≤ ρ p)
    (hD : DobrushinCondition G (fun p => ((-ρ p : ℝ) : ℂ)) c)
    (ha : ∀ p, w {p} * |a p| ≤ ρ p) (Λ : Finset V) :
    Majorizes w (activatedLogPartition G a Λ) (negativeActivatedLogPartition G ρ Λ) := by
  have hDa : DobrushinCondition G (fun p => (a p : ℂ)) c := by
    apply hD.mono_activity
    intro p
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg (hρ p)] using
      (le_mul_of_one_le_left (abs_nonneg (a p)) (w.one_le {p})).trans (ha p)
  induction Λ using Finset.induction_on with
  | empty =>
    have h0 : activatedLogPartition G a ∅ = fun _ => 0 := by
      funext A
      simp [activatedLogPartition]
    have h1 : negativeActivatedLogPartition G ρ ∅ = fun _ => 0 := by
      funext A
      simp [negativeActivatedLogPartition, activatedLogPartition]
    rw [h0, h1]
    exact majorizes_const w (show |(0 : ℝ)| ≤ 0 by norm_num)
  | @insert p Λ hp ih =>
    let R := compatibleWith G Λ p
    have hratio : Majorizes w
        (fun A => Real.exp (activatedLogPartition G a Λ (A ∩ R) - activatedLogPartition G a Λ A))
        (fun A => Real.exp (negativeActivatedLogPartition G ρ Λ A -
          negativeActivatedLogPartition G ρ Λ (A ∩ R))) := by
      simpa only [Pi.neg_apply, Pi.sub_apply, neg_sub] using (ih.sub_restrict R).neg.exp
    have hseed := majorizes_indicator w p (ha p)
    have hins := hseed.mul hratio
    have hlog := hins.log_one_add (negativeInsertion_lt_one G hρ hD Λ p)
    rw [activatedLogPartition_insert G hDa hp, negativeActivatedLogPartition_insert G hD hp]
    exact ih.add hlog

/-- Rooted coefficient sums are the difference made by disabling the root. -/
theorem sum_rooted_coefficient (F : Finset V → ℝ) (p : V) :
    ∑ S ∈ univ.filter (fun S : Finset V => p ∈ S), coefficient F S =
      F univ - F (univ.erase p) := by
  rw [← zeta_coefficient F univ, ← zeta_coefficient F (univ.erase p)]
  unfold zeta
  rw [powerset_univ]
  have he : (univ.erase p).powerset = univ.filter (fun S : Finset V => p ∉ S) := by
    ext S
    simp only [mem_powerset, mem_filter, mem_univ, true_and]
    constructor
    · intro h hp
      exact (notMem_erase p univ) (h hp)
    · intro hp x hx
      exact mem_erase.mpr ⟨fun he => hp (he ▸ hx), mem_univ _⟩
  rw [he, sum_filter, sum_filter, ← sum_sub_distrib]
  apply sum_congr rfl
  intro S hS
  by_cases h : p ∈ S <;> simp [h]

/-- The rooted absolute logarithmic coefficient budget is the Dobrushin
removal weight, independently of the finite polymer volume. -/
theorem sum_weighted_log_coefficients_le (w : UnionWeight V) {a ρ c : V → ℝ}
    (hρ : ∀ p, 0 ≤ ρ p)
    (hD : DobrushinCondition G (fun p => ((-ρ p : ℝ) : ℂ)) c)
    (ha : ∀ p, w {p} * |a p| ≤ ρ p) (Λ : Finset V) (p : V) :
    ∑ S ∈ univ.filter (fun S : Finset V => p ∈ S),
      w S * |coefficient (activatedLogPartition G a Λ) S| ≤ c p := by
  have h := activatedLogPartition_majorizes G w hρ hD ha Λ
  apply (sum_le_sum fun S _ => h S).trans
  rw [sum_rooted_coefficient]
  have he : Λ ∩ univ.erase p = Λ.erase p := by
    ext x
    simp [and_comm]
  simp only [negativeActivatedLogPartition, activatedLogPartition, Pi.neg_apply,
    inter_univ, he, neg_sub_neg]
  exact log_partitionFunction_erase_le hD Λ p

end Mettapedia.Combinatorics.PolymerGas

import Mathlib
import MixedColouring
import PurePartner

/-!
# Coordinates for a pair of disjoint matchings

Two disjoint fixed-point-free involutions with connected union make their sites into a
single alternating cycle.  This file builds that cycle explicitly — the orbit of the
product, together with its image under the first involution — and transports the fourth
matching back from the cycle model.
-/

namespace CycleCoordinates

open Equiv MixedColouring

lemma perm_inv_apply {α : Type*} (f : Perm α) (x : α) : f⁻¹ (f x) = x := by
  rw [Equiv.Perm.inv_def, Equiv.symm_apply_apply]

lemma perm_apply_inv {α : Type*} (f : Perm α) (x : α) : f (f⁻¹ x) = x := by
  rw [Equiv.Perm.inv_def, Equiv.apply_symm_apply]

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **A fourth matching, for an abstract triple of matchings.**  Three pairwise disjoint
fixed-point-free involutions of more than four sites always admit a non-constant colouring
under which every site's colour points at a partner wearing that colour. -/
theorem exists_mixed (σ : Fin 3 → Perm V)
    (hinv : ∀ k x, σ k (σ k x) = x) (hfp : ∀ k x, σ k x ≠ x)
    (hcard : 4 < Fintype.card V) :
    ∃ c : V → Fin 3, (∃ x y, c x ≠ c y) ∧ ∀ x, c (σ (c x) x) = c x := by
  classical
  set R : V → V → Prop := fun a b => b = σ 0 a ∨ b = σ 1 a with hR
  by_cases hconn : ∀ x y : V, Relation.EqvGen R x y
  · -- The union of the first two matchings is a single alternating cycle.
    haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨x₀⟩ := ‹Nonempty V›
    set ρ : Perm V := σ 0 * σ 1 with hρ
    have h00 : σ 0 * σ 0 = 1 := Equiv.ext fun x => hinv 0 x
    have h11 : σ 1 * σ 1 = 1 := Equiv.ext fun x => hinv 1 x
    have hi0 : (σ 0)⁻¹ = σ 0 := inv_eq_of_mul_eq_one_right h00
    have hi1 : (σ 1)⁻¹ = σ 1 := inv_eq_of_mul_eq_one_right h11
    have hρinv : ρ⁻¹ = σ 1 * σ 0 := by rw [hρ, mul_inv_rev, hi0, hi1]
    have hσ1 : σ 0 * ρ = σ 1 := by rw [hρ, ← mul_assoc, h00, one_mul]
    have hkey : σ 0 * ρ = ρ⁻¹ * σ 0 := by
      rw [hσ1, hρinv, mul_assoc, h00, mul_one]
    have hpow : ∀ n : ℕ, σ 0 * ρ ^ n = (ρ⁻¹) ^ n * σ 0 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ, ← mul_assoc, ih, mul_assoc, hkey, ← mul_assoc, ← pow_succ]
    -- the period of the orbit of `x₀`
    have hord : ∃ n : ℕ, 0 < n ∧ (ρ ^ n) x₀ = x₀ :=
      ⟨orderOf ρ, orderOf_pos ρ, by rw [pow_orderOf_eq_one]; rfl⟩
    set m := Nat.find hord with hmdef
    have hm0 : 0 < m := (Nat.find_spec hord).1
    have hmfix : (ρ ^ m) x₀ = x₀ := (Nat.find_spec hord).2
    have hmin : ∀ n, 0 < n → n < m → (ρ ^ n) x₀ ≠ x₀ :=
      fun n hn hlt h => Nat.find_min hord hlt ⟨hn, h⟩
    haveI : NeZero m := ⟨by omega⟩
    have hcyc : ∀ n : ℕ, (ρ ^ (n + m)) x₀ = (ρ ^ n) x₀ := by
      intro n
      rw [pow_add, Equiv.Perm.mul_apply, hmfix]
    have hkm : ∀ q n : ℕ, (ρ ^ (n + m * q)) x₀ = (ρ ^ n) x₀ := by
      intro q
      induction q with
      | zero => intro n; simp
      | succ q ih =>
        intro n
        have hre : n + m * (q + 1) = (n + m * q) + m := by ring
        rw [hre, hcyc, ih]
    have hmod : ∀ n : ℕ, (ρ ^ (n % m)) x₀ = (ρ ^ n) x₀ := by
      intro n
      conv_rhs => rw [← Nat.mod_add_div n m]
      exact (hkm (n / m) (n % m)).symm
    have hinjn : ∀ a b : ℕ, a < m → b < m → (ρ ^ a) x₀ = (ρ ^ b) x₀ → a = b := by
      have key : ∀ a b : ℕ, a < b → b < m → (ρ ^ a) x₀ = (ρ ^ b) x₀ → False := by
        intro a b hab hbm heq
        have h1 : (ρ ^ a) ((ρ ^ (b - a)) x₀) = (ρ ^ a) x₀ := by
          rw [← Equiv.Perm.mul_apply, ← pow_add]
          have hre : a + (b - a) = b := by omega
          rw [hre, heq]
        exact hmin (b - a) (by omega) (by omega) ((ρ ^ a).injective h1)
      intro a b ha hb hab
      rcases lt_trichotomy a b with h | h | h
      · exact absurd hab (fun hc => key a b h hb hc)
      · exact h
      · exact absurd hab.symm (fun hc => key b a h ha hc)
    -- the coordinate map
    set F : Site m → V := fun p => if p.2 then (ρ ^ (p.1.val)) x₀ else σ 0 ((ρ ^ (p.1.val)) x₀)
      with hF
    have hFt : ∀ i : ZMod m, F (i, true) = (ρ ^ (i.val)) x₀ := fun i => rfl
    have hFf : ∀ i : ZMod m, F (i, false) = σ 0 ((ρ ^ (i.val)) x₀) := fun i => rfl
    have hstep : ∀ i : ZMod m, ρ ((ρ ^ (i.val)) x₀) = (ρ ^ ((i + 1).val)) x₀ := by
      intro i
      have hcast : ((i.val + 1 : ℕ) : ZMod m) = i + 1 := by push_cast; simp
      have hv : (i + 1).val = (i.val + 1) % m := by
        rw [← hcast, ZMod.val_natCast]
      rw [hv, hmod, pow_succ']
      rfl
    -- the two matchings act as they do on the model
    have hFs0 : ∀ p : Site m, F (s0 p) = σ 0 (F p) := by
      rintro ⟨i, b⟩
      cases b
      · rw [show (s0 : Perm (Site m)) (i, false) = (i, true) by simp, hFt, hFf, hinv 0]
      · rw [show (s0 : Perm (Site m)) (i, true) = (i, false) by simp, hFf, hFt]
    have hFs1 : ∀ p : Site m, F (s1 p) = σ 1 (F p) := by
      rintro ⟨i, b⟩
      cases b
      · rw [show (s1 : Perm (Site m)) (i, false) = (i - 1, true) by simp, hFt, hFf]
        have h1 : σ 1 (σ 0 ((ρ ^ (i.val)) x₀)) = ρ⁻¹ ((ρ ^ (i.val)) x₀) := by
          rw [hρinv, Equiv.Perm.mul_apply]
        rw [h1]
        have h2 : ρ ((ρ ^ ((i - 1).val)) x₀) = (ρ ^ (i.val)) x₀ := by
          rw [hstep (i - 1)]
          congr 2
          ring
        rw [← h2, perm_inv_apply]
      · rw [show (s1 : Perm (Site m)) (i, true) = (i + 1, false) by simp, hFf, hFt,
          ← hσ1, Equiv.Perm.mul_apply, hstep i]
    -- the two classes are disjoint
    have hcross : ∀ a b : ℕ, σ 0 ((ρ ^ b) x₀) ≠ (ρ ^ a) x₀ := by
      intro a b hcon
      -- `σ 0 x₀` lies on the orbit; derive a fixed point of one of the two matchings
      have hstepK : ∀ n : ℕ, σ 0 ((ρ ^ n) x₀) = ((ρ ^ n)⁻¹) (σ 0 x₀) := by
        intro n
        have h := congrArg (fun g : Perm V => g x₀) (hpow n)
        simp only [Equiv.Perm.mul_apply] at h
        rw [inv_pow] at h
        exact h
      have hy : σ 0 x₀ = (ρ ^ (a + b)) x₀ := by
        have h1 : ((ρ ^ b)⁻¹) (σ 0 x₀) = (ρ ^ a) x₀ := by rw [← hstepK b]; exact hcon
        have h2 : σ 0 x₀ = (ρ ^ b) ((ρ ^ a) x₀) := by
          rw [← h1, perm_apply_inv]
        rw [h2, ← Equiv.Perm.mul_apply, ← pow_add, Nat.add_comm b a]
      set r := (a + b) % m with hr
      have hrm : r < m := Nat.mod_lt _ hm0
      set K := r + m with hK
      have hyK : σ 0 x₀ = (ρ ^ K) x₀ := by
        rw [hy, hK, hcyc r, hr, hmod]
      have hval : ∀ n : ℕ, n ≤ K → σ 0 ((ρ ^ n) x₀) = (ρ ^ (K - n)) x₀ := by
        intro n hn
        rw [hstepK n, hyK]
        have hcomp : (ρ ^ n) ((ρ ^ (K - n)) x₀) = (ρ ^ K) x₀ := by
          rw [← Equiv.Perm.mul_apply, ← pow_add]
          have hre : n + (K - n) = K := by omega
          rw [hre]
        rw [← hcomp, perm_inv_apply]
      have hno0 : ∀ n : ℕ, n < m → (K - n) % m ≠ n := by
        intro n hn hcon2
        refine hfp 0 ((ρ ^ n) x₀) ?_
        rw [hval n (by omega), ← hmod (K - n), hcon2]
      have hno1 : ∀ n : ℕ, n < m → (K - n - 1) % m ≠ n := by
        intro n hn hcon2
        refine hfp 1 ((ρ ^ n) x₀) ?_
        have h1 : σ 1 ((ρ ^ n) x₀) = σ 0 ((ρ ^ (n + 1)) x₀) := by
          rw [← hσ1, Equiv.Perm.mul_apply, pow_succ']
          rfl
        rw [h1, hval (n + 1) (by omega)]
        have hre : K - (n + 1) = K - n - 1 := by omega
        rw [hre, ← hmod (K - n - 1), hcon2]
      rcases Nat.even_or_odd r with he | he
      · obtain ⟨s, hs⟩ := he
        refine hno0 s (by omega) ?_
        have hre : K - s = s + m := by omega
        rw [hre, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : s < m)]
      · obtain ⟨s, hs⟩ := he
        refine hno1 s (by omega) ?_
        have hre : K - s - 1 = s + m := by omega
        rw [hre, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : s < m)]
    have hFinj : Function.Injective F := by
      rintro ⟨i, bi⟩ ⟨j, bj⟩ h
      cases bi <;> cases bj
      · rw [hFf, hFf] at h
        have hij : i = j := ZMod.val_injective m
          (hinjn i.val j.val (ZMod.val_lt _) (ZMod.val_lt _) ((σ 0).injective h))
        rw [hij]
      · rw [hFf, hFt] at h
        exact absurd h (hcross _ _)
      · rw [hFt, hFf] at h
        exact absurd h.symm (hcross _ _)
      · rw [hFt, hFt] at h
        have hij : i = j := ZMod.val_injective m
          (hinjn i.val j.val (ZMod.val_lt _) (ZMod.val_lt _) h)
        rw [hij]
    have hFsurj : Function.Surjective F := by
      have hmem0 : ∀ z, z ∈ Set.range F → σ 0 z ∈ Set.range F := by
        rintro _ ⟨p, rfl⟩
        exact ⟨s0 p, hFs0 p⟩
      have hmem1 : ∀ z, z ∈ Set.range F → σ 1 z ∈ Set.range F := by
        rintro _ ⟨p, rfl⟩
        exact ⟨s1 p, hFs1 p⟩
      have hiff : ∀ a b : V, Relation.EqvGen R a b → (a ∈ Set.range F ↔ b ∈ Set.range F) := by
        intro a b h
        induction h with
        | rel a b hab =>
          rcases hab with rfl | rfl
          · exact ⟨hmem0 a, fun hb => by
              have := hmem0 _ hb; rwa [hinv 0] at this⟩
          · exact ⟨hmem1 a, fun hb => by
              have := hmem1 _ hb; rwa [hinv 1] at this⟩
        | refl a => exact Iff.rfl
        | symm a b _ ih => exact ih.symm
        | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2
      intro y
      have hx₀ : x₀ ∈ Set.range F := ⟨(0, true), by rw [hFt]; simp⟩
      exact (hiff x₀ y (hconn x₀ y)).mp hx₀
    -- transport
    let Φ : Site m ≃ V := Equiv.ofBijective F ⟨hFinj, hFsurj⟩
    have hΦ : ∀ p, Φ p = F p := fun _ => rfl
    have hcard2 : Fintype.card V = 2 * m := by
      have h := Fintype.card_congr Φ.symm
      simpa [Site, Fintype.card_prod, mul_comm] using h
    have hm2 : 2 < m := by omega
    set τ : Fin 3 → Perm (Site m) := fun k => Equiv.permCongr Φ.symm (σ k) with hτ
    have hτapply : ∀ k p, Φ (τ k p) = σ k (Φ p) := by
      intro k p
      simp [hτ, Equiv.permCongr_apply]
    have hτ0 : τ 0 = s0 := Equiv.ext fun p => Φ.injective (by
      rw [hτapply 0 p]; exact (hFs0 p).symm)
    have hτ1 : τ 1 = s1 := Equiv.ext fun p => Φ.injective (by
      rw [hτapply 1 p]; exact (hFs1 p).symm)
    obtain ⟨c, ⟨p, q, hpq⟩, hc⟩ :=
      exists_mixed_model hm2 (τ 2) (fun p => Φ.injective (by rw [hτapply, hτapply, hinv 2]))
        (fun p hcon => hfp 2 (Φ p) (by rw [← hτapply, hcon])) τ hτ0 hτ1 rfl
    refine ⟨fun x => c (Φ.symm x), ⟨Φ p, Φ q, ?_⟩, ?_⟩
    · simpa using hpq
    · intro x
      show c (Φ.symm ((σ (c (Φ.symm x))) x)) = c (Φ.symm x)
      have hcon : Φ.symm ((σ (c (Φ.symm x))) x) = τ (c (Φ.symm x)) (Φ.symm x) := by
        refine Φ.injective ?_
        rw [Equiv.apply_symm_apply, hτapply, Equiv.apply_symm_apply]
      rw [hcon]
      exact hc (Φ.symm x)
  · -- The union of the first two matchings is disconnected.
    push_neg at hconn
    obtain ⟨u, v, huv⟩ := hconn
    have hstep : ∀ (x : V) (j : Fin 3), (j = 0 ∨ j = 1) →
        (Relation.EqvGen R u (σ j x) ↔ Relation.EqvGen R u x) := by
      intro x j hj
      have hxy : Relation.EqvGen R x (σ j x) := by
        refine Relation.EqvGen.rel _ _ ?_
        rcases hj with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      exact ⟨fun h => Relation.EqvGen.trans _ _ _ h (Relation.EqvGen.symm _ _ hxy),
        fun h => Relation.EqvGen.trans _ _ _ h hxy⟩
    refine ⟨fun x => if Relation.EqvGen R u x then 0 else 1, ⟨u, v, ?_⟩, ?_⟩
    · show (if Relation.EqvGen R u u then (0 : Fin 3) else 1)
        ≠ (if Relation.EqvGen R u v then (0 : Fin 3) else 1)
      rw [if_pos (Relation.EqvGen.refl u), if_neg huv]
      decide
    · intro x
      by_cases hx : Relation.EqvGen R u x
      · simp only [if_pos hx]
        exact if_pos ((hstep x 0 (Or.inl rfl)).mpr hx)
      · simp only [if_neg hx]
        exact if_neg (fun hc => hx ((hstep x 1 (Or.inr rfl)).mp hc))

/-! ### The rigid shape above four sites -/

open Amplitude MatchingSum

/-- **A three-regular solution is impossible above four sites.**  Its three matchings admit
a fourth, which is a non-constant colouring whose only contributing matching is itself, and
the no-rival lemma then makes that colouring constant. -/
theorem no_three_regular_uniform (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hV : ∀ x : V, (Finset.univ.erase x).Nonempty)
    (hcard : 4 < Fintype.card V)
    (T : PurePartner.ThreeRegular W) : False := by
  classical
  obtain ⟨σ, hpair, -, -, -, hpart⟩ := PurePartner.three_matchings W hone hzero hV T
  obtain ⟨c, ⟨x, y, hxy⟩, hc⟩ := exists_mixed σ
    (fun k z => (Amplitude.mem_pairings_iff.mp (hpair k)).1 z)
    (fun k z => (Amplitude.mem_pairings_iff.mp (hpair k)).2 z) hcard
  have hinvτ : Function.Involutive (fun z : V => σ (c z) z) := by
    intro z
    show σ (c (σ (c z) z)) (σ (c z) z) = z
    rw [hc z]
    exact (Amplitude.mem_pairings_iff.mp (hpair (c z))).1 z
  refine PurePartner.no_three_regular W hone hzero hV T ⟨hinvτ.toPerm _, c, ?_, ?_, ?_⟩
  · refine Amplitude.mem_pairings_iff.mpr ⟨fun z => hinvτ z, fun z => ?_⟩
    exact (Amplitude.mem_pairings_iff.mp (hpair (c z))).2 z
  · intro z
    exact hpart (c z) z
  · rintro ⟨k, hk⟩
    exact hxy ((hk x).trans (hk y).symm)

end CycleCoordinates

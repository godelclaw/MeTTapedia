import Mathlib
import Mettapedia.Combinatorics.Matching.PfaffianContraction
import CharTwoDescent

/-!
# Fermionic GHZ systems and their descent

Order the sites.  A *fermionic* GHZ system is one whose **signed** matching sum
(`MatchingPfaffian.pfSum`, the Pfaffian of the skew matrix the weights define) is nonzero at
every constant colouring and vanishes at every mixed one.

Capping two sites of a signed matching sum is exact in every characteristic
(`MatchingPfaffian.capVal_mul_pfSum_update_eq_cap`).  So the descent that
`KrennCharTwo.descent` performs for unsigned sums when `2 = 0` works here over every field:
a fermionic GHZ system on at least four sites contracts to one on two fewer sites
(`descent`).  Every even count therefore reduces to six (`no_isFermiGHZ_of_six`).
-/

namespace KrennFermi

open Amplitude MatchingSum MatchingPfaffian MatchingBlockRank KrennCharTwo

variable {F : Type*} [Field F]

section Transport

variable {V C R : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] [CommRing R]

omit [Fintype V] [DecidableEq V] in
/-- Positions are preserved by the inclusion of a subset. -/
theorem pos_map_subtype {S : Finset V} (T : Finset ↥S) (v : ↥S) :
    pos (T.map (Function.Embedding.subtype _)) (v : V) = pos T v := by
  unfold pos
  rw [← Finset.card_map (Function.Embedding.subtype (· ∈ S)), Finset.filter_map]
  congr 2

omit [Fintype V] in
/-- **A signed matching sum over a subset is a signed matching sum on the subtype.** -/
theorem pfSum_restrict_map (W : Sym2 (V × C) → R) (S : Finset V) (c : V → C)
    (T : Finset ↥S) :
    pfSum W c (T.map (Function.Embedding.subtype _))
      = pfSum (restrictW W S) (fun u : ↥S => c (u : V)) T := by
  induction hn : T.card using Nat.strong_induction_on generalizing T with
  | _ n ih =>
  rcases T.eq_empty_or_nonempty with hT | hne
  · subst hT; simp
  set m := T.min' hne with hm
  have hmT : m ∈ T := T.min'_mem hne
  have hmin : ∀ w ∈ T, m ≤ w := fun w hw => Finset.min'_le T w hw
  have hmT' : (m : V) ∈ T.map (Function.Embedding.subtype _) := Finset.mem_map_of_mem _ hmT
  have hmin' : ∀ w ∈ T.map (Function.Embedding.subtype (· ∈ S)), (m : V) ≤ w := by
    intro w hw
    obtain ⟨t, ht, rfl⟩ := Finset.mem_map.mp hw
    exact hmin t ht
  rw [pfSum_min W c hmT' hmin', pfSum_min _ _ hmT hmin]
  have herase : (T.map (Function.Embedding.subtype (· ∈ S))).erase (m : V)
      = (T.erase m).map (Function.Embedding.subtype _) :=
    (Finset.map_erase (Function.Embedding.subtype _) T m).symm
  rw [herase, Finset.sum_map]
  refine Finset.sum_congr rfl fun v hv => ?_
  have hset : ((T.erase m).map (Function.Embedding.subtype (· ∈ S))).erase (v : V)
      = ((T.erase m).erase v).map (Function.Embedding.subtype _) :=
    (Finset.map_erase (Function.Embedding.subtype _) (T.erase m) v).symm
  have hlt : ((T.erase m).erase v).card < n := by
    rw [← hn]
    exact lt_of_le_of_lt Finset.card_erase_le (Finset.card_erase_lt_of_mem hmT)
  simp only [Function.Embedding.coe_subtype]
  rw [hset, ih _ hlt _ rfl, pos_map_subtype]
  rfl

omit [Fintype V] in
/-- The signed matching sum of the restricted system over all of its sites. -/
theorem pfSum_restrict_univ (W : Sym2 (V × C) → R) (S : Finset V) (c : V → C) :
    pfSum (restrictW W S) (fun u : ↥S => c (u : V)) Finset.univ = pfSum W c S := by
  rw [← pfSum_restrict_map W S c]
  congr 1
  ext v
  simp

end Transport

section Defs

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

/-- **A fermionic GHZ system**: the signed matching sum is nonzero at every constant colouring
and vanishes at every mixed one. -/
def IsFermiGHZ (W : Sym2 (V × Fin 3) → F) : Prop :=
  (∀ k : Fin 3, pfSum W (Amplitude.const (V := V) k) Finset.univ ≠ 0) ∧
  (∀ c : V → Fin 3, ¬ Monochromatic c → pfSum W c Finset.univ = 0)

end Defs

section Contract

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

/-- **The capped signed sum of a fermionic GHZ system.**  Capping the pivots kills every
colouring of the rest that is not constant, and scales the constant colouring `k` by
`κ k * μ k`. -/
theorem sum_cap_pfSum_of_isFermiGHZ {W : Sym2 (V × Fin 3) → F} (hW : IsFermiGHZ W)
    {p q : V} (hpq : p ≠ q) (hne : (rest p q).Nonempty) (κ μ : Fin 3 → F) (c : V → Fin 3) :
    ∑ a, ∑ b, κ a * μ b * pfSum W (paintTwo c p q a b) Finset.univ
      = if h : ∃ k, ∀ u ∈ rest p q, c u = k then
          κ h.choose * μ h.choose * pfSum W (Amplitude.const (V := V) h.choose) Finset.univ
        else 0 := by
  classical
  obtain ⟨u₀, hu₀⟩ := hne
  have hu₀p : u₀ ≠ p := fun h => p_notMem_rest p q (h ▸ hu₀)
  have hu₀q : u₀ ≠ q := fun h => q_notMem_rest p q (h ▸ hu₀)
  split_ifs with h
  · set k := h.choose with hk
    have hck : ∀ u ∈ rest p q, c u = k := h.choose_spec
    have hterm : ∀ a b, κ a * μ b * pfSum W (paintTwo c p q a b) Finset.univ
        = if a = k ∧ b = k then
            κ k * μ k * pfSum W (Amplitude.const (V := V) k) Finset.univ else 0 := by
      intro a b
      split_ifs with hab
      · obtain ⟨ha, hb⟩ := hab
        rw [ha, hb]
        congr 2
        funext v
        by_cases hvp : v = p
        · rw [hvp, paintTwo_fst c hpq k k]; rfl
        · by_cases hvq : v = q
          · rw [hvq, paintTwo_snd c p q k k]; rfl
          · rw [paintTwo_other c hvp hvq]
            exact hck v (by simp [rest, hvp, hvq])
      · rw [hW.2 _ ?_, mul_zero]
        rintro ⟨m, hm⟩
        have h1 : m = k := by
          have := hm u₀
          rw [paintTwo_other c hu₀p hu₀q] at this
          rw [← this, hck u₀ hu₀]
        refine hab ⟨?_, ?_⟩
        · have := hm p; rw [paintTwo_fst c hpq] at this; rw [this, h1]
        · have := hm q; rw [paintTwo_snd c p q] at this; rw [this, h1]
    simp_rw [hterm]
    rw [Finset.sum_eq_single k (fun a _ ha => Finset.sum_eq_zero fun b _ => by
      rw [if_neg (fun hab => ha hab.1)]) (by simp)]
    rw [Finset.sum_eq_single k (fun b _ hb => by rw [if_neg (fun hab => hb hab.2)]) (by simp)]
    rw [if_pos ⟨rfl, rfl⟩]
  · refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    rw [hW.2 _ ?_, mul_zero]
    rintro ⟨m, hm⟩
    refine h ⟨m, fun u hu => ?_⟩
    have hup : u ≠ p := fun e => p_notMem_rest p q (e ▸ hu)
    have huq : u ≠ q := fun e => q_notMem_rest p q (e ▸ hu)
    have := hm u
    rwa [paintTwo_other c hup huq] at this

/-- The contracted weights of a fermionic system at the pivots `p, q` with caps `κ, μ`, read on
the remaining sites. -/
noncomputable def contractW (W : Sym2 (V × Fin 3) → F) (p q : V) (κ μ : Fin 3 → F) :
    Sym2 (↥(rest p q) × Fin 3) → F :=
  restrictW (update W (profile W p κ) (profile W q μ) (capVal W p q κ μ)) (rest p q)

/-- **Contraction preserves fermionic GHZ systems, in every characteristic.**  For any cap whose
oriented value on the pivot pair and whose diagonal entries are nonzero, the contracted weights
on the remaining sites form a fermionic GHZ system. -/
theorem isFermiGHZ_contract {W : Sym2 (V × Fin 3) → F} (hW : IsFermiGHZ W)
    {p q : V} (hpq : p ≠ q) (hcard : 4 ≤ Fintype.card V) (κ μ : Fin 3 → F)
    (hs : capVal W p q κ μ ≠ 0) (hdiag : ∀ k, κ k * μ k ≠ 0) :
    IsFermiGHZ (contractW W p q κ μ) := by
  classical
  have hcardU := card_rest (V := V) hpq
  have hne : (rest p q).Nonempty := by
    rw [← Finset.card_pos]; omega
  let ext : (↥(rest p q) → Fin 3) → V → Fin 3 := fun c' v =>
    if h : v ∈ rest p q then c' ⟨v, h⟩ else 0
  have hext : ∀ c' : ↥(rest p q) → Fin 3, (fun u : ↥(rest p q) => ext c' (u : V)) = c' := by
    intro c'; funext u; simp [ext, u.2]
  have hsign : ∀ S : Finset V, ((-1 : F) ^ (pos S p + pos S q + if q < p then 1 else 0)) ≠ 0 :=
    fun S => pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hamp : ∀ c' : ↥(rest p q) → Fin 3,
      capVal W p q κ μ * pfSum (contractW W p q κ μ) c' Finset.univ
        = (-1) ^ (pos (rest p q) p + pos (rest p q) q + if q < p then 1 else 0) *
            capVal W p q κ μ ^ ((rest p q).card / 2) *
              ∑ a, ∑ b, κ a * μ b * pfSum W (paintTwo (ext c') p q a b) Finset.univ := by
    intro c'
    conv_lhs => rw [← hext c']
    rw [contractW, pfSum_restrict_univ,
      capVal_mul_pfSum_update_eq_cap W κ μ (ext c') hpq (p_notMem_rest p q) (q_notMem_rest p q)]
    unfold capPf
    rw [insert_insert_rest p q]
  refine ⟨fun k => ?_, fun c' hc' => ?_⟩
  · intro hzero
    have h0 := hamp (Amplitude.const k)
    rw [hzero, mul_zero, sum_cap_pfSum_of_isFermiGHZ hW hpq hne κ μ] at h0
    have hex : ∃ m, ∀ u ∈ rest p q, ext (Amplitude.const k) u = m :=
      ⟨k, fun u hu => by simp [ext, hu, Amplitude.const]⟩
    rw [dif_pos hex] at h0
    have hm : hex.choose = k := by
      obtain ⟨u, hu⟩ := hne
      have := hex.choose_spec u hu
      simp [ext, hu, Amplitude.const] at this
      exact this.symm
    rw [hm] at h0
    exact (mul_ne_zero (mul_ne_zero (hsign _) (pow_ne_zero _ hs))
      (mul_ne_zero (hdiag k) (hW.1 k))) h0.symm
  · have h0 := hamp c'
    rw [sum_cap_pfSum_of_isFermiGHZ hW hpq hne κ μ] at h0
    have hnex : ¬ ∃ m, ∀ u ∈ rest p q, ext c' u = m := by
      rintro ⟨m, hm⟩
      exact hc' ⟨m, fun u => by have := hm u u.2; simpa [ext, u.2] using this⟩
    rw [dif_neg hnex, mul_zero] at h0
    exact (mul_eq_zero.mp h0).resolve_left hs

/-- A fermionic GHZ system has a live edge in colour `0` at every site. -/
theorem exists_live_pair {W : Sym2 (V × Fin 3) → F} (hW : IsFermiGHZ W) (p : V) :
    ∃ q, q ≠ p ∧ W s((p, 0), (q, 0)) ≠ 0 := by
  have h0 := hW.1 0
  rw [pfSum_expand W _ (Finset.mem_univ p)] at h0
  obtain ⟨q, hq, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h0
  refine ⟨q, (Finset.mem_erase.mp hq).1, fun h => hne ?_⟩
  show _ * W s((p, Amplitude.const 0 p), (q, Amplitude.const 0 q)) * _ = 0
  simp only [Amplitude.const] at h ⊢
  rw [h, mul_zero, zero_mul]

/-- **Descent.**  Over an infinite field, a fermionic GHZ system on at least four sites yields
one on two fewer sites.  No assumption on the characteristic. -/
theorem descent [Infinite F] {W : Sym2 (V × Fin 3) → F} (hW : IsFermiGHZ W)
    (hcard : 4 ≤ Fintype.card V) :
    ∃ U : Finset V, U.card + 2 = Fintype.card V ∧
      ∃ W' : Sym2 (↥U × Fin 3) → F, IsFermiGHZ W' := by
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨p⟩ := hne
  obtain ⟨q, hqp, hlive⟩ := exists_live_pair hW p
  obtain ⟨κ, μ, hs, hdiag⟩ := exists_valid_cap (fun a b => W s((p, a), (q, b))) hlive
  have hs' : capVal W p q κ μ ≠ 0 := by
    unfold capVal orient
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hs
  exact ⟨rest p q, card_rest (Ne.symm hqp), _,
    isFermiGHZ_contract hW (Ne.symm hqp) hcard κ μ hs' hdiag⟩

end Contract

/-- **Every even count reduces to six.**  Over an infinite field, if no six-site fermionic GHZ
system exists then none exists on `2n` sites for any `n ≥ 3`. -/
theorem no_isFermiGHZ_of_six [Infinite F]
    (hbase : ∀ (V : Type) [Fintype V] [DecidableEq V] [LinearOrder V], Fintype.card V = 6 →
      ∀ W : Sym2 (V × Fin 3) → F, ¬ IsFermiGHZ W) :
    ∀ n : ℕ, 3 ≤ n → ∀ (V : Type) [Fintype V] [DecidableEq V] [LinearOrder V],
      Fintype.card V = 2 * n → ∀ W : Sym2 (V × Fin 3) → F, ¬ IsFermiGHZ W := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    intro V _ _ _ hV W hW
    by_cases h3 : n + 1 = 3
    · exact hbase V (by rw [hV, h3]) W hW
    · have hn3 : 3 ≤ n := by omega
      obtain ⟨U, hU, W', hW'⟩ := descent hW (by rw [hV]; omega)
      exact ih hn3 (↥U) (by rw [Fintype.card_coe]; omega) W' hW'

end KrennFermi

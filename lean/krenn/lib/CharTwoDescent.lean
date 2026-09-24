import Mathlib
import Mettapedia.Combinatorics.Matching.CharTwoContraction

/-!
# Descent in characteristic two

Over a field in which `2 = 0`, a three-colour GHZ system on a vertex set contracts to one
on two fewer vertices.  Pick two sites carrying a live edge and a rank-one cap `κ ⊗ μ` whose
value on that edge is nonzero and whose diagonal entries `κ k * μ k` are nonzero.  The
contracted weights of `MatchingCharTwo`, read on the remaining sites, form a GHZ system:
capping the original one kills every mixed colouring and scales each constant colouring
by `κ k * μ k`.

Over an infinite field such a cap always exists, so every GHZ system descends.  A finite
field embeds in its algebraic closure, which is infinite, and GHZ systems survive the
embedding.
-/

namespace KrennCharTwo

open Amplitude MatchingSum MatchingBlockRank MatchingCharTwo

variable {F : Type*} [Field F]

/-- A three-colour GHZ system over an arbitrary field: every constant colouring has a
nonzero amplitude and every mixed colouring a vanishing one. -/
def IsGHZOver {V : Type*} [Fintype V] [DecidableEq V] (W : Sym2 (V × Fin 3) → F) : Prop :=
  (∀ k : Fin 3, amplitude W (Amplitude.const (V := V) k) ≠ 0) ∧
  (∀ c : V → Fin 3, ¬ Monochromatic c → amplitude W c = 0)

section RingHom

variable {V C : Type*} [Fintype V] [DecidableEq V] {R S : Type*} [CommRing R] [CommRing S]

/-- Matching sums commute with ring homomorphisms. -/
theorem pmSum_map_ringHom (f : R →+* S) (W : Sym2 (V × C) → R) (c : V → C) (T : Finset V) :
    pmSum (fun e => f (W e)) c T = f (pmSum W c T) := by
  simp only [pmSum, map_sum, map_prod]

theorem amplitude_map_ringHom (f : R →+* S) (W : Sym2 (V × C) → R) (c : V → C) :
    amplitude (fun e => f (W e)) c = f (amplitude W c) := by
  rw [← pmSum_univ, ← pmSum_univ, pmSum_map_ringHom]

/-- A GHZ system stays one under a field embedding. -/
theorem isGHZOver_map {K : Type*} [Field K] (f : F →+* K) (W : Sym2 (V × Fin 3) → F)
    (hW : IsGHZOver W) : IsGHZOver (fun e => f (W e)) := by
  refine ⟨fun k => ?_, fun c hc => ?_⟩
  · rw [amplitude_map_ringHom]
    exact (map_ne_zero f).mpr (hW.1 k)
  · rw [amplitude_map_ringHom, hW.2 c hc, map_zero]

end RingHom

section Contract

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The sites other than the two pivots. -/
def rest (p q : V) : Finset V := (Finset.univ.erase p).erase q

theorem card_rest {p q : V} (hpq : p ≠ q) : (rest p q).card + 2 = Fintype.card V := by
  have hq : q ∈ Finset.univ.erase p := Finset.mem_erase.mpr ⟨fun h => hpq h.symm, Finset.mem_univ q⟩
  rw [rest, Finset.card_erase_of_mem hq, Finset.card_erase_of_mem (Finset.mem_univ p),
    Finset.card_univ]
  have : 2 ≤ Fintype.card V := by
    have hsub : ({p, q} : Finset V) ⊆ Finset.univ := Finset.subset_univ _
    have := Finset.card_le_card hsub
    rw [Finset.card_pair hpq, Finset.card_univ] at this
    exact this
  omega

theorem insert_insert_rest (p q : V) :
    insert p (insert q (rest p q)) = Finset.univ := by
  ext x
  simp only [rest, Finset.mem_insert, Finset.mem_erase, Finset.mem_univ, and_true, iff_true]
  by_cases hxp : x = p
  · exact Or.inl hxp
  · by_cases hxq : x = q
    · exact Or.inr (Or.inl hxq)
    · exact Or.inr (Or.inr ⟨hxq, hxp⟩)

theorem p_notMem_rest (p q : V) : p ∉ rest p q := by
  simp [rest]

theorem q_notMem_rest (p q : V) : q ∉ rest p q := by
  simp [rest]

/-- **The capped amplitude of a GHZ system.**  Capping the pivots with `κ ⊗ μ` kills every
colouring of the rest that is not constant, and scales the constant colouring `k` by
`κ k * μ k`. -/
theorem sum_cap_amplitude_of_isGHZ {W : Sym2 (V × Fin 3) → F} (hW : IsGHZOver W)
    {p q : V} (hpq : p ≠ q) (hne : (rest p q).Nonempty) (κ μ : Fin 3 → F) (c : V → Fin 3) :
    ∑ a, ∑ b, κ a * μ b * amplitude W (paintTwo c p q a b)
      = if h : ∃ k, ∀ u ∈ rest p q, c u = k then
          κ h.choose * μ h.choose * amplitude W (Amplitude.const (V := V) h.choose)
        else 0 := by
  classical
  obtain ⟨u₀, hu₀⟩ := hne
  have hu₀p : u₀ ≠ p := fun h => p_notMem_rest p q (h ▸ hu₀)
  have hu₀q : u₀ ≠ q := fun h => q_notMem_rest p q (h ▸ hu₀)
  split_ifs with h
  · set k := h.choose with hk
    have hck : ∀ u ∈ rest p q, c u = k := h.choose_spec
    -- only `a = b = k` survives
    have hterm : ∀ a b, κ a * μ b * amplitude W (paintTwo c p q a b)
        = if a = k ∧ b = k then κ k * μ k * amplitude W (Amplitude.const (V := V) k) else 0 := by
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

/-- **Contraction preserves GHZ in characteristic two.**  For any cap whose value on the
pivot edge and whose diagonal entries are nonzero, the contracted weights read on the
remaining sites form a GHZ system. -/
theorem isGHZOver_contract (h2 : (2 : F) = 0) {W : Sym2 (V × Fin 3) → F} (hW : IsGHZOver W)
    {p q : V} (hpq : p ≠ q) (hcard : 4 ≤ Fintype.card V) (κ μ : Fin 3 → F)
    (hs : capValue W p q κ μ ≠ 0) (hdiag : ∀ k, κ k * μ k ≠ 0) :
    IsGHZOver (restrictW (contracted W p q κ μ) (rest p q)) := by
  classical
  have hcardU := card_rest (V := V) hpq
  have hne : (rest p q).Nonempty := by
    rw [← Finset.card_pos]; omega
  -- extend a colouring of the rest to the whole vertex set
  let ext : (↥(rest p q) → Fin 3) → V → Fin 3 := fun c' v =>
    if h : v ∈ rest p q then c' ⟨v, h⟩ else 0
  have hext : ∀ c' : ↥(rest p q) → Fin 3, (fun u : ↥(rest p q) => ext c' (u : V)) = c' := by
    intro c'; funext u; simp [ext, u.2]
  -- the contracted amplitude, in terms of the capped amplitude
  have hamp : ∀ c' : ↥(rest p q) → Fin 3,
      capValue W p q κ μ * amplitude (restrictW (contracted W p q κ μ) (rest p q)) c'
        = capValue W p q κ μ ^ ((rest p q).card / 2) *
            ∑ a, ∑ b, κ a * μ b * amplitude W (paintTwo (ext c') p q a b) := by
    intro c'
    conv_lhs => rw [← hext c']
    rw [amplitude_restrictSites,
      capValue_mul_pmSum_contracted_eq_cap W p q κ μ h2 (ext c') hpq (p_notMem_rest p q)
        (q_notMem_rest p q), insert_insert_rest p q]
    simp only [pmSum_univ]
  have hhalf : 1 ≤ (rest p q).card / 2 := by omega
  refine ⟨fun k => ?_, fun c' hc' => ?_⟩
  · intro hzero
    have h0 := hamp (Amplitude.const k)
    rw [hzero, mul_zero, sum_cap_amplitude_of_isGHZ hW hpq hne κ μ] at h0
    have hex : ∃ m, ∀ u ∈ rest p q, ext (Amplitude.const k) u = m :=
      ⟨k, fun u hu => by simp [ext, hu, Amplitude.const]⟩
    rw [dif_pos hex] at h0
    have hm : hex.choose = k := by
      obtain ⟨u, hu⟩ := hne
      have := hex.choose_spec u hu
      simp [ext, hu, Amplitude.const] at this
      exact this.symm
    rw [hm] at h0
    exact (mul_ne_zero (pow_ne_zero _ hs) (mul_ne_zero (hdiag k) (hW.1 k))) h0.symm
  · have h0 := hamp c'
    rw [sum_cap_amplitude_of_isGHZ hW hpq hne κ μ] at h0
    have hnex : ¬ ∃ m, ∀ u ∈ rest p q, ext c' u = m := by
      rintro ⟨m, hm⟩
      exact hc' ⟨m, fun u => by have := hm u u.2; simpa [ext, u.2] using this⟩
    rw [dif_neg hnex, mul_zero] at h0
    exact (mul_eq_zero.mp h0).resolve_left hs

/-- A GHZ system has a live edge in colour `0` at every site. -/
theorem exists_live_pair {W : Sym2 (V × Fin 3) → F} (hW : IsGHZOver W) (p : V) :
    ∃ q, q ≠ p ∧ W s((p, 0), (q, 0)) ≠ 0 := by
  have h0 := hW.1 0
  rw [← pmSum_univ] at h0
  obtain ⟨q, hq, hw, -⟩ := exists_partner_ne_zero W _ (Finset.mem_univ p) h0
  exact ⟨q, (Finset.mem_erase.mp hq).1, hw⟩

/-- **A valid cap exists over an infinite field.**  If the pivot block has a nonzero entry in
colours `(0,0)`, some cap `κ = μ = (1, t, t)` has nonzero value and nonzero diagonal. -/
theorem exists_valid_cap [Infinite F] (M : Fin 3 → Fin 3 → F) (h00 : M 0 0 ≠ 0) :
    ∃ κ μ : Fin 3 → F, (∑ a, ∑ b, κ a * μ b * M a b) ≠ 0 ∧ ∀ k, κ k * μ k ≠ 0 := by
  classical
  set α := M 0 1 + M 0 2 + M 1 0 + M 2 0 with hα
  set β := M 1 1 + M 1 2 + M 2 1 + M 2 2 with hβ
  let P : Polynomial F := Polynomial.C (M 0 0) + Polynomial.C α * Polynomial.X
    + Polynomial.C β * Polynomial.X ^ 2
  have hP : P ≠ 0 := by
    intro h
    have := congrArg (fun f => Polynomial.coeff f 0) h
    simp [P] at this
    exact h00 this
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset (insert (0 : F) P.roots.toFinset)
  have ht0 : t ≠ 0 := fun h => ht (by simp [h])
  have htP : P.eval t ≠ 0 := by
    intro h
    exact ht (Finset.mem_insert_of_mem (Multiset.mem_toFinset.mpr
      ((Polynomial.mem_roots hP).mpr h)))
  let κ : Fin 3 → F := fun k => if k = 0 then 1 else t
  refine ⟨κ, κ, ?_, fun k => ?_⟩
  · have : (∑ a, ∑ b, κ a * κ b * M a b) = P.eval t := by
      simp only [P, Fin.sum_univ_three, κ, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow, hα, hβ]
      simp
      ring
    rw [this]; exact htP
  · by_cases hk : k = 0
    · simp [κ, hk]
    · simp [κ, hk, ht0]

/-- **Descent.**  Over an infinite field in which `2 = 0`, a GHZ system on at least four sites
yields one on two fewer sites. -/
theorem descent (h2 : (2 : F) = 0) [Infinite F] {W : Sym2 (V × Fin 3) → F}
    (hW : IsGHZOver W) (hcard : 4 ≤ Fintype.card V) :
    ∃ U : Finset V, U.card + 2 = Fintype.card V ∧
      ∃ W' : Sym2 (↥U × Fin 3) → F, IsGHZOver W' := by
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨p⟩ := hne
  obtain ⟨q, hqp, hlive⟩ := exists_live_pair hW p
  obtain ⟨κ, μ, hs, hdiag⟩ := exists_valid_cap (fun a b => W s((p, a), (q, b))) hlive
  exact ⟨rest p q, card_rest (Ne.symm hqp), _,
    isGHZOver_contract h2 hW (Ne.symm hqp) hcard κ μ hs hdiag⟩

end Contract

/-- **Every even count reduces to six.**  Over an infinite field in which `2 = 0`, if no
six-site GHZ system exists then none exists on `2n` sites for any `n ≥ 3`. -/
theorem no_isGHZOver_of_six (h2 : (2 : F) = 0) [Infinite F]
    (hbase : ∀ (V : Type) [Fintype V] [DecidableEq V], Fintype.card V = 6 →
      ∀ W : Sym2 (V × Fin 3) → F, ¬ IsGHZOver W) :
    ∀ n : ℕ, 3 ≤ n → ∀ (V : Type) [Fintype V] [DecidableEq V], Fintype.card V = 2 * n →
      ∀ W : Sym2 (V × Fin 3) → F, ¬ IsGHZOver W := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    intro V _ _ hV W hW
    by_cases h3 : n + 1 = 3
    · exact hbase V (by rw [hV, h3]) W hW
    · have hn3 : 3 ≤ n := by omega
      obtain ⟨U, hU, W', hW'⟩ := descent h2 hW (by rw [hV]; omega)
      exact ih hn3 (↥U) (by rw [Fintype.card_coe]; omega) W' hW'

end KrennCharTwo

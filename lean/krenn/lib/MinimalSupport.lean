import Mathlib
import Amplitude
import Degenerate
import FanStructure
import LiveDegree
import CycleCoordinates
import Separation

/-!
# Minimal-support GHZ systems

The support-degree bound used by the current endgame should be attacked on an
irredundant hypothetical solution, not on every presentation of one.  This file
makes that reduction exact.

Among all GHZ systems on a fixed finite vertex set, choose one minimizing the
sum of its live degrees.  An inert live pair can be zeroed without changing any
amplitude, and doing so strictly decreases that sum.  Consequently every live
pair of a minimal-support system participates in at least one amplitude.
-/

namespace MinimalSupport

open Amplitude MatchingSum
open FanStructure
open LiveDegree

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Zero the entire colour block over the unordered site-pair `{u,v}`. -/
noncomputable def zeroPair (W : Sym2 (V × Fin 3) → ℂ) (u v : V) :
    Sym2 (V × Fin 3) → ℂ :=
  fun e => if Sym2.map Prod.fst e = s(u, v) then 0 else W e

omit [Fintype V] in
@[simp] lemma zeroPair_target (W : Sym2 (V × Fin 3) → ℂ) (u v : V)
    (a b : Fin 3) : zeroPair W u v s((u, a), (v, b)) = 0 := by
  simp [zeroPair]

omit [Fintype V] in
lemma zeroPair_agree (W : Sym2 (V × Fin 3) → ℂ) (u v x y : V)
    (a b : Fin 3) (h₁ : ¬ (x = u ∧ y = v)) (h₂ : ¬ (x = v ∧ y = u)) :
    zeroPair W u v s((x, a), (y, b)) = W s((x, a), (y, b)) := by
  rw [zeroPair]
  split_ifs with h
  · rw [Sym2.map_mk, Sym2.eq_iff] at h
    exact (h.elim h₁ h₂).elim
  · rfl

/-- Zeroing an inert pair preserves every amplitude. -/
theorem amplitude_zeroPair_of_inert (W : Sym2 (V × Fin 3) → ℂ)
    {u v : V} (hvu : v ≠ u) (hinert : Inert W u v) (c : V → Fin 3) :
    amplitude (zeroPair W u v) c = amplitude W c :=
  Degenerate.amplitude_of_inert W (zeroPair W u v) hvu hinert
    (fun x y a b h₁ h₂ => zeroPair_agree W u v x y a b h₁ h₂)
    (zeroPair_target W u v) c

/-- Zeroing an inert pair preserves the GHZ equations. -/
theorem isGHZ_zeroPair_of_inert (W : Sym2 (V × Fin 3) → ℂ)
    {u v : V} (hvu : v ≠ u) (hinert : Inert W u v)
    (hW : KrennGu.IsGHZ W) : KrennGu.IsGHZ (zeroPair W u v) := by
  rcases hW with ⟨hone, hzero⟩
  constructor
  · intro k
    rw [amplitude_zeroPair_of_inert W hvu hinert]
    exact hone k
  · intro c hc
    rw [amplitude_zeroPair_of_inert W hvu hinert]
    exact hzero c hc

/-- Zeroing a pair cannot create a live neighbour. -/
lemma liveNbrs_zeroPair_subset (W : Sym2 (V × Fin 3) → ℂ) (u v x : V) :
    liveNbrs (zeroPair W u v) x ⊆ liveNbrs W x := by
  intro y hy
  rw [mem_liveNbrs] at hy ⊢
  rcases hy with ⟨hyx, a, b, hab⟩
  refine ⟨hyx, a, b, ?_⟩
  rw [zeroPair] at hab
  split_ifs at hab with h
  · exact (hab rfl).elim
  · exact hab

/-- The support size used for minimization: the sum of all live degrees.
Each unordered off-diagonal live pair is counted twice. -/
noncomputable def supportMass (W : Sym2 (V × Fin 3) → ℂ) : ℕ :=
  ∑ u : V, (liveNbrs W u).card

/-- Zeroing a live pair strictly decreases support mass. -/
theorem supportMass_zeroPair_lt (W : Sym2 (V × Fin 3) → ℂ)
    {u v : V} (hvu : v ≠ u) (hlive : ∃ a b : Fin 3,
      W s((u, a), (v, b)) ≠ 0) :
    supportMass (zeroPair W u v) < supportMass W := by
  classical
  rw [supportMass, supportMass]
  apply Finset.sum_lt_sum
  · intro x hx
    exact Finset.card_le_card (liveNbrs_zeroPair_subset W u v x)
  · refine ⟨u, Finset.mem_univ u, ?_⟩
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨liveNbrs_zeroPair_subset W u v u, ?_⟩
    intro heq
    have hv_old : v ∈ liveNbrs W u := mem_liveNbrs.mpr ⟨hvu, hlive⟩
    have hv_new : v ∉ liveNbrs (zeroPair W u v) u := by
      rw [mem_liveNbrs]
      push Not
      intro _ a b
      exact zeroPair_target W u v a b
    exact hv_new (heq ▸ hv_old)

/-- A GHZ system has minimal support if no GHZ system on the same vertex set
has smaller support mass. -/
def IsSupportMinimal (W : Sym2 (V × Fin 3) → ℂ) : Prop :=
  KrennGu.IsGHZ W ∧ ∀ W' : Sym2 (V × Fin 3) → ℂ,
    KrennGu.IsGHZ W' → supportMass W ≤ supportMass W'

/-- Every hypothetical solution has a support-minimal representative on the
same vertex set. -/
theorem exists_supportMinimal (W : Sym2 (V × Fin 3) → ℂ)
    (hW : KrennGu.IsGHZ W) :
    ∃ W' : Sym2 (V × Fin 3) → ℂ,
      IsSupportMinimal W' ∧ supportMass W' ≤ supportMass W := by
  classical
  let P : ℕ → Prop := fun n => ∃ X : Sym2 (V × Fin 3) → ℂ,
    KrennGu.IsGHZ X ∧ supportMass X = n
  have hex : ∃ n, P n := ⟨supportMass W, W, hW, rfl⟩
  obtain ⟨W', hW', hm⟩ := Nat.find_spec hex
  refine ⟨W', ⟨hW', ?_⟩, ?_⟩
  · intro X hX
    have hPX : P (supportMass X) := ⟨X, hX, rfl⟩
    simpa [hm] using Nat.find_min' hex hPX
  · have hPW : P (supportMass W) := ⟨W, hW, rfl⟩
    simpa [hm] using Nat.find_min' hex hPW

/-- In a minimal-support solution every live pair participates: its complementary
matching sum is nonzero for at least one colouring. -/
theorem not_inert_of_supportMinimal {W : Sym2 (V × Fin 3) → ℂ}
    (hmin : IsSupportMinimal W) {u v : V} (hvu : v ≠ u)
    (hlive : ∃ a b : Fin 3, W s((u, a), (v, b)) ≠ 0) :
    ¬ Inert W u v := by
  intro hinert
  have hW' : KrennGu.IsGHZ (zeroPair W u v) :=
    isGHZ_zeroPair_of_inert W hvu hinert hmin.1
  have hle := hmin.2 (zeroPair W u v) hW'
  exact (Nat.not_lt_of_ge hle) (supportMass_zeroPair_lt W hvu hlive)

/-- Minimal support supplies the exact irredundancy hypothesis used by the
support-theoretic arguments: every live neighbour is non-inert. -/
theorem live_not_inert_of_supportMinimal {W : Sym2 (V × Fin 3) → ℂ}
    (hmin : IsSupportMinimal W) {u v : V} (hv : v ∈ liveNbrs W u) :
    ¬ Inert W u v := by
  rw [mem_liveNbrs] at hv
  exact not_inert_of_supportMinimal hmin hv.1 hv.2

/-! ### A first global consequence: no support bridge -/

/-- If an odd cut has only one potentially live crossing pair, every amplitude
uses that pair and factors through its complementary matching sum. -/
theorem amplitude_eq_of_unique_crossing (W : Sym2 (V × Fin 3) → ℂ)
    (S : Finset V) {u v : V} (huS : u ∈ S) (hvS : v ∉ S)
    (hodd : Odd S.card)
    (hcut : ∀ x ∈ S, ∀ y ∈ Finset.univ \ S,
      (x ≠ u ∨ y ≠ v) → ∀ a b : Fin 3, W s((x, a), (y, b)) = 0)
    (c : V → Fin 3) :
    amplitude W c = W s((u, c u), (v, c v)) *
      pmSum W c ((Finset.univ.erase u).erase v) := by
  classical
  rw [← pmSum_univ, pmSum_expand W c (Finset.mem_univ u)]
  apply Finset.sum_eq_single_of_mem v
  · exact Finset.mem_erase.mpr ⟨fun h => hvS (h ▸ huS), Finset.mem_univ v⟩
  · intro y hy hyv
    have hyu : y ≠ u := (Finset.mem_erase.mp hy).1
    by_cases hyS : y ∈ S
    · let A := (S.erase u).erase y
      let T := (Finset.univ.erase u).erase y
      have hsub : A ⊆ T := by
        intro z hz
        simp only [A, T, Finset.mem_erase, Finset.mem_univ, and_true] at hz ⊢
        exact ⟨hz.1, hz.2.1⟩
      have hoddA : Odd A.card := by
        dsimp only [A]
        rw [Finset.card_erase_of_mem
          (Finset.mem_erase.mpr ⟨hyu, hyS⟩),
          Finset.card_erase_of_mem huS]
        rw [odd_iff_exists_bit1] at hodd ⊢
        obtain ⟨m, hm⟩ := hodd
        have hcard2 : 1 < S.card :=
          Finset.one_lt_card.mpr ⟨u, huS, y, hyS, Ne.symm hyu⟩
        have hmpos : 1 ≤ m := by omega
        refine ⟨m - 1, ?_⟩
        omega
      have hcutA : ∀ x ∈ A, ∀ z ∈ T \ A,
          W s((x, c x), (z, c z)) = 0 := by
        intro x hx z hz
        have hx' : x ∈ (S.erase u).erase y := by simpa only [A] using hx
        have hxu : x ≠ u := by
          exact (Finset.mem_erase.mp (Finset.mem_of_mem_erase hx')).1
        have hxS : x ∈ S := by
          exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx')
        have hznotS : z ∉ S := by
          intro hzS
          have hzT : z ∈ (Finset.univ.erase u).erase y := by
            simpa only [T] using (Finset.mem_sdiff.mp hz).1
          have hzu : z ≠ u := by
            exact (Finset.mem_erase.mp (Finset.mem_of_mem_erase hzT)).1
          have hzy : z ≠ y := (Finset.mem_erase.mp hzT).1
          exact (Finset.mem_sdiff.mp hz).2
            (by exact Finset.mem_erase.mpr ⟨hzy, Finset.mem_erase.mpr ⟨hzu, hzS⟩⟩)
        exact hcut x hxS z (Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hznotS⟩)
          (Or.inl hxu) _ _
      have hsplit := Separation.pmSum_split W c A.card A T rfl hsub hcutA
      have hzeroA : pmSum W c A = 0 :=
        pmSum_of_odd W c (Nat.not_even_iff_odd.mpr hoddA)
      rw [show (Finset.univ.erase u).erase y = T from rfl, hsplit, hzeroA,
        zero_mul, mul_zero]
    · have hedge : W (Sym2.map (paint c) s(u, y)) = 0 := by
        rw [Sym2.map_mk]
        exact hcut u huS y (Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hyS⟩)
          (Or.inr hyv) _ _
      rw [hedge, zero_mul]

/-- A support-minimal GHZ system has no bridge: a cut cannot have a single
live crossing pair.  Minimality says that pair participates, which forces the
cut to be odd.  Then every perfect matching uses the pair; the three nonzero
monochromatic amplitudes demand three diagonal colours on it, while any one
participating complementary colouring permits only one. -/
theorem no_unique_crossing_of_supportMinimal {W : Sym2 (V × Fin 3) → ℂ}
    (hmin : IsSupportMinimal W) (hcard : 2 < Fintype.card V)
    (S : Finset V) {u v : V} (huS : u ∈ S) (hvS : v ∉ S)
    (hcut : ∀ x ∈ S, ∀ y ∈ Finset.univ \ S,
      (x ≠ u ∨ y ≠ v) → ∀ a b : Fin 3, W s((x, a), (y, b)) = 0)
    (hlive : ∃ a b : Fin 3, W s((u, a), (v, b)) ≠ 0) : False := by
  classical
  have hvu : v ≠ u := fun h => hvS (h ▸ huS)
  have hnotinert : ¬ Inert W u v :=
    not_inert_of_supportMinimal hmin hvu hlive
  obtain ⟨c, hc⟩ : ∃ c : V → Fin 3,
      pmSum W c ((Finset.univ.erase u).erase v) ≠ 0 := by
    by_contra h
    push Not at h
    exact hnotinert h
  let A := S.erase u
  let T := (Finset.univ.erase u).erase v
  have hsub : A ⊆ T := by
    intro x hx
    have hx' : x ∈ S.erase u := by simpa only [A] using hx
    have hxu : x ≠ u := (Finset.mem_erase.mp hx').1
    have hxS : x ∈ S := Finset.mem_of_mem_erase hx'
    exact Finset.mem_erase.mpr
      ⟨fun h => hvS (h ▸ hxS), Finset.mem_erase.mpr ⟨hxu, Finset.mem_univ x⟩⟩
  have hcutA : ∀ x ∈ A, ∀ z ∈ T \ A,
      W s((x, c x), (z, c z)) = 0 := by
    intro x hx z hz
    have hx' : x ∈ S.erase u := by simpa only [A] using hx
    have hxu : x ≠ u := (Finset.mem_erase.mp hx').1
    have hxS : x ∈ S := Finset.mem_of_mem_erase hx'
    have hznotS : z ∉ S := by
      intro hzS
      have hzT : z ∈ (Finset.univ.erase u).erase v := by
        simpa only [T] using (Finset.mem_sdiff.mp hz).1
      have hzu : z ≠ u :=
        (Finset.mem_erase.mp (Finset.mem_of_mem_erase hzT)).1
      exact (Finset.mem_sdiff.mp hz).2
        (by exact Finset.mem_erase.mpr ⟨hzu, hzS⟩)
    exact hcut x hxS z (Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hznotS⟩)
      (Or.inl hxu) _ _
  have hsplit := Separation.pmSum_split W c A.card A T rfl hsub hcutA
  have hevenA : Even A.card := by
    by_contra hoddA
    have hzeroA : pmSum W c A = 0 := pmSum_of_odd W c hoddA
    exact hc (by rw [show (Finset.univ.erase u).erase v = T from rfl,
      hsplit, hzeroA, zero_mul])
  have hoddS : Odd S.card := by
    rw [even_iff_exists_two_mul] at hevenA
    rw [odd_iff_exists_bit1]
    obtain ⟨m, hm⟩ := hevenA
    refine ⟨m, ?_⟩
    have hcardA : A.card = S.card - 1 := by
      simpa only [A] using Finset.card_erase_of_mem huS
    calc
      S.card = (S.card - 1) + 1 := (Nat.sub_add_cancel (Finset.card_pos.mpr ⟨u, huS⟩)).symm
      _ = A.card + 1 := by rw [hcardA]
      _ = 2 * m + 1 := by rw [hm]
  have hfactor := amplitude_eq_of_unique_crossing W S huS hvS hoddS hcut
  have hTne : T.Nonempty := by
    rw [← Finset.card_pos]
    dsimp only [T]
    rw [Finset.card_erase_of_mem
      (Finset.mem_erase.mpr ⟨hvu, Finset.mem_univ v⟩),
      Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ,
      Nat.sub_sub]
    exact Nat.sub_pos_of_lt hcard
  obtain ⟨z, hzT⟩ := hTne
  obtain ⟨a₀, b₀, hab₀⟩ := hlive
  let d₀ : V → Fin 3 := Function.update (Function.update c u a₀) v b₀
  have hd₀rest : pmSum W d₀ T = pmSum W c T := by
    apply pmSum_congr_colour W
    intro x hx
    have hxv : x ≠ v := (Finset.mem_erase.mp hx).1
    have hxu : x ≠ u :=
      (Finset.mem_erase.mp (Finset.mem_of_mem_erase hx)).1
    simp [d₀, hxu, hxv]
  have hd₀u : d₀ u = a₀ := by simp [d₀, Ne.symm hvu]
  have hd₀v : d₀ v = b₀ := by simp [d₀]
  have hamp₀ : amplitude W d₀ ≠ 0 := by
    rw [hfactor d₀, hd₀u, hd₀v, show ((Finset.univ.erase u).erase v) = T from rfl,
      hd₀rest]
    exact mul_ne_zero hab₀ hc
  have hmono₀ : Amplitude.Monochromatic d₀ := by
    by_contra hnm
    exact hamp₀ (hmin.1.2 d₀ hnm)
  obtain ⟨k₀, hk₀⟩ := hmono₀
  obtain ⟨j, hja⟩ : ∃ j : Fin 3, j ≠ a₀ := exists_ne a₀
  have hedgej : W s((u, j), (v, j)) ≠ 0 := by
    intro hzeroj
    have hj := hmin.1.1 j
    rw [hfactor (Amplitude.const (V := V) j)] at hj
    simp [Amplitude.const, hzeroj] at hj
  let dj : V → Fin 3 := Function.update (Function.update c u j) v j
  have hdjrest : pmSum W dj T = pmSum W c T := by
    apply pmSum_congr_colour W
    intro x hx
    have hxv : x ≠ v := (Finset.mem_erase.mp hx).1
    have hxu : x ≠ u :=
      (Finset.mem_erase.mp (Finset.mem_of_mem_erase hx)).1
    simp [dj, hxu, hxv]
  have hdju : dj u = j := by simp [dj, Ne.symm hvu]
  have hdjv : dj v = j := by simp [dj]
  have hampj : amplitude W dj ≠ 0 := by
    rw [hfactor dj, hdju, hdjv, show ((Finset.univ.erase u).erase v) = T from rfl,
      hdjrest]
    exact mul_ne_zero hedgej hc
  have hmonoj : Amplitude.Monochromatic dj := by
    by_contra hnm
    exact hampj (hmin.1.2 dj hnm)
  obtain ⟨kj, hkj⟩ := hmonoj
  have hzu : z ≠ u :=
    (Finset.mem_erase.mp (Finset.mem_of_mem_erase hzT)).1
  have hzv : z ≠ v := (Finset.mem_erase.mp hzT).1
  have hk_eq : k₀ = kj := by
    rw [← hk₀ z, ← hkj z]
    simp [d₀, dj, hzu, hzv]
  have ha₀ : a₀ = k₀ := by
    rw [← hk₀ u, hd₀u]
  have hjk : j = kj := by
    rw [← hkj u, hdju]
  exact hja (ha₀.trans (hk_eq.trans hjk.symm)).symm


/-! ### The corrected conditional target -/

/-- It is enough to prove the degree bound for support-minimal solutions.
Unlike a bound over every presentation, this carries the indispensable fact that
each live pair actually participates in an amplitude. -/
def MinimalLiveDegreeThree : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V]
    (W : Sym2 (V × Fin 3) → ℂ),
    4 < Fintype.card V → IsSupportMinimal W →
      ∀ u : V, (liveNbrs W u).card ≤ 3

/-- The full Krenn--Gu conjecture follows from the degree bound only on
support-minimal representatives. -/
theorem krenn_gu_of_minimalLiveDegree (h : MinimalLiveDegreeThree) :
    ∀ n : ℕ, 3 ≤ n → ¬ KrennGu.Solvable n := by
  rintro n h3 ⟨W, hW⟩
  obtain ⟨W', hmin, _⟩ := exists_supportMinimal W hW
  have hcard : 4 < Fintype.card (Fin (2 * n)) := by
    rw [Fintype.card_fin]
    omega
  have hdeg : ∀ u : Fin (2 * n), (liveNbrs W' u).card ≤ 3 :=
    h (Fin (2 * n)) W' hcard hmin
  have hone' : ∀ j : Fin 3,
      amplitude (deloop W') (Amplitude.const (V := Fin (2 * n)) j) ≠ 0 := by
    intro j
    rw [amplitude_deloop]
    exact hmin.1.1 j
  have hzero' : ∀ c : Fin (2 * n) → Fin 3, ¬ Amplitude.Monochromatic c →
      amplitude (deloop W') c = 0 := by
    intro c hc
    rw [amplitude_deloop]
    exact hmin.1.2 c hc
  have hdeg' : ∀ u : Fin (2 * n), (liveNbrs (deloop W') u).card ≤ 3 := by
    intro u
    rw [liveNbrs_deloop]
    exact hdeg u
  obtain ⟨T⟩ := threeRegular_of_liveDegree (deloop W') hone' hzero' hcard
    (fun x a b => deloop_loop W' x a b) hdeg'
  have hV : ∀ x : Fin (2 * n), (Finset.univ.erase x).Nonempty := by
    intro x
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ x)]
    have : (Finset.univ : Finset (Fin (2 * n))).card = Fintype.card (Fin (2 * n)) := rfl
    omega
  exact CycleCoordinates.no_three_regular_uniform _ hone' hzero' hV hcard T

end MinimalSupport

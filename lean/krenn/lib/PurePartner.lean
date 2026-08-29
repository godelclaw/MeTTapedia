import Mathlib
import Amplitude
import MatchingSum
import Mettapedia.Combinatorics.Matching.FourthMatching

/-!
# A pure partner at every site and every colour

The results here need no hypothesis beyond the defining equations.  They come from
testing the equations against a *separate* vector at each site, rather than against a
colouring.

Fix a site `u` and a colour `α`.  Weight each colouring by an indicator that pins `u` to
`α` and by one test vector per remaining site, and sum.  Read directly, the defining
equations collapse the sum to a single term: only the constant colouring `α` survives,
and the answer is its amplitude times the test vectors evaluated at `α`.  Read through
the expansion along `u`, the sum splits into one term per partner, and the colour at
that partner is summed against its own test vector alone --- so a test vector
annihilating the partner's row kills its term outright.

Choosing an annihilating test vector at *every* partner would therefore make a non-zero
product vanish.  It follows that some partner admits no annihilator with a non-zero
`α`-component, and for a vector in three-space that means its row is a non-zero multiple
of the `α`-th basis vector.

The conclusion is that at every site and in every colour there is a partner joined by an
edge which, read from that site in that colour, carries no other colour at all.  The
four-vertex solution displays this, and it is the reason its three matchings can wear
three colours.
-/

namespace PurePartner

open Amplitude MatchingSum MixedColouring

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The colourings weighted by an indicator at `u` and one test vector per other site. -/
noncomputable def testSum (W : Sym2 (V × Fin 3) → ℂ) (u : V) (α : Fin 3)
    (ψ : V → Fin 3 → ℂ) : ℂ :=
  ∑ c : V → Fin 3, amplitude W c * (if c u = α then 1 else 0) *
    ∏ w ∈ Finset.univ.erase u, ψ w (c w)

/-- **Read through the equations.**  Every non-constant colouring has zero amplitude and
every constant colouring but one is refused by the indicator, so one term survives. -/
theorem testSum_eq (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (u : V) (α : Fin 3) (ψ : V → Fin 3 → ℂ) :
    testSum W u α ψ
      = amplitude W (Amplitude.const α) * ∏ w ∈ Finset.univ.erase u, ψ w α := by
  classical
  rw [testSum, Finset.sum_eq_single (Amplitude.const (V := V) α)]
  · simp [Amplitude.const]
  · intro c _ hc
    rcases Classical.em (Amplitude.Monochromatic c) with ⟨k, hk⟩ | hmono
    · have : c u ≠ α := by
        intro h
        exact hc (funext fun w => by rw [hk w, ← hk u, h]; rfl)
      simp [this]
    · rw [hzero c hmono]; ring
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Read through the expansion.**  Splitting the colouring at a partner factors its
colour out of the sum, so an annihilating test vector there kills the whole term. -/
theorem testSum_expand (W : Sym2 (V × Fin 3) → ℂ) (u : V) (α : Fin 3) (ψ : V → Fin 3 → ℂ)
    (hann : ∀ v ∈ Finset.univ.erase u, (∑ b : Fin 3, ψ v b * W s((u, α), (v, b))) = 0) :
    testSum W u α ψ = 0 := by
  classical
  have hexp : ∀ c : V → Fin 3, amplitude W c
      = ∑ v ∈ Finset.univ.erase u,
          W s((u, c u), (v, c v)) * pmSum W c ((Finset.univ.erase u).erase v) := by
    intro c
    rw [← pmSum_univ, pmSum_expand W c (Finset.mem_univ u)]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    first
    | rfl
    | (congr 1; simp [Sym2.map_pair_eq, paint])
  have key : ∀ c : V → Fin 3,
      amplitude W c * (if c u = α then 1 else 0) * ∏ w ∈ Finset.univ.erase u, ψ w (c w)
        = ∑ v ∈ Finset.univ.erase u,
            W s((u, c u), (v, c v)) * pmSum W c ((Finset.univ.erase u).erase v)
              * (if c u = α then 1 else 0) * ∏ w ∈ Finset.univ.erase u, ψ w (c w) := by
    intro c
    rw [hexp c, Finset.sum_mul, Finset.sum_mul]
  rw [testSum, Finset.sum_congr rfl (fun c _ => key c), Finset.sum_comm]
  refine Finset.sum_eq_zero (fun v hv => ?_)
  have hvu : v ≠ u := (Finset.mem_erase.mp hv).1
  have hu' : u ≠ v := Ne.symm hvu
  set e := Equiv.funSplitAt v (Fin 3) with he
  have hsplit : ∀ F : (V → Fin 3) → ℂ,
      (∑ c : V → Fin 3, F c)
        = ∑ b : Fin 3, ∑ d : {w : V // w ≠ v} → Fin 3, F (e.symm (b, d)) := by
    intro F
    calc (∑ c : V → Fin 3, F c)
        = ∑ p : Fin 3 × ({w : V // w ≠ v} → Fin 3), F (e.symm p) :=
          Fintype.sum_equiv e (fun c => F c) (fun p => F (e.symm p))
            (fun c => (congrArg F (Equiv.symm_apply_apply e c)).symm)
      _ = ∑ b : Fin 3, ∑ d : {w : V // w ≠ v} → Fin 3, F (e.symm (b, d)) :=
          Fintype.sum_prod_type _
  rw [hsplit, Finset.sum_comm]
  refine Finset.sum_eq_zero (fun d _ => ?_)
  -- the colour at `u` is read off the restricted colouring, so it does not move with `b`
  have hval : ∀ b : Fin 3, ∀ w : V, ∀ h : w ≠ v, (e.symm (b, d)) w = d ⟨w, h⟩ := by
    intro b w h; simp [he, Equiv.funSplitAt_symm_apply, h]
  have hvv : ∀ b : Fin 3, (e.symm (b, d)) v = b := by
    intro b; simp [he, Equiv.funSplitAt_symm_apply]
  by_cases hdu : d ⟨u, hu'⟩ = α
  · -- factor the partner's colour out and apply the annihilation
    have hrest : ∀ b : Fin 3,
        W s((u, (e.symm (b, d)) u), (v, (e.symm (b, d)) v))
            * pmSum W (e.symm (b, d)) ((Finset.univ.erase u).erase v)
            * (if (e.symm (b, d)) u = α then 1 else 0)
            * ∏ w ∈ Finset.univ.erase u, ψ w ((e.symm (b, d)) w)
          = (pmSum W (e.symm (α, d)) ((Finset.univ.erase u).erase v)
              * ∏ w ∈ (Finset.univ.erase u).erase v, ψ w ((e.symm (α, d)) w))
              * (ψ v b * W s((u, α), (v, b))) := by
      intro b
      have h1 : (e.symm (b, d)) u = α := by rw [hval b u hu', hdu]
      have h2 : pmSum W (e.symm (b, d)) ((Finset.univ.erase u).erase v)
          = pmSum W (e.symm (α, d)) ((Finset.univ.erase u).erase v) := by
        refine pmSum_congr_colour W (fun w hw => ?_)
        have : w ≠ v := (Finset.mem_erase.mp hw).1
        rw [hval b w this, hval α w this]
      have h3 : ∏ w ∈ Finset.univ.erase u, ψ w ((e.symm (b, d)) w)
          = ψ v b * ∏ w ∈ (Finset.univ.erase u).erase v, ψ w ((e.symm (α, d)) w) := by
        rw [← Finset.mul_prod_erase _ _ hv, hvv b]
        congr 1
        refine Finset.prod_congr rfl (fun w hw => ?_)
        have : w ≠ v := (Finset.mem_erase.mp hw).1
        rw [hval b w this, hval α w this]
      rw [h1, h2, h3, hvv b]
      first
      | (simp only [if_true]; ring)
      | (simp only [if_pos trivial]; ring)
      | simp
    rw [Finset.sum_congr rfl (fun b _ => hrest b), ← Finset.mul_sum, hann v hv, mul_zero]
  · -- the indicator refuses every term
    refine Finset.sum_eq_zero (fun b _ => ?_)
    have : (e.symm (b, d)) u ≠ α := by rw [hval b u hu']; exact hdu
    simp [this]

/-- **A pure partner.**  At every site and in every colour some partner is joined by an
edge which, read from that site in that colour, carries that colour and nothing else. -/
theorem exists_pure_partner (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const (V := V) k) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (u : V) (α : Fin 3) :
    ∃ v ∈ Finset.univ.erase u,
      (∀ b : Fin 3, b ≠ α → W s((u, α), (v, b)) = 0) ∧ W s((u, α), (v, α)) ≠ 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  -- at every partner choose a test vector annihilating the row, with non-zero α-component
  have hchoice : ∀ v : V, ∃ ψv : Fin 3 → ℂ, ψv α ≠ 0 ∧
      (v ∈ Finset.univ.erase u → (∑ b : Fin 3, ψv b * W s((u, α), (v, b))) = 0) := by
    intro v
    by_cases hv : v ∈ Finset.univ.erase u
    · by_cases hA : W s((u, α), (v, α)) = 0
      · refine ⟨fun b => if b = α then 1 else 0, by simp, fun _ => ?_⟩
        rw [Finset.sum_eq_single_of_mem α (Finset.mem_univ α)
          (fun b _ hb => by simp [hb])]
        simp [hA]
      · obtain ⟨b₀, hb₀, hne⟩ : ∃ b : Fin 3, b ≠ α ∧ W s((u, α), (v, b)) ≠ 0 := by
          by_contra hall
          push_neg at hall
          exact hA (hcon v hv hall)
        refine ⟨fun b => if b = α then W s((u, α), (v, b₀))
            else if b = b₀ then -W s((u, α), (v, α)) else 0, by simpa using hne, fun _ => ?_⟩
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ α),
          Finset.sum_eq_single_of_mem b₀
            (Finset.mem_erase.mpr ⟨hb₀, Finset.mem_univ _⟩)
            (fun b hb hbne => by
              have hba : b ≠ α := (Finset.mem_erase.mp hb).1
              simp [hba, hbne])]
        first
        | (simp [hb₀]; ring)
        | simp [hb₀, mul_comm]
    · exact ⟨fun b => if b = α then 1 else 0, by simp, fun h => absurd h hv⟩
  choose ψ hψα hψ0 using hchoice
  have h0 : testSum W u α ψ = 0 := testSum_expand W u α ψ (fun v hv => hψ0 v hv)
  rw [testSum_eq W hzero u α ψ] at h0
  rcases mul_eq_zero.mp h0 with h | h
  · exact hone α h
  · exact (Finset.prod_ne_zero_iff.mpr (fun w _ => hψα w)) h


/-- **An off-diagonal entry is paid for by a matching sum.**

Suppose that at every site other than `u` and `z` the `α`-row read from `u` has a zero
entry.  Colour those sites there, colour `u` with `α` and `z` with a different colour.
The colouring is non-constant, so its amplitude vanishes; and in the expansion along `u`
every partner but `z` meets one of the zeros chosen for it.  One product survives.

No test vectors are needed here --- one colouring does the work --- and no hypothesis
beyond the equations. -/
theorem offdiag_mul_pmSum (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {u z : V} (hz : z ≠ u) {α β : Fin 3} (hαβ : β ≠ α) (b : V → Fin 3)
    (hb : ∀ w ∈ (Finset.univ.erase u).erase z, W s((u, α), (w, b w)) = 0) :
    W s((u, α), (z, β)) * pmSum W b ((Finset.univ.erase u).erase z) = 0 := by
  classical
  set c : V → Fin 3 := Function.update (Function.update b u α) z β with hc
  have hcu : c u = α := by simp [hc, Function.update_apply, Ne.symm hz]
  have hcz : c z = β := by simp [hc]
  have hcw : ∀ w : V, w ≠ u → w ≠ z → c w = b w := by
    intro w h1 h2; simp [hc, Function.update_apply, h1, h2]
  have hnm : ¬ Amplitude.Monochromatic c := by
    rintro ⟨k, hk⟩
    have h1 : α = k := by rw [← hcu, hk u]
    have h2 : β = k := by rw [← hcz, hk z]
    exact hαβ (h2.trans h1.symm)
  have hamp : amplitude W c = 0 := hzero c hnm
  rw [← pmSum_univ, pmSum_expand W c (Finset.mem_univ u),
    Finset.sum_eq_single_of_mem z (Finset.mem_erase.mpr ⟨hz, Finset.mem_univ z⟩)
      (fun v hv hvz => by
        have hvu : v ≠ u := (Finset.mem_erase.mp hv).1
        have hW : W (Sym2.map (paint c) s(u, v)) = 0 := by
          rw [show Sym2.map (paint c) s(u, v) = s((u, c u), (v, c v)) from rfl, hcu,
            hcw v hvu hvz]
          exact hb v (Finset.mem_erase.mpr
            ⟨hvz, Finset.mem_erase.mpr ⟨hvu, Finset.mem_univ v⟩⟩)
        rw [hW, zero_mul])] at hamp
  rw [show Sym2.map (paint c) s(u, z) = s((u, c u), (z, c z)) from rfl, hcu, hcz] at hamp
  rw [show pmSum W b ((Finset.univ.erase u).erase z)
        = pmSum W c ((Finset.univ.erase u).erase z) from
      pmSum_congr_colour W (fun w hw =>
        (hcw w (Finset.mem_erase.mp (Finset.mem_of_mem_erase hw)).1
          (Finset.mem_erase.mp hw).1).symm)]
  exact hamp

/-- If the matching sum on the complement survives, the off-diagonal entry itself
vanishes: the `α`-row read from `u` toward `z` carries no other colour. -/
theorem offdiag_eq_zero (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {u z : V} (hz : z ≠ u) {α β : Fin 3} (hαβ : β ≠ α) (b : V → Fin 3)
    (hb : ∀ w ∈ (Finset.univ.erase u).erase z, W s((u, α), (w, b w)) = 0)
    (hne : pmSum W b ((Finset.univ.erase u).erase z) ≠ 0) :
    W s((u, α), (z, β)) = 0 :=
  (mul_eq_zero.mp (offdiag_mul_pmSum W hzero hz hαβ b hb)).resolve_right hne

/-- The constant-colouring form: when one colour is missing from the `α`-row everywhere
but at `z`, the complementary constant matching sum multiplies the entry to zero. -/
theorem offdiag_mul_const (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {u z : V} (hz : z ≠ u) {α β γ : Fin 3} (hαβ : β ≠ α)
    (hcol : ∀ w ∈ (Finset.univ.erase u).erase z, W s((u, α), (w, γ)) = 0) :
    W s((u, α), (z, β))
        * pmSum W (Amplitude.const γ) ((Finset.univ.erase u).erase z) = 0 :=
  offdiag_mul_pmSum W hzero hz hαβ (Amplitude.const γ) hcol


/-! ## Isolating a single pairing

Annihilating test vectors kill every matching that touches a site.  Pinning *two* sites
and annihilating at one of them kills every matching except those that pair the two
together --- and those all carry the same block entry.  What survives is a single
product, which no other matching is present to cancel.
-/

/-- **Splitting a sum over colourings at one site.**  When the summand factors into a
weight on the colour worn at that site and a factor blind to it, a cancelling weight
annihilates the whole sum.  This is the mechanism behind every isolation argument here,
and it is stated once so that both of them can use it. -/
theorem sum_colourings_eq_zero (v : V) (g : Fin 3 → ℂ) (H : (V → Fin 3) → ℂ)
    (hH : ∀ (c : V → Fin 3) (b : Fin 3), H (Function.update c v b) = H c)
    (hg : (∑ b : Fin 3, g b) = 0) :
    (∑ c : V → Fin 3, g (c v) * H c) = 0 := by
  classical
  set e := Equiv.funSplitAt v (Fin 3) with he
  have hsplit : ∀ F : (V → Fin 3) → ℂ,
      (∑ c : V → Fin 3, F c)
        = ∑ b : Fin 3, ∑ d : {w : V // w ≠ v} → Fin 3, F (e.symm (b, d)) := by
    intro F
    calc (∑ c : V → Fin 3, F c)
        = ∑ p : Fin 3 × ({w : V // w ≠ v} → Fin 3), F (e.symm p) :=
          Fintype.sum_equiv e (fun c => F c) (fun p => F (e.symm p))
            (fun c => (congrArg F (Equiv.symm_apply_apply e c)).symm)
      _ = ∑ b : Fin 3, ∑ d : {w : V // w ≠ v} → Fin 3, F (e.symm (b, d)) :=
          Fintype.sum_prod_type _
  have hkey : ∀ (b : Fin 3) (d : {w : V // w ≠ v} → Fin 3),
      g ((e.symm (b, d)) v) * H (e.symm (b, d)) = g b * H (e.symm (0, d)) := by
    intro b d
    have h1 : (e.symm (b, d)) v = b := by simp [he, Equiv.funSplitAt_symm_apply]
    have h2 : e.symm (b, d) = Function.update (e.symm (0, d)) v b := by
      funext w
      by_cases hw : w = v
      · subst hw; simp [he, Equiv.funSplitAt_symm_apply]
      · simp [he, Equiv.funSplitAt_symm_apply, hw]
    rw [h1, h2, hH]
  rw [hsplit, Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun d _ => hkey b d))]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, hg, zero_mul]


/-- Colourings weighted by indicators at two sites and by test vectors elsewhere. -/
noncomputable def pairSum (W : Sym2 (V × Fin 3) → ℂ) (u₁ u₂ : V) (α β : Fin 3)
    (ψ : V → Fin 3 → ℂ) : ℂ :=
  ∑ c : V → Fin 3, amplitude W c * (if c u₁ = α then 1 else 0)
    * (if c u₂ = β then 1 else 0)
    * ∏ w ∈ (Finset.univ.erase u₁).erase u₂, ψ w (c w)

/-- The matching sums of the complement, weighted the same way. -/
noncomputable def pairK (W : Sym2 (V × Fin 3) → ℂ) (u₁ u₂ : V) (α β : Fin 3)
    (ψ : V → Fin 3 → ℂ) : ℂ :=
  ∑ c : V → Fin 3, (if c u₁ = α then 1 else 0) * (if c u₂ = β then 1 else 0)
    * pmSum W c ((Finset.univ.erase u₁).erase u₂)
    * ∏ w ∈ (Finset.univ.erase u₁).erase u₂, ψ w (c w)

/-- Two sites pinned to different colours admit no constant colouring at all. -/
theorem pairSum_of_ne (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (u₁ u₂ : V) {α β : Fin 3} (hαβ : α ≠ β) (ψ : V → Fin 3 → ℂ) :
    pairSum W u₁ u₂ α β ψ = 0 := by
  classical
  refine Finset.sum_eq_zero (fun c _ => ?_)
  rcases Classical.em (Amplitude.Monochromatic c) with ⟨k, hk⟩ | hmono
  · by_cases hka : k = α
    · have : c u₂ ≠ β := by rw [hk u₂, hka]; exact hαβ
      simp [this]
    · have : c u₁ ≠ α := by rw [hk u₁]; exact hka
      simp [this]
  · rw [hzero c hmono]; ring

/-- Two sites pinned to the same colour leave exactly the constant colouring. -/
theorem pairSum_of_eq (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (u₁ u₂ : V) (α : Fin 3) (ψ : V → Fin 3 → ℂ) :
    pairSum W u₁ u₂ α α ψ
      = amplitude W (Amplitude.const α)
        * ∏ w ∈ (Finset.univ.erase u₁).erase u₂, ψ w α := by
  classical
  rw [pairSum, Finset.sum_eq_single (Amplitude.const (V := V) α)]
  · simp [Amplitude.const]
  · intro c _ hc
    rcases Classical.em (Amplitude.Monochromatic c) with ⟨k, hk⟩ | hmono
    · have : c u₁ ≠ α := by
        intro h
        exact hc (funext fun w => by rw [hk w, ← hk u₁, h]; rfl)
      simp [this]
    · rw [hzero c hmono]; ring
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Isolation of a single pairing.**  Annihilating the `α`-row of the first pinned
site at every unpinned site kills every matching that does not join the two pinned sites
to each other.  The matchings that do all carry the same block entry, so it factors out
--- and nothing remains that could cancel it. -/
theorem pairSum_expand (W : Sym2 (V × Fin 3) → ℂ) {u₁ u₂ : V} (h12 : u₂ ≠ u₁)
    (α β : Fin 3) (ψ : V → Fin 3 → ℂ)
    (hann : ∀ w ∈ (Finset.univ.erase u₁).erase u₂,
      (∑ b : Fin 3, ψ w b * W s((u₁, α), (w, b))) = 0) :
    pairSum W u₁ u₂ α β ψ = W s((u₁, α), (u₂, β)) * pairK W u₁ u₂ α β ψ := by
  classical
  have hexp : ∀ c : V → Fin 3, amplitude W c
      = ∑ v ∈ Finset.univ.erase u₁,
          W s((u₁, c u₁), (v, c v)) * pmSum W c ((Finset.univ.erase u₁).erase v) := by
    intro c
    rw [← pmSum_univ, pmSum_expand W c (Finset.mem_univ u₁)]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    first
    | rfl
    | (congr 1; simp [Sym2.map_pair_eq, paint])
  have key : ∀ c : V → Fin 3,
      amplitude W c * (if c u₁ = α then 1 else 0) * (if c u₂ = β then 1 else 0)
          * ∏ w ∈ (Finset.univ.erase u₁).erase u₂, ψ w (c w)
        = ∑ v ∈ Finset.univ.erase u₁,
            W s((u₁, c u₁), (v, c v)) * pmSum W c ((Finset.univ.erase u₁).erase v)
              * (if c u₁ = α then 1 else 0) * (if c u₂ = β then 1 else 0)
              * ∏ w ∈ (Finset.univ.erase u₁).erase u₂, ψ w (c w) := by
    intro c
    rw [hexp c, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  rw [pairSum, Finset.sum_congr rfl (fun c _ => key c), Finset.sum_comm,
    Finset.sum_eq_single_of_mem u₂ (Finset.mem_erase.mpr ⟨h12, Finset.mem_univ u₂⟩) ?_]
  · rw [pairK, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    by_cases h1 : c u₁ = α
    · by_cases h2 : c u₂ = β
      · rw [h1, h2]; ring
      · simp [h2]
    · simp [h1]
  · -- every other partner is annihilated
    intro v hv hvu₂
    have hvu₁ : v ≠ u₁ := (Finset.mem_erase.mp hv).1
    have hvS : v ∈ (Finset.univ.erase u₁).erase u₂ :=
      Finset.mem_erase.mpr ⟨hvu₂, Finset.mem_erase.mpr ⟨hvu₁, Finset.mem_univ v⟩⟩
    have hrw : ∀ c : V → Fin 3,
        W s((u₁, c u₁), (v, c v)) * pmSum W c ((Finset.univ.erase u₁).erase v)
            * (if c u₁ = α then 1 else 0) * (if c u₂ = β then 1 else 0)
            * ∏ w ∈ (Finset.univ.erase u₁).erase u₂, ψ w (c w)
          = (ψ v (c v) * W s((u₁, α), (v, c v)))
            * (pmSum W c ((Finset.univ.erase u₁).erase v)
                * (if c u₁ = α then 1 else 0) * (if c u₂ = β then 1 else 0)
                * ∏ w ∈ ((Finset.univ.erase u₁).erase u₂).erase v, ψ w (c w)) := by
      intro c
      rw [← Finset.mul_prod_erase _ _ hvS]
      by_cases h1 : c u₁ = α
      · rw [h1]; ring
      · simp [h1]
    rw [Finset.sum_congr rfl (fun c _ => hrw c)]
    refine sum_colourings_eq_zero v (fun b => ψ v b * W s((u₁, α), (v, b))) _ ?_ (hann v hvS)
    intro c b
    have e1 : (Function.update c v b) u₁ = c u₁ := Function.update_of_ne hvu₁.symm _ _
    have e2 : (Function.update c v b) u₂ = c u₂ := Function.update_of_ne (Ne.symm hvu₂) _ _
    have e3 : pmSum W (Function.update c v b) ((Finset.univ.erase u₁).erase v)
        = pmSum W c ((Finset.univ.erase u₁).erase v) := by
      refine pmSum_congr_colour W (fun w hw => ?_)
      exact Function.update_of_ne (Finset.mem_erase.mp hw).1 _ _
    have e4 : ∏ w ∈ ((Finset.univ.erase u₁).erase u₂).erase v,
          ψ w ((Function.update c v b) w)
        = ∏ w ∈ ((Finset.univ.erase u₁).erase u₂).erase v, ψ w (c w) := by
      refine Finset.prod_congr rfl (fun w hw => ?_)
      rw [Function.update_of_ne (Finset.mem_erase.mp hw).1]
    rw [e1, e2, e3, e4]


/-- **Factoring a sum over colourings at one site.**  When the summand factors into a
weight on the colour worn at a site and a factor blind to it, the sum is the product of
the total weight with the sum taken at any one fixed colour there. -/
theorem sum_colourings_factor (v : V) (g : Fin 3 → ℂ) (H : (V → Fin 3) → ℂ)
    (hH : ∀ (c : V → Fin 3) (b : Fin 3), H (Function.update c v b) = H c) (k : Fin 3) :
    (∑ c : V → Fin 3, g (c v) * H c)
      = (∑ b : Fin 3, g b) * (∑ c : V → Fin 3, (if c v = k then 1 else 0) * H c) := by
  classical
  set e := Equiv.funSplitAt v (Fin 3) with he
  have hsplit : ∀ F : (V → Fin 3) → ℂ,
      (∑ c : V → Fin 3, F c)
        = ∑ b : Fin 3, ∑ d : {w : V // w ≠ v} → Fin 3, F (e.symm (b, d)) := by
    intro F
    calc (∑ c : V → Fin 3, F c)
        = ∑ p : Fin 3 × ({w : V // w ≠ v} → Fin 3), F (e.symm p) :=
          Fintype.sum_equiv e (fun c => F c) (fun p => F (e.symm p))
            (fun c => (congrArg F (Equiv.symm_apply_apply e c)).symm)
      _ = ∑ b : Fin 3, ∑ d : {w : V // w ≠ v} → Fin 3, F (e.symm (b, d)) :=
          Fintype.sum_prod_type _
  have hval : ∀ (b : Fin 3) (d : {w : V // w ≠ v} → Fin 3), (e.symm (b, d)) v = b := by
    intro b d; simp [he, Equiv.funSplitAt_symm_apply]
  have hshift : ∀ (b : Fin 3) (d : {w : V // w ≠ v} → Fin 3),
      H (e.symm (b, d)) = H (e.symm (k, d)) := by
    intro b d
    have h2 : e.symm (b, d) = Function.update (e.symm (k, d)) v b := by
      funext w
      by_cases hw : w = v
      · subst hw; simp [he, Equiv.funSplitAt_symm_apply]
      · simp [he, Equiv.funSplitAt_symm_apply, hw]
    rw [h2, hH]
  rw [hsplit (fun c => g (c v) * H c), hsplit (fun c => (if c v = k then 1 else 0) * H c)]
  have hL : ∀ (b : Fin 3) (d : {w : V // w ≠ v} → Fin 3),
      g ((e.symm (b, d)) v) * H (e.symm (b, d)) = g b * H (e.symm (k, d)) := by
    intro b d; rw [hval b d, hshift b d]
  have hR : ∀ (b : Fin 3) (d : {w : V // w ≠ v} → Fin 3),
      (if (e.symm (b, d)) v = k then (1 : ℂ) else 0) * H (e.symm (b, d))
        = (if b = k then (1 : ℂ) else 0) * H (e.symm (k, d)) := by
    intro b d; rw [hval b d, hshift b d]
  rw [Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun d _ => hL b d)),
    Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun d _ => hR b d))]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  have hone : (∑ i : Fin 3, if i = k then (1 : ℂ) else 0) = 1 := by simp
  rw [hone, one_mul]


/-- **Isolation with one partner spared.**  Annihilating the row at every site but one
leaves exactly the matchings that join `u` to that one, and the colour worn there factors
out of the sum. -/
theorem testSum_expand_one (W : Sym2 (V × Fin 3) → ℂ) {u u₂ : V} (h12 : u₂ ≠ u)
    (α : Fin 3) (ψ : V → Fin 3 → ℂ)
    (hann : ∀ w ∈ (Finset.univ.erase u).erase u₂,
      (∑ b : Fin 3, ψ w b * W s((u, α), (w, b))) = 0) :
    testSum W u α ψ
      = (∑ b : Fin 3, ψ u₂ b * W s((u, α), (u₂, b))) * pairK W u u₂ α α ψ := by
  classical
  have hmem₂ : u₂ ∈ Finset.univ.erase u := Finset.mem_erase.mpr ⟨h12, Finset.mem_univ u₂⟩
  have hexp : ∀ c : V → Fin 3, amplitude W c
      = ∑ v ∈ Finset.univ.erase u,
          W s((u, c u), (v, c v)) * pmSum W c ((Finset.univ.erase u).erase v) := by
    intro c
    rw [← pmSum_univ, pmSum_expand W c (Finset.mem_univ u)]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    first
    | rfl
    | (congr 1; simp [Sym2.map_pair_eq, paint])
  have key : ∀ c : V → Fin 3,
      amplitude W c * (if c u = α then 1 else 0)
          * ∏ w ∈ Finset.univ.erase u, ψ w (c w)
        = ∑ v ∈ Finset.univ.erase u,
            W s((u, c u), (v, c v)) * pmSum W c ((Finset.univ.erase u).erase v)
              * (if c u = α then 1 else 0) * ∏ w ∈ Finset.univ.erase u, ψ w (c w) := by
    intro c
    rw [hexp c, Finset.sum_mul, Finset.sum_mul]
  rw [testSum, Finset.sum_congr rfl (fun c _ => key c), Finset.sum_comm,
    Finset.sum_eq_single_of_mem u₂ hmem₂ ?_]
  · -- the surviving partner: its colour factors out
    have hrw : ∀ c : V → Fin 3,
        W s((u, c u), (u₂, c u₂)) * pmSum W c ((Finset.univ.erase u).erase u₂)
            * (if c u = α then 1 else 0) * ∏ w ∈ Finset.univ.erase u, ψ w (c w)
          = (ψ u₂ (c u₂) * W s((u, α), (u₂, c u₂)))
            * (pmSum W c ((Finset.univ.erase u).erase u₂) * (if c u = α then 1 else 0)
                * ∏ w ∈ (Finset.univ.erase u).erase u₂, ψ w (c w)) := by
      intro c
      rw [← Finset.mul_prod_erase _ _ hmem₂]
      by_cases h1 : c u = α
      · rw [h1]; ring
      · simp [h1]
    rw [Finset.sum_congr rfl (fun c _ => hrw c),
      sum_colourings_factor u₂ (fun b => ψ u₂ b * W s((u, α), (u₂, b))) _ ?_ α]
    · rw [pairK]
      congr 1
      exact Finset.sum_congr rfl (fun c _ => by ring)
    · intro c b
      have e1 : (Function.update c u₂ b) u = c u := Function.update_of_ne (Ne.symm h12) _ _
      have e2 : pmSum W (Function.update c u₂ b) ((Finset.univ.erase u).erase u₂)
          = pmSum W c ((Finset.univ.erase u).erase u₂) :=
        pmSum_congr_colour W (fun w hw =>
          Function.update_of_ne (Finset.mem_erase.mp hw).1 _ _)
      have e3 : ∏ w ∈ (Finset.univ.erase u).erase u₂, ψ w ((Function.update c u₂ b) w)
          = ∏ w ∈ (Finset.univ.erase u).erase u₂, ψ w (c w) :=
        Finset.prod_congr rfl (fun w hw => by
          rw [Function.update_of_ne (Finset.mem_erase.mp hw).1])
      rw [e1, e2, e3]
  · -- every other partner is annihilated
    intro v hv hvu₂
    have hvu : v ≠ u := (Finset.mem_erase.mp hv).1
    have hvS : v ∈ (Finset.univ.erase u).erase u₂ :=
      Finset.mem_erase.mpr ⟨hvu₂, hv⟩
    have hrw : ∀ c : V → Fin 3,
        W s((u, c u), (v, c v)) * pmSum W c ((Finset.univ.erase u).erase v)
            * (if c u = α then 1 else 0) * ∏ w ∈ Finset.univ.erase u, ψ w (c w)
          = (ψ v (c v) * W s((u, α), (v, c v)))
            * (pmSum W c ((Finset.univ.erase u).erase v) * (if c u = α then 1 else 0)
                * ∏ w ∈ (Finset.univ.erase u).erase v, ψ w (c w)) := by
      intro c
      rw [← Finset.mul_prod_erase _ _ hv]
      by_cases h1 : c u = α
      · rw [h1]; ring
      · simp [h1]
    rw [Finset.sum_congr rfl (fun c _ => hrw c)]
    refine sum_colourings_eq_zero v (fun b => ψ v b * W s((u, α), (v, b))) _ ?_ (hann v hvS)
    intro c b
    have e1 : (Function.update c v b) u = c u := Function.update_of_ne (Ne.symm hvu) _ _
    have e2 : pmSum W (Function.update c v b) ((Finset.univ.erase u).erase v)
        = pmSum W c ((Finset.univ.erase u).erase v) :=
      pmSum_congr_colour W (fun w hw => Function.update_of_ne (Finset.mem_erase.mp hw).1 _ _)
    have e3 : ∏ w ∈ (Finset.univ.erase u).erase v, ψ w ((Function.update c v b) w)
        = ∏ w ∈ (Finset.univ.erase u).erase v, ψ w (c w) :=
      Finset.prod_congr rfl (fun w hw => by
        rw [Function.update_of_ne (Finset.mem_erase.mp hw).1])
    rw [e1, e2, e3]


/-- **The vector identity.**  With the `α`-row annihilated at every site but one, the two
readings of the weighted sum meet in a single scalar identity, linear in the covector
tested at the spared partner: on one side it meets that partner's row, on the other the
`α`-th basis vector. -/
theorem row_mul_pairK (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {u u₂ : V} (h12 : u₂ ≠ u) (α : Fin 3) (χ : Fin 3 → ℂ) (ψ : V → Fin 3 → ℂ)
    (hann : ∀ w ∈ (Finset.univ.erase u).erase u₂,
      (∑ b : Fin 3, ψ w b * W s((u, α), (w, b))) = 0) :
    (∑ b : Fin 3, χ b * W s((u, α), (u₂, b))) * pairK W u u₂ α α ψ
      = amplitude W (Amplitude.const α) * χ α
        * ∏ w ∈ (Finset.univ.erase u).erase u₂, ψ w α := by
  classical
  have hmem₂ : u₂ ∈ Finset.univ.erase u := Finset.mem_erase.mpr ⟨h12, Finset.mem_univ u₂⟩
  set ψ' : V → Fin 3 → ℂ := Function.update ψ u₂ χ with hψ'
  have hoff : ∀ w : V, w ≠ u₂ → ψ' w = ψ w := fun w hw => Function.update_of_ne hw _ _
  have hat : ψ' u₂ = χ := Function.update_self _ _ _
  have hann' : ∀ w ∈ (Finset.univ.erase u).erase u₂,
      (∑ b : Fin 3, ψ' w b * W s((u, α), (w, b))) = 0 := by
    intro w hw
    rw [hoff w (Finset.mem_erase.mp hw).1]
    exact hann w hw
  have hK : pairK W u u₂ α α ψ' = pairK W u u₂ α α ψ := by
    refine Finset.sum_congr rfl (fun c _ => ?_)
    congr 1
    exact Finset.prod_congr rfl (fun w hw => by rw [hoff w (Finset.mem_erase.mp hw).1])
  have h1 := testSum_expand_one W h12 α ψ' hann'
  have h2 := testSum_eq W hzero u α ψ'
  rw [hat, hK] at h1
  rw [← Finset.mul_prod_erase _ _ hmem₂, hat] at h2
  rw [h1] at h2
  rw [h2, ← mul_assoc]
  congr 1
  exact Finset.prod_congr rfl (fun w hw => by rw [hoff w (Finset.mem_erase.mp hw).1])

/-- **Purity from annihilators.**  If the annihilating vectors can be chosen with non-zero
component in the colour, the spared partner's row is a non-zero multiple of that colour's
basis vector --- and the complementary weighted matching sum survives, so nothing there
can cancel. -/
theorem pure_of_annihilators (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const (V := V) k) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {u u₂ : V} (h12 : u₂ ≠ u) (α : Fin 3) (ψ : V → Fin 3 → ℂ)
    (hann : ∀ w ∈ (Finset.univ.erase u).erase u₂,
      (∑ b : Fin 3, ψ w b * W s((u, α), (w, b))) = 0)
    (hpos : ∀ w ∈ (Finset.univ.erase u).erase u₂, ψ w α ≠ 0) :
    pairK W u u₂ α α ψ ≠ 0
      ∧ (∀ b : Fin 3, b ≠ α → W s((u, α), (u₂, b)) = 0)
      ∧ W s((u, α), (u₂, α)) ≠ 0 := by
  classical
  have hprod : (∏ w ∈ (Finset.univ.erase u).erase u₂, ψ w α) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hpos
  have hRHS : amplitude W (Amplitude.const (V := V) α)
      * ∏ w ∈ (Finset.univ.erase u).erase u₂, ψ w α ≠ 0 := mul_ne_zero (hone α) hprod
  have hsel : ∀ b : Fin 3,
      (∑ x : Fin 3, (if x = b then (1:ℂ) else 0) * W s((u, α), (u₂, x)))
        = W s((u, α), (u₂, b)) := by
    intro b
    rw [Finset.sum_eq_single_of_mem b (Finset.mem_univ b) (fun x _ hx => by simp [hx])]
    simp
  have hα := row_mul_pairK W hzero h12 α (fun x => if x = α then (1:ℂ) else 0) ψ hann
  rw [hsel α] at hα
  have hαc : W s((u, α), (u₂, α)) * pairK W u u₂ α α ψ
      = amplitude W (Amplitude.const (V := V) α)
        * ∏ w ∈ (Finset.univ.erase u).erase u₂, ψ w α := by
    rw [hα]; simp
  have hKne : pairK W u u₂ α α ψ ≠ 0 := by
    intro h
    rw [h, mul_zero] at hαc
    exact hRHS hαc.symm
  refine ⟨hKne, fun b hb => ?_, ?_⟩
  · have hb' := row_mul_pairK W hzero h12 α (fun x => if x = b then (1:ℂ) else 0) ψ hann
    rw [hsel b] at hb'
    have hz' : (if (α : Fin 3) = b then (1:ℂ) else 0) = 0 := if_neg (Ne.symm hb)
    simp only [hz', mul_zero, zero_mul] at hb'
    exact (mul_eq_zero.mp hb').resolve_right hKne
  · intro h
    rw [h, zero_mul] at hαc
    exact hRHS hαc.symm


/-! ## Compatibility at both ends of an edge

An annihilator that serves *both* ends of an edge at once lets the isolation run in each
direction with the same witnesses.  One direction empties the row, the other empties the
column, and the surviving entry is the same one.
-/

/-- **A block reduced to a single entry.**  If at every other site one vector annihilates
the `α`-rows read from *both* ends of the edge and still has a non-zero `α`-component,
then the edge's block carries the colour `α` at both ends and nothing else, with that
entry non-zero. -/
theorem block_single_entry_of_annihilators (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const (V := V) k) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {u u' : V} (h : u' ≠ u) (α : Fin 3) (ψ : V → Fin 3 → ℂ)
    (hann : ∀ w ∈ (Finset.univ.erase u).erase u',
      (∑ b : Fin 3, ψ w b * W s((u, α), (w, b))) = 0)
    (hann' : ∀ w ∈ (Finset.univ.erase u).erase u',
      (∑ b : Fin 3, ψ w b * W s((u', α), (w, b))) = 0)
    (hpos : ∀ w ∈ (Finset.univ.erase u).erase u', ψ w α ≠ 0) :
    (∀ b : Fin 3, b ≠ α → W s((u, α), (u', b)) = 0)
      ∧ (∀ a : Fin 3, a ≠ α → W s((u, a), (u', α)) = 0)
      ∧ W s((u, α), (u', α)) ≠ 0 := by
  classical
  have hswap : (Finset.univ.erase u').erase u = (Finset.univ.erase u).erase u' :=
    Finset.erase_right_comm
  obtain ⟨-, hrow, hdiag⟩ := pure_of_annihilators W hone hzero h α ψ hann hpos
  obtain ⟨-, hcol, -⟩ :=
    pure_of_annihilators W hone hzero (Ne.symm h) α ψ
      (by rw [hswap]; exact hann') (by rw [hswap]; exact hpos)
  refine ⟨hrow, fun a ha => ?_, hdiag⟩
  have := hcol a ha
  rwa [Sym2.eq_swap] at this

/-- **The block dichotomy.**  For every pair of sites and every colour, either the block
between them is that single entry, or some third site carries two `α`-rows --- one read
from each end --- whose common annihilators all vanish in the colour `α`.

This is the compatibility the two ends of an edge impose on each other.  The second
alternative says exactly that `e_α` lies in the span of those two rows, phrased so that
it can be used without leaving the language of the equations. -/
theorem block_dichotomy (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const (V := V) k) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {u u' : V} (h : u' ≠ u) (α : Fin 3) :
    ((∀ b : Fin 3, b ≠ α → W s((u, α), (u', b)) = 0)
        ∧ (∀ a : Fin 3, a ≠ α → W s((u, a), (u', α)) = 0)
        ∧ W s((u, α), (u', α)) ≠ 0)
      ∨ ∃ w ∈ (Finset.univ.erase u).erase u',
          ∀ x : Fin 3 → ℂ, (∑ b : Fin 3, x b * W s((u, α), (w, b))) = 0 →
            (∑ b : Fin 3, x b * W s((u', α), (w, b))) = 0 → x α = 0 := by
  classical
  by_cases hall : ∀ w : V, ∃ x : Fin 3 → ℂ,
      w ∈ (Finset.univ.erase u).erase u' →
        ((∑ b : Fin 3, x b * W s((u, α), (w, b))) = 0
          ∧ (∑ b : Fin 3, x b * W s((u', α), (w, b))) = 0 ∧ x α ≠ 0)
  · choose ψ hψ using hall
    exact Or.inl (block_single_entry_of_annihilators W hone hzero h α ψ
      (fun w hw => (hψ w hw).1) (fun w hw => (hψ w hw).2.1) (fun w hw => (hψ w hw).2.2))
  · push_neg at hall
    obtain ⟨w, hw⟩ := hall
    obtain ⟨x₀, hx₀⟩ : ∃ x : Fin 3 → ℂ, True := ⟨0, trivial⟩
    refine Or.inr ⟨w, ?_, fun x h1 h2 => ?_⟩
    · exact (hw x₀).1
    · exact (hw x).2 h1 h2


/-! ## The master relation

Testing against a *generic* covector at the expansion site, rather than a basis vector,
turns the isolation into a single relation among all three colours at once.
-/

/-- The complementary sum does not depend on which colours the two sites are pinned to:
the matchings it runs over never touch them. -/
theorem pairK_pin (W : Sym2 (V × Fin 3) → ℂ) {u v : V} (hv : v ≠ u)
    (α β α' β' : Fin 3) (ψ : V → Fin 3 → ℂ) :
    pairK W u v α β ψ = pairK W u v α' β' ψ := by
  classical
  have step : ∀ (x : V) (H : (V → Fin 3) → ℂ),
      (∀ (c : V → Fin 3) (b : Fin 3), H (Function.update c x b) = H c) →
      ∀ p q : Fin 3,
        (∑ c : V → Fin 3, (if c x = p then (1:ℂ) else 0) * H c)
          = ∑ c : V → Fin 3, (if c x = q then (1:ℂ) else 0) * H c := by
    intro x H hH p q
    have hp := sum_colourings_factor x (fun b => if b = p then (1:ℂ) else 0) H hH q
    have hq := sum_colourings_factor x (fun b => if b = q then (1:ℂ) else 0) H hH q
    have e1 : (∑ b : Fin 3, if b = p then (1:ℂ) else 0) = 1 := by simp
    have e2 : (∑ b : Fin 3, if b = q then (1:ℂ) else 0) = 1 := by simp
    rw [e1, one_mul] at hp
    rw [e2, one_mul] at hq
    rw [hp, hq]
  have hHv : ∀ (c : V → Fin 3) (b : Fin 3),
      ((if (Function.update c v b) u = α then (1:ℂ) else 0)
          * pmSum W (Function.update c v b) ((Finset.univ.erase u).erase v)
          * ∏ w ∈ (Finset.univ.erase u).erase v, ψ w ((Function.update c v b) w))
        = ((if c u = α then (1:ℂ) else 0)
          * pmSum W c ((Finset.univ.erase u).erase v)
          * ∏ w ∈ (Finset.univ.erase u).erase v, ψ w (c w)) := by
    intro c b
    rw [Function.update_of_ne (Ne.symm hv),
      pmSum_congr_colour W (c := Function.update c v b) (c' := c)
        (fun w hw => Function.update_of_ne (Finset.mem_erase.mp hw).1 _ _),
      Finset.prod_congr rfl (fun w hw => by
        rw [Function.update_of_ne (Finset.mem_erase.mp hw).1])]
  have hstep1 : pairK W u v α β ψ = pairK W u v α β' ψ := by
    rw [pairK, pairK]
    have h := step v (fun c : V → Fin 3 => (if c u = α then (1:ℂ) else 0)
        * pmSum W c ((Finset.univ.erase u).erase v)
        * ∏ w ∈ (Finset.univ.erase u).erase v, ψ w (c w)) hHv β β'
    calc (∑ c : V → Fin 3, (if c u = α then (1:ℂ) else 0) * (if c v = β then (1:ℂ) else 0)
            * pmSum W c ((Finset.univ.erase u).erase v)
            * ∏ w ∈ (Finset.univ.erase u).erase v, ψ w (c w))
        = ∑ c : V → Fin 3, (if c v = β then (1:ℂ) else 0)
            * ((if c u = α then (1:ℂ) else 0) * pmSum W c ((Finset.univ.erase u).erase v)
              * ∏ w ∈ (Finset.univ.erase u).erase v, ψ w (c w)) :=
          Finset.sum_congr rfl (fun c _ => by ring)
      _ = ∑ c : V → Fin 3, (if c v = β' then (1:ℂ) else 0)
            * ((if c u = α then (1:ℂ) else 0) * pmSum W c ((Finset.univ.erase u).erase v)
              * ∏ w ∈ (Finset.univ.erase u).erase v, ψ w (c w)) := h
      _ = _ := Finset.sum_congr rfl (fun c _ => by ring)
  have hHu : ∀ (c : V → Fin 3) (b : Fin 3),
      ((if (Function.update c u b) v = β' then (1:ℂ) else 0)
          * pmSum W (Function.update c u b) ((Finset.univ.erase u).erase v)
          * ∏ w ∈ (Finset.univ.erase u).erase v, ψ w ((Function.update c u b) w))
        = ((if c v = β' then (1:ℂ) else 0)
          * pmSum W c ((Finset.univ.erase u).erase v)
          * ∏ w ∈ (Finset.univ.erase u).erase v, ψ w (c w)) := by
    intro c b
    rw [Function.update_of_ne hv,
      pmSum_congr_colour W (c := Function.update c u b) (c' := c)
        (fun w hw => Function.update_of_ne
          (Finset.mem_erase.mp (Finset.mem_of_mem_erase hw)).1 _ _),
      Finset.prod_congr rfl (fun w hw => by
        rw [Function.update_of_ne (Finset.mem_erase.mp (Finset.mem_of_mem_erase hw)).1])]
  rw [hstep1, pairK, pairK]
  have h := step u (fun c : V → Fin 3 => (if c v = β' then (1:ℂ) else 0)
      * pmSum W c ((Finset.univ.erase u).erase v)
      * ∏ w ∈ (Finset.univ.erase u).erase v, ψ w (c w)) hHu α α'
  calc (∑ c : V → Fin 3, (if c u = α then (1:ℂ) else 0) * (if c v = β' then (1:ℂ) else 0)
          * pmSum W c ((Finset.univ.erase u).erase v)
          * ∏ w ∈ (Finset.univ.erase u).erase v, ψ w (c w))
      = ∑ c : V → Fin 3, (if c u = α then (1:ℂ) else 0)
          * ((if c v = β' then (1:ℂ) else 0) * pmSum W c ((Finset.univ.erase u).erase v)
            * ∏ w ∈ (Finset.univ.erase u).erase v, ψ w (c w)) :=
        Finset.sum_congr rfl (fun c _ => by ring)
    _ = ∑ c : V → Fin 3, (if c u = α' then (1:ℂ) else 0)
          * ((if c v = β' then (1:ℂ) else 0) * pmSum W c ((Finset.univ.erase u).erase v)
            * ∏ w ∈ (Finset.univ.erase u).erase v, ψ w (c w)) := h
    _ = _ := Finset.sum_congr rfl (fun c _ => by ring)


/-- **The expansion, in full.**  Every partner contributes its own row contracted against
its own test vector, times the complementary sum. -/
theorem testSum_expand_full (W : Sym2 (V × Fin 3) → ℂ) (u : V) (a : Fin 3)
    (ψ : V → Fin 3 → ℂ) :
    testSum W u a ψ
      = ∑ v ∈ Finset.univ.erase u,
          (∑ b : Fin 3, ψ v b * W s((u, a), (v, b))) * pairK W u v a a ψ := by
  classical
  have hexp : ∀ c : V → Fin 3, amplitude W c
      = ∑ v ∈ Finset.univ.erase u,
          W s((u, c u), (v, c v)) * pmSum W c ((Finset.univ.erase u).erase v) := by
    intro c
    rw [← pmSum_univ, pmSum_expand W c (Finset.mem_univ u)]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    first
    | rfl
    | (congr 1; simp [Sym2.map_pair_eq, paint])
  have key : ∀ c : V → Fin 3,
      amplitude W c * (if c u = a then 1 else 0)
          * ∏ w ∈ Finset.univ.erase u, ψ w (c w)
        = ∑ v ∈ Finset.univ.erase u,
            W s((u, c u), (v, c v)) * pmSum W c ((Finset.univ.erase u).erase v)
              * (if c u = a then 1 else 0) * ∏ w ∈ Finset.univ.erase u, ψ w (c w) := by
    intro c
    rw [hexp c, Finset.sum_mul, Finset.sum_mul]
  rw [testSum, Finset.sum_congr rfl (fun c _ => key c), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun v hv => ?_)
  have hvu : v ≠ u := (Finset.mem_erase.mp hv).1
  have hrw : ∀ c : V → Fin 3,
      W s((u, c u), (v, c v)) * pmSum W c ((Finset.univ.erase u).erase v)
          * (if c u = a then 1 else 0) * ∏ w ∈ Finset.univ.erase u, ψ w (c w)
        = (ψ v (c v) * W s((u, a), (v, c v)))
          * ((if c u = a then (1:ℂ) else 0)
              * pmSum W c ((Finset.univ.erase u).erase v)
              * ∏ w ∈ (Finset.univ.erase u).erase v, ψ w (c w)) := by
    intro c
    rw [← Finset.mul_prod_erase _ _ hv]
    by_cases h1 : c u = a
    · rw [h1]; ring
    · simp [h1]
  have hH : ∀ (c : V → Fin 3) (b : Fin 3),
      ((if (Function.update c v b) u = a then (1:ℂ) else 0)
          * pmSum W (Function.update c v b) ((Finset.univ.erase u).erase v)
          * ∏ w ∈ (Finset.univ.erase u).erase v, ψ w ((Function.update c v b) w))
        = ((if c u = a then (1:ℂ) else 0)
          * pmSum W c ((Finset.univ.erase u).erase v)
          * ∏ w ∈ (Finset.univ.erase u).erase v, ψ w (c w)) := by
    intro c b
    rw [Function.update_of_ne (Ne.symm hvu),
      pmSum_congr_colour W (c := Function.update c v b) (c' := c)
        (fun w hw => Function.update_of_ne (Finset.mem_erase.mp hw).1 _ _),
      Finset.prod_congr rfl (fun w hw => by
        rw [Function.update_of_ne (Finset.mem_erase.mp hw).1])]
  rw [Finset.sum_congr rfl (fun c _ => hrw c),
    sum_colourings_factor v (fun b => ψ v b * W s((u, a), (v, b)))
      (fun c : V → Fin 3 => (if c u = a then (1:ℂ) else 0)
        * pmSum W c ((Finset.univ.erase u).erase v)
        * ∏ w ∈ (Finset.univ.erase u).erase v, ψ w (c w)) hH a]
  rw [pairK]
  congr 1
  exact Finset.sum_congr rfl (fun c _ => by ring)

/-- **The master relation.**  Test the equations at one site against an arbitrary
covector, and at every other site against a vector annihilating that site's contracted
row.  The expansion empties; the direct reading still sees all three constant colourings.

This is the strongest form of the isolation method, and the relation every structure
theorem below is read off from. -/
theorem master_relation (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (u : V) (ρ : Fin 3 → ℂ) (ψ : V → Fin 3 → ℂ)
    (hann : ∀ v ∈ Finset.univ.erase u,
      (∑ b : Fin 3, ψ v b * (∑ a : Fin 3, ρ a * W s((u, a), (v, b)))) = 0) :
    (∑ k : Fin 3, ρ k * amplitude W (Amplitude.const (V := V) k)
        * ∏ w ∈ Finset.univ.erase u, ψ w k) = 0 := by
  classical
  have step : (∑ k : Fin 3, ρ k * amplitude W (Amplitude.const (V := V) k)
        * ∏ w ∈ Finset.univ.erase u, ψ w k)
      = ∑ k : Fin 3, ρ k * testSum W u k ψ := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [testSum_eq W hzero u k ψ, mul_assoc]
  rw [step]
  have step2 : (∑ k : Fin 3, ρ k * testSum W u k ψ)
      = ∑ k : Fin 3, ∑ v ∈ Finset.univ.erase u,
          ρ k * ((∑ b : Fin 3, ψ v b * W s((u, k), (v, b))) * pairK W u v 0 0 ψ) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [testSum_expand_full W u k ψ, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun v hv => ?_)
    rw [pairK_pin W (Finset.mem_erase.mp hv).1 k k 0 0 ψ]
  rw [step2, Finset.sum_comm]
  refine Finset.sum_eq_zero (fun v hv => ?_)
  have hfub : (∑ k : Fin 3, ρ k * ((∑ b : Fin 3, ψ v b * W s((u, k), (v, b)))
        * pairK W u v 0 0 ψ))
      = (∑ b : Fin 3, ψ v b * (∑ a : Fin 3, ρ a * W s((u, a), (v, b))))
        * pairK W u v 0 0 ψ := by
    calc (∑ k : Fin 3, ρ k * ((∑ b : Fin 3, ψ v b * W s((u, k), (v, b)))
            * pairK W u v 0 0 ψ))
        = ∑ k : Fin 3, (ρ k * ∑ b : Fin 3, ψ v b * W s((u, k), (v, b)))
            * pairK W u v 0 0 ψ := Finset.sum_congr rfl (fun k _ => by ring)
      _ = (∑ k : Fin 3, ρ k * ∑ b : Fin 3, ψ v b * W s((u, k), (v, b)))
            * pairK W u v 0 0 ψ := (Finset.sum_mul _ _ _).symm
      _ = (∑ b : Fin 3, ψ v b * (∑ a : Fin 3, ρ a * W s((u, a), (v, b))))
            * pairK W u v 0 0 ψ := by
          congr 1
          calc (∑ k : Fin 3, ρ k * ∑ b : Fin 3, ψ v b * W s((u, k), (v, b)))
              = ∑ k : Fin 3, ∑ b : Fin 3, ψ v b * (ρ k * W s((u, k), (v, b))) :=
                Finset.sum_congr rfl (fun k _ => by
                  rw [Finset.mul_sum]
                  exact Finset.sum_congr rfl (fun b _ => by ring))
            _ = ∑ b : Fin 3, ∑ k : Fin 3, ψ v b * (ρ k * W s((u, k), (v, b))) :=
                Finset.sum_comm
            _ = ∑ b : Fin 3, ψ v b * (∑ a : Fin 3, ρ a * W s((u, a), (v, b))) :=
                Finset.sum_congr rfl (fun b _ => (Finset.mul_sum _ _ _).symm)
  rw [hfub, hann v hv, zero_mul]


/-- **The column lemma.**  A covector annihilating one and the same colour's column at
every partner has no component in that colour.  Testing every other site with that
colour's indicator collapses the master relation to a single term. -/
theorem column_lemma (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {u : V} (hu : (Finset.univ.erase u).Nonempty) (ρ : Fin 3 → ℂ) (α : Fin 3)
    (h : ∀ v ∈ Finset.univ.erase u, (∑ a : Fin 3, ρ a * W s((u, a), (v, α))) = 0) :
    ρ α = 0 := by
  classical
  have key := master_relation W hzero u ρ (fun _ b => if b = α then (1:ℂ) else 0) ?_
  · have hcard : (Finset.univ.erase u).card ≠ 0 := Finset.card_ne_zero_of_mem hu.choose_spec
    have hprod : ∀ j : Fin 3,
        (∏ _w ∈ Finset.univ.erase u, (if j = α then (1:ℂ) else 0))
          = if j = α then 1 else 0 := by
      intro j
      rw [Finset.prod_const]
      by_cases hj : j = α
      · simp [hj]
      · rw [if_neg hj, zero_pow hcard]
    rw [Finset.sum_congr rfl (fun j _ => by rw [hprod j])] at key
    rw [Finset.sum_eq_single_of_mem α (Finset.mem_univ α)
      (fun j _ hj => by simp [hj])] at key
    have hii : (if (α : Fin 3) = α then (1:ℂ) else 0) = 1 := by simp
    rw [hii, mul_one] at key
    exact (mul_eq_zero.mp key).resolve_right (hone α)
  · intro v hv
    rw [Finset.sum_eq_single_of_mem α (Finset.mem_univ α) (fun b _ hb => by simp [hb])]
    rw [if_pos rfl, one_mul]
    exact h v hv


/-- An explicit vector supported on two coordinates, and the value it takes against a
covector. -/
theorem two_term_sum (r : Fin 3 → ℂ) (p q : Fin 3) (hpq : p ≠ q) (A B : ℂ) :
    (∑ b : Fin 3, (if b = p then A else if b = q then B else 0) * r b)
      = A * r p + B * r q := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p),
    Finset.sum_eq_single_of_mem q (Finset.mem_erase.mpr ⟨Ne.symm hpq, Finset.mem_univ q⟩)
      (fun b hb hbq => by
        have hbp : b ≠ p := (Finset.mem_erase.mp hb).1
        simp [hbp, hbq])]
  simp [hpq, hpq.symm]

/-- **The fan for a generic covector.**  Contract the equations at a site against a
covector with no vanishing component.  Then in every colour some partner's contracted row
points along that colour's axis alone.

This is the master relation put to work.  Suppose no partner did: then at every partner
one may annihilate the contracted row while keeping a non-zero component in the colour,
and --- unless one colour's contracted column vanishes at every partner, which the column
lemma forbids --- one may in addition arrange two *different* partners to kill the other
two colours outright.  The relation then reads a non-zero product equal to zero. -/
theorem rho_fan (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {u : V} (hu : 2 ≤ (Finset.univ.erase u).card)
    (ρ : Fin 3 → ℂ) (hρ : ∀ j : Fin 3, ρ j ≠ 0)
    (k k' k'' : Fin 3) (hkk' : k ≠ k') (hkk'' : k ≠ k'') (hk'k'' : k' ≠ k'') :
    ∃ w ∈ Finset.univ.erase u,
      (∀ b : Fin 3, b ≠ k → (∑ a : Fin 3, ρ a * W s((u, a), (w, b))) = 0)
        ∧ (∑ a : Fin 3, ρ a * W s((u, a), (w, k))) ≠ 0 := by
  classical
  set S : Finset V := Finset.univ.erase u with hSdef
  set r : V → Fin 3 → ℂ := fun w b => ∑ a : Fin 3, ρ a * W s((u, a), (w, b)) with hrdef
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  by_contra hcon
  push_neg at hcon
  -- `hcon w hw : (∀ b, b ≠ k → r w b = 0) → r w k = 0`
  -- the three colours exhaust `Fin 3`
  have huniv : ({k, k', k''} : Finset (Fin 3)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_insert_of_notMem (by simp [hkk', hkk'']),
      Finset.card_insert_of_notMem (by simp [hk'k'']), Finset.card_singleton]
    first
    | rfl
    | simp
    | decide
  -- the contradiction, given a good family of test vectors
  have contra : ∀ ψ : V → Fin 3 → ℂ,
      (∀ w ∈ S, (∑ b : Fin 3, ψ w b * r w b) = 0) →
      (∀ w ∈ S, ψ w k ≠ 0) →
      (∃ w₁ ∈ S, ψ w₁ k' = 0) → (∃ w₂ ∈ S, ψ w₂ k'' = 0) → False := by
    intro ψ hann hk h1 h2
    have key := master_relation W hzero u ρ ψ hann
    obtain ⟨w₁, hw₁, e₁⟩ := h1
    obtain ⟨w₂, hw₂, e₂⟩ := h2
    have p1 : (∏ w ∈ S, ψ w k') = 0 := Finset.prod_eq_zero hw₁ e₁
    have p2 : (∏ w ∈ S, ψ w k'') = 0 := Finset.prod_eq_zero hw₂ e₂
    rw [← huniv, Finset.sum_insert (by simp [hkk', hkk'']),
      Finset.sum_insert (by simp [hk'k'']), Finset.sum_singleton,
      p1, p2, mul_zero, mul_zero, add_zero, add_zero] at key
    exact mul_ne_zero (mul_ne_zero (hρ k) (hone k))
      (Finset.prod_ne_zero_iff.mpr hk) key
  -- a test vector at any site, non-zero in the colour `k`
  have hgen : ∀ w ∈ S, ∃ x : Fin 3 → ℂ, (∑ b : Fin 3, x b * r w b) = 0 ∧ x k ≠ 0 := by
    intro w hw
    by_cases hk0 : r w k = 0
    · exact ⟨fun b => if b = k then 1 else if b = k' then 0 else 0, by
        rw [two_term_sum (r w) k k' hkk' 1 0]; simp [hk0], by simp⟩
    · obtain ⟨b₀, hb₀, hne⟩ : ∃ b : Fin 3, b ≠ k ∧ r w b ≠ 0 := by
        by_contra hall
        push_neg at hall
        exact hk0 (hcon w hw hall)
      exact ⟨fun b => if b = k then r w b₀ else if b = b₀ then -(r w k) else 0, by
        rw [two_term_sum (r w) k b₀ (Ne.symm hb₀)]; ring, by simpa using hne⟩
  -- a test vector that also kills the colour `k'`
  have hkill' : ∀ w, (r w k'' ≠ 0 ∨ r w k = 0) →
      ∃ x : Fin 3 → ℂ, (∑ b : Fin 3, x b * r w b) = 0 ∧ x k ≠ 0 ∧ x k' = 0 := by
    intro w hw
    rcases hw with h | h
    · exact ⟨fun b => if b = k then r w k'' else if b = k'' then -(r w k) else 0, by
        rw [two_term_sum (r w) k k'' hkk'']; ring, by simpa using h,
        by simp [Ne.symm hkk', hk'k'']⟩
    · exact ⟨fun b => if b = k then 1 else if b = k'' then 0 else 0, by
        rw [two_term_sum (r w) k k'' hkk'' 1 0]; simp [h], by simp,
        by simp [Ne.symm hkk', hk'k'']⟩
  -- a test vector that also kills the colour `k''`
  have hkill'' : ∀ w, (r w k' ≠ 0 ∨ r w k = 0) →
      ∃ x : Fin 3 → ℂ, (∑ b : Fin 3, x b * r w b) = 0 ∧ x k ≠ 0 ∧ x k'' = 0 := by
    intro w hw
    rcases hw with h | h
    · exact ⟨fun b => if b = k then r w k' else if b = k' then -(r w k) else 0, by
        rw [two_term_sum (r w) k k' hkk']; ring, by simpa using h,
        by simp [Ne.symm hkk'', Ne.symm hk'k'']⟩
    · exact ⟨fun b => if b = k then 1 else if b = k' then 0 else 0, by
        rw [two_term_sum (r w) k k' hkk' 1 0]; simp [h], by simp,
        by simp [Ne.symm hkk'', Ne.symm hk'k'']⟩
  -- assemble: a total choice of generic test vectors
  have hgen' : ∀ w : V, ∃ x : Fin 3 → ℂ,
      w ∈ S → ((∑ b : Fin 3, x b * r w b) = 0 ∧ x k ≠ 0) := by
    intro w
    by_cases hw : w ∈ S
    · obtain ⟨x, hx1, hx2⟩ := hgen w hw
      exact ⟨x, fun _ => ⟨hx1, hx2⟩⟩
    · exact ⟨fun b => if b = k then 1 else 0, fun h => absurd h hw⟩
  choose g hg using hgen'
  have final : ∀ w₁ ∈ S, ∀ w₂ ∈ S, w₁ ≠ w₂ →
      (r w₁ k'' ≠ 0 ∨ r w₁ k = 0) → (r w₂ k' ≠ 0 ∨ r w₂ k = 0) → False := by
    intro w₁ hw₁ w₂ hw₂ hne c₁ c₂
    obtain ⟨x₁, hx₁a, hx₁k, hx₁'⟩ := hkill' w₁ c₁
    obtain ⟨x₂, hx₂a, hx₂k, hx₂''⟩ := hkill'' w₂ c₂
    refine contra (fun w => if w = w₁ then x₁ else if w = w₂ then x₂ else g w) ?_ ?_
      ⟨w₁, hw₁, by simp [hx₁']⟩ ⟨w₂, hw₂, by simp [Ne.symm hne, hx₂'']⟩
    · intro w hw
      by_cases h1 : w = w₁
      · subst h1; simpa using hx₁a
      · by_cases h2 : w = w₂
        · subst h2; simp only [if_neg h1, if_pos rfl]; exact hx₂a
        · simp only [if_neg h1, if_neg h2]; exact (hg w hw).1
    · intro w hw
      by_cases h1 : w = w₁
      · subst h1; simpa using hx₁k
      · by_cases h2 : w = w₂
        · subst h2; simp only [if_neg h1, if_pos rfl]; exact hx₂k
        · simp only [if_neg h1, if_neg h2]; exact (hg w hw).2
  by_cases hZ : ∃ w₀ ∈ S, r w₀ k = 0
  · -- one site whose contracted row misses the colour kills both others at once
    obtain ⟨w₀, hw₀, hr0⟩ := hZ
    refine contra (fun w => if w = w₀ then (fun b => if b = k then (1:ℂ) else 0) else g w)
      ?_ ?_ ⟨w₀, hw₀, by simp [Ne.symm hkk']⟩ ⟨w₀, hw₀, by simp [Ne.symm hkk'']⟩
    · intro w hw
      by_cases h1 : w = w₀
      · have hsel : (if w = w₀ then (fun b : Fin 3 => if b = k then (1:ℂ) else 0)
            else g w) = (fun b : Fin 3 => if b = k then (1:ℂ) else 0) := if_pos h1
        rw [hsel, Finset.sum_eq_single_of_mem k (Finset.mem_univ k)
          (fun b _ hb => by simp [hb]), h1]
        simp [hr0]
      · simp only [if_neg h1]; exact (hg w hw).1
    · intro w hw
      by_cases h1 : w = w₀
      · subst h1; simp
      · simp only [if_neg h1]; exact (hg w hw).2
  · push_neg at hZ
    have hsplit : ∀ w ∈ S, r w k' ≠ 0 ∨ r w k'' ≠ 0 := by
      intro w hw
      by_contra hb
      push_neg at hb
      refine hZ w hw (hcon w hw (fun b hbk => ?_))
      have hb3 : b = k ∨ b = k' ∨ b = k'' := by
        have : b ∈ ({k, k', k''} : Finset (Fin 3)) := by rw [huniv]; exact Finset.mem_univ b
        simpa using this
      rcases hb3 with h | h | h
      · exact absurd h hbk
      · rw [h]; exact hb.1
      · rw [h]; exact hb.2
    by_cases hA : ∀ w ∈ S, r w k' = 0
    · exact hρ k' (column_lemma W hone hzero hSne ρ k' (fun v hv => hA v hv))
    · by_cases hB : ∀ w ∈ S, r w k'' = 0
      · exact hρ k'' (column_lemma W hone hzero hSne ρ k'' (fun v hv => hB v hv))
      · push_neg at hA hB
        obtain ⟨z, hz, hzk'⟩ := hA
        obtain ⟨y, hy, hyk''⟩ := hB
        by_cases hzy : z = y
        · subst hzy
          obtain ⟨w, hw, hwz⟩ := Finset.exists_mem_ne (s := S) (by omega) z
          rcases hsplit w hw with h | h
          · exact final z hz w hw (Ne.symm hwz) (Or.inl hyk'') (Or.inl h)
          · exact final w hw z hz hwz (Or.inl h) (Or.inl hzk')
        · exact final y hy z hz (fun e => hzy e.symm) (Or.inl hyk'') (Or.inl hzk')


/-! ## Cancellation, turned around

Cancellation is the standing obstacle: a matching's contribution to a colouring can be
annulled by the other matchings, so exhibiting one contributing matching proves nothing.
The way past it is to isolate combinatorially rather than to estimate.  If a colouring
admits exactly one contributing matching, there is nothing left to cancel it, and the
equations must accept the contribution --- which forces the colouring to be constant.
-/

/-- **A matching with no rival cannot be cancelled.**  If exactly one matching contributes
to a colouring, that colouring is constant. -/
theorem monochromatic_of_unique_matching (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (c : V → Fin 3) {σ : Equiv.Perm V} (hσ : σ ∈ pairings V)
    (hprod : (∏ e ∈ edges σ, W (Sym2.map (paint c) e)) ≠ 0)
    (huniq : ∀ τ ∈ pairings V, τ ≠ σ → (∏ e ∈ edges τ, W (Sym2.map (paint c) e)) = 0) :
    Amplitude.Monochromatic c := by
  by_contra hc
  have hA := hzero c hc
  rw [amplitude, Finset.sum_eq_single_of_mem σ hσ huniq] at hA
  exact hprod hA


/-! ## From covectors to blocks

The partners named by the fan depend on the covector tested against.  They can be made
not to: finitely many proper subspaces cannot cover a space over an infinite field, so one
covector serves as a witness for all of them at once, and what it names is a property of
the block itself.
-/

/-- The linear form a covector induces on one column of a block. -/
noncomputable def colForm (W : Sym2 (V × Fin 3) → ℂ) (u w : V) (b : Fin 3) :
    (Fin 3 → ℂ) →ₗ[ℂ] ℂ where
  toFun ρ := ∑ a : Fin 3, ρ a * W s((u, a), (w, b))
  map_add' x y := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum, mul_assoc]

theorem colForm_apply (W : Sym2 (V × Fin 3) → ℂ) (u w : V) (b : Fin 3) (ρ : Fin 3 → ℂ) :
    colForm W u w b ρ = ∑ a : Fin 3, ρ a * W s((u, a), (w, b)) := rfl

/-- A vanishing column form means the column itself vanishes. -/
theorem entry_eq_zero_of_colForm (W : Sym2 (V × Fin 3) → ℂ) (u w : V) (b : Fin 3)
    (h : colForm W u w b = 0) (a : Fin 3) : W s((u, a), (w, b)) = 0 := by
  classical
  have h0 : colForm W u w b (fun a' => if a' = a then (1 : ℂ) else 0) = 0 := by
    rw [h]; rfl
  rw [colForm_apply, Finset.sum_eq_single_of_mem a (Finset.mem_univ a)
    (fun a' _ ha' => by simp [ha'])] at h0
  simpa using h0

/-- The two colours other than a given one. -/
theorem exists_other_two (k : Fin 3) : ∃ k' k'' : Fin 3, k ≠ k' ∧ k ≠ k'' ∧ k' ≠ k'' := by
  fin_cases k
  · exact ⟨1, 2, by decide, by decide, by decide⟩
  · exact ⟨0, 2, by decide, by decide, by decide⟩
  · exact ⟨0, 1, by decide, by decide, by decide⟩

/-- **A column-supported block.**  For every site and every colour there is a partner
whose block carries that colour alone at the far end, and is not identically zero.

The fan names a partner for each covector; the covectors naming a fixed partner form a
linear subspace, and one that is not the whole space is proper.  Choosing a covector off
all the proper ones --- possible because finitely many proper subspaces do not cover ---
forces the partner it names to be named by every covector, which is a statement about the
block. -/
theorem exists_column_partner (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {u : V} (hu : 2 ≤ (Finset.univ.erase u).card) (k : Fin 3) :
    ∃ w ∈ Finset.univ.erase u,
      (∀ a b : Fin 3, b ≠ k → W s((u, a), (w, b)) = 0)
        ∧ ∃ a : Fin 3, W s((u, a), (w, k)) ≠ 0 := by
  classical
  obtain ⟨k', k'', h1, h2, h3⟩ := exists_other_two k
  set P : (V × Fin 3) ⊕ Fin 3 → Submodule ℂ (Fin 3 → ℂ) := fun i =>
    match i with
    | Sum.inl q => if colForm W u q.1 q.2 = 0 then ⊥ else LinearMap.ker (colForm W u q.1 q.2)
    | Sum.inr j => LinearMap.ker (LinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) j)
    with hP
  have hne : ∀ i, P i ≠ ⊤ := by
    intro i
    match i with
    | Sum.inl q =>
        by_cases hq : colForm W u q.1 q.2 = 0
        · simp only [hP, hq, if_pos]
          exact bot_ne_top
        · simp only [hP, hq, if_neg, not_false_iff]
          exact fun h => hq (LinearMap.ker_eq_top.mp h)
    | Sum.inr j =>
        simp only [hP]
        intro h
        have : (LinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) j) = 0 :=
          LinearMap.ker_eq_top.mp h
        have h1 : (LinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) j)
            (fun _ => (1 : ℂ)) = 1 := rfl
        rw [this] at h1
        exact one_ne_zero h1.symm
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Fin 3 → ℂ, ρ ∉ ⋃ i, (P i : Set (Fin 3 → ℂ)) := by
    rw [← Set.ne_univ_iff_exists_notMem]
    intro h
    obtain ⟨i, hi⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ h
    exact hne i hi
  have hmem : ∀ i, ρ ∉ P i := by
    intro i h
    exact hρ (Set.mem_iUnion.mpr ⟨i, h⟩)
  have hρc : ∀ j : Fin 3, ρ j ≠ 0 := by
    intro j hj
    exact hmem (Sum.inr j) (LinearMap.mem_ker.mpr hj)
  obtain ⟨w, hw, hpure, hnz⟩ := rho_fan W hone hzero hu ρ hρc k k' k'' h1 h2 h3
  refine ⟨w, hw, fun a b hb => ?_, ?_⟩
  · refine entry_eq_zero_of_colForm W u w b ?_ a
    by_contra hq
    exact hmem (Sum.inl (w, b)) (by
      simp only [hP, hq, if_neg, not_false_iff]
      exact LinearMap.mem_ker.mpr (hpure b hb))
  · by_contra hall
    push_neg at hall
    exact hnz (by
      rw [← colForm_apply, show colForm W u w k = 0 from LinearMap.ext (fun x => by
        rw [colForm_apply]
        exact Finset.sum_eq_zero (fun a _ => by rw [hall a, mul_zero]))]
      rfl)


/-- **The column fan.**  The three partners named by the previous theorem, one per
colour, are distinct: a block carrying two colours alone at the far end carries none. -/
theorem exists_column_fan (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {u : V} (hu : 2 ≤ (Finset.univ.erase u).card) :
    ∃ w : Fin 3 → V, Function.Injective w ∧ (∀ k, w k ≠ u) ∧
      (∀ k : Fin 3, ∀ a b : Fin 3, b ≠ k → W s((u, a), (w k, b)) = 0) ∧
      (∀ k : Fin 3, ∃ a : Fin 3, W s((u, a), (w k, k)) ≠ 0) := by
  classical
  choose w hw hpure hnz using fun k : Fin 3 => exists_column_partner W hone hzero hu k
  refine ⟨w, ?_, fun k => (Finset.mem_erase.mp (hw k)).1, hpure, hnz⟩
  intro k k' hkk'
  by_contra hne
  obtain ⟨a, ha⟩ := hnz k
  rw [hkk'] at ha
  exact ha (hpure k' a k hne)


/-! ## The colour-per-matching structure, refuted

Suppose the configuration has reduced to its rigid shape: every live edge joins a site to
its partner in one of three disjoint perfect matchings, and carries that matching's colour
at both of its ends.  Then a perfect matching *mixing* two of the three is fatal.  It
induces a colouring which is non-constant, and for which it is the only contributing
matching --- every other matching sends some site to a partner of the wrong colour.  The
equations cannot accept a lone non-zero contribution on a non-constant colouring.
-/

/-- **A mixed matching is fatal.** -/
theorem mixed_matching_false (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (σ : Fin 3 → Equiv.Perm V)
    (hlive : ∀ (x y : V) (a b : Fin 3), W s((x, a), (y, b)) ≠ 0 →
      ∃ k : Fin 3, y = σ k x ∧ a = k ∧ b = k)
    (τ : Equiv.Perm V) (hτ : τ ∈ pairings V) (c : V → Fin 3)
    (hc : ∀ x : V, τ x = σ (c x) x) (hcc : ∀ x : V, c (τ x) = c x)
    (hne : ∀ x : V, W s((x, c x), (τ x, c x)) ≠ 0)
    (hnm : ¬ Amplitude.Monochromatic c) : False := by
  classical
  have hprod : (∏ e ∈ edges τ, W (Sym2.map (paint c) e)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr (fun e he => ?_)
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp he
    rw [show Sym2.map (paint c) s(x, τ x) = s((x, c x), (τ x, c (τ x))) from rfl, hcc x]
    exact hne x
  have huniq : ∀ ρ ∈ pairings V, ρ ≠ τ →
      (∏ e ∈ edges ρ, W (Sym2.map (paint c) e)) = 0 := by
    intro ρ _ hρτ
    obtain ⟨x, hx⟩ : ∃ x : V, ρ x ≠ τ x := by
      by_contra h
      push_neg at h
      exact hρτ (Equiv.ext h)
    refine Finset.prod_eq_zero (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩) ?_
    rw [show Sym2.map (paint c) s(x, ρ x) = s((x, c x), (ρ x, c (ρ x))) from rfl]
    by_contra hnz
    obtain ⟨k, hk1, hk2, -⟩ := hlive x (ρ x) (c x) (c (ρ x)) hnz
    exact hx (by rw [hk1, ← hk2]; exact (hc x).symm)
  exact hnm (monochromatic_of_unique_matching W hzero c hτ hprod huniq)

/-- **The refutation, packaged.**  Three pairwise disjoint perfect matchings whose edges
are the only live ones, each carrying its own colour at both ends, admit no perfect
matching mixing two of them. -/
theorem no_mixed_matching (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (σ : Fin 3 → Equiv.Perm V) (hσ : ∀ k, σ k ∈ pairings V)
    (hdisj : ∀ k l : Fin 3, k ≠ l → ∀ x : V, σ k x ≠ σ l x)
    (hlive : ∀ (x y : V) (a b : Fin 3), W s((x, a), (y, b)) ≠ 0 →
      ∃ k : Fin 3, y = σ k x ∧ a = k ∧ b = k)
    (hedge : ∀ (x : V) (k : Fin 3), W s((x, k), (σ k x, k)) ≠ 0)
    (τ : Equiv.Perm V) (hτ : τ ∈ pairings V) (c : V → Fin 3)
    (hc : ∀ x : V, τ x = σ (c x) x) (hnm : ¬ Amplitude.Monochromatic c) : False := by
  classical
  have hinv : ∀ k : Fin 3, ∀ x : V, σ k (σ k x) = x := fun k x =>
    (mem_pairings_iff.mp (hσ k)).1 x
  have hτinv : ∀ x : V, τ (τ x) = x := (mem_pairings_iff.mp hτ).1
  have hcc' : ∀ x : V, c (τ x) = c x := by
    intro x
    by_contra hne
    refine hdisj (c (τ x)) (c x) hne (τ x) ?_
    rw [← hc (τ x), hτinv x, hc x, hinv (c x) x]
  refine mixed_matching_false W hzero σ hlive τ hτ c hc hcc' (fun x => ?_) hnm
  rw [hc x]
  exact hedge x (c x)


/-! ## Three partners force the diagonal

A site with exactly three live partners, one column-supported per colour, has no room
left: the column lemma pins each of its blocks to a single entry, and that entry is on the
diagonal.  The reason is that a covector orthogonal to one block's live column is then
orthogonal to *every* block's column in that colour, and the column lemma says such a
covector has no component there.
-/

/-- **Three partners force the diagonal.**  If the only live partners of a site are three
column-supported ones, one per colour, then each of those blocks has its single entry on
the diagonal. -/
theorem diag_of_three_partners (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {u : V} (hu : (Finset.univ.erase u).Nonempty) (w : Fin 3 → V)
    (hcol : ∀ (k : Fin 3) (a b : Fin 3), b ≠ k → W s((u, a), (w k, b)) = 0)
    (hdead : ∀ y : V, y ≠ u → (∀ k, y ≠ w k) → ∀ a b : Fin 3, W s((u, a), (y, b)) = 0)
    (k a : Fin 3) (ha : a ≠ k) : W s((u, a), (w k, k)) = 0 := by
  classical
  set A : ℂ := W s((u, k), (w k, k)) with hA
  set B : ℂ := W s((u, a), (w k, k)) with hB
  have hka : (k : Fin 3) ≠ a := Ne.symm ha
  have hrho : (if (k : Fin 3) = a then A else if (k : Fin 3) = k then -B else 0) = -B := by
    simp [hka]
  have hcolk : ∀ v ∈ Finset.univ.erase u,
      (∑ x : Fin 3, (if x = a then A else if x = k then -B else 0)
        * W s((u, x), (v, k))) = 0 := by
    intro v hv
    by_cases hvw : ∃ j : Fin 3, v = w j
    · obtain ⟨j, rfl⟩ := hvw
      by_cases hjk : j = k
      · subst hjk
        rw [two_term_sum (fun x : Fin 3 => W s((u, x), (w j, j))) a j ha A (-B)]
        rw [← hA, ← hB]
        ring
      · refine Finset.sum_eq_zero (fun x _ => ?_)
        rw [hcol j x k (fun h => hjk h.symm), mul_zero]
    · push_neg at hvw
      refine Finset.sum_eq_zero (fun x _ => ?_)
      rw [hdead v (Finset.mem_erase.mp hv).1 hvw x k, mul_zero]
  have hres := column_lemma W hone hzero hu
    (fun x : Fin 3 => if x = a then A else if x = k then -B else 0) k hcolk
  rw [hrho] at hres
  exact neg_eq_zero.mp hres


/-- A configuration is **three-regular in colour** when every site has exactly three live
partners, one column-supported in each colour.  Weights on a site's pair with itself are
taken to vanish; they never enter an amplitude, since matchings have no fixed points, so
this is a normalisation rather than a restriction. -/
structure ThreeRegular (W : Sym2 (V × Fin 3) → ℂ) where
  /-- the colour-`k` partner of a site -/
  partner : V → Fin 3 → V
  ne_self : ∀ x k, partner x k ≠ x
  no_loop : ∀ x a b, W s((x, a), (x, b)) = 0
  col : ∀ x k a b, b ≠ k → W s((x, a), (partner x k, b)) = 0
  live : ∀ x k, ∃ a, W s((x, a), (partner x k, k)) ≠ 0
  dead : ∀ x y, y ≠ x → (∀ k, y ≠ partner x k) → ∀ a b, W s((x, a), (y, b)) = 0

/-- **The rigid shape, assembled.**  A three-regular configuration is three disjoint
perfect matchings whose edges are the only live ones, each carrying its own colour at both
ends.  Diagonality comes from the column lemma; the partner relation is symmetric because
a single diagonal entry looks the same from either end. -/
theorem three_matchings (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hV : ∀ x : V, (Finset.univ.erase x).Nonempty) (T : ThreeRegular W) :
    ∃ σ : Fin 3 → Equiv.Perm V, (∀ k, σ k ∈ pairings V) ∧
      (∀ k l : Fin 3, k ≠ l → ∀ x : V, σ k x ≠ σ l x) ∧
      (∀ (x y : V) (a b : Fin 3), W s((x, a), (y, b)) ≠ 0 →
        ∃ k : Fin 3, y = σ k x ∧ a = k ∧ b = k) ∧
      (∀ (x : V) (k : Fin 3), W s((x, k), (σ k x, k)) ≠ 0) ∧
      (∀ (k : Fin 3) (x : V), σ k x = T.partner x k) := by
  classical
  have hdiag : ∀ (x : V) (k a : Fin 3), a ≠ k → W s((x, a), (T.partner x k, k)) = 0 :=
    fun x k a ha => diag_of_three_partners W hone hzero (hV x) (T.partner x)
      (T.col x) (T.dead x) k a ha
  have hne : ∀ (x : V) (k : Fin 3), W s((x, k), (T.partner x k, k)) ≠ 0 := by
    intro x k
    obtain ⟨a, ha⟩ := T.live x k
    by_cases hak : a = k
    · rwa [hak] at ha
    · exact absurd (hdiag x k a hak) ha
  have hsingle : ∀ (x : V) (k a b : Fin 3), (a ≠ k ∨ b ≠ k) →
      W s((x, a), (T.partner x k, b)) = 0 := by
    intro x k a b h
    rcases h with h | h
    · by_cases hb : b = k
      · rw [hb]; exact hdiag x k a h
      · exact T.col x k a b hb
    · exact T.col x k a b h
  have hinv : ∀ (x : V) (k : Fin 3), T.partner (T.partner x k) k = x := by
    intro x k
    have hlive : W s((T.partner x k, k), (x, k)) ≠ 0 := by
      rw [Sym2.eq_swap]; exact hne x k
    obtain ⟨j, hj⟩ : ∃ j : Fin 3, x = T.partner (T.partner x k) j := by
      by_contra h
      push_neg at h
      exact hlive (T.dead (T.partner x k) x (fun e => T.ne_self x k e.symm) h k k)
    have hjk : j = k := by
      by_contra hjk
      have hz := hsingle (T.partner x k) j k k (Or.inl (Ne.symm hjk))
      rw [← hj] at hz
      exact hlive hz
    subst hjk
    exact hj.symm
  refine ⟨fun k => Function.Involutive.toPerm (fun x => T.partner x k) (fun x => hinv x k),
    fun k => ?_, fun k l hkl x => ?_, fun x y a b hab => ?_, fun x k => hne x k,
    fun k x => rfl⟩
  · exact mem_pairings_iff.mpr ⟨fun x => hinv x k, fun x => T.ne_self x k⟩
  · show T.partner x k ≠ T.partner x l
    intro he
    have h1 : W s((x, k), (T.partner x l, k)) ≠ 0 := by rw [← he]; exact hne x k
    exact h1 (hsingle x l k k (Or.inl hkl))
  · by_cases hxy : y = x
    · exfalso
      rw [hxy] at hab
      exact hab (T.no_loop x a b)
    · by_cases hp : ∃ k : Fin 3, y = T.partner x k
      · obtain ⟨k, rfl⟩ := hp
        refine ⟨k, rfl, ?_, ?_⟩
        · by_contra h; exact hab (hsingle x k a b (Or.inl h))
        · by_contra h; exact hab (hsingle x k a b (Or.inr h))
      · push_neg at hp
        exact absurd (T.dead x y hxy hp a b) hab


/-- **Everything but the two remaining facts.**  A three-regular solution admits no
perfect matching mixing two of its three colour classes.

This is the whole argument, assembled: the column lemma makes the blocks diagonal, the
diagonal makes the partner relation symmetric, symmetry makes the colour classes perfect
matchings, and a mixed matching is then alone on its colouring, which the equations refuse.
What is not here is that a solution must be three-regular, and that a mixed matching
exists above four sites. -/
theorem three_regular_no_mixed (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hV : ∀ x : V, (Finset.univ.erase x).Nonempty) (T : ThreeRegular W)
    (τ : Equiv.Perm V) (hτ : τ ∈ pairings V) (c : V → Fin 3)
    (hc : ∀ x : V, τ x = T.partner x (c x))
    (hnm : ¬ Amplitude.Monochromatic c) : False := by
  classical
  obtain ⟨σ, hσ, hdisj, hlive, hedge, hval⟩ := three_matchings W hone hzero hV T
  refine no_mixed_matching W hzero σ hσ hdisj hlive hedge τ hτ c ?_ hnm
  intro x
  rw [hval (c x) x]
  exact hc x

/-- The same, with the mixed matching packaged as a hypothesis --- which is what the
fourth-matching lemma supplies above four sites. -/
theorem no_three_regular (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hV : ∀ x : V, (Finset.univ.erase x).Nonempty) (T : ThreeRegular W)
    (hmixed : ∃ (τ : Equiv.Perm V) (c : V → Fin 3), τ ∈ pairings V ∧
      (∀ x : V, τ x = T.partner x (c x)) ∧ ¬ Amplitude.Monochromatic c) : False := by
  obtain ⟨τ, c, hτ, hc, hnm⟩ := hmixed
  exact three_regular_no_mixed W hone hzero hV T τ hτ c hc hnm


/-! ## Orthogonality localises the witness

The column lemma is the case $S = \emptyset$ of a sharper statement.  Test every partner
outside a set with a colour's basis vector --- legitimate exactly when the covector
annihilates that colour's column there --- and the other two colours die outright, because
each of their products picks up a zero factor from any site outside the set.  What is left
says the colour's witness must lie *inside* the set.
-/

/-- **Orthogonality localises the witness.**  If a covector annihilates one colour's
column at every partner outside a set, and has a non-zero component in that colour, then
some partner inside the set has its contracted row pointing along that colour. -/
theorem witness_of_orthogonal (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {u : V} (S : Finset V) (hS : ∃ w ∈ Finset.univ.erase u, w ∉ S)
    (ρ : Fin 3 → ℂ) (α : Fin 3) (hρ : ρ α ≠ 0)
    (h : ∀ v ∈ Finset.univ.erase u, v ∉ S →
      (∑ a : Fin 3, ρ a * W s((u, a), (v, α))) = 0) :
    ∃ v ∈ Finset.univ.erase u, v ∈ S ∧
      ∀ x : Fin 3 → ℂ,
        (∑ b : Fin 3, x b * (∑ a : Fin 3, ρ a * W s((u, a), (v, b)))) = 0 → x α = 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  -- choose, at each partner inside the set, an annihilator with a live α-component
  have hchoice : ∀ v : V, ∃ xv : Fin 3 → ℂ,
      (v ∈ Finset.univ.erase u → v ∈ S →
        (∑ b : Fin 3, xv b * (∑ a : Fin 3, ρ a * W s((u, a), (v, b)))) = 0 ∧ xv α ≠ 0) := by
    intro v
    by_cases hv : v ∈ Finset.univ.erase u
    · by_cases hvS : v ∈ S
      · obtain ⟨x, hx1, hx2⟩ := hcon v hv hvS
        exact ⟨x, fun _ _ => ⟨hx1, hx2⟩⟩
      · exact ⟨fun _ => 0, fun _ h' => absurd h' hvS⟩
    · exact ⟨fun _ => 0, fun h' _ => absurd h' hv⟩
  choose g hg using hchoice
  set ψ : V → Fin 3 → ℂ :=
    fun w => if w ∈ S then g w else (fun b => if b = α then 1 else 0) with hψ
  have hann : ∀ v ∈ Finset.univ.erase u,
      (∑ b : Fin 3, ψ v b * (∑ a : Fin 3, ρ a * W s((u, a), (v, b)))) = 0 := by
    intro v hv
    by_cases hvS : v ∈ S
    · simp only [hψ, if_pos hvS]
      exact (hg v hv hvS).1
    · simp only [hψ, if_neg hvS]
      rw [Finset.sum_eq_single_of_mem α (Finset.mem_univ α) (fun b _ hb => by simp [hb]),
        if_pos rfl, one_mul]
      exact h v hv hvS
  have key := master_relation W hzero u ρ ψ hann
  obtain ⟨w₀, hw₀, hw₀S⟩ := hS
  have hval : ∀ w : V, w ∉ S → ∀ k : Fin 3, ψ w k = if k = α then 1 else 0 := by
    intro w hw k; simp only [hψ, if_neg hw]
  have hkill : ∀ k : Fin 3, k ≠ α →
      (∏ w ∈ Finset.univ.erase u, ψ w k) = 0 :=
    fun k hk => Finset.prod_eq_zero hw₀ (by rw [hval w₀ hw₀S k]; simp [hk])
  have hpos : (∏ w ∈ Finset.univ.erase u, ψ w α) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr (fun w hw => ?_)
    by_cases hwS : w ∈ S
    · simp only [hψ, if_pos hwS]
      exact (hg w hw hwS).2
    · rw [hval w hwS α]; simp
  rw [Finset.sum_eq_single_of_mem α (Finset.mem_univ α)
    (fun k _ hk => by rw [hkill k hk, mul_zero])] at key
  exact mul_ne_zero (mul_ne_zero hρ (hone α)) hpos key


/-! ## Support: which colourings of a complement can survive

Test the spared relation against *basis* vectors rather than general ones.  Each partner
outside the spared pair is then pinned to one colour, the annihilation condition becomes
the vanishing of a single weight, and the complementary sum collapses from a weighted
average to a single matching sum.  What comes out is a support statement: a colouring of
the complement which places every partner at a colour the row misses, and which is not
constant, has vanishing matching sum.
-/

/-- **Support.**  If the `α`-row read from `u` vanishes at every partner's assigned colour,
and the colouring is not constant `α`, then the complement's matching sum vanishes ---
provided the `α`-row toward the spared partner does not. -/
theorem pmSum_eq_zero_of_row (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {u v : V} (hv : v ≠ u) (α : Fin 3) (c : V → Fin 3)
    (hd : ∀ w ∈ (Finset.univ.erase u).erase v, W s((u, α), (w, c w)) = 0)
    (hne : ∃ w ∈ (Finset.univ.erase u).erase v, c w ≠ α)
    {b : Fin 3} (hrow : W s((u, α), (v, b)) ≠ 0) :
    pmSum W c ((Finset.univ.erase u).erase v) = 0 := by
  classical
  set S : Finset V := (Finset.univ.erase u).erase v with hS
  set ψ : V → Fin 3 → ℂ := fun w x => if x = c w then 1 else 0 with hψ
  -- the annihilation hypothesis, read on basis vectors
  have hann : ∀ w ∈ S, (∑ x : Fin 3, ψ w x * W s((u, α), (w, x))) = 0 := by
    intro w hw
    rw [Finset.sum_eq_single_of_mem (c w) (Finset.mem_univ (c w))
      (fun x _ hx => by simp [hψ, hx])]
    simp only [hψ, if_pos rfl, one_mul]
    exact hd w hw
  -- the complementary sum collapses to one matching sum
  have hK : pairK W u v α α ψ = pmSum W c S := by
    rw [pairK]
    refine Finset.sum_eq_single (Function.update (Function.update c u α) v α) ?_ ?_ |>.trans ?_
    · intro c' _ hc'
      by_cases h1 : c' u = α
      · by_cases h2 : c' v = α
        · -- `c'` agrees with `c` off `{u,v}` or some factor kills it
          by_cases h3 : ∀ w ∈ S, c' w = c w
          · exact absurd (funext fun w => by
              by_cases hwu : w = u
              · rw [hwu, h1]; simp [Function.update_apply, Ne.symm hv]
              · by_cases hwv : w = v
                · rw [hwv, h2]; simp
                · rw [h3 w (Finset.mem_erase.mpr ⟨hwv, Finset.mem_erase.mpr
                    ⟨hwu, Finset.mem_univ w⟩⟩)]
                  simp [Function.update_apply, hwu, hwv]) hc'
          · push_neg at h3
            obtain ⟨w, hw, hwne⟩ := h3
            have : (∏ x ∈ S, ψ x (c' x)) = 0 :=
              Finset.prod_eq_zero hw (by simp [hψ, hwne])
            rw [this]; ring
        · simp [h2]
      · simp [h1]
    · intro h; exact absurd (Finset.mem_univ _) h
    · have e1 : (Function.update (Function.update c u α) v α) u = α := by
        simp [Function.update_apply, Ne.symm hv]
      have e2 : (Function.update (Function.update c u α) v α) v = α := by simp
      have e3 : ∀ w ∈ S, (Function.update (Function.update c u α) v α) w = c w := by
        intro w hw
        have hwv : w ≠ v := (Finset.mem_erase.mp hw).1
        have hwu : w ≠ u := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hw)).1
        simp [Function.update_apply, hwu, hwv]
      have e4 : (∏ w ∈ S, ψ w ((Function.update (Function.update c u α) v α) w)) = 1 := by
        refine Finset.prod_eq_one (fun w hw => ?_)
        rw [e3 w hw]; simp [hψ]
      have e5 : pmSum W (Function.update (Function.update c u α) v α) S = pmSum W c S :=
        pmSum_congr_colour W e3
      rw [e1, e2, e4, e5]
      simp
  -- the right-hand side vanishes because the colouring is not constant
  have hprod : (∏ w ∈ S, ψ w α) = 0 := by
    obtain ⟨w, hw, hwne⟩ := hne
    exact Finset.prod_eq_zero hw (by simp [hψ, Ne.symm hwne])
  have key := row_mul_pairK W hzero hv α (fun x => if x = b then (1:ℂ) else 0) ψ hann
  rw [hK, hprod, mul_zero] at key
  rw [Finset.sum_eq_single_of_mem b (Finset.mem_univ b)
    (fun x _ hx => by simp [hx]), if_pos rfl, one_mul] at key
  exact (mul_eq_zero.mp key).resolve_left hrow


/-- **The disconnected case, closed.**  A three-regular solution whose named matchings
have a disconnected pair is impossible.  What remains of the fourth-matching lemma is the
case where every pair of them generates a connected graph. -/
theorem no_three_regular_of_disconnected (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hV : ∀ x : V, (Finset.univ.erase x).Nonempty) (T : ThreeRegular W)
    {k l : Fin 3} (hkl : k ≠ l) {x₀ y₀ : V}
    (hsep : ¬ Relation.EqvGen
      (fun x y : V => y = T.partner x k ∨ y = T.partner x l) y₀ x₀) : False := by
  classical
  obtain ⟨σ, hσ, hdisj, hlive, hedge, hval⟩ := three_matchings W hone hzero hV T
  have hrel : (fun x y : V => y = σ k x ∨ y = σ l x)
      = (fun x y : V => y = T.partner x k ∨ y = T.partner x l) := by
    funext x y; rw [hval k x, hval l x]
  have hsep' : ¬ Relation.EqvGen (fun x y : V => y = σ k x ∨ y = σ l x) y₀ x₀ := by
    rw [hrel]; exact hsep
  obtain ⟨c, hc, hnc⟩ := mixColouring_of_disconnected σ hkl hsep'
  obtain ⟨τ, hτ, hτv⟩ := perm_of_mixColouring σ hσ c hc
  refine no_three_regular W hone hzero hV T ⟨τ, c, hτ, fun x => ?_, ?_⟩
  · rw [hτv x, hval (c x) x]
  · rintro ⟨j, hj⟩
    exact hnc (fun x y => (hj x).trans (hj y).symm)


/-! ## Span domination

The covector in the spared relation is existentially quantified, and choosing it by
separation rather than genericity gives the sharpest form of the gap.  Write
`z w := W_{uw} (ψ w)` for the column combination a test vector picks out.  If the
complementary sum does not vanish, then the column space of the spared block is contained
in the span of those vectors --- otherwise a covector annihilating the span but not that
column space empties the relation.
-/

/-- Factoring a sum over colourings at two sites at once. -/
theorem sum_colourings_factor₂ (u v : V) (hv : v ≠ u) (F : Fin 3 → Fin 3 → ℂ)
    (H : (V → Fin 3) → ℂ)
    (hHu : ∀ (c : V → Fin 3) (b : Fin 3), H (Function.update c u b) = H c)
    (hHv : ∀ (c : V → Fin 3) (b : Fin 3), H (Function.update c v b) = H c) (k l : Fin 3) :
    (∑ c : V → Fin 3, F (c u) (c v) * H c)
      = (∑ a : Fin 3, ∑ b : Fin 3, F a b)
        * ∑ c : V → Fin 3, (if c u = k then (1:ℂ) else 0) * ((if c v = l then (1:ℂ) else 0)
            * H c) := by
  classical
  -- split off the colour at `u`
  have hsplit : ∀ G : (V → Fin 3) → ℂ,
      (∑ c : V → Fin 3, G c)
        = ∑ a : Fin 3, ∑ c : V → Fin 3, (if c u = a then (1:ℂ) else 0) * G c := by
    intro G
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [← Finset.sum_mul]
    have hone : (∑ a : Fin 3, if c u = a then (1:ℂ) else 0) = 1 := by simp
    rw [hone, one_mul]
  -- for each colour at `u`, factor at `v`
  have hstep : ∀ a : Fin 3,
      (∑ c : V → Fin 3, (if c u = a then (1:ℂ) else 0) * (F (c u) (c v) * H c))
        = (∑ b : Fin 3, F a b)
          * ∑ c : V → Fin 3, (if c v = l then (1:ℂ) else 0)
              * ((if c u = a then (1:ℂ) else 0) * H c) := by
    intro a
    have hrw : ∀ c : V → Fin 3,
        (if c u = a then (1:ℂ) else 0) * (F (c u) (c v) * H c)
          = F a (c v) * ((if c u = a then (1:ℂ) else 0) * H c) := by
      intro c
      by_cases h : c u = a
      · rw [h]; ring
      · simp [h]
    rw [Finset.sum_congr rfl (fun c _ => hrw c)]
    refine sum_colourings_factor v (fun b => F a b)
      (fun c => (if c u = a then (1:ℂ) else 0) * H c) ?_ l
    intro c b
    rw [Function.update_of_ne (Ne.symm hv), hHv]
  -- the inner sums do not depend on the colour at `u`
  have hpin : ∀ a : Fin 3,
      (∑ c : V → Fin 3, (if c v = l then (1:ℂ) else 0) * ((if c u = a then (1:ℂ) else 0) * H c))
        = ∑ c : V → Fin 3, (if c v = l then (1:ℂ) else 0)
            * ((if c u = k then (1:ℂ) else 0) * H c) := by
    intro a
    have hH' : ∀ (c : V → Fin 3) (b : Fin 3),
        (if (Function.update c u b) v = l then (1:ℂ) else 0) * H (Function.update c u b)
          = (if c v = l then (1:ℂ) else 0) * H c := by
      intro c b
      rw [Function.update_of_ne hv, hHu]
    have h1 := sum_colourings_factor u (fun x => if x = a then (1:ℂ) else 0)
      (fun c => (if c v = l then (1:ℂ) else 0) * H c) hH' k
    have h2 := sum_colourings_factor u (fun x => if x = k then (1:ℂ) else 0)
      (fun c => (if c v = l then (1:ℂ) else 0) * H c) hH' k
    have e1 : (∑ x : Fin 3, if x = a then (1:ℂ) else 0) = 1 := by simp
    have e2 : (∑ x : Fin 3, if x = k then (1:ℂ) else 0) = 1 := by simp
    rw [e1, one_mul] at h1
    rw [e2, one_mul] at h2
    calc (∑ c : V → Fin 3, (if c v = l then (1:ℂ) else 0)
            * ((if c u = a then (1:ℂ) else 0) * H c))
        = ∑ c : V → Fin 3, (if c u = a then (1:ℂ) else 0)
            * ((if c v = l then (1:ℂ) else 0) * H c) :=
          Finset.sum_congr rfl (fun c _ => by ring)
      _ = _ := by rw [h1, ← h2]; exact Finset.sum_congr rfl (fun c _ => by ring)
  rw [hsplit (fun c => F (c u) (c v) * H c),
    Finset.sum_congr rfl (fun a _ => (hstep a).trans (by rw [hpin a])),
    ← Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl (fun c _ => by ring)


/-- Colourings weighted by a covector at each of two sites and a test vector elsewhere. -/
noncomputable def genSum (W : Sym2 (V × Fin 3) → ℂ) (u v : V) (ρ χ : Fin 3 → ℂ)
    (ψ : V → Fin 3 → ℂ) : ℂ :=
  ∑ c : V → Fin 3, amplitude W c * ρ (c u) * χ (c v)
    * ∏ w ∈ (Finset.univ.erase u).erase v, ψ w (c w)

/-- Read directly, only the constant colourings survive. -/
theorem genSum_eq (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (u v : V) (hne : Nonempty V) (ρ χ : Fin 3 → ℂ) (ψ : V → Fin 3 → ℂ) :
    genSum W u v ρ χ ψ
      = ∑ k : Fin 3, amplitude W (Amplitude.const (V := V) k) * ρ k * χ k
          * ∏ w ∈ (Finset.univ.erase u).erase v, ψ w k := by
  classical
  have hinj : ∀ k l : Fin 3, Amplitude.const (V := V) k = Amplitude.const (V := V) l → k = l := by
    intro k l h
    obtain ⟨x⟩ := hne
    exact congrFun h x
  have hvan : ∀ c ∈ (Finset.univ : Finset (V → Fin 3)),
      c ∉ Finset.univ.image (fun k : Fin 3 => Amplitude.const (V := V) k) →
      amplitude W c * ρ (c u) * χ (c v)
        * ∏ w ∈ (Finset.univ.erase u).erase v, ψ w (c w) = 0 := by
    intro c _ hc
    have hm : ¬ Amplitude.Monochromatic c := by
      rintro ⟨k, hk⟩
      exact hc (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, (funext hk).symm⟩)
    rw [hzero c hm]; ring
  rw [genSum, ← Finset.sum_subset (Finset.subset_univ _) hvan,
    Finset.sum_image (fun k _ l _ h => hinj k l h)]
  exact Finset.sum_congr rfl (fun k _ => by simp [Amplitude.const])

/-- Read through the expansion, with the residual rows annihilated, only the pairing of the
two covector sites survives. -/
theorem genSum_expand (W : Sym2 (V × Fin 3) → ℂ) {u v : V} (hv : v ≠ u)
    (ρ χ : Fin 3 → ℂ) (ψ : V → Fin 3 → ℂ)
    (hann : ∀ w ∈ (Finset.univ.erase u).erase v,
      (∑ b : Fin 3, ψ w b * (∑ a : Fin 3, ρ a * W s((u, a), (w, b)))) = 0) :
    genSum W u v ρ χ ψ
      = (∑ a : Fin 3, ∑ b : Fin 3, ρ a * χ b * W s((u, a), (v, b)))
        * pairK W u v 0 0 ψ := by
  classical
  have hmemv : v ∈ Finset.univ.erase u := Finset.mem_erase.mpr ⟨hv, Finset.mem_univ v⟩
  have hexp : ∀ c : V → Fin 3, amplitude W c
      = ∑ y ∈ Finset.univ.erase u,
          W s((u, c u), (y, c y)) * pmSum W c ((Finset.univ.erase u).erase y) := by
    intro c
    rw [← pmSum_univ, pmSum_expand W c (Finset.mem_univ u)]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    first
    | rfl
    | (congr 1; simp [Sym2.map_pair_eq, paint])
  have key : ∀ c : V → Fin 3,
      amplitude W c * ρ (c u) * χ (c v) * ∏ w ∈ (Finset.univ.erase u).erase v, ψ w (c w)
        = ∑ y ∈ Finset.univ.erase u,
            W s((u, c u), (y, c y)) * pmSum W c ((Finset.univ.erase u).erase y)
              * ρ (c u) * χ (c v) * ∏ w ∈ (Finset.univ.erase u).erase v, ψ w (c w) := by
    intro c
    rw [hexp c, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  rw [genSum, Finset.sum_congr rfl (fun c _ => key c), Finset.sum_comm,
    Finset.sum_eq_single_of_mem v hmemv ?_]
  · -- the surviving term: factor at both covector sites
    have hrw : ∀ c : V → Fin 3,
        W s((u, c u), (v, c v)) * pmSum W c ((Finset.univ.erase u).erase v)
            * ρ (c u) * χ (c v) * ∏ w ∈ (Finset.univ.erase u).erase v, ψ w (c w)
          = (fun a b => ρ a * χ b * W s((u, a), (v, b))) (c u) (c v)
            * (pmSum W c ((Finset.univ.erase u).erase v)
                * ∏ w ∈ (Finset.univ.erase u).erase v, ψ w (c w)) := by
      intro c; dsimp only; ring
    rw [Finset.sum_congr rfl (fun c _ => hrw c),
      sum_colourings_factor₂ u v hv (fun a b => ρ a * χ b * W s((u, a), (v, b)))
        (fun c => pmSum W c ((Finset.univ.erase u).erase v)
          * ∏ w ∈ (Finset.univ.erase u).erase v, ψ w (c w)) ?_ ?_ 0 0]
    · rw [pairK]
      congr 1
      exact Finset.sum_congr rfl (fun c _ => by ring)
    · intro c b
      rw [pmSum_congr_colour W (c := Function.update c u b) (c' := c)
          (fun w hw => Function.update_of_ne
            (Finset.mem_erase.mp (Finset.mem_of_mem_erase hw)).1 _ _),
        Finset.prod_congr rfl (fun w hw => by
          rw [Function.update_of_ne (Finset.mem_erase.mp (Finset.mem_of_mem_erase hw)).1])]
    · intro c b
      rw [pmSum_congr_colour W (c := Function.update c v b) (c' := c)
          (fun w hw => Function.update_of_ne (Finset.mem_erase.mp hw).1 _ _),
        Finset.prod_congr rfl (fun w hw => by
          rw [Function.update_of_ne (Finset.mem_erase.mp hw).1])]
  · -- every other partner is annihilated
    intro y hy hyv
    have hyu : y ≠ u := (Finset.mem_erase.mp hy).1
    have hyS : y ∈ (Finset.univ.erase u).erase v := Finset.mem_erase.mpr ⟨hyv, hy⟩
    have hrw : ∀ c : V → Fin 3,
        W s((u, c u), (y, c y)) * pmSum W c ((Finset.univ.erase u).erase y)
            * ρ (c u) * χ (c v) * ∏ w ∈ (Finset.univ.erase u).erase v, ψ w (c w)
          = (fun a b => ρ a * ψ y b * W s((u, a), (y, b))) (c u) (c y)
            * (χ (c v) * pmSum W c ((Finset.univ.erase u).erase y)
                * ∏ w ∈ ((Finset.univ.erase u).erase v).erase y, ψ w (c w)) := by
      intro c
      rw [← Finset.mul_prod_erase _ _ hyS]
      dsimp only; ring
    rw [Finset.sum_congr rfl (fun c _ => hrw c),
      sum_colourings_factor₂ u y hyu (fun a b => ρ a * ψ y b * W s((u, a), (y, b)))
        (fun c => χ (c v) * pmSum W c ((Finset.univ.erase u).erase y)
          * ∏ w ∈ ((Finset.univ.erase u).erase v).erase y, ψ w (c w)) ?_ ?_ 0 0]
    · have hz : (∑ a : Fin 3, ∑ b : Fin 3, ρ a * ψ y b * W s((u, a), (y, b))) = 0 := by
        rw [Finset.sum_comm, ← hann y hyS]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun a _ => by ring)
      rw [hz, zero_mul]
    · intro c b
      rw [Function.update_of_ne hv,
        pmSum_congr_colour W (c := Function.update c u b) (c' := c)
          (fun w hw => Function.update_of_ne
            (Finset.mem_erase.mp (Finset.mem_of_mem_erase hw)).1 _ _),
        Finset.prod_congr rfl (fun w hw => by
          rw [Function.update_of_ne (Finset.mem_erase.mp
            (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hw))).1])]
    · intro c b
      rw [Function.update_of_ne (Ne.symm hyv),
        pmSum_congr_colour W (c := Function.update c y b) (c' := c)
          (fun w hw => Function.update_of_ne (Finset.mem_erase.mp hw).1 _ _),
        Finset.prod_congr rfl (fun w hw => by
          rw [Function.update_of_ne (Finset.mem_erase.mp hw).1])]


/-- **Span domination.**  In the surviving case, if the complementary sum does not vanish
then the column image of the spared block lies in the span of the columns the test vectors
pick out at the remaining partners.

The proof is separation, not genericity: a column outside that span admits a functional
annihilating the span but not it, and the covector read off that functional empties the
relation.  The three named partners cost nothing --- for each colour, either the covector
vanishes there or the annihilation forces the test vector to. -/
theorem mem_span_of_pairK_ne_zero (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {u v : V} (hv : v ≠ u) (hne : Nonempty V)
    (wn : Fin 3 → V) (hwS : ∀ k, wn k ∈ (Finset.univ.erase u).erase v)
    (hsingle : ∀ k a b : Fin 3, (a ≠ k ∨ b ≠ k) → W s((u, a), (wn k, b)) = 0)
    (hlive : ∀ k : Fin 3, W s((u, k), (wn k, k)) ≠ 0)
    (ψ : V → Fin 3 → ℂ) (hK : pairK W u v 0 0 ψ ≠ 0) (x : Fin 3 → ℂ) :
    (fun a : Fin 3 => ∑ b : Fin 3, W s((u, a), (v, b)) * x b)
      ∈ Submodule.span ℂ
        ((fun w : V => (fun a : Fin 3 => ∑ b : Fin 3, W s((u, a), (w, b)) * ψ w b))
          '' ↑((Finset.univ.erase u).erase v)) := by
  classical
  by_contra hnot
  obtain ⟨f, hfy, hfker⟩ := Submodule.exists_le_ker_of_notMem hnot
  set ρ : Fin 3 → ℂ := fun a => f (fun j => if a = j then (1:ℂ) else 0) with hρ
  have hf : ∀ z : Fin 3 → ℂ, f z = ∑ a : Fin 3, z a * ρ a := by
    intro z
    rw [LinearMap.pi_apply_eq_sum_univ f z]
    exact Finset.sum_congr rfl (fun a _ => by rw [smul_eq_mul])
  have hspan : ∀ w ∈ (Finset.univ.erase u).erase v,
      (∑ a : Fin 3, (∑ b : Fin 3, W s((u, a), (w, b)) * ψ w b) * ρ a) = 0 := by
    intro w hw
    have hmem : (fun a : Fin 3 => ∑ b : Fin 3, W s((u, a), (w, b)) * ψ w b)
        ∈ Submodule.span ℂ
          ((fun w : V => (fun a : Fin 3 => ∑ b : Fin 3, W s((u, a), (w, b)) * ψ w b))
            '' ↑((Finset.univ.erase u).erase v)) :=
      Submodule.subset_span ⟨w, hw, rfl⟩
    have := hfker hmem
    rw [LinearMap.mem_ker, hf] at this
    exact this
  have hann : ∀ w ∈ (Finset.univ.erase u).erase v,
      (∑ b : Fin 3, ψ w b * (∑ a : Fin 3, ρ a * W s((u, a), (w, b)))) = 0 := by
    intro w hw
    rw [← hspan w hw]
    calc (∑ b : Fin 3, ψ w b * (∑ a : Fin 3, ρ a * W s((u, a), (w, b))))
        = ∑ b : Fin 3, ∑ a : Fin 3, ψ w b * (ρ a * W s((u, a), (w, b))) :=
          Finset.sum_congr rfl (fun b _ => Finset.mul_sum _ _ _)
      _ = ∑ a : Fin 3, ∑ b : Fin 3, ψ w b * (ρ a * W s((u, a), (w, b))) := Finset.sum_comm
      _ = ∑ a : Fin 3, (∑ b : Fin 3, W s((u, a), (w, b)) * ψ w b) * ρ a := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl (fun b _ => by ring)
  -- each direct term vanishes
  have hkill : ∀ k : Fin 3, ρ k * ψ (wn k) k = 0 := by
    intro k
    have h0 := hspan (wn k) (hwS k)
    have hz : ∀ a : Fin 3, (∑ b : Fin 3, W s((u, a), (wn k, b)) * ψ (wn k) b)
        = (if a = k then W s((u, k), (wn k, k)) * ψ (wn k) k else 0) := by
      intro a
      rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ k)
        (fun b _ hb => by rw [hsingle k a b (Or.inr hb), zero_mul])]
      by_cases hak : a = k
      · rw [hak, if_pos rfl]
      · rw [if_neg hak, hsingle k a k (Or.inl hak), zero_mul]
    rw [Finset.sum_congr rfl (fun a _ => by rw [hz a]),
      Finset.sum_eq_single_of_mem k (Finset.mem_univ k)
        (fun a _ ha => by rw [if_neg ha, zero_mul]), if_pos rfl] at h0
    have h1 : ψ (wn k) k * ρ k = 0 := by
      rw [mul_assoc] at h0
      exact (mul_eq_zero.mp h0).resolve_left (hlive k)
    rw [mul_comm]; exact h1
  -- the direct reading vanishes
  have hgs : genSum W u v ρ x ψ = 0 := by
    rw [genSum_eq W hzero u v hne ρ x ψ]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [← Finset.mul_prod_erase _ _ (hwS k)]
    calc amplitude W (Amplitude.const (V := V) k) * ρ k * x k
          * (ψ (wn k) k * ∏ w ∈ ((Finset.univ.erase u).erase v).erase (wn k), ψ w k)
        = (amplitude W (Amplitude.const (V := V) k) * x k
            * ∏ w ∈ ((Finset.univ.erase u).erase v).erase (wn k), ψ w k)
          * (ρ k * ψ (wn k) k) := by ring
      _ = 0 := by rw [hkill k, mul_zero]
  rw [genSum_expand W hv ρ x ψ hann] at hgs
  have hcoef : (∑ a : Fin 3, ∑ b : Fin 3, ρ a * x b * W s((u, a), (v, b))) = 0 :=
    (mul_eq_zero.mp hgs).resolve_right hK
  refine hfy ?_
  rw [hf, ← hcoef]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun b _ => by ring)


/-- A named partner contributes nothing to the span once its test vector sits off its own
colour: its block is a single entry, so the column it picks out is a multiple of that
vector's component there. -/
theorem named_column_eq_zero (W : Sym2 (V × Fin 3) → ℂ) {u : V} (wn : Fin 3 → V)
    (hsingle : ∀ k a b : Fin 3, (a ≠ k ∨ b ≠ k) → W s((u, a), (wn k, b)) = 0)
    (ψ : V → Fin 3 → ℂ) (k : Fin 3) (hψ : ψ (wn k) k = 0) :
    (fun a : Fin 3 => ∑ b : Fin 3, W s((u, a), (wn k, b)) * ψ (wn k) b) = 0 := by
  classical
  funext a
  rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ k)
    (fun b _ hb => by rw [hsingle k a b (Or.inr hb), zero_mul]), hψ, mul_zero]
  rfl


/-- On basis test vectors the complementary sum collapses to a single matching sum. -/
theorem pairK_basis (W : Sym2 (V × Fin 3) → ℂ) {u v : V} (hv : v ≠ u) (c : V → Fin 3) :
    pairK W u v 0 0 (fun w x => if x = c w then (1:ℂ) else 0)
      = pmSum W c ((Finset.univ.erase u).erase v) := by
  classical
  set S : Finset V := (Finset.univ.erase u).erase v with hS
  set ψ : V → Fin 3 → ℂ := fun w x => if x = c w then 1 else 0 with hψ
  rw [pairK]
  refine (Finset.sum_eq_single (Function.update (Function.update c u 0) v 0) ?_ ?_).trans ?_
  · intro c' _ hc'
    by_cases h1 : c' u = 0
    · by_cases h2 : c' v = 0
      · by_cases h3 : ∀ w ∈ S, c' w = c w
        · exact absurd (funext fun w => by
            by_cases hwu : w = u
            · rw [hwu, h1]; simp [Function.update_apply, Ne.symm hv]
            · by_cases hwv : w = v
              · rw [hwv, h2]; simp
              · rw [h3 w (Finset.mem_erase.mpr ⟨hwv, Finset.mem_erase.mpr
                  ⟨hwu, Finset.mem_univ w⟩⟩)]
                simp [Function.update_apply, hwu, hwv]) hc'
        · push_neg at h3
          obtain ⟨w, hw, hwne⟩ := h3
          have : (∏ z ∈ S, ψ z (c' z)) = 0 := Finset.prod_eq_zero hw (by simp [hψ, hwne])
          rw [this]; ring
      · simp [h2]
    · simp [h1]
  · intro h; exact absurd (Finset.mem_univ _) h
  · have e1 : (Function.update (Function.update c u 0) v 0) u = 0 := by
      simp [Function.update_apply, Ne.symm hv]
    have e2 : (Function.update (Function.update c u 0) v 0) v = 0 := by simp
    have e3 : ∀ w ∈ S, (Function.update (Function.update c u 0) v 0) w = c w := by
      intro w hw
      have hwv : w ≠ v := (Finset.mem_erase.mp hw).1
      have hwu : w ≠ u := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hw)).1
      simp [Function.update_apply, hwu, hwv]
    have e4 : (∏ w ∈ S, ψ w ((Function.update (Function.update c u 0) v 0) w)) = 1 :=
      Finset.prod_eq_one (fun w hw => by rw [e3 w hw]; simp [hψ])
    have e5 : pmSum W (Function.update (Function.update c u 0) v 0) S = pmSum W c S :=
      pmSum_congr_colour W e3
    rw [e1, e2, e4, e5]
    simp

/-- **Span domination, on colourings.**  If a colouring of the complement has non-vanishing
matching sum, the column image of the spared block lies in the span of the columns that
colouring selects at the remaining partners. -/
theorem mem_span_of_pmSum_ne_zero (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {u v : V} (hv : v ≠ u) (hne : Nonempty V)
    (wn : Fin 3 → V) (hwS : ∀ k, wn k ∈ (Finset.univ.erase u).erase v)
    (hsingle : ∀ k a b : Fin 3, (a ≠ k ∨ b ≠ k) → W s((u, a), (wn k, b)) = 0)
    (hlive : ∀ k : Fin 3, W s((u, k), (wn k, k)) ≠ 0)
    (c : V → Fin 3) (hc : pmSum W c ((Finset.univ.erase u).erase v) ≠ 0) (x : Fin 3 → ℂ) :
    (fun a : Fin 3 => ∑ b : Fin 3, W s((u, a), (v, b)) * x b)
      ∈ Submodule.span ℂ
        ((fun w : V => (fun a : Fin 3 => W s((u, a), (w, c w))))
          '' ↑((Finset.univ.erase u).erase v)) := by
  classical
  set ψ : V → Fin 3 → ℂ := fun w y => if y = c w then (1:ℂ) else 0 with hψ
  have hK : pairK W u v 0 0 ψ ≠ 0 := by rw [pairK_basis W hv c]; exact hc
  have hcol : ∀ w : V, (fun a : Fin 3 => ∑ b : Fin 3, W s((u, a), (w, b)) * ψ w b)
      = (fun a : Fin 3 => W s((u, a), (w, c w))) := by
    intro w
    funext a
    rw [Finset.sum_eq_single_of_mem (c w) (Finset.mem_univ (c w))
      (fun b _ hb => by simp [hψ, hb])]
    simp [hψ]
  have := mem_span_of_pairK_ne_zero W hzero hv hne wn hwS hsingle hlive ψ hK x
  simpa only [hcol] using this


/-- **The live rows are pinned.**  If `u`'s only extra partner is `v`, then any colouring
of the complement with non-vanishing matching sum places the named partner of each *live
row* of the spared block on that very colour.

So the live rows of an extra block are contained in the colours that every surviving
colouring pins --- and since an extra block has at least two live rows, at least two named
partners are pinned by every surviving colouring at once. -/
theorem named_on_colour_of_live_row (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {u v : V} (hv : v ≠ u) (hne : Nonempty V)
    (wn : Fin 3 → V) (hwS : ∀ k, wn k ∈ (Finset.univ.erase u).erase v)
    (hsingle : ∀ k a b : Fin 3, (a ≠ k ∨ b ≠ k) → W s((u, a), (wn k, b)) = 0)
    (hlive : ∀ k : Fin 3, W s((u, k), (wn k, k)) ≠ 0)
    (hlone : ∀ w ∈ (Finset.univ.erase u).erase v, (∀ k, w ≠ wn k) →
      ∀ a b : Fin 3, W s((u, a), (w, b)) = 0)
    (c : V → Fin 3) (hc : pmSum W c ((Finset.univ.erase u).erase v) ≠ 0)
    (a b : Fin 3) (hab : W s((u, a), (v, b)) ≠ 0) :
    c (wn a) = a := by
  classical
  by_contra hcna
  -- every selected column misses the `a`-coordinate
  have hgen : ∀ y ∈ (fun w : V => (fun a' : Fin 3 => W s((u, a'), (w, c w))))
      '' ↑((Finset.univ.erase u).erase v),
      y ∈ LinearMap.ker (LinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) a) := by
    rintro y ⟨w, hw, rfl⟩
    rw [LinearMap.mem_ker]
    show W s((u, a), (w, c w)) = 0
    by_cases hk : ∃ k, w = wn k
    · obtain ⟨k, rfl⟩ := hk
      by_cases hak : a = k
      · refine hsingle k a (c (wn k)) (Or.inr ?_)
        rw [← hak]
        exact hcna
      · exact hsingle k a (c (wn k)) (Or.inl hak)
    · push_neg at hk
      exact hlone w hw hk a (c w)
  have hle : Submodule.span ℂ ((fun w : V => (fun a' : Fin 3 => W s((u, a'), (w, c w))))
      '' ↑((Finset.univ.erase u).erase v))
      ≤ LinearMap.ker (LinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) a) :=
    Submodule.span_le.mpr hgen
  have hmem := mem_span_of_pmSum_ne_zero W hzero hv hne wn hwS hsingle hlive c hc
    (fun y => if y = b then (1:ℂ) else 0)
  have := hle hmem
  rw [LinearMap.mem_ker] at this
  have hval : (fun a' : Fin 3 => ∑ y : Fin 3, W s((u, a'), (v, y))
      * (if y = b then (1:ℂ) else 0)) a = W s((u, a), (v, b)) := by
    show (∑ y : Fin 3, W s((u, a), (v, y)) * (if y = b then (1:ℂ) else 0))
      = W s((u, a), (v, b))
    rw [Finset.sum_eq_single_of_mem b (Finset.mem_univ b)
      (fun y _ hy => by simp [hy])]
    simp
  exact hab (hval ▸ this)

end PurePartner

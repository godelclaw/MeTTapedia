import Mathlib
import Amplitude
import MatchingSum
import FourVertexRank

/-!
# What a fully degenerate site forces

Fix a site `p`.  For each other site `x` one may ask whether the remaining sites,
with `p` and `x` removed, still carry a non-vanishing matching sum on some
non-constant colouring.  When the answer is no — every non-constant colouring of the
complement of `{p, x}` has vanishing matching sum, and this for *every* `x` — the site
is *fully degenerate*.

This file determines what that costs.  The answer is a rigid three-fold structure.
Write `mu p k v` for the matching sum of the constant colouring `k` on the complement
of `{p, v}`.  Expanding the amplitude along `p` shows that these numbers solve a
linear system whose right-hand side is the monochromatic amplitude, so for each colour
some partner has `mu p k v ≠ 0`.  Degeneracy then turns each such partner into a
*pure* one: the edge from `p` to it carries no colour but `k` at the far end.  Two
different colours cannot share a partner, because purity in two colours kills the edge
outright.  So the three colours select three distinct partners, each joined to `p` by
an edge that is monochromatic at its far end.

The four-vertex solution has exactly this shape, and it is the reason it exists: its
three matchings wear three different colours, and site `0` meets the other three sites
along three edges, one per colour.  What is proved here is that no other shape is
available to a fully degenerate site, on any number of vertices.

Nothing here assumes the number of sites, and nothing here assumes a solution exists.
The hypotheses are the defining equations plus degeneracy; the conclusion is a
structure that any such configuration must display.
-/

namespace FanStructure

open Amplitude MatchingSum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The matching sum of the constant colouring `k` on the sites other than `p` and `v`.

These are the coefficients the amplitude expansion along `p` runs over. -/
noncomputable def mu (W : Sym2 (V × Fin 3) → ℂ) (p : V) (k : Fin 3) (v : V) : ℂ :=
  pmSum W (Amplitude.const k) ((Finset.univ.erase p).erase v)

/-- **Full degeneracy at a site.**  Removing `p` and any one further site leaves a
configuration whose non-constant matching sums all vanish. -/
def Degenerate (W : Sym2 (V × Fin 3) → ℂ) (p : V) : Prop :=
  ∀ x ∈ Finset.univ.erase p, ∀ c : V → Fin 3,
    ∀ u ∈ (Finset.univ.erase p).erase x, ∀ w ∈ (Finset.univ.erase p).erase x,
      c u ≠ c w → pmSum W c ((Finset.univ.erase p).erase x) = 0

/-- Expanding the amplitude along `p`, with the constant colouring `k` elsewhere and
the colour `α` at `p`, produces the linear system solved by `mu p k`. -/
theorem site_system (W : Sym2 (V × Fin 3) → ℂ) (p : V) (k α : Fin 3) :
    (∑ v ∈ Finset.univ.erase p, W s((p, α), (v, k)) * mu W p k v)
      = amplitude W (Function.update (Amplitude.const (V := V) k) p α) := by
  classical
  set c : V → Fin 3 := Function.update (Amplitude.const (V := V) k) p α with hc
  have hcp : c p = α := by simp [hc]
  have hcv : ∀ v : V, v ≠ p → c v = k := by
    intro v hv; simp [hc, hv, Amplitude.const]
  rw [← pmSum_univ, pmSum_expand W c (Finset.mem_univ p)]
  refine Finset.sum_congr rfl (fun v hv => ?_)
  have hvp : v ≠ p := (Finset.mem_erase.mp hv).1
  have hedge : W (Sym2.map (paint c) s(p, v)) = W s((p, α), (v, k)) := by
    simp [Sym2.map_pair_eq, paint, hcp, hcv v hvp]
  rw [hedge]
  congr 1
  refine pmSum_congr_colour W (fun x hx => ?_)
  exact (hcv x (Finset.mem_erase.mp (Finset.mem_of_mem_erase hx)).1).symm

/-- For each colour some partner of `p` carries both a live edge in that colour and a
non-vanishing complementary matching sum.  This is the only place the defining
equations are used positively rather than as vanishing conditions. -/
theorem exists_partner (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const (V := V) k) ≠ 0)
    (p : V) (k : Fin 3) :
    ∃ v ∈ Finset.univ.erase p, W s((p, k), (v, k)) ≠ 0 ∧ mu W p k v ≠ 0 := by
  classical
  have hsys := site_system W p k k
  have hupd : Function.update (Amplitude.const (V := V) k) p k
      = Amplitude.const (V := V) k := by
    funext v; by_cases h : v = p <;> simp [Function.update_apply, h, Amplitude.const]
  rw [hupd] at hsys
  by_contra hcon
  push_neg at hcon
  have : (∑ v ∈ Finset.univ.erase p, W s((p, k), (v, k)) * mu W p k v) = 0 := by
    refine Finset.sum_eq_zero (fun v hv => ?_)
    rcases eq_or_ne (W s((p, k), (v, k))) 0 with h | h
    · rw [h, zero_mul]
    · rw [hcon v hv h, mul_zero]
  rw [this] at hsys
  exact hone k hsys.symm

/-- **Purity.**  At a fully degenerate site, a partner whose complementary sum is
non-zero in colour `k` is joined to `p` by an edge carrying no other colour at its far
end.  The proof isolates a single term of the expansion: every other partner sees a
non-constant colouring, which degeneracy annihilates. -/
theorem pure_of_mu_ne_zero (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {p : V} (hdeg : Degenerate W p)
    {x : V} (hx : x ≠ p) (hcard : 4 ≤ Fintype.card V)
    {k : Fin 3} (hmu : mu W p k x ≠ 0) (α : Fin 3) {β : Fin 3} (hβ : β ≠ k) :
    W s((p, α), (x, β)) = 0 := by
  classical
  -- two spare sites, both distinct from `p` and `x`, both wearing colour `k`
  obtain ⟨y, hymem, z, hzmem, hyz⟩ :
      ∃ y ∈ (Finset.univ.erase p).erase x, ∃ z ∈ (Finset.univ.erase p).erase x, y ≠ z := by
    refine Finset.one_lt_card.mp ?_
    have h1 : (Finset.univ.erase p).card = Fintype.card V - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ]
    have h2 : ((Finset.univ.erase p).erase x).card = Fintype.card V - 2 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hx, Finset.mem_univ x⟩), h1]
      omega
    omega
  have hyp : y ≠ p := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hymem)).1
  have hyx : y ≠ x := (Finset.mem_erase.mp hymem).1
  have hzp : z ≠ p := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hzmem)).1
  have hzx : z ≠ x := (Finset.mem_erase.mp hzmem).1
  set c : V → Fin 3 :=
    Function.update (Function.update (Amplitude.const (V := V) k) p α) x β with hc
  have hcp : c p = α := by simp [hc, Function.update_apply, Ne.symm hx, Amplitude.const]
  have hcx : c x = β := by simp [hc, Amplitude.const]
  have hcv : ∀ v : V, v ≠ p → v ≠ x → c v = k := by
    intro v h1 h2; simp [hc, Function.update_apply, h1, h2, Amplitude.const]
  have hnm : ¬ Amplitude.Monochromatic c := by
    rintro ⟨j, hj⟩
    have h1 : β = j := by rw [← hcx, hj x]
    have h2 : k = j := by rw [← hcv y hyp hyx, hj y]
    exact hβ (h1.trans h2.symm)
  have hamp : amplitude W c = 0 := hzero c hnm
  rw [← pmSum_univ, pmSum_expand W c (Finset.mem_univ p)] at hamp
  -- every partner other than `x` sees a non-constant colouring, which degeneracy kills
  have hsplit : ∀ v ∈ Finset.univ.erase p, v ≠ x →
      W (Sym2.map (paint c) s(p, v)) * pmSum W c ((Finset.univ.erase p).erase v) = 0 := by
    intro v hv hvx
    have hxmem : x ∈ (Finset.univ.erase p).erase v :=
      Finset.mem_erase.mpr ⟨Ne.symm hvx, Finset.mem_erase.mpr ⟨hx, Finset.mem_univ x⟩⟩
    -- at least one spare site survives the removal of `v`
    obtain ⟨w, hwmem, hwp, hwx⟩ : ∃ w : V, w ∈ (Finset.univ.erase p).erase v ∧ w ≠ p ∧ w ≠ x := by
      rcases eq_or_ne y v with rfl | hyv
      · exact ⟨z, Finset.mem_erase.mpr ⟨Ne.symm hyz, Finset.mem_erase.mpr
          ⟨hzp, Finset.mem_univ z⟩⟩, hzp, hzx⟩
      · exact ⟨y, Finset.mem_erase.mpr ⟨hyv, Finset.mem_erase.mpr
          ⟨hyp, Finset.mem_univ y⟩⟩, hyp, hyx⟩
    rw [hdeg v hv c x hxmem w hwmem (by rw [hcx, hcv w hwp hwx]; exact hβ), mul_zero]
  rw [Finset.sum_eq_single_of_mem x (Finset.mem_erase.mpr ⟨hx, Finset.mem_univ x⟩)
      (fun v hv hvx => hsplit v hv hvx)] at hamp
  have hedge : W (Sym2.map (paint c) s(p, x)) = W s((p, α), (x, β)) := by
    simp [Sym2.map_pair_eq, paint, hcp, hcx]
  have hrest : pmSum W c ((Finset.univ.erase p).erase x) = mu W p k x := by
    refine pmSum_congr_colour W (fun t ht => ?_)
    exact hcv t (Finset.mem_erase.mp (Finset.mem_of_mem_erase ht)).1
      (Finset.mem_erase.mp ht).1
  rw [hedge, hrest] at hamp
  exact (mul_eq_zero.mp hamp).resolve_right hmu

/-- **A live edge admits only one colour of support.**  If the edge from `p` to `x`
carries any weight at all, then at most one constant colouring survives on the
complement of `{p, x}`: two would make the edge pure in two colours at once, which
leaves it no colour to carry. -/
theorem live_supp_subsingleton (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {p : V} (hdeg : Degenerate W p) {x : V} (hx : x ≠ p) (hcard : 4 ≤ Fintype.card V)
    (hlive : ∃ α β : Fin 3, W s((p, α), (x, β)) ≠ 0)
    {k k' : Fin 3} (hk : mu W p k x ≠ 0) (hk' : mu W p k' x ≠ 0) : k = k' := by
  by_contra hne
  obtain ⟨α, β, hβ⟩ := hlive
  rcases eq_or_ne β k with hbk | hbk
  · exact hβ (pure_of_mu_ne_zero W hzero hdeg hx hcard hk' α (by rw [hbk]; exact hne))
  · exact hβ (pure_of_mu_ne_zero W hzero hdeg hx hcard hk α hbk)

/-- **The fan.**  A fully degenerate site selects three *distinct* partners, one per
colour, joined to it by edges that carry that colour alone at the far end.

This is the shape of the four-vertex solution, and the content of the theorem is that
it is the only shape available, whatever the number of sites. -/
theorem fan (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const (V := V) k) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {p : V} (hdeg : Degenerate W p) (hcard : 4 ≤ Fintype.card V) :
    ∃ v : Fin 3 → V, Function.Injective v ∧ (∀ k, v k ≠ p) ∧
      (∀ k, W s((p, k), (v k, k)) ≠ 0) ∧ (∀ k, mu W p k (v k) ≠ 0) ∧
      (∀ k, ∀ α β : Fin 3, β ≠ k → W s((p, α), (v k, β)) = 0) := by
  classical
  choose v hmem hlive hmu using fun k : Fin 3 => exists_partner W hone p k
  have hne : ∀ k, v k ≠ p := fun k => (Finset.mem_erase.mp (hmem k)).1
  refine ⟨v, ?_, hne, hlive, hmu, ?_⟩
  · intro k k' hkk'
    refine live_supp_subsingleton W hzero hdeg (hne k) hcard ⟨k, k, hlive k⟩ (hmu k) ?_
    rw [hkk']; exact hmu k'
  · intro k α β hβ
    exact pure_of_mu_ne_zero W hzero hdeg (hne k) hcard (hmu k) α hβ

/-- **Descent.**  A fully degenerate site whose complement retains all three constant
colourings hands back a solution on two fewer sites. -/
theorem isGHZ_of_degenerate (W : Sym2 (V × Fin 3) → ℂ)
    {p x : V} (hx : x ≠ p) (hdeg : Degenerate W p)
    [Nonempty ↥((Finset.univ.erase p).erase x)]
    (hmu : ∀ k : Fin 3, mu W p k x ≠ 0) :
    KrennGu.IsGHZ (restrictW W ((Finset.univ.erase p).erase x)) :=
  FourVertexRank.isGHZ_restrict W _
    (fun c hc => by
      obtain ⟨u, hu, w, hw, huw⟩ := hc
      exact hdeg x (Finset.mem_erase.mpr ⟨hx, Finset.mem_univ x⟩) c u hu w hw huw)
    hmu

/-- **Eight sites: every neighbour of a degenerate site has deficient support.**
Full support would produce a six-site solution, and there is none.  So the descent
above never fires at eight sites — which is exactly why the six-vertex case being
settled bites here. -/
theorem exists_mu_eq_zero (W : Sym2 (V × Fin 3) → ℂ)
    (hb : ¬ KrennGu.Solvable 3) (hcard : Fintype.card V = 8)
    {p x : V} (hx : x ≠ p) (hdeg : Degenerate W p) :
    ∃ k : Fin 3, mu W p k x = 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  set S : Finset V := (Finset.univ.erase p).erase x with hS
  have hcardS : Fintype.card ↥S = 2 * 3 := by
    rw [Fintype.card_coe, hS,
      Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hx, Finset.mem_univ x⟩),
      Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ, hcard]
  have hne : Nonempty ↥S := by
    rw [← Fintype.card_pos_iff, hcardS]; omega
  exact FourVertexRank.no_six_subsystem W hb S hcardS
    (fun c hc => by
      obtain ⟨u, hu, w, hw, huw⟩ := hc
      exact hdeg x (Finset.mem_erase.mpr ⟨hx, Finset.mem_univ x⟩) c u hu w hw huw)
    (fun k => hcon k)


/-- An edge is **inert** when the sites other than its two ends carry no matching sum
whatever: every colouring of the complement has vanishing sum.  Such an edge appears
in no amplitude, because every term containing it is multiplied by one of these sums.
-/
def Inert (W : Sym2 (V × Fin 3) → ℂ) (p x : V) : Prop :=
  ∀ c : V → Fin 3, pmSum W c ((Finset.univ.erase p).erase x) = 0

/-- The complementary sums are symmetric in the two sites: the set they run over is
the same one. -/
theorem mu_comm (W : Sym2 (V × Fin 3) → ℂ) (p x : V) (k : Fin 3) :
    mu W p k x = mu W x k p := by
  rw [mu, mu, Finset.erase_right_comm]

/-- **Every edge that matters is monochromatic.**

If every site is fully degenerate then a live edge which is not inert carries a single
colour at *both* ends.  One end is fixed by purity at `p`; the symmetry of the
complementary sums transports the hypothesis to `x`, and purity there fixes the other.

This turns a hypothesis about matching sums into a statement about the weights
themselves: the configuration is carried by three monochromatic spanning subgraphs,
one per colour, with no edge shared between the colours in the sense of mixing them at
its two ends. -/
theorem edge_monochromatic (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hdeg : ∀ q : V, Degenerate W q) (hcard : 4 ≤ Fintype.card V)
    {p x : V} (hx : x ≠ p) (hinert : ¬ Inert W p x)
    {α β : Fin 3} (hlive : W s((p, α), (x, β)) ≠ 0) : α = β := by
  classical
  -- some colouring of the complement survives; degeneracy makes it constant
  obtain ⟨c, hc⟩ : ∃ c : V → Fin 3, pmSum W c ((Finset.univ.erase p).erase x) ≠ 0 := by
    by_contra h; push_neg at h; exact hinert h
  have hSne : ((Finset.univ.erase p).erase x).Nonempty := by
    rw [← Finset.card_pos,
      Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hx, Finset.mem_univ x⟩),
      Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ]
    omega
  obtain ⟨u₀, hu₀⟩ := hSne
  have hconst : ∀ w ∈ (Finset.univ.erase p).erase x, c w = c u₀ := by
    intro w hw
    by_contra hne
    exact hc (hdeg p x (Finset.mem_erase.mpr ⟨hx, Finset.mem_univ x⟩) c w hw u₀ hu₀ hne)
  set k : Fin 3 := c u₀ with hk
  have hmu : mu W p k x ≠ 0 := by
    rw [mu, ← pmSum_congr_colour W (c := c) (c' := Amplitude.const k) hconst]
    exact hc
  -- purity at `p` fixes the far end
  have hβ : β = k := by
    by_contra hbk
    exact hlive (pure_of_mu_ne_zero W hzero (hdeg p) hx hcard hmu α hbk)
  -- the same hypothesis at `x`, by symmetry of the complementary sums
  have hmu' : mu W x k p ≠ 0 := by rw [← mu_comm]; exact hmu
  have hlive' : W s((x, β), (p, α)) ≠ 0 := by rwa [Sym2.eq_swap]
  have hα : α = k := by
    by_contra hak
    exact hlive' (pure_of_mu_ne_zero W hzero (hdeg x) (Ne.symm hx) hcard hmu' β hak)
  rw [hα, hβ]


/-- **A colour for each edge that matters.**  Sharpening the previous theorem: the
block of a live, non-inert pair is not merely diagonal, it has a single entry.  Purity
at `p` kills every column but one, purity at `x` kills every row but one, and the two
survivors are the same colour.

So a configuration all of whose sites are degenerate is a properly colour-labelled
graph: each pair that participates in any amplitude carries exactly one colour, at
both of its ends. -/
theorem edge_single_colour (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hdeg : ∀ q : V, Degenerate W q) (hcard : 4 ≤ Fintype.card V)
    {p x : V} (hx : x ≠ p) (hinert : ¬ Inert W p x) :
    ∃ k : Fin 3, ∀ α β : Fin 3, (α ≠ k ∨ β ≠ k) → W s((p, α), (x, β)) = 0 := by
  classical
  obtain ⟨c, hc⟩ : ∃ c : V → Fin 3, pmSum W c ((Finset.univ.erase p).erase x) ≠ 0 := by
    by_contra h; push_neg at h; exact hinert h
  have hSne : ((Finset.univ.erase p).erase x).Nonempty := by
    rw [← Finset.card_pos,
      Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hx, Finset.mem_univ x⟩),
      Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ]
    omega
  obtain ⟨u₀, hu₀⟩ := hSne
  have hconst : ∀ w ∈ (Finset.univ.erase p).erase x, c w = c u₀ := by
    intro w hw
    by_contra hne
    exact hc (hdeg p x (Finset.mem_erase.mpr ⟨hx, Finset.mem_univ x⟩) c w hw u₀ hu₀ hne)
  refine ⟨c u₀, fun α β hαβ => ?_⟩
  have hmu : mu W p (c u₀) x ≠ 0 := by
    rw [mu, ← pmSum_congr_colour W (c := c) (c' := Amplitude.const (c u₀)) hconst]
    exact hc
  have hmu' : mu W x (c u₀) p ≠ 0 := by rw [← mu_comm]; exact hmu
  rcases hαβ with hα | hβ
  · have := pure_of_mu_ne_zero W hzero (hdeg x) (Ne.symm hx) hcard hmu' β hα
    rwa [Sym2.eq_swap] at this
  · exact pure_of_mu_ne_zero W hzero (hdeg p) hx hcard hmu α hβ

/-- An inert pair contributes nothing to any amplitude: the term it produces in the
expansion along one of its ends is multiplied by a vanishing complementary sum. -/
theorem inert_term_zero (W : Sym2 (V × Fin 3) → ℂ) {p x : V} (h : Inert W p x)
    (c : V → Fin 3) :
    W (Sym2.map (paint c) s(p, x)) * pmSum W c ((Finset.univ.erase p).erase x) = 0 := by
  rw [h c, mul_zero]

end FanStructure

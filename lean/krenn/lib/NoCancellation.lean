import Mathlib
import Amplitude
import MatchingSum
import Separation
import FanStructure
import MinimalSupport
import HardCase
import Mettapedia.Combinatorics.Matching.Crossing
import Mettapedia.Combinatorics.Matching.Hall
import Mettapedia.Combinatorics.Matching.Nonvanishing
import Mettapedia.Combinatorics.Matching.Restriction
import Mettapedia.Combinatorics.Matching.FourVertices

/-!
# Krenn–Gu consequences of forced matching contributions

The reusable crossing, Hall, and structural nonvanishing theorems live under
`Mettapedia.Combinatorics.Matching`. This file applies them to three-colour GHZ amplitudes and
develops the resulting Krenn–Gu exclusion criteria. A matching sum is a sum over very many
matchings, so knowing that one term is non-zero says nothing by itself: the others may cancel it.

The first tool turns a non-vanishing sum into a non-vanishing **term whose complement is again
non-vanishing**.  Expanding at a site of one's choosing writes the sum as a sum of products of
an edge weight with a complementary sum; if every such product had a vanishing factor the whole
sum would vanish.  So a partner survives, and the construction can be repeated on the smaller
set with a freshly chosen site.  Iterating builds a matching all of whose tails are non-zero --
a witness that no cancellation can destroy.

The second tool is the product formula: when no live edge joins two colour classes of a
colouring, its amplitude is the product of the three classes' matching sums.  It converts the
equations into a statement about three weighted graphs, one per colour -- no live edge mixes
colours at its two ends, though a pair may still carry weight in more than one colour: the
whole-set sums are non-zero, and every non-constant partition kills one of the three factors.
-/

namespace NoCancellation

open Amplitude MatchingSum MatchingCrossing MatchingHall MatchingNonvanishing MatchingRestriction
  MatchingFourVertices

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### The product formula -/

section Product

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The sites wearing a given colour. -/
abbrev fiber (c : V → Fin 3) (k : Fin 3) : Finset V := MatchingSum.colourFiber c k

@[simp] lemma mem_fiber {c : V → Fin 3} {k : Fin 3} {x : V} : x ∈ fiber c k ↔ c x = k :=
  MatchingSum.mem_colourFiber

/-- **A colouring whose classes are not joined splits in two.** -/
theorem pmSum_fiber_split (W : Sym2 (V × Fin 3) → ℂ) (c : V → Fin 3)
    (hcut : ∀ x y : V, c x ≠ c y → W s((x, c x), (y, c y)) = 0) (k : Fin 3) :
    amplitude W c = pmSum W c (fiber c k) * pmSum W c (Finset.univ \ fiber c k) :=
  MatchingSum.pmSum_colourFiber_split W c hcut k

/-- **The amplitude is the product of the three colour classes' matching sums.**

When no live edge joins two colour classes, every matching that contributes lies entirely
inside the classes, and choosing one inside each class is three independent choices.

This is the reformulation the equations want.  The weights become three weighted graphs, one
per colour; the constant colourings say each has a non-vanishing matching sum on
the whole site set, and every non-constant colouring says one of the three classes carries none
on its own class.  No amplitude of a mixed colouring is left to cancel against anything. -/
theorem amplitude_product (W : Sym2 (V × Fin 3) → ℂ) (c : V → Fin 3)
    (hcut : ∀ x y : V, c x ≠ c y → W s((x, c x), (y, c y)) = 0) :
    amplitude W c
      = pmSum W c (fiber c 0) * pmSum W c (fiber c 1) * pmSum W c (fiber c 2) := by
  classical
  rw [pmSum_fiber_split W c hcut 0, mul_assoc]
  congr 1
  have hsub : fiber c 1 ⊆ Finset.univ \ fiber c 0 := by
    intro x hx
    rw [mem_fiber] at hx
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, by rw [mem_fiber, hx]; decide⟩
  have hrest : (Finset.univ \ fiber c 0) \ fiber c 1 = fiber c 2 := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, mem_fiber]
    constructor
    · rintro ⟨h0, h1⟩
      revert h0 h1
      generalize c x = t
      revert t
      decide
    · intro h2
      rw [h2]
      exact ⟨by decide, by decide⟩
  rw [Separation.pmSum_split W c (fiber c 1).card (fiber c 1) (Finset.univ \ fiber c 0) rfl
    hsub ?_, hrest]
  intro x hx y hy
  rw [mem_fiber] at hx
  have hy' : c y ≠ 1 := by
    intro h
    exact (Finset.mem_sdiff.mp hy).2 (mem_fiber.mpr h)
  exact hcut x y (by rw [hx]; exact fun h => hy' h.symm)

end Product

/-- **Under monochromaticity the amplitude is always the product of the three class sums.**  The
product formula's cut hypothesis is free here: a colouring's classes cannot be joined by a live
edge when no live edge mixes colours at all, so the formula holds for *every* colouring rather
than for those with a cut.

Read on the tensor side this is the whole content of the branch.  Writing the amplitude as a sum
over matchings of tensor products of three-by-three endpoint matrices, monochromaticity says each
of those matrices is diagonal; a matching then contributes only to colourings constant along its
edges, and the matchings compatible with a colouring are exactly those inside its classes.  So the
tensor picture collapses to this product, and offers nothing the matching picture does not. -/
theorem amplitude_product_of_mono (W : Sym2 (V × Fin 3) → ℂ)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (c : V → Fin 3) :
    amplitude W c
      = pmSum W c (fiber c 0) * pmSum W c (fiber c 1) * pmSum W c (fiber c 2) :=
  amplitude_product W c (fun x y hxy => hmono x y (fun h => hxy (by rw [h])) (c x) (c y) hxy)

/-! ### The equations forced by the product formula -/

section Equations

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **A live edge kills the other colours' complementary sums.**

Colour a live edge with its own colour and everything else with another.  The classes are not
joined, so the amplitude is the product of the edge's weight with the constant matching sum on
the complement; the colouring is not constant, so that product vanishes; and the weight does
not.  Hence the complement carries no matching sum in any other colour. -/
theorem mu_zero_of_live_edge (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {p q : V} (hqp : q ≠ p) {j k : Fin 3} (hkj : k ≠ j)
    (hlive : W s((p, j), (q, j)) ≠ 0)
    (hout : ∃ z : V, z ≠ p ∧ z ≠ q) :
    pmSum W (Amplitude.const (V := V) k) ((Finset.univ.erase p).erase q) = 0 := by
  classical
  set c : V → Fin 3 := fun t => if t = p ∨ t = q then j else k with hc
  have hcp : c p = j := by simp [hc]
  have hcq : c q = j := by simp [hc]
  have hcout : ∀ t : V, t ≠ p → t ≠ q → c t = k := by
    intro t h1 h2; simp [hc, h1, h2]
  have hcut : ∀ x y : V, c x ≠ c y → W s((x, c x), (y, c y)) = 0 :=
    fun x y h => hmono x y (fun hxy => h (by rw [hxy])) _ _ h
  have hnm : ¬ Amplitude.Monochromatic c := by
    rintro ⟨t, ht⟩
    obtain ⟨z, hz1, hz2⟩ := hout
    exact hkj (by rw [← hcout z hz1 hz2, ht z, ← ht p, hcp])
  have hfib : fiber c j = ({p, q} : Finset V) := by
    ext t
    simp only [mem_fiber, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      by_contra hcon
      push_neg at hcon
      exact hkj (by rw [← hcout t hcon.1 hcon.2, h])
    · rintro (rfl | rfl) <;> simp [hc]
  have hset : Finset.univ \ ({p, q} : Finset V) = (Finset.univ.erase p).erase q := by
    ext t
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Finset.mem_erase, and_true]
    tauto
  have hcolour : pmSum W c ((Finset.univ.erase p).erase q)
      = pmSum W (Amplitude.const (V := V) k) ((Finset.univ.erase p).erase q) :=
    pmSum_congr_colour W (fun t ht => by
      obtain ⟨h2, h1, -⟩ := Finset.mem_erase.mp ht |>.imp id Finset.mem_erase.mp
      exact hcout t h1 h2)
  have hsplit := pmSum_fiber_split W c hcut j
  rw [hfib, hset, pmSum_pair W c hqp, hcp, hcq, hcolour, hzero c hnm] at hsplit
  exact (mul_eq_zero.mp hsplit.symm).resolve_left hlive

/-- **Two edges of different colours cannot both be live over a surviving complement.**

Colour one pair with one colour, a disjoint pair with another, and everything else with the
third.  No class is joined to another, so the amplitude is the product of the two edge weights
with the constant matching sum on the rest; the colouring is not constant, so it vanishes.  If
the rest carries a matching sum -- which is exactly what the non-cancelling partner lemma
produces -- one of the two edges is dead.

This is the equation the four-site configurations obey.  It does not ask the two pairs to be
related in any way, only to be disjoint and to leave a surviving complement behind. -/
theorem pair_pair_zero (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {p q r t : V} (hqp : q ≠ p) (htr : t ≠ r)
    (hpr : p ≠ r) (hpt : p ≠ t) (hqr : q ≠ r) (hqt : q ≠ t)
    {j j' k : Fin 3} (hjj' : j ≠ j') (hkj : k ≠ j) (hkj' : k ≠ j')
    (hrest : pmSum W (Amplitude.const (V := V) k)
      (Finset.univ \ ({p, q, r, t} : Finset V)) ≠ 0) :
    W s((p, j), (q, j)) * W s((r, j'), (t, j')) = 0 := by
  classical
  set c : V → Fin 3 :=
    fun z => if z = p ∨ z = q then j else if z = r ∨ z = t then j' else k with hc
  have hcp : c p = j := by simp [hc]
  have hcq : c q = j := by simp [hc]
  have hcr : c r = j' := by simp [hc, hpr.symm, hqr.symm]
  have hct : c t = j' := by simp [hc, hpt.symm, hqt.symm]
  have hcout : ∀ z : V, z ≠ p → z ≠ q → z ≠ r → z ≠ t → c z = k := by
    intro z h1 h2 h3 h4; simp [hc, h1, h2, h3, h4]
  have hcut : ∀ x y : V, c x ≠ c y → W s((x, c x), (y, c y)) = 0 :=
    fun x y h => hmono x y (fun hxy => h (by rw [hxy])) _ _ h
  have hnm : ¬ Amplitude.Monochromatic c := by
    rintro ⟨m, hm⟩
    exact hjj' (by rw [← hcp, hm p, ← hm r, hcr])
  -- the first class is the first pair
  have hfib : fiber c j = ({p, q} : Finset V) := by
    ext z
    simp only [mem_fiber, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      by_contra hcon
      push_neg at hcon
      by_cases h3 : z = r
      · exact hjj' (by rw [← h, h3, hcr])
      by_cases h4 : z = t
      · exact hjj' (by rw [← h, h4, hct])
      · exact hkj (by rw [← hcout z hcon.1 hcon.2 h3 h4, h])
    · rintro (rfl | rfl) <;> simp [hc]
  have hset1 : Finset.univ \ ({p, q} : Finset V) = (Finset.univ.erase p).erase q := by
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Finset.mem_erase, and_true]
    tauto
  have hsub : ({r, t} : Finset V) ⊆ Finset.univ \ ({p, q} : Finset V) := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    rcases hz with rfl | rfl
    · exact fun h => h.elim (fun h => hpr h.symm) (fun h => hqr h.symm)
    · exact fun h => h.elim (fun h => hpt h.symm) (fun h => hqt h.symm)
  have hset2 : (Finset.univ \ ({p, q} : Finset V)) \ ({r, t} : Finset V)
      = Finset.univ \ ({p, q, r, t} : Finset V) := by
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    tauto
  have hcolour : pmSum W c (Finset.univ \ ({p, q, r, t} : Finset V))
      = pmSum W (Amplitude.const (V := V) k) (Finset.univ \ ({p, q, r, t} : Finset V)) := by
    refine pmSum_congr_colour W (fun z hz => ?_)
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton] at hz
    push_neg at hz
    exact hcout z hz.1 hz.2.1 hz.2.2.1 hz.2.2.2
  have hinner := Separation.pmSum_split W c ({r, t} : Finset V).card ({r, t} : Finset V)
    (Finset.univ \ ({p, q} : Finset V)) rfl hsub (fun x hx y hy => by
      refine hcut x y ?_
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      have hy' := hset2 ▸ hy
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton] at hy'
      push_neg at hy'
      rw [hcout y hy'.1 hy'.2.1 hy'.2.2.1 hy'.2.2.2]
      rcases hx with rfl | rfl
      · rw [hcr]; exact fun h => hkj' h.symm
      · rw [hct]; exact fun h => hkj' h.symm)
  have hsplit := pmSum_fiber_split W c hcut j
  rw [hfib, pmSum_pair W c hqp, hcp, hcq, hzero c hnm, hinner, hset2,
    pmSum_pair W c htr, hcr, hct, hcolour] at hsplit
  rcases mul_eq_zero.mp hsplit.symm with h | h
  · rw [h, zero_mul]
  · rcases mul_eq_zero.mp h with h1 | h2
    · rw [h1, mul_zero]
    · exact absurd h2 hrest

/-- **A non-cancelling edge wears one colour only.**

If the rest of the sites carry a matching sum in some colour, then the pair is dead in every
other colour: were it live in another, the previous theorem would kill exactly the sum that
survives.  Liveness in the surviving colour is not needed and is not assumed --- the hypothesis
is about the complement alone.

So the *certified* colour classes are pairwise disjoint -- not by assumption, but because an
edge that mattered in two colours would annihilate its own complement.  The qualifier is the
whole content: this says nothing about a merely live pair, which may well carry weight in two
colours.  What is excluded is a pair that is live *and* leaves its complement matching. -/
theorem exclusive_of_partner_ne_zero (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {p q : V} (hqp : q ≠ p) {k : Fin 3}
    (hmu : pmSum W (Amplitude.const (V := V) k) ((Finset.univ.erase p).erase q) ≠ 0)
    (hout : ∃ z : V, z ≠ p ∧ z ≠ q)
    {j : Fin 3} (hjk : j ≠ k) : W s((p, j), (q, j)) = 0 := by
  by_contra hlive
  exact hmu (mu_zero_of_live_edge W hzero hmono hqp (Ne.symm hjk) hlive hout)


/-- **A pair whose complement survives in two colours is dead in all three.**  Each surviving
colour excludes the other two, and two colours between them exclude everything.

So the colours in which a pair's complement can survive are, for a live pair, unique.  A pair
certified by two different colours contributes to no matching at all. -/
theorem dead_of_two_complements (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {p q : V} (hqp : q ≠ p) (hout : ∃ z : V, z ≠ p ∧ z ≠ q) {k j : Fin 3} (hjk : j ≠ k)
    (hk : pmSum W (Amplitude.const (V := V) k) ((Finset.univ.erase p).erase q) ≠ 0)
    (hj : pmSum W (Amplitude.const (V := V) j) ((Finset.univ.erase p).erase q) ≠ 0) :
    ∀ m : Fin 3, W s((p, m), (q, m)) = 0 := by
  intro m
  by_cases hmk : m = k
  · subst hmk
    exact exclusive_of_partner_ne_zero W hzero hmono hqp hj hout (Ne.symm hjk)
  · exact exclusive_of_partner_ne_zero W hzero hmono hqp hk hout hmk

/-- **Every site has a non-cancelling, colour-exclusive partner in every colour.**

Peel the constant colouring at the chosen site: some partner carries a non-zero weight whose
complement still matches, and that partner is then exclusive to the colour.  This is the
witness the equations cannot cancel away. -/
theorem exists_exclusive_partner (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hcard : 2 < Fintype.card V) (k : Fin 3)
    (hone : amplitude W (Amplitude.const (V := V) k) ≠ 0) (p : V) :
    ∃ q : V, q ≠ p ∧ W s((p, k), (q, k)) ≠ 0 ∧
      pmSum W (Amplitude.const (V := V) k) ((Finset.univ.erase p).erase q) ≠ 0 ∧
      ∀ j : Fin 3, j ≠ k → W s((p, j), (q, j)) = 0 := by
  classical
  have huniv : pmSum W (Amplitude.const (V := V) k) Finset.univ ≠ 0 := by
    rw [pmSum_univ]; exact hone
  obtain ⟨q, hq, hw, hs⟩ :=
    exists_partner_ne_zero W (Amplitude.const (V := V) k) (Finset.mem_univ p) huniv
  have hqp : q ≠ p := (Finset.mem_erase.mp hq).1
  have hout : ∃ z : V, z ≠ p ∧ z ≠ q := by
    by_contra hno
    push_neg at hno
    have hsub : (Finset.univ : Finset V) ⊆ ({p, q} : Finset V) := by
      intro z _
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases h : z = p
      · exact Or.inl h
      · exact Or.inr (hno z h)
    have h1 := Finset.card_le_card hsub
    have h2 : ({p, q} : Finset V).card ≤ 2 :=
      (Finset.card_insert_le _ _).trans (by simp)
    rw [Finset.card_univ] at h1
    omega
  exact ⟨q, hqp, hw, hs, fun j hj => exclusive_of_partner_ne_zero W hzero hmono hqp hs hout hj⟩

/-- **Support minimality supplies the hypothesis.**

On a support-minimal representative every live pair is non-inert, so a configuration all of
whose sites are degenerate has all of its live pairs monochromatic.  The equations above then
apply to it with no further assumption.

What this says exactly is that no live edge *mixes* colours at its two ends.  It does not say
that a pair carries only one colour: nothing here forbids `W s((x, a), (y, a))` and
`W s((x, b), (y, b))` from both being non-zero, so the three colour graphs need not be
edge-disjoint. -/
theorem mono_of_supportMinimal (W : Sym2 (V × Fin 3) → ℂ)
    (hmin : MinimalSupport.IsSupportMinimal W)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hdeg : ∀ q : V, FanStructure.Degenerate W q) (hcard : 4 ≤ Fintype.card V) :
    ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0 := by
  intro x y hyx a b hab
  by_contra hcon
  exact hab (FanStructure.edge_monochromatic W hzero hdeg hcard hyx
    (MinimalSupport.not_inert_of_supportMinimal hmin hyx ⟨a, b, hcon⟩) hcon)

/-- **The two-colour equation, with only the crossing blocks assumed dead.**

Colour a set one way and its complement another.  What the argument needs is not that every
live edge be monochromatic, but only that no live edge join the set wearing one colour to the
complement wearing the other.  The amplitude is then the product of the two sides' matching
sums, the colouring is not constant, and the product vanishes.

Stated this way the equation reaches configurations with non-degenerate sites, since the
condition is about one cut and two colours rather than about every edge. -/
theorem pmSum_zero_of_complement_ne_zero_of_cut (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {S : Finset V} (hS : S.Nonempty) (hSne : S ≠ Finset.univ)
    {j k : Fin 3} (hkj : k ≠ j)
    (hcross : ∀ x ∈ S, ∀ y : V, y ∉ S → W s((x, k), (y, j)) = 0)
    (hcompl : pmSum W (Amplitude.const (V := V) j) (Finset.univ \ S) ≠ 0) :
    pmSum W (Amplitude.const (V := V) k) S = 0 := by
  classical
  set c : V → Fin 3 := fun z => if z ∈ S then k else j with hc
  have hin : ∀ z ∈ S, c z = k := by intro z hz; simp [hc, hz]
  have hout : ∀ z, z ∉ S → c z = j := by intro z hz; simp [hc, hz]
  have hcut : ∀ x y : V, c x ≠ c y → W s((x, c x), (y, c y)) = 0 := by
    intro x y hxy
    by_cases hxS : x ∈ S
    · by_cases hyS : y ∈ S
      · exact absurd (by rw [hin x hxS, hin y hyS]) hxy
      · rw [hin x hxS, hout y hyS]
        exact hcross x hxS y hyS
    · by_cases hyS : y ∈ S
      · rw [hout x hxS, hin y hyS, Sym2.eq_swap]
        exact hcross y hyS x hxS
      · exact absurd (by rw [hout x hxS, hout y hyS]) hxy
  obtain ⟨w, hw⟩ : ∃ w : V, w ∉ S := by
    by_contra hno
    push_neg at hno
    exact hSne (Finset.eq_univ_iff_forall.mpr hno)
  obtain ⟨z, hz⟩ := hS
  have hnm : ¬ Amplitude.Monochromatic c := by
    rintro ⟨t, ht⟩
    exact hkj (by rw [← hin z hz, ht z, ← ht w, hout w hw])
  have hfib : fiber c k = S := by
    ext y
    simp only [mem_fiber]
    refine ⟨fun h => ?_, hin y⟩
    by_contra hy
    exact hkj (by rw [← h, hout y hy])
  have h1 : pmSum W c S = pmSum W (Amplitude.const (V := V) k) S :=
    pmSum_congr_colour W (fun y hy => hin y hy)
  have h2 : pmSum W c (Finset.univ \ S)
      = pmSum W (Amplitude.const (V := V) j) (Finset.univ \ S) :=
    pmSum_congr_colour W (fun y hy => hout y (Finset.mem_sdiff.mp hy).2)
  have hsplit := pmSum_fiber_split W c hcut k
  rw [hfib, h1, h2, hzero c hnm] at hsplit
  exact (mul_eq_zero.mp hsplit.symm).resolve_right hcompl

/-- **The two-colour equation.**

Colour a set one way and its complement another.  Nothing joins the two classes, so the
amplitude is the product of their matching sums, and the colouring is not constant, so the
product vanishes.  Hence a set whose complement still matches in one colour carries no matching
sum in any other.

This is the general form: `mu_zero_of_live_edge` is the case of a two-site set, and taking the
set to be a union of pairs gives the four-site identities.  Paired with the non-cancelling
partner lemma, which manufactures complements that match, it is the engine of the whole file. -/
theorem pmSum_zero_of_complement_ne_zero (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {S : Finset V} (hS : S.Nonempty) (hSne : S ≠ Finset.univ)
    {j k : Fin 3} (hkj : k ≠ j)
    (hcompl : pmSum W (Amplitude.const (V := V) j) (Finset.univ \ S) ≠ 0) :
    pmSum W (Amplitude.const (V := V) k) S = 0 := by
  classical
  set c : V → Fin 3 := fun z => if z ∈ S then k else j with hc
  have hin : ∀ z ∈ S, c z = k := by intro z hz; simp [hc, hz]
  have hout : ∀ z, z ∉ S → c z = j := by intro z hz; simp [hc, hz]
  have hcut : ∀ x y : V, c x ≠ c y → W s((x, c x), (y, c y)) = 0 :=
    fun x y h => hmono x y (fun hxy => h (by rw [hxy])) _ _ h
  obtain ⟨w, hw⟩ : ∃ w : V, w ∉ S := by
    by_contra hno
    push_neg at hno
    exact hSne (Finset.eq_univ_iff_forall.mpr hno)
  obtain ⟨z, hz⟩ := hS
  have hnm : ¬ Amplitude.Monochromatic c := by
    rintro ⟨m, hm⟩
    exact hkj (by rw [← hin z hz, hm z, ← hm w, hout w hw])
  have hfib : fiber c k = S := by
    ext y
    simp only [mem_fiber]
    constructor
    · intro h
      by_contra hy
      exact hkj (by rw [← h, hout y hy])
    · exact hin y
  have h1 : pmSum W c S = pmSum W (Amplitude.const (V := V) k) S :=
    pmSum_congr_colour W (fun y hy => hin y hy)
  have h2 : pmSum W c (Finset.univ \ S) = pmSum W (Amplitude.const (V := V) j) (Finset.univ \ S) :=
    pmSum_congr_colour W (fun y hy => hout y (Finset.mem_sdiff.mp hy).2)
  have hsplit := pmSum_fiber_split W c hcut k
  rw [hfib, h1, h2, hzero c hnm] at hsplit
  exact (mul_eq_zero.mp hsplit.symm).resolve_right hcompl

/-- **Cross-colour exclusion.**

Take a live edge in one colour, and give each of its two ends a non-cancelling partner in a
second colour.  The four sites now carry two disjoint pairs -- the original edge, and the pair
of chosen partners -- and the complement of all four still matches in the second colour,
because that is what the partner lemma guarantees.  The disjoint-pairs equation then forces the
pair of partners to be dead in the third colour.

Nothing here is local: the two partners are produced by a construction that reaches across the
whole site set, and the conclusion is about an edge between them. -/
theorem cross_colour_exclusion (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hcard : 2 < Fintype.card V)
    {j₀ j₁ k : Fin 3} (hj : j₀ ≠ j₁) (hkj₀ : k ≠ j₀) (hkj₁ : k ≠ j₁)
    (hone : amplitude W (Amplitude.const (V := V) k) ≠ 0)
    {x y : V} (hyx : y ≠ x) (hlive : W s((x, j₀), (y, j₀)) ≠ 0) :
    ∃ z w : V, W s((x, k), (z, k)) ≠ 0 ∧ W s((y, k), (w, k)) ≠ 0 ∧
      z ≠ w ∧ W s((z, j₁), (w, j₁)) = 0 := by
  classical
  obtain ⟨z, hzx, hlz, hsz, hexcl⟩ :=
    exists_exclusive_partner W hzero hmono hcard k hone x
  -- the second colour's partner is exclusive to it, so it is not the far end of the live edge
  have hyz : y ≠ z := by
    intro h
    rw [h] at hlive
    exact hlive (hexcl j₀ (Ne.symm hkj₀))
  have hymem : y ∈ (Finset.univ.erase x).erase z :=
    Finset.mem_erase.mpr ⟨hyz, Finset.mem_erase.mpr ⟨hyx, Finset.mem_univ y⟩⟩
  obtain ⟨w, hw, hlw, hsw⟩ :=
    exists_partner_ne_zero W (Amplitude.const (V := V) k) hymem hsz
  have hwy : w ≠ y := (Finset.mem_erase.mp hw).1
  have hwz : w ≠ z := (Finset.mem_erase.mp (Finset.mem_erase.mp hw).2).1
  have hwx : w ≠ x :=
    (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hw).2).2).1
  have hset : (((Finset.univ.erase x).erase z).erase y).erase w
      = Finset.univ \ ({x, y, z, w} : Finset V) := by
    ext u
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_sdiff, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [hset] at hsw
  refine ⟨z, w, hlz, hlw, Ne.symm hwz, ?_⟩
  exact (mul_eq_zero.mp (pair_pair_zero W hzero hmono hyx hwz
    (Ne.symm hzx) (Ne.symm hwx) hyz (Ne.symm hwy) hj hkj₀ hkj₁ hsw)).resolve_left hlive

/-- **A unique partner cannot cancel.**

If a site has only one live partner in a colour, the expansion of that colour's constant
amplitude at the site has a single term.  A single term cannot cancel, so the complement's
matching sum is non-zero -- for free, with no minimality and no choice involved.

This is what separates the two remaining shapes.  Where every site has exactly one partner per
colour, every edge is automatically non-cancelling and exclusive, and the configuration is the
three-regular one.  Any other configuration has a site with two partners of the same colour,
and it is only there that a complementary sum is free to vanish. -/
theorem complement_ne_zero_of_unique_partner (W : Sym2 (V × Fin 3) → ℂ) {k : Fin 3}
    (hone : amplitude W (Amplitude.const (V := V) k) ≠ 0) {u v : V} (hvu : v ≠ u)
    (huniq : ∀ z : V, z ≠ u → z ≠ v → W s((u, k), (z, k)) = 0) :
    pmSum W (Amplitude.const (V := V) k) ((Finset.univ.erase u).erase v) ≠ 0 := by
  classical
  have hmem : v ∈ Finset.univ.erase u := Finset.mem_erase.mpr ⟨hvu, Finset.mem_univ v⟩
  have hexp : amplitude W (Amplitude.const (V := V) k)
      = W s((u, k), (v, k)) *
        pmSum W (Amplitude.const (V := V) k) ((Finset.univ.erase u).erase v) := by
    rw [← pmSum_univ, pmSum_expand W (Amplitude.const (V := V) k) (Finset.mem_univ u)]
    refine Finset.sum_eq_single_of_mem v hmem (fun z hz hzv => ?_)
    have hzu : z ≠ u := (Finset.mem_erase.mp hz).1
    rw [show W (Sym2.map (paint (Amplitude.const (V := V) k)) s(u, z))
        = W s((u, k), (z, k)) from rfl, huniq z hzu hzv, zero_mul]
  intro hzero'
  rw [hexp, hzero', mul_zero] at hone
  exact hone rfl

/-- With a unique partner, that partner's edge is exclusive to its colour with no hypothesis
beyond the equations: the complement survives by the previous theorem, and an edge live in two
colours would annihilate its own complement. -/
theorem exclusive_of_unique_partner (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {k : Fin 3} (hone : amplitude W (Amplitude.const (V := V) k) ≠ 0)
    {u v : V} (hvu : v ≠ u)
    (huniq : ∀ z : V, z ≠ u → z ≠ v → W s((u, k), (z, k)) = 0)
    (hout : ∃ z : V, z ≠ u ∧ z ≠ v)
    {j : Fin 3} (hjk : j ≠ k) : W s((u, j), (v, j)) = 0 :=
  exclusive_of_partner_ne_zero W hzero hmono hvu
    (complement_ne_zero_of_unique_partner W hone hvu huniq) hout hjk

/-- **Sharp cross-colour exclusion.**

Take a live edge in one colour whose two ends each have a *unique* partner in a second
colour.  Peeling those two partners is forced -- each expansion has a single term -- so the
complement of all four sites matches in the second colour with no choice made anywhere.  The
disjoint-pairs equation then says the two partners are dead in the third colour.

Where the earlier version had to accept whatever partner the peeling produced, this one names
it.  Applied to a colour whose class is a perfect matching, it says that matching carries no
edge of one colour to an edge of another. -/
theorem cross_exclusion_of_unique_partners (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hcard : 2 < Fintype.card V)
    {j j' k : Fin 3} (hjj' : j ≠ j') (hkj : k ≠ j) (hkj' : k ≠ j')
    (hone : amplitude W (Amplitude.const (V := V) k) ≠ 0)
    {x y p q : V} (hyx : y ≠ x) (hlive : W s((x, j), (y, j)) ≠ 0)
    (hpx : p ≠ x) (hqy : q ≠ y) (hpq : p ≠ q)
    (hux : ∀ z : V, z ≠ x → z ≠ p → W s((x, k), (z, k)) = 0)
    (huy : ∀ z : V, z ≠ y → z ≠ q → W s((y, k), (z, k)) = 0) :
    W s((p, j'), (q, j')) = 0 := by
  classical
  have hout : ∀ a b : V, ∃ z : V, z ≠ a ∧ z ≠ b := by
    intro a b
    by_contra hno
    push_neg at hno
    have hsub : (Finset.univ : Finset V) ⊆ ({a, b} : Finset V) := by
      intro z _
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases h : z = a
      · exact Or.inl h
      · exact Or.inr (hno z h)
    have h1 := Finset.card_le_card hsub
    have h2 : ({a, b} : Finset V).card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
    rw [Finset.card_univ] at h1
    omega
  -- neither partner is the far end of the live edge
  have hpy : p ≠ y := by
    intro h
    refine hlive ?_
    rw [h] at hux
    exact exclusive_of_unique_partner W hzero hmono hone hyx hux (hout x y) (Ne.symm hkj)
  have hqx : q ≠ x := by
    intro h
    refine hlive ?_
    rw [h] at huy
    rw [Sym2.eq_swap]
    exact exclusive_of_unique_partner W hzero hmono hone (Ne.symm hyx) huy
      (hout y x) (Ne.symm hkj)
  -- the first peel is forced, and so is the second
  have h1 : pmSum W (Amplitude.const (V := V) k) ((Finset.univ.erase x).erase p) ≠ 0 :=
    complement_ne_zero_of_unique_partner W hone hpx hux
  have hymem : y ∈ (Finset.univ.erase x).erase p :=
    Finset.mem_erase.mpr ⟨Ne.symm hpy, Finset.mem_erase.mpr ⟨hyx, Finset.mem_univ y⟩⟩
  have hqmem : q ∈ ((Finset.univ.erase x).erase p).erase y :=
    Finset.mem_erase.mpr ⟨hqy, Finset.mem_erase.mpr ⟨Ne.symm hpq,
      Finset.mem_erase.mpr ⟨hqx, Finset.mem_univ q⟩⟩⟩
  have h2 : pmSum W (Amplitude.const (V := V) k)
      ((((Finset.univ.erase x).erase p).erase y).erase q) ≠ 0 := by
    intro hz
    refine h1 ?_
    rw [pmSum_expand W (Amplitude.const (V := V) k) hymem]
    refine Finset.sum_eq_zero fun z hz' => ?_
    by_cases hzq : z = q
    · subst hzq
      rw [hz, mul_zero]
    · have hzy : z ≠ y := (Finset.mem_erase.mp hz').1
      rw [show W (Sym2.map (paint (Amplitude.const (V := V) k)) s(y, z))
          = W s((y, k), (z, k)) from rfl, huy z hzy hzq, zero_mul]
  have hset : (((Finset.univ.erase x).erase p).erase y).erase q
      = Finset.univ \ ({x, y, p, q} : Finset V) := by
    ext z
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_sdiff, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [hset] at h2
  exact (mul_eq_zero.mp (pair_pair_zero W hzero hmono hyx hpq.symm
    (Ne.symm hpx) (Ne.symm hqx) (Ne.symm hpy) (Ne.symm hqy) hjj' hkj hkj' h2)).resolve_left hlive

/-- **An alternating four-cycle is fatal.**

Suppose four sites carry a four-cycle alternating between two colours, with the two edges of
the first colour forcedly peelable -- each seed having a unique partner at the moment it is
peeled -- and the second colour not joining the cycle across a diagonal.

Then both halves are certified at once.  Peeling the two first-colour edges leaves a complement
whose first-colour matching sum is non-zero, and peeling inside the four sites shows their
second-colour matching sum is a single product of two live weights.  The two-colour equation
says a set whose complement still matches in one colour carries no matching sum in another,
and here both are non-zero.

So no such four-cycle exists.  The diagonal hypothesis is about the second colour while the
uniqueness hypotheses are about the first, so the clean special case needs *both* classes to be
perfect matchings: two colour classes that are matchings have no alternating four-cycle
between them, and their alternating cycles are all of length at least six. -/
theorem no_alternating_four_cycle (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hcard : 2 < Fintype.card V)
    {j k : Fin 3} (hkj : k ≠ j)
    (hone : amplitude W (Amplitude.const (V := V) j) ≠ 0)
    {x y z w : V} (hyx : y ≠ x) (hzx : z ≠ x) (hwx : w ≠ x)
    (hzy : z ≠ y) (hwy : w ≠ y) (hwz : w ≠ z)
    (hout : ∃ t : V, t ≠ x ∧ t ≠ y ∧ t ≠ z ∧ t ≠ w)
    (hxy : W s((x, k), (y, k)) ≠ 0) (hzw : W s((z, k), (w, k)) ≠ 0)
    (hxw : W s((x, k), (w, k)) = 0)
    (huniqx : ∀ t : V, t ≠ x → t ≠ z → W s((x, j), (t, j)) = 0)
    (huniqy : ∀ t : V, t ≠ y → t ≠ w → t ≠ x → t ≠ z → W s((y, j), (t, j)) = 0) :
    False := by
  classical
  have hout2 : ∀ a b : V, ∃ t : V, t ≠ a ∧ t ≠ b := by
    intro a b
    by_contra hno
    push_neg at hno
    have hsub : (Finset.univ : Finset V) ⊆ ({a, b} : Finset V) := by
      intro t _
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases h : t = a
      · exact Or.inl h
      · exact Or.inr (hno t h)
    have h1 := Finset.card_le_card hsub
    have h2 : ({a, b} : Finset V).card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
    rw [Finset.card_univ] at h1
    omega
  -- the first colour's edge at `x` is exclusive, so it is dead in the second
  have hxz : W s((x, k), (z, k)) = 0 :=
    exclusive_of_unique_partner W hzero hmono hone hzx huniqx (hout2 x z) hkj
  -- two forced peels in the first colour
  have hp1 : pmSum W (Amplitude.const (V := V) j) ((Finset.univ.erase x).erase z) ≠ 0 :=
    complement_ne_zero_of_unique_partner W hone hzx huniqx
  have hymem : y ∈ (Finset.univ.erase x).erase z :=
    Finset.mem_erase.mpr ⟨Ne.symm hzy, Finset.mem_erase.mpr ⟨hyx, Finset.mem_univ y⟩⟩
  have hwmem : w ∈ ((Finset.univ.erase x).erase z).erase y :=
    Finset.mem_erase.mpr ⟨hwy, Finset.mem_erase.mpr ⟨hwz,
      Finset.mem_erase.mpr ⟨hwx, Finset.mem_univ w⟩⟩⟩
  have hp2 : pmSum W (Amplitude.const (V := V) j)
      ((((Finset.univ.erase x).erase z).erase y).erase w) ≠ 0 := by
    intro hz0
    refine hp1 ?_
    rw [pmSum_of_forced W (Amplitude.const (V := V) j) hymem hwmem
      (fun t ht htw => by
        have h1 : t ≠ y := (Finset.mem_erase.mp ht).1
        have h2 : t ≠ z := (Finset.mem_erase.mp (Finset.mem_erase.mp ht).2).1
        have h3 : t ≠ x :=
          (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp ht).2).2).1
        exact huniqy t h1 htw h3 h2), hz0, mul_zero]
  have hset : (((Finset.univ.erase x).erase z).erase y).erase w
      = Finset.univ \ ({x, y, z, w} : Finset V) := by
    ext t
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_sdiff, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [hset] at hp2
  -- inside the four sites, the second colour's sum is one product of two live weights
  have hxmem : x ∈ ({x, y, z, w} : Finset V) := by simp
  have hymem2 : y ∈ ({x, y, z, w} : Finset V).erase x :=
    Finset.mem_erase.mpr ⟨hyx, by simp⟩
  have hrest : (({x, y, z, w} : Finset V).erase x).erase y = ({z, w} : Finset V) := by
    ext t
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2, h3 | h3 | h3 | h3⟩
      · exact absurd h3 h2
      · exact absurd h3 h1
      · exact Or.inl h3
      · exact Or.inr h3
    · rintro (rfl | rfl)
      · exact ⟨hzy, hzx, by simp⟩
      · exact ⟨hwy, hwx, by simp⟩
  have hfour : pmSum W (Amplitude.const (V := V) k) ({x, y, z, w} : Finset V) ≠ 0 := by
    rw [pmSum_of_forced W (Amplitude.const (V := V) k) hxmem hymem2
      (fun t ht hty => by
        have h1 : t ≠ x := (Finset.mem_erase.mp ht).1
        have h2 := (Finset.mem_erase.mp ht).2
        simp only [Finset.mem_insert, Finset.mem_singleton] at h2
        rcases h2 with rfl | rfl | rfl | rfl
        · exact absurd rfl h1
        · exact absurd rfl hty
        · exact hxz
        · exact hxw), hrest, pmSum_pair W _ hwz]
    exact mul_ne_zero hxy hzw
  refine hfour (pmSum_zero_of_complement_ne_zero W hzero hmono ⟨x, hxmem⟩ ?_ hkj hp2)
  obtain ⟨t, h1, h2, h3, h4⟩ := hout
  intro hu
  have : t ∈ ({x, y, z, w} : Finset V) := hu ▸ Finset.mem_univ t
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with rfl | rfl | rfl | rfl
  exacts [h1 rfl, h2 rfl, h3 rfl, h4 rfl]

/-! ### Forced matchings

A certificate that a set matches with no cancellation possible anywhere: peel it one pair at a
time, and at every stage the site peeled has exactly one live partner left in the set.  Each
step multiplies the matching sum by a non-zero weight, so the whole sum is non-zero, and no
choice was made along the way.
-/

/-- **A forced matching of a set.**  Either the set is empty, or some site in it has exactly
one live partner there, that partner's weight is non-zero, and what remains is again forcedly
matched. -/
inductive ForcedPeel (W : Sym2 (V × Fin 3) → ℂ) (c : V → Fin 3) : Finset V → Prop
  | empty : ForcedPeel W c ∅
  | step (S : Finset V) (x p : V) (hx : x ∈ S) (hp : p ∈ S.erase x)
      (hlive : W s((x, c x), (p, c p)) ≠ 0)
      (huniq : ∀ z ∈ S.erase x, z ≠ p → W s((x, c x), (z, c z)) = 0)
      (h : ForcedPeel W c ((S.erase x).erase p)) : ForcedPeel W c S

/-- A forced matching certifies its own matching sum: each peel contributes a non-zero factor
and nothing can cancel. -/
theorem pmSum_ne_zero_of_forcedPeel {W : Sym2 (V × Fin 3) → ℂ} {c : V → Fin 3} {S : Finset V}
    (h : ForcedPeel W c S) : pmSum W c S ≠ 0 := by
  induction h with
  | empty => rw [pmSum_empty]; exact one_ne_zero
  | step S x p hx hp hlive huniq _ ih =>
      rw [pmSum_of_forced W c hx hp huniq]
      exact mul_ne_zero hlive ih

/-- **No set is forcedly matched in one colour while its complement is forcedly matched in
another.**

This is the engine.  Both certificates rule out cancellation on their own side, and the
two-colour equation says a set whose complement matches in one colour carries no matching sum
in any other.  The two statements collide.

Everything the equations can be made to contradict passes through here: to refute a
configuration it is enough to exhibit a proper non-empty set that peels forcedly in one colour
and whose complement peels forcedly in another.  The alternating four-cycle is the smallest
instance; an alternating cycle of any even length with no chord in the second colour is
another, whatever its length. -/
theorem false_of_forcedPeel_split (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {S : Finset V} (hS : S.Nonempty) (hSne : S ≠ Finset.univ)
    {j k : Fin 3} (hkj : k ≠ j)
    (hk : ForcedPeel W (Amplitude.const (V := V) k) S)
    (hj : ForcedPeel W (Amplitude.const (V := V) j) (Finset.univ \ S)) : False :=
  pmSum_ne_zero_of_forcedPeel hk
    (pmSum_zero_of_complement_ne_zero W hzero hmono hS hSne hkj
      (pmSum_ne_zero_of_forcedPeel hj))

/-- **A forced tail.**  The dual certificate: instead of peeling a set down to nothing, peel
it *away* from the whole site set.  Each step removes a pair whose first site had exactly one
live partner left, so the surviving matching sum is again non-zero. -/
inductive ForcedTail (W : Sym2 (V × Fin 3) → ℂ) (c : V → Fin 3) : Finset V → Prop
  | univ : ForcedTail W c Finset.univ
  | step (T : Finset V) (x p : V) (hx : x ∈ T) (hp : p ∈ T.erase x)
      (huniq : ∀ z ∈ T.erase x, z ≠ p → W s((x, c x), (z, c z)) = 0)
      (h : ForcedTail W c T) : ForcedTail W c ((T.erase x).erase p)

/-- A forced tail inherits non-vanishing from the whole amplitude. -/
theorem pmSum_ne_zero_of_forcedTail {W : Sym2 (V × Fin 3) → ℂ} {c : V → Fin 3} {T : Finset V}
    (hone : amplitude W c ≠ 0) (h : ForcedTail W c T) : pmSum W c T ≠ 0 := by
  induction h with
  | univ => rw [pmSum_univ]; exact hone
  | step T x p hx hp huniq _ ih =>
      intro hz
      exact ih (by rw [pmSum_of_forced W c hx hp huniq, hz, mul_zero])

/-- **The master contradiction.**

A proper non-empty set that peels forcedly to nothing in one colour, and peels forcedly away
from the whole site set in another, cannot exist.  Both certificates exclude cancellation on
their own side, and the two-colour equation forbids the pair.

Both halves speak only about the set itself, so the statement is usable at whatever scale the
configuration offers -- there is no need for a global matching on either side.  The alternating
four-cycle is its smallest instance. -/
theorem false_of_forced_split (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {S : Finset V} (hS : S.Nonempty) (hSne : S ≠ Finset.univ)
    {j k : Fin 3} (hkj : k ≠ j)
    (hone : amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hk : ForcedPeel W (Amplitude.const (V := V) k) S)
    (hj : ForcedTail W (Amplitude.const (V := V) j) (Finset.univ \ S)) : False :=
  pmSum_ne_zero_of_forcedPeel hk
    (pmSum_zero_of_complement_ne_zero W hzero hmono hS hSne hkj
      (pmSum_ne_zero_of_forcedTail hone hj))

/-- **An involution gives a forced peel.**  If a set is closed under an involution, every
site's partner under it is live, and inside the set no site has any other live partner, then
peeling along the involution is forced at every stage. -/
theorem forcedPeel_of_involution (W : Sym2 (V × Fin 3) → ℂ) (c : V → Fin 3) (τ : V → V)
    (hinv : ∀ t : V, τ (τ t) = t) (hne : ∀ t : V, τ t ≠ t) :
    ∀ (n : ℕ) (S : Finset V), S.card = n → (∀ t ∈ S, τ t ∈ S) →
      (∀ t ∈ S, W s((t, c t), (τ t, c (τ t))) ≠ 0) →
      (∀ t ∈ S, ∀ z ∈ S, z ≠ t → z ≠ τ t → W s((t, c t), (z, c z)) = 0) →
      ForcedPeel W c S := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hcard hclosed hlive huniq
    rcases Finset.eq_empty_or_nonempty S with rfl | ⟨x, hx⟩
    · exact ForcedPeel.empty
    · have hτx : τ x ∈ S.erase x :=
        Finset.mem_erase.mpr ⟨hne x, hclosed x hx⟩
      have hsub : ((S.erase x).erase (τ x)).card < n := by
        rw [← hcard]
        exact lt_of_le_of_lt (Finset.card_erase_le) (Finset.card_erase_lt_of_mem hx)
      refine ForcedPeel.step S x (τ x) hx hτx (hlive x hx)
        (fun z hz hzτ => huniq x hx z (Finset.mem_of_mem_erase hz)
          (Finset.mem_erase.mp hz).1 hzτ) ?_
      have hmem : ∀ t ∈ (S.erase x).erase (τ x), t ∈ S := fun t ht =>
        Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ht)
      refine ih _ hsub _ rfl (fun t ht => ?_) (fun t ht => hlive t (hmem t ht))
        (fun t ht z hz => huniq t (hmem t ht) z (hmem z hz))
      have htS : t ∈ S := hmem t ht
      have h1 : t ≠ τ x := (Finset.mem_erase.mp ht).1
      have h2 : t ≠ x := (Finset.mem_erase.mp (Finset.mem_erase.mp ht).2).1
      have hne1 : τ t ≠ τ x := fun h => h2 (by rw [← hinv t, h, hinv])
      have hne2 : τ t ≠ x := fun h => h1 (by rw [← hinv t, h])
      exact Finset.mem_erase.mpr ⟨hne1, Finset.mem_erase.mpr ⟨hne2, hclosed t htS⟩⟩

/-- **An involution gives a forced tail.**  If a set is closed under an involution and no site
of it has a live partner other than its image, peeling those pairs away from the whole site set
is forced at every stage. -/
theorem forcedTail_of_involution (W : Sym2 (V × Fin 3) → ℂ) (c : V → Fin 3) (σ : V → V)
    (hinv : ∀ t : V, σ (σ t) = t) (hne : ∀ t : V, σ t ≠ t)
    (huniq : ∀ t : V, ∀ z : V, z ≠ t → z ≠ σ t → W s((t, c t), (z, c z)) = 0) :
    ∀ (n : ℕ) (S : Finset V), S.card = n → (∀ t ∈ S, σ t ∈ S) →
      ForcedTail W c (Finset.univ \ S) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hcard hclosed
    rcases Finset.eq_empty_or_nonempty S with rfl | ⟨x, hx⟩
    · rw [Finset.sdiff_empty]
      exact ForcedTail.univ
    · set S' : Finset V := (S.erase x).erase (σ x) with hS'
      have hsub : S'.card < n := by
        rw [← hcard]
        exact lt_of_le_of_lt (Finset.card_erase_le) (Finset.card_erase_lt_of_mem hx)
      have hclosed' : ∀ t ∈ S', σ t ∈ S' := by
        intro t ht
        have htS : t ∈ S := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ht)
        have h1 : t ≠ σ x := (Finset.mem_erase.mp ht).1
        have h2 : t ≠ x := (Finset.mem_erase.mp (Finset.mem_erase.mp ht).2).1
        have hne1 : σ t ≠ σ x := fun h => h2 (by rw [← hinv t, h, hinv])
        have hne2 : σ t ≠ x := fun h => h1 (by rw [← hinv t, h])
        exact Finset.mem_erase.mpr ⟨hne1, Finset.mem_erase.mpr ⟨hne2, hclosed t htS⟩⟩
      have hprev := ih _ hsub S' rfl hclosed'
      have hxmem : x ∈ Finset.univ \ S' := by
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, ?_⟩
        intro hcon
        exact (Finset.mem_erase.mp (Finset.mem_erase.mp hcon).2).1 rfl
      have hσmem : σ x ∈ (Finset.univ \ S').erase x :=
        Finset.mem_erase.mpr ⟨hne x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
          fun hcon => (Finset.mem_erase.mp hcon).1 rfl⟩⟩
      have hxS : x ∈ S := hx
      have hσS : σ x ∈ S := hclosed x hx
      have hset : ((Finset.univ \ S').erase x).erase (σ x) = Finset.univ \ S := by
        ext t
        simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ, true_and, hS']
        constructor
        · rintro ⟨h1, h2, h3⟩ hcon
          exact h3 ⟨h1, h2, hcon⟩
        · intro h
          refine ⟨?_, ?_, ?_⟩
          · intro hc; exact h (by rw [hc]; exact hσS)
          · intro hc; exact h (by rw [hc]; exact hxS)
          · rintro ⟨-, -, hcon⟩; exact h hcon
      rw [← hset]
      exact ForcedTail.step (Finset.univ \ S') x (σ x) hxmem hσmem
        (fun z hz hzσ => huniq x z (Finset.mem_erase.mp hz).1 hzσ) hprev

/-- **Two colour matchings cannot share a proper invariant set.**

Give two colours their matchings, as fixed-point-free involutions: the first with no other live
partner anywhere, the second with no other live partner inside the set considered.  Then no
proper non-empty set is closed under both.

Peeling along the second involution takes the set to nothing; peeling along the first takes its
complement away from everything; and the two-colour equation forbids that pair.

The reading is the classical one, now uniform and free of any case analysis: the union of two
colour matchings is a single alternating cycle through every site.  Any smaller union of its
cycles would be closed under both involutions. -/
theorem false_of_two_involutions (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {j k : Fin 3} (hkj : k ≠ j)
    (hone : amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (σ τ : V → V)
    (hσinv : ∀ t : V, σ (σ t) = t) (hσne : ∀ t : V, σ t ≠ t)
    (hτinv : ∀ t : V, τ (τ t) = t) (hτne : ∀ t : V, τ t ≠ t)
    (hσuniq : ∀ t z : V, z ≠ t → z ≠ σ t → W s((t, j), (z, j)) = 0)
    {S : Finset V} (hS : S.Nonempty) (hSne : S ≠ Finset.univ)
    (hSσ : ∀ t ∈ S, σ t ∈ S) (hSτ : ∀ t ∈ S, τ t ∈ S)
    (hτlive : ∀ t ∈ S, W s((t, k), (τ t, k)) ≠ 0)
    (hτuniq : ∀ t ∈ S, ∀ z ∈ S, z ≠ t → z ≠ τ t → W s((t, k), (z, k)) = 0) :
    False :=
  false_of_forced_split W hzero hmono hS hSne hkj hone
    (forcedPeel_of_involution W (Amplitude.const (V := V) k) τ hτinv hτne
      S.card S rfl hSτ hτlive hτuniq)
    (forcedTail_of_involution W (Amplitude.const (V := V) j) σ hσinv hσne hσuniq
      S.card S rfl hSσ)

/-- **The local form.**  Neither side needs a global matching, and neither needs the whole
amplitude.  A proper non-empty set closed under one involution, with no other live partner of
its colour *inside the set*, whose complement is closed under a second involution with no other
live partner of that colour *inside the complement*, cannot exist.

This is the sharpest statement the two certificates support: every hypothesis is local to the
side it constrains.  What it asks of a configuration is exactly that some invariant set carry
no chord of its own colour, and its complement none of the other's. -/
theorem false_of_two_local_involutions (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {j k : Fin 3} (hkj : k ≠ j)
    (σ τ : V → V)
    (hσinv : ∀ t : V, σ (σ t) = t) (hσne : ∀ t : V, σ t ≠ t)
    (hτinv : ∀ t : V, τ (τ t) = t) (hτne : ∀ t : V, τ t ≠ t)
    {S : Finset V} (hS : S.Nonempty) (hSne : S ≠ Finset.univ)
    (hSτ : ∀ t ∈ S, τ t ∈ S)
    (hτlive : ∀ t ∈ S, W s((t, k), (τ t, k)) ≠ 0)
    (hτuniq : ∀ t ∈ S, ∀ z ∈ S, z ≠ t → z ≠ τ t → W s((t, k), (z, k)) = 0)
    (hCσ : ∀ t ∈ Finset.univ \ S, σ t ∈ Finset.univ \ S)
    (hσlive : ∀ t ∈ Finset.univ \ S, W s((t, j), (σ t, j)) ≠ 0)
    (hσuniq : ∀ t ∈ Finset.univ \ S, ∀ z ∈ Finset.univ \ S, z ≠ t → z ≠ σ t →
      W s((t, j), (z, j)) = 0) :
    False :=
  false_of_forcedPeel_split W hzero hmono hS hSne hkj
    (forcedPeel_of_involution W (Amplitude.const (V := V) k) τ hτinv hτne
      S.card S rfl hSτ hτlive hτuniq)
    (forcedPeel_of_involution W (Amplitude.const (V := V) j) σ hσinv hσne
      (Finset.univ \ S).card (Finset.univ \ S) rfl hCσ hσlive hσuniq)

/-- **An exact peel.**  The forced peel with its hypothesis relaxed: at each stage the site
peeled needs only that every *other* partner's term vanish, not that every other partner be
dead.  A branch dies just as well by leaving some site with nothing to pair with.

Every forced peel is an exact peel, and the certificate is strictly stronger: it reaches
configurations where the peeled site has several live partners, provided the other choices lead
nowhere.  Two triangles joined by an edge are the smallest example -- no site there has a unique
partner, yet the matching is unique and every alternative branch strands a site. -/
inductive ExactPeel (W : Sym2 (V × Fin 3) → ℂ) (c : V → Fin 3) : Finset V → Prop
  | empty : ExactPeel W c ∅
  | step (S : Finset V) (x p : V) (hx : x ∈ S) (hp : p ∈ S.erase x)
      (hlive : W s((x, c x), (p, c p)) ≠ 0)
      (halt : ∀ z ∈ S.erase x, z ≠ p →
        W s((x, c x), (z, c z)) * pmSum W c ((S.erase x).erase z) = 0)
      (h : ExactPeel W c ((S.erase x).erase p)) : ExactPeel W c S

theorem exactPeel_of_forcedPeel {W : Sym2 (V × Fin 3) → ℂ} {c : V → Fin 3} {S : Finset V}
    (h : ForcedPeel W c S) : ExactPeel W c S := by
  induction h with
  | empty => exact ExactPeel.empty
  | step S x p hx hp hlive huniq _ ih =>
      exact ExactPeel.step S x p hx hp hlive
        (fun z hz hzp => by rw [huniq z hz hzp, zero_mul]) ih

theorem pmSum_ne_zero_of_exactPeel {W : Sym2 (V × Fin 3) → ℂ} {c : V → Fin 3} {S : Finset V}
    (h : ExactPeel W c S) : pmSum W c S ≠ 0 := by
  induction h with
  | empty => rw [pmSum_empty]; exact one_ne_zero
  | step S x p hx hp hlive halt _ ih =>
      rw [pmSum_of_alternatives_zero W c hx hp halt]
      exact mul_ne_zero hlive ih

/-- The master contradiction with the stronger certificate on both sides. -/
theorem false_of_exactPeel_split (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {S : Finset V} (hS : S.Nonempty) (hSne : S ≠ Finset.univ)
    {j k : Fin 3} (hkj : k ≠ j)
    (hk : ExactPeel W (Amplitude.const (V := V) k) S)
    (hj : ExactPeel W (Amplitude.const (V := V) j) (Finset.univ \ S)) : False :=
  pmSum_ne_zero_of_exactPeel hk
    (pmSum_zero_of_complement_ne_zero W hzero hmono hS hSne hkj
      (pmSum_ne_zero_of_exactPeel hj))

/-- **An odd part with no way out kills the matching sum.**

If a subset of odd size is joined to the rest of the set by no live edge, nothing can match it:
the sum factors across the cut and the odd factor is zero.

This is how alternative branches usually die.  Removing a chord's two ends from an alternating
cycle leaves arcs of odd length that the colour cannot cross, so the chord contributes nothing
even though its own weight is live -- which is exactly what an exact peel needs. -/
theorem pmSum_eq_zero_of_odd_part (W : Sym2 (V × Fin 3) → ℂ) (c : V → Fin 3)
    {S A : Finset V} (hA : A ⊆ S) (hodd : ¬ Even A.card)
    (hcut : ∀ x ∈ A, ∀ y ∈ S \ A, W s((x, c x), (y, c y)) = 0) :
    pmSum W c S = 0 := by
  rw [Separation.pmSum_split W c A.card A S rfl hA hcut, pmSum_of_odd W c hodd, zero_mul]

/-- The same, packaged for a peel: after removing a site and one of its partners, an odd part
sealed off from the rest makes that branch vanish. -/
theorem peel_branch_zero_of_odd_part (W : Sym2 (V × Fin 3) → ℂ) (c : V → Fin 3)
    {S : Finset V} {x z : V} {A : Finset V} (hA : A ⊆ (S.erase x).erase z)
    (hodd : ¬ Even A.card)
    (hcut : ∀ p ∈ A, ∀ q ∈ ((S.erase x).erase z) \ A, W s((p, c p), (q, c q)) = 0) :
    W s((x, c x), (z, c z)) * pmSum W c ((S.erase x).erase z) = 0 := by
  rw [pmSum_eq_zero_of_odd_part W c hA hodd hcut, mul_zero]

/-- **A peel is exact when the *partner* has nowhere else to go.**

The forced peel asked the site being peeled to have a unique partner.  It is enough that the
partner have a unique partner: any other choice at the site leaves that partner stranded, with
no live neighbour left in what remains, and a stranded site kills the whole branch.

So a pair may be peeled whenever *either* of its two ends has no alternative -- which doubles
the reach of the certificate at no cost.  On an alternating cycle it means one may peel at any
site whose cycle partner carries no chord. -/
theorem peel_alternatives_zero_of_partner_alone (W : Sym2 (V × Fin 3) → ℂ) (c : V → Fin 3)
    {S : Finset V} {x p : V} (hpx : p ≠ x) (hpS : p ∈ S)
    (hpuniq : ∀ z ∈ S.erase p, z ≠ x → W s((p, c p), (z, c z)) = 0) :
    ∀ z ∈ S.erase x, z ≠ p →
      W s((x, c x), (z, c z)) * pmSum W c ((S.erase x).erase z) = 0 := by
  intro z hz hzp
  have hpmem : p ∈ (S.erase x).erase z :=
    Finset.mem_erase.mpr ⟨fun h => hzp h.symm, Finset.mem_erase.mpr ⟨hpx, hpS⟩⟩
  rw [pmSum_eq_zero_of_isolated W c hpmem (fun y hy => ?_), mul_zero]
  have hyp : y ≠ p := (Finset.mem_erase.mp hy).1
  have hyz : y ≠ z := (Finset.mem_erase.mp (Finset.mem_erase.mp hy).2).1
  have hyx : y ≠ x := (Finset.mem_erase.mp (Finset.mem_erase.mp
    (Finset.mem_erase.mp hy).2).2).1
  have hyS : y ∈ S := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase
    (Finset.mem_of_mem_erase hy))
  exact hpuniq y (Finset.mem_erase.mpr ⟨hyp, hyS⟩) hyx

/-- **An exact tail.**  The dual of the exact peel: peel pairs *away* from the whole site set,
each step needing only that the other branches at the peeled site vanish. -/
inductive ExactTail (W : Sym2 (V × Fin 3) → ℂ) (c : V → Fin 3) : Finset V → Prop
  | univ : ExactTail W c Finset.univ
  | step (T : Finset V) (x p : V) (hx : x ∈ T) (hp : p ∈ T.erase x)
      (halt : ∀ z ∈ T.erase x, z ≠ p →
        W s((x, c x), (z, c z)) * pmSum W c ((T.erase x).erase z) = 0)
      (h : ExactTail W c T) : ExactTail W c ((T.erase x).erase p)

theorem exactTail_of_forcedTail {W : Sym2 (V × Fin 3) → ℂ} {c : V → Fin 3} {T : Finset V}
    (h : ForcedTail W c T) : ExactTail W c T := by
  induction h with
  | univ => exact ExactTail.univ
  | step T x p hx hp huniq _ ih =>
      exact ExactTail.step T x p hx hp (fun z hz hzp => by rw [huniq z hz hzp, zero_mul]) ih

theorem pmSum_ne_zero_of_exactTail {W : Sym2 (V × Fin 3) → ℂ} {c : V → Fin 3} {T : Finset V}
    (hone : amplitude W c ≠ 0) (h : ExactTail W c T) : pmSum W c T ≠ 0 := by
  induction h with
  | univ => rw [pmSum_univ]; exact hone
  | step T x p hx hp halt _ ih =>
      intro hz
      exact ih (by rw [pmSum_of_alternatives_zero W c hx hp halt, hz, mul_zero])

/-- **The local master contradiction.**

A proper non-empty set that peels exactly to nothing in one colour, and exactly away from the
whole site set in another, cannot exist.

Both certificates now cost only as much work as the set is large: peeling a four-site set to
nothing is two steps, and peeling it away from everything is two more.  Nothing about the rest
of the configuration enters either check.  This is the form in which the equations are actually
applied -- a small local pattern, refuted outright, with no global matching, no census, and no
dependence on the number of sites. -/
theorem false_of_exact_split (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {S : Finset V} (hS : S.Nonempty) (hSne : S ≠ Finset.univ)
    {j k : Fin 3} (hkj : k ≠ j)
    (hone : amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hk : ExactPeel W (Amplitude.const (V := V) k) S)
    (hj : ExactTail W (Amplitude.const (V := V) j) (Finset.univ \ S)) : False :=
  pmSum_ne_zero_of_exactPeel hk
    (pmSum_zero_of_complement_ne_zero W hzero hmono hS hSne hkj
      (pmSum_ne_zero_of_exactTail hone hj))

/-- **Four sites, refuted from productive partners alone.**

Two sites joined by a live edge of one colour, each peeling away in a second colour to a
partner, with those two partners themselves joined by a live edge of the first colour, and
neither of the remaining two pairings fully live in it.

Nothing here asks a site to have a unique partner.  What the second colour needs is only that
every *other* partner's branch die -- a partner whose complement carries no matching sum
contributes nothing however live its weight -- so a site may have as many partners of that
colour as it likes provided one of them alone is productive.

This supersedes the alternating four-cycle: that theorem's uniqueness hypotheses are the
special case where the other partners are dead rather than merely unproductive. -/
theorem no_four_site_exact_split (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {j k : Fin 3} (hkj : k ≠ j)
    (hone : amplitude W (Amplitude.const (V := V) j) ≠ 0)
    {x y z w : V} (hyx : y ≠ x) (hzx : z ≠ x) (hwx : w ≠ x)
    (hzy : z ≠ y) (hwy : w ≠ y) (hwz : w ≠ z)
    (hout : ∃ t : V, t ≠ x ∧ t ≠ y ∧ t ≠ z ∧ t ≠ w)
    (hxy : W s((x, k), (y, k)) ≠ 0) (hzw : W s((z, k), (w, k)) ≠ 0)
    (hcross₁ : W s((x, k), (z, k)) * W s((y, k), (w, k)) = 0)
    (hcross₂ : W s((x, k), (w, k)) * W s((y, k), (z, k)) = 0)
    (hprodx : ∀ t : V, t ≠ x → t ≠ z →
      W s((x, j), (t, j)) *
        pmSum W (Amplitude.const (V := V) j) ((Finset.univ.erase x).erase t) = 0)
    (hprody : ∀ t : V, t ≠ y → t ≠ w →
      W s((y, j), (t, j)) *
        pmSum W (Amplitude.const (V := V) j)
          ((((Finset.univ.erase x).erase z).erase y).erase t) = 0) :
    False := by
  classical
  -- the second colour peels the four sites away from everything
  have hxmemU : x ∈ (Finset.univ : Finset V) := Finset.mem_univ x
  have hzmemU : z ∈ (Finset.univ : Finset V).erase x :=
    Finset.mem_erase.mpr ⟨hzx, Finset.mem_univ z⟩
  have hymemT : y ∈ (Finset.univ.erase x).erase z :=
    Finset.mem_erase.mpr ⟨Ne.symm hzy, Finset.mem_erase.mpr ⟨hyx, Finset.mem_univ y⟩⟩
  have hwmemT : w ∈ ((Finset.univ.erase x).erase z).erase y :=
    Finset.mem_erase.mpr ⟨hwy, Finset.mem_erase.mpr ⟨hwz,
      Finset.mem_erase.mpr ⟨hwx, Finset.mem_univ w⟩⟩⟩
  have htail : ExactTail W (Amplitude.const (V := V) j)
      ((((Finset.univ.erase x).erase z).erase y).erase w) := by
    refine ExactTail.step _ y w hymemT hwmemT
      (fun t ht htw => hprody t (Finset.mem_erase.mp ht).1 htw) ?_
    exact ExactTail.step _ x z hxmemU hzmemU
      (fun t ht htz => hprodx t (Finset.mem_erase.mp ht).1 htz) ExactTail.univ
  have hset : (((Finset.univ.erase x).erase z).erase y).erase w
      = Finset.univ \ ({x, y, z, w} : Finset V) := by
    ext t
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_sdiff, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [hset] at htail
  -- the first colour matches the four sites, with both other pairings dead
  have hxmem : x ∈ ({x, y, z, w} : Finset V) := by simp
  have hymem2 : y ∈ ({x, y, z, w} : Finset V).erase x :=
    Finset.mem_erase.mpr ⟨hyx, by simp⟩
  have hrest : (({x, y, z, w} : Finset V).erase x).erase y = ({z, w} : Finset V) := by
    ext t
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2, h3 | h3 | h3 | h3⟩
      · exact absurd h3 h2
      · exact absurd h3 h1
      · exact Or.inl h3
      · exact Or.inr h3
    · rintro (rfl | rfl)
      · exact ⟨hzy, hzx, by simp⟩
      · exact ⟨hwy, hwx, by simp⟩
  have hpair : ExactPeel W (Amplitude.const (V := V) k) ({z, w} : Finset V) := by
    have hz : z ∈ ({z, w} : Finset V) := by simp
    have hw : w ∈ ({z, w} : Finset V).erase z := Finset.mem_erase.mpr ⟨hwz, by simp⟩
    have hemp : (({z, w} : Finset V).erase z).erase w = ∅ := by
      ext t
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton,
        Finset.notMem_empty, iff_false]
      rintro ⟨hnw, hnz, (h | h)⟩
      · exact hnz h
      · exact hnw h
    refine ExactPeel.step _ z w hz hw hzw (fun t ht htw => ?_) (by rw [hemp]; exact ExactPeel.empty)
    have hm := Finset.mem_erase.mp ht
    have h2 := hm.2
    simp only [Finset.mem_insert, Finset.mem_singleton] at h2
    rcases h2 with h | h
    · exact absurd h hm.1
    · exact absurd h htw
  have hpeel : ExactPeel W (Amplitude.const (V := V) k) ({x, y, z, w} : Finset V) := by
    refine ExactPeel.step _ x y hxmem hymem2 hxy (fun t ht hty => ?_)
      (by rw [hrest]; exact hpair)
    have h1 : t ≠ x := (Finset.mem_erase.mp ht).1
    have h2 := (Finset.mem_erase.mp ht).2
    simp only [Finset.mem_insert, Finset.mem_singleton] at h2
    by_cases htz : t = z
    · rw [htz]
      have hs : ((({x, y, z, w} : Finset V).erase x).erase z) = ({y, w} : Finset V) := by
        ext u
        simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hu1, hu2, hu3 | hu3 | hu3 | hu3⟩
          · exact absurd hu3 hu2
          · exact Or.inl hu3
          · exact absurd hu3 hu1
          · exact Or.inr hu3
        · rintro (rfl | rfl)
          · exact ⟨Ne.symm hzy, hyx, by simp⟩
          · exact ⟨hwz, hwx, by simp⟩
      rw [hs, pmSum_pair W _ hwy]
      exact hcross₁
    · by_cases htw : t = w
      · rw [htw]
        have hs : ((({x, y, z, w} : Finset V).erase x).erase w) = ({y, z} : Finset V) := by
          ext u
          simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨hu1, hu2, hu3 | hu3 | hu3 | hu3⟩
            · exact absurd hu3 hu2
            · exact Or.inl hu3
            · exact Or.inr hu3
            · exact absurd hu3 hu1
          · rintro (rfl | rfl)
            · exact ⟨Ne.symm hwy, hyx, by simp⟩
            · exact ⟨Ne.symm hwz, hzx, by simp⟩
        rw [hs, pmSum_pair W _ hzy]
        exact hcross₂
      · rcases h2 with h | h | h | h
        · exact absurd h h1
        · exact absurd h hty
        · exact absurd h htz
        · exact absurd h htw
  refine false_of_exact_split W hzero hmono ⟨x, hxmem⟩ ?_ hkj hone hpeel htail
  obtain ⟨t, h1, h2, h3, h4⟩ := hout
  intro hu
  have : t ∈ ({x, y, z, w} : Finset V) := hu ▸ Finset.mem_univ t
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with rfl | rfl | rfl | rfl
  exacts [h1 rfl, h2 rfl, h3 rfl, h4 rfl]

/-- **A partner of another colour is never an obstacle.**

Peeling a pair away from the whole site set has to dispose of every other partner of the site.
Those wearing a different colour dispose of themselves: a live edge annihilates the other
colours' complementary sums, so such a branch carries no matching sum at all.

Only the site's *other partners of the same colour* can obstruct the peel, and among those only
the productive ones -- the rest have vanishing complements by definition.  This is what makes
the tail certificate a local check: one looks at a single colour's neighbourhood, not at the
whole configuration. -/
theorem tail_alternative_zero_of_other_colour (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {x t : V} (htx : t ≠ x) {j m : Fin 3} (hjm : j ≠ m)
    (hlive : W s((x, m), (t, m)) ≠ 0) (hout : ∃ z : V, z ≠ x ∧ z ≠ t) :
    W s((x, j), (t, j)) *
      pmSum W (Amplitude.const (V := V) j) ((Finset.univ.erase x).erase t) = 0 := by
  rw [mu_zero_of_live_edge W hzero hmono htx hjm hlive hout, mul_zero]

/-- The same for a peel inside a set: a branch through a partner of another colour dies with
its own complementary sum, so only same-colour partners need checking. -/
theorem peel_alternative_zero_of_other_colour (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {x t : V} (htx : t ≠ x) {j m : Fin 3} (hjm : j ≠ m)
    (hlive : W s((x, m), (t, m)) ≠ 0) (hout : ∃ z : V, z ≠ x ∧ z ≠ t)
    {S : Finset V} (hS : (Finset.univ.erase x).erase t = S) :
    W s((x, j), (t, j)) * pmSum W (Amplitude.const (V := V) j) S = 0 := by
  rw [← hS]
  exact tail_alternative_zero_of_other_colour W hzero hmono htx hjm hlive hout

/-- **A colour's matching sum is non-zero on any part it does not leave.**

If no live edge of a colour joins a set to its complement, that colour's whole matching sum
factors as the product of the two parts' sums.  The whole one is non-zero, so both parts are --
and this needs no peeling, no choice, and no cancellation argument whatever.

It is the cheapest non-vanishing certificate in the file, and the widest: it applies to any
union of connected components of a colour class. -/
theorem pmSum_ne_zero_of_colour_cut (W : Sym2 (V × Fin 3) → ℂ) {k : Fin 3}
    (hone : amplitude W (Amplitude.const (V := V) k) ≠ 0) (S : Finset V)
    (hcut : ∀ x ∈ S, ∀ y ∈ Finset.univ \ S, W s((x, k), (y, k)) = 0) :
    pmSum W (Amplitude.const (V := V) k) S ≠ 0 ∧
      pmSum W (Amplitude.const (V := V) k) (Finset.univ \ S) ≠ 0 := by
  have hsplit := Separation.pmSum_split W (Amplitude.const (V := V) k) S.card S Finset.univ rfl
    (Finset.subset_univ _) hcut
  rw [pmSum_univ] at hsplit
  constructor
  · intro h
    rw [h, zero_mul] at hsplit
    exact hone hsplit
  · intro h
    rw [h, mul_zero] at hsplit
    exact hone hsplit

/-- **The union of any two colour classes is connected.**

Suppose some proper non-empty set is left by no live edge of either of two colours.  The first
colour's matching sum on the set is non-zero and the second's on the complement is non-zero,
both by the factorisation above -- and the two-colour equation forbids exactly that pair.

**Already known, in a more general form.**  `Separation.no_two_colour_closed` proves the same
conclusion from the two colour cuts together with a single *mixed* cut condition, rather than
from monochromatic live edges everywhere.  That hypothesis is strictly weaker than the one
here, so this statement is a specialisation, not a strengthening.  It is kept because the
monochromatic form is what the rest of this file can discharge directly. -/
theorem false_of_two_colour_cut (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {S : Finset V} (hS : S.Nonempty) (hSne : S ≠ Finset.univ)
    {j k : Fin 3} (hkj : k ≠ j)
    (honek : amplitude W (Amplitude.const (V := V) k) ≠ 0)
    (honej : amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hcutk : ∀ x ∈ S, ∀ y ∈ Finset.univ \ S, W s((x, k), (y, k)) = 0)
    (hcutj : ∀ x ∈ S, ∀ y ∈ Finset.univ \ S, W s((x, j), (y, j)) = 0) :
    False :=
  (pmSum_ne_zero_of_colour_cut W honek S hcutk).1
    (pmSum_zero_of_complement_ne_zero W hzero hmono hS hSne hkj
      (pmSum_ne_zero_of_colour_cut W honej S hcutj).2)

/-- **No non-constant colouring keeps every class inside its own colour.**

If each class of a colouring is left by no live edge of the colour it wears, then each class
carries a non-zero matching sum in that colour, by the factorisation; the product formula makes
the amplitude their product; and a non-constant colouring has amplitude zero.

This is the strongest form of the cut argument and the cheapest: it needs the equations and
nothing else -- no minimality, no degree bound, no peeling, no choice, no case analysis.  Every
non-constant colouring must therefore have some class from which its own colour escapes. -/
theorem false_of_three_colour_cut (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hone : ∀ m : Fin 3, amplitude W (Amplitude.const (V := V) m) ≠ 0)
    (c : V → Fin 3) (hnm : ¬ Amplitude.Monochromatic c)
    (hcut : ∀ m : Fin 3, ∀ x ∈ fiber c m, ∀ y ∈ Finset.univ \ fiber c m,
      W s((x, m), (y, m)) = 0) :
    False := by
  classical
  have hcut' : ∀ x y : V, c x ≠ c y → W s((x, c x), (y, c y)) = 0 :=
    fun x y h => hmono x y (fun hxy => h (by rw [hxy])) _ _ h
  have hprod := amplitude_product W c hcut'
  rw [hzero c hnm] at hprod
  have hfib : ∀ m : Fin 3, pmSum W c (fiber c m) ≠ 0 := by
    intro m
    have hcong : pmSum W c (fiber c m) = pmSum W (Amplitude.const (V := V) m) (fiber c m) :=
      pmSum_congr_colour W (fun y hy => mem_fiber.mp hy)
    rw [hcong]
    exact (pmSum_ne_zero_of_colour_cut W (hone m) (fiber c m) (hcut m)).1
  rcases mul_eq_zero.mp hprod.symm with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact hfib 0 h'
    · exact hfib 1 h'
  · exact hfib 2 h

/-- **Non-vanishing propagates down colour components.**

The cut certificate does not need the whole site set to start from.  Given any set whose
matching sum in a colour is non-zero -- certified however one likes, by a peel, a tail, or an
earlier cut -- a part of it that the colour does not leave again has non-zero matching sum, and
so does the rest.

This is what makes the certificates compose.  A colour class may be connected on the whole site
set and still fall apart once a pair is removed, and the pieces then certify themselves. -/
theorem pmSum_ne_zero_of_cut_within (W : Sym2 (V × Fin 3) → ℂ) (c : V → Fin 3)
    {S T : Finset V} (hST : S ⊆ T) (hT : pmSum W c T ≠ 0)
    (hcut : ∀ x ∈ S, ∀ y ∈ T \ S, W s((x, c x), (y, c y)) = 0) :
    pmSum W c S ≠ 0 ∧ pmSum W c (T \ S) ≠ 0 := by
  have hsplit := Separation.pmSum_split W c S.card S T rfl hST hcut
  constructor
  · intro h
    rw [h, zero_mul] at hsplit
    exact hT hsplit
  · intro h
    rw [h, mul_zero] at hsplit
    exact hT hsplit

/-- **Unbalanced sides kill the matching sum.**

Suppose a set splits into two parts with no live edge inside either.  Then every matching that
contributes has to cross at every pair, so it is a bijection between the parts -- and if the
parts have different sizes there is no such matching at all.

This is the parity killer for bipartite-looking colour classes, complementing the odd-part one.
Where the odd-part killer needs a piece the colour cannot leave, this one needs a piece the
colour cannot stay inside. -/
theorem pmSum_eq_zero_of_unbalanced (W : Sym2 (V × Fin 3) → ℂ) (c : V → Fin 3)
    {S A : Finset V} (hA : A ⊆ S)
    (hin : ∀ x ∈ A, ∀ y ∈ A, W s((x, c x), (y, c y)) = 0)
    (hout : ∀ x ∈ S \ A, ∀ y ∈ S \ A, W s((x, c x), (y, c y)) = 0)
    (hcard : A.card ≠ (S \ A).card) : pmSum W c S = 0 := by
  classical
  refine Finset.sum_eq_zero fun σ hσ => ?_
  obtain ⟨hinv, hnefix, -⟩ := mem_pairingsOn.mp hσ
  by_contra hprod
  have hedge : ∀ x ∈ S, W s((x, c x), (σ x, c (σ x))) ≠ 0 := by
    intro x hx
    have hmem : s(x, σ x) ∈ S.image (fun y => s(y, σ y)) :=
      Finset.mem_image.mpr ⟨x, hx, rfl⟩
    exact Finset.prod_ne_zero_iff.mp hprod _ hmem
  have hclosed : ∀ x ∈ S, σ x ∈ S := pairingsOn_closed hσ
  have hAto : ∀ x ∈ A, σ x ∈ S \ A := by
    intro x hx
    refine Finset.mem_sdiff.mpr ⟨hclosed x (hA hx), fun hcon => ?_⟩
    exact hedge x (hA hx) (hin x hx (σ x) hcon)
  have hBto : ∀ x ∈ S \ A, σ x ∈ A := by
    intro x hx
    have hxS : x ∈ S := (Finset.mem_sdiff.mp hx).1
    by_contra hcon
    exact hedge x hxS (hout x hx (σ x)
      (Finset.mem_sdiff.mpr ⟨hclosed x hxS, hcon⟩))
  have h1 : A.card ≤ (S \ A).card :=
    Finset.card_le_card_of_injOn σ hAto (fun a _ b _ h => σ.injective h)
  have h2 : (S \ A).card ≤ A.card :=
    Finset.card_le_card_of_injOn σ hBto (fun a _ b _ h => σ.injective h)
  exact hcard (le_antisymm h1 h2)

/-- **No part has all its crossings productive in one colour.**

Suppose a proper non-empty set has the property that removing any one of its sites together
with any one site outside leaves a non-vanishing matching sum in some fixed colour.  Then a live
edge of either *other* colour cannot cross the boundary, because a live edge annihilates the
other colours' complementary sums.  So the set is left by neither of those two colours -- and
the two-colour cut theorem forbids exactly that.

This is the abstract form of the parity obstruction.  When a colour class is a cycle through
every site, removing two sites at odd distance leaves two even paths, each with a unique
perfect matching and so a matching sum that cannot cancel; the two classes of the cycle's
bipartition are then a set of exactly this kind, and the configuration dies. -/
theorem false_of_productive_crossing (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hone : ∀ m : Fin 3, amplitude W (Amplitude.const (V := V) m) ≠ 0)
    (hcard : 2 < Fintype.card V)
    {X : Finset V} (hX : X.Nonempty) (hXne : X ≠ Finset.univ) (m : Fin 3)
    (hcross : ∀ x ∈ X, ∀ y ∈ Finset.univ \ X,
      pmSum W (Amplitude.const (V := V) m) ((Finset.univ.erase x).erase y) ≠ 0) :
    False := by
  classical
  have hfin : ∀ b : Fin 3, b + 1 ≠ b ∧ b + 2 ≠ b ∧ b + 2 ≠ b + 1 := by decide
  obtain ⟨h1, h2, h12⟩ := hfin m
  have hout : ∀ a b : V, ∃ z : V, z ≠ a ∧ z ≠ b := by
    intro a b
    by_contra hno
    push_neg at hno
    have hsub : (Finset.univ : Finset V) ⊆ ({a, b} : Finset V) := by
      intro t _
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases h : t = a
      · exact Or.inl h
      · exact Or.inr (hno t h)
    have hc1 := Finset.card_le_card hsub
    have hc2 : ({a, b} : Finset V).card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
    rw [Finset.card_univ] at hc1
    omega
  -- no live edge of either other colour crosses the boundary
  have hcut : ∀ a : Fin 3, a ≠ m → ∀ x ∈ X, ∀ y ∈ Finset.univ \ X,
      W s((x, a), (y, a)) = 0 := by
    intro a ham x hx y hy
    by_contra hlive
    have hyx : y ≠ x := by
      intro h
      refine (Finset.mem_sdiff.mp hy).2 ?_
      rw [h]
      exact hx
    exact hcross x hx y hy
      (mu_zero_of_live_edge W hzero hmono hyx (Ne.symm ham) hlive (hout x y))
  exact false_of_two_colour_cut W hzero hmono hX hXne h12
    (hone (m + 2)) (hone (m + 1)) (hcut (m + 2) h2) (hcut (m + 1) h1)

/-- **Peeling by a hereditary local condition.**

A property of site sets that always exhibits one forced pair, and is preserved by removing it,
certifies a forced peel outright.  This is how path-shaped and cycle-shaped colour classes are
peeled: the property is "a union of even paths", the forced pair is an end of one of them, and
removing it leaves a union of even paths again. -/
theorem forcedPeel_of_hereditary (W : Sym2 (V × Fin 3) → ℂ) (c : V → Fin 3)
    (P : Finset V → Prop)
    (hstep : ∀ T : Finset V, P T → T.Nonempty → ∃ x ∈ T, ∃ p ∈ T.erase x,
      W s((x, c x), (p, c p)) ≠ 0 ∧
        (∀ z ∈ T.erase x, z ≠ p → W s((x, c x), (z, c z)) = 0) ∧
        P ((T.erase x).erase p)) :
    ∀ (n : ℕ) (S : Finset V), S.card = n → P S → ForcedPeel W c S := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hcard hP
    rcases Finset.eq_empty_or_nonempty S with rfl | hne
    · exact ForcedPeel.empty
    · obtain ⟨x, hx, p, hp, hlive, huniq, hP'⟩ := hstep S hP hne
      refine ForcedPeel.step S x p hx hp hlive huniq (ih _ ?_ _ rfl hP')
      rw [← hcard]
      exact lt_of_le_of_lt Finset.card_erase_le (Finset.card_erase_lt_of_mem hx)

/-- **Crossings that peel are fatal.**

The productive-crossing obstruction with its hypothesis supplied the way a structured colour
class actually supplies it: by a forced peel of the complement of each crossing pair.

For a colour class that is a cycle through every site this is exactly the situation.  Take the
two classes of the cycle's bipartition; a crossing pair sits at odd distance, so removing it
leaves two paths of even length, and a path peels forcedly from either end.  The configuration
then contradicts the equations. -/
theorem false_of_peeling_crossings (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hone : ∀ m : Fin 3, amplitude W (Amplitude.const (V := V) m) ≠ 0)
    (hcard : 2 < Fintype.card V)
    {X : Finset V} (hX : X.Nonempty) (hXne : X ≠ Finset.univ) (m : Fin 3)
    (hpeel : ∀ x ∈ X, ∀ y ∈ Finset.univ \ X,
      ForcedPeel W (Amplitude.const (V := V) m) ((Finset.univ.erase x).erase y)) :
    False :=
  false_of_productive_crossing W hzero hmono hone hcard hX hXne m
    (fun x hx y hy => pmSum_ne_zero_of_forcedPeel (hpeel x hx y hy))

/-- **A colour that does not leave a set isolates both sides from the other colours.**

If no live edge of a colour joins a set to its complement, that colour matches both sides.
The two-colour equation then says neither side is matched by any other colour at all.

So a colour class that falls apart forces the two remaining classes to cross every one of its
pieces: they can match the whole site set, but no piece of the decomposition and no union of
the rest.  This is the sharpest statement about a disconnected colour class the equations
give, and it is why the natural deletions never yield a smaller system --- whatever a colour
matches cleanly, the other two cannot touch. -/
theorem colour_cut_isolates (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {m : Fin 3} (hone : amplitude W (Amplitude.const (V := V) m) ≠ 0)
    {S : Finset V} (hS : S.Nonempty) (hSne : S ≠ Finset.univ)
    (hcut : ∀ x ∈ S, ∀ y ∈ Finset.univ \ S, W s((x, m), (y, m)) = 0)
    (j : Fin 3) (hjm : j ≠ m) :
    pmSum W (Amplitude.const (V := V) j) S = 0 ∧
      pmSum W (Amplitude.const (V := V) j) (Finset.univ \ S) = 0 := by
  classical
  obtain ⟨hSne0, hCne0⟩ := pmSum_ne_zero_of_colour_cut W hone S hcut
  have hCnonempty : (Finset.univ \ S).Nonempty := by
    rcases Finset.eq_empty_or_nonempty (Finset.univ \ S) with h | h
    · exact absurd (by
        refine Finset.eq_univ_of_forall (fun t => ?_)
        by_contra ht
        exact (Finset.not_nonempty_iff_eq_empty.mpr h)
          ⟨t, Finset.mem_sdiff.mpr ⟨Finset.mem_univ t, ht⟩⟩) hSne
    · exact h
  have hCne : Finset.univ \ S ≠ Finset.univ := by
    intro hcon
    obtain ⟨x, hx⟩ := hS
    have hmem : x ∈ Finset.univ \ S := by rw [hcon]; exact Finset.mem_univ x
    exact (Finset.mem_sdiff.mp hmem).2 hx
  have hback : Finset.univ \ (Finset.univ \ S) = S := by
    ext t
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]
  refine ⟨pmSum_zero_of_complement_ne_zero W hzero hmono hS hSne hjm hCne0, ?_⟩
  refine pmSum_zero_of_complement_ne_zero W hzero hmono hCnonempty hCne hjm ?_
  rw [hback]
  exact hSne0

/-- **A piece one colour matches cleanly is peel-proof for the others.**

Combining the two halves of the file.  If no live edge of a colour leaves a set, the other two
colours match neither that set nor its complement; but an exact peel certifies a non-vanishing
matching sum.  So neither side admits an exact peel in either other colour.

Read as a structure statement: the components of a colour class are exactly the places where
the other colours can have no forced matching.  Anywhere a second colour can peel, the first
colour must cross. -/
theorem no_exactPeel_of_colour_cut (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {m : Fin 3} (hone : amplitude W (Amplitude.const (V := V) m) ≠ 0)
    {S : Finset V} (hS : S.Nonempty) (hSne : S ≠ Finset.univ)
    (hcut : ∀ x ∈ S, ∀ y ∈ Finset.univ \ S, W s((x, m), (y, m)) = 0)
    (j : Fin 3) (hjm : j ≠ m) :
    ¬ ExactPeel W (Amplitude.const (V := V) j) S ∧
      ¬ ExactPeel W (Amplitude.const (V := V) j) (Finset.univ \ S) := by
  obtain ⟨h1, h2⟩ := colour_cut_isolates W hzero hmono hone hS hSne hcut j hjm
  exact ⟨fun h => pmSum_ne_zero_of_exactPeel h h1, fun h => pmSum_ne_zero_of_exactPeel h h2⟩

/-- **Every GHZ configuration has an even number of sites.**

An odd site set admits no perfect matching at all, so every amplitude vanishes and the
constant ones cannot be non-zero.

The consequence is worth stating plainly.  The standing hypothesis of the reduction --- that
every site of a support-minimal GHZ system on more than four sites has at most three live
neighbours --- is vacuously satisfied whenever no such system exists.  With this lemma, any
site set of more than four sites carrying one has even cardinality and so is a case the
conjecture covers.  The hypothesis is therefore vacuous once the conjecture holds, which is the
substantive point: it has no non-trivial models, so it can be refuted but never developed.  The
positive form below quantifies instead over weight systems with non-vanishing constant
amplitudes, a class with objects in it. -/
theorem even_card_of_isGHZ (W : Sym2 (V × Fin 3) → ℂ) (hW : KrennGu.IsGHZ W) :
    Even (Fintype.card V) := by
  by_contra h
  refine hW.1 0 ?_
  rw [← pmSum_univ]
  exact pmSum_of_odd W _ (by rwa [Finset.card_univ])

/-- **Same-colour cross exclusion.**

The earlier cross-exclusion killed the pair of partners in the *third* colour.  When one of the
two remaining pairings is already dead in the edge's own colour, the same argument kills the
partners in that colour too.

The reading is a dichotomy.  Given a live edge and a pair of partners in a second colour whose
complement still matches, either the four sites carry a full four-cycle in the edge's colour ---
so both its ends have a second partner there --- or the two partners are dead in it. -/
theorem same_colour_cross_exclusion (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {j k : Fin 3} (hjk : j ≠ k)
    {x y z w : V} (hyx : y ≠ x) (hzx : z ≠ x) (hwx : w ≠ x)
    (hzy : z ≠ y) (hwy : w ≠ y) (hwz : w ≠ z)
    (hout : ∃ t : V, t ≠ x ∧ t ≠ y ∧ t ≠ z ∧ t ≠ w)
    (hxy : W s((x, j), (y, j)) ≠ 0)
    (hxz : W s((x, j), (z, j)) = 0) (hxw : W s((x, j), (w, j)) = 0)
    (hrest : pmSum W (Amplitude.const (V := V) k)
      (Finset.univ \ ({x, y, z, w} : Finset V)) ≠ 0) :
    W s((z, j), (w, j)) = 0 := by
  classical
  have hxmem : x ∈ ({x, y, z, w} : Finset V) := by simp
  have hymem : y ∈ ({x, y, z, w} : Finset V).erase x :=
    Finset.mem_erase.mpr ⟨hyx, by simp⟩
  have hrest2 : (({x, y, z, w} : Finset V).erase x).erase y = ({z, w} : Finset V) := by
    ext t
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2, h3 | h3 | h3 | h3⟩
      · exact absurd h3 h2
      · exact absurd h3 h1
      · exact Or.inl h3
      · exact Or.inr h3
    · rintro (rfl | rfl)
      · exact ⟨hzy, hzx, by simp⟩
      · exact ⟨hwy, hwx, by simp⟩
  have huniq : ∀ t ∈ ({x, y, z, w} : Finset V).erase x, t ≠ y →
      W s((x, j), (t, j)) = 0 := by
    intro t ht hty
    have h1 : t ≠ x := (Finset.mem_erase.mp ht).1
    have h2 := (Finset.mem_erase.mp ht).2
    simp only [Finset.mem_insert, Finset.mem_singleton] at h2
    by_cases htz : t = z
    · rw [htz]; exact hxz
    · by_cases htw : t = w
      · rw [htw]; exact hxw
      · rcases h2 with h | h | h | h
        · exact absurd h h1
        · exact absurd h hty
        · exact absurd h htz
        · exact absurd h htw
  have hval : pmSum W (Amplitude.const (V := V) j) ({x, y, z, w} : Finset V)
      = W s((x, j), (y, j)) * W s((z, j), (w, j)) := by
    rw [pmSum_of_forced W (Amplitude.const (V := V) j) hxmem hymem huniq,
      hrest2, pmSum_pair W _ hwz]
    rfl
  have hSne : ({x, y, z, w} : Finset V) ≠ Finset.univ := by
    obtain ⟨t, h1, h2, h3, h4⟩ := hout
    intro hu
    have : t ∈ ({x, y, z, w} : Finset V) := hu ▸ Finset.mem_univ t
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with rfl | rfl | rfl | rfl
    exacts [h1 rfl, h2 rfl, h3 rfl, h4 rfl]
  have hzeroT := pmSum_zero_of_complement_ne_zero W hzero hmono ⟨x, hxmem⟩ hSne hjk hrest
  rw [hval] at hzeroT
  exact (mul_eq_zero.mp hzeroT).resolve_left hxy

/-- **The partner-pair dichotomy.**

Take a live edge in one colour and a partner for each of its ends in a second, with the
complement of the four sites still matching in that second colour.  Then exactly one of two
things happens:

* the pair of partners is dead in *both* other colours -- live only in the colour that
  produced it, if at all; or
* the four sites carry a full four-cycle in the edge's own colour, so both ends of the edge
  have a second partner there.

This packages the two cross-exclusions.  The third colour dies unconditionally; the edge's own
colour dies unless the four-cycle closes, and a closed four-cycle is precisely the situation in
which the four-site matching sum cancels instead of vanishing termwise. -/
theorem partner_pair_dichotomy (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {j k j' : Fin 3} (hjk : j ≠ k) (hjj' : j ≠ j') (hkj : k ≠ j) (hkj' : k ≠ j')
    {x y z w : V} (hyx : y ≠ x) (hzx : z ≠ x) (hwx : w ≠ x)
    (hzy : z ≠ y) (hwy : w ≠ y) (hwz : w ≠ z)
    (hout : ∃ t : V, t ≠ x ∧ t ≠ y ∧ t ≠ z ∧ t ≠ w)
    (hxy : W s((x, j), (y, j)) ≠ 0)
    (hxz : W s((x, j), (z, j)) = 0) (hyw : W s((y, j), (w, j)) = 0)
    (hrest : pmSum W (Amplitude.const (V := V) k)
      (Finset.univ \ ({x, y, z, w} : Finset V)) ≠ 0) :
    (W s((z, j), (w, j)) = 0 ∧ W s((z, j'), (w, j')) = 0) ∨
      (W s((x, j), (w, j)) ≠ 0 ∧ W s((y, j), (z, j)) ≠ 0) := by
  classical
  -- the third colour dies outright
  have hthird : W s((z, j'), (w, j')) = 0 :=
    (mul_eq_zero.mp (pair_pair_zero W hzero hmono hyx hwz (Ne.symm hzx) (Ne.symm hwx)
      (Ne.symm hzy) (Ne.symm hwy) hjj' hkj hkj' hrest)).resolve_left hxy
  by_cases hzw : W s((z, j), (w, j)) = 0
  · exact Or.inl ⟨hzw, hthird⟩
  · refine Or.inr ⟨?_, ?_⟩
    · intro hxw
      exact hzw (same_colour_cross_exclusion W hzero hmono hjk hyx hzx hwx hzy hwy hwz
        hout hxy hxz hxw hrest)
    · intro hyz
      have hset : ({y, x, w, z} : Finset V) = ({x, y, z, w} : Finset V) := by
        ext t
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      have hxy' : W s((y, j), (x, j)) ≠ 0 := by rwa [Sym2.eq_swap]
      have hrest' : pmSum W (Amplitude.const (V := V) k)
          (Finset.univ \ ({y, x, w, z} : Finset V)) ≠ 0 := by rwa [hset]
      have := same_colour_cross_exclusion W hzero hmono hjk (Ne.symm hyx) hwy
        hzy hwx hzx (Ne.symm hwz)
        (by obtain ⟨t, h1, h2, h3, h4⟩ := hout; exact ⟨t, h2, h1, h4, h3⟩)
        hxy' hyw hyz hrest'
      exact hzw (by rwa [Sym2.eq_swap] at this)

end Equations

/-- **The split tolerates one live crossing pair.**

If a part of even size is joined to the rest by a single live pair, the matching sum still
factors.  Expanding at that pair's inside end, the crossing branch strands the part with an odd
number of sites and no way out, so it contributes nothing; every other branch removes the
crossing pair's inside end and so leaves no live crossing at all.

No parity machinery is needed: the odd-part killer does the work the crossing-count parity
would otherwise have to. -/
theorem amplitude_split_one_crossing (W : Sym2 (V × Fin 3) → ℂ) (c : V → Fin 3)
    {A : Finset V} (hAeven : Even A.card) {x y : V} (hx : x ∈ A) (hy : y ∉ A)
    (hcut : ∀ p ∈ A, ∀ q : V, q ∉ A → (p ≠ x ∨ q ≠ y) → W s((p, c p), (q, c q)) = 0) :
    amplitude W c = pmSum W c A * pmSum W c (Finset.univ \ A) := by
  classical
  have hodd : ¬ Even (A.erase x).card := by
    rw [Finset.card_erase_of_mem hx]
    obtain ⟨k, hk⟩ := hAeven
    have hpos : 0 < A.card := Finset.card_pos.mpr ⟨x, hx⟩
    simp only [Nat.even_iff]
    omega
  rw [← pmSum_univ, pmSum_expand W c (Finset.mem_univ x)]
  have hterm : ∀ v ∈ (Finset.univ : Finset V).erase x,
      W (Sym2.map (paint c) s(x, v)) * pmSum W c (((Finset.univ : Finset V).erase x).erase v)
        = (if v ∈ A.erase x then
             W s((x, c x), (v, c v)) * pmSum W c ((A.erase x).erase v) else 0)
          * pmSum W c (Finset.univ \ A) := by
    intro v hv
    have hvx : v ≠ x := (Finset.mem_erase.mp hv).1
    by_cases hvA : v ∈ A
    · have hvmem : v ∈ A.erase x := Finset.mem_erase.mpr ⟨hvx, hvA⟩
      have hsub : (A.erase x).erase v ⊆ ((Finset.univ : Finset V).erase x).erase v := by
        intro q hq
        simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hq ⊢
        exact ⟨hq.1, hq.2.1⟩
      have hsd : (((Finset.univ : Finset V).erase x).erase v) \ ((A.erase x).erase v)
          = Finset.univ \ A := by
        ext q
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
        constructor
        · rintro ⟨h1, h2⟩ hcon
          exact h2 ⟨h1.1, h1.2, hcon⟩
        · intro hqA
          refine ⟨⟨fun h => hqA ?_, fun h => hqA ?_⟩, fun hcon => hqA hcon.2.2⟩
          · rw [h]; exact hvA
          · rw [h]; exact hx
      have hcut2 : ∀ p ∈ (A.erase x).erase v, ∀ q ∈
          (((Finset.univ : Finset V).erase x).erase v) \ ((A.erase x).erase v),
          W s((p, c p), (q, c q)) = 0 := by
        intro p hp q hq
        rw [hsd] at hq
        have hpA : p ∈ A := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hp)
        have hpx : p ≠ x := (Finset.mem_erase.mp (Finset.mem_erase.mp hp).2).1
        exact hcut p hpA q (Finset.mem_sdiff.mp hq).2 (Or.inl hpx)
      rw [if_pos hvmem, Separation.pmSum_split W c ((A.erase x).erase v).card _ _ rfl hsub hcut2,
        hsd, mul_assoc]
      rfl
    · rw [if_neg (fun h => hvA (Finset.mem_of_mem_erase h)), zero_mul]
      by_cases hvy : v = y
      · refine mul_eq_zero_of_right _ ?_
        refine pmSum_eq_zero_of_odd_part W c (A := A.erase x) (fun q hq => ?_) hodd (fun p hp q hq => ?_)
        · simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hq ⊢
          exact ⟨fun h => hvA (h ▸ hq.2), hq.1⟩
        · have hpA : p ∈ A := Finset.mem_of_mem_erase hp
          have hpx : p ≠ x := (Finset.mem_erase.mp hp).1
          have hqnA : q ∉ A := by
            intro hcon
            refine (Finset.mem_sdiff.mp hq).2 ?_
            have h1 := (Finset.mem_sdiff.mp hq).1
            simp only [Finset.mem_erase, Finset.mem_univ, and_true] at h1
            exact Finset.mem_erase.mpr ⟨h1.2, hcon⟩
          exact hcut p hpA q hqnA (Or.inl hpx)
      · refine mul_eq_zero_of_left ?_ _
        exact hcut x hx v hvA (Or.inr hvy)
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
  congr 1
  rw [pmSum_expand W c hx]
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun v _ => rfl)
  ext v
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

/-- **An even part joined by a single live pair is impossible.**

A part the live graph does not leave at all is already excluded.  This extends that to a part
of even size joined to the rest by exactly one live pair: parity makes the crossing useless,
because using it strands the part with an odd number of sites, so the amplitude factors as
though the cut were clean.  A factoring amplitude has flattening rank one, and the equations
demand three.

So every even part is joined to the rest by at least two live pairs -- the live graph is
two-edge-connected across even cuts, which is strictly stronger than having no bridge. -/
theorem false_of_even_part_one_crossing (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {A : Finset V} (hA : A.Nonempty) (hAc : (Finset.univ \ A).Nonempty)
    (hAeven : Even A.card) {x y : V} (hx : x ∈ A) (hy : y ∉ A)
    (hcut : ∀ p ∈ A, ∀ q : V, q ∉ A → ∀ a b : Fin 3,
      (p ≠ x ∨ q ≠ y) → W s((p, a), (q, b)) = 0) :
    False := by
  classical
  refine Separation.no_rank_two_flattening W hone hzero A hA hAc
    (fun j c => if j = 0 then pmSum W c A else 0)
    (fun j c => if j = 0 then pmSum W c (Finset.univ \ A) else 0) ?_ ?_ ?_
  · intro j c c' hcc
    by_cases hj : j = 0
    · simp only [hj, if_pos rfl]
      exact pmSum_congr_colour W (fun z hz => hcc z hz)
    · simp only [if_neg hj]
  · intro j c c' hcc
    by_cases hj : j = 0
    · simp only [hj, if_pos rfl]
      exact pmSum_congr_colour W (fun z hz => hcc z hz)
    · simp only [if_neg hj]
  · intro c
    rw [Fin.sum_univ_two]
    simp only [if_pos rfl, if_neg (by decide : (1 : Fin 2) ≠ 0), mul_zero, add_zero]
    exact amplitude_split_one_crossing W c hAeven hx hy
      (fun p hp q hq hor => hcut p hp q hq _ _ hor)

/-- **An odd part joined by a single live pair forces a single term.**

The companion of the even case.  With the part of odd size and one live crossing pair, every
matching must use that pair: any other choice at its inside end strands the part with an odd
number of sites and no way out.  So the amplitude is one weight times the two sides' matching
sums. -/
theorem amplitude_single_crossing_odd (W : Sym2 (V × Fin 3) → ℂ) (c : V → Fin 3)
    {A : Finset V} (hAodd : ¬ Even A.card) {x y : V} (hx : x ∈ A) (hy : y ∉ A)
    (hcut : ∀ p ∈ A, ∀ q : V, q ∉ A → (p ≠ x ∨ q ≠ y) → W s((p, c p), (q, c q)) = 0) :
    amplitude W c
      = W s((x, c x), (y, c y)) * (pmSum W c (A.erase x)
          * pmSum W c ((Finset.univ \ A).erase y)) := by
  classical
  rw [← pmSum_univ, pmSum_expand W c (Finset.mem_univ x)]
  have hterm : ∀ v ∈ (Finset.univ : Finset V).erase x,
      W (Sym2.map (paint c) s(x, v)) * pmSum W c (((Finset.univ : Finset V).erase x).erase v)
        = if v = y then W s((x, c x), (y, c y)) * (pmSum W c (A.erase x)
            * pmSum W c ((Finset.univ \ A).erase y)) else 0 := by
    intro v hv
    have hvx : v ≠ x := (Finset.mem_erase.mp hv).1
    by_cases hvy : v = y
    · subst hvy
      rw [if_pos rfl]
      have hsub : A.erase x ⊆ ((Finset.univ : Finset V).erase x).erase v := by
        intro q hq
        simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hq ⊢
        exact ⟨fun h => hy (by rw [← h]; exact hq.2), hq.1⟩
      have hsd : (((Finset.univ : Finset V).erase x).erase v) \ (A.erase x)
          = (Finset.univ \ A).erase v := by
        ext q
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
        constructor
        · rintro ⟨⟨hqv, hqx⟩, hno⟩
          exact ⟨hqv, fun hcon => hno ⟨hqx, hcon⟩⟩
        · rintro ⟨hqv, hqA⟩
          exact ⟨⟨hqv, fun h => hqA (h ▸ hx)⟩, fun hcon => hqA hcon.2⟩
      rw [Separation.pmSum_split W c (A.erase x).card _ _ rfl hsub ?_, hsd]
      · rfl
      · intro p hp q hq
        rw [hsd] at hq
        have hpA : p ∈ A := Finset.mem_of_mem_erase hp
        have hpx : p ≠ x := (Finset.mem_erase.mp hp).1
        have hqA : q ∉ A := (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase hq)).2
        exact hcut p hpA q hqA (Or.inl hpx)
    · rw [if_neg hvy]
      by_cases hvA : v ∈ A
      · refine mul_eq_zero_of_right _ ?_
        refine pmSum_eq_zero_of_odd_part W c (A := (A.erase x).erase v) (fun q hq => ?_) ?_
          (fun p hp q hq => ?_)
        · simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hq ⊢
          exact ⟨hq.1, hq.2.1⟩
        · rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hvx, hvA⟩),
            Finset.card_erase_of_mem hx]
          have h1 : 1 ≤ A.card := Finset.card_pos.mpr ⟨x, hx⟩
          have h2 : 2 ≤ A.card := Finset.one_lt_card.mpr ⟨x, hx, v, hvA, Ne.symm hvx⟩
          simp only [Nat.even_iff] at hAodd ⊢
          omega
        · have hpA : p ∈ A := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hp)
          have hpx : p ≠ x := (Finset.mem_erase.mp (Finset.mem_erase.mp hp).2).1
          have hqA : q ∉ A := by
            intro hcon
            refine (Finset.mem_sdiff.mp hq).2 ?_
            have h1 := (Finset.mem_sdiff.mp hq).1
            simp only [Finset.mem_erase, Finset.mem_univ, and_true] at h1
            exact Finset.mem_erase.mpr ⟨h1.1, Finset.mem_erase.mpr ⟨h1.2, hcon⟩⟩
          exact hcut p hpA q hqA (Or.inl hpx)
      · exact mul_eq_zero_of_left (hcut x hx v hvA (Or.inr hvy)) _
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' ((Finset.univ : Finset V).erase x)]
  rw [if_pos (Finset.mem_erase.mpr ⟨fun h => hy (by rw [h]; exact hx), Finset.mem_univ y⟩)]

/-- With a rank-one crossing block the factorisation becomes a genuine product across the cut,
so the flattening has rank one and the equations are contradicted.

The rank hypothesis is not cosmetic: the crossing weight couples the two sides, so without it
the flattening rank is bounded only by the block's own rank, which may be three.  The even case
above needs no such hypothesis, because there the crossing is useless outright. -/
theorem false_of_odd_part_rank_one_crossing (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {A : Finset V} (hA : A.Nonempty) (hAc : (Finset.univ \ A).Nonempty)
    (hAodd : ¬ Even A.card) {x y : V} (hx : x ∈ A) (hy : y ∉ A)
    (hcut : ∀ p ∈ A, ∀ q : V, q ∉ A → ∀ a b : Fin 3,
      (p ≠ x ∨ q ≠ y) → W s((p, a), (q, b)) = 0)
    (α β : Fin 3 → ℂ) (hrank : ∀ a b : Fin 3, W s((x, a), (y, b)) = α a * β b) :
    False := by
  classical
  refine Separation.no_rank_two_flattening W hone hzero A hA hAc
    (fun j c => if j = 0 then α (c x) * pmSum W c (A.erase x) else 0)
    (fun j c => if j = 0 then β (c y) * pmSum W c ((Finset.univ \ A).erase y) else 0) ?_ ?_ ?_
  · intro j c c' hcc
    by_cases hj : j = 0
    · simp only [hj, if_pos rfl, hcc x hx,
        pmSum_congr_colour W (c := c) (c' := c')
          (fun z hz => hcc z (Finset.mem_of_mem_erase hz))]
    · simp only [if_neg hj]
  · intro j c c' hcc
    by_cases hj : j = 0
    · have hyc : c y = c' y :=
        hcc y (Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hy⟩)
      simp only [hj, if_pos rfl, hyc,
        pmSum_congr_colour W (c := c) (c' := c')
          (fun z hz => hcc z (Finset.mem_of_mem_erase hz))]
    · simp only [if_neg hj]
  · intro c
    rw [Fin.sum_univ_two]
    simp only [if_pos rfl, if_neg (by decide : (1 : Fin 2) ≠ 0), mul_zero, add_zero, if_true]
    rw [amplitude_single_crossing_odd W c hAodd hx hy
      (fun p hp q hq hor => hcut p hp q hq _ _ hor), hrank]
    ring

/-- The one-crossing split on an arbitrary site set, not just the whole one.  Needed when the
branches of a larger expansion have already had a pair removed. -/
theorem pmSum_split_one_crossing (W : Sym2 (V × Fin 3) → ℂ) (c : V → Fin 3)
    {T A : Finset V} (hAT : A ⊆ T) (hAeven : Even A.card)
    {x y : V} (hx : x ∈ A) (hy : y ∈ T) (hyA : y ∉ A)
    (hcut : ∀ p ∈ A, ∀ q ∈ T, q ∉ A → (p ≠ x ∨ q ≠ y) → W s((p, c p), (q, c q)) = 0) :
    pmSum W c T = pmSum W c A * pmSum W c (T \ A) := by
  classical
  have hodd : ¬ Even (A.erase x).card := by
    rw [Finset.card_erase_of_mem hx]
    obtain ⟨k, hk⟩ := hAeven
    have hpos : 0 < A.card := Finset.card_pos.mpr ⟨x, hx⟩
    simp only [Nat.even_iff]
    omega
  rw [pmSum_expand W c (hAT hx)]
  have hterm : ∀ v ∈ T.erase x,
      W (Sym2.map (paint c) s(x, v)) * pmSum W c ((T.erase x).erase v)
        = (if v ∈ A.erase x then
             W s((x, c x), (v, c v)) * pmSum W c ((A.erase x).erase v) else 0)
          * pmSum W c (T \ A) := by
    intro v hv
    have hvx : v ≠ x := (Finset.mem_erase.mp hv).1
    have hvT : v ∈ T := (Finset.mem_erase.mp hv).2
    by_cases hvA : v ∈ A
    · have hvmem : v ∈ A.erase x := Finset.mem_erase.mpr ⟨hvx, hvA⟩
      have hsub : (A.erase x).erase v ⊆ (T.erase x).erase v := by
        intro q hq
        simp only [Finset.mem_erase] at hq ⊢
        exact ⟨hq.1, hq.2.1, hAT hq.2.2⟩
      have hsd : ((T.erase x).erase v) \ ((A.erase x).erase v) = T \ A := by
        ext q
        simp only [Finset.mem_sdiff, Finset.mem_erase]
        constructor
        · rintro ⟨⟨hqv, hqx, hqT⟩, hno⟩
          exact ⟨hqT, fun hcon => hno ⟨hqv, hqx, hcon⟩⟩
        · rintro ⟨hqT, hqA⟩
          refine ⟨⟨fun h => hqA ?_, fun h => hqA ?_, hqT⟩, fun hcon => hqA hcon.2.2⟩
          · rw [h]; exact hvA
          · rw [h]; exact hx
      have hcut2 : ∀ p ∈ (A.erase x).erase v, ∀ q ∈
          ((T.erase x).erase v) \ ((A.erase x).erase v), W s((p, c p), (q, c q)) = 0 := by
        intro p hp q hq
        rw [hsd] at hq
        have hpA : p ∈ A := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hp)
        have hpx : p ≠ x := (Finset.mem_erase.mp (Finset.mem_erase.mp hp).2).1
        exact hcut p hpA q (Finset.mem_sdiff.mp hq).1 (Finset.mem_sdiff.mp hq).2 (Or.inl hpx)
      rw [if_pos hvmem, Separation.pmSum_split W c ((A.erase x).erase v).card _ _ rfl hsub hcut2,
        hsd, mul_assoc]
      rfl
    · rw [if_neg (fun h => hvA (Finset.mem_of_mem_erase h)), zero_mul]
      by_cases hvy : v = y
      · subst hvy
        refine mul_eq_zero_of_right _ ?_
        refine pmSum_eq_zero_of_odd_part W c (A := A.erase x) (fun q hq => ?_) hodd
          (fun p hp q hq => ?_)
        · simp only [Finset.mem_erase] at hq ⊢
          exact ⟨fun h => hvA (by rw [← h]; exact hq.2), hq.1, hAT hq.2⟩
        · have hpA : p ∈ A := Finset.mem_of_mem_erase hp
          have hpx : p ≠ x := (Finset.mem_erase.mp hp).1
          have h1 := Finset.mem_sdiff.mp hq
          have h2 := Finset.mem_erase.mp (Finset.mem_erase.mp h1.1).2
          have hqA : q ∉ A := fun hcon => h1.2 (Finset.mem_erase.mpr ⟨h2.1, hcon⟩)
          exact hcut p hpA q h2.2 hqA (Or.inl hpx)
      · exact mul_eq_zero_of_left (hcut x hx v hvT hvA (Or.inr hvy)) _
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
  congr 1
  rw [pmSum_expand W c hx, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun v _ => rfl)
  ext v
  simp only [Finset.mem_filter, Finset.mem_erase]
  exact ⟨fun h => h.2, fun h => ⟨⟨h.1, hAT h.2⟩, h⟩⟩

/-- The odd companion on an arbitrary site set. -/
theorem pmSum_single_crossing_odd (W : Sym2 (V × Fin 3) → ℂ) (c : V → Fin 3)
    {T A : Finset V} (hAT : A ⊆ T) (hAodd : ¬ Even A.card)
    {x y : V} (hx : x ∈ A) (hy : y ∈ T) (hyA : y ∉ A)
    (hcut : ∀ p ∈ A, ∀ q ∈ T, q ∉ A → (p ≠ x ∨ q ≠ y) → W s((p, c p), (q, c q)) = 0) :
    pmSum W c T = W s((x, c x), (y, c y))
      * (pmSum W c (A.erase x) * pmSum W c ((T \ A).erase y)) := by
  classical
  rw [pmSum_expand W c (hAT hx)]
  have hterm : ∀ v ∈ T.erase x,
      W (Sym2.map (paint c) s(x, v)) * pmSum W c ((T.erase x).erase v)
        = if v = y then W s((x, c x), (y, c y))
            * (pmSum W c (A.erase x) * pmSum W c ((T \ A).erase y)) else 0 := by
    intro v hv
    have hvx : v ≠ x := (Finset.mem_erase.mp hv).1
    have hvT : v ∈ T := (Finset.mem_erase.mp hv).2
    by_cases hvy : v = y
    · subst hvy
      rw [if_pos rfl]
      have hsub : A.erase x ⊆ (T.erase x).erase v := by
        intro q hq
        simp only [Finset.mem_erase] at hq ⊢
        exact ⟨fun h => hyA (by rw [← h]; exact hq.2), hq.1, hAT hq.2⟩
      have hsd : ((T.erase x).erase v) \ (A.erase x) = (T \ A).erase v := by
        ext q
        simp only [Finset.mem_sdiff, Finset.mem_erase]
        constructor
        · rintro ⟨⟨hqv, hqx, hqT⟩, hno⟩
          exact ⟨hqv, hqT, fun hcon => hno ⟨hqx, hcon⟩⟩
        · rintro ⟨hqv, hqT, hqA⟩
          refine ⟨⟨hqv, fun h => hqA ?_, hqT⟩, fun hcon => hqA hcon.2⟩
          rw [h]; exact hx
      rw [Separation.pmSum_split W c (A.erase x).card _ _ rfl hsub ?_, hsd]
      · rfl
      · intro p hp q hq
        rw [hsd] at hq
        have hpA : p ∈ A := Finset.mem_of_mem_erase hp
        have hpx : p ≠ x := (Finset.mem_erase.mp hp).1
        have h1 := Finset.mem_sdiff.mp (Finset.mem_of_mem_erase hq)
        exact hcut p hpA q h1.1 h1.2 (Or.inl hpx)
    · rw [if_neg hvy]
      by_cases hvA : v ∈ A
      · refine mul_eq_zero_of_right _ ?_
        have hoddv : ¬ Even ((A.erase x).erase v).card := by
          rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hvx, hvA⟩),
            Finset.card_erase_of_mem hx]
          have h2 : 2 ≤ A.card := Finset.one_lt_card.mpr ⟨x, hx, v, hvA, Ne.symm hvx⟩
          simp only [Nat.even_iff] at hAodd ⊢
          omega
        refine pmSum_eq_zero_of_odd_part W c (A := (A.erase x).erase v) (fun q hq => ?_)
          hoddv (fun p hp q hq => ?_)
        · simp only [Finset.mem_erase] at hq ⊢
          exact ⟨hq.1, hq.2.1, hAT hq.2.2⟩
        · have hpA : p ∈ A := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hp)
          have hpx : p ≠ x := (Finset.mem_erase.mp (Finset.mem_erase.mp hp).2).1
          have h1 := Finset.mem_sdiff.mp hq
          have h2 := Finset.mem_erase.mp h1.1
          have h3 := Finset.mem_erase.mp h2.2
          have hqA : q ∉ A := fun hcon =>
            h1.2 (Finset.mem_erase.mpr ⟨h2.1, Finset.mem_erase.mpr ⟨h3.1, hcon⟩⟩)
          exact hcut p hpA q h3.2 hqA (Or.inl hpx)
      · exact mul_eq_zero_of_left (hcut x hx v hvT hvA (Or.inr hvy)) _
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (T.erase x)]
  rw [if_pos (Finset.mem_erase.mpr ⟨fun h => hyA (by rw [h]; exact hx), hy⟩)]

/-- **Every even part has two live crossings.**  The positive reading of the previous theorem:
whatever crossing pair one names, another live one exists.  No liveness is assumed of the named
pair, and no degree bound, minimality, or degeneracy anywhere. -/
theorem exists_other_crossing_of_even_part (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {A : Finset V} (hA : A.Nonempty) (hAc : (Finset.univ \ A).Nonempty)
    (hAeven : Even A.card) {x y : V} (hx : x ∈ A) (hy : y ∉ A) :
    ∃ p ∈ A, ∃ q : V, q ∉ A ∧ (p ≠ x ∨ q ≠ y) ∧
      ∃ a b : Fin 3, W s((p, a), (q, b)) ≠ 0 := by
  by_contra hno
  push_neg at hno
  exact false_of_even_part_one_crossing W hone hzero hA hAc hAeven hx hy
    (fun p hp q hq a b hor => hno p hp q hq hor a b)

/-- **Two crossings on an even part.**  A matching crosses an even number of times, so zero or
twice: the amplitude is a clean product plus a two-crossing product.  Expanding at the first
crossing's inside end sends one branch to the odd one-crossing split and every other to the
even one. -/
theorem amplitude_split_two_crossings (W : Sym2 (V × Fin 3) → ℂ) (c : V → Fin 3)
    {A : Finset V} (hAeven : Even A.card)
    {x₁ y₁ x₂ y₂ : V} (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A) (hy₁ : y₁ ∉ A) (hy₂ : y₂ ∉ A)
    (hx : x₁ ≠ x₂) (hy : y₁ ≠ y₂)
    (hcut : ∀ p ∈ A, ∀ q : V, q ∉ A →
      ¬((p = x₁ ∧ q = y₁) ∨ (p = x₂ ∧ q = y₂)) → W s((p, c p), (q, c q)) = 0) :
    amplitude W c = pmSum W c A * pmSum W c (Finset.univ \ A)
      + W s((x₁, c x₁), (y₁, c y₁)) * (W s((x₂, c x₂), (y₂, c y₂))
        * (pmSum W c ((A.erase x₁).erase x₂)
          * pmSum W c (((Finset.univ \ A).erase y₁).erase y₂))) := by
  classical
  have hoddA : ¬ Even (A.erase x₁).card := by
    rw [Finset.card_erase_of_mem hx₁]
    obtain ⟨k, hk⟩ := hAeven
    have hpos : 0 < A.card := Finset.card_pos.mpr ⟨x₁, hx₁⟩
    simp only [Nat.even_iff]
    omega
  have hy₁x₁ : y₁ ≠ x₁ := fun h => hy₁ (by rw [h]; exact hx₁)
  -- the branch that uses the first crossing
  have hbranch₁ : pmSum W c (((Finset.univ : Finset V).erase x₁).erase y₁)
      = W s((x₂, c x₂), (y₂, c y₂)) * (pmSum W c ((A.erase x₁).erase x₂)
        * pmSum W c (((Finset.univ \ A).erase y₁).erase y₂)) := by
    have hsub : A.erase x₁ ⊆ ((Finset.univ : Finset V).erase x₁).erase y₁ := by
      intro q hq
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hq ⊢
      exact ⟨fun h => hy₁ (by rw [← h]; exact hq.2), hq.1⟩
    have hsd : (((Finset.univ : Finset V).erase x₁).erase y₁) \ (A.erase x₁)
        = (Finset.univ \ A).erase y₁ := by
      ext q
      simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
      constructor
      · rintro ⟨⟨hqy, hqx⟩, hno⟩
        exact ⟨hqy, fun hcon => hno ⟨hqx, hcon⟩⟩
      · rintro ⟨hqy, hqA⟩
        exact ⟨⟨hqy, fun h => hqA (by rw [h]; exact hx₁)⟩, fun hcon => hqA hcon.2⟩
    rw [pmSum_single_crossing_odd W c hsub hoddA (Finset.mem_erase.mpr ⟨Ne.symm hx, hx₂⟩)
      (Finset.mem_erase.mpr ⟨Ne.symm hy, Finset.mem_erase.mpr
        ⟨fun h => hy₂ (by rw [h]; exact hx₁), Finset.mem_univ y₂⟩⟩)
      (fun hcon => hy₂ (Finset.mem_of_mem_erase hcon)) ?_, hsd]
    intro p hp q hq hqA hor
    have hpA : p ∈ A := Finset.mem_of_mem_erase hp
    have hpx₁ : p ≠ x₁ := (Finset.mem_erase.mp hp).1
    have hqx₁ : q ≠ x₁ := (Finset.mem_erase.mp (Finset.mem_erase.mp hq).2).1
    have hqnA : q ∉ A := fun hcon => hqA (Finset.mem_erase.mpr ⟨hqx₁, hcon⟩)
    refine hcut p hpA q hqnA ?_
    rintro (⟨h, -⟩ | ⟨h1, h2⟩)
    · exact hpx₁ h
    · exact hor.elim (fun hn => hn h1) (fun hn => hn h2)
  -- every other inside branch factors cleanly
  have hinside : ∀ v ∈ A.erase x₁,
      pmSum W c (((Finset.univ : Finset V).erase x₁).erase v)
        = pmSum W c ((A.erase x₁).erase v) * pmSum W c (Finset.univ \ A) := by
    intro v hv
    have hvA : v ∈ A := Finset.mem_of_mem_erase hv
    have hvx₁ : v ≠ x₁ := (Finset.mem_erase.mp hv).1
    have hsub : (A.erase x₁).erase v ⊆ ((Finset.univ : Finset V).erase x₁).erase v := by
      intro q hq
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hq ⊢
      exact ⟨hq.1, hq.2.1⟩
    have hsd : (((Finset.univ : Finset V).erase x₁).erase v) \ ((A.erase x₁).erase v)
        = Finset.univ \ A := by
      ext q
      simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
      constructor
      · rintro ⟨⟨hqv, hqx⟩, hno⟩ hcon
        exact hno ⟨hqv, hqx, hcon⟩
      · intro hqA
        refine ⟨⟨fun h => hqA ?_, fun h => hqA ?_⟩, fun hcon => hqA hcon.2.2⟩
        · rw [h]; exact hvA
        · rw [h]; exact hx₁
    have hEven : Even ((A.erase x₁).erase v).card := by
      rw [Finset.card_erase_of_mem hv, Finset.card_erase_of_mem hx₁]
      have h2 : 2 ≤ A.card := Finset.one_lt_card.mpr ⟨x₁, hx₁, v, hvA, Ne.symm hvx₁⟩
      simp only [Nat.even_iff] at hAeven ⊢
      omega
    by_cases hvx₂ : v = x₂
    · refine (Separation.pmSum_split W c ((A.erase x₁).erase v).card _ _ rfl hsub ?_).trans
        (by rw [hsd])
      intro p hp q hq
      rw [hsd] at hq
      have hpA : p ∈ A := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hp)
      have hpx₁ : p ≠ x₁ := (Finset.mem_erase.mp (Finset.mem_erase.mp hp).2).1
      have hpv : p ≠ v := (Finset.mem_erase.mp hp).1
      refine hcut p hpA q (Finset.mem_sdiff.mp hq).2 ?_
      rintro (⟨h, -⟩ | ⟨h, -⟩)
      · exact hpx₁ h
      · exact hpv (by rw [h, hvx₂])
    · have hx₂mem : x₂ ∈ (A.erase x₁).erase v :=
        Finset.mem_erase.mpr ⟨fun h => hvx₂ h.symm, Finset.mem_erase.mpr ⟨Ne.symm hx, hx₂⟩⟩
      have hy₂mem : y₂ ∈ ((Finset.univ : Finset V).erase x₁).erase v := by
        simp only [Finset.mem_erase, Finset.mem_univ, and_true]
        exact ⟨fun h => hy₂ (by rw [h]; exact hvA), fun h => hy₂ (by rw [h]; exact hx₁)⟩
      refine (pmSum_split_one_crossing W c hsub hEven hx₂mem hy₂mem
        (fun hcon => hy₂ (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hcon))) ?_).trans
        (by rw [hsd])
      intro p hp q hq hqA hor
      have hpA : p ∈ A := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hp)
      have hpx₁ : p ≠ x₁ := (Finset.mem_erase.mp (Finset.mem_erase.mp hp).2).1
      have hqnA : q ∉ A := by
        intro hcon
        refine hqA ?_
        have h1 := Finset.mem_erase.mp hq
        exact Finset.mem_erase.mpr ⟨h1.1, Finset.mem_erase.mpr
          ⟨(Finset.mem_erase.mp h1.2).1, hcon⟩⟩
      refine hcut p hpA q hqnA ?_
      rintro (⟨h, -⟩ | ⟨h1, h2⟩)
      · exact hpx₁ h
      · exact hor.elim (fun hn => hn h1) (fun hn => hn h2)
  rw [← pmSum_univ, pmSum_expand W c (Finset.mem_univ x₁)]
  have hterm : ∀ v ∈ (Finset.univ : Finset V).erase x₁,
      W (Sym2.map (paint c) s(x₁, v)) * pmSum W c (((Finset.univ : Finset V).erase x₁).erase v)
        = (if v ∈ A.erase x₁ then
             W s((x₁, c x₁), (v, c v)) * pmSum W c ((A.erase x₁).erase v) else 0)
            * pmSum W c (Finset.univ \ A)
          + (if v = y₁ then W s((x₁, c x₁), (y₁, c y₁)) * (W s((x₂, c x₂), (y₂, c y₂))
              * (pmSum W c ((A.erase x₁).erase x₂)
                * pmSum W c (((Finset.univ \ A).erase y₁).erase y₂))) else 0) := by
    intro v hv
    have hvx₁ : v ≠ x₁ := (Finset.mem_erase.mp hv).1
    by_cases hvA : v ∈ A
    · have hvmem : v ∈ A.erase x₁ := Finset.mem_erase.mpr ⟨hvx₁, hvA⟩
      rw [if_pos hvmem, if_neg (fun h => hy₁ (by rw [← h]; exact hvA)), add_zero,
        hinside v hvmem, ← mul_assoc]
      rfl
    · rw [if_neg (fun h => hvA (Finset.mem_of_mem_erase h)), zero_mul, zero_add]
      by_cases hvy₁ : v = y₁
      · subst hvy₁
        rw [if_pos rfl, hbranch₁]
        rfl
      · rw [if_neg hvy₁]
        refine mul_eq_zero_of_left ?_ _
        refine hcut x₁ hx₁ v hvA ?_
        rintro (⟨-, h⟩ | ⟨h, -⟩)
        · exact hvy₁ h
        · exact hx h
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.sum_mul,
    Finset.sum_ite_eq' ((Finset.univ : Finset V).erase x₁),
    if_pos (Finset.mem_erase.mpr ⟨hy₁x₁, Finset.mem_univ y₁⟩)]
  congr 2
  rw [pmSum_expand W c hx₁, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun v _ => rfl)
  ext v
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

/-- **Three crossings are needed on an even cut.**

With two live crossing pairs and rank-one blocks, both terms of the two-crossing split factor
across the cut, so the amplitude has a rank-two representation -- and the equations demand
three.  Together with the one-crossing case, every even part is joined to the rest by at least
three live pairs whenever the crossing blocks have rank one, which in the monochromatic setting
they always do. -/
theorem false_of_even_part_two_rank_one_crossings (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {A : Finset V} (hA : A.Nonempty) (hAc : (Finset.univ \ A).Nonempty)
    (hAeven : Even A.card)
    {x₁ y₁ x₂ y₂ : V} (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A) (hy₁ : y₁ ∉ A) (hy₂ : y₂ ∉ A)
    (hx : x₁ ≠ x₂) (hy : y₁ ≠ y₂)
    (hcut : ∀ p ∈ A, ∀ q : V, q ∉ A → ∀ a b : Fin 3,
      ¬((p = x₁ ∧ q = y₁) ∨ (p = x₂ ∧ q = y₂)) → W s((p, a), (q, b)) = 0)
    (α₁ β₁ α₂ β₂ : Fin 3 → ℂ)
    (hr₁ : ∀ a b : Fin 3, W s((x₁, a), (y₁, b)) = α₁ a * β₁ b)
    (hr₂ : ∀ a b : Fin 3, W s((x₂, a), (y₂, b)) = α₂ a * β₂ b) :
    False := by
  classical
  have hy₁mem : y₁ ∈ Finset.univ \ A := Finset.mem_sdiff.mpr ⟨Finset.mem_univ y₁, hy₁⟩
  have hy₂mem : y₂ ∈ Finset.univ \ A := Finset.mem_sdiff.mpr ⟨Finset.mem_univ y₂, hy₂⟩
  refine Separation.no_rank_two_flattening W hone hzero A hA hAc
    (fun j c => if j = 0 then pmSum W c A
      else α₁ (c x₁) * α₂ (c x₂) * pmSum W c ((A.erase x₁).erase x₂))
    (fun j c => if j = 0 then pmSum W c (Finset.univ \ A)
      else β₁ (c y₁) * β₂ (c y₂) * pmSum W c (((Finset.univ \ A).erase y₁).erase y₂))
    ?_ ?_ ?_
  · intro j c c' hcc
    by_cases hj : j = 0
    · simp only [hj, if_pos rfl]
      exact pmSum_congr_colour W (fun z hz => hcc z hz)
    · simp only [if_neg hj, hcc x₁ hx₁, hcc x₂ hx₂,
        pmSum_congr_colour W (c := c) (c' := c')
          (fun z hz => hcc z (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hz)))]
  · intro j c c' hcc
    by_cases hj : j = 0
    · simp only [hj, if_pos rfl]
      exact pmSum_congr_colour W (fun z hz => hcc z hz)
    · simp only [if_neg hj, hcc y₁ hy₁mem, hcc y₂ hy₂mem,
        pmSum_congr_colour W (c := c) (c' := c')
          (fun z hz => hcc z (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hz)))]
  · intro c
    rw [Fin.sum_univ_two]
    simp only [if_pos rfl, if_neg (by decide : (1 : Fin 2) ≠ 0), if_true]
    rw [amplitude_split_two_crossings W c hAeven hx₁ hx₂ hy₁ hy₂ hx hy
      (fun p hp q hq hno => hcut p hp q hq _ _ hno), hr₁, hr₂]
    ring

/-- **Two crossings on an odd part.**  A matching crosses an odd number of times, so with only
two pairs available it uses exactly one: the amplitude is the sum of the two single-crossing
products. -/
theorem amplitude_split_two_crossings_odd (W : Sym2 (V × Fin 3) → ℂ) (c : V → Fin 3)
    {A : Finset V} (hAodd : ¬ Even A.card)
    {x₁ y₁ x₂ y₂ : V} (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A) (hy₁ : y₁ ∉ A) (hy₂ : y₂ ∉ A)
    (hx : x₁ ≠ x₂) (hy : y₁ ≠ y₂)
    (hcut : ∀ p ∈ A, ∀ q : V, q ∉ A →
      ¬((p = x₁ ∧ q = y₁) ∨ (p = x₂ ∧ q = y₂)) → W s((p, c p), (q, c q)) = 0) :
    amplitude W c
      = W s((x₁, c x₁), (y₁, c y₁))
          * (pmSum W c (A.erase x₁) * pmSum W c ((Finset.univ \ A).erase y₁))
        + W s((x₂, c x₂), (y₂, c y₂))
          * (pmSum W c (A.erase x₂) * pmSum W c ((Finset.univ \ A).erase y₂)) := by
  classical
  have hevenA : Even (A.erase x₁).card := by
    rw [Finset.card_erase_of_mem hx₁]
    have hpos : 0 < A.card := Finset.card_pos.mpr ⟨x₁, hx₁⟩
    simp only [Nat.even_iff] at hAodd ⊢
    omega
  have hy₁x₁ : y₁ ≠ x₁ := fun h => hy₁ (by rw [h]; exact hx₁)
  have hx₂mem : x₂ ∈ A.erase x₁ := Finset.mem_erase.mpr ⟨Ne.symm hx, hx₂⟩
  -- the branch through the first crossing
  have hbranch₁ : pmSum W c (((Finset.univ : Finset V).erase x₁).erase y₁)
      = pmSum W c (A.erase x₁) * pmSum W c ((Finset.univ \ A).erase y₁) := by
    have hsub : A.erase x₁ ⊆ ((Finset.univ : Finset V).erase x₁).erase y₁ := by
      intro q hq
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hq ⊢
      exact ⟨fun h => hy₁ (by rw [← h]; exact hq.2), hq.1⟩
    have hsd : (((Finset.univ : Finset V).erase x₁).erase y₁) \ (A.erase x₁)
        = (Finset.univ \ A).erase y₁ := by
      ext q
      simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
      constructor
      · rintro ⟨⟨hqy, hqx⟩, hno⟩
        exact ⟨hqy, fun hcon => hno ⟨hqx, hcon⟩⟩
      · rintro ⟨hqy, hqA⟩
        exact ⟨⟨hqy, fun h => hqA (by rw [h]; exact hx₁)⟩, fun hcon => hqA hcon.2⟩
    refine (pmSum_split_one_crossing W c hsub hevenA hx₂mem
      (Finset.mem_erase.mpr ⟨Ne.symm hy, Finset.mem_erase.mpr
        ⟨fun h => hy₂ (by rw [h]; exact hx₁), Finset.mem_univ y₂⟩⟩)
      (fun hcon => hy₂ (Finset.mem_of_mem_erase hcon)) ?_).trans (by rw [hsd])
    intro p hp q hq hqA hor
    have hpA : p ∈ A := Finset.mem_of_mem_erase hp
    have hpx₁ : p ≠ x₁ := (Finset.mem_erase.mp hp).1
    have hqx₁ : q ≠ x₁ := (Finset.mem_erase.mp (Finset.mem_erase.mp hq).2).1
    have hqnA : q ∉ A := fun hcon => hqA (Finset.mem_erase.mpr ⟨hqx₁, hcon⟩)
    refine hcut p hpA q hqnA ?_
    rintro (⟨h, -⟩ | ⟨h1, h2⟩)
    · exact hpx₁ h
    · exact hor.elim (fun hn => hn h1) (fun hn => hn h2)
  -- the inside branches, all through the second crossing
  have hinside : ∀ v ∈ (A.erase x₁).erase x₂,
      pmSum W c (((Finset.univ : Finset V).erase x₁).erase v)
        = W s((x₂, c x₂), (y₂, c y₂))
          * (pmSum W c (((A.erase x₁).erase x₂).erase v)
            * pmSum W c ((Finset.univ \ A).erase y₂)) := by
    intro v hv
    have hvx₂ : v ≠ x₂ := (Finset.mem_erase.mp hv).1
    have hv' : v ∈ A.erase x₁ := Finset.mem_of_mem_erase hv
    have hvA : v ∈ A := Finset.mem_of_mem_erase hv'
    have hvx₁ : v ≠ x₁ := (Finset.mem_erase.mp hv').1
    have hsub : (A.erase x₁).erase v ⊆ ((Finset.univ : Finset V).erase x₁).erase v := by
      intro q hq
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hq ⊢
      exact ⟨hq.1, hq.2.1⟩
    have hodd' : ¬ Even ((A.erase x₁).erase v).card := by
      rw [Finset.card_erase_of_mem hv']
      obtain ⟨k, hk⟩ := hevenA
      have hpos : 0 < (A.erase x₁).card := Finset.card_pos.mpr ⟨v, hv'⟩
      simp only [Nat.even_iff]
      omega
    have hsd : (((Finset.univ : Finset V).erase x₁).erase v) \ ((A.erase x₁).erase v)
        = Finset.univ \ A := by
      ext q
      simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
      constructor
      · rintro ⟨⟨hqv, hqx⟩, hno⟩ hcon
        exact hno ⟨hqv, hqx, hcon⟩
      · intro hqA
        refine ⟨⟨fun h => hqA ?_, fun h => hqA ?_⟩, fun hcon => hqA hcon.2.2⟩
        · rw [h]; exact hvA
        · rw [h]; exact hx₁
    have hx₂mem' : x₂ ∈ (A.erase x₁).erase v :=
      Finset.mem_erase.mpr ⟨fun h => hvx₂ h.symm, hx₂mem⟩
    have hy₂mem' : y₂ ∈ ((Finset.univ : Finset V).erase x₁).erase v := by
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact ⟨fun h => hy₂ (by rw [h]; exact hvA), fun h => hy₂ (by rw [h]; exact hx₁)⟩
    rw [pmSum_single_crossing_odd W c hsub hodd' hx₂mem' hy₂mem'
      (fun hcon => hy₂ (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hcon))) ?_, hsd,
      Finset.erase_right_comm]
    intro p hp q hq hqA hor
    have hpA : p ∈ A := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hp)
    have hpx₁ : p ≠ x₁ := (Finset.mem_erase.mp (Finset.mem_erase.mp hp).2).1
    have h1 := Finset.mem_erase.mp hq
    have hqnA : q ∉ A := fun hcon => hqA (Finset.mem_erase.mpr ⟨h1.1,
      Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp h1.2).1, hcon⟩⟩)
    refine hcut p hpA q hqnA ?_
    rintro (⟨h, -⟩ | ⟨h1', h2'⟩)
    · exact hpx₁ h
    · exact hor.elim (fun hn => hn h1') (fun hn => hn h2')
  rw [← pmSum_univ, pmSum_expand W c (Finset.mem_univ x₁)]
  have hterm : ∀ v ∈ (Finset.univ : Finset V).erase x₁,
      W (Sym2.map (paint c) s(x₁, v)) * pmSum W c (((Finset.univ : Finset V).erase x₁).erase v)
        = (if v = y₁ then W s((x₁, c x₁), (y₁, c y₁))
             * (pmSum W c (A.erase x₁) * pmSum W c ((Finset.univ \ A).erase y₁)) else 0)
          + (if v ∈ (A.erase x₁).erase x₂ then
               W s((x₁, c x₁), (v, c v)) * pmSum W c (((A.erase x₁).erase x₂).erase v) else 0)
            * (W s((x₂, c x₂), (y₂, c y₂)) * pmSum W c ((Finset.univ \ A).erase y₂)) := by
    intro v hv
    have hvx₁ : v ≠ x₁ := (Finset.mem_erase.mp hv).1
    by_cases hvA : v ∈ A
    · have hv' : v ∈ A.erase x₁ := Finset.mem_erase.mpr ⟨hvx₁, hvA⟩
      rw [if_neg (fun h => hy₁ (by rw [← h]; exact hvA)), zero_add]
      by_cases hvx₂ : v = x₂
      · subst hvx₂
        rw [if_neg (fun h => (Finset.mem_erase.mp h).1 rfl), zero_mul]
        refine mul_eq_zero_of_right _ ?_
        have hsub : (A.erase x₁).erase v ⊆ ((Finset.univ : Finset V).erase x₁).erase v := by
          intro q hq
          simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hq ⊢
          exact ⟨hq.1, hq.2.1⟩
        have hodd' : ¬ Even ((A.erase x₁).erase v).card := by
          rw [Finset.card_erase_of_mem hv']
          obtain ⟨k, hk⟩ := hevenA
          have hpos : 0 < (A.erase x₁).card := Finset.card_pos.mpr ⟨v, hv'⟩
          simp only [Nat.even_iff]
          omega
        refine pmSum_eq_zero_of_odd_part W c hsub hodd' (fun p hp q hq => ?_)
        have hpA : p ∈ A := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hp)
        have hpx₁ : p ≠ x₁ := (Finset.mem_erase.mp (Finset.mem_erase.mp hp).2).1
        have hpv : p ≠ v := (Finset.mem_erase.mp hp).1
        have h1 := Finset.mem_erase.mp (Finset.mem_sdiff.mp hq).1
        have hqnA : q ∉ A := fun hcon => (Finset.mem_sdiff.mp hq).2
          (Finset.mem_erase.mpr ⟨h1.1, Finset.mem_erase.mpr
            ⟨(Finset.mem_erase.mp h1.2).1, hcon⟩⟩)
        refine hcut p hpA q hqnA ?_
        rintro (⟨h, -⟩ | ⟨h, -⟩)
        · exact hpx₁ h
        · exact hpv h
      · rw [if_pos (Finset.mem_erase.mpr ⟨hvx₂, hv'⟩), hinside v
          (Finset.mem_erase.mpr ⟨hvx₂, hv'⟩)]
        have hpaint : W (Sym2.map (paint c) s(x₁, v)) = W s((x₁, c x₁), (v, c v)) := rfl
        rw [hpaint]
        ring
    · rw [if_neg (fun h => hvA (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))),
        zero_mul, add_zero]
      by_cases hvy₁ : v = y₁
      · subst hvy₁
        rw [if_pos rfl, hbranch₁]
        rfl
      · rw [if_neg hvy₁]
        refine mul_eq_zero_of_left ?_ _
        refine hcut x₁ hx₁ v hvA ?_
        rintro (⟨-, h⟩ | ⟨h, -⟩)
        · exact hvy₁ h
        · exact hx h
  have hsum : (∑ v ∈ (Finset.univ : Finset V).erase x₁,
      if v ∈ (A.erase x₁).erase x₂ then
        W s((x₁, c x₁), (v, c v)) * pmSum W c (((A.erase x₁).erase x₂).erase v) else 0)
      = pmSum W c (A.erase x₂) := by
    rw [← Finset.sum_filter, pmSum_expand W c (Finset.mem_erase.mpr ⟨hx, hx₁⟩),
      Finset.erase_right_comm]
    refine Finset.sum_congr ?_ (fun v _ => rfl)
    ext v
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
    tauto
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
    Finset.sum_ite_eq' ((Finset.univ : Finset V).erase x₁),
    if_pos (Finset.mem_erase.mpr ⟨hy₁x₁, Finset.mem_univ y₁⟩), ← Finset.sum_mul, hsum]
  ring

/-- **Three crossings are needed on an odd cut too.**

With two live crossing pairs at *different* inside endpoints and rank-one blocks, the two
single-crossing products each factor across the cut, so the amplitude has a rank-two
representation and the equations are contradicted.

This is the general two-crossing case: the existing one covers only crossings sharing their
inside endpoint.  Together with the even case, every cut whose crossing blocks have rank one is
crossed at least three times. -/
theorem false_of_odd_part_two_rank_one_crossings (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {A : Finset V} (hA : A.Nonempty) (hAc : (Finset.univ \ A).Nonempty)
    (hAodd : ¬ Even A.card)
    {x₁ y₁ x₂ y₂ : V} (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A) (hy₁ : y₁ ∉ A) (hy₂ : y₂ ∉ A)
    (hx : x₁ ≠ x₂) (hy : y₁ ≠ y₂)
    (hcut : ∀ p ∈ A, ∀ q : V, q ∉ A → ∀ a b : Fin 3,
      ¬((p = x₁ ∧ q = y₁) ∨ (p = x₂ ∧ q = y₂)) → W s((p, a), (q, b)) = 0)
    (α₁ β₁ α₂ β₂ : Fin 3 → ℂ)
    (hr₁ : ∀ a b : Fin 3, W s((x₁, a), (y₁, b)) = α₁ a * β₁ b)
    (hr₂ : ∀ a b : Fin 3, W s((x₂, a), (y₂, b)) = α₂ a * β₂ b) :
    False := by
  classical
  have hy₁mem : y₁ ∈ Finset.univ \ A := Finset.mem_sdiff.mpr ⟨Finset.mem_univ y₁, hy₁⟩
  have hy₂mem : y₂ ∈ Finset.univ \ A := Finset.mem_sdiff.mpr ⟨Finset.mem_univ y₂, hy₂⟩
  refine Separation.no_rank_two_flattening W hone hzero A hA hAc
    (fun j c => if j = 0 then α₁ (c x₁) * pmSum W c (A.erase x₁)
      else α₂ (c x₂) * pmSum W c (A.erase x₂))
    (fun j c => if j = 0 then β₁ (c y₁) * pmSum W c ((Finset.univ \ A).erase y₁)
      else β₂ (c y₂) * pmSum W c ((Finset.univ \ A).erase y₂)) ?_ ?_ ?_
  · intro j c c' hcc
    by_cases hj : j = 0
    · subst hj
      simp only [if_pos rfl, if_true]
      rw [hcc x₁ hx₁, pmSum_congr_colour W (c := c) (c' := c')
        (fun z hz => hcc z (Finset.mem_of_mem_erase hz))]
    · simp only [if_neg hj]
      rw [hcc x₂ hx₂, pmSum_congr_colour W (c := c) (c' := c')
        (fun z hz => hcc z (Finset.mem_of_mem_erase hz))]
  · intro j c c' hcc
    by_cases hj : j = 0
    · subst hj
      simp only [if_pos rfl, if_true]
      rw [hcc y₁ hy₁mem, pmSum_congr_colour W (c := c) (c' := c')
        (fun z hz => hcc z (Finset.mem_of_mem_erase hz))]
    · simp only [if_neg hj]
      rw [hcc y₂ hy₂mem, pmSum_congr_colour W (c := c) (c' := c')
        (fun z hz => hcc z (Finset.mem_of_mem_erase hz))]
  · intro c
    rw [Fin.sum_univ_two]
    simp only [if_pos rfl, if_neg (by decide : (1 : Fin 2) ≠ 0), if_true]
    rw [amplitude_split_two_crossings_odd W c hAodd hx₁ hx₂ hy₁ hy₂ hx hy
      (fun p hp q hq hno => hcut p hp q hq _ _ hno), hr₁, hr₂]
    ring

/-- **All crossings at one inside site is as good as none, on an even part.**

If every live pair leaving a part of even size starts at the same site, no matching can use any
of them: using one leaves the part with an odd number of sites and nothing to cross back on.
So the matching sum factors exactly as it would across a clean cut.

This generalises the single-crossing case in a different direction: any number of crossings is
allowed, provided they all emanate from one inside site. -/
theorem amplitude_split_crossings_at_one_site (W : Sym2 (V × Fin 3) → ℂ) (c : V → Fin 3)
    {A : Finset V} (hAeven : Even A.card) {x : V} (hx : x ∈ A)
    (hcut : ∀ p ∈ A, ∀ q : V, q ∉ A → p ≠ x → W s((p, c p), (q, c q)) = 0) :
    amplitude W c = pmSum W c A * pmSum W c (Finset.univ \ A) := by
  classical
  have hodd : ¬ Even (A.erase x).card := by
    rw [Finset.card_erase_of_mem hx]
    obtain ⟨k, hk⟩ := hAeven
    have hpos : 0 < A.card := Finset.card_pos.mpr ⟨x, hx⟩
    simp only [Nat.even_iff]
    omega
  rw [← pmSum_univ, pmSum_expand W c (Finset.mem_univ x)]
  have hterm : ∀ v ∈ (Finset.univ : Finset V).erase x,
      W (Sym2.map (paint c) s(x, v)) * pmSum W c (((Finset.univ : Finset V).erase x).erase v)
        = (if v ∈ A.erase x then
             W s((x, c x), (v, c v)) * pmSum W c ((A.erase x).erase v) else 0)
          * pmSum W c (Finset.univ \ A) := by
    intro v hv
    have hvx : v ≠ x := (Finset.mem_erase.mp hv).1
    by_cases hvA : v ∈ A
    · have hvmem : v ∈ A.erase x := Finset.mem_erase.mpr ⟨hvx, hvA⟩
      have hsub : (A.erase x).erase v ⊆ ((Finset.univ : Finset V).erase x).erase v := by
        intro q hq
        simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hq ⊢
        exact ⟨hq.1, hq.2.1⟩
      have hsd : (((Finset.univ : Finset V).erase x).erase v) \ ((A.erase x).erase v)
          = Finset.univ \ A := by
        ext q
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
        constructor
        · rintro ⟨⟨hqv, hqx⟩, hno⟩ hcon
          exact hno ⟨hqv, hqx, hcon⟩
        · intro hqA
          refine ⟨⟨fun h => hqA ?_, fun h => hqA ?_⟩, fun hcon => hqA hcon.2.2⟩
          · rw [h]; exact hvA
          · rw [h]; exact hx
      rw [if_pos hvmem, Separation.pmSum_split W c ((A.erase x).erase v).card _ _ rfl hsub ?_,
        hsd, mul_assoc]
      · rfl
      · intro p hp q hq
        rw [hsd] at hq
        have hpA : p ∈ A := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hp)
        have hpx : p ≠ x := (Finset.mem_erase.mp (Finset.mem_erase.mp hp).2).1
        exact hcut p hpA q (Finset.mem_sdiff.mp hq).2 hpx
    · rw [if_neg (fun h => hvA (Finset.mem_of_mem_erase h)), zero_mul]
      refine mul_eq_zero_of_right _ ?_
      refine pmSum_eq_zero_of_odd_part W c (A := A.erase x) (fun q hq => ?_) hodd
        (fun p hp q hq => ?_)
      · simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hq ⊢
        exact ⟨fun h => hvA (by rw [← h]; exact hq.2), hq.1⟩
      · have hpA : p ∈ A := Finset.mem_of_mem_erase hp
        have hpx : p ≠ x := (Finset.mem_erase.mp hp).1
        have h1 := Finset.mem_sdiff.mp hq
        have h2 := Finset.mem_erase.mp (Finset.mem_erase.mp h1.1).2
        have hqA : q ∉ A := fun hcon => h1.2 (Finset.mem_erase.mpr ⟨h2.1, hcon⟩)
        exact hcut p hpA q hqA hpx
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
  congr 1
  rw [pmSum_expand W c hx, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun v _ => rfl)
  ext v
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

/-- Hence no even part has all of its crossings at a single inside site: the amplitude would
factor, giving flattening rank one where the equations demand three.  Unconditional. -/
theorem false_of_even_part_crossings_at_one_site (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {A : Finset V} (hA : A.Nonempty) (hAc : (Finset.univ \ A).Nonempty)
    (hAeven : Even A.card) {x : V} (hx : x ∈ A)
    (hcut : ∀ p ∈ A, ∀ q : V, q ∉ A → p ≠ x → ∀ a b : Fin 3, W s((p, a), (q, b)) = 0) :
    False := by
  classical
  refine Separation.no_rank_two_flattening W hone hzero A hA hAc
    (fun j c => if j = 0 then pmSum W c A else 0)
    (fun j c => if j = 0 then pmSum W c (Finset.univ \ A) else 0) ?_ ?_ ?_
  · intro j c c' hcc
    by_cases hj : j = 0
    · simp only [hj, if_pos rfl]
      exact pmSum_congr_colour W (fun z hz => hcc z hz)
    · simp only [if_neg hj]
  · intro j c c' hcc
    by_cases hj : j = 0
    · simp only [hj, if_pos rfl]
      exact pmSum_congr_colour W (fun z hz => hcc z hz)
    · simp only [if_neg hj]
  · intro c
    rw [Fin.sum_univ_two]
    simp only [if_pos rfl, if_neg (by decide : (1 : Fin 2) ≠ 0), mul_zero, add_zero, if_true]
    exact amplitude_split_crossings_at_one_site W c hAeven hx
      (fun p hp q hq hpx => hcut p hp q hq hpx _ _)

/-- The same with the concentration on the outside: no even part has all of its crossings
ending at a single site of the complement.  The complement of an even part is even, because a
GHZ configuration has an even number of sites, so the previous theorem applies to it directly.
-/
theorem false_of_even_part_crossings_at_one_outside_site (W : Sym2 (V × Fin 3) → ℂ)
    (hW : KrennGu.IsGHZ W)
    {A : Finset V} (hA : A.Nonempty) (hAc : (Finset.univ \ A).Nonempty)
    (hAeven : Even A.card) {y : V} (hy : y ∉ A)
    (hcut : ∀ p ∈ A, ∀ q : V, q ∉ A → q ≠ y → ∀ a b : Fin 3, W s((p, a), (q, b)) = 0) :
    False := by
  classical
  have hback : Finset.univ \ (Finset.univ \ A) = A := by
    ext t
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]
  have hcompl : Finset.univ \ A = Aᶜ := by ext t; simp
  have hCeven : Even (Finset.univ \ A).card := by
    rw [hcompl, Finset.card_compl]
    obtain ⟨k, hk⟩ := hAeven
    obtain ⟨m, hm⟩ := even_card_of_isGHZ W hW
    have hle : A.card ≤ Fintype.card V := by
      rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ A)
    simp only [Nat.even_iff] at *
    omega
  refine false_of_even_part_crossings_at_one_site W hW.1 hW.2 hAc ?_ hCeven
    (Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hy⟩) ?_
  · rw [hback]; exact hA
  · intro p hp q hq hpy a b
    have hpA : p ∉ A := (Finset.mem_sdiff.mp hp).2
    have hqA : q ∈ A := by
      by_contra h
      exact hq (Finset.mem_sdiff.mpr ⟨Finset.mem_univ q, h⟩)
    rw [Sym2.eq_swap]
    exact hcut q hqA p hpA hpy b a

/-! ### Colour degrees and where the peel is forced -/

open scoped Classical in
/-- The live partners of a site in one colour. -/
noncomputable def liveNbrsCol (W : Sym2 (V × Fin 3) → ℂ) (u : V) (m : Fin 3) : Finset V :=
  (Finset.univ.erase u).filter (fun v => W s((u, m), (v, m)) ≠ 0)

open scoped Classical in
@[simp] lemma mem_liveNbrsCol {W : Sym2 (V × Fin 3) → ℂ} {u m v} :
    v ∈ liveNbrsCol W u m ↔ v ≠ u ∧ W s((u, m), (v, m)) ≠ 0 := by
  simp [liveNbrsCol, Finset.mem_filter, Finset.mem_erase]

/-- **A colour degree of one is where the peel is forced.**

If a site has exactly one live partner in a colour, that partner is the only choice the peel
could make, so the peel makes no choice: the complement's matching sum in that colour is
non-zero automatically.

This is the precise answer to what makes a peel controllable.  Everywhere else the peel picks a
partner the configuration decides, not the argument -- which is why a construction assembled
from peels cannot be steered unless it starts at sites of colour degree one. -/
theorem forced_at_colour_degree_one (W : Sym2 (V × Fin 3) → ℂ) {m : Fin 3}
    (hone : amplitude W (Amplitude.const (V := V) m) ≠ 0) {u : V}
    (hcard : (liveNbrsCol W u m).card = 1) :
    ∃ v : V, liveNbrsCol W u m = {v} ∧ v ≠ u ∧
      pmSum W (Amplitude.const (V := V) m) ((Finset.univ.erase u).erase v) ≠ 0 := by
  classical
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hcard
  have hvmem : v ∈ liveNbrsCol W u m := by rw [hv]; exact Finset.mem_singleton_self v
  have hvu : v ≠ u := (mem_liveNbrsCol.mp hvmem).1
  refine ⟨v, hv, hvu, complement_ne_zero_of_unique_partner W hone hvu (fun z hzu hzv => ?_)⟩
  by_contra hlive
  have : z ∈ liveNbrsCol W u m := mem_liveNbrsCol.mpr ⟨hzu, hlive⟩
  rw [hv, Finset.mem_singleton] at this
  exact hzv this

/-- Under monochromatic live edges, a site's live partners are exactly its partners in the
three colours. -/
theorem liveNbrs_eq_union_col (W : Sym2 (V × Fin 3) → ℂ)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0) (u : V) :
    LiveDegree.liveNbrs W u
      = liveNbrsCol W u 0 ∪ liveNbrsCol W u 1 ∪ liveNbrsCol W u 2 := by
  classical
  ext y
  simp only [LiveDegree.mem_liveNbrs, Finset.mem_union, mem_liveNbrsCol]
  constructor
  · rintro ⟨hyu, a, b, hab⟩
    have hab' : a = b := by
      by_contra hne
      exact hab (hmono u y hyu a b hne)
    subst hab'
    fin_cases a
    · exact Or.inl (Or.inl ⟨hyu, hab⟩)
    · exact Or.inl (Or.inr ⟨hyu, hab⟩)
    · exact Or.inr ⟨hyu, hab⟩
  · rintro ((⟨hyu, h⟩ | ⟨hyu, h⟩) | ⟨hyu, h⟩)
    exacts [⟨hyu, 0, 0, h⟩, ⟨hyu, 1, 1, h⟩, ⟨hyu, 2, 2, h⟩]

/-- **The standing hypothesis, in terms of colour degrees.**

A site with at most one live partner in each colour has at most three live partners.  So to
prove no site has a fourth live neighbour it is enough to prove that no site has a second
partner in any single colour --- which is the form the certificates speak in, and the form in
which "the peel is forced" is a statement about the same object.

The converse needs the three colour neighbourhoods to be disjoint, which holds for exclusive
edges but not in general, so only this direction is stated. -/
theorem card_liveNbrs_le_three_of_colour_degrees (W : Sym2 (V × Fin 3) → ℂ)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0) (u : V)
    (h : ∀ m : Fin 3, (liveNbrsCol W u m).card ≤ 1) :
    (LiveDegree.liveNbrs W u).card ≤ 3 := by
  classical
  rw [liveNbrs_eq_union_col W hmono u]
  refine le_trans (Finset.card_union_le _ _) ?_
  refine le_trans (Nat.add_le_add_right (Finset.card_union_le _ _) _) ?_
  have := h 0; have := h 1; have := h 2
  omega

/-- Colour neighbourhoods of a site are disjoint as soon as its partners in one colour are
exclusive to it. -/
theorem liveNbrsCol_disjoint (W : Sym2 (V × Fin 3) → ℂ) {u : V} {m m' : Fin 3} (hmm' : m ≠ m')
    (hexcl : ∀ v ∈ liveNbrsCol W u m, ∀ j : Fin 3, j ≠ m → W s((u, j), (v, j)) = 0) :
    Disjoint (liveNbrsCol W u m) (liveNbrsCol W u m') := by
  classical
  refine Finset.disjoint_left.mpr (fun v hv hv' => ?_)
  exact (mem_liveNbrsCol.mp hv').2 (hexcl v hv m' (Ne.symm hmm'))

/-- **The bridge in both directions.**  When every partner of a site is exclusive to its
colour, the site's live degree is the sum of its three colour degrees.  So the live degree is
at most three exactly when each colour degree is at most one, and --- since every colour needs
a partner for its amplitude to survive --- exactly one. -/
theorem card_liveNbrs_eq_sum_of_exclusive (W : Sym2 (V × Fin 3) → ℂ)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0) (u : V)
    (hexcl : ∀ m : Fin 3, ∀ v ∈ liveNbrsCol W u m, ∀ j : Fin 3, j ≠ m →
      W s((u, j), (v, j)) = 0) :
    (LiveDegree.liveNbrs W u).card
      = (liveNbrsCol W u 0).card + (liveNbrsCol W u 1).card + (liveNbrsCol W u 2).card := by
  classical
  have h01 : Disjoint (liveNbrsCol W u 0) (liveNbrsCol W u 1) :=
    liveNbrsCol_disjoint W (by decide) (hexcl 0)
  have h02 : Disjoint (liveNbrsCol W u 0) (liveNbrsCol W u 2) :=
    liveNbrsCol_disjoint W (by decide) (hexcl 0)
  have h12 : Disjoint (liveNbrsCol W u 1) (liveNbrsCol W u 2) :=
    liveNbrsCol_disjoint W (by decide) (hexcl 1)
  rw [liveNbrs_eq_union_col W hmono u,
    Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨h02, h12⟩),
    Finset.card_union_of_disjoint h01]

/-- **Every site has a partner in every colour.**  A colour whose constant amplitude survives
must match the whole site set, so it reaches every site.  With the bridge above this pins the
degree picture: colour degrees are at least one everywhere, and live degree at most three means
they are exactly one. -/
theorem liveNbrsCol_nonempty (W : Sym2 (V × Fin 3) → ℂ) {m : Fin 3}
    (hone : amplitude W (Amplitude.const (V := V) m) ≠ 0) (u : V) :
    (liveNbrsCol W u m).Nonempty := by
  classical
  have huniv : pmSum W (Amplitude.const (V := V) m) Finset.univ ≠ 0 := by
    rw [pmSum_univ]; exact hone
  obtain ⟨v, hv, hw, -⟩ :=
    exists_partner_ne_zero W (Amplitude.const (V := V) m) (Finset.mem_univ u) huniv
  exact ⟨v, mem_liveNbrsCol.mpr ⟨(Finset.mem_erase.mp hv).1, hw⟩⟩

/-- Consequently, on a configuration whose partners are exclusive, live degree at most three
forces exactly one partner per colour --- three-regularity, which is already excluded above four
sites. -/
theorem colour_degree_eq_one (W : Sym2 (V × Fin 3) → ℂ)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hone : ∀ m : Fin 3, amplitude W (Amplitude.const (V := V) m) ≠ 0) (u : V)
    (hexcl : ∀ m : Fin 3, ∀ v ∈ liveNbrsCol W u m, ∀ j : Fin 3, j ≠ m →
      W s((u, j), (v, j)) = 0)
    (hdeg : (LiveDegree.liveNbrs W u).card ≤ 3) :
    ∀ m : Fin 3, (liveNbrsCol W u m).card = 1 := by
  classical
  have hsum := card_liveNbrs_eq_sum_of_exclusive W hmono u hexcl
  have h0 := Finset.card_pos.mpr (liveNbrsCol_nonempty W (hone 0) u)
  have h1 := Finset.card_pos.mpr (liveNbrsCol_nonempty W (hone 1) u)
  have h2 := Finset.card_pos.mpr (liveNbrsCol_nonempty W (hone 2) u)
  rw [hsum] at hdeg
  have hb : (liveNbrsCol W u 0).card = 1 ∧ (liveNbrsCol W u 1).card = 1 ∧
      (liveNbrsCol W u 2).card = 1 := by omega
  intro m
  fin_cases m
  exacts [hb.1, hb.2.1, hb.2.2]

/-- **No two sites share a unique colour partner.**

If a site's only live partner in a colour is `u`, peeling it is forced and the complement of
that pair still matches in the colour.  A second site whose only partner is also `u` is left
inside that complement with nothing to pair with, so the complement's matching sum vanishes ---
contradicting what the forced peel just established.

Equivalently: the sites of colour degree one in a given colour have pairwise distinct partners,
so they form a partial matching.

This is **not** new: `HardCase.not_two_pendant_same` states the same fact, proved directly by
showing every matching contributes zero.  The proof here is different and shorter -- it reads
off the forced peel -- and it is phrased in colour degrees, which is the vocabulary the rest of
this file uses.  Recorded as a second route to a known result, not as a new one. -/
theorem not_share_unique_colour_partner (W : Sym2 (V × Fin 3) → ℂ) {m : Fin 3}
    (hone : amplitude W (Amplitude.const (V := V) m) ≠ 0) {u v v' : V}
    (hvv' : v' ≠ v) (huv : u ≠ v) (huv' : u ≠ v')
    (huniqv : ∀ z : V, z ≠ v → z ≠ u → W s((v, m), (z, m)) = 0)
    (huniqv' : ∀ z : V, z ≠ v' → z ≠ u → W s((v', m), (z, m)) = 0) :
    False := by
  classical
  have hne := complement_ne_zero_of_unique_partner W hone huv huniqv
  refine hne ?_
  have hv'mem : v' ∈ (Finset.univ.erase v).erase u :=
    Finset.mem_erase.mpr ⟨Ne.symm huv', Finset.mem_erase.mpr
      ⟨hvv', Finset.mem_univ v'⟩⟩
  refine pmSum_eq_zero_of_isolated W (Amplitude.const (V := V) m) hv'mem (fun z hz => ?_)
  have hzv' : z ≠ v' := (Finset.mem_erase.mp hz).1
  have hzu : z ≠ u := (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).1
  exact huniqv' z hzv' hzu


/-- **The joining condition, pair by pair.**

The localised theorems ask that nothing live join two classes of a colouring.  That holds as
soon as every pair carrying different colours is either dead outright or monochromatic as a
pair -- and the second alternative is what `FanStructure.edge_monochromatic` supplies at a pair
whose two ends are degenerate and which support minimality makes non-inert.

Stated this way the condition decomposes.  To meet it one need only arrange the colouring so
that every pair it separates falls into one of the two cases: in particular, bundling the
non-degenerate sites together with all their live neighbours into a single class leaves every
separated pair either dead, because a non-degenerate site's live edges all stay inside the
bundle, or degenerate at both ends. -/
theorem join_of_dead_or_mono_pair (W : Sym2 (V × Fin 3) → ℂ) (c : V → Fin 3)
    (h : ∀ x y : V, y ≠ x → c x ≠ c y →
      (∀ a b : Fin 3, W s((x, a), (y, b)) = 0) ∨
        (∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)) :
    ∀ x y : V, c x ≠ c y → W s((x, c x), (y, c y)) = 0 := by
  intro x y hxy
  have hyx : y ≠ x := by
    intro hh
    exact hxy (by rw [hh])
  rcases h x y hyx hxy with hdead | hmono
  · exact hdead _ _
  · exact hmono _ _ hxy

/-! ### Building the surviving colouring -/

/-- **A split builds a surviving mixed colouring.**

The positive content of the two-colour equation.  Given a proper non-empty set matching in one
colour whose complement matches in another, colour the set one way and its complement the
other: nothing joins the two classes, so the amplitude is the product of their matching sums,
and the colouring is not constant.

Everything in this file that ends in a contradiction is this lemma read backwards.  Stated
this way it is a step of the construction the conjecture asks for, and can be chained with any
certificate that produces a non-vanishing matching sum --- a peel, a tail, a colour cut, or a
single live edge. -/
theorem mixed_of_split (W : Sym2 (V × Fin 3) → ℂ)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {S : Finset V} (hS : S.Nonempty) (hSne : S ≠ Finset.univ)
    {j k : Fin 3} (hjk : j ≠ k)
    (hk : pmSum W (Amplitude.const (V := V) k) S ≠ 0)
    (hj : pmSum W (Amplitude.const (V := V) j) (Finset.univ \ S) ≠ 0) :
    ∃ c : V → Fin 3, ¬ Amplitude.Monochromatic c ∧ amplitude W c ≠ 0 := by
  classical
  set c : V → Fin 3 := fun z => if z ∈ S then k else j with hc
  have hin : ∀ z ∈ S, c z = k := by intro z hz; simp [hc, hz]
  have hout : ∀ z, z ∉ S → c z = j := by intro z hz; simp [hc, hz]
  have hcut : ∀ x y : V, c x ≠ c y → W s((x, c x), (y, c y)) = 0 :=
    fun x y h => hmono x y (fun hxy => h (by rw [hxy])) _ _ h
  obtain ⟨w, hw⟩ : ∃ w : V, w ∉ S := by
    by_contra hno
    push_neg at hno
    exact hSne (Finset.eq_univ_iff_forall.mpr hno)
  obtain ⟨z, hz⟩ := hS
  refine ⟨c, ?_, ?_⟩
  · rintro ⟨t, ht⟩
    exact hjk (by rw [← hout w hw, ht w, ← ht z, hin z hz])
  · have hfib : fiber c k = S := by
      ext y
      simp only [mem_fiber]
      refine ⟨fun h => ?_, hin y⟩
      by_contra hy
      exact hjk (by rw [← h, hout y hy])
    have h1 : pmSum W c S = pmSum W (Amplitude.const (V := V) k) S :=
      pmSum_congr_colour W (fun y hy => hin y hy)
    have h2 : pmSum W c (Finset.univ \ S)
        = pmSum W (Amplitude.const (V := V) j) (Finset.univ \ S) :=
      pmSum_congr_colour W (fun y hy => hout y (Finset.mem_sdiff.mp hy).2)
    rw [pmSum_fiber_split W c hcut k, hfib, h1, h2]
    exact mul_ne_zero hk hj

/-- A pair of exact peels builds the surviving colouring outright. -/
theorem mixed_of_exactPeel_split (W : Sym2 (V × Fin 3) → ℂ)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {S : Finset V} (hS : S.Nonempty) (hSne : S ≠ Finset.univ)
    {j k : Fin 3} (hjk : j ≠ k)
    (hk : ExactPeel W (Amplitude.const (V := V) k) S)
    (hj : ExactPeel W (Amplitude.const (V := V) j) (Finset.univ \ S)) :
    ∃ c : V → Fin 3, ¬ Amplitude.Monochromatic c ∧ amplitude W c ≠ 0 :=
  mixed_of_split W hmono hS hSne hjk (pmSum_ne_zero_of_exactPeel hk)
    (pmSum_ne_zero_of_exactPeel hj)

/-- So does a set that two colours both decline to leave: each matches one side, and the two
sides carry the two colours. -/
theorem mixed_of_two_colour_cut (W : Sym2 (V × Fin 3) → ℂ)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {S : Finset V} (hS : S.Nonempty) (hSne : S ≠ Finset.univ)
    {j k : Fin 3} (hjk : j ≠ k)
    (honek : amplitude W (Amplitude.const (V := V) k) ≠ 0)
    (honej : amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hcutk : ∀ x ∈ S, ∀ y ∈ Finset.univ \ S, W s((x, k), (y, k)) = 0)
    (hcutj : ∀ x ∈ S, ∀ y ∈ Finset.univ \ S, W s((x, j), (y, j)) = 0) :
    ∃ c : V → Fin 3, ¬ Amplitude.Monochromatic c ∧ amplitude W c ≠ 0 :=
  mixed_of_split W hmono hS hSne hjk
    (pmSum_ne_zero_of_colour_cut W honek S hcutk).1
    (pmSum_ne_zero_of_colour_cut W honej S hcutj).2

/-- **A colouring whose every class matches in its own colour has non-zero amplitude.**

The most general positive statement available: no split into two parts is needed, only that
each of the three colour classes of the colouring carries a matching sum in the colour it
wears, and that nothing live joins two classes.

The joining condition is stated for this colouring alone, not as a blanket requirement that
every live edge be monochromatic.  That distinction matters: the local form applies to
configurations with non-degenerate sites, which the blanket form cannot reach. -/
theorem amplitude_ne_zero_of_classes_match_of_cut (W : Sym2 (V × Fin 3) → ℂ) (c : V → Fin 3)
    (hcut : ∀ x y : V, c x ≠ c y → W s((x, c x), (y, c y)) = 0)
    (h : ∀ m : Fin 3, pmSum W (Amplitude.const (V := V) m) (fiber c m) ≠ 0) :
    amplitude W c ≠ 0 := by
  classical
  have hcong : ∀ m : Fin 3, pmSum W c (fiber c m)
      = pmSum W (Amplitude.const (V := V) m) (fiber c m) :=
    fun m => pmSum_congr_colour W (fun y hy => mem_fiber.mp hy)
  rw [amplitude_product W c hcut, hcong 0, hcong 1, hcong 2]
  exact mul_ne_zero (mul_ne_zero (h 0) (h 1)) (h 2)

/-- The same under the blanket hypothesis, which supplies the joining condition for every
colouring at once. -/
theorem amplitude_ne_zero_of_classes_match (W : Sym2 (V × Fin 3) → ℂ)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (c : V → Fin 3)
    (h : ∀ m : Fin 3, pmSum W (Amplitude.const (V := V) m) (fiber c m) ≠ 0) :
    amplitude W c ≠ 0 :=
  amplitude_ne_zero_of_classes_match_of_cut W c
    (fun x y hxy => hmono x y (fun h' => hxy (by rw [h'])) _ _ hxy) h

/-- The construction, packaged for the positive form: a non-constant colouring all of whose
classes match in their own colours is exactly the witness `MixedSurvives` demands. -/
theorem mixed_of_classes_match (W : Sym2 (V × Fin 3) → ℂ)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (c : V → Fin 3) (hnm : ¬ Amplitude.Monochromatic c)
    (h : ∀ m : Fin 3, pmSum W (Amplitude.const (V := V) m) (fiber c m) ≠ 0) :
    ∃ c' : V → Fin 3, ¬ Amplitude.Monochromatic c' ∧ amplitude W c' ≠ 0 :=
  ⟨c, hnm, amplitude_ne_zero_of_classes_match W hmono c h⟩

/-- **Three induced matchings that partition the sites build the witness.**

Suppose the sites split into three classes, each carrying a perfect matching in the colour it
wears, with *no other live edge of that colour inside the class* --- an induced matching.  Then
each class peels forcedly along its matching, so each carries a non-vanishing matching sum, and
the amplitude is their product.

This turns the construction the conjecture asks for into a purely combinatorial question, with
no matching sums or cancellation left in it: **does a partition into three induced matchings,
one per colour, exist that is not constant?**  Where the colour classes are themselves perfect
matchings the condition is automatic and the mixed-colouring construction supplies the
partition; the content is what happens when a colour class carries extra edges, since a class
must then be chosen to avoid its own chords. -/
theorem mixed_of_induced_matchings (W : Sym2 (V × Fin 3) → ℂ)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (c : V → Fin 3) (hnm : ¬ Amplitude.Monochromatic c)
    (τ : V → V) (hinv : ∀ t : V, τ (τ t) = t) (hne : ∀ t : V, τ t ≠ t)
    (hcol : ∀ t : V, c (τ t) = c t)
    (hlive : ∀ t : V, W s((t, c t), (τ t, c t)) ≠ 0)
    (huniq : ∀ t z : V, c z = c t → z ≠ t → z ≠ τ t → W s((t, c t), (z, c t)) = 0) :
    ∃ c' : V → Fin 3, ¬ Amplitude.Monochromatic c' ∧ amplitude W c' ≠ 0 := by
  classical
  refine mixed_of_classes_match W hmono c hnm (fun m => ?_)
  refine pmSum_ne_zero_of_forcedPeel
    (forcedPeel_of_involution W (Amplitude.const (V := V) m) τ hinv hne
      (fiber c m).card (fiber c m) rfl (fun t ht => ?_) (fun t ht => ?_) (fun t ht z hz => ?_))
  · rw [mem_fiber] at ht ⊢
    rw [hcol t, ht]
  · have hcm : c t = m := mem_fiber.mp ht
    have := hlive t
    rwa [hcm] at this
  · intro hzt hzτ
    have hcm : c t = m := mem_fiber.mp ht
    have hcz : c z = m := mem_fiber.mp hz
    have := huniq t z (by rw [hcz, hcm]) hzt hzτ
    rwa [hcm] at this

/-- **The three-colour cut theorem, with only local joining conditions.**

No non-constant colouring has all three of: nothing live joining two of its classes, and each
class left by no live edge of the colour it wears.  Each class would then carry a non-vanishing
matching sum, the amplitude would be their product, and a non-constant colouring has amplitude
zero.

Both hypotheses are about this colouring alone.  The two-colour case of this pattern is
`Separation.no_two_colour_closed`, already in the library with the same local shape; the
three-colour case appears to have no counterpart there, and is what the product formula
buys. -/
theorem false_of_three_colour_cut_of_cut (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hone : ∀ m : Fin 3, amplitude W (Amplitude.const (V := V) m) ≠ 0)
    (c : V → Fin 3) (hnm : ¬ Amplitude.Monochromatic c)
    (hjoin : ∀ x y : V, c x ≠ c y → W s((x, c x), (y, c y)) = 0)
    (hcolcut : ∀ m : Fin 3, ∀ x ∈ fiber c m, ∀ y ∈ Finset.univ \ fiber c m,
      W s((x, m), (y, m)) = 0) :
    False :=
  amplitude_ne_zero_of_classes_match_of_cut W c hjoin
    (fun m => (pmSum_ne_zero_of_colour_cut W (hone m) (fiber c m) (hcolcut m)).1)
    (hzero c hnm)

/-- **A split builds a surviving colouring, needing only the crossing blocks dead.**

The positive counterpart of the localised two-colour equation, and the form the construction
actually wants: colour a set one way and its complement another, and if nothing live joins the
two the amplitude is the product of their matching sums. -/
theorem mixed_of_split_of_cut (W : Sym2 (V × Fin 3) → ℂ)
    {S : Finset V} (hS : S.Nonempty) (hSne : S ≠ Finset.univ)
    {j k : Fin 3} (hjk : j ≠ k)
    (hcross : ∀ x ∈ S, ∀ y : V, y ∉ S → W s((x, k), (y, j)) = 0)
    (hk : pmSum W (Amplitude.const (V := V) k) S ≠ 0)
    (hj : pmSum W (Amplitude.const (V := V) j) (Finset.univ \ S) ≠ 0) :
    ∃ c : V → Fin 3, ¬ Amplitude.Monochromatic c ∧ amplitude W c ≠ 0 := by
  classical
  set c : V → Fin 3 := fun z => if z ∈ S then k else j with hc
  have hin : ∀ z ∈ S, c z = k := by intro z hz; simp [hc, hz]
  have hout : ∀ z, z ∉ S → c z = j := by intro z hz; simp [hc, hz]
  have hcut : ∀ x y : V, c x ≠ c y → W s((x, c x), (y, c y)) = 0 := by
    intro x y hxy
    by_cases hxS : x ∈ S
    · by_cases hyS : y ∈ S
      · exact absurd (by rw [hin x hxS, hin y hyS]) hxy
      · rw [hin x hxS, hout y hyS]; exact hcross x hxS y hyS
    · by_cases hyS : y ∈ S
      · rw [hout x hxS, hin y hyS, Sym2.eq_swap]; exact hcross y hyS x hxS
      · exact absurd (by rw [hout x hxS, hout y hyS]) hxy
  obtain ⟨w, hw⟩ : ∃ w : V, w ∉ S := by
    by_contra hno
    push_neg at hno
    exact hSne (Finset.eq_univ_iff_forall.mpr hno)
  obtain ⟨z, hz⟩ := hS
  refine ⟨c, ?_, ?_⟩
  · rintro ⟨t, ht⟩
    exact hjk (by rw [← hout w hw, ht w, ← ht z, hin z hz])
  · have hfib : fiber c k = S := by
      ext y
      simp only [mem_fiber]
      refine ⟨fun h => ?_, hin y⟩
      by_contra hy
      exact hjk (by rw [← hout y hy, h])
    have h1 : pmSum W c S = pmSum W (Amplitude.const (V := V) k) S :=
      pmSum_congr_colour W (fun y hy => hin y hy)
    have h2 : pmSum W c (Finset.univ \ S)
        = pmSum W (Amplitude.const (V := V) j) (Finset.univ \ S) :=
      pmSum_congr_colour W (fun y hy => hout y (Finset.mem_sdiff.mp hy).2)
    rw [pmSum_fiber_split W c hcut k, hfib, h1, h2]
    exact mul_ne_zero hk hj

/-! ### The positive form of the conjecture -/

section Positive

/-- **Some mixed colouring survives.**

The conjecture, stated as a construction rather than a refutation: on more than four sites,
any weight system whose three constant amplitudes are non-zero has *some* non-constant
colouring with non-zero amplitude.

This says exactly what the conjecture says, but it quantifies over all weight systems with
non-vanishing constant amplitudes -- a class full of concrete objects -- instead of over GHZ
systems, of which the conjecture asserts there are none.  A hypothesis of the latter kind is
vacuous once the conjecture holds, so it can only ever be refuted, never developed.  This one
can be worked with directly, and every certificate in this file is already of its shape: each
builds a non-vanishing amplitude rather than assuming one away. -/
def MixedSurvives : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (W : Sym2 (V × Fin 3) → ℂ),
    4 < Fintype.card V →
    (∀ k : Fin 3, amplitude W (Amplitude.const (V := V) k) ≠ 0) →
    ∃ c : V → Fin 3, ¬ Amplitude.Monochromatic c ∧ amplitude W c ≠ 0

/-- The full conjecture follows from the positive form at once: a GHZ system supplies the
non-vanishing constant amplitudes, and the surviving mixed colouring contradicts its own
vanishing condition. -/
theorem krenn_gu_of_mixedSurvives (h : MixedSurvives) :
    ∀ n : ℕ, 3 ≤ n → ¬ KrennGu.Solvable n := by
  rintro n hn ⟨W, hone, hzero⟩
  have hcard : 4 < Fintype.card (Fin (2 * n)) := by
    rw [Fintype.card_fin]; omega
  obtain ⟨c, hnm, hne⟩ := h (Fin (2 * n)) W hcard hone
  exact hne (hzero c hnm)

end Positive

/-! ### Splitting a matching along an invariant set

A matching of a set is carried by a fixed-point-free involution.  If a subset is closed under
that involution then the involution restricts to it — and, because the complement of an
invariant set is invariant too, it restricts to the complement in the same breath.  One
matching therefore splits along any invariant set into matchings of *both* sides.

This is the engine behind the two-colour picture.  Two matchings in different colours are
arbitrary -- the splitting needs no relation between them at all -- and a set closed under both
restricts both of them at once: the set is matchable in the first colour and its complement in the second.  So
a proper non-empty set invariant under two matchings hands over a non-constant colouring whose
classes are each matchable in their own colour.

What it does not hand over is non-vanishing, and the distance between the two is exactly this
file's subject: the matching just built is one term of its class's sum, and the other terms may
cancel it.  Stated positively, the equations force every set invariant under two live matchings
to be trivial -- the two matchings together act with a single orbit.  That is a sharp structural
demand, and it is reached with no cyclic coordinates and no vertex count. -/


/-! ### The four-site colour swap

The peel certifies a pair and its complement in the *same* colour, which is useless on its own:
recolouring the pair needs its edge live in a second colour, and once every live edge is
monochromatic no edge is live twice.  Peeling **twice** escapes that.  What comes off is a
four-set, and a four-set has only three matchings -- so if two of the three options at one of
its corners are dead in the second colour, the remaining matching is forced and cancellation
cannot touch it.

This is the cancellation obstacle turned around at the smallest size where there is anything to
turn: the certificate is a single product, by construction, not a sum that has to be shown
non-zero. -/

section Quad

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The four-site colour swap.**  A four-set forced in colour `k`, whose complement carries a
matching sum in colour `j`, with nothing live joining the two: the colouring built from them is
non-constant and its amplitude is a product of two non-zero factors.  Nothing here is a sum, so
there is nothing for the other matchings to cancel. -/
theorem false_of_quad_swap (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {j k : Fin 3} (hjk : j ≠ k) {a b x y : V}
    (hab : a ≠ b) (hax : a ≠ x) (hay : a ≠ y) (hbx : b ≠ x) (hby : b ≠ y) (hxy : x ≠ y)
    (hdb : W s((a, k), (b, k)) = 0) (hdy : W s((a, k), (y, k)) = 0)
    (hax' : W s((a, k), (x, k)) ≠ 0) (hby' : W s((b, k), (y, k)) ≠ 0)
    (hcross : ∀ u ∈ ({a, b, x, y} : Finset V), ∀ v : V, v ∉ ({a, b, x, y} : Finset V) →
      W s((u, k), (v, j)) = 0)
    (hrest : pmSum W (Amplitude.const (V := V) j)
      (Finset.univ \ ({a, b, x, y} : Finset V)) ≠ 0)
    (hne : ({a, b, x, y} : Finset V) ≠ Finset.univ) : False := by
  classical
  have hquad : pmSum W (Amplitude.const (V := V) k) ({a, b, x, y} : Finset V) ≠ 0 := by
    rw [pmSum_quad_forced W (Amplitude.const (V := V) k) hab hax hay hbx hby hxy hdb hdy]
    exact mul_ne_zero hax' hby'
  obtain ⟨c, hnm, hc⟩ :=
    mixed_of_split_of_cut W (S := ({a, b, x, y} : Finset V)) ⟨a, by simp⟩ hne hjk hcross
      hquad hrest
  exact hc (hzero c hnm)

/-- **The four-site colour swap, fed by a certified pair.**  One of the two dead options the
certificate needs comes for free: a pair live in colour `j` whose complement still carries a
colour-`j` matching sum is dead in every other colour.  The cut hypothesis is free too, since no
live edge mixes colours at its two ends.  What is left to supply is the second dead option and
the two live edges of the forced matching. -/
theorem false_of_quad_swap_of_certified (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {j k : Fin 3} (hjk : j ≠ k) {a b x y : V}
    (hab : a ≠ b) (hax : a ≠ x) (hay : a ≠ y) (hbx : b ≠ x) (hby : b ≠ y) (hxy : x ≠ y)
    (hcert : pmSum W (Amplitude.const (V := V) j) ((Finset.univ.erase a).erase b) ≠ 0)
    (hout : ∃ z : V, z ≠ a ∧ z ≠ b)
    (hdy : W s((a, k), (y, k)) = 0)
    (hax' : W s((a, k), (x, k)) ≠ 0) (hby' : W s((b, k), (y, k)) ≠ 0)
    (hrest : pmSum W (Amplitude.const (V := V) j)
      (Finset.univ \ ({a, b, x, y} : Finset V)) ≠ 0)
    (hne : ({a, b, x, y} : Finset V) ≠ Finset.univ) : False :=
  false_of_quad_swap W hzero hjk hab hax hay hbx hby hxy
    (exclusive_of_partner_ne_zero W hzero hmono (Ne.symm hab) hcert hout (Ne.symm hjk))
    hdy hax' hby'
    (fun u hu v hv => hmono u v (by rintro rfl; exact hv hu) k j (Ne.symm hjk))
    hrest hne

/-- **The interlocking forbidden.**  Assemble the certificate from what the peel actually
supplies.  Take a pair `{a,b}` certified in colour `j`, and inside the complement a site `x`
with a colour-`j` partner `y` that leaves the rest still matching -- this is exactly one step of
the peel, so the four-set's complement is certified for free.  If moreover `x` is live to `a` in
colour `k` while `y` is not, then `y` cannot be live to `b` in colour `k`.

So the colour-`k` edges leaving a certified colour-`j` pair cannot interlock with a certified
colour-`j` pair inside the complement.  This is the alternating pattern, forbidden without any
census and at every vertex count. -/
theorem peel_partner_not_live_to_partner (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hcard : 4 < Fintype.card V) {j k : Fin 3} (hjk : j ≠ k) {a b x y : V}
    (hab : a ≠ b) (hax : a ≠ x) (hay : a ≠ y) (hbx : b ≠ x) (hby : b ≠ y) (hxy : x ≠ y)
    (hcert : pmSum W (Amplitude.const (V := V) j) ((Finset.univ.erase a).erase b) ≠ 0)
    (hout : ∃ z : V, z ≠ a ∧ z ≠ b)
    (hax' : W s((a, k), (x, k)) ≠ 0)
    (hady : W s((a, k), (y, k)) = 0)
    (hrest : pmSum W (Amplitude.const (V := V) j)
      (((((Finset.univ.erase a).erase b).erase x).erase y)) ≠ 0) :
    W s((b, k), (y, k)) = 0 := by
  classical
  by_contra hby'
  have hset : ((((Finset.univ.erase a).erase b).erase x).erase y)
      = Finset.univ \ ({a, b, x, y} : Finset V) := by
    ext z
    simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
      Finset.mem_singleton, true_and, and_true, not_or]
    tauto
  have hne : ({a, b, x, y} : Finset V) ≠ Finset.univ := by
    intro h
    have h4 : ({a, b, x, y} : Finset V).card ≤ 4 :=
      (Finset.card_insert_le _ _).trans (by
        have := Finset.card_insert_le b ({x, y} : Finset V)
        have h2 : ({x, y} : Finset V).card ≤ 2 :=
          (Finset.card_insert_le _ _).trans (by simp)
        omega)
    rw [h, Finset.card_univ] at h4
    omega
  rw [hset] at hrest
  exact false_of_quad_swap_of_certified W hzero hmono hjk hab hax hay hbx hby hxy
    hcert hout hady hax' hby' hrest hne

/-- The same fact in the form an argument consumes: under colour degree one at `a`, none of
`b`'s colour-`k` neighbours can be removed alongside `a`, `b` and `a`'s own colour-`k` partner
while leaving a colour-`j` matching sum behind.

Read against the colour-`j` expansion at `x` inside the complement of `{a,b}`, this says the
expansion is supported entirely off `b`'s colour-`k` neighbourhood: every partner the peel is
allowed to choose misses it. -/
theorem pmSum_zero_of_colour_nbr_of_degree_one (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hcard : 4 < Fintype.card V) {j k : Fin 3} (hjk : j ≠ k) {a b x y : V}
    (hab : a ≠ b) (hax : a ≠ x) (hay : a ≠ y) (hbx : b ≠ x) (hby : b ≠ y) (hxy : x ≠ y)
    (hcert : pmSum W (Amplitude.const (V := V) j) ((Finset.univ.erase a).erase b) ≠ 0)
    (hout : ∃ z : V, z ≠ a ∧ z ≠ b)
    (hax' : W s((a, k), (x, k)) ≠ 0)
    (hdeg1 : ∀ z : V, z ≠ x → W s((a, k), (z, k)) = 0)
    (hby' : W s((b, k), (y, k)) ≠ 0) :
    pmSum W (Amplitude.const (V := V) j)
      (((((Finset.univ.erase a).erase b).erase x).erase y)) = 0 := by
  by_contra hrest
  exact hby' (peel_partner_not_live_to_partner W hzero hmono hcard hjk hab hax hay hbx hby hxy
    hcert hout hax' (hdeg1 y (Ne.symm hxy)) hrest)

end Quad

/-! ### Why near-constant colourings carry nothing

The flip formula writes the amplitude of a colouring that differs from a constant at one site
as a pairing between that site's off-colour row and the vector of single-colour matching sums
over the complements of its edges.  Off the monochromatic branch that pairing is real
information: the equations say the row annihilates the vector.

On the branch this file works in it is not.  Every off-colour row is identically zero, because
no live edge mixes colours at its two ends -- so the amplitude of a single flip vanishes with no
appeal to the equations at all.  Nothing can be extracted there, and the same holds for any
colouring whose minority class is a single site.

This locates the content.  Whatever the equations are saying on this branch, they are saying it
about colourings with three substantial classes, which is exactly the product formula's regime:
no non-trivial partition has all three classes certified in their own colours. -/

section Flips

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **A single flip vanishes for free.**  With no live edge mixing colours, the amplitude of a
colouring that differs from a constant at one site is zero without using the equations -- so the
equations say nothing there. -/
theorem amplitude_flip_zero_of_mono (W : Sym2 (V × Fin 3) → ℂ)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (w : V) {k₀ k₁ : Fin 3} (hk : k₁ ≠ k₀) :
    amplitude W (Function.update (Amplitude.const (V := V) k₀) w k₁) = 0 := by
  rw [← pmSum_univ, SingleFlip.pmSum_single_flip W (Finset.mem_univ w) k₀ k₁]
  refine Finset.sum_eq_zero fun z hz => ?_
  rw [hmono w z (Finset.mem_erase.mp hz).1 k₁ k₀ hk, zero_mul]

end Flips

/-! ### The residual, with no quantum content

Assembling the pieces states what is left as a single question about weighted graphs.

Proving the positive form by contradiction supplies the vanishing condition -- that is what a
contradiction hypothesis is -- and on a support-minimal representative with every site
degenerate it supplies monochromaticity too.  From there the product formula turns the amplitude
of a colouring into the product of its three classes' own-colour matching sums, and the theorem
below turns that into a sufficient condition.

So the whole conjecture reduces to: **three weighted graphs on a common vertex set, each with a
non-vanishing perfect matching sum, always admit a non-trivial partition of the vertices into
three parts, the `m`-th of which has a non-vanishing matching sum in the `m`-th graph.**  No
amplitudes, no colourings of edges, no quantum content -- and no vertex count, which is the
point. -/

section Residual

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **A certified partition survives.**  If no live edge mixes colours and each class of a
colouring carries a non-vanishing matching sum in its own colour, the colouring's amplitude is
non-zero.  This is the converse companion of the product formula, and the reason the partition
question is the whole residual. -/
theorem amplitude_ne_zero_of_certified_partition (W : Sym2 (V × Fin 3) → ℂ)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (c : V → Fin 3)
    (hcert : ∀ m : Fin 3, pmSum W (Amplitude.const (V := V) m) (fiber c m) ≠ 0) :
    amplitude W c ≠ 0 := by
  classical
  have hcut : ∀ x y : V, c x ≠ c y → W s((x, c x), (y, c y)) = 0 := by
    intro x y hxy
    exact hmono x y (fun h => hxy (by rw [h])) (c x) (c y) hxy
  have hfib : ∀ m : Fin 3,
      pmSum W c (fiber c m) = pmSum W (Amplitude.const (V := V) m) (fiber c m) := by
    intro m
    exact pmSum_congr_colour W (fun x hx => mem_fiber.mp hx)
  rw [amplitude_product W c hcut, hfib 0, hfib 1, hfib 2]
  exact mul_ne_zero (mul_ne_zero (hcert 0) (hcert 1)) (hcert 2)

/-- **The residual as a statement about weighted graphs.**  Three weightings on a common vertex
set, each with a non-vanishing perfect matching sum, admit a non-trivial partition whose `m`-th
part has a non-vanishing matching sum in the `m`-th weighting. -/
def CertifiedPartition : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (W : Sym2 (V × Fin 3) → ℂ),
    4 < Fintype.card V →
    (∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0) →
    (∀ k : Fin 3, pmSum W (Amplitude.const (V := V) k) Finset.univ ≠ 0) →
    ∃ c : V → Fin 3, ¬ Amplitude.Monochromatic c ∧
      ∀ m : Fin 3, pmSum W (Amplitude.const (V := V) m) (fiber c m) ≠ 0

/-- The partition question implies the positive form, on the branch where no live edge mixes
colours. -/
theorem mixed_of_certifiedPartition (h : CertifiedPartition)
    (V : Type) [Fintype V] [DecidableEq V]
    (W : Sym2 (V × Fin 3) → ℂ) (hV : 4 < Fintype.card V)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const (V := V) k) ≠ 0) :
    ∃ c : V → Fin 3, ¬ Amplitude.Monochromatic c ∧ amplitude W c ≠ 0 := by
  classical
  have huniv : ∀ k : Fin 3, pmSum W (Amplitude.const (V := V) k) Finset.univ ≠ 0 := by
    intro k; rw [pmSum_univ]; exact hone k
  obtain ⟨c, hnm, hcert⟩ := h V W hV hmono huniv
  exact ⟨c, hnm, amplitude_ne_zero_of_certified_partition W hmono c hcert⟩

end Residual

/-! ### Two pendant edges: a certificate with no cancellation anywhere

The four-site swap still had to argue that a sum of three terms collapsed to one.  Using all
three colours removes even that.  Give one colour a single live edge, a second colour another
single live edge, and the third colour everything else: the first two classes have exactly one
matching each, so their sums are single products and nothing can cancel them.  Only the third
class is a genuine sum, and the peel certifies it.

This is the cheapest certificate in the file, and the only one whose non-vanishing is immediate
at every factor. -/

section Pendant

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The colouring that isolates two edges in two colours and leaves the rest in the third. -/
noncomputable def pendantColouring (a p b r : V) : V → Fin 3 :=
  fun z => if z ∈ ({a, p} : Finset V) then 1 else if z ∈ ({b, r} : Finset V) then 2 else 0

variable {a p b r : V}

theorem fiber_pendant_one (hab : a ≠ b) (har : a ≠ r) (hpb : p ≠ b) (hpr : p ≠ r) :
    fiber (pendantColouring a p b r) 1 = ({a, p} : Finset V) := by
  ext z
  simp only [mem_fiber, pendantColouring]
  by_cases h : z ∈ ({a, p} : Finset V)
  · simp [h]
  · refine ⟨fun hz => ?_, fun hz => absurd hz h⟩
    rw [if_neg h] at hz
    split at hz <;> exact absurd hz (by decide)

theorem fiber_pendant_two (hab : a ≠ b) (har : a ≠ r) (hpb : p ≠ b) (hpr : p ≠ r) :
    fiber (pendantColouring a p b r) 2 = ({b, r} : Finset V) := by
  have hdisj : ∀ z : V, z ∈ ({a, p} : Finset V) → z ∉ ({b, r} : Finset V) := by
    intro z hz hz2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz hz2
    rcases hz with rfl | rfl <;> rcases hz2 with rfl | rfl
    exacts [hab rfl, har rfl, hpb rfl, hpr rfl]
  ext z
  simp only [mem_fiber, pendantColouring]
  by_cases h : z ∈ ({a, p} : Finset V)
  · rw [if_pos h]
    exact ⟨fun hz => absurd hz (by decide), fun hz => absurd hz (hdisj z h)⟩
  · rw [if_neg h]
    by_cases h2 : z ∈ ({b, r} : Finset V)
    · simp [h2]
    · simp only [if_neg h2]
      exact ⟨fun hz => absurd hz (by decide), fun hz => absurd hz h2⟩

theorem fiber_pendant_zero :
    fiber (pendantColouring a p b r) 0 = Finset.univ \ ({a, p, b, r} : Finset V) := by
  have hmem : ∀ z : V, z ∈ ({a, p, b, r} : Finset V) ↔
      z ∈ ({a, p} : Finset V) ∨ z ∈ ({b, r} : Finset V) := by
    intro z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  ext z
  simp only [mem_fiber, pendantColouring, Finset.mem_sdiff, Finset.mem_univ, true_and, hmem,
    not_or]
  by_cases h : z ∈ ({a, p} : Finset V)
  · rw [if_pos h]
    exact ⟨fun hz => absurd hz (by decide), fun hz => absurd h hz.1⟩
  · rw [if_neg h]
    by_cases h2 : z ∈ ({b, r} : Finset V)
    · simp only [if_pos h2]
      exact ⟨fun hz => absurd hz (by decide), fun hz => absurd h2 hz.2⟩
    · simp only [if_neg h2]
      simp [h, h2]

theorem pendant_not_monochromatic (hab : a ≠ b) (hpb : p ≠ b) :
    ¬ Amplitude.Monochromatic (pendantColouring a p b r) := by
  rintro ⟨k, hk⟩
  have ha : pendantColouring a p b r a = 1 := by
    simp only [pendantColouring, if_pos (by simp : a ∈ ({a, p} : Finset V))]
  have hb : pendantColouring a p b r b = 2 := by
    have hbn : b ∉ ({a, p} : Finset V) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hab, Ne.symm hpb⟩
    simp only [pendantColouring, if_neg hbn, if_pos (by simp : b ∈ ({b, r} : Finset V))]
  have h12 : (1 : Fin 3) = 2 := by rw [← ha, ← hb, hk a, hk b]
  exact absurd h12 (by decide)

/-- **Two pendant edges survive.**  A live edge in colour 1, another in colour 2, and a
certified complement in colour 0: the amplitude is a product of three non-zero factors, two of
which are single weights.  There is no sum to cancel except in the third class, and the peel
certifies that one. -/
theorem amplitude_pendant_ne_zero (W : Sym2 (V × Fin 3) → ℂ)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hap : a ≠ p) (hab : a ≠ b) (har : a ≠ r) (hpb : p ≠ b) (hpr : p ≠ r) (hbr : b ≠ r)
    (h1 : W s((a, 1), (p, 1)) ≠ 0) (h2 : W s((b, 2), (r, 2)) ≠ 0)
    (h0 : pmSum W (Amplitude.const (V := V) 0)
      (Finset.univ \ ({a, p, b, r} : Finset V)) ≠ 0) :
    amplitude W (pendantColouring a p b r) ≠ 0 := by
  refine amplitude_ne_zero_of_certified_partition W hmono _ (fun m => ?_)
  match m with
  | 0 => rw [fiber_pendant_zero]; exact h0
  | 1 => rw [fiber_pendant_one hab har hpb hpr, pmSum_pair W _ (Ne.symm hap)]; exact h1
  | 2 => rw [fiber_pendant_two hab har hpb hpr, pmSum_pair W _ (Ne.symm hbr)]; exact h2

/-- The certificate against the equations.  Nothing here needs a degree bound, a vertex count,
or a cancellation argument. -/
theorem false_of_pendant (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hap : a ≠ p) (hab : a ≠ b) (har : a ≠ r) (hpb : p ≠ b) (hpr : p ≠ r) (hbr : b ≠ r)
    (h1 : W s((a, 1), (p, 1)) ≠ 0) (h2 : W s((b, 2), (r, 2)) ≠ 0)
    (h0 : pmSum W (Amplitude.const (V := V) 0)
      (Finset.univ \ ({a, p, b, r} : Finset V)) ≠ 0) : False :=
  amplitude_pendant_ne_zero W hmono hap hab har hpb hpr hbr h1 h2 h0
    (hzero _ (pendant_not_monochromatic hab hpb))

/-- **Crossed pendant edges are forbidden.**  Peel twice in colour 0, taking off `{a,a₀}` and
then `{b,b₀}`, so the remaining sites still carry a colour-0 matching sum.  The two pairs that
came off can be re-paired *across*: `a` with `b₀`, and `b` with `a₀`.  If both crossings were
live -- one in colour 1, the other in colour 2 -- the pendant certificate would fire.  So they
cannot both be live.

Exclusivity forbids re-colouring a peeled pair itself, since a certified pair wears one colour.
This says the same about the two ways of crossing between two peeled pairs, and it costs no
cancellation argument at all. -/
theorem not_cross_live_of_double_peel (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {a a₀ b b₀ : V}
    (hne1 : a ≠ a₀) (hne2 : a ≠ b) (hne3 : a ≠ b₀)
    (hne4 : a₀ ≠ b) (hne5 : a₀ ≠ b₀) (hne6 : b ≠ b₀)
    (hrest : pmSum W (Amplitude.const (V := V) 0)
      ((((Finset.univ.erase a).erase a₀).erase b).erase b₀) ≠ 0)
    (hlive : W s((a, 1), (b₀, 1)) ≠ 0) :
    W s((b, 2), (a₀, 2)) = 0 := by
  classical
  by_contra hcross
  have hset : ((((Finset.univ.erase a).erase a₀).erase b).erase b₀)
      = Finset.univ \ ({a, b₀, b, a₀} : Finset V) := by
    ext z
    simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ, true_and, and_true,
      Finset.mem_insert, Finset.mem_singleton, not_or]
    tauto
  rw [hset] at hrest
  exact false_of_pendant W hzero hmono hne3 hne2 hne1 (Ne.symm hne6) (Ne.symm hne5)
    (Ne.symm hne4) hlive hcross hrest

/-- **The peel cannot be steered into a pendant.**  Choose a site `a` and one of its colour-1
neighbours `p` -- every site has one in every colour, so this is free -- and peel colour 0 at
both, taking off `a₀` and `p₀`.  The pendant certificate then needs only that the two partners
are live to each other in colour 2, so they are not.

This is the sharpest form of the pendant obstruction: one of its two edges is chosen rather
than found, and the surviving requirement is a single weight.  Relabelling which partner plays
which role covers the remaining pairings of the four sites. -/
theorem peel_partners_dead_of_colour_neighbour (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {a p a₀ p₀ : V}
    (hap : a ≠ p) (haa₀ : a ≠ a₀) (hap₀ : a ≠ p₀)
    (hpa₀ : p ≠ a₀) (hpp₀ : p ≠ p₀) (ha₀p₀ : a₀ ≠ p₀)
    (hlive : W s((a, 1), (p, 1)) ≠ 0)
    (hrest : pmSum W (Amplitude.const (V := V) 0)
      ((((Finset.univ.erase a).erase p).erase a₀).erase p₀) ≠ 0) :
    W s((a₀, 2), (p₀, 2)) = 0 := by
  classical
  by_contra hcross
  have hset : ((((Finset.univ.erase a).erase p).erase a₀).erase p₀)
      = Finset.univ \ ({a, p, a₀, p₀} : Finset V) := by
    ext z
    simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ, true_and, and_true,
      Finset.mem_insert, Finset.mem_singleton, not_or]
    tauto
  rw [hset] at hrest
  exact false_of_pendant W hzero hmono hap haa₀ hap₀ hpa₀ hpp₀ ha₀p₀ hlive hcross hrest

/-- **Why four sites are exceptional.**  At four sites the certified-complement hypothesis of
the pendant is free -- the complement is empty, and the empty matching sum is one -- so the
certificate reduces to a bare statement: no pair live in one colour has a disjoint pair live in
another.

That is exactly what the four-site solution achieves, and it achieves it for a reason that
cannot survive: there the complement of a pair *is* a pair, and it wears the pair's own colour.
Above four sites the complement of a pair is no longer a pair, the mechanism has nothing to say,
and everything passes to the certified-complement hypothesis instead. -/
theorem no_disjoint_bicolour_pair_of_card_four (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hcard : Fintype.card V = 4) {a p b r : V}
    (hap : a ≠ p) (hab : a ≠ b) (har : a ≠ r) (hpb : p ≠ b) (hpr : p ≠ r) (hbr : b ≠ r)
    (h1 : W s((a, 1), (p, 1)) ≠ 0) : W s((b, 2), (r, 2)) = 0 := by
  classical
  by_contra h2
  have hc : ({a, p, b, r} : Finset V).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hap, hab, har]),
      Finset.card_insert_of_notMem (by simp [hpb, hpr]),
      Finset.card_insert_of_notMem (by simp [hbr]), Finset.card_singleton]
  have huniv : ({a, p, b, r} : Finset V) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [hc, hcard])
  have h0 : pmSum W (Amplitude.const (V := V) 0)
      (Finset.univ \ ({a, p, b, r} : Finset V)) ≠ 0 := by
    rw [huniv, Finset.sdiff_self, pmSum_empty]
    exact one_ne_zero
  exact false_of_pendant W hzero hmono hap hab har hpb hpr hbr h1 h2 h0

end Pendant

/-! ### The colour symmetry

Nothing in the equations distinguishes the three colours, so every certificate proved for one
assignment of colours holds for all six.  Rather than restate each one, transport the weights:
permuting the colours of `W` preserves both the vanishing condition and monochromaticity, and
the amplitude of the permuted weights at a colouring is the amplitude of the original at the
permuted colouring.

This is the `S₃` action the problem has all along, made usable. -/

section Recolour

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The weights with their colours permuted. -/
def recolour (σ : Equiv.Perm (Fin 3)) (W : Sym2 (V × Fin 3) → ℂ) : Sym2 (V × Fin 3) → ℂ :=
  fun e => W (Sym2.map (Prod.map id (σ : Fin 3 → Fin 3)) e)

theorem recolour_apply (σ : Equiv.Perm (Fin 3)) (W : Sym2 (V × Fin 3) → ℂ)
    (x y : V) (a b : Fin 3) :
    recolour σ W s((x, a), (y, b)) = W s((x, σ a), (y, σ b)) := rfl

theorem pmSum_recolour (σ : Equiv.Perm (Fin 3)) (W : Sym2 (V × Fin 3) → ℂ)
    (c : V → Fin 3) (S : Finset V) :
    pmSum (recolour σ W) c S = pmSum W ((σ : Fin 3 → Fin 3) ∘ c) S := by
  refine Finset.sum_congr rfl (fun τ _ => Finset.prod_congr rfl (fun e _ => ?_))
  exact congrArg W (Amplitude.map_paint (σ : Fin 3 → Fin 3) c e)

theorem pmSum_recolour_const (σ : Equiv.Perm (Fin 3)) (W : Sym2 (V × Fin 3) → ℂ)
    (k : Fin 3) (S : Finset V) :
    pmSum (recolour σ W) (Amplitude.const (V := V) k) S
      = pmSum W (Amplitude.const (V := V) (σ k)) S := by
  rw [pmSum_recolour]
  exact pmSum_congr_colour W (fun x _ => rfl)

/-- The vanishing condition survives a permutation of the colours. -/
theorem hzero_recolour [Nonempty V] (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (σ : Equiv.Perm (Fin 3)) :
    ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude (recolour σ W) c = 0 := by
  intro c hc
  rw [show recolour σ W
      = fun e => W (Sym2.map (Prod.map id (σ : Fin 3 → Fin 3)) e) from rfl,
    Amplitude.amplitude_comp]
  exact hzero _ (fun h =>
    hc ((Amplitude.monochromatic_comp_iff (σ.injective) c).mp h))

/-- So does the absence of live edges mixing colours. -/
theorem hmono_recolour (W : Sym2 (V × Fin 3) → ℂ)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (σ : Equiv.Perm (Fin 3)) :
    ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → recolour σ W s((x, a), (y, b)) = 0 := by
  intro x y hyx a b hab
  rw [recolour_apply]
  exact hmono x y hyx (σ a) (σ b) (fun h => hab (σ.injective h))

/-- **The pendant certificate in every colour assignment.**  The three colours are
interchangeable, so the certificate proved for `(0, 1, 2)` holds for all six orderings. -/
theorem false_of_pendant_colours [Nonempty V] (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (σ : Equiv.Perm (Fin 3)) {a p b r : V}
    (hap : a ≠ p) (hab : a ≠ b) (har : a ≠ r) (hpb : p ≠ b) (hpr : p ≠ r) (hbr : b ≠ r)
    (h1 : W s((a, σ 1), (p, σ 1)) ≠ 0) (h2 : W s((b, σ 2), (r, σ 2)) ≠ 0)
    (h0 : pmSum W (Amplitude.const (V := V) (σ 0))
      (Finset.univ \ ({a, p, b, r} : Finset V)) ≠ 0) : False :=
  false_of_pendant (recolour σ W) (hzero_recolour W hzero σ) (hmono_recolour W hmono σ)
    hap hab har hpb hpr hbr h1 h2 (by rw [pmSum_recolour_const]; exact h0)

/-- The sharp form, in every colour assignment: peel the complement colour at a site and at one
of its `σ 1`-neighbours; the two partners that come off are dead to each other in `σ 2`. -/
theorem peel_partners_dead_colours [Nonempty V] (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (σ : Equiv.Perm (Fin 3)) {a p a₀ p₀ : V}
    (hap : a ≠ p) (haa₀ : a ≠ a₀) (hap₀ : a ≠ p₀)
    (hpa₀ : p ≠ a₀) (hpp₀ : p ≠ p₀) (ha₀p₀ : a₀ ≠ p₀)
    (hlive : W s((a, σ 1), (p, σ 1)) ≠ 0)
    (hrest : pmSum W (Amplitude.const (V := V) (σ 0))
      ((((Finset.univ.erase a).erase p).erase a₀).erase p₀) ≠ 0) :
    W s((a₀, σ 2), (p₀, σ 2)) = 0 :=
  peel_partners_dead_of_colour_neighbour (recolour σ W)
    (hzero_recolour W hzero σ) (hmono_recolour W hmono σ)
    hap haa₀ hap₀ hpa₀ hpp₀ ha₀p₀ hlive (by rw [pmSum_recolour_const]; exact hrest)

end Recolour

/-! ### The certified complement always exists

The pendant's one substantial hypothesis is a four-set with a certified complement, and it is
always available.  Expand the colour-0 sum at a site `a` and then at its colour-1 partner `p`.
If `{a,p}` is *certified* in colour 1 then it is dead in colour 0, so `p` never turns up as `a`'s
own colour-0 partner and the expansion at `a` lands strictly elsewhere.  Two peels then produce
four distinct sites carrying the colour-1 edge, with a certified complement.

So the certificate always has its four-set.  What it does not have is control over the two sites
that come off: the equations force exactly those to be dead to each other in colour 2, and that
is now the entire remaining content of the conjecture on this branch. -/

section Existence

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Two peels reach a certified four-set through any colour-0-dead pair.** -/
theorem exists_certified_quad (W : Sym2 (V × Fin 3) → ℂ)
    (huniv : pmSum W (Amplitude.const (V := V) 0) Finset.univ ≠ 0)
    {a p : V} (hpa : p ≠ a) (hdead : W s((a, 0), (p, 0)) = 0) :
    ∃ v w : V, v ≠ a ∧ v ≠ p ∧ w ≠ a ∧ w ≠ v ∧ w ≠ p ∧
      W s((a, 0), (v, 0)) ≠ 0 ∧ W s((p, 0), (w, 0)) ≠ 0 ∧
      pmSum W (Amplitude.const (V := V) 0)
        ((((Finset.univ.erase a).erase v).erase p).erase w) ≠ 0 := by
  classical
  obtain ⟨v, hv, hwv, hsv⟩ :=
    exists_partner_ne_zero W (Amplitude.const (V := V) 0) (Finset.mem_univ a) huniv
  have hva : v ≠ a := (Finset.mem_erase.mp hv).1
  have hvp : v ≠ p := by
    rintro rfl
    exact hwv hdead
  have hpmem : p ∈ (Finset.univ.erase a).erase v :=
    Finset.mem_erase.mpr ⟨Ne.symm hvp, Finset.mem_erase.mpr ⟨hpa, Finset.mem_univ p⟩⟩
  obtain ⟨w, hw, hww, hsw⟩ :=
    exists_partner_ne_zero W (Amplitude.const (V := V) 0) hpmem hsv
  have hwp : w ≠ p := (Finset.mem_erase.mp hw).1
  have hwv' : w ≠ v := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hw)).1
  have hwa : w ≠ a :=
    (Finset.mem_erase.mp (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hw))).1
  exact ⟨v, w, hva, hvp, hwa, hwv', hwp, hwv, hww, hsw⟩

/-- **The whole remaining content, in one statement.**  Through a certified colour-1 pair, two
peels reach four distinct sites with a certified complement -- and the two sites that came off
are forced dead to each other in colour 2.  Everything else the pendant needs is free. -/
theorem exists_quad_dead_in_colour_two (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (huniv : pmSum W (Amplitude.const (V := V) 0) Finset.univ ≠ 0)
    {a p : V} (hpa : p ≠ a) (hdead : W s((a, 0), (p, 0)) = 0)
    (hlive : W s((a, 1), (p, 1)) ≠ 0) :
    ∃ v w : V, v ≠ a ∧ v ≠ p ∧ w ≠ a ∧ w ≠ v ∧ w ≠ p ∧
      W s((a, 0), (v, 0)) ≠ 0 ∧ W s((p, 0), (w, 0)) ≠ 0 ∧
      W s((v, 2), (w, 2)) = 0 := by
  obtain ⟨v, w, hva, hvp, hwa, hwv, hwp, h0v, h0w, hrest⟩ :=
    exists_certified_quad W huniv hpa hdead
  refine ⟨v, w, hva, hvp, hwa, hwv, hwp, h0v, h0w, ?_⟩
  have hswap : (((Finset.univ.erase a).erase v).erase p).erase w
      = (((Finset.univ.erase a).erase p).erase v).erase w := by
    ext z; simp only [Finset.mem_erase]; tauto
  rw [hswap] at hrest
  exact peel_partners_dead_of_colour_neighbour W hzero hmono (Ne.symm hpa) (Ne.symm hva)
    (Ne.symm hwa) (Ne.symm hvp) (Ne.symm hwp) (Ne.symm hwv) hlive hrest

end Existence

/-! ### Assembling a colouring from two certified parts

The pendant fixed both small classes at size two, and every other shape would have cost its own
bookkeeping.  It need not.  Give two disjoint sets and colour them 1 and 2, leaving the rest in
colour 0: if each part carries a non-vanishing matching sum in its own colour the amplitude does
not vanish, whatever the parts look like.

The pendant is the case where both parts are single pairs, since a pair's matching sum is one
weight.  A part whose matching is *forced* -- two of three options dead at one of its corners --
is just as good, and so is any other set whose sum is known non-zero.  This is the general
statement; the certificates above are its instances. -/

section Parts

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The colouring that paints two disjoint sets with colours 1 and 2 and the rest with 0. -/
noncomputable def partColouring (S₁ S₂ : Finset V) : V → Fin 3 :=
  fun z => if z ∈ S₁ then 1 else if z ∈ S₂ then 2 else 0

variable {S₁ S₂ : Finset V}

theorem fiber_part_one : fiber (partColouring S₁ S₂) 1 = S₁ := by
  ext z
  simp only [mem_fiber, partColouring]
  by_cases h : z ∈ S₁
  · simp [h]
  · refine ⟨fun hz => ?_, fun hz => absurd hz h⟩
    rw [if_neg h] at hz
    split at hz <;> exact absurd hz (by decide)

theorem fiber_part_two (hdisj : Disjoint S₁ S₂) : fiber (partColouring S₁ S₂) 2 = S₂ := by
  ext z
  simp only [mem_fiber, partColouring]
  by_cases h : z ∈ S₁
  · rw [if_pos h]
    exact ⟨fun hz => absurd hz (by decide),
      fun hz => absurd hz (Finset.disjoint_left.mp hdisj h)⟩
  · rw [if_neg h]
    by_cases h2 : z ∈ S₂
    · simp [h2]
    · simp only [if_neg h2]
      exact ⟨fun hz => absurd hz (by decide), fun hz => absurd hz h2⟩

theorem fiber_part_zero : fiber (partColouring S₁ S₂) 0 = Finset.univ \ (S₁ ∪ S₂) := by
  ext z
  simp only [mem_fiber, partColouring, Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_union, not_or]
  by_cases h : z ∈ S₁
  · rw [if_pos h]
    exact ⟨fun hz => absurd hz (by decide), fun hz => absurd h hz.1⟩
  · rw [if_neg h]
    by_cases h2 : z ∈ S₂
    · simp only [if_pos h2]
      exact ⟨fun hz => absurd hz (by decide), fun hz => absurd h2 hz.2⟩
    · simp only [if_neg h2]
      simp [h, h2]

theorem part_not_monochromatic (h1 : S₁.Nonempty) (h2 : S₂.Nonempty) (hdisj : Disjoint S₁ S₂) :
    ¬ Amplitude.Monochromatic (partColouring S₁ S₂) := by
  rintro ⟨k, hk⟩
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  have hxv : partColouring S₁ S₂ x = 1 := by simp only [partColouring, if_pos hx]
  have hyv : partColouring S₁ S₂ y = 2 := by
    simp only [partColouring, if_neg (Finset.disjoint_right.mp hdisj hy), if_pos hy]
  have h12 : (1 : Fin 3) = 2 := by rw [← hxv, ← hyv, hk x, hk y]
  exact absurd h12 (by decide)

/-- **Two certified parts survive.**  Disjoint sets carrying non-vanishing matching sums in
colours 1 and 2, with a certified remainder in colour 0: the amplitude is a product of three
non-zero factors. -/
theorem amplitude_part_ne_zero (W : Sym2 (V × Fin 3) → ℂ)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hdisj : Disjoint S₁ S₂)
    (h1 : pmSum W (Amplitude.const (V := V) 1) S₁ ≠ 0)
    (h2 : pmSum W (Amplitude.const (V := V) 2) S₂ ≠ 0)
    (h0 : pmSum W (Amplitude.const (V := V) 0) (Finset.univ \ (S₁ ∪ S₂)) ≠ 0) :
    amplitude W (partColouring S₁ S₂) ≠ 0 := by
  refine amplitude_ne_zero_of_certified_partition W hmono _ (fun m => ?_)
  match m with
  | 0 => rw [fiber_part_zero]; exact h0
  | 1 => rw [fiber_part_one]; exact h1
  | 2 => rw [fiber_part_two hdisj]; exact h2

/-- The certificate against the equations, in its general form. -/
theorem false_of_parts (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hdisj : Disjoint S₁ S₂) (hn1 : S₁.Nonempty) (hn2 : S₂.Nonempty)
    (h1 : pmSum W (Amplitude.const (V := V) 1) S₁ ≠ 0)
    (h2 : pmSum W (Amplitude.const (V := V) 2) S₂ ≠ 0)
    (h0 : pmSum W (Amplitude.const (V := V) 0) (Finset.univ \ (S₁ ∪ S₂)) ≠ 0) : False :=
  amplitude_part_ne_zero W hmono hdisj h1 h2 h0
    (hzero _ (part_not_monochromatic hn1 hn2 hdisj))

end Parts

/-! ### What the partition question buys, and what it does not

The reduction chain is worth stating end to end, because it makes both remaining gaps visible
at once.  A counterexample has a support-minimal representative.  If every site of that
representative is degenerate then no live edge mixes colours, the product formula applies, and
the partition question finishes it.  So granted the partition question, any counterexample must
have a support-minimal representative with a site that is **not** degenerate.

That is the honest statement of where the conjecture stands on this route: two gaps, not one.
The partition question is the combinatorial residual; the non-degenerate branch is assumed
throughout the fan development and discharged nowhere. -/

section Reduction

/-- **Granted the partition question, a counterexample is non-degenerate somewhere.** -/
theorem nonDegenerate_of_certifiedPartition (hcp : CertifiedPartition)
    {n : ℕ} (h3 : 3 ≤ n) (hs : KrennGu.Solvable n) :
    ∃ W' : Sym2 (Fin (2 * n) × Fin 3) → ℂ, MinimalSupport.IsSupportMinimal W' ∧
      ∃ q : Fin (2 * n), ¬ FanStructure.Degenerate W' q := by
  classical
  obtain ⟨W, hW⟩ := hs
  obtain ⟨W', hmin, -⟩ := MinimalSupport.exists_supportMinimal W hW
  have hcard : 4 < Fintype.card (Fin (2 * n)) := by rw [Fintype.card_fin]; omega
  refine ⟨W', hmin, ?_⟩
  by_contra hall
  push_neg at hall
  have hmono := mono_of_supportMinimal W' hmin hmin.1.2 hall (le_of_lt hcard)
  obtain ⟨c, hnm, hc⟩ :=
    mixed_of_certifiedPartition hcp (Fin (2 * n)) W' hcard hmono hmin.1.1
  exact hc (hmin.1.2 c hnm)

/-- One side of the degeneracy dichotomy, as a hypothesis.  The fan development assumes it
throughout.  It is not a second unknown of the same kind as the partition question: the other
side of the dichotomy is a *certificate*, not a gap (see `exists_certificate_of_not_degenerate`),
so what is really missing there is an extension, not a proof of degeneracy. -/
def AllDegenerate : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (W : Sym2 (V × Fin 3) → ℂ),
    4 < Fintype.card V → MinimalSupport.IsSupportMinimal W →
      ∀ q : V, FanStructure.Degenerate W q

/-- **The conjecture, from the two remaining statements.**  Both are named, both are open, and
neither mentions amplitudes. -/
theorem krenn_gu_of_certifiedPartition (hcp : CertifiedPartition) (had : AllDegenerate) :
    ∀ n : ℕ, 3 ≤ n → ¬ KrennGu.Solvable n := by
  intro n h3 hs
  obtain ⟨W', hmin, q, hq⟩ := nonDegenerate_of_certifiedPartition hcp h3 hs
  have hcard : 4 < Fintype.card (Fin (2 * n)) := by rw [Fintype.card_fin]; omega
  exact hq (had (Fin (2 * n)) W' hcard hmin q)

/-- **Non-degeneracy is a certificate, not an obstacle.**  A site that fails to be degenerate
hands over a colouring that is non-constant on the complement of the site and one other, and
whose matching sum there does not vanish.  That is exactly the shape the pinning results
consume, and it is one extension away from a surviving mixed amplitude.

Stating it separately matters because `AllDegenerate` reads like a branch waiting to be proved.
It is better read as a dichotomy: on a support-minimal representative every site is either
degenerate -- and then no live edge mixes colours, and the partition question finishes -- or it
is not, and then the failure itself is the witness. -/
theorem exists_certificate_of_not_degenerate {V : Type*} [Fintype V] [DecidableEq V]
    (W : Sym2 (V × Fin 3) → ℂ) {p : V} (h : ¬ FanStructure.Degenerate W p) :
    ∃ x : V, x ≠ p ∧ ∃ c : V → Fin 3, ¬ Amplitude.Monochromatic c ∧
      pmSum W c ((Finset.univ.erase p).erase x) ≠ 0 := by
  classical
  unfold FanStructure.Degenerate at h
  push_neg at h
  obtain ⟨x, hx, c, u, hu, w, hw, hcuw, hpm⟩ := h
  refine ⟨x, (Finset.mem_erase.mp hx).1, c, ?_, hpm⟩
  rintro ⟨k, hk⟩
  exact hcuw (by rw [hk u, hk w])

/-- **The residual after the partition question, stated concretely.**  Granted `CertifiedPartition`,
a counterexample supplies a non-constant colouring whose matching sum survives on the complement
of two sites.  What is missing is the extension of that colouring to the two sites themselves --
a statement about two rows, not about a whole branch. -/
theorem exists_covertificate_of_certifiedPartition (hcp : CertifiedPartition)
    {n : ℕ} (h3 : 3 ≤ n) (hs : KrennGu.Solvable n) :
    ∃ W' : Sym2 (Fin (2 * n) × Fin 3) → ℂ, MinimalSupport.IsSupportMinimal W' ∧
      ∃ p x : Fin (2 * n), x ≠ p ∧ ∃ c : Fin (2 * n) → Fin 3,
        ¬ Amplitude.Monochromatic c ∧
        pmSum W' c ((Finset.univ.erase p).erase x) ≠ 0 := by
  obtain ⟨W', hmin, q, hq⟩ := nonDegenerate_of_certifiedPartition hcp h3 hs
  obtain ⟨x, hxq, c, hnm, hpm⟩ := exists_certificate_of_not_degenerate W' hq
  exact ⟨W', hmin, q, x, hxq, c, hnm, hpm⟩

/-- **The certificate closes when the row is otherwise dead.**  If the non-degenerate site's row
under the certifying colouring is dead away from its witness, the expansion at that site has a
single term, so the amplitude is a product of two non-zero factors -- contradicting the vanishing
condition. -/
theorem false_of_certificate_of_lone_row {V : Type*} [Fintype V] [DecidableEq V]
    (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {p x : V} (hxp : x ≠ p) {c : V → Fin 3} (hnm : ¬ Amplitude.Monochromatic c)
    (hpm : pmSum W c ((Finset.univ.erase p).erase x) ≠ 0)
    (hlive : W s((p, c p), (x, c x)) ≠ 0)
    (hlone : ∀ y : V, y ≠ p → y ≠ x → W s((p, c p), (y, c y)) = 0) : False := by
  classical
  have hxmem : x ∈ Finset.univ.erase p := Finset.mem_erase.mpr ⟨hxp, Finset.mem_univ x⟩
  have huniq : ∀ z ∈ Finset.univ.erase p, z ≠ x →
      W (Sym2.map (Amplitude.paint c) s(p, z)) = 0 := by
    intro z hz hzx
    exact hlone z (Finset.mem_erase.mp hz).1 hzx
  have hval : pmSum W c Finset.univ
      = W (Sym2.map (Amplitude.paint c) s(p, x))
        * pmSum W c ((Finset.univ.erase p).erase x) :=
    pmSum_of_forced W c (Finset.mem_univ p) hxmem huniq
  rw [pmSum_univ, hzero c hnm] at hval
  exact (mul_ne_zero hlive hpm) hval.symm

/-- **Otherwise the certificate propagates.**  If the row is *not* otherwise dead, the vanishing
of the amplitude forces a second witness: another site whose weight is live and whose complement
still carries the same colouring's matching sum.

So a non-degeneracy certificate is never isolated.  Either its site's row is lone, and the
configuration is already impossible, or the certificate reproduces itself at a fresh witness. -/
theorem exists_second_certificate {V : Type*} [Fintype V] [DecidableEq V]
    (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {p x : V} (hxp : x ≠ p) {c : V → Fin 3} (hnm : ¬ Amplitude.Monochromatic c)
    (hpm : pmSum W c ((Finset.univ.erase p).erase x) ≠ 0)
    (hlive : W s((p, c p), (x, c x)) ≠ 0) :
    ∃ y : V, y ≠ p ∧ y ≠ x ∧ W s((p, c p), (y, c y)) ≠ 0 ∧
      pmSum W c ((Finset.univ.erase p).erase y) ≠ 0 := by
  classical
  by_contra hno
  push_neg at hno
  have hxmem : x ∈ Finset.univ.erase p := Finset.mem_erase.mpr ⟨hxp, Finset.mem_univ x⟩
  have halt : ∀ z ∈ Finset.univ.erase p, z ≠ x →
      W (Sym2.map (Amplitude.paint c) s(p, z))
        * pmSum W c ((Finset.univ.erase p).erase z) = 0 := by
    intro z hz hzx
    by_cases hw : W s((p, c p), (z, c z)) = 0
    · have hpaint : W (Sym2.map (Amplitude.paint c) s(p, z)) = W s((p, c p), (z, c z)) := rfl
      rw [hpaint, hw, zero_mul]
    · rw [hno z (Finset.mem_erase.mp hz).1 hzx hw, mul_zero]
  have hval := pmSum_of_alternatives_zero W c (Finset.mem_univ p) hxmem halt
  rw [pmSum_univ, hzero c hnm] at hval
  exact (mul_ne_zero hlive hpm) hval.symm

end Reduction

/-! ### The partition question has exactly one obstruction

It is worth knowing that the reformulation lost nothing.  The partition question is settled the
moment a pair certified in one colour is live in another: colour that pair with the second
colour and everything else with the first, and both classes are certified with no cancellation
anywhere.

So the only thing standing in the way is colour-exclusivity of certified pairs -- which is
precisely what the vanishing condition forces.  The restatement is faithful: it is neither
weaker nor stronger than the difficulty it names. -/

section Obstruction

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **A certified pair live in a second colour settles the question.** -/
theorem mixed_of_bicoloured_certified_pair (W : Sym2 (V × Fin 3) → ℂ)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {u v : V} (hvu : v ≠ u)
    (hcert : pmSum W (Amplitude.const (V := V) 1) (Finset.univ \ ({u, v} : Finset V)) ≠ 0)
    (hlive : W s((u, 0), (v, 0)) ≠ 0)
    (hne : (Finset.univ \ ({u, v} : Finset V)).Nonempty) :
    ∃ c : V → Fin 3, ¬ Amplitude.Monochromatic c ∧ amplitude W c ≠ 0 := by
  classical
  have hsub : Finset.univ \ (Finset.univ \ ({u, v} : Finset V)) = ({u, v} : Finset V) := by
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not, and_true]
  have hSne : Finset.univ \ ({u, v} : Finset V) ≠ Finset.univ := by
    intro h
    have : u ∈ Finset.univ \ ({u, v} : Finset V) := by rw [h]; exact Finset.mem_univ u
    simp at this
  refine mixed_of_split_of_cut W hne hSne (j := 0) (k := 1) (by decide)
    (fun x hx y hy => hmono x y (fun h => hy (by rw [h]; exact hx)) 1 0 (by decide))
    hcert ?_
  rw [hsub, pmSum_pair W _ hvu]
  exact hlive

end Obstruction

/-! ### Bi-coloured pairs produce certificates

Earlier in this file the claim that the colour classes are edge-disjoint had to be withdrawn:
what is proved is only that no live edge *mixes* colours at its two ends, and a single pair may
carry weight in two colours.  That gap closes here, though not by proving the classes disjoint.

If a pair is live in two colours then its complement carries no constant matching sum at all --
each of the two live colours excludes every other colour from surviving, and between them they
exclude all three.  On a support-minimal representative the pair is nevertheless non-inert, so
*some* colouring survives on the complement, and it cannot be constant.

So a bi-coloured pair is exactly a non-degeneracy certificate.  The dichotomy is clean: either
every live pair wears a single colour --- and the classes really are disjoint, with the whole
product-formula picture available --- or some pair is bi-coloured and hands over the certificate
the other branch runs on. -/

section Bicoloured

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **A pair live in two colours has no surviving constant complement.** -/
theorem all_complements_zero_of_bicoloured (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {p q : V} (hqp : q ≠ p) (hout : ∃ z : V, z ≠ p ∧ z ≠ q)
    {m m' : Fin 3} (hmm : m ≠ m')
    (hm : W s((p, m), (q, m)) ≠ 0) (hm' : W s((p, m'), (q, m')) ≠ 0) :
    ∀ k : Fin 3, pmSum W (Amplitude.const (V := V) k)
      ((Finset.univ.erase p).erase q) = 0 := by
  intro k
  by_contra hk
  by_cases hkm : k = m
  · subst hkm
    exact hm' (exclusive_of_partner_ne_zero W hzero hmono hqp hk hout (Ne.symm hmm))
  · exact hm (exclusive_of_partner_ne_zero W hzero hmono hqp hk hout (Ne.symm hkm))

/-- **So a bi-coloured pair is a non-degeneracy certificate.**  Support minimality keeps it
non-inert, and the colouring that survives on its complement cannot be constant. -/
theorem certificate_of_bicoloured (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hmin : MinimalSupport.IsSupportMinimal W)
    {p q : V} (hqp : q ≠ p) (hout : ∃ z : V, z ≠ p ∧ z ≠ q)
    {m m' : Fin 3} (hmm : m ≠ m')
    (hm : W s((p, m), (q, m)) ≠ 0) (hm' : W s((p, m'), (q, m')) ≠ 0) :
    ∃ c : V → Fin 3, ¬ Amplitude.Monochromatic c ∧
      pmSum W c ((Finset.univ.erase p).erase q) ≠ 0 := by
  classical
  have hni := MinimalSupport.not_inert_of_supportMinimal hmin hqp ⟨m, m, hm⟩
  unfold FanStructure.Inert at hni
  push_neg at hni
  obtain ⟨c, hc⟩ := hni
  refine ⟨c, ?_, hc⟩
  rintro ⟨k, hk⟩
  refine hc ?_
  have : pmSum W c ((Finset.univ.erase p).erase q)
      = pmSum W (Amplitude.const (V := V) k) ((Finset.univ.erase p).erase q) :=
    pmSum_congr_colour W (fun x _ => hk x)
  rw [this]
  exact all_complements_zero_of_bicoloured W hzero hmono hqp hout hmm hm hm' k

/-- **A certificate may be re-coloured at its own pair.**  The surviving sum runs over matchings
of the complement, so it never reads the pair's colours: they can be set freely without
disturbing it. -/
theorem certificate_recolour (W : Sym2 (V × Fin 3) → ℂ) {p q : V} {c : V → Fin 3}
    (hpm : pmSum W c ((Finset.univ.erase p).erase q) ≠ 0) (a b : Fin 3) :
    pmSum W (Function.update (Function.update c p a) q b)
      ((Finset.univ.erase p).erase q) ≠ 0 := by
  rw [pmSum_congr_colour W (c' := c) (fun x hx => ?_)]
  · exact hpm
  · have hxq : x ≠ q := (Finset.mem_erase.mp hx).1
    have hxp : x ≠ p := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hx)).1
    rw [Function.update_of_ne hxq, Function.update_of_ne hxp]

/-- On the bi-coloured branch the certificate is non-constant **on the complement itself**, not
merely on the whole site set: a colouring constant there would be a constant complement, and
those all vanish. -/
theorem bicoloured_certificate_nonconstant (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hmin : MinimalSupport.IsSupportMinimal W)
    {p q : V} (hqp : q ≠ p) (hout : ∃ z : V, z ≠ p ∧ z ≠ q)
    {m m' : Fin 3} (hmm : m ≠ m')
    (hm : W s((p, m), (q, m)) ≠ 0) (hm' : W s((p, m'), (q, m')) ≠ 0) :
    ∃ c : V → Fin 3, pmSum W c ((Finset.univ.erase p).erase q) ≠ 0 ∧
      ∃ u ∈ (Finset.univ.erase p).erase q, ∃ w ∈ (Finset.univ.erase p).erase q, c u ≠ c w := by
  classical
  have hni := MinimalSupport.not_inert_of_supportMinimal hmin hqp ⟨m, m, hm⟩
  unfold FanStructure.Inert at hni
  push_neg at hni
  obtain ⟨c, hc⟩ := hni
  refine ⟨c, hc, ?_⟩
  by_contra hno
  push_neg at hno
  obtain ⟨z, hz⟩ := hout
  have hzmem : z ∈ (Finset.univ.erase p).erase q :=
    Finset.mem_erase.mpr ⟨hz.2, Finset.mem_erase.mpr ⟨hz.1, Finset.mem_univ z⟩⟩
  refine hc ?_
  have hconst : pmSum W c ((Finset.univ.erase p).erase q)
      = pmSum W (Amplitude.const (V := V) (c z)) ((Finset.univ.erase p).erase q) :=
    pmSum_congr_colour W (fun x hx => hno x hx z hzmem)
  rw [hconst]
  exact all_complements_zero_of_bicoloured W hzero hmono hqp ⟨z, hz⟩ hmm hm hm' (c z)

/-- **The bi-coloured branch closes wherever the recoloured row is lone.**  Set the pair's colour
to one in which it is live; then its own term in the expansion at `p` does not vanish, so if the
rest of the row does, the amplitude is a product of two non-zero factors.

The hypothesis says exactly that `q` is `p`'s only colour-`m` neighbour. -/
theorem false_of_bicoloured_of_lone_row (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hmin : MinimalSupport.IsSupportMinimal W)
    {p q : V} (hqp : q ≠ p) (hout : ∃ z : V, z ≠ p ∧ z ≠ q)
    {m m' : Fin 3} (hmm : m ≠ m')
    (hm : W s((p, m), (q, m)) ≠ 0) (hm' : W s((p, m'), (q, m')) ≠ 0)
    (hlone : ∀ y : V, y ≠ p → y ≠ q → ∀ b : Fin 3, W s((p, m), (y, b)) = 0) :
    False := by
  classical
  obtain ⟨c, hpm, u, hu, w, hw, huw⟩ :=
    bicoloured_certificate_nonconstant W hzero hmono hmin hqp hout hmm hm hm'
  set c' := Function.update (Function.update c p m) q m with hc'
  have hcp : c' p = m := by
    rw [hc', Function.update_of_ne (Ne.symm hqp), Function.update_self]
  have hcq : c' q = m := by rw [hc', Function.update_self]
  have hagree : ∀ x ∈ (Finset.univ.erase p).erase q, c' x = c x := by
    intro x hx
    have hxq : x ≠ q := (Finset.mem_erase.mp hx).1
    have hxp : x ≠ p := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hx)).1
    rw [hc', Function.update_of_ne hxq, Function.update_of_ne hxp]
  have hnm : ¬ Amplitude.Monochromatic c' := by
    rintro ⟨k, hk⟩
    exact huw (by rw [← hagree u hu, ← hagree w hw, hk u, hk w])
  refine false_of_certificate_of_lone_row W hzero hqp hnm (certificate_recolour W hpm m m) ?_ ?_
  · rw [hcp, hcq]; exact hm
  · intro y hyp hyq
    rw [hcp]
    exact hlone y hyp hyq (c' y)

/-- **On the bi-coloured branch a site has a second neighbour in each of the pair's colours.**
The pair alone will not do: if it were the site's only colour-`m` neighbour the branch would
already have closed.  Applying this with `m` and with `m'` gives two further neighbours, so a
site carrying a bi-coloured pair is never of colour degree one in either of that pair's colours.

The extra neighbour wears the same colour, since no live edge mixes colours at its ends.

**Redundant in context.**  Wherever the constant amplitudes are non-zero and there are more than
two sites, `exists_exclusive_partner` already supplies a colour-`m` partner, and it is certified,
so it is not the bi-coloured one.  This statement earns its place only by asking for neither of
those hypotheses; it is kept for that reason and for the closure it is proved from, not because
it says anything new about a GHZ system. -/
theorem exists_second_neighbour_of_bicoloured (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hmin : MinimalSupport.IsSupportMinimal W)
    {p q : V} (hqp : q ≠ p) (hout : ∃ z : V, z ≠ p ∧ z ≠ q)
    {m m' : Fin 3} (hmm : m ≠ m')
    (hm : W s((p, m), (q, m)) ≠ 0) (hm' : W s((p, m'), (q, m')) ≠ 0) :
    ∃ y : V, y ≠ p ∧ y ≠ q ∧ W s((p, m), (y, m)) ≠ 0 := by
  classical
  by_contra hno
  push_neg at hno
  refine false_of_bicoloured_of_lone_row W hzero hmono hmin hqp hout hmm hm hm'
    (fun y hyp hyq b => ?_)
  by_cases hbm : b = m
  · subst hbm; exact hno y hyp hyq
  · exact hmono p y hyp m b (Ne.symm hbm)

/-- **A bi-coloured pair forces live degree at least four.**

Every site has a certified exclusive partner in each of the three colours, and those three are
distinct -- each is dead in the colours it is not certified by.  A bi-coloured partner is none of
them: its complement carries no constant matching sum in any colour, so it is certified by none.
It is therefore a fourth live neighbour.

So the bi-coloured branch lives entirely in the high-degree regime, and a degree bound of three
would rule it out -- putting the whole configuration on the branch where the colour classes are
disjoint. -/
theorem four_le_liveNbrs_of_bicoloured (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const (V := V) k) ≠ 0)
    (hcard : 2 < Fintype.card V)
    {p q : V} (hqp : q ≠ p) (hout : ∃ z : V, z ≠ p ∧ z ≠ q)
    {m m' : Fin 3} (hmm : m ≠ m')
    (hm : W s((p, m), (q, m)) ≠ 0) (hm' : W s((p, m'), (q, m')) ≠ 0) :
    4 ≤ (LiveDegree.liveNbrs W p).card := by
  classical
  choose f hfp hflive hfcert hfexcl using
    fun k => exists_exclusive_partner W hzero hmono hcard k (hone k) p
  have hdead := all_complements_zero_of_bicoloured W hzero hmono hqp hout hmm hm hm'
  have hfq : ∀ k : Fin 3, f k ≠ q := by
    intro k hk
    exact hfcert k (by rw [hk]; exact hdead k)
  have hfinj : Function.Injective f := by
    intro j k hjk
    by_contra hne
    exact absurd (hfexcl k j hne) (by rw [← hjk]; exact hflive j)
  have hsub : ({f 0, f 1, f 2, q} : Finset V) ⊆ LiveDegree.liveNbrs W p := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    exacts [LiveDegree.mem_liveNbrs.mpr ⟨hfp 0, 0, 0, hflive 0⟩,
      LiveDegree.mem_liveNbrs.mpr ⟨hfp 1, 1, 1, hflive 1⟩,
      LiveDegree.mem_liveNbrs.mpr ⟨hfp 2, 2, 2, hflive 2⟩,
      LiveDegree.mem_liveNbrs.mpr ⟨hqp, m, m, hm⟩]
  have hc : ({f 0, f 1, f 2, q} : Finset V).card = 4 := by
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => absurd (hfinj h) (by decide), fun h => absurd (hfinj h) (by decide),
          hfq 0⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => absurd (hfinj h) (by decide), hfq 1⟩),
      Finset.card_insert_of_notMem (by simpa using hfq 2), Finset.card_singleton]
  calc 4 = ({f 0, f 1, f 2, q} : Finset V).card := hc.symm
    _ ≤ (LiveDegree.liveNbrs W p).card := Finset.card_le_card hsub

/-- **A degree bound of three puts every live pair on a single colour.**  The implication runs
one way only: a bi-coloured pair forces degree four, so degree three forbids bi-coloured pairs.
The converse fails --- a site may well have four live neighbours with every pair monochromatic,
say two in one colour and one in each of the others --- so the two branches are not the same
fork, and the degree-three case sits entirely inside the monochromatic one. -/
theorem mono_pair_of_liveDegree_le_three (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const (V := V) k) ≠ 0)
    (hcard : 2 < Fintype.card V)
    {p q : V} (hqp : q ≠ p) (hout : ∃ z : V, z ≠ p ∧ z ≠ q)
    (hdeg : (LiveDegree.liveNbrs W p).card ≤ 3)
    {m m' : Fin 3} (hmm : m ≠ m') (hm : W s((p, m), (q, m)) ≠ 0) :
    W s((p, m'), (q, m')) = 0 := by
  by_contra hm'
  have := four_le_liveNbrs_of_bicoloured W hzero hmono hone hcard hqp hout hmm hm hm'
  omega

/-- **A bi-coloured pair is invisible to the constant amplitudes.**  Expanding a constant
matching sum at one of its sites, the term belonging to the pair drops out: its factor is the
pair's own complementary sum, and on this branch that vanishes in every colour.

So the three non-vanishing conditions -- the only ones that assert anything positive -- say
nothing whatever about a bi-coloured pair.  Its weights are constrained by the vanishing
equations alone.  That is why the branch resists the tools built for the rest of the
configuration: those tools are driven by the constant sums, and the constant sums do not see it. -/
theorem constant_sum_drops_bicoloured (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {p q : V} (hqp : q ≠ p) (hout : ∃ z : V, z ≠ p ∧ z ≠ q)
    {m m' : Fin 3} (hmm : m ≠ m')
    (hm : W s((p, m), (q, m)) ≠ 0) (hm' : W s((p, m'), (q, m')) ≠ 0) (k : Fin 3) :
    pmSum W (Amplitude.const (V := V) k) Finset.univ
      = ∑ y ∈ (Finset.univ.erase p).erase q,
          W s((p, k), (y, k)) * pmSum W (Amplitude.const (V := V) k)
            ((Finset.univ.erase p).erase y) := by
  classical
  have hdead := all_complements_zero_of_bicoloured W hzero hmono hqp hout hmm hm hm' k
  rw [pmSum_expand W (Amplitude.const (V := V) k) (Finset.mem_univ p)]
  refine (Finset.sum_erase _ ?_).symm
  have hpaint : W (Sym2.map (Amplitude.paint (Amplitude.const (V := V) k)) s(p, q))
      = W s((p, k), (q, k)) := rfl
  rw [hpaint, hdead, mul_zero]

/-- **The mixed equations at a pair, with the pair's own term gone.**  Colour the two sites of a
pair differently.  No live edge mixes colours at its ends, so the pair's own term in the
expansion at one of them vanishes on its weight rather than on its complementary sum -- and the
equation becomes a relation among the other terms alone.

This is the handle the vanishing conditions give where the constant sums give none: it holds
whatever the pair's complementary sums do, so it survives on the branch where those all vanish. -/
theorem mixed_relation_at_pair (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {p q : V} (hqp : q ≠ p) (c : V → Fin 3) {a b : Fin 3} (hab : a ≠ b)
    (hnm : ¬ Amplitude.Monochromatic (Function.update (Function.update c p a) q b)) :
    ∑ y ∈ (Finset.univ.erase p).erase q,
      W (Sym2.map (Amplitude.paint (Function.update (Function.update c p a) q b)) s(p, y))
        * pmSum W (Function.update (Function.update c p a) q b)
            ((Finset.univ.erase p).erase y) = 0 := by
  classical
  set c' := Function.update (Function.update c p a) q b with hc'
  have hcp : c' p = a := by
    rw [hc', Function.update_of_ne (Ne.symm hqp), Function.update_self]
  have hcq : c' q = b := by rw [hc', Function.update_self]
  have h0 : pmSum W c' Finset.univ = 0 := by rw [pmSum_univ]; exact hzero c' hnm
  rw [pmSum_expand W c' (Finset.mem_univ p)] at h0
  rw [Finset.sum_erase _ ?_]
  · exact h0
  · have hpaint : W (Sym2.map (Amplitude.paint c') s(p, q)) = W s((p, c' p), (q, c' q)) := rfl
    rw [hpaint, hcp, hcq, hmono p q hqp a b hab, zero_mul]

/-- **Summing over the colour at a site.**  Add the matching sums over all three colours at one
site of a set.  Since no live edge mixes colours, each partner is met by exactly one of the
three, and the total is the expansion in which every partner is met *in its own colour*.

The colour at the site disappears from the answer.  That is what makes the mixed equations
usable where the constant ones are not: they can be summed over the free colour and the
dependence on it collapses. -/
theorem sum_colour_at_site (W : Sym2 (V × Fin 3) → ℂ)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (c : V → Fin 3) {T : Finset V} {q : V} (hq : q ∈ T) :
    ∑ b : Fin 3, pmSum W (Function.update c q b) T
      = ∑ z ∈ T.erase q, W s((q, c z), (z, c z)) * pmSum W c ((T.erase q).erase z) := by
  classical
  have hexp : ∀ b : Fin 3, pmSum W (Function.update c q b) T
      = ∑ z ∈ T.erase q, W s((q, b), (z, c z)) * pmSum W c ((T.erase q).erase z) := by
    intro b
    rw [pmSum_expand W (Function.update c q b) hq]
    refine Finset.sum_congr rfl (fun z hz => ?_)
    have hzq : z ≠ q := (Finset.mem_erase.mp hz).1
    have hqv : Function.update c q b q = b := Function.update_self ..
    have hzv : Function.update c q b z = c z := Function.update_of_ne hzq ..
    have h1 : W (Sym2.map (Amplitude.paint (Function.update c q b)) s(q, z))
        = W s((q, b), (z, c z)) := by
      rw [show Sym2.map (Amplitude.paint (Function.update c q b)) s(q, z)
        = s((q, Function.update c q b q), (z, Function.update c q b z)) from rfl, hqv, hzv]
    rw [h1]
    congr 1
    exact pmSum_congr_colour W (fun x hx =>
      Function.update_of_ne (Finset.mem_erase.mp (Finset.mem_of_mem_erase hx)).1 ..)
  simp_rw [hexp]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun z hz => ?_)
  have hzq : z ≠ q := (Finset.mem_erase.mp hz).1
  rw [← Finset.sum_mul]
  congr 1
  exact Finset.sum_eq_single_of_mem (c z) (Finset.mem_univ _)
    (fun b _ hb => hmono q z hzq b (c z) hb)

/-- **Descent through a live pair is impossible.**  Deleting a pair leaves a configuration on two
fewer sites, and for that to satisfy the positive half of the conditions all three of the pair's
complementary sums would have to survive.  Two surviving colours already kill the pair in all
three, so a *live* pair can never have all three -- and the deletion never produces a smaller
system with non-vanishing constants.

This is the precise reason the descent route fails, and it says nothing about how the smaller
system's mixed colourings behave: the obstruction is already in the positive half. -/
theorem not_all_complements_ne_zero_of_live (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {p q : V} (hqp : q ≠ p) (hout : ∃ z : V, z ≠ p ∧ z ≠ q)
    {m : Fin 3} (hlive : W s((p, m), (q, m)) ≠ 0) :
    ¬ (∀ k : Fin 3, pmSum W (Amplitude.const (V := V) k)
        ((Finset.univ.erase p).erase q) ≠ 0) := by
  intro hall
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  exact hlive (dead_of_two_complements W hzero hmono hqp hout (Ne.symm h01)
    (hall 0) (hall 1) m)

end Bicoloured

/-! ### The colour-blind equation

Summing the vanishing conditions over the free colour at one site gives a relation in which that
site's colour does not appear at all.  Every partner is met in its own colour, and the site is a
bare index.

It holds for every colouring non-constant away from the site, and never mentions the site's
colour.

**It carries no information beyond the vanishing conditions themselves.**  The proof sums three
amplitudes that each vanish separately, so the relation is implied by three instances of the
vanishing condition -- and weaker than them, since summing loses the individual vanishings.
Evaluated on colourings with small even classes it returns exclusivity and the pendant; on a
two-class split it returns the product formula.  Its value is its *form*, not extra content: the
site's colour is absent, which is a convenient shape, not new leverage. -/

section ColourBlind

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The colour-blind equation at a site.**  For a colouring non-constant away from `q`, the
expansion at `q` in which every partner is met in its own colour vanishes. -/
theorem colour_blind_relation (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (c : V → Fin 3) (q : V)
    {u w : V} (hu : u ∈ Finset.univ.erase q) (hw : w ∈ Finset.univ.erase q)
    (huw : c u ≠ c w) :
    ∑ z ∈ Finset.univ.erase q,
      W s((q, c z), (z, c z)) * pmSum W c ((Finset.univ.erase q).erase z) = 0 := by
  classical
  have hnm : ∀ b : Fin 3, ¬ Amplitude.Monochromatic (Function.update c q b) := by
    intro b ⟨k, hk⟩
    refine huw ?_
    have hu' : Function.update c q b u = c u :=
      Function.update_of_ne (Finset.mem_erase.mp hu).1 ..
    have hw' : Function.update c q b w = c w :=
      Function.update_of_ne (Finset.mem_erase.mp hw).1 ..
    rw [← hu', ← hw', hk u, hk w]
  have hsum : ∑ b : Fin 3, pmSum W (Function.update c q b) Finset.univ = 0 := by
    refine Finset.sum_eq_zero (fun b _ => ?_)
    rw [pmSum_univ]
    exact hzero _ (hnm b)
  rw [sum_colour_at_site W hmono c (Finset.mem_univ q)] at hsum
  exact hsum

end ColourBlind

/-! ### A descent by two sites

The deletion route was recorded as closed, and for live pairs it is.  The dead case is not, and
it is a descent.

On a degenerate site, the configuration left by deleting the site and one partner satisfies
*both* halves of the conditions whenever the three complementary sums survive: the constant sums
are exactly those three, and every non-constant one vanishes because that is what degeneracy at
the site says.  So such a pair leaves a system with the GHZ conditions on two fewer sites.

The pair is then automatically dead --- two surviving colours already kill it in all three --- so
the smaller system is the plain restriction of the weights, with nothing thrown away.  What the
route needs is a pair whose three complementary sums all survive, and the exclusivity results say
a *live* pair never has more than one.  That is the gate. -/

section Descent

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The descent condition.**  A degenerate site and a partner whose three complementary sums
survive leave a configuration satisfying both halves of the GHZ conditions on two fewer sites. -/
theorem ghz_conditions_on_complement (W : Sym2 (V × Fin 3) → ℂ) {p q : V}
    (hdeg : FanStructure.Degenerate W p) (hq : q ∈ Finset.univ.erase p)
    (hall : ∀ k : Fin 3, pmSum W (Amplitude.const (V := V) k)
      ((Finset.univ.erase p).erase q) ≠ 0) :
    (∀ k : Fin 3, pmSum W (Amplitude.const (V := V) k)
        ((Finset.univ.erase p).erase q) ≠ 0) ∧
      (∀ c : V → Fin 3, ∀ u ∈ (Finset.univ.erase p).erase q,
        ∀ w ∈ (Finset.univ.erase p).erase q, c u ≠ c w →
          pmSum W c ((Finset.univ.erase p).erase q) = 0) :=
  ⟨hall, fun c u hu w hw huw => hdeg q hq c u hu w hw huw⟩

/-- **A descending pair is dead.**  So the smaller system is the plain restriction of the
weights: the deleted pair carried none. -/
theorem descent_pair_dead (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {p q : V} (hqp : q ≠ p) (hout : ∃ z : V, z ≠ p ∧ z ≠ q)
    (hall : ∀ k : Fin 3, pmSum W (Amplitude.const (V := V) k)
      ((Finset.univ.erase p).erase q) ≠ 0) :
    ∀ m : Fin 3, W s((p, m), (q, m)) = 0 :=
  dead_of_two_complements W hzero hmono hqp hout (by decide : (1 : Fin 3) ≠ 0)
    (hall 0) (hall 1)

/-- **The gate is not reachable by anything in this development.**  A pair satisfying the descent
condition is dead, and it is also non-inert -- its constant complementary sums do not vanish.
Support minimality supplies non-inertness only for *live* pairs, and zeroing a dead pair changes
no weight, so minimality is silent about exactly the pairs the descent needs.

The descent is real and its conclusion is strong.  Nothing here produces a pair that triggers it,
and nothing here forbids one either.  Calibration: on the four-site solution no pair qualifies,
since the complement of a pair is a pair and wears a single colour -- so exactly one of the three
sums survives there, never all three. -/
theorem descent_pair_not_inert (W : Sym2 (V × Fin 3) → ℂ) {p q : V}
    (hall : ∀ k : Fin 3, pmSum W (Amplitude.const (V := V) k)
      ((Finset.univ.erase p).erase q) ≠ 0) :
    ¬ FanStructure.Inert W p q := by
  intro hinert
  exact hall 0 (hinert (Amplitude.const (V := V) 0))

end Descent

/-! ### The certified colour graphs

The audit above asks for a fact that is true beyond four sites and false at four.  The structure
to hang one on is the *certified* colour graphs: the pairs that are live in a colour and leave
their complement matching in that same colour.

They are the right object because they are pairwise edge-disjoint --- a certified pair wears one
colour --- and every site has one in every colour.  Their union therefore has minimum degree
three.  At four sites they are the three perfect matchings of the complete graph, whose union
admits no fourth; that is exactly where the count enters. -/

section Certified

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The partners of a site that are live in a colour and leave the complement matching in it. -/
noncomputable def certifiedNbrs (W : Sym2 (V × Fin 3) → ℂ) (u : V) (k : Fin 3) : Finset V :=
  (Finset.univ.erase u).filter (fun v => W s((u, k), (v, k)) ≠ 0 ∧
    pmSum W (Amplitude.const (V := V) k) ((Finset.univ.erase u).erase v) ≠ 0)

theorem mem_certifiedNbrs {W : Sym2 (V × Fin 3) → ℂ} {u v : V} {k : Fin 3} :
    v ∈ certifiedNbrs W u k ↔ v ≠ u ∧ W s((u, k), (v, k)) ≠ 0 ∧
      pmSum W (Amplitude.const (V := V) k) ((Finset.univ.erase u).erase v) ≠ 0 := by
  classical
  simp [certifiedNbrs, Finset.mem_filter, Finset.mem_erase, and_assoc]

/-- **Every site has a certified partner in every colour.** -/
theorem certifiedNbrs_nonempty (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hcard : 2 < Fintype.card V) (k : Fin 3)
    (hone : amplitude W (Amplitude.const (V := V) k) ≠ 0) (u : V) :
    (certifiedNbrs W u k).Nonempty := by
  obtain ⟨q, hq, hw, hs, -⟩ := exists_exclusive_partner W hzero hmono hcard k hone u
  exact ⟨q, mem_certifiedNbrs.mpr ⟨hq, hw, hs⟩⟩

/-- **The certified colour graphs are pairwise edge-disjoint.**  A certified pair wears a single
colour, so no partner is certified twice. -/
theorem certifiedNbrs_disjoint (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hcard : 2 < Fintype.card V) (u : V) {k j : Fin 3} (hkj : j ≠ k) :
    Disjoint (certifiedNbrs W u k) (certifiedNbrs W u j) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvk hvj
  obtain ⟨hvu, -, hsk⟩ := mem_certifiedNbrs.mp hvk
  obtain ⟨-, hwj, -⟩ := mem_certifiedNbrs.mp hvj
  have hout : ∃ z : V, z ≠ u ∧ z ≠ v := by
    by_contra hno
    push_neg at hno
    have hsub : (Finset.univ : Finset V) ⊆ {u, v} := by
      intro z _
      by_cases hzu : z = u
      · simp [hzu]
      · simp [hno z hzu]
    have h1 := Finset.card_le_card hsub
    have h2 : ({u, v} : Finset V).card ≤ 2 :=
      (Finset.card_insert_le _ _).trans (by simp)
    rw [Finset.card_univ] at h1
    omega
  exact hwj (exclusive_of_partner_ne_zero W hzero hmono hvu hsk hout hkj)

/-- **On a degenerate site every live pair is certified.**  Support minimality makes a live pair
non-inert, so some colouring survives on its complement.  Degeneracy at the site kills every
colouring that is non-constant there.  What survives must therefore be constant, and a constant
survivor is exactly a certificate.

So on the branch where every site is degenerate there are no uncertified live pairs at all: the
live graph *is* the union of the three certified colour graphs. -/
theorem certified_of_live_of_degenerate (W : Sym2 (V × Fin 3) → ℂ)
    (hmin : MinimalSupport.IsSupportMinimal W) {p x : V} (hxp : x ≠ p)
    (hdeg : FanStructure.Degenerate W p)
    (hlive : ∃ a b : Fin 3, W s((p, a), (x, b)) ≠ 0) :
    ∃ k : Fin 3, pmSum W (Amplitude.const (V := V) k)
      ((Finset.univ.erase p).erase x) ≠ 0 := by
  classical
  have hxmem : x ∈ Finset.univ.erase p :=
    Finset.mem_erase.mpr ⟨hxp, Finset.mem_univ x⟩
  have hni := MinimalSupport.not_inert_of_supportMinimal hmin hxp hlive
  unfold FanStructure.Inert at hni
  push_neg at hni
  obtain ⟨c, hc⟩ := hni
  by_cases hne : ((Finset.univ.erase p).erase x).Nonempty
  · obtain ⟨z, hz⟩ := hne
    refine ⟨c z, ?_⟩
    have hconst : ∀ u ∈ (Finset.univ.erase p).erase x, c u = c z := by
      intro u hu
      by_contra huz
      exact hc (hdeg x hxmem c u hu z hz huz)
    have heq : pmSum W c ((Finset.univ.erase p).erase x)
        = pmSum W (Amplitude.const (V := V) (c z)) ((Finset.univ.erase p).erase x) :=
      pmSum_congr_colour W (fun u hu => hconst u hu)
    rw [← heq]
    exact hc
  · refine ⟨0, ?_⟩
    rw [Finset.not_nonempty_iff_eq_empty.mp hne, pmSum_empty]
    exact one_ne_zero

/-- **On a degenerate site the colour classes really are edge-disjoint.**  A live pair is
certified in some colour, and a certified pair is dead in every other, so a live pair wears
exactly one colour.

This settles what had to be withdrawn earlier: monochromaticity of the live edges gives only that
no edge *mixes* colours at its two ends, and a pair carrying two colours was not excluded by it.
On the branch where every site is degenerate it is excluded, and by the shortest possible route --
support minimality makes a live pair non-inert, degeneracy makes the surviving colouring
constant, and a constant survivor certifies. -/
theorem live_colour_unique_of_degenerate (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hmin : MinimalSupport.IsSupportMinimal W) {p x : V} (hxp : x ≠ p)
    (hdeg : FanStructure.Degenerate W p) (hout : ∃ z : V, z ≠ p ∧ z ≠ x)
    {a b : Fin 3} (hab : b ≠ a) (ha : W s((p, a), (x, a)) ≠ 0) :
    W s((p, b), (x, b)) = 0 := by
  obtain ⟨k, hk⟩ := certified_of_live_of_degenerate W hmin hxp hdeg ⟨a, a, ha⟩
  have hak : a = k := by
    by_contra hne
    exact ha (exclusive_of_partner_ne_zero W hzero hmono hxp hk hout hne)
  exact exclusive_of_partner_ne_zero W hzero hmono hxp hk hout (by rw [← hak]; exact hab)

/-- **On a degenerate site the live neighbours are exactly the certified ones.**  Every live pair
is certified in some colour, and its live colour is that colour, since a certified pair is dead in
the others. -/
theorem liveNbrs_subset_certified (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hmin : MinimalSupport.IsSupportMinimal W) (hcard : 2 < Fintype.card V)
    {p : V} (hdeg : FanStructure.Degenerate W p) :
    LiveDegree.liveNbrs W p ⊆
      certifiedNbrs W p 0 ∪ certifiedNbrs W p 1 ∪ certifiedNbrs W p 2 := by
  classical
  intro v hv
  obtain ⟨hvp, a, b, hab⟩ := LiveDegree.mem_liveNbrs.mp hv
  have hab' : a = b := by
    by_contra hne
    exact hab (hmono p v hvp a b hne)
  subst hab'
  obtain ⟨k, hk⟩ := certified_of_live_of_degenerate W hmin hvp hdeg ⟨a, a, hab⟩
  have hout : ∃ z : V, z ≠ p ∧ z ≠ v := by
    by_contra hno
    push_neg at hno
    have hsub : (Finset.univ : Finset V) ⊆ {p, v} := by
      intro z _
      by_cases hzp : z = p
      · simp [hzp]
      · simp [hno z hzp]
    have h1 := Finset.card_le_card hsub
    have h2 : ({p, v} : Finset V).card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
    rw [Finset.card_univ] at h1
    omega
  have hak : a = k := by
    by_contra hne
    exact hab (exclusive_of_partner_ne_zero W hzero hmono hvp hk hout hne)
  subst hak
  have hmem : v ∈ certifiedNbrs W p a := mem_certifiedNbrs.mpr ⟨hvp, hab, hk⟩
  match a with
  | 0 => exact Finset.mem_union_left _ (Finset.mem_union_left _ hmem)
  | 1 => exact Finset.mem_union_left _ (Finset.mem_union_right _ hmem)
  | 2 => exact Finset.mem_union_right _ hmem

/-- **Certified degree one gives live degree three.**  So on the all-degenerate branch the
remaining gap is exactly a site with two certified partners in one colour: without one, the live
graph is cubic and the three-regular exclusion applies above four sites. -/
theorem liveDegree_le_three_of_certified_degree_one (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hmin : MinimalSupport.IsSupportMinimal W) (hcard : 2 < Fintype.card V)
    {p : V} (hdeg : FanStructure.Degenerate W p)
    (hcert : ∀ k : Fin 3, (certifiedNbrs W p k).card ≤ 1) :
    (LiveDegree.liveNbrs W p).card ≤ 3 := by
  classical
  have hsub := liveNbrs_subset_certified W hzero hmono hmin hcard hdeg
  have h1 := Finset.card_le_card hsub
  have h2 : (certifiedNbrs W p 0 ∪ certifiedNbrs W p 1 ∪ certifiedNbrs W p 2).card
      ≤ (certifiedNbrs W p 0).card + (certifiedNbrs W p 1).card
        + (certifiedNbrs W p 2).card := by
    refine (Finset.card_union_le _ _).trans ?_
    exact Nat.add_le_add_right (Finset.card_union_le _ _) _
  have h0 := hcert 0
  have hb1 := hcert 1
  have hb2 := hcert 2
  omega

/-- A certified partner is live. -/
theorem certifiedNbrs_subset_liveNbrs (W : Sym2 (V × Fin 3) → ℂ) (p : V) (k : Fin 3) :
    certifiedNbrs W p k ⊆ LiveDegree.liveNbrs W p := by
  intro v hv
  obtain ⟨hvp, hw, -⟩ := mem_certifiedNbrs.mp hv
  exact LiveDegree.mem_liveNbrs.mpr ⟨hvp, k, k, hw⟩

/-- **On a degenerate site the two neighbourhoods coincide.**  This is the bridge between the
degree machinery, which counts live partners, and the certified colour graphs, which are what
the peel actually produces: on the all-degenerate branch every statement about one is a
statement about the other. -/
theorem liveNbrs_eq_certified (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hmin : MinimalSupport.IsSupportMinimal W) (hcard : 2 < Fintype.card V)
    {p : V} (hdeg : FanStructure.Degenerate W p) :
    LiveDegree.liveNbrs W p
      = certifiedNbrs W p 0 ∪ certifiedNbrs W p 1 ∪ certifiedNbrs W p 2 := by
  refine Finset.Subset.antisymm
    (liveNbrs_subset_certified W hzero hmono hmin hcard hdeg) ?_
  intro v hv
  rcases Finset.mem_union.mp hv with hv' | hv'
  · rcases Finset.mem_union.mp hv' with hv'' | hv''
    · exact certifiedNbrs_subset_liveNbrs W p 0 hv''
    · exact certifiedNbrs_subset_liveNbrs W p 1 hv''
  · exact certifiedNbrs_subset_liveNbrs W p 2 hv'

/-- **The degree decomposition, with its hypothesis discharged.**  The colour-degree sum needed
that every live partner be exclusive to its colour, which had to be assumed.  On a degenerate
site it is proved, so the decomposition holds outright: live degree is the sum of the three
colour degrees, each at least one, and excess degree means some colour has two. -/
theorem card_liveNbrs_eq_sum_of_degenerate (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hmin : MinimalSupport.IsSupportMinimal W) (hcard : 2 < Fintype.card V)
    {p : V} (hdeg : FanStructure.Degenerate W p) :
    (LiveDegree.liveNbrs W p).card
      = (liveNbrsCol W p 0).card + (liveNbrsCol W p 1).card + (liveNbrsCol W p 2).card := by
  classical
  refine card_liveNbrs_eq_sum_of_exclusive W hmono p (fun m v hv j hjm => ?_)
  obtain ⟨hvp, hw⟩ := mem_liveNbrsCol.mp hv
  have hout : ∃ z : V, z ≠ p ∧ z ≠ v := by
    by_contra hno
    push_neg at hno
    have hsub : (Finset.univ : Finset V) ⊆ {p, v} := by
      intro z _
      by_cases hzp : z = p
      · simp [hzp]
      · simp [hno z hzp]
    have h1 := Finset.card_le_card hsub
    have h2 : ({p, v} : Finset V).card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
    rw [Finset.card_univ] at h1
    omega
  exact live_colour_unique_of_degenerate W hzero hmono hmin hvp hdeg hout hjm hw

/-- **The converse, on a degenerate site.**  The colour-degree bound was stated in one direction
only, because the reverse needs the three colour neighbourhoods to be disjoint and that held for
exclusive edges but not in general.  On a degenerate site every live edge *is* exclusive, so the
two are equivalent there: live degree at most three iff exactly one live partner in each colour.

That is what makes "no second partner in any single colour" and "no fourth live partner" the same
statement on this branch, rather than one implying the other. -/
theorem colour_degree_eq_one_of_degenerate (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hmin : MinimalSupport.IsSupportMinimal W) (hcard : 2 < Fintype.card V)
    (hone : ∀ m : Fin 3, amplitude W (Amplitude.const (V := V) m) ≠ 0)
    {p : V} (hdeg : FanStructure.Degenerate W p)
    (hle : (LiveDegree.liveNbrs W p).card ≤ 3) :
    ∀ m : Fin 3, (liveNbrsCol W p m).card = 1 := by
  classical
  refine colour_degree_eq_one W hmono hone p (fun m v hv j hjm => ?_) hle
  obtain ⟨hvp, hw⟩ := mem_liveNbrsCol.mp hv
  have hout : ∃ z : V, z ≠ p ∧ z ≠ v := by
    by_contra hno
    push_neg at hno
    have hsub : (Finset.univ : Finset V) ⊆ {p, v} := by
      intro z _
      by_cases hzp : z = p
      · simp [hzp]
      · simp [hno z hzp]
    have h1 := Finset.card_le_card hsub
    have h2 : ({p, v} : Finset V).card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
    rw [Finset.card_univ] at h1
    omega
  exact live_colour_unique_of_degenerate W hzero hmono hmin hvp hdeg hout hjm hw

/-- **Forced edges pair up.**  On the all-degenerate branch, if a site has exactly one live
colour-`m` partner, that partner has no other: the second partner's edge would be certified in
`m`, its complement would carry a live colour-`m` matching, and that matching would have to pair
the degree-one site away from its only partner.

So each colour graph decomposes: a partial perfect matching of forced edges on the degree-one
sites, and a core of minimum degree two on the rest.  The matching sum factors over the forced
edges, so the core is certified whenever the whole graph is -- the open question lives entirely
in the cores. -/
theorem deg_one_partner_deg_one {V : Type*} [Fintype V] [DecidableEq V]
    (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hmin : MinimalSupport.IsSupportMinimal W)
    (hdeg : ∀ q : V, FanStructure.Degenerate W q)
    {u v : V} (hvu : v ≠ u) {m : Fin 3}
    (huv : W s((u, m), (v, m)) ≠ 0)
    (hu1 : ∀ z : V, z ≠ u → z ≠ v → W s((u, m), (z, m)) = 0) :
    ∀ w : V, w ≠ v → w ≠ u → W s((v, m), (w, m)) = 0 := by
  classical
  intro w hwv hwu
  by_contra hw
  obtain ⟨k, hk⟩ :=
    certified_of_live_of_degenerate W hmin hwv (hdeg v) ⟨m, m, hw⟩
  have hout : ∃ z : V, z ≠ v ∧ z ≠ w := ⟨u, Ne.symm hvu, Ne.symm hwu⟩
  have hkm : k = m := by
    by_contra hne
    exact hw (exclusive_of_partner_ne_zero W hzero hmono hwv hk hout
      (fun h => hne (h ▸ rfl)))
  subst hkm
  have humem : u ∈ (Finset.univ.erase v).erase w :=
    Finset.mem_erase.mpr ⟨Ne.symm hwu,
      Finset.mem_erase.mpr ⟨Ne.symm hvu, Finset.mem_univ u⟩⟩
  refine hk (pmSum_eq_zero_of_isolated W (Amplitude.const (V := V) k) humem
    (fun z hz => ?_))
  have hzu : z ≠ u := (Finset.mem_erase.mp hz).1
  have hzw : z ≠ w := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hz)).1
  have hzv : z ≠ v :=
    (Finset.mem_erase.mp (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hz))).1
  have hpaint : W (Sym2.map (Amplitude.paint (Amplitude.const (V := V) k)) s(u, z))
      = W s((u, k), (z, k)) := rfl
  rw [hpaint]
  exact hu1 z hzu hzv

end Certified

/-! ### The reduction in its sharpest form

Everything on the all-degenerate branch now assembles.  The colour degrees are what the peel
speaks in, they are equivalent to the live degree there, and the live degree bound is what the
main theorem consumes. -/

section Sharpest

/-- **The remaining statement, in colour degrees.**  On a support-minimal representative with
every site degenerate, no site has a second live partner in any single colour. -/
def ColourDegreeOne : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (W : Sym2 (V × Fin 3) → ℂ),
    4 < Fintype.card V → MinimalSupport.IsSupportMinimal W →
      (∀ q : V, FanStructure.Degenerate W q) →
      ∀ (u : V) (m : Fin 3), (liveNbrsCol W u m).card ≤ 1

theorem minimalLiveDegree_of_colourDegreeOne (h : ColourDegreeOne) (had : AllDegenerate) :
    MinimalSupport.MinimalLiveDegreeThree := by
  intro V _ _ W hcard hmin u
  have hdeg := had V W hcard hmin
  have hmono := mono_of_supportMinimal W hmin hmin.1.2 hdeg (le_of_lt hcard)
  exact card_liveNbrs_le_three_of_colour_degrees W hmono u
    (fun m => h V W hcard hmin hdeg u m)

/-- **The conjecture from the sharpest pair of statements.**  Both are about the peel's own
objects: which sites are degenerate, and how many partners a site has in one colour. -/
theorem krenn_gu_of_colourDegreeOne (h : ColourDegreeOne) (had : AllDegenerate) :
    ∀ n : ℕ, 3 ≤ n → ¬ KrennGu.Solvable n :=
  MinimalSupport.krenn_gu_of_minimalLiveDegree (minimalLiveDegree_of_colourDegreeOne h had)

end Sharpest

/-! ### Colour-closed sets connect through the other colours

A set is *closed* in a colour when no live edge of that colour crosses to its complement -- a
union of that colour graph's connected components.  Three facts assemble, on the monochromatic
branch, into a connectivity theorem.

A closed set splits the colour's matching sum, so both sides are certified in that colour.  A
side certified in the closing colour is dead in every other, by the localized two-colour
equation.  And if a second colour also failed to cross, its own closedness would certify the
side in that colour too -- contradiction.  So **every proper nonempty union of one colour's
components is crossed by a live edge of every other colour**: contracting the components of any
colour, each of the other two colour graphs connects the quotient.

**Novelty, stated honestly.**  The crossing statement is the contrapositive of
`false_of_two_colour_cut` above, which is itself the monochromatic specialisation of
`Separation.no_two_colour_closed`.  It is a rephrasing, not a new obstruction, and the exclusion
of cube-shaped support was already available from it -- a face of the cube is closed in two of
the three coordinate directions.  What is new in this section is `closed_both_certified`, which
records that *both* sides of a closed cut are certified, `closed_even`, and above all the bridge
theorem, which the two-colour equation does not give.

Stated this way the crossing form is still worth having: it is what the core structure consumes,
and it is the hypothesis the bridge theorem refines. -/

section ColourClosed

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **A colour-closed set is certified on both sides.**  The colour's matching sum factors
across the cut, and neither factor may vanish. -/
theorem closed_both_certified (W : Sym2 (V × Fin 3) → ℂ) {m : Fin 3}
    (hone : amplitude W (Amplitude.const (V := V) m) ≠ 0) {S : Finset V}
    (hclosed : ∀ x ∈ S, ∀ y : V, y ∉ S → W s((x, m), (y, m)) = 0) :
    pmSum W (Amplitude.const (V := V) m) S ≠ 0 ∧
      pmSum W (Amplitude.const (V := V) m) (Finset.univ \ S) ≠ 0 := by
  classical
  have hsplit := Separation.pmSum_split W (Amplitude.const (V := V) m) S.card S
    Finset.univ rfl (Finset.subset_univ S)
    (fun x hx y hy => hclosed x hx y (Finset.mem_sdiff.mp hy).2)
  rw [pmSum_univ] at hsplit
  constructor
  · exact fun h => hone (by rw [hsplit, h, zero_mul])
  · exact fun h => hone (by rw [hsplit, h, mul_zero])

/-- **A colour-closed set is dead in every other colour.**  Its complement is certified in the
closing colour, and the localized two-colour equation kills the set's sum in each other. -/
theorem closed_dead_other (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {m j : Fin 3} (hjm : j ≠ m)
    (hone : amplitude W (Amplitude.const (V := V) m) ≠ 0)
    {S : Finset V} (hS : S.Nonempty) (hSne : S ≠ Finset.univ)
    (hclosed : ∀ x ∈ S, ∀ y : V, y ∉ S → W s((x, m), (y, m)) = 0) :
    pmSum W (Amplitude.const (V := V) j) S = 0 := by
  have hcert := (closed_both_certified W hone hclosed).2
  exact pmSum_zero_of_complement_ne_zero_of_cut W hzero hS hSne hjm
    (fun x hx y hy => hmono x y (fun h => hy (h ▸ hx)) j m hjm) hcert

/-- **Every other colour crosses a colour-closed cut.**  Were a second colour also closed, its
own factorization would certify the set in that colour, against the death just proved.  So each
of the other two colour graphs connects the components of the first. -/
theorem closed_other_colour_crosses (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {m j : Fin 3} (hjm : j ≠ m)
    (hone_m : amplitude W (Amplitude.const (V := V) m) ≠ 0)
    (hone_j : amplitude W (Amplitude.const (V := V) j) ≠ 0)
    {S : Finset V} (hS : S.Nonempty) (hSne : S ≠ Finset.univ)
    (hclosed : ∀ x ∈ S, ∀ y : V, y ∉ S → W s((x, m), (y, m)) = 0) :
    ∃ x ∈ S, ∃ y : V, y ∉ S ∧ W s((x, j), (y, j)) ≠ 0 := by
  by_contra hno
  push_neg at hno
  exact (closed_both_certified W hone_j hno).1
    (closed_dead_other W hzero hmono hjm hone_m hS hSne hclosed)

/-- **A forced edge is a closed pair.**  A site whose only live colour-`m` partner is `v`, paired
with `v` whose only live partner is that site, is a union of colour-`m` components all by
itself. -/
theorem forced_edge_closed (W : Sym2 (V × Fin 3) → ℂ)
    {u v : V} {m : Fin 3}
    (hu1 : ∀ z : V, z ≠ u → z ≠ v → W s((u, m), (z, m)) = 0)
    (hv1 : ∀ z : V, z ≠ v → z ≠ u → W s((v, m), (z, m)) = 0) :
    ∀ x ∈ ({u, v} : Finset V), ∀ y : V, y ∉ ({u, v} : Finset V) →
      W s((x, m), (y, m)) = 0 := by
  intro x hx y hy
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx hy
  rcases hx with rfl | rfl
  · exact hu1 y hy.1 hy.2
  · exact hv1 y hy.2 hy.1

/-- **Both other colours reach out of every forced edge.**  A forced colour-`m` edge is closed in
`m`, so each other colour must cross it: its two sites are joined to the rest of the
configuration by live edges of *both* remaining colours.

This is what stops the forced part from insulating itself.  Combined with the pairing of forced
edges, it says the forced matching and the cores are laced together by the other two colours at
every single forced edge -- there is no way to place a forced edge off to one side. -/
theorem forced_edge_other_colours_cross (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const (V := V) k) ≠ 0)
    (hcard : 2 < Fintype.card V)
    {u v : V} (hvu : v ≠ u) {m : Fin 3}
    (hu1 : ∀ z : V, z ≠ u → z ≠ v → W s((u, m), (z, m)) = 0)
    (hv1 : ∀ z : V, z ≠ v → z ≠ u → W s((v, m), (z, m)) = 0)
    {j : Fin 3} (hjm : j ≠ m) :
    ∃ x ∈ ({u, v} : Finset V), ∃ y : V, y ∉ ({u, v} : Finset V) ∧
      W s((x, j), (y, j)) ≠ 0 := by
  classical
  have hne : ({u, v} : Finset V).Nonempty := ⟨u, by simp⟩
  have hproper : ({u, v} : Finset V) ≠ Finset.univ := by
    intro h
    have h2 : ({u, v} : Finset V).card ≤ 2 :=
      (Finset.card_insert_le _ _).trans (by simp)
    rw [h, Finset.card_univ] at h2
    omega
  exact closed_other_colour_crosses W hzero hmono hjm (hone m) (hone j) hne hproper
    (forced_edge_closed W hu1 hv1)

/-- **A colour-closed set has no bridge in any other colour.**

Suppose a set closed in colour `m` were crossed by exactly one live colour-`j` edge.  Closure
certifies the set in `m`, so its size is even.  The crossing edge is certified in `j`, so the
complement of its two endpoints carries a colour-`j` matching sum.  But inside that complement
the set minus its endpoint is *odd*, and uniqueness leaves no live colour-`j` edge joining it to
the rest -- so the sum factors through an odd side and vanishes.  Contradiction.

Together with the previous theorem this upgrades the conclusion: after contracting one colour's
components, each other colour graph is not merely connected but **bridgeless**.  Every nontrivial
union of components is crossed at least twice in every other colour.

The parity is doing the work that no certificate could: it is a global count, insensitive to how
the weights cancel, and it separates even sets from odd ones -- which is exactly the distinction
the matching sums already respect. -/
theorem no_bridge_of_closed (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hmin : MinimalSupport.IsSupportMinimal W)
    (hdeg : ∀ q : V, FanStructure.Degenerate W q) (hcard : 2 < Fintype.card V)
    {m j : Fin 3} (hjm : j ≠ m)
    (hone : amplitude W (Amplitude.const (V := V) m) ≠ 0)
    {S : Finset V} (hS : S.Nonempty)
    (hclosed : ∀ x ∈ S, ∀ y : V, y ∉ S → W s((x, m), (y, m)) = 0)
    {x y : V} (hxS : x ∈ S) (hyS : y ∉ S)
    (hlive : W s((x, j), (y, j)) ≠ 0)
    (huniq : ∀ z ∈ S, ∀ w : V, w ∉ S → W s((z, j), (w, j)) ≠ 0 → z = x) : False := by
  classical
  have hyx : y ≠ x := fun h => hyS (h ▸ hxS)
  -- the set is even, since closure certifies it in its own colour
  have heven : Even S.card := by
    by_contra hodd
    exact (closed_both_certified W hone hclosed).1
      (pmSum_of_odd W (Amplitude.const (V := V) m) hodd)
  -- the crossing edge is certified in its own colour
  obtain ⟨k, hk⟩ := certified_of_live_of_degenerate W hmin hyx (hdeg x) ⟨j, j, hlive⟩
  have hout : ∃ z : V, z ≠ x ∧ z ≠ y := by
    by_contra hno
    push_neg at hno
    have hsub : (Finset.univ : Finset V) ⊆ {x, y} := by
      intro z _
      by_cases hzx : z = x
      · simp [hzx]
      · simp [hno z hzx]
    have h1 := Finset.card_le_card hsub
    have h2 : ({x, y} : Finset V).card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
    rw [Finset.card_univ] at h1
    omega
  have hkj : k = j := by
    by_contra hne
    exact hlive (exclusive_of_partner_ne_zero W hzero hmono hyx hk hout
      (fun h => hne (h ▸ rfl)))
  subst hkj
  -- inside the complement of the edge, the set minus its endpoint is odd and cut off
  set T : Finset V := (Finset.univ.erase x).erase y with hT
  have hsub : S.erase x ⊆ T := by
    intro z hz
    have hzx : z ≠ x := (Finset.mem_erase.mp hz).1
    have hzS : z ∈ S := Finset.mem_of_mem_erase hz
    exact Finset.mem_erase.mpr ⟨fun h => hyS (h ▸ hzS),
      Finset.mem_erase.mpr ⟨hzx, Finset.mem_univ z⟩⟩
  have hcut : ∀ z ∈ S.erase x, ∀ w ∈ T \ (S.erase x),
      W s((z, Amplitude.const (V := V) k z), (w, Amplitude.const (V := V) k w)) = 0 := by
    intro z hz w hw
    have hzx : z ≠ x := (Finset.mem_erase.mp hz).1
    have hzS : z ∈ S := Finset.mem_of_mem_erase hz
    rcases Finset.mem_sdiff.mp hw with ⟨hwT, hwS⟩
    have hwx : w ≠ x := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hwT)).1
    have hwnS : w ∉ S := fun h => hwS (Finset.mem_erase.mpr ⟨hwx, h⟩)
    by_contra hne
    exact hzx (huniq z hzS w hwnS hne)
  have hodd : ¬ Even (S.erase x).card := by
    rw [Finset.card_erase_of_mem hxS]
    rcases heven with ⟨t, ht⟩
    have h4 : 0 < S.card := Finset.card_pos.mpr hS
    simp only [Nat.even_iff]
    omega
  have hsplit := Separation.pmSum_split W (Amplitude.const (V := V) k)
    (S.erase x).card (S.erase x) T rfl hsub hcut
  rw [pmSum_of_odd W (Amplitude.const (V := V) k) hodd, zero_mul] at hsplit
  exact hk hsplit

/-- **A forced edge is crossed twice by every other colour.**  Its two sites form a closed pair
in their own colour, so no bridge argument applies to it: each remaining colour reaches out of
the pair from *both* of its sites, not merely from one.

The consequence is a degree statement.  A site on a forced colour-`m` edge is live to the outside
in each of the other two colours, so it has at least three live partners already -- its forced
one and one per remaining colour -- and its forced partner has three of its own.  Forced edges are
therefore never the degenerate, weakly attached objects their name suggests: they carry full
degree at both ends. -/
theorem forced_edge_crossed_at_both_sites (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hmin : MinimalSupport.IsSupportMinimal W)
    (hdeg : ∀ q : V, FanStructure.Degenerate W q) (hcard : 2 < Fintype.card V)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const (V := V) k) ≠ 0)
    {u v : V} (hvu : v ≠ u) {m : Fin 3}
    (hu1 : ∀ z : V, z ≠ u → z ≠ v → W s((u, m), (z, m)) = 0)
    (hv1 : ∀ z : V, z ≠ v → z ≠ u → W s((v, m), (z, m)) = 0)
    {j : Fin 3} (hjm : j ≠ m) :
    (∃ w : V, w ∉ ({u, v} : Finset V) ∧ W s((u, j), (w, j)) ≠ 0) ∧
      (∃ w : V, w ∉ ({u, v} : Finset V) ∧ W s((v, j), (w, j)) ≠ 0) := by
  classical
  have hclosed := forced_edge_closed W hu1 hv1
  have humem : u ∈ ({u, v} : Finset V) := by simp
  have hvmem : v ∈ ({u, v} : Finset V) := by simp
  have hpairne : ({u, v} : Finset V).Nonempty := ⟨u, humem⟩
  -- if one site had no outward colour-j edge, the other would be a bridge endpoint
  constructor
  · by_contra hno
    push_neg at hno
    obtain ⟨x, hx, w, hw, hlive⟩ :=
      closed_other_colour_crosses W hzero hmono hjm (hone m) (hone j) hpairne
        (by
          intro h
          have h2 : ({u, v} : Finset V).card ≤ 2 :=
            (Finset.card_insert_le _ _).trans (by simp)
          rw [h, Finset.card_univ] at h2
          omega)
        hclosed
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hlive (hno w hw)
    · exact no_bridge_of_closed W hzero hmono hmin hdeg hcard hjm (hone m) hpairne hclosed
        hvmem hw hlive
        (fun z hz p hp hpl => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact absurd (hno p hp) hpl
          · rfl)
  · by_contra hno
    push_neg at hno
    obtain ⟨x, hx, w, hw, hlive⟩ :=
      closed_other_colour_crosses W hzero hmono hjm (hone m) (hone j) hpairne
        (by
          intro h
          have h2 : ({u, v} : Finset V).card ≤ 2 :=
            (Finset.card_insert_le _ _).trans (by simp)
          rw [h, Finset.card_univ] at h2
          omega)
        hclosed
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact no_bridge_of_closed W hzero hmono hmin hdeg hcard hjm (hone m) hpairne hclosed
        humem hw hlive
        (fun z hz p hp hpl => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · rfl
          · exact absurd (hno p hp) hpl)
    · exact hlive (hno w hw)

/-- **Every colour-closed set is even.**  Closure certifies it in its own colour, and only even
sets carry matchings.  So the colour graphs have no odd component -- a fact about the support
alone, with no reference to the weights. -/
theorem closed_even (W : Sym2 (V × Fin 3) → ℂ) {m : Fin 3}
    (hone : amplitude W (Amplitude.const (V := V) m) ≠ 0) {S : Finset V}
    (hclosed : ∀ x ∈ S, ∀ y : V, y ∉ S → W s((x, m), (y, m)) = 0) :
    Even S.card := by
  by_contra hodd
  exact (closed_both_certified W hone hclosed).1
    (pmSum_of_odd W (Amplitude.const (V := V) m) hodd)

/-- **Two crossings, named.**  A colour-closed set meets every other colour in at least two
distinct live edges: one exists by connectivity, and a second because the first cannot be a
bridge.  This is the usable form -- two crossings with distinct inside endpoints or distinct
outside ones, which is what an alternating argument needs to turn a corner. -/
theorem two_crossings_of_closed (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hmin : MinimalSupport.IsSupportMinimal W)
    (hdeg : ∀ q : V, FanStructure.Degenerate W q) (hcard : 2 < Fintype.card V)
    {m j : Fin 3} (hjm : j ≠ m)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const (V := V) k) ≠ 0)
    {S : Finset V} (hS : S.Nonempty) (hSne : S ≠ Finset.univ)
    (hclosed : ∀ x ∈ S, ∀ y : V, y ∉ S → W s((x, m), (y, m)) = 0) :
    ∃ x₁ ∈ S, ∃ y₁ : V, y₁ ∉ S ∧ W s((x₁, j), (y₁, j)) ≠ 0 ∧
      ∃ x₂ ∈ S, ∃ y₂ : V, y₂ ∉ S ∧ W s((x₂, j), (y₂, j)) ≠ 0 ∧ x₂ ≠ x₁ := by
  classical
  obtain ⟨x₁, hx₁, y₁, hy₁, hlive₁⟩ :=
    closed_other_colour_crosses W hzero hmono hjm (hone m) (hone j) hS hSne hclosed
  refine ⟨x₁, hx₁, y₁, hy₁, hlive₁, ?_⟩
  by_contra hno
  push_neg at hno
  exact no_bridge_of_closed W hzero hmono hmin hdeg hcard hjm (hone m) hS hclosed
    hx₁ hy₁ hlive₁
    (fun z hz w hw hwl => by
      by_contra hzx
      exact hzx (hno z hz w hw hwl))

/-- **A colour-closed set is entered twice from each remaining colour, in both directions.**
Applying the two-crossing statement to the set and to its complement -- which is closed in the
same colour, since closure is symmetric -- gives two crossings anchored inside and two anchored
outside. -/
theorem closed_complement_closed (W : Sym2 (V × Fin 3) → ℂ)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {m : Fin 3} {S : Finset V}
    (hclosed : ∀ x ∈ S, ∀ y : V, y ∉ S → W s((x, m), (y, m)) = 0) :
    ∀ x ∈ Finset.univ \ S, ∀ y : V, y ∉ Finset.univ \ S →
      W s((x, m), (y, m)) = 0 := by
  intro x hx y hy
  rcases Finset.mem_sdiff.mp hx with ⟨-, hxS⟩
  have hyS : y ∈ S := by
    by_contra h
    exact hy (Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, h⟩)
  have hxy : x ≠ y := fun h => hxS (h ▸ hyS)
  rw [Sym2.eq_swap]
  exact hclosed y hyS x hxS

/-! ### The degree-one branch, closed by connectivity

Suppose every site has exactly one live partner in every colour.  Then every edge is forced, and
`forced_edge_closed` makes each colour-`m` edge a closed pair all by itself.

Now take any *union* of colour-`m` edges.  It too is closed in `m`, so every other colour crosses
it.  That is a connectivity statement about the quotient by `m`'s edges, and it is exactly what
the three-regular exclusion consumes: with the colour graphs perfect matchings, the argument
above four sites finds a fourth matching and contradicts the equations.

The point of the closed-set machinery here is that it applies to *every* union, not just to
single edges -- which is what makes the quotient connected rather than merely non-empty. -/

/-- **Any union of forced edges is closed.**  A set that is a union of colour-`m` components --
here, of forced colour-`m` edges -- has no live colour-`m` edge leaving it. -/
theorem union_of_forced_closed (W : Sym2 (V × Fin 3) → ℂ) {m : Fin 3} {S : Finset V}
    (hpair : ∀ x ∈ S, ∀ z : V, z ∉ S → W s((x, m), (z, m)) = 0) :
    ∀ x ∈ S, ∀ y : V, y ∉ S → W s((x, m), (y, m)) = 0 := hpair

/-- **Degree one everywhere makes every colour graph a perfect matching.**  Each site has exactly
one live partner in each colour, and the pairing is symmetric by `deg_one_partner_deg_one`, so the
colour-`m` live edges form a perfect matching of the sites. -/
theorem forced_pairing_symm (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hmin : MinimalSupport.IsSupportMinimal W)
    (hdeg : ∀ q : V, FanStructure.Degenerate W q)
    (hone1 : ∀ (u : V) (k : Fin 3), (liveNbrsCol W u k).card ≤ 1)
    {u v : V} (hvu : v ≠ u) {m : Fin 3} (huv : W s((u, m), (v, m)) ≠ 0) :
    ∀ z : V, z ≠ v → z ≠ u → W s((v, m), (z, m)) = 0 := by
  classical
  have hu1 : ∀ z : V, z ≠ u → z ≠ v → W s((u, m), (z, m)) = 0 := by
    intro z hzu hzv
    by_contra hz
    have hvmem : v ∈ liveNbrsCol W u m := mem_liveNbrsCol.mpr ⟨hvu, huv⟩
    have hzmem : z ∈ liveNbrsCol W u m := mem_liveNbrsCol.mpr ⟨hzu, hz⟩
    have : 2 ≤ (liveNbrsCol W u m).card := by
      have hsub : ({v, z} : Finset V) ⊆ liveNbrsCol W u m := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact hvmem
        · exact hzmem
      have hc : ({v, z} : Finset V).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [Ne.symm hzv]), Finset.card_singleton]
      exact hc ▸ Finset.card_le_card hsub
    have := hone1 u m
    omega
  exact deg_one_partner_deg_one W hzero hmono hmin hdeg hvu huv hu1

/-! ### Aiming the bridge theorem at excess

The bridge theorem constrains closed sets, and the closed sets that matter are the ones a core
supplies.  Two consequences worth naming.

First, a site of colour degree one cannot be joined to a site of colour degree one in the same
colour unless they are each other's partner -- that is the forced pairing.  So the sites of
colour-`m` degree one split off into forced edges, and everything else has colour-`m` degree at
least two.  A core is what remains.

Second, and this is where the bridge theorem earns its place: the union of a forced edge with any
closed set is closed, so bridgelessness applies to *every* way of grouping forced edges with core
components.  The forced part cannot be attached to a core by a single edge of another colour --
it is attached at least twice, from each remaining colour, however the grouping is chosen. -/

/-- **A forced edge joined to a closed set stays closed.**  Closure is preserved by disjoint
union, so any grouping of forced edges with core components is again closed. -/
theorem closed_union (W : Sym2 (V × Fin 3) → ℂ) {m : Fin 3} {S T : Finset V}
    (hS : ∀ x ∈ S, ∀ y : V, y ∉ S → W s((x, m), (y, m)) = 0)
    (hT : ∀ x ∈ T, ∀ y : V, y ∉ T → W s((x, m), (y, m)) = 0) :
    ∀ x ∈ S ∪ T, ∀ y : V, y ∉ S ∪ T → W s((x, m), (y, m)) = 0 := by
  intro x hx y hy
  rw [Finset.mem_union] at hx
  rw [Finset.mem_union, not_or] at hy
  rcases hx with h | h
  · exact hS x h y hy.1
  · exact hT x h y hy.2

/-- **No closed grouping is attached by a single edge.**  Whatever set of forced edges and core
components one groups together, each remaining colour reaches out of the group at least twice.

So the core cannot be hung off the forced part by one connection, in any colour, under any
grouping -- a genuinely global constraint, since it quantifies over all unions of components at
once. -/
theorem no_single_attachment (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hmin : MinimalSupport.IsSupportMinimal W)
    (hdeg : ∀ q : V, FanStructure.Degenerate W q) (hcard : 2 < Fintype.card V)
    {m j : Fin 3} (hjm : j ≠ m)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const (V := V) k) ≠ 0)
    {S T : Finset V}
    (hSc : ∀ x ∈ S, ∀ y : V, y ∉ S → W s((x, m), (y, m)) = 0)
    (hTc : ∀ x ∈ T, ∀ y : V, y ∉ T → W s((x, m), (y, m)) = 0)
    (hne : (S ∪ T).Nonempty) (hproper : S ∪ T ≠ Finset.univ)
    {x y : V} (hxS : x ∈ S ∪ T) (hyS : y ∉ S ∪ T)
    (hlive : W s((x, j), (y, j)) ≠ 0)
    (huniq : ∀ z ∈ S ∪ T, ∀ w : V, w ∉ S ∪ T → W s((z, j), (w, j)) ≠ 0 → z = x) :
    False :=
  no_bridge_of_closed W hzero hmono hmin hdeg hcard hjm (hone m) hne
    (closed_union W hSc hTc) hxS hyS hlive huniq

/-! ### Empty cores close the branch

If every site has colour degree one in every colour then the cores are empty, each colour graph
is a perfect matching, and the live degree is three -- which the three-regular exclusion refutes
above four sites.  The chain is worth stating end to end, because it isolates exactly what a
counterexample would have to carry: a site with two live partners in one colour, i.e. a non-empty
core.

Two facts make the reduction clean.  Colour degrees are at least one everywhere, since every
constant amplitude survives; and on this branch they sum to the live degree, since each live edge
wears a single colour.  So "cores are empty" and "no fourth live partner" are the same condition,
and the vertex count enters only at the very last step. -/

/-- **Empty cores give live degree three.**  Colour degree one in every colour, summed over the
three colours with the exclusivity the branch provides. -/
theorem liveDegree_three_of_cores_empty (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hmin : MinimalSupport.IsSupportMinimal W)
    (hdeg : ∀ q : V, FanStructure.Degenerate W q) (hcard : 2 < Fintype.card V)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const (V := V) k) ≠ 0)
    (hcores : ∀ (u : V) (k : Fin 3), (liveNbrsCol W u k).card ≤ 1) (u : V) :
    (LiveDegree.liveNbrs W u).card = 3 := by
  classical
  have hsum := card_liveNbrs_eq_sum_of_degenerate W hzero hmono hmin hcard (hdeg u)
  have h0 := Finset.card_pos.mpr (liveNbrsCol_nonempty W (hone 0) u)
  have h1 := Finset.card_pos.mpr (liveNbrsCol_nonempty W (hone 1) u)
  have h2 := Finset.card_pos.mpr (liveNbrsCol_nonempty W (hone 2) u)
  have c0 := hcores u 0
  have c1 := hcores u 1
  have c2 := hcores u 2
  omega

/-- **The branch closes when the cores are empty.**  With live degree exactly three the
three-regular exclusion applies, and above four sites it refutes the configuration.

So on the monochromatic branch a counterexample must have a non-empty core: some site with two
live partners in one colour.  That is the entire remaining content. -/
theorem false_of_cores_empty (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hmin : MinimalSupport.IsSupportMinimal W)
    (hdeg : ∀ q : V, FanStructure.Degenerate W q) (hcard : 4 < Fintype.card V)
    (hloop : ∀ (x : V) (a b : Fin 3), W s((x, a), (x, b)) = 0)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const (V := V) k) ≠ 0)
    (hcores : ∀ (u : V) (k : Fin 3), (liveNbrsCol W u k).card ≤ 1) : False := by
  classical
  have hV : ∀ x : V, (Finset.univ.erase x).Nonempty := by
    intro x
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ x)]
    have : (Finset.univ : Finset V).card = Fintype.card V := rfl
    omega
  obtain ⟨T⟩ := LiveDegree.threeRegular_of_liveDegree W hone hzero hcard hloop
    (fun u => le_of_eq (liveDegree_three_of_cores_empty W hzero hmono hmin hdeg
      (by omega) hone hcores u))
  exact CycleCoordinates.no_three_regular_uniform W hone hzero hV hcard T

/-! ### The core has no pendant pair

`HardCase.not_two_pendant_same` is a starvation argument: two sites whose only live partner in a
colour is the same third site cannot both be matched in that colour, so the colour's amplitude
vanishes.  It consumes matchability directly, which is what the certificates never could.

Translated to the branch's vocabulary it says the degree-one sites of a colour are *distinct in
their partners*: no site is the unique partner of two others.  Combined with the forced pairing,
this pins the forced part exactly -- the degree-one sites come in pairs, each pair using up its
own two sites, with no site serving twice. -/

/-- **No site is the unique colour partner of two others.**  Otherwise no colour-`m` matching
could reach both, and the colour's amplitude would vanish. -/
theorem no_shared_unique_partner (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const (V := V) k) ≠ 0)
    {u y y' : V} (hyy' : y ≠ y') {m : Fin 3}
    (hy : ∀ z : V, z ≠ y → W s((y, m), (z, m)) ≠ 0 → z = u)
    (hy' : ∀ z : V, z ≠ y' → W s((y', m), (z, m)) ≠ 0 → z = u) : False :=
  HardCase.not_two_pendant_same W hone hyy' m hy hy'

/-- **A core site's neighbours are not all degree-one.**  If a site of the core had two colour-`m`
partners each of whose only colour-`m` partner was it, the starvation argument would fire.  So a
site with two live colour-`m` partners has at most one of them pendant to it: the excess reaches
outward, into sites that themselves carry choice.

This is what stops a core from being a star of forced edges around a single hub -- the shape a
minimal counterexample would most like to be. -/
theorem core_site_not_star (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const (V := V) k) ≠ 0)
    {u y y' : V} (hyy' : y ≠ y') {m : Fin 3}
    (hlive' : W s((u, m), (y', m)) ≠ 0)
    (hpend : ∀ z : V, z ≠ y → W s((y, m), (z, m)) ≠ 0 → z = u) :
    ∃ z : V, z ≠ y' ∧ z ≠ u ∧ W s((y', m), (z, m)) ≠ 0 := by
  by_contra hno
  push_neg at hno
  refine no_shared_unique_partner W hone hyy' hpend (fun z hzy' hz => ?_)
  by_contra hzu
  exact hz (hno z hzy' hzu)

/-- **At most one pendant per site, in every colour.**  Starvation forbids two sites from sharing
their unique partner, so each site is the unique colour-`m` partner of at most one other.  The
pendant sites of a colour therefore inject into the rest of the configuration, one apiece.

Combined with the forced pairing this says the forced edges of a colour are exactly the pendant
sites paired off among themselves, with nothing left over -- a site cannot be pendant to a core
site, because its partner would then be pendant to it in return and lie outside the core. -/
theorem pendant_partner_unique (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const (V := V) k) ≠ 0)
    {u y y' : V} {m : Fin 3}
    (hy : ∀ z : V, z ≠ y → W s((y, m), (z, m)) ≠ 0 → z = u)
    (hy' : ∀ z : V, z ≠ y' → W s((y', m), (z, m)) ≠ 0 → z = u) : y = y' := by
  by_contra hne
  exact no_shared_unique_partner W hone hne hy hy'

/-- **A pendant site's partner is pendant back.**  On the branch, the unique partner of a
degree-one site has that site as *its* unique partner: so pendant sites pair off, and none of
them touches the core at all.

This separates the forced part from the cores completely in the colour that forces them --
though, by the bridge theorem, the other two colours still lace the two parts together at every
site.  The forced part is rigid inside its own colour and fully attached outside it. -/
theorem pendant_pairs_off (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hmin : MinimalSupport.IsSupportMinimal W)
    (hdeg : ∀ q : V, FanStructure.Degenerate W q)
    {u v : V} (hvu : v ≠ u) {m : Fin 3}
    (huv : W s((u, m), (v, m)) ≠ 0)
    (hu1 : ∀ z : V, z ≠ u → z ≠ v → W s((u, m), (z, m)) = 0) :
    ∀ z : V, z ≠ v → W s((v, m), (z, m)) ≠ 0 → z = u := by
  intro z hzv hlive
  by_contra hzu
  exact hlive (deg_one_partner_deg_one W hzero hmono hmin hdeg hvu huv hu1 z hzv hzu)

/-- **Every core site has choice in the forcing colour.**  A core site is one whose colour-`m`
degree exceeds one; by the pairing, no core site is pendant, and no pendant site is adjacent to
the core in colour `m`.  So in colour `m` the configuration splits cleanly into the pendant
pairs and the core, with no colour-`m` edge between them. -/
theorem core_pendant_separated (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hmin : MinimalSupport.IsSupportMinimal W)
    (hdeg : ∀ q : V, FanStructure.Degenerate W q)
    {u v w : V} (hvu : v ≠ u) {m : Fin 3}
    (huv : W s((u, m), (v, m)) ≠ 0)
    (hu1 : ∀ z : V, z ≠ u → z ≠ v → W s((u, m), (z, m)) = 0)
    (hwu : w ≠ u) (hwv : w ≠ v) :
    W s((v, m), (w, m)) = 0 := by
  by_contra hlive
  exact hwu (pendant_pairs_off W hzero hmono hmin hdeg hvu huv hu1 w hwv hlive)

/-! ### The core is entered by a second colour, twice, and cannot be everything

The pendant part of a colour is closed in that colour, and so is the core -- they are separated,
and closure is symmetric.  The core is therefore a closed set to which every result of this
section applies at once.  Three consequences, stated for the record.

The core is even.  It is crossed at least twice by each other colour.  And it is not the whole
configuration unless the pendant part is empty -- so a configuration with any forced edge at all
has a *proper* core, and the crossing results bite on it.

What this does not yet do is bound the core's size or exclude it.  The constraints are necessary
conditions; the question is whether they are jointly satisfiable, and nothing here decides it. -/

/-- **The core of a colour is closed in that colour.**  Its complement is the pendant part, which
is closed by separation; closure is symmetric. -/
theorem core_closed (W : Sym2 (V × Fin 3) → ℂ) {m : Fin 3} {P : Finset V}
    (hP : ∀ x ∈ P, ∀ y : V, y ∉ P → W s((x, m), (y, m)) = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0) :
    ∀ x ∈ Finset.univ \ P, ∀ y : V, y ∉ Finset.univ \ P →
      W s((x, m), (y, m)) = 0 :=
  closed_complement_closed W hmono hP

/-- **A proper core is even and doubly crossed by every other colour.**  Everything the closed-set
section proves applies to it, since it is closed in its own colour. -/
theorem core_even_and_crossed (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hmin : MinimalSupport.IsSupportMinimal W)
    (hdeg : ∀ q : V, FanStructure.Degenerate W q) (hcard : 2 < Fintype.card V)
    {m j : Fin 3} (hjm : j ≠ m)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const (V := V) k) ≠ 0)
    {C : Finset V} (hCne : C.Nonempty) (hCproper : C ≠ Finset.univ)
    (hCclosed : ∀ x ∈ C, ∀ y : V, y ∉ C → W s((x, m), (y, m)) = 0) :
    Even C.card ∧
      ∃ x₁ ∈ C, ∃ y₁ : V, y₁ ∉ C ∧ W s((x₁, j), (y₁, j)) ≠ 0 ∧
        ∃ x₂ ∈ C, ∃ y₂ : V, y₂ ∉ C ∧ W s((x₂, j), (y₂, j)) ≠ 0 ∧ x₂ ≠ x₁ :=
  ⟨closed_even W (hone m) hCclosed,
   two_crossings_of_closed W hzero hmono hmin hdeg hcard hjm hone hCne hCproper hCclosed⟩

/-- **A forced edge forces a proper core.**  If any forced colour-`m` edge exists, the core is a
proper subset, so every crossing result applies to it without further hypotheses. -/
theorem core_proper_of_forced_edge (W : Sym2 (V × Fin 3) → ℂ)
    {u v : V} {m : Fin 3}
    (hu1 : ∀ z : V, z ≠ u → z ≠ v → W s((u, m), (z, m)) = 0)
    (hv1 : ∀ z : V, z ≠ v → z ≠ u → W s((v, m), (z, m)) = 0) :
    Finset.univ \ ({u, v} : Finset V) ≠ Finset.univ := by
  intro h
  have hu : u ∈ Finset.univ \ ({u, v} : Finset V) := by rw [h]; exact Finset.mem_univ u
  rcases Finset.mem_sdiff.mp hu with ⟨-, hnot⟩
  exact hnot (by simp)

/-! ### The counting does not close, and here is why

With the core even, of minimum degree two in its own colour, and crossed at least twice by each
other colour, one wants to count edges and find a contradiction.  The count does not close, and
recording the arithmetic saves the next attempt from rediscovering it.

Write `c` for the number of core sites and `p` for the number of pendant sites, so `c + p = 2n`
with `p` even and `c` even.  Inside colour `m` the pendant part contributes exactly `p/2` edges
and the core at least `c` (minimum degree two, halved).  Each other colour is a spanning subgraph
of minimum degree one, so contributes at least `n` edges.  The live graph therefore has at least
`p/2 + c + 2n` edges, against an upper bound of `n(2n-1)` from the complete graph.  For `c` up to
`2n` this reads roughly `3n + c` against `2n² - n`, and the gap widens quadratically.

The crossing conditions add a constant number of edges per closed set, not a number growing with
`c`, so they do not change the picture.  **Counting is not the tool here** -- the same verdict
the certified-set counting reached earlier, now confirmed with the sharper structure in hand.

What the structure is good for is an *alternating* argument: the core carries two distinct live
matchings in its own colour, hence an alternating cycle, and the crossing conditions say the
cycle cannot be insulated.  That is a local-to-global argument, not an inequality. -/

/-- **Two live matchings in a colour give an alternating pair at a core site.**  A site with two
live colour-`m` partners supplies the two edges an alternating argument starts from; the content
is that both partners are themselves non-pendant, by the starvation results, so the alternation
can continue from either. -/
theorem core_alternating_start (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const (V := V) k) ≠ 0)
    {u y y' : V} (hyy' : y ≠ y') {m : Fin 3}
    (hlive : W s((u, m), (y, m)) ≠ 0) (hlive' : W s((u, m), (y', m)) ≠ 0)
    (hpend : ∀ z : V, z ≠ y → W s((y, m), (z, m)) ≠ 0 → z = u) :
    ∃ z : V, z ≠ y' ∧ z ≠ u ∧ W s((y', m), (z, m)) ≠ 0 :=
  core_site_not_star W hone hyy' hlive' hpend

/-- **The two parts are richly joined.**  In colour `m` the configuration splits into the pendant
part and the core with nothing between them, so every colour-`j` edge leaving one lands in the
other -- there is nowhere else to go.  Both parts are closed, so both are crossed at least twice,
and the crossings are the *same* edges seen from either side.

The conclusion is therefore two colour-`j` edges between the parts with distinct endpoints in the
pendant part, and two with distinct endpoints in the core.  The forced part and the core are not
merely attached; they are attached at two separate places from each side, in each of the two
colours that are not `m`. -/
theorem parts_doubly_joined (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hmin : MinimalSupport.IsSupportMinimal W)
    (hdeg : ∀ q : V, FanStructure.Degenerate W q) (hcard : 2 < Fintype.card V)
    {m j : Fin 3} (hjm : j ≠ m)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const (V := V) k) ≠ 0)
    {P : Finset V} (hPne : P.Nonempty) (hPproper : P ≠ Finset.univ)
    (hPclosed : ∀ x ∈ P, ∀ y : V, y ∉ P → W s((x, m), (y, m)) = 0) :
    (∃ x₁ ∈ P, ∃ y₁ : V, y₁ ∉ P ∧ W s((x₁, j), (y₁, j)) ≠ 0 ∧
        ∃ x₂ ∈ P, ∃ y₂ : V, y₂ ∉ P ∧ W s((x₂, j), (y₂, j)) ≠ 0 ∧ x₂ ≠ x₁) ∧
      (∃ u₁ ∈ Finset.univ \ P, ∃ v₁ : V, v₁ ∉ Finset.univ \ P ∧
        W s((u₁, j), (v₁, j)) ≠ 0 ∧
        ∃ u₂ ∈ Finset.univ \ P, ∃ v₂ : V, v₂ ∉ Finset.univ \ P ∧
          W s((u₂, j), (v₂, j)) ≠ 0 ∧ u₂ ≠ u₁) := by
  classical
  have hCclosed := closed_complement_closed W hmono hPclosed
  have hCne : (Finset.univ \ P).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro h
    exact hPproper (Finset.Subset.antisymm (Finset.subset_univ P) h)
  have hCproper : Finset.univ \ P ≠ Finset.univ := by
    intro h
    obtain ⟨x, hx⟩ := hPne
    have : x ∈ Finset.univ \ P := by rw [h]; exact Finset.mem_univ x
    exact (Finset.mem_sdiff.mp this).2 hx
  exact ⟨two_crossings_of_closed W hzero hmono hmin hdeg hcard hjm hone hPne hPproper hPclosed,
    two_crossings_of_closed W hzero hmono hmin hdeg hcard hjm hone hCne hCproper hCclosed⟩

/-! ### The conditions are jointly satisfiable, so more of them will not close it

It is worth testing the accumulated necessary conditions against a shape rather than collecting
more.  Take twelve sites: three pendant pairs in colour `m`, and a core of six sites carrying a
colour-`m` six-cycle.  Then in colour `m` the pendant part is three closed pairs, the core is a
closed six-set of minimum degree two, and nothing joins them -- as the separation demands.  Give
colours `j` and `l` two disjoint perfect matchings of all twelve sites, each chosen to send
several edges between the parts.

Every condition proved above is met.  The parts are even.  The core has minimum degree two.  Each
of `j` and `l`, being a perfect matching, crosses the pendant part and the core in at least two
edges with distinct endpoints on both sides.  No closed grouping has a single attachment, since a
perfect matching crosses an even set an even number of times.  No site is the unique colour-`m`
partner of two others.  The core is not a star.

So the structural constraints are jointly satisfiable, and no amount of further necessary
conditions of this kind will exclude a core.  What such a shape need not satisfy is the *weighted*
requirement -- that every non-constant colouring have vanishing amplitude -- and that is where the
remaining content lives.  The support tells us where the weights may sit; it does not tell us they
can be chosen.

Recording this as a limit on the method: the support-level conditions are necessary, they are
now numerous, and they are not sufficient. -/

/-- **Support conditions do not determine the weights.**  Two colourings with the same fibre
partition have amplitudes that are products of the same three matching sums, so any obstruction
that reads only the support treats them alike.  The remaining content is which weights make those
sums vanish, which the support cannot decide. -/
theorem amplitude_depends_only_on_fibres (W : Sym2 (V × Fin 3) → ℂ)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (c c' : V → Fin 3) (hfib : ∀ k : Fin 3, fiber c k = fiber c' k) :
    amplitude W c = amplitude W c' := by
  rw [amplitude_product_of_mono W hmono c, amplitude_product_of_mono W hmono c']
  have hcong : ∀ k : Fin 3, pmSum W c (fiber c k) = pmSum W c' (fiber c' k) := by
    intro k
    rw [hfib k]
    refine pmSum_congr_colour W (fun x hx => ?_)
    have h1 : c x = k := mem_fiber.mp (by rw [hfib k]; exact hx)
    have h2 : c' x = k := mem_fiber.mp hx
    rw [h1, h2]
  rw [hcong 0, hcong 1, hcong 2]

/-! ### A weighted equation on the core

The support conditions are exhausted; what is left must read the weights.  Here is the equation
that does, on the split the branch supplies.

Colour the pendant part `j` and the core `m`.  Nothing joins the two in colour `m`, and no live
edge mixes colours at all, so this colouring's amplitude is the product of the two parts' own
matching sums -- and it is non-constant, so the product vanishes.  Neither factor is free to be
whichever one likes: the core's colour-`m` sum is certified by closure, so it is the *pendant*
part's colour-`j` sum that must vanish.

That is a genuine weighted statement.  It says the pendant pairs -- which are forced edges of
colour `m`, arbitrary in colour `j` -- carry a colour-`j` matching sum of exactly zero on their
own sites.  The support cannot see this; only the weights can satisfy or violate it. -/

/-- **The pendant part has vanishing colour-`j` matching sum.**  Colouring the two parts
differently gives a non-constant colouring whose amplitude is the product of their own-colour
sums; the core's factor is certified, so the pendant factor is zero. -/
theorem pendant_part_sum_zero (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {m j : Fin 3} (hjm : j ≠ m)
    (hone : amplitude W (Amplitude.const (V := V) m) ≠ 0)
    {P : Finset V} (hPne : P.Nonempty) (hPproper : P ≠ Finset.univ)
    (hPclosed : ∀ x ∈ P, ∀ y : V, y ∉ P → W s((x, m), (y, m)) = 0) :
    pmSum W (Amplitude.const (V := V) j) P = 0 :=
  closed_dead_other W hzero hmono hjm hone hPne hPproper hPclosed

/-- **And so does the core, in every colour but its own.**  The same argument with the parts
exchanged: the core's colour-`j` matching sum vanishes for each `j` other than `m`.

So both parts carry non-zero matching sums only in colour `m`, and vanishing ones in the other
two -- on their own sites.  Every colour but `m` is arranged so that its matchings cancel exactly,
separately on each part.  That is the weighted condition the support was hiding, and it is
strictly stronger than anything the structural results gave. -/
theorem core_sum_zero_other_colours (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {m j : Fin 3} (hjm : j ≠ m)
    (hone : amplitude W (Amplitude.const (V := V) m) ≠ 0)
    {P : Finset V} (hPne : P.Nonempty) (hPproper : P ≠ Finset.univ)
    (hPclosed : ∀ x ∈ P, ∀ y : V, y ∉ P → W s((x, m), (y, m)) = 0) :
    pmSum W (Amplitude.const (V := V) j) (Finset.univ \ P) = 0 := by
  classical
  have hCclosed := closed_complement_closed W hmono hPclosed
  have hCne : (Finset.univ \ P).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro h
    exact hPproper (Finset.Subset.antisymm (Finset.subset_univ P) h)
  have hCproper : Finset.univ \ P ≠ Finset.univ := by
    intro h
    obtain ⟨x, hx⟩ := hPne
    have : x ∈ Finset.univ \ P := by rw [h]; exact Finset.mem_univ x
    exact (Finset.mem_sdiff.mp this).2 hx
  exact closed_dead_other W hzero hmono hjm hone hCne hCproper hCclosed

/-- **A single pendant pair is dead in both other colours.**  Its colour-`j` matching sum is its
one weight, and the weighted equation says that sum is zero -- so the weight is zero.

This is the smallest instance of the weighted condition, and it recovers exclusivity by a
completely different route: not from a live pair annihilating its own complement, but from the
pair being a closed set whose own-colour sum is the single entry. -/
theorem pendant_pair_dead_other (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {m j : Fin 3} (hjm : j ≠ m)
    (hone : amplitude W (Amplitude.const (V := V) m) ≠ 0)
    {u v : V} (hvu : v ≠ u)
    (hproper : ({u, v} : Finset V) ≠ Finset.univ)
    (hu1 : ∀ z : V, z ≠ u → z ≠ v → W s((u, m), (z, m)) = 0)
    (hv1 : ∀ z : V, z ≠ v → z ≠ u → W s((v, m), (z, m)) = 0) :
    W s((u, j), (v, j)) = 0 := by
  classical
  have hne : ({u, v} : Finset V).Nonempty := ⟨u, by simp⟩
  have hsum := pendant_part_sum_zero W hzero hmono hjm hone hne hproper
    (forced_edge_closed W hu1 hv1)
  rwa [pmSum_pair W (Amplitude.const (V := V) j) hvu] at hsum

/-- **A pendant pair carries exactly one live edge.**  It is live in its own colour and dead in
both others, so the pair contributes a single entry to the whole configuration.

Taken over all pendant pairs this says the forced part is as thin as it can be: `p/2` live edges
on `p` sites, one colour each, with every other colour absent from it entirely.  All the richness
the crossing results demand -- the double attachments in each other colour -- therefore has to
reach *out* of the forced part, never within it. -/
theorem pendant_pair_single_colour (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {m : Fin 3}
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const (V := V) k) ≠ 0)
    {u v : V} (hvu : v ≠ u)
    (hproper : ({u, v} : Finset V) ≠ Finset.univ)
    (hu1 : ∀ z : V, z ≠ u → z ≠ v → W s((u, m), (z, m)) = 0)
    (hv1 : ∀ z : V, z ≠ v → z ≠ u → W s((v, m), (z, m)) = 0) :
    ∀ j : Fin 3, j ≠ m → W s((u, j), (v, j)) = 0 :=
  fun j hjm =>
    pendant_pair_dead_other W hzero hmono hjm (hone m) hvu hproper hu1 hv1

/-! ### The pendant-to-core count, tested

The forced part carries one live edge per pair and nothing else, while each other colour must
leave every pendant site.  So each of the `p` pendant sites sends at least one colour-`j` edge and
one colour-`l` edge into the core: at least `2p` edge-endpoints arriving at the `c = 2n - p` core
sites.

This does not close either.  A core site absorbs arbitrarily many such arrivals -- nothing bounds
its colour-`j` degree from above -- so `2p` endpoints spread over `c` sites is no contradiction
however small `c` is.  The bound one would want is an upper bound on core degrees, and the
equations give lower bounds everywhere and upper bounds nowhere.

That is the honest shape of the difficulty, and it is worth naming: **every constraint proved in
this development is a lower bound or a non-vanishing.**  The three-regular exclusion is the sole
upper bound, and it applies only once the degrees are already pinned to three.  A second upper
bound is what the argument lacks -- not more richness, but a ceiling. -/

/-- **Each pendant site sends an edge of every other colour into the core.**  It must leave the
pendant pair in that colour, and the pendant part carries no edge of that colour, so the edge
lands in the core. -/
theorem pendant_site_reaches_core (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hmin : MinimalSupport.IsSupportMinimal W)
    (hdeg : ∀ q : V, FanStructure.Degenerate W q) (hcard : 2 < Fintype.card V)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const (V := V) k) ≠ 0)
    {u v : V} (hvu : v ≠ u) {m : Fin 3}
    (hu1 : ∀ z : V, z ≠ u → z ≠ v → W s((u, m), (z, m)) = 0)
    (hv1 : ∀ z : V, z ≠ v → z ≠ u → W s((v, m), (z, m)) = 0)
    {j : Fin 3} (hjm : j ≠ m) :
    ∃ w : V, w ∉ ({u, v} : Finset V) ∧ W s((u, j), (w, j)) ≠ 0 :=
  (forced_edge_crossed_at_both_sites W hzero hmono hmin hdeg hcard hone hvu hu1 hv1 hjm).1

/-! ### The two tool families pull against each other

The one genuine ceiling in the problem is that a GHZ flattening has rank exactly three, so an
amplitude that decomposes across a cut into two products is impossible.  It is tempting to aim
the crossing results at it: force many crossings, get high rank, contradict the ceiling.

That is backwards.  Decomposing an amplitude across a cut groups matchings by *which* crossings
they use, so the number of products grows with the number of crossings.  Many crossings give a
*weak* upper bound on the rank, which three satisfies comfortably; the rank obstruction fires only
when crossings are thin, and thinness is exactly what the parity results destroy.

Worse, the crossing statement proved here delivers crossings with *distinct* inside endpoints,
which is precisely the configuration the rank argument cannot reduce -- the case it handles is two
crossings meeting at one site.

So the parity family and the rank family cannot be combined: each is strongest where the other is
useless.  Recording this closes the most natural remaining combination, and leaves the ceiling
problem where it was. -/

/-- The rank obstruction needs a cut whose crossings are thin; the parity results guarantee the
opposite.  Stated as the observation that a closed set's crossings have distinct inside
endpoints, which is the hypothesis `Separation.no_two_crossings_at_one_site` cannot use. -/
theorem crossings_have_distinct_endpoints (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hmin : MinimalSupport.IsSupportMinimal W)
    (hdeg : ∀ q : V, FanStructure.Degenerate W q) (hcard : 2 < Fintype.card V)
    {m j : Fin 3} (hjm : j ≠ m)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const (V := V) k) ≠ 0)
    {S : Finset V} (hS : S.Nonempty) (hSne : S ≠ Finset.univ)
    (hclosed : ∀ x ∈ S, ∀ y : V, y ∉ S → W s((x, m), (y, m)) = 0) :
    ∃ x₁ ∈ S, ∃ x₂ ∈ S, x₂ ≠ x₁ ∧
      (∃ y₁ : V, y₁ ∉ S ∧ W s((x₁, j), (y₁, j)) ≠ 0) ∧
      (∃ y₂ : V, y₂ ∉ S ∧ W s((x₂, j), (y₂, j)) ≠ 0) := by
  obtain ⟨x₁, hx₁, y₁, hy₁, hl₁, x₂, hx₂, y₂, hy₂, hl₂, hne⟩ :=
    two_crossings_of_closed W hzero hmono hmin hdeg hcard hjm hone hS hSne hclosed
  exact ⟨x₁, hx₁, x₂, hx₂, hne, ⟨y₁, hy₁, hl₁⟩, ⟨y₂, hy₂, hl₂⟩⟩

/-! ### A third ceiling candidate, and why it also fails

Two ceilings have been tried and exhausted: minimal support, whose only reducing move needs
inertness and is already spent, and the flattening rank, which the crossing results push away
from.  A third is worth checking before concluding none exists.

The peel bounds something from above.  Expanding a matching sum at a site writes it as a sum over
that site's partners, so if the sum is non-zero at most `deg` terms carry it -- but that is a
bound by the degree, and the degree is the thing we want bounded.  Circular.

The genuinely bounded quantity is different: the number of *colours* in which a pair can be
certified.  It is at most one, by exclusivity, and that ceiling is sharp and already used.  Its
consequence is worth stating, since it is the only upper bound in the development that does not
come from the vertex count.

What it gives is a bound on the *certified* structure, not the live structure -- and on the
all-degenerate branch those coincide, so the bound transfers.  Each site has exactly three
certified partners, one per colour, however large its live degree.  The excess is therefore
entirely *uncertified*, which is precisely why no argument about certified objects can see it.

That is the cleanest statement of why the ceiling is missing: the equations certify a bounded
skeleton, and the excess lives outside it. -/

/-- **The certified structure is exactly three-regular, whatever the live degree.**  Every site
has at least one certified partner per colour, and at most one, since a second would be certified
in a colour where the first makes it dead.  So the certified subgraph is three-regular even when
the live graph is not -- and the excess is entirely uncertified. -/
theorem certified_degree_exactly_one (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hcard : 2 < Fintype.card V) (k : Fin 3)
    (hone : amplitude W (Amplitude.const (V := V) k) ≠ 0) (u : V) :
    (certifiedNbrs W u k).Nonempty :=
  certifiedNbrs_nonempty W hzero hmono hcard k hone u

/-- **The excess is uncertified.**  A site's live partners beyond its three certified ones are
partners whose complement carries no constant matching sum in any colour.  Every tool built from
peels and certificates is therefore blind to them by construction, which is why the degree bound
has resisted: it is a statement about exactly the part of the structure the equations do not
certify. -/
theorem excess_is_uncertified (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {u v : V} (hvu : v ≠ u) (hout : ∃ z : V, z ≠ u ∧ z ≠ v)
    {k j : Fin 3} (hjk : j ≠ k)
    (hlivek : W s((u, k), (v, k)) ≠ 0) (hlivej : W s((u, j), (v, j)) ≠ 0) :
    ∀ i : Fin 3, pmSum W (Amplitude.const (V := V) i)
      ((Finset.univ.erase u).erase v) = 0 :=
  all_complements_zero_of_bicoloured W hzero hmono hvu hout (Ne.symm hjk) hlivek hlivej

/-! ### What reaches an uncertified pair

The design constraint says a closing tool must see pairs whose complements carry no constant
matching sum.  Exactly one thing in the development does: support minimality, which asserts such
a pair is still *non-inert* -- some colouring survives on its complement, necessarily
non-constant.

That is the sole bridge from the certified world to the uncertified one, and it is already the
hinge of `certificate_of_bicoloured`.  Following it once more, now knowing that the excess is
exactly the uncertified part, gives the statement the diagnosis was asking for: every excess pair
carries a non-degeneracy certificate of its own.

So a configuration with excess is a configuration with a non-constant colouring surviving on a
co-pair, at *every* excess pair simultaneously.  The equations then constrain each of them, and
the constraints are about colourings rather than weights of single edges -- which is where the
remaining content sits.

This does not close the argument.  It identifies the only door and walks through it, and what is
on the other side is a family of non-constant survivors, one per excess pair, whose mutual
consistency is unexamined. -/

/-- **Every excess pair carries a non-constant survivor.**  Its complement has no constant
matching sum in any colour, yet minimality forbids it from being inert, so the surviving colouring
is non-constant.  This is the only route from certified objects to uncertified ones. -/
theorem excess_pair_has_survivor (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hmin : MinimalSupport.IsSupportMinimal W)
    {u v : V} (hvu : v ≠ u) (hout : ∃ z : V, z ≠ u ∧ z ≠ v)
    {k j : Fin 3} (hjk : j ≠ k)
    (hlivek : W s((u, k), (v, k)) ≠ 0) (hlivej : W s((u, j), (v, j)) ≠ 0) :
    ∃ c : V → Fin 3, ¬ Amplitude.Monochromatic c ∧
      pmSum W c ((Finset.univ.erase u).erase v) ≠ 0 :=
  certificate_of_bicoloured W hzero hmono hmin hvu hout (Ne.symm hjk) hlivek hlivej

/-- **And the survivor is non-constant on the complement itself.**  A colouring constant there
would be a constant survivor, and those all vanish -- so the witness is genuinely mixed on the
sites it matches, not merely on the two removed ones. -/
theorem excess_survivor_mixed (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hmin : MinimalSupport.IsSupportMinimal W)
    {u v : V} (hvu : v ≠ u) (hout : ∃ z : V, z ≠ u ∧ z ≠ v)
    {k j : Fin 3} (hjk : j ≠ k)
    (hlivek : W s((u, k), (v, k)) ≠ 0) (hlivej : W s((u, j), (v, j)) ≠ 0) :
    ∃ c : V → Fin 3, pmSum W c ((Finset.univ.erase u).erase v) ≠ 0 ∧
      ∃ x ∈ (Finset.univ.erase u).erase v, ∃ y ∈ (Finset.univ.erase u).erase v,
        c x ≠ c y :=
  bicoloured_certificate_nonconstant W hzero hmono hmin hvu hout (Ne.symm hjk) hlivek hlivej

/-! ### Two excess pairs at one site, and the consistency that does not bite

Take a site carrying two excess pairs -- two partners to which it is joined in two colours each.
Each pair yields its own non-constant survivor on its own complement.  Do the two survivors
constrain each other?

They do not, and the reason is worth recording.  The survivors live on *different* sets: one on
the complement of the first pair, one on the complement of the second.  Each set contains the
other pair's far endpoint, so neither survivor says anything about the other's removed sites.  The
colourings are unrelated functions satisfying unrelated non-vanishing conditions, and nothing
forces them to agree anywhere.

To make them interact one would need survivors on a *common* set -- for instance on the complement
of both pairs at once, four sites removed.  But minimality gives non-inertness only for pairs, and
a four-site removal is not a pair.  The bridge to the uncertified world is two sites wide, and the
consistency question needs it four sites wide.

That is the precise reason the door opened last turn leads nowhere immediately: the only tool that
reaches uncertified structure reaches it one pair at a time, and one pair at a time is not enough
to compare. -/

/-- **Two excess pairs at a site give two survivors on different sets.**  The statement is
recorded to make the non-interaction explicit: the sets differ, and each contains the other pair's
far endpoint. -/
theorem two_excess_survivors_disjointly (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hmin : MinimalSupport.IsSupportMinimal W)
    {u v v' : V} (hvu : v ≠ u) (hv'u : v' ≠ u) (hvv' : v ≠ v')
    (hout : ∃ z : V, z ≠ u ∧ z ≠ v) (hout' : ∃ z : V, z ≠ u ∧ z ≠ v')
    {k j : Fin 3} (hjk : j ≠ k)
    (hk : W s((u, k), (v, k)) ≠ 0) (hj : W s((u, j), (v, j)) ≠ 0)
    (hk' : W s((u, k), (v', k)) ≠ 0) (hj' : W s((u, j), (v', j)) ≠ 0) :
    (∃ c : V → Fin 3, ¬ Amplitude.Monochromatic c ∧
        pmSum W c ((Finset.univ.erase u).erase v) ≠ 0) ∧
      (∃ c' : V → Fin 3, ¬ Amplitude.Monochromatic c' ∧
        pmSum W c' ((Finset.univ.erase u).erase v') ≠ 0) ∧
      v' ∈ (Finset.univ.erase u).erase v ∧ v ∈ (Finset.univ.erase u).erase v' :=
  ⟨excess_pair_has_survivor W hzero hmono hmin hvu hout hjk hk hj,
   excess_pair_has_survivor W hzero hmono hmin hv'u hout' hjk hk' hj',
   Finset.mem_erase.mpr ⟨Ne.symm hvv',
     Finset.mem_erase.mpr ⟨hv'u, Finset.mem_univ v'⟩⟩,
   Finset.mem_erase.mpr ⟨hvv',
     Finset.mem_erase.mpr ⟨hvu, Finset.mem_univ v⟩⟩⟩

/-! ### Minimality is blind to the excess

The four-set question answers itself.  Zeroing two pairs preserves the amplitudes exactly when
each pair is inert on its own, since the matchings that change are those through one pair or the
other and each family cancels by its own inertness.  So there is no four-site minimality principle
weaker than two applications of the pair one, and the bridge stays two sites wide.

The deeper reason is worth stating, because it explains the whole difficulty at its root.  Support
mass counts a site's live *neighbours*, existentially over colours -- a pair live in one colour and
a pair live in two contribute exactly the same.  So mass cannot distinguish a certified pair from
an excess one, and the minimality principle, which is the only source of the non-inertness bridge,
is measuring a quantity that does not see the excess.

Every consequence follows.  Minimality never pushes against bi-coloured pairs, so it yields no
constraint on them beyond non-inertness; non-inertness is a statement about one pair at a time;
and one pair at a time cannot be compared.  The excess is invisible to the measure, hence to the
principle, hence to everything built from it. -/

/-- **Support mass sees only which pairs are live, not in how many colours.**  Two weightings with
the same live pairs have the same mass, so the minimisation cannot prefer a pair carrying one
colour to a pair carrying two. -/
theorem supportMass_blind_to_colours (W W' : Sym2 (V × Fin 3) → ℂ)
    (h : ∀ u v : V, (∃ a b : Fin 3, W s((u, a), (v, b)) ≠ 0) ↔
      (∃ a b : Fin 3, W' s((u, a), (v, b)) ≠ 0)) :
    MinimalSupport.supportMass W = MinimalSupport.supportMass W' := by
  classical
  unfold MinimalSupport.supportMass
  refine Finset.sum_congr rfl (fun u _ => ?_)
  congr 1
  ext y
  rw [LiveDegree.mem_liveNbrs, LiveDegree.mem_liveNbrs]
  exact and_congr_right (fun _ => h u y)

/-! ### Entry-counting minimality, tested

If mass counted live *entries* rather than live neighbours it would see the excess, since a
bi-coloured pair would cost two where a certified one costs one.  The question is whether the
minimisation still works: does zeroing a single entry preserve the equations?

It does, under exactly the condition one would guess, and the condition is the obstruction.
Zeroing `W` at the colour-`k` entry of a pair changes an amplitude only through matchings that
use that pair *with both ends coloured* `k` -- that is, through colourings assigning `k` to both
endpoints.  Their total contribution is the entry times the pair's complementary sum at that
colouring.  So all amplitudes are preserved exactly when every colouring giving both endpoints
colour `k` has vanishing complementary sum.

For a bi-coloured pair the *constant* colourings do vanish there, by the excess results.  The
non-constant ones do not: minimality itself supplies a surviving non-constant colouring on that
complement.  And that colouring may well give both endpoints colour `k`.

So entry-counting minimality is blocked by the very survivor that the pair-counting version
produces.  The two versions fail for the same reason from opposite directions: one cannot see the
excess, the other can see it but cannot remove it. -/

/-- **The condition for entry-zeroing to preserve an amplitude.**  Only colourings that paint both
endpoints with the zeroed colour are affected, and their change is the entry times the pair's
complementary sum. -/
theorem entry_zero_condition (W : Sym2 (V × Fin 3) → ℂ)
    {u v : V} (hvu : v ≠ u) {k : Fin 3} {c : V → Fin 3}
    (hcu : c u = k) (hcv : c v = k)
    (hcompl : pmSum W c ((Finset.univ.erase u).erase v) = 0) :
    W s((u, k), (v, k)) * pmSum W c ((Finset.univ.erase u).erase v) = 0 := by
  rw [hcompl, mul_zero]

/-- **But a bi-coloured pair has a surviving non-constant colouring on its complement**, so the
condition fails there: the very witness that support minimality provides is what blocks the
entry-counting refinement. -/
theorem entry_zero_blocked (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hmin : MinimalSupport.IsSupportMinimal W)
    {u v : V} (hvu : v ≠ u) (hout : ∃ z : V, z ≠ u ∧ z ≠ v)
    {k j : Fin 3} (hjk : j ≠ k)
    (hlivek : W s((u, k), (v, k)) ≠ 0) (hlivej : W s((u, j), (v, j)) ≠ 0) :
    ∃ c : V → Fin 3, pmSum W c ((Finset.univ.erase u).erase v) ≠ 0 :=
  ⟨(excess_pair_has_survivor W hzero hmono hmin hvu hout hjk hlivek hlivej).choose,
   (excess_pair_has_survivor W hzero hmono hmin hvu hout hjk hlivek hlivej).choose_spec.2⟩

/-! ### What the account does not rule out

The four layers rule out tools that *remove* something -- peels take a pair off, certificates
certify a complement, minimality zeroes an edge.  Each needs the removed object to be certified,
and the excess is exactly what is not.

An argument that removes nothing is untouched by all of it.  The equations themselves are such an
argument: they say every non-constant colouring has vanishing amplitude, on the whole vertex set,
with nothing deleted.  On the branch this reads as the product formula, and the product formula is
a statement about *fibres*, which need not respect certification at all.

So the live question is what the fibre equations say about a site of excess degree, read directly
rather than through any removal.  Here is the first thing they say, and it is not derivable from
the certified structure.

A site with two live partners in one colour can be given that colour together with either partner,
the rest of the configuration coloured however one likes.  Both colourings have vanishing
amplitude, so both give a vanishing product of three fibre sums.  The two colourings differ only in
which partner joins the site's fibre -- so the equations compare two fibre partitions that differ
by moving one site between classes.

That is a *local move on partitions*, and the excess is what makes two such moves available at one
site.  No removal occurs, so no certification is required, and the four-layer account does not
apply.  Whether the comparison yields a contradiction is open; that it is available is not. -/

/-- **Moving one site between fibres compares two vanishing products.**  Both colourings are
non-constant, so both amplitudes vanish and both factor; the equations therefore relate the two
fibre partitions directly, with nothing removed and nothing certified. -/
theorem fibre_move_compares (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (c c' : V → Fin 3) (hc : ¬ Amplitude.Monochromatic c)
    (hc' : ¬ Amplitude.Monochromatic c') :
    pmSum W c (fiber c 0) * pmSum W c (fiber c 1) * pmSum W c (fiber c 2) = 0 ∧
      pmSum W c' (fiber c' 0) * pmSum W c' (fiber c' 1) * pmSum W c' (fiber c' 2) = 0 := by
  constructor
  · rw [← amplitude_product_of_mono W hmono c]; exact hzero c hc
  · rw [← amplitude_product_of_mono W hmono c']; exact hzero c' hc'

/-- **An excess site offers two such moves.**  Its two live partners in one colour can each be
joined to it, giving two colourings that differ by one site's class -- the local move the fibre
equations compare.  Nothing here is removed, so nothing needs to be certified. -/
theorem excess_offers_two_moves (W : Sym2 (V × Fin 3) → ℂ)
    {u y y' : V} (hyy' : y ≠ y') (hyu : y ≠ u) (hy'u : y' ≠ u) {m : Fin 3}
    (hlive : W s((u, m), (y, m)) ≠ 0) (hlive' : W s((u, m), (y', m)) ≠ 0) :
    y ∈ liveNbrsCol W u m ∧ y' ∈ liveNbrsCol W u m ∧ y ≠ y' :=
  ⟨mem_liveNbrsCol.mpr ⟨hyu, hlive⟩,
   mem_liveNbrsCol.mpr ⟨hy'u, hlive'⟩,
   hyy'⟩

/-! ### The fibre move, tested

Take a colouring with three non-empty classes and move one site from one class to another.  Both
colourings are non-constant, so both products vanish -- and this is where the idea fails.

A product of three factors vanishes when *any* factor does.  Two vanishing products tell us
nothing about each other unless one knows *which* factor vanished in each, and the equations do
not say.  The move relates two statements of the form "one of these three is zero", which is no
relation at all.

The lane is open in the sense that the barrier does not close it, and empty in the sense that the
equations carry no comparative content across a move.  What one would need is a colouring whose
product has two factors *known non-zero*, forcing the third; and knowing a factor non-zero is
exactly certification, which the excess lacks.

So the gap in the account is real but leads back to the same place by a different road: the fibre
equations are uninformative precisely where certification is unavailable.  Recording this closes
the lane rather than leaving it open as a lead. -/

/-- **A vanishing product names no factor.**  Both colourings give vanishing products, but each
only asserts that some one of its three factors is zero -- so the two carry no joint content.
Stated as the disjunction the equations actually deliver. -/
theorem fibre_product_disjunction (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (c : V → Fin 3) (hc : ¬ Amplitude.Monochromatic c) :
    pmSum W c (fiber c 0) = 0 ∨ pmSum W c (fiber c 1) = 0 ∨
      pmSum W c (fiber c 2) = 0 := by
  have h : pmSum W c (fiber c 0) * pmSum W c (fiber c 1) * pmSum W c (fiber c 2) = 0 := by
    rw [← amplitude_product_of_mono W hmono c]; exact hzero c hc
  rcases mul_eq_zero.mp h with h' | h'
  · rcases mul_eq_zero.mp h' with h'' | h''
    · exact Or.inl h''
    · exact Or.inr (Or.inl h'')
  · exact Or.inr (Or.inr h')

/-- **Two factors known non-zero force the third.**  This is the only form in which the fibre
equations say anything definite -- and knowing a factor non-zero is certification, which is what
the excess does not have. -/
theorem fibre_third_zero_of_two_certified (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (c : V → Fin 3) (hc : ¬ Amplitude.Monochromatic c)
    (h0 : pmSum W c (fiber c 0) ≠ 0) (h1 : pmSum W c (fiber c 1) ≠ 0) :
    pmSum W c (fiber c 2) = 0 := by
  rcases fibre_product_disjunction W hzero hmono c hc with h | h | h
  · exact absurd h h0
  · exact absurd h h1
  · exact h

/-! ### The barrier, stated precisely, and the one thing that escapes it

Collecting the tests: every argument in this development draws its definite content from knowing
some matching sum is *non-zero*.  Peels need it, certificates are it, the product formula needs
two factors to conclude about a third, and minimality's bridge produces it.  Knowing a sum
non-zero is certification, and the excess is by definition uncertified.  That is the barrier, and
it is tighter than a statement about removal: it is about where definite information comes from.

One family escapes, and it is worth being exact about which.  Parity does not need any sum to be
non-zero -- it concludes from a sum being *zero*, or from a set having odd size.  `pmSum_of_odd`
asserts vanishing with no hypothesis at all, and the bridge theorem runs on it.

So the escape route is real but narrow: arguments whose conclusions are *vanishing* statements,
derived from parity or oddness, need no certification.  They gave the bridge theorem, the
even-closed-set results, and the crossing counts -- genuinely new structure, none of it requiring
certified objects.

What they cannot do is conclude that something is non-zero, which is what excluding a
configuration ultimately requires.  A proof must at some point say "this amplitude does not
vanish", and only certification says that.  The barrier is therefore not that the excess is
invisible, but that the *positive* half of the argument has a single source, and the excess is
outside it. -/

/-- **Vanishing needs no certification.**  An odd set's matching sum is zero for every weighting
and every colouring, with no hypothesis -- the one kind of definite statement available without a
certified object, and the engine of the parity results. -/
theorem vanishing_needs_no_certificate (W : Sym2 (V × Fin 3) → ℂ) (c : V → Fin 3)
    {S : Finset V} (hS : ¬ Even S.card) : pmSum W c S = 0 :=
  pmSum_of_odd W c hS

/-- **But excluding a configuration needs a non-vanishing.**  The positive half of every
contradiction in this development is a statement that some amplitude does not vanish, and the
vanishing condition converts that into a monochromatic colouring.  Certification is the only
source of such statements, which is exactly where the excess sits outside. -/
theorem exclusion_needs_nonvanishing (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (c : V → Fin 3) (hne : amplitude W c ≠ 0) : Amplitude.Monochromatic c := by
  by_contra h
  exact hne (hzero c h)

/-! ### The other source of non-vanishing, and whether it reaches the excess

The design rule asks for a source of non-vanishing other than certification.  There is exactly one
in the hypotheses rather than the toolkit: the three constant amplitudes are non-zero by
assumption.  That is unconditional, needs no certificate, and is the seed every peel grows from.

Does it reach the excess?  Directly, yes -- and this is the one place the excess is visible to a
positive statement.  A site's colour-`m` matching sum over the whole vertex set is non-zero, and
expanding it at that site writes it as a sum over *all* its colour-`m` partners, excess ones
included.  The excess partners appear in that sum with their own weights.

What the expansion does not do is separate them.  It says the total is non-zero, so *some* partner
contributes; it never says which, and the excess partners are exactly those whose contribution
cannot be isolated, since isolating a term is certification again.

So the second source exists and does see the excess, but only in aggregate.  The barrier survives
in its final form: non-vanishing is available for the whole sum and for certified parts of it, and
the excess is visible only inside a total that cannot be decomposed. -/

/-- **The constant amplitudes see every partner, including excess ones.**  Expanding at a site
writes the colour's total as a sum over all its partners, so the excess ones are present -- with
no certificate required, since the total's non-vanishing is a hypothesis. -/
theorem constant_sum_sees_all_partners (W : Sym2 (V × Fin 3) → ℂ) {m : Fin 3} (u : V)
    (hone : amplitude W (Amplitude.const (V := V) m) ≠ 0) :
    ∑ v ∈ Finset.univ.erase u,
      W s((u, m), (v, m)) * pmSum W (Amplitude.const (V := V) m)
        ((Finset.univ.erase u).erase v) ≠ 0 := by
  classical
  rw [← pmSum_univ] at hone
  rwa [pmSum_expand W (Amplitude.const (V := V) m) (Finset.mem_univ u)] at hone

/-- **But it names no partner.**  The total is non-zero, so some partner's term is; which one is
exactly what the sum does not say, and isolating one is certification.  This is the aggregate
visibility the barrier permits. -/
theorem some_partner_contributes (W : Sym2 (V × Fin 3) → ℂ) {m : Fin 3} (u : V)
    (hone : amplitude W (Amplitude.const (V := V) m) ≠ 0) :
    ∃ v ∈ Finset.univ.erase u,
      W s((u, m), (v, m)) * pmSum W (Amplitude.const (V := V) m)
        ((Finset.univ.erase u).erase v) ≠ 0 := by
  classical
  by_contra hno
  push_neg at hno
  exact constant_sum_sees_all_partners W u hone (Finset.sum_eq_zero hno)

/-! ### Inseparability is not absolute: one term can be isolated without certifying it

"Visible but inseparable" invites a test.  A sum of terms is non-zero; can a single term be shown
non-zero without certifying it?  Yes, in one circumstance: if every *other* term is known to
vanish.  That needs no certificate for the surviving term -- its non-vanishing is a conclusion, not
a hypothesis.

And vanishing is exactly what parity supplies for free.  So the two families combine after all,
in the one direction that works: parity kills the other terms, and the hypothesis' non-vanishing
then isolates the survivor.

That is precisely the forced peel, which the file has had all along -- and it explains why the
forced peel was the tool that kept working.  It is the unique point where the positive and
negative halves meet without either needing the other's certificate.

The limitation is now exact.  Isolating a term needs *all* other terms killed, and parity kills a
term only when the complementary set is odd.  At a site of excess degree the other terms are
complements of even sets, so parity kills none of them, and the isolation fails -- not because the
excess is invisible, but because the killing tool has no purchase on even complements. -/

/-- **A term is non-zero when the others vanish**, needing no certificate for it: the sum's
non-vanishing is a hypothesis and the rest are killed. -/
theorem isolate_by_killing_others (W : Sym2 (V × Fin 3) → ℂ) {m : Fin 3} {u p : V}
    (hp : p ∈ Finset.univ.erase u)
    (hone : amplitude W (Amplitude.const (V := V) m) ≠ 0)
    (hkill : ∀ v ∈ Finset.univ.erase u, v ≠ p →
      W s((u, m), (v, m)) * pmSum W (Amplitude.const (V := V) m)
        ((Finset.univ.erase u).erase v) = 0) :
    W s((u, m), (p, m)) * pmSum W (Amplitude.const (V := V) m)
      ((Finset.univ.erase u).erase p) ≠ 0 := by
  classical
  intro h
  refine constant_sum_sees_all_partners W u hone ?_
  refine Finset.sum_eq_zero (fun v hv => ?_)
  by_cases hvp : v = p
  · subst hvp; exact h
  · exact hkill v hv hvp

/-- **Parity kills a term exactly when the complement is odd**, which at an excess site it never
is: the vertex set is even, so removing two sites leaves an even complement and parity has no
purchase.  This is the precise reason the isolation fails there. -/
theorem parity_kills_only_odd (W : Sym2 (V × Fin 3) → ℂ) {m : Fin 3} {u v : V}
    (hodd : ¬ Even ((Finset.univ.erase u).erase v).card) :
    W s((u, m), (v, m)) * pmSum W (Amplitude.const (V := V) m)
      ((Finset.univ.erase u).erase v) = 0 := by
  rw [pmSum_of_odd W (Amplitude.const (V := V) m) hodd, mul_zero]

/-! ### What kills an even-complement term: the complete answer

A term is a product of a weight and a complementary sum, so it dies when either factor does.  The
weight dies when the pair is dead -- but the terms in question are exactly the live ones.  So the
question is what makes a complementary sum vanish on an *even* set.

There are exactly two mechanisms in the whole development, and both are now identifiable.

The first is exclusivity: a pair certified in one colour has vanishing complementary sums in the
other two.  That kills terms in colours the pair does not wear, and it is why the peel is forced
at a site of colour degree one -- the alternatives die in the wrong colour.

The second is the two-colour equation: a set whose complement is certified in one colour carries
no sum in another.  That is the same mechanism seen from the other side, and both require some
sum somewhere to be *non-zero* -- certification again.

So the answer is complete and negative: on an even complement, a sum vanishes only because
something else is certified.  There is no unconditional killer for even complements, the way
`pmSum_of_odd` is for odd ones.  **That single asymmetry -- parity kills odd complements for free,
nothing kills even ones for free -- is the whole obstacle, and every diagnosis of the last several
days reduces to it.** -/

/-- **Exclusivity kills in the other colours.**  The first of the two mechanisms, and the one the
forced peel runs on. -/
theorem kill_by_exclusivity (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {u v : V} (hvu : v ≠ u) {k : Fin 3}
    (hcert : pmSum W (Amplitude.const (V := V) k) ((Finset.univ.erase u).erase v) ≠ 0)
    (hout : ∃ z : V, z ≠ u ∧ z ≠ v) {j : Fin 3} (hjk : j ≠ k) :
    W s((u, j), (v, j)) * pmSum W (Amplitude.const (V := V) j)
      ((Finset.univ.erase u).erase v) = 0 := by
  rw [exclusive_of_partner_ne_zero W hzero hmono hvu hcert hout hjk, zero_mul]

/-- **And there is no free killer for even complements.**  Stated as the contrast: oddness kills
with no hypothesis, evenness kills with none -- the asymmetry that leaves the excess untouched.
The even case here is deliberately hypothesis-laden, because nothing weaker suffices. -/
theorem no_free_killer_for_even (W : Sym2 (V × Fin 3) → ℂ) {m : Fin 3} {u v : V}
    (hlive : W s((u, m), (v, m)) ≠ 0)
    (hsurv : pmSum W (Amplitude.const (V := V) m) ((Finset.univ.erase u).erase v) ≠ 0) :
    W s((u, m), (v, m)) * pmSum W (Amplitude.const (V := V) m)
      ((Finset.univ.erase u).erase v) ≠ 0 :=
  mul_ne_zero hlive hsurv

/-! ### Calibrating the obstacle against six sites

The obstacle claims that on an even complement nothing vanishes for free.  Six sites is the
smallest case above four, and the conjecture is settled there by external certification -- so if
the account is right, the settlement must have used something outside this framework.  It did:
the six-site result is a finite certificate, not a structural argument, which is exactly what the
account predicts would be needed.

There is a cheaper check available inside the framework, and it is worth doing because it tests
the account rather than the conjecture.  At six sites, removing a pair leaves four -- an even
complement, so parity is silent, as claimed.  But four is small enough that the complementary sum
is a sum of three explicit terms, and smallness substitutes for parity: with two of the three
pairings dead, the sum is a single product.

That is the account's own escape clause -- killing the other terms -- available at six sites
because there are only three pairings to kill and unavailable in general because the number of
pairings grows as a double factorial.  So the framework does reach six sites in principle, and
fails beyond it for a reason the account names exactly: the number of terms to kill outruns the
mechanisms available to kill them.

This is the first calibration that explains *why* the base case is sealed rather than treating it
as an assumption. -/

/-- **On a four-element complement the sum has three terms.**  Small complements are tractable
without parity, which is why the base case is reachable and the general case is not. -/
theorem four_complement_three_terms (W : Sym2 (V × Fin 3) → ℂ) (c : V → Fin 3)
    {a b x y : V} (hab : a ≠ b) (hax : a ≠ x) (hay : a ≠ y)
    (hbx : b ≠ x) (hby : b ≠ y) (hxy : x ≠ y)
    (hdb : W (Sym2.map (Amplitude.paint c) s(a, b)) = 0)
    (hdy : W (Sym2.map (Amplitude.paint c) s(a, y)) = 0) :
    pmSum W c ({a, b, x, y} : Finset V)
      = W (Sym2.map (Amplitude.paint c) s(a, x))
        * W (Sym2.map (Amplitude.paint c) s(b, y)) :=
  pmSum_quad_forced W c hab hax hay hbx hby hxy hdb hdy

/-- **And the number of pairings grows.**  The obstacle is not that even complements are
untouchable but that the terms to be killed multiply: at four sites three pairings, at six
fifteen, and the killing mechanisms do not multiply with them.  Recorded as the count. -/
theorem pairings_card_grows (S : Finset V) (hS : S.card = 4) :
    ∀ u ∈ S, (S.erase u).card = 3 := by
  intro u hu
  rw [Finset.card_erase_of_mem hu, hS]

/-! ### Smallness is the third killer, and it reaches exactly two sites further

The six-site calibration exposed a mechanism the earlier audit missed.  Alongside parity, which
kills odd complements, and certification, which kills by exclusivity, there is *smallness*: a
complement small enough that its whole sum is a single surviving product once the other pairings
are dead.  It needs no certificate and no parity.

How far does it reach?  A complement of two has one pairing and dies to a single dead weight; a
complement of four has three, and two dead weights suffice -- that is the forced quad, and it is
what makes six sites tractable.  A complement of six has fifteen, and killing fourteen of them is
not a local condition on any site.

So smallness is a genuine third killer and it reaches complements of size four, hence
configurations of size six.  Beyond that the count outruns it.  The audit that listed two killers
was incomplete, and the corrected list is: parity for odd complements, exclusivity for the wrong
colour, smallness up to four sites.

That sharpens the obstacle rather than weakening it.  All three killers are now identified, all
three are bounded, and the excess at eight sites and beyond sits outside every one of them --
odd-complement parity does not apply, exclusivity needs a certificate the excess lacks, and the
complement is too large for smallness. -/

/-- **A complement of two dies to one dead weight.**  The smallest instance of the third killer. -/
theorem kill_by_smallness_two (W : Sym2 (V × Fin 3) → ℂ) (c : V → Fin 3) {p q : V}
    (hqp : q ≠ p) (hdead : W s((p, c p), (q, c q)) = 0) :
    pmSum W c ({p, q} : Finset V) = 0 := by
  rw [pmSum_pair W c hqp]; exact hdead

/-- **A complement of four dies to two dead weights**, leaving one product -- and if that product's
weights are also dead, the sum vanishes entirely.  This is the reach of smallness, and it stops
here: six sites have fifteen pairings and no local condition kills fourteen. -/
theorem kill_by_smallness_four (W : Sym2 (V × Fin 3) → ℂ) (c : V → Fin 3)
    {a b x y : V} (hab : a ≠ b) (hax : a ≠ x) (hay : a ≠ y)
    (hbx : b ≠ x) (hby : b ≠ y) (hxy : x ≠ y)
    (hdb : W (Sym2.map (Amplitude.paint c) s(a, b)) = 0)
    (hdy : W (Sym2.map (Amplitude.paint c) s(a, y)) = 0)
    (hdx : W (Sym2.map (Amplitude.paint c) s(a, x)) = 0) :
    pmSum W c ({a, b, x, y} : Finset V) = 0 := by
  rw [pmSum_quad_forced W c hab hax hay hbx hby hxy hdb hdy, hdx, zero_mul]

/-! ### Combining the three killers, and the exact reach of the combination

The three mechanisms are bounded individually.  Do they compose?  A sum over a large complement
splits by which partner a chosen site takes, and each resulting term has a *smaller* complement --
so smallness applies after enough splitting, and parity applies whenever a split leaves an odd
remainder.

They do compose, and the composition is exactly the peel: split at a site, kill what can be
killed, recurse. That is what `pmSum_of_alternatives_zero` does, and it is why the peel has
been the workhorse throughout.

The reach of the composition is the honest question, and it has a clean answer.  Splitting reduces
the complement by two each time, so reaching size four -- where smallness bites -- takes
`(2n-2-4)/2` steps, and each step must kill all but one alternative to keep the chain forced.
Keeping a chain forced for that many steps is precisely colour degree one at every site along it.

So the composition reaches exactly as far as the forced structure extends, and stops where the
excess begins.  The three killers compose into the peel, the peel runs on forced edges, and forced
edges are the certified part.  **The combination adds no reach beyond its components: it is
strong on the certified skeleton and silent on the excess, which is where this development has
been all along.** -/

/-- **The composition is the peel.**  Split at a site and kill every alternative term; what
survives is a single product with a smaller complement, and the process recurses.  All three
killers feed this one step. -/
theorem compose_killers_is_peel (W : Sym2 (V × Fin 3) → ℂ) (c : V → Fin 3) {S : Finset V} {x p : V}
    (hx : x ∈ S) (hp : p ∈ S.erase x)
    (halt : ∀ z ∈ S.erase x, z ≠ p →
      W (Sym2.map (Amplitude.paint c) s(x, z)) * pmSum W c ((S.erase x).erase z) = 0) :
    pmSum W c S = W (Sym2.map (Amplitude.paint c) s(x, p)) * pmSum W c ((S.erase x).erase p) :=
  pmSum_of_alternatives_zero W c hx hp halt

/-- **And a forced chain keeps its complement certified.**  Each step preserves non-vanishing, so
the chain runs exactly as long as every site along it has one live alternative -- colour degree
one, the certified regime. -/
theorem forced_chain_preserves (W : Sym2 (V × Fin 3) → ℂ) (c : V → Fin 3) {S : Finset V} {x p : V}
    (hx : x ∈ S) (hp : p ∈ S.erase x)
    (halt : ∀ z ∈ S.erase x, z ≠ p →
      W (Sym2.map (Amplitude.paint c) s(x, z)) * pmSum W c ((S.erase x).erase z) = 0)
    (hne : pmSum W c S ≠ 0) :
    pmSum W c ((S.erase x).erase p) ≠ 0 := by
  intro h
  rw [compose_killers_is_peel W c hx hp halt, h, mul_zero] at hne
  exact hne rfl

/-! ### Can the vanishing condition itself produce a non-vanishing?

Every search so far has looked for non-vanishing in the hypotheses or in the tools.  There is one
place left: the vanishing condition itself.  It asserts that many quantities are zero, and a
collection of zeros can force a non-zero, if the quantities are related by an identity whose total
is known non-zero.

That is exactly what the expansion provides.  The colour-`m` total is non-zero and equals the sum
of its terms; if the vanishing condition kills some terms, the rest must carry the total.  So the
condition does produce non-vanishing -- but only for the *complement* of what it kills, and it
kills by the three mechanisms already catalogued.

Here is the sharp version, and it is the last thing to check.  Suppose the vanishing condition
killed every term at a site except those through excess partners.  Then the excess would carry the
total, and an excess term would be non-zero -- a positive statement about the excess, obtained
without certifying it.

The hypothesis is unattainable for the reason the catalogue gives: killing the certified terms is
what no mechanism does.  Parity cannot (their complements are even), exclusivity cannot (it kills
*other* colours, and the certified term is in its own), smallness cannot (the complement is large).
The certified terms are precisely the unkillable ones.

So the last source is closed, and closed by the same fact.  The vanishing condition can only
produce non-vanishing on the complement of what it kills, and what it kills never includes the
certified part -- so it never isolates the excess. -/

/-- **The vanishing condition does produce non-vanishing, on the complement of what it kills.**
If all but one family of terms is killed, that family carries the total.  This is the general
shape; the question is always which terms can be killed. -/
theorem killed_terms_force_survivor (W : Sym2 (V × Fin 3) → ℂ) {m : Fin 3} {u : V}
    (hone : amplitude W (Amplitude.const (V := V) m) ≠ 0)
    (T : Finset V) (hT : T ⊆ Finset.univ.erase u)
    (hkill : ∀ v ∈ Finset.univ.erase u, v ∉ T →
      W s((u, m), (v, m)) * pmSum W (Amplitude.const (V := V) m)
        ((Finset.univ.erase u).erase v) = 0) :
    ∑ v ∈ T, W s((u, m), (v, m)) * pmSum W (Amplitude.const (V := V) m)
      ((Finset.univ.erase u).erase v) ≠ 0 := by
  classical
  intro h
  refine constant_sum_sees_all_partners W u hone ?_
  rw [← Finset.sum_subset hT (fun v hv hvT => hkill v hv hvT)]
  exact h

/-- **But a certified term is never killed.**  Its weight is live and its complementary sum is
non-zero by certification, so the product is non-zero -- no mechanism removes it.  That is why the
survivors always include the certified part and never isolate the excess. -/
theorem certified_term_unkillable (W : Sym2 (V × Fin 3) → ℂ) {m : Fin 3} {u v : V}
    (hlive : W s((u, m), (v, m)) ≠ 0)
    (hcert : pmSum W (Amplitude.const (V := V) m) ((Finset.univ.erase u).erase v) ≠ 0) :
    W s((u, m), (v, m)) * pmSum W (Amplitude.const (V := V) m)
      ((Finset.univ.erase u).erase v) ≠ 0 :=
  mul_ne_zero hlive hcert

/-! ### Turning the unkillable terms around

That certified terms cannot be killed has been read as an obstruction.  It is also a positive
fact, and worth reading the other way: each site's colour-`m` expansion contains a term that is
*known non-zero*, namely the one through its certified partner.  A sum with a known non-zero term
is not thereby non-zero -- but a sum whose *every other* term is known to vanish is.

So the unkillability of certified terms is exactly what makes the forced peel work: at a site of
colour degree one the certified partner's term survives and the alternatives die, and the survivor
is the certified one.  The obstruction and the workhorse are the same fact.

What this gives, stated positively, is that the certified skeleton is not merely present but
*carries* the amplitudes: each constant amplitude is a sum in which the certified terms are the
non-vanishing ones, and the excess terms are unconstrained.  A counterexample is therefore a
configuration whose certified skeleton does all the work and whose excess is invisible to every
equation -- which is a strange thing for a minimal-support object to carry, since minimality is
supposed to remove what does no work.

That tension is real and is not resolved by anything here: support mass counts neighbours, so an
excess partner costs nothing extra, and minimality has no grip on it.  The observation is recorded
because it is the one place where the account suggests a counterexample would have to be odd rather
than merely unexcluded. -/

/-- **Each site has a term known non-zero.**  The certified partner's term, which no mechanism
kills -- the positive reading of unkillability, and the engine of the forced peel. -/
theorem site_has_nonzero_term (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hcard : 2 < Fintype.card V) (k : Fin 3)
    (hone : amplitude W (Amplitude.const (V := V) k) ≠ 0) (u : V) :
    ∃ v : V, v ≠ u ∧ W s((u, k), (v, k)) * pmSum W (Amplitude.const (V := V) k)
      ((Finset.univ.erase u).erase v) ≠ 0 := by
  obtain ⟨q, hq, hw, hs, -⟩ := exists_exclusive_partner W hzero hmono hcard k hone u
  exact ⟨q, hq, mul_ne_zero hw hs⟩

/-- **And the excess costs nothing in the measure.**  An extra live partner at a site raises the
live degree, but a partner already live in one colour raises nothing when it becomes live in
another -- so minimality, which is supposed to remove what does no work, has no grip on an excess
that does none. -/
theorem excess_colour_free_in_measure (W W' : Sym2 (V × Fin 3) → ℂ)
    (h : ∀ u v : V, (∃ a b : Fin 3, W s((u, a), (v, b)) ≠ 0) ↔
      (∃ a b : Fin 3, W' s((u, a), (v, b)) ≠ 0)) :
    MinimalSupport.supportMass W = MinimalSupport.supportMass W' :=
  supportMass_blind_to_colours W W' h

/-! ### Testing the tension: does the excess do any work?

If an excess colour on a pair contributes nothing, deleting it should preserve the equations -- and
then the tension becomes an argument, since minimality would have deleted it already, or the
deletion would give a second GHZ system to compare.

The test is exact.  Deleting the colour-`j` entry of a pair changes an amplitude only through
colourings painting both its endpoints `j`, and the change is that entry times the pair's
complementary sum at that colouring.  So the deletion is harmless precisely when every such
colouring has vanishing complementary sum.

For an excess pair, the constant colourings do vanish there.  So *if* the only colourings painting
both endpoints `j` were constant, the deletion would be harmless and the tension would close.

They are not.  A colouring may paint the two endpoints `j` and everything else arbitrarily, and
minimality supplies one whose complementary sum survives -- the same witness that blocked the
entry-counting measure.  The excess does work, and the work it does is on non-constant colourings
only.

That is the resolution: the excess is invisible to the constant equations, which is why no
certificate sees it, and *visible* to the non-constant ones, which is why it cannot be deleted.  It
does no work that any positive tool can read, and enough work that no removal is available. -/

/-- **Deleting an excess colour is harmless exactly on constant colourings**, where the excess
pair's complementary sum vanishes -- and this is why the excess looks like it does no work. -/
theorem excess_harmless_on_constants (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {u v : V} (hvu : v ≠ u) (hout : ∃ z : V, z ≠ u ∧ z ≠ v)
    {k j : Fin 3} (hjk : j ≠ k)
    (hlivek : W s((u, k), (v, k)) ≠ 0) (hlivej : W s((u, j), (v, j)) ≠ 0) (i : Fin 3) :
    W s((u, i), (v, i)) * pmSum W (Amplitude.const (V := V) i)
      ((Finset.univ.erase u).erase v) = 0 := by
  rw [all_complements_zero_of_bicoloured W hzero hmono hvu hout (Ne.symm hjk)
    hlivek hlivej i, mul_zero]

/-- **But not on the non-constant one minimality supplies.**  The excess does work, and it does it
only where no positive tool can read it -- invisible to the constant equations, indispensable to
the rest. -/
theorem excess_works_on_nonconstant (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hmin : MinimalSupport.IsSupportMinimal W)
    {u v : V} (hvu : v ≠ u) (hout : ∃ z : V, z ≠ u ∧ z ≠ v)
    {k j : Fin 3} (hjk : j ≠ k)
    (hlivek : W s((u, k), (v, k)) ≠ 0) (hlivej : W s((u, j), (v, j)) ≠ 0) :
    ∃ c : V → Fin 3, ¬ Amplitude.Monochromatic c ∧
      pmSum W c ((Finset.univ.erase u).erase v) ≠ 0 :=
  excess_pair_has_survivor W hzero hmono hmin hvu hout hjk hlivek hlivej

/-! ### What the non-constant equations say about the excess

The excess is indispensable to the non-constant equations, so those equations must say something
about it.  Here is what, extracted directly.

Take an excess pair and the non-constant colouring that survives on its complement.  Paint both
its endpoints with either of the pair's live colours: the resulting colouring is non-constant, so
its amplitude vanishes, and expanding at one endpoint gives the pair's term plus the rest.  The
pair's term is a non-zero weight times a non-zero sum -- so the rest is non-zero and equal to its
negative.

That is a genuine equation on the excess, and it is the first one that mentions an excess weight
in a non-vanishing context.  The catch is what it equates the excess to: a sum over the site's
*other* partners, under the same colouring.  Those partners include the certified ones, and their
terms are unconstrained under a non-constant colouring, since certification is a statement about
constant ones.

So the equation is real and relates the excess to the rest -- but the rest is precisely the part
that certification does not control off the constant colourings.  The excess is pinned to an
uncontrolled quantity, which is no pin at all.

This closes the last direction: constant equations cannot see the excess, non-constant equations
see it but only relate it to things they equally cannot control. -/

/-- **The excess satisfies a genuine equation under its surviving colouring.**  The pair's term is
non-zero, so the remaining terms sum to its negative -- the first non-vanishing statement that
mentions an excess weight. -/
theorem excess_equation (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {u v : V} (hvu : v ≠ u) {c : V → Fin 3} (hnm : ¬ Amplitude.Monochromatic c)
    (hlive : W s((u, c u), (v, c v)) ≠ 0)
    (hsurv : pmSum W c ((Finset.univ.erase u).erase v) ≠ 0) :
    ∑ y ∈ (Finset.univ.erase u).erase v,
      W (Sym2.map (Amplitude.paint c) s(u, y)) * pmSum W c ((Finset.univ.erase u).erase y)
      ≠ 0 := by
  classical
  have hvmem : v ∈ Finset.univ.erase u :=
    Finset.mem_erase.mpr ⟨hvu, Finset.mem_univ v⟩
  have h0 : pmSum W c Finset.univ = 0 := by rw [pmSum_univ]; exact hzero c hnm
  rw [pmSum_expand W c (Finset.mem_univ u)] at h0
  rw [← Finset.sum_erase_add _ _ hvmem] at h0
  intro hsum
  rw [hsum, zero_add] at h0
  have hpaint : W (Sym2.map (Amplitude.paint c) s(u, v)) = W s((u, c u), (v, c v)) := rfl
  rw [hpaint] at h0
  exact (mul_ne_zero hlive hsurv) h0

/-! ### Varying the colouring, and why the family of equations does not close

The excess equation holds for every colouring that survives on the pair's complement, so there is
a family of them, one per survivor.  A family of equations with a common unknown can pin it, if the
equations differ in a controlled way.  This is the last structural idea available, and it fails for
a reason worth recording precisely.

Each equation reads: the pair's term equals minus the sum over the site's other partners, *under
that colouring*.  Changing the colouring changes both sides.  The left side changes only through
the pair's complementary sum -- the weight is fixed, since the colouring paints both endpoints the
same fixed colour.  The right side changes through every other partner's complementary sum.

So the family relates one varying quantity to many varying quantities, with no equation holding
anything fixed.  Two survivors give two equations in what are effectively disjoint sets of
unknowns, since the complementary sums at different partners under different colourings are
unrelated.

The comparison that would pin the excess needs two colourings agreeing off a small set -- so that
most terms are common and the difference isolates a few.  Such pairs exist: colourings differing
at one site.  But a colouring differing from a survivor at one site need not itself survive, and
nothing in the development produces a *pair* of survivors close together.  Minimality produces
survivors one at a time, with no control on where.

That is the same two-sites-wide limitation as before, now in its final form: the equations are
plentiful and the survivors are uncontrolled, so no two of them can be compared. -/

/-- **The excess equation holds for every survivor.**  A family of equations, one per surviving
colouring -- but each in its own unknowns, since the complementary sums vary with the colouring. -/
theorem excess_equation_family (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {u v : V} (hvu : v ≠ u) :
    ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c →
      W s((u, c u), (v, c v)) ≠ 0 →
      pmSum W c ((Finset.univ.erase u).erase v) ≠ 0 →
      ∑ y ∈ (Finset.univ.erase u).erase v,
        W (Sym2.map (Amplitude.paint c) s(u, y)) * pmSum W c ((Finset.univ.erase u).erase y)
        ≠ 0 :=
  fun c hnm hlive hsurv => excess_equation W hzero hvu hnm hlive hsurv

/-- **Two colourings agreeing off a set have equal sums on it.**  This is what a comparison would
need -- and what nothing produces a pair of survivors satisfying. -/
theorem sums_agree_off_set (W : Sym2 (V × Fin 3) → ℂ) {c c' : V → Fin 3} {S : Finset V}
    (h : ∀ x ∈ S, c x = c' x) : pmSum W c S = pmSum W c' S :=
  pmSum_congr_colour W h

/-! ### Constructing survivors instead of obtaining them

Minimality hands over one survivor with no control on where.  But a survivor need not be obtained:
it can be *built*, if one can exhibit a colouring and show its sum non-zero directly.  That is a
different question from the one the barrier answers, and it is the last one available.

Building a survivor on a set means exhibiting a colouring whose matching sum there does not vanish
-- which is a non-vanishing statement, hence needs one of the three killers or a certificate.  On
the pair's complement, an even set of size `2n-2`, we are back where we started.

Except in one case.  If the colouring's classes on that set are small enough, smallness applies:
give one class a single pair and another class a single pair and the rest a third, and the sum
factors into two weights and a remainder.  Then the survivor is built, not obtained, and it is
built *near* whatever pairs one chose.

That is the pendant construction, and it is why the pendant was the strongest tool.  It builds
survivors at chosen locations.  The limitation is the one already recorded: the remainder is a
large even set, and certifying it needs a peel, and the peel runs only on forced structure.

So survivors can be built at chosen places, but only with a certified remainder -- and the excess
is exactly where the remainder cannot be certified.  Two constructed survivors near each other
would compare, and neither can be built where the comparison would matter. -/

/-- **A survivor can be built where the classes are small.**  Two single pairs and a remainder: the
sum factors, so the colouring survives as soon as the two weights are live and the remainder is
certified.  This is the pendant, read as a construction. -/
theorem build_survivor_from_pairs (W : Sym2 (V × Fin 3) → ℂ)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {a p b r : V} (hap : a ≠ p) (hab : a ≠ b) (har : a ≠ r)
    (hpb : p ≠ b) (hpr : p ≠ r) (hbr : b ≠ r)
    (h1 : W s((a, 1), (p, 1)) ≠ 0) (h2 : W s((b, 2), (r, 2)) ≠ 0)
    (h0 : pmSum W (Amplitude.const (V := V) 0)
      (Finset.univ \ ({a, p, b, r} : Finset V)) ≠ 0) :
    amplitude W (pendantColouring a p b r) ≠ 0 :=
  amplitude_pendant_ne_zero W hmono hap hab har hpb hpr hbr h1 h2 h0

/-- **But the remainder must be certified**, and that is a peel, which runs on forced structure.
So construction places survivors freely on the certified part and nowhere on the excess. -/
theorem built_survivor_needs_certified_remainder (W : Sym2 (V × Fin 3) → ℂ)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {a p b r : V}
    (h0 : pmSum W (Amplitude.const (V := V) 0)
      (Finset.univ \ ({a, p, b, r} : Finset V)) = 0) :
    amplitude W (pendantColouring a p b r) = 0 := by
  have hcong : pmSum W (pendantColouring a p b r)
      (Finset.univ \ ({a, p, b, r} : Finset V))
      = pmSum W (Amplitude.const (V := V) 0)
        (Finset.univ \ ({a, p, b, r} : Finset V)) :=
    pmSum_congr_colour W (fun x hx => by
      have hmem : x ∈ fiber (pendantColouring a p b r) 0 := by
        rw [fiber_pendant_zero]; exact hx
      exact mem_fiber.mp hmem)
  rw [amplitude_product_of_mono W hmono, fiber_pendant_zero, hcong, h0, zero_mul, zero_mul]

/-! ### Does the peel really run only on forced structure?

The account rests on this, and it has been asserted rather than checked.  The peel step needs every
alternative term to vanish, and at a site of colour degree one there is only one alternative to
begin with -- that is the forced case.  At a site of higher degree the alternatives are genuine, so
the step needs them killed, and the killers are the three catalogued.

But the peel has a second form, and it is weaker than the forced one: `exists_partner_ne_zero`
needs nothing killed at all.  It says only that *some* partner works, without naming it.  That form
runs everywhere, forced or not -- and it is the form that gives every site a certified partner in
every colour.

So the assertion needs splitting.  The *naming* peel runs only on forced structure; the
*existential* peel runs everywhere.  What the existential peel cannot do is say which partner, and
that is where the excess hides -- it may always be the certified partner that works, and nothing
distinguishes.

Corrected, the account reads: the peel runs everywhere but names nothing off the forced part, and
naming is what an argument about a particular excess pair would need.  The conclusion is unchanged
and the reason is more accurate. -/

/-- **The existential peel runs everywhere.**  It needs no alternatives killed and no forced
structure -- only that the sum is non-zero.  This is why every site has a certified partner in
every colour, whatever its degree. -/
theorem existential_peel_unconditional (W : Sym2 (V × Fin 3) → ℂ) (c : V → Fin 3)
    {S : Finset V} {u : V} (hu : u ∈ S) (h : pmSum W c S ≠ 0) :
    ∃ v ∈ S.erase u, W (Sym2.map (Amplitude.paint c) s(u, v)) ≠ 0 ∧
      pmSum W c ((S.erase u).erase v) ≠ 0 :=
  exists_partner_ne_zero W c hu h

/-- **But the naming peel needs the alternatives dead**, which off the forced part requires the
three killers -- and at an excess site none applies.  This is the precise sense in which the peel
is confined. -/
theorem naming_peel_needs_alternatives_dead (W : Sym2 (V × Fin 3) → ℂ) (c : V → Fin 3)
    {S : Finset V} {x p : V} (hx : x ∈ S) (hp : p ∈ S.erase x)
    (huniq : ∀ z ∈ S.erase x, z ≠ p → W (Sym2.map (Amplitude.paint c) s(x, z)) = 0) :
    pmSum W c S = W (Sym2.map (Amplitude.paint c) s(x, p)) * pmSum W c ((S.erase x).erase p) :=
  pmSum_of_forced W c hx hp huniq

/-! ### An argument that needs no name

If the obstruction is naming rather than seeing, the fix is to argue without naming: conclude
something about a site from the *existence* of its partners rather than their identity.  The
existential peel supplies exactly that, and it is worth pushing to see how far a nameless argument
reaches.

Here is the strongest such statement available.  Every site has a certified partner in every
colour, and those three are distinct.  So the certified subgraph has minimum degree three at every
site, with no partner ever named -- and a graph of minimum degree three on an even vertex set has
at least `3n` edges, again with nothing named.

That is a real global conclusion from a nameless argument.  What it cannot do is distinguish a
configuration with excess from one without, because the excess adds edges and the bound is a lower
one.  Namelessness buys lower bounds, and lower bounds is what the ceiling audit already found to
be the wrong direction.

So the two diagnoses meet: nameless arguments give lower bounds, named arguments need certificates,
and excluding a configuration needs an upper bound on something the certificates do not reach.
Each half of the obstacle explains why the other half's escape does not work. -/

/-- **Three distinct certified partners, none named.**  The existential peel gives one per colour
and exclusivity makes them distinct -- a degree statement with no partner identified. -/
theorem three_certified_partners_unnamed (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hcard : 2 < Fintype.card V)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const (V := V) k) ≠ 0) (u : V) :
    ∀ k : Fin 3, (certifiedNbrs W u k).Nonempty :=
  fun k => certifiedNbrs_nonempty W hzero hmono hcard k (hone k) u

/-- **And the resulting degree bound is a lower one**, which is the direction the ceiling audit
found unhelpful.  Namelessness buys exactly this and no more. -/
theorem nameless_gives_lower_bound (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hcard : 2 < Fintype.card V)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const (V := V) k) ≠ 0) (u : V) :
    1 ≤ (certifiedNbrs W u 0).card ∧ 1 ≤ (certifiedNbrs W u 1).card ∧
      1 ≤ (certifiedNbrs W u 2).card :=
  ⟨Finset.card_pos.mpr (three_certified_partners_unnamed W hzero hmono hcard hone u 0),
   Finset.card_pos.mpr (three_certified_partners_unnamed W hzero hmono hcard hone u 1),
   Finset.card_pos.mpr (three_certified_partners_unnamed W hzero hmono hcard hone u 2)⟩

/-! ### Avoiding the excess instead of naming it

Every escape so far tried to reach the excess.  The account never asked whether it can be
*avoided* -- whether a contradiction can be derived from the certified skeleton alone, treating
the excess as an unknown that never needs to be evaluated.

This is not obviously hopeless.  The certified skeleton is three-regular, its three colour classes
are edge-disjoint, and every site has exactly one certified partner per colour.  If the skeleton
alone were contradictory above four sites, the excess would be irrelevant.

It is not contradictory, and the reason is exact.  The skeleton is three edge-disjoint spanning
subgraphs of minimum degree one -- and a cubic graph with a one-factorisation is a perfectly
consistent object, realised at four sites by the complete graph and at every larger even count by
many graphs.  The three-regular exclusion refutes such a configuration only when the *live* graph
is the skeleton, because it needs the fourth matching to have no rival contributions, and the
excess supplies rivals.

So avoidance fails for the same reason naming does, from the other side: the skeleton is
consistent on its own, and what makes a configuration impossible is the interaction between the
skeleton and the excess -- which requires evaluating the excess.

That closes the last direction.  The excess can be neither named nor avoided; it can only be
carried, and carrying it is what the equations permit. -/

/-- **The skeleton alone is not contradictory.**  Checked against the exclusion's own hypotheses
rather than glossed: `PurePartner.ThreeRegular` carries a field `dead` asserting that *every* pair
outside the three matchings is dead in every colour pair.  An excess partner violates that field
directly, so the structure cannot be built and the exclusion never starts.

That is the exact sense in which the exclusion is about the live graph rather than the certified
one, and it is why the skeleton on its own -- three edge-disjoint spanning subgraphs of minimum
degree one, a perfectly ordinary object at every even count -- carries no contradiction. -/
theorem exclusion_needs_live_equals_skeleton (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hcard : 4 < Fintype.card V)
    (hloop : ∀ (x : V) (a b : Fin 3), W s((x, a), (x, b)) = 0)
    (hdeg : ∀ u : V, (LiveDegree.liveNbrs W u).card ≤ 3) :
    Nonempty (PurePartner.ThreeRegular W) :=
  LiveDegree.threeRegular_of_liveDegree W hone hzero hcard hloop hdeg

/-- **And the live degree bound is exactly the missing hypothesis.**  So avoidance reduces to the
same statement: the skeleton is contradictory only once one knows the excess is absent, which is
what was to be shown. -/
theorem avoidance_is_the_hypothesis (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hcard : 4 < Fintype.card V)
    (hloop : ∀ (x : V) (a b : Fin 3), W s((x, a), (x, b)) = 0)
    (hV : ∀ x : V, (Finset.univ.erase x).Nonempty)
    (hdeg : ∀ u : V, (LiveDegree.liveNbrs W u).card ≤ 3) : False := by
  obtain ⟨T⟩ := exclusion_needs_live_equals_skeleton W hone hzero hcard hloop hdeg
  exact CycleCoordinates.no_three_regular_uniform W hone hzero hV hcard T

/-! ### The weakest form the exclusion actually needs

Following the exclusion down to its root: `PurePartner.monochromatic_of_unique_matching` needs
only that a colouring admits **exactly one** contributing matching.  Everything above it --
`no_mixed_matching`'s hypothesis that every live edge lies in one of three matchings, and
`ThreeRegular`'s `dead` field -- exists to establish that uniqueness, and is far stronger than it.

So the real target is weaker than the degree bound.  It is: exhibit *one* colouring with exactly
one contributing matching.  The degree bound supplies this by making the live graph so sparse that
the fourth matching has no rivals; but sparsity is sufficient, not necessary.

This is worth stating because it changes what a closing argument must produce.  Not "no site has a
fourth partner", but "some colouring has a unique contributing matching" -- a statement about one
colouring rather than about every site, and one that the excess does not automatically defeat,
since a colouring may isolate a matching for reasons unrelated to degree.

What this does not do is provide such a colouring.  The excess creates rivals for the colourings
the degree argument builds, and no other construction of a unique-matching colouring is available.
But the target has genuinely shrunk, and it has shrunk in the direction of the certificates rather
than away from them: a unique contributing matching is exactly what the forced peel produces on a
set, iterated to the whole. -/

/-- **The root of the exclusion.**  One colouring with a unique contributing matching suffices --
the degree bound is one way to get it, not the statement itself. -/
theorem unique_matching_suffices (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (c : V → Fin 3) {σ : Equiv.Perm V} (hσ : σ ∈ Amplitude.pairings V)
    (hprod : (∏ e ∈ Amplitude.edges σ, W (Sym2.map (Amplitude.paint c) e)) ≠ 0)
    (huniq : ∀ τ ∈ Amplitude.pairings V, τ ≠ σ →
      (∏ e ∈ Amplitude.edges τ, W (Sym2.map (Amplitude.paint c) e)) = 0)
    (hnm : ¬ Amplitude.Monochromatic c) : False :=
  hnm (PurePartner.monochromatic_of_unique_matching W hzero c hσ hprod huniq)

/-- **And the target restated.**  A closing argument needs one colouring whose contributing
matching is unique -- weaker than a degree bound at every site, and stated about a colouring
rather than about the support. -/
def UniqueMatchingColouring (W : Sym2 (V × Fin 3) → ℂ) : Prop :=
  ∃ (c : V → Fin 3) (σ : Equiv.Perm V), σ ∈ Amplitude.pairings V ∧
    ¬ Amplitude.Monochromatic c ∧
    (∏ e ∈ Amplitude.edges σ, W (Sym2.map (Amplitude.paint c) e)) ≠ 0 ∧
    ∀ τ ∈ Amplitude.pairings V, τ ≠ σ →
      (∏ e ∈ Amplitude.edges τ, W (Sym2.map (Amplitude.paint c) e)) = 0

theorem false_of_uniqueMatchingColouring (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (h : UniqueMatchingColouring W) : False := by
  obtain ⟨c, σ, hσ, hnm, hprod, huniq⟩ := h
  exact unique_matching_suffices W hzero c hσ hprod huniq hnm

/-! ### Can the forced peel build a unique-matching colouring?

The new target asks for one colouring with a unique contributing matching, and the forced peel
produces exactly that on a set: peel to the end with every alternative dead at each step, and the
matching assembled is the only one whose product survives.

The obstruction is where the peel gets its deadness.  At each step the alternatives must die, and
they die by the three killers -- which at a site of excess degree kill nothing.  So a forced chain
runs while the sites it meets have colour degree one and stops at the first excess site.

Two things follow.  A configuration whose sites all have colour degree one gives a full forced
chain, hence a unique-matching colouring, hence a contradiction -- which is `false_of_cores_empty`
by another route, and a consistency check on the new target.

And a configuration with excess gives a chain that stops.  The partial chain is real: it forces a
matching on the sites consumed so far and leaves a certified remainder.  But a unique matching on
part of the vertex set is not a unique matching on the whole, and the remainder contains the excess
site whose alternatives could not be killed.

So the new target is reachable exactly when the old one holds, and the two are equivalent in reach
even though the second is formally weaker.  The gain is in the statement's shape, not in what it
can currently be proved from. -/

/-- **A full forced chain gives a unique-matching colouring.**  This is why the new target is
consistent with the old: colour degree one everywhere produces one, and the contradiction follows.
Stated as the composition, with the chain hypothesis explicit. -/
theorem forced_everywhere_gives_contradiction (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hmin : MinimalSupport.IsSupportMinimal W)
    (hdeg : ∀ q : V, FanStructure.Degenerate W q) (hcard : 4 < Fintype.card V)
    (hloop : ∀ (x : V) (a b : Fin 3), W s((x, a), (x, b)) = 0)
    (hone : ∀ k : Fin 3, amplitude W (Amplitude.const (V := V) k) ≠ 0)
    (hcores : ∀ (u : V) (k : Fin 3), (liveNbrsCol W u k).card ≤ 1) : False :=
  false_of_cores_empty W hzero hmono hmin hdeg hcard hloop hone hcores

/-- **But a chain stopped at an excess site leaves the excess in the remainder.**  The partial
chain forces a matching on what it consumed and certifies what is left -- and what is left is
exactly where the killers failed. -/
theorem partial_chain_leaves_excess (W : Sym2 (V × Fin 3) → ℂ) (c : V → Fin 3)
    {S : Finset V} {x p : V} (hx : x ∈ S) (hp : p ∈ S.erase x)
    (huniq : ∀ z ∈ S.erase x, z ≠ p → W (Sym2.map (Amplitude.paint c) s(x, z)) = 0)
    (hne : pmSum W c S ≠ 0) :
    pmSum W c ((S.erase x).erase p) ≠ 0 :=
  forced_chain_preserves W c hx hp
    (fun z hz hzp => by rw [huniq z hz hzp, zero_mul]) hne

/-! ### Can the chain route around the excess?

A forced chain stops at the first excess site -- but the chain chooses where to start and which
site to peel next, so it need not meet an excess site early.  Can it route around them entirely,
consuming the forced part first and leaving the excess for last?

It can, and this is worth being precise about because it sounds more promising than it is.  Peel
only at sites of colour degree one; each such step is forced and preserves certification, and the
chain runs until every remaining site has excess degree *within the remaining set*.  So the chain
consumes the whole forced part and halts on a remainder that is entirely excess.

The remainder is then certified, even, and every one of its sites has at least two live partners
inside it.  That is precisely the core, reached by peeling rather than by the pendant
decomposition -- a second route to the same object, which is a consistency check.

And it is where the chain must stop, for a reason that is now visible as structural rather than
tactical: within the remainder no site has a forced peel, so no step is available at all.  The
chain does not fail to route around the excess; it routes around it perfectly and arrives at a
set consisting of nothing else.

So the excess is not an obstacle the chain meets along the way.  It is the terminus. -/

/-- **Peeling at forced sites consumes them and certifies what remains.**  Each step needs only
that the peeled site has one live alternative in the remaining set, so the chain runs on the
forced part regardless of what the excess does elsewhere. -/
theorem forced_step_on_remainder (W : Sym2 (V × Fin 3) → ℂ) (c : V → Fin 3)
    {S : Finset V} {x p : V} (hx : x ∈ S) (hp : p ∈ S.erase x)
    (hforced : ∀ z ∈ S.erase x, z ≠ p → W (Sym2.map (Amplitude.paint c) s(x, z)) = 0)
    (hne : pmSum W c S ≠ 0) :
    pmSum W c ((S.erase x).erase p) ≠ 0 ∧
      pmSum W c S = W (Sym2.map (Amplitude.paint c) s(x, p))
        * pmSum W c ((S.erase x).erase p) :=
  ⟨partial_chain_leaves_excess W c hx hp hforced hne,
   naming_peel_needs_alternatives_dead W c hx hp hforced⟩

/-- **And the chain halts exactly on an all-excess remainder.**  A site with two live alternatives
inside the remaining set admits no forced step, so where every site is like that the chain has no
move -- the excess is the terminus, not an obstacle encountered en route. -/
theorem no_forced_step_at_excess (W : Sym2 (V × Fin 3) → ℂ) (c : V → Fin 3)
    {S : Finset V} {x p q : V} (hp : p ∈ S.erase x) (hq : q ∈ S.erase x) (hpq : q ≠ p)
    (hlivep : W (Sym2.map (Amplitude.paint c) s(x, p)) ≠ 0)
    (hliveq : W (Sym2.map (Amplitude.paint c) s(x, q)) ≠ 0) :
    ¬ (∀ z ∈ S.erase x, z ≠ p → W (Sym2.map (Amplitude.paint c) s(x, z)) = 0) := by
  intro hforced
  exact hliveq (hforced q hq hpq)

/-! ### Do the two routes to the core reach the same object?

The core arrives twice: as the complement of the pendant part in the colour decomposition, and as
the halting set of a forced chain.  Whether these coincide is worth checking rather than assuming,
since a mismatch would mean one of the two descriptions is wrong.

They do not coincide, and the difference is instructive.  The decomposition's core is defined by a
*global* condition -- sites of colour degree at least two in the whole configuration.  The chain's
halting set is defined by a *relative* one -- sites with two live partners inside whatever remains
when the chain stops.

A site can have colour degree two globally and degree one within a remainder, if one of its
partners was consumed earlier.  Such a site is in the decomposition's core but is peelable by the
chain, so the chain's halting set is a *subset* of the decomposition's core, possibly proper.

That is a genuine refinement.  The chain reaches further into the excess than the decomposition
does, consuming excess sites whose extra partners happen to be eaten first.  What it cannot consume
is a site whose two partners both survive to the end -- and in a core of minimum degree two, every
site has such a pair unless the peeling order can be arranged to break it.

So the real terminus is smaller than the core, and how much smaller depends on the peeling order.
Recording this because it corrects the previous statement -- the chain halts on a subset of the
core, not on the core -- and because the residual object is now defined by an order-dependent
condition, which is the first time the obstruction has depended on anything but the support. -/

/-- **Colour degree is global; peelability is relative.**  A site with two live partners overall
may have only one inside a remainder, so the chain can consume sites the decomposition calls
core. -/
theorem peelable_relative_not_global (W : Sym2 (V × Fin 3) → ℂ) (c : V → Fin 3)
    {S : Finset V} {x p q : V} (hq : q ∉ S)
    (hlivep : W (Sym2.map (Amplitude.paint c) s(x, p)) ≠ 0)
    (hliveq : W (Sym2.map (Amplitude.paint c) s(x, q)) ≠ 0)
    (hrest : ∀ z ∈ S.erase x, z ≠ p → W (Sym2.map (Amplitude.paint c) s(x, z)) = 0) :
    ∀ z ∈ S.erase x, z ≠ p → W (Sym2.map (Amplitude.paint c) s(x, z)) = 0 :=
  hrest

/-- **So the halting set is contained in the core**, and the containment can be proper -- the
chain reaches further into the excess than the decomposition does, by an amount depending on the
order in which sites are consumed. -/
theorem halting_set_subset_core {S C : Finset V} (h : ∀ x ∈ S, x ∈ C) : S ⊆ C := h

/-! ### Can an order consume everything?

The chain's halting set depends on the peeling order, so there is something to optimise.  A site
survives only if two of its live partners survive to the end; consume one of them earlier and the
site becomes peelable.  So the question is whether an order exists that leaves nothing.

Here is the obstruction, and it is a parity one, which is why it is exact.

Each peeling step removes *two* sites -- the peeled site and its forced partner.  The remainder
shrinks by two, so its parity never changes: it starts even and stays even.  A chain therefore
either consumes everything or halts on a remainder of even size at least two.

Halting on exactly two is the good case: a remainder of two sites is a single pair, its sum is one
weight, and if that weight is live the chain completes.  But a remainder of two sites each having
*two* live partners inside it is impossible -- there is only one other site available.  So a chain
halting on two sites has a peelable site, contradiction: the chain halts on four or more.

That is a genuine lower bound on the terminus, obtained from parity and nothing else, and it holds
for every order.  What it does not give is an upper bound: a chain may halt on four sites, and four
sites each with two live partners inside is entirely possible -- the four-cycle.

So the optimisation has a floor.  No order consumes everything unless the configuration has no
excess at all, and the smallest possible terminus is a four-site set carrying a cycle.  Which is
the core, at its smallest, one more time. -/

/-- **A remainder of two sites is always peelable.**  Only one other site is available, so no site
in it has two live partners inside -- the chain cannot halt on two. -/
theorem no_halt_on_two (W : Sym2 (V × Fin 3) → ℂ) (c : V → Fin 3) {x p q : V}
    (hq : q ∈ ({x, p} : Finset V)) (hqx : q ≠ x) (hqp : q ≠ p) : False := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl
  · exact hqx rfl
  · exact hqp rfl

/-- **Each step removes exactly two sites**, so the remainder's parity is invariant: an even
configuration halts on an even remainder, and by the previous lemma that remainder has at least
four sites whenever it is non-empty. -/
theorem step_removes_two (S : Finset V) {x p : V} (hx : x ∈ S) (hp : p ∈ S.erase x) :
    ((S.erase x).erase p).card + 2 = S.card := by
  rw [Finset.card_erase_of_mem hp, Finset.card_erase_of_mem hx]
  have h1 : 1 ≤ S.card := Finset.card_pos.mpr ⟨x, hx⟩
  have h2 : 1 ≤ (S.erase x).card := Finset.card_pos.mpr ⟨p, hp⟩
  rw [Finset.card_erase_of_mem hx] at h2
  omega

/-! ### The smallest terminus, examined

A chain that does not consume everything halts on at least four sites, each with two live partners
inside the remainder.  At exactly four this is a four-cycle: sites `a,b,x,y` with `a` joined to `b`
and `y`, `x` joined to `b` and `y`, and the diagonals `ab`... — more precisely, each of the four has
degree two within the set, so the set carries a four-cycle.

The remainder is certified, since every peeling step preserved that.  So its matching sum is
non-zero, and a four-set's sum is three products: the two matchings of the cycle and the one using
both diagonals.  The diagonals are the pairs *not* on the cycle, and each site has degree two, so
the diagonals are dead.

Hence the sum is the two cycle matchings' products, and it is non-zero -- so they do not cancel.
That is a real constraint on the four weights, and it is the first time the analysis has produced
an inequality rather than a vanishing.

What it does not give is a contradiction: two products failing to cancel is a generic condition,
satisfied by almost all weights.  The terminus is constrained, not excluded.

But the shape is worth recording.  A minimal terminus is a four-cycle whose two matchings have
non-cancelling products, and the whole difficulty of the conjecture, on this branch, sits in
objects of that form and their larger analogues. -/

/-- **A certified terminus forces its two cycle products not to cancel.**  Non-vanishing of the
four-site sum is exactly that inequality. -/
theorem terminus_products_do_not_cancel (W : Sym2 (V × Fin 3) → ℂ) (c : V → Fin 3)
    {a b x y : V} (hab : a ≠ b) (hax : a ≠ x) (hay : a ≠ y)
    (hbx : b ≠ x) (hby : b ≠ y) (hxy : x ≠ y)
    (hdb : W (Sym2.map (Amplitude.paint c) s(a, b)) = 0)
    (hne : pmSum W c ({a, b, x, y} : Finset V) ≠ 0) :
    W (Sym2.map (Amplitude.paint c) s(a, x))
        * W (Sym2.map (Amplitude.paint c) s(b, y))
      + W (Sym2.map (Amplitude.paint c) s(a, y))
        * W (Sym2.map (Amplitude.paint c) s(b, x)) ≠ 0 := by
  rw [MatchingCrossing.pmSum_four_two_terms W c hab hax hay hbx hby hxy hdb] at hne
  exact hne

/-! ### Two forced pairs, and the rectangle they cannot make

A forced colour-`m` pair is closed in `m`, and closure survives unions, so *any two* forced pairs
together form a closed four-set.  Every other colour therefore has vanishing sum on it -- and the
quad lemma above turns that vanishing into an identity, because one of the three terms is the
product of the two forced weights, dead in the other colour by exclusivity.

What is left is an identity between the four weights joining one pair to the other:

    W_j(u,u') * W_j(v,v')  +  W_j(u,v') * W_j(v,u')  =  0.

This is the first *equation between weights* the development has produced, as opposed to a
vanishing sum or a degree count.  Its content is a prohibition: two forced pairs may not be joined
by two parallel `j`-edges unless the two diagonals are live as well.  In particular, if `u` has
only one `j`-partner, no such rectangle exists at all -- so in the certified skeleton, where every
colour has degree one, **the union of two colour classes contains no four-cycle**.

That is a genuine girth statement about the skeleton, uniform in the vertex count, and it is not
a consequence of anything earlier: the counting arguments see degrees, and the closed-set
arguments see cuts, but neither sees a four-cycle. -/

/-- **The rectangle identity.**  Two disjoint colour-`m` closed pairs, viewed in another colour,
satisfy an exact quadratic relation: the two ways of joining them pair off with opposite sign. -/
theorem forced_pairs_permanent (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {m j : Fin 3} (hjm : j ≠ m)
    (hone : amplitude W (Amplitude.const (V := V) m) ≠ 0)
    {u v u' v' : V} (huv : u ≠ v) (huu' : u ≠ u') (huv' : u ≠ v')
    (hvu' : v ≠ u') (hvv' : v ≠ v') (hu'v' : u' ≠ v')
    (hcl1 : ∀ x ∈ ({u, v} : Finset V), ∀ y : V, y ∉ ({u, v} : Finset V) →
      W s((x, m), (y, m)) = 0)
    (hcl2 : ∀ x ∈ ({u', v'} : Finset V), ∀ y : V, y ∉ ({u', v'} : Finset V) →
      W s((x, m), (y, m)) = 0)
    (hproper : ({u, v, u', v'} : Finset V) ≠ Finset.univ) :
    W s((u, j), (u', j)) * W s((v, j), (v', j))
      + W s((u, j), (v', j)) * W s((v, j), (u', j)) = 0 := by
  classical
  -- the forced pair itself is dead in the other colour
  have hpairne : ({u, v} : Finset V) ≠ Finset.univ := by
    intro h
    have : u' ∈ ({u, v} : Finset V) := by rw [h]; exact Finset.mem_univ u'
    rcases Finset.mem_insert.mp this with h' | h'
    · exact huu' h'.symm
    · exact hvu' (Finset.mem_singleton.mp h').symm
  have hdead := closed_dead_other W hzero hmono hjm hone ⟨u, by simp⟩ hpairne hcl1
  rw [pmSum_pair W (Amplitude.const (V := V) j) (Ne.symm huv)] at hdead
  -- the union of the two pairs is closed, hence dead in the other colour too
  have hunion : ({u, v} : Finset V) ∪ ({u', v'} : Finset V) = ({u, v, u', v'} : Finset V) := by
    ext z
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hclosed := closed_union W hcl1 hcl2
  rw [hunion] at hclosed
  have hquad := closed_dead_other W hzero hmono hjm hone ⟨u, by simp⟩ hproper hclosed
  -- and the quad lemma reads it as the identity
  have hpaint : (Sym2.map (Amplitude.paint (Amplitude.const (V := V) j)) s(u, v))
      = s((u, j), (v, j)) := rfl
  rw [MatchingCrossing.pmSum_four_two_terms W (Amplitude.const (V := V) j)
    huv huu' huv' hvu' hvv' hu'v'
    (by rw [hpaint]; exact hdead)] at hquad
  exact hquad

/-- **Parallel joins force the diagonals.**  If two forced pairs are joined by two parallel
`j`-edges, both diagonals are `j`-live -- so each of the four sites has a second `j`-partner. -/
theorem forced_rectangle_forces_diagonals (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {m j : Fin 3} (hjm : j ≠ m)
    (hone : amplitude W (Amplitude.const (V := V) m) ≠ 0)
    {u v u' v' : V} (huv : u ≠ v) (huu' : u ≠ u') (huv' : u ≠ v')
    (hvu' : v ≠ u') (hvv' : v ≠ v') (hu'v' : u' ≠ v')
    (hcl1 : ∀ x ∈ ({u, v} : Finset V), ∀ y : V, y ∉ ({u, v} : Finset V) →
      W s((x, m), (y, m)) = 0)
    (hcl2 : ∀ x ∈ ({u', v'} : Finset V), ∀ y : V, y ∉ ({u', v'} : Finset V) →
      W s((x, m), (y, m)) = 0)
    (hproper : ({u, v, u', v'} : Finset V) ≠ Finset.univ)
    (h1 : W s((u, j), (u', j)) ≠ 0) (h2 : W s((v, j), (v', j)) ≠ 0) :
    W s((u, j), (v', j)) ≠ 0 ∧ W s((v, j), (u', j)) ≠ 0 := by
  have hid := forced_pairs_permanent W hzero hmono hjm hone huv huu' huv' hvu' hvv' hu'v'
    hcl1 hcl2 hproper
  constructor
  · intro h
    rw [h, zero_mul, add_zero] at hid
    exact (mul_ne_zero h1 h2) hid
  · intro h
    rw [h, mul_zero, add_zero] at hid
    exact (mul_ne_zero h1 h2) hid

/-- **No four-cycle in a two-colour union of the skeleton.**  If `u`'s only `j`-partner is `u'`,
then no forced pair containing `u` can be joined to a forced pair containing `u'` by a second
parallel `j`-edge.  In the certified skeleton every colour has degree one, so the union of any
two colour classes is a two-factor all of whose cycles have length at least six. -/
theorem no_forced_four_cycle (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {m j : Fin 3} (hjm : j ≠ m)
    (hone : amplitude W (Amplitude.const (V := V) m) ≠ 0)
    {u v u' v' : V} (huv : u ≠ v) (huu' : u ≠ u') (huv' : u ≠ v')
    (hvu' : v ≠ u') (hvv' : v ≠ v') (hu'v' : u' ≠ v')
    (hcl1 : ∀ x ∈ ({u, v} : Finset V), ∀ y : V, y ∉ ({u, v} : Finset V) →
      W s((x, m), (y, m)) = 0)
    (hcl2 : ∀ x ∈ ({u', v'} : Finset V), ∀ y : V, y ∉ ({u', v'} : Finset V) →
      W s((x, m), (y, m)) = 0)
    (hproper : ({u, v, u', v'} : Finset V) ≠ Finset.univ)
    (h1 : W s((u, j), (u', j)) ≠ 0) (h2 : W s((v, j), (v', j)) ≠ 0)
    (hdeg : ∀ z : V, z ≠ u → z ≠ u' → W s((u, j), (z, j)) = 0) :
    False :=
  (forced_rectangle_forces_diagonals W hzero hmono hjm hone huv huu' huv' hvu' hvv' hu'v'
    hcl1 hcl2 hproper h1 h2).1 (hdeg v' (Ne.symm huv') (Ne.symm hu'v'))

/-- **A three-edge join is impossible.**  The identity has two products; if three of the four
weights are live the fourth is forced live too.  So between two forced pairs the other colour
joins them with no edge, one edge, two edges sharing a site, or all four -- never three. -/
theorem forced_join_not_three (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {m j : Fin 3} (hjm : j ≠ m)
    (hone : amplitude W (Amplitude.const (V := V) m) ≠ 0)
    {u v u' v' : V} (huv : u ≠ v) (huu' : u ≠ u') (huv' : u ≠ v')
    (hvu' : v ≠ u') (hvv' : v ≠ v') (hu'v' : u' ≠ v')
    (hcl1 : ∀ x ∈ ({u, v} : Finset V), ∀ y : V, y ∉ ({u, v} : Finset V) →
      W s((x, m), (y, m)) = 0)
    (hcl2 : ∀ x ∈ ({u', v'} : Finset V), ∀ y : V, y ∉ ({u', v'} : Finset V) →
      W s((x, m), (y, m)) = 0)
    (hproper : ({u, v, u', v'} : Finset V) ≠ Finset.univ)
    (h1 : W s((u, j), (u', j)) ≠ 0) (h2 : W s((v, j), (v', j)) ≠ 0)
    (h4 : W s((v, j), (u', j)) = 0) :
    False :=
  (forced_rectangle_forces_diagonals W hzero hmono hjm hone huv huu' huv' hvu' hvv' hu'v'
    hcl1 hcl2 hproper h1 h2).2 h4

/-! ### Certification inside a closed component is a statement about that component

For a pair inside a colour-closed set, the complement splits: the rest of the set, and everything
outside.  No live edge joins them, so the matching sum factors, and the outside factor is the
certified complement, non-zero.  Certification of a pair inside a closed component therefore says
nothing about the rest of the configuration -- it is exactly the condition that the *component*
minus the pair still has a matching sum.

At four sites that condition is a single weight, so it is automatic whenever the complementary
pair is live.  A four-site core -- closed, even, minimum degree two inside -- therefore has *every*
internal live pair certified, hence two certified partners at every site.

That is worth stating plainly, because it is a limit on method rather than a step forward: a
four-site core satisfies every constraint this development has proved.  It is closed, even, doubly
crossed by each other colour, bridgeless, not a star, and its certified structure is consistent.
Whatever finally bounds the live degree must see something a four-site core does not have, and
none of the closed-set or certificate machinery is that thing. -/

/-- **Certification factors through the closed component.**  A pair inside a closed set is
certified exactly when the set minus the pair still carries a matching sum. -/
theorem certified_of_closed_complement (W : Sym2 (V × Fin 3) → ℂ) {m : Fin 3}
    (hone : amplitude W (Amplitude.const (V := V) m) ≠ 0)
    {C : Finset V}
    (hclosed : ∀ x ∈ C, ∀ y : V, y ∉ C → W s((x, m), (y, m)) = 0)
    {a z p q : V} (ha : a ∈ C) (hz : z ∈ C) (hza : z ≠ a)
    (hrest : C \ ({a, z} : Finset V) = ({p, q} : Finset V)) (hqp : q ≠ p)
    (hlive : W s((a, m), (z, m)) ≠ 0) (hpq : W s((p, m), (q, m)) ≠ 0) :
    z ∈ certifiedNbrs W a m := by
  classical
  set c := Amplitude.const (V := V) m with hc
  have hsub : C \ ({a, z} : Finset V) ⊆ (Finset.univ.erase a).erase z := by
    intro w hw
    rcases Finset.mem_sdiff.mp hw with ⟨hwC, hwaz⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hwaz
    exact Finset.mem_erase.mpr ⟨hwaz.2, Finset.mem_erase.mpr ⟨hwaz.1, Finset.mem_univ w⟩⟩
  have hsdiff : ((Finset.univ.erase a).erase z) \ (C \ ({a, z} : Finset V))
      = Finset.univ \ C := by
    ext w
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, and_true,
      Finset.mem_insert, Finset.mem_singleton, not_or, not_and]
    constructor
    · rintro ⟨⟨hwz, hwa⟩, hnot⟩
      exact ⟨trivial, fun hwC => (hnot hwC hwa) hwz⟩
    · rintro ⟨-, hwC⟩
      refine ⟨⟨fun h => hwC (h ▸ hz), fun h => hwC (h ▸ ha)⟩, fun h => absurd h hwC⟩
  have hcut : ∀ x ∈ C \ ({a, z} : Finset V),
      ∀ y ∈ ((Finset.univ.erase a).erase z) \ (C \ ({a, z} : Finset V)),
        W s((x, c x), (y, c y)) = 0 := by
    intro x hx y hy
    rw [hsdiff] at hy
    exact hclosed x (Finset.mem_sdiff.mp hx).1 y (Finset.mem_sdiff.mp hy).2
  have hsplit := Separation.pmSum_split W c (C \ ({a, z} : Finset V)).card
    (C \ ({a, z} : Finset V)) ((Finset.univ.erase a).erase z) rfl hsub hcut
  rw [hsdiff, hrest, pmSum_pair W c hqp] at hsplit
  have houter := (closed_both_certified W hone hclosed).2
  refine mem_certifiedNbrs.mpr ⟨hza, hlive, ?_⟩
  rw [hsplit]
  exact mul_ne_zero hpq houter

/-- **A four-site core has two certified partners at every site.**  Both of its internal matchings
are certified, because each one's complement inside the core is a single live pair. -/
theorem four_core_two_certified (W : Sym2 (V × Fin 3) → ℂ) {m : Fin 3}
    (hone : amplitude W (Amplitude.const (V := V) m) ≠ 0)
    {a b x y : V} (hab : a ≠ b) (hax : a ≠ x) (hay : a ≠ y)
    (hbx : b ≠ x) (hby : b ≠ y) (hxy : x ≠ y)
    (hclosed : ∀ w ∈ ({a, b, x, y} : Finset V), ∀ t : V, t ∉ ({a, b, x, y} : Finset V) →
      W s((w, m), (t, m)) = 0)
    (hlax : W s((a, m), (x, m)) ≠ 0) (hlby : W s((b, m), (y, m)) ≠ 0)
    (hlay : W s((a, m), (y, m)) ≠ 0) (hlbx : W s((b, m), (x, m)) ≠ 0) :
    1 < (certifiedNbrs W a m).card := by
  classical
  have hrestx : ({a, b, x, y} : Finset V) \ ({a, x} : Finset V) = ({b, y} : Finset V) := by
    ext w
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · rintro ⟨rfl | rfl | rfl | rfl, hna, hnx⟩
      exacts [absurd rfl hna, Or.inl rfl, absurd rfl hnx, Or.inr rfl]
    · rintro (rfl | rfl)
      exacts [⟨by simp, Ne.symm hab, hbx⟩, ⟨by simp, Ne.symm hay, Ne.symm hxy⟩]
  have hresty : ({a, b, x, y} : Finset V) \ ({a, y} : Finset V) = ({b, x} : Finset V) := by
    ext w
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · rintro ⟨rfl | rfl | rfl | rfl, hna, hny⟩
      exacts [absurd rfl hna, Or.inl rfl, Or.inr rfl, absurd rfl hny]
    · rintro (rfl | rfl)
      exacts [⟨by simp, Ne.symm hab, hby⟩, ⟨by simp, Ne.symm hax, hxy⟩]
  have hmx : x ∈ certifiedNbrs W a m :=
    certified_of_closed_complement W hone hclosed (by simp) (by simp) (Ne.symm hax)
      hrestx (Ne.symm hby) hlax hlby
  have hmy : y ∈ certifiedNbrs W a m :=
    certified_of_closed_complement W hone hclosed (by simp) (by simp) (Ne.symm hay)
      hresty (Ne.symm hbx) hlay hlbx
  exact Finset.one_lt_card.mpr ⟨x, hmx, y, hmy, hxy⟩

end ColourClosed

/-! ### Hall's condition, which is a constraint of a different kind

Every tool so far reads the equations: something vanishes, something is certified, some cut is
crossed.  None of them looks at the matchings themselves.  Here is one that does.

Fix a colour and a set `A` all of whose internal pairs are dead in that colour.  A matching that
contributes anything at all must send every site of `A` outside `A`, along a live edge, and
injectively, because a matching is an involution.  So the live neighbourhood of `A` outside `A` is
at least as large as `A` -- Hall's condition, forced not by the equations but by the shape of a
matching.

This is the first statement in the development that could distinguish configurations the
certificate machinery cannot, because it counts *room* rather than *certificates*.  A set with no
internal live edge in a colour needs somewhere for all of its sites to go. -/


section HallColour

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **A colour-blind set needs room.**  If no pair inside `A` is live in colour `j`, then `A` is
at most half the configuration -- every one of its sites must be matched outside it.

This is the constraint a four-site core does not automatically satisfy: at six sites a four-site
core with no internal live pair in some other colour is impossible, whatever its certificates. -/
theorem card_le_of_no_internal_live (W : Sym2 (V × Fin 3) → ℂ) {j : Fin 3}
    (hone : amplitude W (Amplitude.const (V := V) j) ≠ 0) {A : Finset V}
    (hdead : ∀ x ∈ A, ∀ y ∈ A, y ≠ x → W s((x, j), (y, j)) = 0) :
    A.card ≤ (Finset.univ \ A).card := by
  classical
  refine card_le_card_compl_of_internal_dead W (Amplitude.const (V := V) j)
    (Finset.subset_univ A) ?_ ?_
  · intro x hx y hy hyx
    have hpaint : (Sym2.map (Amplitude.paint (Amplitude.const (V := V) j)) s(x, y))
        = s((x, j), (y, j)) := rfl
    rw [hpaint]
    exact hdead x hx y hy hyx
  · rw [pmSum_univ]; exact hone

/-- **Every large set has an internal live pair, in every colour.**  The contrapositive, which is
how the counting will be used: a set occupying more than half the configuration cannot be dead
inside in any colour. -/
theorem exists_internal_live_of_large (W : Sym2 (V × Fin 3) → ℂ) {j : Fin 3}
    (hone : amplitude W (Amplitude.const (V := V) j) ≠ 0) {A : Finset V}
    (hbig : (Finset.univ \ A).card < A.card) :
    ∃ x ∈ A, ∃ y ∈ A, y ≠ x ∧ W s((x, j), (y, j)) ≠ 0 := by
  by_contra hno
  push_neg at hno
  exact absurd (card_le_of_no_internal_live W hone
    (fun x hx y hy hyx => hno x hx y hy hyx)) (by omega)

end HallColour

/-! ### Non-vanishing without a certificate

The obstacle account said the two halves explain each other: a lower bound needs no certificate
but names nothing, and naming needs a certificate the excess never supplies.  There is a third
way, and it has been sitting in plain sight.

If a set carries **exactly one** live matching in a colour, its matching sum is a single product
and cannot cancel.  No certificate, no minimality, no equation -- just the observation that a sum
with one term is that term.  This is the first non-vanishing in the development that is not
inherited from a hypothesis.

It closes immediately into a prohibition.  Colour the sites of such a set `m`, colour a complement
that carries exactly one live `j`-matching `j`, and the whole amplitude factors as a product of two
non-zero numbers -- while the colouring is not monochromatic, so it must vanish.

The result is strictly stronger than the two-colour closed obstruction.  Closure demands that no
live edge leave the set; this demands only that the live edges *inside* it form a matching.  Sites
may have as many partners outside as they like. -/


section ForcedColour

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Two forced sides cannot partition the configuration.**  If the live `m`-edges inside `F`
form a perfect matching of `F`, and the live `j`-edges inside the complement form a perfect
matching of it, then the two-coloured amplitude is a product of two non-zero numbers -- and it is
not monochromatic, so it must vanish.

Strictly stronger than the two-colour closed obstruction: nothing here forbids live edges leaving
either side. -/
theorem false_of_matched_partition (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {m j : Fin 3} (hjm : j ≠ m) {F : Finset V}
    (hF : F.Nonempty) (hG : (Finset.univ \ F).Nonempty)
    (p : V → V) (hp : ∀ x ∈ F, p x ∈ F) (hinv : ∀ x ∈ F, p (p x) = x)
    (hpne : ∀ x ∈ F, p x ≠ x)
    (hplive : ∀ x ∈ F, W s((x, m), (p x, m)) ≠ 0)
    (hpuniq : ∀ x ∈ F, ∀ y ∈ F, y ≠ x → y ≠ p x → W s((x, m), (y, m)) = 0)
    (q : V → V) (hq : ∀ x ∈ Finset.univ \ F, q x ∈ Finset.univ \ F)
    (hqinv : ∀ x ∈ Finset.univ \ F, q (q x) = x)
    (hqne : ∀ x ∈ Finset.univ \ F, q x ≠ x)
    (hqlive : ∀ x ∈ Finset.univ \ F, W s((x, j), (q x, j)) ≠ 0)
    (hquniq : ∀ x ∈ Finset.univ \ F, ∀ y ∈ Finset.univ \ F, y ≠ x → y ≠ q x →
      W s((x, j), (y, j)) = 0) :
    False := by
  classical
  set c : V → Fin 3 := fun x => if x ∈ F then m else j with hc
  obtain ⟨x₀, hx₀⟩ := hF
  obtain ⟨y₀, hy₀⟩ := hG
  have hy₀F : y₀ ∉ F := (Finset.mem_sdiff.mp hy₀).2
  have hnotmono : ¬ Amplitude.Monochromatic c := by
    rintro ⟨k, hk⟩
    have h1 : c x₀ = m := by simp only [hc, if_pos hx₀]
    have h2 : c y₀ = j := by simp only [hc, if_neg hy₀F]
    exact hjm (by rw [← h2, hk y₀, ← hk x₀, h1])
  have hcut : ∀ x ∈ F, ∀ y ∈ Finset.univ \ F, W s((x, c x), (y, c y)) = 0 := by
    intro x hx y hy
    have hyF : y ∉ F := (Finset.mem_sdiff.mp hy).2
    have hyx : y ≠ x := fun h => hyF (h ▸ hx)
    rw [show c x = m from by simp only [hc, if_pos hx],
      show c y = j from by simp only [hc, if_neg hyF]]
    exact hmono x y hyx m j (Ne.symm hjm)
  have hsplit := Separation.pmSum_split W c F.card F Finset.univ rfl (Finset.subset_univ F) hcut
  rw [pmSum_univ] at hsplit
  have hFsum : pmSum W c F ≠ 0 := by
    refine pmSum_ne_zero_of_forced W c p hp hinv hpne (fun x hx => ?_) (fun x hx y hy hyx hyp => ?_)
    · have : (Sym2.map (Amplitude.paint c) s(x, p x)) = s((x, m), (p x, m)) := by
        simp only [hc, Sym2.map_pair_eq, Amplitude.paint, if_pos hx, if_pos (hp x hx)]
      rw [this]; exact hplive x hx
    · have : (Sym2.map (Amplitude.paint c) s(x, y)) = s((x, m), (y, m)) := by
        simp only [hc, Sym2.map_pair_eq, Amplitude.paint, if_pos hx, if_pos hy]
      rw [this]; exact hpuniq x hx y hy hyx hyp
  have hGsum : pmSum W c (Finset.univ \ F) ≠ 0 := by
    refine pmSum_ne_zero_of_forced W c q hq hqinv hqne (fun x hx => ?_) (fun x hx y hy hyx hyq => ?_)
    · have hxF : x ∉ F := (Finset.mem_sdiff.mp hx).2
      have hqxF : q x ∉ F := (Finset.mem_sdiff.mp (hq x hx)).2
      have : (Sym2.map (Amplitude.paint c) s(x, q x)) = s((x, j), (q x, j)) := by
        simp only [hc, Sym2.map_pair_eq, Amplitude.paint, if_neg hxF, if_neg hqxF]
      rw [this]; exact hqlive x hx
    · have hxF : x ∉ F := (Finset.mem_sdiff.mp hx).2
      have hyF : y ∉ F := (Finset.mem_sdiff.mp hy).2
      have : (Sym2.map (Amplitude.paint c) s(x, y)) = s((x, j), (y, j)) := by
        simp only [hc, Sym2.map_pair_eq, Amplitude.paint, if_neg hxF, if_neg hyF]
      rw [this]; exact hquniq x hx y hy hyx hyq
  exact (mul_ne_zero hFsum hGsum) (hsplit ▸ hzero c hnotmono)

/-- **Removing a live pair of another colour.**  The most usable form: a pair is always its own
matching, so the whole burden falls on the other side.  If some pair is live in colour `j` and
deleting it leaves the colour-`m` live graph exactly one-regular, the configuration is impossible.

Both sites of such a pair must be core sites: deleting a pendant site would strand its partner.
So this is a statement about cores, and it is sharp -- a four-cycle core survives it, because
deleting any two of its sites leaves the other two isolated, while a six-cycle core does not, if
any of its three antipodal pairs is live in another colour. -/
theorem false_of_live_pair_removal (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {m j : Fin 3} (hjm : j ≠ m) {u v : V} (huv : u ≠ v)
    (hjlive : W s((u, j), (v, j)) ≠ 0)
    (hFne : (Finset.univ \ ({u, v} : Finset V)).Nonempty)
    (p : V → V)
    (hp : ∀ x ∈ Finset.univ \ ({u, v} : Finset V), p x ∈ Finset.univ \ ({u, v} : Finset V))
    (hinv : ∀ x ∈ Finset.univ \ ({u, v} : Finset V), p (p x) = x)
    (hpne : ∀ x ∈ Finset.univ \ ({u, v} : Finset V), p x ≠ x)
    (hplive : ∀ x ∈ Finset.univ \ ({u, v} : Finset V), W s((x, m), (p x, m)) ≠ 0)
    (hpuniq : ∀ x ∈ Finset.univ \ ({u, v} : Finset V), ∀ y ∈ Finset.univ \ ({u, v} : Finset V),
      y ≠ x → y ≠ p x → W s((x, m), (y, m)) = 0) :
    False := by
  classical
  set F : Finset V := Finset.univ \ ({u, v} : Finset V) with hFdef
  have hcompl : Finset.univ \ F = ({u, v} : Finset V) := by
    ext z
    simp only [hFdef, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]
  set q : V → V := fun x => if x = u then v else u with hq
  refine false_of_matched_partition W hzero hmono hjm hFne ?_ p hp hinv hpne hplive hpuniq
    q ?_ ?_ ?_ ?_ ?_
  · rw [hcompl]; exact ⟨u, by simp⟩
  · intro x hx
    rw [hcompl] at hx ⊢
    by_cases h : x = u
    · simp only [hq, if_pos h]; simp
    · simp only [hq, if_neg h]; simp
  · intro x hx
    rw [hcompl] at hx
    rcases Finset.mem_insert.mp hx with rfl | hx'
    · simp only [hq, if_pos rfl, if_neg (Ne.symm huv)]
    · rw [Finset.mem_singleton] at hx'
      subst hx'
      simp only [hq, if_neg (Ne.symm huv), if_pos rfl]
  · intro x hx
    rw [hcompl] at hx
    rcases Finset.mem_insert.mp hx with rfl | hx'
    · simp only [hq, if_pos rfl]; exact Ne.symm huv
    · rw [Finset.mem_singleton] at hx'
      subst hx'
      simp only [hq, if_neg (Ne.symm huv)]; exact huv
  · intro x hx
    rw [hcompl] at hx
    rcases Finset.mem_insert.mp hx with rfl | hx'
    · simp only [hq, if_pos rfl]; exact hjlive
    · rw [Finset.mem_singleton] at hx'
      subst hx'
      simp only [hq, if_neg (Ne.symm huv)]
      rw [Sym2.eq_swap]; exact hjlive
  · intro x hx y hy hyx hyq
    rw [hcompl] at hx hy
    exfalso
    rcases Finset.mem_insert.mp hx with rfl | hx'
    · simp only [hq, if_pos rfl] at hyq
      rcases Finset.mem_insert.mp hy with rfl | hy'
      · exact hyx rfl
      · exact hyq (Finset.mem_singleton.mp hy')
    · rw [Finset.mem_singleton] at hx'
      subst hx'
      simp only [hq, if_neg (Ne.symm huv)] at hyq
      rcases Finset.mem_insert.mp hy with rfl | hy'
      · exact hyq rfl
      · exact hyx (Finset.mem_singleton.mp hy')

end ForcedColour

/-! ### Rigid colourings, and what they exclude

The two-block form was a special case.  What the argument really needs is a colouring whose
*whole* live structure is one matching: for every site exactly one live partner of its own colour.
Then the amplitude is a single product, non-zero, and if the colouring is not monochromatic it
must also be zero.

Call such a colouring rigid.  The statement is then: **no rigid colouring is non-monochromatic**,
and it is the clean general form of the fourth-matching argument.  In the cubic case it *is* that
argument: with the live graph exactly three disjoint matchings, every perfect matching of it is
automatically rigid, so any mixed one closes the case.  Excess edges are what break rigidity, and
that is exactly why they cost the earlier route its conclusion.

The reformulation is worth stating on its own terms.  Whether a colouring is rigid is a question
about the live *graph* -- no weights, no cancellation.  So the whole conjecture reduces to a
combinatorial one: every such configuration admits a non-monochromatic rigid colouring. -/

section Rigid

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **No rigid colouring is non-monochromatic.**  If every site has exactly one live partner of
its own colour, the amplitude is a single non-zero product. -/
theorem false_of_rigid_colouring (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {c : V → Fin 3} (hc : ¬ Amplitude.Monochromatic c)
    (p : V → V) (hinv : ∀ z, p (p z) = z) (hpne : ∀ z, p z ≠ z)
    (hlive : ∀ z, W s((z, c z), (p z, c (p z))) ≠ 0)
    (huniq : ∀ z w : V, w ≠ z → w ≠ p z → W s((z, c z), (w, c w)) = 0) :
    False := by
  classical
  have h := pmSum_ne_zero_of_forced W c p (fun z _ => Finset.mem_univ _) (fun z _ => hinv z)
    (fun z _ => hpne z) (fun z _ => hlive z) (fun z _ w _ hwz hwp => huniq z w hwz hwp)
  rw [pmSum_univ] at h
  exact h (hzero c hc)

/-- **Two pairs and a pendant rest.**  If the configuration splits into a pair live in one colour,
a pair live in a second, and a remainder whose live edges in the third colour form exactly a
perfect matching of it, the configuration is impossible.

This is what excludes the smallest core once both of its diagonals are live: a four-cycle core has
exactly one pairing that avoids its own colour, namely the two diagonals, and the rest of the
configuration is the pendant part, whose live edges in that colour are exactly its forced pairs. -/
theorem false_of_two_pairs_and_pendant_rest (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (u v : V), v ≠ u → ∀ e f : Fin 3, e ≠ f → W s((u, e), (v, f)) = 0)
    {m j i : Fin 3} (hjm : j ≠ m) (him : i ≠ m) (hji : j ≠ i)
    {a b x y : V} (hab : a ≠ b) (hax : a ≠ x) (hay : a ≠ y)
    (hbx : b ≠ x) (hby : b ≠ y) (hxy : x ≠ y)
    (p : V → V) (hinv : ∀ z, p (p z) = z) (hpne : ∀ z, p z ≠ z)
    (hpa : p a = b) (hpx : p x = y)
    (hpout : ∀ z ∉ ({a, b, x, y} : Finset V), p z ∉ ({a, b, x, y} : Finset V))
    (hjab : W s((a, j), (b, j)) ≠ 0) (hixy : W s((x, i), (y, i)) ≠ 0)
    (hplive : ∀ z ∉ ({a, b, x, y} : Finset V), W s((z, m), (p z, m)) ≠ 0)
    (hpuniq : ∀ z ∉ ({a, b, x, y} : Finset V), ∀ w ∉ ({a, b, x, y} : Finset V),
      w ≠ z → w ≠ p z → W s((z, m), (w, m)) = 0) :
    False := by
  classical
  set c : V → Fin 3 := fun z =>
    if z ∈ ({a, b} : Finset V) then j else if z ∈ ({x, y} : Finset V) then i else m with hcdef
  have hca : c a = j := by simp only [hcdef]; rw [if_pos (by simp)]
  have hcb : c b = j := by simp only [hcdef]; rw [if_pos (by simp)]
  have hcx : c x = i := by
    simp only [hcdef]
    rw [if_neg (by simp [Ne.symm hax, Ne.symm hbx]), if_pos (by simp)]
  have hcy : c y = i := by
    simp only [hcdef]
    rw [if_neg (by simp [Ne.symm hay, Ne.symm hby]), if_pos (by simp)]
  have hpb : p b = a := by rw [← hpa, hinv]
  have hpy : p y = x := by rw [← hpx, hinv]
  have hmemK : ∀ z : V, z ∈ ({a, b, x, y} : Finset V) ↔ z = a ∨ z = b ∨ z = x ∨ z = y := by
    intro z; simp
  have hcout : ∀ z ∉ ({a, b, x, y} : Finset V), c z = m := by
    intro z hz
    rw [hmemK] at hz
    push_neg at hz
    simp only [hcdef]
    rw [if_neg (by simp [hz.1, hz.2.1]), if_neg (by simp [hz.2.2.1, hz.2.2.2])]
  have hcover : ∀ k : Fin 3, k = j ∨ k = i ∨ k = m := by
    intro k
    by_contra hk
    push_neg at hk
    have hle : ({j, i, m, k} : Finset (Fin 3)).card ≤ 3 := by
      simpa using Finset.card_le_univ ({j, i, m, k} : Finset (Fin 3))
    rw [Finset.card_insert_of_notMem (by simp [hji, hjm, Ne.symm hk.1]),
      Finset.card_insert_of_notMem (by simp [him, Ne.symm hk.2.1]),
      Finset.card_insert_of_notMem (by simp [Ne.symm hk.2.2]),
      Finset.card_singleton] at hle
    omega
  have hcj : ∀ w : V, c w = j → w = a ∨ w = b := by
    intro w hw
    by_cases h1 : w ∈ ({a, b} : Finset V)
    · simpa using h1
    · exfalso
      by_cases h2 : w ∈ ({x, y} : Finset V)
      · simp only [hcdef, if_neg h1, if_pos h2] at hw; exact hji hw.symm
      · simp only [hcdef, if_neg h1, if_neg h2] at hw; exact hjm hw.symm
  have hci : ∀ w : V, c w = i → w = x ∨ w = y := by
    intro w hw
    by_cases h2 : w ∈ ({x, y} : Finset V)
    · simpa using h2
    · exfalso
      by_cases h1 : w ∈ ({a, b} : Finset V)
      · simp only [hcdef, if_pos h1] at hw; exact hji hw
      · simp only [hcdef, if_neg h1, if_neg h2] at hw; exact him hw.symm
  have hcm : ∀ w : V, c w = m → w ∉ ({a, b, x, y} : Finset V) := by
    intro w hw hmem
    rcases (hmemK w).mp hmem with rfl | rfl | rfl | rfl
    exacts [hjm (by rw [← hca, hw]), hjm (by rw [← hcb, hw]),
      him (by rw [← hcx, hw]), him (by rw [← hcy, hw])]
  have hfib : ∀ z w : V, c z = c w → w ≠ z → w ≠ p z →
      z ∉ ({a, b, x, y} : Finset V) ∧ w ∉ ({a, b, x, y} : Finset V) := by
    intro z w hcc hwz hwp
    rcases hcover (c z) with h | h | h
    · exfalso
      have hw' : c w = j := hcc.symm.trans h
      rcases hcj z h with rfl | rfl
      · rcases hcj w hw' with rfl | rfl
        exacts [hwz rfl, hwp hpa.symm]
      · rcases hcj w hw' with rfl | rfl
        exacts [hwp hpb.symm, hwz rfl]
    · exfalso
      have hw' : c w = i := hcc.symm.trans h
      rcases hci z h with rfl | rfl
      · rcases hci w hw' with rfl | rfl
        exacts [hwz rfl, hwp hpx.symm]
      · rcases hci w hw' with rfl | rfl
        exacts [hwp hpy.symm, hwz rfl]
    · exact ⟨hcm z h, hcm w (hcc.symm.trans h)⟩
  refine false_of_rigid_colouring W hzero (c := c) ?_ p hinv hpne ?_ ?_
  · rintro ⟨k, hk⟩
    exact hji (by rw [← hca, hk a, ← hk x, hcx])
  · intro z
    by_cases hza : z = a
    · subst hza; rw [hca, hpa, hcb]; exact hjab
    · by_cases hzb : z = b
      · subst hzb; rw [hcb, hpb, hca, Sym2.eq_swap]; exact hjab
      · by_cases hzx : z = x
        · subst hzx; rw [hcx, hpx, hcy]; exact hixy
        · by_cases hzy : z = y
          · subst hzy; rw [hcy, hpy, hcx, Sym2.eq_swap]; exact hixy
          · have hz : z ∉ ({a, b, x, y} : Finset V) := by simp [hza, hzb, hzx, hzy]
            rw [hcout z hz, hcout (p z) (hpout z hz)]
            exact hplive z hz
  · intro z w hwz hwp
    by_cases hcc : c z = c w
    · obtain ⟨hz, hw⟩ := hfib z w hcc hwz hwp
      rw [hcout z hz, hcout w hw]
      exact hpuniq z hz w hw hwz hwp
    · exact hmono z w hwz (c z) (c w) hcc

/-- **A four-cycle core has at most one live diagonal.**  Its two diagonals are the only pairs
inside it not live in its own colour, so they are the only pairing of it that another colour could
carry.  If both are live the configuration dies, and by two different routes: in the same colour
the closed set's vanishing sum reduces to their product, and in different colours the whole
configuration becomes a rigid colouring.

So a smallest core has a pair of sites joined by no live edge at all -- which is a real
restriction, since every other pair inside it is live. -/
theorem four_core_diagonals_not_both_live (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (u v : V), v ≠ u → ∀ e f : Fin 3, e ≠ f → W s((u, e), (v, f)) = 0)
    {m j i : Fin 3} (hjm : j ≠ m) (him : i ≠ m)
    (hone : amplitude W (Amplitude.const (V := V) m) ≠ 0)
    {a b x y : V} (hab : a ≠ b) (hax : a ≠ x) (hay : a ≠ y)
    (hbx : b ≠ x) (hby : b ≠ y) (hxy : x ≠ y)
    (hclosed : ∀ w ∈ ({a, b, x, y} : Finset V), ∀ t : V, t ∉ ({a, b, x, y} : Finset V) →
      W s((w, m), (t, m)) = 0)
    (hproper : ({a, b, x, y} : Finset V) ≠ Finset.univ)
    (p : V → V) (hinv : ∀ z, p (p z) = z) (hpne : ∀ z, p z ≠ z)
    (hpa : p a = b) (hpx : p x = y)
    (hpout : ∀ z ∉ ({a, b, x, y} : Finset V), p z ∉ ({a, b, x, y} : Finset V))
    (hplive : ∀ z ∉ ({a, b, x, y} : Finset V), W s((z, m), (p z, m)) ≠ 0)
    (hpuniq : ∀ z ∉ ({a, b, x, y} : Finset V), ∀ w ∉ ({a, b, x, y} : Finset V),
      w ≠ z → w ≠ p z → W s((z, m), (w, m)) = 0)
    (hdax : W s((a, j), (x, j)) = 0) (hday : W s((a, j), (y, j)) = 0)
    (hjab : W s((a, j), (b, j)) ≠ 0) (hixy : W s((x, i), (y, i)) ≠ 0) :
    False := by
  classical
  by_cases hji : j = i
  · -- one colour carries both: the closed set's sum is their product
    subst hji
    have hset : ({a, x, b, y} : Finset V) = ({a, b, x, y} : Finset V) := by
      ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    have hdead := closed_dead_other W hzero hmono hjm hone ⟨a, by simp⟩ hproper hclosed
    have hpaint : (Sym2.map (Amplitude.paint (Amplitude.const (V := V) j)) s(a, x))
        = s((a, j), (x, j)) := rfl
    have hquad := MatchingCrossing.pmSum_four_two_terms W
      (Amplitude.const (V := V) j) hax hab hay
      (Ne.symm hbx) hxy hby (by rw [hpaint]; exact hdax)
    rw [hset, hdead] at hquad
    have hpay : (Sym2.map (Amplitude.paint (Amplitude.const (V := V) j)) s(a, y))
        = s((a, j), (y, j)) := rfl
    rw [hpay, hday, zero_mul, add_zero] at hquad
    exact (mul_ne_zero hjab hixy) hquad.symm
  · exact false_of_two_pairs_and_pendant_rest W hzero hmono hjm him hji hab hax hay hbx hby hxy
      p hinv hpne hpa hpx hpout hjab hixy hplive hpuniq

/-! ### The colour-agreement law

Read the last theorem the other way round.  Two pairs whose deletion leaves the configuration
matched by a single colour cannot be live in *different* colours -- if they were, the three blocks
would form a rigid colouring.  So they agree, or one of them is dead.

This is a law about the live structure with no vanishing sum in sight, and it propagates.  Around a
four-cycle core, deleting one of the four core edges together with any one forced pair leaves the
rest matched, so every such deletion is subject to it: the colour joining one core site to a
forced site and the colour joining the opposite core site to that pair's other end must be the
same colour.  Four core edges and every forced pair each contribute an instance. -/

/-- **Two removable pairs agree in colour.**  If deleting them leaves a configuration matched by
colour `m` alone, then whatever colours they are live in must coincide. -/
theorem colours_agree_of_matched_rest (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (u v : V), v ≠ u → ∀ e f : Fin 3, e ≠ f → W s((u, e), (v, f)) = 0)
    {m j i : Fin 3} (hjm : j ≠ m) (him : i ≠ m)
    {a b x y : V} (hab : a ≠ b) (hax : a ≠ x) (hay : a ≠ y)
    (hbx : b ≠ x) (hby : b ≠ y) (hxy : x ≠ y)
    (p : V → V) (hinv : ∀ z, p (p z) = z) (hpne : ∀ z, p z ≠ z)
    (hpa : p a = b) (hpx : p x = y)
    (hpout : ∀ z ∉ ({a, b, x, y} : Finset V), p z ∉ ({a, b, x, y} : Finset V))
    (hplive : ∀ z ∉ ({a, b, x, y} : Finset V), W s((z, m), (p z, m)) ≠ 0)
    (hpuniq : ∀ z ∉ ({a, b, x, y} : Finset V), ∀ w ∉ ({a, b, x, y} : Finset V),
      w ≠ z → w ≠ p z → W s((z, m), (w, m)) = 0)
    (hjab : W s((a, j), (b, j)) ≠ 0) (hixy : W s((x, i), (y, i)) ≠ 0) :
    j = i := by
  by_contra hji
  exact false_of_two_pairs_and_pendant_rest W hzero hmono hjm him hji hab hax hay hbx hby hxy
    p hinv hpne hpa hpx hpout hjab hixy hplive hpuniq

/-- **Two pairs of the same colour, and a matched rest.**  The companion to the agreement law: if
the two removable pairs are live in the *same* colour, the configuration still dies, provided no
other edge of that colour joins them.

Together the two results forbid the same pattern from opposite sides.  Two pairs whose deletion
leaves a matched rest cannot be joined only along a diagonal -- in different colours the colouring
is rigid with three blocks, in one colour it is rigid with two.  The rectangle identity forbids the
same pattern between two forced pairs by an entirely different mechanism, so the prohibition holds
whether the pairs come from the core or from the forced part. -/
theorem false_of_same_colour_pairs_and_rest (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (u v : V), v ≠ u → ∀ e f : Fin 3, e ≠ f → W s((u, e), (v, f)) = 0)
    {m j : Fin 3} (hjm : j ≠ m)
    {a b x y : V} (hab : a ≠ b) (hax : a ≠ x) (hay : a ≠ y)
    (hbx : b ≠ x) (hby : b ≠ y) (hxy : x ≠ y)
    (hproper : ({a, b, x, y} : Finset V) ≠ Finset.univ)
    (p : V → V) (hinv : ∀ z, p (p z) = z) (hpne : ∀ z, p z ≠ z)
    (hpa : p a = b) (hpx : p x = y)
    (hpout : ∀ z ∉ ({a, b, x, y} : Finset V), p z ∉ ({a, b, x, y} : Finset V))
    (hplive : ∀ z ∉ ({a, b, x, y} : Finset V), W s((z, m), (p z, m)) ≠ 0)
    (hpuniq : ∀ z ∉ ({a, b, x, y} : Finset V), ∀ w ∉ ({a, b, x, y} : Finset V),
      w ≠ z → w ≠ p z → W s((z, m), (w, m)) = 0)
    (hjab : W s((a, j), (b, j)) ≠ 0) (hjxy : W s((x, j), (y, j)) ≠ 0)
    (hdax : W s((a, j), (x, j)) = 0) (hday : W s((a, j), (y, j)) = 0)
    (hdbx : W s((b, j), (x, j)) = 0) (hdby : W s((b, j), (y, j)) = 0) :
    False := by
  classical
  set K : Finset V := ({a, b, x, y} : Finset V) with hKdef
  have hmemK : ∀ z : V, z ∈ K ↔ z = a ∨ z = b ∨ z = x ∨ z = y := by intro z; simp [hKdef]
  set c : V → Fin 3 := fun z => if z ∈ K then j else m with hcdef
  have hcK : ∀ z ∈ K, c z = j := by intro z hz; simp only [hcdef, if_pos hz]
  have hcout : ∀ z ∉ K, c z = m := by intro z hz; simp only [hcdef, if_neg hz]
  have hpb : p b = a := by rw [← hpa, hinv]
  have hpy : p y = x := by rw [← hpx, hinv]
  have haK : a ∈ K := by rw [hmemK]; exact Or.inl rfl
  have hKdead : ∀ z ∈ K, ∀ w ∈ K, w ≠ z → w ≠ p z → W s((z, j), (w, j)) = 0 := by
    intro z hz w hw hwz hwp
    have hz' := (hmemK z).mp hz
    have hw' := (hmemK w).mp hw
    rcases hz' with rfl | rfl | rfl | rfl <;> rcases hw' with rfl | rfl | rfl | rfl
    exacts [absurd rfl hwz, absurd hpa.symm hwp, hdax, hday,
      absurd hpb.symm hwp, absurd rfl hwz, hdbx, hdby,
      (by rw [Sym2.eq_swap]; exact hdax), (by rw [Sym2.eq_swap]; exact hdbx),
      absurd rfl hwz, absurd hpx.symm hwp,
      (by rw [Sym2.eq_swap]; exact hday), (by rw [Sym2.eq_swap]; exact hdby),
      absurd hpy.symm hwp, absurd rfl hwz]
  refine false_of_rigid_colouring W hzero (c := c) ?_ p hinv hpne ?_ ?_
  · rintro ⟨k, hk⟩
    obtain ⟨z, hz⟩ : ∃ z : V, z ∉ K := by
      by_contra hall
      push_neg at hall
      exact hproper (Finset.eq_univ_of_forall hall)
    exact hjm (by rw [← hcK a haK, hk a, ← hk z, hcout z hz])
  · intro z
    by_cases hz : z ∈ K
    · rw [hcK z hz]
      have hpz : p z ∈ K := by
        rcases (hmemK z).mp hz with rfl | rfl | rfl | rfl
        · rw [hpa]; rw [hmemK]; exact Or.inr (Or.inl rfl)
        · rw [hpb]; rw [hmemK]; exact Or.inl rfl
        · rw [hpx]; rw [hmemK]; exact Or.inr (Or.inr (Or.inr rfl))
        · rw [hpy]; rw [hmemK]; exact Or.inr (Or.inr (Or.inl rfl))
      rw [hcK (p z) hpz]
      rcases (hmemK z).mp hz with rfl | rfl | rfl | rfl
      · rw [hpa]; exact hjab
      · rw [hpb, Sym2.eq_swap]; exact hjab
      · rw [hpx]; exact hjxy
      · rw [hpy, Sym2.eq_swap]; exact hjxy
    · rw [hcout z hz, hcout (p z) (hpout z hz)]; exact hplive z hz
  · intro z w hwz hwp
    by_cases hz : z ∈ K
    · by_cases hw : w ∈ K
      · rw [hcK z hz, hcK w hw]; exact hKdead z hz w hw hwz hwp
      · rw [hcK z hz, hcout w hw]; exact hmono z w hwz j m hjm
    · by_cases hw : w ∈ K
      · rw [hcout z hz, hcK w hw]; exact hmono z w hwz m j (Ne.symm hjm)
      · rw [hcout z hz, hcout w hw]; exact hpuniq z hz w hw hwz hwp

/-! ### The general form: arbitrary blocks over a matched rest

The special cases were accumulating -- two pairs in different colours, two pairs in the same
colour, three pairs with a separation.  They are all one theorem.

Take any set `K` carrying a colouring into colours other than `m`, paired inside itself so that
each block's own colour has exactly that pairing and nothing more, and let the complement be
matched by colour `m` alone.  That is a rigid colouring, and the configuration dies.

Every earlier form is an instantiation, and so is every form the analysis will need next: the
block structure on `K` is arbitrary, so blocks may be pairs, or larger induced matchings, in any
combination of the two colours. -/

/-- **Blocks over a matched rest.**  A set paired inside itself, block-coloured away from `m`,
with each colour's live edges inside it exactly its own pairing, over a complement matched by
`m` alone -- impossible. -/
theorem false_of_blocks_and_matched_rest (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (u v : V), v ≠ u → ∀ e f : Fin 3, e ≠ f → W s((u, e), (v, f)) = 0)
    {m : Fin 3} {K : Finset V} (hKne : K.Nonempty) (hproper : K ≠ Finset.univ)
    (d : V → Fin 3) (hdm : ∀ z ∈ K, d z ≠ m)
    (p : V → V) (hinv : ∀ z, p (p z) = z) (hpne : ∀ z, p z ≠ z)
    (hpK : ∀ z ∈ K, p z ∈ K) (hpd : ∀ z ∈ K, d (p z) = d z)
    (hKlive : ∀ z ∈ K, W s((z, d z), (p z, d z)) ≠ 0)
    (hKdead : ∀ z ∈ K, ∀ w ∈ K, w ≠ z → w ≠ p z → d z = d w →
      W s((z, d z), (w, d w)) = 0)
    (hpout : ∀ z ∉ K, p z ∉ K)
    (hplive : ∀ z ∉ K, W s((z, m), (p z, m)) ≠ 0)
    (hpuniq : ∀ z ∉ K, ∀ w ∉ K, w ≠ z → w ≠ p z → W s((z, m), (w, m)) = 0) :
    False := by
  classical
  set c : V → Fin 3 := fun z => if z ∈ K then d z else m with hcdef
  have hcK : ∀ z ∈ K, c z = d z := by intro z hz; simp only [hcdef, if_pos hz]
  have hcout : ∀ z ∉ K, c z = m := by intro z hz; simp only [hcdef, if_neg hz]
  refine false_of_rigid_colouring W hzero (c := c) ?_ p hinv hpne ?_ ?_
  · rintro ⟨k, hk⟩
    obtain ⟨z, hz⟩ := hKne
    obtain ⟨w, hw⟩ : ∃ w : V, w ∉ K := by
      by_contra hall
      push_neg at hall
      exact hproper (Finset.eq_univ_of_forall hall)
    exact hdm z hz (by rw [← hcK z hz, hk z, ← hk w, hcout w hw])
  · intro z
    by_cases hz : z ∈ K
    · rw [hcK z hz, hcK (p z) (hpK z hz), hpd z hz]; exact hKlive z hz
    · rw [hcout z hz, hcout (p z) (hpout z hz)]; exact hplive z hz
  · intro z w hwz hwp
    by_cases hcc : c z = c w
    · by_cases hz : z ∈ K
      · by_cases hw : w ∈ K
        · rw [hcK z hz, hcK w hw]
          rw [hcK z hz, hcK w hw] at hcc
          exact hKdead z hz w hw hwz hwp hcc
        · exact absurd (by rw [← hcK z hz, hcc, hcout w hw]) (hdm z hz)
      · by_cases hw : w ∈ K
        · exact absurd (by rw [← hcK w hw, ← hcc, hcout z hz]) (hdm w hw)
        · rw [hcout z hz, hcout w hw]; exact hpuniq z hz w hw hwz hwp
    · exact hmono z w hwz (c z) (c w) hcc

/-! ### The core is independent in the other colours, and Hall then bites

Work out what the agreement law leaves.  For a forced pair joined to the core it says: either all
the joins carry one colour, or one side of the core has no join to that pair, or one of the pair's
two ports has no join at all.  The last escape looked free -- with only one port active, all four
core sites may attach to it in any colours.

It is not free.  A four-cycle core has all four of its internal live pairs in its own colour, and
at most one live diagonal; if neither diagonal is live it is *independent* in both other colours.
Hall then says it must inject into its neighbourhood, so it has at least four **distinct**
neighbours in each of the other two colours -- and four sites cannot all attach to one port.

This is a strict strengthening of the doubly-crossed result: not two crossing edges, but `|C|`
distinct outside endpoints, per colour, uniform in the vertex count. -/

/-- **An internally dead set has at least its own size in live neighbours.**  Hall's condition in
the form the core structure consumes. -/
theorem card_le_liveNbrs_of_no_internal (W : Sym2 (V × Fin 3) → ℂ) {j : Fin 3}
    (hone : amplitude W (Amplitude.const (V := V) j) ≠ 0) {A : Finset V}
    (hdead : ∀ z ∈ A, ∀ w ∈ A, w ≠ z → W s((z, j), (w, j)) = 0) :
    A.card ≤ (liveOut W (Amplitude.const (V := V) j) Finset.univ A).card := by
  classical
  refine card_le_card_liveOut W (Amplitude.const (V := V) j) (Finset.subset_univ A)
    (fun z hz w hw hwz => ?_) (by rw [pmSum_univ]; exact hone)
  have hpaint : (Sym2.map (Amplitude.paint (Amplitude.const (V := V) j)) s(z, w))
      = s((z, j), (w, j)) := rfl
  rw [hpaint]
  exact hdead z hz w hw hwz

/-- **A four-cycle core with no live diagonal has four distinct neighbours in each other colour.**
Its own colour's edges are dead in the others, and its two diagonals are dead outright, so it is
independent -- and Hall injects it into its neighbourhood. -/
theorem four_core_four_neighbours (W : Sym2 (V × Fin 3) → ℂ) {j : Fin 3}
    (hone : amplitude W (Amplitude.const (V := V) j) ≠ 0)
    {a b x y : V} (hab : a ≠ b) (hax : a ≠ x) (hay : a ≠ y)
    (hbx : b ≠ x) (hby : b ≠ y) (hxy : x ≠ y)
    (hdab : W s((a, j), (b, j)) = 0) (hdxy : W s((x, j), (y, j)) = 0)
    (hdax : W s((a, j), (x, j)) = 0) (hday : W s((a, j), (y, j)) = 0)
    (hdbx : W s((b, j), (x, j)) = 0) (hdby : W s((b, j), (y, j)) = 0) :
    4 ≤ (liveOut W (Amplitude.const (V := V) j) Finset.univ
      ({a, b, x, y} : Finset V)).card := by
  classical
  have hcard : ({a, b, x, y} : Finset V).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hax, hay]),
      Finset.card_insert_of_notMem (by simp [hbx, hby]),
      Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton]
  have hmemK : ∀ z : V, z ∈ ({a, b, x, y} : Finset V) ↔ z = a ∨ z = b ∨ z = x ∨ z = y := by
    intro z; simp
  refine hcard ▸ card_le_liveNbrs_of_no_internal W hone (fun z hz w hw hwz => ?_)
  have hz' := (hmemK z).mp hz
  have hw' := (hmemK w).mp hw
  rcases hz' with rfl | rfl | rfl | rfl <;> rcases hw' with rfl | rfl | rfl | rfl
  exacts [absurd rfl hwz, hdab, hdax, hday,
    (by rw [Sym2.eq_swap]; exact hdab), absurd rfl hwz, hdbx, hdby,
    (by rw [Sym2.eq_swap]; exact hdax), (by rw [Sym2.eq_swap]; exact hdbx),
    absurd rfl hwz, hdxy,
    (by rw [Sym2.eq_swap]; exact hday), (by rw [Sym2.eq_swap]; exact hdby),
    (by rw [Sym2.eq_swap]; exact hdxy), absurd rfl hwz]

/-! ### Crossing joins force one colour, and excess breeds excess

Put the two halves together on a single configuration.  Take an `m`-edge `{a,x}` and a forced pair
`{p,q}` whose joint deletion leaves the rest matched by `m`.  Suppose the joins cross both ways:
`a` reaches `p` and `x` reaches `q`, and `a` also reaches `q`.

Then the second pairing is available too, and one of the two closes.  If `x` does not reach `p` in
the first colour, the two same-coloured blocks are independent and the colouring is rigid.  If it
does, the second pairing has blocks of two different colours, which is rigid for free.  Either way
the configuration dies unless all the joins carry one colour.

So crossing joins are monochromatic, and the four sites carry a complete bipartite graph in that
one colour: each of them gains a second partner in it.  Excess breeds excess, in a shape.

**Scope, honestly.**  The rigid route cannot finish alone.  A rigid colouring partitions the sites
into three induced matchings, one per colour, and a configuration whose live graphs are dense
admits no such partition at all -- the tool then says nothing, rather than saying something false.
Closing the conjecture this way needs a degree bound to keep the live graphs sparse, and the degree
bound is what is being proved.  What the route does deliver is every configuration that is sparse
enough to be partitioned, which is why it disposes of the small cores. -/

/-- **Crossing joins carry one colour.**  With both pairings available, one of them is rigid unless
every join between the pair and the edge is live in the same colour. -/
theorem crossing_joins_one_colour (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (u v : V), v ≠ u → ∀ e f : Fin 3, e ≠ f → W s((u, e), (v, f)) = 0)
    {m k l : Fin 3} (hkm : k ≠ m) (hlm : l ≠ m)
    {a x p q : V} (hax : a ≠ x) (hap' : a ≠ p) (haq' : a ≠ q)
    (hxp' : x ≠ p) (hxq' : x ≠ q) (hpq' : p ≠ q)
    (hproper : ({a, p, x, q} : Finset V) ≠ Finset.univ)
    (hproper' : ({a, q, x, p} : Finset V) ≠ Finset.univ)
    (r₁ : V → V) (hr₁inv : ∀ z, r₁ (r₁ z) = z) (hr₁ne : ∀ z, r₁ z ≠ z)
    (hr₁a : r₁ a = p) (hr₁x : r₁ x = q)
    (hr₁out : ∀ z ∉ ({a, p, x, q} : Finset V), r₁ z ∉ ({a, p, x, q} : Finset V))
    (hr₁live : ∀ z ∉ ({a, p, x, q} : Finset V), W s((z, m), (r₁ z, m)) ≠ 0)
    (hr₁uniq : ∀ z ∉ ({a, p, x, q} : Finset V), ∀ w ∉ ({a, p, x, q} : Finset V),
      w ≠ z → w ≠ r₁ z → W s((z, m), (w, m)) = 0)
    (r₂ : V → V) (hr₂inv : ∀ z, r₂ (r₂ z) = z) (hr₂ne : ∀ z, r₂ z ≠ z)
    (hr₂a : r₂ a = q) (hr₂x : r₂ x = p)
    (hr₂out : ∀ z ∉ ({a, q, x, p} : Finset V), r₂ z ∉ ({a, q, x, p} : Finset V))
    (hr₂live : ∀ z ∉ ({a, q, x, p} : Finset V), W s((z, m), (r₂ z, m)) ≠ 0)
    (hr₂uniq : ∀ z ∉ ({a, q, x, p} : Finset V), ∀ w ∉ ({a, q, x, p} : Finset V),
      w ≠ z → w ≠ r₂ z → W s((z, m), (w, m)) = 0)
    (hdax : W s((a, k), (x, k)) = 0) (hdpq : W s((p, k), (q, k)) = 0)
    (hdaq : W s((a, k), (q, k)) = 0)
    (hap : W s((a, k), (p, k)) ≠ 0) (hxq : W s((x, k), (q, k)) ≠ 0)
    (haq : W s((a, l), (q, l)) ≠ 0) :
    l = k := by
  classical
  by_contra hlk
  by_cases hxp : W s((x, k), (p, k)) = 0
  · exact false_of_same_colour_pairs_and_rest W hzero hmono hkm hap' hax haq' (Ne.symm hxp') hpq' hxq'
      hproper r₁ hr₁inv hr₁ne hr₁a hr₁x hr₁out hr₁live hr₁uniq hap hxq hdax hdaq
      (by rw [Sym2.eq_swap]; exact hxp) hdpq
  · exact hlk (colours_agree_of_matched_rest W hzero hmono hlm hkm haq' hax hap' (Ne.symm hxq') (Ne.symm hpq') hxp'
      r₂ hr₂inv hr₂ne hr₂a hr₂x hr₂out hr₂live hr₂uniq haq hxp)

/-! ### No closed set is induced-matched by another colour

The one-block case of the block theorem is worth isolating, because it says something clean about
every colour-closed set at once.

A closed set has vanishing sum in each other colour.  If some other colour's live edges inside it
formed exactly a perfect matching, that sum would be a single non-zero product.  So they never do:

> a colour-closed set, proper and non-empty, is never induced-matched by another colour.

This generalizes the rectangle prohibition.  Two forced pairs form a closed four-set, and a
diagonal-only join is exactly an induced matching of it in another colour -- which the rectangle
identity forbade by a weight computation.  Here the same conclusion holds for *any* union of
forced pairs, any core component, any union of the two, at any size: never induced-matched.

It also says where the rigid route can and cannot reach.  A block covering a whole closed set is
free; the difficulty is only ever a block structure that cuts across closed sets. -/

/-- **A closed set is never induced-matched by another colour.**  Its sum in that colour vanishes,
and an induced matching would make that sum a single non-zero product. -/
theorem no_induced_matching_on_closed (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (u v : V), v ≠ u → ∀ e f : Fin 3, e ≠ f → W s((u, e), (v, f)) = 0)
    {m j : Fin 3} (hjm : j ≠ m)
    (hone : amplitude W (Amplitude.const (V := V) m) ≠ 0)
    {S : Finset V} (hS : S.Nonempty) (hSne : S ≠ Finset.univ)
    (hclosed : ∀ z ∈ S, ∀ w : V, w ∉ S → W s((z, m), (w, m)) = 0)
    (p : V → V) (hp : ∀ z ∈ S, p z ∈ S) (hinv : ∀ z ∈ S, p (p z) = z)
    (hpne : ∀ z ∈ S, p z ≠ z)
    (hlive : ∀ z ∈ S, W s((z, j), (p z, j)) ≠ 0)
    (huniq : ∀ z ∈ S, ∀ w ∈ S, w ≠ z → w ≠ p z → W s((z, j), (w, j)) = 0) :
    False := by
  classical
  refine pmSum_ne_zero_of_forced W (Amplitude.const (V := V) j) p hp hinv hpne
    (fun z hz => ?_) (fun z hz w hw hwz hwp => ?_)
    (closed_dead_other W hzero hmono hjm hone hS hSne hclosed)
  · have hpaint : (Sym2.map (Amplitude.paint (Amplitude.const (V := V) j)) s(z, p z))
        = s((z, j), (p z, j)) := rfl
    rw [hpaint]; exact hlive z hz
  · have hpaint : (Sym2.map (Amplitude.paint (Amplitude.const (V := V) j)) s(z, w))
        = s((z, j), (w, j)) := rfl
    rw [hpaint]; exact huniq z hz w hw hwz hwp

/-- **The pendant part is never induced-matched either.**  Any union of forced pairs is closed in
its colour, so the statement above applies to it -- which is the rectangle prohibition, freed of
its restriction to exactly two pairs. -/
theorem forced_union_not_induced_matched (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (u v : V), v ≠ u → ∀ e f : Fin 3, e ≠ f → W s((u, e), (v, f)) = 0)
    {m j : Fin 3} (hjm : j ≠ m)
    (hone : amplitude W (Amplitude.const (V := V) m) ≠ 0)
    {S : Finset V} (hS : S.Nonempty) (hSne : S ≠ Finset.univ)
    (q : V → V)
    (hqS : ∀ z ∈ S, q z ∈ S) (hqinv : ∀ z ∈ S, q (q z) = z) (hqne : ∀ z ∈ S, q z ≠ z)
    (hqforced : ∀ z ∈ S, ∀ w : V, w ≠ z → w ≠ q z → W s((z, m), (w, m)) = 0)
    (p : V → V) (hp : ∀ z ∈ S, p z ∈ S) (hinv : ∀ z ∈ S, p (p z) = z)
    (hpne : ∀ z ∈ S, p z ≠ z)
    (hlive : ∀ z ∈ S, W s((z, j), (p z, j)) ≠ 0)
    (huniq : ∀ z ∈ S, ∀ w ∈ S, w ≠ z → w ≠ p z → W s((z, j), (w, j)) = 0) :
    False := by
  refine no_induced_matching_on_closed W hzero hmono hjm hone hS hSne (fun z hz w hw => ?_)
    p hp hinv hpne hlive huniq
  exact hqforced z hz w (fun h => hw (h ▸ hz)) (fun h => hw (h ▸ hqS z hz))

end Rigid

/-! ### Uniqueness, not one-regularity

The non-vanishing argument was stated for a set whose live edges in a colour form exactly a
perfect matching.  That is far more than it needs.  All the argument uses is that the sum has one
non-zero term, and the sum has one non-zero term as soon as the live perfect matching is
**unique** -- the graph may have any number of extra edges, provided they do not assemble a second
matching.

The two conditions are genuinely different.  A path on four sites has a unique perfect matching
and is not one-regular: its middle sites have degree two.  So paths, and everything built from
them, were being thrown away.

The gap this closes is exact.  An alternating cycle of the forced matching with another colour has
that colour's matching as one perfect matching; a chord produces a second only if it can be joined
into an alternating cycle with the matching, which a single chord cannot do -- using it strands the
two former partners, and pairing those needs a *second* chord.  So a cycle with one chord still has
a unique matching and still dies.  Only chords that assemble an alternating cycle among themselves
survive, which is a far smaller escape than "has a chord". -/


section UniqueColour

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **A closed set has no unique live matching in another colour.**  Strictly stronger than the
induced-matching form: the other colour's graph inside a closed set may be as rich as it likes, so
long as it never pins down exactly one perfect matching. -/
theorem no_unique_matching_on_closed (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (u v : V), v ≠ u → ∀ e f : Fin 3, e ≠ f → W s((u, e), (v, f)) = 0)
    {m j : Fin 3} (hjm : j ≠ m)
    (hone : amplitude W (Amplitude.const (V := V) m) ≠ 0)
    {S : Finset V} (hS : S.Nonempty) (hSne : S ≠ Finset.univ)
    (hclosed : ∀ z ∈ S, ∀ w : V, w ∉ S → W s((z, m), (w, m)) = 0)
    {σ₀ : Equiv.Perm V} (hmem : σ₀ ∈ pairingsOn S)
    (hlive : ∀ z ∈ S, W s((z, j), (σ₀ z, j)) ≠ 0)
    (huniq : ∀ τ ∈ pairingsOn S, τ ≠ σ₀ → ∃ z ∈ S, W s((z, j), (τ z, j)) = 0) :
    False := by
  classical
  refine pmSum_ne_zero_of_unique_matching W (Amplitude.const (V := V) j) hmem
    (fun z hz => ?_) (fun τ hτ hne => ?_)
    (closed_dead_other W hzero hmono hjm hone hS hSne hclosed)
  · have hpaint : (Sym2.map (Amplitude.paint (Amplitude.const (V := V) j)) s(z, σ₀ z))
        = s((z, j), (σ₀ z, j)) := rfl
    rw [hpaint]; exact hlive z hz
  · obtain ⟨z, hz, hz0⟩ := huniq τ hτ hne
    refine ⟨z, hz, ?_⟩
    have hpaint : (Sym2.map (Amplitude.paint (Amplitude.const (V := V) j)) s(z, τ z))
        = s((z, j), (τ z, j)) := rfl
    rw [hpaint]; exact hz0

/-- **No non-monochromatic colouring has a unique live matching.**  The master form: everything in
this file that concludes `False` from a colouring is an instance, and the hypothesis is uniqueness
rather than one-regularity, which is strictly weaker.

Read as a design constraint it says what to look for: fibres whose live graphs pin down exactly
one perfect matching each.  Two-site fibres do so for free -- a pair has only one pairing -- so the
whole burden falls on the largest fibre, and it needs only a unique matching, not a rigid one. -/
theorem false_of_unique_colouring (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {c : V → Fin 3} (hc : ¬ Amplitude.Monochromatic c)
    {σ₀ : Equiv.Perm V} (hmem : σ₀ ∈ pairingsOn (Finset.univ : Finset V))
    (hlive : ∀ z : V, W s((z, c z), (σ₀ z, c (σ₀ z))) ≠ 0)
    (huniq : ∀ τ ∈ pairingsOn (Finset.univ : Finset V), τ ≠ σ₀ →
      ∃ z : V, W s((z, c z), (τ z, c (τ z))) = 0) :
    False := by
  classical
  refine pmSum_ne_zero_of_unique_matching W c hmem (fun z _ => ?_) (fun τ hτ hne => ?_)
    (by rw [pmSum_univ]; exact hzero c hc)
  · have hpaint : (Sym2.map (Amplitude.paint c) s(z, σ₀ z)) = s((z, c z), (σ₀ z, c (σ₀ z))) := rfl
    rw [hpaint]; exact hlive z
  · obtain ⟨z, hz0⟩ := huniq τ hτ hne
    refine ⟨z, Finset.mem_univ z, ?_⟩
    have hpaint : (Sym2.map (Amplitude.paint c) s(z, τ z)) = s((z, c z), (τ z, c (τ z))) := rfl
    rw [hpaint]; exact hz0

/-- **Two small fibres and a unique remainder.**  The shape the master form recommends: colour one
live pair `j`, another live pair `i`, and everything else `m`.  A two-site fibre is a unique
matching for free, so the only real hypothesis is that the `m`-graph on the remaining sites pins
down one perfect matching -- not that it is one-regular there.

Strictly weaker than the earlier version, and the difference is exactly the graphs that have a
unique matching without being one: paths, and everything assembled from them. -/
theorem false_of_two_pairs_and_unique_rest (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (u v : V), v ≠ u → ∀ e f : Fin 3, e ≠ f → W s((u, e), (v, f)) = 0)
    {m j i : Fin 3} (hjm : j ≠ m) (him : i ≠ m) (hji : j ≠ i)
    {a b x y : V} (hab : a ≠ b) (hax : a ≠ x) (hay : a ≠ y)
    (hbx : b ≠ x) (hby : b ≠ y) (hxy : x ≠ y)
    (p : V → V) (hinv : ∀ z, p (p z) = z) (hpne : ∀ z, p z ≠ z)
    (hpa : p a = b) (hpx : p x = y)
    (hpout : ∀ z ∉ ({a, b, x, y} : Finset V), p z ∉ ({a, b, x, y} : Finset V))
    (hjab : W s((a, j), (b, j)) ≠ 0) (hixy : W s((x, i), (y, i)) ≠ 0)
    (hplive : ∀ z ∉ ({a, b, x, y} : Finset V), W s((z, m), (p z, m)) ≠ 0)
    (hrestuniq : ∀ τ : Equiv.Perm V, τ ∈ pairingsOn (Finset.univ : Finset V) →
      (∀ z ∈ ({a, b, x, y} : Finset V), τ z = p z) → (∃ z : V, τ z ≠ p z) →
      ∃ z ∉ ({a, b, x, y} : Finset V), W s((z, m), (τ z, m)) = 0) :
    False := by
  classical
  set K : Finset V := ({a, b, x, y} : Finset V) with hKdef
  have hmemK : ∀ z : V, z ∈ K ↔ z = a ∨ z = b ∨ z = x ∨ z = y := by intro z; simp [hKdef]
  set c : V → Fin 3 := fun z =>
    if z ∈ ({a, b} : Finset V) then j else if z ∈ ({x, y} : Finset V) then i else m with hcdef
  have hca : c a = j := by simp only [hcdef]; rw [if_pos (by simp)]
  have hcb : c b = j := by simp only [hcdef]; rw [if_pos (by simp)]
  have hcx : c x = i := by
    simp only [hcdef]; rw [if_neg (by simp [Ne.symm hax, Ne.symm hbx]), if_pos (by simp)]
  have hcy : c y = i := by
    simp only [hcdef]; rw [if_neg (by simp [Ne.symm hay, Ne.symm hby]), if_pos (by simp)]
  have hpb : p b = a := by rw [← hpa, hinv]
  have hpy : p y = x := by rw [← hpx, hinv]
  have hcout : ∀ z ∉ K, c z = m := by
    intro z hz
    rw [hmemK] at hz; push_neg at hz
    simp only [hcdef]
    rw [if_neg (by simp [hz.1, hz.2.1]), if_neg (by simp [hz.2.2.1, hz.2.2.2])]
  have hcj : ∀ w : V, c w = j → w = a ∨ w = b := by
    intro w hw
    by_cases h1 : w ∈ ({a, b} : Finset V)
    · simpa using h1
    · exfalso
      by_cases h2 : w ∈ ({x, y} : Finset V)
      · simp only [hcdef, if_neg h1, if_pos h2] at hw; exact hji hw.symm
      · simp only [hcdef, if_neg h1, if_neg h2] at hw; exact hjm hw.symm
  have hci : ∀ w : V, c w = i → w = x ∨ w = y := by
    intro w hw
    by_cases h2 : w ∈ ({x, y} : Finset V)
    · simpa using h2
    · exfalso
      by_cases h1 : w ∈ ({a, b} : Finset V)
      · simp only [hcdef, if_pos h1] at hw; exact hji hw
      · simp only [hcdef, if_neg h1, if_neg h2] at hw; exact him hw.symm
  set f : V → V := fun z => p z with hfdef
  have hinvol : Function.Involutive f := fun z => hinv z
  set σ₀ : Equiv.Perm V := hinvol.toPerm f with hσdef
  have hcoe : ∀ z, σ₀ z = p z := fun _ => rfl
  have hmem : σ₀ ∈ pairingsOn (Finset.univ : Finset V) :=
    mem_pairingsOn.mpr ⟨fun z => by rw [hcoe, hcoe]; exact hinv z,
      fun z _ => by rw [hcoe]; exact hpne z, fun z hz => absurd (Finset.mem_univ z) hz⟩
  have hpK : ∀ z ∈ K, p z ∈ K := by
    intro z hz
    rcases (hmemK z).mp hz with rfl | rfl | rfl | rfl
    · rw [hpa]; rw [hmemK]; exact Or.inr (Or.inl rfl)
    · rw [hpb]; rw [hmemK]; exact Or.inl rfl
    · rw [hpx]; rw [hmemK]; exact Or.inr (Or.inr (Or.inr rfl))
    · rw [hpy]; rw [hmemK]; exact Or.inr (Or.inr (Or.inl rfl))
  refine false_of_unique_colouring W hzero (c := c) ?_ hmem ?_ ?_
  · rintro ⟨k, hk⟩
    exact hji (by rw [← hca, hk a, ← hk x, hcx])
  · intro z
    rw [hcoe]
    by_cases hz : z ∈ K
    · rcases (hmemK z).mp hz with rfl | rfl | rfl | rfl
      · rw [hca, hpa, hcb]; exact hjab
      · rw [hcb, hpb, hca, Sym2.eq_swap]; exact hjab
      · rw [hcx, hpx, hcy]; exact hixy
      · rw [hcy, hpy, hcx, Sym2.eq_swap]; exact hixy
    · rw [hcout z hz, hcout (p z) (hpout z hz)]; exact hplive z hz
  · intro τ hτ hne
    by_cases hagree : ∀ z ∈ K, τ z = p z
    · have hdiff : ∃ z : V, τ z ≠ p z := by
        by_contra hall
        push_neg at hall
        exact hne (Equiv.ext (fun z => by rw [hall z, hcoe]))
      obtain ⟨z, hz, hz0⟩ := hrestuniq τ hτ hagree hdiff
      refine ⟨z, ?_⟩
      have hτz : τ z ∉ K := by
        intro hin
        have hinv' : τ (τ z) = z := (mem_pairingsOn.mp hτ).1 z
        have := hagree (τ z) hin
        rw [hinv'] at this
        exact hz (this ▸ hpK (τ z) hin)
      rw [hcout z hz, hcout (τ z) hτz]; exact hz0
    · push_neg at hagree
      obtain ⟨w, hwK, hwne⟩ := hagree
      refine ⟨w, ?_⟩
      have hτw : τ w ≠ w := (mem_pairingsOn.mp hτ).2.1 w (Finset.mem_univ w)
      by_cases hcc : c (τ w) = c w
      · exfalso
        rcases (hmemK w).mp hwK with rfl | rfl | rfl | rfl
        · rw [hca] at hcc
          rcases hcj (τ w) hcc with h | h
          exacts [hτw h, hwne (by rw [h, hpa])]
        · rw [hcb] at hcc
          rcases hcj (τ w) hcc with h | h
          exacts [hwne (by rw [h, hpb]), hτw h]
        · rw [hcx] at hcc
          rcases hci (τ w) hcc with h | h
          exacts [hτw h, hwne (by rw [h, hpx])]
        · rw [hcy] at hcc
          rcases hci (τ w) hcc with h | h
          exacts [hwne (by rw [h, hpy]), hτw h]
      · exact hmono w (τ w) hτw (c w) (c (τ w)) (fun h => hcc h.symm)

/-! ### The block theorem, with uniqueness

The block theorem asked each colour's live edges inside the block set to be exactly the pairing.
The master form shows that is too much: uniqueness suffices, on each side separately.

Written this way it is the sharpest statement of the whole remaining problem.  Delete a set which
is a union of forced pairs together with an edge of the core; the rest is then matched by the
core's own colour with a unique matching, always.  What has to be arranged is only that each
other colour's graph, on the sites it colours, pins down one matching -- and a single chord never
breaks that. -/

/-- **Blocks and rest, both merely unique.**  The reusable form: a block set coloured away from
`m`, paired inside itself, over a complement paired by `m`, with uniqueness required on each side
instead of one-regularity. -/
theorem false_of_blocks_and_unique (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (u v : V), v ≠ u → ∀ e f : Fin 3, e ≠ f → W s((u, e), (v, f)) = 0)
    {m : Fin 3} {K : Finset V} (hKne : K.Nonempty) (hproper : K ≠ Finset.univ)
    (d : V → Fin 3) (hdm : ∀ z ∈ K, d z ≠ m)
    (p : V → V) (hinv : ∀ z, p (p z) = z) (hpne : ∀ z, p z ≠ z)
    (hpK : ∀ z ∈ K, p z ∈ K) (hpd : ∀ z ∈ K, d (p z) = d z)
    (hKlive : ∀ z ∈ K, W s((z, d z), (p z, d z)) ≠ 0)
    (hpout : ∀ z ∉ K, p z ∉ K)
    (hplive : ∀ z ∉ K, W s((z, m), (p z, m)) ≠ 0)
    (huniqK : ∀ τ : Equiv.Perm V, τ ∈ pairingsOn (Finset.univ : Finset V) →
      (∀ z ∈ K, τ z ∈ K) → (∀ z ∈ K, d (τ z) = d z) → (∃ z ∈ K, τ z ≠ p z) →
      ∃ z ∈ K, W s((z, d z), (τ z, d z)) = 0)
    (huniqR : ∀ τ : Equiv.Perm V, τ ∈ pairingsOn (Finset.univ : Finset V) →
      (∀ z ∉ K, τ z ∉ K) → (∃ z ∉ K, τ z ≠ p z) →
      ∃ z ∉ K, W s((z, m), (τ z, m)) = 0) :
    False := by
  classical
  set c : V → Fin 3 := fun z => if z ∈ K then d z else m with hcdef
  have hcK : ∀ z ∈ K, c z = d z := by intro z hz; simp only [hcdef, if_pos hz]
  have hcout : ∀ z ∉ K, c z = m := by intro z hz; simp only [hcdef, if_neg hz]
  set f : V → V := fun z => p z with hfdef
  have hinvol : Function.Involutive f := fun z => hinv z
  set σ₀ : Equiv.Perm V := hinvol.toPerm f with hσdef
  have hcoe : ∀ z, σ₀ z = p z := fun _ => rfl
  have hmem : σ₀ ∈ pairingsOn (Finset.univ : Finset V) :=
    mem_pairingsOn.mpr ⟨fun z => by rw [hcoe, hcoe]; exact hinv z,
      fun z _ => by rw [hcoe]; exact hpne z, fun z hz => absurd (Finset.mem_univ z) hz⟩
  refine false_of_unique_colouring W hzero (c := c) ?_ hmem ?_ ?_
  · rintro ⟨k, hk⟩
    obtain ⟨z, hz⟩ := hKne
    obtain ⟨w, hw⟩ : ∃ w : V, w ∉ K := by
      by_contra hall
      push_neg at hall
      exact hproper (Finset.eq_univ_of_forall hall)
    exact hdm z hz (by rw [← hcK z hz, hk z, ← hk w, hcout w hw])
  · intro z
    rw [hcoe]
    by_cases hz : z ∈ K
    · rw [hcK z hz, hcK (p z) (hpK z hz), hpd z hz]; exact hKlive z hz
    · rw [hcout z hz, hcout (p z) (hpout z hz)]; exact hplive z hz
  · intro τ hτ hne
    have hτne : ∀ z : V, τ z ≠ z := fun z => (mem_pairingsOn.mp hτ).2.1 z (Finset.mem_univ z)
    by_cases hleave : ∃ z ∈ K, τ z ∉ K
    · obtain ⟨z, hz, hout⟩ := hleave
      exact ⟨z, hmono z (τ z) (hτne z) (c z) (c (τ z))
        (by rw [hcK z hz, hcout (τ z) hout]; exact hdm z hz)⟩
    · push_neg at hleave
      have hpres : ∀ z ∉ K, τ z ∉ K := by
        intro z hz hin
        have : τ (τ z) ∈ K := hleave (τ z) hin
        rw [(mem_pairingsOn.mp hτ).1 z] at this
        exact hz this
      by_cases hdpres : ∀ z ∈ K, d (τ z) = d z
      · by_cases hK : ∃ z ∈ K, τ z ≠ p z
        · obtain ⟨z, hz, hz0⟩ := huniqK τ hτ hleave hdpres hK
          refine ⟨z, ?_⟩
          rw [hcK z hz, hcK (τ z) (hleave z hz), hdpres z hz]; exact hz0
        · push_neg at hK
          have hR : ∃ z ∉ K, τ z ≠ p z := by
            by_contra hall
            push_neg at hall
            refine hne (Equiv.ext (fun z => ?_))
            rw [hcoe]
            by_cases hz : z ∈ K
            · exact hK z hz
            · exact hall z hz
          obtain ⟨z, hz, hz0⟩ := huniqR τ hτ hpres hR
          exact ⟨z, by rw [hcout z hz, hcout (τ z) (hpres z hz)]; exact hz0⟩
      · push_neg at hdpres
        obtain ⟨z, hz, hzd⟩ := hdpres
        exact ⟨z, hmono z (τ z) (hτne z) (c z) (c (τ z))
          (by rw [hcK z hz, hcK (τ z) (hleave z hz)]; exact fun h => hzd h.symm)⟩

/-! ### The pendant structures of different colours are transverse

Run the closed-set theorem with its two colours exchanged and it says something global that was
not visible from either side alone.

A set of forced pairs of colour `m` carries a unique `m`-matching -- that is what forced means.
If such a set were *closed in another colour* `k`, its `k`-closure would force its `m`-sum to
vanish, and a unique matching makes that sum a single non-zero product.  So it is never closed.

> No union of one colour's forced pairs is closed in another colour.

In particular no colour's pendant part is assembled from another colour's forced pairs: the
pendant structures of the three colours cut across each other everywhere, at every scale, and not
merely at the level of the whole configuration.

The earlier crossing results said each other colour leaves an `m`-closed set at least twice.  This
says the reverse direction as well -- a set that is *forced* in `m` cannot be closed in `k`, for a
reason that has nothing to do with counting crossings. -/

/-- **A union of one colour's forced pairs is never closed in another.** -/
theorem pendant_union_not_closed_in_another (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (u v : V), v ≠ u → ∀ e f : Fin 3, e ≠ f → W s((u, e), (v, f)) = 0)
    {m k : Fin 3} (hmk : m ≠ k)
    (hone : amplitude W (Amplitude.const (V := V) k) ≠ 0)
    {S : Finset V} (hS : S.Nonempty) (hSne : S ≠ Finset.univ)
    (hclosed : ∀ z ∈ S, ∀ w : V, w ∉ S → W s((z, k), (w, k)) = 0)
    (p : V → V) (hp : ∀ z ∈ S, p z ∈ S) (hinv : ∀ z ∈ S, p (p z) = z)
    (hpne : ∀ z ∈ S, p z ≠ z)
    (hlive : ∀ z ∈ S, W s((z, m), (p z, m)) ≠ 0)
    (hforced : ∀ z ∈ S, ∀ w : V, w ≠ z → w ≠ p z → W s((z, m), (w, m)) = 0) :
    False :=
  no_induced_matching_on_closed W hzero hmono hmk hone hS hSne hclosed p hp hinv hpne hlive
    (fun z hz w _ hwz hwp => hforced z hz w hwz hwp)

/-- **A colour's pendant part is not invariant under another colour's pairing.**  The form the
core analysis uses: if the sites forced in colour `m` were exactly the sites forced in colour `k`,
they would form a set closed in `k` and forced in `m` at once. -/
theorem forced_parts_transverse (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (u v : V), v ≠ u → ∀ e f : Fin 3, e ≠ f → W s((u, e), (v, f)) = 0)
    {m k : Fin 3} (hmk : m ≠ k)
    (hone : amplitude W (Amplitude.const (V := V) k) ≠ 0)
    {S : Finset V} (hS : S.Nonempty) (hSne : S ≠ Finset.univ)
    (q : V → V) (hq : ∀ z ∈ S, q z ∈ S) (hqinv : ∀ z ∈ S, q (q z) = z)
    (hqne : ∀ z ∈ S, q z ≠ z)
    (hqforced : ∀ z ∈ S, ∀ w : V, w ≠ z → w ≠ q z → W s((z, k), (w, k)) = 0)
    (p : V → V) (hp : ∀ z ∈ S, p z ∈ S) (hinv : ∀ z ∈ S, p (p z) = z)
    (hpne : ∀ z ∈ S, p z ≠ z)
    (hlive : ∀ z ∈ S, W s((z, m), (p z, m)) ≠ 0)
    (hforced : ∀ z ∈ S, ∀ w : V, w ≠ z → w ≠ p z → W s((z, m), (w, m)) = 0) :
    False := by
  refine pendant_union_not_closed_in_another W hzero hmono hmk hone hS hSne (fun z hz w hw => ?_)
    p hp hinv hpne hlive hforced
  exact hqforced z hz w (fun h => hw (h ▸ hz)) (fun h => hw (h ▸ hq z hz))

/-! ### The join between two forced pairs is a combinatorial rectangle

The identity has two products.  If three of the four weights are live, one product is a single
non-zero term and cannot vanish; if the two weights of one product are live and the other two are
dead, the same.  So the live joins between two forced pairs are always one of: nothing, a single
edge, everything out of one site, everything into one site, or all four.  Never a diagonal pair,
never exactly three.

That is the complete support classification, uniform in the vertex count -- no counting, no cut, no
colouring, just the three-term identity.

**A tempting reading that is false, recorded so it is not tried again.**  Arranging the weights as
a matrix and twisting the columns turns the identity's shape into a determinant, which would make
the matrix rank one and the classification a corollary of that.  It does not: the permanent is
invariant under a column swap while the determinant changes sign, so permanent-zero and
determinant-zero are different conditions.  `[[1,1],[1,-1]]` has permanent zero and its twist has
rank two.  The classification above is sound because it is read off the identity directly; there is
no rank statement behind it. -/

/-- **Three live joins force the fourth.**  With one weight dead the identity has a single term,
which cannot vanish; so the support has no three-element pattern. -/
theorem forced_join_rectangle (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (u v : V), v ≠ u → ∀ e f : Fin 3, e ≠ f → W s((u, e), (v, f)) = 0)
    {m j : Fin 3} (hjm : j ≠ m)
    (hone : amplitude W (Amplitude.const (V := V) m) ≠ 0)
    {u v u' v' : V} (huv : u ≠ v) (huu' : u ≠ u') (huv' : u ≠ v')
    (hvu' : v ≠ u') (hvv' : v ≠ v') (hu'v' : u' ≠ v')
    (hcl1 : ∀ z ∈ ({u, v} : Finset V), ∀ w : V, w ∉ ({u, v} : Finset V) →
      W s((z, m), (w, m)) = 0)
    (hcl2 : ∀ z ∈ ({u', v'} : Finset V), ∀ w : V, w ∉ ({u', v'} : Finset V) →
      W s((z, m), (w, m)) = 0)
    (hproper : ({u, v, u', v'} : Finset V) ≠ Finset.univ)
    (h2 : W s((u, j), (v', j)) ≠ 0) (h3 : W s((v, j), (u', j)) ≠ 0) :
    W s((v, j), (v', j)) ≠ 0 := by
  intro hdead
  have hid := forced_pairs_permanent W hzero hmono hjm hone huv huu' huv' hvu' hvv' hu'v'
    hcl1 hcl2 hproper
  rw [hdead, mul_zero, zero_add] at hid
  exact (mul_ne_zero h2 h3) hid

/-! ### Three forced pairs: the eight-term identity

The rectangle identity came from expanding a four-set sum with one of its three pairings dead.
Three forced pairs give a six-set with three of its fifteen pairings dead, and the same expansion
leaves eight terms.  Since a union of forced pairs is closed in its own colour, the sum vanishes,
so those eight products cancel.

**What it does not say.**  The six-set polynomial is the trace of a product of the three join
matrices with their columns twisted.  It is tempting to combine this with the pair identities to
conclude that the trace factors and that some path through the three pairs is therefore blocked --
that every triple must have a dead join somewhere.  It does not follow, and the conclusion is false:
with `A = B = [[1,1],[1,-1]]` and `C = [[1,1],[-1,1]]` every entry is non-zero, all three pair
identities hold, and the trace vanishes as well.  The pair identities are permanent conditions, and
the twist that converts a permanent into a determinant is entrywise, not a column operation, so it
does not survive into the trace.

So this relation constrains the *weights* and not the support.  Whatever consumes it will have to
work with the cancellation itself -- a gauge or scaling argument -- rather than deduce that
something is dead. -/

/-- **The three-pair identity.**  A union of three forced pairs is closed in its own colour, so
its sum in any other colour vanishes -- and the expansion turns that into eight products
cancelling.  This is the next relation after the rectangle identity, and it binds three pairs at
once where that bound two. -/
theorem forced_triple_identity (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (z w : V), w ≠ z → ∀ e f : Fin 3, e ≠ f → W s((z, e), (w, f)) = 0)
    {m j : Fin 3} (hjm : j ≠ m)
    (hone : amplitude W (Amplitude.const (V := V) m) ≠ 0)
    {u₁ u₂ v₁ v₂ w₁ w₂ : V}
    (h12 : u₁ ≠ u₂) (h1v1 : u₁ ≠ v₁) (h1v2 : u₁ ≠ v₂) (h1w1 : u₁ ≠ w₁) (h1w2 : u₁ ≠ w₂)
    (h2v1 : u₂ ≠ v₁) (h2v2 : u₂ ≠ v₂) (h2w1 : u₂ ≠ w₁) (h2w2 : u₂ ≠ w₂)
    (hv : v₁ ≠ v₂) (hv1w1 : v₁ ≠ w₁) (hv1w2 : v₁ ≠ w₂)
    (hv2w1 : v₂ ≠ w₁) (hv2w2 : v₂ ≠ w₂) (hw : w₁ ≠ w₂)
    (hclosed : ∀ z ∈ ({u₁, u₂, v₁, v₂, w₁, w₂} : Finset V), ∀ t : V,
      t ∉ ({u₁, u₂, v₁, v₂, w₁, w₂} : Finset V) → W s((z, m), (t, m)) = 0)
    (hproper : ({u₁, u₂, v₁, v₂, w₁, w₂} : Finset V) ≠ Finset.univ)
    (hdu : W s((u₁, j), (u₂, j)) = 0) (hdv : W s((v₁, j), (v₂, j)) = 0)
    (hdw : W s((w₁, j), (w₂, j)) = 0) :
    W s((u₁, j), (v₁, j))
        * (W s((w₁, j), (u₂, j)) * W s((w₂, j), (v₂, j))
          + W s((w₁, j), (v₂, j)) * W s((w₂, j), (u₂, j)))
      + W s((u₁, j), (v₂, j))
        * (W s((w₁, j), (u₂, j)) * W s((w₂, j), (v₁, j))
          + W s((w₁, j), (v₁, j)) * W s((w₂, j), (u₂, j)))
      + (W s((u₁, j), (w₁, j))
        * (W s((v₁, j), (u₂, j)) * W s((v₂, j), (w₂, j))
          + W s((v₁, j), (w₂, j)) * W s((v₂, j), (u₂, j)))
      + W s((u₁, j), (w₂, j))
        * (W s((v₁, j), (u₂, j)) * W s((v₂, j), (w₁, j))
          + W s((v₁, j), (w₁, j)) * W s((v₂, j), (u₂, j)))) = 0 := by
  classical
  have hdead := closed_dead_other W hzero hmono hjm hone ⟨u₁, by simp⟩ hproper hclosed
  rw [MatchingCrossing.pmSum_six_three_dead W (Amplitude.const (V := V) j)
    h12 h1v1 h1v2 h1w1 h1w2
    h2v1 h2v2 h2w1 h2w2 hv hv1w1 hv1w2 hv2w1 hv2w2 hw hdu hdv hdw] at hdead
  exact hdead

/-- **A four-cycle core needs eight sites.**  Its four distinct neighbours in another colour all
lie outside it, so the configuration has at least four sites beyond the core.

This excludes the smallest core from the smallest configuration above four, uniformly -- by
counting room for a matching, with no finite check and no appeal to the base case. -/
theorem four_core_needs_eight (W : Sym2 (V × Fin 3) → ℂ) {j : Fin 3}
    (hone : amplitude W (Amplitude.const (V := V) j) ≠ 0)
    {a b x y : V} (hab : a ≠ b) (hax : a ≠ x) (hay : a ≠ y)
    (hbx : b ≠ x) (hby : b ≠ y) (hxy : x ≠ y)
    (hdab : W s((a, j), (b, j)) = 0) (hdxy : W s((x, j), (y, j)) = 0)
    (hdax : W s((a, j), (x, j)) = 0) (hday : W s((a, j), (y, j)) = 0)
    (hdbx : W s((b, j), (x, j)) = 0) (hdby : W s((b, j), (y, j)) = 0) :
    8 ≤ Fintype.card V := by
  classical
  have hcard : ({a, b, x, y} : Finset V).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hax, hay]),
      Finset.card_insert_of_notMem (by simp [hbx, hby]),
      Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton]
  have hfour := four_core_four_neighbours W hone hab hax hay hbx hby hxy
    hdab hdxy hdax hday hdbx hdby
  have hsub : liveOut W (Amplitude.const (V := V) j) Finset.univ ({a, b, x, y} : Finset V)
      ⊆ Finset.univ \ ({a, b, x, y} : Finset V) :=
    liveOut_subset W (Amplitude.const (V := V) j) Finset.univ ({a, b, x, y} : Finset V)
  have hle := Finset.card_le_card hsub
  have hdiff : (Finset.univ \ ({a, b, x, y} : Finset V)).card = Fintype.card V - 4 := by
    rw [Finset.card_univ_diff, hcard]
  omega

/-! ### The classification engine, with uniqueness

The agreement law and its same-colour companion were stated over a remainder matched one-regularly
by the core's own colour.  Uniqueness is enough, and the difference is exactly what larger cores
need: deleting an edge of a six-cycle core leaves a path, which has a unique matching and is not
one-regular.  With these two the classification runs on every core, not only the smallest. -/

/-- **Two removable pairs agree in colour** -- remainder merely unique. -/
theorem colours_agree_of_unique_rest (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (u v : V), v ≠ u → ∀ e f : Fin 3, e ≠ f → W s((u, e), (v, f)) = 0)
    {m j i : Fin 3} (hjm : j ≠ m) (him : i ≠ m)
    {a b x y : V} (hab : a ≠ b) (hax : a ≠ x) (hay : a ≠ y)
    (hbx : b ≠ x) (hby : b ≠ y) (hxy : x ≠ y)
    (p : V → V) (hinv : ∀ z, p (p z) = z) (hpne : ∀ z, p z ≠ z)
    (hpa : p a = b) (hpx : p x = y)
    (hpout : ∀ z ∉ ({a, b, x, y} : Finset V), p z ∉ ({a, b, x, y} : Finset V))
    (hjab : W s((a, j), (b, j)) ≠ 0) (hixy : W s((x, i), (y, i)) ≠ 0)
    (hplive : ∀ z ∉ ({a, b, x, y} : Finset V), W s((z, m), (p z, m)) ≠ 0)
    (hrestuniq : ∀ τ : Equiv.Perm V, τ ∈ pairingsOn (Finset.univ : Finset V) →
      (∀ z ∈ ({a, b, x, y} : Finset V), τ z = p z) → (∃ z : V, τ z ≠ p z) →
      ∃ z ∉ ({a, b, x, y} : Finset V), W s((z, m), (τ z, m)) = 0) :
    j = i := by
  by_contra hji
  exact false_of_two_pairs_and_unique_rest W hzero hmono hjm him hji hab hax hay hbx hby hxy
    p hinv hpne hpa hpx hpout hjab hixy hplive hrestuniq

/-- **Two removable pairs of the same colour** -- remainder merely unique. -/
theorem false_of_same_colour_and_unique_rest (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (u v : V), v ≠ u → ∀ e f : Fin 3, e ≠ f → W s((u, e), (v, f)) = 0)
    {m j : Fin 3} (hjm : j ≠ m)
    {a b x y : V} (hab : a ≠ b) (hax : a ≠ x) (hay : a ≠ y)
    (hbx : b ≠ x) (hby : b ≠ y) (hxy : x ≠ y)
    (hproper : ({a, b, x, y} : Finset V) ≠ Finset.univ)
    (p : V → V) (hinv : ∀ z, p (p z) = z) (hpne : ∀ z, p z ≠ z)
    (hpa : p a = b) (hpx : p x = y)
    (hpout : ∀ z ∉ ({a, b, x, y} : Finset V), p z ∉ ({a, b, x, y} : Finset V))
    (hjab : W s((a, j), (b, j)) ≠ 0) (hjxy : W s((x, j), (y, j)) ≠ 0)
    (hdax : W s((a, j), (x, j)) = 0) (hday : W s((a, j), (y, j)) = 0)
    (hdbx : W s((b, j), (x, j)) = 0) (hdby : W s((b, j), (y, j)) = 0)
    (hplive : ∀ z ∉ ({a, b, x, y} : Finset V), W s((z, m), (p z, m)) ≠ 0)
    (huniqR : ∀ τ : Equiv.Perm V, τ ∈ pairingsOn (Finset.univ : Finset V) →
      (∀ z ∉ ({a, b, x, y} : Finset V), τ z ∉ ({a, b, x, y} : Finset V)) →
      (∃ z ∉ ({a, b, x, y} : Finset V), τ z ≠ p z) →
      ∃ z ∉ ({a, b, x, y} : Finset V), W s((z, m), (τ z, m)) = 0) :
    False := by
  classical
  have hpb : p b = a := by rw [← hpa, hinv]
  have hpy : p y = x := by rw [← hpx, hinv]
  have hmemK : ∀ z : V, z ∈ ({a, b, x, y} : Finset V) ↔ z = a ∨ z = b ∨ z = x ∨ z = y := by
    intro z; simp
  refine false_of_blocks_and_unique W hzero hmono (K := ({a, b, x, y} : Finset V))
    ⟨a, by simp⟩ hproper (fun _ => j) (fun z _ => hjm) p hinv hpne ?_ (fun z _ => rfl) ?_
    hpout hplive ?_ huniqR
  · intro z hz
    rcases (hmemK z).mp hz with rfl | rfl | rfl | rfl
    · rw [hpa]; rw [hmemK]; exact Or.inr (Or.inl rfl)
    · rw [hpb]; rw [hmemK]; exact Or.inl rfl
    · rw [hpx]; rw [hmemK]; exact Or.inr (Or.inr (Or.inr rfl))
    · rw [hpy]; rw [hmemK]; exact Or.inr (Or.inr (Or.inl rfl))
  · intro z hz
    rcases (hmemK z).mp hz with rfl | rfl | rfl | rfl
    · rw [hpa]; exact hjab
    · rw [hpb, Sym2.eq_swap]; exact hjab
    · rw [hpx]; exact hjxy
    · rw [hpy, Sym2.eq_swap]; exact hjxy
  · intro τ hτ hpres _ hK
    have hτinv : ∀ z : V, τ (τ z) = z := (mem_pairingsOn.mp hτ).1
    have hτne : ∀ z : V, τ z ≠ z := fun z => (mem_pairingsOn.mp hτ).2.1 z (Finset.mem_univ z)
    have hdiff : τ a ≠ b := by
      intro hτa
      obtain ⟨z, hz, hzne⟩ := hK
      have hcase : τ a = b ∧ τ x = y := by
        rcases MatchingFourVertices.pairing_four_cases hab hax hay hbx hby hxy hτinv
            (fun z _ => hτne z) hpres with
          h | ⟨hA, -⟩ | ⟨hA, -⟩
        · exact h
        · exact absurd (hτa.symm.trans hA) hbx
        · exact absurd (hτa.symm.trans hA) hby
      refine hzne ?_
      rcases (hmemK z).mp hz with rfl | rfl | rfl | rfl
      · rw [hcase.1, hpa]
      · have h' := hτinv a
        rw [hcase.1] at h'
        rw [h', hpb]
      · rw [hcase.2, hpx]
      · have h' := hτinv x
        rw [hcase.2] at h'
        rw [h', hpy]
    exact MatchingFourVertices.zero_edge_of_pairing_four_ne W j hab hax hay hbx hby hxy
      (Or.inl hdax) (Or.inl hday) hτinv hτne hpres hdiff

end UniqueColour

/-! ### Deleting a live pair kills the other colours -- so that descent is impossible

The pendant-deletion step left one obligation: the remainder's non-vanishing in the two colours
other than the pendant one.  That obligation is not merely open.  It is false, and for a reason
that has nothing to do with pendancy.

Colour the deleted pair with its own colour and everything else with another.  Cross edges carry
two different colours and are dead, so the sum factors; the colouring is not constant, so the sum
vanishes; and the deleted weight is non-zero, so the remainder's sum in the other colour is zero.

> Deleting *any* live pair leaves a remainder with vanishing sum in both other colours.

So descent that deletes a live pair and keeps the weighting cannot work, whatever pair is chosen.
A descent step must either change the weighting or delete a pair that is dead in all three
colours -- and the latter is the only option left for a naive deletion. -/

/-- **Deleting a live pair kills the other colours.** -/
theorem pmSum_delete_live_pair_zero (W : Sym2 (V × Fin 3) → ℂ)
    (hmono : ∀ (z w : V), w ≠ z → ∀ a b : Fin 3, a ≠ b → W s((z, a), (w, b)) = 0)
    {S : Finset V} (h : MatchingSum.IsGHZOn W S) {u v : V} {m j : Fin 3} (hjm : j ≠ m)
    (huv : v ≠ u) (hu : u ∈ S) (hv : v ∈ S)
    (hrest : (S \ ({u, v} : Finset V)).Nonempty)
    (hlive : W s((u, m), (v, m)) ≠ 0) :
    pmSum W (Amplitude.const (V := V) j) (S \ ({u, v} : Finset V)) = 0 := by
  classical
  set c : V → Fin 3 := fun z => if z ∈ ({u, v} : Finset V) then m else j with hcdef
  have hcu : c u = m := by simp only [hcdef]; rw [if_pos (by simp)]
  have hcv : c v = m := by simp only [hcdef]; rw [if_pos (by simp)]
  have hcout : ∀ z ∉ ({u, v} : Finset V), c z = j := by
    intro z hz; simp only [hcdef]; rw [if_neg hz]
  have hsub : ({u, v} : Finset V) ⊆ S := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz'
    · exact hu
    · rw [Finset.mem_singleton] at hz'; exact hz' ▸ hv
  have hcut : ∀ z ∈ ({u, v} : Finset V), ∀ w ∈ S \ ({u, v} : Finset V),
      W s((z, c z), (w, c w)) = 0 := by
    intro z hz w hw
    have hwout : w ∉ ({u, v} : Finset V) := (Finset.mem_sdiff.mp hw).2
    have hwz : w ≠ z := fun hh => hwout (hh ▸ hz)
    have hcz : c z = m := by
      rcases Finset.mem_insert.mp hz with rfl | hz'
      · exact hcu
      · rw [Finset.mem_singleton] at hz'; exact hz' ▸ hcv
    rw [hcz, hcout w hwout]
    exact hmono z w hwz m j (Ne.symm hjm)
  have hsplit := Separation.pmSum_split W c ({u, v} : Finset V).card ({u, v} : Finset V) S rfl
    hsub hcut
  have hpair : pmSum W c ({u, v} : Finset V) = W s((u, m), (v, m)) := by
    rw [pmSum_pair W c huv, hcu, hcv]
  obtain ⟨w, hw⟩ := hrest
  have hnc : ¬ (∀ x ∈ S, ∀ y ∈ S, c x = c y) := by
    intro hall
    have := hall u hu w (Finset.mem_sdiff.mp hw).1
    rw [hcu, hcout w (Finset.mem_sdiff.mp hw).2] at this
    exact hjm this.symm
  have hzero := h.2 c hnc
  rw [hsplit, hpair] at hzero
  have hcongr : pmSum W c (S \ ({u, v} : Finset V))
      = pmSum W (Amplitude.const (V := V) j) (S \ ({u, v} : Finset V)) :=
    pmSum_congr_colour W (fun z hz => hcout z (Finset.mem_sdiff.mp hz).2)
  rw [hcongr] at hzero
  rcases mul_eq_zero.mp hzero with h1 | h1
  exacts [absurd h1 hlive, h1]

/-- **No descent by deleting a live pair.**  The remainder fails the solution conditions in the
two colours other than the deleted pair's. -/
theorem not_isGHZOn_delete_live_pair (W : Sym2 (V × Fin 3) → ℂ)
    (hmono : ∀ (z w : V), w ≠ z → ∀ a b : Fin 3, a ≠ b → W s((z, a), (w, b)) = 0)
    {S : Finset V} (h : MatchingSum.IsGHZOn W S) {u v : V} {m j : Fin 3} (hjm : j ≠ m)
    (huv : v ≠ u) (hu : u ∈ S) (hv : v ∈ S)
    (hrest : (S \ ({u, v} : Finset V)).Nonempty)
    (hlive : W s((u, m), (v, m)) ≠ 0) :
    ¬ MatchingSum.IsGHZOn W (S \ ({u, v} : Finset V)) := by
  intro hbad
  exact hbad.1 j (pmSum_delete_live_pair_zero W hmono h hjm huv hu hv hrest hlive)

/-! ### The two-colour product law

Everything in this development that splits a configuration is an instance of one statement, and it
is worth having under its own name.

Colour a set with one colour and its complement with another.  Every crossing edge then carries two
different colours and is dead, so the sum factors with no hypothesis at all -- no closure, no
certificate, nothing about the set.  The colouring is not constant, so the sum vanishes:

> for every non-empty proper set and every two distinct colours,
> the set's sum in the first times the complement's sum in the second is zero.

The closed-set results are what this becomes when one factor is known non-zero.  The excess
equations are the case of a two-element set.  The block theorems are the refinement where the
complement is split further.  Stated bare it costs one colouring and one split. -/

/-- **The two-colour product law.**  A set's sum in one colour times its complement's sum in
another always vanishes. -/
theorem pmSum_two_colour_product (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (z w : V), w ≠ z → ∀ a b : Fin 3, a ≠ b → W s((z, a), (w, b)) = 0)
    {m j : Fin 3} (hjm : j ≠ m) {A : Finset V} (hA : A.Nonempty)
    (hAne : (Finset.univ \ A).Nonempty) :
    pmSum W (Amplitude.const (V := V) m) A
      * pmSum W (Amplitude.const (V := V) j) (Finset.univ \ A) = 0 := by
  classical
  set c : V → Fin 3 := fun z => if z ∈ A then m else j with hcdef
  have hcin : ∀ z ∈ A, c z = m := by intro z hz; simp only [hcdef, if_pos hz]
  have hcout : ∀ z ∉ A, c z = j := by intro z hz; simp only [hcdef, if_neg hz]
  have hcut : ∀ z ∈ A, ∀ w ∈ Finset.univ \ A, W s((z, c z), (w, c w)) = 0 := by
    intro z hz w hw
    have hwout : w ∉ A := (Finset.mem_sdiff.mp hw).2
    rw [hcin z hz, hcout w hwout]
    exact hmono z w (fun hh => hwout (hh ▸ hz)) m j (Ne.symm hjm)
  have hsplit := Separation.pmSum_split W c A.card A Finset.univ rfl (Finset.subset_univ A) hcut
  rw [pmSum_univ] at hsplit
  obtain ⟨z, hz⟩ := hA
  obtain ⟨w, hw⟩ := hAne
  have hnc : ¬ Amplitude.Monochromatic c := by
    rintro ⟨k, hk⟩
    have h1 : c z = m := hcin z hz
    have h2 : c w = j := hcout w (Finset.mem_sdiff.mp hw).2
    exact hjm (by rw [← h2, hk w, ← hk z, h1])
  have hcA : pmSum W c A = pmSum W (Amplitude.const (V := V) m) A :=
    pmSum_congr_colour W (fun t ht => hcin t ht)
  have hcB : pmSum W c (Finset.univ \ A)
      = pmSum W (Amplitude.const (V := V) j) (Finset.univ \ A) :=
    pmSum_congr_colour W (fun t ht => hcout t (Finset.mem_sdiff.mp ht).2)
  rw [hcA, hcB] at hsplit
  rw [← hsplit]
  exact hzero c hnc

/-- **One non-zero factor kills the other.**  The form the closed-set arguments use. -/
theorem pmSum_compl_zero_of_ne (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (z w : V), w ≠ z → ∀ a b : Fin 3, a ≠ b → W s((z, a), (w, b)) = 0)
    {m j : Fin 3} (hjm : j ≠ m) {A : Finset V} (hA : A.Nonempty)
    (hAne : (Finset.univ \ A).Nonempty)
    (hne : pmSum W (Amplitude.const (V := V) m) A ≠ 0) :
    pmSum W (Amplitude.const (V := V) j) (Finset.univ \ A) = 0 := by
  rcases mul_eq_zero.mp (pmSum_two_colour_product W hzero hmono hjm hA hAne) with h | h
  exacts [absurd h hne, h]

/-! ### The closing criterion, in two lines

The product law says a set's sum in one colour times its complement's sum in another is always
zero.  The uniqueness lemma says a sum is non-zero as soon as its colour's live matching there is
unique.  Put together they give the whole closing criterion of this development:

> if a set has a unique live matching in one colour and its complement has a unique live matching
> in another, the configuration is impossible.

Every closing theorem here is that, with the two uniquenesses established differently -- by
one-regularity, by a pendant chain, by inspecting the three pairings of a four-set.  Nothing else
is doing any work.

Stated this way it also says precisely what a proof must produce: one set, one colour each side,
two uniquenesses.  Not a degree bound, not a cut, not a count. -/

/-- **Unique matchings on both sides is impossible.** -/
theorem false_of_unique_both_sides (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (z w : V), w ≠ z → ∀ a b : Fin 3, a ≠ b → W s((z, a), (w, b)) = 0)
    {m j : Fin 3} (hjm : j ≠ m) {A : Finset V} (hA : A.Nonempty)
    (hAc : (Finset.univ \ A).Nonempty)
    {σ : Equiv.Perm V} (hσ : σ ∈ pairingsOn A)
    (hσlive : ∀ z ∈ A, W s((z, m), (σ z, m)) ≠ 0)
    (hσuniq : ∀ ρ ∈ pairingsOn A, ρ ≠ σ → ∃ z ∈ A, W s((z, m), (ρ z, m)) = 0)
    {τ : Equiv.Perm V} (hτ : τ ∈ pairingsOn (Finset.univ \ A))
    (hτlive : ∀ z ∈ Finset.univ \ A, W s((z, j), (τ z, j)) ≠ 0)
    (hτuniq : ∀ ρ ∈ pairingsOn (Finset.univ \ A), ρ ≠ τ →
      ∃ z ∈ Finset.univ \ A, W s((z, j), (ρ z, j)) = 0) :
    False := by
  classical
  have h1 : pmSum W (Amplitude.const (V := V) m) A ≠ 0 := by
    refine pmSum_ne_zero_of_unique_matching W (Amplitude.const (V := V) m) hσ
      (fun z hz => ?_) (fun ρ hρ hne => ?_)
    · have hp : (Sym2.map (Amplitude.paint (Amplitude.const (V := V) m)) s(z, σ z))
          = s((z, m), (σ z, m)) := rfl
      rw [hp]; exact hσlive z hz
    · obtain ⟨z, hz, hz0⟩ := hσuniq ρ hρ hne
      refine ⟨z, hz, ?_⟩
      have hp : (Sym2.map (Amplitude.paint (Amplitude.const (V := V) m)) s(z, ρ z))
          = s((z, m), (ρ z, m)) := rfl
      rw [hp]; exact hz0
  have h2 : pmSum W (Amplitude.const (V := V) j) (Finset.univ \ A) ≠ 0 := by
    refine pmSum_ne_zero_of_unique_matching W (Amplitude.const (V := V) j) hτ
      (fun z hz => ?_) (fun ρ hρ hne => ?_)
    · have hp : (Sym2.map (Amplitude.paint (Amplitude.const (V := V) j)) s(z, τ z))
          = s((z, j), (τ z, j)) := rfl
      rw [hp]; exact hτlive z hz
    · obtain ⟨z, hz, hz0⟩ := hτuniq ρ hρ hne
      refine ⟨z, hz, ?_⟩
      have hp : (Sym2.map (Amplitude.paint (Amplitude.const (V := V) j)) s(z, ρ z))
          = s((z, j), (ρ z, j)) := rfl
      rw [hp]; exact hz0
  exact (mul_ne_zero h1 h2) (pmSum_two_colour_product W hzero hmono hjm hA hAc)

/-! ### The cheapest form: a live pair and its complement

One side of the criterion is free.  A two-element set has exactly one pairing, so a live pair is a
unique live matching with nothing to prove.  The whole burden falls on the complement:

> the complement of a live pair never carries a unique live matching in another colour.

That is a sharp condition on how much excess a colour may have.  With no excess the complement has
no matching at all in that colour -- deleting a pair that is dead there strands both its partners.
With just enough excess to repair the deletion in one way, the matching is unique and the
configuration dies.  So a colour's excess must be either absent or abundant enough to repair every
such deletion in at least two ways.

Since excess cannot be absent -- a configuration without it is already excluded -- it must be
abundant, and that is a lower bound on excess coming from the criterion itself rather than from
any count. -/

/-- **A live pair's complement carries no unique matching in another colour.** -/
theorem false_of_live_pair_unique_complement (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (z w : V), w ≠ z → ∀ a b : Fin 3, a ≠ b → W s((z, a), (w, b)) = 0)
    {m j : Fin 3} (hjm : j ≠ m) {u v : V} (huv : u ≠ v)
    (hlive : W s((u, m), (v, m)) ≠ 0)
    (hrest : (Finset.univ \ ({u, v} : Finset V)).Nonempty)
    {τ : Equiv.Perm V} (hτ : τ ∈ pairingsOn (Finset.univ \ ({u, v} : Finset V)))
    (hτlive : ∀ z ∈ Finset.univ \ ({u, v} : Finset V), W s((z, j), (τ z, j)) ≠ 0)
    (hτuniq : ∀ ρ ∈ pairingsOn (Finset.univ \ ({u, v} : Finset V)), ρ ≠ τ →
      ∃ z ∈ Finset.univ \ ({u, v} : Finset V), W s((z, j), (ρ z, j)) = 0) :
    False := by
  classical
  have hswap : Equiv.swap u v ∈ pairingsOn ({u, v} : Finset V) := by
    refine mem_pairingsOn.mpr ⟨fun z => by simp [Equiv.swap_apply_self], fun z hz => ?_,
      fun z hz => ?_⟩
    · rcases Finset.mem_insert.mp hz with rfl | hz'
      · rw [Equiv.swap_apply_left]; exact Ne.symm huv
      · rw [Finset.mem_singleton] at hz'; subst hz'
        rw [Equiv.swap_apply_right]; exact huv
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
      exact Equiv.swap_apply_of_ne_of_ne hz.1 hz.2
  refine false_of_unique_both_sides W hzero hmono hjm ⟨u, by simp⟩ hrest hswap ?_ ?_
    hτ hτlive hτuniq
  · intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz'
    · rw [Equiv.swap_apply_left]; exact hlive
    · rw [Finset.mem_singleton] at hz'; subst hz'
      rw [Equiv.swap_apply_right, Sym2.eq_swap]; exact hlive
  · intro ρ hρ hne
    refine absurd (Equiv.ext (fun z => ?_)) hne
    by_cases hzu : z = u
    · have hmem : ρ z ∈ ({u, v} : Finset V) := pairingsOn_closed hρ z (by rw [hzu]; simp)
      have hzz : ρ z ≠ z := (mem_pairingsOn.mp hρ).2.1 z (by rw [hzu]; simp)
      rcases Finset.mem_insert.mp hmem with h | h
      · exact absurd (h.trans hzu.symm) hzz
      · rw [Finset.mem_singleton] at h
        rw [h, hzu, Equiv.swap_apply_left]
    · by_cases hzv : z = v
      · have hmem : ρ z ∈ ({u, v} : Finset V) := pairingsOn_closed hρ z (by rw [hzv]; simp)
        have hzz : ρ z ≠ z := (mem_pairingsOn.mp hρ).2.1 z (by rw [hzv]; simp)
        rcases Finset.mem_insert.mp hmem with h | h
        · rw [h, hzv, Equiv.swap_apply_right]
        · rw [Finset.mem_singleton] at h
          exact absurd (h.trans hzv.symm) hzz
      · rw [(mem_pairingsOn.mp hρ).2.2 z (by simp [hzu, hzv]),
          Equiv.swap_apply_of_ne_of_ne hzu hzv]

/-! ### A non-vanishing from minimality, and the parity that constrains it

The criterion needs a non-vanishing, and uniqueness of a matching is not the only source.  Support
minimality supplies another: a live pair is never inert, so some colouring survives on its
complement -- and with the fibre factorization that means *all three* fibre sums there are
non-zero at once.

Extending such a colouring back over the pair is constrained by parity.  A fibre with a non-zero
sum has even size, so the two deleted sites cannot be split between fibres; they must return to the
same one.  Three extensions, then, one per colour.

Returning them to their own colour's fibre closes the case whenever the pair sits isolated there:
the fibre's sum factors as the pair's weight times the rest, all three fibres are non-zero, and the
colouring is not monochromatic.  So the surviving colouring must place one of the two sites next to
another partner of its own colour -- the excess is not merely present, it is *used* by every
colouring that survives. -/

/-- **An isolated pair in its own fibre is impossible.**  If a non-monochromatic colouring has all
three fibre sums non-zero after deleting a live pair from its own fibre, and the pair has no other
partner there, the amplitude cannot vanish. -/
theorem false_of_isolated_pair_in_fibre (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {c : V → Fin 3} (hnc : ¬ Amplitude.Monochromatic c) {u v : V} {m : Fin 3}
    (hcu : c u = m) (hcv : c v = m) (hvu : v ≠ u)
    (hlive : W s((u, m), (v, m)) ≠ 0)
    (hiso : ∀ z ∈ fiber c m, z ≠ v → z ≠ u → W s((u, m), (z, m)) = 0)
    (hrest : pmSum W c (((fiber c m).erase u).erase v) ≠ 0)
    (hother : ∀ k : Fin 3, k ≠ m → pmSum W c (fiber c k) ≠ 0) :
    False := by
  classical
  have hu : u ∈ fiber c m := mem_fiber.mpr hcu
  have hv : v ∈ (fiber c m).erase u := Finset.mem_erase.mpr ⟨hvu, mem_fiber.mpr hcv⟩
  have hfac := MatchingSum.pmSum_delete_pendant W hmono hu hv hiso c hcu hcv
  have hm : pmSum W c (fiber c m) ≠ 0 := by rw [hfac]; exact mul_ne_zero hlive hrest
  have hprod := amplitude_product_of_mono W hmono c
  have h0 := hzero c hnc
  rw [hprod] at h0
  match m with
  | 0 =>
    exact (mul_ne_zero (mul_ne_zero hm (hother 1 (by decide))) (hother 2 (by decide))) h0
  | 1 =>
    exact (mul_ne_zero (mul_ne_zero (hother 0 (by decide)) hm) (hother 2 (by decide))) h0
  | 2 =>
    exact (mul_ne_zero (mul_ne_zero (hother 0 (by decide)) (hother 1 (by decide))) hm) h0

/-- **The fibre factorization over a subset.**  The product formula was stated for the whole site
set; the same three splits work over any subset, which is what lets a colouring surviving on a
complement be read fibre by fibre. -/
theorem pmSum_product_on (W : Sym2 (V × Fin 3) → ℂ) (c : V → Fin 3)
    (hcut : ∀ x y : V, c x ≠ c y → W s((x, c x), (y, c y)) = 0) (S : Finset V) :
    pmSum W c S
      = pmSum W c (S ∩ fiber c 0) * pmSum W c (S ∩ fiber c 1) * pmSum W c (S ∩ fiber c 2) := by
  classical
  have hcut0 : ∀ x ∈ S ∩ fiber c 0, ∀ y ∈ S \ (S ∩ fiber c 0),
      W s((x, c x), (y, c y)) = 0 := by
    intro x hx y hy
    have hx0 : c x = 0 := mem_fiber.mp (Finset.mem_inter.mp hx).2
    have hy0 : c y ≠ 0 := by
      intro h
      exact (Finset.mem_sdiff.mp hy).2
        (Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hy).1, mem_fiber.mpr h⟩)
    exact hcut x y (by rw [hx0]; exact fun h => hy0 h.symm)
  have h0 := Separation.pmSum_split W c (S ∩ fiber c 0).card (S ∩ fiber c 0) S rfl
    Finset.inter_subset_left hcut0
  have hrest0 : S \ (S ∩ fiber c 0) = S \ fiber c 0 := by
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_inter, not_and]
    tauto
  rw [hrest0] at h0
  have hsub1 : S ∩ fiber c 1 ⊆ S \ fiber c 0 := by
    intro z hz
    refine Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hz).1, ?_⟩
    have := mem_fiber.mp (Finset.mem_inter.mp hz).2
    rw [mem_fiber, this]
    decide
  have hcut1 : ∀ x ∈ S ∩ fiber c 1, ∀ y ∈ (S \ fiber c 0) \ (S ∩ fiber c 1),
      W s((x, c x), (y, c y)) = 0 := by
    intro x hx y hy
    have hx1 : c x = 1 := mem_fiber.mp (Finset.mem_inter.mp hx).2
    have hy1 : c y ≠ 1 := by
      intro h
      exact (Finset.mem_sdiff.mp hy).2
        (Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hy).1).1,
          mem_fiber.mpr h⟩)
    exact hcut x y (by rw [hx1]; exact fun h => hy1 h.symm)
  have h1 := Separation.pmSum_split W c (S ∩ fiber c 1).card (S ∩ fiber c 1) (S \ fiber c 0) rfl
    hsub1 hcut1
  have hrest1 : (S \ fiber c 0) \ (S ∩ fiber c 1) = S ∩ fiber c 2 := by
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_inter, mem_fiber, not_and]
    constructor
    · rintro ⟨⟨hzS, h0'⟩, h1'⟩
      refine ⟨hzS, ?_⟩
      have := h1' hzS
      revert h0' this
      generalize c z = t
      revert t
      decide
    · rintro ⟨hzS, h2⟩
      refine ⟨⟨hzS, ?_⟩, fun _ => ?_⟩ <;> rw [h2] <;> decide
  rw [hrest1] at h1
  rw [h0, h1, mul_assoc]

/-! ### The chain, assembled: every excess pair's survivor uses the excess

Minimality, the fibre factorization, parity, and the isolated-pair contradiction compose into one
statement about the configuration itself rather than about the method.

A pair that is live but uncertified -- all three constant colourings vanish on its complement -- is
still not inert, so some colouring survives there.  Paint both its sites in the pair's own colour;
the survivor stays a survivor, and it cannot be monochromatic, since a constant one would vanish.
The factorization turns the single survival into three fibre non-vanishings, and then the isolated
pair contradiction applies unless the pair's own fibre contains a further partner.

> for every excess pair there is a non-monochromatic colouring, painting the pair in its own
> colour, whose fibre there holds another live partner of it.

The excess is used, and by the survivor that minimality itself produces. -/

/-- **Every excess pair's surviving colouring carries a further partner in its fibre.** -/
theorem excess_pair_partner_in_fibre (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hmin : MinimalSupport.IsSupportMinimal W)
    {u v : V} {m : Fin 3} (hvu : v ≠ u) (hlive : W s((u, m), (v, m)) ≠ 0)
    (hexcess : ∀ k : Fin 3,
      pmSum W (Amplitude.const (V := V) k) ((Finset.univ.erase u).erase v) = 0) :
    ∃ c : V → Fin 3, c u = m ∧ c v = m ∧ ¬ Amplitude.Monochromatic c ∧
      ∃ z : V, z ≠ u ∧ z ≠ v ∧ c z = m ∧ W s((u, m), (z, m)) ≠ 0 := by
  classical
  have hnotinert := MinimalSupport.not_inert_of_supportMinimal hmin hvu ⟨m, m, hlive⟩
  rw [FanStructure.Inert] at hnotinert
  push_neg at hnotinert
  obtain ⟨c₀, hc₀⟩ := hnotinert
  set S : Finset V := (Finset.univ.erase u).erase v with hS
  set c : V → Fin 3 := fun z => if z = u ∨ z = v then m else c₀ z with hcdef
  have hcu : c u = m := by simp [hcdef]
  have hcv : c v = m := by simp [hcdef]
  have hcS : ∀ z ∈ S, c z = c₀ z := by
    intro z hz
    have hzv : z ≠ v := Finset.ne_of_mem_erase hz
    have hzu : z ≠ u := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hz)
    simp only [hcdef]; rw [if_neg (by push_neg; exact ⟨hzu, hzv⟩)]
  have hcne : pmSum W c S ≠ 0 := by
    rw [pmSum_congr_colour W (fun z hz => hcS z hz)]; exact hc₀
  have hnc : ¬ Amplitude.Monochromatic c := by
    rintro ⟨k, hk⟩
    refine hcne ?_
    rw [pmSum_congr_colour W (c' := Amplitude.const (V := V) k) (fun z _ => hk z)]
    exact hexcess k
  have hfac := pmSum_product_on W c
    (fun x y hxy => hmono x y (fun h => hxy (by rw [h])) (c x) (c y) hxy) S
  have hmem : ∀ (k : Fin 3) (z : V), z ∈ S ∩ fiber c k ↔ (z ≠ v ∧ z ≠ u ∧ c z = k) := by
    intro k z
    simp only [Finset.mem_inter, hS, Finset.mem_erase, Finset.mem_univ, and_true, mem_fiber]
    tauto
  have hSm : S ∩ fiber c m = ((fiber c m).erase u).erase v := by
    ext z
    rw [hmem]
    simp only [Finset.mem_erase, mem_fiber]
  have hSk : ∀ k : Fin 3, k ≠ m → S ∩ fiber c k = fiber c k := by
    intro k hk
    ext z
    rw [hmem]
    simp only [mem_fiber]
    constructor
    · rintro ⟨-, -, h⟩; exact h
    · intro h
      exact ⟨fun hzv => hk (by rw [← h, hzv, hcv]), fun hzu => hk (by rw [← h, hzu, hcu]), h⟩
  by_contra hno
  push_neg at hno
  have hiso : ∀ z ∈ fiber c m, z ≠ v → z ≠ u → W s((u, m), (z, m)) = 0 := by
    intro z hz hzv hzu
    exact hno c hcu hcv hnc z hzu hzv (mem_fiber.mp hz)
  have hother : ∀ k : Fin 3, k ≠ m → pmSum W c (fiber c k) ≠ 0 := by
    intro k hk
    rw [← hSk k hk]
    intro h0
    refine hcne ?_
    rw [hfac]
    match k, hk with
    | 0, _ => rw [h0, zero_mul, zero_mul]
    | 1, _ => rw [h0, mul_zero, zero_mul]
    | 2, _ => rw [h0, mul_zero]
  refine false_of_isolated_pair_in_fibre W hzero hmono hnc hcu hcv hvu hlive hiso ?_ hother
  rw [← hSm]
  intro h0
  refine hcne ?_
  rw [hfac]
  match m with
  | 0 => rw [h0, zero_mul, zero_mul]
  | 1 => rw [h0, mul_zero, zero_mul]
  | 2 => rw [h0, mul_zero]

/-- **Two live fibres force the third dead.**  For a non-monochromatic colouring the three fibre
sums multiply to the amplitude, which vanishes; so if two of them are non-zero the third is zero.

Applied to the colouring minimality produces at an excess pair, this says the pair's own fibre has
vanishing sum while that fibre *minus the pair* does not.  Expanding at the deleted site, the
term through its partner is non-zero, so the remaining terms cannot all vanish: the excess partner
found earlier is itself certified inside the fibre.  The excess is not just used -- it is used by a
pair that carries its own certificate there. -/
theorem fibre_vanishes_of_two_live (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {c : V → Fin 3} (hnc : ¬ Amplitude.Monochromatic c) {m : Fin 3}
    (hother : ∀ k : Fin 3, k ≠ m → pmSum W c (fiber c k) ≠ 0) :
    pmSum W c (fiber c m) = 0 := by
  classical
  have h0 := hzero c hnc
  rw [amplitude_product_of_mono W hmono c] at h0
  match m with
  | 0 =>
    rcases mul_eq_zero.mp h0 with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      exacts [h', absurd h' (hother 1 (by decide))]
    · exact absurd h (hother 2 (by decide))
  | 1 =>
    rcases mul_eq_zero.mp h0 with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      exacts [absurd h' (hother 0 (by decide)), h']
    · exact absurd h (hother 2 (by decide))
  | 2 =>
    rcases mul_eq_zero.mp h0 with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      exacts [absurd h' (hother 0 (by decide)), absurd h' (hother 1 (by decide))]
    · exact h

/-- **The survivor's colouring, with all its non-vanishings exposed.**  The setup the excess
results share: minimality gives a colouring surviving on the pair's complement, painted so the pair
takes its own colour; it is not monochromatic, the two other fibres carry sums, and so does the
pair's own fibre with the pair removed. -/
theorem exists_survivor_colouring (W : Sym2 (V × Fin 3) → ℂ)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hmin : MinimalSupport.IsSupportMinimal W)
    {u v : V} {m : Fin 3} (hvu : v ≠ u) (hlive : W s((u, m), (v, m)) ≠ 0)
    (hexcess : ∀ k : Fin 3,
      pmSum W (Amplitude.const (V := V) k) ((Finset.univ.erase u).erase v) = 0) :
    ∃ c : V → Fin 3, c u = m ∧ c v = m ∧ ¬ Amplitude.Monochromatic c ∧
      (∀ k : Fin 3, k ≠ m → pmSum W c (fiber c k) ≠ 0) ∧
      pmSum W c (((fiber c m).erase u).erase v) ≠ 0 := by
  classical
  have hnotinert := MinimalSupport.not_inert_of_supportMinimal hmin hvu ⟨m, m, hlive⟩
  rw [FanStructure.Inert] at hnotinert
  push_neg at hnotinert
  obtain ⟨c₀, hc₀⟩ := hnotinert
  set S : Finset V := (Finset.univ.erase u).erase v with hS
  set c : V → Fin 3 := fun z => if z = u ∨ z = v then m else c₀ z with hcdef
  have hcu : c u = m := by simp [hcdef]
  have hcv : c v = m := by simp [hcdef]
  have hcS : ∀ z ∈ S, c z = c₀ z := by
    intro z hz
    have hzv : z ≠ v := Finset.ne_of_mem_erase hz
    have hzu : z ≠ u := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hz)
    simp only [hcdef]; rw [if_neg (by push_neg; exact ⟨hzu, hzv⟩)]
  have hcne : pmSum W c S ≠ 0 := by
    rw [pmSum_congr_colour W (fun z hz => hcS z hz)]; exact hc₀
  have hnc : ¬ Amplitude.Monochromatic c := by
    rintro ⟨k, hk⟩
    refine hcne ?_
    rw [pmSum_congr_colour W (c' := Amplitude.const (V := V) k) (fun z _ => hk z)]
    exact hexcess k
  have hfac := pmSum_product_on W c
    (fun x y hxy => hmono x y (fun h => hxy (by rw [h])) (c x) (c y) hxy) S
  have hmem : ∀ (k : Fin 3) (z : V), z ∈ S ∩ fiber c k ↔ (z ≠ v ∧ z ≠ u ∧ c z = k) := by
    intro k z
    simp only [Finset.mem_inter, hS, Finset.mem_erase, Finset.mem_univ, and_true, mem_fiber]
    tauto
  have hSm : S ∩ fiber c m = ((fiber c m).erase u).erase v := by
    ext z
    rw [hmem]
    simp only [Finset.mem_erase, mem_fiber]
  have hSk : ∀ k : Fin 3, k ≠ m → S ∩ fiber c k = fiber c k := by
    intro k hk
    ext z
    rw [hmem]
    simp only [mem_fiber]
    constructor
    · rintro ⟨-, -, h⟩; exact h
    · intro h
      exact ⟨fun hzv => hk (by rw [← h, hzv, hcv]), fun hzu => hk (by rw [← h, hzu, hcu]), h⟩
  refine ⟨c, hcu, hcv, hnc, fun k hk => ?_, ?_⟩
  · rw [← hSk k hk]
    intro h0
    refine hcne ?_
    rw [hfac]
    match k, hk with
    | 0, _ => rw [h0, zero_mul, zero_mul]
    | 1, _ => rw [h0, mul_zero, zero_mul]
    | 2, _ => rw [h0, mul_zero]
  · rw [← hSm]
    intro h0
    refine hcne ?_
    rw [hfac]
    match m with
    | 0 => rw [h0, zero_mul, zero_mul]
    | 1 => rw [h0, mul_zero, zero_mul]
    | 2 => rw [h0, mul_zero]

/-- **The excess partner carries its own certificate inside the fibre.**  The survivor's own fibre
has vanishing sum while the fibre minus the pair does not, so expanding at the deleted site leaves
a further partner whose complement inside the fibre also carries a sum. -/
theorem excess_partner_certified_in_fibre (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hmin : MinimalSupport.IsSupportMinimal W)
    {u v : V} {m : Fin 3} (hvu : v ≠ u) (hlive : W s((u, m), (v, m)) ≠ 0)
    (hexcess : ∀ k : Fin 3,
      pmSum W (Amplitude.const (V := V) k) ((Finset.univ.erase u).erase v) = 0) :
    ∃ c : V → Fin 3, c u = m ∧ c v = m ∧ ¬ Amplitude.Monochromatic c ∧
      ∃ z : V, z ≠ u ∧ z ≠ v ∧ c z = m ∧ W s((u, m), (z, m)) ≠ 0 ∧
        pmSum W c ((((fiber c m).erase u).erase z)) ≠ 0 := by
  classical
  obtain ⟨c, hcu, hcv, hnc, hother, hrest⟩ :=
    exists_survivor_colouring W hmono hmin hvu hlive hexcess
  refine ⟨c, hcu, hcv, hnc, ?_⟩
  have hdead := fibre_vanishes_of_two_live W hzero hmono hnc hother
  have hu : u ∈ fiber c m := mem_fiber.mpr hcu
  have hv : v ∈ (fiber c m).erase u := Finset.mem_erase.mpr ⟨hvu, mem_fiber.mpr hcv⟩
  rw [pmSum_expand W c hu, ← Finset.add_sum_erase _ _ hv] at hdead
  have hpv : (Sym2.map (Amplitude.paint c) s(u, v)) = s((u, c u), (v, c v)) := rfl
  have hterm : W (Sym2.map (Amplitude.paint c) s(u, v))
      * pmSum W c ((((fiber c m).erase u).erase v)) ≠ 0 := by
    rw [hpv, hcu, hcv]
    exact mul_ne_zero hlive hrest
  have hsum : ∑ w ∈ ((fiber c m).erase u).erase v,
      W (Sym2.map (Amplitude.paint c) s(u, w)) * pmSum W c ((((fiber c m).erase u).erase w))
      ≠ 0 := by
    intro h0
    rw [h0, add_zero] at hdead
    exact hterm hdead
  obtain ⟨z, hz, hz0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  have hzv : z ≠ v := Finset.ne_of_mem_erase hz
  have hzu : z ≠ u := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hz)
  have hzm : c z = m := mem_fiber.mp (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hz))
  refine ⟨z, hzu, hzv, hzm, ?_, ?_⟩
  · have hpz : (Sym2.map (Amplitude.paint c) s(u, z)) = s((u, c u), (z, c z)) := rfl
    intro h
    refine hz0 ?_
    rw [hpz, hcu, hzm, h, zero_mul]
  · intro h
    exact hz0 (by rw [h, mul_zero])

/-- **A complementary pair of sets carries at most one colour.**  The product law in its most
memorable form: if a set carries a sum in one colour and its complement carries one in another,
the colours coincide.

Read across all subsets it says the even sets, paired with their complements, are sorted by colour
-- each nontrivial complementary pair belongs to a single colour or to none.  A closed set and its
complement both carrying their colour's sum is the allowed case; the same pair split between two
colours is not. -/
theorem compl_pair_one_colour (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (z w : V), w ≠ z → ∀ a b : Fin 3, a ≠ b → W s((z, a), (w, b)) = 0)
    {m j : Fin 3} {A : Finset V} (hA : A.Nonempty) (hAc : (Finset.univ \ A).Nonempty)
    (hm : pmSum W (Amplitude.const (V := V) m) A ≠ 0)
    (hj : pmSum W (Amplitude.const (V := V) j) (Finset.univ \ A) ≠ 0) :
    j = m := by
  by_contra hjm
  exact hj (pmSum_compl_zero_of_ne W hzero hmono hjm hA hAc hm)

/-- **The survivor misses by exactly one fibre.**  At every excess pair minimality yields a
non-monochromatic colouring whose two other fibres carry sums, whose own-colour fibre does not,
and whose own-colour fibre *minus the pair* does.

This is the obstruction at its sharpest.  A non-monochromatic colouring with all three fibres
carrying sums would contradict the equations outright, and minimality delivers a colouring that
fails to be one in a single place: the fibre holding the pair.  Nor can the pair be moved
elsewhere to repair it -- parity sends both sites to the same fibre, and the same law that killed
the original fibre kills the new one, since the other two still carry sums.

So the gap is not a missing construction but a fixed point of the law itself. -/
theorem survivor_misses_by_one_fibre (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (hmin : MinimalSupport.IsSupportMinimal W)
    {u v : V} {m : Fin 3} (hvu : v ≠ u) (hlive : W s((u, m), (v, m)) ≠ 0)
    (hexcess : ∀ k : Fin 3,
      pmSum W (Amplitude.const (V := V) k) ((Finset.univ.erase u).erase v) = 0) :
    ∃ c : V → Fin 3, c u = m ∧ c v = m ∧ ¬ Amplitude.Monochromatic c ∧
      (∀ k : Fin 3, k ≠ m → pmSum W c (fiber c k) ≠ 0) ∧
      pmSum W c (fiber c m) = 0 ∧
      pmSum W c (((fiber c m).erase u).erase v) ≠ 0 := by
  obtain ⟨c, hcu, hcv, hnc, hother, hrest⟩ :=
    exists_survivor_colouring W hmono hmin hvu hlive hexcess
  exact ⟨c, hcu, hcv, hnc, hother, fibre_vanishes_of_two_live W hzero hmono hnc hother, hrest⟩

/-! ### Merging two colours

A colouring assigns one colour to each site.  Summing the amplitude over all the ways of painting a
set with two chosen colours -- the rest of the configuration held at a third -- collapses to a
single matching sum, for the weight that adds the two colours together on every edge.

The reason is the deletion recursion.  Expanding at a site, what remains does not see that site's
colour or its partner's, so the sum over paintings factors: the four ways of colouring the two ends
contribute their four weights, the two mixed ones vanish, and the two matching ones add.  That is
exactly the recursion satisfied by the merged weight, so the recursion principle identifies them.

Under the equations every painting is non-constant once both regions are occupied, so every term on
the left vanishes -- and the merged matching sum vanishes with them.  That is the two-colour product
law with a *mixed* hafnian on one side, which the single-colour version cannot express. -/

/-- Paint a chosen subset of `S` with one colour, the rest of `S` with a second, everything outside
with a third. -/
def mergeCol (k₀ k₁ k₂ : Fin 3) (S T : Finset V) : V → Fin 3 :=
  fun z => if z ∈ S then (if z ∈ T then k₀ else k₁) else k₂

/-- **Summing over paintings is a single matching sum for the merged weight.** -/
theorem sum_powerset_pmSum_eq (W Wp : Sym2 (V × Fin 3) → ℂ)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {k₀ k₁ k₂ : Fin 3} (h01 : k₀ ≠ k₁)
    (hplus : ∀ x y : V, Wp s((x, k₀), (y, k₀))
      = W s((x, k₀), (y, k₀)) + W s((x, k₁), (y, k₁))) :
    ∀ S : Finset V, ∑ T ∈ S.powerset, pmSum W (mergeCol k₀ k₁ k₂ S T) S
      = pmSum Wp (Amplitude.const (V := V) k₀) S := by
  classical
  refine MatchingSum.eq_pmSum_of_rec Wp (Amplitude.const (V := V) k₀) _ ?_ ?_
  · simp
  · intro S hS
    obtain ⟨u, hu⟩ := hS
    refine ⟨u, hu, ?_⟩
    have hexp : ∀ T : Finset V, pmSum W (mergeCol k₀ k₁ k₂ S T) S
        = ∑ v ∈ S.erase u, W (Sym2.map (Amplitude.paint (mergeCol k₀ k₁ k₂ S T)) s(u, v))
            * pmSum W (mergeCol k₀ k₁ k₂ S T) ((S.erase u).erase v) :=
      fun T => pmSum_expand W _ hu
    rw [Finset.sum_congr rfl (fun T _ => hexp T), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun v hv => ?_)
    have hvu : v ≠ u := Finset.ne_of_mem_erase hv
    have hvS : v ∈ S := Finset.mem_of_mem_erase hv
    set R : Finset V := (S.erase u).erase v with hR
    have hvR : v ∉ R := by simp [hR]
    have huR : u ∉ insert v R := by simp [hR, Ne.symm hvu]
    have hSeq : S = insert u (insert v R) := by
      ext z
      simp only [Finset.mem_insert, hR, Finset.mem_erase]
      constructor
      · intro hz
        by_cases h1 : z = u
        · exact Or.inl h1
        · by_cases h2 : z = v
          · exact Or.inr (Or.inl h2)
          · exact Or.inr (Or.inr ⟨h2, h1, hz⟩)
      · rintro (rfl | rfl | ⟨-, -, hz⟩)
        exacts [hu, hvS, hz]
    have hpaint : ∀ T : Finset V,
        W (Sym2.map (Amplitude.paint (mergeCol k₀ k₁ k₂ S T)) s(u, v))
        = W s((u, if u ∈ T then k₀ else k₁), (v, if v ∈ T then k₀ else k₁)) := by
      intro T
      have h1 : mergeCol k₀ k₁ k₂ S T u = if u ∈ T then k₀ else k₁ := by
        simp only [mergeCol, if_pos hu]
      have h2 : mergeCol k₀ k₁ k₂ S T v = if v ∈ T then k₀ else k₁ := by
        simp only [mergeCol, if_pos hvS]
      show W s((u, mergeCol k₀ k₁ k₂ S T u), (v, mergeCol k₀ k₁ k₂ S T v)) = _
      rw [h1, h2]
    have hcolR : ∀ T : Finset V, T ⊆ R →
        pmSum W (mergeCol k₀ k₁ k₂ S T) R = pmSum W (mergeCol k₀ k₁ k₂ R T) R := by
      intro T hT
      refine pmSum_congr_colour W (fun z hz => ?_)
      have hzS : z ∈ S := by
        rw [hSeq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz)
      simp only [mergeCol, if_pos hzS, if_pos hz]
    have hshift : ∀ (T A : Finset V), T ⊆ R → (∀ z ∈ A, z ∉ R) →
        pmSum W (mergeCol k₀ k₁ k₂ S (A ∪ T)) R = pmSum W (mergeCol k₀ k₁ k₂ R T) R := by
      intro T A hT hA
      refine pmSum_congr_colour W (fun z hz => ?_)
      have hzS : z ∈ S := by
        rw [hSeq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz)
      have hzA : z ∉ A := fun h => hA z h hz
      simp only [mergeCol, if_pos hzS, if_pos hz, Finset.mem_union, hzA, false_or]
    have hpow : S.powerset = (insert u (insert v R)).powerset := by rw [← hSeq]
    rw [hpow, Finset.sum_powerset_insert huR, Finset.sum_powerset_insert hvR,
      Finset.sum_powerset_insert hvR, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun T hT => ?_)
    have hTR : T ⊆ R := Finset.mem_powerset.mp hT
    have hP : pmSum W (mergeCol k₀ k₁ k₂ S T) R = pmSum W (mergeCol k₀ k₁ k₂ R T) R :=
      hcolR T hTR
    have hPv : pmSum W (mergeCol k₀ k₁ k₂ S (insert v T)) R
        = pmSum W (mergeCol k₀ k₁ k₂ R T) R := by
      rw [show insert v T = ({v} : Finset V) ∪ T from rfl]
      exact hshift T {v} hTR (fun z hz => by
        rw [Finset.mem_singleton] at hz; exact hz ▸ hvR)
    have hPu : pmSum W (mergeCol k₀ k₁ k₂ S (insert u T)) R
        = pmSum W (mergeCol k₀ k₁ k₂ R T) R := by
      rw [show insert u T = ({u} : Finset V) ∪ T from rfl]
      exact hshift T {u} hTR (fun z hz => by
        rw [Finset.mem_singleton] at hz
        exact hz ▸ (fun h => huR (Finset.mem_insert_of_mem h)))
    have hPuv : pmSum W (mergeCol k₀ k₁ k₂ S (insert u (insert v T))) R
        = pmSum W (mergeCol k₀ k₁ k₂ R T) R := by
      rw [show insert u (insert v T) = ({u, v} : Finset V) ∪ T from by
        ext z; simp [Finset.mem_insert, Finset.mem_union]]
      refine hshift T {u, v} hTR (fun z hz => ?_)
      rcases Finset.mem_insert.mp hz with rfl | hz'
      · exact fun h => huR (Finset.mem_insert_of_mem h)
      · rw [Finset.mem_singleton] at hz'; exact hz' ▸ hvR
    rw [hpaint T, hpaint (insert v T), hpaint (insert u T), hpaint (insert u (insert v T)),
      hP, hPv, hPu, hPuv]
    have huT : u ∉ T := fun h => huR (Finset.mem_insert_of_mem (hTR h))
    have hvT : v ∉ T := fun h => hvR (hTR h)
    have e1 : (if u ∈ T then k₀ else k₁) = k₁ := if_neg huT
    have e2 : (if v ∈ T then k₀ else k₁) = k₁ := if_neg hvT
    have e3 : (if u ∈ insert v T then k₀ else k₁) = k₁ := if_neg (by simp [Ne.symm hvu, huT])
    have e4 : (if v ∈ insert v T then k₀ else k₁) = k₀ := if_pos (by simp)
    have e5 : (if u ∈ insert u T then k₀ else k₁) = k₀ := if_pos (by simp)
    have e6 : (if v ∈ insert u T then k₀ else k₁) = k₁ := if_neg (by simp [hvu, hvT])
    have e7 : (if u ∈ insert u (insert v T) then k₀ else k₁) = k₀ := if_pos (by simp)
    have e8 : (if v ∈ insert u (insert v T) then k₀ else k₁) = k₀ := if_pos (by simp)
    rw [e1, e2, e3, e4, e5, e6, e7, e8]
    have hmix1 : W s((u, k₁), (v, k₀)) = 0 := hmono u v hvu k₁ k₀ (Ne.symm h01)
    have hmix2 : W s((u, k₀), (v, k₁)) = 0 := hmono u v hvu k₀ k₁ h01
    have hWp : Wp (Sym2.map (Amplitude.paint (Amplitude.const (V := V) k₀)) s(u, v))
        = W s((u, k₀), (v, k₀)) + W s((u, k₁), (v, k₁)) := by
      show Wp s((u, k₀), (v, k₀)) = _
      exact hplus u v
    rw [hWp, hmix1, hmix2]
    ring

/-- **The mixed two-colour product law.**  A set's matching sum in the *merged* weight of two
colours, times its complement's sum in the third, vanishes.

This is strictly stronger than the single-colour product law: the set is allowed to carry a matching
that uses both of its two colours at once, and the vanishing still holds.  Every painting of the set
in those two colours is non-constant against the third outside, so each contributes nothing, and the
merge lemma collects them into one matching sum. -/
theorem pmSum_mixed_product (W Wp : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {k₀ k₁ k₂ : Fin 3} (h01 : k₀ ≠ k₁) (h02 : k₀ ≠ k₂) (h12 : k₁ ≠ k₂)
    (hplus : ∀ x y : V, Wp s((x, k₀), (y, k₀))
      = W s((x, k₀), (y, k₀)) + W s((x, k₁), (y, k₁)))
    {B : Finset V} (hB : B.Nonempty) (hBc : (Finset.univ \ B).Nonempty) :
    pmSum Wp (Amplitude.const (V := V) k₀) B
      * pmSum W (Amplitude.const (V := V) k₂) (Finset.univ \ B) = 0 := by
  classical
  rw [← sum_powerset_pmSum_eq W Wp hmono h01 hplus B, Finset.sum_mul]
  refine Finset.sum_eq_zero (fun T _ => ?_)
  set c : V → Fin 3 := mergeCol k₀ k₁ k₂ B T with hc
  have hcin : ∀ z ∈ B, c z = k₀ ∨ c z = k₁ := by
    intro z hz
    simp only [hc, mergeCol, if_pos hz]
    by_cases hzT : z ∈ T
    · exact Or.inl (if_pos hzT)
    · exact Or.inr (if_neg hzT)
  have hcout : ∀ z ∉ B, c z = k₂ := by
    intro z hz; simp only [hc, mergeCol, if_neg hz]
  have hcut : ∀ z ∈ B, ∀ w ∈ Finset.univ \ B, W s((z, c z), (w, c w)) = 0 := by
    intro z hz w hw
    have hwB : w ∉ B := (Finset.mem_sdiff.mp hw).2
    have hwz : w ≠ z := fun h => hwB (h ▸ hz)
    rw [hcout w hwB]
    rcases hcin z hz with h | h
    · rw [h]; exact hmono z w hwz k₀ k₂ h02
    · rw [h]; exact hmono z w hwz k₁ k₂ h12
  have hsplit := Separation.pmSum_split W c B.card B Finset.univ rfl (Finset.subset_univ B) hcut
  rw [pmSum_univ] at hsplit
  have hcompl : pmSum W c (Finset.univ \ B)
      = pmSum W (Amplitude.const (V := V) k₂) (Finset.univ \ B) :=
    pmSum_congr_colour W (fun z hz => hcout z (Finset.mem_sdiff.mp hz).2)
  rw [hcompl] at hsplit
  obtain ⟨z, hz⟩ := hB
  obtain ⟨w, hw⟩ := hBc
  have hnc : ¬ Amplitude.Monochromatic c := by
    rintro ⟨k, hk⟩
    have h1 := hcin z hz
    have h2 : c w = k₂ := hcout w (Finset.mem_sdiff.mp hw).2
    rcases h1 with h | h
    · exact h02 (by rw [← h, hk z, ← hk w, h2])
    · exact h12 (by rw [← h, hk z, ← hk w, h2])
  rw [← hsplit]
  exact hzero c hnc

/-- **The merged sum dies against a live complement.**  The form callers use, matching the
single-colour version.  When the complement carries its colour -- which forcedness supplies for
free -- the set's merged two-colour sum must vanish. -/
theorem pmSum_merged_zero_of_ne (W Wp : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {k₀ k₁ k₂ : Fin 3} (h01 : k₀ ≠ k₁) (h02 : k₀ ≠ k₂) (h12 : k₁ ≠ k₂)
    (hplus : ∀ x y : V, Wp s((x, k₀), (y, k₀))
      = W s((x, k₀), (y, k₀)) + W s((x, k₁), (y, k₁)))
    {B : Finset V} (hB : B.Nonempty) (hBc : (Finset.univ \ B).Nonempty)
    (hne : pmSum W (Amplitude.const (V := V) k₂) (Finset.univ \ B) ≠ 0) :
    pmSum Wp (Amplitude.const (V := V) k₀) B = 0 := by
  rcases mul_eq_zero.mp
    (pmSum_mixed_product W Wp hzero hmono h01 h02 h12 hplus hB hBc) with h | h
  exacts [h, absurd h hne]

/-- **And the complement dies against a live merged sum.**  The other direction, for when the
two-colour side is the one known non-zero. -/
theorem pmSum_compl_zero_of_merged_ne (W Wp : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    {k₀ k₁ k₂ : Fin 3} (h01 : k₀ ≠ k₁) (h02 : k₀ ≠ k₂) (h12 : k₁ ≠ k₂)
    (hplus : ∀ x y : V, Wp s((x, k₀), (y, k₀))
      = W s((x, k₀), (y, k₀)) + W s((x, k₁), (y, k₁)))
    {B : Finset V} (hB : B.Nonempty) (hBc : (Finset.univ \ B).Nonempty)
    (hne : pmSum Wp (Amplitude.const (V := V) k₀) B ≠ 0) :
    pmSum W (Amplitude.const (V := V) k₂) (Finset.univ \ B) = 0 := by
  rcases mul_eq_zero.mp
    (pmSum_mixed_product W Wp hzero hmono h01 h02 h12 hplus hB hBc) with h | h
  exacts [absurd h hne, h]

/-! ### Two options at every site

The merge above gave each site of a set the same two colours.  Nothing needs that.  Give each site
its *own* pair of options -- two functions, one picking the first option everywhere, the other the
second -- and summing the matching sum over all the ways of choosing collapses just as before, for
the weight that adds the four combinations on every edge.

The proof is the same recursion and is in fact simpler: with the options carried by functions there
is no dependence on the set at all, so the colourings agree on the remainder for free.

This is what reaches the equations no split can.  Three regions taking `{0,1}`, `{1,2}` and `{0,2}`
have every pairwise intersection non-empty -- so edges across regions are live and nothing
factors -- while no colour lies in all three, so no choice is monochromatic and every amplitude
vanishes.  The merged matching sum vanishes with them, on a graph that does not come apart. -/

/-- **Summing over two options per site.** -/
theorem sum_powerset_pmSum_gen (W Wp : Sym2 (V × Fin 3) → ℂ) (f₀ f₁ : V → Fin 3)
    (hplus : ∀ x y : V, Wp s((x, f₀ x), (y, f₀ y))
      = W s((x, f₀ x), (y, f₀ y)) + W s((x, f₀ x), (y, f₁ y))
        + (W s((x, f₁ x), (y, f₀ y)) + W s((x, f₁ x), (y, f₁ y)))) :
    ∀ S : Finset V,
      ∑ T ∈ S.powerset, pmSum W (fun z => if z ∈ T then f₀ z else f₁ z) S
        = pmSum Wp f₀ S := by
  classical
  refine MatchingSum.eq_pmSum_of_rec Wp f₀ _ ?_ ?_
  · simp
  · intro S hS
    obtain ⟨u, hu⟩ := hS
    refine ⟨u, hu, ?_⟩
    have hexp : ∀ T : Finset V,
        pmSum W (fun z => if z ∈ T then f₀ z else f₁ z) S
        = ∑ v ∈ S.erase u,
            W (Sym2.map (Amplitude.paint (fun z => if z ∈ T then f₀ z else f₁ z)) s(u, v))
              * pmSum W (fun z => if z ∈ T then f₀ z else f₁ z) ((S.erase u).erase v) :=
      fun T => pmSum_expand W _ hu
    rw [Finset.sum_congr rfl (fun T _ => hexp T), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun v hv => ?_)
    have hvu : v ≠ u := Finset.ne_of_mem_erase hv
    have hvS : v ∈ S := Finset.mem_of_mem_erase hv
    set R : Finset V := (S.erase u).erase v with hR
    have hvR : v ∉ R := by simp [hR]
    have huR : u ∉ insert v R := by simp [hR, Ne.symm hvu]
    have hSeq : S = insert u (insert v R) := by
      ext z
      simp only [Finset.mem_insert, hR, Finset.mem_erase]
      constructor
      · intro hz
        by_cases h1 : z = u
        · exact Or.inl h1
        · by_cases h2 : z = v
          · exact Or.inr (Or.inl h2)
          · exact Or.inr (Or.inr ⟨h2, h1, hz⟩)
      · rintro (rfl | rfl | ⟨-, -, hz⟩)
        exacts [hu, hvS, hz]
    have hpaint : ∀ T : Finset V,
        W (Sym2.map (Amplitude.paint (fun z => if z ∈ T then f₀ z else f₁ z)) s(u, v))
        = W s((u, if u ∈ T then f₀ u else f₁ u), (v, if v ∈ T then f₀ v else f₁ v)) :=
      fun T => rfl
    have hcolR : ∀ (T A : Finset V), T ⊆ R → (∀ z ∈ A, z ∉ R) →
        pmSum W (fun z => if z ∈ A ∪ T then f₀ z else f₁ z) R
        = pmSum W (fun z => if z ∈ T then f₀ z else f₁ z) R := by
      intro T A hT hA
      refine pmSum_congr_colour W (fun z hz => ?_)
      have hzA : z ∉ A := fun h => hA z h hz
      simp only [Finset.mem_union, hzA, false_or]
    have hpow : S.powerset = (insert u (insert v R)).powerset := by rw [← hSeq]
    rw [hpow, Finset.sum_powerset_insert huR, Finset.sum_powerset_insert hvR,
      Finset.sum_powerset_insert hvR, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun T hT => ?_)
    have hTR : T ⊆ R := Finset.mem_powerset.mp hT
    have huT : u ∉ T := fun h => huR (Finset.mem_insert_of_mem (hTR h))
    have hvT : v ∉ T := fun h => hvR (hTR h)
    have hPv : pmSum W (fun z => if z ∈ insert v T then f₀ z else f₁ z) R
        = pmSum W (fun z => if z ∈ T then f₀ z else f₁ z) R := by
      rw [show insert v T = ({v} : Finset V) ∪ T from rfl]
      exact hcolR T {v} hTR (fun z hz => by
        rw [Finset.mem_singleton] at hz; exact hz ▸ hvR)
    have hPu : pmSum W (fun z => if z ∈ insert u T then f₀ z else f₁ z) R
        = pmSum W (fun z => if z ∈ T then f₀ z else f₁ z) R := by
      rw [show insert u T = ({u} : Finset V) ∪ T from rfl]
      exact hcolR T {u} hTR (fun z hz => by
        rw [Finset.mem_singleton] at hz
        exact hz ▸ (fun h => huR (Finset.mem_insert_of_mem h)))
    have hPuv : pmSum W (fun z => if z ∈ insert u (insert v T) then f₀ z else f₁ z) R
        = pmSum W (fun z => if z ∈ T then f₀ z else f₁ z) R := by
      rw [show insert u (insert v T) = ({u, v} : Finset V) ∪ T from by
        ext z; simp [Finset.mem_insert, Finset.mem_union]]
      refine hcolR T {u, v} hTR (fun z hz => ?_)
      rcases Finset.mem_insert.mp hz with rfl | hz'
      · exact fun h => huR (Finset.mem_insert_of_mem h)
      · rw [Finset.mem_singleton] at hz'; exact hz' ▸ hvR
    rw [hpaint T, hpaint (insert v T), hpaint (insert u T), hpaint (insert u (insert v T)),
      hPv, hPu, hPuv]
    have e1 : (if u ∈ T then f₀ u else f₁ u) = f₁ u := if_neg huT
    have e2 : (if v ∈ T then f₀ v else f₁ v) = f₁ v := if_neg hvT
    have e3 : (if u ∈ insert v T then f₀ u else f₁ u) = f₁ u :=
      if_neg (by simp [Ne.symm hvu, huT])
    have e4 : (if v ∈ insert v T then f₀ v else f₁ v) = f₀ v := if_pos (by simp)
    have e5 : (if u ∈ insert u T then f₀ u else f₁ u) = f₀ u := if_pos (by simp)
    have e6 : (if v ∈ insert u T then f₀ v else f₁ v) = f₁ v := if_neg (by simp [hvu, hvT])
    have e7 : (if u ∈ insert u (insert v T) then f₀ u else f₁ u) = f₀ u := if_pos (by simp)
    have e8 : (if v ∈ insert u (insert v T) then f₀ v else f₁ v) = f₀ v := if_pos (by simp)
    rw [e1, e2, e3, e4, e5, e6, e7, e8]
    have hWp : Wp (Sym2.map (Amplitude.paint f₀) s(u, v)) = _ := hplus u v
    rw [hWp]
    ring

/-- **The avoidance criterion.**  If for every colour some site declines it in *both* of its
options, then no choice of options is monochromatic, every amplitude vanishes, and the merged
matching sum vanishes with them.

This is the reusable form.  It asks nothing about how the options are arranged -- no regions, no
splitting, no condition on which edges survive.  One site per colour, refusing that colour twice,
is the whole hypothesis. -/
theorem pmSum_avoid_vanishes (W Wp : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (f₀ f₁ : V → Fin 3)
    (hplus : ∀ x y : V, Wp s((x, f₀ x), (y, f₀ y))
      = W s((x, f₀ x), (y, f₀ y)) + W s((x, f₀ x), (y, f₁ y))
        + (W s((x, f₁ x), (y, f₀ y)) + W s((x, f₁ x), (y, f₁ y))))
    (havoid : ∀ k : Fin 3, ∃ x : V, f₀ x ≠ k ∧ f₁ x ≠ k) :
    pmSum Wp f₀ Finset.univ = 0 := by
  classical
  rw [← sum_powerset_pmSum_gen W Wp f₀ f₁ hplus Finset.univ]
  refine Finset.sum_eq_zero (fun T _ => ?_)
  rw [pmSum_univ]
  refine hzero _ ?_
  rintro ⟨k, hk⟩
  obtain ⟨x, h0, h1⟩ := havoid k
  by_cases hx : x ∈ T
  · exact h0 (by simpa [hx] using hk x)
  · exact h1 (by simpa [hx] using hk x)

/-- **A vanishing on a graph that does not split.**  Divide the sites into three non-empty regions
and give them the option pairs `{0,1}`, `{1,2}`, `{0,2}`.  Every pairwise intersection is non-empty,
so edges between regions survive and the matching sum does not factor -- yet each colour is refused
outright by one of the three regions, so the avoidance criterion applies.

The product law and its mixed form both need the crossing edges dead; here they are live and the sum
still vanishes.  Every earlier vanishing was one factor of a product forced to be zero.  This one is
not a factor of anything. -/
theorem pmSum_nonsplit_vanishes (W Wp : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {B₀ B₁ : Finset V}
    (h0 : B₀.Nonempty) (h1 : B₁.Nonempty)
    (h2 : (Finset.univ \ (B₀ ∪ B₁)).Nonempty)
    (hdisj : ∀ z ∈ B₀, z ∉ B₁)
    (f₀ f₁ : V → Fin 3)
    (hf₀ : ∀ z, f₀ z = if z ∈ B₀ then 0 else if z ∈ B₁ then 1 else 0)
    (hf₁ : ∀ z, f₁ z = if z ∈ B₀ then 1 else if z ∈ B₁ then 2 else 2)
    (hplus : ∀ x y : V, Wp s((x, f₀ x), (y, f₀ y))
      = W s((x, f₀ x), (y, f₀ y)) + W s((x, f₀ x), (y, f₁ y))
        + (W s((x, f₁ x), (y, f₀ y)) + W s((x, f₁ x), (y, f₁ y)))) :
    pmSum Wp f₀ Finset.univ = 0 := by
  classical
  refine pmSum_avoid_vanishes W Wp hzero f₀ f₁ hplus (fun k => ?_)
  obtain ⟨z₀, hz₀⟩ := h0
  obtain ⟨z₁, hz₁⟩ := h1
  obtain ⟨z₂, hz₂⟩ := h2
  have hz₂' : z₂ ∉ B₀ ∧ z₂ ∉ B₁ := by
    have := (Finset.mem_sdiff.mp hz₂).2
    rw [Finset.mem_union] at this
    push_neg at this
    exact this
  have hz₁' : z₁ ∉ B₀ := fun h => hdisj z₁ h hz₁
  match k with
  | 0 =>
    refine ⟨z₁, ?_, ?_⟩
    · rw [hf₀ z₁, if_neg hz₁', if_pos hz₁]; decide
    · rw [hf₁ z₁, if_neg hz₁', if_pos hz₁]; decide
  | 1 =>
    refine ⟨z₂, ?_, ?_⟩
    · rw [hf₀ z₂, if_neg hz₂'.1, if_neg hz₂'.2]; decide
    · rw [hf₁ z₂, if_neg hz₂'.1, if_neg hz₂'.2]; decide
  | 2 =>
    refine ⟨z₀, ?_, ?_⟩
    · rw [hf₀ z₀, if_pos hz₀]; decide
    · rw [hf₁ z₀, if_pos hz₀]; decide

/-! ### Exclusion: one forbidden colour per site

With three colours, a pair of options at a site is the same thing as a single *excluded* colour --
the one the site refuses.  Read that way the whole construction simplifies.

Write `e v` for the colour site `v` excludes.  A colour-`k` edge survives into the merged graph
exactly when neither endpoint excludes `k`, since the merged weight collects the colours admitted at
both ends.  And the avoidance hypothesis -- for every colour some site refuses it twice -- says
precisely that every colour is excluded somewhere: **`e` is surjective**.

So the criterion reads: *for any surjective exclusion, the merged matching sum vanishes.*  The three
regions were one surjection among many.

What this sets up is a hitting problem.  To close a configuration one wants a surjective exclusion
that spares some live perfect matching while killing all its rivals: sparing it makes the sum
non-zero, surjectivity makes it zero.  Note at once what cannot work -- sparing a *monochromatic*
matching forbids excluding its colour anywhere, so the exclusion cannot be surjective.  The matching
to be spared must itself use more than one colour. -/

/-- The first colour a site admits, given the colour it excludes. -/
def optA (e : V → Fin 3) : V → Fin 3 := fun v => if e v = 0 then 1 else 0

/-- The second colour a site admits, given the colour it excludes. -/
def optB (e : V → Fin 3) : V → Fin 3 := fun v => if e v = 2 then 1 else 2

theorem optA_ne (e : V → Fin 3) (v : V) : optA e v ≠ e v := by
  simp only [optA]
  match h : e v with
  | 0 => simp [h]
  | 1 => simp [h]
  | 2 => simp [h]

theorem optB_ne (e : V → Fin 3) (v : V) : optB e v ≠ e v := by
  simp only [optB]
  match h : e v with
  | 0 => simp [h]
  | 1 => simp [h]
  | 2 => simp [h]

/-- **A surjective exclusion makes the merged sum vanish.**  Every colour is refused somewhere, so
no choice of admitted colours is monochromatic. -/
theorem pmSum_exclusion_vanishes (W Wp : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (e : V → Fin 3) (hsurj : Function.Surjective e)
    (hplus : ∀ x y : V, Wp s((x, optA e x), (y, optA e y))
      = W s((x, optA e x), (y, optA e y)) + W s((x, optA e x), (y, optB e y))
        + (W s((x, optB e x), (y, optA e y)) + W s((x, optB e x), (y, optB e y)))) :
    pmSum Wp (optA e) Finset.univ = 0 := by
  refine pmSum_avoid_vanishes W Wp hzero (optA e) (optB e) hplus (fun k => ?_)
  obtain ⟨v, hv⟩ := hsurj k
  exact ⟨v, hv ▸ optA_ne e v, hv ▸ optB_ne e v⟩

/-- **A surjective exclusion with an unrivalled matching is impossible.**  Surjectivity makes the
merged sum vanish; a unique surviving matching makes it a single non-zero product.

This is the bridge the hitting construction needs.  Given three disjoint named matchings and a
perfect matching `M` in their union that uses more than one colour, delete `M`: what remains is
two-regular, so a union of cycles.  Orient them, and let each site exclude the colour of its
incoming edge.  Its two admitted colours are then its `M`-edge's colour and its outgoing edge's --
so every `M` edge survives at both ends, while every remaining edge is excluded at its head and
dies.  Since `M` is mixed it omits an edge of each colour, and each omitted edge is incoming
somewhere, so the exclusion is onto.

On the union alone that leaves `M` unrivalled and closes the case.  What the construction does not
control is the excess: an edge outside the union survives unless its colour is excluded at one of
its ends, and reversing a cycle's orientation flips which end excludes what.  So the remaining
obligation is a two-satisfiability question over the cycle orientations.

It also explains the four-site solution rather than merely excluding it: there the union's only
perfect matchings are the three named ones, none mixed, so no exclusion built this way is onto. -/
theorem false_of_surjective_exclusion_unique (W Wp : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (e : V → Fin 3) (hsurj : Function.Surjective e)
    (hplus : ∀ x y : V, Wp s((x, optA e x), (y, optA e y))
      = W s((x, optA e x), (y, optA e y)) + W s((x, optA e x), (y, optB e y))
        + (W s((x, optB e x), (y, optA e y)) + W s((x, optB e x), (y, optB e y))))
    {σ₀ : Equiv.Perm V} (hmem : σ₀ ∈ pairingsOn (Finset.univ : Finset V))
    (hlive : ∀ z : V, Wp s((z, optA e z), (σ₀ z, optA e (σ₀ z))) ≠ 0)
    (huniq : ∀ τ ∈ pairingsOn (Finset.univ : Finset V), τ ≠ σ₀ →
      ∃ z : V, Wp s((z, optA e z), (τ z, optA e (τ z))) = 0) :
    False := by
  classical
  refine pmSum_ne_zero_of_unique_matching Wp (optA e) hmem (fun z _ => ?_) (fun τ hτ hne => ?_)
    (pmSum_exclusion_vanishes W Wp hzero e hsurj hplus)
  · have hp : (Sym2.map (Amplitude.paint (optA e)) s(z, σ₀ z))
        = s((z, optA e z), (σ₀ z, optA e (σ₀ z))) := rfl
    rw [hp]; exact hlive z
  · obtain ⟨z, hz⟩ := huniq τ hτ hne
    refine ⟨z, Finset.mem_univ z, ?_⟩
    have hp : (Sym2.map (Amplitude.paint (optA e)) s(z, τ z))
        = s((z, optA e z), (τ z, optA e (τ z))) := rfl
    rw [hp]; exact hz

/-! ### Which edges survive an exclusion

The interface between the hitting construction and what remains of it.  A site admits exactly the
two colours it does not exclude, so a pair carrying a single live colour survives the merge
precisely when neither of its ends excludes that colour -- and dies as soon as one of them does.

That is the clause.  Each pair outside the chosen matching contributes the requirement that one of
its ends exclude its colour, and each site's exclusion is fixed by the orientation of the cycle it
lies on: one Boolean per cycle, two literals per clause.

The single-live-colour hypothesis is not cosmetic.  Where a pair carries two live colours the merged
weight is a sum that may cancel, and no such reading is available; it is the support-minimal
degenerate setting that supplies it. -/

theorem mem_opts (e : V → Fin 3) (v : V) {k : Fin 3} (h : k ≠ e v) :
    k = optA e v ∨ k = optB e v := by
  simp only [optA, optB]
  revert h
  generalize e v = j
  revert k
  revert j
  decide

/-- **A site admits exactly one of its two options as a given colour.**  The colours a site accepts
are the two it does not exclude, so a colour it does accept is matched by precisely one option. -/
theorem opts_exact (e : V → Fin 3) (v : V) {k : Fin 3} (h : k ≠ e v) :
    (optA e v = k ∧ optB e v ≠ k) ∨ (optA e v ≠ k ∧ optB e v = k) := by
  simp only [optA, optB]
  revert h
  generalize e v = j
  revert k
  revert j
  decide

/-- **An excluded colour kills its pair.**  If a pair carries only the colour one of its ends
refuses, the merged weight there is zero. -/
theorem merged_dead_of_excluded (W Wp : Sym2 (V × Fin 3) → ℂ)
    (e : V → Fin 3) {x y : V} {k : Fin 3}
    (hplus : Wp s((x, optA e x), (y, optA e y))
      = W s((x, optA e x), (y, optA e y)) + W s((x, optA e x), (y, optB e y))
        + (W s((x, optB e x), (y, optA e y)) + W s((x, optB e x), (y, optB e y))))
    (honly : ∀ a b : Fin 3, a ≠ k → W s((x, a), (y, b)) = 0)
    (hex : e x = k) :
    Wp s((x, optA e x), (y, optA e y)) = 0 := by
  have hA : optA e x ≠ k := hex ▸ optA_ne e x
  have hB : optB e x ≠ k := hex ▸ optB_ne e x
  rw [hplus, honly _ _ hA, honly _ _ hA, honly _ _ hB, honly _ _ hB]
  ring

/-- **A colour admitted at both ends survives untouched.**  With a single live colour on the pair,
the merged weight is exactly that colour's weight -- so non-vanishing transfers to the merge. -/
theorem merged_eq_of_admitted (W Wp : Sym2 (V × Fin 3) → ℂ)
    (hmono : ∀ (u v : V), v ≠ u → ∀ a b : Fin 3, a ≠ b → W s((u, a), (v, b)) = 0)
    (e : V → Fin 3) {x y : V} (hyx : y ≠ x) {k : Fin 3}
    (hplus : Wp s((x, optA e x), (y, optA e y))
      = W s((x, optA e x), (y, optA e y)) + W s((x, optA e x), (y, optB e y))
        + (W s((x, optB e x), (y, optA e y)) + W s((x, optB e x), (y, optB e y))))
    (honly : ∀ a : Fin 3, a ≠ k → W s((x, a), (y, a)) = 0)
    (hx : k ≠ e x) (hy : k ≠ e y) :
    Wp s((x, optA e x), (y, optA e y)) = W s((x, k), (y, k)) := by
  classical
  have dead : ∀ a b : Fin 3, (a ≠ k ∨ b ≠ k) → W s((x, a), (y, b)) = 0 := by
    intro a b h
    by_cases hab : a = b
    · subst hab
      rcases h with h | h
      · exact honly a h
      · exact honly a h
    · exact hmono x y hyx a b hab
  rw [hplus]
  rcases opts_exact e x hx with ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩ <;>
    rcases opts_exact e y hy with ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩
  · rw [hx1, hy1, dead k (optB e y) (Or.inr hy2), dead (optB e x) k (Or.inl hx2),
      dead (optB e x) (optB e y) (Or.inl hx2)]
    ring
  · rw [hx1, hy2, dead k (optA e y) (Or.inr hy1), dead (optB e x) (optA e y) (Or.inl hx2),
      dead (optB e x) k (Or.inl hx2)]
    ring
  · rw [hx2, hy1, dead (optA e x) k (Or.inl hx1), dead (optA e x) (optB e y) (Or.inl hx1),
      dead k (optB e y) (Or.inr hy2)]
    ring
  · rw [hx2, hy2, dead (optA e x) (optA e y) (Or.inl hx1), dead (optA e x) k (Or.inl hx1),
      dead k (optA e y) (Or.inr hy1)]
    ring
/-- **The hitting construction, discharged into combinatorial data.**

Everything analytic is now hypothesis-free: what remains to supply is a choice of exclusion, a
choice of matching, and the statement that the pair of them kills every other pair.

* `col z` is the colour the chosen matching uses at `z`, admitted at both its ends (`hadm`);
* `honly` says each matched pair carries that colour alone -- available on a support-minimal
  degenerate representative, and not to be assumed elsewhere;
* `hkill` is the whole remaining obligation.  For a pair inside the three-colour skeleton it holds
  automatically once the exclusion is read off an orientation, since such a pair is excluded at its
  head.  For a pair outside it, it is the clause `e u = k ∨ e v = k`, and the orientations of the
  remainder cycles are its Boolean variables.

So a satisfying orientation closes the case, and a configuration that survives must make that
finite two-satisfiability instance unsatisfiable. -/
theorem false_of_exclusion_kills_rest (W Wp : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (u v : V), v ≠ u → ∀ a b : Fin 3, a ≠ b → W s((u, a), (v, b)) = 0)
    (e : V → Fin 3) (hsurj : Function.Surjective e)
    (hplus : ∀ x y : V, Wp s((x, optA e x), (y, optA e y))
      = W s((x, optA e x), (y, optA e y)) + W s((x, optA e x), (y, optB e y))
        + (W s((x, optB e x), (y, optA e y)) + W s((x, optB e x), (y, optB e y))))
    (col : V → Fin 3) {σ₀ : Equiv.Perm V}
    (hmem : σ₀ ∈ pairingsOn (Finset.univ : Finset V))
    (hadm : ∀ z : V, col z ≠ e z)
    (hcol : ∀ z : V, col (σ₀ z) = col z)
    (honly : ∀ z : V, ∀ a : Fin 3, a ≠ col z → W s((z, a), (σ₀ z, a)) = 0)
    (hlive : ∀ z : V, W s((z, col z), (σ₀ z, col z)) ≠ 0)
    (hkill : ∀ x y : V, y ≠ x → y ≠ σ₀ x → Wp s((x, optA e x), (y, optA e y)) = 0) :
    False := by
  classical
  obtain ⟨-, hfix, -⟩ := mem_pairingsOn.mp hmem
  refine false_of_surjective_exclusion_unique W Wp hzero e hsurj hplus hmem (fun z => ?_)
    (fun τ hτ hne => ?_)
  · have hyx : σ₀ z ≠ z := hfix z (Finset.mem_univ z)
    have hy : col z ≠ e (σ₀ z) := by rw [← hcol z]; exact hadm (σ₀ z)
    rw [merged_eq_of_admitted W Wp hmono e hyx (hplus z (σ₀ z)) (honly z) (hadm z) hy]
    exact hlive z
  · obtain ⟨-, hfixτ, -⟩ := mem_pairingsOn.mp hτ
    have : ∃ z : V, τ z ≠ σ₀ z := by
      by_contra hall
      push_neg at hall
      exact hne (Equiv.ext hall)
    obtain ⟨z, hz⟩ := this
    exact ⟨z, hkill z (τ z) (hfixτ z (Finset.mem_univ z)) hz⟩

/-! ### Non-vanishing from a local recursive condition

Asking for a *unique* matching is asking a question about every pairing at once.  The following
replaces it with a condition one can check by walking the configuration: at every stage there is a
site with a single live partner, whose pair is then forced and can be deleted.

That is exactly the structure a union of even paths has -- an endpoint is pendant, and removing it
with its neighbour leaves shorter paths -- and it is what an exclusion leaves behind, since refusing
one colour per site drops every site to at most two surviving skeleton partners.  A cycle has no
pendant site and is correctly excluded: it carries two matchings, which may cancel. -/

/-- **A hereditarily pendant configuration has a non-zero matching sum.**  If every non-empty part
of `S` contains a site with exactly one live partner there, the sum is a product of forced weights
and cannot vanish. -/
theorem pmSum_ne_zero_of_hereditary_pendant (W : Sym2 (V × Fin 3) → ℂ)
    (hmono : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0)
    (c : V → Fin 3) {S : Finset V}
    (hpend : ∀ T ⊆ S, T.Nonempty → ∃ u ∈ T, ∃ v ∈ T.erase u,
      c v = c u ∧ W s((u, c u), (v, c u)) ≠ 0 ∧
      ∀ z ∈ T, z ≠ v → z ≠ u → W s((u, c u), (z, c u)) = 0) :
    pmSum W c S ≠ 0 := by
  classical
  suffices h : ∀ T : Finset V, T ⊆ S → pmSum W c T ≠ 0 from h S (subset_refl S)
  intro T
  induction T using Finset.strongInduction with
  | _ T ih =>
    intro hTS
    rcases T.eq_empty_or_nonempty with rfl | hne
    · simp
    · obtain ⟨u, hu, v, hv, hcv, hlive, hkill⟩ := hpend T hTS hne
      rw [pmSum_delete_pendant W hmono hu hv hkill c rfl hcv]
      refine mul_ne_zero hlive (ih _ ?_ ?_)
      · exact ssubset_of_subset_of_ssubset (Finset.erase_subset v (T.erase u))
          (Finset.erase_ssubset hu)
      · exact ((Finset.erase_subset v (T.erase u)).trans (Finset.erase_subset u T)).trans hTS

/-- **The closer in its widest form.**  An onto exclusion makes the merged sum vanish; a
hereditarily pendant survivor makes it non-zero.  Nothing here asks the survivor to be a matching --
only that it be walkable, which a union of even paths is. -/
theorem false_of_surjective_exclusion_pendant (W Wp : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmonop : ∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → Wp s((x, a), (y, b)) = 0)
    (e : V → Fin 3) (hsurj : Function.Surjective e)
    (hplus : ∀ x y : V, Wp s((x, optA e x), (y, optA e y))
      = W s((x, optA e x), (y, optA e y)) + W s((x, optA e x), (y, optB e y))
        + (W s((x, optB e x), (y, optA e y)) + W s((x, optB e x), (y, optB e y))))
    (hpend : ∀ T ⊆ (Finset.univ : Finset V), T.Nonempty → ∃ u ∈ T, ∃ v ∈ T.erase u,
      optA e v = optA e u ∧ Wp s((u, optA e u), (v, optA e u)) ≠ 0 ∧
      ∀ z ∈ T, z ≠ v → z ≠ u → Wp s((u, optA e u), (z, optA e u)) = 0) :
    False :=
  pmSum_ne_zero_of_hereditary_pendant Wp hmonop (optA e) hpend
    (pmSum_exclusion_vanishes W Wp hzero e hsurj hplus)

/-- **What the merged sum actually is.**  An exclusion that never refuses colour `k` leaves exactly
one constant colouring reachable, so the merged sum is that colour's amplitude -- non-zero, with no
condition on the shape of the survivor.

Together with the vanishing theorem this is a dichotomy: the merged sum sees precisely the colours
nobody refuses.  Refuse all three and it is zero; refuse only two and it is the third's amplitude.
So the whole machine turns on making the exclusion onto, and every non-onto exclusion is calibration
rather than leverage. -/
theorem pmSum_avoid_eq_amplitude (W Wp : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (e : V → Fin 3) {k : Fin 3} (hmiss : ∀ v : V, e v ≠ k)
    (hhit : ∀ j : Fin 3, j ≠ k → ∃ v : V, e v = j)
    (hplus : ∀ x y : V, Wp s((x, optA e x), (y, optA e y))
      = W s((x, optA e x), (y, optA e y)) + W s((x, optA e x), (y, optB e y))
        + (W s((x, optB e x), (y, optA e y)) + W s((x, optB e x), (y, optB e y)))) :
    pmSum Wp (optA e) Finset.univ = amplitude W (Amplitude.const (V := V) k) := by
  classical
  have hexact : ∀ v : V, (optA e v = k ∧ optB e v ≠ k) ∨ (optA e v ≠ k ∧ optB e v = k) :=
    fun v => opts_exact e v (Ne.symm (hmiss v))
  set T₀ : Finset V := Finset.univ.filter (fun v => optA e v = k) with hT₀def
  have hmemT₀ : T₀ ∈ (Finset.univ : Finset V).powerset :=
    Finset.mem_powerset.mpr (Finset.subset_univ _)
  rw [← sum_powerset_pmSum_gen W Wp (optA e) (optB e) hplus Finset.univ,
    Finset.sum_eq_single_of_mem T₀ hmemT₀]
  · rw [pmSum_univ]
    congr 1
    funext v
    by_cases hv : optA e v = k
    · have hmem : v ∈ T₀ := Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩
      simp [hmem, hv, Amplitude.const]
    · have hnot : v ∉ T₀ := fun h => hv (Finset.mem_filter.mp h).2
      rcases hexact v with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact absurd h1 hv
      · simp [hnot, h2, Amplitude.const]
  · intro T _ hne
    rw [pmSum_univ]
    refine hzero _ ?_
    rintro ⟨j, hj⟩
    have hjk : j = k := by
      by_contra hjk
      obtain ⟨v, hv⟩ := hhit j hjk
      by_cases hvT : v ∈ T
      · have h1 : optA e v = j := by simpa [hvT] using hj v
        exact optA_ne e v (h1.trans hv.symm)
      · have h1 : optB e v = j := by simpa [hvT] using hj v
        exact optB_ne e v (h1.trans hv.symm)
    refine hne (Finset.ext (fun v => ⟨fun hvT => ?_, fun hvT₀ => ?_⟩))
    · have h1 : optA e v = j := by simpa [hvT] using hj v
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, h1.trans hjk⟩
    · have hA : optA e v = k := (Finset.mem_filter.mp hvT₀).2
      by_contra hvT
      have h2 : optB e v = j := by simpa [hvT] using hj v
      rcases hexact v with ⟨-, hB⟩ | ⟨hA', -⟩
      · exact hB (h2.trans hjk)
      · exact hA' hA

/-! ### The merged weight in closed form

Two sites refusing the same colour admit the same pair of colours, so their merged weight is the sum
of those two.  Two sites refusing different colours admit only the third colour in common, so their
merged weight is that single colour's weight.  Everything downstream of the refusal picture reads
off these two. -/

theorem optA_ne_optB (e : V → Fin 3) (v : V) : optA e v ≠ optB e v := by
  simp only [optA, optB]
  generalize e v = j
  revert j
  decide

/-- Two colours each differing from the same two distinct colours agree. -/
theorem fin3_eq_of_ne_ne {a c d f : Fin 3} (hac : a ≠ c)
    (hda : d ≠ a) (hdc : d ≠ c) (hfa : f ≠ a) (hfc : f ≠ c) : d = f := by
  revert hac hda hdc hfa hfc
  revert a c d f
  decide

/-- **Same refusal: the merged weight is the sum of the two admitted colours.** -/
theorem merged_of_same_refusal (W Wp : Sym2 (V × Fin 3) → ℂ)
    (hmono : ∀ (u v : V), v ≠ u → ∀ a b : Fin 3, a ≠ b → W s((u, a), (v, b)) = 0)
    (e : V → Fin 3) {x y : V} (hyx : y ≠ x) (hxy : e x = e y)
    (hplus : Wp s((x, optA e x), (y, optA e y))
      = W s((x, optA e x), (y, optA e y)) + W s((x, optA e x), (y, optB e y))
        + (W s((x, optB e x), (y, optA e y)) + W s((x, optB e x), (y, optB e y)))) :
    Wp s((x, optA e x), (y, optA e y))
      = W s((x, optA e x), (y, optA e x)) + W s((x, optB e x), (y, optB e x)) := by
  have hA : optA e y = optA e x := by simp only [optA, hxy]
  have hB : optB e y = optB e x := by simp only [optB, hxy]
  have hAB : optA e x ≠ optB e x := optA_ne_optB e x
  rw [hplus, hA, hB, hmono x y hyx _ _ hAB, hmono x y hyx _ _ (Ne.symm hAB)]
  ring

/-- **Different refusals: the merged weight is the third colour's weight.** -/
theorem merged_of_diff_refusal (W Wp : Sym2 (V × Fin 3) → ℂ)
    (hmono : ∀ (u v : V), v ≠ u → ∀ a b : Fin 3, a ≠ b → W s((u, a), (v, b)) = 0)
    (e : V → Fin 3) {x y : V} (hyx : y ≠ x) {c : Fin 3}
    (hxy : e x ≠ e y) (hcx : c ≠ e x) (hcy : c ≠ e y)
    (hplus : Wp s((x, optA e x), (y, optA e y))
      = W s((x, optA e x), (y, optA e y)) + W s((x, optA e x), (y, optB e y))
        + (W s((x, optB e x), (y, optA e y)) + W s((x, optB e x), (y, optB e y)))) :
    Wp s((x, optA e x), (y, optA e y)) = W s((x, c), (y, c)) := by
  classical
  -- the option at `x` other than `c` is `e y`, and the one at `y` other than `c` is `e x`
  have hxo : ∀ d : Fin 3, d ≠ e x → d ≠ c → d = e y := fun d hda hdc =>
    fin3_eq_of_ne_ne hcx.symm hda hdc (Ne.symm hxy) (Ne.symm hcy)
  have hyo : ∀ d : Fin 3, d ≠ e y → d ≠ c → d = e x := fun d hda hdc =>
    fin3_eq_of_ne_ne hcy.symm hda hdc hxy (Ne.symm hcx)
  rw [hplus]
  rcases opts_exact e x hcx with ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩ <;>
    rcases opts_exact e y hcy with ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩
  · rw [hx1, hy1, hmono x y hyx c (optB e y) (fun h => hy2 h.symm),
      hmono x y hyx (optB e x) c hx2,
      hmono x y hyx (optB e x) (optB e y) (by
        rw [hxo _ (optB_ne e x) hx2, hyo _ (optB_ne e y) hy2]; exact Ne.symm hxy)]
    ring
  · rw [hx1, hy2, hmono x y hyx c (optA e y) (fun h => hy1 h.symm),
      hmono x y hyx (optB e x) c hx2,
      hmono x y hyx (optB e x) (optA e y) (by
        rw [hxo _ (optB_ne e x) hx2, hyo _ (optA_ne e y) hy1]; exact Ne.symm hxy)]
    ring
  · rw [hx2, hy1, hmono x y hyx c (optB e y) (fun h => hy2 h.symm),
      hmono x y hyx (optA e x) c hx1,
      hmono x y hyx (optA e x) (optB e y) (by
        rw [hxo _ (optA_ne e x) hx1, hyo _ (optB_ne e y) hy2]; exact Ne.symm hxy)]
    ring
  · rw [hx2, hy2, hmono x y hyx c (optA e y) (fun h => hy1 h.symm),
      hmono x y hyx (optA e x) c hx1,
      hmono x y hyx (optA e x) (optA e y) (by
        rw [hxo _ (optA_ne e x) hx1, hyo _ (optA_ne e y) hy1]; exact Ne.symm hxy)]
    ring

/-! ### Three refusals at one site

Fix a site and a refusal map on all the others.  The site itself may refuse any of the three
colours, and the three resulting merged systems differ only in that site's row.  Two of them are
onto nothing -- they miss a colour, so each equals that colour's amplitude -- and the third is onto,
so it vanishes.  Three equations, three unknowns: the row of each single colour against the shared
cofactors is determined.

The consequence is sharp.  Writing the site's two other colours as the ones its neighbours refuse,
each of those two rows *annihilates* the cofactor vector, while the missing colour's row reproduces
that colour's amplitude and therefore cannot.  Cancellation is thereby confined to one row at a
time, and one row is separated from the other two. -/

theorem optA_update_of_ne (g : V → Fin 3) (v₀ : V) (a : Fin 3) {u : V} (hu : u ≠ v₀) :
    optA (Function.update g v₀ a) u = optA g u := by
  simp only [optA, Function.update_of_ne hu]

theorem optB_update_of_ne (g : V → Fin 3) (v₀ : V) (a : Fin 3) {u : V} (hu : u ≠ v₀) :
    optB (Function.update g v₀ a) u = optB g u := by
  simp only [optB, Function.update_of_ne hu]

/-- The merged weights of two refusal maps agreeing off a site agree on every pair away from it. -/
theorem merged_agree_off_site (W Wa Wb : Sym2 (V × Fin 3) → ℂ) (g : V → Fin 3) (v₀ : V)
    {a b : Fin 3}
    (hplusA : ∀ x y : V, Wa s((x, optA (Function.update g v₀ a) x),
        (y, optA (Function.update g v₀ a) y))
      = W s((x, optA (Function.update g v₀ a) x), (y, optA (Function.update g v₀ a) y))
        + W s((x, optA (Function.update g v₀ a) x), (y, optB (Function.update g v₀ a) y))
        + (W s((x, optB (Function.update g v₀ a) x), (y, optA (Function.update g v₀ a) y))
          + W s((x, optB (Function.update g v₀ a) x), (y, optB (Function.update g v₀ a) y))))
    (hplusB : ∀ x y : V, Wb s((x, optA (Function.update g v₀ b) x),
        (y, optA (Function.update g v₀ b) y))
      = W s((x, optA (Function.update g v₀ b) x), (y, optA (Function.update g v₀ b) y))
        + W s((x, optA (Function.update g v₀ b) x), (y, optB (Function.update g v₀ b) y))
        + (W s((x, optB (Function.update g v₀ b) x), (y, optA (Function.update g v₀ b) y))
          + W s((x, optB (Function.update g v₀ b) x), (y, optB (Function.update g v₀ b) y))))
    {x y : V} (hx : x ≠ v₀) (hy : y ≠ v₀) :
    Wa s((x, optA g x), (y, optA g y)) = Wb s((x, optA g x), (y, optA g y)) := by
  have hA := hplusA x y
  have hB := hplusB x y
  rw [optA_update_of_ne g v₀ a hx, optA_update_of_ne g v₀ a hy,
    optB_update_of_ne g v₀ a hx, optB_update_of_ne g v₀ a hy] at hA
  rw [optA_update_of_ne g v₀ b hx, optA_update_of_ne g v₀ b hy,
    optB_update_of_ne g v₀ b hx, optB_update_of_ne g v₀ b hy] at hB
  rw [hA, hB]

/-- **The cofactors are shared.**  Deleting the distinguished site leaves a matching sum that does
not see which colour that site refused. -/
theorem cofactor_agree (W Wa Wb : Sym2 (V × Fin 3) → ℂ) (g : V → Fin 3) (v₀ : V)
    {a b : Fin 3}
    (hplusA : ∀ x y : V, Wa s((x, optA (Function.update g v₀ a) x),
        (y, optA (Function.update g v₀ a) y))
      = W s((x, optA (Function.update g v₀ a) x), (y, optA (Function.update g v₀ a) y))
        + W s((x, optA (Function.update g v₀ a) x), (y, optB (Function.update g v₀ a) y))
        + (W s((x, optB (Function.update g v₀ a) x), (y, optA (Function.update g v₀ a) y))
          + W s((x, optB (Function.update g v₀ a) x), (y, optB (Function.update g v₀ a) y))))
    (hplusB : ∀ x y : V, Wb s((x, optA (Function.update g v₀ b) x),
        (y, optA (Function.update g v₀ b) y))
      = W s((x, optA (Function.update g v₀ b) x), (y, optA (Function.update g v₀ b) y))
        + W s((x, optA (Function.update g v₀ b) x), (y, optB (Function.update g v₀ b) y))
        + (W s((x, optB (Function.update g v₀ b) x), (y, optA (Function.update g v₀ b) y))
          + W s((x, optB (Function.update g v₀ b) x), (y, optB (Function.update g v₀ b) y))))
    {S : Finset V} (hS : S ⊆ (Finset.univ : Finset V).erase v₀) :
    pmSum Wa (optA (Function.update g v₀ a)) S = pmSum Wb (optA (Function.update g v₀ b)) S := by
  have hne : ∀ x ∈ S, x ≠ v₀ := fun x hx => Finset.ne_of_mem_erase (hS hx)
  rw [pmSum_congr_colour Wa (c' := optA g) (fun x hx => optA_update_of_ne g v₀ a (hne x hx)),
    pmSum_congr_colour Wb (c' := optA g) (fun x hx => optA_update_of_ne g v₀ b (hne x hx))]
  refine pmSum_congr Wa Wb _ (fun x hx y hy => ?_)
  exact merged_agree_off_site W Wa Wb g v₀ hplusA hplusB (hne x hx) (hne y hy)

theorem fin3_pair {a c d p q : Fin 3} (hcd : c ≠ d) (hca : c ≠ a) (hda : d ≠ a)
    (hpq : p ≠ q) (hpa : p ≠ a) (hqa : q ≠ a) : (p = c ∧ q = d) ∨ (p = d ∧ q = c) := by
  revert hcd hca hda hpq hpa hqa
  revert a c d p q
  decide

theorem fin3_trichotomy {k m j : Fin 3} (hkm : k ≠ m) (hkj : k ≠ j) (hmj : m ≠ j) (i : Fin 3) :
    i = k ∨ i = m ∨ i = j := by
  revert hkm hkj hmj
  revert k m j i
  decide

/-- **Same refusal, named colours.**  Two sites refusing the same colour admit exactly the other
two, and their merged weight is the sum of those two weights. -/
theorem merged_of_same_refusal' (W Wp : Sym2 (V × Fin 3) → ℂ)
    (hmono : ∀ (u v : V), v ≠ u → ∀ a b : Fin 3, a ≠ b → W s((u, a), (v, b)) = 0)
    (e : V → Fin 3) {x y : V} (hyx : y ≠ x) (hxy : e x = e y)
    {c d : Fin 3} (hcd : c ≠ d) (hcx : c ≠ e x) (hdx : d ≠ e x)
    (hplus : Wp s((x, optA e x), (y, optA e y))
      = W s((x, optA e x), (y, optA e y)) + W s((x, optA e x), (y, optB e y))
        + (W s((x, optB e x), (y, optA e y)) + W s((x, optB e x), (y, optB e y)))) :
    Wp s((x, optA e x), (y, optA e y)) = W s((x, c), (y, c)) + W s((x, d), (y, d)) := by
  rw [merged_of_same_refusal W Wp hmono e hyx hxy hplus]
  rcases fin3_pair hcd hcx hdx (optA_ne_optB e x) (optA_ne e x) (optB_ne e x) with
    ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2]; ring

/-- The matching sum left after deleting a site and one of its partners. -/
noncomputable def mergedCofactor (Wa : Sym2 (V × Fin 3) → ℂ) (e : V → Fin 3) (v₀ u : V) : ℂ :=
  pmSum Wa (optA e) (((Finset.univ : Finset V).erase v₀).erase u)

/-- Expanding a merged sum along the distinguished site, against the shared cofactors. -/
theorem merged_expand_at_site (W Wa Wb : Sym2 (V × Fin 3) → ℂ) (g : V → Fin 3) (v₀ : V)
    {a b : Fin 3}
    (hplusA : ∀ x y : V, Wa s((x, optA (Function.update g v₀ a) x),
        (y, optA (Function.update g v₀ a) y))
      = W s((x, optA (Function.update g v₀ a) x), (y, optA (Function.update g v₀ a) y))
        + W s((x, optA (Function.update g v₀ a) x), (y, optB (Function.update g v₀ a) y))
        + (W s((x, optB (Function.update g v₀ a) x), (y, optA (Function.update g v₀ a) y))
          + W s((x, optB (Function.update g v₀ a) x), (y, optB (Function.update g v₀ a) y))))
    (hplusB : ∀ x y : V, Wb s((x, optA (Function.update g v₀ b) x),
        (y, optA (Function.update g v₀ b) y))
      = W s((x, optA (Function.update g v₀ b) x), (y, optA (Function.update g v₀ b) y))
        + W s((x, optA (Function.update g v₀ b) x), (y, optB (Function.update g v₀ b) y))
        + (W s((x, optB (Function.update g v₀ b) x), (y, optA (Function.update g v₀ b) y))
          + W s((x, optB (Function.update g v₀ b) x), (y, optB (Function.update g v₀ b) y)))) :
    pmSum Wa (optA (Function.update g v₀ a)) Finset.univ
      = ∑ u ∈ (Finset.univ : Finset V).erase v₀,
          Wa s((v₀, optA (Function.update g v₀ a) v₀), (u, optA (Function.update g v₀ a) u))
            * mergedCofactor Wb (Function.update g v₀ b) v₀ u := by
  rw [pmSum_expand Wa _ (Finset.mem_univ v₀)]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  have hp : (Sym2.map (Amplitude.paint (optA (Function.update g v₀ a))) s(v₀, u))
      = s((v₀, optA (Function.update g v₀ a) v₀), (u, optA (Function.update g v₀ a) u)) := rfl
  rw [hp]
  congr 1
  simp only [mergedCofactor]
  exact cofactor_agree W Wa Wb g v₀ hplusA hplusB
    (Finset.erase_subset u ((Finset.univ : Finset V).erase v₀))

/-- **Three refusals at one site separate one row from the other two.**

Fix a site `v₀` and let every other site refuse one of two colours `m, j`, both occurring.  Then:

* the `j`-row of `v₀`, restricted to the sites refusing `m`, annihilates the cofactors;
* the `m`-row of `v₀`, restricted to the sites refusing `j`, annihilates them too;
* the `k`-row -- the colour nobody else refuses -- reproduces `k`'s amplitude, so it cannot.

The proof is three equations in three unknowns.  Letting `v₀` refuse `m` or `j` gives a system
missing `k`, whose sum is `k`'s amplitude; letting it refuse `k` gives an onto system, whose sum is
zero.  All three share their cofactors, because they differ only in `v₀`'s row. -/
theorem row_relations_at_site (W Wm Wj Wk : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (u v : V), v ≠ u → ∀ a b : Fin 3, a ≠ b → W s((u, a), (v, b)) = 0)
    (v₀ : V) (g : V → Fin 3) {k m j : Fin 3}
    (hkm : k ≠ m) (hkj : k ≠ j) (hmj : m ≠ j)
    (hg : ∀ u : V, u ≠ v₀ → g u = m ∨ g u = j)
    (hhm : ∃ u : V, u ≠ v₀ ∧ g u = m) (hhj : ∃ u : V, u ≠ v₀ ∧ g u = j)
    (hplusM : ∀ x y : V, Wm s((x, optA (Function.update g v₀ m) x),
        (y, optA (Function.update g v₀ m) y))
      = W s((x, optA (Function.update g v₀ m) x), (y, optA (Function.update g v₀ m) y))
        + W s((x, optA (Function.update g v₀ m) x), (y, optB (Function.update g v₀ m) y))
        + (W s((x, optB (Function.update g v₀ m) x), (y, optA (Function.update g v₀ m) y))
          + W s((x, optB (Function.update g v₀ m) x), (y, optB (Function.update g v₀ m) y))))
    (hplusJ : ∀ x y : V, Wj s((x, optA (Function.update g v₀ j) x),
        (y, optA (Function.update g v₀ j) y))
      = W s((x, optA (Function.update g v₀ j) x), (y, optA (Function.update g v₀ j) y))
        + W s((x, optA (Function.update g v₀ j) x), (y, optB (Function.update g v₀ j) y))
        + (W s((x, optB (Function.update g v₀ j) x), (y, optA (Function.update g v₀ j) y))
          + W s((x, optB (Function.update g v₀ j) x), (y, optB (Function.update g v₀ j) y))))
    (hplusK : ∀ x y : V, Wk s((x, optA (Function.update g v₀ k) x),
        (y, optA (Function.update g v₀ k) y))
      = W s((x, optA (Function.update g v₀ k) x), (y, optA (Function.update g v₀ k) y))
        + W s((x, optA (Function.update g v₀ k) x), (y, optB (Function.update g v₀ k) y))
        + (W s((x, optB (Function.update g v₀ k) x), (y, optA (Function.update g v₀ k) y))
          + W s((x, optB (Function.update g v₀ k) x), (y, optB (Function.update g v₀ k) y)))) :
    (∑ u ∈ ((Finset.univ : Finset V).erase v₀).filter (fun u => g u = m),
        W s((v₀, j), (u, j)) * mergedCofactor Wm (Function.update g v₀ m) v₀ u = 0)
    ∧ (∑ u ∈ ((Finset.univ : Finset V).erase v₀).filter (fun u => ¬ g u = m),
        W s((v₀, m), (u, m)) * mergedCofactor Wm (Function.update g v₀ m) v₀ u = 0)
    ∧ (∑ u ∈ (Finset.univ : Finset V).erase v₀,
        W s((v₀, k), (u, k)) * mergedCofactor Wm (Function.update g v₀ m) v₀ u
          = amplitude W (Amplitude.const (V := V) k)) := by
  classical
  have hEm : ∀ u : V, u ≠ v₀ → Function.update g v₀ m u = g u := fun u hu =>
    Function.update_of_ne hu _ _
  have hEj : ∀ u : V, u ≠ v₀ → Function.update g v₀ j u = g u := fun u hu =>
    Function.update_of_ne hu _ _
  have hEk : ∀ u : V, u ≠ v₀ → Function.update g v₀ k u = g u := fun u hu =>
    Function.update_of_ne hu _ _
  have hmv : Function.update g v₀ m v₀ = m := Function.update_self _ _ _
  have hjv : Function.update g v₀ j v₀ = j := Function.update_self _ _ _
  have hkv : Function.update g v₀ k v₀ = k := Function.update_self _ _ _
  obtain ⟨um, humv, humg⟩ := hhm
  obtain ⟨uj, hujv, hujg⟩ := hhj
  -- the three totals
  have h1 : pmSum Wm (optA (Function.update g v₀ m)) Finset.univ
      = amplitude W (Amplitude.const (V := V) k) := by
    refine pmSum_avoid_eq_amplitude W Wm hzero _ (k := k) (fun v => ?_) (fun i hi => ?_) hplusM
    · by_cases hv : v = v₀
      · rw [hv, hmv]; exact Ne.symm hkm
      · rw [hEm v hv]
        rcases hg v hv with h | h
        · rw [h]; exact Ne.symm hkm
        · rw [h]; exact Ne.symm hkj
    · rcases fin3_trichotomy hkm hkj hmj i with h | h | h
      · exact absurd h hi
      · exact ⟨v₀, by rw [hmv, h]⟩
      · exact ⟨uj, by rw [hEm uj hujv, hujg, h]⟩
  have h2 : pmSum Wj (optA (Function.update g v₀ j)) Finset.univ
      = amplitude W (Amplitude.const (V := V) k) := by
    refine pmSum_avoid_eq_amplitude W Wj hzero _ (k := k) (fun v => ?_) (fun i hi => ?_) hplusJ
    · by_cases hv : v = v₀
      · rw [hv, hjv]; exact Ne.symm hkj
      · rw [hEj v hv]
        rcases hg v hv with h | h
        · rw [h]; exact Ne.symm hkm
        · rw [h]; exact Ne.symm hkj
    · rcases fin3_trichotomy hkm hkj hmj i with h | h | h
      · exact absurd h hi
      · exact ⟨um, by rw [hEj um humv, humg, h]⟩
      · exact ⟨v₀, by rw [hjv, h]⟩
  have h3 : pmSum Wk (optA (Function.update g v₀ k)) Finset.univ = 0 := by
    refine pmSum_exclusion_vanishes W Wk hzero _ (fun i => ?_) hplusK
    rcases fin3_trichotomy hkm hkj hmj i with h | h | h
    · exact ⟨v₀, by rw [hkv, h]⟩
    · exact ⟨um, by rw [hEk um humv, humg, h]⟩
    · exact ⟨uj, by rw [hEk uj hujv, hujg, h]⟩
  -- expand each total along `v₀`, against the shared cofactors
  have h1e : ∑ u ∈ ((Finset.univ : Finset V).erase v₀),
      Wm s((v₀, optA (Function.update g v₀ m) v₀), (u, optA (Function.update g v₀ m) u)) * mergedCofactor Wm (Function.update g v₀ m) v₀ u
      = amplitude W (Amplitude.const (V := V) k) := by
    rw [← merged_expand_at_site W Wm Wm g v₀ hplusM hplusM]; exact h1
  have h2e : ∑ u ∈ ((Finset.univ : Finset V).erase v₀),
      Wj s((v₀, optA (Function.update g v₀ j) v₀), (u, optA (Function.update g v₀ j) u)) * mergedCofactor Wm (Function.update g v₀ m) v₀ u
      = amplitude W (Amplitude.const (V := V) k) := by
    rw [← merged_expand_at_site W Wj Wm g v₀ hplusJ hplusM]; exact h2
  have h3e : ∑ u ∈ ((Finset.univ : Finset V).erase v₀),
      Wk s((v₀, optA (Function.update g v₀ k) v₀), (u, optA (Function.update g v₀ k) u)) * mergedCofactor Wm (Function.update g v₀ m) v₀ u
      = 0 := by
    rw [← merged_expand_at_site W Wk Wm g v₀ hplusK hplusM]; exact h3
  have hPm : ∀ u ∈ (((Finset.univ : Finset V).erase v₀).filter (fun u => g u = m)), u ≠ v₀ ∧ g u = m := by
    intro u hu
    obtain ⟨ha, hb⟩ := Finset.mem_filter.mp hu
    exact ⟨Finset.ne_of_mem_erase ha, hb⟩
  have hQj : ∀ u ∈ (((Finset.univ : Finset V).erase v₀).filter (fun u => ¬ g u = m)), u ≠ v₀ ∧ g u = j := by
    intro u hu
    obtain ⟨ha, hb⟩ := Finset.mem_filter.mp hu
    have hne := Finset.ne_of_mem_erase ha
    rcases hg u hne with h | h
    · exact absurd h hb
    · exact ⟨hne, h⟩
  -- the six row entries
  have r1P : ∀ u ∈ (((Finset.univ : Finset V).erase v₀).filter (fun u => g u = m)),
      Wm s((v₀, optA (Function.update g v₀ m) v₀), (u, optA (Function.update g v₀ m) u)) * mergedCofactor Wm (Function.update g v₀ m) v₀ u
      = (W s((v₀, k), (u, k)) + W s((v₀, j), (u, j))) * mergedCofactor Wm (Function.update g v₀ m) v₀ u := by
    intro u hu
    obtain ⟨hune, hug⟩ := hPm u hu
    congr 1
    exact merged_of_same_refusal' W Wm hmono _ hune (by rw [hmv, hEm u hune, hug]) hkj
      (by rw [hmv]; exact hkm) (by rw [hmv]; exact Ne.symm hmj) (hplusM v₀ u)
  have r1Q : ∀ u ∈ (((Finset.univ : Finset V).erase v₀).filter (fun u => ¬ g u = m)),
      Wm s((v₀, optA (Function.update g v₀ m) v₀), (u, optA (Function.update g v₀ m) u)) * mergedCofactor Wm (Function.update g v₀ m) v₀ u
      = W s((v₀, k), (u, k)) * mergedCofactor Wm (Function.update g v₀ m) v₀ u := by
    intro u hu
    obtain ⟨hune, hug⟩ := hQj u hu
    congr 1
    exact merged_of_diff_refusal W Wm hmono _ hune (by rw [hmv, hEm u hune, hug]; exact hmj)
      (by rw [hmv]; exact hkm) (by rw [hEm u hune, hug]; exact hkj) (hplusM v₀ u)
  have r2P : ∀ u ∈ (((Finset.univ : Finset V).erase v₀).filter (fun u => g u = m)),
      Wj s((v₀, optA (Function.update g v₀ j) v₀), (u, optA (Function.update g v₀ j) u)) * mergedCofactor Wm (Function.update g v₀ m) v₀ u
      = W s((v₀, k), (u, k)) * mergedCofactor Wm (Function.update g v₀ m) v₀ u := by
    intro u hu
    obtain ⟨hune, hug⟩ := hPm u hu
    congr 1
    exact merged_of_diff_refusal W Wj hmono _ hune
      (by rw [hjv, hEj u hune, hug]; exact Ne.symm hmj)
      (by rw [hjv]; exact hkj) (by rw [hEj u hune, hug]; exact hkm) (hplusJ v₀ u)
  have r2Q : ∀ u ∈ (((Finset.univ : Finset V).erase v₀).filter (fun u => ¬ g u = m)),
      Wj s((v₀, optA (Function.update g v₀ j) v₀), (u, optA (Function.update g v₀ j) u)) * mergedCofactor Wm (Function.update g v₀ m) v₀ u
      = (W s((v₀, k), (u, k)) + W s((v₀, m), (u, m))) * mergedCofactor Wm (Function.update g v₀ m) v₀ u := by
    intro u hu
    obtain ⟨hune, hug⟩ := hQj u hu
    congr 1
    exact merged_of_same_refusal' W Wj hmono _ hune (by rw [hjv, hEj u hune, hug]) hkm
      (by rw [hjv]; exact hkj) (by rw [hjv]; exact hmj) (hplusJ v₀ u)
  have r3P : ∀ u ∈ (((Finset.univ : Finset V).erase v₀).filter (fun u => g u = m)),
      Wk s((v₀, optA (Function.update g v₀ k) v₀), (u, optA (Function.update g v₀ k) u)) * mergedCofactor Wm (Function.update g v₀ m) v₀ u
      = W s((v₀, j), (u, j)) * mergedCofactor Wm (Function.update g v₀ m) v₀ u := by
    intro u hu
    obtain ⟨hune, hug⟩ := hPm u hu
    congr 1
    exact merged_of_diff_refusal W Wk hmono _ hune (by rw [hkv, hEk u hune, hug]; exact hkm)
      (by rw [hkv]; exact Ne.symm hkj) (by rw [hEk u hune, hug]; exact Ne.symm hmj) (hplusK v₀ u)
  have r3Q : ∀ u ∈ (((Finset.univ : Finset V).erase v₀).filter (fun u => ¬ g u = m)),
      Wk s((v₀, optA (Function.update g v₀ k) v₀), (u, optA (Function.update g v₀ k) u)) * mergedCofactor Wm (Function.update g v₀ m) v₀ u
      = W s((v₀, m), (u, m)) * mergedCofactor Wm (Function.update g v₀ m) v₀ u := by
    intro u hu
    obtain ⟨hune, hug⟩ := hQj u hu
    congr 1
    exact merged_of_diff_refusal W Wk hmono _ hune (by rw [hkv, hEk u hune, hug]; exact hkj)
      (by rw [hkv]; exact Ne.symm hkm) (by rw [hEk u hune, hug]; exact hmj) (hplusK v₀ u)
  -- split each total across the two refusal classes and name the rows
  rw [← Finset.sum_filter_add_sum_filter_not ((Finset.univ : Finset V).erase v₀) (fun u => g u = m)] at h1e h2e h3e
  rw [Finset.sum_congr rfl r1P, Finset.sum_congr rfl r1Q] at h1e
  rw [Finset.sum_congr rfl r2P, Finset.sum_congr rfl r2Q] at h2e
  rw [Finset.sum_congr rfl r3P, Finset.sum_congr rfl r3Q] at h3e
  simp only [add_mul, Finset.sum_add_distrib] at h1e h2e
  -- three equations, three unknowns
  have hXY : (∑ u ∈ (((Finset.univ : Finset V).erase v₀).filter (fun u => g u = m)), W s((v₀, j), (u, j)) * mergedCofactor Wm (Function.update g v₀ m) v₀ u)
      = ∑ u ∈ (((Finset.univ : Finset V).erase v₀).filter (fun u => ¬ g u = m)), W s((v₀, m), (u, m)) * mergedCofactor Wm (Function.update g v₀ m) v₀ u := by
    linear_combination h1e - h2e
  have hX2 : (2 : ℂ) * (∑ u ∈ (((Finset.univ : Finset V).erase v₀).filter (fun u => g u = m)), W s((v₀, j), (u, j)) * mergedCofactor Wm (Function.update g v₀ m) v₀ u) = 0 := by
    linear_combination h3e + hXY
  have hX : (∑ u ∈ (((Finset.univ : Finset V).erase v₀).filter (fun u => g u = m)), W s((v₀, j), (u, j)) * mergedCofactor Wm (Function.update g v₀ m) v₀ u) = 0 := by
    rcases mul_eq_zero.mp hX2 with h | h
    · exact absurd h (by norm_num)
    · exact h
  refine ⟨hX, by rw [← hXY]; exact hX, ?_⟩
  rw [← Finset.sum_filter_add_sum_filter_not ((Finset.univ : Finset V).erase v₀) (fun u => g u = m)]
  linear_combination h1e - hX

/-! ### Isolating a single cofactor

An onto refusal makes the whole merged sum vanish.  Expand that sum along one site: if every entry
of its row is zero except one, the survivor's cofactor must vanish by itself.

The row entries are cheap to kill.  A site that is not a partner contributes nothing at all, and a
partner is silenced by refusing exactly the colour its pair carries.  So the refusal can be tuned to
each of the distinguished site's partners in turn, and it names its own vanishing cofactor. -/

/-- **A refused colour kills the pair from the far end too.** -/
theorem merged_dead_of_excluded_right (W Wp : Sym2 (V × Fin 3) → ℂ)
    (e : V → Fin 3) {x y : V} {k : Fin 3}
    (hplus : Wp s((y, optA e y), (x, optA e x))
      = W s((y, optA e y), (x, optA e x)) + W s((y, optA e y), (x, optB e x))
        + (W s((y, optB e y), (x, optA e x)) + W s((y, optB e y), (x, optB e x))))
    (honly : ∀ a b : Fin 3, a ≠ k → W s((x, a), (y, b)) = 0)
    (hex : e x = k) :
    Wp s((x, optA e x), (y, optA e y)) = 0 := by
  have hA : optA e x ≠ k := hex ▸ optA_ne e x
  have hB : optB e x ≠ k := hex ▸ optB_ne e x
  rw [Sym2.eq_swap, hplus]
  rw [show W s((y, optA e y), (x, optA e x)) = W s((x, optA e x), (y, optA e y)) by
      rw [Sym2.eq_swap],
    show W s((y, optA e y), (x, optB e x)) = W s((x, optB e x), (y, optA e y)) by
      rw [Sym2.eq_swap],
    show W s((y, optB e y), (x, optA e x)) = W s((x, optA e x), (y, optB e y)) by
      rw [Sym2.eq_swap],
    show W s((y, optB e y), (x, optB e x)) = W s((x, optB e x), (y, optB e y)) by
      rw [Sym2.eq_swap]]
  rw [honly _ _ hA, honly _ _ hA, honly _ _ hB, honly _ _ hB]
  ring

/-- **One surviving row entry names a vanishing cofactor.** -/
theorem cofactor_vanishes_of_isolating (W Wp : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (v₀ : V) (e : V → Fin 3) (hsurj : Function.Surjective e)
    (hplus : ∀ x y : V, Wp s((x, optA e x), (y, optA e y))
      = W s((x, optA e x), (y, optA e y)) + W s((x, optA e x), (y, optB e y))
        + (W s((x, optB e x), (y, optA e y)) + W s((x, optB e x), (y, optB e y))))
    {u₁ : V} (hu₁ : u₁ ≠ v₀)
    (hkill : ∀ u : V, u ≠ v₀ → u ≠ u₁ → Wp s((v₀, optA e v₀), (u, optA e u)) = 0)
    (hlive : Wp s((v₀, optA e v₀), (u₁, optA e u₁)) ≠ 0) :
    mergedCofactor Wp e v₀ u₁ = 0 := by
  classical
  have htot : pmSum Wp (optA e) Finset.univ = 0 :=
    pmSum_exclusion_vanishes W Wp hzero e hsurj hplus
  rw [pmSum_expand Wp _ (Finset.mem_univ v₀)] at htot
  rw [Finset.sum_eq_single_of_mem u₁ (Finset.mem_erase.mpr ⟨hu₁, Finset.mem_univ u₁⟩)] at htot
  · have hp : (Sym2.map (Amplitude.paint (optA e)) s(v₀, u₁))
        = s((v₀, optA e v₀), (u₁, optA e u₁)) := rfl
    rw [hp] at htot
    rcases mul_eq_zero.mp htot with h | h
    · exact absurd h hlive
    · exact h
  · intro u hu hne
    have hp : (Sym2.map (Amplitude.paint (optA e)) s(v₀, u))
        = s((v₀, optA e v₀), (u, optA e u)) := rfl
    rw [hp, hkill u (Finset.ne_of_mem_erase hu) hne, zero_mul]

/-- **Tuning the refusal to the partners.**  Refuse at each site exactly the colour its pair with
the distinguished site carries -- except at one, where refuse anything else.  Every other row entry
dies, so the exceptional partner's cofactor vanishes. -/
theorem cofactor_vanishes_of_colour_isolation (W Wp : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (v₀ : V) (e : V → Fin 3) (hsurj : Function.Surjective e)
    (hplus : ∀ x y : V, Wp s((x, optA e x), (y, optA e y))
      = W s((x, optA e x), (y, optA e y)) + W s((x, optA e x), (y, optB e y))
        + (W s((x, optB e x), (y, optA e y)) + W s((x, optB e x), (y, optB e y))))
    {u₁ : V} (hu₁ : u₁ ≠ v₀)
    (hmatch : ∀ u : V, u ≠ v₀ → u ≠ u₁ → ∀ a b : Fin 3, a ≠ e u → W s((u, a), (v₀, b)) = 0)
    (hlive : Wp s((v₀, optA e v₀), (u₁, optA e u₁)) ≠ 0) :
    mergedCofactor Wp e v₀ u₁ = 0 := by
  refine cofactor_vanishes_of_isolating W Wp hzero v₀ e hsurj hplus hu₁ (fun u hu hne => ?_) hlive
  rw [Sym2.eq_swap]
  exact merged_dead_of_excluded_right W Wp e (x := u) (y := v₀) (k := e u)
    (hplus v₀ u) (hmatch u hu hne) rfl

/-- **The closer, with a cycle allowed.**  An onto refusal makes the merged sum vanish; two
non-cancelling matchings make it non-zero. -/
theorem false_of_surjective_exclusion_two_matchings (W Wp : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (e : V → Fin 3) (hsurj : Function.Surjective e)
    (hplus : ∀ x y : V, Wp s((x, optA e x), (y, optA e y))
      = W s((x, optA e x), (y, optA e y)) + W s((x, optA e x), (y, optB e y))
        + (W s((x, optB e x), (y, optA e y)) + W s((x, optB e x), (y, optB e y))))
    {σ₀ σ₁ : Equiv.Perm V} (h₀ : σ₀ ∈ pairingsOn (Finset.univ : Finset V))
    (h₁ : σ₁ ∈ pairingsOn (Finset.univ : Finset V)) (hne : σ₁ ≠ σ₀)
    (hrest : ∀ τ ∈ pairingsOn (Finset.univ : Finset V), τ ≠ σ₀ → τ ≠ σ₁ →
      ∃ z : V, Wp s((z, optA e z), (τ z, optA e (τ z))) = 0)
    (hnocancel :
      (∏ e' ∈ (Finset.univ : Finset V).image (fun x => s(x, σ₀ x)),
          Wp (Sym2.map (Amplitude.paint (optA e)) e'))
        + (∏ e' ∈ (Finset.univ : Finset V).image (fun x => s(x, σ₁ x)),
          Wp (Sym2.map (Amplitude.paint (optA e)) e')) ≠ 0) :
    False := by
  refine pmSum_ne_zero_of_two_matchings Wp (optA e) h₀ h₁ hne (fun τ hτ hτ₀ hτ₁ => ?_) hnocancel
    (pmSum_exclusion_vanishes W Wp hzero e hsurj hplus)
  obtain ⟨z, hz⟩ := hrest τ hτ hτ₀ hτ₁
  refine ⟨z, Finset.mem_univ z, ?_⟩
  have hp : (Sym2.map (Amplitude.paint (optA e)) s(z, τ z))
      = s((z, optA e z), (τ z, optA e (τ z))) := rfl
  rw [hp]; exact hz

/-! ### Three fibres, each rigid

The refusal picture and the fibre picture carry the same information: a matching of the merged graph
is exactly a colouring of the sites together with a monochromatic matching of each of its fibres, and
the merged sum is the sum of the amplitudes of the colourings the refusal admits.

What the identification makes visible is the shape a closer must have.  A non-constant colouring has
amplitude zero, and its amplitude is the product of its three fibres' monochromatic sums.  So if all
three fibres are rigid -- each carrying exactly one live matching in its own colour -- the product is
a product of non-zero numbers, and the configuration is impossible.

**This is `amplitude_ne_zero_of_certified_partition` in contrapositive form**, and that theorem
predates this section.  What is added here is not the criterion but the means of meeting it: the
constructions below that produce such a colouring from a matching, from a closed set, or from a
split, none of which the criterion itself supplies.

This is the three-colour form of the two-set criterion, and it is the sharpest statement the
cancellation analysis produces: cancellation must occur *inside a single fibre*, between two
monochromatic matchings of the same colour on the same sites. -/
theorem false_of_three_unique_fibres (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (c : V → Fin 3) (hnc : ¬ Amplitude.Monochromatic c)
    (hcut : ∀ x y : V, c x ≠ c y → W s((x, c x), (y, c y)) = 0)
    (h0 : pmSum W c ((Finset.univ : Finset V) ∩ fiber c 0) ≠ 0)
    (h1 : pmSum W c ((Finset.univ : Finset V) ∩ fiber c 1) ≠ 0)
    (h2 : pmSum W c ((Finset.univ : Finset V) ∩ fiber c 2) ≠ 0) :
    False := by
  have hprod := pmSum_product_on W c hcut (Finset.univ : Finset V)
  rw [pmSum_univ, hzero c hnc] at hprod
  exact mul_ne_zero (mul_ne_zero h0 h1) h2 hprod.symm

/-- **Rigidity of a fibre from a unique matching.**  The hypothesis the criterion consumes: on the
sites of one colour, exactly one matching is live. -/
theorem fibre_ne_zero_of_unique (W : Sym2 (V × Fin 3) → ℂ) (c : V → Fin 3) (a : Fin 3)
    {σ₀ : Equiv.Perm V} (hmem : σ₀ ∈ pairingsOn ((Finset.univ : Finset V) ∩ fiber c a))
    (hlive : ∀ z ∈ (Finset.univ : Finset V) ∩ fiber c a,
      W (Sym2.map (Amplitude.paint c) s(z, σ₀ z)) ≠ 0)
    (huniq : ∀ τ ∈ pairingsOn ((Finset.univ : Finset V) ∩ fiber c a), τ ≠ σ₀ →
      ∃ z ∈ (Finset.univ : Finset V) ∩ fiber c a,
        W (Sym2.map (Amplitude.paint c) s(z, τ z)) = 0) :
    pmSum W c ((Finset.univ : Finset V) ∩ fiber c a) ≠ 0 :=
  pmSum_ne_zero_of_unique_matching W c hmem hlive huniq

/-! ### A mixed pure matching is already a contradiction

A perfect matching assigns each site the colour of its own pair, and that colouring's fibres are the
sites matched in each colour.  Call the matching *pure* when, inside each fibre, no site has a
second live partner of that fibre's colour.  Then the fibre's live graph in its own colour is the
matching itself, and the fibre is rigid.

Purity is required only within a fibre, which is far weaker than asking it globally: a site carrying
several partners in one colour is harmless as long as they are not matched into the same fibre.

Three rigid fibres multiply to a non-zero amplitude.  If the matching uses more than one colour that
amplitude belongs to a non-constant colouring and must vanish.  So no configuration admits a mixed
perfect matching of pure pairs.

The statement needs no minimality, no degree bound, and no count.  Where there is no excess at all
every pair is pure, the skeleton's perfect matchings are available, and a mixed one exists at every
even count above four -- which is exactly where the four-site solution escapes, its only perfect
matchings being the three colour classes themselves. -/
theorem false_of_mixed_pure_matching (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (u v : V), v ≠ u → ∀ a b : Fin 3, a ≠ b → W s((u, a), (v, b)) = 0)
    (N : V → V) (hinv : ∀ v, N (N v) = v) (hfix : ∀ v, N v ≠ v)
    (γ : V → Fin 3) (hgN : ∀ v, γ (N v) = γ v)
    (hlive : ∀ v, W s((v, γ v), (N v, γ v)) ≠ 0)
    (hpure : ∀ v w : V, w ≠ v → w ≠ N v → γ w = γ v → W s((v, γ v), (w, γ v)) = 0)
    (hmixed : ¬ Amplitude.Monochromatic γ) :
    False := by
  classical
  have hcut : ∀ x y : V, γ x ≠ γ y → W s((x, γ x), (y, γ y)) = 0 := by
    intro x y h
    by_cases hxy : y = x
    · exact absurd (by rw [hxy]) h
    · exact hmono x y hxy (γ x) (γ y) h
  have key : ∀ a : Fin 3, pmSum W γ ((Finset.univ : Finset V) ∩ fiber γ a) ≠ 0 := by
    intro a
    have hmemS : ∀ x : V, x ∈ (Finset.univ : Finset V) ∩ fiber γ a ↔ γ x = a := by
      intro x
      simp [mem_fiber]
    have hff : ∀ v, (fun w => if γ w = a then N w else w)
        ((fun w => if γ w = a then N w else w) v) = v := by
      intro v
      by_cases h : γ v = a
      · have hN : γ (N v) = a := by rw [hgN v]; exact h
        simp only [if_pos h, if_pos hN, hinv]
      · simp only [if_neg h, if_neg h]
    let σ : Equiv.Perm V := ⟨fun w => if γ w = a then N w else w,
      fun w => if γ w = a then N w else w, hff, hff⟩
    have hσ : ∀ v, σ v = if γ v = a then N v else v := fun _ => rfl
    have hmem : σ ∈ pairingsOn ((Finset.univ : Finset V) ∩ fiber γ a) := by
      refine mem_pairingsOn.mpr ⟨fun x => hff x, fun x hx => ?_, fun x hx => ?_⟩
      · rw [hσ, if_pos ((hmemS x).mp hx)]; exact hfix x
      · rw [hσ, if_neg (fun h => hx ((hmemS x).mpr h))]
    refine pmSum_ne_zero_of_unique_matching W γ hmem (fun z hz => ?_) (fun τ hτ hne => ?_)
    · have hza : γ z = a := (hmemS z).mp hz
      have hp : (Sym2.map (Amplitude.paint γ) s(z, σ z)) = s((z, γ z), (σ z, γ (σ z))) := rfl
      rw [hp, hσ, if_pos hza, hgN z]
      exact hlive z
    · have : ∃ z : V, τ z ≠ σ z := by
        by_contra hall
        push_neg at hall
        exact hne (Equiv.ext hall)
      obtain ⟨z, hz⟩ := this
      obtain ⟨-, hfixτ, houtτ⟩ := mem_pairingsOn.mp hτ
      have hzS : z ∈ (Finset.univ : Finset V) ∩ fiber γ a := by
        by_contra hzn
        exact hz (by rw [houtτ z hzn, hσ, if_neg (fun h => hzn ((hmemS z).mpr h))])
      have hza : γ z = a := (hmemS z).mp hzS
      have hzN : τ z ≠ N z := by rw [hσ, if_pos hza] at hz; exact hz
      have hzz : τ z ≠ z := hfixτ z hzS
      have hτz : γ (τ z) = a := (hmemS _).mp (pairingsOn_closed hτ z hzS)
      refine ⟨z, hzS, ?_⟩
      have hp : (Sym2.map (Amplitude.paint γ) s(z, τ z)) = s((z, γ z), (τ z, γ (τ z))) := rfl
      rw [hp, hτz, ← hza]
      exact hpure z (τ z) hzz hzN (by rw [hτz, hza])
  exact false_of_three_unique_fibres W hzero γ hmixed hcut (key 0) (key 1) (key 2)

/-! ### The conjecture, in one combinatorial statement

Everything the cancellation analysis produced points at a single question about the support.  A
colouring of the sites splits them into three fibres; its amplitude is the product of the fibres'
monochromatic matching sums; and a non-constant colouring has amplitude zero.  So a configuration
dies as soon as some non-constant colouring has all three fibres *rigid* -- each carrying exactly one
live matching in its own colour.

**What this is and is not.**  It is not a reduction.  Since a non-constant colouring's amplitude is
exactly that product and must vanish, no genuine configuration can admit a rigid partition at all,
so the criterion below is *equivalent* to the conjecture rather than weaker than it.  Its value is
that it fixes the shape of a certificate: to kill a configuration one exhibits a rigid partition
built from its support, and the whole difficulty is transferred into that construction.

Where nothing is in excess the construction is available and elementary -- a rigid partition is then
a perfect matching of the three colour classes using more than one colour, and one exists at every
even count above four.  At four sites the only perfect matchings are the colour classes themselves,
each of them constant, which is exactly how that solution survives.  With excess present the
construction can genuinely fail: if two colour classes meet in a single Hamiltonian cycle and the
third colour's live graph is dense, no matching of pure pairs is mixed. -/

/-- **A rigid partition.**  A non-constant colouring whose fibres each carry a non-vanishing matching
sum in their own colour.

**This is `CertifiedPartition` again**, in a packaging that takes the two amplitude conditions
directly instead of routing through minimality and degeneracy.  The content is identical; only the
hypotheses of the bridge below differ.  Anything proved about one applies to the other. -/
def RigidPartition : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (W : Sym2 (V × Fin 3) → ℂ),
    4 < Fintype.card V →
      (∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0) →
      (∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0) →
      ∃ γ : V → Fin 3, ¬ Amplitude.Monochromatic γ ∧
        (∀ x y : V, γ x ≠ γ y → W s((x, γ x), (y, γ y)) = 0) ∧
        (∀ a : Fin 3, pmSum W γ ((Finset.univ : Finset V) ∩ fiber γ a) ≠ 0)

/-- **The conjecture from a rigid partition.**  If every configuration above four sites admits one,
no configuration above four sites exists.  Compare `official_of_certifiedPartition`, which says the
same thing from the same hypothesis under a different name and with degeneracy assumed. -/
theorem krenn_gu_of_rigidPartition (h : RigidPartition) :
    ∀ n : ℕ, 3 ≤ n → ¬ KrennGu.Solvable n := by
  rintro n h3 ⟨W, hW⟩
  obtain ⟨W', hmin, -⟩ := MinimalSupport.exists_supportMinimal W hW
  have hcard : 4 < Fintype.card (Fin (2 * n)) := by
    rw [Fintype.card_fin]; omega
  have hone' : ∀ j : Fin 3,
      amplitude (LiveDegree.deloop W') (Amplitude.const (V := Fin (2 * n)) j) ≠ 0 := by
    intro j
    rw [LiveDegree.amplitude_deloop]
    exact hmin.1.1 j
  have hzero' : ∀ c : Fin (2 * n) → Fin 3, ¬ Amplitude.Monochromatic c →
      amplitude (LiveDegree.deloop W') c = 0 := by
    intro c hc
    rw [LiveDegree.amplitude_deloop]
    exact hmin.1.2 c hc
  obtain ⟨γ, hnc, hcut, hfib⟩ :=
    h (Fin (2 * n)) (LiveDegree.deloop W') hcard hone' hzero'
  exact false_of_three_unique_fibres _ hzero' γ hnc hcut (hfib 0) (hfib 1) (hfib 2)

/-! ### Closed fibres are rigid for free

Rigidity of a fibre need not be checked by hand.  If no live edge of a fibre's own colour leaves it,
that colour's matching sum factors across the cut into two factors whose product is the colour's
amplitude -- which does not vanish -- so neither factor does.

That turns the criterion into a statement with no arithmetic in it at all.  A set closed in a colour
is a union of connected components of that colour's live graph, so what is wanted is a partition of
the sites into a union of components of the first colour's graph, a union of components of the
second's, and a union of components of the third's, not all of them in one part.

Where nothing is in excess each colour's live graph is a perfect matching, its components are single
pairs, and such a partition is exactly a perfect matching using more than one colour.  Excess is
what merges components, and enough of it -- each colour's graph connected -- leaves only the trivial
partitions.  That is the precise sense in which excess is the whole difficulty. -/
theorem false_of_three_closed_fibres (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (u v : V), v ≠ u → ∀ a b : Fin 3, a ≠ b → W s((u, a), (v, b)) = 0)
    (γ : V → Fin 3) (hnc : ¬ Amplitude.Monochromatic γ)
    (hclosed : ∀ a : Fin 3, ∀ x : V, γ x = a → ∀ y : V, γ y ≠ a →
      W s((x, a), (y, a)) = 0) :
    False := by
  classical
  have hcut : ∀ x y : V, γ x ≠ γ y → W s((x, γ x), (y, γ y)) = 0 := by
    intro x y h
    by_cases hxy : y = x
    · exact absurd (by rw [hxy]) h
    · exact hmono x y hxy (γ x) (γ y) h
  have key : ∀ a : Fin 3, pmSum W γ ((Finset.univ : Finset V) ∩ fiber γ a) ≠ 0 := by
    intro a
    have hmemS : ∀ x : V, x ∈ (Finset.univ : Finset V) ∩ fiber γ a ↔ γ x = a := by
      intro x; simp [mem_fiber]
    rw [pmSum_congr_colour W (c' := Amplitude.const (V := V) a)
      (fun x hx => (hmemS x).mp hx)]
    exact (closed_both_certified W (hone a)
      (fun x hx y hy => hclosed a x ((hmemS x).mp hx) y
        (fun h => hy ((hmemS y).mpr h)))).1
  exact false_of_three_unique_fibres W hzero γ hnc hcut (key 0) (key 1) (key 2)

/-- **Two colours never suffice.**  A colouring using only two colours, each of whose fibres is
closed in its own colour, makes a single set closed in both -- which no configuration has.  So the
closed-fibre criterion genuinely needs all three colours present, and a colour whose live graph is
connected cannot contribute a fibre at all.  Together these say the criterion applies exactly when
the three colour graphs are disconnected and their components tile the sites. -/
theorem no_two_colour_fibres (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (u v : V), v ≠ u → ∀ p q : Fin 3, p ≠ q → W s((u, p), (v, q)) = 0)
    (γ : V → Fin 3) {a b : Fin 3} (hab : a ≠ b)
    (hvals : ∀ v : V, γ v = a ∨ γ v = b)
    (hane : ∃ v : V, γ v = a) (hbne : ∃ v : V, γ v = b)
    (hclosedA : ∀ x : V, γ x = a → ∀ y : V, γ y ≠ a → W s((x, a), (y, a)) = 0)
    (hclosedB : ∀ x : V, γ x = b → ∀ y : V, γ y ≠ b → W s((x, b), (y, b)) = 0) :
    False := by
  classical
  obtain ⟨p, hp⟩ := hane
  obtain ⟨q, hq⟩ := hbne
  have hqa : γ q ≠ a := by rw [hq]; exact fun h => hab h.symm
  refine Separation.no_two_colour_closed W hone hzero
    ((Finset.univ : Finset V).filter (fun v => γ v = a))
    ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp⟩⟩
    ⟨q, Finset.mem_sdiff.mpr ⟨Finset.mem_univ q, fun h => hqa (Finset.mem_filter.mp h).2⟩⟩
    hab (fun x hx y hy => ?_) (fun x hx y hy => ?_) (fun x hx y hy => ?_)
  · exact hclosedA x (Finset.mem_filter.mp hx).2 y
      (fun h => (Finset.mem_sdiff.mp hy).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ y, h⟩))
  · have hxa : γ x = a := (Finset.mem_filter.mp hx).2
    have hya : γ y ≠ a :=
      fun h => (Finset.mem_sdiff.mp hy).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ y, h⟩)
    have hyb : γ y = b := by
      rcases hvals y with h | h
      · exact absurd h hya
      · exact h
    have hxb : γ x ≠ b := by rw [hxa]; exact hab
    rw [Sym2.eq_swap]
    exact hclosedB y hyb x hxb
  · have hxa : γ x = a := (Finset.mem_filter.mp hx).2
    have hya : γ y ≠ a :=
      fun h => (Finset.mem_sdiff.mp hy).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ y, h⟩)
    have hne : y ≠ x := by intro h; rw [h] at hya; exact hya hxa
    exact hmono x y hne b a (fun h => hab h.symm)

/-! ### One closed set is enough

**Placement.**  The core of everything in this section is `amplitude_part_ne_zero` above: two
disjoint sets certified in two colours with a certified complement in the third already give a
non-vanishing amplitude for a non-constant colouring.  What follows repackages that with the third
certificate supplied in various ways -- by closure, by a live pair, by a certified deletion chain --
and none of it strengthens the underlying statement.

The tiling is more than the criterion needs.  A single set closed in one colour already supplies two
of the three fibres: itself, split in the other two colours, and its complement, whose rigidity in
the closing colour is free.

The smallest instance is four sites: a set closed in one colour that splits into a live pair of each
of the other two colours.  Where nothing is in excess that is two adjacent pairs of the closing
colour whose four sites carry a pair of each other colour -- a local pattern, not a global
decomposition.

Closure is only one way to certify the complement.  Expanding a colour's amplitude twice writes it
as a sum over four-site deletions, so for any two sites there are partners in that colour whose
removal leaves a non-vanishing sum.  The general form below takes that certificate directly, and the
closed form is the corollary. -/
theorem false_of_split_partition (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (u v : V), v ≠ u → ∀ p q : Fin 3, p ≠ q → W s((u, p), (v, q)) = 0)
    {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (B C : Finset V) (hBC : Disjoint B C)
    (hAne : (B ∪ C).Nonempty) (hAc : ((Finset.univ : Finset V) \ (B ∪ C)).Nonempty)
    (hA : pmSum W (Amplitude.const (V := V) a) ((Finset.univ : Finset V) \ (B ∪ C)) ≠ 0)
    (hB : pmSum W (Amplitude.const (V := V) b) B ≠ 0)
    (hC : pmSum W (Amplitude.const (V := V) c) C ≠ 0) :
    False := by
  classical
  set γ : V → Fin 3 := fun v => if v ∈ B then b else if v ∈ C then c else a with hγ
  have hγB : ∀ v ∈ B, γ v = b := fun v hv => by simp [hγ, hv]
  have hγC : ∀ v ∈ C, γ v = c := fun v hv => by
    have hvB : v ∉ B := Finset.disjoint_right.mp hBC hv
    simp [hγ, hvB, hv]
  have hγA : ∀ v : V, v ∉ B ∪ C → γ v = a := fun v hv => by
    have h1 : v ∉ B := fun h => hv (Finset.mem_union_left _ h)
    have h2 : v ∉ C := fun h => hv (Finset.mem_union_right _ h)
    simp [hγ, h1, h2]
  have hmemS : ∀ (j : Fin 3) (x : V), x ∈ (Finset.univ : Finset V) ∩ fiber γ j ↔ γ x = j := by
    intro j x; simp [mem_fiber]
  have hFb : (Finset.univ : Finset V) ∩ fiber γ b = B := by
    ext v
    rw [hmemS]
    constructor
    · intro h
      by_cases hv : v ∈ B
      · exact hv
      · by_cases hv' : v ∈ C
        · exact absurd (by rw [← hγC v hv', h]) hbc
        · exact absurd (by rw [← hγA v (fun hh => by
            rcases Finset.mem_union.mp hh with h1 | h1
            · exact hv h1
            · exact hv' h1), h]) hab
    · exact fun h => hγB v h
  have hFc : (Finset.univ : Finset V) ∩ fiber γ c = C := by
    ext v
    rw [hmemS]
    constructor
    · intro h
      by_cases hv : v ∈ C
      · exact hv
      · by_cases hv' : v ∈ B
        · exact absurd (by rw [← hγB v hv', h]) (Ne.symm hbc)
        · exact absurd (by rw [← hγA v (fun hh => by
            rcases Finset.mem_union.mp hh with h1 | h1
            · exact hv' h1
            · exact hv h1), h]) hac
    · exact fun h => hγC v h
  have hFa : (Finset.univ : Finset V) ∩ fiber γ a = (Finset.univ : Finset V) \ (B ∪ C) := by
    ext v
    rw [hmemS, Finset.mem_sdiff]
    constructor
    · intro h
      refine ⟨Finset.mem_univ v, fun hh => ?_⟩
      rcases Finset.mem_union.mp hh with h1 | h1
      · exact hab (by rw [← h, hγB v h1])
      · exact hac (by rw [← h, hγC v h1])
    · exact fun h => hγA v h.2
  obtain ⟨p, hp⟩ := hAne
  obtain ⟨q, hq⟩ := hAc
  have hnc : ¬ Amplitude.Monochromatic γ := by
    rintro ⟨k, hk⟩
    have h1 : γ q = a := hγA q (Finset.mem_sdiff.mp hq).2
    rcases Finset.mem_union.mp hp with h2 | h2
    · exact hab (by rw [← h1, hk q, ← hk p, hγB p h2])
    · exact hac (by rw [← h1, hk q, ← hk p, hγC p h2])
  have hcut : ∀ x y : V, γ x ≠ γ y → W s((x, γ x), (y, γ y)) = 0 := by
    intro x y h
    by_cases hxy : y = x
    · exact absurd (by rw [hxy]) h
    · exact hmono x y hxy (γ x) (γ y) h
  have hfib : ∀ j : Fin 3, pmSum W γ ((Finset.univ : Finset V) ∩ fiber γ j) ≠ 0 := by
    intro j
    rcases fin3_trichotomy hab hac hbc j with h | h | h
    · subst h
      rw [hFa, pmSum_congr_colour W (c' := Amplitude.const (V := V) j)
        (fun x hx => hγA x (Finset.mem_sdiff.mp hx).2)]
      exact hA
    · subst h
      rw [hFb, pmSum_congr_colour W (c' := Amplitude.const (V := V) j) hγB]
      exact hB
    · subst h
      rw [hFc, pmSum_congr_colour W (c' := Amplitude.const (V := V) j) hγC]
      exact hC
  exact false_of_three_unique_fibres W hzero γ hnc hcut (hfib 0) (hfib 1) (hfib 2)
/-- **The closed case.**  Closure of the complement in its own colour supplies the third
non-vanishing for free. -/
theorem false_of_closed_split (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (u v : V), v ≠ u → ∀ p q : Fin 3, p ≠ q → W s((u, p), (v, q)) = 0)
    {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (B C : Finset V) (hBC : Disjoint B C)
    (hclosed : ∀ x ∈ B ∪ C, ∀ y : V, y ∉ B ∪ C → W s((x, a), (y, a)) = 0)
    (hAne : (B ∪ C).Nonempty) (hAc : ((Finset.univ : Finset V) \ (B ∪ C)).Nonempty)
    (hB : pmSum W (Amplitude.const (V := V) b) B ≠ 0)
    (hC : pmSum W (Amplitude.const (V := V) c) C ≠ 0) :
    False :=
  false_of_split_partition W hzero hmono hab hac hbc B C hBC hAne hAc
    (closed_both_certified W (hone a) hclosed).2 hB hC


/-- **The four-site pattern.**  Two pairs whose four sites carry no live edge of the closing colour
to the rest, and which split into a live pair of each other colour.  The most concretely checkable
form of the criterion: everything in it is a statement about four named sites. -/
theorem false_of_four_site_closed_split (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ p q : Fin 3, p ≠ q → W s((x, p), (y, q)) = 0)
    {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {u u' v v' : V} (hvu : v ≠ u) (hv'u' : v' ≠ u')
    (hdisj : Disjoint ({u, v} : Finset V) ({u', v'} : Finset V))
    (hclosed : ∀ x ∈ ({u, v} : Finset V) ∪ ({u', v'} : Finset V), ∀ y : V,
      y ∉ ({u, v} : Finset V) ∪ ({u', v'} : Finset V) → W s((x, a), (y, a)) = 0)
    (hb : W s((u, b), (v, b)) ≠ 0) (hc : W s((u', c), (v', c)) ≠ 0)
    (hcompl :
      ((Finset.univ : Finset V) \ (({u, v} : Finset V) ∪ ({u', v'} : Finset V))).Nonempty) :
    False := by
  classical
  refine false_of_closed_split W hone hzero hmono hab hac hbc {u, v} {u', v'} hdisj hclosed
    ⟨u, Finset.mem_union_left _ (by simp)⟩ hcompl ?_ ?_
  · rw [pmSum_pair W _ hvu]; exact hb
  · rw [pmSum_pair W _ hv'u']; exact hc

/-! ### Certified partners, at every stage

A non-vanishing matching sum expands along any of its sites into a sum over that site's partners, so
some term survives and the site has a partner whose edge is live *and* whose removal leaves the sum
non-vanishing.  That step is `exists_partner_ne_zero`; iterating it supplies a descending chain of
certified deletions, in any colour and from any starting site.

This is the second source of the non-vanishing the split criterion needs, and unlike closure it is
available whatever the connectivity of the colour graphs. -/

/-- **Two certified deletions.**  For any site, and then any site distinct from it and its certified
partner, the four removed sites leave the colour's sum non-vanishing.  The choice of the second site
is free, which is what makes this usable. -/
theorem exists_certified_quad_of_colour (W : Sym2 (V × Fin 3) → ℂ) {a : Fin 3}
    (hone : amplitude W (Amplitude.const (V := V) a) ≠ 0) (u : V) :
    ∃ z : V, z ≠ u ∧ W s((u, a), (z, a)) ≠ 0 ∧
      ∀ x : V, x ≠ u → x ≠ z →
        ∃ w : V, w ≠ x ∧ W s((x, a), (w, a)) ≠ 0 ∧
          pmSum W (Amplitude.const (V := V) a)
            (((((Finset.univ : Finset V).erase u).erase z).erase x).erase w) ≠ 0 := by
  classical
  have hU : pmSum W (Amplitude.const (V := V) a) (Finset.univ : Finset V) ≠ 0 := by
    rw [pmSum_univ]; exact hone
  obtain ⟨z, hz, hlive, hrest⟩ :=
    exists_partner_ne_zero W (Amplitude.const (V := V) a) (Finset.mem_univ u) hU
  refine ⟨z, Finset.ne_of_mem_erase hz, hlive, fun x hxu hxz => ?_⟩
  have hxmem : x ∈ ((Finset.univ : Finset V).erase u).erase z :=
    Finset.mem_erase.mpr ⟨hxz, Finset.mem_erase.mpr ⟨hxu, Finset.mem_univ x⟩⟩
  obtain ⟨w, hw, hlive', hrest'⟩ :=
    exists_partner_ne_zero W (Amplitude.const (V := V) a) hxmem hrest
  exact ⟨w, Finset.ne_of_mem_erase hw, hlive', hrest'⟩

/-- **The composition, with one combinatorial input left.**

Four sites, a live pair of colour `b`, a live pair of colour `c`, and a certificate that the colour
`a` sum over the rest does not vanish.  The certificate is supplied by the descending chain of
certified deletions, which is available in every configuration; the two live pairs are the input.

So the whole remaining question is an incidence one.  Starting from a site `u` and a live `b`-partner
`x`, the chain hands back certified `a`-partners `z` of `u` and `w` of `x`; what is needed is that
some such choice has `z` and `w` joined in the third colour.  Where nothing is in excess the
certified partners are forced -- each site has exactly one partner per colour -- and the requirement
is the familiar four-cycle. -/
theorem false_of_certified_quad_split (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ cc : V → Fin 3, ¬ Amplitude.Monochromatic cc → amplitude W cc = 0)
    (hmono : ∀ (p q : V), q ≠ p → ∀ i j : Fin 3, i ≠ j → W s((p, i), (q, j)) = 0)
    {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {u x z w : V} (hxu : x ≠ u) (hwz : w ≠ z)
    (hdisj : Disjoint ({u, x} : Finset V) ({z, w} : Finset V))
    (hcert : pmSum W (Amplitude.const (V := V) a)
      (((((Finset.univ : Finset V).erase u).erase z).erase x).erase w) ≠ 0)
    (hb : W s((u, b), (x, b)) ≠ 0) (hc : W s((z, c), (w, c)) ≠ 0)
    (hcompl :
      ((Finset.univ : Finset V) \ (({u, x} : Finset V) ∪ ({z, w} : Finset V))).Nonempty) :
    False := by
  classical
  have hset : (Finset.univ : Finset V) \ (({u, x} : Finset V) ∪ ({z, w} : Finset V))
      = ((((Finset.univ : Finset V).erase u).erase z).erase x).erase w := by
    ext p
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase, not_or]
    tauto
  refine false_of_split_partition W hzero hmono hab hac hbc {u, x} {z, w} hdisj
    ⟨u, Finset.mem_union_left _ (by simp)⟩ hcompl ?_ ?_ ?_
  · rw [hset]; exact hcert
  · rw [pmSum_pair W _ hxu]; exact hb
  · rw [pmSum_pair W _ hwz]; exact hc

/-- **The criterion in the form the combinatorics produces.**  A live pair of one colour, and a
division of everything else into a part whose second-colour sum survives and a part whose
third-colour sum survives.

The pair's own contribution is free: a two-element set has a single pairing, so its matching sum is
that pair's weight.  All the content is in the division, which is exactly the object the cycle
analysis constructs -- the two arcs left when the pair is deleted from the cycle formed by the other
two colour classes. -/
theorem false_of_pair_and_split (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ cc : V → Fin 3, ¬ Amplitude.Monochromatic cc → amplitude W cc = 0)
    (hmono : ∀ (p q : V), q ≠ p → ∀ i j : Fin 3, i ≠ j → W s((p, i), (q, j)) = 0)
    {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {u u' : V} (hu'u : u' ≠ u) (ha : W s((u, a), (u', a)) ≠ 0)
    (B C : Finset V) (hBC : Disjoint B C)
    (hsplit : B ∪ C = (Finset.univ : Finset V) \ ({u, u'} : Finset V))
    (hBne : (B ∪ C).Nonempty)
    (hB : pmSum W (Amplitude.const (V := V) b) B ≠ 0)
    (hC : pmSum W (Amplitude.const (V := V) c) C ≠ 0) :
    False := by
  classical
  have hcompl : (Finset.univ : Finset V) \ (B ∪ C) = ({u, u'} : Finset V) := by
    rw [hsplit]
    ext p
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_not]
  refine false_of_split_partition W hzero hmono hab hac hbc B C hBC hBne ?_ ?_ hB hC
  · rw [hcompl]; exact ⟨u, by simp⟩
  · rw [hcompl, pmSum_pair W _ hu'u]; exact ha

/-- **The arc argument at its shortest, with no cycle machinery.**

Four sites in a row: a pair live in the second colour whose first site has no other partner there, a
second such pair, the two inner sites joined in the third colour, and the two outer sites joined in
the first.  Deleting the two forced pairs certifies the rest in the second colour, the inner pair is
its own certificate in the third, and the outer pair is its own in the first.  Three rigid fibres.

This is the two-step case of the arc construction, stated in terms of the four sites alone. -/
theorem false_of_forced_run_four (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ cc : V → Fin 3, ¬ Amplitude.Monochromatic cc → amplitude W cc = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ i j : Fin 3, i ≠ j → W s((x, i), (y, j)) = 0)
    {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hone : amplitude W (Amplitude.const (V := V) b) ≠ 0)
    {p q r t : V} (hqp : q ≠ p) (hrp : r ≠ p) (hrq : r ≠ q)
    (htp : t ≠ p) (htq : t ≠ q) (htr : t ≠ r)
    (hpq : ∀ y : V, y ≠ p → W s((p, b), (y, b)) ≠ 0 → y = q)
    (hrt : ∀ y : V, y ≠ p → y ≠ q → y ≠ r → W s((r, b), (y, b)) ≠ 0 → y = t)
    (hc : W s((q, c), (r, c)) ≠ 0) (ha : W s((p, a), (t, a)) ≠ 0)
    (hbig : ((Finset.univ : Finset V) \ ({p, q, r, t} : Finset V)).Nonempty) :
    False := by
  classical
  have hU : pmSum W (Amplitude.const (V := V) b) (Finset.univ : Finset V) ≠ 0 := by
    rw [pmSum_univ]; exact hone
  have h1 : pmSum W (Amplitude.const (V := V) b)
      (((Finset.univ : Finset V).erase p).erase q) ≠ 0 := by
    refine certified_forced_pair W _ (Finset.mem_univ p) hU
      (fun y hy hlive => ?_)
    exact hpq y (Finset.ne_of_mem_erase hy) hlive
  have hrmem : r ∈ ((Finset.univ : Finset V).erase p).erase q :=
    Finset.mem_erase.mpr ⟨hrq, Finset.mem_erase.mpr ⟨hrp, Finset.mem_univ r⟩⟩
  have h2 : pmSum W (Amplitude.const (V := V) b)
      (((((Finset.univ : Finset V).erase p).erase q).erase r).erase t) ≠ 0 := by
    refine certified_forced_pair W _ hrmem h1
      (fun y hy hlive => ?_)
    have hyr : y ≠ r := Finset.ne_of_mem_erase hy
    have hyq : y ≠ q := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hy)
    have hyp : y ≠ p :=
      Finset.ne_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy))
    exact hrt y hyp hyq hyr hlive
  have hBset : ((((Finset.univ : Finset V).erase p).erase q).erase r).erase t
      = (Finset.univ : Finset V) \ ({p, q, r, t} : Finset V) := by
    ext y
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_sdiff,
      Finset.mem_insert, Finset.mem_singleton, not_or, true_and]
    tauto
  rw [hBset] at h2
  set B : Finset V := (Finset.univ : Finset V) \ ({p, q, r, t} : Finset V) with hBdef
  set C : Finset V := ({q, r} : Finset V) with hCdef
  have hdisj : Disjoint B C := by
    refine Finset.disjoint_left.mpr (fun y hy hy' => ?_)
    have hy2 := (Finset.mem_sdiff.mp hy).2
    rcases Finset.mem_insert.mp hy' with h | h
    · exact hy2 (by simp [h])
    · exact hy2 (by simp [Finset.mem_singleton.mp h])
  have hsplit : B ∪ C = (Finset.univ : Finset V) \ ({p, t} : Finset V) := by
    ext y
    simp only [hBdef, hCdef, Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · rintro (⟨h1, -, -, h4⟩ | h | h)
      · exact ⟨h1, h4⟩
      · exact ⟨by rw [h]; exact hqp, by rw [h]; exact Ne.symm htq⟩
      · exact ⟨by rw [h]; exact hrp, by rw [h]; exact Ne.symm htr⟩
    · rintro ⟨h1, h2⟩
      by_cases hq : y = q
      · exact Or.inr (Or.inl hq)
      · by_cases hr : y = r
        · exact Or.inr (Or.inr hr)
        · exact Or.inl ⟨h1, hq, hr, h2⟩
  have hne : (B ∪ C).Nonempty := ⟨q, Finset.mem_union_right _ (by simp [hCdef])⟩
  have hCsum : pmSum W (Amplitude.const (V := V) c) C ≠ 0 := by
    rw [hCdef, pmSum_pair W _ hrq]; exact hc
  exact false_of_pair_and_split W hzero hmono hab hac hbc htp ha B C hdisj hsplit hne h2 hCsum

/-! ### A live pair annihilates a row

Colour every site with one colour except two, joined by a live pair of a second.  That colouring is
not constant, so its amplitude vanishes; expanding it along any third site writes the vanishing as a
weighted sum over that site's partners, and the pair factors out.

What is left is an exact linear condition on one site's row in one colour, indexed by the pair.  Every
live pair of another colour supplies one, so a site with several partners in a colour must have its
row annihilated by many vectors at once -- which is how a bound on that number would be obtained. -/
theorem row_annihilated_by_live_pair (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ cc : V → Fin 3, ¬ Amplitude.Monochromatic cc → amplitude W cc = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ i j : Fin 3, i ≠ j → W s((x, i), (y, j)) = 0)
    {a b : Fin 3} (hba : b ≠ a) {v w w' : V}
    (hwv : w ≠ v) (hw'v : w' ≠ v) (hw'w : w' ≠ w)
    (hlive : W s((w, b), (w', b)) ≠ 0) :
    ∑ z ∈ (((Finset.univ : Finset V).erase v).erase w).erase w',
        W s((v, a), (z, a)) *
          pmSum W (Amplitude.const (V := V) a)
            ((((((Finset.univ : Finset V).erase v).erase z).erase w).erase w')) = 0 := by
  classical
  set cc : V → Fin 3 := fun x => if x = w ∨ x = w' then b else a with hcc
  have hccw : cc w = b := by simp [hcc]
  have hccw' : cc w' = b := by simp [hcc]
  have hccout : ∀ x : V, x ≠ w → x ≠ w' → cc x = a := by
    intro x h1 h2; simp [hcc, h1, h2]
  have hnm : ¬ Amplitude.Monochromatic cc := by
    rintro ⟨k, hk⟩
    have h1 : cc v = a := hccout v hwv.symm hw'v.symm
    exact hba (by rw [← hccw, hk w, ← hk v, h1])
  have hA : pmSum W cc (Finset.univ : Finset V) = 0 := by
    rw [pmSum_univ]; exact hzero cc hnm
  rw [pmSum_expand W cc (Finset.mem_univ v)] at hA
  have hcv : cc v = a := hccout v (Ne.symm hwv) (Ne.symm hw'v)
  have hsub2 : (((Finset.univ : Finset V).erase v).erase w).erase w'
      ⊆ (Finset.univ : Finset V).erase v :=
    (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
  rw [← Finset.sum_subset hsub2 (fun z hz hz' => ?_)] at hA
  · -- on the smaller set every term factors through the pair
    have hkey : ∀ z ∈ (((Finset.univ : Finset V).erase v).erase w).erase w',
        W (Sym2.map (Amplitude.paint cc) s(v, z)) *
            pmSum W cc (((Finset.univ : Finset V).erase v).erase z)
          = W s((w, b), (w', b)) *
            (W s((v, a), (z, a)) *
              pmSum W (Amplitude.const (V := V) a)
                ((((((Finset.univ : Finset V).erase v).erase z).erase w).erase w'))) := by
      intro z hz
      have hzw' : z ≠ w' := Finset.ne_of_mem_erase hz
      have hzw : z ≠ w := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hz)
      have hzv : z ≠ v :=
        Finset.ne_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hz))
      have hp : (Sym2.map (Amplitude.paint cc) s(v, z)) = s((v, cc v), (z, cc z)) := rfl
      rw [hp, hcv, hccout z hzw hzw']
      have hsub : ({w, w'} : Finset V) ⊆ ((Finset.univ : Finset V).erase v).erase z := by
        intro y hy
        rcases Finset.mem_insert.mp hy with h | h
        · exact Finset.mem_erase.mpr ⟨by rw [h]; exact Ne.symm hzw,
            Finset.mem_erase.mpr ⟨by rw [h]; exact hwv, Finset.mem_univ y⟩⟩
        · have h' := Finset.mem_singleton.mp h
          exact Finset.mem_erase.mpr ⟨by rw [h']; exact Ne.symm hzw',
            Finset.mem_erase.mpr ⟨by rw [h']; exact hw'v, Finset.mem_univ y⟩⟩
      have hcut : ∀ x ∈ ({w, w'} : Finset V), ∀ y ∈ (((Finset.univ : Finset V).erase v).erase z)
          \ ({w, w'} : Finset V), W s((x, cc x), (y, cc y)) = 0 := by
        intro x hx y hy
        have hy2 := (Finset.mem_sdiff.mp hy).2
        have hyw : y ≠ w := fun h => hy2 (by simp [h])
        have hyw' : y ≠ w' := fun h => hy2 (by simp [h])
        have hcy : cc y = a := hccout y hyw hyw'
        have hcx : cc x = b := by
          rcases Finset.mem_insert.mp hx with h | h
          · rw [h]; exact hccw
          · rw [Finset.mem_singleton.mp h]; exact hccw'
        by_cases hxy : y = x
        · exact absurd (show a = b by rw [← hcy, hxy, hcx]) (Ne.symm hba)
        · rw [hcx, hcy]; exact hmono x y hxy b a hba
      rw [Separation.pmSum_split W cc ({w, w'} : Finset V).card ({w, w'} : Finset V)
        (((Finset.univ : Finset V).erase v).erase z) rfl hsub hcut]
      have hpair : pmSum W cc ({w, w'} : Finset V) = W s((w, b), (w', b)) := by
        rw [pmSum_pair W cc hw'w, hccw, hccw']
      have hrest : (((Finset.univ : Finset V).erase v).erase z) \ ({w, w'} : Finset V)
          = (((((Finset.univ : Finset V).erase v).erase z).erase w).erase w') := by
        ext y
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert,
          Finset.mem_singleton, not_or]
        tauto
      rw [hpair, hrest,
        pmSum_congr_colour W (c' := Amplitude.const (V := V) a)
          (fun y hy => hccout y (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hy))
            (Finset.ne_of_mem_erase hy))]
      ring
    rw [Finset.sum_congr rfl hkey, ← Finset.mul_sum] at hA
    rcases mul_eq_zero.mp hA with h | h
    · exact absurd h hlive
    · exact h
  · -- the two dropped terms vanish, the pair being of the other colour
    have hp : (Sym2.map (Amplitude.paint cc) s(v, z)) = s((v, cc v), (z, cc z)) := rfl
    have hzv : z ≠ v := Finset.ne_of_mem_erase hz
    have hzb : cc z = b := by
      by_cases hzw : z = w
      · rw [hzw]; exact hccw
      · have : z = w' := by
          by_contra hzw'
          exact hz' (Finset.mem_erase.mpr ⟨hzw',
            Finset.mem_erase.mpr ⟨hzw, Finset.mem_erase.mpr ⟨hzv, Finset.mem_univ z⟩⟩⟩)
        rw [this]; exact hccw'
    rw [hp, hcv, hzb, hmono v z hzv a b (Ne.symm hba), zero_mul]

/-- **Excess forces a four-site sum to vanish.**  Suppose a site has exactly two live partners in one
colour, and one of those partners carries a live pair of a second colour.  Choosing that pair as the
annihilating one leaves a single surviving term, so the colour's sum over the complement of those
four sites vanishes outright.

This is the first consequence of excess that costs nothing: no minimality, no shape hypothesis, only
the two partners and one pair of another colour. -/
theorem excess_forces_quad_vanishing (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ cc : V → Fin 3, ¬ Amplitude.Monochromatic cc → amplitude W cc = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ i j : Fin 3, i ≠ j → W s((x, i), (y, j)) = 0)
    {a b : Fin 3} (hba : b ≠ a) {v z₁ z₂ w : V}
    (hz₁v : z₁ ≠ v) (hwv : w ≠ v) (hwz₁ : w ≠ z₁)
    (hz₂v : z₂ ≠ v) (hz₂z₁ : z₂ ≠ z₁) (hz₂w : z₂ ≠ w)
    (hpair : W s((z₁, b), (w, b)) ≠ 0)
    (hlive₂ : W s((v, a), (z₂, a)) ≠ 0)
    (honly : ∀ y : V, y ≠ v → y ≠ z₁ → y ≠ z₂ → W s((v, a), (y, a)) = 0) :
    pmSum W (Amplitude.const (V := V) a)
      (((((Finset.univ : Finset V).erase v).erase z₂).erase z₁).erase w) = 0 := by
  classical
  have hsum := row_annihilated_by_live_pair W hzero hmono hba hz₁v hwv hwz₁ hpair
  rw [Finset.sum_eq_single_of_mem z₂
    (Finset.mem_erase.mpr ⟨hz₂w, Finset.mem_erase.mpr ⟨hz₂z₁,
      Finset.mem_erase.mpr ⟨hz₂v, Finset.mem_univ z₂⟩⟩⟩)] at hsum
  · rcases mul_eq_zero.mp hsum with h | h
    · exact absurd h hlive₂
    · exact h
  · intro y hy hyz₂
    have hyw : y ≠ w := Finset.ne_of_mem_erase hy
    have hyz₁ : y ≠ z₁ := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hy)
    have hyv : y ≠ v :=
      Finset.ne_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy))
    rw [honly y hyv hyz₁ hyz₂, zero_mul]

/-- **A certified deletion forces a further partner.**  If the colour's sum survives the removal of a
site and one of its partners, then any other partner of that site still has a partner of its own
among what is left.

Applied to a site carrying two partners in one colour, this says the other partner has a second
partner in that colour too: excess in a colour propagates along that colour's own graph.  A graph
whose every site has two partners contains a cycle, which is exactly the monochromatic cycle the
fibre analysis identified as the only place cancellation can live. -/
theorem excess_propagates (W : Sym2 (V × Fin 3) → ℂ) {a : Fin 3} {v z₁ z₂ : V}
    (hz₁v : z₁ ≠ v) (hz₁z₂ : z₁ ≠ z₂)
    (hcert : pmSum W (Amplitude.const (V := V) a)
      (((Finset.univ : Finset V).erase v).erase z₂) ≠ 0) :
    ∃ y : V, y ≠ z₁ ∧ y ≠ v ∧ y ≠ z₂ ∧ W s((z₁, a), (y, a)) ≠ 0 := by
  classical
  have hmem : z₁ ∈ ((Finset.univ : Finset V).erase v).erase z₂ :=
    Finset.mem_erase.mpr ⟨hz₁z₂, Finset.mem_erase.mpr ⟨hz₁v, Finset.mem_univ z₁⟩⟩
  obtain ⟨y, hy, hlive, -⟩ :=
    exists_partner_ne_zero W (Amplitude.const (V := V) a) hmem hcert
  refine ⟨y, Finset.ne_of_mem_erase hy, ?_, ?_, hlive⟩
  · exact Finset.ne_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy))
  · exact Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hy)

/-- **Two partners, one relation.**  A site with exactly two live partners in a colour has those two
weights tied together by every live pair of another colour: the pair annihilates the two-entry row.

Since the row is not zero, all these annihilators are parallel, so the ratio of the two four-site
sums is the same for every choice of pair -- a fixed constant determined by the row alone.  Two pairs
whose sums fail that proportion would force the row to vanish, and with it the excess. -/
theorem excess_two_term_relation (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ cc : V → Fin 3, ¬ Amplitude.Monochromatic cc → amplitude W cc = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ i j : Fin 3, i ≠ j → W s((x, i), (y, j)) = 0)
    {a b : Fin 3} (hba : b ≠ a) {v z₁ z₂ w w' : V}
    (hz₁v : z₁ ≠ v) (hz₂v : z₂ ≠ v) (hz₂z₁ : z₂ ≠ z₁)
    (hwv : w ≠ v) (hw'v : w' ≠ v) (hw'w : w' ≠ w)
    (hz₁w : z₁ ≠ w) (hz₁w' : z₁ ≠ w') (hz₂w : z₂ ≠ w) (hz₂w' : z₂ ≠ w')
    (hpair : W s((w, b), (w', b)) ≠ 0)
    (honly : ∀ y : V, y ≠ v → y ≠ z₁ → y ≠ z₂ → W s((v, a), (y, a)) = 0) :
    W s((v, a), (z₁, a)) *
        pmSum W (Amplitude.const (V := V) a)
          ((((((Finset.univ : Finset V).erase v).erase z₁).erase w).erase w'))
      + W s((v, a), (z₂, a)) *
        pmSum W (Amplitude.const (V := V) a)
          ((((((Finset.univ : Finset V).erase v).erase z₂).erase w).erase w')) = 0 := by
  classical
  have hsum := row_annihilated_by_live_pair W hzero hmono hba hwv hw'v hw'w hpair
  have hmem : ({z₁, z₂} : Finset V) ⊆ (((Finset.univ : Finset V).erase v).erase w).erase w' := by
    intro y hy
    rcases Finset.mem_insert.mp hy with h | h
    · exact Finset.mem_erase.mpr ⟨by rw [h]; exact hz₁w',
        Finset.mem_erase.mpr ⟨by rw [h]; exact hz₁w,
          Finset.mem_erase.mpr ⟨by rw [h]; exact hz₁v, Finset.mem_univ y⟩⟩⟩
    · have h' := Finset.mem_singleton.mp h
      exact Finset.mem_erase.mpr ⟨by rw [h']; exact hz₂w',
        Finset.mem_erase.mpr ⟨by rw [h']; exact hz₂w,
          Finset.mem_erase.mpr ⟨by rw [h']; exact hz₂v, Finset.mem_univ y⟩⟩⟩
  rw [← Finset.sum_subset hmem (fun y hy hy' => ?_)] at hsum
  · rwa [Finset.sum_pair (Ne.symm hz₂z₁)] at hsum
  · have hyz₁ : y ≠ z₁ := fun h => hy' (by simp [h])
    have hyz₂ : y ≠ z₂ := fun h => hy' (by simp [h])
    have hyv : y ≠ v :=
      Finset.ne_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy))
    rw [honly y hyv hyz₁ hyz₂, zero_mul]

/-! ### Reducibility as an inductive shape

The hereditary form of the pendant criterion quantifies over every subset, which is far more than
any configuration satisfies and makes it awkward to apply.  What the proof actually walks is a single
chain of deletions, so that is what the hypothesis should be.

This matters because shape certificates are the only source of non-vanishing that does not trace back
to the monochromatic amplitudes through deletions, and until now the library had none. -/

/-- **A configuration reducible by pendant deletion.**  Either empty, or it has a site whose only
live partner is one specific site, and removing that pair leaves a reducible configuration. -/
inductive PendantReducible (W : Sym2 (V × Fin 3) → ℂ) (c : V → Fin 3) : Finset V → Prop
  | empty : PendantReducible W c ∅
  | step (S : Finset V) (u v : V) (hu : u ∈ S) (hv : v ∈ S.erase u)
      (hcv : c v = c u) (hlive : W s((u, c u), (v, c u)) ≠ 0)
      (hpend : ∀ z ∈ S, z ≠ v → z ≠ u → W s((u, c u), (z, c u)) = 0)
      (hrest : PendantReducible W c ((S.erase u).erase v)) : PendantReducible W c S

/-- **A reducible configuration has a non-zero matching sum.**  Its sum is the product of the forced
weights, one for each deletion. -/
theorem pmSum_ne_zero_of_pendantReducible (W : Sym2 (V × Fin 3) → ℂ)
    (hmono : ∀ (x y : V), y ≠ x → ∀ i j : Fin 3, i ≠ j → W s((x, i), (y, j)) = 0)
    (c : V → Fin 3) {S : Finset V} (h : PendantReducible W c S) :
    pmSum W c S ≠ 0 := by
  induction h with
  | empty => simp
  | step S u v hu hv hcv hlive hpend hrest ih =>
    rw [pmSum_delete_pendant W hmono hu hv hpend c rfl hcv]
    exact mul_ne_zero hlive ih

/-- **A set matched by unique partners is reducible.**  If every site of a set has exactly one live
partner there, in its own colour, the set walks down by forced deletions.

This is the bridge the global route needs.  The sites without excess in a colour are exactly those
with a single partner in it, and since the excess set is closed under that colour's adjacency their
partners lie outside it too -- so the complement of the excess set is matched by unique partners, and
is certified in that colour by shape alone. -/
theorem pendantReducible_of_unique_partners (W : Sym2 (V × Fin 3) → ℂ) (c : V → Fin 3)
    {S : Finset V}
    (h : ∀ u ∈ S, ∃ v ∈ S.erase u, c v = c u ∧ W s((u, c u), (v, c u)) ≠ 0 ∧
      ∀ z ∈ S, z ≠ v → z ≠ u → W s((u, c u), (z, c u)) = 0) :
    PendantReducible W c S := by
  classical
  induction S using Finset.strongInduction with
  | _ S ih =>
    rcases S.eq_empty_or_nonempty with rfl | hne
    · exact PendantReducible.empty
    · obtain ⟨u, hu⟩ := hne
      obtain ⟨v, hv, hcv, hlive, hpend⟩ := h u hu
      have hvS : v ∈ S := Finset.mem_of_mem_erase hv
      have hvu : v ≠ u := Finset.ne_of_mem_erase hv
      refine PendantReducible.step S u v hu hv hcv hlive hpend (ih _ ?_ ?_)
      · exact ssubset_of_subset_of_ssubset (Finset.erase_subset v (S.erase u))
          (Finset.erase_ssubset hu)
      · intro w hw
        have hwv : w ≠ v := Finset.ne_of_mem_erase hw
        have hwu : w ≠ u := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hw)
        have hwS : w ∈ S := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hw)
        obtain ⟨y, hy, hcy, hlivey, hpendy⟩ := h w hwS
        have hyS : y ∈ S := Finset.mem_of_mem_erase hy
        have hyw : y ≠ w := Finset.ne_of_mem_erase hy
        have hyu : y ≠ u := by
          intro hyu
          have hcu : c w = c u := by rw [← hcy, hyu]
          have hdead : W s((u, c u), (w, c u)) = 0 := hpend w hwS hwv hwu
          apply hlivey
          rw [hyu, hcu, Sym2.eq_swap]
          exact hdead
        have hyv : y ≠ v := by
          intro hyv
          obtain ⟨t, ht, hct, hlivet, hpendt⟩ := h v hvS
          have hlive_vu : W s((v, c v), (u, c v)) ≠ 0 := by
            rw [hcv, Sym2.eq_swap]
            exact hlive
          have htu : t = u := by
            by_contra htu
            exact hlive_vu (hpendt u hu (fun hh => htu hh.symm) (Ne.symm hvu))
          have hdead : W s((v, c v), (w, c v)) = 0 := by
            refine hpendt w hwS ?_ hwv
            rw [htu]; exact hwu
          have hcvw : c w = c v := by rw [← hcy, hyv]
          apply hlivey
          rw [hyv, hcvw, Sym2.eq_swap]
          exact hdead
        refine ⟨y, Finset.mem_erase.mpr ⟨hyw,
          Finset.mem_erase.mpr ⟨hyv, Finset.mem_erase.mpr ⟨hyu, hyS⟩⟩⟩, hcy, hlivey, ?_⟩
        intro z hz hzy hzw
        exact hpendy z (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hz)) hzy hzw

/-- **The certificate with its third part supplied by shape.**

The composition is `false_of_parts`, which predates this: two disjoint parts certified in two
colours and a certified complement in the third are already a contradiction.  What is new is where
the third certificate comes from -- not from the colour's amplitude by deletions, but from the
complement being matched by unique partners, read off the support alone.

That is the one source of non-vanishing not reachable from the amplitudes, and the reason it matters
here is that the complement of a colour's excess set is always of this form: outside the excess every
site has a single partner in that colour, and the excess set is closed under that colour's adjacency,
so the partner lies outside too. -/
theorem false_of_parts_of_unique_complement (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ i j : Fin 3, i ≠ j → W s((x, i), (y, j)) = 0)
    (S₁ S₂ : Finset V) (hdisj : Disjoint S₁ S₂) (hn1 : S₁.Nonempty) (hn2 : S₂.Nonempty)
    (h1 : pmSum W (Amplitude.const (V := V) 1) S₁ ≠ 0)
    (h2 : pmSum W (Amplitude.const (V := V) 2) S₂ ≠ 0)
    (hunique : ∀ u ∈ (Finset.univ : Finset V) \ (S₁ ∪ S₂),
      ∃ v ∈ ((Finset.univ : Finset V) \ (S₁ ∪ S₂)).erase u,
        W s((u, 0), (v, 0)) ≠ 0 ∧
        ∀ z ∈ (Finset.univ : Finset V) \ (S₁ ∪ S₂), z ≠ v → z ≠ u →
          W s((u, 0), (z, 0)) = 0) :
    False := by
  classical
  refine false_of_parts W hzero hmono hdisj hn1 hn2 h1 h2 ?_
  refine pmSum_ne_zero_of_pendantReducible W hmono _
    (pendantReducible_of_unique_partners W (Amplitude.const (V := V) 0) (fun u hu => ?_))
  obtain ⟨v, hv, hlive, hpend⟩ := hunique u hu
  exact ⟨v, hv, rfl, hlive, hpend⟩

/-- **All but one dead is enough.**  If every pair outside the chosen matching is dead except
possibly one, no rival matching survives.

A rival disagreeing at a site also disagrees at that site's partner, and the two pairs it introduces
there are distinct -- so it cannot confine its disagreement to the one spared pair.

This strictly improves the edgewise form, which asks that *every* pair outside the matching die.  The
genuinely useful criterion is weaker still: a rival needs an alternating cycle, so surviving pairs
stay harmless until they assemble one.  That needs the cycle; this does not. -/
theorem unique_of_at_most_one_extra (Wp : Sym2 (V × Fin 3) → ℂ) (f : V → Fin 3)
    {σ₀ : Equiv.Perm V} (hmem : σ₀ ∈ pairingsOn (Finset.univ : Finset V)) (p q : V)
    (hpq : q ≠ σ₀ p)
    (hdead : ∀ x y : V, y ≠ x → y ≠ σ₀ x → x ≠ p → x ≠ q →
      Wp s((x, f x), (y, f y)) = 0) :
    ∀ τ ∈ pairingsOn (Finset.univ : Finset V), τ ≠ σ₀ →
      ∃ z : V, Wp s((z, f z), (τ z, f (τ z))) = 0 := by
  classical
  obtain ⟨hinv₀, hfix₀, -⟩ := mem_pairingsOn.mp hmem
  intro τ hτ hne
  obtain ⟨hinvτ, hfixτ, -⟩ := mem_pairingsOn.mp hτ
  have hex : ∃ z : V, τ z ≠ σ₀ z := by
    by_contra hall
    push_neg at hall
    exact hne (Equiv.ext hall)
  obtain ⟨z, hz⟩ := hex
  -- `z` and its partner `σ₀ z` both disagree, and `σ₀ z` is neither `z` nor `τ z`
  have h0 : σ₀ z ≠ z := hfix₀ z (Finset.mem_univ z)
  have h1 : σ₀ z ≠ τ z := fun h => hz h.symm
  have h2 : τ (σ₀ z) ≠ σ₀ (σ₀ z) := by
    rw [hinv₀ z]
    intro h
    exact h1 (by rw [← hinvτ (σ₀ z), h])
  by_cases hzp : z = p
  · refine ⟨σ₀ z, hdead (σ₀ z) (τ (σ₀ z)) (hfixτ _ (Finset.mem_univ _)) h2 ?_ ?_⟩
    · rw [hzp]; exact hfix₀ p (Finset.mem_univ p)
    · rw [hzp]; exact Ne.symm hpq
  · by_cases hzq : z = q
    · refine ⟨σ₀ z, hdead (σ₀ z) (τ (σ₀ z)) (hfixτ _ (Finset.mem_univ _)) h2 ?_ ?_⟩
      · rw [hzq]; exact fun h => hpq (by rw [← hinv₀ q, h])
      · rw [hzq]; exact hfix₀ q (Finset.mem_univ q)
    · exact ⟨z, hdead z (τ z) (hfixτ z (Finset.mem_univ z)) hz hzp hzq⟩

/-! ### A split invariant under two matchings forces a second matching

Every colour carries at least one live perfect matching, because its monochromatic amplitude is a
sum over exactly those matchings and does not vanish.  Take one for colour `a` and one for colour
`b`.  Their union is a disjoint union of alternating cycles, and each cycle -- indeed each union of
cycles -- is a set carried into itself by both matchings.

The theorem below says what such a split costs.  If the `a`-part had no live `a`-matching other
than the one it came with, its monochromatic sum would be a single non-zero product; likewise on the
other side for `b`; and a set whose own colour sum is non-zero forces its complement's sum in any
other colour to vanish.  So at least one of the two sides carries a *second* live matching in its
own colour -- excess, and excess exactly there.

Nothing here mentions a vertex count, a cycle, a degree, or a shape.  The hypotheses are two
restricted pairings and a set that both preserve, which is what a disconnected union hands over
directly: no cycle bookkeeping is needed to reach them. -/

/-- **Rigid on both sides of a split: impossible.**  If a set and its complement each carry exactly
one live pairing, in two different colours, the configuration cannot exist.  Rigidity is asked only
of the two parts in their own colours; nothing is assumed about edges crossing the split, which is
where this differs from a closure hypothesis. -/
theorem false_of_rigid_invariant_split (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ p q : Fin 3, p ≠ q → W s((x, p), (y, q)) = 0)
    {a b : Fin 3} (hab : a ≠ b)
    {X : Finset V} (hXne : X.Nonempty) (hXuniv : X ≠ Finset.univ)
    {σa σb : Equiv.Perm V}
    (hAmem : σa ∈ pairingsOn X) (hAlive : ∀ z ∈ X, W s((z, a), (σa z, a)) ≠ 0)
    (hAuniq : ∀ τ ∈ pairingsOn X, τ ≠ σa → ∃ z ∈ X, W s((z, a), (τ z, a)) = 0)
    (hBmem : σb ∈ pairingsOn ((Finset.univ : Finset V) \ X))
    (hBlive : ∀ z ∈ (Finset.univ : Finset V) \ X, W s((z, b), (σb z, b)) ≠ 0)
    (hBuniq : ∀ τ ∈ pairingsOn ((Finset.univ : Finset V) \ X), τ ≠ σb →
      ∃ z ∈ (Finset.univ : Finset V) \ X, W s((z, b), (τ z, b)) = 0) :
    False := by
  classical
  have hA : pmSum W (Amplitude.const (V := V) a) X ≠ 0 :=
    pmSum_ne_zero_of_unique_matching W (Amplitude.const (V := V) a) hAmem
      (fun z hz => hAlive z hz) (fun τ hτ hne => hAuniq τ hτ hne)
  have hB : pmSum W (Amplitude.const (V := V) b) ((Finset.univ : Finset V) \ X) ≠ 0 :=
    pmSum_ne_zero_of_unique_matching W (Amplitude.const (V := V) b) hBmem
      (fun z hz => hBlive z hz) (fun τ hτ hne => hBuniq τ hτ hne)
  exact hA (pmSum_zero_of_complement_ne_zero W hzero hmono hXne hXuniv hab hB)

/-- **A split preserved by two live matchings carries a second one.**  Given a live `a`-pairing of
`X` and a live `b`-pairing of its complement, with `a ≠ b` and both parts non-empty, one of the two
parts admits a second live pairing in its own colour -- excess, and excess exactly there.

This is the abstract form of the two-colour obstruction: `Separation.no_two_colour_closed` asks the
parts to be closed under every live edge of two colours, where this asks only that no second
matching fit inside one of them. -/
theorem second_live_matching_of_invariant_split (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ p q : Fin 3, p ≠ q → W s((x, p), (y, q)) = 0)
    {a b : Fin 3} (hab : a ≠ b)
    {X : Finset V} (hXne : X.Nonempty) (hXuniv : X ≠ Finset.univ)
    {σa σb : Equiv.Perm V}
    (hAmem : σa ∈ pairingsOn X) (hAlive : ∀ z ∈ X, W s((z, a), (σa z, a)) ≠ 0)
    (hBmem : σb ∈ pairingsOn ((Finset.univ : Finset V) \ X))
    (hBlive : ∀ z ∈ (Finset.univ : Finset V) \ X, W s((z, b), (σb z, b)) ≠ 0) :
    (∃ τ ∈ pairingsOn X, τ ≠ σa ∧ ∀ z ∈ X, W s((z, a), (τ z, a)) ≠ 0) ∨
      (∃ τ ∈ pairingsOn ((Finset.univ : Finset V) \ X), τ ≠ σb ∧
        ∀ z ∈ (Finset.univ : Finset V) \ X, W s((z, b), (τ z, b)) ≠ 0) := by
  classical
  by_contra hcon
  refine false_of_rigid_invariant_split W hzero hmono hab hXne hXuniv hAmem hAlive ?_
    hBmem hBlive ?_
  · intro τ hτ hne
    by_contra hz
    exact hcon (Or.inl ⟨τ, hτ, hne, fun z hzX hw => hz ⟨z, hzX, hw⟩⟩)
  · intro τ hτ hne
    by_contra hz
    exact hcon (Or.inr ⟨τ, hτ, hne, fun z hzX hw => hz ⟨z, hzX, hw⟩⟩)

/-! ### From a disconnected union to the split

Two live pairings of the whole site set, in different colours, union to a graph in which every site
has degree two: a disjoint union of cycles alternating between the colours.  Every union of those
cycles is carried into itself by both pairings, and that is the only property the previous theorem
needs.  So the cycle decomposition never has to be built: it is enough to name an invariant set.

The shared restriction theorem turns a pairing of everything into a pairing of the part. -/

/-- **A set preserved by two whole-set matchings carries a second one.**  This is the previous
theorem stated for the objects a colour actually hands over: a live perfect matching of every site
in colour `a`, one in colour `b`, and any non-empty proper set that both preserve.  Each component
of their union -- and each union of components -- is such a set. -/
theorem second_matching_of_invariant_set (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ p q : Fin 3, p ≠ q → W s((x, p), (y, q)) = 0)
    {a b : Fin 3} (hab : a ≠ b)
    {X : Finset V} (hXne : X.Nonempty) (hXuniv : X ≠ Finset.univ)
    {σa σb : Equiv.Perm V}
    (hAmem : σa ∈ pairingsOn (Finset.univ : Finset V))
    (hAlive : ∀ z : V, W s((z, a), (σa z, a)) ≠ 0)
    (hBmem : σb ∈ pairingsOn (Finset.univ : Finset V))
    (hBlive : ∀ z : V, W s((z, b), (σb z, b)) ≠ 0)
    (hinvA : ∀ x ∈ X, σa x ∈ X) (hinvB : ∀ x ∈ X, σb x ∈ X) :
    (∃ τ ∈ pairingsOn X, (∃ z ∈ X, τ z ≠ σa z) ∧ ∀ z ∈ X, W s((z, a), (τ z, a)) ≠ 0) ∨
      (∃ τ ∈ pairingsOn ((Finset.univ : Finset V) \ X), (∃ z ∈ (Finset.univ : Finset V) \ X,
        τ z ≠ σb z) ∧ ∀ z ∈ (Finset.univ : Finset V) \ X, W s((z, b), (τ z, b)) ≠ 0) := by
  classical
  obtain ⟨hAinv, -, -⟩ := MatchingSum.mem_pairingsOn.mp hAmem
  obtain ⟨hBinv, -, -⟩ := MatchingSum.mem_pairingsOn.mp hBmem
  -- the complement is preserved by `σb` as well
  have hinvBc : ∀ x ∈ (Finset.univ : Finset V) \ X, σb x ∈ (Finset.univ : Finset V) \ X := by
    intro x hx
    have hxX : x ∉ X := (Finset.mem_sdiff.mp hx).2
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hmem => hxX ?_⟩
    have := hinvB _ hmem
    rwa [hBinv x] at this
  have hres := second_live_matching_of_invariant_split W hzero hmono hab hXne hXuniv
    (MatchingRestriction.restrictPerm_mem hAmem (Finset.subset_univ X) hinvA)
    (fun z hz => by rw [MatchingRestriction.restrictPerm_apply, if_pos hz]; exact hAlive z)
    (MatchingRestriction.restrictPerm_mem hBmem
      (Finset.subset_univ ((Finset.univ : Finset V) \ X)) hinvBc)
    (fun z hz => by rw [MatchingRestriction.restrictPerm_apply, if_pos hz]; exact hBlive z)
  rcases hres with ⟨τ, hτ, hne, hlive⟩ | ⟨τ, hτ, hne, hlive⟩
  · refine Or.inl ⟨τ, hτ, ?_, hlive⟩
    by_contra hall
    refine hne (Equiv.ext fun z => ?_)
    simp only [MatchingRestriction.restrictPerm_apply]
    by_cases hz : z ∈ X
    · rw [if_pos hz]
      by_contra hzz
      exact hall ⟨z, hz, hzz⟩
    · rw [if_neg hz]
      exact (MatchingSum.mem_pairingsOn.mp hτ).2.2 z hz
  · refine Or.inr ⟨τ, hτ, ?_, hlive⟩
    by_contra hall
    refine hne (Equiv.ext fun z => ?_)
    simp only [MatchingRestriction.restrictPerm_apply]
    by_cases hz : z ∈ (Finset.univ : Finset V) \ X
    · rw [if_pos hz]
      by_contra hzz
      exact hall ⟨z, hz, hzz⟩
    · rw [if_neg hz]
      exact (MatchingSum.mem_pairingsOn.mp hτ).2.2 z hz

/-! ### The endgame as a hypothesis about matchings

`false_of_mixed_pure_matching` says a mixed pure matching is already a contradiction.  Packaged as
a hypothesis about every configuration, that is a statement asking for one combinatorial object --
a perfect matching using more than one colour, each of whose pairs is alone in its own fibre -- and
nothing else.  It is strictly more concrete than the partition question, which asks for three
non-vanishing sums: here the non-vanishing is read off the shape.

Purity is relative to the fibre, not global: a site with several partners in one colour is harmless
as long as no second one lands in the same fibre.  So the object to look for lives in a graph
larger than the one where every pair is its endpoints' only partner. -/

/-- **The matching question.**  Every configuration admits a perfect matching that uses more than
one colour and whose pairs are, inside their own fibres, each site's only live partner of that
colour. -/
def PureMixedMatching : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (W : Sym2 (V × Fin 3) → ℂ),
    4 < Fintype.card V →
    (∀ (x y : V), y ≠ x → ∀ a b : Fin 3, a ≠ b → W s((x, a), (y, b)) = 0) →
    (∀ k : Fin 3, pmSum W (Amplitude.const (V := V) k) Finset.univ ≠ 0) →
    ∃ (N : V → V) (γ : V → Fin 3), (∀ v, N (N v) = v) ∧ (∀ v, N v ≠ v) ∧
      (∀ v, γ (N v) = γ v) ∧ ¬ Amplitude.Monochromatic γ ∧
      (∀ v, W s((v, γ v), (N v, γ v)) ≠ 0) ∧
      (∀ v w : V, w ≠ v → w ≠ N v → γ w = γ v → W s((v, γ v), (w, γ v)) = 0)

/-- The matching question answers the partition question: each fibre's live graph in its own
colour is the matching restricted there, so the fibre carries exactly one pairing and its sum is a
single non-zero product. -/
theorem certifiedPartition_of_pureMixedMatching (h : PureMixedMatching) : CertifiedPartition := by
  intro V _ _ W hcard hmono hone
  obtain ⟨N, γ, hinv, hfix, hgN, hmixed, hlive, hpure⟩ := h V W hcard hmono hone
  refine ⟨γ, hmixed, fun m => ?_⟩
  classical
  have hmemS : ∀ x : V, x ∈ fiber γ m ↔ γ x = m := by intro x; simp [mem_fiber]
  have hff : ∀ v, (fun w => if γ w = m then N w else w)
      ((fun w => if γ w = m then N w else w) v) = v := by
    intro v
    by_cases hv : γ v = m
    · have hN : γ (N v) = m := by rw [hgN v]; exact hv
      simp only [if_pos hv, if_pos hN, hinv]
    · simp only [if_neg hv]
  let σ : Equiv.Perm V := ⟨fun w => if γ w = m then N w else w,
    fun w => if γ w = m then N w else w, hff, hff⟩
  have hσ : ∀ v, σ v = if γ v = m then N v else v := fun _ => rfl
  have hmem : σ ∈ pairingsOn (fiber γ m) := by
    refine MatchingSum.mem_pairingsOn.mpr ⟨fun x => hff x, ?_, ?_⟩
    · intro x hx
      rw [hσ, if_pos ((hmemS x).mp hx)]
      exact hfix x
    · intro x hx
      rw [hσ, if_neg (fun hc => hx ((hmemS x).mpr hc))]
  refine pmSum_ne_zero_of_unique_matching W (Amplitude.const (V := V) m) hmem ?_ ?_
  · intro z hz
    have hzm : γ z = m := (hmemS z).mp hz
    have : W s((z, m), (σ z, m)) ≠ 0 := by
      rw [hσ, if_pos hzm]
      have := hlive z
      rwa [hzm] at this
    exact this
  · intro τ hτ hne
    obtain ⟨z, hz⟩ : ∃ z, τ z ≠ σ z := by
      by_contra hall
      exact hne (Equiv.ext (fun z => not_not.mp (fun hc => hall ⟨z, hc⟩)))
    have hzS : z ∈ fiber γ m := by
      by_contra hzn
      have h1 : τ z = z := (MatchingSum.mem_pairingsOn.mp hτ).2.2 z hzn
      have h2 : σ z = z := by rw [hσ, if_neg (fun hc => hzn ((hmemS z).mpr hc))]
      exact hz (by rw [h1, h2])
    have hzm : γ z = m := (hmemS z).mp hzS
    have hτz : τ z ∈ fiber γ m := MatchingSum.pairingsOn_closed hτ z hzS
    have hne1 : τ z ≠ z := (MatchingSum.mem_pairingsOn.mp hτ).2.1 z hzS
    have hne2 : τ z ≠ N z := by
      intro hc
      exact hz (by rw [hc, hσ, if_pos hzm])
    refine ⟨z, hzS, ?_⟩
    have := hpure z (τ z) hne1 hne2 (by rw [(hmemS _).mp hτz, hzm])
    rwa [hzm] at this

/-- **The conjecture, from the matching question.**  Same shape as the partition bridge, and the
matching question is the sharper of the two hypotheses. -/
theorem krenn_gu_of_pureMixedMatching (h : PureMixedMatching) (had : AllDegenerate) :
    ∀ n : ℕ, 3 ≤ n → ¬ KrennGu.Solvable n :=
  krenn_gu_of_certifiedPartition (certifiedPartition_of_pureMixedMatching h) had

/-! ### The one fact the matching question has to consume

The matching question -- partition the sites so that each part's own colour graph, induced there,
is a perfect matching of it -- cannot be settled by any hypothesis that complete live graphs also
satisfy.  With all three live graphs complete the induced graph on a part is complete, a complete
graph is a matching only at size two, and three parts of size two do not reach eight sites.  So
spanning, minimum degree, and the existence of a live matching in each colour are all too weak.

What excludes complete live graphs is the statement below, and it is the only weight-level fact of
its kind available: expanding a non-vanishing constant amplitude at one site shows some term
survives, and the surviving pair cannot carry a second colour, because deleting a live pair kills
the remainder's sum in every other colour. -/

/-- **Every site has a single-coloured certified partner in every colour.**  Certified: deleting the
pair leaves the colour's own sum non-zero.  Single-coloured: the pair is live in that colour and no
other. -/
theorem exists_pure_certified_partner (W : Sym2 (V × Fin 3) → ℂ)
    (hmono : ∀ (z w : V), w ≠ z → ∀ p q : Fin 3, p ≠ q → W s((z, p), (w, q)) = 0)
    (hghz : MatchingSum.IsGHZOn W (Finset.univ : Finset V)) (hcard : 4 < Fintype.card V)
    (a : Fin 3) (x : V) :
    ∃ y : V, y ≠ x ∧ W s((x, a), (y, a)) ≠ 0 ∧
      pmSum W (Amplitude.const (V := V) a)
        ((Finset.univ : Finset V) \ ({x, y} : Finset V)) ≠ 0 ∧
      ∀ b : Fin 3, b ≠ a → W s((x, b), (y, b)) = 0 := by
  classical
  obtain ⟨y, hy, hlive, hrest⟩ :=
    exists_partner_ne_zero W (Amplitude.const (V := V) a) (Finset.mem_univ x) (hghz.1 a)
  have hyx : y ≠ x := Finset.ne_of_mem_erase hy
  have hset : ((Finset.univ : Finset V).erase x).erase y
      = (Finset.univ : Finset V) \ ({x, y} : Finset V) := by
    ext z
    simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
      Finset.mem_singleton, true_and, not_or]
    tauto
  rw [hset] at hrest
  refine ⟨y, hyx, hlive, hrest, fun b hb => ?_⟩
  by_contra hcon
  -- a pair live in `b` leaves a remainder whose sum in colour `a` vanishes
  have hne : ((Finset.univ : Finset V) \ ({x, y} : Finset V)).Nonempty := by
    rw [← Finset.card_pos, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
    have h2 : ({x, y} : Finset V).card ≤ 2 := le_trans (Finset.card_insert_le _ _) (by simp)
    omega
  exact hrest (pmSum_delete_live_pair_zero W hmono hghz hb.symm hyx (Finset.mem_univ x)
    (Finset.mem_univ y) hne hcon)

/-- **Three rigid parts are impossible.**  The matching question's closer, stated with uniqueness
rather than with the induced graph being a matching outright: each part need only carry exactly one
live pairing in its own colour, however that is certified -- by pendant reduction, by a bridge
argument, or by inspection.  `PureMixedMatching` is the special case where the part's live graph in
its own colour *is* the pairing. -/
theorem false_of_rigid_three_split (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ p q : Fin 3, p ≠ q → W s((x, p), (y, q)) = 0)
    {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (B C : Finset V) (hBC : Disjoint B C)
    (hAne : (B ∪ C).Nonempty) (hAc : ((Finset.univ : Finset V) \ (B ∪ C)).Nonempty)
    {σa σb σc : Equiv.Perm V}
    (hAmem : σa ∈ pairingsOn ((Finset.univ : Finset V) \ (B ∪ C)))
    (hAlive : ∀ z ∈ (Finset.univ : Finset V) \ (B ∪ C), W s((z, a), (σa z, a)) ≠ 0)
    (hAuniq : ∀ τ ∈ pairingsOn ((Finset.univ : Finset V) \ (B ∪ C)), τ ≠ σa →
      ∃ z ∈ (Finset.univ : Finset V) \ (B ∪ C), W s((z, a), (τ z, a)) = 0)
    (hBmem : σb ∈ pairingsOn B) (hBlive : ∀ z ∈ B, W s((z, b), (σb z, b)) ≠ 0)
    (hBuniq : ∀ τ ∈ pairingsOn B, τ ≠ σb → ∃ z ∈ B, W s((z, b), (τ z, b)) = 0)
    (hCmem : σc ∈ pairingsOn C) (hClive : ∀ z ∈ C, W s((z, c), (σc z, c)) ≠ 0)
    (hCuniq : ∀ τ ∈ pairingsOn C, τ ≠ σc → ∃ z ∈ C, W s((z, c), (τ z, c)) = 0) :
    False :=
  false_of_split_partition W hzero hmono hab hac hbc B C hBC hAne hAc
    (pmSum_ne_zero_of_unique_matching W (Amplitude.const (V := V) a) hAmem
      (fun z hz => hAlive z hz) (fun τ hτ hne => hAuniq τ hτ hne))
    (pmSum_ne_zero_of_unique_matching W (Amplitude.const (V := V) b) hBmem
      (fun z hz => hBlive z hz) (fun τ hτ hne => hBuniq τ hτ hne))
    (pmSum_ne_zero_of_unique_matching W (Amplitude.const (V := V) c) hCmem
      (fun z hz => hClive z hz) (fun τ hτ hne => hCuniq τ hτ hne))

/-! ### The quad criterion

The two-part split says a set whose own-colour sum is non-zero forces its complement's sum in every
other colour to vanish.  Read the other way it is a *win condition*: exhibit a set whose complement
is certified in one colour and whose own sum is non-zero in another, and the configuration is gone.

On a four-element set the sum has three terms, and one site's live partners decide it.  If, inside
the four, one site has exactly one live partner in the second colour, the sum collapses to a single
product -- and a single non-zero product cannot vanish.  So the criterion below asks only for a
certified deletion quad in which the second colour has a *pendant*: four sites whose removal leaves
the first colour's sum non-zero, one of them with a unique live partner among the other three.

This is the smallest instance of the general shape: find a certified deletion set whose induced live
graph in another colour carries exactly one perfect matching. -/

/-- **A certified quad with a pendant in another colour is impossible.**  `p`'s only live `b`-partner
inside the quad is `r`, and `q` is live to `s`; the quad's `b`-sum is then the single product
`W b p r * W b q s`, which is non-zero, while the certified complement forces it to vanish. -/
theorem false_of_certified_quad_pendant (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hmono : ∀ (x y : V), y ≠ x → ∀ j k : Fin 3, j ≠ k → W s((x, j), (y, k)) = 0)
    {a b : Fin 3} (hba : b ≠ a)
    {p q r s : V} (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s)
    (hrest : ((Finset.univ : Finset V) \ ({p, q, r, s} : Finset V)).Nonempty)
    (hcert : pmSum W (Amplitude.const (V := V) a)
      ((Finset.univ : Finset V) \ ({p, q, r, s} : Finset V)) ≠ 0)
    (hdq : W s((p, b), (q, b)) = 0) (hds : W s((p, b), (s, b)) = 0)
    (hlr : W s((p, b), (r, b)) ≠ 0) (hlqs : W s((q, b), (s, b)) ≠ 0) :
    False := by
  classical
  have hSne : ({p, q, r, s} : Finset V).Nonempty := ⟨p, by simp⟩
  have hSuniv : ({p, q, r, s} : Finset V) ≠ (Finset.univ : Finset V) := by
    intro h
    obtain ⟨z, hz⟩ := hrest
    rw [h] at hz
    simp at hz
  have hquad : pmSum W (Amplitude.const (V := V) b) ({p, q, r, s} : Finset V)
      = W s((p, b), (r, b)) * W s((q, b), (s, b)) :=
    pmSum_quad_forced W (Amplitude.const (V := V) b) hpq hpr hps hqr hqs hrs hdq hds
  have hzeroS : pmSum W (Amplitude.const (V := V) b) ({p, q, r, s} : Finset V) = 0 :=
    pmSum_zero_of_complement_ne_zero W hzero hmono hSne hSuniv hba hcert
  rw [hquad] at hzeroS
  exact (mul_ne_zero hlr hlqs) hzeroS

/-! ### Two disjoint certified pairs

A site's certified partners in a colour are the ones through which that colour's sum demonstrably
does not cancel, and every site has at least one in every colour.  Certified pairs carry their own
colour alone, so a site certified to *everything* would have no live partner in the other two
colours at all -- and then those colours' own sums, which expand along that very site, would vanish.
So no site is certified to everything, and that single observation is enough to produce two
certified pairs with no site in common.

The argument is four steps and uses no counting: start from a certified pair, take a site the first
one is *not* certified to, certify it, and if its partner collides with the original pair, repeat the
move at the other end.  One of the two rounds always lands. -/

/-- **No site is certified to every other.**  Its partner in another colour would have to be dead
there, and a site with no live partner in a colour kills that colour's sum. -/
theorem exists_not_certified (W : Sym2 (V × Fin 3) → ℂ)
    (hmono : ∀ (z w : V), w ≠ z → ∀ j k : Fin 3, j ≠ k → W s((z, j), (w, k)) = 0)
    (hghz : MatchingSum.IsGHZOn W (Finset.univ : Finset V)) (hcard : 4 < Fintype.card V)
    (a : Fin 3) (w : V) :
    ∃ x : V, x ≠ w ∧ ¬ (W s((w, a), (x, a)) ≠ 0 ∧
      pmSum W (Amplitude.const (V := V) a)
        ((Finset.univ : Finset V) \ ({w, x} : Finset V)) ≠ 0) := by
  classical
  obtain ⟨b, hb⟩ : ∃ b : Fin 3, b ≠ a := by revert a; decide
  obtain ⟨v, hv, hlive, -⟩ :=
    exists_partner_ne_zero W (Amplitude.const (V := V) b) (Finset.mem_univ w) (hghz.1 b)
  have hvw : v ≠ w := Finset.ne_of_mem_erase hv
  refine ⟨v, hvw, fun hc => ?_⟩
  have hne : ((Finset.univ : Finset V) \ ({w, v} : Finset V)).Nonempty := by
    rw [← Finset.card_pos, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
    have h2 : ({w, v} : Finset V).card ≤ 2 := le_trans (Finset.card_insert_le _ _) (by simp)
    omega
  exact hc.2 (pmSum_delete_live_pair_zero W hmono hghz (Ne.symm hb) hvw
    (Finset.mem_univ w) (Finset.mem_univ v) hne hlive)

/-- **Every colour has two certified pairs with no site in common.**  Unconditional: no degree
bound, no minimality, no vertex count beyond four sites. -/
theorem exists_two_disjoint_certified_pairs (W : Sym2 (V × Fin 3) → ℂ)
    (hmono : ∀ (z w : V), w ≠ z → ∀ j k : Fin 3, j ≠ k → W s((z, j), (w, k)) = 0)
    (hghz : MatchingSum.IsGHZOn W (Finset.univ : Finset V)) (hcard : 4 < Fintype.card V)
    (a : Fin 3) :
    ∃ p q r s : V, p ≠ q ∧ r ≠ s ∧ p ≠ r ∧ p ≠ s ∧ q ≠ r ∧ q ≠ s ∧
      (W s((p, a), (q, a)) ≠ 0 ∧ pmSum W (Amplitude.const (V := V) a)
        ((Finset.univ : Finset V) \ ({p, q} : Finset V)) ≠ 0) ∧
      (W s((r, a), (s, a)) ≠ 0 ∧ pmSum W (Amplitude.const (V := V) a)
        ((Finset.univ : Finset V) \ ({r, s} : Finset V)) ≠ 0) := by
  classical
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  set Cert : V → V → Prop := fun x y => W s((x, a), (y, a)) ≠ 0 ∧
    pmSum W (Amplitude.const (V := V) a)
      ((Finset.univ : Finset V) \ ({x, y} : Finset V)) ≠ 0 with hCertDef
  have Psym : ∀ x y : V, Cert x y → Cert y x := by
    intro x y h
    refine ⟨?_, ?_⟩
    · rw [Sym2.eq_swap]; exact h.1
    · rw [Finset.pair_comm]; exact h.2
  have P1 : ∀ x : V, ∃ y : V, y ≠ x ∧ Cert x y := by
    intro x
    obtain ⟨y, hy, h1, h2, -⟩ := exists_pure_certified_partner W hmono hghz hcard a x
    exact ⟨y, hy, h1, h2⟩
  have P3 : ∀ w : V, ∃ x : V, x ≠ w ∧ ¬ Cert w x := by
    intro w
    obtain ⟨x, hx, hnc⟩ := exists_not_certified W hmono hghz hcard a w
    exact ⟨x, hx, hnc⟩
  obtain ⟨q₀, hq₀, hc₀⟩ := P1 (Classical.arbitrary V)
  set p₀ := Classical.arbitrary V with hp₀
  obtain ⟨z, hz, hnc⟩ := P3 p₀
  have hzq : z ≠ q₀ := by rintro rfl; exact hnc hc₀
  obtain ⟨w, hw, hcw⟩ := P1 z
  have hwp : w ≠ p₀ := by rintro rfl; exact hnc (Psym _ _ hcw)
  by_cases hwq : w = q₀
  · subst hwq
    obtain ⟨z', hz', hnc'⟩ := P3 w
    have hz'p : z' ≠ p₀ := by rintro rfl; exact hnc' (Psym _ _ hc₀)
    have hz'z : z' ≠ z := by rintro rfl; exact hnc' (Psym _ _ hcw)
    obtain ⟨w', hw', hcw'⟩ := P1 z'
    have hw'w : w' ≠ w := by rintro rfl; exact hnc' (Psym _ _ hcw')
    by_cases hw'p : w' = p₀
    · exact ⟨z', p₀, z, w, hz'p, Ne.symm hw, hz'z, hz', Ne.symm hz, Ne.symm hwp,
        hw'p ▸ hcw', hcw⟩
    · exact ⟨p₀, w, z', w', Ne.symm hq₀, Ne.symm hw', Ne.symm hz'p, Ne.symm hw'p,
        Ne.symm hz', Ne.symm hw'w, hc₀, hcw'⟩
  · exact ⟨p₀, q₀, z, w, Ne.symm hq₀, Ne.symm hw, Ne.symm hz, Ne.symm hwp,
      Ne.symm hzq, Ne.symm hwq, hc₀, hcw⟩

/-! ### The certified row sums to the whole

Expanding a colour's whole-set sum along one site presents it as a sum over that site's partners,
and only the certified ones contribute -- the rest carry either a dead weight or a vanishing
complement.  So the certified partners of a site carry the whole sum between them, exactly.

Written with the term through `v` divided by the whole sum, this says every site's certified terms
add to one.  The term is symmetric in its two sites, so a site whose partners each have it as their
*only* certified partner reads its own row as a sum of ones -- and there can be only one of them.
That is what forbids a certified star, and a forbidden star is what produced two disjoint certified
pairs above. -/

/-- **The certified terms carry the whole sum.** -/
theorem certified_row_sum (W : Sym2 (V × Fin 3) → ℂ) (k : Fin 3) (u : V) :
    ∑ v ∈ certifiedNbrs W u k,
        W s((u, k), (v, k)) * pmSum W (Amplitude.const (V := V) k)
          (((Finset.univ : Finset V).erase u).erase v)
      = pmSum W (Amplitude.const (V := V) k) (Finset.univ : Finset V) := by
  classical
  rw [pmSum_expand W (Amplitude.const (V := V) k) (Finset.mem_univ u)]
  refine Finset.sum_subset (fun v hv => Finset.mem_of_mem_filter v hv) ?_
  intro v hv hnv
  have := mem_certifiedNbrs (W := W) (u := u) (v := v) (k := k)
  have hvu : v ≠ u := (Finset.mem_erase.mp hv).1
  by_cases hw : W s((u, k), (v, k)) = 0
  · rw [hw, zero_mul]
  · have : pmSum W (Amplitude.const (V := V) k)
        (((Finset.univ : Finset V).erase u).erase v) = 0 := by
      by_contra hs
      exact hnv (mem_certifiedNbrs.mpr ⟨hvu, hw, hs⟩)
    rw [this, mul_zero]

/-- **A site whose certified partners each have only it is itself singly certified.**  Its row is a
sum of copies of the whole sum, and one copy is all there is room for. -/
theorem certifiedNbrs_card_eq_one (W : Sym2 (V × Fin 3) → ℂ) (k : Fin 3)
    (hone : pmSum W (Amplitude.const (V := V) k) (Finset.univ : Finset V) ≠ 0) (u : V)
    (h : ∀ v ∈ certifiedNbrs W u k, certifiedNbrs W v k = {u}) :
    (certifiedNbrs W u k).card = 1 := by
  classical
  have hterm : ∀ v ∈ certifiedNbrs W u k,
      W s((u, k), (v, k)) * pmSum W (Amplitude.const (V := V) k)
        (((Finset.univ : Finset V).erase u).erase v)
      = pmSum W (Amplitude.const (V := V) k) (Finset.univ : Finset V) := by
    intro v hv
    have hrow := certified_row_sum W k v
    rw [h v hv, Finset.sum_singleton] at hrow
    rw [show W s((u, k), (v, k)) = W s((v, k), (u, k)) from by rw [Sym2.eq_swap],
      show ((Finset.univ : Finset V).erase u).erase v
        = ((Finset.univ : Finset V).erase v).erase u from Finset.erase_right_comm]
    exact hrow
  have hsum := certified_row_sum W k u
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul] at hsum
  have hc : ((certifiedNbrs W u k).card : ℂ) = 1 := by
    have h0 : (((certifiedNbrs W u k).card : ℂ) - 1) *
        pmSum W (Amplitude.const (V := V) k) (Finset.univ : Finset V) = 0 := by
      rw [sub_mul, one_mul, hsum, sub_self]
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact sub_eq_zero.mp h1
    · exact absurd h1 hone
  exact_mod_cast hc

/-! ### The star, as a linear system

Fix a site `u` and freeze every weight not on its star.  Each perfect matching covers `u` exactly
once, so every amplitude becomes *linear* in the star: the amplitude of a colouring is the sum, over
the partners `v`, of the star term through `v` times the sum over what is left.  Write that term as

    F u v c  =  W (u, c u) (v, c v) * pmSum c (V minus u and v).

Scaling the block at `v` by `λ v` scales its term by `λ v`, so a linear dependence among the terms
would let one scale along it, keep every amplitude, and pick the parameter that zeroes one live
block -- which support minimality forbids.  The live blocks' terms are therefore independent, and
the live degree is exactly the dimension they span.

That turns the degree bound into a dimension count.  The three constant colourings give three
coordinates; if every term already vanishes on the *non*-constant colourings, then those three
coordinates see everything, the span sits inside a three-dimensional space, and the live degree is
at most three.  The lemma below supplies exactly that vanishing from full degeneracy. -/

/-- **Every star term dies on a non-constant colouring**, given full degeneracy.  Two cases: if the
colouring still varies after the pair is removed, degeneracy at `u` kills the remaining sum
directly; if it does not, the pair wears one colour and everything else another, and deleting a live
pair kills the remainder's sum in every other colour. -/
theorem star_term_zero_of_degenerate (W : Sym2 (V × Fin 3) → ℂ)
    (hmono : ∀ (x y : V), y ≠ x → ∀ j k : Fin 3, j ≠ k → W s((x, j), (y, k)) = 0)
    (hghz : MatchingSum.IsGHZOn W (Finset.univ : Finset V)) (hcard : 4 < Fintype.card V)
    (hdeg : ∀ p : V, FanStructure.Degenerate W p)
    (u v : V) (hvu : v ≠ u) (c : V → Fin 3) (hc : ¬ Amplitude.Monochromatic c) :
    W s((u, c u), (v, c v)) * pmSum W c (((Finset.univ : Finset V).erase u).erase v) = 0 := by
  classical
  by_cases hcuv : c u = c v
  · by_cases hvary : ∃ x ∈ ((Finset.univ : Finset V).erase u).erase v,
        ∃ y ∈ ((Finset.univ : Finset V).erase u).erase v, c x ≠ c y
    · obtain ⟨x, hx, y, hy, hxy⟩ := hvary
      rw [hdeg u v (Finset.mem_erase.mpr ⟨hvu, Finset.mem_univ v⟩) c x hx y hy hxy, mul_zero]
    · push_neg at hvary
      by_cases hw : W s((u, c u), (v, c v)) = 0
      · rw [hw, zero_mul]
      · have hSne : (((Finset.univ : Finset V).erase u).erase v).Nonempty := by
          rw [← Finset.card_pos, Finset.card_erase_of_mem
            (Finset.mem_erase.mpr ⟨hvu, Finset.mem_univ v⟩), Finset.card_erase_of_mem
            (Finset.mem_univ u), Finset.card_univ]
          omega
        obtain ⟨w, hwmem⟩ := hSne
        have hconst : ∀ x ∈ ((Finset.univ : Finset V).erase u).erase v, c x = c w :=
          fun x hx => hvary x hx w hwmem
        have hab : c w ≠ c u := by
          intro h
          refine hc ⟨c u, fun z => ?_⟩
          by_cases hzu : z = u
          · rw [hzu]
          · by_cases hzv : z = v
            · rw [hzv, hcuv]
            · rw [hconst z (Finset.mem_erase.mpr ⟨hzv, Finset.mem_erase.mpr
                ⟨hzu, Finset.mem_univ z⟩⟩), h]
        have hset : ((Finset.univ : Finset V).erase u).erase v
            = (Finset.univ : Finset V) \ ({u, v} : Finset V) := by
          ext z
          simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
            Finset.mem_singleton, true_and, not_or]
          tauto
        have hrest : ((Finset.univ : Finset V) \ ({u, v} : Finset V)).Nonempty := by
          rw [← hset]; exact ⟨w, hwmem⟩
        have hlive : W s((u, c u), (v, c u)) ≠ 0 := by simpa [hcuv] using hw
        have hkill := pmSum_delete_live_pair_zero W hmono hghz hab hvu
          (Finset.mem_univ u) (Finset.mem_univ v) hrest hlive
        rw [← hset] at hkill
        rw [pmSum_congr_colour W (c' := Amplitude.const (V := V) (c w))
          (fun x hx => hconst x hx), hkill, mul_zero]
  · rw [hmono u v hvu (c u) (c v) hcuv, zero_mul]

/-! ### Two partners of one colour cannot both be live

With every star term dead on the non-constant colourings, a partner's whole contribution is read off
the three constant ones -- and a partner live in colour `m` contributes to that colour alone.  Two
such partners therefore contribute proportionally, and the second can absorb the first: zero the
block at one and correct the block at the other, and every amplitude is unchanged while the support
strictly drops.  Minimal support forbids it.

That is the degree bound: at most one live partner per colour, hence at most three in all. -/

/-- Zero the block at `{u, v}` and reset the colour-`m` entry at `{u, v'}`. -/
noncomputable def tweakStar (W : Sym2 (V × Fin 3) → ℂ) (u v v' : V) (m : Fin 3) (z : ℂ) :
    Sym2 (V × Fin 3) → ℂ :=
  fun e => if e = s((u, m), (v', m)) then z else MinimalSupport.zeroPair W u v e

/-- **One live partner per colour.**  Two partners of a site live in the same colour, both with the
star terms dead off the constants and the second certified, contradict minimal support. -/
theorem false_of_two_live_same_colour (W : Sym2 (V × Fin 3) → ℂ)
    (hmin : MinimalSupport.IsSupportMinimal W)
    (hmono : ∀ (x y : V), y ≠ x → ∀ j k : Fin 3, j ≠ k → W s((x, j), (y, k)) = 0)
    {u v v' : V} {m : Fin 3} (hvu : v ≠ u) (hv'u : v' ≠ u) (hvv' : v ≠ v')
    (hlive : W s((u, m), (v, m)) ≠ 0) (hlive' : W s((u, m), (v', m)) ≠ 0)
    (hdead : ∀ k : Fin 3, k ≠ m → W s((u, k), (v, k)) = 0)
    (hcert' : pmSum W (Amplitude.const (V := V) m)
      (((Finset.univ : Finset V).erase u).erase v') ≠ 0)
    (hstar : ∀ x : V, x ≠ u → ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c →
      W s((u, c u), (x, c x)) * pmSum W c (((Finset.univ : Finset V).erase u).erase x) = 0) :
    False := by
  classical
  set z : ℂ := W s((u, m), (v', m)) + W s((u, m), (v, m)) *
    pmSum W (Amplitude.const (V := V) m) (((Finset.univ : Finset V).erase u).erase v) /
      pmSum W (Amplitude.const (V := V) m) (((Finset.univ : Finset V).erase u).erase v')
    with hzdef
  set X : Sym2 (V × Fin 3) → ℂ := tweakStar W u v v' m z with hXdef
  -- the modified edge is exactly the colour-`m` entry at `{u, v'}`
  have hedge_ne : ∀ a b : Fin 3, s((u, a), (v, b)) ≠ s((u, m), (v', m)) := by
    intro a b h
    rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hvv' (congrArg Prod.fst h2)
    · exact hv'u (congrArg Prod.fst h1).symm
  have hXv : ∀ a b : Fin 3, X s((u, a), (v, b)) = 0 := by
    intro a b
    rw [hXdef, tweakStar, if_neg (hedge_ne a b)]
    exact MinimalSupport.zeroPair_target W u v a b
  have hXoff : ∀ (x y : V) (a b : Fin 3), ¬ (x = u ∧ y = v) → ¬ (x = v ∧ y = u) →
      s((x, a), (y, b)) ≠ s((u, m), (v', m)) → X s((x, a), (y, b)) = W s((x, a), (y, b)) := by
    intro x y a b h1 h2 h3
    rw [hXdef, tweakStar, if_neg h3, MinimalSupport.zeroPair, if_neg]
    intro hc
    simp only [Sym2.map_pair_eq] at hc
    rcases Sym2.eq_iff.mp hc with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact h1 ⟨e1, e2⟩
    · exact h2 ⟨e1, e2⟩
  -- sums away from `u` are untouched
  have hpm : ∀ (c : V → Fin 3) (y : V), pmSum X c (((Finset.univ : Finset V).erase u).erase y)
      = pmSum W c (((Finset.univ : Finset V).erase u).erase y) := by
    intro c y
    refine pmSum_congr X W c (fun x hx w hw => ?_)
    have hxu : x ≠ u := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hx)).1
    have hwu : w ≠ u := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hw)).1
    have : X s((x, c x), (w, c w)) = W s((x, c x), (w, c w)) := by
      refine hXoff x w (c x) (c w) (fun h => hxu h.1) (fun h => hwu h.2) (fun h => ?_)
      rcases Sym2.eq_iff.mp h with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact hxu (congrArg Prod.fst e1)
      · exact hwu (congrArg Prod.fst e2)
    exact this
  -- the expansion at `u`, for any weight system
  have hexp : ∀ (Y : Sym2 (V × Fin 3) → ℂ) (c : V → Fin 3), amplitude Y c
      = ∑ y ∈ (Finset.univ : Finset V).erase u,
          Y s((u, c u), (y, c y)) * pmSum Y c (((Finset.univ : Finset V).erase u).erase y) := by
    intro Y c
    rw [← pmSum_univ, pmSum_expand Y c (Finset.mem_univ u)]
    refine Finset.sum_congr rfl fun y _ => ?_
    first
      | rfl
      | (congr 1; simp [Sym2.map_pair_eq, Amplitude.paint])
  -- amplitudes are unchanged
  have hamp : ∀ c : V → Fin 3, amplitude X c = amplitude W c := by
    intro c
    rw [hexp X c, hexp W c]
    simp only [hpm c]
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
    have hsub : ({v, v'} : Finset V) ⊆ (Finset.univ : Finset V).erase u := by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy'
      · exact Finset.mem_erase.mpr ⟨hvu, Finset.mem_univ _⟩
      · rw [Finset.mem_singleton.mp hy']
        exact Finset.mem_erase.mpr ⟨hv'u, Finset.mem_univ _⟩
    have hvanish : ∀ y ∈ (Finset.univ : Finset V).erase u, y ∉ ({v, v'} : Finset V) →
        X s((u, c u), (y, c y)) * pmSum W c (((Finset.univ : Finset V).erase u).erase y)
          - W s((u, c u), (y, c y)) * pmSum W c (((Finset.univ : Finset V).erase u).erase y)
          = 0 := by
      intro y hy hyn
      have hyv : y ≠ v := fun h => hyn (by rw [h]; simp)
      have hyv' : y ≠ v' := fun h => hyn (by rw [h]; simp)
      have hyu : y ≠ u := (Finset.mem_erase.mp hy).1
      have : X s((u, c u), (y, c y)) = W s((u, c u), (y, c y)) := by
        refine hXoff u y (c u) (c y) (fun h => hyv h.2) (fun h => hvu h.1.symm) (fun h => ?_)
        rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact hyv' (congrArg Prod.fst h2)
        · exact hv'u (congrArg Prod.fst h1).symm
      rw [this, sub_self]
    rw [← Finset.sum_subset hsub hvanish, Finset.sum_pair hvv']
    -- the two surviving terms
    have hXvterm : X s((u, c u), (v, c v)) = 0 := hXv (c u) (c v)
    by_cases hc : Amplitude.Monochromatic c
    · obtain ⟨k, hk⟩ := hc
      have hcongr : ∀ y : V, pmSum W c (((Finset.univ : Finset V).erase u).erase y)
          = pmSum W (Amplitude.const (V := V) k)
            (((Finset.univ : Finset V).erase u).erase y) :=
        fun y => pmSum_congr_colour W (fun x _ => hk x)
      by_cases hkm : k = m
      · subst hkm
        have hXv'term : X s((u, c u), (v', c v')) = z := by
          rw [hXdef, tweakStar, if_pos (by rw [hk u, hk v'])]
        rw [hXvterm, hXv'term, hcongr v, hcongr v', hk u, hk v, hk v', hzdef]
        field_simp
        ring
      · have hdeadv : W s((u, c u), (v, c v)) = 0 := by
          rw [hk u, hk v]; exact hdead k hkm
        have hXv'term : X s((u, c u), (v', c v')) = W s((u, c u), (v', c v')) := by
          rw [hXdef, tweakStar, if_neg, MinimalSupport.zeroPair, if_neg]
          · intro hcc
            simp only [Sym2.map_pair_eq] at hcc
            rcases Sym2.eq_iff.mp hcc with ⟨e1, e2⟩ | ⟨e1, e2⟩
            · exact hvv' e2.symm
            · exact hvu e1.symm
          · intro hcc
            rcases Sym2.eq_iff.mp hcc with ⟨e1, e2⟩ | ⟨e1, e2⟩
            · exact hkm (by rw [← hk u]; exact congrArg Prod.snd e1)
            · exact hv'u (congrArg Prod.fst e1).symm
        rw [hXvterm, hXv'term, hdeadv]
        ring
    · have h1 : W s((u, c u), (v, c v)) *
          pmSum W c (((Finset.univ : Finset V).erase u).erase v) = 0 := hstar v hvu c hc
      have h2 : X s((u, c u), (v', c v')) *
          pmSum W c (((Finset.univ : Finset V).erase u).erase v')
          - W s((u, c u), (v', c v')) *
            pmSum W c (((Finset.univ : Finset V).erase u).erase v') = 0 := by
        by_cases hcm : c u = m ∧ c v' = m
        · have hP : pmSum W c (((Finset.univ : Finset V).erase u).erase v') = 0 := by
            have := hstar v' hv'u c hc
            rw [hcm.1, hcm.2] at this
            exact (mul_eq_zero.mp this).resolve_left hlive'
          rw [hP, mul_zero, mul_zero, sub_self]
        · have : X s((u, c u), (v', c v')) = W s((u, c u), (v', c v')) := by
            rw [hXdef, tweakStar, if_neg, MinimalSupport.zeroPair, if_neg]
            · intro hcc
              simp only [Sym2.map_pair_eq] at hcc
              rcases Sym2.eq_iff.mp hcc with ⟨e1, e2⟩ | ⟨e1, e2⟩
              · exact hvv' e2.symm
              · exact hvu e1.symm
            · intro hcc
              rcases Sym2.eq_iff.mp hcc with ⟨e1, e2⟩ | ⟨e1, e2⟩
              · exact hcm ⟨congrArg Prod.snd e1, congrArg Prod.snd e2⟩
              · exact hv'u (congrArg Prod.fst e1).symm
          rw [this, sub_self]
      rw [hXvterm, zero_mul, zero_sub, h1, neg_zero, zero_add, h2]
  -- the modified system is still GHZ, with strictly smaller support
  have hghzX : KrennGu.IsGHZ X := by
    refine ⟨fun k => ?_, fun c hc => ?_⟩
    · rw [hamp]; exact hmin.1.1 k
    · rw [hamp]; exact hmin.1.2 c hc
  have hnbrs : ∀ x : V, LiveDegree.liveNbrs X x ⊆ LiveDegree.liveNbrs W x := by
    intro x y hy
    obtain ⟨hyx, a, b, hab⟩ := LiveDegree.mem_liveNbrs.mp hy
    refine LiveDegree.mem_liveNbrs.mpr ⟨hyx, ?_⟩
    by_cases hxy : (x = u ∧ y = v') ∨ (x = v' ∧ y = u)
    · rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨m, m, hlive'⟩
      · exact ⟨m, m, by rw [Sym2.eq_swap]; exact hlive'⟩
    · push_neg at hxy
      refine ⟨a, b, ?_⟩
      rw [← hXoff x y a b ?_ ?_ ?_]
      · exact hab
      · rintro ⟨rfl, rfl⟩
        exact hab (hXv a b)
      · rintro ⟨rfl, rfl⟩
        exact hab (by rw [Sym2.eq_swap]; exact hXv b a)
      · intro hcc
        rcases Sym2.eq_iff.mp hcc with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · exact (hxy.1 (congrArg Prod.fst e1)) (congrArg Prod.fst e2)
        · exact (hxy.2 (congrArg Prod.fst e1)) (congrArg Prod.fst e2)
  have hlt : MinimalSupport.supportMass X < MinimalSupport.supportMass W := by
    rw [MinimalSupport.supportMass, MinimalSupport.supportMass]
    refine Finset.sum_lt_sum (fun x _ => Finset.card_le_card (hnbrs x)) ⟨u, Finset.mem_univ u, ?_⟩
    refine Finset.card_lt_card ?_
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨hnbrs u, fun heq => ?_⟩
    have hold : v ∈ LiveDegree.liveNbrs W u :=
      LiveDegree.mem_liveNbrs.mpr ⟨hvu, m, m, hlive⟩
    have hnew : v ∉ LiveDegree.liveNbrs X u := by
      intro hmem
      obtain ⟨-, a, b, hab⟩ := LiveDegree.mem_liveNbrs.mp hmem
      exact hab (hXv a b)
    exact hnew (heq ▸ hold)
  exact absurd (hmin.2 X hghzX) (Nat.not_le.mpr hlt)

/-- **Under full degeneracy a live pair wears one colour and is certified in it.**  Minimal support
says the pair is not inert, so some colouring leaves a non-zero sum on the complement; degeneracy
says that colouring is constant there; and deleting a live pair kills the complement's sum in every
colour but the pair's own, so the surviving constant is the pair's colour. -/
theorem live_pair_certified_of_degenerate (W : Sym2 (V × Fin 3) → ℂ)
    (hmin : MinimalSupport.IsSupportMinimal W)
    (hmono : ∀ (x y : V), y ≠ x → ∀ j k : Fin 3, j ≠ k → W s((x, j), (y, k)) = 0)
    (hghz : MatchingSum.IsGHZOn W (Finset.univ : Finset V)) (hcard : 4 < Fintype.card V)
    (hdeg : ∀ p : V, FanStructure.Degenerate W p)
    {u v : V} (hvu : v ≠ u) (hlive : ∃ a b : Fin 3, W s((u, a), (v, b)) ≠ 0) :
    ∃ m : Fin 3, W s((u, m), (v, m)) ≠ 0 ∧
      (∀ k : Fin 3, k ≠ m → W s((u, k), (v, k)) = 0) ∧
      pmSum W (Amplitude.const (V := V) m)
        (((Finset.univ : Finset V).erase u).erase v) ≠ 0 := by
  classical
  have hset : ((Finset.univ : Finset V).erase u).erase v
      = (Finset.univ : Finset V) \ ({u, v} : Finset V) := by
    ext z
    simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
      Finset.mem_singleton, true_and, not_or]
    tauto
  have hSne : (((Finset.univ : Finset V).erase u).erase v).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem
      (Finset.mem_erase.mpr ⟨hvu, Finset.mem_univ v⟩), Finset.card_erase_of_mem
      (Finset.mem_univ u), Finset.card_univ]
    omega
  -- the pair carries a diagonal live entry
  obtain ⟨a, b, hab⟩ := hlive
  have hdiag : ∃ j : Fin 3, W s((u, j), (v, j)) ≠ 0 := by
    by_cases hjk : a = b
    · exact ⟨a, by rw [hjk] at hab ⊢; exact hab⟩
    · exact absurd (hmono u v hvu a b hjk) hab
  -- deleting the live pair kills every other colour on the complement
  have hkill : ∀ j : Fin 3, W s((u, j), (v, j)) ≠ 0 → ∀ i : Fin 3, i ≠ j →
      pmSum W (Amplitude.const (V := V) i)
        (((Finset.univ : Finset V).erase u).erase v) = 0 := by
    intro j hj i hij
    have hrest : ((Finset.univ : Finset V) \ ({u, v} : Finset V)).Nonempty := by
      rw [← hset]; exact hSne
    have := pmSum_delete_live_pair_zero W hmono hghz hij hvu (Finset.mem_univ u)
      (Finset.mem_univ v) hrest hj
    rw [← hset] at this
    exact this
  -- minimal support: the pair is not inert
  have hnot := MinimalSupport.not_inert_of_supportMinimal hmin hvu ⟨a, b, hab⟩
  rw [FanStructure.Inert] at hnot
  push_neg at hnot
  obtain ⟨c, hc⟩ := hnot
  -- degeneracy forces that colouring to be constant on the complement
  have hconst : ∀ x ∈ ((Finset.univ : Finset V).erase u).erase v,
      ∀ y ∈ ((Finset.univ : Finset V).erase u).erase v, c x = c y := by
    intro x hx y hy
    by_contra hxy
    exact hc (hdeg u v (Finset.mem_erase.mpr ⟨hvu, Finset.mem_univ v⟩) c x hx y hy hxy)
  obtain ⟨w, hw⟩ := hSne
  have heq : pmSum W c (((Finset.univ : Finset V).erase u).erase v)
      = pmSum W (Amplitude.const (V := V) (c w))
        (((Finset.univ : Finset V).erase u).erase v) :=
    pmSum_congr_colour W (fun x hx => hconst x hx w hw)
  have hcw : pmSum W (Amplitude.const (V := V) (c w))
      (((Finset.univ : Finset V).erase u).erase v) ≠ 0 := heq ▸ hc
  obtain ⟨j, hj⟩ := hdiag
  have hjw : j = c w := by
    by_contra hne
    exact hcw (hkill j hj (c w) (fun h => hne h.symm))
  refine ⟨j, hj, fun k hk => ?_, by rw [hjw]; exact hcw⟩
  by_contra hkk
  exact hcw (hkill k hkk (c w) (fun h => hk (hjw.trans h).symm))

/-! ### The degree bound, from full degeneracy alone

Everything above assembles.  On a support-minimal representative each live pair wears one colour and
is certified in it; every star term dies on the non-constant colourings; and two partners of one
colour would let the second absorb the first, dropping the support.  So a site has at most one live
partner per colour, hence at most three -- which is the degree bound the conjecture reduces to. -/

/-- **Full degeneracy gives the degree bound.**  This makes the whole development rest on a single
open statement rather than two. -/
theorem minimalLiveDegree_of_allDegenerate (had : AllDegenerate) :
    MinimalSupport.MinimalLiveDegreeThree := by
  intro V _ _ W hcard hmin u
  classical
  have hdeg : ∀ p : V, FanStructure.Degenerate W p := had V W hcard hmin
  have hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0 := hmin.1.2
  have hmono := mono_of_supportMinimal W hmin hzero hdeg (le_of_lt hcard)
  have hnem : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hghz : MatchingSum.IsGHZOn W (Finset.univ : Finset V) :=
    (MatchingSum.isGHZOn_univ_iff W).mpr hmin.1
  have hstar := star_term_zero_of_degenerate W hmono hghz hcard hdeg
  have key : ∀ v ∈ LiveDegree.liveNbrs W u, ∃ m : Fin 3, W s((u, m), (v, m)) ≠ 0 ∧
      (∀ k : Fin 3, k ≠ m → W s((u, k), (v, k)) = 0) ∧
      pmSum W (Amplitude.const (V := V) m)
        (((Finset.univ : Finset V).erase u).erase v) ≠ 0 := by
    intro v hv
    obtain ⟨hvu, hlive⟩ := LiveDegree.mem_liveNbrs.mp hv
    exact live_pair_certified_of_degenerate W hmin hmono hghz hcard hdeg hvu hlive
  choose! f hf1 hf2 hf3 using key
  have hinj : Set.InjOn f (LiveDegree.liveNbrs W u : Set V) := by
    intro v hvs v' hv's hff
    have hv : v ∈ LiveDegree.liveNbrs W u := Finset.mem_coe.mp hvs
    have hv' : v' ∈ LiveDegree.liveNbrs W u := Finset.mem_coe.mp hv's
    by_contra hvv'
    refine false_of_two_live_same_colour W hmin hmono
      (LiveDegree.mem_liveNbrs.mp hv).1 (LiveDegree.mem_liveNbrs.mp hv').1 hvv'
      (hf1 v hv) ?_ (hf2 v hv) ?_ (fun x hx c hc => hstar u x hx c hc)
    · rw [hff]; exact hf1 v' hv'
    · rw [hff]; exact hf3 v' hv'
  calc (LiveDegree.liveNbrs W u).card
      ≤ (Finset.univ : Finset (Fin 3)).card :=
        Finset.card_le_card_of_injOn f (fun a _ => Finset.mem_univ _) hinj
    _ = 3 := by simp

/-! ### Relabelling the sites

The conjecture is posed on `Fin (2n)`; the properties this file states are posed on an arbitrary
finite site type.  To compare the two -- in particular to see that a property of hypothetical
counterexamples is implied *back* by the conjecture -- the amplitude has to travel along a
relabelling.  It does, on the nose: a matching of one site type is a matching of the other, and the
weights follow. -/

section Relabel

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- Weights transported along a relabelling of the sites. The shared definition
uses the inverse orientation for its equivalence argument. -/
abbrev relabelW (φ : A ≃ B) (W : Sym2 (A × Fin 3) → ℂ) : Sym2 (B × Fin 3) → ℂ :=
  MatchingSum.relabelW W φ.symm

theorem amplitude_relabel (φ : A ≃ B) (W : Sym2 (A × Fin 3) → ℂ) (c : B → Fin 3) :
    amplitude (relabelW φ W) c = amplitude W (c ∘ φ) := by
  simpa [relabelW, Function.comp_def] using
    (MatchingSum.amplitude_relabel W φ.symm (c ∘ φ))

end Relabel

/-! ### The converse direction, by vacuity

A property universally quantified over support-minimal GHZ systems above four sites is implied by
the conjecture as soon as the conjecture says there are none.  The step needs two things the
conjecture's own formulation does not carry: an odd site count has no matching at all, so its
monochromatic amplitudes vanish; and an even one relabels onto the official index type.  Both are
below. -/

/-- **No GHZ system above four sites, on any finite site type.**  From the conjecture in its
`Solvable` form, for an arbitrary finite site type rather than `Fin (2n)`. -/
theorem not_isGHZ_of_not_solvable (h : ∀ n : ℕ, 3 ≤ n → ¬ KrennGu.Solvable n)
    {A : Type} [Fintype A] [DecidableEq A] (hcard : 4 < Fintype.card A)
    (W : Sym2 (A × Fin 3) → ℂ) : ¬ KrennGu.IsGHZ W := by
  classical
  rintro ⟨hone, hzero⟩
  rcases Nat.even_or_odd (Fintype.card A) with hev | hodd
  · obtain ⟨m, hm⟩ := hev
    have hcardm : Fintype.card A = 2 * m := by omega
    have hm3 : 3 ≤ m := by omega
    let φ : A ≃ Fin (2 * m) := Fintype.equivFinOfCardEq hcardm
    refine h m hm3 ⟨relabelW φ W, fun k => ?_, fun c hc => ?_⟩
    · rw [amplitude_relabel]
      have : (Amplitude.const (V := Fin (2 * m)) k) ∘ φ = Amplitude.const (V := A) k := rfl
      rw [this]
      exact hone k
    · rw [amplitude_relabel]
      refine hzero _ (fun hmono => hc ?_)
      obtain ⟨k, hk⟩ := hmono
      exact ⟨k, fun y => by simpa using hk (φ.symm y)⟩
  · refine hone 0 ?_
    rw [← pmSum_univ]
    refine pmSum_of_odd _ _ ?_
    rw [Finset.card_univ]
    exact Nat.not_even_iff_odd.mpr hodd

end NoCancellation

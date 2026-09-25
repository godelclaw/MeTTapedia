import GeneralOfficialBridge
import NoCancellation
import StarNormalForm
import TightCut

/-!
# The conditional results, in the official formulation

The library's `Solvable` is identified with the official equation system in
`GeneralOfficialBridge`.  Composing that identification with the conditional theorems states
them where the conjecture is actually posed, rather than in a paraphrase of it -- and without
the six-vertex base case, which the uniform argument does not use.
-/

open MonochromaticQuantumGraph GeneralOfficialBridge

/-- **The conjecture itself**, in the official formulation, as a proposition. -/
def OfficialKrennGu : Prop :=
  ∀ n : ℕ, 3 ≤ n → ¬ ∃ W : WeightsN (2 * n) 3 ℂ, EqSystemN (2 * n) 3 W

/-- **The official conjecture, from the sharpest pair of statements.**  No base case. -/
theorem official_of_colourDegreeOne
    (h : NoCancellation.ColourDegreeOne) (had : NoCancellation.AllDegenerate) :
    ∀ n : ℕ, 3 ≤ n → ¬ ∃ W : WeightsN (2 * n) 3 ℂ, EqSystemN (2 * n) 3 W :=
  fun n hn hex =>
    NoCancellation.krenn_gu_of_colourDegreeOne h had n hn (solvable_of_eqSystemN hex)

/-- **The official conjecture, from the partition question.**  No base case. -/
theorem official_of_certifiedPartition
    (h : NoCancellation.CertifiedPartition) (had : NoCancellation.AllDegenerate) :
    ∀ n : ℕ, 3 ≤ n → ¬ ∃ W : WeightsN (2 * n) 3 ℂ, EqSystemN (2 * n) 3 W :=
  fun n hn hex =>
    NoCancellation.krenn_gu_of_certifiedPartition h had n hn (solvable_of_eqSystemN hex)

/-- **The official conjecture, from the matching question.**  No base case.  The sharpest of the
partition-shaped hypotheses: it asks for one perfect matching using more than one colour, whose
pairs are each site's only live partner of that colour inside its own fibre. -/
theorem official_of_pureMixedMatching
    (h : NoCancellation.PureMixedMatching) (had : NoCancellation.AllDegenerate) :
    ∀ n : ℕ, 3 ≤ n → ¬ ∃ W : WeightsN (2 * n) 3 ℂ, EqSystemN (2 * n) 3 W :=
  fun n hn hex =>
    NoCancellation.krenn_gu_of_pureMixedMatching h had n hn (solvable_of_eqSystemN hex)

/-- **The official conjecture, from the degree bound alone.**  No base case. -/
theorem official_of_minimalLiveDegree (h : MinimalSupport.MinimalLiveDegreeThree) :
    ∀ n : ℕ, 3 ≤ n → ¬ ∃ W : WeightsN (2 * n) 3 ℂ, EqSystemN (2 * n) 3 W :=
  fun n hn hex =>
    MinimalSupport.krenn_gu_of_minimalLiveDegree h n hn (solvable_of_eqSystemN hex)

/-- **The official conjecture, from full degeneracy alone.**  The degree bound follows from it, and
the degree bound is the whole reduction, so the development rests on this one statement: every star
term dies on the non-constant colourings, each live pair then wears one colour and is certified in
it, and two partners of one colour would let the second absorb the first while the support drops --
which minimal support forbids. -/
theorem official_of_allDegenerate (had : NoCancellation.AllDegenerate) :
    ∀ n : ℕ, 3 ≤ n → ¬ ∃ W : WeightsN (2 * n) 3 ℂ, EqSystemN (2 * n) 3 W :=
  official_of_minimalLiveDegree (NoCancellation.minimalLiveDegree_of_allDegenerate had)

#print axioms official_of_colourDegreeOne
#print axioms official_of_certifiedPartition
#print axioms official_of_minimalLiveDegree
#print axioms official_of_pureMixedMatching
#print axioms official_of_allDegenerate

/-! ## Status audit

Each statement below is a universal property of support-minimal GHZ systems above four sites.  Each
already implies that no such system exists, so the conjecture implies it *back*, vacuously: an odd
site count carries no matching at all, and an even one relabels onto the official index type, where
the gauge-normalized bridge applies.

They are therefore **equivalent structural targets**, not weaker hypotheses.  Neither the count of
such statements nor the passage from one to another measures distance to the theorem. -/

theorem notSolvable_of_official (h : OfficialKrennGu) :
    ∀ n : ℕ, 3 ≤ n → ¬ KrennGu.Solvable n :=
  fun n hn hs => h n hn ((solvable_iff_eqSystemN (by omega)).mp hs)

/-- **Full degeneracy is an equivalent structural target.** -/
theorem allDegenerate_iff_official : NoCancellation.AllDegenerate ↔ OfficialKrennGu := by
  constructor
  · exact official_of_allDegenerate
  · intro h V _ _ W hcard hmin q
    exact absurd hmin.1
      (NoCancellation.not_isGHZ_of_not_solvable (notSolvable_of_official h) hcard W)

/-- **The degree bound is an equivalent structural target.** -/
theorem minimalLiveDegreeThree_iff_official :
    MinimalSupport.MinimalLiveDegreeThree ↔ OfficialKrennGu := by
  constructor
  · exact official_of_minimalLiveDegree
  · intro h V _ _ W hcard hmin u
    exact absurd hmin.1
      (NoCancellation.not_isGHZ_of_not_solvable (notSolvable_of_official h) hcard W)

#print axioms allDegenerate_iff_official
#print axioms minimalLiveDegreeThree_iff_official

/-- **The official conjecture, from the star-circuit normal form.** -/
theorem official_of_noStarCircuit (h : StarNormalForm.NoStarCircuit) : OfficialKrennGu :=
  official_of_minimalLiveDegree (StarNormalForm.minimalLiveDegreeThree_of_noStarCircuit h)

/-- **The normal form is an equivalent structural target.**  Recorded so that it is never reported
as a logically weaker theorem: the conjecture implies it back, because it is a universal property of
support-minimal GHZ systems above four sites and the conjecture says there are none. -/
theorem noStarCircuit_iff_official : StarNormalForm.NoStarCircuit ↔ OfficialKrennGu := by
  constructor
  · exact official_of_noStarCircuit
  · intro h V _ _ W hcard hmin u
    exact absurd hmin.1
      (NoCancellation.not_isGHZ_of_not_solvable (notSolvable_of_official h) hcard W)

#print axioms official_of_noStarCircuit
#print axioms noStarCircuit_iff_official

/-! ## The heart: what a smallest counterexample must be after collapsing tight cuts

A shore-tight cut (`KrennTightCut.ShoreTight`) collapses exactly: the kept side plus one site
carries a GHZ system again.  So a smallest counterexample has no shore-tight cut keeping five or
more sites.  At six sites, two shore-tight triangles are ruled out separately
(`KrennTightCut.false_of_shoreTight_six`).  What remains is `Heart`. -/

/-- **No GHZ system on a site count below a bound, from the smaller cases.**  The bounded form of
`NoCancellation.not_isGHZ_of_not_solvable`: an odd count carries no matching, and an even count
relabels onto the official index type. -/
theorem not_isGHZ_of_not_solvable_lt {N : ℕ}
    (h : ∀ m : ℕ, 3 ≤ m → 2 * m < N → ¬ KrennGu.Solvable m)
    {A : Type} [Fintype A] [DecidableEq A] (hcard : 4 < Fintype.card A)
    (hlt : Fintype.card A < N) (W : Sym2 (A × Fin 3) → ℂ) : ¬ KrennGu.IsGHZ W := by
  classical
  rintro ⟨hone, hzero⟩
  rcases Nat.even_or_odd (Fintype.card A) with hev | hodd
  · obtain ⟨m, hm⟩ := hev
    have hcardm : Fintype.card A = 2 * m := by omega
    let φ : A ≃ Fin (2 * m) := Fintype.equivFinOfCardEq hcardm
    refine h m (by omega) (by omega) ⟨NoCancellation.relabelW φ W, fun k => ?_, fun c hc => ?_⟩
    · rw [NoCancellation.amplitude_relabel]
      have : (Amplitude.const (V := Fin (2 * m)) k) ∘ φ = Amplitude.const (V := A) k := rfl
      rw [this]
      exact hone k
    · rw [NoCancellation.amplitude_relabel]
      refine hzero _ (fun hmono => hc ?_)
      obtain ⟨k, hk⟩ := hmono
      exact ⟨k, fun y => by simpa using hk (φ.symm y)⟩
  · refine hone 0 ?_
    rw [← MatchingSum.pmSum_univ]
    refine MatchingSum.pmSum_of_odd _ _ ?_
    rw [Finset.card_univ]
    exact Nat.not_even_iff_odd.mpr hodd

/-- **The heart.**  A support-minimal GHZ system above four sites, all of whose smaller site
counts from six up are already impossible, with no shore-tight cut that keeps at least five sites
and collapses at least three.

Its live graph therefore has no nontrivial tight cut keeping five or more sites.  At six sites
this is joined by `KrennTightCut.false_of_shoreTight_six`. -/
def Heart : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (W : Sym2 (V × Fin 3) → ℂ),
    4 < Fintype.card V → MinimalSupport.IsSupportMinimal W →
    (∀ n : ℕ, 3 ≤ n → 2 * n < Fintype.card V → ¬ KrennGu.Solvable n) →
    (∀ S : Finset V, 5 ≤ S.card → 3 ≤ (Finset.univ \ S).card →
      ¬ KrennTightCut.ShoreTight W S) →
    False

/-- **The official conjecture, from the heart.**  By strong induction on the site count.  A
support-minimal representative with a shore-tight cut keeping at least five sites collapses to a
GHZ system on fewer sites, which the induction hypothesis excludes; otherwise it is a heart
configuration. -/
theorem official_of_heart (h : Heart) : OfficialKrennGu := by
  intro n hn hex
  suffices H : ∀ n : ℕ, 3 ≤ n → ¬ KrennGu.Solvable n from H n hn (solvable_of_eqSystemN hex)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rintro hn ⟨W, hW⟩
    obtain ⟨W', hmin, -⟩ := MinimalSupport.exists_supportMinimal W hW
    have hsmall : ∀ m : ℕ, 3 ≤ m → 2 * m < Fintype.card (Fin (2 * n)) →
        ¬ KrennGu.Solvable m := by
      intro m hm hlt
      rw [Fintype.card_fin] at hlt
      exact ih m (by omega) hm
    refine h (Fin (2 * n)) W' (by rw [Fintype.card_fin]; omega) hmin hsmall ?_
    intro S hS5 hS3 ht
    have hcompl : (Finset.univ \ S).Nonempty := Finset.card_pos.mp (by omega)
    have hGHZ := KrennTightCut.isGHZOver_shoreContract hmin.1 hcompl ht
    have hSle : S.card + 3 ≤ 2 * n := by
      have := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
      rw [Finset.card_univ, Fintype.card_fin] at this
      omega
    refine not_isGHZ_of_not_solvable_lt hsmall (A := Option ↥S) ?_ ?_ _ hGHZ
    · rw [Fintype.card_option, Fintype.card_coe]
      omega
    · rw [Fintype.card_option, Fintype.card_coe, Fintype.card_fin]
      omega

/-- **The heart is an equivalent structural target.**  Recorded so that it is never reported as a
weaker theorem: the conjecture implies it back, because it is a universal property of
support-minimal GHZ systems above four sites and the conjecture says there are none. -/
theorem heart_iff_official : Heart ↔ OfficialKrennGu := by
  constructor
  · exact official_of_heart
  · intro h V _ _ W hcard hmin _ _
    exact absurd hmin.1
      (NoCancellation.not_isGHZ_of_not_solvable (notSolvable_of_official h) hcard W)

#print axioms official_of_heart
#print axioms heart_iff_official

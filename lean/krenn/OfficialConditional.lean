import GeneralOfficialBridge
import NoCancellation
import StarNormalForm

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

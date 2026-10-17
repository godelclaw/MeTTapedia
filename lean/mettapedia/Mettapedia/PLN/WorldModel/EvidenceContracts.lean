import Mettapedia.PLN.WorldModel.EvidenceSpaces
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction
import Mettapedia.Logic.WorldModel.Basic
import Mettapedia.ProbabilityTheory.ImpreciseProbability.WalleyBinaryIDM
import Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions

/-!
# Observation contracts for evidence

A count pair `(n⁺, n⁻)` summarizes observations.  Which operations on count
pairs are sound depends on what was observed and how the observations relate.
This module states four observation contracts and derives, for each, the
operations it licenses and the ones it refutes.

## 1. Identified observations (the ledger contract)

Each observation has an identity and records one world (`ledgerEvidence`).  A
ledger is a finite set of identities, so ledgers form a distributive lattice and
merging two replicas is their union: idempotent, commutative and associative.

* **Evidence is a valuation** (`ledgerEvidence_union_add_inter`): the evidence of
  a union plus the evidence of the overlap is the sum of the two evidences.
* **Additive revision is exact exactly for disjoint ledgers**
  (`additive_revision_exact_iff_disjoint`); otherwise it counts the overlap twice
  (`revision_counts_overlap_twice`).  The disjointness check on evidential bases
  of non-axiomatic reasoning is this condition.
* **Retraction is exact with identities** (`ledgerEvidence_sdiff`): removing a
  ledger subtracts the evidence of its overlap, by the monus of counts.
* **Revision under unknown overlap is an interval** (`unknown_overlap_bounds`,
  `Controls.overlap_interval_ends`): the merged evidence lies between the
  coordinatewise maximum and the sum, and both ends occur with the same two
  evidences.  The maximum is the conservative revision, sound for every
  overlap, the counting analogue of covariance intersection; the sum is exact
  only for disjoint ledgers.
* **Overlap revision is derived** (`ledgerOverlapModel`): the abstract
  `OverlapWorldModel` with `combine x y o = x + y - o`, the overlap being the
  evidence of the intersection.
* **Source-keyed maximum is the union under per-source nesting**
  (`ledgerEvidence_union_eq_sourceMerge`): the coordination-free revision of
  `EvidenceSpaces` computes the evidence of the merged ledger exactly when each
  source's observations on the two replicas are nested, as with cumulative
  publication.  Without nesting it under-counts
  (`Controls.sourceMerge_undercounts`).

## 2. Observations of one world (the same-world contract)

When two predicates are evaluated on the same bag of worlds, their marginal
counts do not determine the count of their conjunction
(`EvidenceSpaces.no_same_world_conjunction_from_marginals`).  The possible
conjunction counts are exactly the Fréchet interval
`max 0 (a + b - n) ≤ c ≤ min a b` (`conjunction_counts_iff`): every value in it
is realized by some bag and no value outside it is.  The product of the two
frequencies, the reading under independence, lies inside that interval
(`independence_within_frechet`).  So for dependent observations the sound
readout of a conjunction is an interval, and independence selects one point
of it.

## 3. Pairs of samples (the Cartesian contract)

Pairing two bags of samples gives the paired product of
`EvidenceSpaces.ofSamples_product`.  Its total counts pairs, not independent
samples of the conjunction: see `Mettapedia.PLN.WorldModel.PairedSampleDispersion`.

## 4. Reports about one hypothesis (the likelihood contract)

A report is read as the pair of masses of the hypothesis and of its negation
jointly with the report (`testimony`).  For two reports conditionally
independent given the hypothesis, under a uniform prior, the evidence of the
joint report is the coordinatewise product of the two single-report evidences,
up to the prior constant (`testimony_fuse_uniform`), and its strength is the
posterior probability of the hypothesis (`strength_fuse_uniform`).  This
coordinatewise product is PLN's binary-evidence tensor (`toPaired_tensor`).

* Its zero divisor is total conflict: two certain, contradictory reports leave no
  mass (`fuse_total_conflict`).
* Its strength is the logarithmic opinion pool, or Dempster's rule on Bayesian
  mass functions over a two-element frame (`strength_fuse`).
* Fusing two posteriors that each contain a non-uniform prior counts the prior
  twice (`testimony_fuse_counts_prior_twice`, `Controls.prior_counted_twice`).
* It is not conjunction: on two half-strength premises its strength is `1/2`,
  while the strength of the paired product, the direct-path term `s_AB · s_BC`
  of PLN deduction, is `1/4` (`Controls.fuse_not_direct_path`).

## Readouts

Strength is undetermined with no samples (`EvidenceSpaces.readout_zero`).  The
credal readout of Walley's imprecise Dirichlet model is `[0, 1]` at zero counts
(`idm_vacuous`), its width is one minus the PLN confidence `n / (n + s)`
(`idm_width`), and with samples it contains the observed frequency
(`idm_contains_frequency`).  Revision shrinks the width but moves the interval:
the intervals of successive evidence states are not nested
(`idm_not_nested`).

## Evidential negation is presence; Heyting negation is not

Negative evidence is recorded, not inferred from absence.  Swapping the two
counts (`against`) is an involution that is monotone in the information order
and distributes over revision (`against_mono`, `against_add`).  The truth-order meet and
join of the evidence bilattice are monotone in the information order
(`tmeet_mono`, `tjoin_mono`) and are exchanged by negation (`against_tmeet`).  The
four-valued reading (neither, true, false, both) is monotone (`belnap_mono`).
So every connective of this evidential logic only grows with evidence, and a
program built from them stays presence-only.  The intuitionistic negation
`a ⇨ ⊥` of a nontrivial Heyting algebra is not monotone
(`hnot_not_monotone`); on PLN's evidence frame it fails
(`binaryEvidence_hnot_not_monotone`).  Absence-based negation therefore needs a
frontier (`Mettapedia.GSLT.Contracts.FrontierNegation`), while evidence against
does not.

## PLN deduction is derived under screening off

For a bag of worlds over `A`, `B`, `C`, if `C` is independent of `A` given `B`
and given `¬B` in the counts, the frequency of `C` among the `A`-worlds is
`s_AB · s_BC + (1 - s_AB) · (p_C - p_B · s_BC) / (1 - p_B)`, the PLN deduction
formula (`deduction_exact_of_screening`).  Without screening off it fails
(`Controls.deduction_fails_without_screening`).

## Conclusion confidence is derived through intervals

The confidence of a conclusion is derived, not posited, by a route with three
steps.

1. **Premises to intervals.**  Premise evidence `(n⁺, n⁻)` becomes the imprecise
   Dirichlet interval with a declared prior strength `s`; its evidence weight
   reads back `n⁺ + n⁻` (`idm_intervalWeight`).
2. **Intervals through the rule.**  The observation contract fixes the map:
   the product interval for independent pairs (`product_interval`), the
   Fréchet interval for conjunction on one world (`frechet_interval`), the
   corner interval of the bilinear deduction map under screening off
   (`deduction_interval`, `bilinear_between_corners`), and the vacuous
   interval `[0, 1]` without screening off (`Controls.unscreened_vacuous`).
3. **Interval to truth value.**  A declared selector gives strength; the
   width-complement chart gives confidence, and it is the PLN odds chart
   `w / (w + s)` for the interval's evidence weight (`widthConfidence_eq_odds`).
   `deduction_confidence_route` assembles the three steps for deduction.

Degrees of freedom: the prior strength `s` and the strength selector are
genuine choices; the range `[0, 1]` is a convention once declared; the chart is
free until the Walley gate, which forces the PLN odds chart; the propagation map
is fixed by the observation contract, not chosen.

Against this route, PLN's deduction evidence, which gives its conclusion the
sum of the premise totals (`deductionEvidence_total`), is neither an upper nor a
lower bound: on premises `(1, 1)` and `(1, 1)` it posits `4`
(`Controls.deductionEvidence_posits_four`) where the route derives weight `2` at
`p_B = p_C = 0` and `8` at `p_B = p_C = 1/2`, and it agrees, at `5`, on premises
`(0, 2)` and `(1, 2)` (`Controls.deduction_posited_overstates`,
`Controls.deduction_posited_understates`, `Controls.deduction_posited_agrees`).
The weight-product conjunction of the tree gives confidence `4/5` on premises
`(1, 1)` and `(1, 1)` where the route derives `2/3`
(`Controls.conjunction_through_intervals`).
-/

set_option autoImplicit false

namespace Mettapedia.PLN.WorldModel.EvidenceContracts

open Mettapedia.PLN.WorldModel.EvidenceSpaces
open Mettapedia.PLN.WorldModel.EvidenceSpaces.Evidence

universe u v w

/-! ## Cancellation of counts -/

theorem evidence_add_right_cancel {a b c : Evidence ℕ} (h : a + c = b + c) : a = b := by
  have hp := congrArg Evidence.pos h
  have hn := congrArg Evidence.neg h
  simp only [Evidence.add_pos, Evidence.add_neg] at hp hn
  ext
  · omega
  · omega

theorem evidence_le_def (a b : Evidence ℕ) : a ≤ b ↔ a.pos ≤ b.pos ∧ a.neg ≤ b.neg := Iff.rfl

/-! ## 1. The ledger contract -/

section Ledger

variable {Id : Type u} {W : Type v} [DecidableEq Id]

/-- **The evidence of a ledger**: each identified observation `i` records the
world `world i`, and contributes one sample of it. -/
def ledgerEvidence (world : Id → W) (φ : W → Bool) (ledger : Finset Id) : Evidence ℕ :=
  ∑ i ∈ ledger, sampleEvidence φ (world i)

omit [DecidableEq Id] in
/-- A ledger gives the evidence of the bag of worlds it records. -/
theorem ledgerEvidence_eq_ofSamples (world : Id → W) (φ : W → Bool) (ledger : Finset Id) :
    ledgerEvidence world φ ledger = ofSamples φ (ledger.val.map world) := by
  simp only [ledgerEvidence, ofSamples, Finset.sum, Multiset.map_map]
  rfl

omit [DecidableEq Id] in
/-- Every recorded observation is one sample. -/
theorem ledgerEvidence_total (world : Id → W) (φ : W → Bool) (ledger : Finset Id) :
    (ledgerEvidence world φ ledger).total = ledger.card := by
  rw [ledgerEvidence_eq_ofSamples, ofSamples_total, Multiset.card_map]
  rfl

omit [DecidableEq Id] in
theorem ledgerEvidence_eq_zero_iff (world : Id → W) (φ : W → Bool) (ledger : Finset Id) :
    ledgerEvidence world φ ledger = 0 ↔ ledger = ∅ := by
  constructor
  · intro zero
    have := ledgerEvidence_total world φ ledger
    rw [zero] at this
    simp only [total, Evidence.zero_pos, Evidence.zero_neg, add_zero] at this
    exact Finset.card_eq_zero.1 this.symm
  · rintro rfl
    simp [ledgerEvidence]

/-- **Evidence is a valuation on ledgers**: inclusion–exclusion. -/
theorem ledgerEvidence_union_add_inter (world : Id → W) (φ : W → Bool) (first second : Finset Id) :
    ledgerEvidence world φ (first ∪ second) + ledgerEvidence world φ (first ∩ second) =
      ledgerEvidence world φ first + ledgerEvidence world φ second :=
  Finset.sum_union_inter

/-- Disjoint ledgers revise by addition. -/
theorem ledgerEvidence_union_of_disjoint (world : Id → W) (φ : W → Bool) {first second : Finset Id}
    (disjoint : Disjoint first second) :
    ledgerEvidence world φ (first ∪ second) =
      ledgerEvidence world φ first + ledgerEvidence world φ second :=
  Finset.sum_union disjoint

/-- **Additive revision counts the overlap twice.** -/
theorem revision_counts_overlap_twice (world : Id → W) (φ : W → Bool) (first second : Finset Id) :
    ledgerEvidence world φ first + ledgerEvidence world φ second =
      ledgerEvidence world φ (first ∪ second) + ledgerEvidence world φ (first ∩ second) :=
  (ledgerEvidence_union_add_inter world φ first second).symm

/-- **Additive revision is exact exactly for disjoint ledgers.** -/
theorem additive_revision_exact_iff_disjoint (world : Id → W) (φ : W → Bool)
    (first second : Finset Id) :
    ledgerEvidence world φ first + ledgerEvidence world φ second =
        ledgerEvidence world φ (first ∪ second) ↔ Disjoint first second := by
  constructor
  · intro exact
    rw [revision_counts_overlap_twice] at exact
    have overlap : ledgerEvidence world φ (first ∩ second) = 0 := by
      apply evidence_add_right_cancel (c := ledgerEvidence world φ (first ∪ second))
      rw [zero_add, add_comm]
      exact exact
    rw [ledgerEvidence_eq_zero_iff] at overlap
    exact Finset.disjoint_iff_inter_eq_empty.2 overlap
  · intro disjoint
    exact (ledgerEvidence_union_of_disjoint world φ disjoint).symm

/-- **Retraction with identities is exact**: removing a ledger subtracts the
evidence of the overlap. -/
theorem ledgerEvidence_sdiff (world : Id → W) (φ : W → Bool) (first second : Finset Id) :
    ledgerEvidence world φ (first \ second) =
      ledgerEvidence world φ first - ledgerEvidence world φ (first ∩ second) := by
  have split : ledgerEvidence world φ first =
      ledgerEvidence world φ (first \ second) + ledgerEvidence world φ (first ∩ second) := by
    conv_lhs => rw [← Finset.sdiff_union_inter first second]
    exact ledgerEvidence_union_of_disjoint world φ (Finset.disjoint_sdiff_inter first second)
  rw [split, retract_revision]

/-- Evidence grows with the ledger. -/
theorem ledgerEvidence_mono (world : Id → W) (φ : W → Bool) {first second : Finset Id}
    (sub : first ⊆ second) : ledgerEvidence world φ first ≤ ledgerEvidence world φ second := by
  have split : ledgerEvidence world φ second =
      ledgerEvidence world φ first + ledgerEvidence world φ (second \ first) := by
    conv_lhs => rw [← Finset.union_sdiff_of_subset sub]
    exact ledgerEvidence_union_of_disjoint world φ Finset.disjoint_sdiff
  rw [split]
  exact le_self_add

/-- **Overlap revision is derived**: the union of two ledgers has the sum of
their evidence minus the evidence of their overlap. -/
theorem ledgerEvidence_union (world : Id → W) (φ : W → Bool) (first second : Finset Id) :
    ledgerEvidence world φ (first ∪ second) =
      ledgerEvidence world φ first + ledgerEvidence world φ second -
        ledgerEvidence world φ (first ∩ second) := by
  rw [revision_counts_overlap_twice, retract_revision]

/-- **The ledger world model**: revision is union, and extraction obeys the
overlap law with the overlap read off the intersection. -/
@[instance_reducible]
def ledgerOverlapModel (world : Id → W) :
    OverlapWorldModel (Finset Id) (W → Bool) (Evidence ℕ) (Evidence ℕ) where
  revise := (· ∪ ·)
  empty := ∅
  extract ledger φ := ledgerEvidence world φ ledger
  revise_assoc := Finset.union_assoc
  revise_empty_left := Finset.empty_union
  revise_empty_right := Finset.union_empty
  overlap first second φ := ledgerEvidence world φ (first ∩ second)
  combine x y o := x + y - o
  extract_revise first second φ := ledgerEvidence_union world φ first second

/-- **Revision under unknown overlap is bounded by the maximum and the sum**: the
evidence of the merged ledger lies between the coordinatewise maximum of the
two evidences and their sum.  The maximum is the conservative revision, sound
whatever the overlap; the sum assumes disjointness. -/
theorem unknown_overlap_bounds (world : Id → W) (φ : W → Bool) (first second : Finset Id) :
    (⟨max (ledgerEvidence world φ first).pos (ledgerEvidence world φ second).pos,
        max (ledgerEvidence world φ first).neg (ledgerEvidence world φ second).neg⟩ : Evidence ℕ) ≤
        ledgerEvidence world φ (first ∪ second) ∧
      ledgerEvidence world φ (first ∪ second) ≤
        ledgerEvidence world φ first + ledgerEvidence world φ second := by
  have left := ledgerEvidence_mono world φ (Finset.subset_union_left : first ⊆ first ∪ second)
  have right := ledgerEvidence_mono world φ (Finset.subset_union_right : second ⊆ first ∪ second)
  refine ⟨⟨max_le left.1 right.1, max_le left.2 right.2⟩, ?_⟩
  rw [revision_counts_overlap_twice]
  exact le_self_add

/-- Merging ledgers is idempotent: duplicate delivery is harmless. -/
theorem ledger_merge_idem (ledger : Finset Id) : ledger ∪ ledger = ledger := Finset.union_idempotent ledger

/-! ### Source-keyed revision is ledger union under nesting -/

section Sources

variable {Src : Type w} [Fintype Src] [DecidableEq Src]

/-- The part of a ledger observed by one source. -/
def bySource (source : Id → Src) (ledger : Finset Id) (src : Src) : Finset Id :=
  ledger.filter fun i => source i = src

omit [DecidableEq Id] in
theorem ledgerEvidence_fiberwise (world : Id → W) (φ : W → Bool) (source : Id → Src)
    (ledger : Finset Id) :
    ledgerEvidence world φ ledger = ∑ src, ledgerEvidence world φ (bySource source ledger src) := by
  unfold ledgerEvidence bySource
  exact (Finset.sum_fiberwise ledger source _).symm

theorem merge_of_le {a b : Evidence ℕ} (le : a ≤ b) :
    (⟨max a.pos b.pos, max a.neg b.neg⟩ : Evidence ℕ) = b := by
  ext
  · exact max_eq_right le.1
  · exact max_eq_right le.2

/-- **Source-keyed maximum is ledger union under per-source nesting**: when, for
every source, its observations held by one replica are among those held by the
other, the source-keyed merge of `EvidenceSpaces` reads out the evidence of the
merged ledger. -/
theorem ledgerEvidence_union_eq_sourceMerge (world : Id → W) (φ : W → Bool) (source : Id → Src)
    (first second : Finset Id)
    (nested : ∀ src, bySource source first src ⊆ bySource source second src ∨
      bySource source second src ⊆ bySource source first src) :
    ledgerEvidence world φ (first ∪ second) =
      sourceReadout (sourceMerge (fun src => ledgerEvidence world φ (bySource source first src))
        (fun src => ledgerEvidence world φ (bySource source second src))) := by
  rw [ledgerEvidence_fiberwise world φ source, sourceReadout]
  refine Finset.sum_congr rfl fun src _ => ?_
  have union : bySource source (first ∪ second) src =
      bySource source first src ∪ bySource source second src := Finset.filter_union _ _ _
  rw [union, sourceMerge]
  rcases nested src with sub | sub
  · rw [Finset.union_eq_right.2 sub, merge_of_le (ledgerEvidence_mono world φ sub)]
  · rw [Finset.union_eq_left.2 sub, max_comm, max_comm (ledgerEvidence world φ _).neg,
      merge_of_le (ledgerEvidence_mono world φ sub)]

end Sources

end Ledger

/-! ## 2. The same-world contract: the Fréchet interval -/

section SameWorld

variable {W : Type v}

/-- The number of worlds of a bag satisfying a predicate. -/
abbrev count (bag : Multiset W) (p : W → Bool) : ℕ := Multiset.countP (fun w => p w = true) bag

theorem ofSamples_pos_eq_count (φ : W → Bool) (bag : Multiset W) :
    (ofSamples φ bag).pos = count bag φ := ofSamples_pos φ bag

/-- Splitting a count along a second predicate. -/
theorem count_split (bag : Multiset W) (p q : W → Bool) :
    count bag p = count bag (fun w => p w && q w) + count bag (fun w => p w && !q w) := by
  induction bag using Multiset.induction_on with
  | empty => simp
  | cons w bag ih =>
      simp only [count, Multiset.countP_cons] at ih ⊢
      rw [ih]
      cases hp : p w <;> cases hq : q w <;>
        simp only [Bool.and_true, Bool.and_false, Bool.not_true, Bool.not_false,
          Bool.false_eq_true, if_true, if_false] <;> omega

/-- **Fréchet upper bound**: a conjunction holds at most as often as each conjunct. -/
theorem frechet_upper (bag : Multiset W) (φ ψ : W → Bool) :
    count bag (fun w => φ w && ψ w) ≤ count bag φ ∧ count bag (fun w => φ w && ψ w) ≤ count bag ψ := by
  induction bag using Multiset.induction_on with
  | empty => simp
  | cons w bag ih =>
      simp only [count, Multiset.countP_cons] at ih ⊢
      cases hφ : φ w <;> cases hψ : ψ w <;>
        simp only [Bool.and_true, Bool.and_false, Bool.false_eq_true, if_true, if_false] <;> omega

/-- **Fréchet lower bound**: `a + b ≤ c + n`. -/
theorem frechet_lower (bag : Multiset W) (φ ψ : W → Bool) :
    count bag φ + count bag ψ ≤ count bag (fun w => φ w && ψ w) + Multiset.card bag := by
  induction bag using Multiset.induction_on with
  | empty => simp
  | cons w bag ih =>
      simp only [count, Multiset.countP_cons, Multiset.card_cons] at ih ⊢
      cases hφ : φ w <;> cases hψ : ψ w <;>
        simp only [Bool.and_true, Bool.and_false, Bool.false_eq_true, if_true, if_false] <;> omega

theorem countP_replicate' {α : Type*} (p : α → Prop) [DecidablePred p] (n : ℕ) (a : α) :
    Multiset.countP p (Multiset.replicate n a) = if p a then n else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Multiset.replicate_succ, Multiset.countP_cons, ih]
      split_ifs <;> simp

/-- The bag realizing given marginal and joint counts. -/
def frechetBag (n a b c : ℕ) : Multiset (Bool × Bool) :=
  Multiset.replicate c (true, true) + Multiset.replicate (a - c) (true, false) +
    Multiset.replicate (b - c) (false, true) + Multiset.replicate (n + c - a - b) (false, false)

/-- **The conjunction counts compatible with marginal counts are exactly the
Fréchet interval.** -/
theorem conjunction_counts_iff (n a b c : ℕ) :
    (∃ bag : Multiset (Bool × Bool), Multiset.card bag = n ∧
        count bag Prod.fst = a ∧ count bag Prod.snd = b ∧
        count bag (fun w => w.1 && w.2) = c) ↔
      a ≤ n ∧ b ≤ n ∧ a + b ≤ c + n ∧ c ≤ a ∧ c ≤ b := by
  constructor
  · rintro ⟨bag, card, ha, hb, hc⟩
    have upper := frechet_upper bag Prod.fst Prod.snd
    have lower := frechet_lower bag Prod.fst Prod.snd
    have aLe : count bag Prod.fst ≤ Multiset.card bag := Multiset.countP_le_card _ _
    have bLe : count bag Prod.snd ≤ Multiset.card bag := Multiset.countP_le_card _ _
    subst card ha hb hc
    exact ⟨aLe, bLe, lower, upper.1, upper.2⟩
  · rintro ⟨ha, hb, hab, hca, hcb⟩
    refine ⟨frechetBag n a b c, ?_, ?_, ?_, ?_⟩ <;>
      simp [frechetBag, count, Multiset.countP_add, countP_replicate'] <;> omega

/-- **Independence is one point of the Fréchet interval**: with marginal
frequencies `a / n` and `b / n`, the product `a b / n²` lies between
`(a + b - n) / n` and `min a b / n`. -/
theorem independence_within_frechet {n a b : ℕ} (ha : a ≤ n) (hb : b ≤ n) :
    n * a + n * b ≤ a * b + n * n ∧ a * b ≤ n * a ∧ a * b ≤ n * b := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_le ha
    obtain ⟨y, hy⟩ := Nat.exists_eq_add_of_le hb
    rw [hy]
    nlinarith
  · exact (Nat.mul_le_mul_left a hb).trans_eq (mul_comm a n)
  · exact Nat.mul_le_mul_right b ha

end SameWorld

/-! ## 4. The likelihood contract: PLN's tensor -/

section Likelihood

variable {R : Type u}

/-- **Fusion of likelihood evidence**: the coordinatewise product. -/
def fuse [Mul R] (a b : Evidence R) : Evidence R := ⟨a.pos * b.pos, a.neg * b.neg⟩

/-- The evidence a report gives a binary hypothesis: the masses of the
hypothesis and of its negation jointly with the report. -/
def testimony (mass : Bool → R) : Evidence R := ⟨mass true, mass false⟩

variable [CommSemiring R]

/-- A joint distribution of a hypothesis and two reports, conditionally
independent given the hypothesis: `prior h · first h e₁ · second h e₂`. -/
def ciJoint (prior : Bool → R) (first second : Bool → Bool → R) (h e₁ e₂ : Bool) : R :=
  prior h * first h e₁ * second h e₂

/-- A report's likelihoods sum to one under each value of the hypothesis. -/
def Stochastic (report : Bool → Bool → R) : Prop := ∀ h, report h true + report h false = 1

/-- The evidence of the first report alone. -/
def firstReport (prior : Bool → R) (first second : Bool → Bool → R) : Evidence R :=
  testimony fun h => ciJoint prior first second h true true + ciJoint prior first second h true false

/-- The evidence of the second report alone. -/
def secondReport (prior : Bool → R) (first second : Bool → Bool → R) : Evidence R :=
  testimony fun h => ciJoint prior first second h true true + ciJoint prior first second h false true

/-- The evidence of both reports. -/
def jointReport (prior : Bool → R) (first second : Bool → Bool → R) : Evidence R :=
  testimony fun h => ciJoint prior first second h true true

theorem report_mass_first (prior : Bool → R) (first second : Bool → Bool → R)
    (stochSecond : Stochastic second) (h : Bool) :
    ciJoint prior first second h true true + ciJoint prior first second h true false =
      prior h * first h true := by
  simp only [ciJoint]
  rw [← mul_add, stochSecond h, mul_one]

theorem report_mass_second (prior : Bool → R) (first second : Bool → Bool → R)
    (stochFirst : Stochastic first) (h : Bool) :
    ciJoint prior first second h true true + ciJoint prior first second h false true =
      prior h * second h true := by
  simp only [ciJoint]
  rw [← add_mul, ← mul_add, stochFirst h, mul_one]

/-- **Fusing two single-report evidences counts the prior twice**: the product
is the joint-report evidence scaled once more by the prior. -/
theorem testimony_fuse_counts_prior_twice (prior : Bool → R) (first second : Bool → Bool → R)
    (stochFirst : Stochastic first) (stochSecond : Stochastic second) :
    fuse (firstReport prior first second) (secondReport prior first second) =
      ⟨prior true * (jointReport prior first second).pos,
        prior false * (jointReport prior first second).neg⟩ := by
  simp only [fuse, firstReport, secondReport, jointReport, testimony,
    report_mass_first prior first second stochSecond,
    report_mass_second prior first second stochFirst]
  ext <;> simp only [ciJoint] <;> ring

/-- **Under a uniform prior the tensor is the evidence of both reports**, up to
the prior constant. -/
theorem testimony_fuse_uniform (c : R) (first second : Bool → Bool → R)
    (stochFirst : Stochastic first) (stochSecond : Stochastic second) :
    fuse (firstReport (fun _ => c) first second) (secondReport (fun _ => c) first second) =
      ⟨c * (jointReport (fun _ => c) first second).pos,
        c * (jointReport (fun _ => c) first second).neg⟩ :=
  testimony_fuse_counts_prior_twice _ first second stochFirst stochSecond

/-- **PLN's binary-evidence tensor is likelihood fusion.** -/
theorem toPaired_tensor (x y : Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence) :
    toPaired (x * y) = fuse (toPaired x) (toPaired y) := rfl

/-- **Total conflict is the zero divisor**: two certain, contradictory reports
leave no mass. -/
theorem fuse_total_conflict : fuse (⟨1, 0⟩ : Evidence R) ⟨0, 1⟩ = 0 := by
  ext <;> simp [fuse]

end Likelihood

section LikelihoodField

variable {F : Type u} [Field F]

/-- **The strength of fused evidence is the posterior** of the hypothesis given
both reports, under a uniform prior and conditional independence. -/
theorem strength_fuse_uniform {c : F} (hc : c ≠ 0) (first second : Bool → Bool → F)
    (stochFirst : Stochastic first) (stochSecond : Stochastic second) :
    strength (fuse (firstReport (fun _ => c) first second) (secondReport (fun _ => c) first second)) =
      ciJoint (fun _ => c) first second true true true /
        (ciJoint (fun _ => c) first second true true true +
          ciJoint (fun _ => c) first second false true true) := by
  rw [testimony_fuse_uniform c first second stochFirst stochSecond]
  simp only [strength, total, jointReport, testimony]
  rw [← mul_add, mul_div_mul_left _ _ hc]

/-- **The strength of fused evidence is the logarithmic opinion pool**, which is
Dempster's rule on Bayesian mass functions over a two-element frame. -/
theorem strength_fuse (a b : Evidence F) (ha : a.total ≠ 0) (hb : b.total ≠ 0)
    (hab : a.pos * b.pos + a.neg * b.neg ≠ 0) :
    strength (fuse a b) =
      strength a * strength b /
        (strength a * strength b + (1 - strength a) * (1 - strength b)) := by
  have one_sub_a : 1 - strength a = a.neg / a.total := by
    rw [strength, eq_div_iff ha, sub_mul, one_mul, div_mul_cancel₀ _ ha, total]; ring
  have one_sub_b : 1 - strength b = b.neg / b.total := by
    rw [strength, eq_div_iff hb, sub_mul, one_mul, div_mul_cancel₀ _ hb, total]; ring
  rw [one_sub_a, one_sub_b]
  simp only [strength, fuse, total]
  simp only [total] at ha hb
  field_simp

end LikelihoodField

/-! ## Evidential negation -/

section Negation

variable {R : Type u}

/-- **Evidence against**: exchange the two counts. -/
def against (e : Evidence R) : Evidence R := ⟨e.neg, e.pos⟩

@[simp] theorem against_pos (e : Evidence R) : (against e).pos = e.neg := rfl
@[simp] theorem against_neg (e : Evidence R) : (against e).neg = e.pos := rfl

theorem against_against (e : Evidence R) : against (against e) = e := rfl

theorem against_add [CommSemiring R] (a b : Evidence R) : against (a + b) = against a + against b := rfl

/-- **Evidential negation is monotone in the information order.** -/
theorem against_mono {a b : Evidence ℕ} (le : a ≤ b) : against a ≤ against b := ⟨le.2, le.1⟩

/-- The truth-order meet of the evidence bilattice. -/
def tmeet (a b : Evidence ℕ) : Evidence ℕ := ⟨min a.pos b.pos, max a.neg b.neg⟩

/-- The truth-order join of the evidence bilattice. -/
def tjoin (a b : Evidence ℕ) : Evidence ℕ := ⟨max a.pos b.pos, min a.neg b.neg⟩

/-- **The truth-order meet is monotone in the information order.** -/
theorem tmeet_mono {a a' b b' : Evidence ℕ} (ha : a ≤ a') (hb : b ≤ b') :
    tmeet a b ≤ tmeet a' b' :=
  ⟨min_le_min ha.1 hb.1, max_le_max ha.2 hb.2⟩

/-- **The truth-order join is monotone in the information order.** -/
theorem tjoin_mono {a a' b b' : Evidence ℕ} (ha : a ≤ a') (hb : b ≤ b') :
    tjoin a b ≤ tjoin a' b' :=
  ⟨max_le_max ha.1 hb.1, min_le_min ha.2 hb.2⟩

/-- Negation exchanges the truth-order meet and join. -/
theorem against_tmeet (a b : Evidence ℕ) : against (tmeet a b) = tjoin (against a) (against b) := rfl

/-- The four-valued reading: is there evidence for, is there evidence against. -/
def belnap (e : Evidence ℕ) : Bool × Bool := (decide (e.pos ≠ 0), decide (e.neg ≠ 0))

/-- **The four-valued reading is monotone**: once there is evidence for (or
against), there remains evidence for (or against). -/
theorem belnap_mono {a b : Evidence ℕ} (le : a ≤ b) :
    ((belnap a).1 = true → (belnap b).1 = true) ∧ ((belnap a).2 = true → (belnap b).2 = true) := by
  simp only [belnap, decide_eq_true_eq]
  exact ⟨fun h => by have := le.1; omega, fun h => by have := le.2; omega⟩

/-- **Intuitionistic negation is not monotone**: in a Heyting algebra where
`a ↦ a ⇨ ⊥` is monotone, top equals bottom. -/
theorem top_eq_bot_of_hnot_monotone {α : Type u} [HeytingAlgebra α]
    (mono : Monotone fun a : α => a ⇨ ⊥) : (⊤ : α) = ⊥ := by
  have := mono (bot_le : (⊥ : α) ≤ ⊤)
  simp only [bot_himp, top_himp] at this
  exact le_bot_iff.1 this

theorem hnot_not_monotone {α : Type u} [HeytingAlgebra α] [Nontrivial α] :
    ¬ Monotone fun a : α => a ⇨ ⊥ :=
  fun mono => top_ne_bot (top_eq_bot_of_hnot_monotone mono)

/-- **On PLN's evidence frame, intuitionistic negation is not monotone.** -/
theorem binaryEvidence_hnot_not_monotone :
    ¬ Monotone fun a : Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence => a ⇨ ⊥ := by
  intro mono
  have collapse := top_eq_bot_of_hnot_monotone mono
  have high : (⟨1, 0⟩ : Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence) ≤ ⊥ :=
    collapse ▸ le_top
  have low : (⊥ : Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence) ≤ ⟨0, 0⟩ := bot_le
  have := ((Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence.le_def _ _).1
    (high.trans low)).1
  exact absurd this (by norm_num)

end Negation

/-! ## The credal readout -/

section Credal

open Mettapedia.ProbabilityTheory.ImpreciseProbability.WalleyBinaryIDM

/-- **No evidence, no information**: the imprecise Dirichlet interval of zero
counts is `[0, 1]`, undetermined, not strength `0`. -/
theorem idm_vacuous {s : ℝ} (hs : 0 < s) : lowerEndpoint 0 0 s = 0 ∧ upperEndpoint 0 0 s = 1 := by
  constructor
  · simp [lowerEndpoint]
  · simp [upperEndpoint, hs.ne']

/-- **The width is one minus the PLN confidence** `n / (n + s)`. -/
theorem idm_width {pos neg s : ℝ} (total : pos + neg + s ≠ 0) :
    upperEndpoint pos neg s - lowerEndpoint pos neg s = 1 - (pos + neg) / (pos + neg + s) := by
  unfold upperEndpoint lowerEndpoint
  field_simp
  ring

/-- With samples, the interval contains the observed frequency. -/
theorem idm_contains_frequency {pos neg s : ℝ} (hpos : 0 ≤ pos) (hneg : 0 ≤ neg) (hs : 0 < s)
    (some : 0 < pos + neg) :
    lowerEndpoint pos neg s ≤ pos / (pos + neg) ∧ pos / (pos + neg) ≤ upperEndpoint pos neg s := by
  unfold lowerEndpoint upperEndpoint
  constructor
  · exact div_le_div_of_nonneg_left hpos some (by linarith)
  · rw [div_le_div_iff₀ some (by linarith)]
    nlinarith

/-- **Revision moves the interval rather than nesting it**: one negative sample
gives `[0, 1/2]`; a further positive sample gives `[1/3, 2/3]`, whose upper end
is higher. -/
theorem idm_not_nested :
    upperEndpoint 0 1 1 = 1 / 2 ∧ lowerEndpoint 1 1 1 = 1 / 3 ∧ upperEndpoint 1 1 1 = 2 / 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [upperEndpoint, lowerEndpoint]

end Credal

/-! ## PLN deduction under screening off -/

section Deduction

variable {W : Type v}

theorem count_congr (bag : Multiset W) {p q : W → Bool} (same : ∀ w, p w = q w) :
    count bag p = count bag q := by
  have : p = q := funext same
  rw [this]

theorem card_split (bag : Multiset W) (B : W → Bool) :
    Multiset.card bag = count bag B + count bag (fun w => !B w) := by
  induction bag using Multiset.induction_on with
  | empty => simp
  | cons w bag ih =>
      simp only [count, Multiset.countP_cons, Multiset.card_cons] at ih ⊢
      rw [ih]
      cases hB : B w <;> simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, if_true,
        if_false] <;> omega

/-- **PLN deduction is exact under screening off**: if, in the counts of a bag of
worlds, `C` is independent of `A` given `B` and given `¬B`, the frequency of `C`
among the `A`-worlds is the PLN deduction formula in the frequencies. -/
theorem deduction_exact_of_screening (bag : Multiset W) (A B C : W → Bool)
    (screenB : count bag (fun w => A w && B w && C w) * count bag B =
      count bag (fun w => A w && B w) * count bag (fun w => B w && C w))
    (screenNotB : count bag (fun w => A w && !B w && C w) * count bag (fun w => !B w) =
      count bag (fun w => A w && !B w) * count bag (fun w => !B w && C w))
    (hA : count bag A ≠ 0) (hB : count bag B ≠ 0) (hNB : count bag (fun w => !B w) ≠ 0) :
    (count bag (fun w => A w && C w) : ℝ) / count bag A =
      (count bag (fun w => A w && B w) / count bag A : ℝ) *
          (count bag (fun w => B w && C w) / count bag B) +
        (1 - (count bag (fun w => A w && B w) / count bag A : ℝ)) *
          Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction.complementConditionalFromMarginal
            (count bag B / Multiset.card bag) (count bag C / Multiset.card bag)
            (count bag (fun w => B w && C w) / count bag B) := by
  have splitAC : count bag (fun w => A w && C w) =
      count bag (fun w => A w && B w && C w) + count bag (fun w => A w && !B w && C w) := by
    rw [count_split bag (fun w => A w && C w) B]
    congr 1 <;> exact count_congr bag fun w => by cases A w <;> cases B w <;> cases C w <;> rfl
  have splitA := count_split bag A B
  have splitC : count bag C = count bag (fun w => B w && C w) + count bag (fun w => !B w && C w) := by
    rw [count_split bag C B]
    congr 1 <;> exact count_congr bag fun w => by cases B w <;> cases C w <;> rfl
  have card := card_split bag B
  unfold Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction.complementConditionalFromMarginal
  set a := count bag A
  set ab := count bag (fun w => A w && B w)
  set anb := count bag (fun w => A w && !B w)
  set b := count bag B
  set nb := count bag (fun w => !B w)
  set bc := count bag (fun w => B w && C w)
  set nbc := count bag (fun w => !B w && C w)
  set abc := count bag (fun w => A w && B w && C w)
  set anbc := count bag (fun w => A w && !B w && C w)
  set c := count bag C
  set ac := count bag (fun w => A w && C w)
  have rA : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hA
  have rB : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hB
  have rNB : (nb : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hNB
  have rN : (Multiset.card bag : ℝ) ≠ 0 := by
    rw [card]; push_cast; positivity
  have eAC : (ac : ℝ) = abc + anbc := by rw [splitAC]; push_cast; ring
  have eA : (a : ℝ) = ab + anb := by rw [splitA]; push_cast; ring
  have eC : (c : ℝ) = bc + nbc := by rw [splitC]; push_cast; ring
  have eN : (Multiset.card bag : ℝ) = b + nb := by rw [card]; push_cast; ring
  have sB : (abc : ℝ) * b = ab * bc := by exact_mod_cast screenB
  have sNB : (anbc : ℝ) * nb = anb * nbc := by exact_mod_cast screenNotB
  have oneSub : (1 : ℝ) - b / Multiset.card bag = nb / Multiset.card bag := by
    rw [eN] at rN ⊢; field_simp; ring
  have resid : ((c : ℝ) / Multiset.card bag - b / Multiset.card bag * (bc / b)) /
      (1 - b / Multiset.card bag) = nbc / nb := by
    rw [oneSub, eC]
    field_simp
    ring
  rw [resid, eAC]
  have oneSubA : (1 : ℝ) - ab / a = anb / a := by rw [eA] at rA ⊢; field_simp; ring
  rw [oneSubA]
  field_simp
  linear_combination (nb : ℝ) * sB + (b : ℝ) * sNB

end Deduction

/-! ## Conclusion confidence through intervals

A conclusion's confidence is derived in three steps.  Premise evidence becomes a
credal interval (Walley's imprecise Dirichlet model with a declared prior
strength `s`, whose envelope theorem is
`WalleyBinaryIDM.credal_envelope_matches_Walley_ITV_bounds`).  The rule maps the
premise intervals to a conclusion interval, by the map its observation contract
fixes.  The conclusion interval is read as a truth value by a declared selector
for strength and the width-complement chart for confidence, which the Walley
gate forces to be the PLN odds chart
(`PLNConfidenceWeight.EvidenceWeightCoordinate.walley_width_complement_forces_plnOdds`).
-/

section IntervalRoute

open Mettapedia.ProbabilityTheory.ImpreciseProbability.WalleyBinaryIDM
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction

/-- **The width-complement chart** on the unit range: one minus the width. -/
def widthConfidence (lower upper : ℝ) : ℝ := 1 - (upper - lower)

/-- **The evidence weight of an interval**, in units of the prior strength `s`:
the weight `w` with `w / (w + s)` equal to the width-complement confidence. -/
noncomputable def intervalWeight (s lower upper : ℝ) : ℝ :=
  s * (1 - (upper - lower)) / (upper - lower)

/-- **The chart is the PLN odds chart**: the width-complement confidence is
`w / (w + s)` for the interval's evidence weight `w`. -/
theorem widthConfidence_eq_odds {s lower upper : ℝ} (hs : 0 < s) (width : 0 < upper - lower) :
    widthConfidence lower upper =
      intervalWeight s lower upper / (intervalWeight s lower upper + s) := by
  unfold widthConfidence intervalWeight
  have hw : upper - lower ≠ 0 := width.ne'
  have hden : s * (1 - (upper - lower)) / (upper - lower) + s = s / (upper - lower) := by
    field_simp
    ring
  rw [hden]
  field_simp

/-- **Premises read back their own evidence**: the interval of `(n⁺, n⁻)` has
evidence weight `n⁺ + n⁻`. -/
theorem idm_intervalWeight {pos neg s : ℝ} (hs : 0 < s) (hpos : 0 ≤ pos) (hneg : 0 ≤ neg) :
    intervalWeight s (lowerEndpoint pos neg s) (upperEndpoint pos neg s) = pos + neg := by
  unfold intervalWeight lowerEndpoint upperEndpoint
  have hden : pos + neg + s ≠ 0 := by linarith
  have width : (pos + s) / (pos + neg + s) - pos / (pos + neg + s) = s / (pos + neg + s) := by
    field_simp
    ring
  rw [width]
  field_simp
  ring

/-- An affine function on an interval lies between its endpoint values. -/
theorem affine_between {L U x p q : ℝ} (hL : L ≤ x) (hU : x ≤ U) :
    min (p + q * L) (p + q * U) ≤ p + q * x ∧ p + q * x ≤ max (p + q * L) (p + q * U) := by
  rcases le_total 0 q with hq | hq
  · exact ⟨min_le_of_left_le (by nlinarith), le_max_of_le_right (by nlinarith)⟩
  · exact ⟨min_le_of_right_le (by nlinarith), le_max_of_le_left (by nlinarith)⟩

/-- The least value of a function at the four corners of a box. -/
def cornerMin (f : ℝ → ℝ → ℝ) (L₁ U₁ L₂ U₂ : ℝ) : ℝ :=
  min (min (f L₁ L₂) (f L₁ U₂)) (min (f U₁ L₂) (f U₁ U₂))

/-- The greatest value of a function at the four corners of a box. -/
def cornerMax (f : ℝ → ℝ → ℝ) (L₁ U₁ L₂ U₂ : ℝ) : ℝ :=
  max (max (f L₁ L₂) (f L₁ U₂)) (max (f U₁ L₂) (f U₁ U₂))

/-- **A bilinear function on a box lies between its corner values.** -/
theorem bilinear_between_corners {f : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (bilinear : ∀ x y, f x y = a + b * x + c * y + d * x * y)
    {L₁ U₁ L₂ U₂ x y : ℝ} (hx : L₁ ≤ x ∧ x ≤ U₁) (hy : L₂ ≤ y ∧ y ≤ U₂) :
    cornerMin f L₁ U₁ L₂ U₂ ≤ f x y ∧ f x y ≤ cornerMax f L₁ U₁ L₂ U₂ := by
  have inX : ∀ y', min (f L₁ y') (f U₁ y') ≤ f x y' ∧ f x y' ≤ max (f L₁ y') (f U₁ y') := by
    intro y'
    have := affine_between (p := a + c * y') (q := b + d * y') hx.1 hx.2
    simp only [bilinear]
    constructor
    · calc min (a + b * L₁ + c * y' + d * L₁ * y') (a + b * U₁ + c * y' + d * U₁ * y')
          = min (a + c * y' + (b + d * y') * L₁) (a + c * y' + (b + d * y') * U₁) := by
            congr 1 <;> ring
        _ ≤ a + c * y' + (b + d * y') * x := this.1
        _ = a + b * x + c * y' + d * x * y' := by ring
    · calc a + b * x + c * y' + d * x * y' = a + c * y' + (b + d * y') * x := by ring
        _ ≤ max (a + c * y' + (b + d * y') * L₁) (a + c * y' + (b + d * y') * U₁) := this.2
        _ = max (a + b * L₁ + c * y' + d * L₁ * y') (a + b * U₁ + c * y' + d * U₁ * y') := by
            congr 1 <;> ring
  have inY : ∀ x', min (f x' L₂) (f x' U₂) ≤ f x' y ∧ f x' y ≤ max (f x' L₂) (f x' U₂) := by
    intro x'
    have := affine_between (p := a + b * x') (q := c + d * x') hy.1 hy.2
    simp only [bilinear]
    constructor
    · calc min (a + b * x' + c * L₂ + d * x' * L₂) (a + b * x' + c * U₂ + d * x' * U₂)
          = min (a + b * x' + (c + d * x') * L₂) (a + b * x' + (c + d * x') * U₂) := by
            congr 1 <;> ring
        _ ≤ a + b * x' + (c + d * x') * y := this.1
        _ = a + b * x' + c * y + d * x' * y := by ring
    · calc a + b * x' + c * y + d * x' * y = a + b * x' + (c + d * x') * y := by ring
        _ ≤ max (a + b * x' + (c + d * x') * L₂) (a + b * x' + (c + d * x') * U₂) := this.2
        _ = max (a + b * x' + c * L₂ + d * x' * L₂) (a + b * x' + c * U₂ + d * x' * U₂) := by
            congr 1 <;> ring
  obtain ⟨lowX, highX⟩ := inX y
  obtain ⟨lowL, highL⟩ := inY L₁
  obtain ⟨lowU, highU⟩ := inY U₁
  unfold cornerMin cornerMax
  constructor
  · refine le_trans ?_ lowX
    refine le_min ?_ ?_
    · exact (min_le_left _ _).trans lowL
    · exact (min_le_right _ _).trans lowU
  · refine highX.trans (max_le ?_ ?_)
    · exact highL.trans (le_max_left _ _)
    · exact highU.trans (le_max_right _ _)

/-- **Independent conjunction maps intervals to the product interval.** -/
theorem product_interval {L₁ U₁ L₂ U₂ x y : ℝ} (h₁ : 0 ≤ L₁) (h₂ : 0 ≤ L₂)
    (hx : L₁ ≤ x ∧ x ≤ U₁) (hy : L₂ ≤ y ∧ y ≤ U₂) : L₁ * L₂ ≤ x * y ∧ x * y ≤ U₁ * U₂ := by
  constructor
  · exact mul_le_mul hx.1 hy.1 h₂ (h₁.trans hx.1)
  · exact mul_le_mul hx.2 hy.2 (h₂.trans hy.1) ((h₁.trans hx.1).trans hx.2)

/-- **Conjunction on one world maps intervals to the Fréchet interval**: a joint
probability compatible with marginals in the two intervals lies in
`[max 0 (L₁ + L₂ - 1), min U₁ U₂]`. -/
theorem frechet_interval {L₁ U₁ L₂ U₂ a b c : ℝ} (ha : L₁ ≤ a ∧ a ≤ U₁) (hb : L₂ ≤ b ∧ b ≤ U₂)
    (nonneg : 0 ≤ c) (lower : a + b - 1 ≤ c) (left : c ≤ a) (right : c ≤ b) :
    max 0 (L₁ + L₂ - 1) ≤ c ∧ c ≤ min U₁ U₂ :=
  ⟨max_le nonneg (by linarith), le_min (left.trans ha.2) (right.trans hb.2)⟩

/-- **The deduction map under screening off**, with point marginals `p_B`, `p_C`:
`s_AB s_BC + (1 - s_AB) (p_C - p_B s_BC) / (1 - p_B)`. -/
noncomputable def deductionMap (pB pC : ℝ) (x y : ℝ) : ℝ :=
  x * y + (1 - x) * complementConditionalFromMarginal pB pC y

theorem deductionMap_bilinear (pB pC x y : ℝ) :
    deductionMap pB pC x y =
      pC / (1 - pB) + (-(pC / (1 - pB))) * x + (-(pB / (1 - pB))) * y +
        (1 + pB / (1 - pB)) * x * y := by
  unfold deductionMap complementConditionalFromMarginal
  ring

/-- **Deduction maps premise intervals into the corner interval**: when the
strengths of `A → B` and `B → C` lie in their premise intervals, the deduced
strength lies between the least and greatest corner values. -/
theorem deduction_interval {pB pC L₁ U₁ L₂ U₂ x y : ℝ} (hx : L₁ ≤ x ∧ x ≤ U₁)
    (hy : L₂ ≤ y ∧ y ≤ U₂) :
    cornerMin (deductionMap pB pC) L₁ U₁ L₂ U₂ ≤ deductionMap pB pC x y ∧
      deductionMap pB pC x y ≤ cornerMax (deductionMap pB pC) L₁ U₁ L₂ U₂ :=
  bilinear_between_corners (deductionMap_bilinear pB pC) hx hy

/-- **The derived deduction route**: from the evidence of `A → B` and `B → C`,
through their imprecise Dirichlet intervals, to the conclusion interval, its
width-complement confidence and its evidence weight. -/
theorem deduction_confidence_route {s pB pC posAB negAB posBC negBC x y : ℝ}
    (hx : lowerEndpoint posAB negAB s ≤ x ∧ x ≤ upperEndpoint posAB negAB s)
    (hy : lowerEndpoint posBC negBC s ≤ y ∧ y ≤ upperEndpoint posBC negBC s) :
    let lower := cornerMin (deductionMap pB pC) (lowerEndpoint posAB negAB s)
      (upperEndpoint posAB negAB s) (lowerEndpoint posBC negBC s) (upperEndpoint posBC negBC s)
    let upper := cornerMax (deductionMap pB pC) (lowerEndpoint posAB negAB s)
      (upperEndpoint posAB negAB s) (lowerEndpoint posBC negBC s) (upperEndpoint posBC negBC s)
    (lower ≤ deductionMap pB pC x y ∧ deductionMap pB pC x y ≤ upper) ∧
      (0 < s → 0 < upper - lower →
        widthConfidence lower upper =
          intervalWeight s lower upper / (intervalWeight s lower upper + s)) :=
  ⟨deduction_interval hx hy, fun hs width => widthConfidence_eq_odds hs width⟩

/-- **PLN's deduction evidence posits the sum of the premise totals**: whenever
its strength is at most one, its total is `E_AB.total + E_BC.total`. -/
theorem deductionEvidence_total
    (E_AB E_BC : Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence) (pB pC : ENNReal)
    (hAB : E_AB.total ≠ 0) (hBC : E_BC.total ≠ 0) (hpB : pB ≠ 1)
    (le : Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence.deductionStrength
      (Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence.toStrength E_AB)
      (Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence.toStrength E_BC) pB pC ≤ 1) :
    (Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence.deductionEvidence
        E_AB E_BC pB pC hAB hBC hpB).total = E_AB.total + E_BC.total := by
  set strength := Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence.deductionStrength
    (Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence.toStrength E_AB)
    (Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence.toStrength E_BC) pB pC
  set total := E_AB.total + E_BC.total
  have built : Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence.deductionEvidence
      E_AB E_BC pB pC hAB hBC hpB = ⟨strength * total, (1 - strength) * total⟩ := rfl
  rw [built]
  change strength * total + (1 - strength) * total = total
  rw [← add_mul, add_tsub_cancel_of_le le, one_mul]

end IntervalRoute

/-! ## Controls -/

namespace Controls

open Mettapedia.PLN.Evidence.EvidenceQuantale

/-- **Additive revision of overlapping ledgers double counts**: two ledgers
sharing one positive observation. -/
theorem overlap_double_counted :
    ledgerEvidence (fun _ : Fin 3 => ()) (fun _ => true) {0, 1} +
        ledgerEvidence (fun _ : Fin 3 => ()) (fun _ => true) {1, 2} = ⟨4, 0⟩ ∧
      ledgerEvidence (fun _ : Fin 3 => ()) (fun _ => true) ({0, 1} ∪ {1, 2}) = ⟨3, 0⟩ := by
  constructor <;> ext <;> decide

/-- **The two ends of the overlap interval are attained**: two ledgers with the
same evidence, one positive sample each, merge to two samples when disjoint and
to one when they record the same observation. -/
theorem overlap_interval_ends :
    ledgerEvidence (fun _ : Fin 2 => ()) (fun _ => true) {0} = ⟨1, 0⟩ ∧
      ledgerEvidence (fun _ : Fin 2 => ()) (fun _ => true) {1} = ⟨1, 0⟩ ∧
      ledgerEvidence (fun _ : Fin 2 => ()) (fun _ => true) ({0} ∪ {1}) = ⟨2, 0⟩ ∧
      ledgerEvidence (fun _ : Fin 2 => ()) (fun _ => true) ({0} ∪ {0}) = ⟨1, 0⟩ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext <;> decide

/-- **Source-keyed maximum under-counts without nesting**: one source, two
replicas each holding a different positive observation of it. -/
theorem sourceMerge_undercounts :
    ledgerEvidence (fun _ : Fin 2 => ()) (fun _ => true) ({0} ∪ {1}) = ⟨2, 0⟩ ∧
      sourceReadout (sourceMerge
        (fun src : Unit => ledgerEvidence (fun _ : Fin 2 => ()) (fun _ => true)
          (bySource (fun _ => ()) {0} src))
        (fun src : Unit => ledgerEvidence (fun _ : Fin 2 => ()) (fun _ => true)
          (bySource (fun _ => ()) {1} src))) = ⟨1, 0⟩ := by
  constructor <;> ext <;> decide

/-- Uninformative reports. -/
def coinReport : Bool → Bool → ℚ := fun _ _ => 1 / 2

/-- A non-uniform prior. -/
def skewedPrior : Bool → ℚ := fun h => if h then 3 / 4 else 1 / 4

/-- **Fusing two posteriors counts the prior twice**: with uninformative reports
the posterior is the prior `3/4`, while the fused strength is `9/10`. -/
theorem prior_counted_twice :
    strength (jointReport skewedPrior coinReport coinReport) = 3 / 4 ∧
      strength (fuse (firstReport skewedPrior coinReport coinReport)
        (secondReport skewedPrior coinReport coinReport)) = 9 / 10 := by
  constructor <;>
    norm_num [strength, total, fuse, firstReport, secondReport, jointReport, testimony, ciJoint,
      skewedPrior, coinReport]

/-- **The tensor is not the deduction direct path**: on two half-strength
premises fused evidence has strength `1/2`, while the paired product has the
direct-path strength `s_AB · s_BC = 1/4`. -/
theorem fuse_not_direct_path :
    strength (fuse (⟨1, 1⟩ : Evidence ℚ) ⟨1, 1⟩) = 1 / 2 ∧
      strength ((⟨1, 1⟩ : Evidence ℚ) * ⟨1, 1⟩) = 1 / 4 := by
  constructor
  · norm_num [strength, total, fuse]
  · rw [strength_mul]
    norm_num [strength, total]

/-- **Total conflict leaves the readout undetermined.** -/
theorem total_conflict_undetermined : readout (fuse (⟨1, 0⟩ : Evidence ℚ) ⟨0, 1⟩) = none := by
  rw [fuse_total_conflict]
  exact readout_zero

/-- Three binary features of a world. -/
abbrev World3 := Bool × Bool × Bool

/-- Four worlds in which `C` is not screened off from `A` by `B`. -/
def unscreened : Multiset World3 :=
  {(true, true, false), (false, true, true), (false, false, false), (true, false, false)}

/-- **Without screening off the deduction formula fails**: the formula gives
`1/4`, while no `A`-world has `C`. -/
theorem deduction_fails_without_screening :
    count unscreened (fun w => w.1 && w.2.2) = 0 ∧
      ((count unscreened (fun w => w.1 && w.2.1) / count unscreened (fun w => w.1) : ℝ) *
          (count unscreened (fun w => w.2.1 && w.2.2) / count unscreened (fun w => w.2.1)) +
        (1 - (count unscreened (fun w => w.1 && w.2.1) / count unscreened (fun w => w.1) : ℝ)) *
          Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction.complementConditionalFromMarginal
            (count unscreened (fun w => w.2.1) / Multiset.card unscreened)
            (count unscreened (fun w => w.2.2) / Multiset.card unscreened)
            (count unscreened (fun w => w.2.1 && w.2.2) / count unscreened (fun w => w.2.1))) =
        1 / 4 := by
  have h1 : count unscreened (fun w => w.1 && w.2.2) = 0 := by decide
  have h2 : count unscreened (fun w => w.1 && w.2.1) = 1 := by decide
  have h3 : count unscreened (fun w => w.1) = 2 := by decide
  have h4 : count unscreened (fun w => w.2.1 && w.2.2) = 1 := by decide
  have h5 : count unscreened (fun w => w.2.1) = 2 := by decide
  have h6 : count unscreened (fun w => w.2.2) = 1 := by decide
  have h7 : Multiset.card unscreened = 4 := by decide
  refine ⟨h1, ?_⟩
  rw [h2, h3, h4, h5, h6, h7]
  unfold Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction.complementConditionalFromMarginal
  norm_num

/-! ### Canaries for the interval route -/

open Mettapedia.ProbabilityTheory.ImpreciseProbability.WalleyBinaryIDM

/-- One sample each way with prior strength `1` gives the interval `[1/3, 2/3]`. -/
theorem idm_one_one : lowerEndpoint 1 1 1 = 1 / 3 ∧ upperEndpoint 1 1 1 = 2 / 3 := by
  constructor <;> norm_num [lowerEndpoint, upperEndpoint]

/-- **Independent conjunction through intervals**: premises `(1, 1)` and `(1, 1)`
give the product interval `[1/9, 4/9]`, confidence `2/3` and weight `2`.  The
tree's weight-product conjunction gives confidence `4/5`, the paired total `4`. -/
theorem conjunction_through_intervals :
    widthConfidence ((1 / 3) * (1 / 3)) ((2 / 3) * (2 / 3)) = 2 / 3 ∧
      intervalWeight 1 ((1 / 3) * (1 / 3)) ((2 / 3) * (2 / 3)) = 2 ∧
      (Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthConjunctionIndependentEvidenceStyle
        ⟨1 / 2, 2 / 3⟩ ⟨1 / 2, 2 / 3⟩).c = 4 / 5 := by
  refine ⟨by norm_num [widthConfidence], by norm_num [intervalWeight], ?_⟩
  simp only [Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthConjunctionIndependent_conf_eq,
    Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.c2w,
    Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.w2c,
    Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.capConf,
    Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.MAX_CONF]
  norm_num [min_def, max_def]

/-- **Conjunction on one world through intervals**: the same premises give the
Fréchet interval `[0, 2/3]`, confidence `1/3` and weight `1/2`. -/
theorem frechet_through_intervals :
    max 0 ((1 : ℝ) / 3 + 1 / 3 - 1) = 0 ∧ min ((2 : ℝ) / 3) (2 / 3) = 2 / 3 ∧
      widthConfidence 0 (2 / 3) = 1 / 3 ∧ intervalWeight 1 0 (2 / 3) = 1 / 2 := by
  refine ⟨by norm_num, by norm_num, by norm_num [widthConfidence], by norm_num [intervalWeight]⟩

/-- **Deduction through intervals, where the posited total overstates**: premises
`(1, 1)` and `(1, 1)`, marginals `p_B = p_C = 0`.  The conclusion interval is
`[1/9, 4/9]` with weight `2`, while PLN's deduction evidence posits `2 + 2 = 4`. -/
theorem deduction_posited_overstates :
    cornerMin (deductionMap 0 0) (1 / 3) (2 / 3) (1 / 3) (2 / 3) = 1 / 9 ∧
      cornerMax (deductionMap 0 0) (1 / 3) (2 / 3) (1 / 3) (2 / 3) = 4 / 9 ∧
      intervalWeight 1 (1 / 9) (4 / 9) = 2 ∧
      (⟨1, 1⟩ : BinaryEvidence).total + (⟨1, 1⟩ : BinaryEvidence).total = 4 := by
  refine ⟨?_, ?_, by norm_num [intervalWeight], ?_⟩
  · norm_num [cornerMin, deductionMap,
      Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction.complementConditionalFromMarginal, min_def]
  · norm_num [cornerMax, deductionMap,
      Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction.complementConditionalFromMarginal, max_def]
  · simp only [BinaryEvidence.total]
    norm_num

theorem one_one_total_ne : (⟨1, 1⟩ : BinaryEvidence).total ≠ 0 := by
  simp [BinaryEvidence.total]

/-- **The posited total, on PLN's own definition**: with these premises and
`p_B = p_C = 0`, the deduction evidence of the tree has total `4`. -/
theorem deductionEvidence_posits_four :
    (BinaryEvidence.deductionEvidence ⟨1, 1⟩ ⟨1, 1⟩ 0 0 one_one_total_ne one_one_total_ne
        zero_ne_one).total = 4 := by
  have strengthLe : BinaryEvidence.deductionStrength
      (BinaryEvidence.toStrength ⟨1, 1⟩) (BinaryEvidence.toStrength ⟨1, 1⟩) 0 0 ≤ 1 := by
    have one := BinaryEvidence.toStrength_le_one (⟨1, 1⟩ : BinaryEvidence)
    simp only [BinaryEvidence.deductionStrength, BinaryEvidence.directPathStrength,
      BinaryEvidence.indirectPathStrength, BinaryEvidence.complementStrength, zero_ne_one,
      if_false, zero_mul, tsub_zero, ENNReal.zero_div, mul_zero, add_zero]
    exact mul_le_one' one one
  refine (deductionEvidence_total ⟨1, 1⟩ ⟨1, 1⟩ 0 0 one_one_total_ne one_one_total_ne zero_ne_one
    strengthLe).trans ?_
  simp only [BinaryEvidence.total]
  norm_num

/-- **Deduction through intervals, where the posited total understates**: the
same premises with `p_B = p_C = 1/2` give the interval `[4/9, 5/9]` with weight
`8`, while the posited total is still `4`. -/
theorem deduction_posited_understates :
    cornerMin (deductionMap (1 / 2) (1 / 2)) (1 / 3) (2 / 3) (1 / 3) (2 / 3) = 4 / 9 ∧
      cornerMax (deductionMap (1 / 2) (1 / 2)) (1 / 3) (2 / 3) (1 / 3) (2 / 3) = 5 / 9 ∧
      intervalWeight 1 (4 / 9) (5 / 9) = 8 := by
  refine ⟨?_, ?_, by norm_num [intervalWeight]⟩
  · norm_num [cornerMin, deductionMap,
      Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction.complementConditionalFromMarginal, min_def]
  · norm_num [cornerMax, deductionMap,
      Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction.complementConditionalFromMarginal, max_def]

/-- **Deduction through intervals, where the posited total agrees**: premises
`(0, 2)` and `(1, 2)` with `p_B = p_C = 0` give the interval `[0, 1/6]` with
weight `5`, equal to the posited `2 + 3`. -/
theorem deduction_posited_agrees :
    lowerEndpoint 0 2 1 = 0 ∧ upperEndpoint 0 2 1 = 1 / 3 ∧
      lowerEndpoint 1 2 1 = 1 / 4 ∧ upperEndpoint 1 2 1 = 1 / 2 ∧
      cornerMin (deductionMap 0 0) 0 (1 / 3) (1 / 4) (1 / 2) = 0 ∧
      cornerMax (deductionMap 0 0) 0 (1 / 3) (1 / 4) (1 / 2) = 1 / 6 ∧
      intervalWeight 1 0 (1 / 6) = 5 := by
  refine ⟨by norm_num [lowerEndpoint], by norm_num [upperEndpoint], by norm_num [lowerEndpoint],
    by norm_num [upperEndpoint], ?_, ?_, by norm_num [intervalWeight]⟩
  · norm_num [cornerMin, deductionMap,
      Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction.complementConditionalFromMarginal, min_def]
  · norm_num [cornerMax, deductionMap,
      Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction.complementConditionalFromMarginal, max_def]

/-- No `A`-world has `C`. -/
def unscreenedLow : Multiset World3 :=
  {(true, true, false), (true, false, false), (false, true, true)}

/-- Every `A`-world has `C`. -/
def unscreenedHigh : Multiset World3 :=
  {(true, true, true), (true, false, true), (false, true, false)}

/-- **Without screening off the conclusion interval is vacuous**: two bags agree
on `s_AB = 1/2` and `s_BC = 1/2` while the frequency of `C` among the
`A`-worlds is `0` in one and `1` in the other.  The derived interval is `[0, 1]`
and its width-complement confidence is `0`. -/
theorem unscreened_vacuous :
    (count unscreenedLow (fun w => w.1) = 2 ∧ count unscreenedLow (fun w => w.1 && w.2.1) = 1 ∧
      count unscreenedLow (fun w => w.2.1) = 2 ∧ count unscreenedLow (fun w => w.2.1 && w.2.2) = 1 ∧
      count unscreenedLow (fun w => w.1 && w.2.2) = 0) ∧
    (count unscreenedHigh (fun w => w.1) = 2 ∧ count unscreenedHigh (fun w => w.1 && w.2.1) = 1 ∧
      count unscreenedHigh (fun w => w.2.1) = 2 ∧ count unscreenedHigh (fun w => w.2.1 && w.2.2) = 1 ∧
      count unscreenedHigh (fun w => w.1 && w.2.2) = 2) ∧
    widthConfidence 0 1 = 0 := by
  refine ⟨by decide, by decide, by norm_num [widthConfidence]⟩

end Controls


end Mettapedia.PLN.WorldModel.EvidenceContracts

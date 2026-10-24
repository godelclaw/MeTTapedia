import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mettapedia.ProbabilityTheory.FiniteEventMass
import Mathlib.Combinatorics.SetFamily.Shatter

/-!
# Finite-class learning and candidate refinement

Distributions are Mathlib's finite standard simplex. Samples have product
weights, and hypotheses are Boolean functions. `occam_bound` bounds the chance
of any consistent hypothesis with risk above `ε` by `|H| exp (-ε m)`;
`occam_sample_complexity` gives the corresponding sufficient sample size.

`no_free_lunch_unseen` proves that every learner is wrong on exactly half of
all targets at an unseen point. Through Mathlib's Sauer–Shelah theorem,
`vc_occam_bound` replaces class size by a VC-dimension counting bound over the
whole finite domain; this is not a domain-independent VC sample bound.

The halving learner makes at most `log₂ |H|` mistakes when the target belongs
to the class. Candidate filtering computes `versionSpace` independently of
observation order or repetition; the ordered learner's mistake count need not
share those invariances. Empty classes expose the realizability premise.
-/

set_option autoImplicit false

namespace Mettapedia.LearningTheory

open Finset Classical
open Mettapedia.ProbabilityTheory

variable {Point : Type*}

/-- One observation eliminates precisely the hypotheses that disagree with it. -/
def updateCandidates (hypotheses : Finset (Point → Bool)) (observation : Point × Bool) :=
  hypotheses.filter fun h => h observation.1 == observation.2

/-- The denotational candidate set for an entire observation trace. -/
def versionSpace (hypotheses : Finset (Point → Bool)) (observations : List (Point × Bool)) :=
  hypotheses.filter fun h => observations.all fun e => h e.1 == e.2

theorem foldl_updateCandidates (hypotheses : Finset (Point → Bool))
    (observations : List (Point × Bool)) :
    observations.foldl updateCandidates hypotheses = versionSpace hypotheses observations := by
  induction observations generalizing hypotheses with
  | nil => simp [versionSpace]
  | cons e rest ih =>
      rw [List.foldl_cons, ih]
      ext h
      simp [versionSpace, updateCandidates, and_assoc]

theorem versionSpace_append (hypotheses : Finset (Point → Bool)) (first second : List (Point × Bool)) :
    versionSpace hypotheses (first ++ second) = versionSpace (versionSpace hypotheses first) second := by
  ext h
  simp [versionSpace, and_assoc]

theorem versionSpace_perm (hypotheses : Finset (Point → Bool))
    {first second : List (Point × Bool)} (permutation : first.Perm second) :
    versionSpace hypotheses first = versionSpace hypotheses second := by
  simp_rw [versionSpace, permutation.all_eq]

theorem updateCandidates_commute (hypotheses : Finset (Point → Bool)) (first second : Point × Bool) :
    updateCandidates (updateCandidates hypotheses first) second =
      updateCandidates (updateCandidates hypotheses second) first := by
  ext h
  simp only [updateCandidates, Finset.mem_filter]
  exact and_right_comm

theorem updateCandidates_idempotent (hypotheses : Finset (Point → Bool)) (e : Point × Bool) :
    updateCandidates (updateCandidates hypotheses e) e = updateCandidates hypotheses e := by
  ext h
  simp [updateCandidates]

section FiniteDomain
variable [Fintype Point]

/-- A probability distribution on a finite domain. -/
abbrev Distribution (Point : Type*) [Fintype Point] := ↥(stdSimplex ℝ Point)

/-- The probability of an event. -/
noncomputable def prob (distribution : Distribution Point) (event : Point → Prop) : ℝ :=
  ∑ x, if event x then distribution.1 x else 0

theorem prob_nonneg (distribution : Distribution Point) (event : Point → Prop) :
    0 ≤ prob distribution event :=
  sum_nonneg fun x _ => by split_ifs <;> simp [distribution.2.1 x]

theorem prob_add_prob_not (distribution : Distribution Point) (event : Point → Prop) :
    prob distribution event + prob distribution (fun x => ¬ event x) = 1 := by
  rw [prob, prob, ← sum_add_distrib, ← distribution.2.2]
  exact sum_congr rfl fun x _ => by split_ifs <;> simp_all

/-- The true risk of a hypothesis against a target. -/
noncomputable def risk (distribution : Distribution Point) (hypothesis target : Point → Bool) : ℝ :=
  prob distribution fun x => hypothesis x ≠ target x

/-- The probability of an event about an independent sample of size `m`. -/
noncomputable def sampleProb (distribution : Distribution Point) (m : ℕ)
    (event : (Fin m → Point) → Prop) : ℝ :=
  ∑ sample, if event sample then ∏ i, distribution.1 (sample i) else 0

/-- A hypothesis agrees with the target on every sample point. -/
def Consistent {m : ℕ} (hypothesis target : Point → Bool) (sample : Fin m → Point) : Prop :=
  ∀ i, hypothesis (sample i) = target (sample i)

theorem sampleProb_consistent (distribution : Distribution Point) (m : ℕ)
    (hypothesis target : Point → Bool) :
    sampleProb distribution m (Consistent hypothesis target) =
      (1 - risk distribution hypothesis target) ^ m := by
  have agree : FiniteEventMass.mass distribution.1 (fun x => decide (hypothesis x = target x)) =
      1 - risk distribution hypothesis target := by
    calc
      _ = FiniteEventMass.mass distribution.1 (fun x => !decide (hypothesis x ≠ target x)) :=
        FiniteEventMass.congr _ fun x => by by_cases h : hypothesis x = target x <;> simp [h]
      _ = _ := by
        rw [FiniteEventMass.complement, distribution.2.2]
        congr 1
        exact FiniteEventMass.indicator distribution.1 _ (fun x => hypothesis x ≠ target x)
          (decision := fun _ => Classical.propDecidable _) (fun _ => by simp)
  calc
    _ = FiniteEventMass.mass (fun sample : Fin m → Point => ∏ i, distribution.1 (sample i))
        (fun sample => decide (∀ i, (decide (hypothesis (sample i) = target (sample i))) = true)) :=
      (FiniteEventMass.indicator _ _ _ (fun _ => by simp [Consistent])).symm
    _ = _ := (FiniteEventMass.product_event _ _ m).trans (congrArg (· ^ m) agree)

/-- **Occam bound.** -/
theorem occam_bound (distribution : Distribution Point) [DecidableEq Point]
    (hypotheses : Finset (Point → Bool)) (target : Point → Bool) (ε : ℝ) (m : ℕ) :
    sampleProb distribution m
        (fun sample => ∃ hypothesis ∈ hypotheses, Consistent hypothesis target sample ∧
          ε < risk distribution hypothesis target) ≤
      hypotheses.card * Real.exp (-(ε * m)) := by
  set bad := hypotheses.filter fun hypothesis => ε < risk distribution hypothesis target
  have weight_nonneg : ∀ sample : Fin m → Point, 0 ≤ ∏ i, distribution.1 (sample i) :=
    fun sample => prod_nonneg fun i _ => distribution.2.1 _
  have union : sampleProb distribution m
      (fun sample => ∃ hypothesis ∈ hypotheses, Consistent hypothesis target sample ∧
        ε < risk distribution hypothesis target) ≤
      ∑ hypothesis ∈ bad, sampleProb distribution m (Consistent hypothesis target) := by
    have bound := FiniteEventMass.finset_union_le bad
      (fun sample : Fin m → Point => ∏ i, distribution.1 (sample i)) weight_nonneg
      (fun h sample => decide (Consistent h target sample))
    simpa [FiniteEventMass.mass, sampleProb, bad, and_assoc, and_comm] using bound
  have each : ∀ hypothesis ∈ bad,
      sampleProb distribution m (Consistent hypothesis target) ≤ Real.exp (-(ε * m)) := by
    intro hypothesis member
    rw [sampleProb_consistent]
    have large := (mem_filter.mp member).2
    have lower : 0 ≤ 1 - risk distribution hypothesis target := by
      have := prob_add_prob_not distribution fun x => hypothesis x ≠ target x
      have := prob_nonneg distribution fun x => ¬ hypothesis x ≠ target x
      simp only [risk]; linarith
    calc (1 - risk distribution hypothesis target) ^ m ≤ (1 - ε) ^ m :=
          pow_le_pow_left₀ lower (by linarith) m
      _ ≤ Real.exp (-ε) ^ m := pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg ε) m
      _ = Real.exp (-(ε * m)) := by rw [← Real.exp_nat_mul]; ring_nf
  calc _ ≤ ∑ hypothesis ∈ bad, sampleProb distribution m (Consistent hypothesis target) := union
    _ ≤ ∑ _hypothesis ∈ bad, Real.exp (-(ε * m)) := sum_le_sum each
    _ = bad.card * Real.exp (-(ε * m)) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ hypotheses.card * Real.exp (-(ε * m)) := by
        gcongr
        exact filter_subset _ _

/-- **Sample complexity.**  Enough samples make the Occam bound at most `δ`. -/
theorem occam_sample_complexity (distribution : Distribution Point) [DecidableEq Point]
    (hypotheses : Finset (Point → Bool)) (target : Point → Bool) {ε δ : ℝ}
    (positive : 0 < ε) (confidence : 0 < δ) (nonempty : hypotheses.Nonempty)
    {m : ℕ} (enough : (Real.log hypotheses.card + Real.log (1 / δ)) / ε ≤ m) :
    sampleProb distribution m
        (fun sample => ∃ hypothesis ∈ hypotheses, Consistent hypothesis target sample ∧
          ε < risk distribution hypothesis target) ≤ δ := by
  refine (occam_bound distribution hypotheses target ε m).trans ?_
  have cardPositive : (0 : ℝ) < hypotheses.card := by exact_mod_cast nonempty.card_pos
  have scaled : Real.log hypotheses.card + Real.log (1 / δ) ≤ ε * m := by
    rwa [div_le_iff₀ positive, mul_comm] at enough
  have logBound : Real.log (hypotheses.card * Real.exp (-(ε * m))) ≤ Real.log δ := by
    rw [Real.log_mul cardPositive.ne' (Real.exp_pos _).ne', Real.log_exp,
      one_div, Real.log_inv] at *
    linarith
  exact (Real.log_le_log_iff (mul_pos cardPositive (Real.exp_pos _)) confidence).mp logBound

/-! ## No free lunch -/

/-- A learner maps a labelled sample to a hypothesis. -/
abbrev Learner (Point : Type*) (m : ℕ) := (Fin m → Point × Bool) → Point → Bool

/-- The labelled sample a target produces on given sample points. -/
def label {m : ℕ} (target : Point → Bool) (sample : Fin m → Point) : Fin m → Point × Bool :=
  fun i => (sample i, target (sample i))

/-- **No free lunch on unseen points.**  For any learner, sample points, and a point
the sample does not contain, the learner is wrong at that point for exactly half
of all targets. -/
theorem no_free_lunch_unseen [DecidableEq Point] {m : ℕ} (learner : Learner Point m)
    (sample : Fin m → Point) (unseen : Point) (notSampled : ∀ i, sample i ≠ unseen) :
    2 * (univ.filter fun target : Point → Bool =>
        learner (label target sample) unseen ≠ target unseen).card =
      Fintype.card (Point → Bool) := by
  let flip : (Point → Bool) → (Point → Bool) := fun target => Function.update target unseen (!target unseen)
  have flip_label : ∀ target, label (flip target) sample = label target sample := by
    intro target
    funext i
    simp [label, flip, Function.update_of_ne (notSampled i)]
  have flip_flip : ∀ target, flip (flip target) = target := by
    intro target
    simp [flip, Function.update_idem]
  set wrong := univ.filter fun target : Point → Bool =>
    learner (label target sample) unseen ≠ target unseen
  set right := univ.filter fun target : Point → Bool =>
    ¬ learner (label target sample) unseen ≠ target unseen
  have swap : wrong.card = right.card := by
    apply card_equiv (⟨flip, flip, flip_flip, flip_flip⟩ : (Point → Bool) ≃ (Point → Bool))
    intro target
    change target ∈ wrong ↔ flip target ∈ right
    simp only [wrong, right, mem_filter, mem_univ, true_and]
    rw [flip_label]
    simp only [flip, Function.update_self]
    cases learner (label target sample) unseen <;> cases target unseen <;> decide
  have partition := card_filter_add_card_filter_not
    (s := (univ : Finset (Point → Bool)))
    (fun target : Point → Bool => learner (label target sample) unseen ≠ target unseen)
  rw [card_univ] at partition
  change wrong.card + right.card = Fintype.card (Point → Bool) at partition
  omega

/-! ## VC dimension -/

/-- A hypothesis class as a family of subsets of the domain. -/
noncomputable def classFamily [DecidableEq Point] (hypotheses : Finset (Point → Bool)) :
    Finset (Finset Point) :=
  hypotheses.image fun hypothesis => univ.filter fun x => hypothesis x = true

theorem classFamily_card [DecidableEq Point] (hypotheses : Finset (Point → Bool)) :
    (classFamily hypotheses).card = hypotheses.card := by
  refine card_image_of_injOn fun first _ second _ same => ?_
  funext x
  have := congrArg (fun set : Finset Point => x ∈ set) same
  simp only [mem_filter, mem_univ, true_and, eq_iff_iff] at this
  cases h₁ : first x <;> cases h₂ : second x <;> simp_all

/-- **Sauer–Shelah through Mathlib.**  A class of VC dimension `d` has at most
`∑_{k ≤ d} (n choose k)` members. -/
theorem card_le_sum_vcDim [DecidableEq Point] (hypotheses : Finset (Point → Bool)) :
    hypotheses.card ≤
      ∑ k ∈ Iic (classFamily hypotheses).vcDim, (Fintype.card Point).choose k := by
  rw [← classFamily_card]
  exact (card_le_card_shatterer _).trans card_shatterer_le_sum_vcDim

/-- The Occam bound stated through VC dimension, with the Sauer–Shelah count over
the whole finite domain in place of the class size. -/
theorem vc_occam_bound (distribution : Distribution Point) [DecidableEq Point]
    (hypotheses : Finset (Point → Bool)) (target : Point → Bool) (ε : ℝ) (m : ℕ) :
    sampleProb distribution m
        (fun sample => ∃ hypothesis ∈ hypotheses, Consistent hypothesis target sample ∧
          ε < risk distribution hypothesis target) ≤
      (∑ k ∈ Iic (classFamily hypotheses).vcDim, (Fintype.card Point).choose k : ℕ) *
        Real.exp (-(ε * m)) := by
  refine (occam_bound distribution hypotheses target ε m).trans ?_
  gcongr
  exact_mod_cast card_le_sum_vcDim hypotheses

/-- The two constant hypotheses. -/
def constants : Finset (Point → Bool) := {fun _ => false, fun _ => true}

/-- The constant class has VC dimension at most one. -/
theorem constants_vcDim_le_one [DecidableEq Point] :
    (classFamily (constants : Finset (Point → Bool))).vcDim ≤ 1 := by
  refine Finset.sup_le fun shattered member => ?_
  rw [mem_shatterer] at member
  by_contra small
  have large := not_le.mp small
  obtain ⟨a, aMem, b, bMem, different⟩ := one_lt_card.mp large
  obtain ⟨u, uMem, singleton⟩ := member (singleton_subset_iff.mpr aMem)
  simp only [classFamily, constants, image_insert, image_singleton, mem_insert, mem_singleton]
    at uMem
  rcases uMem with rfl | rfl
  · simp at singleton
  · have := congrArg (fun set : Finset Point => b ∈ set) singleton
    simp [bMem, different.symm] at this

/-- The class of all hypotheses shatters the whole domain. -/
theorem all_shatters_univ [DecidableEq Point] :
    (classFamily (univ : Finset (Point → Bool))).Shatters univ := by
  intro subset _
  refine ⟨subset, ?_, by simp⟩
  simp only [classFamily, mem_image, mem_univ, true_and]
  exact ⟨fun x => decide (x ∈ subset), by ext x; simp⟩

end FiniteDomain

/-! ## Online learning by halving -/

/-- The majority prediction of a set of hypotheses: `true` when strictly more than
half of them say `true`. -/
def majority (hypotheses : Finset (Point → Bool)) (x : Point) : Bool :=
  decide (hypotheses.card < 2 * (hypotheses.filter fun hypothesis => hypothesis x = true).card)

/-- The mistakes the halving learner makes on a sequence of points, starting from a
set of hypotheses and keeping those consistent with each revealed label. -/
def halvingMistakes (target : Point → Bool) :
    Finset (Point → Bool) → List Point → ℕ
  | _, [] => 0
  | hypotheses, x :: rest =>
      (if majority hypotheses x = target x then 0 else 1) +
        halvingMistakes target (hypotheses.filter fun hypothesis => hypothesis x = target x) rest

/-- A mistake leaves at most half of the hypotheses. -/
theorem card_consistent_le_half_of_mistake (hypotheses : Finset (Point → Bool))
    (target : Point → Bool) (x : Point) (mistake : majority hypotheses x ≠ target x) :
    2 * (hypotheses.filter fun hypothesis => hypothesis x = target x).card ≤ hypotheses.card := by
  have partition := card_filter_add_card_filter_not (s := hypotheses)
    (fun hypothesis : Point → Bool => hypothesis x = true)
  cases targetValue : target x with
  | true =>
      rw [targetValue] at mistake
      simp only [majority, ne_eq, decide_eq_true_eq, not_lt] at mistake
      exact mistake
  | false =>
      rw [targetValue] at mistake
      simp only [majority, ne_eq, decide_eq_false_iff_not, not_not] at mistake
      have falseIsNotTrue : (hypotheses.filter fun hypothesis : Point → Bool => hypothesis x = false) =
          hypotheses.filter fun hypothesis => ¬ hypothesis x = true := by
        congr 1
        funext hypothesis
        simp
      rw [falseIsNotTrue]
      omega

/-- **The halving mistake bound.**  When the target is among the hypotheses, two to
the number of mistakes never exceeds the number of hypotheses. -/
theorem halving_mistake_bound (target : Point → Bool) (hypotheses : Finset (Point → Bool))
    (realizable : target ∈ hypotheses) (points : List Point) :
    2 ^ halvingMistakes target hypotheses points ≤ hypotheses.card := by
  induction points generalizing hypotheses with
  | nil => exact card_pos.mpr ⟨target, realizable⟩
  | cons x rest ih =>
      have kept : target ∈ hypotheses.filter fun hypothesis => hypothesis x = target x :=
        mem_filter.mpr ⟨realizable, rfl⟩
      have smaller := ih _ kept
      simp only [halvingMistakes]
      split_ifs with correct
      · simp only [zero_add]
        exact smaller.trans (card_filter_le _ _)
      · rw [add_comm, pow_succ]
        have halved := card_consistent_le_half_of_mistake hypotheses target x correct
        omega

theorem halving_mistakes_le_log (target : Point → Bool) (hypotheses : Finset (Point → Bool))
    (realizable : target ∈ hypotheses) (points : List Point) :
    halvingMistakes target hypotheses points ≤ Nat.log 2 hypotheses.card :=
  Nat.le_log_of_pow_le (by norm_num) (halving_mistake_bound target hypotheses realizable points)

/-- **Realizability is load-bearing.**  With no hypotheses at all, the learner
predicts `false` and errs on every point labeled `true`. -/
theorem halving_without_target (x : Point) :
    halvingMistakes (fun _ => true) ∅ [x, x] = 2 := by
  simp [halvingMistakes, majority]

end Mettapedia.LearningTheory

import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajoritySupport

/-!
# PNP bounded sample-majority combinatorics

Bounded sample index types, sparse override supports, small-subset counting, radius covers, and fallback-family counting lemmas.
-/

namespace Mettapedia.Computability.PNP

universe v

abbrev BoundedSampleIndex (U : Type v) (sampleBound : ℕ) :=
  { sample : Sample U Bool // sample.length ≤ sampleBound }

/-- A bounded sample together with an input-dependent fallback rule.  The
fallback component is itself a full Boolean lookup table on the input surface;
the theorems below make that side-channel explicit. -/
abbrev BoundedSampleFallbackIndex (U : Type v) (sampleBound : ℕ) :=
  (U → Bool) × BoundedSampleIndex U sampleBound

/-- A bounded sample together with a code selecting a fallback rule from a
structured fallback family. -/
abbrev BoundedSampleFallbackFamilyIndex
    (FallbackIndex U : Type v) (sampleBound : ℕ) :=
  FallbackIndex × BoundedSampleIndex U sampleBound

namespace PluginSampleMajority

/-- A bounded sample-level plug-in majority predictor can be false on at most
`sampleBound` inputs. -/
theorem falseSupport_predict_card_le_bound
    {U : Type v} [Fintype U] [DecidableEq U] {sampleBound : ℕ}
    (sample : BoundedSampleIndex U sampleBound) :
    (falseSupport (fun u : U => predict sample.1 u)).card ≤ sampleBound :=
  le_trans (falseSupport_predict_card_le_length sample.1) sample.2

/-- A bounded explicit-default sample-level plug-in majority predictor can
differ from the default on at most `sampleBound` inputs. -/
theorem nondefaultSupport_predictWithDefault_card_le_bound
    {U : Type v} [Fintype U] [DecidableEq U] {sampleBound : ℕ}
    (default : Bool) (sample : BoundedSampleIndex U sampleBound) :
    (nondefaultSupport default
      (fun u : U => predictWithDefault default sample.1 u)).card ≤ sampleBound :=
  le_trans (nondefaultSupport_predictWithDefault_card_le_length default sample.1) sample.2

/-- A bounded input-dependent fallback plug-in majority predictor can differ
from its fallback on at most `sampleBound` inputs. -/
theorem disagreementSupport_predictWithFallback_card_le_bound
    {U : Type v} [Fintype U] [DecidableEq U] {sampleBound : ℕ}
    (fallback : U → Bool) (sample : BoundedSampleIndex U sampleBound) :
    (disagreementSupport fallback
      (fun u : U => predictWithFallback fallback sample.1 u)).card ≤ sampleBound :=
  le_trans (disagreementSupport_predictWithFallback_card_le_length fallback sample.1) sample.2

/-- Flip a Boolean reference rule exactly on a finite set of inputs. -/
noncomputable def flipOn {U : Type v}
    (reference : U → Bool) (s : Finset U) : U → Bool := by
  classical
  exact fun u => if u ∈ s then !reference u else reference u

/-- Small subsets of a finite input alphabet, used to count Hamming balls of
Boolean rules. -/
noncomputable def smallSubsets (U : Type v) [Fintype U] (radius : ℕ) :
    Finset (Finset U) := by
  classical
  exact (Finset.univ : Finset (Finset U)).filter (fun s => s.card ≤ radius)

@[simp] theorem mem_smallSubsets {U : Type v} [Fintype U]
    {radius : ℕ} {s : Finset U} :
    s ∈ smallSubsets U radius ↔ s.card ≤ radius := by
  classical
  simp [smallSubsets]

/-- At radius zero the only allowed sparse override support is the empty set. -/
@[simp] theorem smallSubsets_zero {U : Type v} [Fintype U] :
    smallSubsets U 0 = ({∅} : Finset (Finset U)) := by
  classical
  ext s
  simp [smallSubsets]

/-- There is exactly one radius-zero sparse override support. -/
@[simp] theorem card_smallSubsets_zero {U : Type v} [Fintype U] :
    (smallSubsets U 0).card = 1 := by
  classical
  simp

/-- At radius one the allowed sparse override supports are exactly the empty
set and all singleton supports. -/
theorem smallSubsets_one {U : Type v} [Fintype U] [DecidableEq U] :
    smallSubsets U 1 =
      insert ∅ ((Finset.univ : Finset U).image (fun u => ({u} : Finset U))) := by
  classical
  ext s
  constructor
  · intro hs
    have hcard : s.card ≤ 1 := by
      simpa using
        (mem_smallSubsets (U := U) (radius := 1) (s := s)).1 hs
    by_cases hempty : s = ∅
    · simp [hempty]
    · have hpos : 0 < s.card :=
        Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hempty)
      have hone : s.card = 1 := le_antisymm hcard (Nat.succ_le_of_lt hpos)
      rcases Finset.card_eq_one.mp hone with ⟨u, rfl⟩
      simp
  · intro hs
    rw [mem_smallSubsets]
    rcases Finset.mem_insert.mp hs with hempty | hsingle
    · subst s
      simp
    · rcases Finset.mem_image.mp hsingle with ⟨u, _hu, rfl⟩
      simp

/-- There are exactly `#U + 1` radius-one sparse override supports: the empty
support and one singleton support for each input. -/
@[simp] theorem card_smallSubsets_one {U : Type v} [Fintype U] :
    (smallSubsets U 1).card = Fintype.card U + 1 := by
  classical
  rw [smallSubsets_one]
  have hnot :
      ∅ ∉ ((Finset.univ : Finset U).image (fun u => ({u} : Finset U))) := by
    intro hmem
    rcases Finset.mem_image.mp hmem with ⟨u, _hu, hsingle⟩
    have hcard := congrArg Finset.card hsingle
    simp at hcard
  rw [Finset.card_insert_of_notMem hnot]
  have hinj : Function.Injective (fun u : U => ({u} : Finset U)) := by
    intro u v hsingle
    have hu : u ∈ ({v} : Finset U) := by
      simp [← hsingle]
    simpa using hu
  rw [Finset.card_image_of_injective _ hinj]
  simp

/-- Small subsets are the disjoint union of fixed-cardinality powersets up to
the radius.  This is the exact finite Hamming-ball support partition. -/
theorem smallSubsets_eq_biUnion_powersetCard_range
    {U : Type v} [Fintype U] [DecidableEq U] (radius : ℕ) :
    smallSubsets U radius =
      (Finset.range (radius + 1)).biUnion
        (fun i => (Finset.univ : Finset U).powersetCard i) := by
  classical
  ext s
  constructor
  · intro hs
    have hcard : s.card ≤ radius := by
      simpa using
        (mem_smallSubsets (U := U) (radius := radius) (s := s)).1 hs
    exact Finset.mem_biUnion.mpr
      ⟨s.card, by simpa [Nat.lt_succ_iff] using hcard, by
        rw [Finset.mem_powersetCard]
        exact ⟨by simp, rfl⟩⟩
  · intro hs
    rw [mem_smallSubsets]
    rcases Finset.mem_biUnion.mp hs with ⟨i, hi, hsi⟩
    have hi_le : i ≤ radius := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hcard : s.card = i := (Finset.mem_powersetCard.mp hsi).2
    exact hcard.trans_le hi_le

/-- Exact cardinality of the radius-`radius` sparse support family.  A sampled
override budget of radius `r` buys exactly the finite Hamming-ball support count
`∑ i ≤ r, (#U choose i)`. -/
theorem card_smallSubsets_eq_sum_range_choose
    {U : Type v} [Fintype U] (radius : ℕ) :
    (smallSubsets U radius).card =
      ∑ i ∈ Finset.range (radius + 1), (Fintype.card U).choose i := by
  classical
  rw [smallSubsets_eq_biUnion_powersetCard_range (U := U) radius]
  rw [Finset.card_biUnion]
  · simp [Finset.card_powersetCard]
  · exact ((Finset.univ : Finset U).pairwise_disjoint_powersetCard.set_pairwise _)

/-- Exact cardinality of the two-sample sparse support family.  With at most
two sampled overrides, the support budget is the empty support, one overwritten
input, or an unordered pair of overwritten inputs. -/
@[simp] theorem card_smallSubsets_two
    {U : Type v} [Fintype U] :
    (smallSubsets U 2).card =
      1 + Fintype.card U + (Fintype.card U).choose 2 := by
  rw [card_smallSubsets_eq_sum_range_choose]
  simp [Finset.sum_range_succ, Nat.choose_one_right, Nat.add_assoc]

/-- Coarse polynomial upper bound for the finite Hamming-ball support count.
The `+ 1` in the base makes the statement valid even for empty finite types. -/
theorem sum_range_choose_le_succ_mul_succ_pow (n radius : ℕ) :
    (∑ i ∈ Finset.range (radius + 1), n.choose i) ≤
      (radius + 1) * (n + 1) ^ radius := by
  classical
  calc
    (∑ i ∈ Finset.range (radius + 1), n.choose i) ≤
        ∑ _i ∈ Finset.range (radius + 1), (n + 1) ^ radius := by
      refine Finset.sum_le_sum ?_
      intro i hi
      have hi_le : i ≤ radius := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      calc
        n.choose i ≤ n ^ i := Nat.choose_le_pow n i
        _ ≤ (n + 1) ^ i := Nat.pow_le_pow_left (Nat.le_succ n) i
        _ ≤ (n + 1) ^ radius := Nat.pow_le_pow_right (Nat.succ_pos n) hi_le
    _ = (radius + 1) * (n + 1) ^ radius := by
      simp [Finset.card_range]

/-- Coarse polynomial upper bound for the number of sparse override supports. -/
theorem card_smallSubsets_le_succ_mul_succ_card_pow
    {U : Type v} [Fintype U] (radius : ℕ) :
    (smallSubsets U radius).card ≤
      (radius + 1) * (Fintype.card U + 1) ^ radius := by
  rw [card_smallSubsets_eq_sum_range_choose]
  exact sum_range_choose_le_succ_mul_succ_pow (Fintype.card U) radius

/-- If the sparse support radius is below the finite alphabet size, then the
Hamming-ball support family is a proper subfamily of all finite subsets. -/
theorem smallSubsets_ssubset_univ_of_radius_lt_card
    {U : Type v} [Fintype U] {radius : ℕ}
    (hradius : radius < Fintype.card U) :
    smallSubsets U radius ⊂ (Finset.univ : Finset (Finset U)) := by
  classical
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro s _hs
    simp
  · intro hsmall
    have hmem : (Finset.univ : Finset U) ∈ smallSubsets U radius := by
      rw [hsmall]
      simp
    have hcard :
        Fintype.card U ≤ radius := by
      simpa [Finset.card_univ] using
        (mem_smallSubsets
          (U := U) (radius := radius) (s := (Finset.univ : Finset U))).1 hmem
    exact (not_lt_of_ge hcard) hradius

/-- Strict Hamming-ball support count: below full radius, the sparse support
family is strictly smaller than the full Boolean truth-table cube. -/
theorem card_smallSubsets_lt_twoPow_card_of_radius_lt_card
    {U : Type v} [Fintype U] {radius : ℕ}
    (hradius : radius < Fintype.card U) :
    (smallSubsets U radius).card < 2 ^ Fintype.card U := by
  classical
  have hlt :
      (smallSubsets U radius).card <
        (Finset.univ : Finset (Finset U)).card :=
    Finset.card_lt_card
      (smallSubsets_ssubset_univ_of_radius_lt_card
        (U := U) (radius := radius) hradius)
  simpa [Finset.card_univ, Fintype.card_finset] using hlt

/-- Strict binomial-prefix form of the Hamming-ball support count. -/
theorem sum_range_choose_lt_twoPow_of_lt {n radius : ℕ}
    (hradius : radius < n) :
    (∑ i ∈ Finset.range (radius + 1), n.choose i) < 2 ^ n := by
  classical
  have hlt :=
    card_smallSubsets_lt_twoPow_card_of_radius_lt_card
      (U := Fin n) (radius := radius) (by simpa using hradius)
  simpa [card_smallSubsets_eq_sum_range_choose] using hlt

/-- Bit-cost certificate for the coarse polynomial Hamming-ball envelope.  If
the radius multiplier and input-alphabet base each fit in explicit powers of
two, then the whole envelope fits in their additive exponent budget. -/
theorem succ_mul_succ_pow_le_twoPow_add_mul
    {n radius radiusBits baseBits : ℕ}
    (hradius : radius + 1 ≤ 2 ^ radiusBits)
    (hbase : n + 1 ≤ 2 ^ baseBits) :
    (radius + 1) * (n + 1) ^ radius ≤
      2 ^ (radiusBits + baseBits * radius) := by
  have hpow : (n + 1) ^ radius ≤ (2 ^ baseBits) ^ radius :=
    Nat.pow_le_pow_left hbase radius
  calc
    (radius + 1) * (n + 1) ^ radius ≤
        2 ^ radiusBits * (2 ^ baseBits) ^ radius :=
      Nat.mul_le_mul hradius hpow
    _ = 2 ^ (radiusBits + baseBits * radius) := by
      rw [← pow_mul, ← pow_add]

/-- If a radius is bounded by `2 ^ bits`, then its successor is bounded by the
next power of two.  This is the precise one-bit overhead needed when the
Hamming-ball envelope carries the factor `radius + 1`. -/
theorem succ_le_twoPow_succ_of_le_twoPow {radius bits : ℕ}
    (h : radius ≤ 2 ^ bits) :
    radius + 1 ≤ 2 ^ (bits + 1) := by
  have hsucc : radius + 1 ≤ 2 ^ bits + 1 := Nat.succ_le_succ h
  calc
    radius + 1 ≤ 2 ^ bits + 1 := hsucc
    _ ≤ 2 ^ bits + 2 ^ bits := Nat.add_le_add_left Nat.one_le_two_pow (2 ^ bits)
    _ = 2 ^ (bits + 1) := by
      rw [← Nat.mul_two, ← Nat.pow_succ]

/-- Variant of `succ_mul_succ_pow_le_twoPow_add_mul` for routes that state the
sample radius itself, rather than its successor, as fitting in a bit budget. -/
theorem succ_mul_succ_pow_le_twoPow_succ_add_mul
    {n radius radiusBits baseBits : ℕ}
    (hradius : radius ≤ 2 ^ radiusBits)
    (hbase : n + 1 ≤ 2 ^ baseBits) :
    (radius + 1) * (n + 1) ^ radius ≤
      2 ^ ((radiusBits + 1) + baseBits * radius) :=
  succ_mul_succ_pow_le_twoPow_add_mul
    (radiusBits := radiusBits + 1)
    (succ_le_twoPow_succ_of_le_twoPow hradius) hbase

/-- Flipping a reference rule on `s` creates disagreement support exactly `s`. -/
theorem disagreementSupport_flipOn
    {U : Type v} [Fintype U] (reference : U → Bool) (s : Finset U) :
    disagreementSupport reference (flipOn reference s) = s := by
  classical
  ext u
  by_cases hu : u ∈ s <;> cases reference u <;> simp [disagreementSupport, flipOn, hu]

/-- Any Boolean rule is the reference rule flipped on its disagreement support. -/
theorem flipOn_disagreementSupport_eq
    {U : Type v} [Fintype U] (reference rule : U → Bool) :
    flipOn reference (disagreementSupport reference rule) = rule := by
  classical
  funext u
  by_cases hmem : u ∈ disagreementSupport reference rule
  · have hne : rule u ≠ reference u := by
      simpa using
        (mem_disagreementSupport
          (reference := reference) (rule := rule) (u := u)).1 hmem
    have hflip : Bool.not (reference u) = rule u := by
      cases href : reference u <;> cases hrule : rule u <;> simp [href, hrule] at hne ⊢
    change (if u ∈ disagreementSupport reference rule then Bool.not (reference u) else reference u) =
      rule u
    rw [if_pos hmem]
    exact hflip
  · have hnot : ¬ rule u ≠ reference u := by
      simpa using
        mt
          ((mem_disagreementSupport
            (reference := reference) (rule := rule) (u := u)).2) hmem
    have heq : rule u = reference u := not_not.mp hnot
    change (if u ∈ disagreementSupport reference rule then Bool.not (reference u) else reference u) =
      rule u
    rw [if_neg hmem]
    exact heq.symm

/-- Boolean rules within `radius` point changes of a reference rule. -/
noncomputable def disagreementBall
    {U : Type v} [Fintype U] (reference : U → Bool) (radius : ℕ) :
    Finset (U → Bool) := by
  classical
  exact (Finset.univ : Finset (U → Bool)).filter
    (fun rule => (disagreementSupport reference rule).card ≤ radius)

@[simp] theorem mem_disagreementBall
    {U : Type v} [Fintype U] {reference rule : U → Bool} {radius : ℕ} :
    rule ∈ disagreementBall reference radius ↔
      (disagreementSupport reference rule).card ≤ radius := by
  classical
  simp [disagreementBall]

/-- A Hamming ball is covered by flipping the center on one small subset of
inputs. -/
theorem disagreementBall_subset_image_smallSubsets
    {U : Type v} [Fintype U] (reference : U → Bool) (radius : ℕ) :
    disagreementBall reference radius ⊆
      (smallSubsets U radius).image (flipOn reference) := by
  classical
  intro rule hrule
  have hsmall :
      disagreementSupport reference rule ∈ smallSubsets U radius := by
    simpa using
      (mem_disagreementBall
        (reference := reference) (rule := rule) (radius := radius)).1 hrule
  rw [← flipOn_disagreementSupport_eq reference rule]
  exact Finset.mem_image.mpr ⟨disagreementSupport reference rule, hsmall, rfl⟩

/-- The number of Boolean rules within `radius` point changes of one reference
rule is at most the number of input subsets of size at most `radius`. -/
theorem disagreementBall_card_le_smallSubsets_card
    {U : Type v} [Fintype U] (reference : U → Bool) (radius : ℕ) :
    (disagreementBall reference radius).card ≤ (smallSubsets U radius).card := by
  classical
  calc
    (disagreementBall reference radius).card
        ≤ ((smallSubsets U radius).image (flipOn reference)).card :=
          Finset.card_le_card
            (disagreementBall_subset_image_smallSubsets reference radius)
    _ ≤ (smallSubsets U radius).card := Finset.card_image_le

/-- The union of radius-`radius` Hamming balls around a structured fallback
family. -/
noncomputable def fallbackFamilyRadiusCover
    {FallbackIndex U : Type v} [Fintype FallbackIndex] [Fintype U]
    (fallback : FallbackIndex → U → Bool) (radius : ℕ) :
    Finset (U → Bool) := by
  classical
  exact (Finset.univ : Finset FallbackIndex).biUnion
    (fun code => disagreementBall (fallback code) radius)

@[simp] theorem mem_fallbackFamilyRadiusCover
    {FallbackIndex U : Type v} [Fintype FallbackIndex] [Fintype U]
    {fallback : FallbackIndex → U → Bool} {radius : ℕ} {rule : U → Bool} :
    rule ∈ fallbackFamilyRadiusCover fallback radius ↔
      ∃ code : FallbackIndex,
        (disagreementSupport (fallback code) rule).card ≤ radius := by
  classical
  simp [fallbackFamilyRadiusCover, disagreementBall]

/-- If the radius reaches the whole finite input alphabet, every Boolean rule
lies in the radius cover of any nonempty fallback family.  The membership form
keeps the theorem independent of extra function-space `Fintype` synthesis. -/
theorem mem_fallbackFamilyRadiusCover_of_nonempty_of_card_le_radius
    {FallbackIndex U : Type v} [Fintype FallbackIndex] [Nonempty FallbackIndex]
    [Fintype U] (fallback : FallbackIndex → U → Bool) {radius : ℕ}
    (hcard : Fintype.card U ≤ radius) (rule : U → Bool) :
    rule ∈ fallbackFamilyRadiusCover fallback radius := by
  classical
  exact
    (mem_fallbackFamilyRadiusCover
      (fallback := fallback) (radius := radius) (rule := rule)).2
      ⟨Classical.arbitrary FallbackIndex,
        (disagreementSupport_card_le_card
          (fallback (Classical.arbitrary FallbackIndex)) rule).trans hcard⟩

/-- A finite fallback family plus radius-`radius` sparse overrides covers at
most `#FallbackIndex` times the number of small input subsets. -/
theorem fallbackFamilyRadiusCover_card_le
    {FallbackIndex U : Type v} [Fintype FallbackIndex] [Fintype U]
    (fallback : FallbackIndex → U → Bool) (radius : ℕ) :
    (fallbackFamilyRadiusCover fallback radius).card ≤
      Fintype.card FallbackIndex * (smallSubsets U radius).card := by
  classical
  simpa [fallbackFamilyRadiusCover] using
    Finset.card_biUnion_le_card_mul
      (s := (Finset.univ : Finset FallbackIndex))
      (f := fun code => disagreementBall (fallback code) radius)
      (n := (smallSubsets U radius).card)
      (by
        intro code _hcode
        exact disagreementBall_card_le_smallSubsets_card (fallback code) radius)

/-- If a finite fallback-family radius cover is the whole Boolean rule cube,
then the number of fallback codes times the number of sparse supports must be
at least the full Boolean truth-table count. -/
theorem boolClassifierSpace_card_le_code_mul_smallSubsets_card_of_radiusCover_eq_univ
    {FallbackIndex U : Type v} [Fintype FallbackIndex] [Fintype U] [DecidableEq U]
    (fallback : FallbackIndex → U → Bool) {radius : ℕ}
    (hcover :
      fallbackFamilyRadiusCover fallback radius =
        (Finset.univ : Finset (U → Bool))) :
    2 ^ Fintype.card U ≤
      Fintype.card FallbackIndex * (smallSubsets U radius).card := by
  classical
  calc
    2 ^ Fintype.card U
        = (fallbackFamilyRadiusCover fallback radius).card := by
          rw [hcover]
          simp [Finset.card_univ, card_boolClassifierSpace U]
    _ ≤ Fintype.card FallbackIndex * (smallSubsets U radius).card :=
          fallbackFamilyRadiusCover_card_le fallback radius

/-- If the radius-cover union is smaller than the full Boolean rule space, some
rule is farther than `radius` from every fallback code. -/
theorem exists_rule_forall_radius_lt_disagreementSupport_card_of_radiusCover_card_lt
    {FallbackIndex U : Type v} [Fintype FallbackIndex] [Fintype U]
    (fallback : FallbackIndex → U → Bool) {radius : ℕ}
    (hcard : (fallbackFamilyRadiusCover fallback radius).card < 2 ^ Fintype.card U) :
    ∃ rule : U → Bool,
      ∀ code : FallbackIndex,
        radius < (disagreementSupport (fallback code) rule).card := by
  classical
  have hspace :
      (Finset.univ : Finset (U → Bool)).card = 2 ^ Fintype.card U := by
    simp [Finset.card_univ, card_boolClassifierSpace U]
  have hlt :
      (fallbackFamilyRadiusCover fallback radius).card <
        (Finset.univ : Finset (U → Bool)).card := by
    simpa [hspace] using hcard
  rcases Finset.exists_mem_notMem_of_card_lt_card hlt with ⟨rule, _hrule, hnotmem⟩
  refine ⟨rule, ?_⟩
  intro code
  exact Nat.lt_of_not_ge (by
    intro hle
    exact hnotmem
      ((mem_fallbackFamilyRadiusCover
        (fallback := fallback) (radius := radius) (rule := rule)).2
          ⟨code, hle⟩))

/-- Product-count form of the previous obstruction: if fallback codes times
small override supports are fewer than all Boolean rules, one target rule is
outside every radius ball. -/
theorem exists_rule_forall_radius_lt_disagreementSupport_card_of_code_mul_smallSubsets_card_lt
    {FallbackIndex U : Type v} [Fintype FallbackIndex] [Fintype U]
    (fallback : FallbackIndex → U → Bool) {radius : ℕ}
    (hcard :
      Fintype.card FallbackIndex * (smallSubsets U radius).card <
        2 ^ Fintype.card U) :
    ∃ rule : U → Bool,
      ∀ code : FallbackIndex,
        radius < (disagreementSupport (fallback code) rule).card :=
  exists_rule_forall_radius_lt_disagreementSupport_card_of_radiusCover_card_lt
    fallback
    (lt_of_le_of_lt (fallbackFamilyRadiusCover_card_le fallback radius) hcard)

end PluginSampleMajority

end Mettapedia.Computability.PNP

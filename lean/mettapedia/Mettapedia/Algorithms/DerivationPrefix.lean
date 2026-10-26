import Mettapedia.Algorithms.LazyRankFamilies

/-!
# Truncating child caches for Cartesian derivations

Generic prefix certificates and reconstruction live in `RankedPrefix`.
Here independently valid child prefixes supply distinct cheap replacements
for omitted parent derivations. This proves that bounded child caches suffice
for lazy parent selection; optimality is not assumed as an algorithm premise.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.DerivationPrefix

variable {Value Left Right : Type*}

def product (left : List Left) (right : List Right) : List (Left × Right) :=
  left.flatMap fun first => right.map (first, ·)

@[simp] theorem mem_product (left : List Left) (right : List Right) (pair : Left × Right) :
    pair ∈ product left right ↔ pair.1 ∈ left ∧ pair.2 ∈ right := by
  simp [product, List.mem_flatMap, List.mem_map, Prod.ext_iff]

def pairCost (leftCost : Left → Nat) (rightCost : Right → Nat) (pair : Left × Right) : Nat :=
  leftCost pair.1 + rightCost pair.2

/-- Omission from the truncated Cartesian family yields k distinct retained
parents that cost no more than the omitted independently valid parent. -/
theorem product_dominates (requested : Nat) (positive : 0 < requested)
    (leftCost : Left → Nat) (rightCost : Right → Nat)
    (leftSource : Left → Prop) (rightSource : Right → Prop)
    (left : List Left) (right : List Right)
    (leftValid : Correct requested leftCost leftSource left)
    (rightValid : Correct requested rightCost rightSource right)
    (pair : Left × Right) (allowed : leftSource pair.1 ∧ rightSource pair.2)
    (omitted : pair ∉ product left right) :
    ∃ witnesses : List (Left × Right), witnesses.Nodup ∧ witnesses.length = requested ∧
      witnesses ⊆ product left right ∧
      ∀ witness ∈ witnesses, pairCost leftCost rightCost witness ≤
        pairCost leftCost rightCost pair := by
  classical
  by_cases leftPresent : pair.1 ∈ left
  · have rightMissing : pair.2 ∉ right := fun rightPresent =>
      omitted ((mem_product left right pair).mpr ⟨leftPresent, rightPresent⟩)
    have full := rightValid.omitted pair.2 allowed.2 rightMissing
    exact mapped_witnesses requested (pairCost leftCost rightCost) (· ∈ product left right)
      (pairCost leftCost rightCost pair) right rightValid.distinct full.1 (pair.1, ·)
      (fun first second same => congrArg Prod.snd same)
      (fun other present => (mem_product left right _).mpr ⟨leftPresent, present⟩)
      (fun other present => Nat.add_le_add_left (full.2 other present) _)
  · have full := leftValid.omitted pair.1 allowed.1 leftPresent
    obtain ⟨other, rightPresent, cheaper⟩ :=
      cheap_member requested positive rightCost rightSource right rightValid allowed.2
    exact mapped_witnesses requested (pairCost leftCost rightCost) (· ∈ product left right)
      (pairCost leftCost rightCost pair) left leftValid.distinct full.1 (·, other)
      (fun first second same => congrArg Prod.fst same)
      (fun first present => (mem_product left right _).mpr ⟨present, rightPresent⟩)
      (fun first present => Nat.add_le_add (full.2 first present) cheaper)

/-- A minimum prefix of a retained finite family remains a minimum prefix of
the independent larger source when omitted source members have k cheap
retained witnesses. This is used after lazy rank extraction, not as a premise
that the lazy algorithm is optimal. -/
theorem extend_by_dominance (requested : Nat) (cost : Value → Nat)
    (source retained : Value → Prop) (cached : List Value)
    (valid : Correct requested cost retained cached)
    (retainedSound : ∀ value, retained value → source value)
    (domination : ∀ value, source value → ¬ retained value →
      ∃ witnesses : List Value, witnesses.Nodup ∧ witnesses.length = requested ∧
        (∀ witness ∈ witnesses, retained witness) ∧
        ∀ witness ∈ witnesses, cost witness ≤ cost value) :
    Correct requested cost source cached := by
  classical
  refine ⟨valid.distinct, fun value member => retainedSound value (valid.sound value member),
    valid.ordered, valid.bounded, ?_⟩
  intro value allowed missing
  by_cases retainedValue : retained value
  · exact valid.omitted value retainedValue missing
  · obtain ⟨witnesses, distinct, count, witnessesRetained, witnessesCheap⟩ :=
      domination value allowed retainedValue
    by_cases allSeen : witnesses ⊆ cached
    · have same := (List.subperm_of_subset distinct allSeen).perm_of_length_le
        (valid.bounded.trans_eq count.symm)
      exact ⟨same.length_eq.symm.trans count,
        fun selected member => witnessesCheap selected (same.mem_iff.mpr member)⟩
    · obtain ⟨witness, present, notSeen⟩ : ∃ witness ∈ witnesses, witness ∉ cached := by
        simpa only [List.subset_def, not_forall, exists_prop] using allSeen
      have full := valid.omitted witness (witnessesRetained witness present) notSeen
      exact ⟨full.1, fun selected member =>
        (full.2 selected member).trans (witnessesCheap witness present)⟩

/-- The lazy family algorithm itself constructs a correct complete prefix
over the independently specified rank combinations. -/
theorem rank_prefix_correct (families : List LazyRankFamilies.Family) (requested : Nat) :
    Correct requested (LazyRankFamilies.cost families) (fun _ => True)
      (LazyRankFamilies.completePrefix families requested) := by
  exact graph_prefix_correct (LazyRankFamilies.graph families) (LazyRankFamilies.monotone families)
    (LazyRankFamilies.roots families) (LazyRankFamilies.candidate_reachable families) requested

namespace Controls

def small : List Nat := [0, 1]

theorem smallCorrect : Correct 2 id (fun value => value < 3) small := by
  constructor
  · decide
  · intro value member; simp [small] at member; omega
  · decide
  · decide
  · intro value allowed omitted
    have valueTwo : value = 2 := by simp [small] at omitted; omega
    subst value
    refine ⟨rfl, ?_⟩
    intro selected member
    simp [small] at member
    change selected ≤ 2
    omega

example : ∃ witnesses : List (Nat × Nat), witnesses.Nodup ∧ witnesses.length = 2 ∧
    witnesses ⊆ product small small ∧
    ∀ witness ∈ witnesses, pairCost id id witness ≤ pairCost id id (2, 2) :=
  product_dominates 2 (by decide) id id (fun value => value < 3) (fun value => value < 3)
    small small smallCorrect smallCorrect (2, 2) ⟨by decide, by decide⟩ (by decide)

/-- Parent extraction must retain physical derivations even if their costs
and answer values coincide. -/
example : product [0, 1] [0] = [(0, 0), (1, 0)] := rfl

end Controls

end Mettapedia.Algorithms.DerivationPrefix

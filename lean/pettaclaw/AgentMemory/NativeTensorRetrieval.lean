import Mathlib.Data.Finset.Card

/-!
# Stamped tensor selectors and incremental exact retrieval

This model describes the selector/base/delta composition used by the native
tensor collection. It is not a verification of the C allocator, floating-point
kernels, transport, or compiler. Implementation conformance must additionally
check those boundaries. `RetrievalContract.lean` supplies the general
filter/refine and exact reranking contracts.

The row selector is meaningful only in its admitted source view. Equal shapes
do not establish view compatibility. A changed ID is retired from the base
*before* selection; the delta reads its latest source value. This preserves
updates and deletion even when the base index lags the source. Local top-k
selections suffice as candidates for a final top-k under a common total order.
-/

set_option autoImplicit false

namespace AgentMemory.NativeTensor

inductive Filter (K V : Type*) where
  | all
  | eq (key : K) (value : V)
  | conj (left right : Filter K V)
  | disj (left right : Filter K V)

def evalFilter {K V R : Type*} (fields : K → V → R → Bool) : Filter K V → R → Bool
  | .all, _ => true
  | .eq k v, r => fields k v r
  | .conj a b, r => evalFilter fields a r && evalFilter fields b r
  | .disj a b, r => evalFilter fields a r || evalFilter fields b r

theorem filter_transport {K V R : Type*} (left right : K → V → R → Bool)
    (h : ∀ k v r, left k v r = right k v r) (f : Filter K V) (r : R) :
    evalFilter left f r = evalFilter right f r := by
  induction f with
  | all => rfl
  | eq k v => exact h k v r
  | conj a b ha hb => simp only [evalFilter, ha, hb]
  | disj a b ha hb => simp only [evalFilter, ha, hb]

def checkedMask {K V R : Type*} (expected built : Nat)
    (fields : K → V → R → Bool) (f : Filter K V) : Option (R → Bool) :=
  if expected = built then some (evalFilter fields f) else none

theorem stale_selector_refused {K V R : Type*} (expected built : Nat)
    (fields : K → V → R → Bool) (f : Filter K V) (h : expected ≠ built) :
    checkedMask expected built fields f = none := by
  simp [checkedMask, h]

theorem matching_selector_admitted {K V R : Type*} (stamp : Nat)
    (fields : K → V → R → Bool) (f : Filter K V) :
    checkedMask stamp stamp fields f = some (evalFilter fields f) := by
  simp [checkedMask]

/-- A stamp check establishes identity; posting correctness is a separate
obligation, maintained by construction and cache invalidation. -/
theorem admitted_selector_exact {K V R : Type*} (stamp : Nat)
    (postings source : K → V → R → Bool)
    (h : ∀ k v r, postings k v r = source k v r) (f : Filter K V) :
    checkedMask stamp stamp postings f = some (evalFilter source f) := by
  rw [matching_selector_admitted]
  congr 1
  funext r
  exact filter_transport postings source h f r

theorem same_shape_can_have_different_masks :
    (fun _ : Fin 1 => true) ≠ (fun _ : Fin 1 => false) := by
  intro h
  have bad := congrFun h 0
  contradiction

def enabled {R : Type*} (live selected : R → Bool) (r : R) : Bool := live r && selected r

theorem retired_row_never_enabled {R : Type*} (live selected : R → Bool) (r : R)
    (h : live r = false) : enabled live selected r = false := by
  simp [enabled, h]

theorem enabled_iff {R : Type*} (live selected : R → Bool) (r : R) :
    enabled live selected r = true ↔ live r = true ∧ selected r = true := by
  simp [enabled]

theorem mask_and_truth (a b : Bool) : (a && b) = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem mask_or_truth (a b : Bool) : (a || b) = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> decide

theorem mask_not_truth (a : Bool) : (!a) = true ↔ a = false := by
  cases a <;> decide

theorem mask_not_involution (a : Bool) : !(!a) = a := by
  cases a <;> rfl

def visibleBase {I A : Type*} (base : I → Option A) (dirty : I → Bool) (i : I) : Option A :=
  if dirty i then none else base i

def latestDelta {I A : Type*} (current : I → Option A) (dirty : I → Bool) (i : I) : Option A :=
  if dirty i then current i else none

def merged {I A : Type*} (base current : I → Option A) (dirty : I → Bool) (i : I) : Option A :=
  (visibleBase base dirty i).orElse (fun _ => latestDelta current dirty i)

/-- The invariant is preserved by retiring every written ID, including removed
IDs. Untouched IDs must still equal their admitted base value. -/
theorem base_delta_exact {I A : Type*} (base current : I → Option A) (dirty : I → Bool)
    (clean : ∀ i, dirty i = false → base i = current i) (i : I) :
    merged base current dirty i = current i := by
  cases h : dirty i with
  | false => simp [merged, visibleBase, latestDelta, h, clean i h]
  | true => simp [merged, visibleBase, latestDelta, h]

theorem changed_id_uses_latest {I A : Type*} (base current : I → Option A)
    (dirty : I → Bool) (i : I) (h : dirty i = true) :
    merged base current dirty i = current i := by
  simp [merged, visibleBase, latestDelta, h]

theorem deleted_id_not_resurrected {I A : Type*} (base current : I → Option A)
    (dirty : I → Bool) (i : I) (hd : dirty i = true) (hc : current i = none) :
    merged base current dirty i = none := by
  rw [changed_id_uses_latest base current dirty i hd, hc]

theorem compaction_preserves_view {I A : Type*} (base current : I → Option A)
    (dirty : I → Bool) (clean : ∀ i, dirty i = false → base i = current i) :
    merged current current (fun _ => false) = merged base current dirty := by
  funext i
  rw [base_delta_exact current current (fun _ => false) (fun _ _ => rfl)]
  exact (base_delta_exact base current dirty clean i).symm

def needsCompaction (changed budget : Nat) : Bool := decide (budget ≤ changed)

theorem delta_bounded_without_compaction (changed budget : Nat)
    (h : needsCompaction changed budget = false) : changed < budget := by
  simp only [needsCompaction, decide_eq_false_iff_not, not_le] at h
  exact h

/-- Concrete omission control: taking top-1 and only then dropping a retired
row loses an available answer. Retirement must precede top-k. -/
theorem post_selection_deletion_loses_answer :
    (([0, 1] : List Nat).take 1).filter (fun i => i != 0) = [] ∧
      (([0, 1] : List Nat).filter (fun i => i != 0)).take 1 = [1] := by
  decide

section Ranking

variable {I B : Type*} [DecidableEq I] [LinearOrder B]

/-- `key` includes a stable tie ordinal. Smaller keys rank first. The numerical
score and tie order must agree between the two kernels and the final merge. -/
def rank (key : I → B) (source : Finset I) (i : I) : Nat :=
  (source.filter (fun j => key j < key i)).card

def topK (key : I → B) (k : Nat) (source : Finset I) : Finset I :=
  source.filter (fun i => rank key source i < k)

omit [DecidableEq I] in
theorem rank_mono (key : I → B) {small large : Finset I} (h : small ⊆ large) (i : I) :
    rank key small i ≤ rank key large i := by
  apply Finset.card_le_card
  intro j hj
  rcases Finset.mem_filter.mp hj with ⟨hs, hk⟩
  exact Finset.mem_filter.mpr ⟨h hs, hk⟩

/-- No false dismissal when each partition supplies its local top-k. Exact
reranking of their union is justified by `Retrieval.rerank_exact`. -/
theorem two_top_k_cover (key : I → B) (k : Nat) (base delta : Finset I) :
    topK key k (base ∪ delta) ⊆ topK key k base ∪ topK key k delta := by
  intro i hi
  rcases Finset.mem_filter.mp hi with ⟨hs, hk⟩
  rcases Finset.mem_union.mp hs with hb | hd
  · apply Finset.mem_union_left
    apply Finset.mem_filter.mpr
    exact ⟨hb, lt_of_le_of_lt (rank_mono key Finset.subset_union_left i) hk⟩
  · apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    exact ⟨hd, lt_of_le_of_lt (rank_mono key Finset.subset_union_right i) hk⟩

theorem top_k_candidates_in_source (key : I → B) (k : Nat) (base delta : Finset I) :
    topK key k base ∪ topK key k delta ⊆ base ∪ delta := by
  exact Finset.union_subset_union (Finset.filter_subset _ _) (Finset.filter_subset _ _)

/-- The host-facing result shaping touches at most two kernel selections. -/
theorem shaping_card_bound (k : Nat) (left right : Finset I)
    (hl : left.card ≤ k) (hr : right.card ≤ k) : (left ∪ right).card ≤ k + k :=
  (Finset.card_union_le _ _).trans (Nat.add_le_add hl hr)

end Ranking

end AgentMemory.NativeTensor

import Mettapedia.OSLF.PathMap.PLNBridge
import Mettapedia.PLN.WorldModel.PLNWorldModel
import Mathlib.Data.Multiset.Filter

/-!
# PathMap → BinaryWorldModel Bridge

This module shows how PathMap evidence connects to the `BinaryWorldModel` typeclass
(`PLNWorldModel.lean`) — overcoming the obstacle that `Finset α` union is idempotent.

## The Obstacle

`PathMapWorldModel` (PLNBridge) only guarantees additivity for **disjoint** stores.
`BinaryWorldModel` requires additivity for **all** states.  The gap: `Finset α` union is
idempotent (`W ∪ W = W`), so `ev(W ∪ W, q) = ev(W, q) ≠ ev(W, q) + ev(W, q)`.

## The Fix: `Multiset α`

`Multiset α` is the **free commutative monoid** on `α`: multiset sum `+` is
non-idempotent, so `evidence_add` holds for ALL pairs.

BinaryEvidence extraction counts multiset elements by (non)membership in query `q`:
- `pos = #{elements of m in q}`
- `neg = #{elements of m not in q}`

For a `Finset`-backed store `W`, this recovers `finsetPathEvidence` via the
embedding `Finset.val : Finset α → Multiset α` (see `finset_multiset_evidence_agree`).

## Main results

- `multisetPathWorldModel` — `BinaryWorldModel (Multiset α) (Finset α)` instance
- `finset_multiset_evidence_agree` — embedding compatibility

## Weighted / Finsupp case

For the weighted generalization (`weightedPathEvidence`), the natural state type
is `α →₀ ℝ≥0∞` (finitely-supported weight functions with pointwise `+`).  This
extension is future work; the Multiset case covers the counting evidence.
-/

namespace Mettapedia.OSLF.PathMap.WorldModelBridge

open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.WorldModel.PLNWorldModel
open Mettapedia.OSLF.PathMap.PLNBridge
open scoped ENNReal

/-! ## Section 1: Multiset EvidenceType -/

/-- `Multiset α` is an `EvidenceType` (additive commutative monoid) under multiset sum.
    The `+` operation represents **independent store revision**: combining two independent
    sets of PathMap paths into a single (potentially non-deduplicated) multiset store. -/
instance {α : Type*} : EvidenceType (Multiset α) where
  toAddCommMonoid := inferInstance

/-! ## Section 2: BinaryEvidence Extraction from Multiset -/

/-- BinaryEvidence extraction from a `Multiset α` store for query `q : Finset α`.

    - `pos` = number of elements of `m` lying in `q` (with multiplicity)
    - `neg` = number of elements of `m` not in `q` (with multiplicity)

    For a Finset store W, use `m = W.val` (the underlying nodup multiset). -/
noncomputable def multisetPathEvidence {α : Type*} [DecidableEq α]
    (m : Multiset α) (q : Finset α) : BinaryEvidence :=
  ⟨(m.filter (· ∈ q)).card, (m.filter (· ∉ q)).card⟩

@[simp]
theorem multisetPathEvidence_zero {α : Type*} [DecidableEq α] (q : Finset α) :
    multisetPathEvidence (0 : Multiset α) q = 0 := by
  simp [multisetPathEvidence]; rfl

/-- K&S sum rule: positive and negative counts together equal total multiplicity. -/
theorem multisetPathEvidence_total {α : Type*} [DecidableEq α]
    (m : Multiset α) (q : Finset α) :
    (multisetPathEvidence m q).pos + (multisetPathEvidence m q).neg = m.card := by
  simp only [multisetPathEvidence]
  have h := Multiset.filter_add_not (p := (· ∈ q)) m
  -- h : m.filter (· ∈ q) + m.filter (fun a => ¬a ∈ q) = m
  have hcard : (m.filter (· ∈ q)).card + (m.filter (· ∉ q)).card = m.card := by
    have : m.filter (· ∉ q) = m.filter (fun a => ¬a ∈ q) := rfl
    rw [this, ← Multiset.card_add, h]
  exact_mod_cast hcard

/-! ## Section 3: Additivity — The Key Theorem -/

/-- `multisetPathEvidence` is additive over multiset sum for **all** pairs (not just disjoint).

    This holds because:
    1. `filter p (m₁ + m₂) = filter p m₁ + filter p m₂` (Multiset.filter_add)
    2. `card (s + t) = card s + card t` (Multiset.card_add)

    This is why `Multiset α` works where `Finset α` fails: multiset `+` does not
    deduplicate, so a path that appears in both m₁ and m₂ is counted twice. -/
theorem multisetPathEvidence_additive {α : Type*} [DecidableEq α]
    (m₁ m₂ : Multiset α) (q : Finset α) :
    multisetPathEvidence (m₁ + m₂) q =
    multisetPathEvidence m₁ q + multisetPathEvidence m₂ q := by
  simp only [multisetPathEvidence, BinaryEvidence.hplus_def, BinaryEvidence.mk.injEq]
  constructor
  · -- pos: |filter (·∈q) (m₁+m₂)| = |filter (·∈q) m₁| + |filter (·∈q) m₂|
    rw [Multiset.filter_add]
    exact_mod_cast Multiset.card_add _ _
  · -- neg: |filter (·∉q) (m₁+m₂)| = |filter (·∉q) m₁| + |filter (·∉q) m₂|
    rw [Multiset.filter_add]
    exact_mod_cast Multiset.card_add _ _

/-! ## Section 4: BinaryWorldModel Instance -/

/-- `Multiset α` stores form a full `BinaryWorldModel` — the correct solution to the
    idempotency obstacle that blocks the `Finset α` instance.

    The key difference from `PathMapWorldModel`:
    - `PathMapWorldModel (Finset α)` : additivity only for disjoint stores
    - `BinaryWorldModel (Multiset α)`      : additivity for ALL pairs (free monoid structure) -/
noncomputable instance multisetPathWorldModel {α : Type*} [DecidableEq α] :
    BinaryWorldModel (Multiset α) (Finset α) where
  evidence := multisetPathEvidence
  evidence_add := multisetPathEvidence_additive

/-! ## Section 5: Embedding Finset into the BinaryWorldModel -/

/-- The embedding `Finset.val : Finset α → Multiset α` preserves evidence.
    A Finset store W gives the same evidence whether viewed via `finsetPathEvidence`
    or via the `Multiset BinaryWorldModel`. -/
theorem finset_multiset_evidence_agree {α : Type*} [DecidableEq α]
    (W q : Finset α) :
    multisetPathEvidence W.val q = finsetPathEvidence W q := by
  simp only [multisetPathEvidence, finsetPathEvidence, BinaryEvidence.mk.injEq]
  constructor
  · -- pos: |W.val.filter (·∈q)| = (W ∩ q).card
    have h1 : W.val.filter (· ∈ q) = (W.filter (· ∈ q)).val :=
      (Finset.filter_val _ _).symm
    have h2 : W.filter (· ∈ q) = W ∩ q := by
      ext x; simp [Finset.mem_filter, Finset.mem_inter]
    simp [h1, h2, Finset.card_def]
  · -- neg: |W.val.filter (·∉q)| = (W \ q).card
    have h1 : W.val.filter (· ∉ q) = (W.filter (· ∉ q)).val :=
      (Finset.filter_val _ _).symm
    have h2 : W.filter (· ∉ q) = W \ q := by
      ext x; simp [Finset.mem_filter, Finset.mem_sdiff]
    simp [h1, h2, Finset.card_def]

/-- BinaryWorldModel evidence query for a Finset-backed store equals `finsetPathEvidence`. -/
theorem multisetWorldModel_finset_eq {α : Type*} [DecidableEq α]
    (W q : Finset α) :
    BinaryWorldModel.evidence (State := Multiset α) W.val q = finsetPathEvidence W q :=
  finset_multiset_evidence_agree W q

end Mettapedia.OSLF.PathMap.WorldModelBridge

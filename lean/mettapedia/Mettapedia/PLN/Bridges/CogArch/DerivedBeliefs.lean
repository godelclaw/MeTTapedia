import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.MinMax
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Derived beliefs: deduction, contradiction and withdrawal

WMTM in `bgoertzel-sing/iter` (master `3399366`, live branch `4564185`) runs
two inference engines over its working set. One extracts subject–relation–object
triples from text and applies deduction, induction, abduction, analogy and
noisy-OR aggregation; the other builds PLN atoms with simple truth values and
applies PLN deduction and induction. A contradiction detector reports a
subject and relation with several objects. Each report is resolved by
attention: the item with the highest `sti + utility / 2` wins, the others are
penalized, and with four or more objects they are evicted. On the live
branch only `implies` and `is-a` count as exclusive, and deduction is applied
separately to each of them. Derived items record their direct parents but are
never re-checked against them.

Results:
* `exclusive_closed_trivial`: a relation that is both closed under deduction
  and checked for conflicts can only hold trivial chains. If `a r b` and
  `b r c` hold with `b ≠ c`, deduction adds `a r c` and the checker reports a
  conflict at `a`. `deduction_conflicts_with_premise` is this case for `is-a`
  on the live branch, and `master_flags_consistent_has` shows the master
  branch reporting three compatible `has` facts.
* `premise_evicted_by_own_conclusions`: with four objects the resolver evicts
  every loser. Three valid conclusions of a premise outscore it on attention,
  and the premise itself is evicted. `three_objects_only_penalize`: three
  objects are not enough, because the severity `3 · 0.3` is below `0.9` in
  floating point.
* `resolution_ignores_evidence`: the resolver ranks by attention, so the item
  with more evidence can lose.
* `product_le_cond` and `product_unsound`: the deduction strength
  `s_AB · s_BC` is a lower bound for `P(C | A)` when `P(C | A ∧ B) ≥ P(C | B)`,
  and can exceed `P(C | A)` otherwise. `product_le_independence` shows that it
  never exceeds PLN's independence-based deduction strength.
* `abduction_overstates`, `induction_overstates` and
  `analogy_conflicts_with_premise`: abduction can reach `1` while `P(A | B)`
  is small. The induction expression labeled `Similarity(B, C)` is contrasted
  numerically with `P(C | B)`; no semantics of Similarity is formalized here.
  The analogy rule conflicts with its own premise under the supplied checker.
* `default_deduction_constant`: on the live branch an item without a stored
  truth value gets `(stv 0.8 0.5)`, so every deduction over such items yields
  the same truth value.
* `conclude_holds_iff`, `holds_erase_iff` and `holds_restore`: the union of
  premise supports is contained in the live base exactly when each premise
  support is contained in it. Retracting a base entry invalidates exactly the
  supports that contain it; restoring the entry restores availability. These
  are support-availability laws, not logical truth or inference-soundness laws.
  `orphan_survives_upstream` shows the upstream gap: a derived item outlives
  the premise it was derived from.

A CeTTa-native design declares functional slots instead of exclusive relation
names (the bitemporal model of `BitemporalClaims.lean` gives one value per slot
and event time), resolves conflicts by evidence and time rather than attention,
and stores each derived atom with its rule, premises and support. Retracting a
claim then withdraws its consequences, and their truth values are recomputed
from the evidence that remains.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.Bridges.CogArch.DerivedBeliefs

/-! ## Exclusive relations and transitive deduction -/

/-- A subject–relation–object triple. -/
structure Triple (E R : Type) where
  subj : E
  rel : R
  obj : E
  deriving DecidableEq

section Exclusive

variable {E R : Type}

/-- The upstream contradiction check for relation `r` at subject `a`: two
different objects. -/
def Conflict (T : List (Triple E R)) (r : R) (a : E) : Prop :=
  ∃ b c, ⟨a, r, b⟩ ∈ T ∧ ⟨a, r, c⟩ ∈ T ∧ b ≠ c

/-- Closure under the deduction rule `a r b, b r c ⊢ a r c`. -/
def Closed (T : List (Triple E R)) (r : R) : Prop :=
  ∀ a b c, ⟨a, r, b⟩ ∈ T → ⟨b, r, c⟩ ∈ T → ⟨a, r, c⟩ ∈ T

/-- A relation that is closed under deduction and free of reported conflicts
holds only trivial chains. -/
theorem exclusive_closed_trivial (T : List (Triple E R)) (r : R) (hcl : Closed T r)
    (hnc : ∀ a, ¬ Conflict T r a) :
    ∀ a b c, ⟨a, r, b⟩ ∈ T → ⟨b, r, c⟩ ∈ T → b = c := by
  intro a b c hab hbc
  by_contra hne
  exact hnc a ⟨b, c, hab, hcl a b c hab hbc, hne⟩

end Exclusive

/-- The relations the triple extractor recognizes. -/
inductive Rel
  | implies
  | isA
  | has
  deriving DecidableEq

/-- `a is-a b` and `b is-a c` raise no conflict. After the live branch's own
`is-a` deduction adds `a is-a c`, the checker reports a conflict at `a`. -/
theorem deduction_conflicts_with_premise :
    let T : List (Triple ℕ Rel) := [⟨0, .isA, 1⟩, ⟨1, .isA, 2⟩]
    (∀ a, ¬ Conflict T .isA a) ∧ Conflict (T ++ [⟨0, .isA, 2⟩]) .isA 0 := by
  refine ⟨?_, ⟨1, 2, by simp, by simp, by decide⟩⟩
  rintro a ⟨b, c, hb, hc, hne⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, Triple.mk.injEq] at hb hc
  omega

/-- On the master branch every relation is exclusive, so three compatible
`has` facts about one subject are reported as a conflict. This theorem does
not assert eviction; `three_objects_only_penalize` gives that separate control. -/
theorem master_flags_consistent_has :
    let T : List (Triple ℕ Rel) := [⟨0, .has, 1⟩, ⟨0, .has, 2⟩, ⟨0, .has, 3⟩]
    Conflict T .has 0 := ⟨1, 2, by simp, by simp, by decide⟩

/-- The text engine's analogy rule takes `s₁ r o₁` and `s₂ r o₂` to `s₁ r o₂`.
From `cat is-a mammal` and `rose is-a flower` it derives `cat is-a flower`, which
conflicts with its own premise under the live branch's exclusive `is-a`. -/
theorem analogy_conflicts_with_premise :
    let T : List (Triple ℕ Rel) := [⟨0, .isA, 1⟩, ⟨2, .isA, 3⟩]
    (∀ a, ¬ Conflict T .isA a) ∧ Conflict (T ++ [⟨0, .isA, 3⟩]) .isA 0 := by
  refine ⟨?_, ⟨1, 3, by simp, by simp, by decide⟩⟩
  rintro a ⟨b, c, hb, hc, hne⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, Triple.mk.injEq] at hb hc
  omega

/-! ## Resolution by attention -/

/-- An item in a conflict group: identity, attention and utility in hundredths,
and evidence confidence in tenths. -/
structure Contender where
  id : ℕ
  sti : ℕ
  util : ℕ
  conf : ℕ
  deriving DecidableEq

/-- The resolver's score `sti + utility / 2`, doubled to stay in `ℕ`. -/
def score (x : Contender) : ℕ := 2 * x.sti + x.util

/-- The winner: an item of maximal score, the first one on ties. -/
def winner (g : List Contender) : Option Contender := g.argmax score

/-- Severity is `len(objects) * 0.3`, and the losers are evicted instead of
penalized when it reaches `0.9`. In binary floating point `3 * 0.3` is
`0.8999999999999999`, so eviction starts at four objects. -/
def evicts (objects : ℕ) : Bool := 4 ≤ objects

/-- The items the resolver evicts from a group. -/
def evicted (g : List Contender) (objects : ℕ) : List Contender :=
  if evicts objects then
    match winner g with
    | some w => g.filter (· ≠ w)
    | none => []
  else []

/-- Premises `p implies q` (STI 1) and `q implies r`, `q implies s`,
`q implies t` (STI 10) share the store with five unrelated items of lower STI,
so all four premises are in the inference focus (the upper half by STI).
Deduction yields `p implies r`, `p implies s` and `p implies t`, each with
initial STI `0.64 · (1 + 10) / 2 + 0.5 = 4.02`. The group at `(p, implies)`
has the four objects `q, r, s, t`, and the resolver evicts the premise. -/
theorem premise_evicted_by_own_conclusions :
    let premise : Contender := ⟨1, 100, 0, 5⟩
    let conclusion1 : Contender := ⟨4, 402, 0, 3⟩
    let conclusion2 : Contender := ⟨5, 402, 0, 3⟩
    let conclusion3 : Contender := ⟨6, 402, 0, 3⟩
    premise ∈ evicted [premise, conclusion1, conclusion2, conclusion3] 4 := by
  decide

/-- With three objects the losers are only penalized: nothing is evicted. -/
theorem three_objects_only_penalize (g : List Contender) : evicted g 3 = [] := by
  simp [evicted, evicts]

/-- The resolver ranks by attention: an item with confidence `0.9` loses to an
item with confidence `0.1` and slightly more attention. -/
theorem resolution_ignores_evidence :
    let strong : Contender := ⟨1, 100, 0, 9⟩
    let weak : Contender := ⟨2, 200, 0, 1⟩
    winner [strong, weak] = some weak ∧ weak.conf < strong.conf := by
  decide

/-! ## The deduction strength as a probability bound -/

/-- Conditional frequency `P(Y | X)` on a finite population. -/
def cond (X Y : Finset ℕ) : ℚ := ((X ∩ Y).card : ℚ) / X.card

theorem cond_nonneg (X Y : Finset ℕ) : 0 ≤ cond X Y := by
  unfold cond
  positivity

/-- The product rule `s_AB · s_BC` is a sound lower bound for `P(C | A)` when
learning `A` does not lower the probability of `C` given `B`. -/
theorem product_le_cond (A B C : Finset ℕ) (hAB : (A ∩ B).Nonempty)
    (hM : cond B C ≤ cond (A ∩ B) C) : cond A B * cond B C ≤ cond A C := by
  have hA : A.Nonempty := hAB.mono Finset.inter_subset_left
  have hApos : (0 : ℚ) < A.card := by exact_mod_cast hA.card_pos
  have hABpos : (0 : ℚ) < (A ∩ B).card := by exact_mod_cast hAB.card_pos
  have hsub : A ∩ B ∩ C ⊆ A ∩ C := by
    intro x hx
    simp only [Finset.mem_inter] at hx ⊢
    exact ⟨hx.1.1, hx.2⟩
  have hcard : ((A ∩ B ∩ C).card : ℚ) ≤ (A ∩ C).card := by
    exact_mod_cast Finset.card_le_card hsub
  calc cond A B * cond B C ≤ cond A B * cond (A ∩ B) C :=
        mul_le_mul_of_nonneg_left hM (cond_nonneg A B)
    _ = ((A ∩ B ∩ C).card : ℚ) / A.card := by
        unfold cond
        field_simp
    _ ≤ cond A C := by
        unfold cond
        exact div_le_div_of_nonneg_right hcard hApos.le

/-- Without that condition the product overstates `P(C | A)`: `A` is the one
member of `B` outside `C`. -/
theorem product_unsound :
    let A : Finset ℕ := {9}
    let B : Finset ℕ := Finset.range 10
    let C : Finset ℕ := Finset.range 9
    cond A B = 1 ∧ cond B C = 9 / 10 ∧ cond A C = 0 ∧ cond A C < cond A B * cond B C := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [cond]

/-- PLN's independence-based deduction strength
`s_AB s_BC + (1 - s_AB)(s_C - s_B s_BC)/(1 - s_B)` is never below the product
used by WMTM, for consistent inputs. -/
theorem product_le_independence (sAB sBC sB sC : ℚ) (hAB : sAB ≤ 1) (hB : sB < 1)
    (hcons : sB * sBC ≤ sC) :
    sAB * sBC ≤ sAB * sBC + (1 - sAB) * (sC - sB * sBC) / (1 - sB) := by
  have h1 : 0 ≤ 1 - sAB := by linarith
  have h2 : 0 ≤ sC - sB * sBC := by linarith
  have h3 : 0 < 1 - sB := by linarith
  have : 0 ≤ (1 - sAB) * (sC - sB * sBC) / (1 - sB) := by positivity
  linarith

/-- The abduction strength of the WMTM PLN module, `s_AB · s_B` for `A` given an
observed `B`, can far exceed `P(A | B)`: here it is `1` while `P(A | B) = 1/10`. -/
theorem abduction_overstates :
    let U : Finset ℕ := Finset.range 10
    let A : Finset ℕ := {0}
    let B : Finset ℕ := Finset.range 10
    cond A B * cond U B = 1 ∧ cond B A = 1 / 10 := by
  refine ⟨?_, ?_⟩ <;> simp [cond]

/-- The induction strength of the WMTM PLN module for `Similarity(B, C)` from
`A → B` and `A → C`, `s_AB s_AC + (1 - s_AB)(1 - s_AC)`, is `1` here although
`P(C | B) = 1/3`. -/
theorem induction_overstates :
    let A : Finset ℕ := {0}
    let B : Finset ℕ := {0, 1, 2}
    let C : Finset ℕ := {0, 3, 4}
    cond A B * cond A C + (1 - cond A B) * (1 - cond A C) = 1 ∧ cond B C = 1 / 3 := by
  refine ⟨?_, ?_⟩ <;> simp [cond]

/-- The deduction rule of the WMTM PLN module: strength `s₁ s₂`, confidence
`c₁ c₂ (1 - |s₁ - s₂|)`. -/
def wmtmDeduction (s1 c1 s2 c2 : ℚ) : ℚ × ℚ := (s1 * s2, c1 * c2 * (1 - |s1 - s2|))

/-- Items without a stored truth value receive `(stv 0.8 0.5)` on the live branch,
so every deduction over them yields `(0.64, 0.25)`, whatever the premises. -/
theorem default_deduction_constant :
    wmtmDeduction (4 / 5) (1 / 2) (4 / 5) (1 / 2) = (16 / 25, 1 / 4) := by
  simp [wmtmDeduction]
  norm_num

/-! ## Conclusions that carry their support -/

section Support

variable {B : Type} [DecidableEq B]

/-- The support of a conclusion: the union of its premises' supports. -/
def conclude (ps : List (Finset B)) : Finset B := ps.foldr (· ∪ ·) ∅

/-- A conclusion's union support is available exactly when each premise's
support is available. Logical truth and rule soundness are not modeled here. -/
theorem conclude_holds_iff (live : Finset B) (ps : List (Finset B)) :
    conclude ps ⊆ live ↔ ∀ p ∈ ps, p ⊆ live := by
  induction ps with
  | nil => simp [conclude]
  | cons p ps ih =>
    simp only [conclude, List.foldr_cons, Finset.union_subset_iff, List.mem_cons,
      forall_eq_or_imp] at ih ⊢
    rw [ih]

/-- Retracting a base fact withdraws exactly the conclusions whose support
contains it. -/
theorem holds_erase_iff (live : Finset B) (b : B) (s : Finset B) :
    s ⊆ live.erase b ↔ s ⊆ live ∧ b ∉ s := by
  constructor
  · intro h
    refine ⟨h.trans (Finset.erase_subset b live), fun hb => ?_⟩
    exact (Finset.notMem_erase b live) (h hb)
  · rintro ⟨h, hb⟩ x hx
    exact Finset.mem_erase.mpr ⟨fun hxb => hb (hxb ▸ hx), h hx⟩

/-- Restoring the base entry restores exactly the supports available before. -/
theorem holds_restore (live : Finset B) (b : B) (hb : b ∈ live) (s : Finset B) :
    s ⊆ insert b (live.erase b) ↔ s ⊆ live := by
  rw [Finset.insert_erase hb]

end Support

/-- Upstream, a derived item stays in the store when its premise is evicted: the
store is `[premise, derived]` with the derived item's support `{premise}`. After
evicting the premise the derived item remains, although its support no longer
holds. -/
theorem orphan_survives_upstream :
    let store : List ℕ := [1, 2]
    let support : Finset ℕ := {1}
    2 ∈ store.erase 1 ∧ ¬ support ⊆ ({1, 2} : Finset ℕ).erase 1 := by
  decide

end Mettapedia.PLN.Bridges.CogArch.DerivedBeliefs

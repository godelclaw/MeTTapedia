import Mathlib.Data.List.Range
import Mathlib.Data.List.Pairwise
import Lean.Elab.Tactic.Omega

/-!
# Exact stack transitions for noncrossing involutions

Scan the natural-number positions from left to right. An involution records
paired endpoints; fixed points are unused positions. The stack contains the
earlier endpoints whose partners have not yet been scanned. Noncrossing
makes a closing endpoint remove exactly the top entry, at every width.
-/

namespace Mettapedia.GraphTheory.NoncrossingMatchingStack

/-- The oriented crossing pattern is forbidden. Involutivity supplies the
opposite orientations when this predicate is used for a matching. -/
def Noncrossing (mate : ℕ → ℕ) : Prop :=
  ∀ a b, a < b → b < mate a → mate a < mate b → False

/-- Earlier open endpoints in reverse opening order, top first. -/
def stack (mate : ℕ → ℕ) (cut : ℕ) : List ℕ :=
  (List.range cut).reverse.filter fun j => decide (cut ≤ mate j)

@[simp] theorem mem_stack {mate : ℕ → ℕ} {cut j : ℕ} :
    j ∈ stack mate cut ↔ j < cut ∧ cut ≤ mate j := by
  simp [stack]

@[simp] theorem stack_zero (mate : ℕ → ℕ) : stack mate 0 = [] := by
  simp [stack]

theorem stack_end (mate : ℕ → ℕ) (n : ℕ) (h : ∀ j < n, mate j < n) :
    stack mate n = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro j hj
  obtain ⟨hj, hm⟩ := mem_stack.mp hj
  exact (Nat.not_le_of_gt (h j hj)) hm

theorem stack_descending (mate : ℕ → ℕ) (i : ℕ) :
    (stack mate i).Pairwise (· > ·) :=
  (List.pairwise_reverse.mpr List.pairwise_lt_range).filter _

variable {mate : ℕ → ℕ} (hinv : Function.Involutive mate)
include hinv

theorem mate_eq_iff (i j : ℕ) : mate j = i ↔ j = mate i := by
  constructor
  · intro h
    simpa only [hinv j] using congrArg mate h
  · intro h
    rw [h, hinv]

/-- Before using planarity, advancing the scan deletes the unique possible
closing endpoint and inserts the current endpoint if it opens a chord. -/
theorem stack_advance (i : ℕ) :
    stack mate (i + 1) =
      if i < mate i then i :: (stack mate i).filter (fun j => decide (j ≠ mate i))
      else (stack mate i).filter (fun j => decide (j ≠ mate i)) := by
  have hf : (List.range i).reverse.filter (fun j => decide (i + 1 ≤ mate j)) =
      (stack mate i).filter (fun j => decide (j ≠ mate i)) := by
    unfold stack
    rw [List.filter_filter]
    apply List.filter_congr
    intro j _
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    have he := mate_eq_iff hinv i j
    omega
  change ((List.range (i + 1)).reverse.filter _) = _
  rw [List.range_succ, List.reverse_append]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
    List.filter_cons]
  rw [hf]
  simp only [Nat.add_one_le_iff, decide_eq_true_eq]

theorem stack_fixed (i : ℕ) (hi : mate i = i) : stack mate (i + 1) = stack mate i := by
  rw [stack_advance hinv, hi, ite_eq_right (lt_irrefl i)]
  apply List.filter_eq_self.mpr
  intro j hj
  exact decide_eq_true (by have := (mem_stack.mp hj).1; omega)

theorem stack_open (i : ℕ) (hi : i < mate i) :
    stack mate (i + 1) = i :: stack mate i := by
  rw [stack_advance hinv, ite_eq_left hi]
  congr 1
  apply List.filter_eq_self.mpr
  intro j hj
  exact decide_eq_true (by have := (mem_stack.mp hj).1; omega)

omit hinv in
private theorem descending_max_head {l : List ℕ} {a : ℕ}
    (horder : l.Pairwise (· > ·)) (ha : a ∈ l) (hmax : ∀ b ∈ l, b ≤ a) :
    l = a :: l.filter (fun b => decide (b ≠ a)) := by
  cases l with
  | nil => simp at ha
  | cons b bs =>
    have hba : b = a := by
      have hb := hmax b (by simp)
      rcases List.mem_cons.mp ha with ha | ha
      · exact ha.symm
      · have hl := (List.pairwise_cons.mp horder).1 a ha
        omega
    subst b
    have hf : bs.filter (fun b => decide (b ≠ a)) = bs := by
      apply List.filter_eq_self.mpr
      intro b hb
      have hlt := (List.pairwise_cons.mp horder).1 b hb
      exact decide_eq_true (by omega)
    rw [List.filter_cons_of_neg (by simp), hf]

/-- The partner of a closing endpoint is the latest still-open endpoint.
All other open chords surround this one, so its removal is a literal pop. -/
theorem stack_close (hnc : Noncrossing mate) (i : ℕ) (hi : mate i < i) :
    stack mate i = mate i :: stack mate (i + 1) := by
  have hmem : mate i ∈ stack mate i := mem_stack.mpr ⟨hi, by rw [hinv]⟩
  have hmax : ∀ j ∈ stack mate i, j ≤ mate i := by
    intro j hj
    obtain ⟨hj, hm⟩ := mem_stack.mp hj
    by_contra hn
    have hlt : mate i < j := by omega
    have hne : mate j ≠ i := by
      intro he
      have he' := (mate_eq_iff hinv i j).mp he
      omega
    exact hnc (mate i) j hlt (by simpa only [hinv i] using hj)
      (by simpa only [hinv i] using (show i < mate j by omega))
  rw [stack_advance hinv, ite_eq_right (by omega)]
  exact descending_max_head (stack_descending mate i) hmem hmax

end Mettapedia.GraphTheory.NoncrossingMatchingStack

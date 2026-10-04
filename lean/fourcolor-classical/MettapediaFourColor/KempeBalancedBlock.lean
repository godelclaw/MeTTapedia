import MettapediaFourColor.KempeChromogramMatching
import Mathlib.Order.Preorder.Finite

/-!
# A balanced block either exposes an ear or fixes the entire matching

For a noncrossing perfect matching on twice as many ports as the displayed
initial block, an internal chord supplies an adjacent pair in that block.
If no such pair exists, all chords join the two halves in reverse order.
This dichotomy is uniform in the number of ports.

The repair consumer retains one exterior matching. In the rigid case an
arbitrary finite batch of its prescribed components can be switched before
invoking a compatible continuation.
-/

namespace FourColor.KempeBalancedBlock

open Color KempeIntervalRepair
open Mettapedia.GraphTheory.FourColor.Compositional.CyclicBoundaryMatching

variable {k n : ℕ}

/-- Positive cyclic order of three distinct displayed coordinates. -/
def cyclic {m : ℕ} (a b c : Fin m) : Prop :=
  (a.val < b.val ∧ b.val < c.val) ∨
  (b.val < c.val ∧ c.val < a.val) ∨
  (c.val < a.val ∧ a.val < b.val)

instance {m : ℕ} (a b c : Fin m) : Decidable (cyclic a b c) := by
  unfold cyclic
  infer_instance

theorem crossing_iff_cyclic {m : ℕ} (a b c d : Fin m) :
    ChordsCross a b c d ↔
      (cyclic a c b ∧ cyclic a b d) ∨ (cyclic a d b ∧ cyclic a b c) := by
  unfold ChordsCross cyclic
  omega

/-- Cyclic order on triples suffices to transport noncrossing. -/
theorem noncross_of_cyclic {m : ℕ} (embed : Fin m → Fin n)
    (h : ∀ a b c, cyclic a b c → cyclic (embed a) (embed b) (embed c))
    (a b x y : Fin m) (hc : ¬ ChordsCross (embed a) (embed x) (embed b) (embed y)) :
    ¬ ChordsCross a x b y := by
  intro crossed
  apply hc
  rw [crossing_iff_cyclic] at crossed ⊢
  rcases crossed with ⟨left,right⟩ | ⟨left,right⟩
  · exact Or.inl ⟨h _ _ _ left,h _ _ _ right⟩
  · exact Or.inr ⟨h _ _ _ left,h _ _ _ right⟩

/-- Avoiding every ear in a half-block forces the unique nested matching. -/
theorem ear_or_nested (mate : Fin (2 * k) → Fin (2 * k))
    (hinv : Function.Involutive mate) (hfree : ∀ i, mate i ≠ i)
    (hplanar : IsNoncrossingMatching mate) :
    (∃ i, i.val < k ∧ (mate i).val < k ∧ (mate i).val = i.val + 1) ∨
      ∀ i, mate i = i.rev := by
  classical
  by_cases ear : ∃ i, i.val < k ∧ (mate i).val < k ∧ (mate i).val = i.val + 1
  · exact Or.inl ear
  right
  let block : Finset (Fin (2 * k)) := Finset.univ.filter fun i => i.val < k
  have outside (i : Fin (2 * k)) (hi : i.val < k) : k ≤ (mate i).val := by
    by_contra h
    have inside : (mate i).val < k := by omega
    obtain ⟨j,hj,hm,ha⟩ := exists_adjacent_within mate hinv hfree hplanar block
      (by intro a ha b hb c hac hcb; simp only [block, Finset.mem_filter,
          Finset.mem_univ, true_and] at *; change c.val < b.val at hcb; omega)
      ⟨i,by simpa [block] using hi,by simpa [block] using inside⟩
    exact ear ⟨j,by simpa [block] using hj,by simpa [block] using hm,ha⟩
  let left : Fin k → Fin (2 * k) := fun i => ⟨i.val, by have := i.isLt; omega⟩
  let f : Fin k → Fin k := fun i =>
    ⟨(mate (left i)).val - k, by
      have := (mate (left i)).isLt
      have := outside (left i) i.isLt
      omega⟩
  have anti : StrictAnti f := by
    intro i j hij
    have hi := outside (left i) i.isLt
    have hj := outside (left j) j.isLt
    have ilt := i.isLt
    have jlt := j.isLt
    have ine : (mate (left i)).val ≠ (mate (left j)).val := by
      intro he
      have he := hinv.injective (Fin.ext he)
      have hv := congrArg (fun x : Fin (2 * k) => x.val) he
      have he : i = j := Fin.ext hv
      exact (ne_of_lt hij) he
    have nc := hplanar (left i) (left j)
    unfold ChordsCross at nc
    have li : (left i).val = i.val := rfl
    have lj : (left j).val = j.val := rfl
    have ii : (left i).val ≤ (mate (left i)).val := le_trans (show (left i).val < k from ilt).le hi
    have jj : (left j).val ≤ (mate (left j)).val := le_trans (show (left j).val < k from jlt).le hj
    rw [Nat.min_eq_left ii, Nat.max_eq_right ii,
      Nat.min_eq_left jj, Nat.max_eq_right jj] at nc
    change i.val < j.val at hij
    change (mate (left j)).val - k < (mate (left i)).val - k
    rw [li,lj] at nc
    omega
  have ident : (fun i => (f i).rev) = id := (Fin.rev_strictAnti.comp anti).eq_id
  have first (i : Fin (2 * k)) (hi : i.val < k) : mate i = i.rev := by
    let j : Fin k := ⟨i.val,hi⟩
    have h := congrArg Fin.val (congrFun ident j)
    have ho := outside i hi
    have bound := (mate i).isLt
    have hl : left j = i := Fin.ext rfl
    simp only [id_eq, Fin.val_rev] at h
    change k - ((mate (left j)).val - k + 1) = i.val at h
    rw [hl] at h
    apply Fin.ext
    simp only [Fin.val_rev]
    omega
  intro i
  by_cases hi : i.val < k
  · exact first i hi
  · have hri : i.rev.val < k := by simp only [Fin.val_rev]; have := i.isLt; omega
    have h := first i.rev hri
    rw [Fin.rev_rev] at h
    have h := congrArg mate h
    rw [hinv] at h
    exact h.symm

/-- A fixed list of components in the nested matching, retaining their order. -/
def batch (embed : Fin (2 * k) → Fin n) : List (Fin (2 * k)) → (Fin n → Color) → Fin n → Color
  | [], c => c
  | i :: is, c => batch embed is (switch c (embed i) (embed i.rev))

/-- Either a whole ear component is repaired, or the rigid matching supplies
all components of the given batch in the same exterior. -/
theorem coclosure {P : List Color → Prop} (c : Fin n → Color)
    (embed : Fin (2 * k) → Fin n) (rank : Fin n → Fin (2 * k))
    (hre : ∀ i, rank (embed i) = i)
    (her : ∀ i, c i ≠ c1 → embed (rank i) = i)
    (ha : ∀ i, c (embed i) ≠ c1)
    (horder : ∀ a b x y,
      ¬ ChordsCross (embed a) (embed x) (embed b) (embed y) → ¬ ChordsCross a x b y)
    (ears : ∀ i j, i.val < k → j.val < k → j.val = i.val + 1 →
      KempeCoclosure P (List.ofFn (switch c (embed i) (embed j))))
    (moves : List (Fin (2 * k)))
    (nested : KempeCoclosure P (List.ofFn (batch embed moves c))) :
    KempeCoclosure P (List.ofFn c) := by
  intro outside hout hold
  obtain ⟨_,w,hw,hall⟩ := hout _ hold
  obtain ⟨partner,hi,hn,hf,hs⟩ := KempeChromogramMatching.recover_stable c w hw
  obtain ⟨lift,inv,free⟩ := KempeMajorityRepair.active_mate c partner hi hf
    embed rank hre her ha
  have order : IsNoncrossingMatching (fun i => rank (partner (embed i))) := by
    intro a b
    apply horder a b
    rw [lift,lift]
    exact hn (embed a) (embed b)
  rcases ear_or_nested _ inv free order with ⟨i,hil,hjl,hadj⟩ | rigid
  · have repair := ears i _ hil hjl hadj
    rw [lift] at repair
    exact repair outside hout (hall _ (hs c hw (embed i) (ha i)))
  · have partner_eq (i) : partner (embed i) = embed i.rev := (lift i).symm.trans (congrArg embed (rigid i))
    have accepted (is : List (Fin (2 * k))) (d : Fin n → Color)
        (hd : matchg [] (List.ofFn d) w) : matchg [] (List.ofFn (batch embed is d)) w := by
      induction is generalizing d with
      | nil => exact hd
      | cons i is ih =>
        apply ih
        simpa only [partner_eq] using hs d hd (embed i) (ha i)
    exact nested outside hout (hall _ (accepted moves c hw))

end FourColor.KempeBalancedBlock

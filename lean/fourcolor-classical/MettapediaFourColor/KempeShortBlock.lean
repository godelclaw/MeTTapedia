import MettapediaFourColor.KempeBalancedBlock
import Mathlib.Order.Interval.Finset.Fin

/-!
# A block one port short of half

The complementary block has a majority, so it contains an adjacent matched
pair. Removing that pair leaves equal halves. The balanced-block law then
either supplies an internal ear or determines every remaining component.
-/

namespace FourColor.KempeShortBlock

open Color KempeIntervalRepair
open Mettapedia.GraphTheory.FourColor.Compositional.CyclicBoundaryMatching

variable {k n : ℕ}

/-- Insert a gap of two adjacent ports at the displayed cut. -/
def skip (t : Fin (2 * k + 1)) (i : Fin (2 * k)) : Fin (2 * k + 2) :=
  ⟨if i.val < t.val then i.val else i.val + 2, by
    have := i.isLt
    split_ifs <;> omega⟩

theorem skip_strictMono (t : Fin (2 * k + 1)) : StrictMono (skip t) := by
  intro i j hij
  change i.val < j.val at hij
  change (if i.val < t.val then i.val else i.val + 2) <
    (if j.val < t.val then j.val else j.val + 2)
  split_ifs <;> omega

theorem skip_avoids (t : Fin (2 * k + 1)) (i : Fin (2 * k)) :
    skip t i ≠ t.castSucc ∧ skip t i ≠ t.succ := by
  constructor <;> intro h <;> have h := congrArg Fin.val h <;>
    simp only [skip, Fin.val_castSucc, Fin.val_succ] at h <;> split_ifs at h <;> omega

theorem skip_covers (t : Fin (2 * k + 1)) (v : Fin (2 * k + 2))
    (hl : v ≠ t.castSucc) (hr : v ≠ t.succ) : ∃ i, skip t i = v := by
  have hlv : v.val ≠ t.val := fun h => hl (Fin.ext h)
  have hrv : v.val ≠ t.val + 1 := fun h => hr (Fin.ext h)
  have hv := v.isLt
  have ht := t.isLt
  by_cases h : v.val < t.val
  · refine ⟨⟨v.val, by omega⟩, ?_⟩
    apply Fin.ext
    simp [skip, h]
  · refine ⟨⟨v.val - 2, by omega⟩, ?_⟩
    apply Fin.ext
    change (if v.val - 2 < t.val then v.val - 2 else v.val - 2 + 2) = v.val
    split_ifs <;> omega

theorem skip_cycles (t : Fin (2 * k + 1)) (a b c : Fin (2 * k))
    (h : KempeBalancedBlock.cyclic a b c) :
    KempeBalancedBlock.cyclic (skip t a) (skip t b) (skip t c) := by
  rcases h with ⟨hab,hbc⟩ | ⟨hbc,hca⟩ | ⟨hca,hab⟩
  · exact Or.inl ⟨skip_strictMono t hab, skip_strictMono t hbc⟩
  · exact Or.inr (Or.inl ⟨skip_strictMono t hbc, skip_strictMono t hca⟩)
  · exact Or.inr (Or.inr ⟨skip_strictMono t hca, skip_strictMono t hab⟩)

/-- Deleting a whole component retains an actual noncrossing matching. -/
theorem delete_pair (mate : Fin (2 * k + 2) → Fin (2 * k + 2))
    (hinv : Function.Involutive mate) (hfree : ∀ i, mate i ≠ i)
    (hplanar : IsNoncrossingMatching mate)
    (t : Fin (2 * k + 1)) (hedge : mate t.castSucc = t.succ) :
    ∃ small : Fin (2 * k) → Fin (2 * k),
      (∀ i, skip t (small i) = mate (skip t i)) ∧
      Function.Involutive small ∧ (∀ i, small i ≠ i) ∧ IsNoncrossingMatching small := by
  classical
  have reverse : mate t.succ = t.castSucc := by rw [← hedge, hinv]
  have covered (i) : ∃ j, skip t j = mate (skip t i) := by
    apply skip_covers
    · intro h
      exact (skip_avoids t i).2 (hinv.injective (h.trans reverse.symm))
    · intro h
      exact (skip_avoids t i).1 (hinv.injective (h.trans hedge.symm))
  choose small lift using covered
  refine ⟨small,lift,?_,?_,?_⟩
  · intro i
    apply (skip_strictMono t).injective
    rw [lift, lift, hinv]
  · intro i h
    have he := lift i
    rw [h] at he
    exact hfree _ he.symm
  · intro a b
    apply KempeBalancedBlock.noncross_of_cyclic (skip t) (skip_cycles t)
    rw [lift, lift]
    exact hplanar _ _

/-- Either the short block supplies an ear, or one outside ear determines
the entire remaining matching. The cut is allowed at every outside position. -/
theorem ear_or_punctured (mate : Fin (2 * k + 2) → Fin (2 * k + 2))
    (hinv : Function.Involutive mate) (hfree : ∀ i, mate i ≠ i)
    (hplanar : IsNoncrossingMatching mate) :
    (∃ i, i.val < k ∧ (mate i).val < k ∧ (mate i).val = i.val + 1) ∨
      ∃ t : Fin (2 * k + 1), k ≤ t.val ∧ mate t.castSucc = t.succ ∧
        ∀ i, mate (skip t i) = skip t i.rev := by
  classical
  let first : Fin (2 * k + 2) := ⟨k, by omega⟩
  obtain ⟨v,hv,_,hadj⟩ := exists_adjacent_majority mate hinv hfree hplanar
    (Finset.Ici first)
    (by intro a ha b hb c hac hcb
        exact Finset.mem_Ici.mpr (le_trans (Finset.mem_Ici.mp ha) hac.le))
    (by simp only [Fin.card_Ici]; change 2 * k + 2 < 2 * (2 * k + 2 - k); omega)
  have hk : k ≤ v.val := show first ≤ v from Finset.mem_Ici.mp hv
  have vb := (mate v).isLt
  let t : Fin (2 * k + 1) := ⟨v.val, by omega⟩
  have hedge : mate t.castSucc = t.succ := Fin.ext hadj
  obtain ⟨small,lift,inv,free,planar⟩ := delete_pair mate hinv hfree hplanar t hedge
  rcases KempeBalancedBlock.ear_or_nested small inv free planar with
    ⟨i,hi,hj,hij⟩ | nested
  · left
    have il : i.val < t.val := by change i.val < v.val; omega
    have jl : (small i).val < t.val := by change (small i).val < v.val; omega
    refine ⟨skip t i, ?_, ?_, ?_⟩
    · simpa [skip, il] using hi
    · rw [← lift]; simpa [skip, jl] using hj
    · rw [← lift]; simpa [skip, il, jl] using hij
  · exact Or.inr ⟨t,hk,hedge,fun i => (lift i).symm.trans (congrArg (skip t) (nested i))⟩

/-- `none` selects the deleted pair; `some i` selects a remaining component. -/
def batch (embed : Fin (2 * k + 2) → Fin n) (t : Fin (2 * k + 1)) :
    List (Option (Fin (2 * k))) → (Fin n → Color) → Fin n → Color
  | [], c => c
  | none :: is, c => batch embed t is (switch c (embed t.castSucc) (embed t.succ))
  | some i :: is, c => batch embed t is (switch c (embed (skip t i)) (embed (skip t i.rev)))

/-- Both the removed component and the balanced remainder retain the same
exterior. Their selected switches may be combined before a continuation. -/
theorem coclosure {P : List Color → Prop} (c : Fin n → Color)
    (embed : Fin (2 * k + 2) → Fin n) (rank : Fin n → Fin (2 * k + 2))
    (hre : ∀ i, rank (embed i) = i)
    (her : ∀ i, c i ≠ c1 → embed (rank i) = i)
    (ha : ∀ i, c (embed i) ≠ c1)
    (horder : ∀ a b x y,
      ¬ ChordsCross (embed a) (embed x) (embed b) (embed y) → ¬ ChordsCross a x b y)
    (ears : ∀ i j, i.val < k → j.val < k → j.val = i.val + 1 →
      KempeCoclosure P (List.ofFn (switch c (embed i) (embed j))))
    (moves : Fin (2 * k + 1) → List (Option (Fin (2 * k))))
    (punctured : ∀ t, k ≤ t.val →
      KempeCoclosure P (List.ofFn (batch embed t (moves t) c))) :
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
  rcases ear_or_punctured _ inv free order with ⟨i,hil,hjl,hadj⟩ | ⟨t,ht,gap,rigid⟩
  · have repair := ears i _ hil hjl hadj
    rw [lift] at repair
    exact repair outside hout (hall _ (hs c hw (embed i) (ha i)))
  · have gap_eq : partner (embed t.castSucc) = embed t.succ :=
      (lift _).symm.trans (congrArg embed gap)
    have partner_eq (i) : partner (embed (skip t i)) = embed (skip t i.rev) :=
      (lift _).symm.trans (congrArg embed (rigid i))
    have accepted (is : List (Option (Fin (2 * k)))) (d : Fin n → Color)
        (hd : matchg [] (List.ofFn d) w) : matchg [] (List.ofFn (batch embed t is d)) w := by
      induction is generalizing d with
      | nil => exact hd
      | cons choice is ih =>
        cases choice with
        | none =>
          apply ih
          simpa only [gap_eq] using hs d hd (embed t.castSucc) (ha _)
        | some i =>
          apply ih
          simpa only [partner_eq] using hs d hd (embed (skip t i)) (ha _)
    exact punctured t ht outside hout (hall _ (accepted (moves t) c hw))

end FourColor.KempeShortBlock

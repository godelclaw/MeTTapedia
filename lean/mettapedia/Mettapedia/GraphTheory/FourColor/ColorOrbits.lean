import Mettapedia.GraphTheory.FourColor.ZigzagRingTable
import Mathlib.Data.Fin.VecNotation

/-!
# Colour orbits of zero-sum digit words

Boundary words with digits `0,1,2` for the three nonzero colours; the six
permutations of the digits act; the *key* of a word is the least encoding in
its orbit.  A set of zero-sum words that is closed under the six permutations is
determined by its set of keys (`eq_of_image_key_eq`), so there are at most
`2^(orbitCount k)` such sets, with `orbitCount 5 = 10` and `orbitCount 6 = 31`
checked in the kernel.
-/

namespace Mettapedia.GraphTheory.FourColor
namespace TubeSlab
namespace ColorOrbits

open ZigzagRing

/-- digit words -/
abbrev DWord (k : Nat) := Fin k → Fin 3

/-- the colour sum of a digit word -/
def csum {k : Nat} (w : DWord k) : Color := ∑ i, col (w i).val

/-- the six permutations of the digits, indexed -/
def perm : Fin 6 → Fin 3 → Fin 3 :=
  ![![0, 1, 2], ![0, 2, 1], ![1, 0, 2], ![1, 2, 0], ![2, 0, 1], ![2, 1, 0]]

theorem perm_zero : ∀ i, perm 0 i = i := by decide

theorem perm_comp : ∀ a b : Fin 6, ∃ c : Fin 6, ∀ i, perm c i = perm a (perm b i) := by decide

theorem perm_inv : ∀ a : Fin 6, ∃ b : Fin 6, ∀ i, perm b (perm a i) = i := by decide

/-- the action -/
def act {k : Nat} (a : Fin 6) (w : DWord k) : DWord k := fun i => perm a (w i)

theorem act_zero {k : Nat} (w : DWord k) : act 0 w = w := by
  funext i; exact perm_zero _

/-- injective base-3 encoding -/
def enc {k : Nat} (w : DWord k) : Nat :=
  encB 3 (fun i => if h : i < k then (w ⟨i, h⟩).val else 0) k

theorem enc_inj {k : Nat} {w w' : DWord k} (h : enc w = enc w') : w = w' := by
  funext i
  have hd := congrArg (fun n => digB 3 n i.val) h
  simp only [enc] at hd
  rw [digB_encB (by omega) k (fun j hj => by
        split_ifs <;> first | exact (w _).isLt | omega) i.val i.isLt,
    digB_encB (by omega) k (fun j hj => by
        split_ifs <;> first | exact (w' _).isLt | omega) i.val i.isLt] at hd
  simp only [i.isLt, dite_true] at hd
  exact Fin.ext hd

/-- the encodings in the orbit -/
def orbitEncs {k : Nat} (w : DWord k) : List Nat := (List.finRange 6).map fun a => enc (act a w)

/-- the orbit key: the least encoding in the orbit -/
def key {k : Nat} (w : DWord k) : Nat := (orbitEncs w).foldr min (enc w)

theorem key_mem {k : Nat} (w : DWord k) : ∃ a : Fin 6, key w = enc (act a w) := by
  unfold key orbitEncs
  have : ∀ l : List (Fin 6), ∀ x, (∃ a, x = enc (act a w)) →
      ∃ a, (l.map fun a => enc (act a w)).foldr min x = enc (act a w) := by
    intro l
    induction l with
    | nil => intro x hx; simpa using hx
    | cons a l ih =>
      intro x hx
      obtain ⟨q, hq'⟩ := ih x hx
      simp only [List.map_cons, List.foldr_cons, hq']
      rcases le_total (enc (act a w)) (enc (act q w)) with h | h
      · exact ⟨a, min_eq_left h⟩
      · exact ⟨q, min_eq_right h⟩
  exact this _ (enc w) ⟨0, by rw [act_zero]⟩

theorem key_le {k : Nat} (w : DWord k) (a : Fin 6) : key w ≤ enc (act a w) := by
  unfold key orbitEncs
  have : ∀ (l : List (Fin 6)) x, a ∈ l →
      (l.map fun a => enc (act a w)).foldr min x ≤ enc (act a w) := by
    intro l x hal
    induction l with
    | nil => exact absurd hal List.not_mem_nil
    | cons b l ih =>
      simp only [List.map_cons, List.foldr_cons]
      rcases List.mem_cons.mp hal with rfl | hal'
      · exact min_le_left _ _
      · exact le_trans (min_le_right _ _) (ih hal')
  exact this _ (enc w) (List.mem_finRange a)

/-- keys are orbit invariants -/
theorem key_act {k : Nat} (w : DWord k) (a : Fin 6) : key (act a w) = key w := by
  apply le_antisymm
  · obtain ⟨q, hq'⟩ := key_mem w
    rw [hq']
    obtain ⟨r, hr'⟩ := perm_inv a
    obtain ⟨c, hc⟩ := perm_comp q r
    have : act q w = act c (act a w) := by
      funext i; simp [act, hc, hr']
    rw [this]
    exact key_le _ _
  · obtain ⟨q, hq'⟩ := key_mem (act a w)
    rw [hq']
    obtain ⟨c, hc⟩ := perm_comp q a
    have : act q (act a w) = act c w := by
      funext i; simp [act, hc]
    rw [this]
    exact key_le _ _

/-- equal keys mean the same orbit -/
theorem exists_act_of_key_eq {k : Nat} {w w' : DWord k} (h : key w = key w') :
    ∃ a : Fin 6, act a w = w' := by
  obtain ⟨p, hp'⟩ := key_mem w
  obtain ⟨q, hq'⟩ := key_mem w'
  have he : act p w = act q w' := enc_inj (by rw [← hp', ← hq', h])
  obtain ⟨r, hr'⟩ := perm_inv q
  obtain ⟨c, hc⟩ := perm_comp r p
  refine ⟨c, ?_⟩
  have : act c w = act r (act p w) := by
    funext i; simp [act, hc]
  rw [this, he]
  funext i; simp [act, hr']

/-- **an invariant set of words is determined by its keys** -/
theorem eq_of_image_key_eq {k : Nat} {S S' : Finset (DWord k)}
    (hS : ∀ a : Fin 6, ∀ w ∈ S, act a w ∈ S) (hS' : ∀ a : Fin 6, ∀ w ∈ S', act a w ∈ S')
    (h : S.image key = S'.image key) : S = S' := by
  have aux : ∀ {A B : Finset (DWord k)}, (∀ a : Fin 6, ∀ w ∈ B, act a w ∈ B) →
      A.image key = B.image key → A ⊆ B := by
    intro A B hB hAB w hw
    have : key w ∈ B.image key := hAB ▸ Finset.mem_image_of_mem key hw
    obtain ⟨w', hw', hk⟩ := Finset.mem_image.mp this
    obtain ⟨a, rfl⟩ := exists_act_of_key_eq hk
    exact hB a w' hw'
  exact Finset.Subset.antisymm (aux hS' h) (aux hS h.symm)

/-- zero-sum words, their keys, and the orbit count -/
def zeroSumWords (k : Nat) : Finset (DWord k) := Finset.univ.filter fun w => csum w = 0

def keys (k : Nat) : Finset Nat := (zeroSumWords k).image key

def orbitCount (k : Nat) : Nat := (keys k).card

theorem mem_keys {k : Nat} {w : DWord k} (h : csum w = 0) : key w ∈ keys k :=
  Finset.mem_image_of_mem key (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)

set_option maxRecDepth 100000 in
theorem orbitCount_five : orbitCount 5 = 10 := by decide +kernel

set_option maxRecDepth 100000 in
theorem orbitCount_six : orbitCount 6 = 31 := by decide +kernel

end ColorOrbits
end TubeSlab
end Mettapedia.GraphTheory.FourColor

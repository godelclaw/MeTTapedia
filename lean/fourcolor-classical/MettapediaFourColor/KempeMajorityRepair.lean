import MettapediaFourColor.KempeIntervalRepair
import Mettapedia.GraphTheory.FourColor.Compositional.NoncrossingMatchingEar

/-!
# Adaptive repair from a majority block of active ports

A convex block containing more than half the active ports has an adjacent
pair in every noncrossing component matching. If all adjacent pairs in the
block admit a terminal repair, one of those repairs uses a whole component
of the original exterior. No interval search or matching table is needed.
-/

namespace FourColor.KempeMajorityRepair

open Color KempeMatchingChromogram
open Mettapedia.GraphTheory.FourColor.Compositional.CyclicBoundaryMatching

variable {n m : ℕ}

/-- Removing fixed ports retains each actual component and its inverse. -/
theorem active_mate (c : Fin n → Color) (mate : Fin n → Fin n)
    (hinv : Function.Involutive mate) (hf : ∀ i, mate i = i ↔ c i = c1)
    (embed : Fin m → Fin n) (rank : Fin n → Fin m)
    (hre : ∀ i, rank (embed i) = i)
    (her : ∀ i, c i ≠ c1 → embed (rank i) = i)
    (ha : ∀ i, c (embed i) ≠ c1) :
    let small := fun i => rank (mate (embed i))
    (∀ i, embed (small i) = mate (embed i)) ∧
      Function.Involutive small ∧ ∀ i, small i ≠ i := by
  dsimp only
  have partner (i) : c (mate (embed i)) ≠ c1 := by
    intro h
    have fixed := (hf (mate (embed i))).mpr h
    rw [hinv] at fixed
    exact ha i ((hf (embed i)).mp fixed.symm)
  have lift (i) : embed (rank (mate (embed i))) = mate (embed i) :=
    her _ (partner i)
  refine ⟨lift, ?_, ?_⟩
  · intro i
    change rank (mate (embed (rank (mate (embed i))))) = i
    rw [lift, hinv, hre]
  · intro i h
    have he := lift i
    rw [h] at he
    exact ha i ((hf _).mp he.symm)

/-- The successful adjacent pair is chosen from the supplied matching.
The terminal witness and the original chromogram are both retained. -/
theorem answer (c : Fin n → Color) (good : Fin n → Fin n → Bool)
    (P : List Color → Prop)
    (terminal : ∀ a b, good a b = true → P (List.ofFn (KempeIntervalRepair.switch c a b)))
    (embed : Fin m → Fin n) (rank : Fin n → Fin m)
    (hre : ∀ i, rank (embed i) = i)
    (her : ∀ i, c i ≠ c1 → embed (rank i) = i)
    (ha : ∀ i, c (embed i) ≠ c1)
    (block : Finset (Fin m))
    (hconvex : ∀ a ∈ block, ∀ b ∈ block, ∀ x, a < x → x < b → x ∈ block)
    (hmajor : m < 2 * block.card)
    (hg : ∀ a ∈ block, ∀ b ∈ block, b.val = a.val + 1 → good (embed a) (embed b) = true)
    (mate : Fin n → Fin n) (hinv : Function.Involutive mate)
    (hnc : Noncrossing mate) (hz : ∀ i, c i ≠ 0)
    (hf : ∀ i, mate i = i ↔ c i = c1)
    (horder : IsNoncrossingMatching (fun i => rank (mate (embed i)))) :
    ∃ a : Fin n, good a (mate a) = true ∧
      P (List.ofFn (KempeIntervalRepair.switch c a (mate a))) ∧
      matchg [] (List.ofFn (KempeIntervalRepair.switch c a (mate a))) (gram mate c) := by
  obtain ⟨lift, inv, free⟩ := active_mate c mate hinv hf embed rank hre her ha
  obtain ⟨i, hi, hj, hadj⟩ := exists_adjacent_majority
    (fun i => rank (mate (embed i))) inv free horder block hconvex hmajor
  have good_pair := hg i hi _ hj hadj
  rw [lift] at good_pair
  exact ⟨embed i, good_pair, terminal _ _ good_pair,
    KempeIntervalRepair.switch_matches mate c hinv hnc hz hf (embed i)⟩

end FourColor.KempeMajorityRepair

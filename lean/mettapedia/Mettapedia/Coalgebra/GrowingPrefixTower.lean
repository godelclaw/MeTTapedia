import Mettapedia.Coalgebra.CoherentPrefixTower

/-!
# Growing words as coherent finite observations

Extension preserves already published positions. Coverage makes every position
readable at a supplied stage; the tower is built from those words directly.
-/

namespace Mettapedia.Coalgebra.CoherentPrefixTower

variable {A : Type*} (words : ℕ → List A)
    (grows : ∀ n, words n <+: words (n + 1))
include grows

theorem prefix_of_le {i j : ℕ} (h : i ≤ j) : words i <+: words j := by
  induction j, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ j _ ih => exact ih.trans (grows j)

theorem lookup_eq {i j k : ℕ} (hi : k < (words i).length) (hj : k < (words j).length) :
    (words i)[k] = (words j)[k] := by
  rcases le_total i j with h | h
  · exact (prefix_of_le words grows h).getElem hi
  · exact ((prefix_of_le words grows h).getElem hj).symm

variable (covers : ∀ n, n ≤ (words n).length)
include covers

def Tower.ofGrowingLists : Tower A where
  view n i := (words n)[i.val]'(lt_of_lt_of_le i.isLt (covers n))
  coherent h := by
    funext i
    exact ((prefix_of_le words grows h).getElem (lt_of_lt_of_le i.isLt (covers _))).symm

theorem Tower.ofGrowingLists_read (stage k : ℕ) (hk : k < (words stage).length) :
    (ofGrowingLists words grows covers).toStream k = (words stage)[k] :=
  lookup_eq words grows (lt_of_lt_of_le (Nat.lt_succ_self k) (covers _)) hk

theorem Tower.ofGrowingLists_word (stage : ℕ) :
    List.ofFn (fun i : Fin (words stage).length =>
      (ofGrowingLists words grows covers).toStream i.val) = words stage := by
  apply List.ext_getElem (by simp) fun i hi hj => ?_
  simpa using ofGrowingLists_read words grows covers stage i hj

end Mettapedia.Coalgebra.CoherentPrefixTower

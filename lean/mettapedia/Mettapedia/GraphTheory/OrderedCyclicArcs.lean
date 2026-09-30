import Mathlib.Logic.Equiv.Fin.Rotate
import Lean.Elab.Tactic.Omega

/-!
# Two avoiding arcs between interleaved cyclic positions

Four positions in increasing order determine the two disjoint arcs needed
by a planar separation argument. The witnesses are literal iteration counts
of the cyclic successor, at arbitrary finite width.
-/

namespace Mettapedia.GraphTheory.OrderedCyclicArcs

variable {n : ℕ}

theorem iterate_val (i : Fin n) (k : ℕ) (hk : k < n) :
    ((finRotate n)^[k] i).val = (i.val + k) % n := by
  rw [← finCycle_eq_finRotate_iterate (k := ⟨k, hk⟩)]
  rfl

def Witness (cut separator left right : Fin n) : Prop :=
  ∃ leftSteps rightSteps : ℕ,
    (finRotate n)^[leftSteps] (finRotate n cut) = left ∧
    (finRotate n)^[rightSteps] right = cut ∧
    (∀ index, index < leftSteps →
      let port := (finRotate n)^[index] (finRotate n cut)
      port ≠ cut ∧ port ≠ separator) ∧
    (∀ index, index < rightSteps →
      let port := (finRotate n)^[index] right
      port ≠ cut ∧ port ≠ separator)

theorem witness_of_lt (cut left separator right : Fin n)
    (hcl : cut < left) (hls : left < separator) (hsr : separator < right) :
    Witness cut separator left right := by
  have hn : 0 < n := cut.pos
  have hcl' : cut.val < left.val := hcl
  have hls' : left.val < separator.val := hls
  have hsr' : separator.val < right.val := hsr
  have hc : (finRotate n cut).val = cut.val + 1 := by
    have := iterate_val cut 1 (by omega)
    simpa only [Function.iterate_one, Nat.mod_eq_of_lt (show cut.val + 1 < n by omega)]
      using this
  refine ⟨left.val - cut.val - 1, n - right.val + cut.val, ?_, ?_, ?_, ?_⟩
  · apply Fin.ext
    rw [iterate_val _ _ (by omega), hc]
    have he : cut.val + 1 + (left.val - cut.val - 1) = left.val := by omega
    rw [he, Nat.mod_eq_of_lt left.isLt]
  · apply Fin.ext
    rw [iterate_val _ _ (by omega)]
    have he : right.val + (n - right.val + cut.val) = n + cut.val := by omega
    rw [he, Nat.add_mod_left, Nat.mod_eq_of_lt cut.isLt]
  · intro j hj
    have hjn : j < n := by omega
    have hv : ((finRotate n)^[j] (finRotate n cut)).val = cut.val + 1 + j := by
      rw [iterate_val _ _ hjn, hc, Nat.mod_eq_of_lt (by omega)]
    constructor <;> intro he <;> have he' := congrArg Fin.val he <;> rw [hv] at he' <;> omega
  · intro j hj
    have hv := iterate_val right j (by omega)
    by_cases hw : right.val + j < n
    · rw [Nat.mod_eq_of_lt hw] at hv
      constructor <;> intro he <;> have he' := congrArg Fin.val he <;> rw [hv] at he' <;> omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hv
      constructor <;> intro he <;> have he' := congrArg Fin.val he <;> rw [hv] at he' <;> omega

end Mettapedia.GraphTheory.OrderedCyclicArcs

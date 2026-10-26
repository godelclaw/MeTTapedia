import Mettapedia.Algebra.TemporalQuantale
import Mettapedia.Algebra.HyperstructureQuantale
import Mettapedia.GSLT.Dynamics.OrderedListFold

/-!
# Temporal transport as ordered execution

Each shift occurrence is consumed separately. Additive totals determine the
endpoint, while different prefixes and different occurrence counts can remain
observable. The complete-path theorem applies to every supplied execution.
-/

set_option autoImplicit false
namespace Mettapedia.GSLT.Dynamics.TemporalTransport
open TemporalQuantale
open Mettapedia.Algebra.QuantaleWeakness

section Execution
variable {Q T : Type} [CommSemigroup Q] [CompleteLattice Q] [IsCommQuantale Q]
  [AddCommGroup T] [TemporalQuantale Q T]

/-- Sequential application, defined independently of the summed readout. -/
def run (times : List T) (initial : Q) : Q :=
  times.foldl (fun q t => shift t q) initial

theorem run_eq_shift_sum (times : List T) (initial : Q) :
    run times initial = shift times.sum initial := by
  induction times generalizing initial with
  | nil => exact (shift_zero initial).symm
  | cons t rest ih =>
      change run rest (shift t initial) = shift (t + rest.sum) initial
      rw [ih, ← shift_add, add_comm]

theorem run_append (first second : List T) (initial : Q) :
    run (first ++ second) initial = run second (run first initial) := List.foldl_append

theorem run_perm {first second : List T} (same : first.Perm second) (initial : Q) :
    run first initial = run second initial := by rw [run_eq_shift_sum, run_eq_shift_sum, same.sum_eq]

/-- No complete execution invents a result or discards a consumed occurrence. -/
theorem complete_path (times : List T) (initial result : Q)
    (path : (OrderedListFold.theory (fun q t => shift t q)).RewritePath
      (.active times initial) (.done result)) :
    result = shift times.sum initial ∧ path.length = times.length + 1 := by
  obtain ⟨value, visits⟩ := OrderedListFold.complete_path (fun q t => shift t q) times initial result path
  exact ⟨value.trans (run_eq_shift_sum times initial), visits⟩
end Execution

namespace Controls
open Mettapedia.Algebra.FootprintQuantale
abbrev Timed := Footprint (ℤ × Unit)
local instance : TemporalQuantale Timed ℤ := timedFootprint

def origin : Timed := Footprint.ofSet {(0, ())}

theorem cancellation_endpoint : run ([1, -1] : List ℤ) origin = origin := by
  rw [run_eq_shift_sum]
  exact shift_zero origin

theorem permutation_endpoint : run ([1, 2] : List ℤ) origin = run ([2, 1] : List ℤ) origin :=
  run_perm (by decide : ([1, 2] : List ℤ).Perm [2, 1]) origin

theorem prefixes_distinguished : run ([1] : List ℤ) origin ≠ run ([2] : List ℤ) origin := by
  intro same
  have observed := congrArg (fun q : Timed => (-1, ()) ∈ q.labels) same
  change ((-1 + (1 : ℤ), ()) ∈ origin.labels) = ((-1 + (2 : ℤ), ()) ∈ origin.labels) at observed
  simp [origin] at observed

theorem cancelled_visits :
    (OrderedListFold.runPath (fun q t => shift t q) ([1, -1] : List ℤ) origin).length = 3 :=
  (OrderedListFold.complete_path _ _ _ _ _).2

theorem empty_visits :
    (OrderedListFold.runPath (fun q t => shift t q) ([] : List ℤ) origin).length = 1 :=
  (OrderedListFold.complete_path _ _ _ _ _).2

/-- Summing two equal shifts preserves the endpoint but changes the consumed occurrences. -/
theorem fusion_endpoint : run ([1, 1] : List ℤ) origin = run ([2] : List ℤ) origin := by
  rw [run_eq_shift_sum, run_eq_shift_sum]
  rfl

theorem duplicate_visits :
    (OrderedListFold.runPath (fun q t => shift t q) ([1, 1] : List ℤ) origin).length = 3 :=
  (OrderedListFold.complete_path _ _ _ _ _).2

end Controls
end Mettapedia.GSLT.Dynamics.TemporalTransport

namespace Mettapedia.GSLT.Dynamics.TemporalTransport.NoncommutativeControls
open Mettapedia.Algebra
open Mettapedia.Algebra.QuantaleWeakness

def composition : HyperOp (Bool → Bool) := HyperOp.lift Function.comp
local instance : Fact composition.isAssociative := ⟨HyperOp.lift_assoc _ (fun _ _ _ => rfl)⟩
abbrev Endomorphisms := HyperOp.Powerset composition

def point (f : Bool → Bool) : Endomorphisms := HyperOp.Powerset.ofSet composition {f}

private theorem point_mul (f g : Bool → Bool) : point f * point g = point (f ∘ g) :=
  HyperOp.setExtend_singletons composition f g

private theorem point_into_residual (f g : Bool → Bool) :
    point f ≤ leftResiduate (point g) (point (f ∘ g)) := by
  rw [← residuate_galois, point_mul]

/-- The composition theorem applies to this noncommutative quantale. -/
theorem ordered_composition :
    leftResiduate (point Bool.not) (point fun _ => false) *
      leftResiduate (point id) (point Bool.not) ≤
        leftResiduate (point id) (point fun _ => false) := leftResiduate_comp _ _ _

/-- Swapping the two implications can manufacture the opposite Boolean answer. -/
theorem swapped_composition_fails :
    ¬ leftResiduate (point id) (point Bool.not) *
      leftResiduate (point Bool.not) (point fun _ => false) ≤
        leftResiduate (point id) (point fun _ => false) := by
  intro wrong
  have steps := mul_le_mul' (point_into_residual Bool.not id)
    (point_into_residual (fun _ => false) Bool.not)
  have reduced := (residuate_galois _ _ _).mpr (steps.trans wrong)
  rw [point_mul, point_mul] at reduced
  change ({fun _ : Bool => true} : Set (Bool → Bool)) ⊆ {fun _ => false} at reduced
  have equal : (fun _ : Bool => true) = (fun _ => false) :=
    Set.mem_singleton_iff.mp (reduced (Set.mem_singleton _))
  exact Bool.noConfusion (congrFun equal false)

end Mettapedia.GSLT.Dynamics.TemporalTransport.NoncommutativeControls

import Mettapedia.GraphTheory.Kempe.IndependentLift
import Mettapedia.GraphTheory.FourColor.KempeBoundaryObservation

/-!
# A relational repair of the four-cycle observation obstruction

The failed deterministic summary has a faithful alternative: keep the joint
extension constraint, and lift compatible sequences through the independent
hidden vertex. The generic theorem retains all physical component witnesses
and can keep a designated part of the surrounding boundary fixed.
-/

namespace Mettapedia.GraphTheory.FourColor.IndependentBoundaryRepair

open SimpleGraph KempeChainCertificate KempeBoundaryObservation
open Mettapedia.Combinatorics.Reconfiguration

abbrev hidden : Finset (Fin 4) := {3}

theorem hidden_independent : Square.graph.IsIndepSet (hidden : Set (Fin 4)) := by
  decide +kernel

/-- The same graph that refutes deterministic summary update admits this
uniform relational lift, for every palette and every compatible pair of
full colourings. No case table for those colourings is used. -/
theorem square_repair {α : Type*} [DecidableEq α]
    (C D : Square.graph.Coloring α) (a b : α)
    (pair : ∀ x, x ∉ hidden → D x = C x ∨ D x = Equiv.swap a b (C x)) :
    Nonempty (History C D) :=
  nonempty_history_iff.mpr
    (KempeIndependentLift.partial_swap hidden hidden_independent C D a b pair)

/-- This obtains the previously prepared outcome from the general law;
the other two ports remain fixed throughout every component switch. -/
theorem square_prepared_relative :
    Relation.ReflTransGen (Square.graph.KempeStepAvoiding {1, 2})
      (Square.state 0) (Square.state 3) :=
  KempeIndependentLift.partial_swap_avoiding hidden hidden_independent {1, 2}
    (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl <;> decide) (Square.state 0) (Square.state 3) (by decide +kernel) 0 2
    (by decide +kernel)

/-- Successive jointly compatible abstract operations lift to one actual
history, even though the current pair-partition summary is not deterministic. -/
theorem square_paths_lift {α : Type*} [DecidableEq α]
    (C D : Square.graph.Coloring α)
    (path : Relation.ReflTransGen
      (ImageStep (KempeIndependentLift.PairStep (Square.graph.induce (↑hidden)ᶜ) ∅)
        (fun E : Square.graph.Coloring α => E.restrictInduce (↑hidden)ᶜ))
      (C.restrictInduce (↑hidden)ᶜ) (D.restrictInduce (↑hidden)ᶜ)) :
    Nonempty (History C D) := by
  apply nonempty_history_iff.mpr
  have h := (KempeIndependentLift.projected_history_iff hidden hidden_independent
    ∅ (Set.empty_subset _) C D).mp (by simpa using path)
  exact Relation.ReflTransGen.mono (fun _ _ step => step.kempeStep) _ _ h

namespace CoupledStar

/-- One hidden hub and four retained leaves. -/
def graph : SimpleGraph (Fin 5) where
  Adj u v := u ≠ v ∧ (u = 0 ∨ v = 0)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance : DecidableRel graph.Adj := by unfold graph; infer_instance

def before : Fin 5 → Fin 4 := ![0, 1, 1, 2, 3]
def after : Fin 5 → Fin 4 := ![1, 0, 0, 2, 3]

theorem proper_before : ∀ u v, graph.Adj u v → before u ≠ before v := by decide +kernel
theorem proper_after : ∀ u v, graph.Adj u v → after u ≠ after v := by decide +kernel

def start : graph.Coloring (Fin 4) := .mk before (fun h => proper_before _ _ h)
def finish : graph.Coloring (Fin 4) := .mk after (fun h => proper_after _ _ h)

/-- The two leaves carrying colour one can switch jointly. The other two
leaves retain their colours throughout the reconstructed physical history. -/
theorem joint_repair :
    Relation.ReflTransGen (graph.KempeStepAvoiding {3, 4}) start finish :=
  KempeIndependentLift.partial_swap_avoiding {0} (by decide +kernel) {3, 4}
    (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl <;> decide)
    start finish (by decide +kernel) 0 1 (by decide +kernel)

theorem joint_history : Nonempty (History start finish) :=
  nonempty_history_iff.mpr
    (Relation.ReflTransGen.mono (fun _ _ h => h.kempeStep) _ _ joint_repair)

/-- Either individual leaf switch presents all four colours to the hub.
Both targets are proper on the retained edgeless graph, but neither extends. -/
theorem no_individual_extension (side : Bool) :
    ¬ ∃ C : graph.Coloring (Fin 4),
      C 1 = (if side then 0 else 1) ∧ C 2 = (if side then 1 else 0) ∧
      C 3 = 2 ∧ C 4 = 3 := by
  rintro ⟨C, h1, h2, h3, h4⟩
  have n1 := C.valid (show graph.Adj 0 1 from by decide)
  have n2 := C.valid (show graph.Adj 0 2 from by decide)
  have n3 := C.valid (show graph.Adj 0 3 from by decide)
  have n4 := C.valid (show graph.Adj 0 4 from by decide)
  rw [h1] at n1
  rw [h2] at n2
  rw [h3] at n3
  rw [h4] at n4
  have colours : ∀ c : Fin 4, c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by decide
  cases side <;> rcases colours (C 0) with h | h | h | h <;> simp_all

end CoupledStar
end Mettapedia.GraphTheory.FourColor.IndependentBoundaryRepair

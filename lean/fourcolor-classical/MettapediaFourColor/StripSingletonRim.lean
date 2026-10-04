import MettapediaFourColor.StripSingletonRepair

/-!
# Deriving the separation guard on the source rim

Every proper rim colouring in the local list domain supplies the first
component and its separation from the three retained ports. The two fixed
colour barriers stop that component from leaving the four-port arc. The
uniform repair then reconstructs the source for the entire domain.
-/

namespace FourColor.StripSingletonRim

open SimpleGraph Color
open Mettapedia.GraphTheory.FourColor.KempeChainCertificate

def graph := TriangleStripAnchors.input0099.graph.comap StripResponseSummary.port
instance : DecidableRel graph.Adj := by unfold graph; infer_instance
def arc : List (Fin 11) := [0,1,2,10]

theorem barriers : ∀ x ∈ arc, ∀ y, graph.Adj x y → y ∉ arc →
    ∀ a ∈ StripSingletonRepair.before y, a ≠ c0 ∧ a ≠ c1 := by decide +kernel
theorem missing_check : ∀ y, graph.Adj 1 y →
    ∀ a ∈ StripSingletonRepair.before y, a ≠ c2 := by decide +kernel
theorem arc_avoids : ∀ i ∈ StripSingletonRepair.retainedPorts, i ∉ arc := by decide +kernel

variable (C : graph.Coloring Color) (initial : ∀ i, C i ∈ StripSingletonRepair.before i)

def component : (C.bicoloredSubgraph c0 c1).ConnectedComponent :=
  (C.bicoloredSubgraph c0 c1).connectedComponentMk
    ⟨1,Or.inr (StripSingletonRepair.root_colour C id initial)⟩

theorem member : (1 : Fin 11) ∈ C.kempeComponentSet c0 c1 (component C initial) :=
  C.mem_kempeComponentSet_self (Or.inr (StripSingletonRepair.root_colour C id initial))

theorem confined : C.kempeComponentSet c0 c1 (component C initial) ⊆ {i | i ∈ arc} := by
  apply C.kempeComponentSet_subset_of_closed
    (Or.inr (StripSingletonRepair.root_colour C id initial)) (by decide : (1 : Fin 11) ∈ arc)
  intro x y hx edge active
  by_contra outside
  have none := barriers x hx y edge outside _ (initial y)
  exact active.elim none.1 none.2

theorem separated : ∀ i ∈ StripSingletonRepair.retainedPorts,
    i ∉ C.kempeComponentSet c0 c1 (component C initial) :=
  fun i hi hm => arc_avoids i hi (confined C initial hm)

include initial in
theorem missing : ∀ y, graph.Adj 1 y → C y ≠ c2 :=
  fun y edge => missing_check y edge _ (initial y)

include initial in
/-- Both component supply and separation follow from the actual rim. -/
theorem repair : ∃ D : graph.Coloring Color, ∃ h : History C D, h.length = 2 ∧
    ∃ k : TriangleStripAnchors.input0099.graph.Coloring Color,
      ∀ i, k (StripResponseSummary.port i) = D i :=
  StripSingletonRepair.repair C id (component C initial) initial (member C initial)
    (missing C initial) (fun _ _ h => h) Function.injective_id (separated C initial)

end FourColor.StripSingletonRim

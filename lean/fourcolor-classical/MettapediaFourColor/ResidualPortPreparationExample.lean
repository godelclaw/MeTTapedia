import MettapediaFourColor.ResidualPortPreparation
import Mettapedia.GraphTheory.FourColor.ComponentDetachExample

/-!
# The retained exterior supplies the free-port preparation

This checks the local supplier on the existing 155-vertex exterior without
adding another graph or colouring table. Its sphere rotation and source
embedding remain separately checked by the program replay.
-/

namespace FourColor.ResidualPortPreparation.Example

open SimpleGraph Color KempeDetachExample

noncomputable section

def palette : Fin 4 ↪ Color where
  toFun := ![c0,c1,c2,c3]
  inj' := by decide +kernel

def initial : graph.Coloring Color := graph.recolorOfEmbedding palette (state 0)

def boundaryPorts (j : Fin 11) : Fin 155 := ports.get j

theorem ports_injective : Function.Injective boundaryPorts := by decide +kernel

theorem initial_boundary : ∀ j, initial (boundaryPorts j) =
    ThreeBlockCore.word false false false j := by decide +kernel

theorem free_edges : ∀ e ∈ edges,
    (e.1 = boundaryPorts 2 → initial e.2 ≠ c1) ∧
    (e.2 = boundaryPorts 2 → initial e.1 ≠ c1) := by
  have h : edges.all (fun e => decide
      ((e.1 = boundaryPorts 2 → initial e.2 ≠ c1) ∧
       (e.2 = boundaryPorts 2 → initial e.1 ≠ c1))) = true := by decide +kernel
  exact fun e he => of_decide_eq_true (List.all_eq_true.mp h e he)

theorem free_port : ∀ x, graph.Adj (boundaryPorts 2) x → initial x ≠ c1 := by
  intro x edge
  exact on_edges (fun u v => u = boundaryPorts 2 → initial v ≠ c1) free_edges _ _ edge rfl

def path36 : graph.Walk (boundaryPorts 3) (boundaryPorts 6) :=
  .cons (show graph.Adj 98 16 by decide +kernel)
  (.cons (show graph.Adj 16 64 by decide +kernel)
  (.cons (show graph.Adj 64 31 by decide +kernel)
  (.cons (show graph.Adj 31 137 by decide +kernel)
  (.cons (show graph.Adj 137 21 by decide +kernel)
  (.cons (show graph.Adj 21 68 by decide +kernel)
  (.cons (show graph.Adj 68 71 by decide +kernel)
  (.cons (show graph.Adj 71 17 by decide +kernel) .nil)))))))

theorem path_active : ∀ x ∈ path36.support, initial x = c1 ∨ initial x = c3 := by
  decide +kernel

/-- The exact physical input consumes the general preparation law. The
new path is constructed, rather than supplied as a certificate. -/
theorem physical_preparation :
    ∃ D : graph.Coloring Color, graph.KempeStep initial D ∧
      (∀ j, D (boundaryPorts j) = preparedWord j) ∧
      ∃ q : graph.Walk (boundaryPorts 1) (boundaryPorts 6),
        ∀ x ∈ q.support, D x = c1 ∨ D x = c3 :=
  prepare initial boundaryPorts ports_injective (by decide +kernel) (by decide +kernel)
    initial_boundary free_port path36 path_active

end
end FourColor.ResidualPortPreparation.Example

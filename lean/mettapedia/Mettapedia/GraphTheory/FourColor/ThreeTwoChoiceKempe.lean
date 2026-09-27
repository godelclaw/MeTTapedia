import Mettapedia.GraphTheory.FourColor.ThreeTwoChoiceExample
import Mettapedia.GraphTheory.FourColor.IncidenceKempeSwitch
import Mettapedia.GraphTheory.FourColor.KempeChainCertificate

/-!
# A physical component realizing the explicit colouring revision

The four changed original edges of the three/two example form one
complete two-colour component. Its single switch produces exactly the
revised original assignment, which the final colouring extends.
-/

namespace Mettapedia.GraphTheory.FourColor.ThreeTwoChoiceExample

open GoertzelV24ForkInterfaceSupport IncidenceKempeSwitch KempeChainCertificate
open Mettapedia.GSLT.Ultrainfinite

noncomputable section

def originalColouring : (graph incidence original).Coloring (Fin 3) :=
  colouring incidence original firstChoice original_proper

def repairComponent : (originalColouring.bicoloredSubgraph 0 1).ConnectedComponent :=
  (originalColouring.bicoloredSubgraph 0 1).connectedComponentMk ⟨12, Or.inl rfl⟩

private theorem root_member :
    (12 : Fin 18) ∈ originalColouring.kempeComponentSet 0 1 repairComponent :=
  originalColouring.mem_kempeComponentSet_self (Or.inl rfl)

/-- The chain is connected and saturated in the actual original patch. -/
theorem repair_component_edges (x : Fin 18) :
    x ∈ originalColouring.kempeComponentSet 0 1 repairComponent ↔ x ∈ [12, 1, 2, 17] :=
  originalColouring.kempe_component_iff_mem_chain 0 1 repairComponent [12, 1, 2, 17]
    (by decide) (by decide) (by decide) (by decide : (12 : Fin 18) ∈ [12, 1, 2, 17])
    root_member x

/-- The physical switch gives exactly the four-edge revision on the
old patch, without treating an arbitrary edge set as a component. -/
theorem repair_switch_matches (x : Fin 18) (hx : x ∈ original) :
    originalColouring.swapOnKempeComponent 0 1 repairComponent x = revisedChoice x := by
  rw [originalColouring.swap_apply_of_chain 0 1 repairComponent [12, 1, 2, 17]
    (by decide) (by decide) (by decide) (by decide : (12 : Fin 18) ∈ [12, 1, 2, 17]) root_member]
  revert x
  decide

/-- A one-step GSLT history repairs the original witness, and the supplied
proper final colouring agrees with the repaired witness on all old edges. -/
theorem repaired_history_extends :
    ∃ D : (graph incidence original).Coloring (Fin 3),
      (∃ history : History originalColouring D, history.length = 1) ∧
      Proper incidence finalEdges revisedChoice ∧
      ∀ x ∈ original, revisedChoice x = D x := by
  refine ⟨originalColouring.swapOnKempeComponent 0 1 repairComponent,
    ⟨.cons (.switch _ 0 1 repairComponent) (.refl _), rfl⟩, revised_proper, ?_⟩
  exact fun x hx => (repair_switch_matches x hx).symm

end
end Mettapedia.GraphTheory.FourColor.ThreeTwoChoiceExample

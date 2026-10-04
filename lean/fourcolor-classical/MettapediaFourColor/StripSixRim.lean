import MettapediaFourColor.StripSixConnection

/-! The two port-six boundary forms use the same one-switch repair on the
actual source rim. This consumer does not assert confinement in arbitrary
exteriors; those may take the joint-connection branch. -/

namespace FourColor.StripSixRim

open SimpleGraph Color StripSixConnection StripSingletonRim StripResponseSummary
open Mettapedia.GraphTheory.FourColor.KempeChainCertificate

theorem proper : ∀ s i j, graph.Adj i j → input s i ≠ input s j := by decide +kernel
def initial (s : Bool) : graph.Coloring Color := .mk (input s) (fun h => proper s _ _ h)
theorem barriers : ∀ s y, graph.Adj 7 y → input s y ≠ c0 ∧ input s y ≠ c2 := by
  decide +kernel

theorem repair (s : Bool) : ∃ D : graph.Coloring Color,
    ∃ h : History (initial s) D, h.length = 1 ∧
    ∃ k : TriangleStripAnchors.input0099.graph.Coloring Color,
      ∀ i, k (port i) = D i := by
  classical
  let C := initial s
  have active : C 7 = c2 := by cases s <;> rfl
  let K := (C.bicoloredSubgraph c0 c2).connectedComponentMk ⟨7,Or.inr active⟩
  have m7 : (7 : Fin 11) ∈ C.kempeComponentSet c0 c2 K :=
    C.mem_kempeComponentSet_self (Or.inr active)
  have confined : C.kempeComponentSet c0 c2 K ⊆ {i | i = 7} := by
    apply C.kempeComponentSet_subset_of_closed (Or.inr active)
      (show (7 : Fin 11) ∈ {i : Fin 11 | i = 7} from rfl)
    intro x y hx edge hy
    change x = 7 at hx
    subst x
    have none := barriers s y edge
    exact (hy.elim none.1 none.2).elim
  have guard : ¬ (anchor s ∈ C.kempeComponentSet c0 c2 K ∧
      middle s ∈ C.kempeComponentSet c0 c2 K) := by
    intro both
    have eq : anchor s = 7 := confined both.1
    cases s <;> simp [anchor] at eq
  exact direct C id (fun _ _ h => h) s (fun _ => rfl) K m7 guard

end FourColor.StripSixRim

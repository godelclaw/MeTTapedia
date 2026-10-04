import MettapediaFourColor.StripSixSamePair
import MettapediaFourColor.StripSixOrderExample

/-! # A single-pair repair of the fixed-order obstruction

The existing spherical example defeats every zero/one phase followed by
every one/three phase. The one/two rule instead repairs it with two physical
switches and reconstructs a colouring of the entire sphere. No new graph
fixture or table of repair histories is needed.
-/

namespace FourColor.StripSixSamePairExample

open SimpleGraph Color StripSixOrderExample
open Mettapedia.GraphTheory.FourColor.KempeChainCertificate

def chain : List (Fin 33) := [6,7,8]

theorem checked : (6 : Fin 33) ∈ chain ∧ chain.IsChain exterior.Adj ∧
    (∀ x ∈ chain, state 0 x = c1 ∨ state 0 x = c2) ∧
    (∀ x ∈ chain, ∀ y, exterior.Adj x y →
      (state 0 y = c1 ∨ state 0 y = c2) → y ∈ chain) := by decide +kernel

def selected : KempeSeparatedChains.Certificate (state 0) c1 c2 :=
  ⟨chain,6,checked.1,checked.2.1,checked.2.2.1,checked.2.2.2⟩

theorem guard : port 6 ∈ (state 0).kempeComponentSet c1 c2 selected.component ∧
    port 4 ∉ (state 0).kempeComponentSet c1 c2 selected.component ∧
    port 10 ∉ (state 0).kempeComponentSet c1 c2 selected.component := by
  simp only [selected.component_mem]
  decide +kernel

theorem repaired : ∃ D : exterior.Coloring Color, ∃ h : History (state 0) D,
    h.length = 2 ∧ ∃ k : TriangleStripAnchors.input0099.graph.Coloring Color,
      ∀ i, k (StripResponseSummary.port i) = D (port i) :=
  StripSixSamePair.repair (state 0) port (by decide +kernel) port_edges
    initial_form missing_colour selected.component guard.1 guard.2.1 guard.2.2

theorem reconstructed : ∃ D : exterior.Coloring Color, ∃ h : History (state 0) D,
    h.length = 2 ∧ ∃ whole : ambient.Coloring Color,
      ∀ v, whole (includeExterior v) = D v := by
  obtain ⟨D,h,two,k,agree⟩ := repaired
  exact ⟨D,h,two,assemble D k agree⟩

end FourColor.StripSixSamePairExample

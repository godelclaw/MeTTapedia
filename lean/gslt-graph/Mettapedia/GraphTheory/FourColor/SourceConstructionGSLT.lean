import Mettapedia.GraphTheory.FourColor.VertexConstructionGSLT
import Mettapedia.GraphTheory.FourColor.SourceVertexCodeTerminalAcceptance

/-!
# Source maps represented by colouring construction routes

The source sweep already constructs a trace with the original vertices,
darts, edge mates and rotations. This file connects that round trip to the
GSLT witness interpretation. Coverage of the raw construction language is
therefore available independently of a colouring theorem.

The remaining existence problem is to prove compatible witnesses for these
source routes, or reconstruct them through certified reductions. Merely
having a structural route is not terminal colour acceptance.
-/

namespace Mettapedia.GraphTheory.FourColor.SourceConstructionGSLT

open GoertzelV24RotationCutDartDecomposition GoertzelV24FaceDualConnectedness
open GoertzelV24TwoEdgeCutMinimality
open TubeSlab.VertexTransfer
open VertexCodeSourceGeometry SourceVertexCodeTrace
open SourceVertexCodeTerminalAcceptance VertexConstructionGSLT

noncomputable section
attribute [local instance] Classical.propDecidable

universe u
variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable {RS : RotationSystem.{u,u,u} V E}

/-- The colouring witnesses on a complete encoded route are exactly
colourings of the original source rotation system. -/
theorem encoded_support_iff
    (hc : RS.IsCubic) (hcyc : VertexRotationCyclic RS)
    (order : List V) (hn : order.Nodup) (he : order ≠ [])
    (hcover : ∀ v, visited order v) :
    colouring.Supports (route (encodeClosed hc hcyc order hn he hcover).trace)
        Fin.elim0 Fin.elim0 ↔ RotationSystemTaitColorable RS :=
  (closed_realization_iff _).trans
    (tangle_taitColorable_iff (encodeClosed hc hcyc order hn he hcover).model hcover)

/-- Every map in the source class has an exact operational representation.
The existential supplies the route and its geometric model, not a colouring. -/
theorem class_represented (hclass : BridgelessSphericalCubicMapData RS) :
    ∃ trace : VertexCodeTrace.Trace 0,
      Nonempty (Model trace.realize
        (terminalCoordinates (RS := RS) completeOrder visited_complete)) ∧
      Fintype.card trace.Vertex = Fintype.card V ∧
      (colouring.Supports (route trace) Fin.elim0 Fin.elim0 ↔
        RotationSystemTaitColorable RS) := by
  obtain ⟨trace, ⟨model⟩, _, _, hcard, _⟩ := class_terminal_covered hclass
  exact ⟨trace, ⟨model⟩, hcard,
    (closed_realization_iff trace).trans (tangle_taitColorable_iff model visited_complete)⟩

/-- Changing the sweep order changes the operational route, while terminal
support is the same source observation. No successful colouring is assumed. -/
theorem sweep_support_iff
    (hc : RS.IsCubic) (hcyc : VertexRotationCyclic RS)
    (first second : List V) (hfirst : first.Nodup) (hsecond : second.Nodup)
    (hneFirst : first ≠ []) (hneSecond : second ≠ [])
    (hcoverFirst : ∀ v, visited first v) (hcoverSecond : ∀ v, visited second v) :
    colouring.Supports (route (encodeClosed hc hcyc first hfirst hneFirst hcoverFirst).trace)
        Fin.elim0 Fin.elim0 ↔
      colouring.Supports (route (encodeClosed hc hcyc second hsecond hneSecond hcoverSecond).trace)
        Fin.elim0 Fin.elim0 :=
  (encoded_support_iff hc hcyc first hfirst hneFirst hcoverFirst).trans
    (encoded_support_iff hc hcyc second hsecond hneSecond hcoverSecond).symm

end
end Mettapedia.GraphTheory.FourColor.SourceConstructionGSLT

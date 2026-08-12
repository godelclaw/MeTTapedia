import Mettapedia.GraphTheory.FourColor.GoertzelV24CorridorTransferWordReachablePumping
import Mettapedia.GraphTheory.FourColor.GoertzelV24SpliceUnification

/-!
# Colorability reflection from reachable-set pumping

The compositional route only needs a global reflection statement for
reductive descent: if the shortened splice is Tait colorable, then the source
is Tait colorable.  Reachable-set pumping supplies exactly that polarity once
the physical shortened and source objects have been related to the shortened
and full transfer words.

This connector deliberately does not preserve a chosen shortened coloring.
Insertion of the removed word may select a different profile before the
right-hand context, so pointwise reverse completion and a positive diagonal
at every displayed seam word are stronger sufficient conditions, not the
logical target used here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SpliceUnification

open GoertzelV24CorridorTransferWord
open GoertzelV24CorridorTransferWordReachablePumping

universe u

noncomputable section

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

namespace OrderedCutSpliceData

variable {RS : RotationSystem V E}
  {n terminalCount faceFragmentCount : Nat}

/-- Equality of the complete reachable profile supports before and after the
removed middle word gives the exact global colorability reflection required
by reductive descent, provided the two physical/word semantic adapters are
available.

The adapters remain explicit premises: this theorem does not identify a
transfer word with an annular splice or construct either direction of that
identification. -/
theorem colorabilityReflection_of_transferWordReachableSet_eq
    {Profile : Type u} [Fintype Profile] [DecidableEq Profile]
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (left middle right : List (Profile → Profile → Prop))
    (initial : Finset Profile) (isAccepting : Profile → Prop)
    (hreachable : transferWordReachableSet left initial =
      transferWordReachableSet (left ++ middle) initial)
    (output_accepts : TaitColorable data.output →
      TransferWordAccepts (left ++ right) initial isAccepting)
    (source_colorable :
      TransferWordAccepts (left ++ middle ++ right) initial isAccepting →
        TaitColorable (RS := RS)) :
    data.ColorabilityReflection := by
  intro houtput
  apply source_colorable
  exact transferWordAccepts_insert_of_reachableSet_eq
    left middle right initial isAccepting hreachable (output_accepts houtput)

/-- Package reachable-set pumping directly as a completed splice step.  The
strict size decrease is already intrinsic to `OrderedCutSpliceData`; the
arguments of this constructor display the remaining semantic identifications
instead of hiding them behind a stronger pointwise completion interface. -/
def CompletedStep.ofTransferWordReachableSetEq
    {Profile : Type u} [Fintype Profile] [DecidableEq Profile]
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (left middle right : List (Profile → Profile → Prop))
    (initial : Finset Profile) (isAccepting : Profile → Prop)
    (hreachable : transferWordReachableSet left initial =
      transferWordReachableSet (left ++ middle) initial)
    (output_accepts : TaitColorable data.output →
      TransferWordAccepts (left ++ right) initial isAccepting)
    (source_colorable :
      TransferWordAccepts (left ++ middle ++ right) initial isAccepting →
        TaitColorable (RS := RS)) :
    data.CompletedStep where
  colorability_reflection :=
    data.colorabilityReflection_of_transferWordReachableSet_eq
      left middle right initial isAccepting hreachable output_accepts
      source_colorable

end OrderedCutSpliceData

end

end GoertzelV24SpliceUnification

end Mettapedia.GraphTheory.FourColor

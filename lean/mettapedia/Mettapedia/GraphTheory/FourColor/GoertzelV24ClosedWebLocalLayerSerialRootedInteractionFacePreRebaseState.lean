import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialRootedInteractionPreRebaseState
import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceExteriorLabelCapFactorUpdate

/-!
# Graph-free facial update on the complete interaction root

The rolling facial state has twenty-four coordinates, while the following
boundary rebase can inspect a forty-eight-dart interaction carrier.  The rooted
state now carries the prefix factor on both interfaces and the inclusion of the
current coordinates into the larger carrier.

This file lifts one physical Cell's finite facial adjacency and presence rows
along that inclusion, then adjoins them to the cap-six interaction factor.  The
operation is entirely graph-free.  Source exactness is proved separately from
the definition so arbitrary finite inputs remain executable data.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFacePreRebaseState

open GoertzelV24ClosedWebLocalLayerSerialCellNativeFactorization
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionPreRebaseState
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionState
open GoertzelV24InterfaceExteriorLabelCapFactorUpdate

/-- Lift a Boolean activity row from a smaller named interface to a larger
one.  The existential definition remains sound even for arbitrary records
whose coordinate map contains aliases. -/
def liftInterfacePresence
    {Old New : Type*} [Fintype Old] [DecidableEq Old] [DecidableEq New]
    (coordinate : Old → New) (present : Old → Bool) (slot : New) : Bool :=
  decide (∃ old, coordinate old = slot ∧ present old = true)

@[simp]
theorem liftInterfacePresence_eq_true_iff
    {Old New : Type*} [Fintype Old] [DecidableEq Old] [DecidableEq New]
    (coordinate : Old → New) (present : Old → Bool) (slot : New) :
    liftInterfacePresence coordinate present slot = true ↔
      ∃ old, coordinate old = slot ∧ present old = true := by
  simp [liftInterfacePresence]

/-- Exactness of lifted presence when every literally present large-interface
vertex is named by the smaller interface. -/
theorem liftInterfacePresence_eq_true_iff_of_exact
    {N Old New : Type*} [Fintype Old] [DecidableEq Old] [DecidableEq New]
    (oldVertex : Old → N) (newVertex : New → N)
    (coordinate : Old → New)
    (hcoordinate : ∀ old, newVertex (coordinate old) = oldVertex old)
    (hnewInjective : Function.Injective newVertex)
    (present : Old → Bool) (actualPresent : N → Prop)
    (hpresent : ∀ old, present old = true ↔ actualPresent (oldVertex old))
    (hcovered : ∀ new, actualPresent (newVertex new) →
      ∃ old, oldVertex old = newVertex new)
    (slot : New) :
    liftInterfacePresence coordinate present slot = true ↔
      actualPresent (newVertex slot) := by
  rw [liftInterfacePresence_eq_true_iff]
  constructor
  · rintro ⟨old, hslot, hpresentOld⟩
    have hold := (hpresent old).1 hpresentOld
    simpa [← hslot, hcoordinate] using hold
  · intro hpresentNew
    rcases hcovered slot hpresentNew with ⟨old, hold⟩
    have hslot : coordinate old = slot := by
      apply hnewInjective
      exact (hcoordinate old).trans hold
    have hpresentOld : actualPresent (oldVertex old) := by
      simpa [hold] using hpresentNew
    exact ⟨old, hslot, (hpresent old).2 hpresentOld⟩

/-- Lift the physical Cell/seam facial adjacency from the current rolling
coordinates to the complete facial interaction coordinates. -/
def sourceLocalLayerSerialRootedInteractionFaceLocalAdjacency
    {outputCount : Fin 5}
    (state : SourceLocalLayerSerialRootedInteractionState)
    (localFactor : SourceLocalLayerSerialCellPhysicalBoolLocalFactor outputCount)
    (hcount : state.faceCapSix.vertexCount =
      localFactor.faceCode.vertexCount) :
    Fin state.faceInteractionExterior.vertexCount.val →
      Fin state.faceInteractionExterior.vertexCount.val → Bool :=
  liftInterfaceAdjacency state.faceCurrentCoordinate
    (sourceLocalLayerSerialCellPhysicalFaceLocalAdjacency
      state.toSourceLocalLayerSerialColoredCumulativeState localFactor hcount)

/-- Lift literal Cell presence from the current rolling coordinates to the
complete facial interaction coordinates. -/
def sourceLocalLayerSerialRootedInteractionFaceLocalPresence
    {outputCount : Fin 5}
    (state : SourceLocalLayerSerialRootedInteractionState)
    (localFactor : SourceLocalLayerSerialCellPhysicalBoolLocalFactor outputCount) :
    Fin state.faceInteractionExterior.vertexCount.val → Bool :=
  liftInterfacePresence state.faceCurrentCoordinate (fun slot ↦
    localFactor.faceEdgeState.cellPresent
      (Fin.castLE
        (Nat.le_of_lt_succ state.faceCapSix.vertexCount.isLt) slot))

/-- Adjoin one physical Cell and its residual seam to the cap-six factor on
the complete facial interaction carrier. -/
def sourceLocalLayerSerialRootedInteractionFacePreRebaseState
    {outputCount : Fin 5}
    (state : SourceLocalLayerSerialRootedInteractionState)
    (localFactor : SourceLocalLayerSerialCellPhysicalBoolLocalFactor outputCount)
    (hcount : state.faceCapSix.vertexCount =
      localFactor.faceCode.vertexCount) :
    SourceLocalLayerSerialFaceInteractionPrefixState where
  vertexCount := state.faceInteractionExterior.vertexCount
  code := fun _ ↦ addInterfaceAdjacencyAndPresence
    (state.faceInteractionExterior.code ())
    (sourceLocalLayerSerialRootedInteractionFaceLocalAdjacency state localFactor
      hcount)
    (sourceLocalLayerSerialRootedInteractionFaceLocalPresence state localFactor)

/-- Executable guarded form of the facial interaction update. -/
def sourceLocalLayerSerialRootedInteractionFacePreRebaseState?
    {outputCount : Fin 5}
    (state : SourceLocalLayerSerialRootedInteractionState)
    (localFactor : SourceLocalLayerSerialCellPhysicalBoolLocalFactor outputCount) :
    Option SourceLocalLayerSerialFaceInteractionPrefixState :=
  if hcount : state.faceCapSix.vertexCount =
      localFactor.faceCode.vertexCount then
    some (sourceLocalLayerSerialRootedInteractionFacePreRebaseState state
      localFactor hcount)
  else none

end GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFacePreRebaseState

end Mettapedia.GraphTheory.FourColor

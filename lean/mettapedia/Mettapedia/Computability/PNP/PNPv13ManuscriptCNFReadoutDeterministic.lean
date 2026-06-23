import Mettapedia.Computability.PNP.PNPv13ManuscriptCNFReadoutLockedLayer

/-!
# PNP v13: deterministic readout repair boundary

This module isolates the extra accepted-state constancy needed to turn
deterministic readout into locked-layer rigidity.
-/

namespace Mettapedia.Computability.PNP

universe u v w x y z

/-- A refinement that exposes the manuscript's deterministic readout predicate
`Read_Y(z, ξ_lock, M)`.  Determinism says a fixed readout state has at most one
message, but this is weaker than locked-layer rigidity unless all accepted
locked views are forced into a message-compatible readout state. -/
structure DeterministicReadoutLockedLayerData (Public : Type u)
    (Var : Public → Type v) (Witness : Public → Type w)
    (LockView : Public → Type x) (ReadState : Public → Type y)
    (Message : Type z) extends
    LockedLayerCNFReadoutData Public Var Witness LockView Message where
  /-- The part of `(z, ξ_lock)` seen by the deterministic readout predicate. -/
  readState : (Y : Public) → LockView Y → ReadState Y
  /-- The readout predicate `Read_Y(state,M)=1`. -/
  readAccept : (Y : Public) → ReadState Y → Message → Prop
  /-- Accepted locked views satisfy the deterministic readout predicate for
  their own message. -/
  lockAccept_readAccept :
    ∀ {Y : Public} {L : LockView Y},
      lockAccept Y L → readAccept Y (readState Y L) (lockMessage Y L)
  /-- Determinism of `Read_Y`: for a fixed readout state, at most one message
  is accepted. -/
  readAccept_deterministic :
    ∀ {Y : Public} {state : ReadState Y} {M M' : Message},
      readAccept Y state M → readAccept Y state M' → M = M'

namespace DeterministicReadoutLockedLayerData

variable {Public : Type u} {Var : Public → Type v}
variable {Witness : Public → Type w} {LockView : Public → Type x}
variable {ReadState : Public → Type y} {Message : Type z}

/-- A sufficient condition turning deterministic readout into locked-layer
rigidity: accepted locked views over the same supported public input have the
same readout state. -/
def AcceptedReadStateConstancy
    (D : DeterministicReadoutLockedLayerData
      Public Var Witness LockView ReadState Message) : Prop :=
  ∀ {Y : Public} {L L' : LockView Y},
    D.support Y →
      D.lockAccept Y L →
        D.lockAccept Y L' →
          D.readState Y L = D.readState Y L'

/-- Deterministic readout plus accepted-state constancy implies Hypothesis 4.9
locked-layer rigidity. -/
theorem lockedLayerRigidity_of_acceptedReadStateConstancy
    (D : DeterministicReadoutLockedLayerData
      Public Var Witness LockView ReadState Message)
    (hstate : D.AcceptedReadStateConstancy) :
    D.toLockedLayerCNFReadoutData.LockedLayerRigidity := by
  intro Y L L' hY hL hL'
  have hs : D.readState Y L = D.readState Y L' :=
    hstate hY hL hL'
  have hreadL : D.readAccept Y (D.readState Y L) (D.lockMessage Y L) :=
    D.lockAccept_readAccept hL
  have hreadL' : D.readAccept Y (D.readState Y L') (D.lockMessage Y L') :=
    D.lockAccept_readAccept hL'
  rw [← hs] at hreadL'
  exact D.readAccept_deterministic hreadL hreadL'

/-- Deterministic readout closes the SAT-search readout route only with the
extra accepted-state constancy premise. -/
theorem exists_correctForAllSatSearchOutputs_of_acceptedReadStateConstancy
    (D : DeterministicReadoutLockedLayerData
      Public Var Witness LockView ReadState Message)
    (hstate : D.AcceptedReadStateConstancy)
    {Y : Public} (hY : D.support Y)
    {α₀ : ConcreteCNF.Assignment (Var Y)}
    (hα₀ : ConcreteCNF.IsSatFormula (D.formula Y) α₀) :
    ∃ msg : Message,
      CorrectForAllSatSearchOutputs
        (ConcreteCNF.IsSatFormula (D.formula Y)) (D.projection Y) msg := by
  exact
    D.toLockedLayerCNFReadoutData.exists_correctForAllSatSearchOutputs_of_lockedLayerRigidity
      (D.lockedLayerRigidity_of_acceptedReadStateConstancy hstate) hY hα₀

/-- Exact obstruction to the extra state-constancy premise: deterministic
readout is compatible with several accepted readout states, and two such
states already refute accepted-state constancy. -/
theorem not_acceptedReadStateConstancy_of_distinct_accepted_readStates
    (D : DeterministicReadoutLockedLayerData
      Public Var Witness LockView ReadState Message)
    {Y : Public} {L L' : LockView Y}
    (hY : D.support Y)
    (hL : D.lockAccept Y L) (hL' : D.lockAccept Y L')
    (hdiff : D.readState Y L ≠ D.readState Y L') :
    ¬ D.AcceptedReadStateConstancy := by
  intro hstate
  exact hdiff (hstate hY hL hL')

end DeterministicReadoutLockedLayerData

end Mettapedia.Computability.PNP

import Mettapedia.Computability.PNP.PNPv13ManuscriptCNFReadoutCore

/-!
# PNP v13: locked-layer CNF readout repair

This module refines the manuscript CNF-readout interface with the locked-layer
view used in v13 Proposition 4.10.
-/

namespace Mettapedia.Computability.PNP

universe u v w x y z

/-- A refinement of `ManuscriptCNFReadoutData` that exposes exactly the
locked-layer data used in v13 Proposition 4.10.  A valid witness has a
locked-layer view, the locked layer accepts that view, and the witness message
is the message read from that view. -/
structure LockedLayerCNFReadoutData (Public : Type u)
    (Var : Public → Type v) (Witness : Public → Type w)
    (LockView : Public → Type x) (Message : Type z) extends
    ManuscriptCNFReadoutData Public Var Witness Message where
  /-- The locked-layer coordinates `(z, ξ_lock, M)` extracted from a witness. -/
  lockView : (Y : Public) → Witness Y → LockView Y
  /-- The locked-layer predicate `Lock_Y(z, ξ_lock, M)=1`. -/
  lockAccept : (Y : Public) → LockView Y → Prop
  /-- The message coordinate carried by a locked-layer view. -/
  lockMessage : (Y : Public) → LockView Y → Message
  /-- Definition 4.8, locked-layer clause: every valid witness satisfies the
  locked layer. -/
  validWitness_lockAccept :
    ∀ {Y : Public} {W : Witness Y},
      validWitness Y W → lockAccept Y (lockView Y W)
  /-- The semantic witness message is the message coordinate in its locked view. -/
  witnessMessage_eq_lockMessage :
    ∀ {Y : Public} {W : Witness Y},
      validWitness Y W → witnessMessage Y W = lockMessage Y (lockView Y W)

namespace LockedLayerCNFReadoutData

variable {Public : Type u} {Var : Public → Type v}
variable {Witness : Public → Type w} {LockView : Public → Type x}
variable {Message : Type z}

/-- Hypothesis 4.9: accepted locked-layer views over a supported public input
all carry the same message. -/
def LockedLayerRigidity
    (D : LockedLayerCNFReadoutData Public Var Witness LockView Message) : Prop :=
  ∀ {Y : Public} {L L' : LockView Y},
    D.support Y →
      D.lockAccept Y L →
        D.lockAccept Y L' →
          D.lockMessage Y L = D.lockMessage Y L'

/-- Proposition 4.10 in the locked-layer interface: locked-layer rigidity
implies the witness-level single-message promise. -/
theorem singleMessagePromise_of_lockedLayerRigidity
    (D : LockedLayerCNFReadoutData Public Var Witness LockView Message)
    (hrigid : D.LockedLayerRigidity) :
    D.toManuscriptCNFReadoutData.SingleMessagePromise := by
  intro Y W W' hY hW hW'
  calc
    D.witnessMessage Y W = D.lockMessage Y (D.lockView Y W) :=
      D.witnessMessage_eq_lockMessage hW
    _ = D.lockMessage Y (D.lockView Y W') :=
      hrigid hY (D.validWitness_lockAccept hW) (D.validWitness_lockAccept hW')
    _ = D.witnessMessage Y W' :=
      (D.witnessMessage_eq_lockMessage hW').symm

/-- Combining Proposition 4.10 with Appendix I.23: locked-layer rigidity
implies CNF-level readout constancy for the fixed message projection. -/
theorem singleMessageReadout_of_lockedLayerRigidity
    (D : LockedLayerCNFReadoutData Public Var Witness LockView Message)
    (hrigid : D.LockedLayerRigidity)
    {Y : Public} (hY : D.support Y) :
    SingleMessageReadout
      (ConcreteCNF.IsSatFormula (D.formula Y)) (D.projection Y) := by
  exact
    D.toManuscriptCNFReadoutData.singleMessageReadout_of_singleMessagePromise
      (D.singleMessagePromise_of_lockedLayerRigidity hrigid) hY

/-- The arbitrary-output SAT-search decoder obligation closes from
locked-layer rigidity plus one satisfying CNF assignment. -/
theorem exists_correctForAllSatSearchOutputs_of_lockedLayerRigidity
    (D : LockedLayerCNFReadoutData Public Var Witness LockView Message)
    (hrigid : D.LockedLayerRigidity)
    {Y : Public} (hY : D.support Y)
    {α₀ : ConcreteCNF.Assignment (Var Y)}
    (hα₀ : ConcreteCNF.IsSatFormula (D.formula Y) α₀) :
    ∃ msg : Message,
      CorrectForAllSatSearchOutputs
        (ConcreteCNF.IsSatFormula (D.formula Y)) (D.projection Y) msg := by
  exact
    D.toManuscriptCNFReadoutData.exists_correctForAllSatSearchOutputs_of_singleMessagePromise
      (D.singleMessagePromise_of_lockedLayerRigidity hrigid) hY hα₀

/-- Exact obstruction to Hypothesis 4.9: two accepted locked-layer views over
one supported public input with different message coordinates refute
locked-layer rigidity. -/
theorem not_lockedLayerRigidity_of_distinct_accepted_lockMessages
    (D : LockedLayerCNFReadoutData Public Var Witness LockView Message)
    {Y : Public} {L L' : LockView Y}
    (hY : D.support Y)
    (hL : D.lockAccept Y L) (hL' : D.lockAccept Y L')
    (hdiff : D.lockMessage Y L ≠ D.lockMessage Y L') :
    ¬ D.LockedLayerRigidity := by
  intro hrigid
  exact hdiff (hrigid hY hL hL')

end LockedLayerCNFReadoutData

end Mettapedia.Computability.PNP

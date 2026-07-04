import Mettapedia.Computability.PNP.PNPv13LockedCoreLabCanaries
import Mettapedia.Computability.PNP.V13ConditionalClash
import Mettapedia.Computability.PNP.V13RealRungOneLinear

/-!
# PNP v15 real ensemble spine

This module starts the real-ensemble lift beyond the v14 toy endpoint.  It
records the manuscript-facing single-message SAT spine as an interface over a
public instance, hidden witness, verifier, fixed public message, and witness
readout.  The checked inhabitant below is the real v13 linear public surface:
the full public instance `(A, A x)` fixes the target coordinate and any valid
witness reads the same message.

This is not yet the full M4 SAT ensemble.  The ledger at the end records the
remaining construction obligations separately from the four irreducible
mathematical inputs.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

universe u v w x y z

/-- Real single-message SAT spine: every supported world supplies a public
instance and a hidden witness; every verifier-valid witness reads the fixed
message of that public instance. -/
structure RealSingleMessageSATSpine
    (World : Type u) (Public : Type v) (Witness : Type w) where
  publicInput : World -> Public
  witnessOfWorld : World -> Witness
  verifier : Public -> Witness -> Prop
  messageOfPublic : Public -> Bool
  witnessReadout : Witness -> Bool
  target : World -> Bool
  worldWitnessValid :
    ∀ omega, verifier (publicInput omega) (witnessOfWorld omega)
  readout_eq_message_of_valid :
    ∀ {Y W}, verifier Y W -> witnessReadout W = messageOfPublic Y
  target_eq_message :
    ∀ omega, target omega = messageOfPublic (publicInput omega)

namespace RealSingleMessageSATSpine

variable {World : Type u} {Public : Type v} {Witness : Type w}

/-- The fixed public message makes the target single-valued over the full
public instance. -/
theorem singleMessage
    (S : RealSingleMessageSATSpine World Public Witness) :
    ∀ w0 w1, S.publicInput w0 = S.publicInput w1 ->
      S.target w0 = S.target w1 := by
  intro w0 w1 hPublic
  calc
    S.target w0 = S.messageOfPublic (S.publicInput w0) :=
      S.target_eq_message w0
    _ = S.messageOfPublic (S.publicInput w1) := by rw [hPublic]
    _ = S.target w1 := (S.target_eq_message w1).symm

/-- Any two verifier-valid hidden witnesses over one public instance have the
same readout. -/
theorem readout_eq_of_valid
    (S : RealSingleMessageSATSpine World Public Witness)
    {Y : Public} {W W' : Witness}
    (hW : S.verifier Y W) (hW' : S.verifier Y W') :
    S.witnessReadout W = S.witnessReadout W' := by
  calc
    S.witnessReadout W = S.messageOfPublic Y :=
      S.readout_eq_message_of_valid hW
    _ = S.witnessReadout W' :=
      (S.readout_eq_message_of_valid hW').symm

/-- The canonical hidden witness attached to a world reads the target bit. -/
theorem worldWitness_readout_eq_target
    (S : RealSingleMessageSATSpine World Public Witness)
    (omega : World) :
    S.witnessReadout (S.witnessOfWorld omega) = S.target omega := by
  calc
    S.witnessReadout (S.witnessOfWorld omega) =
        S.messageOfPublic (S.publicInput omega) :=
      S.readout_eq_message_of_valid (S.worldWitnessValid omega)
    _ = S.target omega := (S.target_eq_message omega).symm

end RealSingleMessageSATSpine

/-! ## Real v13 linear surface as a single-message spine -/

def v13RealLinearBit (a : ZMod 2) : Bool :=
  decide (a = 1)

def v13RealLinearVerifier {m : Nat}
    (Y : V13RealLinearPublic m) (W : F2Vec m) : Prop :=
  Y.A.toEquiv W = Y.b

def v13RealLinearWitnessReadout {m : Nat}
    (i₀ : Fin m) (W : F2Vec m) : Bool :=
  v13RealLinearBit (W i₀)

def v13RealLinearMessageOfPublic {m : Nat}
    (i₀ : Fin m) (Y : V13RealLinearPublic m) : Bool :=
  v13RealLinearBit (Y.A.toEquiv.symm Y.b i₀)

def v13RealLinearTargetBit {m : Nat}
    (i₀ : Fin m) (omega : V13RealLinearWorld m) : Bool :=
  v13RealLinearBit (v13RealLinearTarget i₀ omega)

theorem v13RealLinearVerifier_readout_eq_message {m : Nat}
    (i₀ : Fin m) {Y : V13RealLinearPublic m} {W : F2Vec m}
    (hW : v13RealLinearVerifier Y W) :
    v13RealLinearWitnessReadout i₀ W =
      v13RealLinearMessageOfPublic i₀ Y := by
  have hWitness : W = Y.A.toEquiv.symm Y.b := by
    calc
      W = Y.A.toEquiv.symm (Y.A.toEquiv W) := by simp
      _ = Y.A.toEquiv.symm Y.b := by rw [hW]
  unfold v13RealLinearWitnessReadout v13RealLinearMessageOfPublic
  rw [hWitness]

theorem v13RealLinear_worldWitness_valid {m : Nat}
    (omega : V13RealLinearWorld m) :
    v13RealLinearVerifier (v13RealLinearPublicInput omega) omega.x := by
  rfl

theorem v13RealLinearTargetBit_eq_messageOfPublic {m : Nat}
    (i₀ : Fin m) (omega : V13RealLinearWorld m) :
    v13RealLinearTargetBit i₀ omega =
      v13RealLinearMessageOfPublic i₀ (v13RealLinearPublicInput omega) := by
  unfold v13RealLinearTargetBit v13RealLinearMessageOfPublic
  change
    v13RealLinearBit (v13RealLinearTarget i₀ omega) =
      v13RealLinearBit
        (v13RealLinearFullDecoder i₀ (v13RealLinearPublicInput omega))
  rw [v13RealLinear_fullPublic_decodes_target]

/-- The real linear public surface supplies the readout/single-message spine:
valid hidden witnesses over `(A, A x)` all read the public message
`(A^{-1} b)_{i₀}`. -/
def v13RealLinearSingleMessageSATSpine {m : Nat} (i₀ : Fin m) :
    RealSingleMessageSATSpine
      (V13RealLinearWorld m) (V13RealLinearPublic m) (F2Vec m) where
  publicInput := v13RealLinearPublicInput
  witnessOfWorld := fun omega => omega.x
  verifier := v13RealLinearVerifier
  messageOfPublic := v13RealLinearMessageOfPublic i₀
  witnessReadout := v13RealLinearWitnessReadout i₀
  target := v13RealLinearTargetBit i₀
  worldWitnessValid := v13RealLinear_worldWitness_valid
  readout_eq_message_of_valid := v13RealLinearVerifier_readout_eq_message i₀
  target_eq_message := v13RealLinearTargetBit_eq_messageOfPublic i₀

theorem v13RealLinearSingleMessageSATSpine_singleMessage {m : Nat}
    (i₀ : Fin m) :
    ∀ w0 w1 : V13RealLinearWorld m,
      v13RealLinearPublicInput w0 = v13RealLinearPublicInput w1 ->
        v13RealLinearTargetBit i₀ w0 = v13RealLinearTargetBit i₀ w1 :=
  (v13RealLinearSingleMessageSATSpine i₀).singleMessage

theorem v13RealLinear_validWitness_readout_eq_publicMessage {m : Nat}
    (i₀ : Fin m) {Y : V13RealLinearPublic m} {W : F2Vec m}
    (hW : v13RealLinearVerifier Y W) :
    v13RealLinearWitnessReadout i₀ W =
      v13RealLinearMessageOfPublic i₀ Y :=
  (v13RealLinearSingleMessageSATSpine i₀).readout_eq_message_of_valid hW

/-! ## Appendix D locked-core adapter for the real spine -/

/-- A supported public lock together with one locked completion.  This is the
world shape used to adapt Appendix D locked cores to the real single-message
spine. -/
structure RealM4LockedCoreWorld
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    (C : AppendixDLockedCore PublicLock Quotient LockAux Message) where
  publicLock : PublicLock
  support : C.support publicLock
  completion : C.LockedCompletion publicLock

/-- Hidden witness package for one Appendix D locked completion. -/
structure RealM4LockedCoreWitness
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    (C : AppendixDLockedCore PublicLock Quotient LockAux Message) where
  publicLock : PublicLock
  completion : C.LockedCompletion publicLock

def RealM4LockedCoreWorld.toWitness
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {C : AppendixDLockedCore PublicLock Quotient LockAux Message}
    (omega : RealM4LockedCoreWorld C) :
    RealM4LockedCoreWitness C where
  publicLock := omega.publicLock
  completion := omega.completion

def realM4LockedCoreVerifier
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    (C : AppendixDLockedCore PublicLock Quotient LockAux Message)
    (Y : PublicLock) (W : RealM4LockedCoreWitness C) : Prop :=
  W.publicLock = Y ∧ C.support Y

def realM4LockedCoreWitnessReadout
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {C : AppendixDLockedCore PublicLock Quotient LockAux Message}
    (messageBit : Message -> Bool)
    (W : RealM4LockedCoreWitness C) : Bool :=
  messageBit W.completion.message

def realM4LockedCoreMessageOfPublic
    {PublicLock : Type u} {Message : Type z}
    (publicMessage : PublicLock -> Message)
    (messageBit : Message -> Bool)
    (Y : PublicLock) : Bool :=
  messageBit (publicMessage Y)

theorem realM4LockedCoreWitness_readout_eq_publicMessage
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    (C : AppendixDLockedCore PublicLock Quotient LockAux Message)
    (publicMessage : PublicLock -> Message)
    (messageBit : Message -> Bool)
    (hinvariant : C.PublicMessageInvariant publicMessage)
    {Y : PublicLock} {W : RealM4LockedCoreWitness C}
    (hW : realM4LockedCoreVerifier C Y W) :
    realM4LockedCoreWitnessReadout messageBit W =
      realM4LockedCoreMessageOfPublic publicMessage messageBit Y := by
  rcases hW with ⟨hPublic, hSupportY⟩
  have hSupportW : C.support W.publicLock := by
    simpa [hPublic] using hSupportY
  have hMessage : W.completion.message = publicMessage W.publicLock :=
    hinvariant hSupportW W.completion
  unfold realM4LockedCoreWitnessReadout realM4LockedCoreMessageOfPublic
  rw [hMessage, hPublic]

/-- A public-message invariant adapts an Appendix D locked core to the real
single-message spine.  This proves the wiring from the invariant to the
single-message interface; it does not construct the invariant for M4. -/
def realM4LockedCoreSingleMessageSATSpine
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    (C : AppendixDLockedCore PublicLock Quotient LockAux Message)
    (publicMessage : PublicLock -> Message)
    (messageBit : Message -> Bool)
    (hinvariant : C.PublicMessageInvariant publicMessage) :
    RealSingleMessageSATSpine
      (RealM4LockedCoreWorld C) PublicLock (RealM4LockedCoreWitness C) where
  publicInput := fun omega => omega.publicLock
  witnessOfWorld := fun omega => omega.toWitness
  verifier := realM4LockedCoreVerifier C
  messageOfPublic := realM4LockedCoreMessageOfPublic publicMessage messageBit
  witnessReadout := realM4LockedCoreWitnessReadout messageBit
  target := fun omega =>
    realM4LockedCoreMessageOfPublic publicMessage messageBit omega.publicLock
  worldWitnessValid := by
    intro omega
    exact ⟨rfl, omega.support⟩
  readout_eq_message_of_valid :=
    realM4LockedCoreWitness_readout_eq_publicMessage
      C publicMessage messageBit hinvariant
  target_eq_message := by
    intro omega
    rfl

theorem realM4LockedCore_singleMessage_of_publicMessageInvariant
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    (C : AppendixDLockedCore PublicLock Quotient LockAux Message)
    (publicMessage : PublicLock -> Message)
    (messageBit : Message -> Bool)
    (hinvariant : C.PublicMessageInvariant publicMessage) :
    ∀ w0 w1 : RealM4LockedCoreWorld C,
      w0.publicLock = w1.publicLock ->
        realM4LockedCoreMessageOfPublic publicMessage messageBit w0.publicLock =
          realM4LockedCoreMessageOfPublic publicMessage messageBit w1.publicLock :=
  (realM4LockedCoreSingleMessageSATSpine
    C publicMessage messageBit hinvariant).singleMessage

theorem realM4LockedCore_readout_eq_of_valid_of_publicMessageInvariant
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    (C : AppendixDLockedCore PublicLock Quotient LockAux Message)
    (publicMessage : PublicLock -> Message)
    (messageBit : Message -> Bool)
    (hinvariant : C.PublicMessageInvariant publicMessage)
    {Y : PublicLock} {W W' : RealM4LockedCoreWitness C}
    (hW : realM4LockedCoreVerifier C Y W)
    (hW' : realM4LockedCoreVerifier C Y W') :
    realM4LockedCoreWitnessReadout messageBit W =
      realM4LockedCoreWitnessReadout messageBit W' :=
  (realM4LockedCoreSingleMessageSATSpine
    C publicMessage messageBit hinvariant).readout_eq_of_valid hW hW'

theorem realM4_lockedMessageRigidity_of_publicMessageInvariant
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    (C : AppendixDLockedCore PublicLock Quotient LockAux Message)
    {publicMessage : PublicLock -> Message}
    (hinvariant : C.PublicMessageInvariant publicMessage) :
    C.LockedMessageRigidity :=
  C.lockedMessageRigidity_of_publicMessageInvariant hinvariant

theorem realM4_cnfSingleMessageReadout_of_publicMessageInvariant
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness)
    {publicMessage : PublicLock -> Message}
    (hinvariant : D.core.PublicMessageInvariant publicMessage)
    {Y : Public} (hY : D.support Y) :
    SingleMessageReadout
      (ConcreteCNF.IsSatFormula (D.formula Y)) (D.projection Y) :=
  D.singleMessageReadout_of_lockedMessageRigidity
    (D.core.lockedMessageRigidity_of_publicMessageInvariant hinvariant) hY

theorem realM4_semanticI26_of_publicMessageInvariant
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness)
    {publicMessage : PublicLock -> Message}
    (hinvariant : D.core.PublicMessageInvariant publicMessage)
    {Y : Public} (hY : D.support Y) :
    (∃ α : ConcreteCNF.Assignment (Var Y),
      ConcreteCNF.IsSatFormula (D.formula Y) α) ∧
    (∀ α : ConcreteCNF.Assignment (Var Y),
      ConcreteCNF.IsSatFormula (D.formula Y) α ->
        D.validWitness Y (D.extract Y α)) ∧
    SingleMessageReadout
      (ConcreteCNF.IsSatFormula (D.formula Y)) (D.projection Y) :=
  D.semantic_i26_items_of_lockedMessageRigidity
    (D.core.lockedMessageRigidity_of_publicMessageInvariant hinvariant) hY

theorem realM4_exists_correctForAllSatSearchOutputs_of_publicMessageInvariant
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness)
    {publicMessage : PublicLock -> Message}
    (hinvariant : D.core.PublicMessageInvariant publicMessage)
    {Y : Public} (hY : D.support Y) :
    ∃ msg : Message,
      CorrectForAllSatSearchOutputs
        (ConcreteCNF.IsSatFormula (D.formula Y)) (D.projection Y) msg :=
  D.exists_correctForAllSatSearchOutputs_of_lockedMessageRigidity
    (D.core.lockedMessageRigidity_of_publicMessageInvariant hinvariant) hY

theorem realM4_supportedArbitraryOutputSATSearchCorrect_of_publicMessageInvariant
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness)
    {publicMessage : PublicLock -> Message}
    (hinvariant : D.core.PublicMessageInvariant publicMessage) :
    D.toManuscriptCNFReadoutData.SupportedArbitraryOutputSATSearchCorrect := by
  intro Y hY
  exact
    realM4_exists_correctForAllSatSearchOutputs_of_publicMessageInvariant
      D hinvariant hY

/-! ## Appendix I CNF adapter for the real spine -/

/-- A supported public CNF instance together with a satisfying assignment. -/
structure RealM4CNFWorld
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness) where
  publicInstance : Public
  support : D.support publicInstance
  assignment : ConcreteCNF.Assignment (Var publicInstance)
  sat : ConcreteCNF.IsSatFormula (D.formula publicInstance) assignment

/-- Hidden CNF witness package for the real Appendix I spine. -/
structure RealM4CNFWitness
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness) where
  publicInstance : Public
  assignment : ConcreteCNF.Assignment (Var publicInstance)

def RealM4CNFWorld.toWitness
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness}
    (omega : RealM4CNFWorld D) :
    RealM4CNFWitness D where
  publicInstance := omega.publicInstance
  assignment := omega.assignment

def realM4CNFVerifier
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness)
    (Y : Public) (W : RealM4CNFWitness D) : Prop :=
  D.support Y ∧
    ∃ _hPublic : W.publicInstance = Y,
      ConcreteCNF.IsSatFormula (D.formula W.publicInstance) W.assignment

def realM4CNFWitnessReadout
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness}
    (messageBit : Message -> Bool)
    (W : RealM4CNFWitness D) : Bool :=
  messageBit (D.projection W.publicInstance W.assignment)

def realM4CNFMessageOfPublic
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness)
    (publicMessage : PublicLock -> Message)
    (messageBit : Message -> Bool)
    (Y : Public) : Bool :=
  messageBit (publicMessage (D.publicLock Y))

theorem realM4CNFWitness_readout_eq_publicMessage
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness)
    (publicMessage : PublicLock -> Message)
    (messageBit : Message -> Bool)
    (hinvariant : D.core.PublicMessageInvariant publicMessage)
    {Y : Public} {W : RealM4CNFWitness D}
    (hW : realM4CNFVerifier D Y W) :
    realM4CNFWitnessReadout messageBit W =
      realM4CNFMessageOfPublic D publicMessage messageBit Y := by
  rcases W with ⟨YW, α⟩
  change D.support Y ∧
    ∃ hPublic : YW = Y,
      ConcreteCNF.IsSatFormula (D.formula YW) α at hW
  rcases hW with ⟨hSupportY, ⟨hPublic, hSat⟩⟩
  have hSupportYW : D.support YW := by
    rw [hPublic]
    exact hSupportY
  have hCompletionMessage :
      (D.witnessCompletion (D.extract YW α) (D.cnfSound hSat)).message =
        publicMessage (D.publicLock YW) :=
    hinvariant (D.support_publicLock hSupportYW)
      (D.witnessCompletion (D.extract YW α) (D.cnfSound hSat))
  have hProjection :
      D.projection YW α = publicMessage (D.publicLock Y) := by
    calc
      D.projection YW α =
          D.witnessMessage YW (D.extract YW α) :=
        D.projection_eq_witnessMessage hSat
      _ = (D.witnessCompletion (D.extract YW α) (D.cnfSound hSat)).message :=
        D.witnessMessage_eq_completionMessage (D.cnfSound hSat)
      _ = publicMessage (D.publicLock YW) :=
        hCompletionMessage
      _ = publicMessage (D.publicLock Y) := by rw [hPublic]
  exact congrArg messageBit hProjection

/-- Appendix I CNF assignments form the real single-message SAT spine once the
locked core supplies a public-message invariant.  This is the SAT-assignment
spine; it does not construct the invariant or the polynomial uniformity data. -/
def realM4CNFSingleMessageSATSpine
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness)
    (publicMessage : PublicLock -> Message)
    (messageBit : Message -> Bool)
    (hinvariant : D.core.PublicMessageInvariant publicMessage) :
    RealSingleMessageSATSpine
      (RealM4CNFWorld D) Public (RealM4CNFWitness D) where
  publicInput := fun omega => omega.publicInstance
  witnessOfWorld := fun omega => omega.toWitness
  verifier := realM4CNFVerifier D
  messageOfPublic := realM4CNFMessageOfPublic D publicMessage messageBit
  witnessReadout := realM4CNFWitnessReadout messageBit
  target := fun omega =>
    realM4CNFMessageOfPublic D publicMessage messageBit omega.publicInstance
  worldWitnessValid := by
    intro omega
    exact ⟨omega.support, ⟨rfl, omega.sat⟩⟩
  readout_eq_message_of_valid :=
    realM4CNFWitness_readout_eq_publicMessage
      D publicMessage messageBit hinvariant
  target_eq_message := by
    intro omega
    rfl

theorem realM4CNF_singleMessage_of_publicMessageInvariant
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness)
    (publicMessage : PublicLock -> Message)
    (messageBit : Message -> Bool)
    (hinvariant : D.core.PublicMessageInvariant publicMessage) :
    ∀ w0 w1 : RealM4CNFWorld D,
      w0.publicInstance = w1.publicInstance ->
        realM4CNFMessageOfPublic D publicMessage messageBit w0.publicInstance =
          realM4CNFMessageOfPublic D publicMessage messageBit w1.publicInstance :=
  (realM4CNFSingleMessageSATSpine
    D publicMessage messageBit hinvariant).singleMessage

theorem realM4CNF_readout_eq_of_valid_of_publicMessageInvariant
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness)
    (publicMessage : PublicLock -> Message)
    (messageBit : Message -> Bool)
    (hinvariant : D.core.PublicMessageInvariant publicMessage)
    {Y : Public} {W W' : RealM4CNFWitness D}
    (hW : realM4CNFVerifier D Y W)
    (hW' : realM4CNFVerifier D Y W') :
    realM4CNFWitnessReadout messageBit W =
      realM4CNFWitnessReadout messageBit W' :=
  (realM4CNFSingleMessageSATSpine
    D publicMessage messageBit hinvariant).readout_eq_of_valid
      (W := W) (W' := W') hW hW'

/-! ## Real CNF bit-fixing self-reduction core -/

namespace ConcreteCNF

variable {Var : Type u}

def Literal.var : Literal Var -> Var
  | .pos v => v
  | .neg v => v

def unitLiteral (v : Var) (value : Bool) : Literal Var :=
  if value then Literal.pos v else Literal.neg v

def unitClause (v : Var) (value : Bool) : Clause Var :=
  [unitLiteral v value]

def prefixClauses (pre : List (Var × Bool)) : Formula Var :=
  pre.map (fun fixed => unitClause fixed.1 fixed.2)

def restrictWithPrefix
    (formula : Formula Var) (pre : List (Var × Bool)) :
    Formula Var :=
  formula ++ prefixClauses pre

def FormulaUsesOnly (formula : Formula Var) (vars : List Var) : Prop :=
  ∀ {clause}, clause ∈ formula ->
    ∀ {lit}, lit ∈ clause -> lit.var ∈ vars

theorem isSatClause_unitClause_iff
    (σ : Assignment Var) (v : Var) (value : Bool) :
    IsSatClause (unitClause v value) σ ↔ σ v = value := by
  cases value <;>
    simp [unitClause, unitLiteral, IsSatClause, Literal.eval]

theorem isSatFormula_append_iff
    (formula extra : Formula Var) (σ : Assignment Var) :
    IsSatFormula (formula ++ extra) σ ↔
      IsSatFormula formula σ ∧ IsSatFormula extra σ := by
  constructor
  · intro h
    constructor
    · intro clause hclause
      exact h clause (List.mem_append_left extra hclause)
    · intro clause hclause
      exact h clause (List.mem_append_right formula hclause)
  · intro h clause hclause
    rcases List.mem_append.mp hclause with hformula | hextra
    · exact h.1 clause hformula
    · exact h.2 clause hextra

end ConcreteCNF

namespace CNFPrefix

variable {Var : Type u}

def Satisfied (σ : ConcreteCNF.Assignment Var)
    (pre : List (Var × Bool)) : Prop :=
  ∀ {v value}, (v, value) ∈ pre -> σ v = value

def value [DecidableEq Var] : List (Var × Bool) -> Var -> Bool
  | [], _ => false
  | (u, bit) :: rest, v => if v = u then bit else value rest v

def assignment [DecidableEq Var]
    (pre : List (Var × Bool)) : ConcreteCNF.Assignment Var :=
  fun v => value pre v

theorem satisfied_nil (σ : ConcreteCNF.Assignment Var) :
    Satisfied σ [] := by
  intro v value hmem
  cases hmem

theorem satisfied_append_single
    {σ : ConcreteCNF.Assignment Var} {pre : List (Var × Bool)}
    {v : Var} {value : Bool}
    (hprefix : Satisfied σ pre) (hvalue : σ v = value) :
    Satisfied σ (pre ++ [(v, value)]) := by
  intro u bit hmem
  rcases List.mem_append.mp hmem with hprefixMem | hsingle
  · exact hprefix hprefixMem
  · have hpair : (u, bit) = (v, value) := by
      simpa using hsingle
    cases hpair
    exact hvalue

theorem exists_pair_of_mem_keys
    {pre : List (Var × Bool)} {v : Var}
    (hmem : v ∈ pre.map Prod.fst) :
    ∃ value, (v, value) ∈ pre := by
  induction pre with
  | nil =>
      cases hmem
  | cons head tail ih =>
      rcases head with ⟨u, bit⟩
      simp only [List.map_cons, List.mem_cons] at hmem
      rcases hmem with hhead | htail
      · exact ⟨bit, by simp [hhead]⟩
      · rcases ih htail with ⟨value, hvalue⟩
        exact ⟨value, by simp [hvalue]⟩

theorem value_eq_of_mem [DecidableEq Var]
    {pre : List (Var × Bool)}
    (hnodup : (pre.map Prod.fst).Nodup)
    {v : Var} {bit : Bool} (hmem : (v, bit) ∈ pre) :
    value pre v = bit := by
  induction pre with
  | nil =>
      cases hmem
  | cons head tail ih =>
      rcases head with ⟨u, headBit⟩
      simp only [List.map_cons, List.nodup_cons] at hnodup
      rcases hnodup with ⟨hnotMem, htailNodup⟩
      simp only [List.mem_cons] at hmem
      rcases hmem with hhead | htail
      · cases hhead
        simp [value]
      · have hv_ne_u : v ≠ u := by
          intro hv_eq_u
          apply hnotMem
          have hv_in_tail_keys : v ∈ tail.map Prod.fst := by
            exact List.mem_map.mpr ⟨(v, bit), htail, rfl⟩
          simpa [hv_eq_u] using hv_in_tail_keys
        simp [value, hv_ne_u]
        exact ih htailNodup htail

theorem assignment_eq_of_mem [DecidableEq Var]
    {pre : List (Var × Bool)}
    (hnodup : (pre.map Prod.fst).Nodup)
    {v : Var} {bit : Bool} (hmem : (v, bit) ∈ pre) :
    assignment pre v = bit :=
  value_eq_of_mem hnodup hmem

end CNFPrefix

namespace ConcreteCNF

variable {Var : Type u}

theorem isSatFormula_prefixClauses_iff
    (pre : List (Var × Bool)) (σ : Assignment Var) :
    IsSatFormula (prefixClauses pre) σ ↔
      CNFPrefix.Satisfied σ pre := by
  constructor
  · intro h v value hmem
    have hclause :
        unitClause v value ∈ prefixClauses pre := by
      exact List.mem_map.mpr ⟨(v, value), hmem, rfl⟩
    exact (isSatClause_unitClause_iff σ v value).mp (h _ hclause)
  · intro hprefix clause hclause
    rcases List.mem_map.mp hclause with ⟨fixed, hfixed, hclauseEq⟩
    rcases fixed with ⟨v, value⟩
    cases hclauseEq
    exact (isSatClause_unitClause_iff σ v value).mpr (hprefix hfixed)

theorem isSatFormula_restrictWithPrefix_iff
    (formula : Formula Var) (pre : List (Var × Bool))
    (σ : Assignment Var) :
    IsSatFormula (restrictWithPrefix formula pre) σ ↔
      IsSatFormula formula σ ∧ CNFPrefix.Satisfied σ pre := by
  rw [restrictWithPrefix, isSatFormula_append_iff,
    isSatFormula_prefixClauses_iff]

theorem isSatFormula_of_agree_on_formulaUsesOnly
    {formula : Formula Var} {vars : List Var}
    {σ τ : Assignment Var}
    (hvars : FormulaUsesOnly formula vars)
    (hσ : IsSatFormula formula σ)
    (hagree : ∀ {v : Var}, v ∈ vars -> τ v = σ v) :
    IsSatFormula formula τ := by
  intro clause hclause
  rcases hσ clause hclause with ⟨lit, hlit, heval⟩
  refine ⟨lit, hlit, ?_⟩
  have hvar : lit.var ∈ vars := hvars hclause hlit
  cases lit with
  | pos v =>
      have hag : τ v = σ v := hagree (by simpa [Literal.var] using hvar)
      simpa [Literal.eval, hag] using heval
  | neg v =>
      have hag : τ v = σ v := hagree (by simpa [Literal.var] using hvar)
      simpa [Literal.eval, hag] using heval

end ConcreteCNF

def RealCNFRestrictedSatisfiable
    {Var : Type u} (formula : ConcreteCNF.Formula Var)
    (pre : List (Var × Bool)) : Prop :=
  ∃ σ : ConcreteCNF.Assignment Var,
    ConcreteCNF.IsSatFormula formula σ ∧ CNFPrefix.Satisfied σ pre

/-- Explicit P=NP-side SAT decider object for real CNF formulas at a fixed
variable type.  The program and clock fields are charged by the constant
decoder cost model below; the theorem remains conditional on this object. -/
structure RealCNFPNPSATDecider (Var : Type u) where
  decideSat : ConcreteCNF.Formula Var -> Bool
  decidesSat :
    ∀ formula, decideSat formula = true ↔
      ∃ σ : ConcreteCNF.Assignment Var,
        ConcreteCNF.IsSatFormula formula σ
  programLength : Nat
  clockExponent : Nat
  clockExponent_pos : 0 < clockExponent

theorem realCNFRestricted_decideSat_true_iff
    {Var : Type u} (D : RealCNFPNPSATDecider Var)
    (formula : ConcreteCNF.Formula Var)
    (pre : List (Var × Bool)) :
    D.decideSat (ConcreteCNF.restrictWithPrefix formula pre) = true ↔
      RealCNFRestrictedSatisfiable formula pre := by
  constructor
  · intro hdec
    rcases (D.decidesSat _).mp hdec with ⟨σ, hσ⟩
    exact
      ⟨σ, (ConcreteCNF.isSatFormula_restrictWithPrefix_iff
        formula pre σ).mp hσ⟩
  · intro hsat
    rcases hsat with ⟨σ, hσ⟩
    exact
      (D.decidesSat _).mpr
        ⟨σ, (ConcreteCNF.isSatFormula_restrictWithPrefix_iff
          formula pre σ).mpr hσ⟩

def realCNFBitFixPrefixAux
    {Var : Type u} (D : RealCNFPNPSATDecider Var)
    (formula : ConcreteCNF.Formula Var) :
    List (Var × Bool) -> List Var -> List (Var × Bool)
  | pre, [] => pre
  | pre, v :: vars =>
      let falsePrefix := pre ++ [(v, false)]
      if D.decideSat (ConcreteCNF.restrictWithPrefix formula falsePrefix) then
        realCNFBitFixPrefixAux D formula falsePrefix vars
      else
        realCNFBitFixPrefixAux D formula (pre ++ [(v, true)]) vars

def realCNFBitFixPrefix
    {Var : Type u} (D : RealCNFPNPSATDecider Var)
    (formula : ConcreteCNF.Formula Var) (vars : List Var) :
    List (Var × Bool) :=
  realCNFBitFixPrefixAux D formula [] vars

def realCNFBitFixAssignment
    {Var : Type u} [DecidableEq Var]
    (D : RealCNFPNPSATDecider Var)
    (formula : ConcreteCNF.Formula Var) (vars : List Var) :
    ConcreteCNF.Assignment Var :=
  CNFPrefix.assignment (realCNFBitFixPrefix D formula vars)

theorem realCNFBitFixPrefixAux_keys
    {Var : Type u} (D : RealCNFPNPSATDecider Var)
    (formula : ConcreteCNF.Formula Var)
    (pre : List (Var × Bool)) (vars : List Var) :
    (realCNFBitFixPrefixAux D formula pre vars).map Prod.fst =
      pre.map Prod.fst ++ vars := by
  induction vars generalizing pre with
  | nil =>
      simp [realCNFBitFixPrefixAux]
  | cons v vars ih =>
      unfold realCNFBitFixPrefixAux
      by_cases hdec :
          D.decideSat
            (ConcreteCNF.restrictWithPrefix formula
              (pre ++ [(v, false)])) = true
      · simp [hdec, ih, List.map_append, List.append_assoc]
      · simp [hdec, ih, List.map_append, List.append_assoc]

theorem realCNFBitFixPrefixAux_satisfiable
    {Var : Type u} (D : RealCNFPNPSATDecider Var)
    {formula : ConcreteCNF.Formula Var}
    {pre : List (Var × Bool)} {vars : List Var}
    (hSat : RealCNFRestrictedSatisfiable formula pre) :
    RealCNFRestrictedSatisfiable formula
      (realCNFBitFixPrefixAux D formula pre vars) := by
  induction vars generalizing pre with
  | nil =>
      simpa [realCNFBitFixPrefixAux] using hSat
  | cons v vars ih =>
      unfold realCNFBitFixPrefixAux
      by_cases hdec :
          D.decideSat
            (ConcreteCNF.restrictWithPrefix formula
              (pre ++ [(v, false)])) = true
      · simp [hdec]
        exact ih ((realCNFRestricted_decideSat_true_iff
          D formula (pre ++ [(v, false)])).mp hdec)
      · simp [hdec]
        apply ih
        rcases hSat with ⟨σ, hformula, hprefix⟩
        by_cases hvFalse : σ v = false
        · have hFalseSat :
            RealCNFRestrictedSatisfiable formula
              (pre ++ [(v, false)]) :=
            ⟨σ, hformula,
              CNFPrefix.satisfied_append_single hprefix hvFalse⟩
          exact False.elim
            (hdec ((realCNFRestricted_decideSat_true_iff
              D formula (pre ++ [(v, false)])).mpr hFalseSat))
        · have hvTrue : σ v = true := by
            cases hσv : σ v <;> simp [hσv] at hvFalse ⊢
          exact
            ⟨σ, hformula,
              CNFPrefix.satisfied_append_single hprefix hvTrue⟩

theorem realCNFBitFixAssignment_satisfies
    {Var : Type u} [DecidableEq Var]
    (D : RealCNFPNPSATDecider Var)
    {formula : ConcreteCNF.Formula Var} {vars : List Var}
    (hvars : ConcreteCNF.FormulaUsesOnly formula vars)
    (hnodup : vars.Nodup)
    (hSat : ∃ σ : ConcreteCNF.Assignment Var,
      ConcreteCNF.IsSatFormula formula σ) :
    ConcreteCNF.IsSatFormula formula
      (realCNFBitFixAssignment D formula vars) := by
  have hStart : RealCNFRestrictedSatisfiable formula [] := by
    rcases hSat with ⟨σ, hσ⟩
    exact ⟨σ, hσ, CNFPrefix.satisfied_nil σ⟩
  have hFinal :
      RealCNFRestrictedSatisfiable formula
        (realCNFBitFixPrefix D formula vars) := by
    simpa [realCNFBitFixPrefix] using
      (realCNFBitFixPrefixAux_satisfiable
        D (formula := formula) (pre := []) (vars := vars) hStart)
  rcases hFinal with ⟨σ, hσformula, hσpre⟩
  apply ConcreteCNF.isSatFormula_of_agree_on_formulaUsesOnly
    hvars hσformula
  intro v hv
  let finalPrefix := realCNFBitFixPrefix D formula vars
  have hkeys : finalPrefix.map Prod.fst = vars := by
    simpa [finalPrefix, realCNFBitFixPrefix] using
      (realCNFBitFixPrefixAux_keys
        D formula ([] : List (Var × Bool)) vars)
  have hprefixNodup : (finalPrefix.map Prod.fst).Nodup := by
    simpa [hkeys] using hnodup
  have hvKey : v ∈ finalPrefix.map Prod.fst := by
    simpa [hkeys] using hv
  rcases CNFPrefix.exists_pair_of_mem_keys hvKey with ⟨bit, hbit⟩
  have hAssignment :
      realCNFBitFixAssignment D formula vars v = bit := by
    simpa [realCNFBitFixAssignment, finalPrefix] using
      (CNFPrefix.assignment_eq_of_mem hprefixNodup hbit)
  have hSigma : σ v = bit := hσpre hbit
  exact hAssignment.trans hSigma.symm

theorem realM4_bitFixingAssignment_satisfies
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness)
    {Y : Public} (hY : D.support Y)
    [DecidableEq (Var Y)]
    (A : RealCNFPNPSATDecider (Var Y))
    (vars : List (Var Y))
    (hvars : ConcreteCNF.FormulaUsesOnly (D.formula Y) vars)
    (hnodup : vars.Nodup) :
    ConcreteCNF.IsSatFormula (D.formula Y)
      (realCNFBitFixAssignment A (D.formula Y) vars) :=
  realCNFBitFixAssignment_satisfies A hvars hnodup (D.satOnSupport hY)

theorem realM4_bitFixingReadout_eq_publicMessage_of_publicMessageInvariant
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness)
    {publicMessage : PublicLock -> Message}
    (hinvariant : D.core.PublicMessageInvariant publicMessage)
    {Y : Public} (hY : D.support Y)
    [DecidableEq (Var Y)]
    (A : RealCNFPNPSATDecider (Var Y))
    (vars : List (Var Y))
    (hvars : ConcreteCNF.FormulaUsesOnly (D.formula Y) vars)
    (hnodup : vars.Nodup) :
    D.projection Y (realCNFBitFixAssignment A (D.formula Y) vars) =
      publicMessage (D.publicLock Y) := by
  let α := realCNFBitFixAssignment A (D.formula Y) vars
  have hα :
      ConcreteCNF.IsSatFormula (D.formula Y) α :=
    realM4_bitFixingAssignment_satisfies
      D hY A vars hvars hnodup
  have hValid : D.validWitness Y (D.extract Y α) :=
    D.cnfSound hα
  calc
    D.projection Y α = D.witnessMessage Y (D.extract Y α) :=
      D.projection_eq_witnessMessage hα
    _ = (D.witnessCompletion (D.extract Y α) hValid).message :=
      D.witnessMessage_eq_completionMessage hValid
    _ = publicMessage (D.publicLock Y) :=
      hinvariant (D.support_publicLock hY)
        (D.witnessCompletion (D.extract Y α) hValid)

/-- Family-level packaging of the real Appendix I data needed by the CNF
bit-fixing self-reduction.  It records, for each public instance, an ordered
finite variable cover for the CNF formula and an explicit P=NP-side SAT
decider, together with a uniform program-length bound for that decider family.
-/
structure RealM4CNFUniformBitFixingData
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness) where
  varDecidable : (Y : Public) -> DecidableEq (Var Y)
  varOrder : (Y : Public) -> List (Var Y)
  varOrder_nodup : ∀ Y : Public, (varOrder Y).Nodup
  formulaUsesOnly :
    ∀ {Y : Public}, D.support Y ->
      ConcreteCNF.FormulaUsesOnly (D.formula Y) (varOrder Y)
  satDecider : (Y : Public) -> RealCNFPNPSATDecider (Var Y)
  programLengthBound : Nat
  satDecider_programLength_le :
    ∀ Y : Public, (satDecider Y).programLength ≤ programLengthBound

namespace RealM4CNFUniformBitFixingData

variable {PublicLock : Type u} {Quotient : Type v}
variable {LockAux : Type w} {Message : Type z}
variable {Public : Type x} {Var : Public -> Type y}
variable {Witness : Public -> Type y}
variable
  {D : AppendixICNFReadoutData
    PublicLock Quotient LockAux Message Public Var Witness}

def bitFixingAssignment
    (U : RealM4CNFUniformBitFixingData D) (Y : Public) :
    ConcreteCNF.Assignment (Var Y) := by
  letI := U.varDecidable Y
  exact realCNFBitFixAssignment (U.satDecider Y) (D.formula Y) (U.varOrder Y)

theorem bitFixingAssignment_satisfies
    (U : RealM4CNFUniformBitFixingData D)
    {Y : Public} (hY : D.support Y) :
    ConcreteCNF.IsSatFormula (D.formula Y)
      (U.bitFixingAssignment Y) := by
  dsimp [bitFixingAssignment]
  letI := U.varDecidable Y
  exact
    realM4_bitFixingAssignment_satisfies
      D hY (U.satDecider Y) (U.varOrder Y)
      (U.formulaUsesOnly hY) (U.varOrder_nodup Y)

end RealM4CNFUniformBitFixingData

theorem realM4_uniformBitFixingAssignment_satisfies
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness)
    (U : RealM4CNFUniformBitFixingData D)
    {Y : Public} (hY : D.support Y) :
    ConcreteCNF.IsSatFormula (D.formula Y)
      (U.bitFixingAssignment Y) :=
  U.bitFixingAssignment_satisfies hY

theorem realM4_uniformBitFixingReadout_eq_publicMessage_of_publicMessageInvariant
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness)
    (U : RealM4CNFUniformBitFixingData D)
    {publicMessage : PublicLock -> Message}
    (hinvariant : D.core.PublicMessageInvariant publicMessage)
    {Y : Public} (hY : D.support Y) :
    D.projection Y (U.bitFixingAssignment Y) =
      publicMessage (D.publicLock Y) := by
  dsimp [RealM4CNFUniformBitFixingData.bitFixingAssignment]
  letI := U.varDecidable Y
  exact
    realM4_bitFixingReadout_eq_publicMessage_of_publicMessageInvariant
      D hinvariant hY (U.satDecider Y) (U.varOrder Y)
      (U.formulaUsesOnly hY) (U.varOrder_nodup Y)

def realCNFRestrictedFormulaCompilerProgramLength : Nat :=
  1

def realCNFBitFixingDriverProgramLength : Nat :=
  1

def realCNFReadoutProgramLength : Nat :=
  1

def realCNFSelfReductionDecoderCost
    {Var : Type u} (D : RealCNFPNPSATDecider Var) : Nat :=
  D.programLength +
    realCNFRestrictedFormulaCompilerProgramLength +
      realCNFBitFixingDriverProgramLength +
        realCNFReadoutProgramLength

def realCNFConstantDecoderKpolyAt
    {Var : Type u} (D : RealCNFPNPSATDecider Var) : Nat -> Nat :=
  fun _targetBlocks => realCNFSelfReductionDecoderCost D

def realCNFLinearEtaTimes (eta : Nat) : Nat -> Nat :=
  fun targetBlocks => eta * targetBlocks

theorem realCNFConstantDecoderKpolyAt_eq
    {Var : Type u} (D : RealCNFPNPSATDecider Var) (targetBlocks : Nat) :
    realCNFConstantDecoderKpolyAt D targetBlocks =
      realCNFSelfReductionDecoderCost D :=
  rfl

def realM4UniformSelfReductionDecoderCost
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness}
    (U : RealM4CNFUniformBitFixingData D) : Nat :=
  U.programLengthBound +
    realCNFRestrictedFormulaCompilerProgramLength +
      realCNFBitFixingDriverProgramLength +
        realCNFReadoutProgramLength

theorem realM4UniformSelfReductionDecoderCost_bounds_instance
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness}
    (U : RealM4CNFUniformBitFixingData D) (Y : Public) :
    realCNFSelfReductionDecoderCost (U.satDecider Y) ≤
      realM4UniformSelfReductionDecoderCost U := by
  unfold realCNFSelfReductionDecoderCost
    realM4UniformSelfReductionDecoderCost
  exact
    Nat.add_le_add_right
      (Nat.add_le_add_right
        (Nat.add_le_add_right
          (U.satDecider_programLength_le Y)
          realCNFRestrictedFormulaCompilerProgramLength)
        realCNFBitFixingDriverProgramLength)
      realCNFReadoutProgramLength

def realM4UniformConstantDecoderKpolyAt
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness}
    (U : RealM4CNFUniformBitFixingData D) : Nat -> Nat :=
  fun _targetBlocks => realM4UniformSelfReductionDecoderCost U

theorem realM4UniformConstantDecoderKpolyAt_eq
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness}
    (U : RealM4CNFUniformBitFixingData D) (targetBlocks : Nat) :
    realM4UniformConstantDecoderKpolyAt U targetBlocks =
      realM4UniformSelfReductionDecoderCost U :=
  rfl

structure RealCNFConstantDecoderRegime
    {Var : Type u} (F : CompressionLowerFramework)
    (D : RealCNFPNPSATDecider Var) where
  eta : Nat
  kpolyAt_eq : F.kpolyAt = realCNFConstantDecoderKpolyAt D
  etaTimes_eq : F.etaTimes = realCNFLinearEtaTimes eta
  floor_dominates_decoder :
    realCNFSelfReductionDecoderCost D < eta * F.targetBlocks

/-- Construction-side discharge of the upper inequality once the real lower
framework's `kpolyAt` is identified with the fixed CNF bit-fixing decoder.
The theorem is conditional on the explicit P=NP SAT decider object. -/
theorem realCNF_selfReductionUpperHypothesis_givenPNP
    {Var : Type u} {F : CompressionLowerFramework}
    (D : RealCNFPNPSATDecider Var)
    (R : RealCNFConstantDecoderRegime F D) :
    SelfReductionUpperHypothesis F where
  upperStrictlyBelowCompressionFloor := by
    rw [R.kpolyAt_eq, R.etaTimes_eq]
    exact R.floor_dominates_decoder

structure RealM4UniformConstantDecoderRegime
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness}
    (F : CompressionLowerFramework)
    (U : RealM4CNFUniformBitFixingData D) where
  eta : Nat
  kpolyAt_eq : F.kpolyAt = realM4UniformConstantDecoderKpolyAt U
  etaTimes_eq : F.etaTimes = realCNFLinearEtaTimes eta
  floor_dominates_decoder :
    realM4UniformSelfReductionDecoderCost U < eta * F.targetBlocks

/-- Family-level real upper-side discharge, conditional on explicit P=NP SAT
deciders and a uniform program-length bound for the Appendix I bit-fixing
decoder family.  The real lower framework must still identify its `kpolyAt`
with this uniform constant decoder cost. -/
theorem realM4_uniformSelfReductionUpperHypothesis_givenPNP
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness}
    {F : CompressionLowerFramework}
    (U : RealM4CNFUniformBitFixingData D)
    (R : RealM4UniformConstantDecoderRegime F U) :
    SelfReductionUpperHypothesis F where
  upperStrictlyBelowCompressionFloor := by
    rw [R.kpolyAt_eq, R.etaTimes_eq]
    exact R.floor_dominates_decoder

/-! ## Real-M4 lift ledger -/

inductive RealM4LiftStatus where
  | constructionTransferred
  | partialConstructionTransferred
  | openConstruction
  | blockedByCounterexample
  | irreducibleInput
  | pnpConditionalInput
deriving DecidableEq, Repr

structure RealM4LiftLedgerRow where
  item : String
  status : RealM4LiftStatus
  checkedName : String
  note : String
deriving Repr

/-- Current real-ensemble lift ledger.  The theorem above transfers the
single-message readout spine to the real linear public surface.  The remaining
M4 construction obligations are deliberately not collapsed into the four
irreducible mathematical inputs. -/
def realM4LiftLedger : List RealM4LiftLedgerRow := [
  {
    item := "singleMessageSpine"
    status := .constructionTransferred
    checkedName := "v13RealLinearSingleMessageSATSpine_singleMessage"
    note := "The real linear public instance fixes the target bit and valid witnesses read the same public message."
  },
  {
    item := "publicMessageInvariantAdapter"
    status := .constructionTransferred
    checkedName := "realM4LockedCoreSingleMessageSATSpine"
    note := "Given a public-message invariant, the Appendix D locked core maps into the real single-message spine and Appendix I CNF readout."
  },
  {
    item := "appendixICNFSpineAdapter"
    status := .constructionTransferred
    checkedName := "realM4CNFSingleMessageSATSpine"
    note := "Given the same public-message invariant, satisfying Appendix I CNF assignments form the real single-message SAT spine."
  },
  {
    item := "appendixISATSearchReadoutAdapter"
    status := .constructionTransferred
    checkedName := "realM4_supportedArbitraryOutputSATSearchCorrect_of_publicMessageInvariant"
    note := "Given the same public-message invariant, the Appendix I projection is correct for every satisfying assignment that SAT search may return."
  },
  {
    item := "cnfBitFixingSelfReduction"
    status := .constructionTransferred
    checkedName := "realM4_bitFixingReadout_eq_publicMessage_of_publicMessageInvariant"
    note := "Given a public-message invariant, a finite variable cover, and an explicit SAT decider, CNF bit-fixing produces a satisfying assignment whose projection is the public message."
  },
  {
    item := "uniformCNFBitFixingPackage"
    status := .partialConstructionTransferred
    checkedName := "realM4_uniformBitFixingReadout_eq_publicMessage_of_publicMessageInvariant"
    note := "The family-level adapter is checked once Appendix I supplies variable orders, formula coverage, explicit SAT deciders, and a uniform program-length bound."
  },
  {
    item := "constantDecoderUpperInequality"
    status := .partialConstructionTransferred
    checkedName := "realM4_uniformSelfReductionUpperHypothesis_givenPNP"
    note := "The uniform CNF bit-fixing decoder gives the formal upper inequality once the real lower framework identifies kpolyAt with this constant decoder cost."
  },
  {
    item := "deterministicReadoutOnly"
    status := .blockedByCounterexample
    checkedName := "lockedCoreIdentityReadoutFamily_lab_refutation"
    note := "Deterministic per-state readout alone does not supply cross-completion message rigidity."
  },
  {
    item := "publicMessageInvariant"
    status := .openConstruction
    checkedName := "lockedCorePublicMessageInvariant_lab_guardrails"
    note := "A real M4 lock needs a public-message invariant or equivalent cross-completion rigidity theorem."
  },
  {
    item := "noPublicTargetTags"
    status := .partialConstructionTransferred
    checkedName := "v13RealLinear_publicSurfaceCertificate"
    note := "The real linear surface proves no elementary public coordinate determines the target; the full neutral-skeleton/opposite-pair field remains to be packaged for M4."
  },
  {
    item := "atomCompleteness"
    status := .openConstruction
    checkedName := "GaugeBufferedLockedInterface.atomCompleteness"
    note := "The M4 raw evidence atoms still need a concrete CD-ENF completeness proof."
  },
  {
    item := "gaugeFaithfulness"
    status := .openConstruction
    checkedName := "GaugeBufferedLockedInterface.gaugeFaithfulness"
    note := "The M4 hidden-gauge leaves still need a concrete faithfulness proof."
  },
  {
    item := "hiddenGaugeProduct"
    status := .openConstruction
    checkedName := "GaugeBufferedLockedInterface.hiddenGaugeProduct"
    note := "The M4 hidden-gauge product law is not yet constructed."
  },
  {
    item := "admissibleHistories"
    status := .openConstruction
    checkedName := "GaugeBufferedLockedInterface.admissibleHistories"
    note := "The M4 history field still needs balance and balanced-conditioning proofs."
  },
  {
    item := "realCompressionLowerFramework"
    status := .openConstruction
    checkedName := "CompressionLowerFramework"
    note := "The real lower framework must use manuscript compression-from-success data, not toy dummy budgets."
  },
  {
    item := "selfReductionUpper"
    status := .openConstruction
    checkedName := "SelfReductionUpperHypothesis"
    note := "The real SAT bit-fixing decoder should be construction-proved from an explicit P=NP decider once the M4 restricted formulas and program model exist."
  },
  {
    item := "pnpDecider"
    status := .pnpConditionalInput
    checkedName := "explicit SAT decider object"
    note := "This is the P=NP-side conditional object for the upper self-reduction, not irreducible lower-bound content."
  },
  {
    item := "starSWHardness"
    status := .irreducibleInput
    checkedName := "CompressionStarSWHardness"
    note := "Irreducible SW-shaped hardness input after the construction layer is real."
  },
  {
    item := "safeQSSM"
    status := .irreducibleInput
    checkedName := "SafeQSSMFrontier"
    note := "Irreducible analytic input after the construction layer is real."
  },
  {
    item := "boundedGaugeIncidence"
    status := .irreducibleInput
    checkedName := "BoundedGaugeIncidenceFrontier"
    note := "Irreducible analytic input after the construction layer is real."
  },
  {
    item := "boundaryMixing"
    status := .irreducibleInput
    checkedName := "BoundaryMixingFrontier"
    note := "Irreducible analytic input after the construction layer is real."
  }
]

theorem realM4LiftLedger_statuses_exact :
    List.map (fun row => row.status) realM4LiftLedger =
      [ RealM4LiftStatus.constructionTransferred,
        RealM4LiftStatus.constructionTransferred,
        RealM4LiftStatus.constructionTransferred,
        RealM4LiftStatus.constructionTransferred,
        RealM4LiftStatus.constructionTransferred,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.blockedByCounterexample,
        RealM4LiftStatus.openConstruction,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.openConstruction,
        RealM4LiftStatus.openConstruction,
        RealM4LiftStatus.openConstruction,
        RealM4LiftStatus.openConstruction,
        RealM4LiftStatus.openConstruction,
        RealM4LiftStatus.openConstruction,
        RealM4LiftStatus.pnpConditionalInput,
        RealM4LiftStatus.irreducibleInput,
        RealM4LiftStatus.irreducibleInput,
        RealM4LiftStatus.irreducibleInput,
        RealM4LiftStatus.irreducibleInput] := by
  rfl

def realM4OpenConstructionItems : List String := [
  "publicMessageInvariant",
  "noPublicTargetTags",
  "atomCompleteness",
  "gaugeFaithfulness",
  "hiddenGaugeProduct",
  "admissibleHistories",
  "realCompressionLowerFramework",
  "selfReductionUpper"
]

theorem realM4OpenConstructionItems_exact :
    realM4OpenConstructionItems =
      [ "publicMessageInvariant",
        "noPublicTargetTags",
        "atomCompleteness",
        "gaugeFaithfulness",
        "hiddenGaugeProduct",
        "admissibleHistories",
        "realCompressionLowerFramework",
        "selfReductionUpper" ] := by
  rfl

def realM4AfterConstructionIrreducibleInputs : List String := [
  "starSWHardness",
  "safeQSSM",
  "boundedGaugeIncidence",
  "boundaryMixing"
]

theorem realM4AfterConstructionIrreducibleInputs_exact :
    realM4AfterConstructionIrreducibleInputs =
      [ "starSWHardness",
        "safeQSSM",
        "boundedGaugeIncidence",
        "boundaryMixing" ] := by
  rfl

/-- Guardrail imported into the real lift: deterministic readout by itself has
a checked finite counterexample, so M4 must provide public-message invariance
or an equivalent cross-completion rigidity theorem before SAT-search promotion. -/
theorem realM4_deterministicReadoutOnly_counterexample :
    ∃ C : AppendixDLockedCore Unit Bool Unit Bool,
      C.LockSatisfiable ∧ C.ReadDeterministic ∧
        ¬ C.LockedMessageRigidity :=
  lockedCoreLabCanaries_separate_readDeterministic_from_lockedMessageRigidity.2

theorem realM4_publicMessageInvariant_guardrails :
    (rigidAppendixDLockedCore.PublicMessageInvariant
        rigidAppendixDLockedCore_publicMessage ∧
      rigidAppendixDLockedCore.LockedMessageRigidity) ∧
      (∀ publicMessage : Unit -> Bool,
        ¬ ambiguousAppendixDLockedCore.PublicMessageInvariant publicMessage) ∧
      ¬ ambiguousAppendixDLockedCore.LockedMessageRigidity :=
  lockedCorePublicMessageInvariant_lab_guardrails

end Mettapedia.Computability.PNP

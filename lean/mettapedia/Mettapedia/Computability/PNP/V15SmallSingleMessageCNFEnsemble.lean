import Mettapedia.Computability.PNP.PNPv13ManuscriptCNFReadoutCore
import Mettapedia.Computability.PNP.V15RealEnsembleSpine

/-!
# PNP v15: small concrete single-message CNF ensemble

This file gives a concrete finite CNF/SAT ensemble rather than an endpoint
wrapper.  The public instance is a Boolean message bit `Y`; the CNF is the
single unit clause forcing one assignment variable to equal `M(Y) = Y`, and the
CNF-level readout reads that assignment variable.  This is not the manuscript
M4 construction; it is the smallest concrete single-message CNF anchor for the
readout interface.
-/

namespace Mettapedia.Computability.PNP

/-- Public instances for the small concrete ensemble: the public bit is the
message bit. -/
abbrev SmallSingleMessagePublic :=
  Bool

/-- One Boolean CNF variable for each public instance. -/
abbrev SmallSingleMessageVar (_Y : SmallSingleMessagePublic) :=
  Fin 1

/-- The hidden witness type is singleton-valued for each public instance. -/
abbrev SmallSingleMessageWitness (_Y : SmallSingleMessagePublic) :=
  Unit

/-- The fixed public message readout `M(Y)`. -/
def smallSingleMessageM (Y : SmallSingleMessagePublic) : Bool :=
  Y

/-- The concrete CNF `F_Y`: a single unit clause locking the assignment bit to
`M(Y)`. -/
def smallSingleMessageFormula :
    (Y : SmallSingleMessagePublic) →
      ConcreteCNF.Formula (SmallSingleMessageVar Y)
  | false => [[ConcreteCNF.Literal.neg (0 : Fin 1)]]
  | true => [[ConcreteCNF.Literal.pos (0 : Fin 1)]]

/-- Every public instance is in support for this finite ensemble. -/
def smallSingleMessageSupport (_Y : SmallSingleMessagePublic) : Prop :=
  True

/-- Semantic verifier relation for the unique hidden witness. -/
def smallSingleMessageVerifier
    (_Y : SmallSingleMessagePublic)
    (_W : SmallSingleMessageWitness _Y) : Prop :=
  True

/-- Executable verifier program for the small ensemble.  It accepts the unique
hidden witness in constant time. -/
def smallSingleMessageVerifierDecision
    (Y : SmallSingleMessagePublic)
    (_W : SmallSingleMessageWitness Y) : Bool :=
  true

/-- The executable verifier decides the semantic verifier relation. -/
theorem smallSingleMessageVerifierDecision_correct
    {Y : SmallSingleMessagePublic}
    {_W : SmallSingleMessageWitness Y} :
    smallSingleMessageVerifierDecision Y _W = true ↔
      smallSingleMessageVerifier Y _W := by
  simp [smallSingleMessageVerifierDecision, smallSingleMessageVerifier]

/-- The satisfying assignment selected by the construction: set the single CNF
variable to `M(Y)`. -/
def smallSingleMessageAssignment
    (Y : SmallSingleMessagePublic) :
    ConcreteCNF.Assignment (SmallSingleMessageVar Y) :=
  fun _ => smallSingleMessageM Y

/-- Extract the unique semantic witness from any CNF assignment. -/
def smallSingleMessageExtract
    (Y : SmallSingleMessagePublic)
    (_α : ConcreteCNF.Assignment (SmallSingleMessageVar Y)) :
    SmallSingleMessageWitness Y :=
  ()

/-- Semantic message carried by the unique witness. -/
def smallSingleMessageWitnessMessage
    (Y : SmallSingleMessagePublic)
    (_W : SmallSingleMessageWitness Y) : Bool :=
  smallSingleMessageM Y

/-- CNF-level message readout: read the single assignment bit. -/
def smallSingleMessageProjection
    (Y : SmallSingleMessagePublic)
    (α : ConcreteCNF.Assignment (SmallSingleMessageVar Y)) : Bool :=
  α 0

/-- The construction's assignment satisfies the concrete CNF. -/
theorem smallSingleMessageFormula_satisfied_messageAssignment
    (Y : SmallSingleMessagePublic) :
    ConcreteCNF.IsSatFormula
      (smallSingleMessageFormula Y)
      (smallSingleMessageAssignment Y) := by
  cases Y
  · intro clause hclause
    rw [smallSingleMessageFormula] at hclause
    simp only [List.mem_singleton] at hclause
    rw [hclause]
    exact
      ⟨ConcreteCNF.Literal.neg (0 : Fin 1), by simp,
        by simp [ConcreteCNF.Literal.eval, smallSingleMessageAssignment,
          smallSingleMessageM]⟩
  · intro clause hclause
    rw [smallSingleMessageFormula] at hclause
    simp only [List.mem_singleton] at hclause
    rw [hclause]
    exact
      ⟨ConcreteCNF.Literal.pos (0 : Fin 1), by simp,
        by simp [ConcreteCNF.Literal.eval, smallSingleMessageAssignment,
          smallSingleMessageM]⟩

/-- Any satisfying assignment has its single variable locked to `M(Y)`. -/
theorem smallSingleMessageFormula_forces_message
    {Y : SmallSingleMessagePublic}
    {α : ConcreteCNF.Assignment (SmallSingleMessageVar Y)}
    (hα :
      ConcreteCNF.IsSatFormula
        (smallSingleMessageFormula Y) α) :
    α 0 = smallSingleMessageM Y := by
  cases Y
  · have hclause :
        ConcreteCNF.IsSatClause
          [ConcreteCNF.Literal.neg (0 : Fin 1)] α := by
      exact hα [ConcreteCNF.Literal.neg (0 : Fin 1)] (by simp [smallSingleMessageFormula])
    rcases hclause with ⟨lit, hlit, heval⟩
    simp only [List.mem_singleton] at hlit
    subst lit
    cases hbit : α 0 <;>
      simp [ConcreteCNF.Literal.eval, smallSingleMessageM, hbit] at heval ⊢
  · have hclause :
        ConcreteCNF.IsSatClause
          [ConcreteCNF.Literal.pos (0 : Fin 1)] α := by
      exact hα [ConcreteCNF.Literal.pos (0 : Fin 1)] (by simp [smallSingleMessageFormula])
    rcases hclause with ⟨lit, hlit, heval⟩
    simp only [List.mem_singleton] at hlit
    subst lit
    simpa [ConcreteCNF.Literal.eval, smallSingleMessageM] using heval

/-- The CNF readout on any satisfying assignment returns the fixed message
`M(Y)`. -/
theorem smallSingleMessageProjection_eq_M_of_sat
    {Y : SmallSingleMessagePublic}
    {α : ConcreteCNF.Assignment (SmallSingleMessageVar Y)}
    (hα :
      ConcreteCNF.IsSatFormula
        (smallSingleMessageFormula Y) α) :
    smallSingleMessageProjection Y α = smallSingleMessageM Y := by
  exact smallSingleMessageFormula_forces_message hα

/-- The concrete small ensemble instantiated in the manuscript CNF readout
interface. -/
def smallSingleMessageCNFReadoutData :
    ManuscriptCNFReadoutData
      SmallSingleMessagePublic
      SmallSingleMessageVar
      SmallSingleMessageWitness
      Bool where
  support := smallSingleMessageSupport
  formula := smallSingleMessageFormula
  validWitness := smallSingleMessageVerifier
  extract := smallSingleMessageExtract
  witnessMessage := smallSingleMessageWitnessMessage
  projection := smallSingleMessageProjection
  cnfSound := by
    intro Y α hα
    trivial
  projection_eq_witnessMessage := by
    intro Y α hα
    exact smallSingleMessageProjection_eq_M_of_sat hα

/-- The concrete small ensemble has the semantic single-message promise. -/
theorem smallSingleMessageCNFReadoutData_singleMessagePromise :
    smallSingleMessageCNFReadoutData.SingleMessagePromise := by
  intro Y W W' hY hW hW'
  rfl

/-- Every supported public instance has a satisfying CNF assignment. -/
theorem smallSingleMessageCNFReadoutData_supportedSatisfiable :
    smallSingleMessageCNFReadoutData.SupportedCNFSatisfiable := by
  intro Y hY
  exact
    ⟨smallSingleMessageAssignment Y,
      smallSingleMessageFormula_satisfied_messageAssignment Y⟩

/-- Every satisfying SAT-search output reads out the fixed message `M(Y)`. -/
theorem smallSingleMessageCNFReadoutData_projection_eq_M
    {Y : SmallSingleMessagePublic}
    (_hY : smallSingleMessageCNFReadoutData.support Y)
    {α : ConcreteCNF.Assignment (SmallSingleMessageVar Y)}
    (hα :
      ConcreteCNF.IsSatFormula
        (smallSingleMessageCNFReadoutData.formula Y) α) :
    smallSingleMessageCNFReadoutData.projection Y α =
      smallSingleMessageM Y := by
  exact smallSingleMessageProjection_eq_M_of_sat hα

/-- The arbitrary-output SAT-search readout obligation holds for the concrete
small ensemble. -/
theorem smallSingleMessageCNFReadoutData_supportedArbitraryOutputSATSearchCorrect :
    smallSingleMessageCNFReadoutData.SupportedArbitraryOutputSATSearchCorrect := by
  exact
    smallSingleMessageCNFReadoutData.supportedArbitraryOutputSATSearchCorrect_of_singleMessagePromise
      smallSingleMessageCNFReadoutData_singleMessagePromise
      smallSingleMessageCNFReadoutData_supportedSatisfiable

/-! ## Public-target-tag obstruction -/

/-- The small construction has one public coordinate: the public bit itself. -/
abbrev SmallSingleMessagePublicCoordinate :=
  Unit

/-- The only public coordinate reads the public bit. -/
def smallSingleMessagePublicCoordinateValue
    (_coord : SmallSingleMessagePublicCoordinate)
    (Y : SmallSingleMessagePublic) : Bool :=
  Y

/-- No public coordinate should determine the fixed message.  This is the
no-public-target-tag shape that the small construction fails. -/
def SmallSingleMessageNoPublicCoordinateTargetTags : Prop :=
  ∀ coord : SmallSingleMessagePublicCoordinate,
    ¬ ∃ f : Bool → Bool,
      ∀ Y : SmallSingleMessagePublic,
        smallSingleMessageM Y =
          f (smallSingleMessagePublicCoordinateValue coord Y)

/-- The only public coordinate determines `M(Y)`. -/
theorem smallSingleMessage_publicCoordinate_determines_message :
    ∃ coord : SmallSingleMessagePublicCoordinate,
      ∃ f : Bool → Bool,
        ∀ Y : SmallSingleMessagePublic,
          smallSingleMessageM Y =
            f (smallSingleMessagePublicCoordinateValue coord Y) := by
  exact ⟨(), id, by intro Y; rfl⟩

/-- Named obstruction: the small CNF anchor is single-message, but it fails the
no-public-target-tag requirement because its public coordinate is the message
bit itself. -/
theorem smallSingleMessage_noPublicTargetTags_obstruction :
    ¬ SmallSingleMessageNoPublicCoordinateTargetTags := by
  intro hNoTags
  rcases smallSingleMessage_publicCoordinate_determines_message with
    ⟨coord, f, hf⟩
  exact hNoTags coord ⟨f, hf⟩

/-- No public coordinate should determine the CNF-level readout on every
satisfying SAT-search output.  This stronger CNF-readout form is also false
for the small construction. -/
def SmallSingleMessageNoPublicCoordinateReadoutTags : Prop :=
  ∀ coord : SmallSingleMessagePublicCoordinate,
    ¬ ∃ f : Bool → Bool,
      ∀ {Y : SmallSingleMessagePublic}
        {α : ConcreteCNF.Assignment (SmallSingleMessageVar Y)},
          ConcreteCNF.IsSatFormula (smallSingleMessageFormula Y) α →
            smallSingleMessageProjection Y α =
              f (smallSingleMessagePublicCoordinateValue coord Y)

/-- The only public coordinate determines the CNF-level readout on every
satisfying assignment. -/
theorem smallSingleMessage_publicCoordinate_determines_satProjection :
    ∃ coord : SmallSingleMessagePublicCoordinate,
      ∃ f : Bool → Bool,
        ∀ {Y : SmallSingleMessagePublic}
          {α : ConcreteCNF.Assignment (SmallSingleMessageVar Y)},
            ConcreteCNF.IsSatFormula (smallSingleMessageFormula Y) α →
              smallSingleMessageProjection Y α =
                f (smallSingleMessagePublicCoordinateValue coord Y) := by
  refine ⟨(), id, ?_⟩
  intro Y α hα
  calc
    smallSingleMessageProjection Y α = smallSingleMessageM Y :=
      smallSingleMessageProjection_eq_M_of_sat hα
    _ = smallSingleMessagePublicCoordinateValue () Y := rfl

/-- Named CNF-readout obstruction: the small single-message CNF anchor cannot
serve as a no-public-target-tags ensemble, since its public bit predicts every
valid SAT-search readout. -/
theorem smallSingleMessage_noPublicReadoutTags_obstruction :
    ¬ SmallSingleMessageNoPublicCoordinateReadoutTags := by
  intro hNoTags
  rcases smallSingleMessage_publicCoordinate_determines_satProjection with
    ⟨coord, f, hf⟩
  exact hNoTags coord ⟨f, hf⟩

/-! ## Two-coordinate XOR public surface -/

/-- Public instances for the XOR anchor: two public bits.  The whole public
instance fixes the message, but neither single coordinate does. -/
abbrev XorSingleMessagePublic :=
  Bool × Bool

/-- One Boolean CNF variable for each XOR public instance. -/
abbrev XorSingleMessageVar (_Y : XorSingleMessagePublic) :=
  Fin 1

/-- The hidden witness type is singleton-valued for each XOR public instance. -/
abbrev XorSingleMessageWitness (_Y : XorSingleMessagePublic) :=
  Unit

/-- The fixed public message readout `M(Y)`: XOR of the two public bits. -/
def xorSingleMessageM : XorSingleMessagePublic -> Bool
  | (false, false) => false
  | (false, true) => true
  | (true, false) => true
  | (true, true) => false

/-- The concrete CNF `F_Y`: a single unit clause locking the assignment bit to
`M(Y)`. -/
def xorSingleMessageFormula
    (Y : XorSingleMessagePublic) :
    ConcreteCNF.Formula (XorSingleMessageVar Y) :=
  if xorSingleMessageM Y then
    [[ConcreteCNF.Literal.pos (0 : Fin 1)]]
  else
    [[ConcreteCNF.Literal.neg (0 : Fin 1)]]

/-- Every XOR public instance is in support for this finite ensemble. -/
def xorSingleMessageSupport (_Y : XorSingleMessagePublic) : Prop :=
  True

/-- Semantic verifier relation for the unique XOR hidden witness. -/
def xorSingleMessageVerifier
    (_Y : XorSingleMessagePublic)
    (_W : XorSingleMessageWitness _Y) : Prop :=
  True

/-- Executable verifier program for the XOR anchor. -/
def xorSingleMessageVerifierDecision
    (Y : XorSingleMessagePublic)
    (_W : XorSingleMessageWitness Y) : Bool :=
  true

/-- The executable verifier decides the semantic verifier relation. -/
theorem xorSingleMessageVerifierDecision_correct
    {Y : XorSingleMessagePublic}
    {_W : XorSingleMessageWitness Y} :
    xorSingleMessageVerifierDecision Y _W = true ↔
      xorSingleMessageVerifier Y _W := by
  simp [xorSingleMessageVerifierDecision, xorSingleMessageVerifier]

/-- The satisfying assignment selected by the XOR construction. -/
def xorSingleMessageAssignment
    (Y : XorSingleMessagePublic) :
    ConcreteCNF.Assignment (XorSingleMessageVar Y) :=
  fun _ => xorSingleMessageM Y

/-- Extract the unique semantic witness from any XOR CNF assignment. -/
def xorSingleMessageExtract
    (Y : XorSingleMessagePublic)
    (_α : ConcreteCNF.Assignment (XorSingleMessageVar Y)) :
    XorSingleMessageWitness Y :=
  ()

/-- Semantic message carried by the unique XOR witness. -/
def xorSingleMessageWitnessMessage
    (Y : XorSingleMessagePublic)
    (_W : XorSingleMessageWitness Y) : Bool :=
  xorSingleMessageM Y

/-- CNF-level XOR message readout: read the single assignment bit. -/
def xorSingleMessageProjection
    (Y : XorSingleMessagePublic)
    (α : ConcreteCNF.Assignment (XorSingleMessageVar Y)) : Bool :=
  α 0

/-- The construction's assignment satisfies the concrete XOR CNF. -/
theorem xorSingleMessageFormula_satisfied_messageAssignment
    (Y : XorSingleMessagePublic) :
    ConcreteCNF.IsSatFormula
      (xorSingleMessageFormula Y)
      (xorSingleMessageAssignment Y) := by
  intro clause hclause
  unfold xorSingleMessageFormula at hclause
  by_cases hM : xorSingleMessageM Y
  · simp [hM] at hclause
    rw [hclause]
    exact
      ⟨ConcreteCNF.Literal.pos (0 : Fin 1), by simp,
        by simp [ConcreteCNF.Literal.eval, xorSingleMessageAssignment,
          hM]⟩
  · simp [hM] at hclause
    rw [hclause]
    exact
      ⟨ConcreteCNF.Literal.neg (0 : Fin 1), by simp,
        by simp [ConcreteCNF.Literal.eval, xorSingleMessageAssignment,
          hM]⟩

/-- Any satisfying XOR assignment has its single variable locked to `M(Y)`. -/
theorem xorSingleMessageFormula_forces_message
    {Y : XorSingleMessagePublic}
    {α : ConcreteCNF.Assignment (XorSingleMessageVar Y)}
    (hα :
      ConcreteCNF.IsSatFormula
        (xorSingleMessageFormula Y) α) :
    α 0 = xorSingleMessageM Y := by
  by_cases hM : xorSingleMessageM Y
  · have hclause :
        ConcreteCNF.IsSatClause
          [ConcreteCNF.Literal.pos (0 : Fin 1)] α := by
      exact hα [ConcreteCNF.Literal.pos (0 : Fin 1)]
        (by simp [xorSingleMessageFormula, hM])
    rcases hclause with ⟨lit, hlit, heval⟩
    simp only [List.mem_singleton] at hlit
    subst lit
    simpa [ConcreteCNF.Literal.eval, hM] using heval
  · have hclause :
        ConcreteCNF.IsSatClause
          [ConcreteCNF.Literal.neg (0 : Fin 1)] α := by
      exact hα [ConcreteCNF.Literal.neg (0 : Fin 1)]
        (by simp [xorSingleMessageFormula, hM])
    rcases hclause with ⟨lit, hlit, heval⟩
    simp only [List.mem_singleton] at hlit
    subst lit
    cases hbit : α 0 <;>
      simp [ConcreteCNF.Literal.eval, hbit, hM] at heval ⊢

/-- The XOR CNF readout on any satisfying assignment returns the fixed message
`M(Y)`. -/
theorem xorSingleMessageProjection_eq_M_of_sat
    {Y : XorSingleMessagePublic}
    {α : ConcreteCNF.Assignment (XorSingleMessageVar Y)}
    (hα :
      ConcreteCNF.IsSatFormula
        (xorSingleMessageFormula Y) α) :
    xorSingleMessageProjection Y α = xorSingleMessageM Y := by
  exact xorSingleMessageFormula_forces_message hα

/-- The concrete XOR anchor instantiated in the manuscript CNF readout
interface. -/
def xorSingleMessageCNFReadoutData :
    ManuscriptCNFReadoutData
      XorSingleMessagePublic
      XorSingleMessageVar
      XorSingleMessageWitness
      Bool where
  support := xorSingleMessageSupport
  formula := xorSingleMessageFormula
  validWitness := xorSingleMessageVerifier
  extract := xorSingleMessageExtract
  witnessMessage := xorSingleMessageWitnessMessage
  projection := xorSingleMessageProjection
  cnfSound := by
    intro Y α hα
    trivial
  projection_eq_witnessMessage := by
    intro Y α hα
    exact xorSingleMessageProjection_eq_M_of_sat hα

/-- The concrete XOR anchor has the semantic single-message promise. -/
theorem xorSingleMessageCNFReadoutData_singleMessagePromise :
    xorSingleMessageCNFReadoutData.SingleMessagePromise := by
  intro Y W W' hY hW hW'
  rfl

/-- Every supported XOR public instance has a satisfying CNF assignment. -/
theorem xorSingleMessageCNFReadoutData_supportedSatisfiable :
    xorSingleMessageCNFReadoutData.SupportedCNFSatisfiable := by
  intro Y hY
  exact
    ⟨xorSingleMessageAssignment Y,
      xorSingleMessageFormula_satisfied_messageAssignment Y⟩

/-- Every satisfying XOR SAT-search output reads out the fixed message `M(Y)`. -/
theorem xorSingleMessageCNFReadoutData_projection_eq_M
    {Y : XorSingleMessagePublic}
    (_hY : xorSingleMessageCNFReadoutData.support Y)
    {α : ConcreteCNF.Assignment (XorSingleMessageVar Y)}
    (hα :
      ConcreteCNF.IsSatFormula
        (xorSingleMessageCNFReadoutData.formula Y) α) :
    xorSingleMessageCNFReadoutData.projection Y α =
      xorSingleMessageM Y := by
  exact xorSingleMessageProjection_eq_M_of_sat hα

/-- The arbitrary-output SAT-search readout obligation holds for the concrete
XOR anchor. -/
theorem xorSingleMessageCNFReadoutData_supportedArbitraryOutputSATSearchCorrect :
    xorSingleMessageCNFReadoutData.SupportedArbitraryOutputSATSearchCorrect := by
  exact
    xorSingleMessageCNFReadoutData.supportedArbitraryOutputSATSearchCorrect_of_singleMessagePromise
      xorSingleMessageCNFReadoutData_singleMessagePromise
      xorSingleMessageCNFReadoutData_supportedSatisfiable

/-! ## XOR CNF SAT spine -/

/-- Hidden SAT witnesses for the XOR anchor are concrete assignments to the
single CNF variable. -/
abbrev XorSingleMessageSATWitness :=
  ConcreteCNF.Assignment (Fin 1)

/-- A world of the XOR SAT spine is a public instance together with a
satisfying CNF assignment. -/
structure XorSingleMessageSATWorld where
  publicInput : XorSingleMessagePublic
  assignment : XorSingleMessageSATWitness
  sat : ConcreteCNF.IsSatFormula
    (xorSingleMessageFormula publicInput) assignment

/-- The verifier for the XOR SAT spine is ordinary CNF satisfaction. -/
def xorSingleMessageSATVerifier
    (Y : XorSingleMessagePublic)
    (W : XorSingleMessageSATWitness) : Prop :=
  ConcreteCNF.IsSatFormula (xorSingleMessageFormula Y) W

/-- The SAT-spine readout reads the single CNF assignment bit. -/
def xorSingleMessageSATReadout
    (W : XorSingleMessageSATWitness) : Bool :=
  W 0

/-- Every verifier-valid XOR SAT witness reads the fixed public message. -/
theorem xorSingleMessageSATReadout_eq_M_of_valid
    {Y : XorSingleMessagePublic}
    {W : XorSingleMessageSATWitness}
    (hW : xorSingleMessageSATVerifier Y W) :
    xorSingleMessageSATReadout W = xorSingleMessageM Y := by
  simpa [xorSingleMessageSATReadout, xorSingleMessageProjection,
    xorSingleMessageSATVerifier] using
    xorSingleMessageProjection_eq_M_of_sat (Y := Y) (α := W) hW

/-- The XOR CNF anchor inhabits the real single-message SAT spine interface
with CNF assignments as hidden witnesses. -/
def xorSingleMessageRealSingleMessageSATSpine :
    RealSingleMessageSATSpine
      XorSingleMessageSATWorld
      XorSingleMessagePublic
      XorSingleMessageSATWitness where
  publicInput := fun omega => omega.publicInput
  witnessOfWorld := fun omega => omega.assignment
  verifier := xorSingleMessageSATVerifier
  messageOfPublic := xorSingleMessageM
  witnessReadout := xorSingleMessageSATReadout
  target := fun omega => xorSingleMessageM omega.publicInput
  worldWitnessValid := by
    intro omega
    exact omega.sat
  readout_eq_message_of_valid := by
    intro Y W hW
    exact xorSingleMessageSATReadout_eq_M_of_valid hW
  target_eq_message := by
    intro omega
    rfl

/-- Structural `singleMessage` field for the XOR CNF SAT spine. -/
theorem xorSingleMessageRealSingleMessageSATSpine_singleMessage :
    ∀ w0 w1 : XorSingleMessageSATWorld,
      w0.publicInput = w1.publicInput ->
        xorSingleMessageM w0.publicInput =
          xorSingleMessageM w1.publicInput :=
  xorSingleMessageRealSingleMessageSATSpine.singleMessage

/-- Any two verifier-valid XOR SAT witnesses over one public instance have the
same readout. -/
theorem xorSingleMessageSATReadout_eq_of_valid
    {Y : XorSingleMessagePublic}
    {W W' : XorSingleMessageSATWitness}
    (hW : xorSingleMessageSATVerifier Y W)
    (hW' : xorSingleMessageSATVerifier Y W') :
    xorSingleMessageSATReadout W =
      xorSingleMessageSATReadout W' :=
  xorSingleMessageRealSingleMessageSATSpine.readout_eq_of_valid hW hW'

/-- The world witness of the XOR SAT spine reads the world target. -/
theorem xorSingleMessageSATWorld_readout_eq_target
    (omega : XorSingleMessageSATWorld) :
    xorSingleMessageSATReadout omega.assignment =
      xorSingleMessageM omega.publicInput :=
  xorSingleMessageRealSingleMessageSATSpine.worldWitness_readout_eq_target
    omega

/-- The two single public coordinates of the XOR anchor. -/
inductive XorSingleMessagePublicCoordinate where
  | left
  | right
  deriving DecidableEq

/-- Read one public coordinate of the XOR anchor. -/
def xorSingleMessagePublicCoordinateValue :
    XorSingleMessagePublicCoordinate -> XorSingleMessagePublic -> Bool
  | .left, Y => Y.1
  | .right, Y => Y.2

/-- No single public coordinate should determine the fixed XOR message. -/
def XorSingleMessageNoPublicCoordinateTargetTags : Prop :=
  ∀ coord : XorSingleMessagePublicCoordinate,
    ¬ ∃ f : Bool -> Bool,
      ∀ Y : XorSingleMessagePublic,
        xorSingleMessageM Y =
          f (xorSingleMessagePublicCoordinateValue coord Y)

/-- Every single public coordinate has two equal-coordinate public instances
with opposite XOR messages. -/
theorem xorSingleMessage_publicCoordinate_has_oppositeMessages
    (coord : XorSingleMessagePublicCoordinate) :
    ∃ Y₀ Y₁ : XorSingleMessagePublic,
      xorSingleMessagePublicCoordinateValue coord Y₀ =
        xorSingleMessagePublicCoordinateValue coord Y₁ ∧
        xorSingleMessageM Y₀ ≠ xorSingleMessageM Y₁ := by
  cases coord
  · exact ⟨(false, false), (false, true), rfl, by simp [xorSingleMessageM]⟩
  · exact ⟨(false, false), (true, false), rfl, by simp [xorSingleMessageM]⟩

/-- Structural field for the XOR anchor: neither single public coordinate
determines the fixed message. -/
theorem xorSingleMessage_noPublicTargetTags :
    XorSingleMessageNoPublicCoordinateTargetTags := by
  intro coord htag
  rcases htag with ⟨f, hf⟩
  rcases xorSingleMessage_publicCoordinate_has_oppositeMessages coord with
    ⟨Y₀, Y₁, hcoord, hmsg⟩
  have hsame : xorSingleMessageM Y₀ = xorSingleMessageM Y₁ := by
    calc
      xorSingleMessageM Y₀ =
          f (xorSingleMessagePublicCoordinateValue coord Y₀) :=
        hf Y₀
      _ = f (xorSingleMessagePublicCoordinateValue coord Y₁) := by
        rw [hcoord]
      _ = xorSingleMessageM Y₁ :=
        (hf Y₁).symm
  exact hmsg hsame

/-- No single public coordinate should determine the CNF-level XOR readout on
every satisfying SAT-search output. -/
def XorSingleMessageNoPublicCoordinateReadoutTags : Prop :=
  ∀ coord : XorSingleMessagePublicCoordinate,
    ¬ ∃ f : Bool -> Bool,
      ∀ {Y : XorSingleMessagePublic}
        {α : ConcreteCNF.Assignment (XorSingleMessageVar Y)},
          ConcreteCNF.IsSatFormula (xorSingleMessageFormula Y) α ->
            xorSingleMessageProjection Y α =
              f (xorSingleMessagePublicCoordinateValue coord Y)

/-- Structural field for the XOR anchor: neither single public coordinate
determines the CNF-level readout over satisfying assignments. -/
theorem xorSingleMessage_noPublicReadoutTags :
    XorSingleMessageNoPublicCoordinateReadoutTags := by
  intro coord htag
  exact xorSingleMessage_noPublicTargetTags coord
    (by
      rcases htag with ⟨f, hf⟩
      refine ⟨f, ?_⟩
      intro Y
      have hsat :
          ConcreteCNF.IsSatFormula
            (xorSingleMessageFormula Y)
            (xorSingleMessageAssignment Y) :=
        xorSingleMessageFormula_satisfied_messageAssignment Y
      have hreadout :=
        hf (Y := Y) (α := xorSingleMessageAssignment Y) hsat
      simpa [xorSingleMessageProjection, xorSingleMessageAssignment] using
        hreadout)

/-! ## XOR admissible histories -/

/-- The target bit for the XOR public surface. -/
def xorSingleMessageTarget (Y : XorSingleMessagePublic) : Bool :=
  xorSingleMessageM Y

/-- Flip the left public coordinate.  This toggles the XOR target and gives
the global target-balance pairing. -/
def xorSingleMessageFlipLeft
    (Y : XorSingleMessagePublic) : XorSingleMessagePublic :=
  (!Y.1, Y.2)

/-- The global XOR target false fiber is in bijection with its true fiber. -/
def xorSingleMessageTargetFlipEquiv :
    {Y : XorSingleMessagePublic // xorSingleMessageTarget Y = false} ≃
      {Y : XorSingleMessagePublic // xorSingleMessageTarget Y = true} where
  toFun := fun Y =>
    ⟨xorSingleMessageFlipLeft Y.val, by
      rcases Y with ⟨Y, hY⟩
      cases Y with
      | mk b0 b1 =>
          cases b0 <;> cases b1 <;>
            simp [xorSingleMessageTarget, xorSingleMessageFlipLeft,
              xorSingleMessageM] at hY ⊢⟩
  invFun := fun Y =>
    ⟨xorSingleMessageFlipLeft Y.val, by
      rcases Y with ⟨Y, hY⟩
      cases Y with
      | mk b0 b1 =>
          cases b0 <;> cases b1 <;>
            simp [xorSingleMessageTarget, xorSingleMessageFlipLeft,
              xorSingleMessageM] at hY ⊢⟩
  left_inv := by
    intro Y
    apply Subtype.ext
    rcases Y with ⟨Y, hY⟩
    rcases Y with ⟨b0, b1⟩
    simp [xorSingleMessageFlipLeft]
  right_inv := by
    intro Y
    apply Subtype.ext
    rcases Y with ⟨Y, hY⟩
    rcases Y with ⟨b0, b1⟩
    simp [xorSingleMessageFlipLeft]

theorem xorSingleMessageTarget_false_card_eq_true :
    Fintype.card
        {Y : XorSingleMessagePublic //
          xorSingleMessageTarget Y = false} =
      Fintype.card
        {Y : XorSingleMessagePublic //
          xorSingleMessageTarget Y = true} :=
  Fintype.card_congr xorSingleMessageTargetFlipEquiv

theorem xorSingleMessage_constantTrue_correct_card_eq_true :
    Fintype.card
        {Y : XorSingleMessagePublic //
          (fun _ : XorSingleMessagePublic => true) Y =
            xorSingleMessageTarget Y} =
      Fintype.card
        {Y : XorSingleMessagePublic //
          xorSingleMessageTarget Y = true} := by
  let e :
      {Y : XorSingleMessagePublic //
        (fun _ : XorSingleMessagePublic => true) Y =
          xorSingleMessageTarget Y} ≃
        {Y : XorSingleMessagePublic //
          xorSingleMessageTarget Y = true} :=
    { toFun := fun Y => ⟨Y.val, Y.property.symm⟩
      invFun := fun Y => ⟨Y.val, Y.property.symm⟩
      left_inv := by
        intro Y
        cases Y
        rfl
      right_inv := by
        intro Y
        cases Y
        rfl }
  exact Fintype.card_congr e

theorem xorSingleMessage_world_card_eq_two_mul_target_true :
    Fintype.card XorSingleMessagePublic =
      2 * Fintype.card
        {Y : XorSingleMessagePublic //
          xorSingleMessageTarget Y = true} := by
  set a : Nat :=
    Fintype.card
      {Y : XorSingleMessagePublic //
        xorSingleMessageTarget Y = true}
  have hcomp :
      Fintype.card
          {Y : XorSingleMessagePublic //
            xorSingleMessageTarget Y = false} =
        Fintype.card XorSingleMessagePublic - a := by
    simpa [a] using
      (Fintype.card_subtype_compl
        (fun Y : XorSingleMessagePublic =>
          xorSingleMessageTarget Y = true))
  have heq :
      a =
        Fintype.card
          {Y : XorSingleMessagePublic //
            xorSingleMessageTarget Y = false} := by
    simpa [a] using xorSingleMessageTarget_false_card_eq_true.symm
  have hsub :
      Fintype.card XorSingleMessagePublic - a = a := by
    simpa [heq] using hcomp.symm
  have hle :
      a ≤ Fintype.card XorSingleMessagePublic := by
    simpa [a] using
      Fintype.card_subtype_le
        (fun Y : XorSingleMessagePublic =>
          xorSingleMessageTarget Y = true)
  have hsum :
      Fintype.card XorSingleMessagePublic = a + a :=
    Nat.eq_add_of_sub_eq hle hsub
  simpa [a, two_mul, Nat.add_comm] using hsum

theorem xorSingleMessageTarget_true_card_pos :
    0 <
      Fintype.card
        {Y : XorSingleMessagePublic //
          xorSingleMessageTarget Y = true} := by
  exact
    Fintype.card_pos_iff.mpr
      ⟨⟨(false, true), by
        simp [xorSingleMessageTarget, xorSingleMessageM]⟩⟩

/-- The XOR target is balanced on the finite public surface. -/
theorem xorSingleMessage_target_balanced :
    BalancedBit xorSingleMessageTarget := by
  unfold BalancedBit globalDecoderSuccess
  rw [xorSingleMessage_constantTrue_correct_card_eq_true]
  rw [xorSingleMessage_world_card_eq_two_mul_target_true]
  set a : Nat :=
    Fintype.card
      {Y : XorSingleMessagePublic //
        xorSingleMessageTarget Y = true}
  have hpos : 0 < a := by
    simpa [a] using xorSingleMessageTarget_true_card_pos
  have hne : (a : Rat) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hpos)
  rw [Nat.cast_mul]
  field_simp [hne]
  norm_num

/-- The single-coordinate history field for the XOR public surface. -/
def xorSingleMessageHistoryField
    (coord : XorSingleMessagePublicCoordinate) :
    FiniteSigmaField XorSingleMessagePublic where
  Atom := Bool
  atomDecidable := inferInstance
  atom := xorSingleMessagePublicCoordinateValue coord

/-- Flip the coordinate not observed by a history field.  This preserves the
history atom and toggles the XOR target. -/
def xorSingleMessageFlipUnobserved
    (coord : XorSingleMessagePublicCoordinate)
    (Y : XorSingleMessagePublic) : XorSingleMessagePublic :=
  match coord with
  | .left => (Y.1, !Y.2)
  | .right => (!Y.1, Y.2)

/-- Within any single-coordinate fiber, the true and false XOR target fibers
are paired by flipping the unobserved coordinate. -/
def xorSingleMessageHistoryFieldFiberFlipEquiv
    (coord : XorSingleMessagePublicCoordinate) (atom : Bool) :
    FiberTrue (xorSingleMessagePublicCoordinateValue coord)
        xorSingleMessageTarget atom ≃
      FiberFalse (xorSingleMessagePublicCoordinateValue coord)
        xorSingleMessageTarget atom where
  toFun := fun Y =>
    ⟨xorSingleMessageFlipUnobserved coord Y.val, by
      rcases Y with ⟨Y, hY⟩
      cases coord <;> rcases Y with ⟨b0, b1⟩ <;>
        cases b0 <;> cases b1 <;> cases atom <;>
          simp [xorSingleMessageFlipUnobserved,
            xorSingleMessagePublicCoordinateValue,
            xorSingleMessageTarget, xorSingleMessageM] at hY ⊢⟩
  invFun := fun Y =>
    ⟨xorSingleMessageFlipUnobserved coord Y.val, by
      rcases Y with ⟨Y, hY⟩
      cases coord <;> rcases Y with ⟨b0, b1⟩ <;>
        cases b0 <;> cases b1 <;> cases atom <;>
          simp [xorSingleMessageFlipUnobserved,
            xorSingleMessagePublicCoordinateValue,
            xorSingleMessageTarget, xorSingleMessageM] at hY ⊢⟩
  left_inv := by
    intro Y
    apply Subtype.ext
    rcases Y with ⟨Y, hY⟩
    cases coord <;> rcases Y with ⟨b0, b1⟩ <;>
      simp [xorSingleMessageFlipUnobserved]
  right_inv := by
    intro Y
    apply Subtype.ext
    rcases Y with ⟨Y, hY⟩
    cases coord <;> rcases Y with ⟨b0, b1⟩ <;>
      simp [xorSingleMessageFlipUnobserved]

/-- Every single-coordinate XOR history field has balanced target fibers. -/
theorem xorSingleMessage_historyField_balancedConditioning
    (coord : XorSingleMessagePublicCoordinate) :
    BalancedConditioning
      (xorSingleMessageHistoryField coord) xorSingleMessageTarget := by
  change Neutral
    (xorSingleMessagePublicCoordinateValue coord) xorSingleMessageTarget
  intro atom
  exact
    Fintype.card_congr
      (xorSingleMessageHistoryFieldFiberFlipEquiv coord atom)

/-- Structural `admissibleHistories` field for the XOR public surface:
the target is globally balanced and remains balanced after conditioning on
either single public coordinate. -/
theorem xorSingleMessage_admissibleHistories
    (coord : XorSingleMessagePublicCoordinate) :
    BalancedBit xorSingleMessageTarget ∧
      BalancedConditioning
        (xorSingleMessageHistoryField coord) xorSingleMessageTarget :=
  ⟨xorSingleMessage_target_balanced,
    xorSingleMessage_historyField_balancedConditioning coord⟩

/-! ## Two-variable XOR gauge CNF anchor -/

/-- Public instances for the gauge-buffered XOR anchor reuse the two-coordinate
XOR public surface. -/
abbrev XorGaugeSingleMessagePublic :=
  XorSingleMessagePublic

/-- The two CNF variables are the message bit and a free hidden gauge bit. -/
abbrev XorGaugeSingleMessageVar (_Y : XorGaugeSingleMessagePublic) :=
  Fin 2

/-- Hidden SAT witnesses are concrete assignments to the two CNF variables. -/
abbrev XorGaugeSingleMessageWitness (_Y : XorGaugeSingleMessagePublic) :=
  ConcreteCNF.Assignment (Fin 2)

/-- Variable `0` is the fixed message/readout coordinate. -/
def xorGaugeSingleMessageMessageVar
    (Y : XorGaugeSingleMessagePublic) :
    XorGaugeSingleMessageVar Y :=
  0

/-- Variable `1` is a free hidden gauge coordinate. -/
def xorGaugeSingleMessageGaugeVar
    (Y : XorGaugeSingleMessagePublic) :
    XorGaugeSingleMessageVar Y :=
  1

/-- The fixed public message readout for the gauge-buffered anchor. -/
def xorGaugeSingleMessageM (Y : XorGaugeSingleMessagePublic) : Bool :=
  xorSingleMessageM Y

/-- The concrete CNF locks only the message variable to `M(Y)`; the second
variable is deliberately unconstrained hidden gauge state. -/
def xorGaugeSingleMessageFormula
    (Y : XorGaugeSingleMessagePublic) :
    ConcreteCNF.Formula (XorGaugeSingleMessageVar Y) :=
  [ConcreteCNF.unitClause (0 : Fin 2) (xorGaugeSingleMessageM Y)]

/-- Every public instance is in support for the gauge-buffered anchor. -/
def xorGaugeSingleMessageSupport
    (_Y : XorGaugeSingleMessagePublic) : Prop :=
  True

/-- The semantic verifier is ordinary CNF satisfaction. -/
def xorGaugeSingleMessageVerifier
    (Y : XorGaugeSingleMessagePublic)
    (W : XorGaugeSingleMessageWitness Y) : Prop :=
  ConcreteCNF.IsSatFormula (xorGaugeSingleMessageFormula Y) W

/-- Executable verifier: check the forced message bit. -/
def xorGaugeSingleMessageVerifierDecision
    (Y : XorGaugeSingleMessagePublic)
    (W : XorGaugeSingleMessageWitness Y) : Bool :=
  decide (W 0 = xorGaugeSingleMessageM Y)

/-- The one-clause formula is satisfied exactly when the message coordinate is
locked to the public XOR message. -/
theorem xorGaugeSingleMessageFormula_sat_iff
    {Y : XorGaugeSingleMessagePublic}
    {W : XorGaugeSingleMessageWitness Y} :
    ConcreteCNF.IsSatFormula (xorGaugeSingleMessageFormula Y) W ↔
      W 0 = xorGaugeSingleMessageM Y := by
  constructor
  · intro hW
    have hclause :
        ConcreteCNF.IsSatClause
          (ConcreteCNF.unitClause (0 : Fin 2)
            (xorGaugeSingleMessageM Y)) W := by
      exact hW _ (by simp [xorGaugeSingleMessageFormula])
    exact
      (ConcreteCNF.isSatClause_unitClause_iff W (0 : Fin 2)
        (xorGaugeSingleMessageM Y)).mp hclause
  · intro hmsg clause hclause
    simp [xorGaugeSingleMessageFormula] at hclause
    rw [hclause]
    exact
      (ConcreteCNF.isSatClause_unitClause_iff W (0 : Fin 2)
        (xorGaugeSingleMessageM Y)).mpr hmsg

/-- The executable verifier decides the semantic verifier relation. -/
theorem xorGaugeSingleMessageVerifierDecision_correct
    {Y : XorGaugeSingleMessagePublic}
    {W : XorGaugeSingleMessageWitness Y} :
    xorGaugeSingleMessageVerifierDecision Y W = true ↔
      xorGaugeSingleMessageVerifier Y W := by
  simp [xorGaugeSingleMessageVerifierDecision,
    xorGaugeSingleMessageVerifier,
    xorGaugeSingleMessageFormula_sat_iff]

/-- A satisfying assignment with a chosen hidden gauge bit. -/
def xorGaugeSingleMessageAssignment
    (Y : XorGaugeSingleMessagePublic) (gauge : Bool) :
    XorGaugeSingleMessageWitness Y :=
  fun i => if i = (0 : Fin 2) then xorGaugeSingleMessageM Y else gauge

@[simp] theorem xorGaugeSingleMessageAssignment_message
    (Y : XorGaugeSingleMessagePublic) (gauge : Bool) :
    xorGaugeSingleMessageAssignment Y gauge 0 =
      xorGaugeSingleMessageM Y := by
  simp [xorGaugeSingleMessageAssignment]

@[simp] theorem xorGaugeSingleMessageAssignment_gauge
    (Y : XorGaugeSingleMessagePublic) (gauge : Bool) :
    xorGaugeSingleMessageAssignment Y gauge 1 = gauge := by
  simp [xorGaugeSingleMessageAssignment]

/-- The selected assignment satisfies the CNF for either hidden gauge bit. -/
theorem xorGaugeSingleMessageFormula_satisfied_assignment
    (Y : XorGaugeSingleMessagePublic) (gauge : Bool) :
    ConcreteCNF.IsSatFormula
      (xorGaugeSingleMessageFormula Y)
      (xorGaugeSingleMessageAssignment Y gauge) := by
  exact xorGaugeSingleMessageFormula_sat_iff.mpr
    (xorGaugeSingleMessageAssignment_message Y gauge)

/-- Any satisfying witness reads out the fixed public message. -/
theorem xorGaugeSingleMessageWitness_message_eq_M
    {Y : XorGaugeSingleMessagePublic}
    {W : XorGaugeSingleMessageWitness Y}
    (hW : xorGaugeSingleMessageVerifier Y W) :
    W 0 = xorGaugeSingleMessageM Y := by
  exact xorGaugeSingleMessageFormula_sat_iff.mp hW

/-- The extraction map is identity: SAT assignments are the hidden witnesses. -/
def xorGaugeSingleMessageExtract
    (Y : XorGaugeSingleMessagePublic)
    (W : ConcreteCNF.Assignment (XorGaugeSingleMessageVar Y)) :
    XorGaugeSingleMessageWitness Y :=
  W

/-- The witness-level message is the forced message variable. -/
def xorGaugeSingleMessageWitnessMessage
    (Y : XorGaugeSingleMessagePublic)
    (W : XorGaugeSingleMessageWitness Y) : Bool :=
  W 0

/-- The CNF-level message projection reads the forced message variable. -/
def xorGaugeSingleMessageProjection
    (Y : XorGaugeSingleMessagePublic)
    (W : ConcreteCNF.Assignment (XorGaugeSingleMessageVar Y)) : Bool :=
  W 0

/-- The gauge-buffered anchor instantiated in the manuscript CNF readout
interface. -/
def xorGaugeSingleMessageCNFReadoutData :
    ManuscriptCNFReadoutData
      XorGaugeSingleMessagePublic
      XorGaugeSingleMessageVar
      XorGaugeSingleMessageWitness
      Bool where
  support := xorGaugeSingleMessageSupport
  formula := xorGaugeSingleMessageFormula
  validWitness := xorGaugeSingleMessageVerifier
  extract := xorGaugeSingleMessageExtract
  witnessMessage := xorGaugeSingleMessageWitnessMessage
  projection := xorGaugeSingleMessageProjection
  cnfSound := by
    intro Y W hW
    exact hW
  projection_eq_witnessMessage := by
    intro Y W hW
    rfl

/-- The gauge-buffered anchor has the semantic single-message promise:
the hidden gauge bit may vary, but the message bit is forced. -/
theorem xorGaugeSingleMessageCNFReadoutData_singleMessagePromise :
    xorGaugeSingleMessageCNFReadoutData.SingleMessagePromise := by
  intro Y W W' hY hW hW'
  have hmsg := xorGaugeSingleMessageWitness_message_eq_M hW
  have hmsg' := xorGaugeSingleMessageWitness_message_eq_M hW'
  simp [xorGaugeSingleMessageCNFReadoutData,
    xorGaugeSingleMessageWitnessMessage, hmsg, hmsg']

/-- Every supported public instance has satisfying assignments, one for each
choice of hidden gauge bit. -/
theorem xorGaugeSingleMessageCNFReadoutData_supportedSatisfiable :
    xorGaugeSingleMessageCNFReadoutData.SupportedCNFSatisfiable := by
  intro Y hY
  exact
    ⟨xorGaugeSingleMessageAssignment Y false,
      xorGaugeSingleMessageFormula_satisfied_assignment Y false⟩

/-- Any satisfying SAT-search output reads the fixed public message. -/
theorem xorGaugeSingleMessageCNFReadoutData_projection_eq_M
    {Y : XorGaugeSingleMessagePublic}
    (_hY : xorGaugeSingleMessageCNFReadoutData.support Y)
    {W : ConcreteCNF.Assignment (XorGaugeSingleMessageVar Y)}
    (hW :
      ConcreteCNF.IsSatFormula
        (xorGaugeSingleMessageCNFReadoutData.formula Y) W) :
    xorGaugeSingleMessageCNFReadoutData.projection Y W =
      xorGaugeSingleMessageM Y := by
  exact xorGaugeSingleMessageFormula_sat_iff.mp hW

/-- The arbitrary-output SAT-search readout obligation holds although the
hidden gauge bit is unconstrained. -/
theorem xorGaugeSingleMessageCNFReadoutData_supportedArbitraryOutputSATSearchCorrect :
    xorGaugeSingleMessageCNFReadoutData.SupportedArbitraryOutputSATSearchCorrect := by
  exact
    xorGaugeSingleMessageCNFReadoutData.supportedArbitraryOutputSATSearchCorrect_of_singleMessagePromise
      xorGaugeSingleMessageCNFReadoutData_singleMessagePromise
      xorGaugeSingleMessageCNFReadoutData_supportedSatisfiable

/-! ## Gauge-buffered XOR public-tag structural field -/

/-- No single public coordinate should determine the fixed message in the
gauge-buffered XOR anchor. -/
def XorGaugeSingleMessageNoPublicCoordinateTargetTags : Prop :=
  ∀ coord : XorSingleMessagePublicCoordinate,
    ¬ ∃ f : Bool -> Bool,
      ∀ Y : XorGaugeSingleMessagePublic,
        xorGaugeSingleMessageM Y =
          f (xorSingleMessagePublicCoordinateValue coord Y)

/-- Structural `noPublicTargetTags` field for the gauge-buffered XOR anchor:
the added hidden gauge variable does not change the XOR public surface. -/
theorem xorGaugeSingleMessage_noPublicTargetTags :
    XorGaugeSingleMessageNoPublicCoordinateTargetTags := by
  intro coord
  simpa [XorGaugeSingleMessageNoPublicCoordinateTargetTags,
    xorGaugeSingleMessageM] using
    xorSingleMessage_noPublicTargetTags coord

/-- No single public coordinate should determine the CNF-level readout on
every satisfying SAT-search output for the gauge-buffered XOR anchor. -/
def XorGaugeSingleMessageNoPublicCoordinateReadoutTags : Prop :=
  ∀ coord : XorSingleMessagePublicCoordinate,
    ¬ ∃ f : Bool -> Bool,
      ∀ {Y : XorGaugeSingleMessagePublic}
        {W : ConcreteCNF.Assignment (XorGaugeSingleMessageVar Y)},
          ConcreteCNF.IsSatFormula (xorGaugeSingleMessageFormula Y) W ->
            xorGaugeSingleMessageProjection Y W =
              f (xorSingleMessagePublicCoordinateValue coord Y)

/-- Structural CNF-readout form of `noPublicTargetTags`: even after SAT search
chooses an arbitrary hidden gauge bit, no single public coordinate predicts the
forced message readout. -/
theorem xorGaugeSingleMessage_noPublicReadoutTags :
    XorGaugeSingleMessageNoPublicCoordinateReadoutTags := by
  intro coord htag
  exact xorGaugeSingleMessage_noPublicTargetTags coord
    (by
      rcases htag with ⟨f, hf⟩
      refine ⟨f, ?_⟩
      intro Y
      have hsat :
          ConcreteCNF.IsSatFormula
            (xorGaugeSingleMessageFormula Y)
            (xorGaugeSingleMessageAssignment Y false) :=
        xorGaugeSingleMessageFormula_satisfied_assignment Y false
      have hreadout :=
        hf (Y := Y) (W := xorGaugeSingleMessageAssignment Y false) hsat
      simpa [xorGaugeSingleMessageProjection,
        xorGaugeSingleMessageAssignment, xorGaugeSingleMessageM] using
        hreadout)

/-- Flip the hidden gauge coordinate when `gamma = true`; leave the message
coordinate unchanged. -/
def xorGaugeSingleMessageGaugeAction
    (gamma : Bool) {Y : XorGaugeSingleMessagePublic}
    (W : XorGaugeSingleMessageWitness Y) :
    XorGaugeSingleMessageWitness Y :=
  fun i => if i = (1 : Fin 2) then (if gamma then !W i else W i) else W i

@[simp] theorem xorGaugeSingleMessageGaugeAction_message
    (gamma : Bool) {Y : XorGaugeSingleMessagePublic}
    (W : XorGaugeSingleMessageWitness Y) :
    xorGaugeSingleMessageGaugeAction gamma W 0 = W 0 := by
  simp [xorGaugeSingleMessageGaugeAction]

@[simp] theorem xorGaugeSingleMessageGaugeAction_gauge_false
    {Y : XorGaugeSingleMessagePublic}
    (W : XorGaugeSingleMessageWitness Y) :
    xorGaugeSingleMessageGaugeAction false W = W := by
  funext i
  by_cases hi : i = (1 : Fin 2) <;>
    simp [xorGaugeSingleMessageGaugeAction, hi]

/-- The hidden gauge action preserves verifier validity because the CNF only
mentions the message variable. -/
theorem xorGaugeSingleMessageGaugeAction_preserves_verifier
    (gamma : Bool) {Y : XorGaugeSingleMessagePublic}
    {W : XorGaugeSingleMessageWitness Y}
    (hW : xorGaugeSingleMessageVerifier Y W) :
    xorGaugeSingleMessageVerifier Y
      (xorGaugeSingleMessageGaugeAction gamma W) := by
  exact xorGaugeSingleMessageFormula_sat_iff.mpr
    (by
      simpa using
        (xorGaugeSingleMessageFormula_sat_iff.mp hW))

/-- The hidden gauge action preserves the message readout. -/
theorem xorGaugeSingleMessageGaugeAction_preserves_readout
    (gamma : Bool) {Y : XorGaugeSingleMessagePublic}
    (W : XorGaugeSingleMessageWitness Y) :
    xorGaugeSingleMessageWitnessMessage Y
        (xorGaugeSingleMessageGaugeAction gamma W) =
      xorGaugeSingleMessageWitnessMessage Y W := by
  simp [xorGaugeSingleMessageWitnessMessage]

/-- The hidden gauge action is nontrivial on satisfying witnesses: flipping
the hidden coordinate changes the `gauge = false` witness. -/
theorem xorGaugeSingleMessageGaugeAction_nontrivial :
    ∃ Y : XorGaugeSingleMessagePublic,
      ∃ W : XorGaugeSingleMessageWitness Y,
        xorGaugeSingleMessageVerifier Y W ∧
          xorGaugeSingleMessageGaugeAction true W ≠ W := by
  let Y : XorGaugeSingleMessagePublic := (false, false)
  let W : XorGaugeSingleMessageWitness Y :=
    xorGaugeSingleMessageAssignment Y false
  refine
    ⟨Y, W,
      xorGaugeSingleMessageFormula_satisfied_assignment Y false, ?_⟩
  intro hfixed
  have hcoord := congrFun hfixed (1 : Fin 2)
  simp [W, xorGaugeSingleMessageGaugeAction] at hcoord

/-- A world of the gauge-buffered XOR SAT spine is a public instance together
with a satisfying two-variable assignment. -/
structure XorGaugeSingleMessageSATWorld where
  publicInput : XorGaugeSingleMessagePublic
  assignment : XorGaugeSingleMessageWitness publicInput
  sat : xorGaugeSingleMessageVerifier publicInput assignment

/-- Build a gauge-buffered SAT world from a public instance and a hidden gauge
bit.  The message bit is the canonical forced assignment. -/
def xorGaugeSingleMessageSATWorldOf
    (Y : XorGaugeSingleMessagePublic) (gauge : Bool) :
    XorGaugeSingleMessageSATWorld where
  publicInput := Y
  assignment := xorGaugeSingleMessageAssignment Y gauge
  sat := xorGaugeSingleMessageFormula_satisfied_assignment Y gauge

/-- Read the hidden gauge bit from a gauge-buffered SAT world. -/
def xorGaugeSingleMessageSATWorldGauge
    (omega : XorGaugeSingleMessageSATWorld) : Bool :=
  omega.assignment 1

@[simp] theorem xorGaugeSingleMessageSATWorldOf_publicInput
    (Y : XorGaugeSingleMessagePublic) (gauge : Bool) :
    (xorGaugeSingleMessageSATWorldOf Y gauge).publicInput = Y :=
  rfl

@[simp] theorem xorGaugeSingleMessageSATWorldOf_gauge
    (Y : XorGaugeSingleMessagePublic) (gauge : Bool) :
    xorGaugeSingleMessageSATWorldGauge
      (xorGaugeSingleMessageSATWorldOf Y gauge) = gauge := by
  simp [xorGaugeSingleMessageSATWorldGauge,
    xorGaugeSingleMessageSATWorldOf]

/-- A satisfying two-variable world is exactly a public XOR instance plus the
free hidden gauge bit. -/
def xorGaugeSingleMessageSATWorldEquiv :
    XorGaugeSingleMessageSATWorld ≃
      XorGaugeSingleMessagePublic × Bool where
  toFun := fun omega =>
    (omega.publicInput, xorGaugeSingleMessageSATWorldGauge omega)
  invFun := fun yg =>
    xorGaugeSingleMessageSATWorldOf yg.1 yg.2
  left_inv := by
    intro omega
    cases omega with
    | mk Y W sat =>
        have hmsg : W 0 = xorGaugeSingleMessageM Y :=
          xorGaugeSingleMessageFormula_sat_iff.mp sat
        simp [xorGaugeSingleMessageSATWorldGauge,
          xorGaugeSingleMessageSATWorldOf,
          XorGaugeSingleMessageSATWorld.mk.injEq]
        funext i
        fin_cases i <;>
          simp [xorGaugeSingleMessageAssignment, hmsg]
  right_inv := by
    intro yg
    cases yg with
    | mk Y gauge =>
        simp [xorGaugeSingleMessageSATWorldGauge,
          xorGaugeSingleMessageSATWorldOf]

/-- The gauge-buffered SAT-world surface is finite because it is equivalent to
a finite public instance plus one hidden gauge bit. -/
noncomputable instance :
    Fintype XorGaugeSingleMessageSATWorld :=
  Fintype.ofEquiv (XorGaugeSingleMessagePublic × Bool)
    xorGaugeSingleMessageSATWorldEquiv.symm

/-- The gauge-buffered SAT-world surface is inhabited by any canonical
satisfying assignment. -/
instance : Nonempty XorGaugeSingleMessageSATWorld :=
  ⟨xorGaugeSingleMessageSATWorldOf (false, false) false⟩

/-- SAT-spine readout for the gauge-buffered anchor. -/
def xorGaugeSingleMessageSATReadout
    {Y : XorGaugeSingleMessagePublic}
    (W : XorGaugeSingleMessageWitness Y) : Bool :=
  W 0

/-- Every verifier-valid gauge-buffered witness reads the public message. -/
theorem xorGaugeSingleMessageSATReadout_eq_M_of_valid
    {Y : XorGaugeSingleMessagePublic}
    {W : XorGaugeSingleMessageWitness Y}
    (hW : xorGaugeSingleMessageVerifier Y W) :
    xorGaugeSingleMessageSATReadout W = xorGaugeSingleMessageM Y := by
  exact xorGaugeSingleMessageWitness_message_eq_M hW

/-- The gauge-buffered anchor inhabits the real single-message SAT spine
interface; the hidden gauge coordinate is irrelevant to the readout. -/
def xorGaugeSingleMessageRealSingleMessageSATSpine :
    RealSingleMessageSATSpine
      XorGaugeSingleMessageSATWorld
      XorGaugeSingleMessagePublic
      (ConcreteCNF.Assignment (Fin 2)) where
  publicInput := fun omega => omega.publicInput
  witnessOfWorld := fun omega => omega.assignment
  verifier := xorGaugeSingleMessageVerifier
  messageOfPublic := xorGaugeSingleMessageM
  witnessReadout := fun W => W 0
  target := fun omega => xorGaugeSingleMessageM omega.publicInput
  worldWitnessValid := by
    intro omega
    exact omega.sat
  readout_eq_message_of_valid := by
    intro Y W hW
    exact xorGaugeSingleMessageSATReadout_eq_M_of_valid hW
  target_eq_message := by
    intro omega
    rfl

/-- Structural `singleMessage` field for the gauge-buffered XOR CNF SAT spine. -/
theorem xorGaugeSingleMessageRealSingleMessageSATSpine_singleMessage :
    ∀ w0 w1 : XorGaugeSingleMessageSATWorld,
      w0.publicInput = w1.publicInput ->
        xorGaugeSingleMessageM w0.publicInput =
          xorGaugeSingleMessageM w1.publicInput :=
  xorGaugeSingleMessageRealSingleMessageSATSpine.singleMessage

/-! ## Gauge-buffered XOR SAT-world admissible histories -/

/-- The target bit over gauge-buffered SAT worlds. -/
def xorGaugeSingleMessageSATWorldTarget
    (omega : XorGaugeSingleMessageSATWorld) : Bool :=
  xorGaugeSingleMessageM omega.publicInput

/-- Flipping the left public coordinate toggles the world target while keeping
the hidden gauge bit fixed. -/
def xorGaugeSingleMessageSATWorldFlipLeft
    (omega : XorGaugeSingleMessageSATWorld) :
    XorGaugeSingleMessageSATWorld :=
  xorGaugeSingleMessageSATWorldOf
    (xorSingleMessageFlipLeft omega.publicInput)
    (xorGaugeSingleMessageSATWorldGauge omega)

theorem xorSingleMessageFlipLeft_involutive
    (Y : XorSingleMessagePublic) :
    xorSingleMessageFlipLeft (xorSingleMessageFlipLeft Y) = Y := by
  rcases Y with ⟨b0, b1⟩
  simp [xorSingleMessageFlipLeft]

theorem xorGaugeSingleMessageSATWorldOf_public_gauge_eq
    (omega : XorGaugeSingleMessageSATWorld) :
    xorGaugeSingleMessageSATWorldOf omega.publicInput
        (xorGaugeSingleMessageSATWorldGauge omega) =
      omega :=
  xorGaugeSingleMessageSATWorldEquiv.left_inv omega

/-- The false and true target fibers of the gauge-buffered SAT-world surface
are paired by flipping the left public coordinate and preserving the hidden
gauge bit. -/
def xorGaugeSingleMessageSATWorldTargetFlipEquiv :
    {omega : XorGaugeSingleMessageSATWorld //
      xorGaugeSingleMessageSATWorldTarget omega = false} ≃
      {omega : XorGaugeSingleMessageSATWorld //
        xorGaugeSingleMessageSATWorldTarget omega = true} where
  toFun := fun omega =>
    ⟨xorGaugeSingleMessageSATWorldFlipLeft omega.val, by
      rcases omega with ⟨omega, hω⟩
      cases omega with
      | mk Y W sat =>
          rcases Y with ⟨b0, b1⟩
          cases b0 <;> cases b1 <;>
            simp [xorGaugeSingleMessageSATWorldTarget,
              xorGaugeSingleMessageSATWorldFlipLeft,
              xorGaugeSingleMessageSATWorldOf, xorGaugeSingleMessageM,
              xorSingleMessageFlipLeft, xorSingleMessageM] at hω ⊢⟩
  invFun := fun omega =>
    ⟨xorGaugeSingleMessageSATWorldFlipLeft omega.val, by
      rcases omega with ⟨omega, hω⟩
      cases omega with
      | mk Y W sat =>
          rcases Y with ⟨b0, b1⟩
          cases b0 <;> cases b1 <;>
            simp [xorGaugeSingleMessageSATWorldTarget,
              xorGaugeSingleMessageSATWorldFlipLeft,
              xorGaugeSingleMessageSATWorldOf, xorGaugeSingleMessageM,
              xorSingleMessageFlipLeft, xorSingleMessageM] at hω ⊢⟩
  left_inv := by
    intro omega
    apply Subtype.ext
    change
      xorGaugeSingleMessageSATWorldFlipLeft
          (xorGaugeSingleMessageSATWorldFlipLeft omega.val) =
        omega.val
    simp [xorGaugeSingleMessageSATWorldFlipLeft,
      xorSingleMessageFlipLeft_involutive,
      xorGaugeSingleMessageSATWorldOf_public_gauge_eq]
  right_inv := by
    intro omega
    apply Subtype.ext
    change
      xorGaugeSingleMessageSATWorldFlipLeft
          (xorGaugeSingleMessageSATWorldFlipLeft omega.val) =
        omega.val
    simp [xorGaugeSingleMessageSATWorldFlipLeft,
      xorSingleMessageFlipLeft_involutive,
      xorGaugeSingleMessageSATWorldOf_public_gauge_eq]

theorem xorGaugeSingleMessageSATWorldTarget_false_card_eq_true :
    Fintype.card
        {omega : XorGaugeSingleMessageSATWorld //
          xorGaugeSingleMessageSATWorldTarget omega = false} =
      Fintype.card
        {omega : XorGaugeSingleMessageSATWorld //
          xorGaugeSingleMessageSATWorldTarget omega = true} :=
  Fintype.card_congr xorGaugeSingleMessageSATWorldTargetFlipEquiv

theorem xorGaugeSingleMessageSATWorld_constantTrue_correct_card_eq_true :
    Fintype.card
        {omega : XorGaugeSingleMessageSATWorld //
          (fun _ : XorGaugeSingleMessageSATWorld => true) omega =
            xorGaugeSingleMessageSATWorldTarget omega} =
      Fintype.card
        {omega : XorGaugeSingleMessageSATWorld //
          xorGaugeSingleMessageSATWorldTarget omega = true} := by
  let e :
      {omega : XorGaugeSingleMessageSATWorld //
        (fun _ : XorGaugeSingleMessageSATWorld => true) omega =
          xorGaugeSingleMessageSATWorldTarget omega} ≃
        {omega : XorGaugeSingleMessageSATWorld //
          xorGaugeSingleMessageSATWorldTarget omega = true} :=
    { toFun := fun omega => ⟨omega.val, omega.property.symm⟩
      invFun := fun omega => ⟨omega.val, omega.property.symm⟩
      left_inv := by
        intro omega
        cases omega
        rfl
      right_inv := by
        intro omega
        cases omega
        rfl }
  exact Fintype.card_congr e

theorem xorGaugeSingleMessageSATWorld_card_eq_two_mul_target_true :
    Fintype.card XorGaugeSingleMessageSATWorld =
      2 * Fintype.card
        {omega : XorGaugeSingleMessageSATWorld //
          xorGaugeSingleMessageSATWorldTarget omega = true} := by
  set a : Nat :=
    Fintype.card
      {omega : XorGaugeSingleMessageSATWorld //
        xorGaugeSingleMessageSATWorldTarget omega = true}
  have hcomp :
      Fintype.card
          {omega : XorGaugeSingleMessageSATWorld //
            xorGaugeSingleMessageSATWorldTarget omega = false} =
        Fintype.card XorGaugeSingleMessageSATWorld - a := by
    simpa [a] using
      (Fintype.card_subtype_compl
        (fun omega : XorGaugeSingleMessageSATWorld =>
          xorGaugeSingleMessageSATWorldTarget omega = true))
  have heq :
      a =
        Fintype.card
          {omega : XorGaugeSingleMessageSATWorld //
            xorGaugeSingleMessageSATWorldTarget omega = false} := by
    simpa [a] using
      xorGaugeSingleMessageSATWorldTarget_false_card_eq_true.symm
  have hsub :
      Fintype.card XorGaugeSingleMessageSATWorld - a = a := by
    simpa [heq] using hcomp.symm
  have hle :
      a ≤ Fintype.card XorGaugeSingleMessageSATWorld := by
    simpa [a] using
      Fintype.card_subtype_le
        (fun omega : XorGaugeSingleMessageSATWorld =>
          xorGaugeSingleMessageSATWorldTarget omega = true)
  have hsum :
      Fintype.card XorGaugeSingleMessageSATWorld = a + a :=
    Nat.eq_add_of_sub_eq hle hsub
  simpa [a, two_mul, Nat.add_comm] using hsum

theorem xorGaugeSingleMessageSATWorldTarget_true_card_pos :
    0 <
      Fintype.card
        {omega : XorGaugeSingleMessageSATWorld //
          xorGaugeSingleMessageSATWorldTarget omega = true} := by
  exact
    Fintype.card_pos_iff.mpr
      ⟨⟨xorGaugeSingleMessageSATWorldOf (false, true) false, by
        simp [xorGaugeSingleMessageSATWorldTarget,
          xorGaugeSingleMessageSATWorldOf, xorGaugeSingleMessageM,
          xorSingleMessageM]⟩⟩

/-- The gauge-buffered SAT-world target is globally balanced. -/
theorem xorGaugeSingleMessageSATWorld_target_balanced :
    BalancedBit xorGaugeSingleMessageSATWorldTarget := by
  unfold BalancedBit globalDecoderSuccess
  rw [xorGaugeSingleMessageSATWorld_constantTrue_correct_card_eq_true]
  rw [xorGaugeSingleMessageSATWorld_card_eq_two_mul_target_true]
  set a : Nat :=
    Fintype.card
      {omega : XorGaugeSingleMessageSATWorld //
        xorGaugeSingleMessageSATWorldTarget omega = true}
  have hpos : 0 < a := by
    simpa [a] using
      xorGaugeSingleMessageSATWorldTarget_true_card_pos
  have hne : (a : Rat) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hpos)
  rw [Nat.cast_mul]
  field_simp [hne]
  norm_num

/-- A single-public-coordinate history field over gauge-buffered SAT worlds. -/
def xorGaugeSingleMessageSATWorldHistoryField
    (coord : XorSingleMessagePublicCoordinate) :
    FiniteSigmaField XorGaugeSingleMessageSATWorld where
  Atom := Bool
  atomDecidable := inferInstance
  atom := fun omega =>
    xorSingleMessagePublicCoordinateValue coord omega.publicInput

/-- Flip the public coordinate not observed by the history field, preserving
the observed atom and hidden gauge bit while toggling the target. -/
def xorGaugeSingleMessageSATWorldFlipUnobserved
    (coord : XorSingleMessagePublicCoordinate)
    (omega : XorGaugeSingleMessageSATWorld) :
    XorGaugeSingleMessageSATWorld :=
  xorGaugeSingleMessageSATWorldOf
    (xorSingleMessageFlipUnobserved coord omega.publicInput)
    (xorGaugeSingleMessageSATWorldGauge omega)

theorem xorSingleMessageFlipUnobserved_involutive
    (coord : XorSingleMessagePublicCoordinate)
    (Y : XorSingleMessagePublic) :
    xorSingleMessageFlipUnobserved coord
        (xorSingleMessageFlipUnobserved coord Y) =
      Y := by
  cases coord <;> rcases Y with ⟨b0, b1⟩ <;>
    simp [xorSingleMessageFlipUnobserved]

/-- Inside each single-coordinate history atom, preserving the hidden gauge bit
and flipping the unobserved public coordinate pairs target-true and
target-false worlds. -/
def xorGaugeSingleMessageSATWorldHistoryFieldFiberFlipEquiv
    (coord : XorSingleMessagePublicCoordinate) (atom : Bool) :
    FiberTrue
        (fun omega : XorGaugeSingleMessageSATWorld =>
          xorSingleMessagePublicCoordinateValue coord omega.publicInput)
        xorGaugeSingleMessageSATWorldTarget atom ≃
      FiberFalse
        (fun omega : XorGaugeSingleMessageSATWorld =>
          xorSingleMessagePublicCoordinateValue coord omega.publicInput)
        xorGaugeSingleMessageSATWorldTarget atom where
  toFun := fun omega =>
    ⟨xorGaugeSingleMessageSATWorldFlipUnobserved coord omega.val, by
      rcases omega with ⟨omega, hω⟩
      cases omega with
      | mk Y W sat =>
          cases coord <;> rcases Y with ⟨b0, b1⟩ <;>
            cases b0 <;> cases b1 <;> cases atom <;>
              simp [xorGaugeSingleMessageSATWorldFlipUnobserved,
                xorGaugeSingleMessageSATWorldOf,
                xorSingleMessagePublicCoordinateValue,
                xorGaugeSingleMessageSATWorldTarget,
                xorGaugeSingleMessageM, xorSingleMessageFlipUnobserved,
                xorSingleMessageM] at hω ⊢⟩
  invFun := fun omega =>
    ⟨xorGaugeSingleMessageSATWorldFlipUnobserved coord omega.val, by
      rcases omega with ⟨omega, hω⟩
      cases omega with
      | mk Y W sat =>
          cases coord <;> rcases Y with ⟨b0, b1⟩ <;>
            cases b0 <;> cases b1 <;> cases atom <;>
              simp [xorGaugeSingleMessageSATWorldFlipUnobserved,
                xorGaugeSingleMessageSATWorldOf,
                xorSingleMessagePublicCoordinateValue,
                xorGaugeSingleMessageSATWorldTarget,
                xorGaugeSingleMessageM, xorSingleMessageFlipUnobserved,
                xorSingleMessageM] at hω ⊢⟩
  left_inv := by
    intro omega
    apply Subtype.ext
    change
      xorGaugeSingleMessageSATWorldFlipUnobserved coord
          (xorGaugeSingleMessageSATWorldFlipUnobserved coord omega.val) =
        omega.val
    simp [xorGaugeSingleMessageSATWorldFlipUnobserved,
      xorSingleMessageFlipUnobserved_involutive,
      xorGaugeSingleMessageSATWorldOf_public_gauge_eq]
  right_inv := by
    intro omega
    apply Subtype.ext
    change
      xorGaugeSingleMessageSATWorldFlipUnobserved coord
          (xorGaugeSingleMessageSATWorldFlipUnobserved coord omega.val) =
        omega.val
    simp [xorGaugeSingleMessageSATWorldFlipUnobserved,
      xorSingleMessageFlipUnobserved_involutive,
      xorGaugeSingleMessageSATWorldOf_public_gauge_eq]

/-- Every single-public-coordinate history field over gauge-buffered SAT worlds
has balanced target fibers. -/
theorem xorGaugeSingleMessageSATWorld_historyField_balancedConditioning
    (coord : XorSingleMessagePublicCoordinate) :
    BalancedConditioning
      (xorGaugeSingleMessageSATWorldHistoryField coord)
      xorGaugeSingleMessageSATWorldTarget := by
  change Neutral
    (fun omega : XorGaugeSingleMessageSATWorld =>
      xorSingleMessagePublicCoordinateValue coord omega.publicInput)
    xorGaugeSingleMessageSATWorldTarget
  intro atom
  exact
    Fintype.card_congr
      (xorGaugeSingleMessageSATWorldHistoryFieldFiberFlipEquiv coord atom)

/-- Structural `admissibleHistories` field for the gauge-buffered XOR CNF SAT
worlds: the target is globally balanced and remains balanced after conditioning
on either single public coordinate, with hidden gauge multiplicity preserved. -/
theorem xorGaugeSingleMessageSATWorld_admissibleHistories
    (coord : XorSingleMessagePublicCoordinate) :
    BalancedBit xorGaugeSingleMessageSATWorldTarget ∧
      BalancedConditioning
        (xorGaugeSingleMessageSATWorldHistoryField coord)
        xorGaugeSingleMessageSATWorldTarget :=
  ⟨xorGaugeSingleMessageSATWorld_target_balanced,
    xorGaugeSingleMessageSATWorld_historyField_balancedConditioning coord⟩

/-- CD-ENF neutral evidence for the gauge-buffered anchor. -/
abbrev XorGaugeSingleMessageNeutral :=
  Unit

/-- CD-ENF safe evidence for the gauge-buffered anchor. -/
abbrev XorGaugeSingleMessageSafe :=
  Unit

/-- The evidence-level hidden gauge coordinate is Boolean. -/
abbrev XorGaugeSingleMessageGauge :=
  Bool

/-- Evidence semantics for the gauge-buffered anchor.  Gauge leaves are hidden
and universally satisfied; the nontrivial SAT-level gauge action above records
the concrete hidden degree of freedom. -/
def xorGaugeSingleMessageSemantics :
    EvidenceSemantics
      XorGaugeSingleMessageSATWorld
      XorGaugeSingleMessageNeutral
      XorGaugeSingleMessageSafe
      XorGaugeSingleMessageGauge where
  neutralSat := fun _ _ => True
  safeSat := fun _ _ => True
  gaugeSat := fun _ _ => True

/-- Structural `atomCompleteness` field for the gauge-buffered anchor. -/
theorem xorGaugeSingleMessage_atomCompleteness :
    ∀ E : RawEvidence
      XorGaugeSingleMessageNeutral
      XorGaugeSingleMessageSafe
      XorGaugeSingleMessageGauge,
      xorGaugeSingleMessageSemantics.SatNormal (CDENF E) =
        xorGaugeSingleMessageSemantics.SatRaw E := by
  intro E
  exact CDENF_semantics xorGaugeSingleMessageSemantics E

/-- Structural `gaugeFaithfulness` field for the gauge-buffered anchor. -/
theorem xorGaugeSingleMessage_gaugeFaithfulness :
    ∀ gamma : XorGaugeSingleMessageGauge,
      xorGaugeSingleMessageSemantics.SatNormal (CDENF (.gauge gamma)) =
        xorGaugeSingleMessageSemantics.gaugeSat gamma := by
  intro gamma
  rfl

/-- Structural `hiddenGaugeProduct` field for the gauge-buffered anchor. -/
theorem xorGaugeSingleMessage_hiddenGaugeProduct :
    ∀ gamma omega,
      xorGaugeSingleMessageSemantics.gaugeSat gamma omega := by
  intro gamma omega
  trivial

/-! ## Gauge-buffered XOR CNF Appendix-D/I readout lift -/

/-- Appendix-D locked core for the concrete gauge-buffered CNF anchor.  The
public lock is the public XOR instance; the quotient stores the hidden gauge
bit; the read predicate forces the message to the public readout `M(Y)`. -/
def xorGaugeSingleMessageAppendixDLockedCore :
    AppendixDLockedCore XorGaugeSingleMessagePublic Bool Unit Bool where
  publicLockFinite := inferInstance
  quotientFinite := inferInstance
  lockAuxFinite := inferInstance
  messageFinite := inferInstance
  support := fun _ => True
  lockPredicate := fun _ _ _ _ => True
  readPredicate := fun Y _ _ M => M = xorGaugeSingleMessageM Y

/-- Convert any valid concrete witness into the Appendix-D locked completion:
the hidden gauge coordinate is the quotient and the message is the forced
public readout. -/
def xorGaugeSingleMessageLockedCompletionOfWitness
    {Y : XorGaugeSingleMessagePublic}
    (W : XorGaugeSingleMessageWitness Y)
    (_hW : xorGaugeSingleMessageVerifier Y W) :
    xorGaugeSingleMessageAppendixDLockedCore.LockedCompletion Y where
  quotient := W 1
  lockAux := ()
  message := xorGaugeSingleMessageM Y
  lock_ok := trivial
  read_ok := rfl

/-- The concrete locked core has a public-message invariant: every accepted
completion over public lock `Y` reads exactly `M(Y)`. -/
theorem xorGaugeSingleMessageAppendixD_publicMessageInvariant :
    xorGaugeSingleMessageAppendixDLockedCore.PublicMessageInvariant
      xorGaugeSingleMessageM := by
  intro Y _hY L
  simpa [xorGaugeSingleMessageAppendixDLockedCore] using L.read_ok

/-- Hence the concrete locked core satisfies Appendix-D locked-message
rigidity.  The proof uses the read predicate forcing `M(Y)`, not a separate
assumption. -/
theorem xorGaugeSingleMessageAppendixD_lockedMessageRigidity :
    xorGaugeSingleMessageAppendixDLockedCore.LockedMessageRigidity :=
  AppendixDLockedCore.lockedMessageRigidity_of_publicMessageInvariant
    xorGaugeSingleMessageAppendixDLockedCore
    xorGaugeSingleMessageAppendixD_publicMessageInvariant

/-- The concrete gauge-buffered CNF anchor inhabits the stronger Appendix-I
readout interface over its real Appendix-D locked core. -/
def xorGaugeSingleMessageAppendixICNFReadoutData :
    AppendixICNFReadoutData
      XorGaugeSingleMessagePublic
      Bool
      Unit
      Bool
      XorGaugeSingleMessagePublic
      XorGaugeSingleMessageVar
      XorGaugeSingleMessageWitness where
  core := xorGaugeSingleMessageAppendixDLockedCore
  support := xorGaugeSingleMessageSupport
  publicLock := fun Y => Y
  validWitness := xorGaugeSingleMessageVerifier
  witnessMessage := xorGaugeSingleMessageWitnessMessage
  witnessCompletion := by
    intro Y W hW
    exact xorGaugeSingleMessageLockedCompletionOfWitness W hW
  support_publicLock := by
    intro Y hY
    trivial
  witnessMessage_eq_completionMessage := by
    intro Y W hW
    simp [xorGaugeSingleMessageWitnessMessage,
      xorGaugeSingleMessageLockedCompletionOfWitness,
      xorGaugeSingleMessageWitness_message_eq_M hW]
  formula := xorGaugeSingleMessageFormula
  extract := xorGaugeSingleMessageExtract
  projection := xorGaugeSingleMessageProjection
  cnfSound := by
    intro Y W hW
    exact hW
  projection_eq_witnessMessage := by
    intro Y W hW
    rfl
  satOnSupport := by
    intro Y hY
    exact
      ⟨xorGaugeSingleMessageAssignment Y false,
        xorGaugeSingleMessageFormula_satisfied_assignment Y false⟩

/-- Appendix-I semantic readout items for the concrete gauge-buffered CNF:
supported instances are satisfiable, satisfying assignments extract to valid
witnesses, and the fixed projection has single-message readout. -/
theorem xorGaugeSingleMessageAppendixI_semantic_i26_items
    (Y : XorGaugeSingleMessagePublic) :
    (∃ α : ConcreteCNF.Assignment (XorGaugeSingleMessageVar Y),
      ConcreteCNF.IsSatFormula (xorGaugeSingleMessageFormula Y) α) ∧
    (∀ α : ConcreteCNF.Assignment (XorGaugeSingleMessageVar Y),
      ConcreteCNF.IsSatFormula (xorGaugeSingleMessageFormula Y) α →
        xorGaugeSingleMessageVerifier Y
          (xorGaugeSingleMessageExtract Y α)) ∧
    SingleMessageReadout
      (ConcreteCNF.IsSatFormula (xorGaugeSingleMessageFormula Y))
      (xorGaugeSingleMessageProjection Y) := by
  simpa [xorGaugeSingleMessageAppendixICNFReadoutData]
    using
      (xorGaugeSingleMessageAppendixICNFReadoutData
        |>.semantic_i26_items_of_lockedMessageRigidity
          xorGaugeSingleMessageAppendixD_lockedMessageRigidity
          (Y := Y)
          trivial)

/-- The Appendix-I CNF assignments for the concrete gauge-buffered anchor form
the real single-message SAT spine. -/
def xorGaugeSingleMessageAppendixICNFSingleMessageSATSpine :
    RealSingleMessageSATSpine
      (RealM4CNFWorld xorGaugeSingleMessageAppendixICNFReadoutData)
      XorGaugeSingleMessagePublic
      (RealM4CNFWitness xorGaugeSingleMessageAppendixICNFReadoutData) :=
  realM4CNFSingleMessageSATSpine
    xorGaugeSingleMessageAppendixICNFReadoutData
    xorGaugeSingleMessageM
    (fun bit => bit)
    xorGaugeSingleMessageAppendixD_publicMessageInvariant

/-- Structural `singleMessage` for the concrete Appendix-I CNF SAT spine. -/
theorem xorGaugeSingleMessageAppendixICNFSingleMessageSATSpine_singleMessage :
    ∀ w0 w1 :
      RealM4CNFWorld xorGaugeSingleMessageAppendixICNFReadoutData,
      w0.publicInstance = w1.publicInstance →
        realM4CNFMessageOfPublic
            xorGaugeSingleMessageAppendixICNFReadoutData
            xorGaugeSingleMessageM
            (fun bit => bit)
            w0.publicInstance =
          realM4CNFMessageOfPublic
            xorGaugeSingleMessageAppendixICNFReadoutData
            xorGaugeSingleMessageM
            (fun bit => bit)
            w1.publicInstance :=
  xorGaugeSingleMessageAppendixICNFSingleMessageSATSpine.singleMessage

/-- Target bit on the concrete Appendix-I CNF world spine. -/
def xorGaugeSingleMessageAppendixICNFWorldTarget
    (omega : RealM4CNFWorld xorGaugeSingleMessageAppendixICNFReadoutData) :
    Bool :=
  realM4CNFMessageOfPublic
    xorGaugeSingleMessageAppendixICNFReadoutData
    xorGaugeSingleMessageM
    (fun bit => bit)
    omega.publicInstance

/-- No single public coordinate should determine the concrete Appendix-I CNF
world target. -/
def XorGaugeSingleMessageAppendixICNFNoPublicCoordinateTargetTags : Prop :=
  ∀ coord : XorSingleMessagePublicCoordinate,
    ¬ ∃ f : Bool -> Bool,
      ∀ omega :
        RealM4CNFWorld xorGaugeSingleMessageAppendixICNFReadoutData,
        xorGaugeSingleMessageAppendixICNFWorldTarget omega =
          f (xorSingleMessagePublicCoordinateValue coord omega.publicInstance)

/-- Structural `noPublicTargetTags` transferred to the stronger Appendix-I CNF
world spine: adding satisfying assignments and the Appendix-D/I readout layer
does not make one public coordinate determine the target. -/
theorem xorGaugeSingleMessageAppendixICNF_noPublicTargetTags :
    XorGaugeSingleMessageAppendixICNFNoPublicCoordinateTargetTags := by
  intro coord htag
  exact xorGaugeSingleMessage_noPublicTargetTags coord
    (by
      rcases htag with ⟨f, hf⟩
      refine ⟨f, ?_⟩
      intro Y
      let omega :
          RealM4CNFWorld xorGaugeSingleMessageAppendixICNFReadoutData :=
        { publicInstance := Y
          support := trivial
          assignment := xorGaugeSingleMessageAssignment Y false
          sat := xorGaugeSingleMessageFormula_satisfied_assignment Y false }
      have htarget := hf omega
      simpa [omega, xorGaugeSingleMessageAppendixICNFWorldTarget,
        realM4CNFMessageOfPublic, xorGaugeSingleMessageAppendixICNFReadoutData]
        using htarget)

/-- No single public coordinate should determine the readout of every
verifier-valid witness in the concrete Appendix-I CNF spine. -/
def XorGaugeSingleMessageAppendixICNFNoPublicCoordinateReadoutTags : Prop :=
  ∀ coord : XorSingleMessagePublicCoordinate,
    ¬ ∃ f : Bool -> Bool,
      ∀ {Y : XorGaugeSingleMessagePublic}
        {W : RealM4CNFWitness xorGaugeSingleMessageAppendixICNFReadoutData},
          realM4CNFVerifier
              xorGaugeSingleMessageAppendixICNFReadoutData Y W ->
            realM4CNFWitnessReadout (fun bit => bit) W =
              f (xorSingleMessagePublicCoordinateValue coord Y)

/-- Structural readout-tag transfer for the concrete Appendix-I CNF spine:
even after moving to verifier-valid CNF witnesses, no single public coordinate
predicts the fixed message readout. -/
theorem xorGaugeSingleMessageAppendixICNF_noPublicReadoutTags :
    XorGaugeSingleMessageAppendixICNFNoPublicCoordinateReadoutTags := by
  intro coord htag
  exact xorGaugeSingleMessage_noPublicTargetTags coord
    (by
      rcases htag with ⟨f, hf⟩
      refine ⟨f, ?_⟩
      intro Y
      let W :
          RealM4CNFWitness xorGaugeSingleMessageAppendixICNFReadoutData :=
        { publicInstance := Y
          assignment := xorGaugeSingleMessageAssignment Y false }
      have hvalid :
          realM4CNFVerifier
              xorGaugeSingleMessageAppendixICNFReadoutData Y W := by
        exact
          ⟨trivial, ⟨rfl,
            xorGaugeSingleMessageFormula_satisfied_assignment Y false⟩⟩
      have hreadout := hf (Y := Y) (W := W) hvalid
      simpa [W, realM4CNFWitnessReadout,
        xorGaugeSingleMessageAppendixICNFReadoutData,
        xorGaugeSingleMessageProjection, xorGaugeSingleMessageAssignment,
        xorGaugeSingleMessageM] using hreadout)

/-! ## Gauge-buffered XOR CNF self-reduction under an explicit decider -/

/-- Explicit P=NP-side SAT decider object for the concrete gauge-buffered
anchor.  The theorem statements below remain conditional on this object; they
do not construct an unconditional SAT solver. -/
abbrev XorGaugeSingleMessagePNPSATDecider :=
  RealCNFPNPSATDecider (Fin 2)

/-- Bit-fixing order for the two-variable anchor: first the forced message
coordinate, then the hidden gauge coordinate. -/
def xorGaugeSingleMessageVarOrder : List (Fin 2) :=
  [0, 1]

theorem xorGaugeSingleMessageVarOrder_nodup :
    xorGaugeSingleMessageVarOrder.Nodup := by
  simp [xorGaugeSingleMessageVarOrder]

theorem xorGaugeSingleMessageFormula_usesOnly
    (Y : XorGaugeSingleMessagePublic) :
    ConcreteCNF.FormulaUsesOnly
      (xorGaugeSingleMessageFormula Y)
      xorGaugeSingleMessageVarOrder := by
  intro clause hclause lit hlit
  cases hmsg : xorGaugeSingleMessageM Y
  · simp [xorGaugeSingleMessageFormula, ConcreteCNF.unitClause,
      ConcreteCNF.unitLiteral, hmsg] at hclause
    subst clause
    have hlit_eq : lit = ConcreteCNF.Literal.neg (0 : Fin 2) := by
      simpa using hlit
    subst lit
    simp [xorGaugeSingleMessageVarOrder, ConcreteCNF.Literal.var]
  · simp [xorGaugeSingleMessageFormula, ConcreteCNF.unitClause,
      ConcreteCNF.unitLiteral, hmsg] at hclause
    subst clause
    have hlit_eq : lit = ConcreteCNF.Literal.pos (0 : Fin 2) := by
      simpa using hlit
    subst lit
    simp [xorGaugeSingleMessageVarOrder, ConcreteCNF.Literal.var]

theorem xorGaugeSingleMessageFormula_satisfiable
    (Y : XorGaugeSingleMessagePublic) :
    ∃ σ : ConcreteCNF.Assignment (Fin 2),
      ConcreteCNF.IsSatFormula (xorGaugeSingleMessageFormula Y) σ :=
  ⟨xorGaugeSingleMessageAssignment Y false,
    xorGaugeSingleMessageFormula_satisfied_assignment Y false⟩

/-- The standard bit-fixing search-to-decision assignment for the concrete
gauge-buffered CNF, conditional on the explicit SAT decider object. -/
def xorGaugeSingleMessageSelfReductionAssignment
    (D : XorGaugeSingleMessagePNPSATDecider)
    (Y : XorGaugeSingleMessagePublic) :
    ConcreteCNF.Assignment (Fin 2) :=
  realCNFBitFixAssignment D
    (xorGaugeSingleMessageFormula Y)
    xorGaugeSingleMessageVarOrder

/-- Bit-fixing with the explicit SAT decider returns a satisfying assignment
for the concrete locked CNF. -/
theorem xorGaugeSingleMessageSelfReductionAssignment_satisfies
    (D : XorGaugeSingleMessagePNPSATDecider)
    (Y : XorGaugeSingleMessagePublic) :
    ConcreteCNF.IsSatFormula
      (xorGaugeSingleMessageFormula Y)
      (xorGaugeSingleMessageSelfReductionAssignment D Y) := by
  exact
    realCNFBitFixAssignment_satisfies
      D
      (xorGaugeSingleMessageFormula_usesOnly Y)
      xorGaugeSingleMessageVarOrder_nodup
      (xorGaugeSingleMessageFormula_satisfiable Y)

/-- The readout of the recovered bit-fixing witness is exactly the fixed
public message `M(Y)`.  This is the concrete search-to-decision upper side:
the hidden gauge bit may be chosen arbitrarily by search, but the readout is
forced by the single-message promise. -/
theorem xorGaugeSingleMessageSelfReduction_readout_eq_M
    (D : XorGaugeSingleMessagePNPSATDecider)
    (Y : XorGaugeSingleMessagePublic) :
    xorGaugeSingleMessageProjection Y
        (xorGaugeSingleMessageSelfReductionAssignment D Y) =
      xorGaugeSingleMessageM Y := by
  exact
    xorGaugeSingleMessageCNFReadoutData_projection_eq_M
      (Y := Y)
      (W := xorGaugeSingleMessageSelfReductionAssignment D Y)
      trivial
      (xorGaugeSingleMessageSelfReductionAssignment_satisfies D Y)

/-- The concrete self-reduction uses a fixed program skeleton around the
explicit SAT decider, so its `kpolyAt` model is constant in `targetBlocks`. -/
theorem xorGaugeSingleMessageConstantDecoderKpolyAt_const
    (D : XorGaugeSingleMessagePNPSATDecider)
    (targetBlocks targetBlocks' : Nat) :
    realCNFConstantDecoderKpolyAt D targetBlocks =
      realCNFConstantDecoderKpolyAt D targetBlocks' :=
  realCNFConstantDecoderKpolyAt_const D targetBlocks targetBlocks'

/-- Conditional upper-bound discharge for the concrete gauge-buffered CNF:
given the explicit P=NP-side SAT decider object and a lower-framework regime
identifying `kpolyAt` with the constant self-reduction decoder and
`etaTimes t` with a linear floor, the upper cost lies below the floor. -/
theorem xorGaugeSingleMessage_selfReductionUpperHypothesis_givenPNP
    {F : CompressionLowerFramework}
    (D : XorGaugeSingleMessagePNPSATDecider)
    (R : RealCNFConstantDecoderRegime F D) :
    SelfReductionUpperHypothesis F where
  upperStrictlyBelowCompressionFloor := by
    rw [R.kpolyAt_eq, R.etaTimes_eq]
    exact R.floor_dominates_decoder

end Mettapedia.Computability.PNP

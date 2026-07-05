import Mettapedia.Computability.PNP.PNPv13ManuscriptCNFReadoutCore

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

end Mettapedia.Computability.PNP

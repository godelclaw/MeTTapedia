import Mettapedia.Computability.PNP.PNPv13ConcreteSATReadoutObstruction

/-!
# PNP v13: manuscript CNF readout core

This module formalizes the exact readout-constancy bridge used in v13,
Appendix I.4. The manuscript proves CNF-level constancy from three ingredients:

* every satisfying CNF assignment extracts to a valid witness;
* the fixed CNF projection reads the same message as the extracted witness;
* valid witnesses for a supported public instance satisfy the single-message
  promise.
-/

namespace Mettapedia.Computability.PNP

universe u v w x y z

/-- The manuscript-shaped interface behind v13 Appendix I.19--I.23.

For each public instance `Y`, `formula Y` is the CNF `F_Y`, `extract Y`
is `Wit_Y`, and `projection Y` is the fixed message projection `π_M`.
The fields keep only the hypotheses needed to prove CNF-level readout
constancy; uniformity, polynomial size, and clock bounds live outside this
local constancy argument. -/
structure ManuscriptCNFReadoutData (Public : Type u)
    (Var : Public → Type v) (Witness : Public → Type w)
    (Message : Type z) where
  /-- Public instances on which the manuscript ensemble promises a message. -/
  support : Public → Prop
  /-- The concrete CNF `F_Y`. -/
  formula : (Y : Public) → ConcreteCNF.Formula (Var Y)
  /-- The semantic witness relation `R(Y,W)=1`. -/
  validWitness : (Y : Public) → Witness Y → Prop
  /-- The witness extraction map `Wit_Y(α)` from CNF assignments. -/
  extract : (Y : Public) → ConcreteCNF.Assignment (Var Y) → Witness Y
  /-- The semantic message coordinate `M(W)`. -/
  witnessMessage : (Y : Public) → Witness Y → Message
  /-- The fixed CNF-level message projection `π_M(α)`. -/
  projection : (Y : Public) → ConcreteCNF.Assignment (Var Y) → Message
  /-- Proposition I.19, forward direction: satisfying CNF assignments extract
  to valid semantic witnesses. -/
  cnfSound :
    ∀ {Y : Public} {α : ConcreteCNF.Assignment (Var Y)},
      ConcreteCNF.IsSatFormula (formula Y) α →
        validWitness Y (extract Y α)
  /-- Definition I.18 compatibility: the extracted witness message is exactly
  the fixed CNF projection on satisfying assignments. -/
  projection_eq_witnessMessage :
    ∀ {Y : Public} {α : ConcreteCNF.Assignment (Var Y)},
      ConcreteCNF.IsSatFormula (formula Y) α →
        projection Y α = witnessMessage Y (extract Y α)

namespace ManuscriptCNFReadoutData

variable {Public : Type u} {Var : Public → Type v}
variable {Witness : Public → Type w} {Message : Type z}

/-- The v13 single-message promise, restricted to supported public instances:
any two valid witnesses carry the same semantic message. -/
def SingleMessagePromise
    (D : ManuscriptCNFReadoutData Public Var Witness Message) : Prop :=
  ∀ {Y : Public} {W W' : Witness Y},
    D.support Y →
      D.validWitness Y W →
        D.validWitness Y W' →
          D.witnessMessage Y W = D.witnessMessage Y W'

/-- Every valid semantic witness over a supported public instance is
represented by some satisfying CNF assignment.  This is the completeness
direction needed to turn CNF-level SAT-search correctness back into the
semantic single-message promise. -/
def CNFExtractionComplete
    (D : ManuscriptCNFReadoutData Public Var Witness Message) : Prop :=
  ∀ {Y : Public} {W : Witness Y},
    D.support Y →
      D.validWitness Y W →
        ∃ α : ConcreteCNF.Assignment (Var Y),
          ConcreteCNF.IsSatFormula (D.formula Y) α ∧ D.extract Y α = W

/-- Every supported public instance has at least one satisfying CNF assignment.
This is the satisfiability side needed for the forward arbitrary-output
SAT-search decoder theorem. -/
def SupportedCNFSatisfiable
    (D : ManuscriptCNFReadoutData Public Var Witness Message) : Prop :=
  ∀ {Y : Public},
    D.support Y →
      ∃ α : ConcreteCNF.Assignment (Var Y),
        ConcreteCNF.IsSatFormula (D.formula Y) α

/-- The supported arbitrary-output SAT-search decoder obligation: for every
supported public instance, there is a message correct for every satisfying
CNF assignment that SAT search may return. -/
def SupportedArbitraryOutputSATSearchCorrect
    (D : ManuscriptCNFReadoutData Public Var Witness Message) : Prop :=
  ∀ {Y : Public},
    D.support Y →
      ∃ msg : Message,
        CorrectForAllSatSearchOutputs
          (ConcreteCNF.IsSatFormula (D.formula Y)) (D.projection Y) msg

/-- Lemma I.23 in the manuscript-shaped interface: the witness-level
single-message promise implies CNF-level readout constancy for the fixed
projection. -/
theorem singleMessageReadout_of_singleMessagePromise
    (D : ManuscriptCNFReadoutData Public Var Witness Message)
    (hpromise : D.SingleMessagePromise)
    {Y : Public} (hY : D.support Y) :
    SingleMessageReadout
      (ConcreteCNF.IsSatFormula (D.formula Y)) (D.projection Y) := by
  intro α β hα hβ
  calc
    D.projection Y α = D.witnessMessage Y (D.extract Y α) :=
      D.projection_eq_witnessMessage hα
    _ = D.witnessMessage Y (D.extract Y β) :=
      hpromise hY (D.cnfSound hα) (D.cnfSound hβ)
    _ = D.projection Y β :=
      (D.projection_eq_witnessMessage hβ).symm

/-- The arbitrary-output SAT-search decoder obligation closes once the
manuscript-shaped CNF is satisfiable and satisfies the single-message promise. -/
theorem exists_correctForAllSatSearchOutputs_of_singleMessagePromise
    (D : ManuscriptCNFReadoutData Public Var Witness Message)
    (hpromise : D.SingleMessagePromise)
    {Y : Public} (hY : D.support Y)
    {α₀ : ConcreteCNF.Assignment (Var Y)}
    (hα₀ : ConcreteCNF.IsSatFormula (D.formula Y) α₀) :
    ∃ msg : Message,
      CorrectForAllSatSearchOutputs
        (ConcreteCNF.IsSatFormula (D.formula Y)) (D.projection Y) msg := by
  exact
    cnf_exists_correctForAllSatSearchOutputs_of_singleMessageReadout
      hα₀ (D.singleMessageReadout_of_singleMessagePromise hpromise hY)

/-- Supported form of the forward bridge: the single-message promise plus
supported satisfiability supplies a message correct for every satisfying
SAT-search output on each supported public instance. -/
theorem supportedArbitraryOutputSATSearchCorrect_of_singleMessagePromise
    (D : ManuscriptCNFReadoutData Public Var Witness Message)
    (hpromise : D.SingleMessagePromise)
    (hsat : D.SupportedCNFSatisfiable) :
    D.SupportedArbitraryOutputSATSearchCorrect := by
  intro Y hY
  rcases hsat hY with ⟨α₀, hα₀⟩
  exact D.exists_correctForAllSatSearchOutputs_of_singleMessagePromise hpromise hY hα₀

/-- Converse bridge: if every valid witness is represented by a satisfying
assignment, then arbitrary-output SAT-search correctness on supported public
instances forces the semantic single-message promise.  Thus SAT search
correctness cannot replace the manuscript's single-message theorem; under the
natural completeness direction it is at least as strong. -/
theorem singleMessagePromise_of_cnfExtractionComplete_of_supportedArbitraryOutputSATSearchCorrect
    (D : ManuscriptCNFReadoutData Public Var Witness Message)
    (hcomplete : D.CNFExtractionComplete)
    (hcorrect : D.SupportedArbitraryOutputSATSearchCorrect) :
    D.SingleMessagePromise := by
  intro Y W W' hY hW hW'
  rcases hcomplete hY hW with ⟨α, hα, hextract⟩
  rcases hcomplete hY hW' with ⟨β, hβ, hextract'⟩
  rcases hcorrect hY with ⟨msg, hmsg⟩
  have hproj :
      D.projection Y α = D.witnessMessage Y W := by
    simpa [hextract] using D.projection_eq_witnessMessage hα
  have hproj' :
      D.projection Y β = D.witnessMessage Y W' := by
    simpa [hextract'] using D.projection_eq_witnessMessage hβ
  calc
    D.witnessMessage Y W = D.projection Y α := hproj.symm
    _ = msg := hmsg ⟨α, hα⟩
    _ = D.projection Y β := (hmsg ⟨β, hβ⟩).symm
    _ = D.witnessMessage Y W' := hproj'

/-- Under supported satisfiability and CNF extraction completeness,
arbitrary-output SAT-search correctness is equivalent to the semantic
single-message promise.  This is the minimal repair target for the v13 CNF
readout route. -/
theorem supportedArbitraryOutputSATSearchCorrect_iff_singleMessagePromise
    (D : ManuscriptCNFReadoutData Public Var Witness Message)
    (hsat : D.SupportedCNFSatisfiable)
    (hcomplete : D.CNFExtractionComplete) :
    D.SupportedArbitraryOutputSATSearchCorrect ↔ D.SingleMessagePromise := by
  constructor
  · intro hcorrect
    exact
      D.singleMessagePromise_of_cnfExtractionComplete_of_supportedArbitraryOutputSATSearchCorrect
        hcomplete hcorrect
  · intro hpromise
    exact D.supportedArbitraryOutputSATSearchCorrect_of_singleMessagePromise hpromise hsat

/-- If CNF extraction is complete, failure of the semantic single-message
promise rules out the supported arbitrary-output SAT-search decoder theorem. -/
theorem not_supportedArbitraryOutputSATSearchCorrect_of_cnfExtractionComplete_of_not_singleMessagePromise
    (D : ManuscriptCNFReadoutData Public Var Witness Message)
    (hcomplete : D.CNFExtractionComplete)
    (hnot : ¬ D.SingleMessagePromise) :
    ¬ D.SupportedArbitraryOutputSATSearchCorrect := by
  intro hcorrect
  exact hnot
    (D.singleMessagePromise_of_cnfExtractionComplete_of_supportedArbitraryOutputSATSearchCorrect
      hcomplete hcorrect)

/-- Exact obstruction to the v13 witness-level single-message promise:
two valid witnesses over one supported public input with different semantic
messages refute the promise. -/
theorem not_singleMessagePromise_of_distinct_valid_witnessMessages
    (D : ManuscriptCNFReadoutData Public Var Witness Message)
    {Y : Public} {W W' : Witness Y}
    (hY : D.support Y)
    (hW : D.validWitness Y W) (hW' : D.validWitness Y W')
    (hdiff : D.witnessMessage Y W ≠ D.witnessMessage Y W') :
    ¬ D.SingleMessagePromise := by
  intro hpromise
  exact hdiff (hpromise hY hW hW')

/-- Complete-CNF form of the readout blocker: once every valid witness is
represented by a satisfying assignment, two valid witnesses with distinct
messages rule out arbitrary-output SAT-search correctness on supported
instances. -/
theorem not_supportedArbitraryOutputSATSearchCorrect_of_complete_distinct_valid_witnessMessages
    (D : ManuscriptCNFReadoutData Public Var Witness Message)
    (hcomplete : D.CNFExtractionComplete)
    {Y : Public} {W W' : Witness Y}
    (hY : D.support Y)
    (hW : D.validWitness Y W) (hW' : D.validWitness Y W')
    (hdiff : D.witnessMessage Y W ≠ D.witnessMessage Y W') :
    ¬ D.SupportedArbitraryOutputSATSearchCorrect := by
  exact
    D.not_supportedArbitraryOutputSATSearchCorrect_of_cnfExtractionComplete_of_not_singleMessagePromise
      hcomplete
      (D.not_singleMessagePromise_of_distinct_valid_witnessMessages
        hY hW hW' hdiff)

end ManuscriptCNFReadoutData

end Mettapedia.Computability.PNP

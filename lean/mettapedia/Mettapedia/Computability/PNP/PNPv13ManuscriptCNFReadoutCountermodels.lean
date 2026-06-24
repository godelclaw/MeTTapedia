import Mettapedia.Computability.PNP.PNPv13ManuscriptCNFReadoutDeterministic

/-!
# PNP v13: CNF readout countermodels

This module collects the one-variable models showing which hypotheses are
strictly needed for the manuscript CNF-readout route.
-/

namespace Mettapedia.Computability.PNP

universe u v w x y z

/-- A single supported public instance used to stress-test the interface without
the witness-level single-message promise. -/
def oneVarReadoutPublicVar (_ : Unit) : Type :=
  Fin 1

/-- In this countermodel, a semantic witness is just the CNF assignment read
through the intended witness blocks. -/
def oneVarReadoutWitness (_ : Unit) : Type :=
  ConcreteCNF.Assignment (Fin 1)

/-- In the locked-layer countermodel, the locked view is just the same free CNF
assignment. -/
def oneVarReadoutLockView (_ : Unit) : Type :=
  ConcreteCNF.Assignment (Fin 1)

/-- The readout state in the deterministic-readout countermodel is the state
whose unique message is its Boolean value. -/
def oneVarReadoutReadState (_ : Unit) : Type :=
  Bool

/-- The compiler/extraction/projection shape alone can be satisfied by a CNF
whose free satisfying assignments have different projected messages. -/
def ambiguousOneVarManuscriptCNFReadoutData :
    ManuscriptCNFReadoutData
      Unit oneVarReadoutPublicVar oneVarReadoutWitness Bool where
  support := fun _ => True
  formula := fun _ => oneVarTautologyCNF
  validWitness := fun _ σ => ConcreteCNF.IsSatFormula oneVarTautologyCNF σ
  extract := fun _ σ => σ
  witnessMessage := fun _ σ => oneVarReadout σ
  projection := fun _ σ => oneVarReadout σ
  cnfSound := by
    intro _ _ h
    exact h
  projection_eq_witnessMessage := by
    intro _ _ _
    rfl

/-- The countermodel public instance is in support. -/
theorem ambiguousOneVarManuscriptCNFReadoutData_support :
    ambiguousOneVarManuscriptCNFReadoutData.support () := by
  trivial

/-- The countermodel CNF is satisfiable. -/
theorem ambiguousOneVarManuscriptCNFReadoutData_satisfiable :
    ∃ α : ConcreteCNF.Assignment (oneVarReadoutPublicVar ()),
      ConcreteCNF.IsSatFormula
        (ambiguousOneVarManuscriptCNFReadoutData.formula ()) α := by
  exact ⟨oneVarFalseAssignment, oneVarTautologyCNF_satisfied_false⟩

/-- The countermodel is supported-satisfiable in the manuscript-shaped
interface. -/
theorem ambiguousOneVarManuscriptCNFReadoutData_supportedCNFSatisfiable :
    ambiguousOneVarManuscriptCNFReadoutData.SupportedCNFSatisfiable := by
  intro Y _hY
  cases Y
  exact ambiguousOneVarManuscriptCNFReadoutData_satisfiable

/-- The countermodel also satisfies the natural extraction-completeness
direction: every valid witness is already a satisfying CNF assignment and is
extracted by the identity map. -/
theorem ambiguousOneVarManuscriptCNFReadoutData_cnfExtractionComplete :
    ambiguousOneVarManuscriptCNFReadoutData.CNFExtractionComplete := by
  intro Y W _hY hW
  cases Y
  exact ⟨W, hW, rfl⟩

/-- Without the single-message promise, the manuscript-shaped compiler
interface permits two valid witnesses with different messages. -/
theorem ambiguousOneVarManuscriptCNFReadoutData_not_singleMessagePromise :
    ¬ ambiguousOneVarManuscriptCNFReadoutData.SingleMessagePromise := by
  exact
    ManuscriptCNFReadoutData.not_singleMessagePromise_of_distinct_valid_witnessMessages
      ambiguousOneVarManuscriptCNFReadoutData
      (Y := ())
      trivial
      oneVarTautologyCNF_satisfied_false
      oneVarTautologyCNF_satisfied_true
      oneVarReadout_false_ne_true

/-- Consequently the compiler/extraction/projection interface alone does not
give the arbitrary-output SAT-search decoder theorem. -/
theorem ambiguousOneVarManuscriptCNFReadoutData_not_exists_correctForAll :
    ¬ ∃ msg : Bool,
      CorrectForAllSatSearchOutputs
        (ConcreteCNF.IsSatFormula
          (ambiguousOneVarManuscriptCNFReadoutData.formula ()))
        (ambiguousOneVarManuscriptCNFReadoutData.projection ()) msg := by
  change ¬ ∃ msg : Bool,
    CorrectForAllSatSearchOutputs
      (ConcreteCNF.IsSatFormula oneVarTautologyCNF) oneVarReadout msg
  exact oneVarTautologyCNF_not_exists_correctForAllSatSearchOutputs

/-- Complete extraction plus the two-message ambiguity rules out the supported
arbitrary-output SAT-search obligation globally, not merely at a hand-selected
message. -/
theorem ambiguousOneVarManuscriptCNFReadoutData_not_supportedArbitraryOutputSATSearchCorrect :
    ¬ ambiguousOneVarManuscriptCNFReadoutData.SupportedArbitraryOutputSATSearchCorrect := by
  exact
    ManuscriptCNFReadoutData.not_supportedArbitraryOutputSATSearchCorrect_of_cnfExtractionComplete_of_not_singleMessagePromise
      ambiguousOneVarManuscriptCNFReadoutData
      ambiguousOneVarManuscriptCNFReadoutData_cnfExtractionComplete
      ambiguousOneVarManuscriptCNFReadoutData_not_singleMessagePromise

/-- A semantic witness type used to test whether CNF-side readout constancy can
replace extraction completeness.  The CNF below only extracts the `false`
witness, while `true` remains a valid unrepresented semantic witness. -/
def unrepresentedOneVarReadoutWitness (_ : Unit) : Type :=
  Bool

/-- CNF-side SAT-search correctness can hold vacuously on the extracted image
while the semantic witness relation is still ambiguous.  This is not a complete
CNF realization; it marks why `CNFExtractionComplete` is a real premise in the
converse bridge above. -/
def unrepresentedOneVarManuscriptCNFReadoutData :
    ManuscriptCNFReadoutData
      Unit oneVarReadoutPublicVar unrepresentedOneVarReadoutWitness Bool where
  support := fun _ => True
  formula := fun _ => oneVarTautologyCNF
  validWitness := fun _ _ => True
  extract := fun _ _ => false
  witnessMessage := fun _ W => W
  projection := fun _ _ => false
  cnfSound := by
    intro _ _ _
    trivial
  projection_eq_witnessMessage := by
    intro _ _ _
    rfl

/-- The unrepresented-witness countermodel is supported-satisfiable. -/
theorem unrepresentedOneVarManuscriptCNFReadoutData_supportedCNFSatisfiable :
    unrepresentedOneVarManuscriptCNFReadoutData.SupportedCNFSatisfiable := by
  intro Y _hY
  cases Y
  exact ⟨oneVarFalseAssignment, oneVarTautologyCNF_satisfied_false⟩

/-- The CNF projection in the unrepresented-witness countermodel is constant
on all satisfying assignments. -/
theorem unrepresentedOneVarManuscriptCNFReadoutData_singleMessageReadout :
    SingleMessageReadout
      (ConcreteCNF.IsSatFormula
        (unrepresentedOneVarManuscriptCNFReadoutData.formula ()))
      (unrepresentedOneVarManuscriptCNFReadoutData.projection ()) := by
  intro _ _ _ _
  rfl

/-- Hence the supported arbitrary-output SAT-search obligation holds on the
CNF side. -/
theorem unrepresentedOneVarManuscriptCNFReadoutData_supportedArbitraryOutputSATSearchCorrect :
    unrepresentedOneVarManuscriptCNFReadoutData.SupportedArbitraryOutputSATSearchCorrect := by
  intro Y _hY
  cases Y
  exact
    ⟨false, by
      intro _out
      rfl⟩

/-- But the semantic witness relation still has two valid witnesses with
different messages. -/
theorem unrepresentedOneVarManuscriptCNFReadoutData_not_singleMessagePromise :
    ¬ unrepresentedOneVarManuscriptCNFReadoutData.SingleMessagePromise := by
  exact
    ManuscriptCNFReadoutData.not_singleMessagePromise_of_distinct_valid_witnessMessages
      unrepresentedOneVarManuscriptCNFReadoutData
      (Y := ())
      (W := false)
      (W' := true)
      trivial
      trivial
      trivial
      (by simp [unrepresentedOneVarManuscriptCNFReadoutData])

/-- The missing hypothesis is exactly extraction completeness: the valid `true`
witness is not the extraction of any satisfying assignment. -/
theorem unrepresentedOneVarManuscriptCNFReadoutData_not_cnfExtractionComplete :
    ¬ unrepresentedOneVarManuscriptCNFReadoutData.CNFExtractionComplete := by
  intro hcomplete
  rcases hcomplete (Y := ()) (W := true) trivial trivial with
    ⟨α, _hα, hextract⟩
  simp [unrepresentedOneVarManuscriptCNFReadoutData] at hextract

/-- Boundary theorem: without extraction completeness, supported
arbitrary-output SAT-search correctness over the CNF can coexist with failure
of the semantic single-message promise. -/
theorem unrepresentedOneVarManuscriptCNFReadoutData_satSearchCorrect_and_not_singleMessagePromise :
    unrepresentedOneVarManuscriptCNFReadoutData.SupportedArbitraryOutputSATSearchCorrect ∧
      ¬ unrepresentedOneVarManuscriptCNFReadoutData.SingleMessagePromise := by
  exact
    ⟨unrepresentedOneVarManuscriptCNFReadoutData_supportedArbitraryOutputSATSearchCorrect,
      unrepresentedOneVarManuscriptCNFReadoutData_not_singleMessagePromise⟩

/-- The same ambiguity satisfies the locked-layer shape if the locked layer is
not rigid: its accepted views are precisely the satisfying assignments, and
their messages are the projected variable. -/
def ambiguousOneVarLockedLayerCNFReadoutData :
    LockedLayerCNFReadoutData
      Unit oneVarReadoutPublicVar oneVarReadoutWitness oneVarReadoutLockView Bool where
  toManuscriptCNFReadoutData := ambiguousOneVarManuscriptCNFReadoutData
  lockView := fun _ σ => σ
  lockAccept := fun _ σ => ConcreteCNF.IsSatFormula oneVarTautologyCNF σ
  lockMessage := fun _ σ => oneVarReadout σ
  validWitness_lockAccept := by
    intro _ _ h
    exact h
  witnessMessage_eq_lockMessage := by
    intro _ _ _
    rfl

/-- Without locked-layer rigidity, the locked-layer-shaped interface itself can
still have two accepted lock views with different messages. -/
theorem ambiguousOneVarLockedLayerCNFReadoutData_not_lockedLayerRigidity :
    ¬ ambiguousOneVarLockedLayerCNFReadoutData.LockedLayerRigidity := by
  exact
    LockedLayerCNFReadoutData.not_lockedLayerRigidity_of_distinct_accepted_lockMessages
      ambiguousOneVarLockedLayerCNFReadoutData
      (Y := ())
      trivial
      oneVarTautologyCNF_satisfied_false
      oneVarTautologyCNF_satisfied_true
      oneVarReadout_false_ne_true

/-- The locked-layer-shaped countermodel inherits the same failure of
arbitrary-output SAT-search correctness. -/
theorem ambiguousOneVarLockedLayerCNFReadoutData_not_exists_correctForAll :
    ¬ ∃ msg : Bool,
      CorrectForAllSatSearchOutputs
        (ConcreteCNF.IsSatFormula
          (ambiguousOneVarLockedLayerCNFReadoutData.formula ()))
        (ambiguousOneVarLockedLayerCNFReadoutData.projection ()) msg := by
  simpa [ambiguousOneVarLockedLayerCNFReadoutData] using
    ambiguousOneVarManuscriptCNFReadoutData_not_exists_correctForAll

/-- This model satisfies deterministic readout: each Boolean readout state
accepts exactly its own Boolean message.  It still has two accepted states. -/
def ambiguousOneVarDeterministicReadoutLockedLayerData :
    DeterministicReadoutLockedLayerData
      Unit oneVarReadoutPublicVar oneVarReadoutWitness oneVarReadoutLockView
      oneVarReadoutReadState Bool where
  toLockedLayerCNFReadoutData := ambiguousOneVarLockedLayerCNFReadoutData
  readState := fun _ σ => oneVarReadout σ
  readAccept := fun _ state msg => msg = state
  lockAccept_readAccept := by
    intro _ _ _
    rfl
  readAccept_deterministic := by
    intro _ state M M' hM hM'
    exact hM.trans hM'.symm

/-- Deterministic readout alone does not force all accepted locked views into
the same readout state. -/
theorem ambiguousOneVarDeterministicReadoutLockedLayerData_not_acceptedReadStateConstancy :
    ¬ ambiguousOneVarDeterministicReadoutLockedLayerData.AcceptedReadStateConstancy := by
  exact
    DeterministicReadoutLockedLayerData.not_acceptedReadStateConstancy_of_distinct_accepted_readStates
      ambiguousOneVarDeterministicReadoutLockedLayerData
      (Y := ())
      trivial
      oneVarTautologyCNF_satisfied_false
      oneVarTautologyCNF_satisfied_true
      oneVarReadout_false_ne_true

/-- Even with deterministic readout, the nonconstant one-variable model has no
message correct for arbitrary satisfying SAT-search outputs. -/
theorem ambiguousOneVarDeterministicReadoutLockedLayerData_not_exists_correctForAll :
    ¬ ∃ msg : Bool,
      CorrectForAllSatSearchOutputs
        (ConcreteCNF.IsSatFormula
          (ambiguousOneVarDeterministicReadoutLockedLayerData.formula ()))
        (ambiguousOneVarDeterministicReadoutLockedLayerData.projection ()) msg := by
  simpa [ambiguousOneVarDeterministicReadoutLockedLayerData] using
    ambiguousOneVarLockedLayerCNFReadoutData_not_exists_correctForAll

end Mettapedia.Computability.PNP

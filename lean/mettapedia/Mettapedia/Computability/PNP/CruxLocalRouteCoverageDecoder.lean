import Mettapedia.Computability.PNP.PNPv13ManuscriptCNFReadoutCore
import Mettapedia.Computability.PNP.PNPv13ManuscriptCNFReadoutLockedLayer
import Mettapedia.Computability.PNP.PNPv13ManuscriptCNFReadoutDeterministic
import Mettapedia.Computability.PNP.PNPv13ManuscriptCNFReadoutCountermodels

/-!
# PNP local route coverage: decoder repair anchors

CNF readout and short-global-decoder coverage anchors for the local PNP crux
packet.
-/

namespace Mettapedia.Computability.PNP

universe u v w z

/-- The short global decoder repair is covered only in the precise sense that a
concrete CNF countermodel now separates favorable-witness correctness from
arbitrary SAT-search-output correctness.  This does not prove any manuscript
CNF construction ambiguous; it pins the missing readout-constancy theorem that
such a construction must supply. -/
def ShortGlobalDecoderRepairCoverage : Prop :=
  (∀ readout : ConcreteCNF.Assignment (Fin 1) → Bool,
    (∃ msg : Bool,
      CorrectForAllSatSearchOutputs
        (ConcreteCNF.IsSatFormula oneVarTautologyCNF) readout msg) ↔
      SingleMessageReadout
        (ConcreteCNF.IsSatFormula oneVarTautologyCNF) readout) ∧
  (¬ ∃ msg : Bool,
    CorrectForAllSatSearchOutputs
      (ConcreteCNF.IsSatFormula oneVarTautologyCNF) oneVarReadout msg) ∧
    CorrectForSomeSatSearchOutput
      (ConcreteCNF.IsSatFormula oneVarTautologyCNF) oneVarReadout false ∧
    CorrectForSomeSatSearchOutput
      (ConcreteCNF.IsSatFormula oneVarTautologyCNF) oneVarReadout true

@[simp] theorem shortGlobalDecoderRepairCoverage :
    ShortGlobalDecoderRepairCoverage := by
  exact
    ⟨by
      intro readout
      exact
        cnf_exists_correctForAllSatSearchOutputs_iff_singleMessageReadout_of_satisfying_assignment
          (formula := oneVarTautologyCNF) (readout := readout)
          oneVarTautologyCNF_satisfied_false,
      oneVarTautologyCNF_not_exists_correctForAllSatSearchOutputs,
      oneVarTautologyCNF_correctForSomeSatSearchOutput_false_and_true.1,
      oneVarTautologyCNF_correctForSomeSatSearchOutput_false_and_true.2⟩

/-- Route-coverage anchor: under the natural CNF extraction-completeness and
supported-satisfiability directions, the manuscript-shaped arbitrary-output
SAT-search repair is exactly the semantic single-message promise. -/
theorem shortGlobalDecoderCoverage_anchor_supported_sat_search_equiv_singleMessagePromise
    {Public : Type u} {Var : Public → Type v}
    {Witness : Public → Type w} {Message : Type z}
    (D : ManuscriptCNFReadoutData Public Var Witness Message)
    (hsat : D.SupportedCNFSatisfiable)
    (hcomplete : D.CNFExtractionComplete) :
    D.SupportedArbitraryOutputSATSearchCorrect ↔ D.SingleMessagePromise := by
  exact D.supportedArbitraryOutputSATSearchCorrect_iff_singleMessagePromise hsat hcomplete

/-- Route-coverage anchor: extraction completeness is not a cosmetic premise.
There is a one-variable manuscript-shaped CNF whose CNF projection is constant
and therefore supports arbitrary-output SAT-search correctness, while an
unrepresented semantic witness still refutes the semantic single-message
promise. -/
theorem shortGlobalDecoderCoverage_anchor_incomplete_extraction_countermodel :
    unrepresentedOneVarManuscriptCNFReadoutData.SupportedArbitraryOutputSATSearchCorrect ∧
      ¬ unrepresentedOneVarManuscriptCNFReadoutData.SingleMessagePromise ∧
      ¬ unrepresentedOneVarManuscriptCNFReadoutData.CNFExtractionComplete := by
  exact
    ⟨unrepresentedOneVarManuscriptCNFReadoutData_supportedArbitraryOutputSATSearchCorrect,
      unrepresentedOneVarManuscriptCNFReadoutData_not_singleMessagePromise,
      unrepresentedOneVarManuscriptCNFReadoutData_not_cnfExtractionComplete⟩

end Mettapedia.Computability.PNP

import Mettapedia.Computability.PNP.PNPv13CruxLedgerReadoutAmbiguity

/-!
# PNP v13 crux ledger: Boolean readout countermodel

The two-witness Boolean realization shows why bare SAT satisfiability is weaker
than a single-message readout promise.
-/

namespace Mettapedia.Computability.PNP

/-- The smallest finite obstruction: a satisfiable relation with two satisfying
witnesses and identity readout does not have the single-message property. -/
theorem not_singleMessageReadout_bool_true_id :
    ¬ SingleMessageReadout (fun _ : Bool => True) (fun w : Bool => w) := by
  intro h
  have hfalse : (fun _ : Bool => True) false := trivial
  have htrue : (fun _ : Bool => True) true := trivial
  have hread : false = true := h false true hfalse htrue
  cases hread

/-- Equivalently, the finite countermodel has two satisfying outputs with
distinct message readouts. -/
theorem exists_two_satisfying_outputs_with_distinct_readouts_bool_true_id :
    ∃ w₁ w₂ : Bool,
      (fun _ : Bool => True) w₁ ∧
      (fun _ : Bool => True) w₂ ∧
      (fun w : Bool => w) w₁ ≠ (fun w : Bool => w) w₂ := by
  exact ⟨false, true, trivial, trivial, by
    intro h
    cases h⟩

/-- The same two Boolean witnesses can be packaged as two valid SAT-search
outputs with different message readouts. -/
theorem exists_two_satSearchOutputs_with_distinct_readouts_bool_true_id :
    ∃ out₁ out₂ : SatSearchOutput (fun _ : Bool => True),
      (fun w : Bool => w) out₁.witness ≠ (fun w : Bool => w) out₂.witness := by
  exact ⟨⟨false, trivial⟩, ⟨true, trivial⟩, by
    intro h
    cases h⟩

/-- Therefore the fixed-message correctness condition is impossible for the
unconstrained two-witness Boolean realization.  This is the finite formal
obstruction to replacing the v13 single-message promise by bare SAT
satisfiability. -/
theorem not_exists_fixedMessageReadout_bool_true_id :
    ¬ ∃ msg : Bool,
      FixedMessageReadout (fun _ : Bool => True) (fun w : Bool => w) msg := by
  intro h
  cases h with
  | intro msg hmsg =>
      exact not_singleMessageReadout_bool_true_id
        (singleMessageReadout_of_fixedMessageReadout hmsg)

/-- Equivalently, no message is correct for all valid SAT-search outputs in the
unconstrained two-witness Boolean realization. -/
theorem not_exists_correctForAllSatSearchOutputs_bool_true_id :
    ¬ ∃ msg : Bool,
      CorrectForAllSatSearchOutputs
        (fun _ : Bool => True) (fun w : Bool => w) msg := by
  intro h
  rcases h with ⟨msg, hmsg⟩
  exact not_exists_fixedMessageReadout_bool_true_id
    ⟨msg, correctForAllSatSearchOutputs_iff_fixedMessageReadout.mp hmsg⟩

/-- In the Boolean countermodel, selected-output correctness holds for both
messages.  This is why a favorable-witness repair is too weak. -/
theorem bool_true_id_correctForSomeSatSearchOutput_false_and_true :
    CorrectForSomeSatSearchOutput
        (fun _ : Bool => True) (fun w : Bool => w) false ∧
      CorrectForSomeSatSearchOutput
        (fun _ : Bool => True) (fun w : Bool => w) true := by
  exact ⟨⟨⟨false, trivial⟩, rfl⟩, ⟨⟨true, trivial⟩, rfl⟩⟩

/-- The Boolean countermodel has selected-output correctness but no
arbitrary-output correctness. -/
theorem bool_true_id_correctForSomeSatSearchOutput_not_correctForAll :
    (∃ msg : Bool,
      CorrectForSomeSatSearchOutput
        (fun _ : Bool => True) (fun w : Bool => w) msg) ∧
      ¬ ∃ msg : Bool,
        CorrectForAllSatSearchOutputs
          (fun _ : Bool => True) (fun w : Bool => w) msg := by
  exact
    exists_correctForSomeSatSearchOutput_and_not_exists_correctForAll_of_distinct_satisfying_readouts
      (sat := fun _ : Bool => True) (readout := fun w : Bool => w)
      (w₁ := false) (w₂ := true) trivial trivial (by
        intro h
        cases h)

end Mettapedia.Computability.PNP

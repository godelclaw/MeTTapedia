import Mettapedia.Computability.PNP.PNPv13CruxLedgerReadoutCore

/-!
# PNP v13 crux ledger: ambiguous SAT readouts

Two satisfying witnesses with distinct readouts separate selected-output
correctness from the arbitrary-output contract needed by SAT search.
-/

namespace Mettapedia.Computability.PNP

universe u v

/-- If two satisfying witnesses have different readouts, selected-output
correctness certifies two incompatible messages. -/
theorem exists_two_messages_correctForSomeSatSearchOutput_of_distinct_satisfying_readouts
    {Witness : Type u} {Message : Type v}
    {sat : Witness → Prop} {readout : Witness → Message}
    {w₁ w₂ : Witness}
    (hw₁ : sat w₁) (hw₂ : sat w₂)
    (hdiff : readout w₁ ≠ readout w₂) :
    ∃ msg₁ msg₂ : Message,
      msg₁ ≠ msg₂ ∧
        CorrectForSomeSatSearchOutput sat readout msg₁ ∧
        CorrectForSomeSatSearchOutput sat readout msg₂ := by
  exact
    ⟨readout w₁, readout w₂, hdiff,
      correctForSomeSatSearchOutput_of_satisfying_witness hw₁,
      correctForSomeSatSearchOutput_of_satisfying_witness hw₂⟩

/-- Distinct satisfying readouts separate the weak selected-output contract from
the strong arbitrary-output contract. -/
theorem exists_correctForSomeSatSearchOutput_and_not_exists_correctForAll_of_distinct_satisfying_readouts
    {Witness : Type u} {Message : Type v}
    {sat : Witness → Prop} {readout : Witness → Message}
    {w₁ w₂ : Witness}
    (hw₁ : sat w₁) (hw₂ : sat w₂)
    (hdiff : readout w₁ ≠ readout w₂) :
    (∃ msg : Message, CorrectForSomeSatSearchOutput sat readout msg) ∧
      ¬ ∃ msg : Message, CorrectForAllSatSearchOutputs sat readout msg := by
  exact
    ⟨⟨readout w₁, correctForSomeSatSearchOutput_of_satisfying_witness hw₁⟩,
      by
        intro h
        rcases h with ⟨msg, hmsg⟩
        have hfixed :
            FixedMessageReadout sat readout msg :=
          correctForAllSatSearchOutputs_iff_fixedMessageReadout.mp hmsg
        exact hdiff ((hfixed w₁ hw₁).trans (hfixed w₂ hw₂).symm)⟩

/-- Any claimed correctness theorem for all SAT-search outputs immediately
forces readout constancy across satisfying witnesses. -/
theorem singleMessageReadout_of_correctForAllSatSearchOutputs
    {Witness : Type u} {Message : Type v}
    {sat : Witness → Prop} {readout : Witness → Message}
    {msg : Message}
    (h : CorrectForAllSatSearchOutputs sat readout msg) :
    SingleMessageReadout sat readout := by
  exact singleMessageReadout_of_fixedMessageReadout
    (correctForAllSatSearchOutputs_iff_fixedMessageReadout.mp h)

/-- In the satisfiable case, correctness for all SAT-search outputs at the
message read from one satisfying witness is equivalent to readout constancy. -/
theorem correctForAllSatSearchOutputs_iff_singleMessageReadout_of_witness
    {Witness : Type u} {Message : Type v}
    {sat : Witness → Prop} {readout : Witness → Message}
    {w₀ : Witness} (hw₀ : sat w₀) :
    CorrectForAllSatSearchOutputs sat readout (readout w₀) ↔
      SingleMessageReadout sat readout := by
  constructor
  · intro h
    exact singleMessageReadout_of_correctForAllSatSearchOutputs h
  · intro h
    exact correctForAllSatSearchOutputs_iff_fixedMessageReadout.mpr
      (fixedMessageReadout_of_singleMessageReadout hw₀ h)

/-- In the satisfiable case, the existence of any message correct for every
valid SAT-search output is equivalent to single-message readout constancy. -/
theorem exists_correctForAllSatSearchOutputs_iff_singleMessageReadout_of_witness
    {Witness : Type u} {Message : Type v}
    {sat : Witness → Prop} {readout : Witness → Message}
    {w₀ : Witness} (hw₀ : sat w₀) :
    (∃ msg : Message, CorrectForAllSatSearchOutputs sat readout msg) ↔
      SingleMessageReadout sat readout := by
  constructor
  · intro h
    rcases h with ⟨msg, hmsg⟩
    exact singleMessageReadout_of_correctForAllSatSearchOutputs hmsg
  · intro h
    exact
      ⟨readout w₀,
        (correctForAllSatSearchOutputs_iff_singleMessageReadout_of_witness
          hw₀).mpr h⟩

/-- Two satisfying witnesses with different readouts are a generic obstruction
to the single-message property. -/
theorem not_singleMessageReadout_of_distinct_satisfying_readouts
    {Witness : Type u} {Message : Type v}
    {sat : Witness → Prop} {readout : Witness → Message}
    {w₁ w₂ : Witness}
    (hw₁ : sat w₁) (hw₂ : sat w₂)
    (hdiff : readout w₁ ≠ readout w₂) :
    ¬ SingleMessageReadout sat readout := by
  intro h
  exact hdiff (h w₁ w₂ hw₁ hw₂)

/-- The same ambiguity packaged at the operational SAT-search-output layer. -/
theorem exists_two_satSearchOutputs_with_distinct_readouts_of_distinct_satisfying_readouts
    {Witness : Type u} {Message : Type v}
    {sat : Witness → Prop} {readout : Witness → Message}
    {w₁ w₂ : Witness}
    (hw₁ : sat w₁) (hw₂ : sat w₂)
    (hdiff : readout w₁ ≠ readout w₂) :
    ∃ out₁ out₂ : SatSearchOutput sat,
      readout out₁.witness ≠ readout out₂.witness := by
  exact ⟨⟨w₁, hw₁⟩, ⟨w₂, hw₂⟩, hdiff⟩

/-- If a satisfiable realization has two satisfying witnesses with different
readouts, no fixed message can be correct for all satisfying witnesses. -/
theorem not_exists_fixedMessageReadout_of_distinct_satisfying_readouts
    {Witness : Type u} {Message : Type v}
    {sat : Witness → Prop} {readout : Witness → Message}
    {w₁ w₂ : Witness}
    (hw₁ : sat w₁) (hw₂ : sat w₂)
    (hdiff : readout w₁ ≠ readout w₂) :
    ¬ ∃ msg : Message, FixedMessageReadout sat readout msg := by
  intro h
  rcases h with ⟨msg, hmsg⟩
  exact
    not_singleMessageReadout_of_distinct_satisfying_readouts hw₁ hw₂ hdiff
      (singleMessageReadout_of_fixedMessageReadout hmsg)

/-- Therefore any ambiguous satisfiable realization blocks every decoder whose
correctness must hold for all valid SAT-search outputs. -/
theorem not_exists_correctForAllSatSearchOutputs_of_distinct_satisfying_readouts
    {Witness : Type u} {Message : Type v}
    {sat : Witness → Prop} {readout : Witness → Message}
    {w₁ w₂ : Witness}
    (hw₁ : sat w₁) (hw₂ : sat w₂)
    (hdiff : readout w₁ ≠ readout w₂) :
    ¬ ∃ msg : Message, CorrectForAllSatSearchOutputs sat readout msg := by
  intro h
  rcases h with ⟨msg, hmsg⟩
  exact
    not_exists_fixedMessageReadout_of_distinct_satisfying_readouts
      hw₁ hw₂ hdiff
      ⟨msg, correctForAllSatSearchOutputs_iff_fixedMessageReadout.mp hmsg⟩

end Mettapedia.Computability.PNP

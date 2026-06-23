/-!
# PNP v13 crux ledger: SAT-search readout interfaces

The SAT-search contract may return any satisfying witness. Correctness for all
valid SAT-search outputs is therefore the same obligation as fixed-message
readout, and in the satisfiable case it is equivalent to single-message
readout constancy.
-/

namespace Mettapedia.Computability.PNP

universe u v

/-- A SAT-realization readout has the single-message property when every
satisfying witness projects to the same message. -/
def SingleMessageReadout {Witness : Type u} {Message : Type v}
    (sat : Witness → Prop) (readout : Witness → Message) : Prop :=
  ∀ w₁ w₂, sat w₁ → sat w₂ → readout w₁ = readout w₂

/-- A stronger pointed form: every satisfying witness decodes to one fixed
message.  This is the shape needed by an arbitrary SAT-search upper-bound
decoder. -/
def FixedMessageReadout {Witness : Type u} {Message : Type v}
    (sat : Witness → Prop) (readout : Witness → Message) (msg : Message) : Prop :=
  ∀ w, sat w → readout w = msg

/-- The output contract of a SAT-search subroutine on one satisfiable
realization: it may return any witness, but must return a satisfying one. -/
structure SatSearchOutput {Witness : Type u} (sat : Witness → Prop) where
  witness : Witness
  isSat : sat witness

/-- A decoder is correct for all valid SAT-search outputs when every satisfying
output witness decodes to the claimed message. -/
def CorrectForAllSatSearchOutputs {Witness : Type u} {Message : Type v}
    (sat : Witness → Prop) (readout : Witness → Message) (msg : Message) : Prop :=
  ∀ out : SatSearchOutput sat, readout out.witness = msg

/-- A deliberately weak selected-output contract: there exists some valid
SAT-search output whose readout is the claimed message.  This models a repair
that silently relies on choosing a favorable satisfying witness. -/
def CorrectForSomeSatSearchOutput {Witness : Type u} {Message : Type v}
    (sat : Witness → Prop) (readout : Witness → Message) (msg : Message) : Prop :=
  ∃ out : SatSearchOutput sat, readout out.witness = msg

/-- Correctness for one fixed message and arbitrary satisfying SAT-search output
implies readout constancy across all satisfying witnesses. -/
theorem singleMessageReadout_of_fixedMessageReadout
    {Witness : Type u} {Message : Type v}
    {sat : Witness → Prop} {readout : Witness → Message}
    {msg : Message}
    (h : FixedMessageReadout sat readout msg) :
    SingleMessageReadout sat readout := by
  intro w₁ w₂ hw₁ hw₂
  exact (h w₁ hw₁).trans (h w₂ hw₂).symm

/-- Once one satisfying witness exists, readout constancy supplies a pointed
message to which every satisfying witness decodes. -/
theorem fixedMessageReadout_of_singleMessageReadout
    {Witness : Type u} {Message : Type v}
    {sat : Witness → Prop} {readout : Witness → Message}
    {w₀ : Witness}
    (hw₀ : sat w₀)
    (h : SingleMessageReadout sat readout) :
    FixedMessageReadout sat readout (readout w₀) := by
  intro w hw
  exact (h w w₀ hw hw₀)

/-- Correctness for all possible satisfying SAT-search outputs is exactly the
fixed-message readout obligation.  Thus a proof that uses SAT search cannot
hide behind a particular witness-selection policy. -/
theorem correctForAllSatSearchOutputs_iff_fixedMessageReadout
    {Witness : Type u} {Message : Type v}
    {sat : Witness → Prop} {readout : Witness → Message}
    {msg : Message} :
    CorrectForAllSatSearchOutputs sat readout msg ↔
      FixedMessageReadout sat readout msg := by
  constructor
  · intro h w hw
    exact h ⟨w, hw⟩
  · intro h out
    exact h out.witness out.isSat

/-- Selected-output correctness is only existence of one satisfying witness with
the desired readout.  It is therefore not the theorem needed for arbitrary SAT
search. -/
theorem correctForSomeSatSearchOutput_iff_exists_satisfying_readout
    {Witness : Type u} {Message : Type v}
    {sat : Witness → Prop} {readout : Witness → Message}
    {msg : Message} :
    CorrectForSomeSatSearchOutput sat readout msg ↔
      ∃ w : Witness, sat w ∧ readout w = msg := by
  constructor
  · intro h
    rcases h with ⟨out, hout⟩
    exact ⟨out.witness, out.isSat, hout⟩
  · intro h
    rcases h with ⟨w, hw, hread⟩
    exact ⟨⟨w, hw⟩, hread⟩

/-- Every satisfying witness is enough to prove selected-output correctness for
its own readout. -/
theorem correctForSomeSatSearchOutput_of_satisfying_witness
    {Witness : Type u} {Message : Type v}
    {sat : Witness → Prop} {readout : Witness → Message}
    {w : Witness} (hw : sat w) :
    CorrectForSomeSatSearchOutput sat readout (readout w) := by
  exact ⟨⟨w, hw⟩, rfl⟩

end Mettapedia.Computability.PNP

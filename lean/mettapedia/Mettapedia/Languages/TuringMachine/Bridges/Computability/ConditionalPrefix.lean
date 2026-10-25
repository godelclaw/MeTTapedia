import Mettapedia.Languages.TuringMachine.PartrecBridge
import Mettapedia.Languages.TuringMachine.NativeTypes
import Mettapedia.Computability.KolmogorovComplexity.EffectiveConditionalPrefixInterpreter
import Mettapedia.Computability.KolmogorovComplexity.PrefixMass

/-!
# Effective conditional prefix machines as authored Turing languages

Each effective conditional prefix machine compiles to a finite deterministic
table, with binary programs and conditions encoded on the work tape. Its
generated halting type has the source's prefix-free program mass. Completed
output mass, including total readouts, has exactly that same total.

The effective trimmed interpreter supplies one table hosting every effective
conditional prefix machine with a fixed compiler prefix and preserved outputs.
A one-way streaming input protocol requires a separate operational model.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.TuringMachine.Bridges.Computability.ConditionalPrefix

open Turing.ToPartrec KolmogorovComplexity
open scoped Classical ENNReal BigOperators

variable (source : ConditionalPrefixFreeMachine)
variable (effective : Partrec₂ fun program condition => Part.ofOption (source.compute program condition))

include effective in
theorem exists_nativeCode : ∃ code : Nat.Partrec.Code, ∀ program condition,
    code.eval (Encodable.encode (program, condition)) =
      Encodable.encode <$> Part.ofOption (source.compute program condition) := by
  unfold Partrec₂ Partrec at effective
  obtain ⟨code, specification⟩ := Nat.Partrec.Code.exists_code.mp effective
  refine ⟨code, fun program condition => ?_⟩
  simpa using congrArg (fun compute => compute (Encodable.encode (program, condition))) specification

noncomputable def nativeCode : Nat.Partrec.Code :=
  Classical.choose (exists_nativeCode source effective)

theorem nativeCode_eval (program condition : BinString) :
    (nativeCode source effective).eval (Encodable.encode (program, condition)) =
      Encodable.encode <$> Part.ofOption (source.compute program condition) :=
  Classical.choose_spec (exists_nativeCode source effective) program condition

noncomputable def programCode : Code := PartrecMachine.compile (nativeCode source effective)

theorem programCode_eval (program condition : BinString) :
    (programCode source effective).eval [Encodable.encode (program, condition)] =
      (fun output => [Encodable.encode output]) <$> Part.ofOption (source.compute program condition) := by
  rw [programCode, PartrecMachine.compile_eval, List.headI_cons, nativeCode_eval]
  simp only [Part.map_eq_map, Part.map_map]
  rfl

noncomputable def machine : Machine := PartrecBridge.machine (programCode source effective)

noncomputable def inputConfiguration (program condition : BinString) : Configuration :=
  PartrecBridge.inputConfiguration (programCode source effective) [Encodable.encode (program, condition)]

theorem deterministic : (machine source effective).Deterministic := PartrecBridge.deterministic _

theorem input_state (program condition : BinString) :
    (inputConfiguration source effective program condition).state = 0 :=
  PartrecBridge.input_state _ _

theorem halts_iff (program condition : BinString) :
    HaltsFrom (machine source effective) (inputConfiguration source effective program condition).term ↔
      source.compute program condition ≠ none := by
  simp only [machine, inputConfiguration, PartrecBridge.halts_iff, programCode_eval]
  cases result : source.compute program condition <;> simp [Part.ofOption]

def HaltingPrograms (condition : BinString) : Set BinString :=
  {program | HaltsFrom (machine source effective) (inputConfiguration source effective program condition).term}

theorem prefix_free (condition : BinString) : PrefixFree (HaltingPrograms source effective condition) := by
  simpa only [HaltingPrograms, halts_iff] using conditionalHaltingPrograms_prefixFree source condition

theorem halting_type_iff (program condition : BinString) :
    Mettapedia.OSLF.Framework.FormulaFixpoint.lfp (haltingTransformer (machine source effective))
      (inputConfiguration source effective program condition).term ↔
      source.compute program condition ≠ none := by
  rw [← haltsFrom_eq_lfp]
  exact halts_iff _ _ _ _

noncomputable def haltingMass (condition : BinString) : ENNReal :=
  prefixProgramMass (HaltingPrograms source effective condition)

theorem haltingMass_le_one (condition : BinString) : haltingMass source effective condition ≤ 1 :=
  prefixProgramMass_le_one _ (prefix_free source effective condition)

/-- Completed output mass agrees with the weight of the actual table's
halting type under its binary program interface. -/
theorem outputMass_total (condition : BinString) :
    (∑' output, prefixOutputMass (source.compute · condition) output) =
      haltingMass source effective condition := by
  simpa only [haltingMass, HaltingPrograms, halts_iff] using
    prefixOutputMass_total (source.compute · condition)

/-- A total output readout preserves the weight of the actual table's halting type. -/
theorem observed_outputMass_total {Observed : Type*} (observe : BinString → Observed)
    (condition : BinString) :
    (∑' output, prefixOutputMass (fun program => (source.compute program condition).map observe) output) =
      haltingMass source effective condition := by
  simpa only [prefixOutputMass_total, ne_eq, Option.map_eq_none_iff] using outputMass_total source effective condition

theorem outputMass_total_le_one (condition : BinString) :
    (∑' output, prefixOutputMass (source.compute · condition) output) ≤ 1 :=
  prefixOutputMass_total_le_one _ (conditionalHaltingPrograms_prefixFree source condition)

/-- A source answer is retained in the terminal table configuration. -/
theorem output_preserved (program condition output : BinString)
    (computed : source.compute program condition = some output) :
    ∃ final, final ∈ _root_.StateTransition.eval (machine source effective).next?
      (inputConfiguration source effective program condition) ∧
      PartrecBridge.Represents (programCode source effective)
        (Turing.PartrecToTM2.halt [Encodable.encode output]) final := by
  exact PartrecBridge.eval_preserved _ _ _ (by simp only [programCode_eval, computed, Part.ofOption]; simp)

/-- Every terminal table run is certified by a returned source string. -/
theorem output_reflected (program condition : BinString) {final : Configuration}
    (computed : final ∈ _root_.StateTransition.eval (machine source effective).next?
      (inputConfiguration source effective program condition)) :
    ∃ output, source.compute program condition = some output ∧
      PartrecBridge.Represents (programCode source effective)
        (Turing.PartrecToTM2.halt [Encodable.encode output]) final := by
  have reflected := PartrecBridge.eval_reflected (programCode source effective) _ computed
  simp only [programCode_eval, Part.map_eq_map, Part.mem_map_iff, Part.mem_ofOption,
    Option.mem_def, ← exists_and_right] at reflected
  rw [exists_comm] at reflected
  simpa only [and_assoc, exists_and_left, exists_eq_left'] using reflected

noncomputable def universalMachine : Machine := machine trimmedIndexedHost trimmedIndexedHost_effective

/-- One fixed table hosts all effective conditional prefix machines, with
one compiler prefix per source machine and the original auxiliary condition. -/
theorem universal_prefix_simulation (other : ConditionalPrefixFreeMachine)
    (otherEffective : Partrec₂ fun program condition => Part.ofOption (other.compute program condition)) :
    ∃ compilerPrefix : BinString, ∀ program condition,
      HaltsFrom universalMachine
        (inputConfiguration trimmedIndexedHost trimmedIndexedHost_effective (compilerPrefix ++ program) condition).term ↔
      HaltsFrom (machine other otherEffective) (inputConfiguration other otherEffective program condition).term := by
  obtain ⟨simulation⟩ := trimmedIndexedHost_simulates_effective other otherEffective
  refine ⟨simulation.compilerPrefix, fun program condition => ?_⟩
  rw [universalMachine, halts_iff, halts_iff, simulation.compute_eq]

/-- Uniform interpretation preserves returned binary strings, with the
same fixed program prefix for every program and auxiliary condition. -/
theorem universal_prefix_outputs (other : ConditionalPrefixFreeMachine)
    (otherEffective : Partrec₂ fun program condition => Part.ofOption (other.compute program condition)) :
    ∃ compilerPrefix : BinString, ∀ program condition output,
      other.compute program condition = some output →
      ∃ final, final ∈ _root_.StateTransition.eval universalMachine.next?
        (inputConfiguration trimmedIndexedHost trimmedIndexedHost_effective
          (compilerPrefix ++ program) condition) ∧
        PartrecBridge.Represents (programCode trimmedIndexedHost trimmedIndexedHost_effective)
          (Turing.PartrecToTM2.halt [Encodable.encode output]) final := by
  obtain ⟨simulation⟩ := trimmedIndexedHost_simulates_effective other otherEffective
  refine ⟨simulation.compilerPrefix, fun program condition output computed => ?_⟩
  apply output_preserved
  rw [simulation.compute_eq, computed]

end Mettapedia.Languages.TuringMachine.Bridges.Computability.ConditionalPrefix

import Mettapedia.OSLF.Syntax.RhoScopedReactionReadout

/-!
# Channel agreement from an actual original communication

A process consisting of one output and one input has an original core
reaction only when their complete name classes agree. The proof reads the
full original root inventory, including the bound continuation, rather than
assuming a channel-matching decision procedure.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoScopedChannelSeparation

open RhoSchema RhoQuotationClassFibres RhoScopedParallelEvents
open RhoScopedReactionReadout RhoScopedConstructorInventory RhoScopedParallelInventory
open RhoIntrinsicCanonicalBag RhoIntrinsicReadback MeTTaIL.Syntax

theorem output_not_input {context : Ctx sig} (outArguments : Output context)
    (inArguments : Input context) : outputPattern outArguments ≠ inputPattern inArguments := by
  intro same
  have tag := congrArg (fun pattern : Pattern => match pattern with
    | .apply name _ => name
    | _ => "") same
  change ("POutput" : String) = "PInput" at tag
  exact (by decide : ("POutput" : String) ≠ "PInput") tag

theorem channels_agree_of_original_reaction {context : Ctx sig}
    (outputName inputName : Name context) (payload : Process context)
    (continuation : Process (Srt.nm :: context)) {result : Process context}
    (event : RhoScopedParallelEvents.Step (rules := sourceRules) (admitted := core)
      (join (outputClass outputName payload) (inputClass inputName continuation)) result) :
    outputName = inputName := by
  obtain ⟨root, surrounding, sourceReadout, _targetReadout⟩ :=
    (step_iff_root_surrounding _ _).mp event
  have included : read root.source ≤
      read (join (outputClass outputName payload) (inputClass inputName continuation)) := by
    rw [sourceReadout, read_join]
    exact Multiset.le_add_right _ _
  have patternInclusion := components_le included
  rw [← rootReading_source root] at patternInclusion
  cases reading : rootReading root with
  | communication channel sent body =>
      rw [reading] at patternInclusion
      change components (join (outputClass channel sent) (inputClass channel body)) ≤ _ at patternInclusion
      rw [join_components, output_components, input_components, join_components,
        output_components, input_components] at patternInclusion
      have foundOutput : outputPattern (channel, sent) ∈
          ({outputPattern (outputName, payload)} + {inputPattern (inputName, continuation)}) :=
        Multiset.mem_of_le patternInclusion (by simp)
      have foundInput : inputPattern (channel, body) ∈
          ({outputPattern (outputName, payload)} + {inputPattern (inputName, continuation)}) :=
        Multiset.mem_of_le patternInclusion (by simp)
      simp only [Multiset.mem_add, Multiset.mem_singleton] at foundOutput foundInput
      have outputRead : channel = outputName := by
        rcases foundOutput with actual | impossible
        · exact congrArg Prod.fst (outputPattern_injective context actual)
        · exact False.elim (output_not_input _ _ impossible)
      have inputRead : channel = inputName := by
        rcases foundInput with impossible | actual
        · exact False.elim (output_not_input _ _ impossible.symm)
        · exact congrArg Prod.fst (inputPattern_injective context actual)
      exact outputRead.symm.trans inputRead
  | reflection value =>
      have origin := rootReading_rule root
      rw [reading] at origin
      have excluded := root.1.property
      rw [← origin] at excluded
      exact False.elim excluded

end Mettapedia.OSLF.Binding.RhoScopedChannelSeparation

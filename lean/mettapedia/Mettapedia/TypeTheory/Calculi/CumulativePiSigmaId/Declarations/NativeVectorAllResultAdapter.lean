import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FunctionArgumentAdapters
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAllOriginalInputUniversesChecking

/-!
# A typed mixed-argument adapter using the native Vector result programme

The outer method has three arguments: a direct result, a complete All bundle,
and another direct result. The generic adapter changes only the middle
argument to the ordered vector of results. Its projection is the existing
declared programme on the original lower-universe input, with types as its
higher-universe results. Primitive formation and projection evidence is
checked independently of the generated adapter.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAllResultAdapter

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation FormationSensitive FunctionArgumentAdapters
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open NativeNaturalVectorFamilies RussellTarski TypedEquality.Normalization
open NativeVectorAll.CanonicalAdequacy

open NativeVectorAll.ResultView

abbrev rules := OriginalInputUniverses.ClosedResultDefinition.rules
abbrev decoder := OriginalInputUniverses.ClosedResultDefinition.decoder
abbrev choices := OriginalInputUniverses.ClosedResultDefinition.choices

local instance : DecidableRel rules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred rules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (rules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel rules.cumulative :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.cumulative h u))
local instance : DecidableRel rules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

def resultType : Tower.Tm 0 := sortTm Tower.zero
def inputType : Tower.Tm 0 :=
  substLevelsTm OriginalInputUniverses.closedLevels
    (NativeVectorAll.Universes.allType natTm (NativeVectorAll.ResultView.predicate resultType)
      (numeral 2) OriginalInputUniverses.ClosedResultDefinition.source)
def projection : Tower.Tm 0 :=
  appSpine (.const OriginalInputUniverses.ClosedResultDefinition.selfName) [natTm, resultType, numeral 2, OriginalInputUniverses.ClosedResultDefinition.source]

def directSlot : Slot Tower.Head 0 := ⟨resultType, resultType, .lam (.var 0)⟩
def nestedSlot : Slot Tower.Head 0 := ⟨inputType, OriginalInputUniverses.ClosedResultDefinition.outputType, projection⟩
def slots : List (Slot Tower.Head 0) := [directSlot, nestedSlot, directSlot]

def checked (term type : Tower.Tm 0) : Bool :=
  (FormationSensitiveElaboration.elaborate rules decoder choices 256 .nil term type).isSome

theorem checked_sound {term type : Tower.Tm 0} (accepted : checked term type = true) :
    Judgment rules .nil term type := by
  obtain ⟨submission, produced⟩ := Option.isSome_iff_exists.mp accepted
  exact FormationSensitiveElaboration.elaborate_sound rules decoder choices 256 .nil
    term type submission produced

set_option maxRecDepth 8192 in
theorem input_formed : checked inputType (sortTm (.succ Tower.zero)) = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem output_formed : checked OriginalInputUniverses.ClosedResultDefinition.outputType (sortTm (.succ Tower.zero)) = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem projection_checked : checked projection (arrow inputType OriginalInputUniverses.ClosedResultDefinition.outputType) = true := by decide +kernel

theorem result_formed : Typing rules .nil resultType (sortTm (.succ Tower.zero)) :=
  .headType (.sort _)

theorem method_universe : rules.isUniverse (.sort (.succ Tower.zero)) := .sort _

theorem product_closure : ∃ result,
    rules.join (.sort (.succ Tower.zero)) (.sort (.succ Tower.zero)) result ∧
      (result = .sort (.succ Tower.zero) ∨ rules.cumulative result (.sort (.succ Tower.zero))) :=
  ⟨.sort (.max (.succ Tower.zero) (.succ Tower.zero)), .sorts _ _,
    Or.inr (fun _ => max_le le_rfl le_rfl)⟩

theorem direct_typed : Typing rules .nil directSlot.projection
    (arrow directSlot.input directSlot.output) := by
  apply Typing.lamIntro
    (piForm_bounded method_universe product_closure result_formed result_formed.weaken)
    method_universe
  exact .var 0

theorem slots_typed : SlotsTyped rules .nil (.sort (.succ Tower.zero)) slots := by
  intro slot present
  simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl
  · exact ⟨result_formed, result_formed, direct_typed⟩
  · exact ⟨(checked_sound input_formed).typing, (checked_sound output_formed).typing,
      (checked_sound projection_checked).typing⟩
  · exact ⟨result_formed, result_formed, direct_typed⟩

def sourceType : Tower.Tm 0 := curriedType (slots.map Slot.output) resultType
def targetType : Tower.Tm 0 := curriedType (slots.map Slot.input) resultType
def context : Tower.Ctx 1 := .snoc .nil sourceType
def adapter : Tower.Tm 1 := adapt (slots.map Slot.weaken) (.var 0)

theorem context_formed : ContextFormation rules context := by
  refine .snoc .nil ?_ method_universe
  exact curriedType_formed method_universe product_closure
    (slots.map Slot.output) resultType
    (by
      intro type member
      obtain ⟨slot, present, rfl⟩ := List.mem_map.mp member
      exact (slots_typed slot present).2.1) result_formed

theorem adapter_typed : Judgment rules context adapter (rename wk targetType) := by
  have source : Judgment rules context (.var 0)
      (curriedType ((slots.map Slot.weaken).map Slot.output) (rename wk resultType)) := by
    refine ⟨context_formed, ?_⟩
    simpa only [context, sourceType, Ctx.lookup_snoc_zero, curriedType_rename,
      List.map_map, Slot.weaken, Slot.map, Function.comp_def] using
      (Typing.var (R := rules) (Γ := context) 0)
  have derived := adapt_judgment method_universe product_closure
    (slots.map Slot.weaken) (slots_typed.weaken sourceType) result_formed.weaken source
  simpa only [context, adapter, targetType, curriedType_rename, List.map_map, Slot.weaken,
    Slot.map, Function.comp_def] using derived

def arguments : List (Tower.Tm 1) :=
  [liftClosed natTm, liftClosed OriginalInputUniverses.ClosedResultDefinition.witnesses, liftClosed NativeVectorAll.unitType]
def application : Tower.Tm 1 := arguments.foldl Tm.app adapter
def projectedApplication : Tower.Tm 1 :=
  ((slots.map Slot.weaken).zip arguments |>.map
    (fun pair => Tm.app pair.1.projection pair.2)).foldl Tm.app (.var 0)

theorem adapter_beta : TelescopeAbstraction.BetaSteps application projectedApplication :=
  adapt_apply (slots.map Slot.weaken) arguments (.var 0) rfl

def outputApplication : Tower.Tm 1 :=
  appSpine (.var 0) [liftClosed natTm, liftClosed OriginalInputUniverses.ClosedResultDefinition.output, liftClosed NativeVectorAll.unitType]
def swappedApplication : Tower.Tm 1 :=
  appSpine (.var 0) [liftClosed natTm, liftClosed OriginalInputUniverses.ClosedResultDefinition.swapped, liftClosed NativeVectorAll.unitType]
def resultCode := choices.conversion 256 application outputApplication
def resultAccepted : Bool := resultCode.any
  (fun code => code.check rules.headEq decoder.decode application outputApplication)
def swappedAccepted : Bool := resultCode.any
  (fun code => code.check rules.headEq decoder.decode application swappedApplication)

set_option maxRecDepth 8192 in
theorem results_in_order : resultAccepted = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem swapped_results_refused : swappedAccepted = false := by decide +kernel

theorem results_convertible : Conv rules.headEq application outputApplication rules.computation := by
  have accepted := results_in_order
  unfold resultAccepted at accepted
  cases codeFound : resultCode with
  | none => simp only [codeFound, Option.any_none, Bool.false_eq_true] at accepted
  | some code =>
      simp only [codeFound, Option.any_some] at accepted
      exact StructuralConversionCode.Code.check_sound decoder accepted

set_option maxRecDepth 8192 in
theorem raw_children_refused : checked OriginalInputUniverses.ClosedResultDefinition.source inputType = false := by decide +kernel

#print axioms projection_checked
#print axioms adapter_typed
#print axioms adapter_beta
#print axioms results_in_order
#print axioms results_convertible
#print axioms swapped_results_refused
#print axioms raw_children_refused

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAllResultAdapter

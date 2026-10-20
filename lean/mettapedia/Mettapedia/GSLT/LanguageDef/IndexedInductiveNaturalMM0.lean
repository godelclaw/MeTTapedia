import Mettapedia.GSLT.LanguageDef.IndexedInductiveNaturalMegalodon
import Mettapedia.Languages.MM0.NaturalFactsMeaning

/-!
# Native MM0 natural-law readings on the authored natural carrier

The comparison uses the actual admitted source carrier and its existing
recursor. It retains bare zero, the native method's result-first order and
the finite graph's actual output. Native checking is a separately qualified
boundary; truth in this interpretation does not supply a proof exporter,
a logical theory retraction or linked-C refinement.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedInductiveNaturalMM0

open Mettapedia.Logic.HOL
open IndexedInductiveNatVec
open Mettapedia.Languages.MM0
open Mettapedia.Languages.HOLLight.NaturalFacts (Fact)
open Mettapedia.Languages.Megalodon.NaturalRecursion (Graph)

abbrev Number := ULift.{1} Natural.Carrier

/-- The constructed source model validates each native closed reading.
The proof uses the independent formula comparison and actual source laws. -/
theorem all_models (result : Type 1) (fact : Fact) :
    (IndexedInductiveNaturalHOL.NativeFacts.model result).models
      (NaturalFactsMeaning.formula fact) :=
  (NaturalFactsMeaning.shared_fact_meaning IndexedInductiveNaturalHOL.peanoStructure.zero
    IndexedInductiveNaturalHOL.peanoStructure.succ result fact).mpr
      (IndexedInductiveNaturalHOL.NativeFacts.all_models result fact)

/-- The exact native alias-bearing infinity formula holds in the constructed
definition reduct of the authored model. No new source infinity assumption is
introduced; the existing source successor supplies the infinite injection. -/
theorem native_infinity_model (result : Type 1) :
    ((IndexedInductiveNaturalHOL.NativeFacts.model result).constantSubstitutionReduct
      NaturalFactsMeaning.definitions).models NaturalFactsMeaning.nativeInfinity :=
  (NaturalFactsMeaning.infinity_definitions_meaning _).mpr (all_models result .infinity)

/-- The source induction law supplies the actual open native conclusion,
with its initial and successor hypotheses retained as distinct evidence. -/
theorem induction_rule (result : Type 1)
    (valuation : (Mettapedia.Logic.HOL.NaturalFacts.model IndexedInductiveNaturalHOL.peanoStructure.zero
      IndexedInductiveNaturalHOL.peanoStructure.succ result).Valuation NaturalFactsMeaning.inductionContext)
    (initial : ((IndexedInductiveNaturalHOL.NativeFacts.model result).denote
      NaturalFactsMeaning.inductionInitial valuation).down)
    (step : ((IndexedInductiveNaturalHOL.NativeFacts.model result).denote
      NaturalFactsMeaning.inductionStep valuation).down) :
    ((IndexedInductiveNaturalHOL.NativeFacts.model result).denote
      NaturalFactsMeaning.inductionConclusion valuation).down :=
  NaturalFactsMeaning.induction_rule _ _ result (all_models result .induction)
    valuation initial step

/-- Native free arguments retain both the result and the natural index. -/
def graphArguments (result : Type 1) (start : result) (method : result → Number → result)
    (number : Number) (value : result) :
    (Mettapedia.Logic.HOL.NaturalFacts.model IndexedInductiveNaturalHOL.peanoStructure.zero
      IndexedInductiveNaturalHOL.peanoStructure.succ result).Valuation NaturalFactsMeaning.graphContext
  | _, .vz => value
  | _, .vs .vz => number
  | _, .vs (.vs .vz) => method
  | _, .vs (.vs (.vs .vz)) => start

/-- The native graph contains exactly the source recursor value. The ULift
comparison changes the index representation and transposes the method once. -/
theorem source_graph_iff (result : Type 1) (start : result)
    (method : result → Number → result) (number : Natural.Carrier) (value : result) :
    ((IndexedInductiveNaturalHOL.NativeFacts.model result).denote
      NaturalFactsMeaning.graphDefinition
        (graphArguments result start method (ULift.up number) value)).down ↔
      value = IndexedInductiveNaturalHOL.recurse start
        (fun previous prior => method prior (ULift.up previous)) number := by
  unfold IndexedInductiveNaturalHOL.NativeFacts.model
  rw [NaturalFactsMeaning.graph_meaning]
  constructor
  · intro graph
    have original := graph.mapIndex ULift.down Natural.zero Natural.succ
      (fun previous prior => method prior (ULift.up previous)) rfl
      (fun _ => rfl) (fun _ _ => rfl)
    exact (IndexedInductiveNaturalMegalodon.source_graph_iff start
      (fun previous prior => method prior (ULift.up previous)) number value).mp original
  · intro same
    have original := (IndexedInductiveNaturalMegalodon.source_graph_iff start
      (fun previous prior => method prior (ULift.up previous)) number value).mpr same
    exact original.mapIndex ULift.up IndexedInductiveNaturalHOL.peanoStructure.zero
      IndexedInductiveNaturalHOL.peanoStructure.succ (fun previous prior => method prior previous)
      rfl (fun _ => rfl) (fun _ _ => rfl)

/-- A genuine recursive output satisfies the exact typed native graph. -/
theorem source_graph (result : Type 1) (start : result)
    (method : result → Number → result) (number : Natural.Carrier) :
    ((IndexedInductiveNaturalHOL.NativeFacts.model result).denote
      NaturalFactsMeaning.graphDefinition
        (graphArguments result start method (ULift.up number)
          (IndexedInductiveNaturalHOL.recurse start
            (fun previous prior => method prior (ULift.up previous)) number))).down :=
  (source_graph_iff result start method number _).mpr rfl

/-- Interpret selection at the exact intrinsically typed native graph
predicate. Every selector satisfying its stated law agrees with the existing
source recursor; choice is kept as an explicit hypothesis on this edge. -/
theorem source_selector_agrees (result : Type 1) (start : result)
    (method : result → Number → result)
    (choose : (result → Prop) → result)
    (selects : ∀ predicate : result → Prop,
      (∃ value, predicate value) → predicate (choose predicate))
    (number : Natural.Carrier) :
    choose (fun value => ((IndexedInductiveNaturalHOL.NativeFacts.model result).denote
      NaturalFactsMeaning.graphDefinition
        (graphArguments result start method (ULift.up number) value)).down) =
      IndexedInductiveNaturalHOL.recurse start
        (fun previous prior => method prior (ULift.up previous)) number := by
  let predicate : result → Prop := fun value =>
    ((IndexedInductiveNaturalHOL.NativeFacts.model result).denote
      NaturalFactsMeaning.graphDefinition
        (graphArguments result start method (ULift.up number) value)).down
  have inhabited : ∃ value, predicate value := ⟨_, source_graph result start method number⟩
  exact (source_graph_iff result start method number _).mp (selects predicate inhabited)

/-- Returning zero after a successor, with a step that increments its result,
fails this graph on the actual source carrier. Both indices and result are
well formed; the rejected value is the defect. -/
theorem wrong_successor_output_refused :
    ¬ ((IndexedInductiveNaturalHOL.NativeFacts.model (ULift.{1} Nat)).denote
      NaturalFactsMeaning.graphDefinition
        (graphArguments (ULift.{1} Nat) (ULift.up 0)
          (fun prior _ => ULift.up (prior.down + 1))
          (ULift.up (Natural.succ Natural.zero)) (ULift.up 0))).down := by
  rw [source_graph_iff]
  rw [IndexedInductiveNaturalHOL.recurse_succ, IndexedInductiveNaturalHOL.recurse_zero]
  intro same
  exact Nat.zero_ne_one (congrArg ULift.down same)

/-- Nonconstant output supplies a positive source instance at the same index. -/
theorem successor_output_accepted :
    ((IndexedInductiveNaturalHOL.NativeFacts.model (ULift.{1} Nat)).denote
      NaturalFactsMeaning.graphDefinition
        (graphArguments (ULift.{1} Nat) (ULift.up 0)
          (fun prior _ => ULift.up (prior.down + 1))
          (ULift.up (Natural.succ Natural.zero)) (ULift.up 1))).down := by
  rw [source_graph_iff]
  rw [IndexedInductiveNaturalHOL.recurse_succ, IndexedInductiveNaturalHOL.recurse_zero]

end Mettapedia.GSLT.LanguageDef.IndexedInductiveNaturalMM0

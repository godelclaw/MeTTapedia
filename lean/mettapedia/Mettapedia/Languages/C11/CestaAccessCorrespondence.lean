import Mettapedia.Languages.C11.CestaAccessExecution

/-!
# Constructive realization of independent identifier-access histories

Finite storage lists retain shadowed records. The representation into resource
heaps is therefore many to one. A source history cannot require execution to
return an arbitrarily chosen list representative of its endpoint. Instead,
realization constructs the returned configuration and proves its heap,
catalog, bindings, pending requests and occurrence counter correspond exactly.
The ordered request/response observations also agree.

The result concerns the sorted whole-object integer access profile. It does
not establish declaration elaboration, full C expression execution, native
compiler refinement, or host publication authority.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.CestaAccessCorrespondence

open ObjectAccessMemory CestaAccessExecution
open Mettapedia.GSLT.Parsing.SortedCanonicalSExprCodec
open Mettapedia.GSLT.Distinction.ProductiveBlocks

def Corresponds {layout : Layout} (actual expected : Configuration layout) : Prop :=
  represent actual.memory = represent expected.memory ∧
    actual.environment = expected.environment ∧ actual.pending = expected.pending ∧ actual.ordinal = expected.ordinal

theorem Corresponds.refl {layout : Layout} (configuration : Configuration layout) :
    Corresponds configuration configuration := ⟨rfl, rfl, rfl, rfl⟩

theorem Corresponds.symm {layout : Layout} {first second : Configuration layout}
    (same : Corresponds first second) : Corresponds second first :=
  ⟨same.1.symm, same.2.1.symm, same.2.2.1.symm, same.2.2.2.symm⟩

theorem Corresponds.trans {layout : Layout} {first second third : Configuration layout}
    (left : Corresponds first second) (right : Corresponds second third) : Corresponds first third :=
  ⟨left.1.trans right.1, left.2.1.trans right.2.1,
    left.2.2.1.trans right.2.2.1, left.2.2.2.trans right.2.2.2⟩

structure Observation (layout : Layout) where
  ordinal : Nat
  request : Request layout
  response : Response
  deriving DecidableEq, Repr

def observe {layout : Layout} (receipt : Receipt layout) : Observation layout :=
  ⟨receipt.before.ordinal, receipt.request, receipt.response⟩

theorem realize_advance (schema : Schema) (codecProfile : Notation) (sort : String) (layout : Layout)
    (before after actual : Configuration layout) (request : Request layout) (response : Response)
    (advanced : Advance schema codecProfile sort layout before request response after)
    (same : Corresponds actual before) :
    ∃ saved, (machine schema codecProfile sort layout).step actual =
      some (.publish [⟨actual, request, response, saved⟩] saved) ∧ Corresponds saved after := by
  cases advanced with
  | consume memory savedMemory environment request response rest ordinal reduced =>
      obtain ⟨heap, bindings, pending, counter⟩ := same
      have actualReduction : Reduction schema codecProfile sort layout actual.environment
          (represent actual.memory) request response (represent savedMemory) := by
        rw [heap, bindings]
        exact reduced
      obtain ⟨saved, executed, endpoint⟩ := execute_complete schema codecProfile sort layout
        actual.memory actual.environment request response (represent savedMemory) actualReduction
      let next : Configuration layout := ⟨saved, actual.environment, rest, actual.ordinal + 1⟩
      refine ⟨next, ?_, ?_⟩
      · change actual.pending = request :: rest at pending
        simp [machine, pending, executed, next]
      · exact ⟨endpoint, bindings, rfl, congrArg (fun value => value + 1) counter⟩

theorem realize_history (schema : Schema) (codecProfile : Notation) (sort : String) (layout : Layout)
    (before after : Configuration layout) (events : List (Receipt layout))
    (history : History schema codecProfile sort layout before events after)
    (actual : Configuration layout) (same : Corresponds actual before) :
    ∃ saved, ((machine schema codecProfile sort layout).run events.length actual).2 = .exhausted saved ∧
      ((machine schema codecProfile sort layout).run events.length actual).1.map observe = events.map observe ∧
      Corresponds saved after := by
  induction history generalizing actual with
  | nil state => exact ⟨actual, rfl, rfl, same⟩
  | cons receipt events final advanced following ih =>
      obtain ⟨next, stepped, corresponding⟩ := realize_advance schema codecProfile sort layout
        receipt.before receipt.after actual receipt.request receipt.response advanced same
      obtain ⟨saved, exhausted, observed, endpoint⟩ := ih next corresponding
      simp only [List.length_cons]
      rw [(machine schema codecProfile sort layout).run_succ_publish stepped]
      refine ⟨saved, exhausted, ?_, endpoint⟩
      simp only [List.singleton_append, List.map_cons, observe]
      rw [same.2.2.2, observed]

theorem history_has_execution (schema : Schema) (codecProfile : Notation) (sort : String) (layout : Layout)
    (before after : Configuration layout) (events : List (Receipt layout))
    (history : History schema codecProfile sort layout before events after) :
    ∃ saved, ((machine schema codecProfile sort layout).run events.length before).2 = .exhausted saved ∧
      ((machine schema codecProfile sort layout).run events.length before).1.map observe = events.map observe ∧
      Corresponds saved after :=
  realize_history schema codecProfile sort layout before after events history before (.refl before)

end Mettapedia.Languages.C11.CestaAccessCorrespondence

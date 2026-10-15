import Mettapedia.OSLF.Syntax.RhoPayloadRuntimeObservations
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingObserverAdequacy
import Mettapedia.GSLT.Core.OperationalPathFibration

/-!
# Actual compiled executions in the payload rho presentation

The established compiler's free infrastructure variables are names. Its actual
runtime states therefore enter the admitted, locally covered payload
interpretation. Complete supplied paths retain their lengths and endpoints.
The target's public observer reads payload code, and contextual adequacy uses
the established source-origin admission of protocol clients.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingPayloadRuntime

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.RhoPayloadParameterizedRuntime
open Mettapedia.OSLF.MeTTaIL.Syntax (rhoReflectivePresentation)
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoEncodingTyping
open NamePassingLambda NamePassingContexts NamePassingObserverAdequacy

theorem atomic_names_only (name : String) :
    rhoAtomicNameContext name ≠ some rhoReflectivePresentation.processSort := by
  change some "Name" ≠ some "Proc"
  decide

def presentation : CoveredTranslation RhoUnaryReadback.Target targetTheory :=
  covered atomic_names_only

def state (process : RhoUnaryReadback.TargetProcess) : targetTheory.Term :=
  presentation.mapTerm process

def executionFunctor : ExecutionObject RhoUnaryReadback.Target ⥤ ExecutionObject targetTheory :=
  presentation.toOperational.pathFunctor

def mappedPrefix {initial final : RhoUnaryReadback.TargetProcess}
    (actual : ExecutionPath RhoUnaryReadback.Target initial final) :
    ExecutionPath targetTheory (state initial) (state final) :=
  presentation.toOperational.mapRoute actual

theorem prefix_length {initial final : RhoUnaryReadback.TargetProcess}
    (actual : ExecutionPath RhoUnaryReadback.Target initial final) :
    (mappedPrefix actual).length = actual.length :=
  presentation.toOperational.mapRoute_length actual

theorem prefix_append {initial middle final : RhoUnaryReadback.TargetProcess}
    (first : ExecutionPath RhoUnaryReadback.Target initial middle)
    (second : ExecutionPath RhoUnaryReadback.Target middle final) :
    mappedPrefix (first.append second) = (mappedPrefix first).append (mappedPrefix second) :=
  presentation.toOperational.mapRoute_append first second

theorem runtime_step_iff (before after : RhoUnaryReadback.TargetProcess) :
    RhoUnaryReadback.Target.Step before after ↔ targetTheory.Step (state before) (state after) :=
  RhoPayloadParameterizedRuntime.step_iff atomic_names_only before after

theorem runtime_equation_iff (before after : RhoUnaryReadback.TargetProcess) :
    state before = state after ↔ RhoUnaryReadback.Target.Equiv before after :=
  mapClass_eq_iff atomic_names_only before after

theorem runtime_bisimilar_iff (before after : RhoUnaryReadback.TargetProcess) :
    RhoUnaryReadback.Target.Bisimilar before after ↔
      targetTheory.Bisimilar (state before) (state after) :=
  bisimilar_iff atomic_names_only before after

theorem public_return_iff {Γ : Ctx Mettapedia.Languages.ProcessCalculi.PolyadicPi.sig}
    (world : RhoUnaryWorld.SeedWorld Γ) (channel : Var Γ .nm)
    (current : RhoUnaryReadback.TargetProcess) :
    (RhoUnaryInputObservation.targetPredicate world channel).1 current ↔
      (publicInput (world.world channel).term).1 (state current) :=
  (publicInput_map atomic_names_only (world.world channel).term current).symm

theorem native_may_return_iff {Γ : Ctx Mettapedia.Languages.ProcessCalculi.PolyadicPi.sig}
    (world : RhoUnaryWorld.SeedWorld Γ) (channel : Var Γ .nm)
    (current : RhoUnaryReadback.TargetProcess) :
    (semanticDiamond RhoUnaryReadback.Target.closure
      (RhoUnaryInputObservation.targetPredicate world channel)).1 current ↔
    (semanticDiamond targetTheory.closure (publicInput (world.world channel).term)).1
      (state current) :=
  may_input_iff atomic_names_only (world.world channel).term current

/-- The client executes the actual compiler and the independent target
presentation before inspecting the public receiving channel. -/
def PayloadMayReturn {Γ : Ctx Mettapedia.Languages.ProcessCalculi.PolyadicPi.sig} (component : ProtocolContexts.Program Γ) : Prop :=
  ∃ code : RhoUnaryCode.Code 0,
    RhoUnaryCompiler.compile (RhoUnaryWorld.initial (.nm :: Γ)).world
      (MonadicProtocol.lower (component (NamePassingUnaryForward.references Γ) .zero)) = some code ∧
    (semanticDiamond targetTheory.closure
      (publicInput ((RhoUnaryWorld.initial (.nm :: Γ)).world .zero).term)).1
      (state (RhoUnaryReadback.runtimeProcess code
        (RhoUnaryWorld.initial (.nm :: Γ)).available))

theorem payload_may_return_iff {Γ : Ctx Mettapedia.Languages.ProcessCalculi.PolyadicPi.sig}
    (component : ProtocolContexts.Program Γ) :
    PayloadMayReturn component ↔ ProtocolMayReturn component := by
  constructor
  · rintro ⟨code, compiled, observed⟩
    exact ⟨code, compiled,
      (native_may_return_iff (RhoUnaryWorld.initial (.nm :: Γ)) .zero _).mpr observed⟩
  · rintro ⟨code, compiled, observed⟩
    exact ⟨code, compiled,
      (native_may_return_iff (RhoUnaryWorld.initial (.nm :: Γ)) .zero _).mp observed⟩

theorem context_may_return_iff {Γ Δ : Ctx Mettapedia.Languages.ProcessCalculi.PolyadicPi.sig}
    (context : SourceContext Γ Δ) (source : Expr Γ) :
    MayReturn (context.plug source) ↔ PayloadMayReturn ((translate context).plug (program source)) :=
  (context_mayReturn_iff context source).trans (payload_may_return_iff _).symm

def PayloadEquivalent {Γ : Ctx Mettapedia.Languages.ProcessCalculi.PolyadicPi.sig}
    (left right : ProtocolContexts.Program Γ) : Prop :=
  ∀ (Δ : Ctx Mettapedia.Languages.ProcessCalculi.PolyadicPi.sig) (context : ProtocolContexts.Context Γ Δ), Admitted context →
    (PayloadMayReturn (context.plug left) ↔ PayloadMayReturn (context.plug right))

theorem payload_equivalent_iff {Γ : Ctx Mettapedia.Languages.ProcessCalculi.PolyadicPi.sig}
    (left right : ProtocolContexts.Program Γ) :
    PayloadEquivalent left right ↔ ProtocolEquivalent left right := by
  constructor
  · intro equivalent Δ context admitted
    exact (payload_may_return_iff _).symm.trans
      ((equivalent Δ context admitted).trans (payload_may_return_iff _))
  · intro equivalent Δ context admitted
    exact (payload_may_return_iff _).trans
      ((equivalent Δ context admitted).trans (payload_may_return_iff _).symm)

theorem contextual_adequacy {Γ : Ctx Mettapedia.Languages.ProcessCalculi.PolyadicPi.sig} (left right : Expr Γ) :
    SourceEquivalent left right ↔ PayloadEquivalent (program left) (program right) :=
  (NamePassingObserverAdequacy.contextual_adequacy left right).trans
    (payload_equivalent_iff _ _).symm

theorem admitted_context_congruence {Γ Δ : Ctx Mettapedia.Languages.ProcessCalculi.PolyadicPi.sig}
    {context : ProtocolContexts.Context Γ Δ} (admitted : Admitted context)
    {left right : ProtocolContexts.Program Γ} (equivalent : PayloadEquivalent left right) :
    PayloadEquivalent (context.plug left) (context.plug right) :=
  (payload_equivalent_iff _ _).mpr
    (NamePassingObserverAdequacy.admitted_context_congruence admitted
      ((payload_equivalent_iff left right).mp equivalent))

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingPayloadRuntime

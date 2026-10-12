import Mettapedia.GSLT.Core.OperationalPathFibration

/-!
# Exact instruction counts when lifting covered executions

A locally covered one-step translation lifts every supplied target prefix
from an image state. The lifted source prefix has the exact target endpoint
and the same number of primitive steps. This differs from compilation with
administrative steps, where only a bound is generally available.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Ultrainfinite.StepCover

open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational

theorem liftExecutionPath {source target : GSLT} {mapTerm : source.Term → target.Term}
    (cover : StepCover source target mapTerm)
    {initial : source.Term} {final : target.Term}
    (path : ExecutionPath target (mapTerm initial) final) :
    ∃ endpoint, ∃ actual : ExecutionPath source initial endpoint,
      mapTerm endpoint = final ∧ actual.length = path.length := by
  have lift : ∀ {first last : target.Term} (route : ExecutionPath target first last),
      ∀ start : source.Term, mapTerm start = first →
        ∃ endpoint, ∃ actual : ExecutionPath source start endpoint,
          mapTerm endpoint = last ∧ actual.length = route.length := by
    intro first last route
    induction route with
    | refl state =>
        intro start equal
        exact ⟨start, .refl start, equal, rfl⟩
    | @cons before middle after head rest ih =>
        intro start equal
        have headStep : target.Step (mapTerm start) middle := by
          rw [equal]
          exact head.down
        obtain ⟨next, nextStep, nextEq⟩ := cover.liftStep headStep
        obtain ⟨endpoint, actual, endpointEq, countEq⟩ := ih next nextEq
        exact ⟨endpoint, .cons ⟨nextStep⟩ actual, endpointEq,
          congrArg (fun count => count + 1) countEq⟩
  exact lift path initial rfl

/-- The lifted execution recovers the entire supplied target path, not only
its final state and length. The heterogeneous equality accounts solely for
the proved equality of its endpoint. -/
theorem liftExecutionPath_exact {source target : GSLT}
    (translation : OperationalTranslation source target)
    (cover : StepCover source target translation.mapTerm)
    {initial : source.Term} {final : target.Term}
    (path : ExecutionPath target (translation.mapTerm initial) final) :
    ∃ endpoint, ∃ actual : ExecutionPath source initial endpoint,
      translation.mapTerm endpoint = final ∧
        HEq (translation.mapRoute actual) path ∧ actual.length = path.length := by
  have lift : ∀ {first last : target.Term} (route : ExecutionPath target first last),
      ∀ start : source.Term, translation.mapTerm start = first →
        ∃ endpoint, ∃ actual : ExecutionPath source start endpoint,
          translation.mapTerm endpoint = last ∧
            HEq (translation.mapRoute actual) route ∧ actual.length = route.length := by
    intro first last route
    induction route with
    | refl state =>
        intro start equal
        refine ⟨start, .refl start, equal, ?_, rfl⟩
        cases equal
        rfl
    | @cons before middle after head rest ih =>
        intro start equal
        have headStep : target.Step (translation.mapTerm start) middle := by
          rw [equal]
          exact head.down
        obtain ⟨next, nextStep, nextEq⟩ := cover.liftStep headStep
        obtain ⟨endpoint, actual, endpointEq, exactRest, countEq⟩ := ih next nextEq
        refine ⟨endpoint, .cons ⟨nextStep⟩ actual, endpointEq, ?_,
          congrArg (fun count => count + 1) countEq⟩
        cases equal
        cases nextEq
        cases endpointEq
        change HEq (Route.cons ⟨translation.mapStep nextStep⟩ (translation.mapRoute actual))
          (Route.cons head rest)
        rw [eq_of_heq exactRest]
  exact lift path initial rfl

end Mettapedia.GSLT.Ultrainfinite.StepCover

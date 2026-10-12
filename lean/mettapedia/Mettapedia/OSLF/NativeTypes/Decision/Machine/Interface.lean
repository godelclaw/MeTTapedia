import Mettapedia.OSLF.NativeTypes.Decision.Reference.Core
import Mettapedia.OSLF.NativeTypes.Decision.Stream

open Mettapedia.OSLF.Framework

/-!
# Suspended primitive work for total-budget native decisions

The operational backend supplies an actual delayed receipt stream.
Its complete readout has independently proved step coverage. Leaf streams
carry their own native certificates and eventually decide admitted sources.
Flattening occurs only in the laws; starting work does not ask for a bound.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Decision.Machine

open Mettapedia.GSLT GSLTTypeSynthesis
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core Mettapedia.OSLF.NativeTypes.Decision.Scheduling

universe u v w

structure CursorBackend (system : GSLT.{u}) (admitted : system.Term → Prop) where
  Receipt : system.Term → Type v
  target : (source : system.Term) → Receipt source → system.Term
  tasks : (source : system.Term) → Stream (Receipt source)
  sound : ∀ source receipt, receipt ∈ (tasks source).flatten → system.Step source (target source receipt)
  coverage : ∀ source, admitted source → ∀ actual, system.Step source actual →
    ∃ receipt, receipt ∈ (tasks source).flatten ∧ system.Equiv actual (target source receipt)
  target_admitted : ∀ source, admitted source → ∀ receipt,
    receipt ∈ (tasks source).flatten → admitted (target source receipt)

structure LeafBackend (system : GSLT.{u}) (admitted : system.Term → Prop) where
  predicate : EquationPredicate system
  tasks : (source : system.Term) → Stream (Outcome (predicate source))
  complete : ∀ source, admitted source →
    ∃ result, result ∈ (tasks source).flatten ∧ result.Decided

def LeafBackend.ofBoolean {system : GSLT.{u}} {admitted : system.Term → Prop}
    (predicate : EquationPredicate system) (accepts : system.Term → Bool)
    (exact : ∀ source, accepts source = true ↔ predicate source) : LeafBackend system admitted where
  predicate := predicate
  tasks source := .pause fun _ =>
    if found : accepts source = true then
      .yield (.proved ((exact source).mp found)) fun _ => .done
    else .yield (.refuted (fun holds => found ((exact source).mpr holds))) fun _ => .done
  complete source _ := by
    by_cases found : accepts source = true
    · exact ⟨.proved ((exact source).mp found), by simp [found, Stream.flatten],
        true, rfl⟩
    · exact ⟨.refuted (fun holds => found ((exact source).mpr holds)), by simp [found, Stream.flatten],
        false, rfl⟩

end Mettapedia.OSLF.NativeTypes.Decision.Machine

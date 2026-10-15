import Mettapedia.GSLT.Core.SemanticInvariant
import Mettapedia.GSLT.Core.Composition

/-!
# Changing authoring interfaces through exact elaboration

Translations reuse `GSLT.ExactElaboration`: they recover a payload and quote
it in another interface. Composition retains failure and the complete payload.
The round trip is a canonicalization, not an assertion that arbitrary source
syntax is recovered. The interface-change machine retains the interface tag
and source term, and permits both source rewrites and explicit re-quotation.
Its equations are literal protocol-state equality; each source's own equations
remain respected by elaboration without erasing protocol occurrence data.
-/

set_option autoImplicit false
set_option linter.dupNamespace false

namespace Mettapedia.GSLT

universe u v w x

namespace GSLT.ExactElaboration

variable {Payload : Type u} {Source : GSLT.{v}} {Target : GSLT.{w}}
  {Third : GSLT.{x}}

/-- Recover the complete payload, then print it in the chosen interface. -/
def translate (source : GSLT.ExactElaboration Source Payload)
    (target : GSLT.ExactElaboration Target Payload) (term : Source.Term) :
    Option Target.Term :=
  (source.elaborate term).map target.quote

/-- Translating cannot add, remove, or change an elaborated payload. -/
theorem elaborate_translate (source : GSLT.ExactElaboration Source Payload)
    (target : GSLT.ExactElaboration Target Payload) (term : Source.Term) :
    (translate source target term).bind target.elaborate = source.elaborate term := by
  cases h : source.elaborate term with
  | none => simp [translate, h]
  | some payload => simp [translate, h, target.elaborate_quote]

theorem translate_none_iff (source : GSLT.ExactElaboration Source Payload)
    (target : GSLT.ExactElaboration Target Payload) (term : Source.Term) :
    translate source target term = none ↔ source.elaborate term = none := by
  cases h : source.elaborate term <;> simp [translate, h]

/-- The intermediate interface may normalize spelling, but cannot affect
the final canonical result or failure. -/
theorem translate_comp (source : GSLT.ExactElaboration Source Payload)
    (target : GSLT.ExactElaboration Target Payload)
    (third : GSLT.ExactElaboration Third Payload) (term : Source.Term) :
    (translate source target term).bind (translate target third) =
      translate source third term := by
  cases h : source.elaborate term with
  | none => simp [translate, h]
  | some payload => simp [translate, h, target.elaborate_quote]

@[simp] theorem translate_quote (source : GSLT.ExactElaboration Source Payload)
    (target : GSLT.ExactElaboration Target Payload) (payload : Payload) :
    translate source target (source.quote payload) = some (target.quote payload) := by
  simp [translate, source.elaborate_quote]

/-- Distinct complete payloads remain distinct after canonical printing. -/
theorem translate_eq_iff (source : GSLT.ExactElaboration Source Payload)
    (target : GSLT.ExactElaboration Target Payload) (first second : Source.Term) :
    translate source target first = translate source target second ↔
      source.elaborate first = source.elaborate second := by
  constructor
  · intro equal
    have checked := congrArg (fun result => result.bind target.elaborate) equal
    simpa only [elaborate_translate] using checked
  · intro equal
    simp only [translate, equal]

/-- Re-quotation is idempotent, including the rejection case. -/
theorem normalize_idempotent (source : GSLT.ExactElaboration Source Payload)
    (term : Source.Term) :
    (translate source source term).bind (translate source source) =
      translate source source term :=
  translate_comp source source source term

/-- An additional source-equation round-trip law is sufficient to reflect
payload equality on admitted inputs. It is not supplied by exact elaboration. -/
theorem source_equiv_iff_of_roundTrip
    (source : GSLT.ExactElaboration Source Payload)
    (roundTrip : ∀ term payload, source.elaborate term = some payload →
      Source.Equiv term (source.quote payload))
    {first second : Source.Term} {payload : Payload}
    (admitted : source.elaborate first = some payload) :
    Source.Equiv first second ↔ source.elaborate first = source.elaborate second := by
  constructor
  · exact source.equation
  · intro equal
    exact Source.equations.iseqv.trans (roundTrip first payload admitted)
      (Source.equations.iseqv.symm (roundTrip second payload (equal ▸ admitted)))

end GSLT.ExactElaboration

namespace GSLT.CompositionalElaboration

/-- Translate parts and compose them in the target, or compose in the source
and elaborate: both routes retain the same complete payload and rejection,
provided the two authoring interfaces implement the same partial merge. -/
theorem translate_append_observe {Payload : Type u}
    (source target : GSLT.CompositionalElaboration Payload)
    (sameMerge : source.merge = target.merge)
    (first second : source.authoring.theory.Term) :
    ((GSLT.ExactElaboration.translate source.elaboration target.elaboration first).bind
      fun left =>
        (GSLT.ExactElaboration.translate source.elaboration target.elaboration second).map
          (fun right => target.authoring.append left right)).bind
      target.elaboration.elaborate =
        source.elaboration.elaborate (source.authoring.append first second) := by
  rw [source.elaborate_append]
  cases hfirst : source.elaboration.elaborate first <;>
    cases hsecond : source.elaboration.elaborate second <;>
    simp [GSLT.ExactElaboration.translate, hfirst, hsecond,
      target.elaborate_append, target.elaboration.elaborate_quote, sameMerge]

end GSLT.CompositionalElaboration

namespace PresentationChange

variable {Interface : Type v} {Payload : Type u}
  {interfaces : Interface → GSLT.{w}}

/-- Interface identity is retained with the authored term. -/
abbrev State (interfaces : Interface → GSLT.{w}) :=
  (interface : Interface) × (interfaces interface).Term

def observe (family : ∀ interface, GSLT.ExactElaboration (interfaces interface) Payload)
    (state : State interfaces) : Option Payload :=
  (family state.1).elaborate state.2

@[simp] theorem observe_quote (family : ∀ interface,
    GSLT.ExactElaboration (interfaces interface) Payload)
    (interface : Interface) (payload : Payload) :
    observe family ⟨interface, (family interface).quote payload⟩ = some payload :=
  (family interface).elaborate_quote payload

/-- An executable change requests one particular target interface. -/
def switch (family : ∀ interface, GSLT.ExactElaboration (interfaces interface) Payload)
    (target : Interface) (state : State interfaces) : Option (State interfaces) :=
  (observe family state).map (fun payload => ⟨target, (family target).quote payload⟩)

/-- Source rewriting and re-quotation are distinct protocol transitions. -/
inductive Step (family : ∀ interface,
    GSLT.ExactElaboration (interfaces interface) Payload) : State interfaces → State interfaces → Prop
  | source {interface : Interface} {first second : (interfaces interface).Term}
      (step : (interfaces interface).Step first second) :
      Step family ⟨interface, first⟩ ⟨interface, second⟩
  | change {state : State interfaces} {payload : Payload} (target : Interface)
      (checked : observe family state = some payload) :
      Step family state ⟨target, (family target).quote payload⟩

/-- This protocol acts on actual source terms; it is not an identity or
constant machine on already elaborated payloads. -/
def system (family : ∀ interface,
    GSLT.ExactElaboration (interfaces interface) Payload) : GSLT where
  Term := State interfaces
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := Step family
  rewrites_resp_left := by
    intro first other target equal step
    cases equal
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro first target other step equal
    cases equal
    exact step

theorem step_observe (family : ∀ interface,
    GSLT.ExactElaboration (interfaces interface) Payload)
    {first second : State interfaces} (step : Step family first second) :
    observe family first = observe family second := by
  cases step with
  | source sourceStep => exact (family _).rewrite sourceStep
  | change target checked =>
      exact checked.trans ((family target).elaborate_quote _).symm

/-- Reuse the established invariant and path machinery. -/
def invariant (family : ∀ interface,
    GSLT.ExactElaboration (interfaces interface) Payload) :
    SemanticInvariant (system family) (Option Payload) where
  denote := observe family
  equation := fun equal => congrArg (observe family) equal
  rewrite := step_observe family

theorem path_observe (family : ∀ interface,
    GSLT.ExactElaboration (interfaces interface) Payload)
    {first second : State interfaces}
    (path : IndexedOperational.ExecutionPath (system family) first second) :
    observe family first = observe family second :=
  (invariant family).executionPath_eq path

theorem switch_observe (family : ∀ interface,
    GSLT.ExactElaboration (interfaces interface) Payload)
    (target : Interface) (state : State interfaces) :
    (switch family target state).bind (observe family) = observe family state := by
  cases h : observe family state with
  | none => simp [switch, h]
  | some payload => simp [switch, h]

theorem switch_comp (family : ∀ interface,
    GSLT.ExactElaboration (interfaces interface) Payload)
    (middle target : Interface) (state : State interfaces) :
    (switch family middle state).bind (switch family target) =
      switch family target state := by
  cases h : observe family state with
  | none => simp [switch, h]
  | some payload => simp [switch, h]

/-- Failed inputs cannot acquire a successful target by an interface change. -/
theorem rejected_no_change (family : ∀ interface,
    GSLT.ExactElaboration (interfaces interface) Payload)
    {state : State interfaces} (rejected : observe family state = none)
    (target : Interface) :
    switch family target state = none := by
  simp [switch, rejected]

end PresentationChange
end Mettapedia.GSLT

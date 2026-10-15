import Mettapedia.OSLF.Syntax.ScopedBindingInstrumentTheory
import Mettapedia.OSLF.Framework.SortedInstrumentCongruenceSystem
import Mettapedia.GSLT.Logic.HennessyMilnerTransport

/-!
# Binding instruments on original scoped terms and arguments

The steps below are stated directly on binding terms. An operator probe
returns the actual argument list; projection enters that argument's declared
binder context. A variable probe retains its position and returns an empty
list. Authored steps remain separately labelled. The independently constructed
context-indexed encoding preserves and reflects every instrument step.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.ScopedInstruments

open ScopedEncoding

open Mettapedia.OSLF.Framework

universe uAtom uLabel

variable {S : Signature} {E : EquationTheory S}

-- The authored observation and action carriers are independently sized.
set_option linter.checkUnivs false in
structure BaseSystem (E : EquationTheory S) where
  Atom : Type uAtom
  observes : Atom → {context : Ctx S} → {sort : S.Srt} → Term S context sort → Prop
  observes_resp : ∀ atom {context : Ctx S} {sort : S.Srt} {first second : Term S context sort},
    E.relation first second → (observes atom first ↔ observes atom second)
  Label : Type uLabel
  act : Label → {source target : Scope S} →
    Term S source.1 source.2 → Term S target.1 target.2 → Prop
  act_resp_left : ∀ {label : Label} {source target : Scope S}
    {first second : Term S source.1 source.2} {next : Term S target.1 target.2},
    E.relation first second → act label first next →
      ∃ next' : Term S target.1 target.2, act label second next' ∧ E.relation next next'
  act_resp_right : ∀ {label : Label} {source target : Scope S}
    {start : Term S source.1 source.2} {next next' : Term S target.1 target.2},
    act label start next → E.relation next next' → act label start next'

/-- A profile with no authored steps; its instruments are still operational. -/
def BaseSystem.silent (E : EquationTheory S) : BaseSystem.{0,0} E where
  Atom := Empty
  observes atom := atom.elim
  observes_resp atom := atom.elim
  Label := Empty
  act label := label.elim
  act_resp_left {label} := label.elim
  act_resp_right {label} := label.elim

def sortedBase (base : BaseSystem.{uAtom,uLabel} E) :
    SortedInstrumentCongruence.BaseSystem.{0,0,uAtom,uLabel} (sortedTheory E) where
  Atom := base.Atom
  observes := fun atom {_} value => base.observes atom (decode value)
  observes_resp := fun atom {_} {_} {_} relation => base.observes_resp atom relation
  Label := base.Label
  act := fun label {_} {_} start next => base.act label (decode start) (decode next)
  act_resp_left := by
    intro label source target first second previous relation step
    obtain ⟨next, matched, equation⟩ := base.act_resp_left relation step
    refine ⟨encode next, ?_, ?_⟩
    · simpa only [decode_encode] using matched
    · simpa only [sortedTheory, decode_encode] using equation
  act_resp_right := by
    intro label source target start next next' step relation
    exact base.act_resp_right step relation

inductive State (S : Signature) where
  | term {context : Ctx S} {sort : S.Srt} (value : Term S context sort)
  | bundle (constructor : Constructor S) (arguments : Arguments constructor)

namespace State

def encode : State S → SortedInstrumentCongruence.State (signature S)
  | .term value => .term (ScopedEncoding.encode value)
  | .bundle constructor arguments => .bundle constructor
      (fun position => ScopedEncoding.encode (readArguments constructor arguments position))

def decode : SortedInstrumentCongruence.State (signature S) → State S
  | .term value => .term (ScopedEncoding.decode value)
  | .bundle constructor arguments => .bundle constructor
      (assemble constructor (fun position => ScopedEncoding.decode (arguments position)))

@[simp]
theorem decode_encode (state : State S) : decode (encode state) = state := by
  cases state with
  | term value => exact congrArg State.term (ScopedEncoding.decode_encode value)
  | bundle constructor arguments =>
      change State.bundle constructor (assemble constructor
        (fun position => ScopedEncoding.decode
          (ScopedEncoding.encode (readArguments constructor arguments position)))) = _
      simp only [ScopedEncoding.decode_encode, assemble_read]

@[simp]
theorem encode_decode (state : SortedInstrumentCongruence.State (signature S)) : encode (decode state) = state := by
  cases state with
  | term value => exact congrArg SortedInstrumentCongruence.State.term (ScopedEncoding.encode_decode value)
  | bundle constructor arguments =>
      apply congrArg (SortedInstrumentCongruence.State.bundle constructor)
      change (fun position => ScopedEncoding.encode (readArguments constructor
        (assemble constructor (fun position => ScopedEncoding.decode (arguments position))) position)) = _
      rw [read_assemble]
      funext position
      exact ScopedEncoding.encode_decode (arguments position)

def equivalence : State S ≃ SortedInstrumentCongruence.State (signature S) where
  toFun := encode
  invFun := decode
  left_inv := decode_encode
  right_inv := encode_decode

end State

abbrev Label (S : Signature) (Proper : Type uLabel) := SortedInstrumentCongruence.Label (signature S) Proper

/-- This rule presentation uses original binding terms, not sorted steps. -/
inductive Act (base : BaseSystem.{uAtom,uLabel} E) (opened : Constructor S → Prop) :
    Label S base.Label → State S → State S → Prop where
  | proper {label : base.Label} {source target : Scope S}
      {start : Term S source.1 source.2} {next : Term S target.1 target.2} :
      base.act label start next → Act base opened (.proper label) (.term start) (.term next)
  | ask (constructor : Constructor S) (permission : opened constructor)
      {source : Term S ((signature S).output constructor).1 ((signature S).output constructor).2}
      {arguments : Arguments constructor} :
      E.relation source (buildTerm constructor arguments) →
        Act base opened (.ask constructor) (.term source) (.bundle constructor arguments)
  | get (constructor : Constructor S) (permission : opened constructor)
      {arguments : Arguments constructor} (position : Fin ((signature S).arity constructor))
      {target : Term S ((signature S).input constructor position).1
        ((signature S).input constructor position).2} :
      E.relation (readArguments constructor arguments position) target →
        Act base opened (.get constructor position) (.bundle constructor arguments) (.term target)
  | build (constructor : Constructor S) (permission : opened constructor)
      {arguments : Arguments constructor}
      {target : Term S ((signature S).output constructor).1 ((signature S).output constructor).2} :
      E.relation (buildTerm constructor arguments) target →
        Act base opened (.build constructor) (.bundle constructor arguments) (.term target)

namespace Act

variable {base : BaseSystem.{uAtom,uLabel} E} {opened : Constructor S → Prop}

/-- Projection retains the exact supplied argument, up to the authored equations. -/
theorem get_readout (constructor : Constructor S) (arguments : Arguments constructor)
    (position : Fin ((signature S).arity constructor))
    (target : Term S ((signature S).input constructor position).1
      ((signature S).input constructor position).2)
    (step : Act base opened (.get constructor position) (.bundle constructor arguments) (.term target)) :
    E.relation (readArguments constructor arguments position) target := by
  cases step with
  | get _ _ _ relation => exact relation

theorem encode {label : Label S base.Label} {source target : State S}
    (step : Act base opened label source target) :
    SortedInstrumentCongruence.Act (sortedBase base) opened label (State.encode source) (State.encode target) := by
  cases step with
  | proper step =>
      apply SortedInstrumentCongruence.Act.proper
      simpa only [sortedBase, ScopedEncoding.decode_encode] using step
  | ask constructor permission relation =>
      cases constructor <;> apply SortedInstrumentCongruence.Act.ask _ permission
      all_goals
        rw [← encode_build]
        exact (sorted_relation_encode E _ _).mpr relation
  | get constructor permission position relation =>
      cases constructor with
      | «variable» context sort originalPosition => exact Fin.elim0 position
      | operation context sort operator =>
          apply SortedInstrumentCongruence.Act.get _ permission position
          simpa only [sortedTheory, ScopedEncoding.decode_encode] using relation
  | build constructor permission relation =>
      cases constructor <;> apply SortedInstrumentCongruence.Act.build _ permission
      all_goals
        change E.relation (ScopedEncoding.decode (SortedConstructors.Term.node _ _))
          (ScopedEncoding.decode (ScopedEncoding.encode _))
        rw [← encode_build, ScopedEncoding.decode_encode, ScopedEncoding.decode_encode]
        exact relation

theorem decode {label : Label S base.Label} {source target : SortedInstrumentCongruence.State (signature S)}
    (step : SortedInstrumentCongruence.Act (sortedBase base) opened label source target) :
    Act base opened label (State.decode source) (State.decode target) := by
  cases label with
  | proper label =>
      obtain ⟨first, second, start, next, rfl, rfl, authored⟩ :=
        SortedInstrumentCongruence.Act.proper_inv step
      exact Act.proper authored
  | ask constructor =>
      obtain ⟨permission, value, arguments, rfl, rfl, relation⟩ :=
        SortedInstrumentCongruence.Act.ask_inv step
      cases constructor <;> apply Act.ask _ permission
      all_goals
        change E.relation (ScopedEncoding.decode _) (ScopedEncoding.decode _) at relation
        rw [decode_node] at relation
        exact relation
  | get constructor position =>
      obtain ⟨permission, arguments, value, rfl, rfl, relation⟩ :=
        SortedInstrumentCongruence.Act.get_inv step
      cases constructor with
      | «variable» context sort originalPosition => exact Fin.elim0 position
      | operation context sort operator =>
          apply Act.get _ permission position
          change E.relation (ScopedEncoding.decode _) (ScopedEncoding.decode _) at relation
          simpa only [read_assemble] using relation
  | build constructor =>
      obtain ⟨permission, arguments, value, rfl, rfl, relation⟩ :=
        SortedInstrumentCongruence.Act.build_inv step
      cases constructor <;> apply Act.build _ permission
      all_goals
        change E.relation (ScopedEncoding.decode _) (ScopedEncoding.decode _) at relation
        rw [decode_node] at relation
        exact relation

theorem encode_iff {label : Label S base.Label} {source target : State S} :
    Act base opened label source target ↔
      SortedInstrumentCongruence.Act (sortedBase base) opened label (State.encode source) (State.encode target) := by
  constructor
  · exact encode
  · intro step
    simpa only [State.decode_encode] using decode step

end Act

end Mettapedia.OSLF.Binding.ScopedInstruments

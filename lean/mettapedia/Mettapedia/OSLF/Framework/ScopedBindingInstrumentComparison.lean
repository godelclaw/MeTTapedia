import Mettapedia.OSLF.Framework.ScopedBindingInstrumentSystem

/-!
# Exact behavioral comparison for scoped binding instruments

The original binding-state equations, observations and labelled steps are
compared with the context-indexed constructor system. The state equivalence
gives a cover of the entire outgoing relation, hence preserves and reflects
bisimilarity for every instrument policy. No branching or equation matching
algorithm is assumed.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.ScopedInstruments

open ScopedEncoding
open Mettapedia.GSLT
open Mettapedia.OSLF.Framework

universe uAtom uLabel

variable {S : Signature} {E : EquationTheory S}

inductive StateRel (E : EquationTheory S) : State S → State S → Prop where
  | term {context : Ctx S} {sort : S.Srt} {first second : Term S context sort} :
      E.relation first second → StateRel E (.term first) (.term second)
  | bundle (constructor : Constructor S) {first second : Arguments constructor} :
      (∀ position, E.relation (readArguments constructor first position)
        (readArguments constructor second position)) →
      StateRel E (.bundle constructor first) (.bundle constructor second)

namespace StateRel

theorem encode {first second : State S} (related : StateRel E first second) :
    SortedInstrumentCongruence.StateRel (sortedTheory E) (State.encode first) (State.encode second) := by
  cases related with
  | term equation => exact .term ((sorted_relation_encode E _ _).mpr equation)
  | bundle constructor children =>
      exact .bundle constructor (fun position =>
        (sorted_relation_encode E _ _).mpr (children position))

theorem decode {first second : SortedInstrumentCongruence.State (signature S)}
    (related : SortedInstrumentCongruence.StateRel (sortedTheory E) first second) :
    StateRel E (State.decode first) (State.decode second) := by
  cases related with
  | term equation => exact .term equation
  | bundle constructor children =>
      apply StateRel.bundle constructor
      cases constructor with
      | «variable» context sort originalPosition =>
          intro position
          exact Fin.elim0 position
      | operation context sort operator =>
          intro position
          simpa only [read_assemble, sortedTheory] using children position

theorem encode_iff {first second : State S} :
    StateRel E first second ↔
      SortedInstrumentCongruence.StateRel (sortedTheory E) (State.encode first) (State.encode second) := by
  constructor
  · exact encode
  · intro related
    simpa only [State.decode_encode] using decode related

theorem refl (E : EquationTheory S) : ∀ state : State S, StateRel E state state
  | .term value => .term (E.reflexive value)
  | .bundle constructor _ => .bundle constructor (fun _ => E.reflexive _)

theorem symm {first second : State S} (related : StateRel E first second) :
    StateRel E second first :=
  encode_iff.mpr (SortedInstrumentCongruence.StateRel.symm related.encode)

theorem trans {first middle last : State S} (firstRelated : StateRel E first middle)
    (secondRelated : StateRel E middle last) : StateRel E first last :=
  encode_iff.mpr (SortedInstrumentCongruence.StateRel.trans firstRelated.encode secondRelated.encode)

end StateRel

namespace Act

variable {base : BaseSystem.{uAtom,uLabel} E} {opened : Constructor S → Prop}

theorem resp_left {label : Label S base.Label} {first second target : State S}
    (equation : StateRel E first second) (step : Act base opened label first target) :
    ∃ target', Act base opened label second target' ∧ StateRel E target target' := by
  obtain ⟨next, matched, related⟩ := SortedInstrumentCongruence.Act.resp_left equation.encode step.encode
  refine ⟨State.decode next, ?_, ?_⟩
  · simpa only [State.decode_encode] using Act.decode matched
  · simpa only [State.decode_encode] using StateRel.decode related

theorem resp_right {label : Label S base.Label} {source target target' : State S}
    (step : Act base opened label source target) (equation : StateRel E target target') :
    Act base opened label source target' :=
  encode_iff.mpr (SortedInstrumentCongruence.Act.resp_right step.encode equation.encode)

theorem lift {label : Label S base.Label} {source : State S}
    {target : SortedInstrumentCongruence.State (signature S)}
    (step : SortedInstrumentCongruence.Act (sortedBase base) opened label (State.encode source) target) :
    ∃ next : State S, Act base opened label source next ∧
      SortedInstrumentCongruence.StateRel (sortedTheory E) (State.encode next) target := by
  refine ⟨State.decode target, ?_, ?_⟩
  · simpa only [State.decode_encode] using Act.decode step
  · rw [State.encode_decode]
    exact SortedInstrumentCongruence.StateRel.refl (sortedTheory E) _

end Act

def observes (base : BaseSystem.{uAtom,uLabel} E) (atom : Scope S ⊕ base.Atom) :
    State S → Prop
  | @State.term _ context sort value => match atom with
      | .inl scope => (context, sort) = scope
      | .inr authored => base.observes authored value
  | .bundle _ _ => False

theorem observes_encode (base : BaseSystem.{uAtom,uLabel} E)
    (atom : Scope S ⊕ base.Atom) (state : State S) :
    observes base atom state ↔ SortedInstrumentCongruence.observes (sortedBase base) atom (State.encode state) := by
  cases state <;> cases atom <;>
    simp only [observes, SortedInstrumentCongruence.observes, State.encode, sortedBase, ScopedEncoding.decode_encode]

def gslt (base : BaseSystem.{uAtom,uLabel} E) : GSLT where
  Term := State S
  equations := ⟨StateRel E, StateRel.refl E, StateRel.symm, StateRel.trans⟩
  rewrites source target := ∃ label, Act base (fun _ => False) label source target
  rewrites_resp_left equation rewrite := by
    obtain ⟨label, step⟩ := rewrite
    obtain ⟨target, matched, related⟩ := Act.resp_left equation step
    exact ⟨target, ⟨label, matched⟩, related⟩
  rewrites_resp_right := by
    rintro source target target' ⟨label, step⟩ equation
    exact ⟨label, Act.resp_right step equation⟩

def system (base : BaseSystem.{uAtom,uLabel} E) (opened : Constructor S → Prop) :
    HennessyMilner.System (gslt base) where
  Atom := Scope S ⊕ base.Atom
  observes := observes base
  observes_resp := by
    intro atom first second related
    cases related with
    | term equation =>
        cases atom with
        | inl scope => exact Iff.rfl
        | inr atom => exact base.observes_resp atom equation
    | bundle constructor children => exact Iff.rfl
  Label := Label S base.Label
  act := Act base opened
  act_resp_left := fun equation step => Act.resp_left equation step
  act_resp_right := fun step equation => Act.resp_right step equation

/-- Complete state and transition coverage, including all open contexts. -/
def cover (base : BaseSystem.{uAtom,uLabel} E) (opened : Constructor S → Prop) :
    HennessyMilner.SystemCover (system base opened) (SortedInstrumentCongruence.system (sortedBase base) opened) where
  mapTerm := State.encode
  mapAtom := id
  mapLabel := id
  mapEquiv := StateRel.encode
  observes_iff := observes_encode base
  mapAct := Act.encode
  liftAct := Act.lift

abbrev Bisimilar (base : BaseSystem.{uAtom,uLabel} E) (opened : Constructor S → Prop)
    (first second : State S) : Prop := (system base opened).Bisimilar first second

theorem bisimilar_encode_iff (base : BaseSystem.{uAtom,uLabel} E) (opened : Constructor S → Prop)
    (first second : State S) :
    SortedInstrumentCongruence.Bisimilar (sortedBase base) opened (State.encode first) (State.encode second) ↔
      Bisimilar base opened first second :=
  (cover base opened).bisimilar_map_iff (fun atom => ⟨atom, rfl⟩) (fun label => ⟨label, rfl⟩)
    first second

end Mettapedia.OSLF.Binding.ScopedInstruments

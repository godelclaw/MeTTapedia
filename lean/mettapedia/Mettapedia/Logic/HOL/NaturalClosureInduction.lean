import Mettapedia.Logic.HOL.NaturalClosure

/-!
# Closure-premised induction over admitted Henkin predicates

The strengthened predicate is the denotation of an actual intrinsic term.
Term closure therefore admits it whenever zero, successor and the property
are admitted; full function domains are unnecessary. This is the guarded
induction statement, distinct from ordinary closure elimination.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.NaturalClosure

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

def strengthening (type : Ty Base) :
    Term Const [type ⇒ .prop, type ⇒ type, type] (type ⇒ .prop) :=
  .lam (.and
    (predicate (.var (.vs (.vs (.vs .vz)))) (.var (.vs (.vs .vz))) (.var .vz))
    (.app (.var (.vs .vz)) (.var .vz)))

def parameterValuation (model : HenkinModel.{u, v, w} Base Const) (type : Ty Base)
    (zero : Ty.denote.{u, w} model.Carrier type)
    (successor : Ty.denote.{u, w} model.Carrier (type ⇒ type))
    (property : Ty.denote.{u, w} model.Carrier (type ⇒ .prop)) :
    model.Valuation [type ⇒ .prop, type ⇒ type, type] :=
  let empty : model.Valuation [] := fun impossible => nomatch impossible
  let first : model.Valuation [type] := fun index =>
    model.extend (Γ := []) (σ := type) empty zero index
  let second : model.Valuation [type ⇒ type, type] := fun index =>
    model.extend (Γ := [type]) (σ := type ⇒ type) first successor index
  fun index =>
    model.extend (Γ := [type ⇒ type, type]) (σ := type ⇒ .prop) second property index


theorem parameterValuation_admissible (model : HenkinModel.{u, v, w} Base Const) (type : Ty Base)
    (zero : Ty.denote.{u, w} model.Carrier type)
    (successor : Ty.denote.{u, w} model.Carrier (type ⇒ type))
    (property : Ty.denote.{u, w} model.Carrier (type ⇒ .prop))
    (zeroAdmitted : model.adm type zero) (successorAdmitted : model.adm (type ⇒ type) successor)
    (propertyAdmitted : model.adm (type ⇒ .prop) property) :
    model.ValuationAdmissible (@parameterValuation Base Const model type zero successor property) := by
  intro result index
  cases index with
  | vz => exact propertyAdmitted
  | vs previous => cases previous with
    | vz => exact successorAdmitted
    | vs previous => cases previous with
      | vz => exact zeroAdmitted
      | vs impossible => nomatch impossible

theorem denote_strengthening (model : HenkinModel.{u, v, w} Base Const) (type : Ty Base)
    (zero : Ty.denote.{u, w} model.Carrier type)
    (successor : Ty.denote.{u, w} model.Carrier (type ⇒ type))
    (property : Ty.denote.{u, w} model.Carrier (type ⇒ .prop)) :
    model.denote (strengthening (Const := Const) type)
      (@parameterValuation Base Const model type zero successor property) =
      (fun number => .up (ClosedUnder model type zero successor number ∧ (property number).down)) :=
  rfl

/-- The particular comprehension needed by induction is supplied by the
model's existing term-closure law, not by all predicates being admitted. -/
theorem strengthening_admitted (model : HenkinModel.{u, v, w} Base Const) (type : Ty Base)
    (zero : Ty.denote.{u, w} model.Carrier type)
    (successor : Ty.denote.{u, w} model.Carrier (type ⇒ type))
    (property : Ty.denote.{u, w} model.Carrier (type ⇒ .prop))
    (zeroAdmitted : model.adm type zero) (successorAdmitted : model.adm (type ⇒ type) successor)
    (propertyAdmitted : model.adm (type ⇒ .prop) property) :
    model.adm (type ⇒ .prop)
      (fun number => .up (ClosedUnder model type zero successor number ∧ (property number).down)) := by
  exact model.denote_admissible
    (@parameterValuation_admissible Base Const model type zero successor property
      zeroAdmitted successorAdmitted propertyAdmitted) (strengthening type)

theorem closedUnder_induction_admitted (model : HenkinModel.{u, v, w} Base Const) (type : Ty Base)
    (zero : Ty.denote.{u, w} model.Carrier type)
    (successor : Ty.denote.{u, w} model.Carrier (type ⇒ type))
    (property : Ty.denote.{u, w} model.Carrier (type ⇒ .prop))
    (zeroAdmitted : model.adm type zero) (successorAdmitted : model.adm (type ⇒ type) successor)
    (propertyAdmitted : model.adm (type ⇒ .prop) property)
    (atZero : (property zero).down)
    (atSuccessor : ∀ number, model.adm type number →
      ClosedUnder model type zero successor number →
        (property number).down → (property (successor number)).down)
    (number : Ty.denote.{u, w} model.Carrier type)
    (closed : ClosedUnder model type zero successor number) : (property number).down := by
  let strengthened : Ty.denote.{u, w} model.Carrier (type ⇒ .prop) :=
    fun previous => .up (ClosedUnder model type zero successor previous ∧ (property previous).down)
  have start : (strengthened zero).down :=
    ⟨closedUnder_zero model type zero successor, atZero⟩
  have step : ∀ previous, model.adm type previous →
      (strengthened previous).down → (strengthened (successor previous)).down := by
    intro previous admitted holds
    exact ⟨closedUnder_successor model type zero successor previous admitted holds.1,
      atSuccessor previous admitted holds.1 holds.2⟩
  exact (closed strengthened
    (strengthening_admitted model type zero successor property
      zeroAdmitted successorAdmitted propertyAdmitted) start step).2

theorem models_induction_henkin (model : HenkinModel.{u, v, w} Base Const) (type : Ty Base) :
    model.models (inductionStatement type) := by
  intro zero zeroAdmitted successor successorAdmitted property propertyAdmitted
    atZero atSuccessor number _ closed
  exact closedUnder_induction_admitted model type zero successor property
    zeroAdmitted successorAdmitted propertyAdmitted atZero atSuccessor number closed

namespace InductionControls

abbrev EmptyConstants : Ty Unit → Type := fun _ => Empty

def carrier : Ty Unit := .base ()
def model : HenkinModel.{0, 0, 0} Unit EmptyConstants :=
  .standard (fun _ => ULift.{1} (Fin 3)) (fun impossible => nomatch impossible)
def zero : Ty.denote.{0, 0} model.Carrier carrier := .up 0
def successor : Ty.denote.{0, 0} model.Carrier (carrier ⇒ carrier) :=
  fun number => .up (if number.down = 0 then 0 else 2)
def property : Ty.denote.{0, 0} model.Carrier (carrier ⇒ .prop) := fun number => .up (number.down ≠ 2)

theorem closed_iff_zero (number : Ty.denote.{0, 0} model.Carrier carrier) :
    ClosedUnder model carrier zero successor number ↔ number = zero := by
  constructor
  · intro closed
    have same := closed (fun previous => .up (previous = zero)) (by trivial) rfl (by
      intro previous _ equality
      subst previous
      rfl)
    exact same
  · rintro rfl
    exact closedUnder_zero model carrier zero successor

theorem guarded_step : ∀ number, model.adm carrier number →
    ClosedUnder model carrier zero successor number →
      (property number).down → (property (successor number)).down := by
  intro number _ closed _
  rw [closed_iff_zero] at closed
  subst number
  change (0 : Fin 3) ≠ 2
  decide +kernel

/-- The unreachable point one satisfies the property but maps to point two,
which does not. The ordinary unguarded step therefore fails. -/
theorem unguarded_step_refused : ¬ ∀ number, model.adm carrier number →
    (property number).down → (property (successor number)).down := by
  intro step
  have atOne : (property (.up 1)).down := by
    change (1 : Fin 3) ≠ 2
    decide +kernel
  have impossible := step (.up 1) (by trivial) atOne
  change (2 : Fin 3) ≠ 2 at impossible
  exact impossible rfl

theorem guarded_induction : ∀ number, ClosedUnder model carrier zero successor number →
    (property number).down := by
  intro number closed
  have atZero : (property zero).down := by
    change (0 : Fin 3) ≠ 2
    decide +kernel
  exact closedUnder_induction_admitted model carrier zero successor property
    (by trivial) (by trivial) (by trivial) atZero guarded_step number closed

end InductionControls

end Mettapedia.Logic.HOL.NaturalClosure

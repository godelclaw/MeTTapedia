import Mettapedia.Logic.HOL.Semantics.ModelProperties

/-!
# The least zero/successor closure in intrinsic HOL

The carrier, zero and successor are parameters. Quantified predicates range
only over the chosen Henkin domains; the strengthened induction comparison
states its full-domain assumption separately. Closure supplies neither
successor injectivity nor separation, recursion or an infinite carrier.

Native proof services reuse this typed syntax and its meaning. Their proof
formats, acceptance and authority remain independent obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.NaturalClosure

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}

/-- The body under the declared number, successor and zero arguments. -/
def declarationBody (type : Ty Base) : Formula Const (type :: (type ⇒ type) :: type :: Γ) :=
  .all (σ := type ⇒ .prop)
    (.imp (.app (.var .vz) (.var (.vs (.vs (.vs .vz)))))
      (.imp (.all (σ := type)
        (.imp (.app (.var (.vs .vz)) (.var .vz))
          (.app (.var (.vs .vz)) (.app (.var (.vs (.vs (.vs .vz)))) (.var .vz)))))
        (.app (.var .vz) (.var (.vs .vz)))))

/-- A closed definition, usable in any context without introducing constants. -/
def body (type : Ty Base) : Term Const Γ (type ⇒ (type ⇒ type) ⇒ type ⇒ .prop) :=
  .lam (.lam (.lam (declarationBody type)))

def predicate {type : Ty Base} (zero : Term Const Γ type)
    (successor : Term Const Γ (type ⇒ type)) (number : Term Const Γ type) :
    Formula Const Γ := .app (.app (.app (body type) zero) successor) number

def zeroStatement (type : Ty Base) : ClosedFormula Const :=
  .all (σ := type) (.all (σ := type ⇒ type)
    (predicate (.var (.vs .vz)) (.var .vz) (.var (.vs .vz))))

def successorStatement (type : Ty Base) : ClosedFormula Const :=
  .all (σ := type) (.all (σ := type ⇒ type) (.all (σ := type)
    (.imp (predicate (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz))
      (predicate (.var (.vs (.vs .vz))) (.var (.vs .vz))
        (.app (.var (.vs .vz)) (.var .vz))))))

def inductionStatement (type : Ty Base) : ClosedFormula Const :=
  .all (σ := type) (.all (σ := type ⇒ type) (.all (σ := type ⇒ .prop)
    (.imp (.app (.var .vz) (.var (.vs (.vs .vz))))
      (.imp (.all (σ := type)
        (.imp (predicate (.var (.vs (.vs (.vs .vz)))) (.var (.vs (.vs .vz))) (.var .vz))
          (.imp (.app (.var (.vs .vz)) (.var .vz))
            (.app (.var (.vs .vz)) (.app (.var (.vs (.vs .vz))) (.var .vz))))))
        (.all (σ := type)
          (.imp (predicate (.var (.vs (.vs (.vs .vz)))) (.var (.vs (.vs .vz))) (.var .vz))
            (.app (.var (.vs .vz)) (.var .vz))))))))

/-- The quantified predicates range over the selected model's admitted domain. -/
def ClosedUnder (model : HenkinModel.{u, v, w} Base Const) (type : Ty Base)
    (zero : Ty.denote model.Carrier type)
    (successor : Ty.denote model.Carrier (type ⇒ type))
    (number : Ty.denote model.Carrier type) : Prop :=
  ∀ property : Ty.denote model.Carrier (type ⇒ .prop),
    model.adm (type ⇒ .prop) property → (property zero).down →
      (∀ previous, model.adm type previous →
        (property previous).down → (property (successor previous)).down) →
      (property number).down

theorem denote_body (model : HenkinModel.{u, v, w} Base Const) (type : Ty Base)
    (valuation : model.Valuation Γ) (zero : Ty.denote model.Carrier type)
    (successor : Ty.denote model.Carrier (type ⇒ type))
    (number : Ty.denote model.Carrier type) :
    (model.denote (body type) valuation zero successor number).down ↔
      ClosedUnder model type zero successor number := Iff.rfl

theorem denote_predicate (model : HenkinModel.{u, v, w} Base Const) {type : Ty Base}
    (valuation : model.Valuation Γ) (zero : Term Const Γ type)
    (successor : Term Const Γ (type ⇒ type)) (number : Term Const Γ type) :
    (model.denote (predicate zero successor number) valuation).down ↔
      ClosedUnder model type (model.denote zero valuation)
        (model.denote successor valuation) (model.denote number valuation) := Iff.rfl

theorem closedUnder_zero (model : HenkinModel.{u, v, w} Base Const) (type : Ty Base)
    (zero : Ty.denote model.Carrier type)
    (successor : Ty.denote model.Carrier (type ⇒ type)) :
    ClosedUnder model type zero successor zero := by
  intro _ _ atZero _
  exact atZero

theorem closedUnder_successor (model : HenkinModel.{u, v, w} Base Const) (type : Ty Base)
    (zero : Ty.denote model.Carrier type)
    (successor : Ty.denote model.Carrier (type ⇒ type))
    (number : Ty.denote model.Carrier type) (admitted : model.adm type number)
    (closed : ClosedUnder model type zero successor number) :
    ClosedUnder model type zero successor (successor number) := by
  intro property propertyAdmitted atZero atSuccessor
  exact atSuccessor number admitted (closed property propertyAdmitted atZero atSuccessor)

/-- Strengthening the induction predicate retains its closure proof. This
semantic comparison uses full domains; the native source proof has no model
parameter or full-domain assumption. -/
theorem closedUnder_induction (model : HenkinModel.{u, v, w} Base Const)
    (full : model.FullDomains) (type : Ty Base) (zero : Ty.denote model.Carrier type)
    (successor : Ty.denote model.Carrier (type ⇒ type))
    (property : Ty.denote model.Carrier (type ⇒ .prop)) (atZero : (property zero).down)
    (atSuccessor : ∀ number, model.adm type number →
      ClosedUnder model type zero successor number →
        (property number).down → (property (successor number)).down)
    (number : Ty.denote model.Carrier type)
    (closed : ClosedUnder model type zero successor number) : (property number).down := by
  let strengthened : Ty.denote model.Carrier (type ⇒ .prop) :=
    fun previous => .up (ClosedUnder model type zero successor previous ∧ (property previous).down)
  have start : (strengthened zero).down :=
    ⟨closedUnder_zero model type zero successor, atZero⟩
  have step : ∀ previous, model.adm type previous →
      (strengthened previous).down → (strengthened (successor previous)).down := by
    intro previous admitted holds
    exact ⟨closedUnder_successor model type zero successor previous admitted holds.1,
      atSuccessor previous admitted holds.1 holds.2⟩
  exact (closed strengthened (full _ _) start step).2

theorem models_zero (model : HenkinModel.{u, v, w} Base Const) (type : Ty Base) :
    model.models (zeroStatement type) := by
  intro zero _ successor _
  exact closedUnder_zero model type zero successor

theorem models_successor (model : HenkinModel.{u, v, w} Base Const) (type : Ty Base) :
    model.models (successorStatement type) := by
  intro zero _ successor _ number admitted closed
  exact closedUnder_successor model type zero successor number admitted closed

theorem models_induction (model : HenkinModel.{u, v, w} Base Const)
    (full : model.FullDomains) (type : Ty Base) :
    model.models (inductionStatement type) := by
  intro zero _ successor _ property _ atZero atSuccessor number _ closed
  exact closedUnder_induction model full type zero successor property atZero atSuccessor number closed

end Mettapedia.Logic.HOL.NaturalClosure

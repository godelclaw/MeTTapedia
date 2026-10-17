import Mettapedia.Languages.MeTTa.HE.HOLContract.Signature
import Mettapedia.Logic.HOL.Semantics.Henkin

/-!
# HE tuples are products

A model of the contract (`ProductModel`) is a Henkin model of the contract
signature in which the base type of a compound non-arrow type is the product
of its components: the carrier of `(T₀ T₁ … Tₙ)` is in bijection with the
carrier of `T₀` times the carrier of `(T₁ … Tₙ)`, the pairing and the two
projections denote that bijection and its components, and the carrier of
`()` has one element.

The laws of products are theorems about every such model, not assumptions:

* binary β and surjective pairing (`fst_pair`, `snd_pair`, `pair_fst_snd`)
  and the uniqueness of the unit (`unit_eq`), together with the HOL sentences
  that state them (`models_fstPairLaw`, `models_sndPairLaw`,
  `models_surjectivePairingLaw`, `models_unitLaw`);
* the carrier of `(T₀ … Tₙ)` is the n-ary product of the denotations of the
  `Tᵢ` (`productEquiv`), so the projection of the `i`-th component of a tuple
  is that component (`project_tuple`) and the tuple of the projections of a
  value is the value (`tuple_project`); for intrinsic terms these are the
  n-ary β and surjective-pairing laws (`denote_projectOf_tupleOf`,
  `denote_tupleOf_projections`).

Products cost nothing: over any carriers of the leaf types and any
interpretation of the declared and application constants there is a model
whose product carriers are the products themselves (`standard`).  The laws are not
consequences of the signature: a standard model whose constants denote
constant functions refutes `∀ a b. FST (a, b) = a`
(`constantModel_not_models_fstPairLaw`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.HOLContract

universe w

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.TypeGrounding
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Logic.HOL

/-- A Henkin model of the contract whose product types are products. -/
structure ProductModel (space : Space) extends HenkinModel.{0, 0, w} Atom (Const space) where
  /-- The carrier of a product is the product of its first component and the
  product of the rest. -/
  split : ∀ (component : Atom) (components : List Atom),
    Carrier (.expression (component :: components)) ≃
      Ty.denote Carrier (.base component) × Carrier (.expression components)
  pair_eq : ∀ (component : Atom) (components : List Atom)
      (left : Ty.denote Carrier (.base component)) (right : Carrier (.expression components)),
    constDen (pairConst space component components) left right =
      (split component components).symm (left, right)
  fst_eq : ∀ (component : Atom) (components : List Atom)
      (value : Carrier (.expression (component :: components))),
    constDen (fstConst space component components) value =
      (split component components value).1
  snd_eq : ∀ (component : Atom) (components : List Atom)
      (value : Carrier (.expression (component :: components))),
    constDen (sndConst space component components) value =
      (split component components value).2
  /-- The empty product has one element. -/
  unit_subsingleton : Subsingleton (Carrier (.expression []))

namespace ProductModel

variable {space : Space} (M : ProductModel.{w} space)

/-! ## Binary laws -/

theorem fst_pair (component : Atom) (components : List Atom)
    (left : Ty.denote M.Carrier (.base component)) (right : M.Carrier (.expression components)) :
    M.constDen (fstConst space component components)
        (M.constDen (pairConst space component components) left right) = left := by
  rw [M.pair_eq, M.fst_eq, Equiv.apply_symm_apply]

theorem snd_pair (component : Atom) (components : List Atom)
    (left : Ty.denote M.Carrier (.base component)) (right : M.Carrier (.expression components)) :
    M.constDen (sndConst space component components)
        (M.constDen (pairConst space component components) left right) = right := by
  rw [M.pair_eq, M.snd_eq, Equiv.apply_symm_apply]

theorem pair_fst_snd (component : Atom) (components : List Atom)
    (value : M.Carrier (.expression (component :: components))) :
    M.constDen (pairConst space component components)
        (M.constDen (fstConst space component components) value)
        (M.constDen (sndConst space component components) value) = value := by
  rw [M.fst_eq, M.snd_eq, M.pair_eq]
  exact (M.split component components).symm_apply_apply value

theorem unit_eq (value : M.Carrier (.expression [])) :
    value = M.constDen (oneConst space) :=
  M.unit_subsingleton.elim _ _

/-! ## The laws as HOL sentences -/

/-- `∀ a b. FST (a, b) = a`. -/
def fstPairLaw (space : Space) (component : Atom) (components : List Atom) :
    ClosedFormula (Const space) :=
  .all (σ := .base component) (.all (σ := productTy components)
    (.eq (.app (.const (fstConst space component components))
        (.app (.app (.const (pairConst space component components)) (.var (.vs .vz)))
          (.var .vz)))
      (.var (.vs .vz))))

/-- `∀ a b. SND (a, b) = b`. -/
def sndPairLaw (space : Space) (component : Atom) (components : List Atom) :
    ClosedFormula (Const space) :=
  .all (σ := .base component) (.all (σ := productTy components)
    (.eq (.app (.const (sndConst space component components))
        (.app (.app (.const (pairConst space component components)) (.var (.vs .vz)))
          (.var .vz)))
      (.var .vz)))

/-- `∀ p. (FST p, SND p) = p`. -/
def surjectivePairingLaw (space : Space) (component : Atom) (components : List Atom) :
    ClosedFormula (Const space) :=
  .all (σ := productTy (component :: components))
    (.eq (.app (.app (.const (pairConst space component components))
          (.app (.const (fstConst space component components)) (.var .vz)))
        (.app (.const (sndConst space component components)) (.var .vz)))
      (.var .vz))

/-- `∀ u. u = one`. -/
def unitLaw (space : Space) : ClosedFormula (Const space) :=
  .all (σ := productTy []) (.eq (.var .vz) (.const (oneConst space)))

theorem models_fstPairLaw (component : Atom) (components : List Atom) :
    M.models (fstPairLaw space component components) := by
  simp only [HenkinModel.models, PreModel.models, fstPairLaw, PreModel.denote_all]
  intro left leftAdmissible right _
  show PreModel.Eqv M.toPreModel (.base component)
    (M.constDen (fstConst space component components)
      (M.constDen (pairConst space component components) left right)) left
  exact (congrArg (fun value => PreModel.Eqv M.toPreModel (.base component) value left)
    (M.fst_pair component components left right)).mpr
    (PreModel.eqv_refl M.toPreModel leftAdmissible)

theorem models_sndPairLaw (component : Atom) (components : List Atom) :
    M.models (sndPairLaw space component components) := by
  simp only [HenkinModel.models, PreModel.models, sndPairLaw, PreModel.denote_all]
  intro left _ right _
  show M.constDen (sndConst space component components)
    (M.constDen (pairConst space component components) left right) = right
  exact M.snd_pair component components left right

theorem models_surjectivePairingLaw (component : Atom) (components : List Atom) :
    M.models (surjectivePairingLaw space component components) := by
  simp only [HenkinModel.models, PreModel.models, surjectivePairingLaw, PreModel.denote_all]
  intro value _
  show M.constDen (pairConst space component components)
      (M.constDen (fstConst space component components) value)
      (M.constDen (sndConst space component components) value) = value
  exact M.pair_fst_snd component components value

theorem models_unitLaw : M.models (unitLaw space) := by
  simp only [HenkinModel.models, PreModel.models, unitLaw, PreModel.denote_all]
  intro value _
  show value = M.constDen (oneConst space)
  exact M.unit_eq value

/-! ## The n-ary product -/

/-- One value at the denotation of each component type. -/
def Values : List Atom → Type (max 1 w)
  | [] => PUnit
  | component :: components => Ty.denote M.Carrier (.base component) × Values components

/-- The tuple of values. -/
def tupleValue : (components : List Atom) → Values M components → M.Carrier (.expression components)
  | [], _ => M.constDen (oneConst space)
  | component :: components, values =>
      (M.split component components).symm (values.1, tupleValue components values.2)

/-- The values of the components of an element of a product. -/
def projectValues : (components : List Atom) → M.Carrier (.expression components) → Values M components
  | [], _ => PUnit.unit
  | component :: components, value =>
      ((M.split component components value).1,
        projectValues components (M.split component components value).2)

theorem projectValues_tupleValue :
    ∀ (components : List Atom) (values : Values M components),
      projectValues M components (tupleValue M components values) = values
  | [], _ => rfl
  | component :: components, values => by
      simp only [tupleValue, projectValues, Equiv.apply_symm_apply]
      rw [projectValues_tupleValue components values.2]
      rfl

theorem tupleValue_projectValues :
    ∀ (components : List Atom) (value : M.Carrier (.expression components)),
      tupleValue M components (projectValues M components value) = value
  | [], _value => (M.unit_eq _value).symm
  | component :: components, value => by
      simp only [tupleValue, projectValues]
      rw [tupleValue_projectValues components]
      exact (M.split component components).symm_apply_apply value

/-- **The carrier of `(T₀ … Tₙ)` is the n-ary product of the denotations of
the `Tᵢ`.** -/
def productEquiv (components : List Atom) :
    M.Carrier (.expression components) ≃ Values M components where
  toFun := projectValues M components
  invFun := tupleValue M components
  left_inv := tupleValue_projectValues M components
  right_inv := projectValues_tupleValue M components

/-- The value at the component `index`. -/
def Values.get : (components : List Atom) → Values M components →
    (index : Fin components.length) → Ty.denote M.Carrier (.base (components.get index))
  | _ :: _, values, ⟨0, _⟩ => values.1
  | _ :: components, values, ⟨index + 1, bound⟩ =>
      Values.get components values.2 ⟨index, Nat.lt_of_succ_lt_succ bound⟩

/-- The `index`-th projection of an element of a product. -/
def projectValue : (components : List Atom) → (index : Fin components.length) →
    M.Carrier (.expression components) → Ty.denote M.Carrier (.base (components.get index))
  | component :: components, ⟨0, _⟩, value => (M.split component components value).1
  | component :: components, ⟨index + 1, bound⟩, value =>
      projectValue components ⟨index, Nat.lt_of_succ_lt_succ bound⟩
        (M.split component components value).2

/-- **n-ary β.**  The `index`-th projection of a tuple is its `index`-th
component. -/
theorem project_tuple :
    ∀ (components : List Atom) (values : Values M components) (index : Fin components.length),
      projectValue M components index (tupleValue M components values) =
        Values.get M components values index
  | _ :: _, values, ⟨0, _⟩ => by
      simp [projectValue, tupleValue, Values.get]
  | _ :: components, values, ⟨index + 1, bound⟩ => by
      simp only [projectValue, tupleValue, Values.get, Equiv.apply_symm_apply]
      exact project_tuple components values.2 ⟨index, Nat.lt_of_succ_lt_succ bound⟩

/-- **n-ary surjective pairing.**  The tuple of the projections of a value is
the value. -/
theorem tuple_project (components : List Atom) (value : M.Carrier (.expression components)) :
    tupleValue M components (projectValues M components value) = value :=
  tupleValue_projectValues M components value

/-- Projections and the components of `projectValues` agree. -/
theorem get_projectValues :
    ∀ (components : List Atom) (value : M.Carrier (.expression components))
      (index : Fin components.length),
      Values.get M components (projectValues M components value) index =
        projectValue M components index value
  | _ :: _, _, ⟨0, _⟩ => rfl
  | _ :: components, _, ⟨index + 1, bound⟩ =>
      get_projectValues components _ ⟨index, Nat.lt_of_succ_lt_succ bound⟩

/-! ## Intrinsic tuples and projections -/

/-- One intrinsic term at each component type. -/
inductive Components (context : Ctx Atom) : List Atom → Type where
  | nil : Components context []
  | cons {component : Atom} {components : List Atom} :
      Term (Const space) context (.base component) → Components context components →
      Components context (component :: components)

/-- The intrinsic tuple `t₀, (t₁, … (tₙ, one))`. -/
def tupleOf {context : Ctx Atom} :
    {components : List Atom} → Components (space := space) context components →
      Term (Const space) context (productTy components)
  | [], .nil => .const (oneConst space)
  | component :: components, .cons term terms =>
      .app (.app (.const (pairConst space component components)) term) (tupleOf terms)

/-- The intrinsic `index`-th projection. -/
def projectOf {context : Ctx Atom} :
    (components : List Atom) → (index : Fin components.length) →
      Term (Const space) context (productTy components) →
        Term (Const space) context (.base (components.get index))
  | component :: components, ⟨0, _⟩, term =>
      .app (.const (fstConst space component components)) term
  | component :: components, ⟨index + 1, bound⟩, term =>
      projectOf components ⟨index, Nat.lt_of_succ_lt_succ bound⟩
        (.app (.const (sndConst space component components)) term)

/-- The denotations of a list of intrinsic terms. -/
def denoteComponents {context : Ctx Atom} (valuation : HenkinModel.Valuation M.toHenkinModel context) :
    {components : List Atom} → Components (space := space) context components →
      Values M components
  | [], .nil => PUnit.unit
  | _ :: _, .cons term terms =>
      (HenkinModel.denote M.toHenkinModel term valuation, denoteComponents valuation terms)

/-- The intrinsic term at the component `index`. -/
def Components.get {context : Ctx Atom} :
    {components : List Atom} → Components (space := space) context components →
      (index : Fin components.length) → Term (Const space) context (.base (components.get index))
  | _ :: _, .cons term _, ⟨0, _⟩ => term
  | _ :: _, .cons _ terms, ⟨index + 1, bound⟩ =>
      Components.get terms ⟨index, Nat.lt_of_succ_lt_succ bound⟩

theorem denote_tupleOf {context : Ctx Atom} (valuation : HenkinModel.Valuation M.toHenkinModel context) :
    ∀ {components : List Atom} (terms : Components (space := space) context components),
      HenkinModel.denote M.toHenkinModel (tupleOf terms) valuation =
        tupleValue M components (denoteComponents M valuation terms)
  | [], .nil => rfl
  | component :: components, .cons term terms => by
      show M.constDen (pairConst space component components)
          (HenkinModel.denote M.toHenkinModel term valuation)
          (HenkinModel.denote M.toHenkinModel (tupleOf terms) valuation) = _
      rw [denote_tupleOf valuation terms]
      exact M.pair_eq component components _ _

theorem denote_projectOf {context : Ctx Atom} (valuation : HenkinModel.Valuation M.toHenkinModel context) :
    ∀ (components : List Atom) (index : Fin components.length)
      (term : Term (Const space) context (productTy components)),
      HenkinModel.denote M.toHenkinModel (projectOf components index term) valuation =
        projectValue M components index (HenkinModel.denote M.toHenkinModel term valuation)
  | component :: components, ⟨0, _⟩, term => by
      show M.constDen (fstConst space component components)
        (HenkinModel.denote M.toHenkinModel term valuation) = _
      exact M.fst_eq component components _
  | component :: components, ⟨index + 1, bound⟩, term => by
      rw [projectOf, denote_projectOf valuation components ⟨index, Nat.lt_of_succ_lt_succ bound⟩]
      show projectValue M components _
          (M.constDen (sndConst space component components)
            (HenkinModel.denote M.toHenkinModel term valuation)) = _
      exact congrArg (projectValue M components _) (M.snd_eq component components _)

theorem get_denoteComponents {context : Ctx Atom}
    (valuation : HenkinModel.Valuation M.toHenkinModel context) :
    ∀ {components : List Atom} (terms : Components (space := space) context components)
      (index : Fin components.length),
      Values.get M components (denoteComponents M valuation terms) index =
        HenkinModel.denote M.toHenkinModel (terms.get index) valuation
  | _ :: _, .cons _ _, ⟨0, _⟩ => rfl
  | _ :: _, .cons _ terms, ⟨index + 1, bound⟩ =>
      get_denoteComponents valuation terms ⟨index, Nat.lt_of_succ_lt_succ bound⟩

/-- **n-ary β for intrinsic terms.**  In every model, under every valuation,
the `index`-th projection of a tuple denotes its `index`-th element. -/
theorem denote_projectOf_tupleOf {context : Ctx Atom}
    (valuation : HenkinModel.Valuation M.toHenkinModel context) {components : List Atom}
    (terms : Components (space := space) context components) (index : Fin components.length) :
    HenkinModel.denote M.toHenkinModel (projectOf components index (tupleOf terms)) valuation =
      HenkinModel.denote M.toHenkinModel (terms.get index) valuation := by
  rw [denote_projectOf, denote_tupleOf, project_tuple, get_denoteComponents]

/-- The projections of a term, one per component. -/
def projections {context : Ctx Atom} :
    (components : List Atom) → Term (Const space) context (productTy components) →
      Components (space := space) context components
  | [], _ => .nil
  | component :: components, term =>
      .cons (.app (.const (fstConst space component components)) term)
        (projections components (.app (.const (sndConst space component components)) term))

theorem denoteComponents_projections {context : Ctx Atom}
    (valuation : HenkinModel.Valuation M.toHenkinModel context) :
    ∀ (components : List Atom) (term : Term (Const space) context (productTy components)),
      denoteComponents M valuation (projections components term) =
        projectValues M components (HenkinModel.denote M.toHenkinModel term valuation)
  | [], _ => rfl
  | component :: components, term => by
      show (HenkinModel.denote M.toHenkinModel
            (.app (.const (fstConst space component components)) term) valuation,
          denoteComponents M valuation (projections components
            (.app (.const (sndConst space component components)) term))) =
        projectValues M (component :: components)
          (HenkinModel.denote M.toHenkinModel term valuation)
      rw [denoteComponents_projections valuation components]
      exact Prod.ext (M.fst_eq component components _)
        (congrArg (projectValues M components) (M.snd_eq component components _))

/-- **n-ary surjective pairing for intrinsic terms.**  In every model, under
every valuation, the tuple of the projections of a term denotes the term. -/
theorem denote_tupleOf_projections {context : Ctx Atom}
    (valuation : HenkinModel.Valuation M.toHenkinModel context) (components : List Atom)
    (term : Term (Const space) context (productTy components)) :
    HenkinModel.denote M.toHenkinModel (tupleOf (projections components term)) valuation =
      HenkinModel.denote M.toHenkinModel term valuation := by
  rw [denote_tupleOf, denoteComponents_projections]
  exact tuple_project M components _

end ProductModel

/-! ## Models with products exist -/

section Standard

variable (leaf : Atom → Type (max 1 w))

mutual

/-- The carrier of a base type in the standard product model: a leaf's own carrier, and the
product of the elements of an expression.  An arrow is a base type of the contract; the
standard model reads it as the product of its elements too, which the contract allows. -/
def baseCarrier : Atom → Type (max 1 w)
  | .symbol name => leaf (.symbol name)
  | .var name => leaf (.var name)
  | .grounded value => leaf (.grounded value)
  | .expression atoms => listCarrier atoms

/-- The product of the carriers of a list of types. -/
def listCarrier : List Atom → Type (max 1 w)
  | [] => PUnit.{max 1 w + 1}
  | atom :: atoms => baseCarrier atom × listCarrier atoms

end

theorem baseCarrier_cons (component : Atom) (components : List Atom) :
    baseCarrier leaf (.expression (component :: components)) =
      (baseCarrier leaf component × baseCarrier leaf (.expression components)) := by
  simp only [baseCarrier, listCarrier]

theorem baseCarrier_nil : baseCarrier leaf (.expression []) = PUnit.{max 1 w + 1} := by
  simp only [baseCarrier, listCarrier]

/-- The standard split of a product carrier. -/
def standardSplit (component : Atom) (components : List Atom) :
    baseCarrier leaf (.expression (component :: components)) ≃
      Ty.denote (baseCarrier leaf) (.base component) × baseCarrier leaf (.expression components) :=
  Equiv.cast (baseCarrier_cons leaf component components)

variable {space : Space}

/-- The standard interpretation of the contract's constants: the declared constants and the
application constants as given, and the pairing, projections and unit of the standard
products. -/
noncomputable def standardConstDen
    (interpret : ∀ (constant : Atom) (occurrence : Nat) (instanceType : Atom),
      Instance space constant occurrence instanceType →
        Ty.denote (baseCarrier leaf) (.base instanceType))
    (interpretApply : ∀ (parameters : List Atom) (result : Atom),
      TypeAtom (arrowAtom parameters result) →
        Ty.denote (baseCarrier leaf) (.arr (.base (arrowAtom parameters result))
          (applyTy parameters result))) :
    {type : Ty Atom} → Const space type → Ty.denote (baseCarrier leaf) type
  | _, ⟨.declared constant occurrence instanceType, lookup⟩ =>
      (nameType_declared_eq_some_iff.mp lookup).2 ▸
        interpret constant occurrence instanceType (nameType_declared_eq_some_iff.mp lookup).1
  | _, ⟨.apply parameters result, lookup⟩ =>
      (nameType_apply_eq_some_iff.mp lookup).2 ▸
        interpretApply parameters result (nameType_apply_eq_some_iff.mp lookup).1
  | _, ⟨.pair (component :: components), lookup⟩ =>
      Option.some.inj lookup ▸ fun left right =>
        (standardSplit leaf component components).symm (left, right)
  | _, ⟨.fst (component :: components), lookup⟩ =>
      Option.some.inj lookup ▸ fun value => (standardSplit leaf component components value).1
  | _, ⟨.snd (component :: components), lookup⟩ =>
      Option.some.inj lookup ▸ fun value => (standardSplit leaf component components value).2
  | _, ⟨.one, lookup⟩ =>
      Option.some.inj lookup ▸ cast (baseCarrier_nil leaf).symm PUnit.unit
  | _, ⟨.pair [], lookup⟩ => absurd lookup (by simp [nameType])
  | _, ⟨.fst [], lookup⟩ => absurd lookup (by simp [nameType])
  | _, ⟨.snd [], lookup⟩ => absurd lookup (by simp [nameType])

/-- **Models with genuine products exist.**  Over any carriers of the leaf types and any
interpretation of the declared and application constants, the standard model, whose product
carriers are the products of their components, is a model of the contract. -/
noncomputable def standard
    (interpret : ∀ (constant : Atom) (occurrence : Nat) (instanceType : Atom),
      Instance space constant occurrence instanceType →
        Ty.denote (baseCarrier leaf) (.base instanceType))
    (interpretApply : ∀ (parameters : List Atom) (result : Atom),
      TypeAtom (arrowAtom parameters result) →
        Ty.denote (baseCarrier leaf) (.arr (.base (arrowAtom parameters result))
          (applyTy parameters result))) :
    ProductModel.{w} space where
  toHenkinModel :=
    HenkinModel.standard (baseCarrier leaf) (standardConstDen leaf interpret interpretApply)
  split := standardSplit leaf
  pair_eq := fun _ _ _ _ => rfl
  fst_eq := fun _ _ _ => rfl
  snd_eq := fun _ _ _ => rfl
  unit_subsingleton := by
    show Subsingleton (baseCarrier leaf (.expression []))
    rw [baseCarrier_nil]
    infer_instance

/-- The standard model interprets every declared constant as given. -/
theorem standard_declared
    (interpret : ∀ (constant : Atom) (occurrence : Nat) (instanceType : Atom),
      Instance space constant occurrence instanceType →
        Ty.denote (baseCarrier leaf) (.base instanceType))
    (interpretApply : ∀ (parameters : List Atom) (result : Atom),
      TypeAtom (arrowAtom parameters result) →
        Ty.denote (baseCarrier leaf) (.arr (.base (arrowAtom parameters result))
          (applyTy parameters result)))
    {constant instanceType : Atom} {occurrence : Nat}
    (isInstance : Instance space constant occurrence instanceType) :
    (standard leaf interpret interpretApply).constDen
        (⟨.declared constant occurrence instanceType,
          nameType_declared_eq_some_iff.mpr ⟨isInstance, rfl⟩⟩ : Const space (.base instanceType)) =
      interpret constant occurrence instanceType isInstance :=
  rfl

end Standard

/-! ## A model of the signature without products -/

section Control

/-- Every base type carries the Booleans. -/
private abbrev boolCarrier : Atom → Type 1 := fun _ => ULift.{1} Bool

/-- A value of every type over the Boolean carriers. -/
private def defaultValue : (type : Ty Atom) → Ty.denote.{0, 0} boolCarrier type
  | .prop => ULift.up True
  | .base _ => ULift.up false
  | .arr _ codomain => fun _ => defaultValue codomain

/-- The standard model over the Boolean carriers in which every constant
denotes a constant function; in particular its first projection ignores the
pair it is applied to. -/
def constantModel (space : Space) : HenkinModel.{0, 0, 0} Atom (Const space) :=
  HenkinModel.standard boolCarrier (fun {type} _ => defaultValue type)

private theorem exists_not_eqv_default (space : Space) :
    ∀ type : Ty Atom, (∃ leaf, type = .base leaf) →
      ∃ value, ¬PreModel.Eqv (constantModel space).toPreModel type (defaultValue type) value := by
  rintro _ ⟨leaf, rfl⟩
  exact ⟨ULift.up true, fun equal => Bool.false_ne_true (congrArg ULift.down equal)⟩

/-- **Negative control.**  `∀ a b. FST (a, b) = a` is not a consequence of
the contract signature: it fails in `constantModel`.  Every model of the
contract satisfies it (`ProductModel.models_fstPairLaw`), so the product
structure of a model is what makes it hold. -/
theorem constantModel_not_models_fstPairLaw (space : Space) :
    ¬(constantModel space).models (ProductModel.fstPairLaw space (.symbol "B") []) := by
  intro law
  simp only [HenkinModel.models, PreModel.models, ProductModel.fstPairLaw,
    PreModel.denote_all] at law
  obtain ⟨value, differs⟩ := exists_not_eqv_default space (.base (.symbol "B")) ⟨.symbol "B", rfl⟩
  exact differs (law value trivial (defaultValue (productTy [])) trivial)

end Control

#print axioms ProductModel.models_fstPairLaw
#print axioms ProductModel.models_sndPairLaw
#print axioms ProductModel.models_surjectivePairingLaw
#print axioms ProductModel.models_unitLaw
#print axioms ProductModel.productEquiv
#print axioms ProductModel.denote_projectOf_tupleOf
#print axioms ProductModel.denote_tupleOf_projections
#print axioms standard
#print axioms standard_declared
#print axioms constantModel_not_models_fstPairLaw

end Mettapedia.Languages.MeTTa.HE.HOLContract

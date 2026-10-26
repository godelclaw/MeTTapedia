import Mettapedia.Logic.HOL.PredicateFixedPoint

/-!
# Predicate lifting from constructor and child relations

The operator selects a constructor layer and requires its complete child
relation to satisfy the input predicate. The retained monotonicity program
uses covariance of that predicate position. Instantiating the existing
least-predicate theorem supplies a pointwise fixed-point proof without an
external monotonicity assumption.

This is a truth-valued lifting. A child relation records its support; repeated
child occurrences require a separate occurrence-preserving observation.
Datatype-specific constructor definitions, representations and recursion are
not provided by the logical schemas.
-/

set_option autoImplicit false
namespace Mettapedia.Logic.HOL.PolynomialPredicate
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
variable {α β : Ty Base}

def children (relation : Term Const Γ (β ⇒ α ⇒ .prop))
    (property : Term Const Γ (α ⇒ .prop)) (layer : Term Const Γ β) : Formula Const Γ :=
  .all (.imp (.app (.app (weaken relation) (weaken layer)) (.var .vz))
    (.app (weaken property) (.var .vz)))

def body (constructor child : Term Const Γ (β ⇒ α ⇒ .prop))
    (property : Term Const Γ (α ⇒ .prop)) (point : Term Const Γ α) : Formula Const Γ :=
  .ex (.and (.app (.app (weaken constructor) (.var .vz)) (weaken point))
    (children (weaken child) (weaken property) (.var .vz)))

def operator (constructor child : Term Const Γ (β ⇒ α ⇒ .prop)) :
    Term Const Γ (PredicateFixedPoint.Operator α) :=
  .lam (.lam (body (weaken (weaken constructor)) (weaken (weaken child))
    (.var (.vs .vz)) (.var .vz)))

@[simp] theorem rename_children {Ξ : Ctx Base} (ρ : Rename Base Γ Ξ)
    (relation : Term Const Γ (β ⇒ α ⇒ .prop))
    (property : Term Const Γ (α ⇒ .prop)) (layer : Term Const Γ β) :
    rename ρ (children relation property layer) =
      children (rename ρ relation) (rename ρ property) (rename ρ layer) := by
  simp [children, rename, Rename.lift]

@[simp] theorem rename_body {Ξ : Ctx Base} (ρ : Rename Base Γ Ξ)
    (constructor child : Term Const Γ (β ⇒ α ⇒ .prop))
    (property : Term Const Γ (α ⇒ .prop)) (point : Term Const Γ α) :
    rename ρ (body constructor child property point) =
      body (rename ρ constructor) (rename ρ child) (rename ρ property) (rename ρ point) := by
  simp [body, rename, Rename.lift]

@[simp] theorem rename_operator {Ξ : Ctx Base} (ρ : Rename Base Γ Ξ)
    (constructor child : Term Const Γ (β ⇒ α ⇒ .prop)) :
    rename ρ (operator constructor child) = operator (rename ρ constructor) (rename ρ child) := by
  simp [operator, rename, Rename.lift]

@[simp] theorem subst_children {Ξ : Ctx Base} (θ : Subst Const Γ Ξ)
    (relation : Term Const Γ (β ⇒ α ⇒ .prop))
    (property : Term Const Γ (α ⇒ .prop)) (layer : Term Const Γ β) :
    subst θ (children relation property layer) =
      children (subst θ relation) (subst θ property) (subst θ layer) := by
  simp [children, subst, Subst.lift]

@[simp] theorem subst_body {Ξ : Ctx Base} (θ : Subst Const Γ Ξ)
    (constructor child : Term Const Γ (β ⇒ α ⇒ .prop))
    (property : Term Const Γ (α ⇒ .prop)) (point : Term Const Γ α) :
    subst θ (body constructor child property point) =
      body (subst θ constructor) (subst θ child) (subst θ property) (subst θ point) := by
  simp [body, subst, Subst.lift]

variable {Δ : List (Formula Const Γ)}

def operator_beta (constructor child : Term Const Γ (β ⇒ α ⇒ .prop))
    (property : Term Const Γ (α ⇒ .prop)) (point : Term Const Γ α) :
    ProofSyntax Const Δ (.eq (.app (.app (operator constructor child) property) point)
      (body constructor child property point)) := by
  have first : ProofSyntax Const Δ (.eq (.app (.app (operator constructor child) property) point)
      (.app (.lam (body (weaken constructor) (weaken child) (weaken property) (.var .vz))) point)) := by
    apply ProofSyntax.castIndices rfl ?_
      (ProofSyntax.eqApp point (ProofSyntax.beta property
        (.lam (body (weaken (weaken constructor)) (weaken (weaken child))
          (.var (.vs .vz)) (.var .vz)))))
    simp [operator, instantiate, subst, Subst.lift, Subst.single]
    rfl
  have second : ProofSyntax Const Δ
      (.eq (.app (.lam (body (weaken constructor) (weaken child) (weaken property) (.var .vz))) point)
        (body constructor child property point)) := by
    apply ProofSyntax.castIndices rfl ?_
      (ProofSyntax.beta point (body (weaken constructor) (weaken child) (weaken property) (.var .vz)))
    simp [instantiate, subst, Subst.single]
  exact .eqTrans first second

def children_monotone (relation : Term Const Γ (β ⇒ α ⇒ .prop))
    (first second : Term Const Γ (α ⇒ .prop)) (layer : Term Const Γ β)
    (inclusion : ProofSyntax Const Δ (PredicateFixedPoint.included first second)) :
    ProofSyntax Const Δ (.imp (children relation first layer) (children relation second layer)) := by
  refine .impI (.allI (.impI ?_))
  let premise : Formula Const (α :: Γ) :=
    .app (.app (weaken relation) (weaken layer)) (.var .vz)
  let assumptions := premise :: weakenHyps (children relation first layer :: Δ)
  have included : ProofSyntax Const assumptions
      (PredicateFixedPoint.included (weaken first) (weaken second)) := by
    apply ProofSyntax.castIndices rfl ?_
      (((PredicateFixedPoint.weakenProof (inclusion.prepend (children relation first layer))).prepend premise))
    simp [weaken, PredicateFixedPoint.rename_included]
  have universal : ProofSyntax Const assumptions (children (weaken relation) (weaken first) (weaken layer)) := by
    apply ProofSyntax.castIndices rfl ?_
      (ProofSyntax.hyp (Const := Const) (Δ := assumptions) ⟨1, by simp [assumptions, weakenHyps]⟩)
    simp [assumptions, weakenHyps, weaken, rename_children]
  have guarded : ProofSyntax Const assumptions
      (.imp premise (.app (weaken first) (.var .vz))) := by
    apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.allE (.var .vz) universal)
    simp [premise, instantiate, subst, Subst.single]
  exact PredicateFixedPoint.inclusion_elim (weaken first) (weaken second) (.var .vz)
    included (.impE guarded (.hyp ⟨0, by simp⟩))

def body_monotone (constructor child : Term Const Γ (β ⇒ α ⇒ .prop))
    (first second : Term Const Γ (α ⇒ .prop)) (point : Term Const Γ α)
    (inclusion : ProofSyntax Const Δ (PredicateFixedPoint.included first second)) :
    ProofSyntax Const Δ (.imp (body constructor child first point) (body constructor child second point)) := by
  refine .impI (.exE (.hyp ⟨0, by simp⟩) ?_)
  let premise : Formula Const (β :: Γ) :=
    .and (.app (.app (weaken constructor) (.var .vz)) (weaken point))
      (children (weaken child) (weaken first) (.var .vz))
  let assumptions := premise :: weakenHyps (body constructor child first point :: Δ)
  have included : ProofSyntax Const assumptions
      (PredicateFixedPoint.included (weaken first) (weaken second)) := by
    apply ProofSyntax.castIndices rfl ?_
      ((PredicateFixedPoint.weakenProof (inclusion.prepend (body constructor child first point))).prepend premise)
    simp [weaken, PredicateFixedPoint.rename_included]
  have pair : ProofSyntax Const assumptions premise := .hyp ⟨0, by simp [assumptions]⟩
  have mapped : ProofSyntax Const assumptions
      (children (weaken child) (weaken second) (.var .vz)) :=
    .impE (children_monotone (weaken child) (weaken first) (weaken second) (.var .vz) included)
      (.andER pair)
  have result : ProofSyntax Const assumptions
      (body (weaken constructor) (weaken child) (weaken second) (weaken point)) := by
    refine .exI (.var .vz) ?_
    apply ProofSyntax.castIndices rfl ?_ (.andI (.andEL pair) mapped)
    simp [instantiate, subst, Subst.single]
  apply ProofSyntax.castIndices rfl ?_ result
  simp [weaken, rename_body]

def operator_monotone (constructor child : Term Const Γ (β ⇒ α ⇒ .prop)) :
    ProofSyntax Const Δ (PredicateFixedPoint.monotone (operator constructor child)) := by
  refine .allI (.allI (.impI (.allI (.impI ?_))))
  let raisedConstructor : Term Const (α :: (α ⇒ .prop) :: (α ⇒ .prop) :: Γ) (β ⇒ α ⇒ .prop) :=
    weaken (weaken (weaken constructor))
  let raisedChild : Term Const (α :: (α ⇒ .prop) :: (α ⇒ .prop) :: Γ) (β ⇒ α ⇒ .prop) :=
    weaken (weaken (weaken child))
  let first : Term Const (α :: (α ⇒ .prop) :: (α ⇒ .prop) :: Γ) (α ⇒ .prop) := .var (.vs (.vs .vz))
  let second : Term Const (α :: (α ⇒ .prop) :: (α ⇒ .prop) :: Γ) (α ⇒ .prop) := .var (.vs .vz)
  let point : Term Const (α :: (α ⇒ .prop) :: (α ⇒ .prop) :: Γ) α := .var .vz
  let assumptions :=
    .app (.app (operator raisedConstructor raisedChild) first) point ::
      PredicateFixedPoint.included first second ::
        weakenHyps (σ := α) (weakenHyps (σ := α ⇒ .prop) (weakenHyps (σ := α ⇒ .prop) Δ))
  have inclusion : ProofSyntax Const assumptions (PredicateFixedPoint.included first second) :=
    .hyp ⟨1, by simp [assumptions]⟩
  have present : ProofSyntax Const assumptions
      (.app (.app (operator raisedConstructor raisedChild) first) point) :=
    .hyp ⟨0, by simp [assumptions]⟩
  have transformed := ProofSyntax.impE (body_monotone raisedConstructor raisedChild first second point inclusion)
    (.impE (.eqPropEL (operator_beta raisedConstructor raisedChild first point)) present)
  have result := ProofSyntax.impE (.eqPropER (operator_beta raisedConstructor raisedChild second point)) transformed
  apply ProofSyntax.castIndices ?_ ?_ result
  · simp [assumptions, PredicateFixedPoint.included, raisedConstructor, raisedChild,
      first, second, point, weakenHyps, weaken, rename_operator, rename, Rename.lift, Rename.weaken]
  · simp [raisedConstructor, raisedChild, second, point,
      weaken, rename_operator, rename, Rename.weaken]

set_option backward.isDefEq.respectTransparency false in
theorem operator_monotone_functionExtensionalityFree
    (constructor child : Term Const Γ (β ⇒ α ⇒ .prop)) :
    ProofSyntax.FunctionExtensionalityFree (operator_monotone (Δ := Δ) constructor child) := by
  simp [operator_monotone, body_monotone, children_monotone, operator_beta,
    PredicateFixedPoint.inclusion_elim, PredicateFixedPoint.weakenProof,
    ProofSyntax.prepend, ProofSyntax.FunctionExtensionalityFree]

def monotonicity_schema (source layer : Ty Base) :
    ProofSyntax Const ([] : List (Formula Const []))
      (.all (.all (PredicateFixedPoint.monotone
        (operator (α := source) (β := layer) (.var (.vs .vz)) (.var .vz))))) :=
  .allI (.allI (operator_monotone (.var (.vs .vz)) (.var .vz)))

def fixed_point_schema (source layer : Ty Base) :
    ProofSyntax Const ([] : List (Formula Const []))
      (.all (.all (PredicateFixedPoint.equation
        (operator (α := source) (β := layer) (.var (.vs .vz)) (.var .vz))))) := by
  refine .allI (.allI ?_)
  let op : Term Const [layer ⇒ source ⇒ .prop, layer ⇒ source ⇒ .prop]
      (PredicateFixedPoint.Operator source) := operator (.var (.vs .vz)) (.var .vz)
  have rule : ProofSyntax Const ([] : List (Formula Const [layer ⇒ source ⇒ .prop, layer ⇒ source ⇒ .prop]))
      (.imp (PredicateFixedPoint.monotone op) (PredicateFixedPoint.equation op)) := by
    apply ProofSyntax.castIndices rfl ?_
      (ProofSyntax.allE op
        (PredicateFixedPoint.weakenProof (σ := layer ⇒ source ⇒ .prop)
          (PredicateFixedPoint.weakenProof (σ := layer ⇒ source ⇒ .prop)
            (PredicateFixedPoint.fixed_point_schema (Const := Const) source))))
    simp [PredicateFixedPoint.monotone, PredicateFixedPoint.equation,
      instantiate, subst, Subst.lift, Subst.single, weaken, rename, Rename.lift, Rename.weaken]
  exact .impE rule (operator_monotone (.var (.vs .vz)) (.var .vz))

set_option backward.isDefEq.respectTransparency false in
theorem monotonicity_schema_functionExtensionalityFree (source layer : Ty Base) :
    ProofSyntax.FunctionExtensionalityFree (monotonicity_schema (Const := Const) source layer) := by
  simp [monotonicity_schema, ProofSyntax.FunctionExtensionalityFree,
    operator_monotone_functionExtensionalityFree]

set_option backward.isDefEq.respectTransparency false in
theorem fixed_point_schema_functionExtensionalityFree (source layer : Ty Base) :
    ProofSyntax.FunctionExtensionalityFree (fixed_point_schema (Const := Const) source layer) := by
  simp [fixed_point_schema, PredicateFixedPoint.weakenProof,
    ProofSyntax.FunctionExtensionalityFree,
    PredicateFixedPoint.fixed_point_schema_functionExtensionalityFree,
    operator_monotone_functionExtensionalityFree]

#print axioms children_monotone
#print axioms body_monotone
#print axioms operator_beta
#print axioms operator_monotone
#print axioms operator_monotone_functionExtensionalityFree
#print axioms fixed_point_schema
#print axioms fixed_point_schema_functionExtensionalityFree
end Mettapedia.Logic.HOL.PolynomialPredicate

/-! Constructor and child relations can be defined from typed operations and
explicit layer/position guards. These lambda bodies add no constructor law
and require no relation constant as an additional primitive. -/

namespace Mettapedia.Logic.HOL.PolynomialPredicate.Relations
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
variable {α β ι : Ty Base}

def constructorBody (valid : Term Const Γ (β ⇒ .prop)) (build : Term Const Γ (β ⇒ α))
    (layer : Term Const Γ β) (point : Term Const Γ α) : Formula Const Γ :=
  .and (.app valid layer) (.eq point (.app build layer))

def constructorRelation (valid : Term Const Γ (β ⇒ .prop)) (build : Term Const Γ (β ⇒ α)) :
    Term Const Γ (β ⇒ α ⇒ .prop) :=
  .lam (.lam (constructorBody (weaken (weaken valid)) (weaken (weaken build))
    (.var (.vs .vz)) (.var .vz)))

def childBody (valid : Term Const Γ (β ⇒ ι ⇒ .prop)) (childAt : Term Const Γ (β ⇒ ι ⇒ α))
    (layer : Term Const Γ β) (point : Term Const Γ α) : Formula Const Γ :=
  .ex (.and (.app (.app (weaken valid) (weaken layer)) (.var .vz))
    (.eq (weaken point) (.app (.app (weaken childAt) (weaken layer)) (.var .vz))))

def childRelation (valid : Term Const Γ (β ⇒ ι ⇒ .prop)) (childAt : Term Const Γ (β ⇒ ι ⇒ α)) :
    Term Const Γ (β ⇒ α ⇒ .prop) :=
  .lam (.lam (childBody (weaken (weaken valid)) (weaken (weaken childAt))
    (.var (.vs .vz)) (.var .vz)))

@[simp] theorem rename_constructorBody {Ξ : Ctx Base} (ρ : Rename Base Γ Ξ)
    (valid : Term Const Γ (β ⇒ .prop)) (build : Term Const Γ (β ⇒ α))
    (layer : Term Const Γ β) (point : Term Const Γ α) :
    rename ρ (constructorBody valid build layer point) = constructorBody
      (rename ρ valid) (rename ρ build) (rename ρ layer) (rename ρ point) := rfl

@[simp] theorem rename_childBody {Ξ : Ctx Base} (ρ : Rename Base Γ Ξ)
    (valid : Term Const Γ (β ⇒ ι ⇒ .prop)) (childAt : Term Const Γ (β ⇒ ι ⇒ α))
    (layer : Term Const Γ β) (point : Term Const Γ α) :
    rename ρ (childBody valid childAt layer point) = childBody
      (rename ρ valid) (rename ρ childAt) (rename ρ layer) (rename ρ point) := by
  simp [childBody, rename, Rename.lift]

@[simp] theorem subst_constructorBody {Ξ : Ctx Base} (θ : Subst Const Γ Ξ)
    (valid : Term Const Γ (β ⇒ .prop)) (build : Term Const Γ (β ⇒ α))
    (layer : Term Const Γ β) (point : Term Const Γ α) :
    subst θ (constructorBody valid build layer point) = constructorBody
      (subst θ valid) (subst θ build) (subst θ layer) (subst θ point) := rfl

@[simp] theorem subst_childBody {Ξ : Ctx Base} (θ : Subst Const Γ Ξ)
    (valid : Term Const Γ (β ⇒ ι ⇒ .prop)) (childAt : Term Const Γ (β ⇒ ι ⇒ α))
    (layer : Term Const Γ β) (point : Term Const Γ α) :
    subst θ (childBody valid childAt layer point) = childBody
      (subst θ valid) (subst θ childAt) (subst θ layer) (subst θ point) := by
  simp [childBody, subst, Subst.lift]

variable {Δ : List (Formula Const Γ)}

def constructor_beta (valid : Term Const Γ (β ⇒ .prop)) (build : Term Const Γ (β ⇒ α))
    (layer : Term Const Γ β) (point : Term Const Γ α) :
    ProofSyntax Const Δ (.eq (.app (.app (constructorRelation valid build) layer) point)
      (constructorBody valid build layer point)) := by
  have first : ProofSyntax Const Δ (.eq (.app (.app (constructorRelation valid build) layer) point)
      (.app (.lam (constructorBody (weaken valid) (weaken build) (weaken layer) (.var .vz))) point)) := by
    apply ProofSyntax.castIndices rfl ?_
      (ProofSyntax.eqApp point (ProofSyntax.beta layer
        (.lam (constructorBody (weaken (weaken valid)) (weaken (weaken build))
          (.var (.vs .vz)) (.var .vz)))))
    simp [constructorRelation, constructorBody, instantiate, subst, Subst.lift, Subst.single]
    rfl
  have second : ProofSyntax Const Δ
      (.eq (.app (.lam (constructorBody (weaken valid) (weaken build) (weaken layer) (.var .vz))) point)
        (constructorBody valid build layer point)) := by
    apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.beta point
      (constructorBody (weaken valid) (weaken build) (weaken layer) (.var .vz)))
    simp [instantiate, subst, Subst.single]
  exact .eqTrans first second

def child_beta (valid : Term Const Γ (β ⇒ ι ⇒ .prop)) (childAt : Term Const Γ (β ⇒ ι ⇒ α))
    (layer : Term Const Γ β) (point : Term Const Γ α) :
    ProofSyntax Const Δ (.eq (.app (.app (childRelation valid childAt) layer) point)
      (childBody valid childAt layer point)) := by
  have first : ProofSyntax Const Δ (.eq (.app (.app (childRelation valid childAt) layer) point)
      (.app (.lam (childBody (weaken valid) (weaken childAt) (weaken layer) (.var .vz))) point)) := by
    apply ProofSyntax.castIndices rfl ?_
      (ProofSyntax.eqApp point (ProofSyntax.beta layer
        (.lam (childBody (weaken (weaken valid)) (weaken (weaken childAt))
          (.var (.vs .vz)) (.var .vz)))))
    simp [childRelation, instantiate, subst, Subst.lift, Subst.single]
    rfl
  have second : ProofSyntax Const Δ
      (.eq (.app (.lam (childBody (weaken valid) (weaken childAt) (weaken layer) (.var .vz))) point)
        (childBody valid childAt layer point)) := by
    apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.beta point
      (childBody (weaken valid) (weaken childAt) (weaken layer) (.var .vz)))
    simp [instantiate, subst, Subst.single]
  exact .eqTrans first second

set_option backward.isDefEq.respectTransparency false in
theorem constructor_beta_functionExtensionalityFree
    (valid : Term Const Γ (β ⇒ .prop)) (build : Term Const Γ (β ⇒ α))
    (layer : Term Const Γ β) (point : Term Const Γ α) :
    ProofSyntax.FunctionExtensionalityFree (constructor_beta (Δ := Δ) valid build layer point) := by
  simp [constructor_beta, ProofSyntax.FunctionExtensionalityFree]

set_option backward.isDefEq.respectTransparency false in
theorem child_beta_functionExtensionalityFree
    (valid : Term Const Γ (β ⇒ ι ⇒ .prop)) (childAt : Term Const Γ (β ⇒ ι ⇒ α))
    (layer : Term Const Γ β) (point : Term Const Γ α) :
    ProofSyntax.FunctionExtensionalityFree (child_beta (Δ := Δ) valid childAt layer point) := by
  simp [child_beta, ProofSyntax.FunctionExtensionalityFree]


/-- A closed higher-order definition body. Operations remain explicit arguments. -/
def constructorDefinition (source layer : Ty Base) : ClosedTerm Const
    ((layer ⇒ .prop) ⇒ (layer ⇒ source) ⇒ layer ⇒ source ⇒ .prop) :=
  .lam (.lam (constructorRelation (.var (.vs .vz)) (.var .vz)))

def childDefinition (source layer position : Ty Base) : ClosedTerm Const
    ((layer ⇒ position ⇒ .prop) ⇒ (layer ⇒ position ⇒ source) ⇒ layer ⇒ source ⇒ .prop) :=
  .lam (.lam (childRelation (.var (.vs .vz)) (.var .vz)))

#print axioms constructor_beta
#print axioms child_beta
#print axioms constructor_beta_functionExtensionalityFree
#print axioms child_beta_functionExtensionalityFree
end Mettapedia.Logic.HOL.PolynomialPredicate.Relations

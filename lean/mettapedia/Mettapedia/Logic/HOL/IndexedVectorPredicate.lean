import Mettapedia.Logic.HOL.PredicatePair
import Mettapedia.Logic.HOL.PositivePredicate
import Mettapedia.Logic.HOL.PredicateFixedPointInduction

/-!
# Constructed length-indexed vector membership

The least predicate ranges over encoded index/value pairs. Its nil clause
keeps the zero index, and its cons clause retains the predecessor, element
guard and recursive tail membership. Constructor operations are parameters;
monotonicity and induction are generated from the positive operator.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.IndexedVectorPredicate
universe u v
variable {Base : Type u} {Const : Ty Base → Type v}

structure Signature (Const : Ty Base → Type v) where
  number : Ty Base
  element : Ty Base
  vector : Ty Base
  zero : ClosedTerm Const number
  successor : ClosedTerm Const (number ⇒ number)
  nil : ClosedTerm Const vector
  cons : ClosedTerm Const (number ⇒ element ⇒ vector ⇒ vector)

namespace Signature
variable (signature : Signature Const) {Γ Ξ : Ctx Base}

abbrev Point := PredicatePair.Pair signature.number signature.vector
abbrev Property := PredicatePair.Relation signature.number signature.vector

def consValue (index : Term Const Γ signature.number) (head : Term Const Γ signature.element)
    (tail : Term Const Γ signature.vector) : Term Const Γ signature.vector :=
  .app (.app (.app (weakenCtx Γ signature.cons) index) head) tail

def consBody (elements : Term Const Γ (signature.element ⇒ .prop))
    (predicate : Term Const Γ (signature.Point ⇒ .prop)) (point : Term Const Γ signature.Point)
    (index : Term Const Γ signature.number) (head : Term Const Γ signature.element)
    (tail : Term Const Γ signature.vector) : Formula Const Γ :=
  .and (.app elements head) (.and (.app predicate (PredicatePair.pair index tail))
    (.eq point (PredicatePair.pair (.app (weakenCtx Γ signature.successor) index)
      (signature.consValue index head tail))))

def consClause (elements : Term Const Γ (signature.element ⇒ .prop))
    (predicate : Term Const Γ (signature.Point ⇒ .prop)) (point : Term Const Γ signature.Point) : Formula Const Γ :=
  .ex (σ := signature.number) (.ex (σ := signature.element) (.ex (σ := signature.vector)
    (signature.consBody (weaken (weaken (weaken elements))) (weaken (weaken (weaken predicate)))
      (weaken (weaken (weaken point))) (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz))))

def tailClause (elements : Term Const Γ (signature.element ⇒ .prop))
    (predicate : Term Const Γ (signature.Point ⇒ .prop)) (point : Term Const Γ signature.Point)
    (index : Term Const Γ signature.number) (head : Term Const Γ signature.element) : Formula Const Γ :=
  .ex (σ := signature.vector) (signature.consBody (weaken elements) (weaken predicate) (weaken point)
    (weaken index) (weaken head) (.var .vz))

def headClause (elements : Term Const Γ (signature.element ⇒ .prop))
    (predicate : Term Const Γ (signature.Point ⇒ .prop)) (point : Term Const Γ signature.Point)
    (index : Term Const Γ signature.number) : Formula Const Γ :=
  .ex (σ := signature.element) (signature.tailClause (weaken elements) (weaken predicate)
    (weaken point) (weaken index) (.var .vz))

def layer (elements : Term Const Γ (signature.element ⇒ .prop))
    (predicate : Term Const Γ (signature.Point ⇒ .prop)) (point : Term Const Γ signature.Point) : Formula Const Γ :=
  .or (.eq point (PredicatePair.pair (weakenCtx Γ signature.zero) (weakenCtx Γ signature.nil)))
    (signature.consClause elements predicate point)

def code (elements : Term Const Γ (signature.element ⇒ .prop)) :
    PositivePredicate.Code Const signature.Point (signature.Point :: Γ) :=
  .disj (.atom (.eq (.var .vz) (PredicatePair.pair (weakenCtx _ signature.zero) (weakenCtx _ signature.nil))))
    (.ex (domain := signature.number) (.ex (domain := signature.element) (.ex (domain := signature.vector)
      (.conj (.atom (.app (weaken (weaken (weaken (weaken elements)))) (.var (.vs .vz))))
        (.conj (.member (PredicatePair.pair (.var (.vs (.vs .vz))) (.var .vz)))
          (.atom (.eq (.var (.vs (.vs (.vs .vz))))
            (PredicatePair.pair (.app (weakenCtx _ signature.successor) (.var (.vs (.vs .vz))))
              (signature.consValue (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz))))))))))

def operator (elements : Term Const Γ (signature.element ⇒ .prop)) := (signature.code elements).operator
def least (elements : Term Const Γ (signature.element ⇒ .prop)) := PredicateFixedPoint.least (signature.operator elements)
def member (elements : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (value : Term Const Γ signature.vector) : Formula Const Γ :=
  .app (signature.least elements) (PredicatePair.pair index value)

@[simp] theorem subst_consValue (substitution : Subst Const Γ Ξ)
    (index : Term Const Γ signature.number) (head : Term Const Γ signature.element) (tail : Term Const Γ signature.vector) :
    subst substitution (signature.consValue index head tail) =
      signature.consValue (subst substitution index) (subst substitution head) (subst substitution tail) := by
  simp [consValue, subst, subst_weakenCtx]

@[simp] theorem subst_consBody (substitution : Subst Const Γ Ξ)
    (elements : Term Const Γ (signature.element ⇒ .prop)) (predicate : Term Const Γ (signature.Point ⇒ .prop))
    (point : Term Const Γ signature.Point) (index : Term Const Γ signature.number)
    (head : Term Const Γ signature.element) (tail : Term Const Γ signature.vector) :
    subst substitution (signature.consBody elements predicate point index head tail) =
      signature.consBody (subst substitution elements) (subst substitution predicate) (subst substitution point)
        (subst substitution index) (subst substitution head) (subst substitution tail) := by
  simp [consBody, subst, PredicatePair.subst_pair, subst_weakenCtx]

@[simp] theorem subst_consClause (substitution : Subst Const Γ Ξ)
    (elements : Term Const Γ (signature.element ⇒ .prop)) (predicate : Term Const Γ (signature.Point ⇒ .prop))
    (point : Term Const Γ signature.Point) :
    subst substitution (signature.consClause elements predicate point) =
      signature.consClause (subst substitution elements) (subst substitution predicate) (subst substitution point) := by
  simp [consClause, subst, subst_consBody, subst_weaken, Subst.lift, Rename.weaken]

@[simp] theorem code_subst (substitution : Subst Const Γ Ξ) (elements : Term Const Γ (signature.element ⇒ .prop)) :
    (signature.code elements).subst (Subst.lift substitution) = signature.code (subst substitution elements) := by
  simp [code, PositivePredicate.Code.subst, subst, subst_weaken, subst_weakenCtx,
    PredicatePair.subst_pair, Subst.lift, Rename.weaken]

theorem body_eq_layer (elements : Term Const Γ (signature.element ⇒ .prop))
    (predicate : Term Const Γ (signature.Point ⇒ .prop)) (point : Term Const Γ signature.Point) :
    (signature.code elements).body predicate point = signature.layer elements predicate point := by
  simp [code, PositivePredicate.Code.body, PositivePredicate.Code.subst, PositivePredicate.Code.interpret,
    layer, consClause, consBody, subst, subst_weaken, PredicatePair.subst_pair,
    Subst.lift, Subst.single, Rename.weaken]
  simp [weaken, rename_comp, Rename.weaken]

@[simp] theorem subst_operator (substitution : Subst Const Γ Ξ) (elements : Term Const Γ (signature.element ⇒ .prop)) :
    subst substitution (signature.operator elements) = signature.operator (subst substitution elements) := by
  rw [operator, ← PositivePredicate.Code.operator_subst, code_subst]
  rfl

@[simp] theorem rename_operator (rho : Rename Base Γ Ξ) (elements : Term Const Γ (signature.element ⇒ .prop)) :
    rename rho (signature.operator elements) = signature.operator (rename rho elements) := by
  simpa only [subst_ofRename] using signature.subst_operator (Subst.ofRename rho) elements

@[simp] theorem subst_least (substitution : Subst Const Γ Ξ) (elements : Term Const Γ (signature.element ⇒ .prop)) :
    subst substitution (signature.least elements) = signature.least (subst substitution elements) := by
  simp [least, PredicateFixedPoint.subst_least]

@[simp] theorem rename_least (rho : Rename Base Γ Ξ) (elements : Term Const Γ (signature.element ⇒ .prop)) :
    rename rho (signature.least elements) = signature.least (rename rho elements) := by
  simpa only [subst_ofRename] using signature.subst_least (Subst.ofRename rho) elements

@[simp] theorem subst_member (substitution : Subst Const Γ Ξ) (elements : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (value : Term Const Γ signature.vector) :
    subst substitution (signature.member elements index value) =
      signature.member (subst substitution elements) (subst substitution index) (subst substitution value) := by
  simp [member, least, subst, PredicateFixedPoint.subst_least, PredicatePair.subst_pair]

@[simp] theorem rename_member (rho : Rename Base Γ Ξ) (elements : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (value : Term Const Γ signature.vector) :
    rename rho (signature.member elements index value) =
      signature.member (rename rho elements) (rename rho index) (rename rho value) := by
  simpa only [subst_ofRename] using signature.subst_member (Subst.ofRename rho) elements index value

def stepBody (elements : Term Const Γ (signature.element ⇒ .prop)) (property : Term Const Γ signature.Property)
    (index : Term Const Γ signature.number) (head : Term Const Γ signature.element) (tail : Term Const Γ signature.vector) :
    Formula Const Γ :=
  .imp (.app elements head) (.imp (signature.member elements index tail)
    (.imp (PredicatePair.holds property index tail)
      (PredicatePair.holds property (.app (weakenCtx Γ signature.successor) index)
        (signature.consValue index head tail))))

def stepCondition (elements : Term Const Γ (signature.element ⇒ .prop)) (property : Term Const Γ signature.Property) :
    Formula Const Γ :=
  .all (σ := signature.number) (.all (σ := signature.element) (.all (σ := signature.vector)
    (signature.stepBody (weaken (weaken (weaken elements))) (weaken (weaken (weaken property)))
      (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz))))

@[simp] theorem subst_stepBody (substitution : Subst Const Γ Ξ)
    (elements : Term Const Γ (signature.element ⇒ .prop)) (property : Term Const Γ signature.Property)
    (index : Term Const Γ signature.number) (head : Term Const Γ signature.element) (tail : Term Const Γ signature.vector) :
    subst substitution (signature.stepBody elements property index head tail) =
      signature.stepBody (subst substitution elements) (subst substitution property)
        (subst substitution index) (subst substitution head) (subst substitution tail) := by
  simp [stepBody, subst, PredicatePair.subst_holds, subst_weakenCtx]

@[simp] theorem subst_stepCondition (substitution : Subst Const Γ Ξ)
    (elements : Term Const Γ (signature.element ⇒ .prop)) (property : Term Const Γ signature.Property) :
    subst substitution (signature.stepCondition elements property) =
      signature.stepCondition (subst substitution elements) (subst substitution property) := by
  simp [stepCondition, subst, subst_stepBody, subst_weaken, Subst.lift, Rename.weaken]

@[simp] theorem rename_stepCondition (rho : Rename Base Γ Ξ)
    (elements : Term Const Γ (signature.element ⇒ .prop)) (property : Term Const Γ signature.Property) :
    rename rho (signature.stepCondition elements property) =
      signature.stepCondition (rename rho elements) (rename rho property) := by
  simpa only [subst_ofRename] using signature.subst_stepCondition (Subst.ofRename rho) elements property

variable {Δ : List (Formula Const Γ)}

def operator_layer (elements : Term Const Γ (signature.element ⇒ .prop))
    (predicate : Term Const Γ (signature.Point ⇒ .prop)) (point : Term Const Γ signature.Point) :
    ProofSyntax Const Δ (.eq (.app (.app (signature.operator elements) predicate) point)
      (signature.layer elements predicate point)) :=
  ProofSyntax.castIndices rfl (congrArg (Term.eq (.app (.app (signature.operator elements) predicate) point))
    (signature.body_eq_layer elements predicate point)) ((signature.code elements).operator_beta predicate point)

def fold (elements : Term Const Γ (signature.element ⇒ .prop)) (point : Term Const Γ signature.Point)
    (constructed : ProofSyntax Const Δ (signature.layer elements (signature.least elements) point)) :
    ProofSyntax Const Δ (.app (signature.least elements) point) :=
  PredicateFixedPoint.closure_at _ point (signature.code elements).operator_monotone
    (.impE (.eqPropER (signature.operator_layer elements (signature.least elements) point)) constructed)

def nil_member (elements : Term Const Γ (signature.element ⇒ .prop)) :
    ProofSyntax Const Δ (signature.member elements (weakenCtx Γ signature.zero) (weakenCtx Γ signature.nil)) :=
  signature.fold elements _ (.orIL (.eqRefl _))

/-- Every member has an actual constructor layer, including its index and
recursive membership evidence. This is the converse of `fold`. -/
def unfold_member (elements : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (value : Term Const Γ signature.vector)
    (present : ProofSyntax Const Δ (signature.member elements index value)) :
    ProofSyntax Const Δ (signature.layer elements (signature.least elements) (PredicatePair.pair index value)) :=
  .impE (.eqPropEL (signature.operator_layer elements (signature.least elements) (PredicatePair.pair index value)))
    (PredicateFixedPoint.inclusion_elim _ _ (PredicatePair.pair index value)
      (PredicateFixedPoint.least_postfixed (signature.operator elements) (signature.code elements).operator_monotone)
      present)

private theorem subst_vars {carrier : Ty Base} (term : Term Const Γ carrier) :
    subst (fun {type} (index : Var Γ type) => Term.var index) term = term := HOL.subst_id term

private theorem subst_drop_shift {type carrier : Ty Base} (value : Term Const Γ type)
    (term : Term Const Γ carrier) :
    subst (Subst.comp (Subst.single value) (fun index => Term.var (.vs index))) term = term := by
  have identity : (Subst.comp (Subst.single value) (fun index => Term.var (.vs index)) : Subst Const Γ Γ) =
      (fun {type} (index : Var Γ type) => Term.var index) := by
    funext type index
    rfl
  rw [identity, subst_vars]

def apply_step (elements : Term Const Γ (signature.element ⇒ .prop)) (property : Term Const Γ signature.Property)
    (index : Term Const Γ signature.number) (head : Term Const Γ signature.element) (tail : Term Const Γ signature.vector)
    (step : ProofSyntax Const Δ (signature.stepCondition elements property)) :
    ProofSyntax Const Δ (signature.stepBody elements property index head tail) := by
  apply ProofSyntax.castIndices rfl ?_ (.allE tail (.allE head (.allE index step)))
  simp [instantiate, subst, subst_stepBody, subst_weaken, Subst.single, Subst.lift,
    subst_rename, subst_comp, Rename.weaken, subst_drop_shift, subst_vars]

def consClause_intro (elements : Term Const Γ (signature.element ⇒ .prop))
    (predicate : Term Const Γ (signature.Point ⇒ .prop)) (point : Term Const Γ signature.Point)
    (index : Term Const Γ signature.number) (head : Term Const Γ signature.element) (tail : Term Const Γ signature.vector)
    (body : ProofSyntax Const Δ (signature.consBody elements predicate point index head tail)) :
    ProofSyntax Const Δ (signature.consClause elements predicate point) := by
  refine .exI index (.exI head (.exI tail ?_))
  apply ProofSyntax.castIndices rfl ?_ body
  simp [instantiate, subst, subst_consBody, subst_weaken, Subst.single, Subst.lift,
    subst_rename, subst_comp, Rename.weaken, subst_drop_shift, subst_vars]

def cons_member (elements : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (head : Term Const Γ signature.element) (tail : Term Const Γ signature.vector)
    (headMember : ProofSyntax Const Δ (.app elements head))
    (tailMember : ProofSyntax Const Δ (signature.member elements index tail)) :
    ProofSyntax Const Δ (signature.member elements (.app (weakenCtx Γ signature.successor) index)
      (signature.consValue index head tail)) :=
  signature.fold elements _ (.orIR (signature.consClause_intro elements _ _ index head tail
    (.andI headMember (.andI tailMember (.eqRefl _)))))

/-- One positive layer preserves the property while retaining membership of
the recursive tail. Existential constructor fields keep their actual order. -/
def layer_property (elements : Term Const Γ (signature.element ⇒ .prop))
    (property : Term Const Γ signature.Property) (point : Term Const Γ signature.Point)
    (base : ProofSyntax Const Δ (PredicatePair.holds property (weakenCtx Γ signature.zero) (weakenCtx Γ signature.nil)))
    (step : ProofSyntax Const Δ (signature.stepCondition elements property))
    (constructed : ProofSyntax Const Δ
      (signature.layer elements (PredicateFixedPoint.intersection (signature.least elements) (PredicatePair.view property)) point)) :
    ProofSyntax Const Δ (.app (PredicatePair.view property) point) := by
  let predicate := PredicateFixedPoint.intersection (signature.least elements) (PredicatePair.view property)
  refine .orE constructed ?_ ?_
  · exact PredicatePair.property_of_equal_pair property point _ _ (.hyp 0) (base.prepend _)
  · refine .exE (.hyp 0) ?_
    refine .exE (.hyp 0) ?_
    refine .exE (.hyp 0) ?_
    let Θ := signature.vector :: signature.element :: signature.number :: Γ
    let a : Term Const Θ (signature.element ⇒ .prop) := weaken (weaken (weaken elements))
    let q : Term Const Θ signature.Property := weaken (weaken (weaken property))
    let p : Term Const Θ (signature.Point ⇒ .prop) := weaken (weaken (weaken predicate))
    let x : Term Const Θ signature.Point := weaken (weaken (weaken point))
    let n : Term Const Θ signature.number := .var (.vs (.vs .vz))
    let h : Term Const Θ signature.element := .var (.vs .vz)
    let t : Term Const Θ signature.vector := .var .vz
    let before := signature.consClause elements predicate point
    let first := signature.headClause (weaken elements) (weaken predicate) (weaken point) (.var .vz)
    let second := signature.tailClause (weaken (weaken elements)) (weaken (weaken predicate))
      (weaken (weaken point)) (.var (.vs .vz)) (.var .vz)
    let body := signature.consBody a p x n h t
    let assumptions := body :: weakenHyps (second :: weakenHyps (first :: weakenHyps (before :: Δ)))
    change ProofSyntax Const assumptions (weaken (weaken (weaken (.app (PredicatePair.view property) point))))
    have liftedStep : ProofSyntax Const assumptions (signature.stepCondition a q) := by
      have lifted :=
        ((PredicateFixedPoint.weakenProof (σ := signature.vector)
          ((PredicateFixedPoint.weakenProof (σ := signature.element)
            ((PredicateFixedPoint.weakenProof (σ := signature.number) (step.prepend before)).prepend first)).prepend second)).prepend body)
      apply ProofSyntax.castIndices rfl ?_ lifted
      simp only [a, q, weaken, rename_stepCondition]
    have fields : ProofSyntax Const assumptions (signature.consBody a p x n h t) := .hyp 0
    have recursive : ProofSyntax Const assumptions
        (.app (PredicateFixedPoint.intersection (signature.least a) (PredicatePair.view q)) (PredicatePair.pair n t)) := by
      apply ProofSyntax.castIndices rfl ?_ (.andEL (.andER fields))
      simp [p, predicate, a, q, weaken, PredicateFixedPoint.rename_intersection,
        rename_least, PredicatePair.rename_view]
    have both := ProofSyntax.impE
      (.eqPropEL (PredicateFixedPoint.intersection_beta (signature.least a) (PredicatePair.view q) (PredicatePair.pair n t))) recursive
    have child := ProofSyntax.impE (.eqPropEL (PredicatePair.view_pair q n t)) (.andER both)
    have output := ProofSyntax.impE
      (.impE (.impE (signature.apply_step a q n h t liftedStep) (.andEL fields)) (.andEL both)) child
    apply ProofSyntax.castIndices rfl ?_
      (PredicatePair.property_of_equal_pair q x _ _ (.andER (.andER fields)) output)
    simp [q, x, weaken, rename, PredicatePair.rename_view]

def inductionProof (elements : Term Const Γ (signature.element ⇒ .prop)) (property : Term Const Γ signature.Property)
    (index : Term Const Γ signature.number) (value : Term Const Γ signature.vector)
    (base : ProofSyntax Const Δ (PredicatePair.holds property (weakenCtx Γ signature.zero) (weakenCtx Γ signature.nil)))
    (step : ProofSyntax Const Δ (signature.stepCondition elements property))
    (member : ProofSyntax Const Δ (signature.member elements index value)) :
    ProofSyntax Const Δ (PredicatePair.holds property index value) := by
  have closed : ProofSyntax Const Δ (PredicateFixedPoint.included
      (.app (signature.operator elements)
        (PredicateFixedPoint.intersection (signature.least elements) (PredicatePair.view property)))
      (PredicatePair.view property)) := by
    refine .allI (.impI ?_)
    let a := weaken (σ := signature.Point) elements
    let q := weaken (σ := signature.Point) property
    let p := PredicateFixedPoint.intersection (signature.least a) (PredicatePair.view q)
    let premise : Formula Const (signature.Point :: Γ) :=
      .app (weaken (.app (signature.operator elements)
        (PredicateFixedPoint.intersection (signature.least elements) (PredicatePair.view property)))) (.var .vz)
    have supplied : ProofSyntax Const (premise :: weakenHyps Δ)
        (.app (.app (signature.operator a) p) (.var .vz)) := by
      apply ProofSyntax.castIndices rfl ?_ (.hyp 0)
      simp [premise, a, p, q, weaken, rename, rename_operator,
        PredicateFixedPoint.rename_intersection, rename_least, PredicatePair.rename_view]
    have unfolded := ProofSyntax.impE (.eqPropEL (signature.operator_layer a p (.var .vz))) supplied
    have liftedBase : ProofSyntax Const (premise :: weakenHyps Δ)
        (PredicatePair.holds q (weakenCtx _ signature.zero) (weakenCtx _ signature.nil)) := by
      apply ProofSyntax.castIndices rfl ?_ ((PredicateFixedPoint.weakenProof (σ := signature.Point) base).prepend premise)
      simp only [q, PredicatePair.holds, weaken, rename, rename_weakenCtx]
    have liftedStep : ProofSyntax Const (premise :: weakenHyps Δ) (signature.stepCondition a q) := by
      apply ProofSyntax.castIndices rfl ?_ ((PredicateFixedPoint.weakenProof step).prepend premise)
      simp only [a, q, weaken, rename_stepCondition]
    apply ProofSyntax.castIndices rfl ?_ (signature.layer_property a q (.var .vz) liftedBase liftedStep unfolded)
    simp [q, weaken, PredicatePair.rename_view]
  have proved := PredicateFixedPoint.guarded_induction (signature.operator elements) (PredicatePair.view property)
    (PredicatePair.pair index value) (signature.code elements).operator_monotone closed member
  exact .impE (.eqPropEL (PredicatePair.view_pair property index value)) proved

theorem operator_layer_free (elements : Term Const Γ (signature.element ⇒ .prop))
    (predicate : Term Const Γ (signature.Point ⇒ .prop)) (point : Term Const Γ signature.Point) :
    (signature.operator_layer (Δ := Δ) elements predicate point).FunctionExtensionalityFree := by
  simp [operator_layer, PositivePredicate.Code.operator_beta, ProofSyntax.FunctionExtensionalityFree]

theorem fold_free (elements : Term Const Γ (signature.element ⇒ .prop)) (point : Term Const Γ signature.Point)
    (constructed : ProofSyntax Const Δ (signature.layer elements (signature.least elements) point))
    (free : constructed.FunctionExtensionalityFree) :
    (signature.fold elements point constructed).FunctionExtensionalityFree := by
  apply PredicateFixedPoint.closure_at_free
  · exact (signature.code elements).operator_monotone_functionExtensionalityFree
  · simp [ProofSyntax.FunctionExtensionalityFree, operator_layer_free, free]

theorem nil_member_free (elements : Term Const Γ (signature.element ⇒ .prop)) :
    (signature.nil_member (Δ := Δ) elements).FunctionExtensionalityFree :=
  signature.fold_free _ _ _ True.intro

theorem consClause_intro_free (elements : Term Const Γ (signature.element ⇒ .prop))
    (predicate : Term Const Γ (signature.Point ⇒ .prop)) (point : Term Const Γ signature.Point)
    (index : Term Const Γ signature.number) (head : Term Const Γ signature.element) (tail : Term Const Γ signature.vector)
    (body : ProofSyntax Const Δ (signature.consBody elements predicate point index head tail))
    (free : body.FunctionExtensionalityFree) :
    (signature.consClause_intro elements predicate point index head tail body).FunctionExtensionalityFree := by
  simpa [consClause_intro, ProofSyntax.FunctionExtensionalityFree] using free

theorem cons_member_free (elements : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (head : Term Const Γ signature.element) (tail : Term Const Γ signature.vector)
    (headMember : ProofSyntax Const Δ (.app elements head))
    (tailMember : ProofSyntax Const Δ (signature.member elements index tail))
    (headFree : headMember.FunctionExtensionalityFree) (tailFree : tailMember.FunctionExtensionalityFree) :
    (signature.cons_member elements index head tail headMember tailMember).FunctionExtensionalityFree := by
  apply fold_free
  apply consClause_intro_free
  exact ⟨headFree, tailFree, True.intro⟩

theorem apply_step_free (elements : Term Const Γ (signature.element ⇒ .prop)) (property : Term Const Γ signature.Property)
    (index : Term Const Γ signature.number) (head : Term Const Γ signature.element) (tail : Term Const Γ signature.vector)
    (step : ProofSyntax Const Δ (signature.stepCondition elements property)) (free : step.FunctionExtensionalityFree) :
    (signature.apply_step elements property index head tail step).FunctionExtensionalityFree := by
  simpa [apply_step, ProofSyntax.FunctionExtensionalityFree] using free

theorem layer_property_free (elements : Term Const Γ (signature.element ⇒ .prop))
    (property : Term Const Γ signature.Property) (point : Term Const Γ signature.Point)
    (base : ProofSyntax Const Δ (PredicatePair.holds property (weakenCtx Γ signature.zero) (weakenCtx Γ signature.nil)))
    (step : ProofSyntax Const Δ (signature.stepCondition elements property))
    (constructed : ProofSyntax Const Δ
      (signature.layer elements (PredicateFixedPoint.intersection (signature.least elements) (PredicatePair.view property)) point))
    (baseFree : base.FunctionExtensionalityFree) (stepFree : step.FunctionExtensionalityFree)
    (constructedFree : constructed.FunctionExtensionalityFree) :
    (signature.layer_property elements property point base step constructed).FunctionExtensionalityFree := by
  simp [layer_property, ProofSyntax.FunctionExtensionalityFree, apply_step_free,
    PredicateFixedPoint.intersection_beta_free, PredicatePair.property_of_equal_pair_free,
    PredicatePair.view_pair_free, PredicateFixedPoint.weakenProof, ProofSyntax.prepend,
    baseFree, stepFree, constructedFree]

theorem inductionProof_free (elements : Term Const Γ (signature.element ⇒ .prop)) (property : Term Const Γ signature.Property)
    (index : Term Const Γ signature.number) (value : Term Const Γ signature.vector)
    (base : ProofSyntax Const Δ (PredicatePair.holds property (weakenCtx Γ signature.zero) (weakenCtx Γ signature.nil)))
    (step : ProofSyntax Const Δ (signature.stepCondition elements property))
    (member : ProofSyntax Const Δ (signature.member elements index value))
    (baseFree : base.FunctionExtensionalityFree) (stepFree : step.FunctionExtensionalityFree)
    (memberFree : member.FunctionExtensionalityFree) :
    (signature.inductionProof elements property index value base step member).FunctionExtensionalityFree := by
  simp only [inductionProof, ProofSyntax.FunctionExtensionalityFree,
    PredicatePair.view_pair_free, true_and]
  apply PredicateFixedPoint.guarded_induction_free
  · exact (signature.code elements).operator_monotone_functionExtensionalityFree
  · simp [ProofSyntax.FunctionExtensionalityFree, layer_property_free, operator_layer_free,
      PredicateFixedPoint.weakenProof, ProofSyntax.prepend, baseFree, stepFree]
  · exact memberFree

def inductionImplication (elements : Term Const Γ (signature.element ⇒ .prop)) (property : Term Const Γ signature.Property)
    (index : Term Const Γ signature.number) (value : Term Const Γ signature.vector) :
    ProofSyntax Const Δ
      (.imp (PredicatePair.holds property (weakenCtx Γ signature.zero) (weakenCtx Γ signature.nil))
        (.imp (signature.stepCondition elements property)
          (.imp (signature.member elements index value) (PredicatePair.holds property index value)))) :=
  .impI (.impI (.impI (signature.inductionProof elements property index value (.hyp 2) (.hyp 1) (.hyp 0))))

theorem inductionImplication_free (elements : Term Const Γ (signature.element ⇒ .prop)) (property : Term Const Γ signature.Property)
    (index : Term Const Γ signature.number) (value : Term Const Γ signature.vector) :
    (signature.inductionImplication (Δ := Δ) elements property index value).FunctionExtensionalityFree :=
  signature.inductionProof_free _ _ _ _ _ _ _ True.intro True.intro True.intro

#print axioms code_subst
#print axioms body_eq_layer
#print axioms subst_member
#print axioms nil_member
#print axioms cons_member
#print axioms inductionProof
#print axioms inductionProof_free
end Signature
end Mettapedia.Logic.HOL.IndexedVectorPredicate

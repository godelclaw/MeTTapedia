import Mettapedia.Logic.HOL.PredicateFixedPoint

/-!
# Induction retaining recursive membership

The invariant is strengthened by intersection with the constructed least
predicate. A constructor step may consequently use both recursive membership
and the induction hypothesis. The retained proof is derived from monotonicity,
least-predicate closure and minimality; no induction axiom is introduced.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.PredicateFixedPoint
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base} {α : Ty Base}

def intersection (first second : Term Const Γ (Predicate α)) : Term Const Γ (Predicate α) :=
  .lam (.and (.app (weaken first) (.var .vz)) (.app (weaken second) (.var .vz)))

@[simp] theorem subst_intersection (substitution : Subst Const Γ Ξ)
    (first second : Term Const Γ (Predicate α)) :
    subst substitution (intersection first second) = intersection (subst substitution first) (subst substitution second) := by
  simp [intersection, subst, subst_weaken, Subst.lift]

@[simp] theorem rename_intersection (rho : Rename Base Γ Ξ)
    (first second : Term Const Γ (Predicate α)) :
    rename rho (intersection first second) = intersection (rename rho first) (rename rho second) := by
  simpa only [subst_ofRename] using subst_intersection (Subst.ofRename rho) first second

variable {Δ : List (Formula Const Γ)}

def intersection_beta (first second : Term Const Γ (Predicate α)) (point : Term Const Γ α) :
    ProofSyntax Const Δ (.eq (.app (intersection first second) point)
      (.and (.app first point) (.app second point))) := by
  apply ProofSyntax.castIndices rfl ?_
    (.beta point (.and (.app (weaken first) (.var .vz)) (.app (weaken second) (.var .vz))))
  simp only [instantiate, subst, Subst.single]
  rw [show subst (Subst.single point) (weaken first) = first from instantiate_weaken _ _,
    show subst (Subst.single point) (weaken second) = second from instantiate_weaken _ _]
  rfl

def intersection_left (first second : Term Const Γ (Predicate α)) :
    ProofSyntax Const Δ (included (intersection first second) first) := by
  refine .allI (.impI ?_)
  have present : ProofSyntax Const
      (.app (weaken (intersection first second)) (.var .vz) :: weakenHyps Δ)
      (.app (intersection (weaken first) (weaken second)) (.var .vz)) := by
    apply ProofSyntax.castIndices rfl ?_ (.hyp 0)
    simp [weaken, rename_intersection]
  exact .andEL (.impE (.eqPropEL (intersection_beta (weaken first) (weaken second) (.var .vz))) present)

def strengthened_at (operator : Term Const Γ (Operator α)) (property : Term Const Γ (Predicate α))
    (point : Term Const Γ α) (order : ProofSyntax Const Δ (monotone operator))
    (step : ProofSyntax Const Δ (included (.app operator (intersection (least operator) property)) property))
    (present : ProofSyntax Const Δ (.app (.app operator (intersection (least operator) property)) point)) :
    ProofSyntax Const Δ (.app (intersection (least operator) property) point) := by
  have smaller : ProofSyntax Const Δ
      (included (.app operator (intersection (least operator) property)) (.app operator (least operator))) :=
    monotonicity_elim operator _ _ order (intersection_left (least operator) property)
  have member : ProofSyntax Const Δ (.app (least operator) point) :=
    closure_at operator point order (inclusion_elim _ _ point smaller present)
  have proved : ProofSyntax Const Δ (.app property point) := inclusion_elim _ _ point step present
  exact .impE (.eqPropER (intersection_beta (least operator) property point)) (.andI member proved)

def strengthened_prefixed (operator : Term Const Γ (Operator α)) (property : Term Const Γ (Predicate α))
    (order : ProofSyntax Const Δ (monotone operator))
    (step : ProofSyntax Const Δ (included (.app operator (intersection (least operator) property)) property)) :
    ProofSyntax Const Δ (prefixed operator (intersection (least operator) property)) := by
  refine .allI (.impI ?_)
  let premise : Formula Const (α :: Γ) :=
    .app (weaken (.app operator (intersection (least operator) property))) (.var .vz)
  have liftedOrder : ProofSyntax Const (premise :: weakenHyps Δ) (monotone (weaken operator)) := by
    apply ProofSyntax.castIndices rfl ?_ ((weakenProof order).prepend premise)
    simp [weaken, rename_monotone]
  have liftedStep : ProofSyntax Const (premise :: weakenHyps Δ)
      (included (.app (weaken operator) (intersection (least (weaken operator)) (weaken property))) (weaken property)) := by
    apply ProofSyntax.castIndices rfl ?_ ((weakenProof step).prepend premise)
    simp [weaken, rename_included, rename_intersection, rename_least, rename]
  have present : ProofSyntax Const (premise :: weakenHyps Δ)
      (.app (.app (weaken operator) (intersection (least (weaken operator)) (weaken property))) (.var .vz)) := by
    apply ProofSyntax.castIndices rfl ?_ (.hyp 0)
    simp [premise, weaken, rename, rename_intersection, rename_least]
  apply ProofSyntax.castIndices rfl ?_
    (strengthened_at (weaken operator) (weaken property) (.var .vz) liftedOrder liftedStep present)
  simp [weaken, rename_intersection, rename_least]

def guarded_induction (operator : Term Const Γ (Operator α)) (property : Term Const Γ (Predicate α))
    (point : Term Const Γ α) (order : ProofSyntax Const Δ (monotone operator))
    (step : ProofSyntax Const Δ (included (.app operator (intersection (least operator) property)) property))
    (member : ProofSyntax Const Δ (.app (least operator) point)) :
    ProofSyntax Const Δ (.app property point) :=
  .andER (.impE (.eqPropEL (intersection_beta (least operator) property point))
    (least_elim operator _ point member (strengthened_prefixed operator property order step)))

theorem intersection_beta_free (first second : Term Const Γ (Predicate α)) (point : Term Const Γ α) :
    (intersection_beta (Δ := Δ) first second point).FunctionExtensionalityFree := by
  simp [intersection_beta, ProofSyntax.FunctionExtensionalityFree]

theorem intersection_left_free (first second : Term Const Γ (Predicate α)) :
    (intersection_left (Δ := Δ) first second).FunctionExtensionalityFree := by
  simp [intersection_left, intersection_beta_free, ProofSyntax.FunctionExtensionalityFree]

theorem closure_at_free (operator : Term Const Γ (Operator α)) (point : Term Const Γ α)
    (order : ProofSyntax Const Δ (monotone operator))
    (member : ProofSyntax Const Δ (.app (.app operator (least operator)) point))
    (orderFree : order.FunctionExtensionalityFree) (memberFree : member.FunctionExtensionalityFree) :
    (closure_at operator point order member).FunctionExtensionalityFree := by
  simp [closure_at, least_intro, least_beta, minimality, least_elim, monotonicity_elim,
    inclusion_elim, weakenProof, ProofSyntax.prepend, ProofSyntax.FunctionExtensionalityFree,
    orderFree, memberFree]

theorem guarded_induction_free (operator : Term Const Γ (Operator α)) (property : Term Const Γ (Predicate α))
    (point : Term Const Γ α) (order : ProofSyntax Const Δ (monotone operator))
    (step : ProofSyntax Const Δ (included (.app operator (intersection (least operator) property)) property))
    (member : ProofSyntax Const Δ (.app (least operator) point))
    (orderFree : order.FunctionExtensionalityFree) (stepFree : step.FunctionExtensionalityFree)
    (memberFree : member.FunctionExtensionalityFree) :
    (guarded_induction operator property point order step member).FunctionExtensionalityFree := by
  simp [guarded_induction, strengthened_prefixed, strengthened_at, intersection_left, intersection_beta,
    least_elim, least_beta, monotonicity_elim, closure_at, least_intro, minimality, inclusion_elim,
    weakenProof, ProofSyntax.prepend, ProofSyntax.FunctionExtensionalityFree,
    orderFree, stepFree, memberFree]

#print axioms strengthened_prefixed
#print axioms guarded_induction
#print axioms guarded_induction_free
end Mettapedia.Logic.HOL.PredicateFixedPoint

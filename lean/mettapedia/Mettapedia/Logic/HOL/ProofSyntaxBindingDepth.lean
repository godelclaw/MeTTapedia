import Mettapedia.Logic.HOL.ProofSyntax
import Mettapedia.Logic.HOL.Syntax.BindingDepth

/-!
# Object-binder budgets for retained HOL proofs

The budget inspects every retained rule, its source interface, its term
parameters and its recursive premises. Quantifier instantiation and beta
include the source-body and substitution-image bound. It is a sufficient
syntactic budget for named interpretations, not a checking-time estimate.

An ignored specialization argument can have unbounded binder depth while
the existing proof observation and node count stay fixed. Those observations
cannot supply this allocation bound without inspecting the retained terms.
-/

set_option autoImplicit false
namespace Mettapedia.Logic.HOL.ProofSyntax
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
variable {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}

def assumptionBinderDepth : List (Formula Const Γ) → Nat
  | [] => 0
  | first :: rest => max first.binderDepth (assumptionBinderDepth rest)

theorem binderDepth_le_assumptionBinderDepth (assumptions : List (Formula Const Γ))
    (formula : Formula Const Γ) (member : formula ∈ assumptions) :
    formula.binderDepth ≤ assumptionBinderDepth assumptions := by
  induction assumptions with
  | nil => simp at member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih later) (Nat.le_max_right _ _)

theorem assumptionBinderDepth_weaken {domain : Ty Base} (assumptions : List (Formula Const Γ)) :
    assumptionBinderDepth (weakenHyps (σ := domain) assumptions) = assumptionBinderDepth assumptions := by
  induction assumptions with
  | nil => rfl
  | cons first rest ih =>
      simpa only [weakenHyps, List.map_cons, assumptionBinderDepth, weaken, Term.binderDepth_rename] using
        congrArg (max first.binderDepth) ih

def interfaceBinderDepth (assumptions : List (Formula Const Γ)) (conclusion : Formula Const Γ) : Nat :=
  max conclusion.binderDepth (assumptionBinderDepth assumptions)

def localBinderBudget (proof : ProofSyntax Const Δ φ) : Nat :=
  max (interfaceBinderDepth Δ φ + 1) (match proof with
    | .allE (φ := body) argument _ | .exI (φ := body) argument _ =>
        body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1
    | .beta argument body => body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1
    | .eqRefl term | .eqApp term _ | .eqAppArg term _ | .eta term => term.binderDepth + 1
    | .hyp _ | .topI | .botE _ | .andI _ _ | .andEL _ | .andER _ | .orIL _ | .orIR _
    | .orE _ _ _ | .impI _ | .impE _ _ | .notI _ | .notE _ _ | .allI _ | .exE _ _
    | .eqSymm _ | .eqTrans _ _ | .eqPropI _ _ | .eqPropEL _ | .eqPropER _ | .eqLam _ | .funExt _ => 0)

def binderBudget {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (proof : ProofSyntax Const Δ φ) : Nat :=
  let own := localBinderBudget proof
  match proof with
  | .hyp _ | .topI | .eqRefl _ | .beta _ _ | .eta _ => own
  | .botE child | .andEL child | .andER child | .orIL child | .orIR child | .impI child
  | .notI child | .eqSymm child | .eqPropEL child | .eqPropER child | .funExt child =>
      max own child.binderBudget
  | .allI child | .eqLam child => max own (child.binderBudget + 1)
  | .allE _ child | .exI _ child | .eqApp _ child | .eqAppArg _ child => max own child.binderBudget
  | .andI first second | .impE first second | .notE first second | .eqTrans first second
  | .eqPropI first second | .exE first second => max own (max first.binderBudget second.binderBudget)
  | .orE cases first second => max own (max cases.binderBudget (max first.binderBudget second.binderBudget))
termination_by structural proof

def premiseMeasures (measure : ∀ {gamma : Ctx Base} {assumptions : List (Formula Const gamma)} {conclusion : Formula Const gamma},
    ProofSyntax Const assumptions conclusion → Nat) (proof : ProofSyntax Const Δ φ) : List Nat :=
  match proof with
  | .hyp _ | .topI | .eqRefl _ | .beta _ _ | .eta _ => []
  | .botE child | .andEL child | .andER child | .orIL child | .orIR child | .impI child
  | .notI child | .eqSymm child | .eqPropEL child | .eqPropER child | .funExt child
  | .allI child | .eqLam child => [measure child]
  | .allE _ child | .exI _ child | .eqApp _ child | .eqAppArg _ child => [measure child]
  | .andI first second | .impE first second | .notE first second | .eqTrans first second
  | .eqPropI first second | .exE first second => [measure first, measure second]
  | .orE cases first second => [measure cases, measure first, measure second]

def premiseBinderBudgets (proof : ProofSyntax Const Δ φ) : List Nat := premiseMeasures (@binderBudget Base Const) proof

theorem nodeCount_eq_premiseSum (proof : ProofSyntax Const Δ φ) :
    proof.nodeCount = 1 + (premiseMeasures (@nodeCount Base Const) proof).sum := by
  cases proof <;> simp [nodeCount, observe, premiseMeasures, Fin.sum_univ_succ]

theorem premiseBinderBudget_le (proof : ProofSyntax Const Δ φ) (budget : Nat)
    (member : budget ∈ proof.premiseBinderBudgets) : budget ≤ proof.binderBudget := by
  cases proof <;> simp only [premiseBinderBudgets, premiseMeasures, List.mem_cons, List.not_mem_nil, or_false] at member
  all_goals
    simp only [binderBudget]
    rcases member with rfl | rfl | rfl <;> omega

theorem localBinderBudget_le (proof : ProofSyntax Const Δ φ) : proof.localBinderBudget ≤ proof.binderBudget := by
  cases proof <;> simp only [binderBudget, Nat.le_refl, Nat.le_max_left]

theorem interfaceBinderDepth_lt (proof : ProofSyntax Const Δ φ) : interfaceBinderDepth Δ φ < proof.binderBudget := by
  have rootBound : interfaceBinderDepth Δ φ + 1 ≤ proof.localBinderBudget := Nat.le_max_left _ _
  have global := proof.localBinderBudget_le
  omega

theorem conclusionBinderDepth_lt (proof : ProofSyntax Const Δ φ) : φ.binderDepth < proof.binderBudget :=
  Nat.lt_of_le_of_lt (Nat.le_max_left _ _) proof.interfaceBinderDepth_lt

theorem assumptionBinderDepth_lt (proof : ProofSyntax Const Δ φ) (formula : Formula Const Γ) (member : formula ∈ Δ) :
    formula.binderDepth < proof.binderBudget :=
  Nat.lt_of_le_of_lt (Nat.le_trans (binderDepth_le_assumptionBinderDepth Δ formula member) (Nat.le_max_right _ _))
    proof.interfaceBinderDepth_lt

theorem binderBudget_pos (proof : ProofSyntax Const Δ φ) : 0 < proof.binderBudget := by
  have positive := proof.conclusionBinderDepth_lt
  omega

theorem specialization_requirement_le {domain : Ty Base} {body : Formula Const (domain :: Γ)}
    (argument : Term Const Γ domain) (proof : ProofSyntax Const Δ (.all body)) :
    body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1 ≤ (ProofSyntax.allE argument proof).binderBudget := by
  have rootBound := (ProofSyntax.allE argument proof).localBinderBudget_le
  have required : body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1 ≤
      (ProofSyntax.allE argument proof).localBinderBudget := Nat.le_max_right _ _
  exact required.trans rootBound

theorem existential_requirement_le {domain : Ty Base} {body : Formula Const (domain :: Γ)}
    (argument : Term Const Γ domain) (proof : ProofSyntax Const Δ (instantiate argument body)) :
    body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1 ≤ (ProofSyntax.exI argument proof).binderBudget := by
  have rootBound := (ProofSyntax.exI argument proof).localBinderBudget_le
  have required : body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1 ≤
      (ProofSyntax.exI argument proof).localBinderBudget := Nat.le_max_right _ _
  exact required.trans rootBound

theorem beta_requirement_le {domain result : Ty Base} (argument : Term Const Γ domain)
    (body : Term Const (domain :: Γ) result) :
    body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1 ≤
      (ProofSyntax.beta (Δ := Δ) argument body).binderBudget := by
  exact Nat.le_max_right _ _

namespace BindingDepthControls
abbrev Constants : Ty Unit → Type := fun _ => Empty

def ignoredArgument : Nat → Term Constants [] .prop
  | 0 => .top
  | n + 1 => .app (.lam (weaken (σ := .prop) (ignoredArgument n))) .top

theorem ignoredArgument_depth (n : Nat) : (ignoredArgument n).binderDepth = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [ignoredArgument, Term.binderDepth, weaken, Term.binderDepth_rename, ih, Nat.max_zero]

def specialization (n : Nat) : ProofSyntax Constants [] (.top : ClosedFormula Constants) :=
  .allE (φ := (.top : Formula Constants [.prop])) (ignoredArgument n) (.allI .topI)

theorem identical_observations (n : Nat) : (specialization n).observe = (specialization 0).observe := rfl

theorem identical_node_counts (n : Nat) : (specialization n).nodeCount = (specialization 0).nodeCount :=
  congrArg Mettapedia.Logic.Derivation.nodeCount (identical_observations n)

theorem specialization_budget (n : Nat) : (specialization n).binderBudget = max 2 (n + 1) := by
  simp [specialization, binderBudget, localBinderBudget, interfaceBinderDepth, assumptionBinderDepth,
    Term.binderDepth, Subst.maxBinderDepth, Subst.single, ignoredArgument_depth, weakenHyps]
  omega

theorem unbounded_budget_same_observation (limit : Nat) :
    ∃ n, (specialization n).observe = (specialization 0).observe ∧ limit < (specialization n).binderBudget := by
  refine ⟨limit + 1, identical_observations _, ?_⟩
  rw [specialization_budget]
  omega
end BindingDepthControls

#print axioms nodeCount_eq_premiseSum
#print axioms premiseBinderBudget_le
#print axioms assumptionBinderDepth_weaken
#print axioms localBinderBudget_le
#print axioms conclusionBinderDepth_lt
#print axioms assumptionBinderDepth_lt
#print axioms specialization_requirement_le
#print axioms existential_requirement_le
#print axioms beta_requirement_le
#print axioms BindingDepthControls.unbounded_budget_same_observation
end Mettapedia.Logic.HOL.ProofSyntax

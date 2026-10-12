import Mettapedia.GSLT.Causality.DoCalculus.LatentMargin
import Mettapedia.GSLT.Causality.DoCalculus.Soundness
import Mettapedia.GSLT.Core.NonFactorization

/-!
# A hedge that is not the bow

`ChildBow` is the bow `U → X → Y`, `U → Y`, plus the observed child `Y → D`.
The pair `X, Y` still shares the latent parent `U`. The graph is not the bow:
it has four vertices. `idFragment` refuses `P(y | do(x))`. The two tables
below share the margin of `U` and disagree on that query.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.DoCalculus

open Mettapedia.ProbabilityTheory.BayesianNetworks
open BayesianNetwork
open DirectedGraph
open Mettapedia.GSLT.Core.NonFactorization
open scoped BigOperators ENNReal

inductive ChildBow
  | u
  | x
  | y
  | d
  deriving DecidableEq

instance : Fintype ChildBow where
  elems := {ChildBow.u, ChildBow.x, ChildBow.y, ChildBow.d}
  complete := by intro v; cases v <;> simp

def childBowGraph : DirectedGraph ChildBow where
  edges a b :=
    (a = .u ∧ b = .x) ∨ (a = .u ∧ b = .y) ∨ (a = .x ∧ b = .y) ∨ (a = .y ∧ b = .d)

instance : DecidableRel childBowGraph.edges := fun a b => by
  unfold childBowGraph
  infer_instance

def childBowRank : ChildBow → ℕ
  | .u => 0
  | .x => 1
  | .y => 2
  | .d => 3

lemma childBow_edge_increases {a b : ChildBow} (h : childBowGraph.edges a b) : childBowRank a < childBowRank b := by
  cases a <;> cases b <;> simp [childBowGraph, childBowRank] at h ⊢

lemma childBow_reachable_rank {a b : ChildBow} (h : childBowGraph.Reachable a b) : childBowRank a ≤ childBowRank b := by
  induction h with
  | refl => exact le_rfl
  | step hedge _ ih => exact le_trans (Nat.le_of_lt (childBow_edge_increases hedge)) ih

lemma childBowAcyclic : childBowGraph.IsAcyclic := by
  intro v ⟨src, hedge, hreach⟩
  exact (lt_irrefl _) <|
    lt_of_lt_of_le (childBow_edge_increases hedge) (childBow_reachable_rank hreach)

theorem childBow_four_vertices : Fintype.card ChildBow = 4 := by
  decide

theorem childBow_child_edge : childBowGraph.edges ChildBow.y ChildBow.d := by
  decide

theorem childBow_fragment_refuses :
    idFragment childBowGraph {ChildBow.y} {ChildBow.x} (∅ : Finset ChildBow) = .refuse := by
  decide

lemma childBow_u_parent_x :
    ChildBow.u ∈ (network (β := Bool) childBowGraph childBowAcyclic).parents ChildBow.x := by
  simp [BayesianNetwork.parents, DirectedGraph.parents, childBowGraph]

lemma childBow_u_parent_y :
    ChildBow.u ∈ (network (β := Bool) childBowGraph childBowAcyclic).parents ChildBow.y := by
  simp [BayesianNetwork.parents, DirectedGraph.parents, childBowGraph]

lemma childBow_x_parent_y :
    ChildBow.x ∈ (network (β := Bool) childBowGraph childBowAcyclic).parents ChildBow.y := by
  simp [BayesianNetwork.parents, DirectedGraph.parents, childBowGraph]

lemma childBow_y_parent_d :
    ChildBow.y ∈ (network (β := Bool) childBowGraph childBowAcyclic).parents ChildBow.d := by
  simp [BayesianNetwork.parents, DirectedGraph.parents, childBowGraph]

noncomputable def childBowCPT1 : (network (β := Bool) childBowGraph childBowAcyclic).DiscreteCPT where
  cpt := fun v pa =>
    match v with
    | .u => fairBit
    | .x => PMF.pure (pa .u childBow_u_parent_x)
    | .y => PMF.pure (pa .x childBow_x_parent_y)
    | .d => PMF.pure (pa .y childBow_y_parent_d)

noncomputable def childBowCPT2 : (network (β := Bool) childBowGraph childBowAcyclic).DiscreteCPT where
  cpt := fun v pa =>
    match v with
    | .u => fairBit
    | .x => PMF.pure (pa .u childBow_u_parent_x)
    | .y => PMF.pure (pa .u childBow_u_parent_y)
    | .d => PMF.pure (pa .y childBow_y_parent_d)

def childBowOf (bu bx byy bd : Bool) : ChildBow → Bool
  | .u => bu
  | .x => bx
  | .y => byy
  | .d => bd

lemma prod_childBow (g : ChildBow → ℝ≥0∞) : ∏ v, g v = g .u * (g .x * (g .y * g .d)) := by
  have huniv : (Finset.univ : Finset ChildBow) = insert .u (insert .x (insert .y {.d})) := by
    ext v
    cases v <;> simp
  rw [huniv, Finset.prod_insert (by simp), Finset.prod_insert (by simp),
    Finset.prod_insert (by simp), Finset.prod_singleton]

lemma sum_childBow (g : (ChildBow → Bool) → ℝ≥0∞) :
    ∑ f, g f = ∑ bu, ∑ bx, ∑ byy, ∑ bd, g (childBowOf bu bx byy bd) := by
  let e : (ChildBow → Bool) ≃ Bool × Bool × Bool × Bool :=
    { toFun := fun f => (f .u, f .x, f .y, f .d)
      invFun := fun p => childBowOf p.1 p.2.1 p.2.2.1 p.2.2.2
      left_inv := by
        intro f
        ext v
        cases v <;> rfl
      right_inv := by
        rintro ⟨bu, bx, byy, bd⟩
        rfl }
  rw [← Equiv.sum_comp e.symm g]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun bu _ => ?_
  rw [← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun bx _ => ?_
  rw [← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun byy _ => ?_
  refine Finset.sum_congr rfl fun bd _ => ?_
  rfl

lemma childBow_node1_u (f : ChildBow → Bool) :
    DiscreteCPT.nodeProb childBowCPT1 f .u = fairBit (f .u) := by
  simp [DiscreteCPT.nodeProb, childBowCPT1]

lemma childBow_node1_x (f : ChildBow → Bool) :
    DiscreteCPT.nodeProb childBowCPT1 f .x = PMF.pure (f .u) (f .x) := by
  simp [DiscreteCPT.nodeProb, DiscreteCPT.parentAssignOfConfig, childBowCPT1]

lemma childBow_node1_y (f : ChildBow → Bool) :
    DiscreteCPT.nodeProb childBowCPT1 f .y = PMF.pure (f .x) (f .y) := by
  simp [DiscreteCPT.nodeProb, DiscreteCPT.parentAssignOfConfig, childBowCPT1]

lemma childBow_node1_d (f : ChildBow → Bool) :
    DiscreteCPT.nodeProb childBowCPT1 f .d = PMF.pure (f .y) (f .d) := by
  simp [DiscreteCPT.nodeProb, DiscreteCPT.parentAssignOfConfig, childBowCPT1]

lemma childBow_node2_u (f : ChildBow → Bool) :
    DiscreteCPT.nodeProb childBowCPT2 f .u = fairBit (f .u) := by
  simp [DiscreteCPT.nodeProb, childBowCPT2]

lemma childBow_node2_x (f : ChildBow → Bool) :
    DiscreteCPT.nodeProb childBowCPT2 f .x = PMF.pure (f .u) (f .x) := by
  simp [DiscreteCPT.nodeProb, DiscreteCPT.parentAssignOfConfig, childBowCPT2]

lemma childBow_node2_y (f : ChildBow → Bool) :
    DiscreteCPT.nodeProb childBowCPT2 f .y = PMF.pure (f .u) (f .y) := by
  simp [DiscreteCPT.nodeProb, DiscreteCPT.parentAssignOfConfig, childBowCPT2]

lemma childBow_node2_d (f : ChildBow → Bool) :
    DiscreteCPT.nodeProb childBowCPT2 f .d = PMF.pure (f .y) (f .d) := by
  simp [DiscreteCPT.nodeProb, DiscreteCPT.parentAssignOfConfig, childBowCPT2]

lemma childBow_joint1 (f : ChildBow → Bool) :
    childBowCPT1.jointWeight f =
      fairBit (f .u) * (PMF.pure (f .u) (f .x) * (PMF.pure (f .x) (f .y) * PMF.pure (f .y) (f .d))) := by
  unfold DiscreteCPT.jointWeight
  rw [prod_childBow]
  simp [childBow_node1_u, childBow_node1_x, childBow_node1_y, childBow_node1_d]

lemma childBow_joint2 (f : ChildBow → Bool) :
    childBowCPT2.jointWeight f =
      fairBit (f .u) * (PMF.pure (f .u) (f .x) * (PMF.pure (f .u) (f .y) * PMF.pure (f .y) (f .d))) := by
  unfold DiscreteCPT.jointWeight
  rw [prod_childBow]
  simp [childBow_node2_u, childBow_node2_x, childBow_node2_y, childBow_node2_d]

lemma childBow_support1 (fu fx fy fd : Bool) :
    fairBit fu * (PMF.pure fu fx * (PMF.pure fx fy * PMF.pure fy fd)) =
      if fx = fu ∧ fy = fu ∧ fd = fu then fairBit fu else 0 := by
  cases fu <;> cases fx <;> cases fy <;> cases fd <;> simp [fairBit_apply]

lemma childBow_support2 (fu fx fy fd : Bool) :
    fairBit fu * (PMF.pure fu fx * (PMF.pure fu fy * PMF.pure fy fd)) =
      if fx = fu ∧ fy = fu ∧ fd = fu then fairBit fu else 0 := by
  cases fu <;> cases fx <;> cases fy <;> cases fd <;> simp [fairBit_apply]

theorem childBow_joint_agree (f : ChildBow → Bool) :
    childBowCPT1.jointWeight f = childBowCPT2.jointWeight f := by
  rw [childBow_joint1, childBow_joint2, childBow_support1, childBow_support2]

noncomputable def childBowMargin
    (cpt : (network (β := Bool) childBowGraph childBowAcyclic).DiscreteCPT) :
    ({v // v ∉ ({ChildBow.u} : Finset ChildBow)} → Bool) → ℝ≥0∞ :=
  fun observed => observedMargin {ChildBow.u} (fun assignment => cpt.jointWeight assignment) observed

theorem childBow_margins_agree : childBowMargin childBowCPT1 = childBowMargin childBowCPT2 := by
  funext observed
  unfold childBowMargin observedMargin
  refine Finset.sum_congr rfl fun latent _ => ?_
  exact childBow_joint_agree (glue {ChildBow.u} latent observed)

def childBowDoX : ChildBow → Option Bool :=
  fun v => if v = .x then some true else none

lemma childBow_trunc1 (f : ChildBow → Bool) :
    truncatedWeight childBowGraph childBowAcyclic childBowCPT1 childBowDoX f =
      (if f .x = true then 1 else 0) *
        (fairBit (f .u) * (PMF.pure (f .x) (f .y) * PMF.pure (f .y) (f .d))) := by
  unfold truncatedWeight
  rw [prod_childBow]
  have hu : truncatedFactor childBowGraph childBowAcyclic childBowCPT1 childBowDoX f .u = fairBit (f .u) := by
    simp [truncatedFactor, childBowDoX, ← childBow_node1_u, cptAt_eq_nodeProb]
  have hx : truncatedFactor childBowGraph childBowAcyclic childBowCPT1 childBowDoX f .x =
      if f .x = true then 1 else 0 := by
    simp [truncatedFactor, childBowDoX]
  have hy : truncatedFactor childBowGraph childBowAcyclic childBowCPT1 childBowDoX f .y =
      PMF.pure (f .x) (f .y) := by
    have hne : ChildBow.y ≠ ChildBow.x := by decide
    simp only [truncatedFactor, childBowDoX, if_neg hne, cptAt_eq_nodeProb, childBow_node1_y]
  have hd : truncatedFactor childBowGraph childBowAcyclic childBowCPT1 childBowDoX f .d =
      PMF.pure (f .y) (f .d) := by
    have hne : ChildBow.d ≠ ChildBow.x := by decide
    simp only [truncatedFactor, childBowDoX, if_neg hne, cptAt_eq_nodeProb, childBow_node1_d]
  rw [hu, hx, hy, hd, mul_left_comm]

lemma childBow_trunc2 (f : ChildBow → Bool) :
    truncatedWeight childBowGraph childBowAcyclic childBowCPT2 childBowDoX f =
      (if f .x = true then 1 else 0) *
        (fairBit (f .u) * (PMF.pure (f .u) (f .y) * PMF.pure (f .y) (f .d))) := by
  unfold truncatedWeight
  rw [prod_childBow]
  have hu : truncatedFactor childBowGraph childBowAcyclic childBowCPT2 childBowDoX f .u = fairBit (f .u) := by
    simp [truncatedFactor, childBowDoX, ← childBow_node2_u, cptAt_eq_nodeProb]
  have hx : truncatedFactor childBowGraph childBowAcyclic childBowCPT2 childBowDoX f .x =
      if f .x = true then 1 else 0 := by
    simp [truncatedFactor, childBowDoX]
  have hy : truncatedFactor childBowGraph childBowAcyclic childBowCPT2 childBowDoX f .y =
      PMF.pure (f .u) (f .y) := by
    have hne : ChildBow.y ≠ ChildBow.x := by decide
    simp only [truncatedFactor, childBowDoX, if_neg hne, cptAt_eq_nodeProb, childBow_node2_y]
  have hd : truncatedFactor childBowGraph childBowAcyclic childBowCPT2 childBowDoX f .d =
      PMF.pure (f .y) (f .d) := by
    have hne : ChildBow.d ≠ ChildBow.x := by decide
    simp only [truncatedFactor, childBowDoX, if_neg hne, cptAt_eq_nodeProb, childBow_node2_d]
  rw [hu, hx, hy, hd, mul_left_comm]

noncomputable def childBowDoMass
    (cpt : (network (β := Bool) childBowGraph childBowAcyclic).DiscreteCPT) (y : Bool) : ℝ≥0∞ :=
  ∑ f, if f .y = y then truncatedWeight childBowGraph childBowAcyclic cpt childBowDoX f else 0

theorem childBow_do_model1 : childBowDoMass childBowCPT1 true = 1 := by
  unfold childBowDoMass
  rw [sum_childBow]
  simp_rw [childBow_trunc1, childBowOf, sum_bool]
  simp [fairBit_apply, ENNReal.inv_two_add_inv_two]

theorem childBow_do_model2 : childBowDoMass childBowCPT2 true = (2 : ℝ≥0∞)⁻¹ := by
  unfold childBowDoMass
  rw [sum_childBow]
  simp_rw [childBow_trunc2, childBowOf, sum_bool]
  simp [fairBit_apply]

noncomputable def childBowQuery :
    (network (β := Bool) childBowGraph childBowAcyclic).DiscreteCPT → ℝ≥0∞ :=
  fun cpt => childBowDoMass cpt true

theorem childBow_two_models_one_margin :
    childBowMargin childBowCPT1 = childBowMargin childBowCPT2 ∧ childBowQuery childBowCPT1 ≠ childBowQuery childBowCPT2 := by
  refine ⟨childBow_margins_agree, ?_⟩
  unfold childBowQuery
  rw [childBow_do_model1, childBow_do_model2]
  exact one_ne_inv_two

theorem childBow_query_not_factors_margin : ¬ Factors childBowMargin childBowQuery :=
  (⟨childBowCPT1, childBowCPT2, childBow_margins_agree, childBow_two_models_one_margin.2⟩ :
    NonTrivialFiber childBowMargin childBowQuery).not_factors

end Mettapedia.GSLT.Causality.DoCalculus

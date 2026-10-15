import Mettapedia.GSLT.Causality.DoCalculus.CheckerRules

/-!
# Back-door premises for the finite checker

`BackDoorCriterion` separates the treatment from the outcome after the arrows
out of the treatment are deleted. Rule 2's checker asks for the opposite
endpoint order, on the same mutilation, and it also asks that both endpoints
lie outside the adjustment set. On an acyclic graph the two separations
agree. An admissible finset whose outcome lies outside it, and which is not
the treatment, therefore makes the premise of `rule2_of_check` true.

The door graph `Z → X`, `Z → Y`, `X → Y` meets the criterion at `{Z}`.
Both endpoint orders are accepted, and rule 3's checker accepts
`P(Z | do(X)) = P(Z)`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.DoCalculus

open Mettapedia.ProbabilityTheory.BayesianNetworks
open Mettapedia.ProbabilityTheory.BayesianNetworks.FiniteDSeparation
open DirectedGraph
open DSeparation

variable {V : Type}
variable [Fintype V] [DecidableEq V]
variable (graph : DirectedGraph V)
variable [DecidableRel graph.edges]

omit [Fintype V] [DecidableEq V] [DecidableRel graph.edges] in
/-- Deleting the arrows into the empty set leaves the edge relation. -/
lemma deleteIncoming_empty :
    deleteIncoming graph (∅ : Finset V) = graph := by
  ext u v
  simp [deleteIncoming]

omit [Fintype V] [DecidableEq V] [DecidableRel graph.edges] in
/-- With no kept intervention, rule 2's mutilation is deletion of the
outgoing arrows. -/
lemma gout_emptyIncoming_eq_deleteOutgoing (forbidden : Finset V) :
    gout graph (∅ : Finset V) forbidden = deleteOutgoing graph forbidden := by
  ext u v
  simp [gout, gx, deleteOutgoing, deleteIncoming]

/-- Every finset admissible for the back-door criterion, with the outcome
outside that finset and distinct from the treatment, is accepted by rule 2's
checker. The criterion separates treatment from outcome; the checker
separates outcome from treatment. -/
theorem backDoor_exchange_checked
    {treatment outcome : V} {adjustment : Finset V}
    (hAcyclic : graph.IsAcyclic)
    (hcrit : BackDoorCriterion graph treatment outcome (adjustment : Set V))
    (houtcome : outcome ∉ adjustment)
    (hdistinct : outcome ≠ treatment) :
    FiniteDSeparation.check (gout graph (∅ : Finset V) {treatment})
      (rule2Profile {outcome} {treatment} ((∅ : Finset V) ∪ adjustment)) = true := by
  have hgraph :
      gout graph (∅ : Finset V) {treatment} =
        deleteOutgoing graph {treatment} :=
    gout_emptyIncoming_eq_deleteOutgoing graph {treatment}
  have hacy : (deleteOutgoing graph {treatment}).IsAcyclic :=
    deleteOutgoing_acyclic graph hAcyclic {treatment}
  have hswap :
      DSeparatedFull (deleteOutgoing graph {treatment})
        ({outcome} : Set V) ({treatment} : Set V) (adjustment : Set V) :=
    dsepFull_symmetric (deleteOutgoing graph {treatment})
      ({treatment} : Set V) ({outcome} : Set V) (adjustment : Set V)
      hacy
      (fun vertex =>
        DirectedGraph.isAcyclic_irrefl (deleteOutgoing graph {treatment}) hacy vertex)
      hcrit.separated
  have hprofile :
      rule2Profile {outcome} {treatment} ((∅ : Finset V) ∪ adjustment) =
        { X := {outcome}, Y := {treatment}, Z := (∅ : Finset V) ∪ adjustment } := rfl
  have hsep :
      DSeparatedFull (gout graph (∅ : Finset V) {treatment})
        (((rule2Profile {outcome} {treatment} ((∅ : Finset V) ∪ adjustment)).X :
            Finset V) : Set V)
        (((rule2Profile {outcome} {treatment} ((∅ : Finset V) ∪ adjustment)).Y :
            Finset V) : Set V)
        (((rule2Profile {outcome} {treatment} ((∅ : Finset V) ∪ adjustment)).Z :
            Finset V) : Set V) := by
    rw [hprofile]
    simp only [hgraph, Finset.coe_singleton, Finset.coe_union, Finset.coe_empty,
      Set.empty_union]
    exact hswap
  apply (check_eq_true_iff (gout graph (∅ : Finset V) {treatment})
      (rule2Profile {outcome} {treatment} ((∅ : Finset V) ∪ adjustment))
      (gout_acyclic graph hAcyclic (∅ : Finset V) {treatment})
      (fun vertex =>
        DirectedGraph.isAcyclic_irrefl (gout graph (∅ : Finset V) {treatment})
          (gout_acyclic graph hAcyclic (∅ : Finset V) {treatment}) vertex)).2
  refine ⟨⟨?_, hsep⟩, ?_, ?_⟩
  · simp only [Condition.Compatible, rule2Profile]
    intro vertex hmember
    simp only [Finset.mem_inter, Finset.mem_singleton] at hmember
    exact absurd (hmember.1.symm.trans hmember.2) hdistinct
  · rw [Finset.disjoint_left]
    intro vertex hmember hunion
    simp only [rule2Profile, Finset.mem_singleton] at hmember
    subst hmember
    simp only [rule2Profile] at hunion
    rw [Finset.mem_union] at hunion
    rcases hunion with hempty | hmem
    · exact absurd hempty (Finset.notMem_empty _)
    · exact houtcome hmem
  · rw [Finset.disjoint_left]
    intro vertex hmember hunion
    simp only [rule2Profile, Finset.mem_singleton] at hmember
    simp only [rule2Profile] at hunion
    rw [Finset.mem_union] at hunion
    rcases hunion with hempty | hmem
    · exact absurd hempty (Finset.notMem_empty _)
    · exact hcrit.avoidsTreatment vertex (Finset.mem_coe.mpr hmem) hmember

/-! ## The door graph -/

/-- Covariate, treatment, outcome. -/
inductive Door
  | z
  | x
  | y
  deriving DecidableEq

instance : Fintype Door where
  elems := {Door.z, Door.x, Door.y}
  complete := by intro vertex; cases vertex <;> simp

/-- `Z → X`, `Z → Y`, `X → Y`. -/
def doorGraph : DirectedGraph Door where
  edges source target :=
    (source = .z ∧ target = .x) ∨ (source = .z ∧ target = .y) ∨
      (source = .x ∧ target = .y)

instance : DecidableRel doorGraph.edges := fun _ _ => by
  unfold doorGraph
  infer_instance

/-- Rank increases along every edge. -/
def doorRank : Door → ℕ
  | .z => 0
  | .x => 1
  | .y => 2

lemma door_edge_increases {source target : Door} (hedge : doorGraph.edges source target) :
    doorRank source < doorRank target := by
  cases source <;> cases target <;> simp [doorGraph, doorRank] at hedge ⊢

lemma door_reachable_rank {source target : Door} (hreach : doorGraph.Reachable source target) :
    doorRank source ≤ doorRank target := by
  induction hreach with
  | refl => exact le_rfl
  | step hedge _ ih =>
      exact le_trans (Nat.le_of_lt (door_edge_increases hedge)) ih

/-- The door graph is acyclic. -/
lemma doorAcyclic : doorGraph.IsAcyclic := by
  intro vertex ⟨source, hedge, hreach⟩
  exact (lt_irrefl _) <|
    lt_of_lt_of_le (door_edge_increases hedge) (door_reachable_rank hreach)

/-- The covariate. -/
def doorZ : Finset Door := {Door.z}

/-- The treatment. -/
def doorX : Finset Door := {Door.x}

/-- The outcome. -/
def doorY : Finset Door := {Door.y}

/-- Rule 2, checker order: outcome separated from treatment given the covariate. -/
theorem door_rule2_outcome_treatment_checked :
    FiniteDSeparation.check (gout doorGraph (∅ : Finset Door) doorX)
      (rule2Profile doorY doorX ((∅ : Finset Door) ∪ doorZ)) = true := by
  decide

/-- Rule 2, criterion order: treatment separated from outcome given the covariate. -/
theorem door_rule2_treatment_outcome_checked :
    FiniteDSeparation.check (gout doorGraph (∅ : Finset Door) doorX)
      (rule2Profile doorX doorY ((∅ : Finset Door) ∪ doorZ)) = true := by
  decide

/-- Rule 3 drops `do(X)` from `P(Z | do(X))`. -/
theorem door_rule3_covariate_checked :
    FiniteDSeparation.check
      (rule3Graph doorGraph (∅ : Finset Door) doorX (∅ : Finset Door))
      (rule3Profile doorZ doorX ((∅ : Finset Door) ∪ ∅)) = true := by
  decide

/-- `{Z}` meets the back-door criterion for treatment `X` and outcome `Y`. -/
theorem door_set_meets_backDoor :
    BackDoorCriterion doorGraph Door.x Door.y (doorZ : Set Door) where
  avoidsTreatment := by
    intro vertex hmember
    simp only [doorZ, Finset.mem_coe, Finset.mem_singleton] at hmember
    subst hmember
    decide
  avoidsDescendants := by
    intro vertex hmember hdesc
    simp only [doorZ, Finset.mem_coe, Finset.mem_singleton] at hmember
    subst hmember
    have hrank := door_reachable_rank (And.left hdesc)
    simp only [doorRank] at hrank
    exact Nat.not_succ_le_zero 0 hrank
  separated := by
    have haccepted :=
      (check_eq_true_iff (gout doorGraph (∅ : Finset Door) doorX)
        (rule2Profile doorX doorY ((∅ : Finset Door) ∪ doorZ))
        (gout_acyclic doorGraph doorAcyclic (∅ : Finset Door) doorX)
        (fun vertex =>
          DirectedGraph.isAcyclic_irrefl (gout doorGraph (∅ : Finset Door) doorX)
            (gout_acyclic doorGraph doorAcyclic (∅ : Finset Door) doorX) vertex)).1
        door_rule2_treatment_outcome_checked
    have hsep := haccepted.1.2
    rw [gout_emptyIncoming_eq_deleteOutgoing doorGraph doorX] at hsep
    simpa [rule2Profile, doorX, doorY, doorZ, Finset.coe_singleton, Finset.coe_union,
      Finset.coe_empty, Set.empty_union] using hsep

end Mettapedia.GSLT.Causality.DoCalculus

import Mettapedia.GSLT.Causality.DoCalculus.BackDoorCheck
import Mettapedia.GSLT.Causality.DoCalculus.Derivation
import Mettapedia.GSLT.Causality.DoCalculus.LatentMargin

/-!
# Back door for an arbitrary admissible set

`backDoor_exchange_checked` accepts rule 2 for every finset that meets
`BackDoorCriterion`, once the outcome lies outside that finset and is
distinct from the treatment. Rule 3's checker accepts
`P(adjustment | do(treatment)) = P(adjustment)` from the same criterion:
`avoidsTreatment` and `avoidsDescendants` put the adjustment set
d-separated from the treatment, given the empty set, once the arrows into
the treatment are deleted. The derivation below turns `P(y | do(x))` into
`Σ_z P(z) P(y | x, z)` from those two premises. That do-free sum reads
only the treatment, the outcome, and the adjustment set, so the query
`Factors` through the margin that sums out every other vertex.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.DoCalculus

open Mettapedia.ProbabilityTheory.BayesianNetworks
open BayesianNetwork
open DirectedGraph
open DSeparation
open Mettapedia.ProbabilityTheory.BayesianNetworks.FiniteDSeparation
open Mettapedia.GSLT.Core.NonFactorization
open scoped ENNReal

variable {V : Type} [Fintype V] [DecidableEq V]
variable (graph : DirectedGraph V) [DecidableRel graph.edges]

omit [Fintype V] in
lemma cup_comm (a b : Finset V) : a ∪ b = b ∪ a :=
  Finset.union_comm a b

omit [Fintype V] in
lemma cup_empty (a : Finset V) : a ∪ (∅ : Finset V) = a :=
  Finset.union_empty a

omit [Fintype V] in
lemma empty_cup (a : Finset V) : (∅ : Finset V) ∪ a = a :=
  Finset.empty_union a

omit [Fintype V] [DecidableEq V] in
lemma condSetEq {i n d i' n' d' : Finset V}
    (hi : i = i') (hn : n = n') (hd : d = d') :
    (MassExpr.cond i n d : MassExpr V) = .cond i' n' d' := by
  cases hi
  cases hn
  cases hd
  rfl

def backDoorQuery (treatment outcome : V) : MassExpr V :=
  .cond {treatment} ({outcome} ∪ {treatment}) {treatment}

def backDoorMarginalSource (treatment outcome : V) : MassExpr V :=
  .cond {treatment}
    ({treatment} ∪ {outcome} ∪ (∅ : Finset V))
    ({treatment} ∪ ∅)

omit [Fintype V] in
theorem backDoorQuery_eq_marginalSource (treatment outcome : V) :
    backDoorQuery treatment outcome = backDoorMarginalSource treatment outcome := by
  unfold backDoorQuery backDoorMarginalSource
  refine condSetEq rfl ?_ ?_
  · rw [cup_comm ({outcome} : Finset V) {treatment}]
    exact (cup_empty _).symm
  · exact (cup_empty _).symm

def backDoorOpened (treatment outcome : V) (adjustment : Finset V) : MassExpr V :=
  .sum adjustment
    (.cond {treatment}
      ({treatment} ∪ {outcome} ∪ adjustment ∪ (∅ : Finset V))
      ({treatment} ∪ ∅))

omit [Fintype V] [DecidableEq V] [DecidableRel graph.edges] in
lemma adjustment_disjoint_treatment
    {treatment outcome : V} {adjustment : Finset V}
    (hcrit : BackDoorCriterion graph treatment outcome (adjustment : Set V)) :
    Disjoint adjustment {treatment} := by
  rw [Finset.disjoint_left]
  intro vertex hmember htreatment
  rw [Finset.mem_singleton] at htreatment
  exact hcrit.avoidsTreatment vertex (Finset.mem_coe.mpr hmember) htreatment

omit [Fintype V] [DecidableEq V] in
lemma adjustment_disjoint_outcome
    {outcome : V} {adjustment : Finset V}
    (houtcome : outcome ∉ adjustment) :
    Disjoint adjustment {outcome} := by
  rw [Finset.disjoint_left]
  intro vertex hmember houtcomeMem
  rw [Finset.mem_singleton] at houtcomeMem
  subst houtcomeMem
  exact houtcome hmember

def openBackDoor
    {treatment outcome : V} {adjustment : Finset V}
    (hcrit : BackDoorCriterion graph treatment outcome (adjustment : Set V))
    (houtcome : outcome ∉ adjustment) :
    Deriv graph (backDoorMarginalSource treatment outcome)
      (backDoorOpened treatment outcome adjustment) :=
  .marginalIntro {treatment} {outcome} adjustment ∅
    (adjustment_disjoint_treatment graph hcrit)
    (adjustment_disjoint_outcome houtcome)
    (Finset.disjoint_empty_right _)

def backDoorChainedBody (treatment outcome : V) (adjustment : Finset V) : MassExpr V :=
  .mul
    (.cond {treatment}
      ({treatment} ∪ {outcome} ∪ adjustment ∪ (∅ : Finset V))
      ({treatment} ∪ adjustment ∪ ∅))
    (.cond {treatment}
      ({treatment} ∪ adjustment ∪ (∅ : Finset V))
      ({treatment} ∪ ∅))

def chainBackDoorBody (treatment outcome : V) (adjustment : Finset V) :
    Deriv graph
      (.cond {treatment}
        ({treatment} ∪ {outcome} ∪ adjustment ∪ (∅ : Finset V))
        ({treatment} ∪ ∅))
      (backDoorChainedBody treatment outcome adjustment) :=
  .chain {treatment} {outcome} adjustment ∅

def backDoorChained (treatment outcome : V) (adjustment : Finset V) : MassExpr V :=
  .sum adjustment (backDoorChainedBody treatment outcome adjustment)

def chainBackDoor (treatment outcome : V) (adjustment : Finset V) :
    Deriv graph (backDoorOpened treatment outcome adjustment)
      (backDoorChained treatment outcome adjustment) :=
  .sumBody (chainBackDoorBody graph treatment outcome adjustment)

def backDoorRule2Source (treatment outcome : V) (adjustment : Finset V) : MassExpr V :=
  .cond ((∅ : Finset V) ∪ {treatment})
    ((∅ : Finset V) ∪ {outcome} ∪ {treatment} ∪ adjustment)
    ((∅ : Finset V) ∪ {treatment} ∪ adjustment)

/-- `P(y | x, z)`, do-free. -/
def backDoorOutcomeObs (treatment outcome : V) (adjustment : Finset V) : MassExpr V :=
  .cond (∅ : Finset V)
    ((∅ : Finset V) ∪ {outcome} ∪ {treatment} ∪ adjustment)
    ((∅ : Finset V) ∪ {treatment} ∪ adjustment)

omit [Fintype V] in
theorem backDoorLeft_eq_rule2 (treatment outcome : V) (adjustment : Finset V) :
    (.cond {treatment}
        ({treatment} ∪ {outcome} ∪ adjustment ∪ (∅ : Finset V))
        ({treatment} ∪ adjustment ∪ ∅)) =
      backDoorRule2Source treatment outcome adjustment := by
  unfold backDoorRule2Source
  refine condSetEq ?_ ?_ ?_
  · exact (empty_cup _).symm
  · rw [cup_empty, cup_comm ({treatment} : Finset V) {outcome}, empty_cup]
  · rw [cup_empty, empty_cup]

def exchangeBackDoorOutcome
    {treatment outcome : V} {adjustment : Finset V}
    (hAcyclic : graph.IsAcyclic)
    (hcrit : BackDoorCriterion graph treatment outcome (adjustment : Set V))
    (houtcome : outcome ∉ adjustment)
    (hdistinct : outcome ≠ treatment) :
    Deriv graph (backDoorRule2Source treatment outcome adjustment)
      (backDoorOutcomeObs treatment outcome adjustment) :=
  .rule2 ∅ {outcome} {treatment} adjustment
    (backDoor_exchange_checked graph hAcyclic hcrit houtcome hdistinct)

def leftToBackDoorObs
    {treatment outcome : V} {adjustment : Finset V}
    (hAcyclic : graph.IsAcyclic)
    (hcrit : BackDoorCriterion graph treatment outcome (adjustment : Set V))
    (houtcome : outcome ∉ adjustment)
    (hdistinct : outcome ≠ treatment) :
    Deriv graph
      (.cond {treatment}
        ({treatment} ∪ {outcome} ∪ adjustment ∪ (∅ : Finset V))
        ({treatment} ∪ adjustment ∪ ∅))
      (backDoorOutcomeObs treatment outcome adjustment) :=
  .rewriteEq (backDoorLeft_eq_rule2 treatment outcome adjustment).symm rfl
    (exchangeBackDoorOutcome graph hAcyclic hcrit houtcome hdistinct)

def backDoorCovariateNow (treatment : V) (adjustment : Finset V) : MassExpr V :=
  .cond {treatment}
    ({treatment} ∪ adjustment ∪ (∅ : Finset V))
    ({treatment} ∪ ∅)

def backDoorAbsorbSource (treatment : V) (adjustment : Finset V) : MassExpr V :=
  .cond {treatment} (adjustment ∪ {treatment}) ((∅ : Finset V) ∪ {treatment})

omit [Fintype V] in
theorem backDoorRight_eq_absorb (treatment : V) (adjustment : Finset V) :
    backDoorCovariateNow treatment adjustment =
      backDoorAbsorbSource treatment adjustment := by
  unfold backDoorCovariateNow backDoorAbsorbSource
  refine condSetEq rfl ?_ ?_
  · rw [cup_empty, cup_comm]
  · rw [cup_empty]
    exact (empty_cup _).symm

def absorbBackDoorTreatment (treatment : V) (adjustment : Finset V) :
    Deriv graph (backDoorAbsorbSource treatment adjustment)
      (.cond {treatment} adjustment ∅) :=
  .absorb {treatment} adjustment ∅ {treatment} (fun _ hmember => hmember)

def backDoorRule3Source (treatment : V) (adjustment : Finset V) : MassExpr V :=
  .cond ((∅ : Finset V) ∪ {treatment})
    ((∅ : Finset V) ∪ adjustment ∪ ∅)
    ((∅ : Finset V) ∪ ∅)

/-- `P(z)`, do-free. -/
def backDoorCovariateObs (adjustment : Finset V) : MassExpr V :=
  .cond (∅ : Finset V)
    ((∅ : Finset V) ∪ adjustment ∪ ∅)
    ((∅ : Finset V) ∪ ∅)

omit [Fintype V] in
theorem backDoorAbsorb_eq_rule3 (treatment : V) (adjustment : Finset V) :
    (.cond {treatment} adjustment ∅) = backDoorRule3Source treatment adjustment := by
  unfold backDoorRule3Source
  refine condSetEq ?_ ?_ ?_
  · exact (empty_cup _).symm
  · rw [empty_cup]
    exact (cup_empty _).symm
  · exact (cup_empty _).symm

omit [Fintype V] [DecidableEq V] [DecidableRel graph.edges] in
/-- An active triple given the empty conditioning set is not a collider:
a collider is active only when it or a descendant is conditioned on. -/
lemma not_collider_of_active_empty
    {G : DirectedGraph V} {triple : PathTriple G}
    (hact : IsActive G (∅ : Set V) triple) : ¬ IsCollider G triple := by
  intro hcol
  rcases active_collider_desc_in_Z G (∅ : Set V) triple hact hcol with
    hmember | ⟨_, _, hmember⟩
  · exact Set.notMem_empty _ hmember
  · exact Set.notMem_empty _ hmember

omit [Fintype V] [DecidableEq V] [DecidableRel graph.edges] in
lemma backDoor_pathEndpoints_cons {a b c : V} {rest : List V} {s e : V}
    (h : PathEndpoints (a :: b :: c :: rest) = some (s, e)) :
    s = a ∧ PathEndpoints (b :: c :: rest) = some (b, e) := by
  simp only [PathEndpoints] at h
  injection h with hpair
  refine ⟨((Prod.ext_iff.mp hpair).1).symm, ?_⟩
  simp only [PathEndpoints]
  have he : e = (b :: c :: rest).getLast (by simp) :=
    ((Prod.ext_iff.mp hpair).2).symm
  have hlast :
      (b :: c :: rest).getLast (by simp) = (c :: rest).getLast (by simp) := by
    simp [List.getLast_cons]
  simp [he, hlast]

omit [Fintype V] [DecidableEq V] [DecidableRel graph.edges] in
/-- An active trail given the empty set that ends at a vertex with no incoming
edge is the reverse of a directed path. The sink reaches the start, and the
first step of the trail points back toward the start. -/
lemma sink_reaches_active_start
    {H : DirectedGraph V} {sink : V}
    (hno : ∀ u, ¬ H.edges u sink)
    {p : List V}
    (hact : ActiveTrail H (∅ : Set V) p) :
    ∀ s, PathEndpoints p = some (s, sink) →
      H.Reachable sink s ∧
        ∀ mid rest, p = s :: mid :: rest → H.edges mid s := by
  refine ActiveTrail.rec
    (motive := fun trail _ =>
      ∀ s, PathEndpoints trail = some (s, sink) →
        H.Reachable sink s ∧
          ∀ mid rest, trail = s :: mid :: rest → H.edges mid s)
    (fun v s hpe => by
      simp only [PathEndpoints] at hpe
      injection hpe with hpair
      have hsv : v = s := (Prod.ext_iff.mp hpair).1
      have hvs : v = sink := (Prod.ext_iff.mp hpair).2
      cases hsv
      cases hvs
      refine ⟨reachable_refl H sink, ?_⟩
      intro mid rest hp
      have hlen := congrArg List.length hp
      simp only [List.length_cons, List.length_nil] at hlen
      omega)
    (fun {u v} (hEdge : UndirectedEdge H u v) s hpe => by
      simp only [PathEndpoints, List.getLast_singleton] at hpe
      injection hpe with hpair
      have hsu : u = s := (Prod.ext_iff.mp hpair).1
      have hvv : v = sink := (Prod.ext_iff.mp hpair).2
      have hout : H.edges sink s := by
        rw [← hsu, ← hvv]
        rcases hEdge with hinto | hout
        · rw [hvv] at hinto
          exact absurd hinto (hno u)
        · exact hout
      refine ⟨edge_reachable H hout, ?_⟩
      intro mid rest hp
      rw [← hsu] at hp
      injection hp with _ htail
      injection htail with hmid hnil
      cases hmid
      cases hnil
      rw [hvv]
      exact hout)
    (fun {a b c : V} {rest : List V} hab hbc hac hAct _hTail ih s hpe => by
      have hsplit := backDoor_pathEndpoints_cons hpe
      have hs : s = a := hsplit.1
      have hpeTail := hsplit.2
      cases hs
      have ihb := ih b hpeTail
      have hcb : H.edges c b := ihb.2 c rest rfl
      have hnot : ¬ IsCollider H ⟨a, b, c, hab, hbc, hac⟩ :=
        not_collider_of_active_empty hAct
      have hba : H.edges b a := by
        rcases hab with hab | hab
        · exact absurd hab (fun hin => hnot ⟨hin, hcb⟩)
        · exact hab
      refine ⟨reachable_trans H ihb.1 (edge_reachable H hba), ?_⟩
      intro mid rest' hp
      injection hp with _ htail
      injection htail with hmid _
      cases hmid
      exact hba)
    hact

omit [Fintype V] [DecidableEq V] [DecidableRel graph.edges] in
/-- After the arrows into `treatment` are deleted, a set that avoids the
descendants of `treatment` is d-separated from `treatment` given nothing. -/
lemma dsep_adjustment_treatment_incoming
    {treatment : V} {adjustment : Finset V}
    (hdesc : ∀ z ∈ (adjustment : Set V), z ∉ graph.descendants treatment) :
    DSeparatedFull (deleteIncoming graph {treatment})
      (adjustment : Set V) ({treatment} : Set V) (∅ : Set V) := by
  intro z hz vertex hvertex hne htrail
  have htreatment : vertex = treatment := by
    simpa [Set.mem_singleton_iff] using hvertex
  subst htreatment
  rcases htrail with ⟨_p, _, hends, hact⟩
  have hno : ∀ u, ¬ (deleteIncoming graph ({vertex} : Finset V)).edges u vertex := by
    intro u hedge
    simp only [deleteIncoming] at hedge
    rcases hedge with ⟨_, hnot⟩
    exact hnot (Finset.mem_singleton_self vertex)
  have hreach :=
    (sink_reaches_active_start hno hact z hends).1
  have hsub : ∀ u v,
      (deleteIncoming graph ({vertex} : Finset V)).edges u v → graph.edges u v := by
    intro u v hedge
    simp only [deleteIncoming] at hedge
    exact hedge.1
  exact hdesc z hz
    ⟨reachable_of_edge_subset graph hsub hreach, hne⟩

/-- Rule 3's checker for deleting `do(treatment)` from the adjustment margin.
`BackDoorCriterion.avoidsDescendants` is the separation; `avoidsTreatment`
keeps the adjustment set off the deleted vertex, which is the checker's
support. -/
theorem backDoor_rule3_checked
    {treatment outcome : V} {adjustment : Finset V}
    (hAcyclic : graph.IsAcyclic)
    (hcrit : BackDoorCriterion graph treatment outcome (adjustment : Set V)) :
    FiniteDSeparation.check
      (rule3Graph graph (∅ : Finset V) {treatment} (∅ : Finset V))
      (rule3Profile adjustment {treatment} ((∅ : Finset V) ∪ ∅)) = true := by
  have hgraph :
      rule3Graph graph (∅ : Finset V) {treatment} (∅ : Finset V) =
        deleteIncoming graph {treatment} := by
    unfold rule3Graph
    rw [deleteIncoming_empty]
    congr 1
    ext vertex
    simp only [zOfFinset, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro hmember
      exact hmember.1
    · intro hmember
      refine ⟨hmember, ?_⟩
      intro w hw
      exact absurd hw (Finset.notMem_empty w)
  have hAcy : (rule3Graph graph (∅ : Finset V) {treatment} (∅ : Finset V)).IsAcyclic := by
    rw [hgraph]
    exact deleteIncoming_acyclic graph hAcyclic {treatment}
  apply (check_eq_true_iff
      (rule3Graph graph (∅ : Finset V) {treatment} (∅ : Finset V))
      (rule3Profile adjustment {treatment} ((∅ : Finset V) ∪ ∅))
      hAcy
      (fun vertex =>
        isAcyclic_irrefl
          (rule3Graph graph (∅ : Finset V) {treatment} (∅ : Finset V))
          hAcy vertex)).2
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro vertex hmember
    simp only [rule3Profile, Finset.mem_inter, Finset.mem_singleton] at hmember
    exact absurd hmember.2
      (hcrit.avoidsTreatment vertex (Finset.mem_coe.mpr hmember.1))
  · have hsep :=
      dsep_adjustment_treatment_incoming graph hcrit.avoidsDescendants
    rw [← hgraph] at hsep
    simpa [rule3Profile, Finset.coe_singleton, Finset.coe_union, Finset.coe_empty,
      Set.empty_union] using hsep
  · simp [rule3Profile, Finset.disjoint_empty_right]
  · simp [rule3Profile]

def deleteBackDoorTreatment
    (treatment outcome : V) (adjustment : Finset V)
    (hAcyclic : graph.IsAcyclic)
    (hcrit : BackDoorCriterion graph treatment outcome (adjustment : Set V)) :
    Deriv graph (backDoorRule3Source treatment adjustment)
      (backDoorCovariateObs adjustment) :=
  .rule3 ∅ adjustment {treatment} ∅
    (backDoor_rule3_checked graph hAcyclic hcrit)

def rightToBackDoorObs
    (treatment outcome : V) (adjustment : Finset V)
    (hAcyclic : graph.IsAcyclic)
    (hcrit : BackDoorCriterion graph treatment outcome (adjustment : Set V)) :
    Deriv graph (backDoorCovariateNow treatment adjustment)
      (backDoorCovariateObs adjustment) :=
  .trans
    (.rewriteEq (backDoorRight_eq_absorb treatment adjustment).symm rfl
      (absorbBackDoorTreatment graph treatment adjustment))
    (.rewriteEq (backDoorAbsorb_eq_rule3 treatment adjustment).symm rfl
      (deleteBackDoorTreatment graph treatment outcome adjustment hAcyclic hcrit))

def backDoorAdjustedBody (treatment outcome : V) (adjustment : Finset V) : MassExpr V :=
  .mul (backDoorOutcomeObs treatment outcome adjustment) (backDoorCovariateObs adjustment)

def adjustBackDoorBody
    {treatment outcome : V} {adjustment : Finset V}
    (hAcyclic : graph.IsAcyclic)
    (hcrit : BackDoorCriterion graph treatment outcome (adjustment : Set V))
    (houtcome : outcome ∉ adjustment)
    (hdistinct : outcome ≠ treatment) :
    Deriv graph (backDoorChainedBody treatment outcome adjustment)
      (backDoorAdjustedBody treatment outcome adjustment) :=
  .trans
    (.mulLeft (leftToBackDoorObs graph hAcyclic hcrit houtcome hdistinct))
    (.mulRight
      (rightToBackDoorObs graph treatment outcome adjustment hAcyclic hcrit))

/-- `Σ_z P(z) P(y | x, z)`. -/
def backDoorExpr (treatment outcome : V) (adjustment : Finset V) : MassExpr V :=
  .sum adjustment (backDoorAdjustedBody treatment outcome adjustment)

def adjustBackDoor
    {treatment outcome : V} {adjustment : Finset V}
    (hAcyclic : graph.IsAcyclic)
    (hcrit : BackDoorCriterion graph treatment outcome (adjustment : Set V))
    (houtcome : outcome ∉ adjustment)
    (hdistinct : outcome ≠ treatment) :
    Deriv graph (backDoorChained treatment outcome adjustment)
      (backDoorExpr treatment outcome adjustment) :=
  .sumBody (adjustBackDoorBody graph hAcyclic hcrit houtcome hdistinct)

def backDoorFromMarginal
    {treatment outcome : V} {adjustment : Finset V}
    (hAcyclic : graph.IsAcyclic)
    (hcrit : BackDoorCriterion graph treatment outcome (adjustment : Set V))
    (houtcome : outcome ∉ adjustment)
    (hdistinct : outcome ≠ treatment) :
    Deriv graph (backDoorMarginalSource treatment outcome)
      (backDoorExpr treatment outcome adjustment) :=
  .trans (openBackDoor graph hcrit houtcome)
    (.trans (chainBackDoor graph treatment outcome adjustment)
      (adjustBackDoor graph hAcyclic hcrit houtcome hdistinct))

/-- From `P(y | do(x))` to the back-door adjustment, for any admissible set. -/
def backDoorDerivOf
    {treatment outcome : V} {adjustment : Finset V}
    (hAcyclic : graph.IsAcyclic)
    (hcrit : BackDoorCriterion graph treatment outcome (adjustment : Set V))
    (houtcome : outcome ∉ adjustment)
    (hdistinct : outcome ≠ treatment) :
    Deriv graph (backDoorQuery treatment outcome)
      (backDoorExpr treatment outcome adjustment) :=
  .rewriteEq (backDoorQuery_eq_marginalSource treatment outcome).symm rfl
    (backDoorFromMarginal graph hAcyclic hcrit houtcome hdistinct)

omit [Fintype V] in
theorem backDoorExpr_doFree (treatment outcome : V) (adjustment : Finset V) :
    doFree (backDoorExpr treatment outcome adjustment) = true := by
  simp only [backDoorExpr, backDoorAdjustedBody, backDoorOutcomeObs,
    backDoorCovariateObs, doFree, Bool.and_eq_true]
  decide

section Denote

variable {β : Type}
variable [Fintype β] [DecidableEq β] [Inhabited β] [MeasurableSpace β]
variable [MeasurableSingletonClass β] [StandardBorelSpace β]
variable [StandardBorelSpace (V → β)]

theorem backDoor_ends_agree
    {treatment outcome : V} {adjustment : Finset V}
    (hAcyclic : graph.IsAcyclic)
    (hcrit : BackDoorCriterion graph treatment outcome (adjustment : Set V))
    (houtcome : outcome ∉ adjustment)
    (hdistinct : outcome ≠ treatment)
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (anchor : V → β)
    (hpos : Positive graph hAcyclic
      (backDoorDerivOf graph hAcyclic hcrit houtcome hdistinct) cpt anchor) :
    doFree (backDoorExpr treatment outcome adjustment) = true ∧
      gDenote graph hAcyclic cpt anchor (backDoorQuery treatment outcome) =
        gDenote graph hAcyclic cpt anchor
          (backDoorExpr treatment outcome adjustment) :=
  ⟨backDoorExpr_doFree treatment outcome adjustment,
    deriv_gDenote graph hAcyclic
      (backDoorDerivOf graph hAcyclic hcrit houtcome hdistinct)
      cpt anchor hpos⟩

def BackDoorRows
    {treatment outcome : V} {adjustment : Finset V}
    (hAcyclic : graph.IsAcyclic)
    (hcrit : BackDoorCriterion graph treatment outcome (adjustment : Set V))
    (houtcome : outcome ∉ adjustment)
    (hdistinct : outcome ≠ treatment)
    (anchor : V → β) :=
  {cpt : (network (β := β) graph hAcyclic).DiscreteCPT //
    Positive graph hAcyclic
      (backDoorDerivOf graph hAcyclic hcrit houtcome hdistinct) cpt anchor}

theorem backDoor_query_factors_joint
    {treatment outcome : V} {adjustment : Finset V}
    (hAcyclic : graph.IsAcyclic)
    (hcrit : BackDoorCriterion graph treatment outcome (adjustment : Set V))
    (houtcome : outcome ∉ adjustment)
    (hdistinct : outcome ≠ treatment)
    (anchor : V → β) :
    Factors
      (fun cpt : BackDoorRows graph hAcyclic hcrit houtcome hdistinct anchor =>
        cpt.1.jointWeight)
      (fun cpt =>
        gDenote graph hAcyclic cpt.1 anchor (backDoorQuery treatment outcome)) := by
  refine ⟨fun joint => denoteJoint anchor joint (backDoorExpr treatment outcome adjustment),
    fun cpt => ?_⟩
  have hends :=
    (backDoor_ends_agree graph hAcyclic hcrit houtcome hdistinct cpt.1 anchor cpt.2).2
  change denoteJoint anchor cpt.1.jointWeight (backDoorExpr treatment outcome adjustment) =
    gDenote graph hAcyclic cpt.1 anchor (backDoorQuery treatment outcome)
  rw [hends]
  exact (denote_eq_joint graph hAcyclic (backDoorExpr treatment outcome adjustment)
    (backDoorExpr_doFree treatment outcome adjustment) cpt.1 anchor).symm

/-- Vertices the back-door sum does not read. -/
def backDoorLatent (treatment outcome : V) (adjustment : Finset V) : Finset V :=
  Finset.univ \ ({treatment} ∪ {outcome} ∪ adjustment)

omit graph [DecidableRel graph.edges] [MeasurableSpace β] [MeasurableSingletonClass β]
  [StandardBorelSpace β] [StandardBorelSpace (V → β)] in
lemma disjoint_backDoorLatent
    {treatment outcome : V} {adjustment fixed : Finset V}
    (hsub : fixed ⊆ {treatment} ∪ {outcome} ∪ adjustment) :
    Disjoint fixed (backDoorLatent treatment outcome adjustment) := by
  rw [backDoorLatent, Finset.disjoint_left]
  intro vertex hfixed hlatent
  exact (Finset.mem_sdiff.mp hlatent).2 (hsub hfixed)

omit graph [DecidableRel graph.edges] [MeasurableSpace β] [MeasurableSingletonClass β]
  [StandardBorelSpace β] [StandardBorelSpace (V → β)] in
lemma denoteSlice_of_margin
    (L fixed : Finset V) (hdisj : Disjoint fixed L)
    (anchor : V → β) (joint : (V → β) → ℝ≥0∞) :
    denoteJoint anchor joint (.slice (∅ : Finset V) fixed) =
      ∑ out : {v // v ∉ L} → β,
        if agreesOn fixed anchor (glue L (fun _ => default) out) = true then
          observedMargin L joint out else 0 := by
  simp only [denoteJoint]
  rw [sum_glue L, Finset.sum_comm]
  refine Finset.sum_congr rfl fun out _ => ?_
  have hagree : ∀ inn,
      agreesOn fixed anchor (glue L inn out) =
        agreesOn fixed anchor (glue L (fun _ => default) out) :=
    fun inn => agrees_glue_indep hdisj anchor inn (fun _ => default) out
  by_cases hp : agreesOn fixed anchor (glue L (fun _ => default) out) = true
  · rw [if_pos hp]
    unfold observedMargin
    refine Finset.sum_congr rfl fun inn _ => ?_
    have hpred : agreesOn fixed anchor (glue L inn out) = true := by
      rw [hagree inn]
      exact hp
    rw [if_pos hpred]
  · rw [if_neg hp]
    refine Finset.sum_eq_zero fun inn _ => ?_
    rw [if_neg ?_]
    rw [hagree inn]
    exact hp

omit graph [DecidableRel graph.edges] [MeasurableSpace β] [MeasurableSingletonClass β]
  [StandardBorelSpace β] [StandardBorelSpace (V → β)] in
/-- `Σ_z P(z) P(y | x, z)` read from a margin that has already summed out `L`. -/
noncomputable def backDoorFromMargin
    (treatment outcome : V) (adjustment : Finset V) (anchor : V → β)
    (margin : ({v // v ∉ backDoorLatent treatment outcome adjustment} → β) → ℝ≥0∞) :
    ℝ≥0∞ :=
  let L := backDoorLatent treatment outcome adjustment
  ∑ inn : {v // v ∈ adjustment} → β,
    let shifted := extendAnchor adjustment inn anchor
    ((∑ out : {v // v ∉ L} → β,
        if agreesOn ((∅ : Finset V) ∪ {outcome} ∪ {treatment} ∪ adjustment)
            shifted (glue L (fun _ => default) out) = true then
          margin out else 0) /
      (∑ out : {v // v ∉ L} → β,
        if agreesOn ((∅ : Finset V) ∪ {treatment} ∪ adjustment)
            shifted (glue L (fun _ => default) out) = true then
          margin out else 0)) *
    ((∑ out : {v // v ∉ L} → β,
        if agreesOn ((∅ : Finset V) ∪ adjustment ∪ ∅)
            shifted (glue L (fun _ => default) out) = true then
          margin out else 0) /
      (∑ out : {v // v ∉ L} → β,
        if agreesOn ((∅ : Finset V) ∪ ∅)
            shifted (glue L (fun _ => default) out) = true then
          margin out else 0))

omit graph [DecidableRel graph.edges] [MeasurableSpace β] [MeasurableSingletonClass β]
  [StandardBorelSpace β] [StandardBorelSpace (V → β)] in
theorem backDoorExpr_through_margin
    (treatment outcome : V) (adjustment : Finset V)
    (anchor : V → β) (joint : (V → β) → ℝ≥0∞) :
    denoteJoint anchor joint (backDoorExpr treatment outcome adjustment) =
      backDoorFromMargin treatment outcome adjustment anchor
        (observedMargin (backDoorLatent treatment outcome adjustment) joint) := by
  have hnum : Disjoint ((∅ : Finset V) ∪ {outcome} ∪ {treatment} ∪ adjustment)
      (backDoorLatent treatment outcome adjustment) := by
    refine disjoint_backDoorLatent ?_
    intro vertex hmember
    simp only [Finset.mem_union, Finset.mem_singleton] at hmember ⊢
    tauto
  have hden : Disjoint ((∅ : Finset V) ∪ {treatment} ∪ adjustment)
      (backDoorLatent treatment outcome adjustment) := by
    refine disjoint_backDoorLatent ?_
    intro vertex hmember
    simp only [Finset.mem_union, Finset.mem_singleton] at hmember ⊢
    tauto
  have hcov : Disjoint ((∅ : Finset V) ∪ adjustment ∪ ∅)
      (backDoorLatent treatment outcome adjustment) := by
    refine disjoint_backDoorLatent ?_
    intro vertex hmember
    simp only [Finset.mem_union, Finset.mem_singleton] at hmember ⊢
    tauto
  have hempty : Disjoint ((∅ : Finset V) ∪ ∅)
      (backDoorLatent treatment outcome adjustment) := by
    refine disjoint_backDoorLatent ?_
    intro vertex hmember
    simp only [Finset.mem_union, Finset.mem_singleton] at hmember ⊢
    tauto
  rw [backDoorExpr, denoteJoint.eq_5]
  unfold backDoorFromMargin
  refine Finset.sum_congr rfl fun inn _ => ?_
  rw [backDoorAdjustedBody, denoteJoint.eq_3]
  congr 1
  · rw [backDoorOutcomeObs, denoteJoint.eq_2]
    congr 1
    · exact denoteSlice_of_margin _ _ hnum _ joint
    · exact denoteSlice_of_margin _ _ hden _ joint
  · rw [backDoorCovariateObs, denoteJoint.eq_2]
    congr 1
    · exact denoteSlice_of_margin _ _ hcov _ joint
    · exact denoteSlice_of_margin _ _ hempty _ joint

/-- For any admissible set, `P(y | do(x))` `Factors` through the margin of the
treatment, the outcome, and that set. -/
theorem backDoor_query_factors_margin
    {treatment outcome : V} {adjustment : Finset V}
    (hAcyclic : graph.IsAcyclic)
    (hcrit : BackDoorCriterion graph treatment outcome (adjustment : Set V))
    (houtcome : outcome ∉ adjustment)
    (hdistinct : outcome ≠ treatment)
    (anchor : V → β) :
    Factors
      (fun cpt : BackDoorRows graph hAcyclic hcrit houtcome hdistinct anchor =>
        observedMargin (backDoorLatent treatment outcome adjustment)
          (fun assignment => cpt.1.jointWeight assignment))
      (fun cpt =>
        gDenote graph hAcyclic cpt.1 anchor (backDoorQuery treatment outcome)) := by
  refine ⟨fun margin =>
      backDoorFromMargin treatment outcome adjustment anchor margin, fun cpt => ?_⟩
  have hends :=
    (backDoor_ends_agree graph hAcyclic hcrit houtcome hdistinct cpt.1 anchor cpt.2).2
  change backDoorFromMargin treatment outcome adjustment anchor
      (observedMargin (backDoorLatent treatment outcome adjustment)
        (fun assignment => cpt.1.jointWeight assignment)) =
    gDenote graph hAcyclic cpt.1 anchor (backDoorQuery treatment outcome)
  rw [hends, denote_eq_joint graph hAcyclic (backDoorExpr treatment outcome adjustment)
    (backDoorExpr_doFree treatment outcome adjustment) cpt.1 anchor]
  exact (backDoorExpr_through_margin treatment outcome adjustment anchor
    (fun assignment => cpt.1.jointWeight assignment)).symm

end Denote

end Mettapedia.GSLT.Causality.DoCalculus

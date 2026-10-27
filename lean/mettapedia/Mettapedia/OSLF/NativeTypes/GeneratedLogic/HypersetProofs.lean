import Mettapedia.OSLF.NativeTypes.GeneratedLogic.HypersetGraphs
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipProofTerms

/-!
# Hyperset verdicts as theorems of the package of set theory

The package of set theory has set induction among its laws, so no set in it is its own member: a hyperset such as
Ω = {Ω} is not one of its sets. Under anti-foundation, a finite membership graph pictures hypersets, and inside the
well-founded sets the standard reading of a hyperset is a graph up to bisimilarity. So hyperset verdicts become
theorems of the package about coded graphs.

- **A coding** (`GraphCode`) gives each node a hereditary term, the codes of different nodes presenting different
  sets: von Neumann numerals, for example (`numeralCode`).
- **An edge** (`edgeFormula`) is a finite disjunction, over the graph's edges, of forward and existential
  descriptions of the two codes.
- **A native type at a node** (`graphFormula`) becomes a sentence about the code, for the fragment of steps,
  connectives and fixed points: a step is an edge to some set, and a fixed point a predicate on all sets.
- **The compiler** (`proveGraph`, `refuteGraph`) proves the sentence from the laws of the empty set, the power set and
  separation when the graph's evaluation accepts the type at the node, and its negation otherwise. A step goes to the
  set a child's code describes; an every-step case splits on which edge a set is reached by, and an edge from another
  node is impossible because its code presents another set. A least fixed point is proved stage by stage, a greatest
  one by the predicate "described by the code of a node of the stable stage".
- **Each derivation is a closed term of the package** (`graphVerdict`).

The reading of the sentences among the sets, and through decoration among the hypersets, is in
`HypersetMeaning`.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Logic.HOL (Ty Ctx Var Term ClosedFormula weaken rename subst instantiate Subst Rename
  ProofSyntaxModulo weakenHyps)
open Mettapedia.Logic.HOL.ImpredicativeConnectives (truth falsity conjunctionFormula disjunctionFormula
  existentialInline subst_conjunctionFormula subst_disjunctionFormula subst_existentialInline)
open Mettapedia.Logic.HOL.ImpredicativeConnectives.Modulo (truthIntro conjunctionIntro conjunctionLeft
  conjunctionRight disjunctionLeft disjunctionRight disjunctionElim existentialIntro existentialElim)
open Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation (Symbol member)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.HypersetGraphs (MembershipGraph)

/-! ## Coding a graph in the sets -/

/-- **A coding of a graph's nodes in the hereditarily finite sets**: hereditary terms presenting different sets for
different nodes. -/
structure GraphCode (graph : MembershipGraph) where
  code : Fin graph.size → Pattern
  hereditary : ∀ node, IsHF (code node)
  apart : ∀ first second, first ≠ second → zfOf (code first) ≠ zfOf (code second)

/-- The edges of a graph. -/
def graphEdges (graph : MembershipGraph) : List (Fin graph.size × Fin graph.size) :=
  (List.finRange graph.size).flatMap fun node => (graph.children node).map fun child => (node, child)

theorem mem_graphEdges {graph : MembershipGraph} {node child : Fin graph.size} :
    (node, child) ∈ graphEdges graph ↔ child ∈ graph.children node := by
  simp [graphEdges, List.mem_flatMap, List.mem_map, List.mem_finRange]

section Formulas

variable {graph : MembershipGraph} (coding : GraphCode graph)

/-- **An edge between two sets**: for one of the listed edges, the first is described by the code of its node and the
second by the code of its child, forward and existentially. -/
def edgeFormula : List (Fin graph.size × Fin graph.size) → {Γ : Ctx Unit} → Term Symbol Γ setTy →
    Term Symbol Γ setTy → Term Symbol Γ .prop
  | [], _, _, _ => falsity
  | entry :: rest, _, a, b => disjunctionFormula
      (conjunctionFormula (describesSome (membersOf (coding.code entry.1)) a)
        (describesSome (membersOf (coding.code entry.2)) b))
      (edgeFormula rest a b)

/-- The steps-and-fixed-points fragment. -/
def Formula.graphFragment : {n : ℕ} → Formula n → Bool
  | _, .top | _, .bot | _, .var _ => true
  | _, .and left right | _, .or left right => Formula.graphFragment left && Formula.graphFragment right
  | _, .mu inner | _, .nu inner => Formula.graphFragment inner
  | _, .possibly label inner | _, .necessarily label inner => !label.isContext && Formula.graphFragment inner
  | _, _ => false

/-- **A native type of the graph, about the set term `x`**: a step is an edge to some set, and the fixed points are
predicates on all sets. Outside the fragment it is falsity. -/
def graphFormula : {n : ℕ} → Formula n → {Γ : Ctx Unit} → Term Symbol Γ setTy → (Fin n → Term Symbol Γ predTy) →
    Term Symbol Γ .prop
  | _, .top, _, _, _ => truth
  | _, .bot, _, _, _ => falsity
  | _, .and left right, _, x, env => conjunctionFormula (graphFormula left x env) (graphFormula right x env)
  | _, .or left right, _, x, env => disjunctionFormula (graphFormula left x env) (graphFormula right x env)
  | _, .var index, _, x, env => .app (env index) x
  | _, .mu inner, _, x, env =>
    .all (σ := predTy) (.imp (.all (σ := setTy) (.imp (graphFormula inner (.var .vz) (underFixedPoint env))
      (.app (.var (.vs .vz)) (.var .vz)))) (.app (.var .vz) (weaken x)))
  | _, .nu inner, _, x, env =>
    existentialInline (σ := predTy) (conjunctionFormula (.all (σ := setTy) (.imp (.app (.var (.vs .vz)) (.var .vz))
      (graphFormula inner (.var .vz) (underFixedPoint env)))) (.app (.var .vz) (weaken x)))
  | _, .possibly label inner, _, x, env =>
    if memberLabel label then
      existentialInline (σ := setTy) (conjunctionFormula (edgeFormula coding (graphEdges graph) (weaken x) (.var .vz))
        (graphFormula inner (.var .vz) (underElement env)))
    else falsity
  | _, .necessarily label inner, _, x, env =>
    if memberLabel label then
      .all (σ := setTy) (.imp (edgeFormula coding (graphEdges graph) (weaken x) (.var .vz))
        (graphFormula inner (.var .vz) (underElement env)))
    else truth
  | _, _, _, _, _ => falsity

theorem subst_edgeFormula {Γ Γ' : Ctx Unit} (θ : Subst Symbol Γ Γ') :
    ∀ (edges : List (Fin graph.size × Fin graph.size)) (a b : Term Symbol Γ setTy),
      subst θ (edgeFormula coding edges a b) = edgeFormula coding edges (subst θ a) (subst θ b)
  | [], _, _ => rfl
  | entry :: rest, a, b => by
    simp only [edgeFormula, subst_disjunctionFormula, subst_conjunctionFormula, subst_describesSome,
      subst_edgeFormula θ rest a b]

theorem subst_graphFormula {Γ Γ' : Ctx Unit} (θ : Subst Symbol Γ Γ') :
    ∀ {n : ℕ} (formula : Formula n), Formula.graphFragment formula = true → ∀ (x : Term Symbol Γ setTy)
      (env : Fin n → Term Symbol Γ predTy),
      subst θ (graphFormula coding formula x env) = graphFormula coding formula (subst θ x) fun index => subst θ (env index)
  | _, .top, _, _, _ => rfl
  | _, .bot, _, _, _ => rfl
  | _, .and left right, fragment, x, env => by
    simp only [Formula.graphFragment, Bool.and_eq_true] at fragment
    simp only [graphFormula, subst_conjunctionFormula, subst_graphFormula θ left fragment.1,
      subst_graphFormula θ right fragment.2]
  | _, .or left right, fragment, x, env => by
    simp only [Formula.graphFragment, Bool.and_eq_true] at fragment
    simp only [graphFormula, subst_disjunctionFormula, subst_graphFormula θ left fragment.1,
      subst_graphFormula θ right fragment.2]
  | _, .var index, _, x, env => rfl
  | _, .mu inner, fragment, x, env => by
    simp only [Formula.graphFragment] at fragment
    simp only [graphFormula, subst, subst_graphFormula (Subst.lift (Subst.lift θ)) inner fragment,
      subst_underFixedPoint, Mettapedia.Logic.HOL.subst_weaken]
    rfl
  | _, .nu inner, fragment, x, env => by
    simp only [Formula.graphFragment] at fragment
    simp only [graphFormula, subst_existentialInline, subst_conjunctionFormula, subst,
      subst_graphFormula (Subst.lift (Subst.lift θ)) inner fragment, subst_underFixedPoint,
      Mettapedia.Logic.HOL.subst_weaken]
    rfl
  | _, .possibly label inner, fragment, x, env => by
    simp only [Formula.graphFragment, Bool.and_eq_true] at fragment
    replace fragment := fragment.2
    by_cases labelled : memberLabel label
    · simp only [graphFormula, if_pos labelled, subst_existentialInline, subst_conjunctionFormula,
        subst_edgeFormula, subst_graphFormula (Subst.lift θ) inner fragment, subst_underElement,
        Mettapedia.Logic.HOL.subst_weaken]
      rfl
    · simp only [graphFormula, if_neg labelled]
      rfl
  | _, .necessarily label inner, fragment, x, env => by
    simp only [Formula.graphFragment, Bool.and_eq_true] at fragment
    replace fragment := fragment.2
    by_cases labelled : memberLabel label
    · simp only [graphFormula, if_pos labelled, subst, subst_edgeFormula,
        subst_graphFormula (Subst.lift θ) inner fragment, subst_underElement, Mettapedia.Logic.HOL.subst_weaken]
      rfl
    · simp only [graphFormula, if_neg labelled]
      rfl

theorem weaken_graphFormula {Γ : Ctx Unit} {σ : Ty Unit} {n : ℕ} (formula : Formula n)
    (fragment : Formula.graphFragment formula = true) (x : Term Symbol Γ setTy) (env : Fin n → Term Symbol Γ predTy) :
    weaken (σ := σ) (graphFormula coding formula x env) =
      graphFormula coding formula (weaken x) fun index => weaken (env index) := by
  rw [weaken_eq_subst, subst_graphFormula coding _ formula fragment]
  simp only [← weaken_eq_subst]

theorem weaken_edgeFormula {Γ : Ctx Unit} {σ : Ty Unit} (edges : List (Fin graph.size × Fin graph.size))
    (a b : Term Symbol Γ setTy) :
    weaken (σ := σ) (edgeFormula coding edges a b) = edgeFormula coding edges (weaken a) (weaken b) := by
  rw [weaken_eq_subst, subst_edgeFormula, ← weaken_eq_subst, ← weaken_eq_subst]

end Formulas

/-! ## Edges in derivations -/

section Edges

variable {graph : MembershipGraph} (coding : GraphCode graph) {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)}

/-- **An edge, from descriptions of the two sets by the codes of a listed edge.** -/
def edgeIntro {a b : Term Symbol Γ setTy} {entry : Fin graph.size × Fin graph.size}
    (atNode : Proof Δ (describesSome (membersOf (coding.code entry.1)) a))
    (atChild : Proof Δ (describesSome (membersOf (coding.code entry.2)) b)) :
    ∀ (edges : List (Fin graph.size × Fin graph.size)), entry ∈ edges → Proof Δ (edgeFormula coding edges a b)
  | [], found => absurd found List.not_mem_nil
  | head :: rest, found =>
    if same : entry = head then disjunctionLeft (same ▸ conjunctionIntro atNode atChild)
    else disjunctionRight (edgeIntro atNode atChild rest ((List.mem_cons.mp found).resolve_left same))

/-- **Cases on the listed edge an edge is by.** -/
def edgeCases {a b : Term Symbol Γ setTy} {goal : Term Symbol Γ .prop} : ∀ {Δ : List (Term Symbol Γ .prop)}
    (edges : List (Fin graph.size × Fin graph.size)), Proof Δ (edgeFormula coding edges a b) →
      (∀ entry ∈ edges, Proof (conjunctionFormula (describesSome (membersOf (coding.code entry.1)) a)
        (describesSome (membersOf (coding.code entry.2)) b) :: Δ) goal) → Proof Δ goal
  | _, [], edge, _ => Proof.absurd edge
  | Δ, entry :: rest, edge, branch =>
    disjunctionElim edge (branch entry List.mem_cons_self)
      (edgeCases (Δ := edgeFormula coding rest a b :: Δ) rest (Proof.newest _) fun other found =>
        Proof.insertSecond _ (branch other (List.mem_cons_of_mem _ found)))

theorem instantiate_edgeBody (x y : Term Symbol Γ setTy) (edges : List (Fin graph.size × Fin graph.size)) :
    instantiate y (edgeFormula coding edges (weaken x) (.var .vz)) = edgeFormula coding edges x y := by
  unfold instantiate
  rw [subst_edgeFormula, ← instantiate, Mettapedia.Logic.HOL.instantiate_weaken]
  rfl

end Edges

/-! ## Instantiating the bodies -/

section Instances

variable {graph : MembershipGraph} (coding : GraphCode graph) {Γ : Ctx Unit}

theorem instantiate_graphPossiblyBody {n : ℕ} {inner : Formula n} (fragment : Formula.graphFragment inner = true)
    (t x : Term Symbol Γ setTy) (env : Fin n → Term Symbol Γ predTy) :
    instantiate t (conjunctionFormula (edgeFormula coding (graphEdges graph) (weaken x) (.var .vz))
      (graphFormula coding inner (.var .vz) (underElement env))) =
      conjunctionFormula (edgeFormula coding (graphEdges graph) x t) (graphFormula coding inner t env) := by
  unfold instantiate
  rw [subst_conjunctionFormula, subst_graphFormula coding _ inner fragment, instantiate_underElement,
    subst_edgeFormula, ← instantiate, Mettapedia.Logic.HOL.instantiate_weaken]
  rfl

theorem instantiate_graphNecessarilyBody {n : ℕ} {inner : Formula n} (fragment : Formula.graphFragment inner = true)
    (t x : Term Symbol Γ setTy) (env : Fin n → Term Symbol Γ predTy) :
    instantiate t (.imp (edgeFormula coding (graphEdges graph) (weaken x) (.var .vz))
      (graphFormula coding inner (.var .vz) (underElement env))) =
      .imp (edgeFormula coding (graphEdges graph) x t) (graphFormula coding inner t env) := by
  unfold instantiate
  show Term.imp _ _ = _
  rw [subst_graphFormula coding _ inner fragment, instantiate_underElement, subst_edgeFormula, ← instantiate,
    Mettapedia.Logic.HOL.instantiate_weaken]
  rfl

theorem instantiate_graphNuBody {n : ℕ} {inner : Formula (n + 1)} (fragment : Formula.graphFragment inner = true)
    (predicate : Term Symbol Γ predTy) (x : Term Symbol Γ setTy) (env : Fin n → Term Symbol Γ predTy) :
    instantiate predicate (conjunctionFormula (.all (σ := setTy) (.imp (.app (.var (.vs .vz)) (.var .vz))
        (graphFormula coding inner (.var .vz) (underFixedPoint env)))) (.app (.var .vz) (weaken x))) =
      conjunctionFormula (.all (σ := setTy) (.imp (.app (weaken predicate) (.var .vz))
        (graphFormula coding inner (.var .vz) (Fin.cons (weaken predicate) (underElement env))))) (.app predicate x) := by
  unfold instantiate
  rw [subst_conjunctionFormula]
  congr 1
  · change Term.all (.imp (.app (weaken predicate) (.var .vz))
      (subst (Subst.lift (Subst.single predicate)) (graphFormula coding inner (.var .vz) (underFixedPoint env)))) = _
    rw [subst_graphFormula coding _ inner fragment]
    congr 3
    funext index
    refine Fin.cases rfl (fun index => ?_) index
    change subst (Subst.lift (Subst.single predicate)) (weaken (weaken (env index))) = weaken (env index)
    rw [Mettapedia.Logic.HOL.subst_weaken, ← instantiate, Mettapedia.Logic.HOL.instantiate_weaken]
  · show Term.app predicate (instantiate predicate (weaken x)) = _
    rw [Mettapedia.Logic.HOL.instantiate_weaken]

/-- The closure hypothesis of a least fixed point of the graph. -/
def graphClosureHyp {n : ℕ} (inner : Formula (n + 1)) (env : Fin n → Term Symbol Γ predTy) :
    Term Symbol (predTy :: Γ) .prop :=
  .all (σ := setTy) (.imp (graphFormula coding inner (.var .vz) (underFixedPoint env)) (.app (.var (.vs .vz)) (.var .vz)))

theorem instantiate_graphMuBody {n : ℕ} {inner : Formula (n + 1)} (fragment : Formula.graphFragment inner = true)
    (predicate : Term Symbol Γ predTy) (x : Term Symbol Γ setTy) (env : Fin n → Term Symbol Γ predTy) :
    instantiate predicate (.imp (graphClosureHyp coding inner env) (.app (.var .vz) (weaken x))) =
      .imp (.all (σ := setTy) (.imp (graphFormula coding inner (.var .vz) (Fin.cons (weaken predicate) (underElement env)))
        (.app (weaken predicate) (.var .vz)))) (.app predicate x) := by
  change Term.imp (.all (.imp (subst (Subst.lift (Subst.single predicate))
    (graphFormula coding inner (.var .vz) (underFixedPoint env))) (.app (weaken predicate) (.var .vz))))
    (.app predicate (instantiate predicate (weaken x))) = _
  rw [subst_graphFormula coding _ inner fragment, Mettapedia.Logic.HOL.instantiate_weaken]
  congr 4
  funext index
  refine Fin.cases rfl (fun index => ?_) index
  change subst (Subst.lift (Subst.single predicate)) (weaken (weaken (env index))) = weaken (env index)
  rw [Mettapedia.Logic.HOL.subst_weaken, ← instantiate, Mettapedia.Logic.HOL.instantiate_weaken]

end Instances

/-! ## Described by the code of one of a list of nodes -/

section Codes

variable {graph : MembershipGraph} (coding : GraphCode graph) {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)}

/-- **The set term is described, forward and existentially, by the code of one of the nodes.** -/
def someCode : List (Fin graph.size) → {Γ : Ctx Unit} → Term Symbol Γ setTy → Term Symbol Γ .prop
  | [], _, _ => falsity
  | node :: nodes, _, y => disjunctionFormula (describesSome (membersOf (coding.code node)) y) (someCode nodes y)

theorem subst_someCode {Γ' : Ctx Unit} (θ : Subst Symbol Γ Γ') :
    ∀ (nodes : List (Fin graph.size)) (y : Term Symbol Γ setTy), subst θ (someCode coding nodes y) = someCode coding nodes (subst θ y)
  | [], _ => rfl
  | node :: nodes, y => by
    simp only [someCode, subst_disjunctionFormula, subst_describesSome, subst_someCode θ nodes y]

theorem instantiate_someCode (nodes : List (Fin graph.size)) (y : Term Symbol Γ setTy) :
    instantiate y (someCode coding nodes (.var .vz)) = someCode coding nodes y := by
  unfold instantiate
  rw [subst_someCode]
  rfl

theorem isCore_someCode : ∀ (nodes : List (Fin graph.size)) {y : Term Symbol Γ setTy}, y.isCore = true →
    (someCode coding nodes y).isCore = true
  | [], _, _ => rfl
  | _ :: nodes, _, coreY => isCore_disjunctionFormula (isCore_describesSome _ coreY) (isCore_someCode nodes coreY)

/-- A set described by the code of a listed node is described by the code of one of them. -/
def someCodeIntro {y : Term Symbol Γ setTy} {node : Fin graph.size}
    (described : Proof Δ (describesSome (membersOf (coding.code node)) y)) :
    ∀ (nodes : List (Fin graph.size)), node ∈ nodes → Proof Δ (someCode coding nodes y)
  | [], found => absurd found List.not_mem_nil
  | head :: rest, found =>
    if same : node = head then disjunctionLeft (same ▸ described)
    else disjunctionRight (someCodeIntro described rest ((List.mem_cons.mp found).resolve_left same))

/-- Cases on which listed node's code describes a set. -/
def someCodeCases {y : Term Symbol Γ setTy} {goal : Term Symbol Γ .prop} : ∀ {Δ : List (Term Symbol Γ .prop)}
    (nodes : List (Fin graph.size)), Proof Δ (someCode coding nodes y) →
      (∀ node ∈ nodes, Proof (describesSome (membersOf (coding.code node)) y :: Δ) goal) → Proof Δ goal
  | _, [], one, _ => Proof.absurd one
  | Δ, node :: nodes, one, branch =>
    disjunctionElim one (branch node List.mem_cons_self)
      (someCodeCases (Δ := someCode coding nodes y :: Δ) nodes (Proof.newest _) fun other found =>
        Proof.insertSecond _ (branch other (List.mem_cons_of_mem _ found)))

/-- The predicate "described by the code of one of the nodes". -/
def codePredicate (nodes : List (Fin graph.size)) {Γ : Ctx Unit} : Term Symbol Γ predTy := .lam (someCode coding nodes (.var .vz))

theorem weaken_codePredicate {σ : Ty Unit} (nodes : List (Fin graph.size)) :
    weaken (σ := σ) (codePredicate coding nodes (Γ := Γ)) = codePredicate coding nodes := by
  change Term.lam (rename (Rename.lift Rename.weaken) (someCode coding nodes (.var .vz))) = _
  rw [rename_eq_subst, subst_someCode]
  rfl

/-- The predicate "described by the code of none of the nodes". -/
def codeRefusal (nodes : List (Fin graph.size)) {Γ : Ctx Unit} : Term Symbol Γ predTy :=
  .lam (negCore (someCode coding nodes (.var .vz)))

theorem weaken_codeRefusal {σ : Ty Unit} (nodes : List (Fin graph.size)) :
    weaken (σ := σ) (codeRefusal coding nodes (Γ := Γ)) = codeRefusal coding nodes := by
  change Term.lam (.imp (rename (Rename.lift Rename.weaken) (someCode coding nodes (.var .vz))) falsity) = _
  rw [rename_eq_subst, subst_someCode]
  rfl

theorem isCore_codeRefusalBody (nodes : List (Fin graph.size)) :
    (negCore (someCode coding nodes (.var .vz : Term Symbol (setTy :: Γ) setTy))).isCore = true := by
  simp only [negCore, Mettapedia.Logic.HOL.Term.isCore,
    isCore_someCode coding nodes (y := (.var .vz : Term Symbol (setTy :: Γ) setTy)) rfl, isCore_falsity, Bool.and_true]

theorem instantiate_codeRefusalBody (nodes : List (Fin graph.size)) (y : Term Symbol Γ setTy) :
    instantiate y (negCore (someCode coding nodes (.var .vz))) = negCore (someCode coding nodes y) := by
  change Term.imp (instantiate y (someCode coding nodes (.var .vz))) falsity = _
  rw [instantiate_someCode]
  rfl

end Codes

/-! ## Knowledge about predicates at nodes -/

section Knowledge

variable {graph : MembershipGraph} (coding : GraphCode graph)

/-- **Positive knowledge at nodes**: at every node a decision accepts, the predicate term holds at what the node's code
describes. -/
def GraphKnows {n : ℕ} {Γ : Ctx Unit} (Δ : List (Term Symbol Γ .prop)) (env : Fin n → Term Symbol Γ predTy)
    (decision : Fin n → Fin graph.size → Bool) : Type :=
  ∀ (index : Fin n) (node : Fin graph.size), decision index node = true → Proof Δ (knowsAt (env index) (coding.code node))

/-- **Negative knowledge at nodes**: at every node a decision rejects, the predicate term fails at what the node's code
describes. -/
def GraphRefuses {n : ℕ} {Γ : Ctx Unit} (Δ : List (Term Symbol Γ .prop)) (env : Fin n → Term Symbol Γ predTy)
    (decision : Fin n → Fin graph.size → Bool) : Type :=
  ∀ (index : Fin n) (node : Fin graph.size), decision index node = false →
    Proof Δ (refusesAt (env index) (coding.code node))

variable {coding} {n : ℕ} {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)} {env : Fin n → Term Symbol Γ predTy}
  {decision : Fin n → Fin graph.size → Bool}

def GraphKnows.prepend (know : GraphKnows coding Δ env decision) (ψ : Term Symbol Γ .prop) :
    GraphKnows coding (ψ :: Δ) env decision :=
  fun index node accepted => (know index node accepted).prepend ψ

def GraphKnows.lift (know : GraphKnows coding Δ env decision) (σ : Ty Unit) :
    GraphKnows coding (weakenHyps (σ := σ) Δ) (fun index => weaken (env index)) decision :=
  fun index node accepted => Proof.cast (weaken_knowsAt _ _) (know index node accepted).lift

def GraphRefuses.prepend (refuse : GraphRefuses coding Δ env decision) (ψ : Term Symbol Γ .prop) :
    GraphRefuses coding (ψ :: Δ) env decision :=
  fun index node rejected => (refuse index node rejected).prepend ψ

def GraphRefuses.lift (refuse : GraphRefuses coding Δ env decision) (σ : Ty Unit) :
    GraphRefuses coding (weakenHyps (σ := σ) Δ) (fun index => weaken (env index)) decision :=
  fun index node rejected => Proof.cast (weaken_refusesAt _ _) (refuse index node rejected).lift

end Knowledge

/-! ## Proving and refuting at nodes -/

section Compiler

variable {graph : MembershipGraph} (coding : GraphCode graph)

theorem graphEval_mono {n : ℕ} (inner : Formula (n + 1)) (decision : Fin n → Fin graph.size → Bool) :
    ∀ smaller larger, Listed.Le smaller larger →
      Listed.Le (fun other => graph.finite.eval (Fin.cons smaller decision) inner other)
        (fun other => graph.finite.eval (Fin.cons larger decision) inner other) := by
  intro smaller larger le other holds
  rw [graph.finite.eval_iff, FiniteStructure.sets_cons] at holds ⊢
  exact graph.finite.native.sat_mono inner ((FiniteStructure.sets decision).extend_sub fun member inside => le member inside) other
    holds

/-- The nodes of a graph. -/
abbrev graphNodes (graph : MembershipGraph) : List (Fin graph.size) := List.finRange graph.size

theorem graphStep_iff {node next : Fin graph.size} {label : StepLabel} :
    graph.finite.step node label next = true ↔ memberLabel label ∧ next ∈ graph.children node := by
  change (decide (memberLabel label) && (graph.children node).contains next) = true ↔ _
  rw [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem]

/-- **A proof that a native type of the graph holds** at the set a node's code describes, whenever the graph's
evaluation accepts it at the node. -/
def proveGraph : ∀ {n : ℕ} (formula : Formula n), Formula.graphFragment formula = true →
    ∀ {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)}, HasLaws Δ → ∀ (env : Fin n → Term Symbol Γ predTy)
      (decision : Fin n → Fin graph.size → Bool), GraphKnows coding Δ env decision → ∀ node : Fin graph.size,
        graph.finite.eval decision formula node = true → ∀ x : Term Symbol Γ setTy, x.isCore = true →
          Proof Δ (describesSome (membersOf (coding.code node)) x) → Proof Δ (graphFormula coding formula x env)
  | _, .top, _, _, _, _, _, _, _, _, _, _, _, _ => truthIntro
  | _, .bot, _, _, _, _, _, _, _, _, holds, _, _, _ => Bool.noConfusion holds
  | _, .and left right, fragment, _, _, laws, env, decision, know, node, holds, x, coreX, described => by
    simp only [Formula.graphFragment, Bool.and_eq_true] at fragment
    change (graph.finite.eval decision left node && graph.finite.eval decision right node) = true at holds
    rw [Bool.and_eq_true] at holds
    exact conjunctionIntro (proveGraph left fragment.1 laws env decision know node holds.1 x coreX described)
      (proveGraph right fragment.2 laws env decision know node holds.2 x coreX described)
  | _, .or left right, fragment, _, _, laws, env, decision, know, node, holds, x, coreX, described => by
    simp only [Formula.graphFragment, Bool.and_eq_true] at fragment
    change (graph.finite.eval decision left node || graph.finite.eval decision right node) = true at holds
    refine if first : graph.finite.eval decision left node = true then ?_ else ?_
    · exact disjunctionLeft (proveGraph left fragment.1 laws env decision know node first x coreX described)
    · exact disjunctionRight (proveGraph right fragment.2 laws env decision know node
        ((Bool.or_eq_true _ _ ▸ holds).resolve_left first) x coreX described)
  | _, .var index, _, _, _, _, _, _, know, node, holds, _, _, described =>
    useKnows (know index node holds) described
  | _, .mu inner, fragment, Γ, Δ, laws, env, decision, know, node, holds, x, coreX, described => by
    have fragmentInner : Formula.graphFragment inner = true := fragment
    change Proof Δ (.all (σ := predTy) (.imp (graphClosureHyp coding inner env) (.app (.var .vz) (weaken x))))
    refine .allI (.impI (useKnows (?_ : Proof _ (knowsAt (.var .vz) (coding.code node))) (describesSomeUnder described predTy _)))
    have stages : ∀ (k : ℕ) (other : Fin graph.size),
        Listed.up (fun set => graph.finite.eval (Fin.cons set decision) inner) k other = true →
          Proof (graphClosureHyp coding inner env :: weakenHyps (σ := predTy) Δ) (knowsAt (.var .vz) (coding.code other)) := by
      intro k
      induction k with
      | zero => intro other member; exact Bool.noConfusion member
      | succ k ih =>
        intro other member
        refine .allI (.impI ?_)
        have closure : Proof (describesSome (membersOf (coding.code other)) (.var .vz) :: weakenHyps (σ := setTy)
            (graphClosureHyp coding inner env :: weakenHyps (σ := predTy) Δ))
            (.imp (graphFormula coding inner (.var .vz) (underFixedPoint env)) (.app (.var (.vs .vz)) (.var .vz))) :=
          Proof.atNewest (((Proof.newest (graphClosureHyp coding inner env)).lift (σ := setTy)).prepend _)
        refine .impE closure (proveGraph inner fragmentInner ((((laws.lift predTy).prepend _).lift setTy).prepend _)
          (underFixedPoint env) (Fin.cons (Listed.up (fun set => graph.finite.eval (Fin.cons set decision) inner) k)
            decision) (fun index => ?_) other member (.var .vz) rfl (Proof.newest _))
        refine Fin.cases (motive := fun index => ∀ node' : Fin graph.size,
          (Fin.cons (Listed.up (fun set => graph.finite.eval (Fin.cons set decision) inner) k) decision :
            Fin _ → Fin graph.size → Bool) index node' = true →
          Proof (describesSome (membersOf (coding.code other)) (.var .vz) :: weakenHyps (σ := setTy)
            (graphClosureHyp coding inner env :: weakenHyps (σ := predTy) Δ))
            (knowsAt (underFixedPoint env index) (coding.code node'))) ?_ (fun index => ?_) index
        · intro node' accepted
          exact (Proof.cast (weaken_knowsAt _ _) (ih node' accepted).lift).prepend _
        · exact (((know.lift predTy).prepend _).lift setTy).prepend _ index
    exact stages _ node holds
  | _, .nu inner, fragment, Γ, Δ, laws, env, decision, know, node, holds, x, coreX, described => by
    have fragmentInner : Formula.graphFragment inner = true := fragment
    let operator := fun set => graph.finite.eval (Fin.cons set decision) inner
    let stable := Listed.down operator (graphNodes graph).length
    let chosen := (graphNodes graph).filter stable
    have stableFixed : operator stable = stable :=
      Listed.down_stable (graphEval_mono inner decision) List.mem_finRange
    have chosenIff : ∀ other, other ∈ chosen ↔ stable other = true := fun other => by
      simp [chosen, List.mem_filter, List.mem_finRange]
    have knows : ∀ {Γ' : Ctx Unit} {Δ' : List (Term Symbol Γ' .prop)} (other : Fin graph.size), stable other = true →
        Proof Δ' (knowsAt (codePredicate coding chosen) (coding.code other)) := by
      intro Γ' Δ' other member
      refine .allI (.impI ?_)
      rw [weaken_codePredicate]
      exact Proof.betaExpand (isCore_someCode coding chosen rfl) rfl (Proof.cast (instantiate_someCode coding chosen _).symm
        (someCodeIntro coding (Proof.newest _) chosen ((chosenIff other).mpr member)))
    change Proof _ (existentialInline (σ := predTy) (conjunctionFormula (.all (σ := setTy)
      (.imp (.app (.var (.vs .vz)) (.var .vz)) (graphFormula coding inner (.var .vz) (underFixedPoint env))))
        (.app (.var .vz) (weaken x))))
    refine existentialIntro (codePredicate coding chosen) (Proof.cast
      (instantiate_graphNuBody coding fragmentInner _ x env).symm (conjunctionIntro (.allI (.impI ?_)) ?_))
    · have unfolded : Proof (.app (weaken (codePredicate coding chosen)) (.var .vz) :: weakenHyps (σ := setTy) Δ)
          (someCode coding chosen (.var .vz)) := by
        refine Proof.cast (instantiate_newest_lifted (someCode coding chosen (.var .vz))) ?_
        exact Proof.betaReduce (by rw [Mettapedia.Logic.HOL.Term.isCore_rename]; exact isCore_someCode coding chosen rfl)
          rfl (Proof.newest _)
      refine someCodeCases coding chosen unfolded fun other member => ?_
      have otherStable := (chosenIff other).mp member
      have otherHolds : graph.finite.eval (Fin.cons stable decision) inner other = true := by
        have := congrFun stableFixed other
        exact this.trans otherStable
      refine proveGraph inner fragmentInner ((laws.lift setTy).prepend _ |>.prepend _)
        (Fin.cons (weaken (codePredicate coding chosen)) (underElement env)) (Fin.cons stable decision)
        (fun index => ?_) other otherHolds (.var .vz) rfl (Proof.newest _)
      refine Fin.cases (motive := fun index => ∀ node' : Fin graph.size,
        (Fin.cons stable decision : Fin _ → Fin graph.size → Bool) index node' = true →
          Proof _ (knowsAt ((Fin.cons (weaken (codePredicate coding chosen)) (underElement env) :
            Fin _ → Term Symbol (setTy :: Γ) predTy) index) (coding.code node'))) ?_ (fun index => ?_) index
      · intro node' accepted
        rw [Fin.cons_zero, weaken_codePredicate]
        exact knows node' accepted
      · exact ((know.lift setTy).prepend _ |>.prepend _) index
    · refine Proof.betaExpand (isCore_someCode coding chosen rfl) coreX
        (Proof.cast (instantiate_someCode coding chosen x).symm ?_)
      exact someCodeIntro coding described chosen ((chosenIff node).mpr holds)
  | _, .possibly label inner, fragment, Γ, Δ, laws, env, decision, know, node, holds, x, coreX, described => by
    have fragmentInner : Formula.graphFragment inner = true := by
      simp only [Formula.graphFragment, Bool.and_eq_true] at fragment
      exact fragment.2
    have found : ∃ next ∈ graphNodes graph,
        (graph.finite.step node label next && graph.finite.eval decision inner next) = true := by
      have any : (graph.finite.elements.any fun next => graph.finite.step node label next &&
          graph.finite.eval decision inner next) = true := holds
      exact List.any_eq_true.mp any
    let next := (graphNodes graph).get (chooseIndex (graphNodes graph) _ found).1
    have chosen := Bool.and_eq_true_iff.mp (chooseIndex (graphNodes graph) _ found).2
    have stepped := graphStep_iff.mp chosen.1
    have codeHolds := coding.hereditary next
    rw [show graphFormula coding (.possibly label inner) x env = existentialInline (σ := setTy) (conjunctionFormula
      (edgeFormula coding (graphEdges graph) (weaken x) (.var .vz)) (graphFormula coding inner (.var .vz) (underElement env)))
      by simp only [graphFormula, if_pos stepped.1]]
    refine existentialIntro (witness (coding.code next)) (Proof.cast
      (instantiate_graphPossiblyBody coding fragmentInner _ x env).symm (conjunctionIntro ?_ ?_))
    · exact edgeIntro coding (entry := (node, next)) described
        (describesSomeOfTerm laws codeHolds (describedWitness laws _ codeHolds)) (graphEdges graph)
        (mem_graphEdges.mpr stepped.2)
    · exact proveGraph inner fragmentInner laws env decision know next chosen.2 _ (isCore_witness _)
        (describesSomeOfTerm laws codeHolds (describedWitness laws _ codeHolds))
  | _, .necessarily label inner, fragment, Γ, Δ, laws, env, decision, know, node, holds, x, coreX, described => by
    have fragmentInner : Formula.graphFragment inner = true := by
      simp only [Formula.graphFragment, Bool.and_eq_true] at fragment
      exact fragment.2
    refine if labelled : memberLabel label then ?_ else ?_
    · rw [show graphFormula coding (.necessarily label inner) x env = .all (σ := setTy)
        (.imp (edgeFormula coding (graphEdges graph) (weaken x) (.var .vz)) (graphFormula coding inner (.var .vz)
          (underElement env))) by simp only [graphFormula, if_pos labelled]]
      have every : (graph.finite.elements.all fun next => !graph.finite.step node label next ||
          graph.finite.eval decision inner next) = true := holds
      refine .allI (.impI (edgeCases coding (graphEdges graph) (Proof.newest _) fun entry found => ?_))
      refine if same : entry.1 = node then ?_ else ?_
      · have child : entry.2 ∈ graph.children node := by
          have := mem_graphEdges.mp (show (entry.1, entry.2) ∈ graphEdges graph from found)
          rw [same] at this
          exact this
        have childHolds : graph.finite.eval decision inner entry.2 = true := by
          have atChild := List.all_eq_true.mp every entry.2 (List.mem_finRange _)
          rw [Bool.or_eq_true, Bool.not_eq_true'] at atChild
          refine atChild.resolve_left fun notStep => ?_
          rw [graphStep_iff.mpr ⟨labelled, child⟩] at notStep
          exact Bool.noConfusion notStep
        exact proveGraph inner fragmentInner (((laws.lift setTy).prepend _).prepend _) (underElement env) decision
          (((know.lift setTy).prepend _).prepend _) entry.2 childHolds (.var .vz) rfl (conjunctionRight (Proof.newest _))
      · exact Proof.absurd (describesSomeDistinct (((laws.lift setTy).prepend _).prepend _) (coding.hereditary node)
          (coding.hereditary entry.1) (coding.apart node entry.1 (Ne.symm same))
          (Proof.prepend _ (describesSomeUnder described setTy _)) (conjunctionLeft (Proof.newest _)))
    · rw [show graphFormula coding (.necessarily label inner) x env = truth by simp only [graphFormula, if_neg labelled]]
      exact truthIntro
  | _, .sometimeBefore _ _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .alwaysBefore _ _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .atLeast _ _ _ _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .allButFewer _ _ _ _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .built _ _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .everyBuilt _ _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .split _ _ _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .everySplit _ _ _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .empty _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .nonEmpty _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .single _ _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .everySingle _ _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .body _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .everyBody _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .multiBody _ _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .everyMultiBody _ _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .bound _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .notBound _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .typed _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .untyped _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .is _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .isNot _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .mapsAll _ _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .mapsSome _ _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .someOf _ _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .everyOf _ _, fragment, _, _, _, _, _, _, _, _, _, _, _ => absurd fragment Bool.false_ne_true

end Compiler

section Refuter

variable {graph : MembershipGraph} (coding : GraphCode graph)

/-- The invariance hypothesis of a greatest fixed point of the graph. -/
def graphInvariantHyp {n : ℕ} (inner : Formula (n + 1)) {Γ : Ctx Unit} (env : Fin n → Term Symbol Γ predTy) :
    Term Symbol (predTy :: Γ) .prop :=
  .all (σ := setTy) (.imp (.app (.var (.vs .vz)) (.var .vz)) (graphFormula coding inner (.var .vz) (underFixedPoint env)))

/-- **A proof that a native type of the graph fails** at the set a node's code describes, whenever the graph's
evaluation rejects it at the node. -/
def refuteGraph : ∀ {n : ℕ} (formula : Formula n), Formula.graphFragment formula = true →
    ∀ {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)}, HasLaws Δ → ∀ (env : Fin n → Term Symbol Γ predTy)
      (decision : Fin n → Fin graph.size → Bool), GraphRefuses coding Δ env decision → ∀ node : Fin graph.size,
        graph.finite.eval decision formula node = false → ∀ x : Term Symbol Γ setTy, x.isCore = true →
          Proof Δ (describesSome (membersOf (coding.code node)) x) →
            Proof Δ (negCore (graphFormula coding formula x env))
  | _, .top, _, _, _, _, _, _, _, _, fails, _, _, _ => Bool.noConfusion fails
  | _, .bot, _, _, _, _, _, _, _, _, _, _, _, _ => .impI (Proof.newest _)
  | _, .and left right, fragment, _, _, laws, env, decision, refuse, node, fails, x, coreX, described => by
    simp only [Formula.graphFragment, Bool.and_eq_true] at fragment
    change (graph.finite.eval decision left node && graph.finite.eval decision right node) = false at fails
    refine if first : graph.finite.eval decision left node = true then ?_ else ?_
    · have second : graph.finite.eval decision right node = false := by
        rw [first, Bool.true_and] at fails
        exact fails
      exact .impI (.impE ((refuteGraph right fragment.2 laws env decision refuse node second x coreX described).prepend _)
        (conjunctionRight (Proof.newest _)))
    · exact .impI (.impE ((refuteGraph left fragment.1 laws env decision refuse node (Bool.eq_false_iff.mpr first) x coreX
        described).prepend _) (conjunctionLeft (Proof.newest _)))
  | _, .or left right, fragment, _, _, laws, env, decision, refuse, node, fails, x, coreX, described => by
    simp only [Formula.graphFragment, Bool.and_eq_true] at fragment
    change (graph.finite.eval decision left node || graph.finite.eval decision right node) = false at fails
    rw [Bool.or_eq_false_iff] at fails
    exact .impI (disjunctionElim (Proof.newest _)
      (.impE (((refuteGraph left fragment.1 laws env decision refuse node fails.1 x coreX described).prepend _).prepend _)
        (Proof.newest _))
      (.impE (((refuteGraph right fragment.2 laws env decision refuse node fails.2 x coreX described).prepend _).prepend _)
        (Proof.newest _)))
  | _, .var index, _, _, _, _, _, _, refuse, node, fails, _, _, described =>
    useRefuses (refuse index node fails) described
  | _, .mu inner, fragment, Γ, Δ, laws, env, decision, refuse, node, fails, x, coreX, described => by
    have fragmentInner : Formula.graphFragment inner = true := fragment
    let operator := fun set => graph.finite.eval (Fin.cons set decision) inner
    let stable := Listed.up operator (graphNodes graph).length
    let outside := (graphNodes graph).filter fun other => !stable other
    have stableFixed : operator stable = stable := Listed.up_stable (graphEval_mono inner decision) List.mem_finRange
    have outsideIff : ∀ other, other ∈ outside ↔ stable other = false := fun other => by
      simp [outside, List.mem_filter, List.mem_finRange]
    have refusalKnows : ∀ {Γ' : Ctx Unit} {Δ' : List (Term Symbol Γ' .prop)} (other : Fin graph.size),
        stable other = false → Proof Δ' (refusesAt (codeRefusal coding outside) (coding.code other)) := by
      intro Γ' Δ' other missing
      refine .allI (.impI (.impI ?_))
      have applied := Proof.cast (congrArg (Term.app · (.var .vz)) (weaken_codeRefusal (Γ := Γ') coding outside))
        (Proof.newest (Δ := describesSome (membersOf (coding.code other)) (.var .vz) :: weakenHyps (σ := setTy) Δ')
          (.app (weaken (codeRefusal coding outside)) (.var .vz)))
      have unfolded := Proof.cast (instantiate_codeRefusalBody coding outside (.var .vz))
        (Proof.betaReduce (isCore_codeRefusalBody coding outside) rfl applied)
      exact .impE unfolded (someCodeIntro coding ((Proof.newest _).prepend _) outside ((outsideIff other).mpr missing))
    let hypothesis : Term Symbol Γ .prop := .all (σ := predTy) (.imp (graphClosureHyp coding inner env)
      (.app (.var .vz) (weaken x)))
    change Proof Δ (negCore hypothesis)
    refine .impI ?_
    have instance' : Proof (hypothesis :: Δ) (.imp (.all (σ := setTy) (.imp (graphFormula coding inner (.var .vz)
        (Fin.cons (weaken (codeRefusal coding outside)) (underElement env)))
        (.app (weaken (codeRefusal coding outside)) (.var .vz)))) (.app (codeRefusal coding outside) x)) :=
      Proof.cast (instantiate_graphMuBody coding fragmentInner (codeRefusal coding outside) x env)
        (.allE (codeRefusal coding outside) (Proof.newest hypothesis))
    have closedness : Proof (hypothesis :: Δ)
        (.all (σ := setTy) (.imp (graphFormula coding inner (.var .vz)
          (Fin.cons (weaken (codeRefusal coding outside)) (underElement env)))
          (.app (weaken (codeRefusal coding outside)) (.var .vz)))) := by
      refine .allI (.impI ?_)
      refine Proof.cast (congrArg (Term.app · (.var .vz)) (weaken_codeRefusal coding outside).symm) ?_
      refine Proof.betaExpand (isCore_codeRefusalBody coding outside) rfl
        (Proof.cast (instantiate_codeRefusalBody coding outside (.var .vz)).symm (.impI ?_))
      refine someCodeCases coding outside (Proof.newest _) fun other member => ?_
      have missing := (outsideIff other).mp member
      have bodyFails : graph.finite.eval (Fin.cons stable decision) inner other = false := by
        have := congrFun stableFixed other
        exact this.trans missing
      refine .impE (refuteGraph inner fragmentInner ((((laws.prepend _).lift setTy).prepend _ |>.prepend _).prepend _)
        (Fin.cons (weaken (codeRefusal coding outside)) (underElement env)) (Fin.cons stable decision)
        (fun index => ?_) other bodyFails (.var .vz) rfl (Proof.newest _))
        (((Proof.newest _).prepend _).prepend _)
      refine Fin.cases (motive := fun index => ∀ node' : Fin graph.size,
        (Fin.cons stable decision : Fin _ → Fin graph.size → Bool) index node' = false →
          Proof _ (refusesAt ((Fin.cons (weaken (codeRefusal coding outside)) (underElement env) :
            Fin _ → Term Symbol (setTy :: Γ) predTy) index) (coding.code node'))) ?_ (fun index => ?_) index
      · intro node' rejected
        exact Proof.cast (congrArg (refusesAt · (coding.code node')) (weaken_codeRefusal coding outside).symm)
          (refusalKnows node' rejected)
      · exact (((((refuse.prepend _).lift setTy).prepend _).prepend _).prepend _) index
    have atTerm := Proof.cast (instantiate_codeRefusalBody coding outside x)
      (Proof.betaReduce (isCore_codeRefusalBody coding outside) coreX (.impE instance' closedness))
    exact .impE atTerm (someCodeIntro coding (described.prepend _) outside ((outsideIff node).mpr fails))
  | _, .nu inner, fragment, Γ, Δ, laws, env, decision, refuse, node, fails, x, coreX, described => by
    have fragmentInner : Formula.graphFragment inner = true := fragment
    let operator := fun set => graph.finite.eval (Fin.cons set decision) inner
    change Proof Δ (negCore (existentialInline (σ := predTy) (conjunctionFormula (graphInvariantHyp coding inner env)
      (.app (.var .vz) (weaken x)))))
    refine .impI (existentialElim (Proof.newest _) ?_)
    let hypotheses := conjunctionFormula (graphInvariantHyp coding inner env) (.app (.var .vz) (weaken x)) ::
      weakenHyps (σ := predTy) (existentialInline (σ := predTy) (conjunctionFormula (graphInvariantHyp coding inner env)
        (.app (.var .vz) (weaken x))) :: Δ)
    have laws' : HasLaws hypotheses := ((laws.prepend _).lift predTy).prepend _
    have refuse' : GraphRefuses coding hypotheses (fun index => weaken (env index)) decision :=
      ((refuse.prepend _).lift predTy).prepend _
    have invariant : Proof hypotheses (graphInvariantHyp coding inner env) := conjunctionLeft (Proof.newest _)
    have stages : ∀ (k : ℕ) (other : Fin graph.size), Listed.down operator k other = false →
        Proof hypotheses (refusesAt (.var .vz) (coding.code other)) := by
      intro k
      induction k with
      | zero => intro other missing; exact Bool.noConfusion missing
      | succ k ih =>
        intro other missing
        refine .allI (.impI (.impI ?_))
        have preserved : Proof (.app (.var (.vs .vz)) (.var .vz) :: describesSome (membersOf (coding.code other)) (.var .vz) ::
            weakenHyps (σ := setTy) hypotheses)
            (.imp (.app (.var (.vs .vz)) (.var .vz)) (graphFormula coding inner (.var .vz) (underFixedPoint env))) :=
          Proof.atNewest ((invariant.lift (σ := setTy)).prepend _ |>.prepend _)
        refine .impE (refuteGraph inner fragmentInner (((laws'.lift setTy).prepend _).prepend _) (underFixedPoint env)
          (Fin.cons (Listed.down operator k) decision) (fun index => ?_) other missing (.var .vz) rfl
          ((Proof.newest _).prepend _)) (.impE preserved (Proof.newest _))
        refine Fin.cases (motive := fun index => ∀ node' : Fin graph.size,
          (Fin.cons (Listed.down operator k) decision : Fin _ → Fin graph.size → Bool) index node' = false →
            Proof (.app (.var (.vs .vz)) (.var .vz) :: describesSome (membersOf (coding.code other)) (.var .vz) ::
              weakenHyps (σ := setTy) hypotheses) (refusesAt (underFixedPoint env index) (coding.code node')))
          ?_ (fun index => ?_) index
        · intro node' rejected
          exact ((Proof.cast (weaken_refusesAt _ _) (ih node' rejected).lift).prepend _).prepend _
        · exact ((refuse'.lift setTy).prepend _ |>.prepend _) index
    exact .impE (useRefuses (stages _ node fails) (describesSomeUnder (described.prepend _) predTy _))
      (conjunctionRight (Proof.newest _))
  | _, .possibly label inner, fragment, Γ, Δ, laws, env, decision, refuse, node, fails, x, coreX, described => by
    have fragmentInner : Formula.graphFragment inner = true := by
      simp only [Formula.graphFragment, Bool.and_eq_true] at fragment
      exact fragment.2
    refine if labelled : memberLabel label then ?_ else ?_
    · rw [show graphFormula coding (.possibly label inner) x env = existentialInline (σ := setTy) (conjunctionFormula
        (edgeFormula coding (graphEdges graph) (weaken x) (.var .vz)) (graphFormula coding inner (.var .vz)
          (underElement env))) by simp only [graphFormula, if_pos labelled]]
      have none : (graph.finite.elements.any fun next => graph.finite.step node label next &&
          graph.finite.eval decision inner next) = false := fails
      refine .impI (existentialElim (Proof.newest _) ?_)
      refine edgeCases coding (graphEdges graph) (conjunctionLeft (Proof.newest _)) fun entry found => ?_
      refine if same : entry.1 = node then ?_ else ?_
      · have child : entry.2 ∈ graph.children node := by
          have := mem_graphEdges.mp (show (entry.1, entry.2) ∈ graphEdges graph from found)
          rw [same] at this
          exact this
        have childFails : graph.finite.eval decision inner entry.2 = false := by
          have atChild := List.any_eq_false.mp none entry.2 (List.mem_finRange _)
          rw [graphStep_iff.mpr ⟨labelled, child⟩, Bool.true_and] at atChild
          exact Bool.eq_false_iff.mpr atChild
        exact .impE (refuteGraph inner fragmentInner ((((laws.prepend _).lift setTy).prepend _).prepend _)
          (underElement env) decision ((((refuse.prepend _).lift setTy).prepend _).prepend _) entry.2 childFails
          (.var .vz) rfl (conjunctionRight (Proof.newest _))) (Proof.prepend _ (conjunctionRight (Proof.newest _)))
      · exact describesSomeDistinct ((((laws.prepend _).lift setTy).prepend _).prepend _) (coding.hereditary node)
          (coding.hereditary entry.1) (coding.apart node entry.1 (Ne.symm same))
          (Proof.prepend _ (describesSomeUnder (described.prepend _) setTy _)) (conjunctionLeft (Proof.newest _))
    · rw [show graphFormula coding (.possibly label inner) x env = falsity by simp only [graphFormula, if_neg labelled]]
      exact .impI (Proof.newest _)
  | _, .necessarily label inner, fragment, Γ, Δ, laws, env, decision, refuse, node, fails, x, coreX, described => by
    have fragmentInner : Formula.graphFragment inner = true := by
      simp only [Formula.graphFragment, Bool.and_eq_true] at fragment
      exact fragment.2
    have some' : ∃ next ∈ graphNodes graph,
        (graph.finite.step node label next && !graph.finite.eval decision inner next) = true := by
      have notAll : (graph.finite.elements.all fun next => !graph.finite.step node label next ||
          graph.finite.eval decision inner next) = false := fails
      obtain ⟨next, member, bad⟩ := List.all_eq_false.mp notAll
      refine ⟨next, member, ?_⟩
      simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false] at bad
      simp [bad.1, bad.2]
    let next := (graphNodes graph).get (chooseIndex (graphNodes graph) _ some').1
    have chosen := Bool.and_eq_true_iff.mp (chooseIndex (graphNodes graph) _ some').2
    have stepped := graphStep_iff.mp chosen.1
    have bad : (!graph.finite.eval decision inner next) = true := chosen.2
    have nextFails : graph.finite.eval decision inner next = false :=
      Bool.eq_false_iff.mpr fun accepted => by
        rw [accepted] at bad
        exact Bool.noConfusion bad
    have codeHolds := coding.hereditary next
    rw [show graphFormula coding (.necessarily label inner) x env = .all (σ := setTy)
      (.imp (edgeFormula coding (graphEdges graph) (weaken x) (.var .vz)) (graphFormula coding inner (.var .vz)
        (underElement env))) by simp only [graphFormula, if_pos stepped.1]]
    refine .impI (.impE (refuteGraph inner fragmentInner (laws.prepend _) env decision (refuse.prepend _) next nextFails
      (witness (coding.code next)) (isCore_witness _)
      (describesSomeOfTerm (laws.prepend _) codeHolds (describedWitness (laws.prepend _) _ codeHolds))) ?_)
    refine .impE (Proof.cast (instantiate_graphNecessarilyBody coding fragmentInner _ x env)
      (.allE (witness (coding.code next)) (Proof.newest _))) ?_
    exact edgeIntro coding (entry := (node, next)) (described.prepend _)
      (describesSomeOfTerm (laws.prepend _) codeHolds (describedWitness (laws.prepend _) _ codeHolds)) (graphEdges graph)
      (mem_graphEdges.mpr stepped.2)
  | _, .sometimeBefore _ _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .alwaysBefore _ _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .atLeast _ _ _ _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .allButFewer _ _ _ _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .built _ _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .everyBuilt _ _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .split _ _ _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .everySplit _ _ _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .empty _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .nonEmpty _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .single _ _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .everySingle _ _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .body _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .everyBody _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .multiBody _ _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .everyMultiBody _ _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .bound _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .notBound _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .typed _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .untyped _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .is _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .isNot _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .mapsAll _ _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .mapsSome _ _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .someOf _ _, fragment, _, _, _, _, _, _, _, _, _, _, _
  | _, .everyOf _ _, fragment, _, _, _, _, _, _, _, _, _, _, _ => absurd fragment Bool.false_ne_true

end Refuter

/-! ## Sentences about coded graphs -/

section Sentences

variable {graph : MembershipGraph} (coding : GraphCode graph)

/-- **The sentence of a native type at a node**: some set is described by the node's code and has the type. -/
def graphSentence (formula : Formula 0) (node : Fin graph.size) : ClosedFormula Symbol :=
  existentialInline (σ := setTy) (conjunctionFormula (describes (coding.code node) (.var .vz))
    (graphFormula coding formula (.var .vz) Fin.elim0))

theorem instantiate_graphSentenceBody {formula : Formula 0} (fragment : Formula.graphFragment formula = true)
    (node : Fin graph.size) (t : Term Symbol [] setTy) :
    instantiate t (conjunctionFormula (describes (coding.code node) (.var .vz))
      (graphFormula coding formula (.var .vz) Fin.elim0)) =
      conjunctionFormula (describes (coding.code node) t) (graphFormula coding formula t Fin.elim0) := by
  unfold instantiate
  rw [subst_conjunctionFormula, subst_describes, subst_graphFormula coding _ formula fragment]
  congr 2
  funext index
  exact index.elim0

/-- **The sentence of a native type the graph's evaluation accepts at a node, proved from the three laws.** -/
def graphSentenceProof {formula : Formula 0} (fragment : Formula.graphFragment formula = true) (node : Fin graph.size)
    (accepted : graph.finite.eval Fin.elim0 formula node = true) : Proof lawList (graphSentence coding formula node) :=
  existentialIntro (witness (coding.code node)) (Proof.cast (instantiate_graphSentenceBody coding fragment node _).symm
    (conjunctionIntro (describedWitness lawsOfList _ (coding.hereditary node))
      (proveGraph coding formula fragment lawsOfList Fin.elim0 Fin.elim0 (fun index => index.elim0) node accepted
        (witness (coding.code node)) (isCore_witness _)
        (describesSomeOfTerm lawsOfList (coding.hereditary node)
          (describedWitness lawsOfList _ (coding.hereditary node))))))

/-- **The negation of the sentence of a native type the graph's evaluation rejects, proved from the three laws.** -/
def graphSentenceRefutation {formula : Formula 0} (fragment : Formula.graphFragment formula = true)
    (node : Fin graph.size) (rejected : graph.finite.eval Fin.elim0 formula node = false) :
    Proof lawList (negCore (graphSentence coding formula node)) :=
  .impI (existentialElim (Proof.newest _)
    (.impE (refuteGraph coding formula fragment (((lawsOfList.prepend _).lift setTy).prepend _) Fin.elim0 Fin.elim0
      (fun index => index.elim0) node rejected (.var .vz) rfl
      (describesSomeOfTerm (((lawsOfList.prepend _).lift setTy).prepend _) (coding.hereditary node)
        (conjunctionLeft (Proof.newest _)))) (conjunctionRight (Proof.newest _))))

/-- **The graph's certificate compiler**: the sentence of a native type at a node, or its negation, from the three
laws, decided by the graph's evaluation. -/
def compileGraph {formula : Formula 0} (fragment : Formula.graphFragment formula = true) (node : Fin graph.size) :
    Proof lawList (graphSentence coding formula node) ⊕ Proof lawList (negCore (graphSentence coding formula node)) :=
  if accepted : graph.finite.eval Fin.elim0 formula node = true then .inl (graphSentenceProof coding fragment node accepted)
  else .inr (graphSentenceRefutation coding fragment node (Bool.eq_false_iff.mpr accepted))

theorem compileGraph_isLeft_iff {formula : Formula 0} (fragment : Formula.graphFragment formula = true)
    (node : Fin graph.size) :
    (compileGraph coding fragment node).isLeft = true ↔ graph.finite.eval Fin.elim0 formula node = true := by
  unfold compileGraph
  split <;> simp_all

end Sentences

/-! ## Codings -/

/-- Whether the codes of different nodes present different sets. -/
def codesApart {graph : MembershipGraph} (code : Fin graph.size → Pattern) : Bool :=
  (List.finRange graph.size).all fun first => (List.finRange graph.size).all fun second =>
    decide (first = second) || !sameSet (code first) (code second)

/-- **A coding from codes checked apart.** -/
def GraphCode.ofApart {graph : MembershipGraph} (code : Fin graph.size → Pattern) (hereditary : ∀ node, IsHF (code node))
    (checked : codesApart code = true) : GraphCode graph where
  code := code
  hereditary := hereditary
  apart := fun first second differ same => by
    have atPair := List.all_eq_true.mp (List.all_eq_true.mp checked first (List.mem_finRange _)) second
      (List.mem_finRange _)
    rw [Bool.or_eq_true, decide_eq_true_eq] at atPair
    rcases atPair with equal | apartCodes
    · exact differ equal
    · rw [(sameSet_iff _ (hereditary first) _ (hereditary second)).mpr same] at apartCodes
      exact Bool.noConfusion apartCodes

/-- **A one-node graph's coding**: its node coded by the empty set. -/
def GraphCode.single {graph : MembershipGraph} (sized : graph.size = 1) : GraphCode graph where
  code _ := zero
  hereditary _ := (hereditary_iff _).mp (by decide)
  apart := fun first second differ => absurd (Fin.ext (by have := first.2; have := second.2; omega)) differ

/-! ## In the package of set theory -/

section Package

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.MegalodonHOTG
open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseInterpretation (embed)

variable {L : Type} [LevelOrder L] {graph : MembershipGraph} (coding : GraphCode graph)

/-- **The graph verdict compiler into the package**: for a native type at a node, a closed term of the type of the
proofs of its sentence, or of the negation. -/
def graphVerdict {formula : Formula 0} (fragment : Formula.graphFragment formula = true) (node : Fin graph.size) :
    {proofTerm : CTm (Head L) 0 //
        CTyped (setLaws L) .nil proofTerm (cHolds (trTerm (embed (graphSentence coding formula node))))} ⊕
      {proofTerm : CTm (Head L) 0 //
        CTyped (setLaws L) .nil proofTerm (cHolds (trTerm (embed (negCore (graphSentence coding formula node)))))} :=
  match compileGraph coding fragment node with
  | .inl proof => .inl ⟨packageTerm proof, packageTerm_typed proof⟩
  | .inr proof => .inr ⟨packageTerm proof, packageTerm_typed proof⟩

end Package

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

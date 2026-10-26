import Mettapedia.OSLF.NativeTypes.GeneratedLogic.HypersetProofs

/-!
# What the sentences about coded graphs mean

A coding of a graph's nodes gives a native structure on all the sets (`codedGraph`): a set steps to another when
they are the codes of a node and of one of its children, and two codes are the same when their nodes are bisimilar.

- **The sentences mean the coded graph** (`denote_graphFormula`): on the fragment of steps, connectives and fixed
  points, a translated formula is true at a set exactly when the native type holds there in the coded graph. An edge
  is true exactly between the codes of a node and a child (`denote_edgeFormula`).
- **Coding is a step morphism** from the graph's finite structure onto the coded graph (`codeMorphism`): the codes of
  different nodes are different sets.
- **So a sentence about a coded graph is true in the model of the sets exactly when the hyperset the node pictures has
  the native type** (`models_graphSentence`), through decoration (`MembershipGraph.eval_iff_hyperset`). The package's
  proof of the sentence for Ω's graph and the native type `νX. ◇X` is a proof, inside the well-founded sets, that Ω
  descends forever.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Logic.HOL (Ty Ctx Var Term ClosedFormula weaken rename subst instantiate Subst Rename)
open Mettapedia.Logic.HOL.ImpredicativeConnectives (truth falsity conjunctionFormula disjunctionFormula
  existentialInline)
open Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation (Symbol model member)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.HypersetGraphs (MembershipGraph hypersets)
open Mettapedia.TypeTheory.MaterialSets.Hypersets (HSet)

variable {graph : MembershipGraph} (coding : GraphCode graph)

/-- **The coded graph among the sets**: a set steps to another when they are the codes of a node and of one of its
children, and two codes are the same when their nodes are bisimilar. -/
def codedGraph : NativeStructure ZFSet.{0} where
  step source label target := memberLabel label ∧ ∃ node child, child ∈ graph.children node ∧
    source = zfOf (coding.code node) ∧ target = zfOf (coding.code child)
  built _ _ _ := False
  split _ _ _ _ := False
  empty _ _ := False
  single _ _ _ := False
  body _ _ := False
  multiBody _ _ _ := False
  bound _ _ := False
  typed _ _ := False
  named _ _ := False
  same first second := ∃ a b, first = zfOf (coding.code a) ∧ second = zfOf (coding.code b) ∧ graph.bisim a b = true
  apply inner _ := inner

theorem code_injective {first second : Fin graph.size} (same : zfOf (coding.code first) = zfOf (coding.code second)) :
    first = second := by
  by_contra differ
  exact coding.apart first second differ same

theorem setValue_code_iff {Γ : Ctx Unit} (valuation : model.{0}.Valuation Γ) (x : Term Symbol Γ setTy) (node : Fin graph.size) :
    (model.denote (describesSome (membersOf (coding.code node)) x) valuation).down ↔
      setValue x valuation = zfOf (coding.code node) := by
  rw [denote_describesSome (hf_members (coding.hereditary node)), ← zfOf_eq_zfOfList (coding.hereditary node)]

/-- **An edge is true exactly between the codes of a listed node and its child.** -/
theorem denote_edgeFormula {Γ : Ctx Unit} (valuation : model.{0}.Valuation Γ) (a b : Term Symbol Γ setTy) :
    ∀ edges : List (Fin graph.size × Fin graph.size),
      (model.denote (edgeFormula coding edges a b) valuation).down ↔
        ∃ entry ∈ edges, setValue a valuation = zfOf (coding.code entry.1) ∧
          setValue b valuation = zfOf (coding.code entry.2)
  | [] => (denote_falsity valuation).trans ⟨False.elim, fun ⟨_, member, _⟩ => (nomatch member)⟩
  | entry :: rest => by
    rw [edgeFormula, denote_disjunctionFormula, denote_conjunctionFormula, setValue_code_iff, setValue_code_iff,
      denote_edgeFormula valuation a b rest]
    constructor
    · rintro (found | ⟨other, member, found⟩)
      · exact ⟨entry, List.mem_cons_self, found⟩
      · exact ⟨other, List.mem_cons_of_mem _ member, found⟩
    · rintro ⟨other, member, found⟩
      rcases List.mem_cons.mp member with rfl | member
      · exact Or.inl found
      · exact Or.inr ⟨other, member, found⟩

theorem edge_step_iff {Γ : Ctx Unit} (valuation : model.{0}.Valuation Γ) (a b : Term Symbol Γ setTy) :
    (model.denote (edgeFormula coding (graphEdges graph) a b) valuation).down ↔
      ∃ node child, child ∈ graph.children node ∧ setValue a valuation = zfOf (coding.code node) ∧
        setValue b valuation = zfOf (coding.code child) := by
  rw [denote_edgeFormula]
  constructor
  · rintro ⟨⟨node, child⟩, member, found⟩
    exact ⟨node, child, mem_graphEdges.mp member, found⟩
  · rintro ⟨node, child, member, found⟩
    exact ⟨(node, child), mem_graphEdges.mpr member, found⟩

/-- **The sentences mean the coded graph**: on the fragment of steps, connectives and fixed points, a translated
formula is true exactly where its native type holds in the coded graph. -/
theorem denote_graphFormula : ∀ {n : ℕ} (formula : Formula n), Formula.graphFragment formula = true →
    ∀ {Γ : Ctx Unit} (valuation : model.{0}.Valuation Γ) (x : Term Symbol Γ setTy) (env : Fin n → Term Symbol Γ predTy)
      (sets : Env ZFSet.{0} n), EnvAgrees valuation env sets →
      ((model.denote (graphFormula coding formula x env) valuation).down ↔
        (codedGraph coding).sat sets formula (setValue x valuation))
  | _, .top, _, _, valuation, _, _, _, _ => iff_of_true (denote_truth valuation) trivial
  | _, .bot, _, _, valuation, _, _, _, _ => denote_falsity valuation
  | _, .and left right, fragment, _, valuation, x, env, sets, agrees => by
    simp only [Formula.graphFragment, Bool.and_eq_true] at fragment
    rw [graphFormula, denote_conjunctionFormula, denote_graphFormula left fragment.1 valuation x env sets agrees,
      denote_graphFormula right fragment.2 valuation x env sets agrees]
    rfl
  | _, .or left right, fragment, _, valuation, x, env, sets, agrees => by
    simp only [Formula.graphFragment, Bool.and_eq_true] at fragment
    rw [graphFormula, denote_disjunctionFormula, denote_graphFormula left fragment.1 valuation x env sets agrees,
      denote_graphFormula right fragment.2 valuation x env sets agrees]
    rfl
  | _, .var index, _, _, valuation, x, env, sets, agrees => agrees index (setValue x valuation)
  | _, .mu inner, fragment, _, valuation, x, env, sets, agrees => by
    have fragmentInner : Formula.graphFragment inner = true := fragment
    change (∀ predicate : Ty.denote model.{0}.Carrier predTy, True →
      (∀ z : ZFSet.{0}, True → (model.denote (graphFormula coding inner (.var .vz) (underFixedPoint env))
          (model.extend (σ := setTy) (model.extend (σ := predTy) valuation predicate) z)).down → (predicate z).down) →
        (predicate (setValue (weaken x) (model.extend (σ := predTy) valuation predicate))).down) ↔ _
    simp only [true_implies, setValue_weaken_pred]
    constructor
    · intro holds closed isClosed
      exact holds (fun w => ULift.up (w ∈ closed)) fun z inside => isClosed z
        ((denote_graphFormula inner fragmentInner _ (.var .vz) (underFixedPoint env) _
          (envAgrees_underFixedPoint valuation agrees (fun w => ULift.up (w ∈ closed)) z)).mp inside)
    · intro holds predicate isClosed
      exact holds {w | (predicate w).down} fun z inside => isClosed z
        ((denote_graphFormula inner fragmentInner _ (.var .vz) (underFixedPoint env) _
          (envAgrees_underFixedPoint valuation agrees predicate z)).mpr inside)
  | _, .nu inner, fragment, _, valuation, x, env, sets, agrees => by
    have fragmentInner : Formula.graphFragment inner = true := fragment
    rw [graphFormula, denote_existentialInline]
    change (∃ predicate : Ty.denote model.{0}.Carrier predTy, True ∧ (model.denote (conjunctionFormula
      (.all (σ := setTy) (.imp (.app (.var (.vs .vz)) (.var .vz))
        (graphFormula coding inner (.var .vz) (underFixedPoint env))))
      (.app (.var .vz) (weaken x))) (model.extend (σ := predTy) valuation predicate)).down) ↔ _
    simp only [true_and, denote_conjunctionFormula]
    change (∃ predicate : Ty.denote model.{0}.Carrier predTy,
      (∀ z : ZFSet.{0}, True → (predicate z).down → (model.denote (graphFormula coding inner (.var .vz)
          (underFixedPoint env)) (model.extend (σ := setTy) (model.extend (σ := predTy) valuation predicate) z)).down) ∧
        (predicate (setValue (weaken x) (model.extend (σ := predTy) valuation predicate))).down) ↔ _
    simp only [true_implies, setValue_weaken_pred]
    constructor
    · rintro ⟨predicate, preserved, inside⟩
      exact ⟨{w | (predicate w).down}, inside, fun z member =>
        (denote_graphFormula inner fragmentInner _ (.var .vz) (underFixedPoint env) _
          (envAgrees_underFixedPoint valuation agrees predicate z)).mp (preserved z member)⟩
    · rintro ⟨invariant, inside, preserved⟩
      exact ⟨fun w => ULift.up (w ∈ invariant), fun z member =>
        (denote_graphFormula inner fragmentInner _ (.var .vz) (underFixedPoint env) _
          (envAgrees_underFixedPoint valuation agrees (fun w => ULift.up (w ∈ invariant)) z)).mpr (preserved z member),
        inside⟩
  | _, .possibly label inner, fragment, _, valuation, x, env, sets, agrees => by
    have fragmentInner : Formula.graphFragment inner = true := fragment
    by_cases labelled : memberLabel label
    · simp only [graphFormula, if_pos labelled]
      rw [denote_existentialInline]
      change (∃ z : ZFSet.{0}, True ∧ (model.denote (conjunctionFormula
        (edgeFormula coding (graphEdges graph) (weaken x) (.var .vz))
        (graphFormula coding inner (.var .vz) (underElement env))) (model.extend (σ := setTy) valuation z)).down) ↔ _
      simp only [true_and, denote_conjunctionFormula, edge_step_iff, setValue_weaken_set, setValue_newest]
      refine exists_congr fun z => ?_
      rw [denote_graphFormula inner fragmentInner _ (.var .vz) (underElement env) sets
        (envAgrees_underElement valuation agrees z)]
      exact ⟨fun ⟨edge, holds⟩ => ⟨⟨labelled, edge⟩, holds⟩, fun ⟨⟨_, edge⟩, holds⟩ => ⟨edge, holds⟩⟩
    · simp only [graphFormula, if_neg labelled]
      exact (denote_falsity valuation).trans (iff_of_false id fun ⟨_, ⟨found, _⟩, _⟩ => labelled found)
  | _, .necessarily label inner, fragment, _, valuation, x, env, sets, agrees => by
    have fragmentInner : Formula.graphFragment inner = true := fragment
    by_cases labelled : memberLabel label
    · simp only [graphFormula, if_pos labelled]
      change (∀ z : ZFSet.{0}, True → (model.denote (edgeFormula coding (graphEdges graph) (weaken x) (.var .vz))
          (model.extend (σ := setTy) valuation z)).down →
        (model.denote (graphFormula coding inner (.var .vz) (underElement env)) (model.extend (σ := setTy) valuation z)).down)
          ↔ _
      simp only [true_implies, edge_step_iff, setValue_weaken_set, setValue_newest]
      refine forall_congr' fun z => ?_
      rw [denote_graphFormula inner fragmentInner _ (.var .vz) (underElement env) sets
        (envAgrees_underElement valuation agrees z)]
      exact ⟨fun holds step => holds step.2, fun holds edge => holds ⟨labelled, edge⟩⟩
    · simp only [graphFormula, if_neg labelled]
      exact iff_of_true (denote_truth valuation) fun _ step => (labelled step.1).elim
  | _, .sometimeBefore _ _, fragment, _, _, _, _, _, _ | _, .alwaysBefore _ _, fragment, _, _, _, _, _, _
  | _, .atLeast _ _ _ _, fragment, _, _, _, _, _, _ | _, .allButFewer _ _ _ _, fragment, _, _, _, _, _, _
  | _, .built _ _, fragment, _, _, _, _, _, _ | _, .everyBuilt _ _, fragment, _, _, _, _, _, _
  | _, .split _ _ _, fragment, _, _, _, _, _, _ | _, .everySplit _ _ _, fragment, _, _, _, _, _, _
  | _, .empty _, fragment, _, _, _, _, _, _ | _, .nonEmpty _, fragment, _, _, _, _, _, _
  | _, .single _ _, fragment, _, _, _, _, _, _ | _, .everySingle _ _, fragment, _, _, _, _, _, _
  | _, .body _, fragment, _, _, _, _, _, _ | _, .everyBody _, fragment, _, _, _, _, _, _
  | _, .multiBody _ _, fragment, _, _, _, _, _, _ | _, .everyMultiBody _ _, fragment, _, _, _, _, _, _
  | _, .bound _, fragment, _, _, _, _, _, _ | _, .notBound _, fragment, _, _, _, _, _, _
  | _, .typed _, fragment, _, _, _, _, _, _ | _, .untyped _, fragment, _, _, _, _, _, _
  | _, .is _, fragment, _, _, _, _, _, _ | _, .isNot _, fragment, _, _, _, _, _, _
  | _, .mapsAll _ _, fragment, _, _, _, _, _, _ | _, .mapsSome _ _, fragment, _, _, _, _, _, _
  | _, .someOf _ _, fragment, _, _, _, _, _, _ | _, .everyOf _ _, fragment, _, _, _, _, _, _ =>
    absurd fragment Bool.false_ne_true

/-- **Coding is a step morphism** from the graph's finite structure onto the coded graph. -/
def codeMorphism : StepMorphism graph.finite.native (codedGraph coding) where
  map node := zfOf (coding.code node)
  step := by
    intro source label target stepped
    have found := graphStep_iff.mp stepped
    exact ⟨found.1, source, target, found.2, rfl, rfl⟩
  stepBack := by
    rintro source label _ ⟨labelled, node, child, member, same, rfl⟩
    have equal := code_injective coding same
    subst equal
    exact ⟨child, graphStep_iff.mpr ⟨labelled, member⟩, rfl⟩
  sameIff first second := by
    change graph.bisim first second = true ↔ _
    constructor
    · exact fun related => ⟨first, second, rfl, rfl, related⟩
    · rintro ⟨a, b, sameA, sameB, related⟩
      rw [code_injective coding sameA, code_injective coding sameB]
      exact related
  namedIff _ _ := by
    change (false = true) ↔ False
    simp

theorem behaviouralForward_of_graphFragment : ∀ {n : ℕ} (formula : Formula n), Formula.graphFragment formula = true →
    formula.behaviouralForward = true
  | _, .top, _ | _, .bot, _ | _, .var _, _ => rfl
  | _, .and left right, fragment | _, .or left right, fragment => by
    simp only [Formula.graphFragment, Bool.and_eq_true] at fragment
    simp only [Formula.behaviouralForward, behaviouralForward_of_graphFragment left fragment.1,
      behaviouralForward_of_graphFragment right fragment.2, Bool.and_self]
  | _, .mu inner, fragment | _, .nu inner, fragment | _, .possibly _ inner, fragment
  | _, .necessarily _ inner, fragment => behaviouralForward_of_graphFragment inner fragment
  | _, .sometimeBefore _ _, fragment | _, .alwaysBefore _ _, fragment | _, .atLeast _ _ _ _, fragment
  | _, .allButFewer _ _ _ _, fragment | _, .built _ _, fragment | _, .everyBuilt _ _, fragment
  | _, .split _ _ _, fragment | _, .everySplit _ _ _, fragment | _, .empty _, fragment | _, .nonEmpty _, fragment
  | _, .single _ _, fragment | _, .everySingle _ _, fragment | _, .body _, fragment | _, .everyBody _, fragment
  | _, .multiBody _ _, fragment | _, .everyMultiBody _ _, fragment | _, .bound _, fragment
  | _, .notBound _, fragment | _, .typed _, fragment | _, .untyped _, fragment | _, .is _, fragment
  | _, .isNot _, fragment | _, .mapsAll _ _, fragment | _, .mapsSome _ _, fragment | _, .someOf _ _, fragment
  | _, .everyOf _ _, fragment => absurd fragment Bool.false_ne_true

/-- **A sentence about a coded graph is true in the model of the sets exactly when the hyperset the node pictures has
the native type.** -/
theorem models_graphSentence {formula : Formula 0} (fragment : Formula.graphFragment formula = true)
    (node : Fin graph.size) :
    model.{0}.models (graphSentence coding formula node) ↔ hypersets.sat Env.closed formula (HSet.decorate graph.edge node) := by
  rw [← graph.eval_iff_hyperset (behaviouralForward_of_graphFragment formula fragment) node,
    graph.finite.eval_iff formula Fin.elim0 node,
    (codeMorphism coding).sat_iff formula (behaviouralForward_of_graphFragment formula fragment)
      (targetEnv := Env.closed) (fun index => index.elim0) node]
  change (model.denote (existentialInline (σ := setTy) (conjunctionFormula (describes (coding.code node) (.var .vz))
    (graphFormula coding formula (.var .vz) Fin.elim0))) _).down ↔ _
  rw [denote_existentialInline]
  change (∃ z : ZFSet.{0}, True ∧ (model.denote (conjunctionFormula (describes (coding.code node) (.var .vz))
    (graphFormula coding formula (.var .vz) Fin.elim0)) (model.extend (σ := setTy) _ z)).down) ↔ _
  simp only [true_and, denote_conjunctionFormula, denote_describes (coding.hereditary node), setValue_newest]
  constructor
  · rintro ⟨z, rfl, holds⟩
    exact (denote_graphFormula coding formula fragment _ (.var .vz) Fin.elim0 Env.closed (fun index => index.elim0)).mp
      holds
  · intro holds
    exact ⟨_, rfl, (denote_graphFormula coding formula fragment _ (.var .vz) Fin.elim0 Env.closed
      (fun index => index.elim0)).mpr holds⟩

/-! ### Examples among the sets -/

section Examples

open Mettapedia.OSLF.NativeTypes.GeneratedLogic.HypersetGraphs (omega emptyGraph descendsForever wellFounded
  omega_decorate omega_descends_forever omega_not_wellFounded empty_wellFounded)

/-- **Ω's sentence "descends forever" is true among the well-founded sets**: its invariant is the set of codes. -/
theorem omega_sentence_descendsForever :
    model.{0}.models (graphSentence (GraphCode.single (graph := omega) rfl) descendsForever 0) := by
  rw [models_graphSentence _ rfl, omega_decorate]
  exact omega_descends_forever

/-- **Ω's sentence "every descent ends" is false among the well-founded sets.** -/
theorem omega_sentence_not_wellFounded :
    ¬ model.{0}.models (graphSentence (GraphCode.single (graph := omega) rfl) wellFounded 0) := by
  rw [models_graphSentence _ rfl, omega_decorate]
  exact omega_not_wellFounded

/-- **The empty set's sentences go the other way round.** -/
theorem empty_sentences :
    model.{0}.models (graphSentence (GraphCode.single (graph := emptyGraph) rfl) wellFounded 0) ∧
      ¬ model.{0}.models (graphSentence (GraphCode.single (graph := emptyGraph) rfl) descendsForever 0) := by
  rw [models_graphSentence _ rfl, models_graphSentence _ rfl]
  exact empty_wellFounded

end Examples

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

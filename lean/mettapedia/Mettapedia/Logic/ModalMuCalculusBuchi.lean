import Mettapedia.Logic.ModalQuantaleSemantics
import Mettapedia.Logic.Arithmetic.BuchiAutomaton
import Mettapedia.GSLT.LanguageDef.CertificateGSLTUltrainfinite
import Mettapedia.GSLT.LanguageDef.CertificateGSLTMuCalculusBoundary

/-!
# Existential Büchi recurrence in the modal μ-calculus

The formula `ν Z. μ Y. ((F ∧ ◇ Z) ∨ ◇ Y)` holds exactly when an infinite
path visits `F` beyond every finite prefix.  The free variable supplies `F`;
both bound variables occur positively.  All modalities here follow outgoing
transitions.  In particular this is neither the OSLF incoming right adjoint
nor an assertion about every nondeterministic path.

On finite state carriers, the existing least-fixed-point entry ranks select a
legal recurrent path.  Its recurrence follows from the existing controller
progress theorem.  Conversely, each accepting path gives a postfixed set by
backwards induction from its next accepting visit.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ModalMuCalculus

open Mettapedia.Logic.ModalQuantaleSemantics.Boolean
open Mettapedia.Order.FiniteSetFixedPoints
open Mettapedia.GSLT.LanguageDef.CertificateGSLT

universe u v

namespace Formula

/-- Existential infinite recurrence of the free observation at index zero. -/
def buchi {Act : Type v} (action : Act) : Formula Act 1 :=
  .nu (.mu (.disj
    (.conj (.var 2) (.diamond action (.var 1)))
    (.diamond action (.var 0))))

theorem buchi_positive {Act : Type v} (action : Act) :
    MuCalculusBoundary.fixedPointsPositive (buchi action) = true := rfl

end Formula

private def returnBody {Act : Type v} (action : Act) : Formula Act 3 :=
  .disj (.conj (.var 2) (.diamond action (.var 1)))
    (.diamond action (.var 0))

/-- Infinite recurrence along some outgoing path of one chosen action. -/
def BuchiPath {S : Type u} {Act : Type v} (lts : LTS S Act)
    (action : Act) (accepting : Set S) (root : S) : Prop :=
  ∃ path : Nat → S, path 0 = root ∧
    (∀ index, lts.trans (path index) action (path (index + 1))) ∧
    ∀ lower, ∃ visit, lower ≤ visit ∧ path visit ∈ accepting

private theorem buchi_unfold {S : Type u} {Act : Type v}
    (lts : LTS S Act) (action : Act) (accepting : Set S) (state : S) :
    satisfies lts (fun _ => accepting) (Formula.buchi action) state ↔
      satisfies lts
        (Env.extend ((fun _ => accepting) : Env S 1)
          (sat lts (fun _ => accepting) (Formula.buchi action)))
        (.mu (returnBody action)) state :=
  satisfies_nu_unfold_iff lts (fun _ => accepting)
    (.mu (returnBody action)) rfl state

private theorem path_satisfies_buchi {S : Type u} {Act : Type v}
    (lts : LTS S Act) (action : Act) (accepting : Set S) (root : S)
    (pathExists : BuchiPath lts action accepting root) :
    satisfies lts (fun _ => accepting) (Formula.buchi action) root := by
  obtain ⟨path, starts, edges, recurring⟩ := pathExists
  refine ⟨Set.range path, ⟨0, starts⟩, ?_⟩
  rintro _ ⟨index, rfl⟩ candidate preFixed
  obtain ⟨visit, after, accepted⟩ := recurring index
  have atVisit : path visit ∈ candidate := by
    apply preFixed (path visit)
    left
    refine ⟨accepted, path (visit + 1), edges visit, ?_⟩
    exact ⟨visit + 1, rfl⟩
  have backwards : ∀ distance, ∀ start, visit = start + distance →
      path start ∈ candidate := by
    intro distance
    induction distance with
    | zero =>
        intro start equal
        have equal' : visit = start := by omega
        simpa only [equal'] using atVisit
    | succ distance ih =>
        intro start equal
        apply preFixed (path start)
        right
        refine ⟨path (start + 1), edges start, ?_⟩
        apply ih (start + 1)
        omega
  exact backwards (visit - index) index (by omega)

private theorem buchi_has_path {S : Type u} [Finite S] {Act : Type v}
    (lts : LTS S Act) (action : Act) (accepting : Set S) (root : S)
    (satisfied : satisfies lts (fun _ => accepting) (Formula.buchi action) root) :
    BuchiPath lts action accepting root := by
  classical
  let winning := sat lts (fun _ => accepting) (Formula.buchi action)
  let environment : Env S 2 := Env.extend ((fun _ => accepting) : Env S 1) winning
  have unfoldWinning (state : S) : state ∈ winning ↔
      satisfies lts environment (.mu (returnBody action)) state :=
    buchi_unfold lts action accepting state
  let rank : S → Nat := fun state =>
    if member : state ∈ winning then
      muSemanticRank lts environment (returnBody action) rfl state
        ((unfoldWinning state).mp member)
    else 0
  have nextExists (state : S) (member : state ∈ winning) :
      ∃ target, lts.trans state action target ∧ target ∈ winning ∧
        (state ∉ accepting → rank target < rank state) := by
    let inner := (unfoldWinning state).mp member
    obtain ⟨previous, rankEq, body⟩ :=
      muSemanticRank_unfold lts environment (returnBody action) rfl state inner
    change (state ∈ accepting ∧ ∃ target, lts.trans state action target ∧
      target ∈ winning) ∨
      (∃ target, lts.trans state action target ∧ target ∈
        lowerApproximation (bodyOrderHom lts environment (returnBody action) rfl)
          previous) at body
    rcases body with ⟨accepted, target, edge, targetMember⟩ |
        ⟨target, edge, atPrevious⟩
    · exact ⟨target, edge, targetMember, fun absent => False.elim (absent accepted)⟩
    · obtain ⟨targetInner, targetRank⟩ :=
        exists_muSemanticRank_le_of_mem_lowerApproximation
          lts environment (returnBody action) rfl target previous atPrevious
      have targetMember := (unfoldWinning target).mpr targetInner
      refine ⟨target, edge, targetMember, fun _ => ?_⟩
      simp only [rank, dif_pos member, dif_pos targetMember]
      omega
  let next : S → S := fun state =>
    if member : state ∈ winning then (nextExists state member).choose else state
  have nextSpec (state : S) (member : state ∈ winning) :
      lts.trans state action (next state) ∧ next state ∈ winning ∧
        (state ∉ accepting → rank (next state) < rank state) := by
    simpa only [next, dif_pos member] using (nextExists state member).choose_spec
  let system : LabeledSystem S Unit :=
    ⟨fun source _ target => decide (lts.trans source action target),
      fun state => decide (state ∈ accepting)⟩
  let controller : MemorylessController S Unit :=
    ⟨fun state => decide (state ∈ winning), fun _ => (), next⟩
  let measure : ProgressMeasure S :=
    ⟨fun state => if state ∈ accepting then 0 else rank state⟩
  have valid : measure.Valid system controller root := by
    constructor
    · constructor
      · exact decide_eq_true satisfied
      · intro state active
        have member : state ∈ winning := of_decide_eq_true active
        exact ⟨decide_eq_true (nextSpec state member).1,
          decide_eq_true (nextSpec state member).2.1⟩
    · intro state active
      have member : state ∈ winning := of_decide_eq_true active
      change if decide (state ∈ accepting) then
        (if state ∈ accepting then 0 else rank state) = 0 else
        decide (next state ∈ accepting) = true ∨
          (if next state ∈ accepting then 0 else rank (next state)) <
            (if state ∈ accepting then 0 else rank state)
      by_cases accepted : state ∈ accepting
      · simp [accepted]
      · by_cases targetAccepted : next state ∈ accepting
        · simp [accepted, targetAccepted]
        · simp only [accepted, targetAccepted, decide_false, Bool.false_eq_true,
            ↓reduceIte, false_or]
          exact (nextSpec state member).2.2 accepted
  let execution := controller.canonicalExecution root
  have recurring := ProgressMeasure.buchi_sound valid execution
  have active : ∀ index, execution.state index ∈ winning := by
    intro index
    induction index with
    | zero =>
        change root ∈ winning
        exact satisfied
    | succ index ih =>
        rw [execution.follows]
        exact (nextSpec _ ih).2.1
  refine ⟨execution.state, execution.starts, ?_, ?_⟩
  · intro index
    rw [execution.follows]
    exact (nextSpec _ (active index)).1
  · intro lower
    obtain ⟨visit, after, accepted⟩ := recurring lower
    exact ⟨visit, after, of_decide_eq_true accepted⟩

/-- Exact existential Büchi semantics on a finite transition system. -/
theorem satisfies_buchi_iff_path {S : Type u} [Finite S] {Act : Type v}
    (lts : LTS S Act) (action : Act) (accepting : Set S) (root : S) :
    satisfies lts (fun _ => accepting) (Formula.buchi action) root ↔
      BuchiPath lts action accepting root :=
  ⟨buchi_has_path lts action accepting root,
    path_satisfies_buchi lts action accepting root⟩

namespace Buchi

open Mettapedia.Logic.Arithmetic.BuchiAutomaton

/-- Read an automaton's independently declared labelled transitions as an LTS. -/
def nbaLTS {S Act : Type} (automaton : NBA Act S) : LTS S Act where
  trans source action target := automaton.step source action target = true
  final := {state | automaton.accept state = true}

/-- Restrict only the initial-state predicate to the queried root. -/
def atRoot {S Act : Type} [DecidableEq S] (automaton : NBA Act S)
    (root : S) : NBA Act S :=
  { automaton with start := fun state => decide (state = root) }

/-- A native Büchi query at one root is acceptance by the automaton with that
root selected.  A unit alphabet quantifies over outgoing graph paths without
imposing an external word schedule. -/
theorem satisfies_buchi_iff_accepts {S : Type} [Finite S] [DecidableEq S]
    (automaton : NBA Unit S) (root : S) :
    satisfies (nbaLTS automaton)
        (fun _ => {state | automaton.accept state = true})
        (Formula.buchi ()) root ↔
      Accepts (atRoot automaton root) (fun _ => ()) := by
  rw [satisfies_buchi_iff_path]
  constructor
  · rintro ⟨path, starts, edges, recurring⟩
    exact ⟨path, decide_eq_true starts, edges, recurring⟩
  · rintro ⟨path, starts, edges, recurring⟩
    exact ⟨path, of_decide_eq_true starts, edges, recurring⟩

/-- The original initial-state predicate is retained when asking whether any
admitted root has an accepting infinite path. -/
theorem accepts_iff_exists_satisfies_buchi {S : Type} [Finite S]
    (automaton : NBA Unit S) :
    Accepts automaton (fun _ => ()) ↔
      ∃ root, automaton.start root = true ∧
        satisfies (nbaLTS automaton)
          (fun _ => {state | automaton.accept state = true})
          (Formula.buchi ()) root := by
  constructor
  · rintro ⟨path, starts, edges, recurring⟩
    refine ⟨path 0, starts, (satisfies_buchi_iff_path _ _ _ _).mpr ?_⟩
    exact ⟨path, rfl, edges, recurring⟩
  · rintro ⟨root, starts, satisfied⟩
    obtain ⟨path, pathStarts, edges, recurring⟩ :=
      (satisfies_buchi_iff_path _ _ _ _).mp satisfied
    exact ⟨path, pathStarts.symm ▸ starts, edges, recurring⟩

/-- Reuse the independently proved finite Büchi emptiness checker. -/
theorem decideNonempty_iff_buchi {S : Type} [Fintype S] [DecidableEq S]
    [Enumerable S] (automaton : NBA Unit S) (root : S) :
    decideNonempty (atRoot automaton root) = true ↔
      satisfies (nbaLTS automaton)
        (fun _ => {state | automaton.accept state = true})
        (Formula.buchi ()) root := by
  rw [decideNonempty_iff, satisfies_buchi_iff_accepts]
  constructor
  · rintro ⟨word, accepted⟩
    simpa only [Subsingleton.elim word (fun _ : Nat => ())] using accepted
  · intro accepted
    exact ⟨_, accepted⟩

/-- A finite native Büchi query has exactly the positive evidence checked by
the existing retained lasso machine.  Refusing one supplied lasso does not
refute the query. -/
theorem buchi_iff_lassoChecker {S : Type} [Fintype S] [DecidableEq S]
    (automaton : NBA Unit S) (root : S) :
    satisfies (nbaLTS automaton)
        (fun _ => {state | automaton.accept state = true})
        (Formula.buchi ()) root ↔
      ∃ certificate,
        (lassoChecker.run (lassoBudget certificate.stem certificate.loop)
          (Lasso.checkpoint (atRoot automaton root) certificate)).2 =
            .finished true := by
  rw [← accepts_iff_lassoChecker, satisfies_buchi_iff_accepts]
  constructor
  · intro accepted
    exact ⟨_, accepted⟩
  · rintro ⟨word, accepted⟩
    simpa only [Subsingleton.elim word (fun _ : Nat => ())] using accepted

namespace Controls

/-- Acceptance at a deadlock supplies no infinite path. -/
def acceptingTerminal : NBA Unit Unit where
  step _ _ _ := false
  start _ := true
  accept _ := true

theorem accepting_terminal_not_buchi :
    ¬ satisfies (nbaLTS acceptingTerminal) (fun _ => Set.univ)
      (Formula.buchi ()) () := by
  rw [satisfies_buchi_iff_path]
  rintro ⟨path, _starts, edges, _recurring⟩
  have impossible := edges 0
  change false = true at impossible
  cases impossible

/-- `AG EF True` is true at a deadlock, separating it from infinite recurrence. -/
theorem accepting_terminal_agef :
    satisfies (nbaLTS acceptingTerminal) Env.empty
      (Formula.alwaysEventually () .tt) () := by
  refine ⟨Set.univ, Set.mem_univ (), ?_⟩
  intro state _
  constructor
  · intro candidate preFixed
    exact preFixed state (Or.inl trivial)
  · intro target edge
    change false = true at edge
    cases edge

/-- Repeated visits on a genuine loop satisfy the same formula. -/
theorem accepting_loop_buchi :
    satisfies (nbaLTS ({ acceptingTerminal with step := fun _ _ _ => true }))
      (fun _ => Set.univ) (Formula.buchi ()) () := by
  apply (satisfies_buchi_iff_path _ _ _ _).mpr
  exact ⟨fun _ => (), rfl, fun _ => rfl, fun lower => ⟨lower, le_rfl, trivial⟩⟩

end Controls

end Buchi

end Mettapedia.Logic.ModalMuCalculus

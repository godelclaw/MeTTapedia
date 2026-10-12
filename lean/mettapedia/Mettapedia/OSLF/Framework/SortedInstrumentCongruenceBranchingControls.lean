import Mettapedia.OSLF.Framework.SortedInstrumentCongruenceLogic
import Mathlib.Data.Fintype.Order

/-!
# Control: finite conjunctions need finite branching

The signature has only constants and no equation beyond equality. Nothing
is admitted to the kit, so every step is authored and no instrument is
involved. One point steps to a chain of each finite length; another steps
to those chains and also to a point that steps forever.

The two points satisfy the same admitted formulas with finite conjunctions:
a formula of a given depth cannot tell the endless point from a chain at
least that long. They are not bisimilar: one infinite conjunction, which the
adequacy theorem makes sound, separates them. Consequently the authored
steps do not branch finitely, and the finite-conjunction characterization
cannot be stated without its branching hypothesis.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.SortedInstrumentCongruence.BranchingControls

open Mettapedia.OSLF.SortedConstructors

inductive Point where
  | left
  | right
  | endless
  | chain (remaining : Nat)

abbrev signature : Signature.{0,0} where
  Srt := Unit
  Constructor := Point
  arity _ := 0
  input _ _ := ()
  output _ := ()

/-- The constant of a point. -/
def constant (sort : signature.Srt) (point : Point) : Term signature sort :=
  Term.node (signature := signature) point (fun position => position.elim0)

/-- The point a closed term is the constant of. -/
def pointOf : {sort : signature.Srt} → Term signature sort → Point
  | _, .node constructor _ => constructor

theorem eq_constant {sort : signature.Srt} (term : Term signature sort) :
    term = constant sort (pointOf term) := by
  cases term with
  | node constructor arguments =>
    exact congrArg (Term.node (signature := signature) constructor)
      (funext fun position => position.elim0)

inductive Step : Point → Point → Prop where
  | leftChain (remaining : Nat) : Step .left (.chain remaining)
  | rightChain (remaining : Nat) : Step .right (.chain remaining)
  | rightEndless : Step .right .endless
  | endless : Step .endless .endless
  | chain (remaining : Nat) : Step (.chain (remaining + 1)) (.chain remaining)

theorem step_endless_iff (target : Point) : Step .endless target ↔ target = .endless := by
  constructor
  · intro step
    cases step
    rfl
  · rintro rfl
    exact .endless

theorem step_chain_succ_iff (remaining : Nat) (target : Point) :
    Step (.chain (remaining + 1)) target ↔ target = .chain remaining := by
  constructor
  · intro step
    cases step
    rfl
  · rintro rfl
    exact .chain remaining

theorem not_step_chain_zero (target : Point) : ¬ Step (.chain 0) target := by
  intro step
  cases step

theorem step_left_iff (target : Point) :
    Step .left target ↔ ∃ remaining, target = .chain remaining := by
  constructor
  · intro step
    cases step with
    | leftChain remaining => exact ⟨remaining, rfl⟩
  · rintro ⟨remaining, rfl⟩
    exact .leftChain remaining

theorem step_right_iff (target : Point) :
    Step .right target ↔ (∃ remaining, target = .chain remaining) ∨ target = .endless := by
  constructor
  · intro step
    cases step with
    | rightChain remaining => exact Or.inl ⟨remaining, rfl⟩
    | rightEndless => exact Or.inr rfl
  · rintro (⟨remaining, rfl⟩ | rfl)
    · exact .rightChain remaining
    · exact .rightEndless

/-- One authored label; no authored observation; equality as the equations. -/
def walking : BaseSystem.{0,0,0,0} (Congruence.equality signature) where
  Atom := Empty
  observes observation := observation.elim
  observes_resp observation := observation.elim
  Label := Unit
  act _ _ _ start next := Step (pointOf start) (pointOf next)
  act_resp_left := by
    rintro _ _ _ left right next rfl step
    exact ⟨next, step, rfl⟩
  act_resp_right := by
    rintro _ _ _ start next next' step rfl
    exact step

abbrev Sentence (sort : signature.Srt) := Formula signature walking.Atom walking.Label sort

/-- The authored diamond at a constant reads the step relation on points. -/
theorem holds_proper_iff {sort : signature.Srt} (label : Unit) (next : signature.Srt)
    (inner : Sentence next) (point : Point) :
    Holds walking (Formula.proper label next inner : Sentence sort) (constant sort point) ↔
      ∃ target : Point, Step point target ∧ Holds walking inner (constant next target) := by
  constructor
  · rintro ⟨target, step, satisfied⟩
    refine ⟨pointOf target, step, ?_⟩
    rw [← eq_constant target]
    exact satisfied
  · rintro ⟨target, step, satisfied⟩
    exact ⟨constant next target, step, satisfied⟩

/-- A bound on the nesting of authored diamonds. -/
def Bounded : {sort : signature.Srt} → Sentence sort → Nat → Prop
  | _, .conj parts, depth => ∀ index, Bounded (parts index) depth
  | _, .neg inner, depth => Bounded inner depth
  | _, .atom _, _ => True
  | _, .proper _ _ inner, depth => ∃ smaller, depth = smaller + 1 ∧ Bounded inner smaller
  | _, .node _ _, _ => True

theorem bounded_mono {sort : signature.Srt} (formula : Sentence sort) :
    ∀ {depth larger : Nat}, Bounded formula depth → depth ≤ larger → Bounded formula larger := by
  induction formula with
  | conj parts inductionHypothesis =>
    intro depth larger bounded le index
    exact inductionHypothesis index (bounded index) le
  | neg inner inductionHypothesis =>
    intro depth larger bounded le
    exact inductionHypothesis bounded le
  | atom observation =>
    intro depth larger _ _
    exact trivial
  | proper label next inner inductionHypothesis =>
    rintro depth larger ⟨smaller, rfl, bounded⟩ le
    obtain ⟨previous, rfl⟩ : ∃ previous, larger = previous + 1 := ⟨larger - 1, by omega⟩
    exact ⟨previous, rfl, inductionHypothesis bounded (by omega)⟩
  | node constructor arguments _ =>
    intro depth larger _ _
    exact trivial

/-- Finite conjunctions keep the nesting bounded. -/
theorem exists_bound {sort : signature.Srt} (formula : Sentence sort) :
    formula.Finitary → ∃ depth, Bounded formula depth := by
  induction formula with
  | @conj sort Index parts inductionHypothesis =>
    rintro ⟨finite, finitary⟩
    choose bound bounded using fun index => inductionHypothesis index (finitary index)
    obtain ⟨common, le⟩ := Finite.exists_le bound
    exact ⟨common, fun index => bounded_mono (parts index) (bounded index) (le index)⟩
  | neg inner inductionHypothesis => exact inductionHypothesis
  | atom observation => exact fun _ => ⟨0, trivial⟩
  | proper label next inner inductionHypothesis =>
    intro finitary
    obtain ⟨depth, bounded⟩ := inductionHypothesis finitary
    exact ⟨depth + 1, depth, rfl, bounded⟩
  | node constructor arguments _ => exact fun _ => ⟨0, trivial⟩

/-- A formula cannot tell the endless point from a chain at least as long as
its nesting. -/
theorem endless_iff_chain {sort : signature.Srt} (formula : Sentence sort) :
    ∀ depth, Bounded formula depth → formula.Allowed (fun _ => False) →
      ∀ remaining, depth ≤ remaining →
        (Holds walking formula (constant sort .endless) ↔
          Holds walking formula (constant sort (.chain remaining))) := by
  induction formula with
  | conj parts inductionHypothesis =>
    intro depth bounded allowed remaining le
    exact forall_congr' (fun index =>
      inductionHypothesis index depth (bounded index) (allowed index) remaining le)
  | neg inner inductionHypothesis =>
    intro depth bounded allowed remaining le
    exact not_congr (inductionHypothesis depth bounded allowed remaining le)
  | atom observation => exact observation.elim
  | proper label next inner inductionHypothesis =>
    rintro depth ⟨smaller, rfl, bounded⟩ allowed remaining le
    obtain ⟨previous, rfl⟩ : ∃ previous, remaining = previous + 1 := ⟨remaining - 1, by omega⟩
    refine (holds_proper_iff label next inner Point.endless).trans
      (Iff.trans ?_ (holds_proper_iff label next inner (Point.chain (previous + 1))).symm)
    constructor
    · rintro ⟨target, step, satisfied⟩
      obtain rfl := (step_endless_iff target).mp step
      exact ⟨.chain previous, .chain previous,
        (inductionHypothesis smaller bounded allowed previous (by omega)).mp satisfied⟩
    · rintro ⟨target, step, satisfied⟩
      obtain rfl := (step_chain_succ_iff previous target).mp step
      exact ⟨.endless, .endless,
        (inductionHypothesis smaller bounded allowed previous (by omega)).mpr satisfied⟩
  | node constructor arguments _ =>
    intro depth _ allowed
    exact allowed.1.elim

/-- The two starting points satisfy the same admitted formulas with finite
conjunctions. -/
theorem left_iff_right {sort : signature.Srt} (formula : Sentence sort) :
    formula.Finitary → formula.Allowed (fun _ => False) →
      (Holds walking formula (constant sort .left) ↔
        Holds walking formula (constant sort .right)) := by
  induction formula with
  | conj parts inductionHypothesis =>
    intro finitary allowed
    exact forall_congr' (fun index =>
      inductionHypothesis index (finitary.2 index) (allowed index))
  | neg inner inductionHypothesis =>
    intro finitary allowed
    exact not_congr (inductionHypothesis finitary allowed)
  | atom observation => exact observation.elim
  | proper label next inner _ =>
    intro finitary allowed
    refine (holds_proper_iff label next inner Point.left).trans
      (Iff.trans ?_ (holds_proper_iff label next inner Point.right).symm)
    constructor
    · rintro ⟨target, step, satisfied⟩
      obtain ⟨remaining, rfl⟩ := (step_left_iff target).mp step
      exact ⟨.chain remaining, .rightChain remaining, satisfied⟩
    · rintro ⟨target, step, satisfied⟩
      rcases (step_right_iff target).mp step with ⟨remaining, rfl⟩ | rfl
      · exact ⟨.chain remaining, .leftChain remaining, satisfied⟩
      · obtain ⟨depth, bounded⟩ := exists_bound inner finitary
        exact ⟨.chain depth, .leftChain depth,
          (endless_iff_chain inner depth bounded allowed depth le_rfl).mp satisfied⟩
  | node constructor arguments _ =>
    intro _ allowed
    exact allowed.1.elim

theorem finitaryEquivalent_left_right :
    FinitaryEquivalent walking (fun _ => False) (constant () .left) (constant () .right) :=
  fun formula allowed finitary => left_iff_right formula finitary allowed

/-- A run of the given length exists. -/
def runs : Nat → Sentence ()
  | 0 => Formula.top
  | length + 1 => Formula.proper () () (runs length)

theorem runs_allowed : ∀ length, (runs length).Allowed (fun _ => False)
  | 0 => fun index => index.elim
  | length + 1 => runs_allowed length

theorem endless_runs : ∀ length, Holds walking (runs length) (constant () .endless)
  | 0 => holds_top walking _
  | length + 1 =>
      (holds_proper_iff () () (runs length) .endless).mpr
        ⟨.endless, .endless, endless_runs length⟩

theorem chain_stops : ∀ remaining,
    ¬ Holds walking (runs (remaining + 1)) (constant () (.chain remaining))
  | 0 => by
      intro holds
      obtain ⟨target, step, -⟩ := (holds_proper_iff () () (runs 0) (.chain 0)).mp holds
      exact not_step_chain_zero target step
  | remaining + 1 => by
      intro holds
      obtain ⟨target, step, satisfied⟩ :=
        (holds_proper_iff () () (runs (remaining + 1)) (.chain (remaining + 1))).mp holds
      obtain rfl := (step_chain_succ_iff remaining target).mp step
      exact chain_stops remaining satisfied

/-- Some successor has runs of every length. The conjunction is infinite. -/
def reachesEndless : Sentence () :=
  Formula.proper () () (Formula.conj (Index := Nat) runs)

theorem right_reachesEndless : Holds walking reachesEndless (constant () .right) :=
  (holds_proper_iff () () _ .right).mpr ⟨.endless, .rightEndless, endless_runs⟩

theorem left_not_reachesEndless : ¬ Holds walking reachesEndless (constant () .left) := by
  intro holds
  obtain ⟨target, step, satisfied⟩ := (holds_proper_iff () () _ .left).mp holds
  obtain ⟨remaining, rfl⟩ := (step_left_iff target).mp step
  exact chain_stops remaining (satisfied (remaining + 1))

/-- The two starting points are not bisimilar. -/
theorem not_bisimilar_left_right :
    ¬ Bisimilar walking (fun _ => False) (.term (constant () .left))
      (.term (constant () .right)) := by
  intro related
  have equivalent :=
    (logicallyEquivalent_iff_bisimilar walking (fun _ => False) _ _).mpr related
  exact left_not_reachesEndless
    ((equivalent reachesEndless runs_allowed).mpr right_reachesEndless)

/-- **Finite conjunctions are not adequate without a branching hypothesis.** -/
theorem finite_conjunctions_inadequate :
    FinitaryEquivalent walking (fun _ => False) (constant () .left) (constant () .right) ∧
      ¬ Bisimilar walking (fun _ => False) (.term (constant () .left))
        (.term (constant () .right)) :=
  ⟨finitaryEquivalent_left_right, not_bisimilar_left_right⟩

/-- The authored steps of this system do not branch finitely. -/
theorem not_finiteAuthoredBranching : ¬ FiniteAuthoredBranching walking := by
  intro finite
  have decompositions : FiniteDecompositions (Congruence.equality signature) (fun _ => False) :=
    fun _ permission => permission.elim
  exact not_bisimilar_left_right
    ((finitaryEquivalent_iff_bisimilar finite decompositions _ _).mp
      finitaryEquivalent_left_right)

end Mettapedia.OSLF.Framework.SortedInstrumentCongruence.BranchingControls

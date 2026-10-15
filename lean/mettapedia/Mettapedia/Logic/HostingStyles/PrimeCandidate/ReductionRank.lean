import Mettapedia.GSLT.Contexts.HostingInvariants
import Mettapedia.GSLT.Contexts.ReductionProfiles
import Mettapedia.GSLT.Dedukti.TableEvaluator

/-!
# Ranks: a bound on the length of reductions, and what it excludes

A *rank* on a theory is a natural number on its terms that every step lowers
(`ContextTheory.Rank`).  A theory with a rank is terminating
(`Rank.terminating`), a reduction of `count` steps starts at a term of rank at
least `count` (`Rank.steps_le`), and the same rank serves when a nonempty
finite reduction is counted as one transition (`Rank.nonempty`).

A map that preserves transitions sends a reduction of `count` steps to one of
`count` steps (`ContextMap.steps_of_preserves`) and a cycle to a cycle
(`ContextMap.cycle_of_preserves`).  So a theory with a rank receives no
transition-preserving map from a theory with a cyclic reduction, at the
profile of single steps (`ContextMap.not_preserves_of_cycle_of_rank`) and at
the profile of nonempty reductions (`ContextMap.not_simulates_of_cycle_of_rank`);
and a theory whose ranks are at most `bound` receives none from a theory with
a reduction of more than `bound` steps (`ContextMap.not_preserves_of_steps`).

The rule-table evaluator has a cyclic reduction under every table: the term
`(λ x. x x) (λ x. x x)` contracts to itself (`omega_step`,
`tableEvaluator_cycle`).  Every theory of the λΠ-calculus modulo has it too.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT

universe u

namespace ContextTheory

variable (theory : ContextTheory.{u})

/-- **A rank**: a natural number on the terms of a theory that every step
lowers. -/
structure Rank where
  /-- The rank of a term. -/
  rank : {interface : theory.Interface} → theory.Term interface → Nat
  lowers : ∀ {interface : theory.Interface} {term next : theory.Term interface},
    theory.rewrites term next → rank next < rank term

/-- A reduction of exactly `count` steps. -/
inductive Steps {interface : theory.Interface} :
    Nat → theory.Term interface → theory.Term interface → Prop where
  | zero (term : theory.Term interface) : Steps 0 term term
  | succ {count : Nat} {term next final : theory.Term interface} :
      theory.rewrites term next → Steps count next final → Steps (count + 1) term final

variable {theory}

namespace Rank

/-- **A theory with a rank is terminating.** -/
theorem terminating (ranked : theory.Rank) : theory.Terminating :=
  fun _ => Subrelation.wf (fun step => ranked.lowers step) (InvImage.wf ranked.rank Nat.lt_wfRel.wf)

/-- A nonempty reduction lowers the rank. -/
theorem transGen_lt (ranked : theory.Rank) {interface : theory.Interface}
    {term final : theory.Term interface}
    (steps : Relation.TransGen theory.rewrites term final) : ranked.rank final < ranked.rank term := by
  induction steps with
  | single step => exact ranked.lowers step
  | tail _ step ih => exact (ranked.lowers step).trans ih

/-- **A reduction of `count` steps starts at a term of rank at least
`count`** above the rank it ends at. -/
theorem steps_le (ranked : theory.Rank) {interface : theory.Interface} {count : Nat}
    {term final : theory.Term interface}
    (steps : theory.Steps count term final) : count + ranked.rank final ≤ ranked.rank term := by
  induction steps with
  | zero term => exact (Nat.zero_add _).le
  | succ step _ ih =>
      have lowered := ranked.lowers step
      omega

/-- A theory with a rank has no cyclic reduction. -/
theorem not_cycle (ranked : theory.Rank) {interface : theory.Interface}
    {term : theory.Term interface}
    (cycle : Relation.TransGen theory.rewrites term term) : False :=
  lt_irrefl _ (ranked.transGen_lt cycle)

/-- **The same rank serves at the profile of nonempty reductions.** -/
def nonempty (ranked : theory.Rank) : theory.nonemptyReduction.Rank where
  rank := ranked.rank
  lowers := fun steps => ranked.transGen_lt steps

end Rank

/-- A reduction of a positive number of steps is a nonempty reduction. -/
theorem Steps.transGen {interface : theory.Interface} {count : Nat}
    {term final : theory.Term interface} (steps : theory.Steps (count + 1) term final) :
    Relation.TransGen theory.rewrites term final := by
  generalize size : count + 1 = total at steps
  induction steps generalizing count with
  | zero term => exact absurd size (Nat.succ_ne_zero count)
  | @succ rest term next final step tail ih =>
      cases rest with
      | zero =>
          cases tail
          exact .single step
      | succ rest => exact Relation.TransGen.head step (ih rfl)

end ContextTheory

namespace ContextMap

variable {source target : ContextTheory.{u}} (map : ContextMap source target)

/-- **A map that preserves transitions sends a reduction of `count` steps to
a reduction of `count` steps.** -/
theorem steps_of_preserves (preserves : map.PreservesTransitions) {interface : source.Interface}
    {count : Nat} {term final : source.Term interface} (steps : source.Steps count term final) :
    target.Steps count (map.term term) (map.term final) := by
  induction steps with
  | zero term => exact .zero _
  | succ step _ ih => exact .succ (map.preservesRewrites_of_transitions preserves step) ih

/-- **A map that preserves transitions sends a cycle to a cycle.**  A host of
a theory with a cyclic reduction has one. -/
theorem cycle_of_preserves (preserves : map.PreservesTransitions) {interface : source.Interface}
    {term : source.Term interface} (cycle : Relation.TransGen source.rewrites term term) :
    Relation.TransGen target.rewrites (map.term term) (map.term term) := by
  have lifted : ∀ {final : source.Term interface}, Relation.TransGen source.rewrites term final →
      Relation.TransGen target.rewrites (map.term term) (map.term final) := by
    intro final steps
    induction steps with
    | single step => exact .single (map.preservesRewrites_of_transitions preserves step)
    | tail _ step ih => exact ih.tail (map.preservesRewrites_of_transitions preserves step)
  exact lifted cycle

/-- **No theory with a rank receives a transition-preserving map from a
theory with a cyclic reduction.** -/
theorem not_preserves_of_cycle_of_rank (ranked : target.Rank) {interface : source.Interface}
    {term : source.Term interface} (cycle : Relation.TransGen source.rewrites term term) :
    ¬ map.PreservesTransitions :=
  fun preserves => ranked.not_cycle (map.cycle_of_preserves preserves cycle)

/-- **Nor at the profile of nonempty reductions**: no map sends each step of
a theory with a cyclic reduction to a nonempty reduction of a theory with a
rank. -/
theorem not_simulates_of_cycle_of_rank (ranked : target.Rank)
    (map : ContextMap source target.nonemptyReduction) {interface : source.Interface}
    {term : source.Term interface} (cycle : Relation.TransGen source.rewrites term term) :
    ¬ map.PreservesTransitions :=
  map.not_preserves_of_cycle_of_rank ranked.nonempty cycle

/-- **A theory whose ranks are at most `bound` receives no
transition-preserving map from a theory with a reduction of more than `bound`
steps.** -/
theorem not_preserves_of_steps (ranked : target.Rank) {bound : Nat}
    (bounded : ∀ {interface : target.Interface} (term : target.Term interface),
      ranked.rank term ≤ bound)
    {interface : source.Interface} {count : Nat} {term final : source.Term interface}
    (steps : source.Steps count term final) (longer : bound < count) :
    ¬ map.PreservesTransitions := by
  intro preserves
  have image := ranked.steps_le (map.steps_of_preserves preserves steps)
  have top := bounded (map.term term)
  omega

end ContextMap

/-! ## The cyclic reduction of the rule-table evaluator -/

namespace Dedukti

open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (subst0)

/-- `λ x : Type. x x`. -/
def selfApplication : Term := .lam (.srt .type) (.app (.var 0) (.var 0))

/-- `(λ x. x x) (λ x. x x)`. -/
def omega : Term := .app selfApplication selfApplication

/-- **`omega` contracts to itself**, in every theory. -/
theorem omega_step (theory : Theory) : Step theory omega omega := by
  have contracted : subst0 selfApplication (.app (.var 0) (.var 0)) = omega := by decide
  have root : RootStep theory omega (subst0 selfApplication (.app (.var 0) (.var 0))) :=
    .beta (.srt .type) (.app (.var 0) (.var 0)) selfApplication
  rw [contracted] at root
  exact Step.root root

/-- **The rule-table evaluator has a cyclic reduction under every table.** -/
theorem tableEvaluator_cycle (table : RuleTable) :
    Relation.TransGen (tableEvaluator.rewrites (interface := ()))
      (⟨table, omega⟩ : Tabled) ⟨table, omega⟩ :=
  .single ⟨rfl, omega_step _⟩

/-- Every theory of the λΠ-calculus modulo has a cyclic reduction. -/
theorem rewritingTheory_cycle (theory : Theory) :
    Relation.TransGen ((rewritingTheory theory).rewrites (interface := ())) omega omega :=
  .single (omega_step theory)

/-- The evaluator has reductions of every length. -/
theorem tableEvaluator_steps (table : RuleTable) (count : Nat) :
    tableEvaluator.Steps (interface := ()) count (⟨table, omega⟩ : Tabled) ⟨table, omega⟩ := by
  induction count with
  | zero => exact .zero _
  | succ count ih => exact .succ ⟨rfl, omega_step _⟩ ih

/-- **Negative**: the rule-table evaluator has no rank. -/
theorem tableEvaluator_not_rank : IsEmpty tableEvaluator.Rank :=
  ⟨fun ranked => ranked.not_cycle (tableEvaluator_cycle ∅)⟩

/-- **No theory with a rank receives a transition-preserving map from the
rule-table evaluator.** -/
theorem tableEvaluator_not_preserves_into_rank {target : ContextTheory.{0}} (ranked : target.Rank)
    (map : ContextMap tableEvaluator target) : ¬ map.PreservesTransitions :=
  map.not_preserves_of_cycle_of_rank ranked (tableEvaluator_cycle ∅)

end Dedukti

/-- **Positive**: a theory without reduction has the rank that is zero
everywhere. -/
def ContextTheory.Rank.ofStatic {theory : ContextTheory.{u}} (static : theory.Static) :
    theory.Rank where
  rank := fun _ => 0
  lowers := fun step => (static _ _ step).elim

#print axioms ContextTheory.Rank.terminating
#print axioms ContextTheory.Rank.steps_le
#print axioms ContextTheory.Rank.nonempty
#print axioms ContextTheory.Steps.transGen
#print axioms ContextMap.steps_of_preserves
#print axioms ContextMap.cycle_of_preserves
#print axioms ContextMap.not_preserves_of_cycle_of_rank
#print axioms ContextMap.not_simulates_of_cycle_of_rank
#print axioms ContextMap.not_preserves_of_steps
#print axioms Dedukti.omega_step
#print axioms Dedukti.tableEvaluator_cycle
#print axioms Dedukti.tableEvaluator_steps
#print axioms Dedukti.tableEvaluator_not_rank
#print axioms Dedukti.tableEvaluator_not_preserves_into_rank

end Mettapedia.GSLT

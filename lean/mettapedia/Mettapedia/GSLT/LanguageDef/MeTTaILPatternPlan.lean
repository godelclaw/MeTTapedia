import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# First-order pattern plans

The carrier of first-order rule compilation (`MeTTaILFirstOrderRuleCompilation`): metavariables,
rigid bound occurrences and ordered applications, with their structural work and their erasure
back to source patterns. Matchers that only consume plans import this module, not the compiler.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderRuleCompilation

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- The admitted first-order pattern fragment. -/
inductive PatternPlan where
  | metavariable (name : String)
  | bound (index : Nat)
  | application (constructor : String) (arguments : List PatternPlan)
deriving Repr

mutual
  /-- Structural work of one pattern plan.  Besides proving totality, this is
  the source-size component of later residual-code bounds. -/
  def PatternPlan.work : PatternPlan -> Nat
    | .metavariable _ | .bound _ => 1
    | .application _ arguments => 1 + patternPlansWork arguments

  /-- Structural work of an ordered child vector. -/
  def patternPlansWork : List PatternPlan -> Nat
    | [] => 0
    | plan :: plans => plan.work + patternPlansWork plans
end

@[simp] theorem PatternPlan.work_pos (plan : PatternPlan) : 0 < plan.work := by
  cases plan <;> simp [PatternPlan.work]

mutual
  /-- Erase a compiled plan to its complete source pattern. -/
  def PatternPlan.erase : PatternPlan -> Pattern
    | .metavariable name => .fvar name
    | .bound index => .bvar index
    | .application constructor arguments =>
        .apply constructor (erasePatterns arguments)

  /-- Erase an ordered row of plans. -/
  def erasePatterns : List PatternPlan -> List Pattern
    | [] => []
    | plan :: plans => plan.erase :: erasePatterns plans
end

/-- Erasure retains each child occurrence in its authored order. -/
theorem erasePatterns_eq_map (plans : List PatternPlan) :
    erasePatterns plans = plans.map PatternPlan.erase := by
  induction plans with
  | nil => rfl
  | cons plan plans ih => simp only [erasePatterns, List.map_cons, ih]

@[simp] theorem erasePatterns_length (plans : List PatternPlan) :
    (erasePatterns plans).length = plans.length := by
  induction plans with
  | nil => rfl
  | cons plan plans inductionHypothesis =>
      simp [erasePatterns, inductionHypothesis]

end Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderRuleCompilation

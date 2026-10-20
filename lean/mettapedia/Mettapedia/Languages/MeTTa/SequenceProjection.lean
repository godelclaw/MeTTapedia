import Mettapedia.Languages.MeTTa.SubstitutionAlgebra

/-!
# Structural projection and delayed substitution

The shared atom carrier represents a MeTTa expression as a sequence. Once
argument evaluation and root resolution have exposed that sequence, selecting
its first element or suffix commutes with substitution. Unselected structure
need not be rebuilt. The selected syntax retains its environment: later
substitution still applies, including to repeated occurrences of a variable.

These are laws of the structural observation, not definitions of argument
evaluation, callable-head selection, empty-input errors or internal carriers.
In particular the root-shape premise cannot be dropped for an unresolved
variable. Physical ownership and representation checks remain separate.
-/

namespace Mettapedia.Languages.MeTTa.SequenceProjection

open OSLFCore (Atom)
open SubstitutionAlgebra

inductive Direction where
  | head
  | tail
  deriving DecidableEq

/-- The successful nonempty structural observation. Dialect-specific handling
of empty and non-sequence inputs belongs to its caller. -/
def project : Direction → Atom → Option Atom
  | .head, .expression (first :: _) => some first
  | .tail, .expression (_ :: rest) => some (.expression rest)
  | _, _ => none

/-- Independent eager and deferred observations agree after the root has
been exposed as an expression. -/
theorem project_subst_expression (direction : Direction) (σ : Subst)
    (elements : List Atom) :
    project direction (subst σ (.expression elements)) =
      (project direction (.expression elements)).map (subst σ) := by
  cases direction <;> cases elements <;> rfl

/-- Retaining the environment through another refinement preserves projection;
the first observation does not freeze the selected variables. -/
theorem project_subst_refinement (direction : Direction) (σ τ : Subst)
    (elements : List Atom) :
    project direction (subst τ (subst σ (.expression elements))) =
      (project direction (.expression elements)).map (subst (comp σ τ)) := by
  rw [subst_subst]
  exact project_subst_expression direction (comp σ τ) elements

/-- Head projection depends only on the selected element's variable support,
even when the unused suffix has different bindings. -/
theorem head_subst_congr (σ τ : Subst) (first : Atom) (rest : List Atom)
    (agree : ∀ name ∈ vars first, σ name = τ name) :
    project .head (subst σ (.expression (first :: rest))) =
      project .head (subst τ (.expression (first :: rest))) := by
  change some (subst σ first) = some (subst τ first)
  rw [subst_congr_on_vars σ τ first agree]

/-- Tail projection does not demand the discarded head. -/
theorem tail_subst_ignores_head (σ : Subst) (left right : Atom)
    (rest : List Atom) :
    project .tail (subst σ (.expression (left :: rest))) =
      project .tail (subst σ (.expression (right :: rest))) := by
  rfl

private def renameX : Subst
  | "x" => some (.var "y")
  | _ => none

private def finish : Subst
  | "y" => some (.symbol "done")
  | _ => none

example :
    project .tail
      (subst finish (subst renameX
        (.expression [.symbol "tag", .var "x", .var "x"]))) =
      some (.expression [.symbol "done", .symbol "done"]) := by
  rfl

example :
    project .head (subst renameX (.expression [.var "x"])) ≠
      project .head
        (subst finish (subst renameX (.expression [.var "x"]))) := by
  decide

/-- A root variable can acquire sequence shape. Projecting before resolving
that root loses an answer, so the expression premise above is necessary. -/
example :
    let σ : Subst := fun name =>
      if name = "root" then some (.expression [.symbol "value"]) else none
    project .head (subst σ (.var "root")) ≠
      (project .head (.var "root")).map (subst σ) := by
  decide

end Mettapedia.Languages.MeTTa.SequenceProjection

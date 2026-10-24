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

/-! ## Open-cons values

The runtime's open-cons carrier is a resolved constructor with two borrowed
children.  It can have an improper or still-open tail, so it is deliberately
not identified with `Atom.expression`.  Once this constructor has been
recognized, its eliminator reads exactly one child and leaves the other child
and every deeper node untouched.
-/

/-- The semantic payload of an already-recognized open-cons carrier. -/
structure OpenCons where
  head : Atom
  tail : Atom
  deriving DecidableEq

def OpenCons.subst (σ : Subst) (cell : OpenCons) : OpenCons :=
  ⟨SubstitutionAlgebra.subst σ cell.head,
   SubstitutionAlgebra.subst σ cell.tail⟩

/-- Projection after carrier recognition. Root recognition and ownership are
separate premises of the runtime admission check. -/
def projectOpenCons : Direction → OpenCons → Atom
  | .head, cell => cell.head
  | .tail, cell => cell.tail

/-- Selecting a carrier child commutes with every later substitution. -/
theorem projectOpenCons_subst (direction : Direction) (σ : Subst)
    (cell : OpenCons) :
    projectOpenCons direction (cell.subst σ) =
      SubstitutionAlgebra.subst σ (projectOpenCons direction cell) := by
  cases direction <;> rfl

/-- Tail observation does not inspect or substitute the discarded head. -/
theorem openCons_tail_ignores_head (left right tail : Atom) :
    projectOpenCons .tail ⟨left, tail⟩ =
      projectOpenCons .tail ⟨right, tail⟩ := by
  rfl

/-! ### Root-query lower bound

This is the exact pointer-access region used by the fast path: before the
carrier is recognized, the algorithm either returns a constant without
reading it, or performs one root read which exposes both child pointers.  It
does not claim an allocation or cache bound for the surrounding evaluator.
-/

/-- Decision programs in the opaque-root access model. -/
inductive RootProgram where
  | constant (answer : Atom)
  | inspect (select : Atom → Atom → Atom)

def RootProgram.run : RootProgram → OpenCons → Atom
  | .constant answer, _ => answer
  | .inspect select, cell => select cell.head cell.tail

def RootProgram.rootReads : RootProgram → Nat
  | .constant _ => 0
  | .inspect _ => 1

def RootProgram.Correct (direction : Direction) (program : RootProgram) : Prop :=
  ∀ cell, program.run cell = projectOpenCons direction cell

/-- The direct constructor eliminator. -/
def directRootProgram : Direction → RootProgram
  | .head => .inspect fun head _ => head
  | .tail => .inspect fun _ tail => tail

theorem directRootProgram_correct (direction : Direction) :
    (directRootProgram direction).Correct direction := by
  intro cell
  cases direction <;> rfl

theorem directRootProgram_one_read (direction : Direction) :
    (directRootProgram direction).rootReads = 1 := by
  cases direction <;> rfl

/-- No zero-read program can implement either projection for all carriers.
Thus the one-read eliminator is optimal in this root-query model. -/
theorem correct_rootReads_lower_bound (direction : Direction)
    (program : RootProgram) (correct : program.Correct direction) :
    1 ≤ program.rootReads := by
  cases program with
  | inspect select => rfl
  | constant answer =>
      cases direction with
      | head =>
          have first := correct ⟨.symbol "first", .symbol "tail"⟩
          have second := correct ⟨.symbol "second", .symbol "tail"⟩
          simp only [RootProgram.run, projectOpenCons] at first second
          have impossible : (Atom.symbol "first") = Atom.symbol "second" :=
            first.symm.trans second
          have absurd : False :=
            (by decide : (Atom.symbol "first") ≠ Atom.symbol "second") impossible
          exact absurd.elim
      | tail =>
          have first := correct ⟨.symbol "head", .symbol "first"⟩
          have second := correct ⟨.symbol "head", .symbol "second"⟩
          simp only [RootProgram.run, projectOpenCons] at first second
          have impossible : (Atom.symbol "first") = Atom.symbol "second" :=
            first.symm.trans second
          have absurd : False :=
            (by decide : (Atom.symbol "first") ≠ Atom.symbol "second") impossible
          exact absurd.elim

/-- The direct path attains the lower bound. -/
theorem directRootProgram_optimal (direction : Direction) :
    (directRootProgram direction).Correct direction ∧
      (directRootProgram direction).rootReads = 1 ∧
      ∀ (program : RootProgram), program.Correct direction →
        (directRootProgram direction).rootReads ≤ program.rootReads := by
  refine ⟨directRootProgram_correct direction,
    directRootProgram_one_read direction, ?_⟩
  intro program correct
  rw [directRootProgram_one_read]
  exact correct_rootReads_lower_bound direction program correct

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

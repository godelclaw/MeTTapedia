import Mettapedia.Logic.HostingStyles.AuthoredEvaluators.MatchingSpec

/-!
# Writing equation programs on patterns, and proving what they compute

A small vocabulary for the equations of a program that computes on the data
of `PatternData`, and two tactics for the proofs that such a program computes
a given function.

* `call`, `slot`, `cell`, `empty`, `absent`, `present`, `pair`, `yes`, `no`,
  `same`: the terms of an equation.  `same` calls the equality primitive of
  the shared host; every other head that no equation defines is a
  constructor.
* `encodeBindings`: bindings as data, a chain of cells of pairs.
* `Constructs program head` declares a head as a constructor of a program on
  the shared host.
* `by_equation` unfolds a call by the equation that the program selects for
  it.  The selection is computed, so the equations before it are checked not
  to match.
* `engine keeps` evaluates the body of the selected equation: variables,
  names, constructors and comparisons by themselves, and each call of a head
  of the program by a statement given after `using`.  A call of a head of the
  program for which no statement is given is unfolded by its own equation.

Nothing here is assumed of a program: each use of the two tactics produces a
proof term over the engine's own `Applies` and `Evaluates`.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AuthoredEvaluators

open Mettapedia.GSLT.LanguageDef.DeterministicEquations
open Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction (encodeOption encoded_comparison)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match

/-! ## The terms of an equation -/

/-- A call of a head on arguments; a constructor when no equation defines the
head and the host does not handle it. -/
def call (head : String) (arguments : List Term) : Term := .expr (.sym head :: arguments)

/-- A variable of an equation. -/
def slot (name : String) : Term := .var name

/-- A cell of a list. -/
def cell (head tail : Term) : Term := call "Cons" [head, tail]

/-- The empty list. -/
def empty : Term := .sym "Nil"

/-- No value. -/
def absent : Term := .sym "None"

/-- A value. -/
def present (value : Term) : Term := call "Some" [value]

/-- A pair. -/
def pair (first second : Term) : Term := call "Pair" [first, second]

/-- The two answers of a comparison. -/
def yes : Term := .sym "True"

/-- The other answer. -/
def no : Term := .sym "False"

/-- The comparison of two data by the equality primitive of the shared
host. -/
def same (first second : Term) : Term := call "nik:data-eq" [first, second]

/-- **Positive**: a cell of the vocabulary is a cell of the data. -/
theorem cell_eq_cells (head : Term) (tail : List Term) : cell head (cells tail) = cells (head :: tail) :=
  rfl

/-- **Negative**: a variable of an equation is no data of a pattern. -/
theorem decodePattern_slot (name : String) : decodePattern (slot name) = none := rfl

/-! ## Bindings as data -/

/-- One binding: the name and the value. -/
def encodeBinding (binding : String × Pattern) : Term :=
  call "Pair" [encodeName binding.1, encodePattern binding.2]

/-- **Bindings, as data.** -/
def encodeBindings (bindings : Bindings) : Term := cells (bindings.map encodeBinding)

theorem encodeBinding_injective : Function.Injective encodeBinding := by
  rintro ⟨firstName, firstValue⟩ ⟨secondName, secondValue⟩ equal
  simp only [encodeBinding, call, Term.expr.injEq, List.cons.injEq, and_true, true_and] at equal
  rw [encodeName_injective equal.1, encodePattern_injective equal.2]

theorem encodeBindings_injective : Function.Injective encodeBindings := fun _ _ equal =>
  List.map_injective_iff.mpr encodeBinding_injective (cells_injective equal)

/-- **Positive**: one binding. -/
theorem encodeBindings_singleton (name : String) (value : Pattern) :
    encodeBindings [(name, value)] = cell (pair (encodeName name) (encodePattern value)) empty := rfl

/-- **Negative**: the bindings of two names are two data. -/
theorem encodeBindings_ne (value : Pattern) :
    encodeBindings [("x", value)] ≠ encodeBindings [("y", value)] := fun equal => by
  have names := encodeBindings_injective equal
  simp at names

/-! ## Constructors -/

/-- **A constructor of a program on the shared host**: no equation of the
program defines the head, and the host does not handle it.  Declared once for
a program and a head, it spares each proof the search through the
equations. -/
class Constructs (program : Program) (head : String) : Prop where
  undefined : program.defines head = false
  unhandled : ∀ arguments, sharedHost.primitive head arguments = .unhandled

/-- A constructor, applied, gives the application itself. -/
theorem Constructs.applies {program : Program} {head : String} [built : Constructs program head]
    (arguments : List Term) :
    Applies program sharedHost head arguments (.expr (.sym head :: arguments)) :=
  Applies.constructor built.undefined (built.unhandled arguments)

/-- **Positive**: the tag of cells is a constructor of the empty program. -/
theorem constructs_empty_cons : Constructs [] "Cons" := ⟨rfl, fun _ => rfl⟩

/-- **Negative**: a head with an equation is no constructor. -/
theorem not_constructs_of_defined :
    ¬ Constructs [⟨"cons", "Cons", [.var "head", .var "tail"], .var "tail"⟩] "Cons" := fun built => by
  have defined := built.undefined
  revert defined
  decide

/-- **Negative**: the equality primitive of the shared host is no constructor
of any program. -/
theorem not_constructs_comparison (program : Program) : ¬ Constructs program "nik:data-eq" :=
  fun built => by
    have handled := built.unhandled [.sym "a", .sym "a"]
    rw [dataEqualityHost_compare] at handled
    cases handled

/-! ## The two tactics -/

/-- Unfold a call by the equation that the program selects for it. -/
macro "by_equation" : tactic => `(tactic| refine Applies.equation (by rfl) (by rfl) ?_)

/-- Evaluate the body of an equation.  Variables, names, constructors and
comparisons are evaluated by themselves; each call of a head of the program is
closed by the tactic after `using`.

A goal is first told apart by its head, without unfolding: the application of
a head is tried against the declared constructors, the tactic after `using`,
the constructors found by search and the comparisons; the evaluation of a term
against the rules of evaluation.  The last alternatives are tried on every
goal that these leave, in one order. -/
syntax "engine " term (" using " tacticSeq)? : tactic

macro_rules
  | `(tactic| engine $keeps) => `(tactic| engine $keeps using fail)
  | `(tactic| engine $keeps using $calls) => `(tactic|
      repeat (first
        | (with_reducible (show Applies _ _ _ _ _)
           first
             | exact Constructs.applies _
             | $calls
             | exact Applies.constructor (by rfl) (by rfl)
             | exact encoded_comparison encodeName encodeName_injective _ _ (by rfl)
             | exact encoded_comparison natural natural_injective _ _ (by rfl)
             | exact encoded_comparison encodePattern encodePattern_injective _ _ (by rfl))
        | (with_reducible (show Evaluates _ _ _ _ _)
           first
             | exact Evaluates.variable (by rfl)
             | exact Evaluates.symbol _ _ _ _
             | exact Evaluates.literal _ _ _ _
             | exact encodeName_evaluates $keeps _ _
             | apply Evaluates.call)
        | exact List.Forall₂.nil
        | apply List.Forall₂.cons
        | (show ¬ Special _ _; simp [Special])
        | exact Evaluates.variable (by rfl)
        | exact Evaluates.symbol _ _ _ _
        | exact Evaluates.literal _ _ _ _
        | exact encodeName_evaluates $keeps _ _
        | $calls
        | apply Evaluates.call
        | exact Applies.constructor (by rfl) (by rfl)
        | exact encoded_comparison encodeName encodeName_injective _ _ (by rfl)
        | exact encoded_comparison natural natural_injective _ _ (by rfl)
        | exact encoded_comparison encodePattern encodePattern_injective _ _ (by rfl)))

#print axioms encodeBindings_injective

end Mettapedia.Logic.HostingStyles.AuthoredEvaluators

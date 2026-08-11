import Mettapedia.Logic.Prolog.Syntax

/-!
# Concrete source signature for Prolog text

This module instantiates the canonical `Logic.LP` representation with the
symbols and atomic values needed by a Prolog reader. Predicate and compound
symbols include their arity, matching SWI-Prolog's predicate-indicator and
functor discipline. Compounds have positive arity by construction; source
atoms and other zero-arity values use `Constant` instead.

Variables carry an occurrence identity in addition to their source spelling.
A reader can therefore share repeated named variables while assigning every
anonymous `_` occurrence a distinct identity before the ordinary LP
standardize-apart pass adds an activation scope.
-/

namespace Mettapedia.Logic.Prolog.SourceSignature

/-- Atomic Prolog data retained without passing through a host-language
number or string conversion. IEEE floats are stored by their 64-bit payload
so NaNs and signed zero remain distinguishable. -/
inductive Constant where
  | atom (name : String)
  | integer (value : Int)
  | floatBits (bits : UInt64)
  | string (value : String)
deriving DecidableEq, Repr

/-- Clause- or query-local source variable identity. -/
structure Variable where
  spelling : String
  occurrence : Nat
deriving DecidableEq, Repr

/-- Prolog predicates are identified by both name and arity. -/
structure PredicateIndicator where
  name : String
  arity : Nat
deriving DecidableEq, Repr

/-- A compound functor has positive arity. Zero-arity syntax is represented
by `Constant.atom`, so the two source forms cannot be confused. -/
structure CompoundIndicator where
  name : String
  arity : Nat
  positive : 0 < arity

@[ext]
theorem CompoundIndicator.ext
    {first second : CompoundIndicator}
    (name : first.name = second.name) (arity : first.arity = second.arity) :
    first = second := by
  cases first
  cases second
  simp_all

instance : DecidableEq CompoundIndicator := fun first second =>
  if hName : first.name = second.name then
    if hArity : first.arity = second.arity then
      isTrue (CompoundIndicator.ext hName hArity)
    else isFalse fun equal => hArity (congrArg CompoundIndicator.arity equal)
  else isFalse fun equal => hName (congrArg CompoundIndicator.name equal)

/-- The concrete signature consumed by the source reader and the same LP
runtime used by hand-constructed and verified programs. -/
@[reducible]
def signature : LP.LPSignature where
  constants := Constant
  vars := Variable
  relationSymbols := PredicateIndicator
  relationArity := PredicateIndicator.arity
  functionSymbols := CompoundIndicator
  functionArity := CompoundIndicator.arity

abbrev Term := LP.Term signature
abbrev Atom := LP.Atom signature
abbrev Goal := Prolog.Goal signature
abbrev Clause := Prolog.Clause signature
abbrev Program := Prolog.Program signature

def atom (name : String) : Term := .const (.atom name)
def integer (value : Int) : Term := .const (.integer value)
def floatBits (bits : UInt64) : Term := .const (.floatBits bits)
def string (value : String) : Term := .const (.string value)
def var (spelling : String) (occurrence : Nat) : Term :=
  .var { spelling, occurrence }

/-- Build a positive-arity compound from an already ordered, nonempty
argument list. Its arity index is the list length, so malformed compounds
cannot be constructed by the reader. -/
def compound (name : String) : (args : List Term) → args ≠ [] → Term
  | [], nonempty => nomatch nonempty rfl
  | first :: rest, _ =>
      .app {
        name
        arity := (first :: rest).length
        positive := by simp
      } (first :: rest).get

/-- Checked compound constructor used at the parser boundary. -/
def compound? (name : String) : List Term → Option Term
  | [] => none
  | first :: rest => some (compound name (first :: rest) (by simp))

/-- Build one relation atom with arity exactly equal to its ordered argument
list length. Name-equal predicates at different arities remain distinct. -/
def predicate (name : String) (args : List Term) : Atom := {
  symbol := { name, arity := args.length }
  args := args.get
}

def call (name : String) (args : List Term) : Goal :=
  .call (predicate name args)

/-- SWI-Prolog's canonical list functor is `[|]/2`; `[]` remains an atom. -/
def nil : Term := atom "[]"

def cons (head tail : Term) : Term :=
  compound "[|]" [head, tail] (by simp)

def list (elements : List Term) (tail : Term := nil) : Term :=
  elements.foldr cons tail

@[simp]
theorem compound?_nil (name : String) : compound? name [] = none := rfl

@[simp]
theorem compound?_cons (name : String) (first : Term) (rest : List Term) :
    compound? name (first :: rest) =
      some (compound name (first :: rest) (by simp)) := rfl

@[simp]
theorem predicate_arity (name : String) (args : List Term) :
    (predicate name args).symbol.arity = args.length := rfl

theorem predicate_same_name_different_arity
    (name : String) (left right : List Term)
    (different : left.length ≠ right.length) :
    (predicate name left).symbol ≠ (predicate name right).symbol := by
  intro equal
  exact different (congrArg PredicateIndicator.arity equal)

theorem anonymous_occurrences_distinct (first second : Nat)
    (different : first ≠ second) :
    ({ spelling := "_", occurrence := first } : Variable) ≠
      { spelling := "_", occurrence := second } := by
  intro equal
  exact different (congrArg Variable.occurrence equal)

end Mettapedia.Logic.Prolog.SourceSignature

import Mathlib.Data.List.Basic

/-!
# Options and operands: what `--` guarantees

A command line is a list of arguments. A program reads each one as an option, an
option with its argument, or an operand. POSIX Utility Syntax Guideline 10 makes
`--` the end of the options: every later argument is an operand, even one that
begins with `-`. Without it, text that a caller passes through from someone else
is read as an option whenever it begins with `-`.

The parser here is GNU-style: an option is recognized anywhere before `--`, as
GNU `getopt_long` and Go's urfave/cli do by default. POSIX itself stops at the
first operand, and that only removes cases, so the results below cover it too.
An option that takes an argument consumes the next argument as its value,
whatever that value looks like (Guideline 7).

The theorems:
- `parse_terminated`: after a complete prefix, `--` followed by any arguments
  parses as the prefix's items, the end of options, then exactly those
  arguments as operands.
- `operand_confined`: so an argument placed after `--` adds exactly the one
  operand it is, whatever its text.
- `parse_injects`: without `--`, an argument that begins with `-` is an option:
  `decrypt -p KEY --sec=bunker://…` sets `--sec`.

Scope. This is a contract for parsers of this kind, not a model of nak's parser
(urfave/cli) or of every command-line parser. The prefix must be complete: every
option in it has its value, so `--` is not taken as one. A shell keeps that true
by quoting: an empty, unquoted `$k` in `-p $k --` is no argument at all, and `-p`
takes the `--`; the client writes `-p "$k" --`.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Injection.Options

/-- An argument, as characters. -/
abbrev Arg := List Char

/-- `--`. -/
def terminator : Arg := ['-', '-']

/-- An option: two or more characters, the first a `-`. (A lone `-` is an
operand, conventionally standard input.) -/
def IsOption (a : Arg) : Prop := a.head? = some '-' ∧ 2 ≤ a.length

instance (a : Arg) : Decidable (IsOption a) := by unfold IsOption; infer_instance

/-- What the parser makes of the arguments. -/
inductive Item where
  | flag (name : Arg)
  | withValue (name value : Arg)
  | operand (value : Arg)
  | endOfOptions
  deriving DecidableEq, Repr

/-- GNU-style parsing. `takesValue` says which options consume the next argument. -/
def parse (takesValue : Arg → Bool) : List Arg → List Item
  | [] => []
  | a :: rest =>
    if a = terminator then .endOfOptions :: rest.map .operand
    else if IsOption a then
      if takesValue a then
        match rest with
        | v :: rest' => .withValue a v :: parse takesValue rest'
        | [] => [.flag a]
      else .flag a :: parse takesValue rest
    else .operand a :: parse takesValue rest

theorem parse_nil (takesValue : Arg → Bool) : parse takesValue [] = [] := rfl

/-- One step of the parser on a nonempty list. -/
theorem parse_cons (takesValue : Arg → Bool) (a : Arg) (rest : List Arg) :
    parse takesValue (a :: rest) =
      if a = terminator then .endOfOptions :: rest.map .operand
      else if IsOption a then
        if takesValue a then
          match rest with
          | v :: rest' => .withValue a v :: parse takesValue rest'
          | [] => [.flag a]
        else .flag a :: parse takesValue rest
      else .operand a :: parse takesValue rest := by
  cases rest <;> rfl

/-- A prefix the parser reads to its end without reaching past it: no `--`, and
no option left waiting for its value. -/
inductive Complete (takesValue : Arg → Bool) : List Arg → Prop where
  | nil : Complete takesValue []
  | operand {a : Arg} {rest : List Arg} (ht : a ≠ terminator) (ho : ¬ IsOption a)
      (h : Complete takesValue rest) : Complete takesValue (a :: rest)
  | flag {a : Arg} {rest : List Arg} (ht : a ≠ terminator) (ho : IsOption a)
      (hv : takesValue a = false) (h : Complete takesValue rest) :
      Complete takesValue (a :: rest)
  | withValue {a v : Arg} {rest : List Arg} (ht : a ≠ terminator) (ho : IsOption a)
      (hv : takesValue a = true) (h : Complete takesValue rest) :
      Complete takesValue (a :: v :: rest)

/-- **After `--`, operands only.** A complete prefix, then `--`, then any
arguments: the arguments are read as operands, exactly. -/
theorem parse_terminated {takesValue : Arg → Bool} {pre : List Arg}
    (hpre : Complete takesValue pre) (args : List Arg) :
    parse takesValue (pre ++ terminator :: args) =
      parse takesValue pre ++ .endOfOptions :: args.map .operand := by
  induction hpre with
  | nil => simp [parse_cons, parse_nil]
  | operand ht ho _ ih => simp only [List.cons_append, parse_cons]; simp [ht, ho, ih]
  | flag ht ho hv _ ih => simp only [List.cons_append, parse_cons]; simp [ht, ho, hv, ih]
  | withValue ht ho hv _ ih => simp only [List.cons_append, parse_cons]; simp [ht, ho, hv, ih]

/-- **Confinement.** An argument placed after `--` adds exactly one item, the
operand it is, whatever its text: it can name no option and consume nothing. -/
theorem operand_confined {takesValue : Arg → Bool} {pre : List Arg}
    (hpre : Complete takesValue pre) (x : Arg) :
    parse takesValue (pre ++ [terminator, x]) = parse takesValue pre ++ [.endOfOptions, .operand x] := by
  simpa using parse_terminated hpre [x]

/-! ## The bug: no `--` -/

/-- `decrypt`. -/
def wordDecrypt : Arg := ['d', 'e', 'c', 'r', 'y', 'p', 't']
/-- `-p`, which takes a value. -/
def optP : Arg := ['-', 'p']
/-- A key, as hex. -/
def key : Arg := ['a', 'b', 'c', 'd']
/-- `--sec=bunker://x`: a "ciphertext" that is an option. -/
def hostile : Arg := ['-', '-', 's', 'e', 'c', '=', 'b', 'u', 'n', 'k', 'e', 'r', ':', '/', '/', 'x']

/-- `nak`'s options here: `-p` takes a value. -/
def nakTakesValue (a : Arg) : Bool := a == optP

/-- Without `--`, the hostile text is read as an option. -/
theorem parse_injects :
    parse nakTakesValue [wordDecrypt, optP, key, hostile] =
      [.operand wordDecrypt, .withValue optP key, .flag hostile] := by
  decide

/-- With `--`, it is an operand. -/
theorem parse_terminated_hostile :
    parse nakTakesValue [wordDecrypt, optP, key, terminator, hostile] =
      [.operand wordDecrypt, .withValue optP key, .endOfOptions, .operand hostile] := by
  decide

end Mettapedia.Protocols.Injection.Options

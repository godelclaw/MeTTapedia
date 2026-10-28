import Mathlib.Logic.Function.Defs

/-!
# Python text at the PeTTa boundary

`py-call` turns the value a Python function returns into a MeTTa atom.  SWI-Prolog's
Janus interface maps a Python `str` to a Prolog atom by default (`py_string_as(atom)`),
as the PIP interface standard asks of Prologs that may have no string type.  SWI-PeTTa
calls Janus with that default, and in PeTTa a Prolog atom is a MeTTa symbol: Python
text arrives as a name.

This module models both conversions on a small fragment of the two value spaces and
proves what the symbol default costs a language in which a symbol is a name and a
string is data:

* it identifies distinct Python values: the text `"true"` and the boolean `True` arrive
  as the same atom, so nothing can decode a result back into what Python returned
  (`viaAtom_not_injective`, `viaAtom_no_decoding`);
* it forges names: the text `"name"` is the authored symbol `name`
  (`viaAtom_forges_symbols`);
* identity does not survive the boundary: the string `"a"`, handed to Python and back,
  is the symbol `a` (`viaAtom_roundtrip_fails`);
* the printed form loses the line between text and code: text that spells an
  expression prints exactly as that expression, its variable included
  (`viaAtom_text_prints_as_code`), and the empty text prints as nothing at all
  (`viaAtom_empty_prints_empty`).

The string conversion has none of these faults.  The export to Python inverts it
(`viaString_roundtrip`), so it is injective (`viaString_injective`); text never becomes
a symbol (`viaString_text_not_symbol`); and text prints quoted, so its printed form is
never that of an expression or a variable (`viaString_text_never_prints_as_code`).

The fragment is deliberately small.  Python values are text, booleans, integers and
`None`; atoms are symbols, strings, integers, variables and expressions, printed in
PeTTa's surface syntax.  PeTTa's `True` and `False` are the symbols `true` and `false`,
and `None` is the empty expression.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.PythonTextBoundary

/-- The Python values a `py-call` result is drawn from here. -/
inductive PyValue where
  | text (s : String)
  | bool (b : Bool)
  | int (n : Int)
  | none
  deriving DecidableEq, Repr

/-- The PeTTa atoms involved. -/
inductive Atom where
  | sym (name : String)
  | str (s : String)
  | int (n : Int)
  | var (name : String)
  | expr (items : List Atom)
  deriving Repr

/-- PeTTa's booleans are the symbols `true` and `false`. -/
def boolAtom : Bool → Atom
  | true => .sym "true"
  | false => .sym "false"

/-- Janus's default, `py_string_as(atom)`: Python text becomes a symbol. -/
def viaAtom : PyValue → Atom
  | .text s => .sym s
  | .bool b => boolAtom b
  | .int n => .int n
  | .none => .expr []

/-- Python text becomes MeTTa text. -/
def viaString : PyValue → Atom
  | .text s => .str s
  | .bool b => boolAtom b
  | .int n => .int n
  | .none => .expr []

/-- Handing an atom to Python: text and names become `str`, PeTTa's booleans become
`bool`.  Variables and nonempty expressions lie outside the fragment. -/
def toPython : Atom → Option PyValue
  | .str s => some (.text s)
  | .sym "true" => some (.bool true)
  | .sym "false" => some (.bool false)
  | .sym s => some (.text s)
  | .int n => some (.int n)
  | .expr [] => some .none
  | _ => none

/-- A character of quoted text: `"` and `\` are escaped. -/
def escapeChar : Char → List Char
  | '"' => ['\\', '"']
  | '\\' => ['\\', '\\']
  | c => [c]

mutual
/-- PeTTa's surface syntax for the fragment.  A symbol is its name as it stands; a
string is quoted. -/
def printAtom : Atom → List Char
  | .sym name => name.toList
  | .str s => '"' :: (s.toList.flatMap escapeChar ++ ['"'])
  | .int n => (toString n).toList
  | .var name => '$' :: name.toList
  | .expr items => '(' :: (printItems items ++ [')'])

/-- The items of an expression, separated by spaces. -/
def printItems : List Atom → List Char
  | [] => []
  | [a] => printAtom a
  | a :: b :: rest => printAtom a ++ ' ' :: printItems (b :: rest)
end

/-! ## What the symbol conversion costs -/

theorem viaAtom_collides : viaAtom (.text "true") = viaAtom (.bool true) := rfl

theorem viaAtom_not_injective : ¬ Function.Injective viaAtom := by
  intro injective
  cases injective viaAtom_collides

theorem viaAtom_no_decoding :
    ¬ ∃ decode : Atom → PyValue, ∀ v, decode (viaAtom v) = v := by
  rintro ⟨decode, inverse⟩
  have fromText := inverse (.text "true")
  have fromBool := inverse (.bool true)
  rw [viaAtom_collides, fromBool] at fromText
  cases fromText

theorem viaAtom_forges_symbols (name : String) : viaAtom (.text name) = .sym name := rfl

theorem viaAtom_roundtrip_fails : (toPython (.str "a")).map viaAtom ≠ some (.str "a") := by
  intro h
  simp [toPython, viaAtom] at h

theorem viaAtom_text_prints_as_code :
    printAtom (viaAtom (.text "(f $x)")) = printAtom (.expr [.sym "f", .var "x"]) := by
  simp only [viaAtom, printAtom, printItems]
  decide

theorem viaAtom_empty_prints_empty : printAtom (viaAtom (.text "")) = [] := by
  simp only [viaAtom, printAtom]
  decide

/-! ## The string conversion -/

theorem viaString_roundtrip (v : PyValue) : toPython (viaString v) = some v := by
  cases v with
  | text s => simp [viaString, toPython]
  | bool b => cases b <;> simp [viaString, boolAtom, toPython]
  | int n => simp [viaString, toPython]
  | none => simp [viaString, toPython]

theorem viaString_injective : Function.Injective viaString := by
  intro a b same
  have fromA := viaString_roundtrip a
  rw [same, viaString_roundtrip b] at fromA
  exact (Option.some.inj fromA).symm

theorem viaString_text_not_symbol (s name : String) : viaString (.text s) ≠ .sym name := by
  intro h
  cases h

theorem viaString_text_prints_quoted (s : String) :
    (printAtom (viaString (.text s))).head? = some '"' := by
  simp [viaString, printAtom]

theorem expr_prints_parenthesized (items : List Atom) :
    (printAtom (.expr items)).head? = some '(' := by
  simp [printAtom]

theorem var_prints_dollar (name : String) : (printAtom (.var name)).head? = some '$' := by
  simp [printAtom]

theorem viaString_text_never_prints_as_code (s : String) (items : List Atom) (name : String) :
    printAtom (viaString (.text s)) ≠ printAtom (.expr items) ∧
      printAtom (viaString (.text s)) ≠ printAtom (.var name) := by
  constructor
  · intro h
    have quoted := viaString_text_prints_quoted s
    rw [h, expr_prints_parenthesized] at quoted
    exact absurd quoted (by decide)
  · intro h
    have quoted := viaString_text_prints_quoted s
    rw [h, var_prints_dollar] at quoted
    exact absurd quoted (by decide)

end Mettapedia.Languages.MeTTa.PeTTa.PythonTextBoundary

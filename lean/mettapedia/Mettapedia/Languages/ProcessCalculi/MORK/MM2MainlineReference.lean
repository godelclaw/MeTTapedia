import Mettapedia.Languages.ProcessCalculi.MORK.MM2MainlineProviders

/-!
# Mainline MM2 in the kernel's text format, with reference primitives

`Mainline` leaves the kernel's foreign computation as parameters.  This module fixes them for
a fragment that a test corpus can exercise exactly, and adds the kernel's text format, so a
program can be run through the model and its final space compared with the kernel's
printed one.

* `parseProgram` reads the kernel's s-expression syntax: parentheses, `$name` variables,
  whitespace-separated symbols and `;` line comments.  Numbers are symbols, as in the
  kernel.
* `renderAtom` prints as the kernel does: within each atom, variables are named by first
  occurrence, `$a` … `$j`, then `$x10`, `$x11`, ….
* `referencePrimitives` fixes:
  - `pure`: `tuple`, `reverse_symbol`, `collapse_symbol`, `explode_symbol`,
    `i32_from_string`, `i32_to_string`, `sum_i32`, `product_i32` and `sub_i32`.  As in the
    kernel's evaluator, every argument is evaluated first, an expression must be a call of a
    registered function, and a variable is an error.  Between calls an `i32` value is kept as
    a grounded integer; the kernel keeps it as a four-byte symbol.
  - `U` and `AU`: most general unifier and least general generalization of the instances.
  - the aggregates: `sum` of decimal `u32` values, `and` of first characters, and the float
    reductions on dyadic decimals, printed as the kernel prints a double.  `hash` gives a
    placeholder naming the payload set; the kernel's sixteen hash bytes are not modelled.
* `runProgram` runs a program to quiescence, a fault, or the fuel bound, and prints the
  final space one atom per line, sorted.

The named fixtures at the end are kernel probes: each states the kernel's printed result for a
program, checked here against the model.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.Mainline.Reference

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Mainline

/-! ## Reading -/

/-- Tokens of the kernel's s-expression syntax. -/
inductive Token where
  | openParen
  | closeParen
  | word (text : String)
  deriving Repr, DecidableEq

/-- Close the word being read, if any. -/
def flushWord (word : List Char) (tokens : List Token) : List Token :=
  if word.isEmpty then tokens else .word (String.ofList word.reverse) :: tokens

/-- Split text into tokens, in reverse order.  `;` starts a comment that runs to the end of
the line; `inComment` records that one is open. -/
def tokenizeAux : List Char → Bool → List Char → List Token → List Token
  | [], _, word, tokens => flushWord word tokens
  | c :: rest, true, word, tokens =>
      tokenizeAux rest (c ≠ '\n') word tokens
  | c :: rest, false, word, tokens =>
      if c = ';' then tokenizeAux rest true [] (flushWord word tokens)
      else if c = '(' then tokenizeAux rest false [] (.openParen :: flushWord word tokens)
      else if c = ')' then tokenizeAux rest false [] (.closeParen :: flushWord word tokens)
      else if c.isWhitespace then tokenizeAux rest false [] (flushWord word tokens)
      else tokenizeAux rest false (c :: word) tokens

def tokenize (text : String) : List Token := (tokenizeAux text.toList false [] []).reverse

/-- A word is a variable when it starts with `$`, and a symbol otherwise. -/
def wordAtom (text : String) : Atom :=
  match text.toList with
  | '$' :: name => .var (String.ofList name)
  | _ => .symbol text

/-- Read tokens into top-level atoms with an explicit stack of open expressions. -/
def parseTokens : List Token → List (List Atom) → List Atom → Except String (List Atom)
  | [], [], top => .ok top.reverse
  | [], _ :: _, _ => .error "unclosed parenthesis"
  | .openParen :: rest, stack, top => parseTokens rest ([] :: stack) top
  | .closeParen :: _, [], _ => .error "unexpected closing parenthesis"
  | .closeParen :: rest, frame :: stack, top =>
      let atom := Atom.expression frame.reverse
      match stack with
      | [] => parseTokens rest [] (atom :: top)
      | parent :: more => parseTokens rest ((atom :: parent) :: more) top
  | .word text :: rest, stack, top =>
      match stack with
      | [] => parseTokens rest [] (wordAtom text :: top)
      | frame :: more => parseTokens rest ((wordAtom text :: frame) :: more) top

/-- A program: its atoms, as the kernel loads them into one space. -/
def parseProgram (text : String) : Except String (List Atom) :=
  (parseTokens (tokenize text) [] []).map fun atoms => atoms.foldl morkInsertSupport []

/-! ## Printing -/

/-- The kernel's name for the variable introduced at an index. -/
def variableSpelling (index : ℕ) : String :=
  if index < 10 then "$" ++ String.singleton (Char.ofNat (97 + index)) else "$x" ++ toString index

/-- A grounded value has no kernel spelling; it prints with a marker. -/
def groundedSpelling (value : GroundedValue) : String :=
  match value with
  | .int n => "#int:" ++ toString n
  | other => "#grounded:" ++ toString other

/-- Print an atom, naming variables by first occurrence. -/
def renderWith : List String → Atom → String × List String
  | seen, .var name =>
      match compactVariableIndex name seen with
      | some index => (variableSpelling index, seen)
      | none => (variableSpelling seen.length, seen ++ [name])
  | seen, .symbol name => (name, seen)
  | seen, .grounded value => (groundedSpelling value, seen)
  | seen, .expression children =>
      let printed := renderList seen children
      ("(" ++ " ".intercalate printed.1 ++ ")", printed.2)
where
  renderList : List String → List Atom → List String × List String
    | seen, [] => ([], seen)
    | seen, atom :: rest =>
        let first := renderWith seen atom
        let others := renderList first.2 rest
        (first.1 :: others.1, others.2)

def renderAtom (atom : Atom) : String := (renderWith [] atom).1

/-! ## Reference primitives -/

/-- Rust's `str::parse::<i32>`: an optional sign, then at least one digit, in range. -/
def parseI32 (text : String) : Option Int :=
  let (negative, digits) :=
    match text.toList with
    | '-' :: rest => (true, rest)
    | '+' :: rest => (false, rest)
    | rest => (false, rest)
  if digits.isEmpty || !digits.all Char.isDigit then none
  else
    let magnitude : Int := digits.foldl (fun value digit => value * 10 + (digit.toNat - 48)) 0
    let value := if negative then -magnitude else magnitude
    if -2147483648 ≤ value ∧ value ≤ 2147483647 then some value else none

/-- Wrapping `i32` arithmetic. -/
def wrapI32 (value : Int) : Int := (value + 2147483648) % 4294967296 - 2147483648

def i32Value : Atom → Option Int
  | .grounded (.int value) => some value
  | _ => none

/-- Concatenate the symbols of an expression, as `collapse_symbol` does (at most 63 bytes). -/
def collapseSymbols : List Atom → Option String
  | [] => some ""
  | .symbol part :: rest => (collapseSymbols rest).map (part ++ ·)
  | _ :: _ => none

/-- The registered functions of the reference fragment, on evaluated arguments. -/
def applyRegistered (name : String) (values : List Atom) : Option Atom :=
  match name, values with
  | "tuple", values => some (.expression values)
  | "reverse_symbol", [.symbol text] => some (.symbol (String.ofList text.toList.reverse))
  | "collapse_symbol", [.expression parts] =>
      (collapseSymbols parts).bind fun text =>
        if text.utf8ByteSize < 64 then some (.symbol text) else none
  | "explode_symbol", [.symbol text] =>
      some (.expression (text.toList.map fun c => .symbol (String.singleton c)))
  | "i32_from_string", [.symbol text] => (parseI32 text).map fun value => .grounded (.int value)
  | "i32_to_string", [value] => (i32Value value).map fun n => .symbol (toString n)
  | "sum_i32", values => (values.mapM i32Value).map fun ns => .grounded (.int (wrapI32 ns.sum))
  | "product_i32", values =>
      (values.mapM i32Value).map fun ns => .grounded (.int (wrapI32 (ns.foldl (· * ·) 1)))
  | "sub_i32", [left, right] =>
      (i32Value left).bind fun a => (i32Value right).map fun b => .grounded (.int (wrapI32 (a - b)))
  | _, _ => none

/-- Strict evaluation: symbols are values, an expression is a call of a registered function
on evaluated arguments, and anything else is an error.  (`quote` is not registered in the
kernel, so a call of it is an error too.) -/
def evalPure : Atom → Option Atom
  | .symbol name => some (.symbol name)
  | .expression (.symbol name :: arguments) =>
      (evalList arguments).bind (applyRegistered name)
  | _ => none
where
  evalList : List Atom → Option (List Atom)
    | [] => some []
    | argument :: rest =>
        (evalPure argument).bind fun value => (evalList rest).map (value :: ·)

/-- The most general unifier of a batch: every instance renamed apart and unified with the
first. -/
def unifyBatch (batch : List Atom) : Option Atom :=
  match (batch.zipIdx.map fun entry => renameApart ("#u" ++ toString entry.2 ++ "|") entry.1) with
  | [] => none
  | first :: others =>
      (unifyOption [] (others.map fun other => (first, other))).map fun θ => applySubst θ first

/-- One least general generalization, memoizing disagreement pairs; variables never agree. -/
def lggWith : List ((Atom × Atom) × ℕ) → Atom → Atom → Atom × List ((Atom × Atom) × ℕ)
  | memo, .symbol left, .symbol right =>
      if left = right then (.symbol left, memo) else disagree memo (.symbol left) (.symbol right)
  | memo, .expression lefts, .expression rights =>
      if lefts.length = rights.length then
        let general := lggList memo lefts rights
        (.expression general.1, general.2)
      else disagree memo (.expression lefts) (.expression rights)
  | memo, left, right => disagree memo left right
where
  disagree (memo : List ((Atom × Atom) × ℕ)) (left right : Atom) : Atom × List ((Atom × Atom) × ℕ) :=
    match memo.lookup (left, right) with
    | some index => (.var ("#g" ++ toString index), memo)
    | none => (.var ("#g" ++ toString memo.length), memo ++ [((left, right), memo.length)])
  lggList : List ((Atom × Atom) × ℕ) → List Atom → List Atom → List Atom × List ((Atom × Atom) × ℕ)
    | memo, left :: lefts, right :: rights =>
        let first := lggWith memo left right
        let others := lggList first.2 lefts rights
        (first.1 :: others.1, others.2)
    | memo, _, _ => ([], memo)

/-- The generalization of a batch: pairwise from the first, each step with a fresh memo, as
the kernel's `AU` sink does. -/
def antiUnifyBatch : List Atom → Option Atom
  | [] => none
  | first :: rest =>
      some (rest.foldl (fun general next =>
        (lggWith [] general (renameApart "#n|" next)).1) first)

/-- A decimal `u32`. -/
def parseU32 (text : String) : Option ℕ :=
  let digits := text.toList
  if digits.isEmpty || !digits.all Char.isDigit then none
  else
    let value := digits.foldl (fun value digit => value * 10 + (digit.toNat - 48)) 0
    if value < 4294967296 then some value else none

/-- A dyadic decimal `±digits[.digits]`, as a numerator over a power of two. -/
def parseDyadic (text : String) : Option (Int × ℕ) :=
  let (negative, rest) :=
    match text.toList with
    | '-' :: rest => (true, rest)
    | rest => (false, rest)
  let (whole, fraction) := (rest.takeWhile (· ≠ '.'), (rest.dropWhile (· ≠ '.')).drop 1)
  if whole.isEmpty || !whole.all Char.isDigit || !fraction.all Char.isDigit then none
  else
    let scale := 10 ^ fraction.length
    let numerator := (whole ++ fraction).foldl (fun value digit => value * 10 + (digit.toNat - 48)) 0
    -- `numerator / 10^k` is dyadic when `5^k` divides the numerator.
    let fives := 5 ^ fraction.length
    if numerator % fives = 0 then
      let value : Int := (numerator / fives : ℕ)
      some (if negative then -value else value, 2 ^ fraction.length)
    else if scale = 1 then some (if negative then -(numerator : Int) else numerator, 1)
    else none

/-- The exact decimal of `numerator / 2^k`, as a double prints: no exponent, no trailing
zeros, no point for an integer. -/
def renderDyadic (numerator : Int) (denominator : ℕ) : String :=
  let exponent := Nat.log2 denominator
  let scaled : ℕ := numerator.natAbs * 5 ^ exponent
  let whole := scaled / 10 ^ exponent
  let fraction := scaled % 10 ^ exponent
  let digits := (toString fraction).toList
  let padded := List.replicate (exponent - digits.length) '0' ++ digits
  let trimmed := (padded.reverse.dropWhile (· = '0')).reverse
  let sign := if numerator < 0 then "-" else ""
  if trimmed.isEmpty then sign ++ toString whole else sign ++ toString whole ++ "." ++ String.ofList trimmed

/-- Dyadic values over a common power-of-two denominator. -/
def commonDyadic (values : List (Int × ℕ)) : List Int × ℕ :=
  let denominator := values.foldl (fun bound value => max bound value.2) 1
  (values.map fun value => value.1 * ((denominator / value.2 : ℕ) : Int), denominator)

/-- Reduce a dyadic fraction. -/
def reduceDyadic : ℕ → Int → ℕ → Int × ℕ
  | 0, numerator, denominator => (numerator, denominator)
  | fuel + 1, numerator, denominator =>
      if denominator > 1 ∧ numerator % 2 = 0 then reduceDyadic fuel (numerator / 2) (denominator / 2)
      else (numerator, denominator)

def floatValue (kind : AggregateKind) (payloads : List Atom) : Option Atom := do
  let values ← payloads.mapM fun payload =>
    match payload with
    | .symbol text => parseDyadic text
    | _ => none
  match values with
  | [] => none
  | first :: rest =>
      let (numerators, denominator) := commonDyadic (first :: rest)
      let result : Int × ℕ :=
        match kind with
        | .fsum => (numerators.foldl (· + ·) 0, denominator)
        | .fmin => (numerators.foldl min (numerators.headD 0), denominator)
        | .fmax => (numerators.foldl max (numerators.headD 0), denominator)
        | .fprod =>
            (((first :: rest).map Prod.fst).foldl (· * ·) 1,
              ((first :: rest).map Prod.snd).foldl (· * ·) 1)
        | _ => (0, 1)
      let reduced := reduceDyadic 64 result.1 result.2
      pure (.symbol (renderDyadic reduced.1 reduced.2))

/-- The reference aggregates. -/
def referenceAggregate (kind : AggregateKind) (payloads : List Atom) : Option Atom :=
  match kind with
  | .count => some (.symbol (toString payloads.length))
  | .sum =>
      (payloads.mapM fun (payload : Atom) =>
        match payload with
        | .symbol text => parseU32 text
        | _ => none).map fun (values : List ℕ) => Atom.symbol (toString (values.sum % 4294967296))
  | .bitAnd =>
      (payloads.mapM fun (payload : Atom) =>
        match payload with
        | .symbol text => text.toList.head?.map Char.toNat
        | _ => none).bind fun (bytes : List ℕ) =>
          match bytes with
          | [] => none
          | first :: rest => some (.symbol (String.singleton (Char.ofNat (rest.foldl (· &&& ·) first))))
  | .hash => some (.symbol ("#hash:" ++ ",".intercalate (payloads.map renderAtom)))
  | kind => floatValue kind payloads

/-- The reference primitives. -/
def referencePrimitives : Primitives where
  eval := evalPure
  unify := unifyBatch
  antiUnify := antiUnifyBatch
  aggregate := referenceAggregate
  model := fun _ => []
  wasm := fun _ _ => none

/-! ## Running -/

/-- The constructor of a fault, as the comparison names it. -/
def faultName : MainlineFault → String
  | .unrecognizedSink _ => "unrecognizedSink"
  | .unrecognizedSource _ => "unrecognizedSource"
  | .missingFeature _ _ => "missingFeature"
  | .malformed _ => "malformed"
  | .unimplementedPureShape _ => "unimplementedPureShape"
  | .extremaDuplicate _ => "extremaDuplicate"
  | .antiUnifySingleRow _ => "antiUnifySingleRow"
  | .aggregateValue _ => "aggregateValue"
  | .misKeyedAggregate _ => "misKeyedAggregate"
  | .missingSolver _ => "missingSolver"
  | .missingFile _ => "missingFile"

/-- Sort printed atoms. -/
def sortLines (lines : List String) : List String :=
  lines.mergeSort fun left right => decide (left < right) || left == right

/-- Run a program with at most `fuel` steps from no files and no solvers.  The result is the
printed final space, `FAULT name` when the kernel would abort, or `FUEL` when executables
remain after `fuel` steps. -/
def runProgram (fuel : ℕ) (text : String) : String :=
  match parseProgram text with
  | .error message => "PARSE " ++ message
  | .ok atoms =>
      let (space, _, fault) := mainlineRun defaultProfile referencePrimitives fuel ExternalState.empty atoms
      match fault with
      | some fault => "FAULT " ++ faultName fault
      | none =>
          if (WQComputable.cRawExecFacts space).isEmpty then
            "\n".intercalate (sortLines (space.map renderAtom))
          else "FUEL"

/-! ## Kernel probes

Each fixture is a program run on the kernel binary at the pinned revision; the right-hand
side is the kernel's final space, compared by physical key (so up to variable names). -/

/-- Two spaces hold the same atoms, by physical key. -/
def sameSupport (left right : List Atom) : Bool :=
  left.all (morkSupportContains right) && right.all (morkSupportContains left)

/-- Run a program, as atoms, with the reference primitives from no files and no solvers. -/
def runAtoms (fuel : ℕ) (program : List Atom) : List Atom × Option MainlineFault :=
  let result := mainlineRun defaultProfile referencePrimitives fuel ExternalState.empty
    (program.foldl morkInsertSupport [])
  (result.1, result.2.2)

/-- The kernel reached `expected` without a fault. -/
def reaches (fuel : ℕ) (program expected : List Atom) : Bool :=
  let result := runAtoms fuel program
  result.2.isNone && sameSupport result.1 expected

abbrev sym (name : String) : Atom := Atom.symbol name
abbrev v (name : String) : Atom := Atom.var name
abbrev ex (children : List Atom) : Atom := Atom.expression children

/-- `(exec 0 INPUT OUTPUT)` at the symbol location `0`. -/
abbrev exec0 (input output : Atom) : Atom := ex [sym "exec", sym "0", input, output]

/-- A pattern constant meets a stored variable. -/
theorem probe_constant_meets_stored_variable :
    reaches 10 [ex [sym "foo", v "q"], exec0 (ex [sym ",", ex [sym "foo", sym "a"]]) (ex [sym ",", ex [sym "hit"]])]
      [ex [sym "foo", v "q"], ex [sym "hit"]] = true := by
  decide +kernel

/-- A stored repeated variable constrains the pattern. -/
theorem probe_stored_coreference :
    reaches 10 [ex [sym "foo", v "q", v "q"],
        exec0 (ex [sym ",", ex [sym "foo", sym "a", v "y"]]) (ex [sym ",", ex [sym "got", v "y"]])]
      [ex [sym "foo", v "q", v "q"], ex [sym "got", sym "a"]] = true := by
  decide +kernel

/-- The occurs check: `(foo $q (f $q))` does not unify with `(foo $x $x)`. -/
theorem probe_occurs_check :
    reaches 10 [ex [sym "foo", v "q", ex [sym "f", v "q"]],
        exec0 (ex [sym ",", ex [sym "foo", v "x", v "x"]]) (ex [sym ",", ex [sym "cyc", v "x"]])]
      [ex [sym "foo", v "q", ex [sym "f", v "q"]]] = true := by
  decide +kernel

/-- One stored atom read by two conjuncts is two independent copies. -/
theorem probe_renamed_apart :
    reaches 10 [ex [sym "p", v "q"],
        exec0 (ex [sym ",", ex [sym "p", sym "a"], ex [sym "p", sym "b"]]) (ex [sym ",", ex [sym "both"]])]
      [ex [sym "p", v "q"], ex [sym "both"]] = true := by
  decide +kernel

/-- `==` reads an independent copy of the stored atom. -/
theorem probe_eq_copy :
    reaches 10 [ex [sym "foo", v "q"],
        exec0 (ex [sym "I", ex [sym "==", ex [sym "foo", v "x"], ex [sym "foo", sym "a"]]])
          (ex [sym ",", ex [sym "eq1", v "x"]])]
      [ex [sym "foo", v "q"], ex [sym "eq1", v "x"]] = true := by
  decide +kernel

/-- The `!=` level defect: a repeated variable of the second atom names a variable of the first. -/
theorem probe_neq_levels :
    reaches 10 [ex [sym "p", v "a"], ex [sym "q", v "b", v "b"],
        exec0 (ex [sym "I", ex [sym "!=", ex [sym "p", v "x"], ex [sym "q", v "y", v "z"]]])
          (ex [sym ",", ex [sym "ne1", v "x", v "y", v "z"]])]
      [ex [sym "p", v "a"], ex [sym "q", v "b", v "b"], ex [sym "ne1", v "x", v "y", v "x"]] = true := by
  decide +kernel

/-- With a ground first atom the reading is correct. -/
theorem probe_neq_ground_first :
    reaches 10 [ex [sym "p", sym "c"], ex [sym "q", v "b", v "b"],
        exec0 (ex [sym "I", ex [sym "!=", ex [sym "p", v "x"], ex [sym "q", v "y", v "z"]]])
          (ex [sym ",", ex [sym "ne2", v "x", v "y", v "z"]])]
      [ex [sym "p", sym "c"], ex [sym "q", v "b", v "b"], ex [sym "ne2", sym "c", v "y", v "y"]] = true := by
  decide +kernel

/-- Adds are eager: a remove listed before an add of the same atom still removes it. -/
theorem probe_remove_then_add :
    reaches 10 [exec0 (ex [sym ","]) (ex [sym "O", ex [sym "-", ex [sym "x"]], ex [sym "+", ex [sym "x"]]])]
      [] = true := by
  decide +kernel

/-- The programmable-space conflict program leaves `a` in both sink orders. -/
theorem probe_edge_orders :
    reaches 10 [ex [sym "edge", sym "a", sym "b"], ex [sym "edge", sym "b", sym "c"],
        ex [sym "exec", ex [sym "0", sym "overlap"], ex [sym ",", ex [sym "edge", v "x", v "y"]],
          ex [sym "O", ex [sym "+", v "x"], ex [sym "-", v "y"]]]]
      [ex [sym "edge", sym "a", sym "b"], ex [sym "edge", sym "b", sym "c"], sym "a"] = true ∧
    reaches 10 [ex [sym "edge", sym "a", sym "b"], ex [sym "edge", sym "b", sym "c"],
        ex [sym "exec", ex [sym "0", sym "overlap"], ex [sym ",", ex [sym "edge", v "x", v "y"]],
          ex [sym "O", ex [sym "-", v "y"], ex [sym "+", v "x"]]]]
      [ex [sym "edge", sym "a", sym "b"], ex [sym "edge", sym "b", sym "c"], sym "a"] = true := by
  decide +kernel

/-- The numbering defect of an `(I …)` input with an `(O …)` output: after a sink that
introduces `$k`, the next sink numbers its first `$w` from the input's count again and its
second `$w` by the whole atom, so they become two variables. -/
theorem probe_io_numbering :
    reaches 10 [ex [sym "q", sym "b"],
        ex [sym "exec", sym "z", ex [sym "I", ex [sym "BTM", ex [sym "q", v "z"]]],
          ex [sym "O", ex [sym "count", ex [sym "cnt", v "k"], v "k", v "z"],
            ex [sym "+", ex [sym "t", v "w", v "w"]]]]]
      [ex [sym "q", sym "b"], ex [sym "cnt", sym "1"], ex [sym "t", v "a", v "b"]] = true := by
  decide +kernel

/-- With a comma input the count is carried, and both occurrences of `$w` are one variable. -/
theorem probe_comma_numbering :
    reaches 10 [ex [sym "q", sym "b"],
        ex [sym "exec", sym "z", ex [sym ",", ex [sym "q", v "z"]],
          ex [sym "O", ex [sym "count", ex [sym "cnt", v "k"], v "k", v "z"],
            ex [sym "+", ex [sym "t", v "w", v "w"]]]]]
      [ex [sym "q", sym "b"], ex [sym "cnt", sym "1"], ex [sym "t", v "a", v "a"]] = true := by
  decide +kernel

/-- Under an `(I …)` input a later sink's new variable takes the number of an earlier sink's:
`(+ (t $w)) (+ (s $w $v $v))` writes `(s $a $a $b)`. -/
theorem probe_io_collision :
    reaches 10 [ex [sym "q", sym "b"],
        ex [sym "exec", sym "z", ex [sym "I", ex [sym "BTM", ex [sym "q", v "z"]]],
          ex [sym "O", ex [sym "+", ex [sym "t", v "w"]], ex [sym "+", ex [sym "s", v "w", v "v", v "v"]]]]]
      [ex [sym "q", sym "b"], ex [sym "t", v "a"], ex [sym "s", v "a", v "a", v "b"]] = true := by
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.MORK.Mainline.Reference

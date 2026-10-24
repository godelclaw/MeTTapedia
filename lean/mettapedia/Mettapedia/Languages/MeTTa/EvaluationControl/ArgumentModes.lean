import Mettapedia.Languages.MeTTa.OSLFCore.Atom
import Mathlib.Data.Multiset.Bind

/-!
# Argument modes: which arguments evaluate, and the let-transparency law

A MeTTa operation either receives an argument as a value (the argument is
evaluated first) or holds it (the operation receives the syntax as written).
This module compares two ways of deciding that, in one small calculus.

* **Type-directed holding** (`runHE`), the rule of Hyperon Experimental: a
  parameter declared `Expression` or `Atom` holds its argument; the
  polymorphic parameter of `==` holds both arguments when one of them is a call
  whose declared result is `Expression`; a let-bound value standing in an
  evaluated position is read back as code and evaluated again; a call that
  reduced is evaluated again unless its declared result is `Atom`.
* **Positional value modes** (`runV`): every data-taking parameter is a value
  position; let-bound variables hold values that are never run again;
  `superpose` over a literal tuple chooses among the tuple's computations,
  and over any other argument enumerates the elements of its value; quotation
  produces the syntax as data and `eval` runs data as code.

## Results

* `he_traps`: under type-directed holding, naming an argument with `let`
  changes the answers of `superpose`, `foldl-atom`, `==`, `car-atom` and `+`.
  Each pair is what the HE-extended lane of CeTTa answers for the same program.
  `he_traps_cdr` gives three pairs in operations that upstream Hyperon
  Experimental defines, each as upstream answers it.
* `runHE_held`: at a held position the operation receives the argument's
  syntax, while the let-named form receives each of its answers;
  `he_eq_mode_depends_on_argument`: the mode of `==` depends on its arguments'
  form.
* `runV_letTransparent_op`, `runV_letTransparent_tuple`,
  `runV_letTransparent_superpose`, `runV_letTransparent_foldl`: under positional
  value modes, naming an argument of an operation, a constructor field, the
  argument of `superpose` (other than a literal tuple) or the list of
  `foldl-atom` with a fresh `let` leaves the answer bag unchanged, for every
  argument, environment and evaluator for data. `runV_eval_routes` is the case
  of `eval`.
* `choice_not_letTransparent`: in both disciplines of this module, choice among
  the computations of a literal tuple differs from enumeration of the tuple's
  values once the tuple is named.
* `print_parse`, `ev_eval_quote`, `ev_eval_requote`, `quote_raises_level`:
  printing after reading is the identity, `eval` after `quote` runs the source
  program, `eval` removes exactly one quotation level, and quoting changes the
  data.

## Fragment boundaries

Values are `OSLFCore.Atom`. The operations are a fixed table; there are no
user equations, so a symbol evaluates to itself and an expression whose head
is not an operation is a constructor application whose fields are evaluated.
Answers are lists read as bags; theorems that reorder independent choices are
stated on `Multiset`. Effects are not modelled. The type-directed discipline
models the parameter and result conventions of the listed operations, not
HE's general type checker.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.EvaluationControl.ArgumentModes

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-- Answers of a computation, in the order a depth-first run produces them. -/
abbrev Answers := List Atom

/-- Let-bound variables and the values they hold. -/
abbrev Env := List (String × Atom)

def num (n : Int) : Atom := .grounded (.int n)

def sym (s : String) : Atom := .symbol s

/-! ## Operations -/

/-- The operations of the fragment. -/
inductive Op where
  | carAtom
  | cdrAtom
  | consAtom
  | sizeAtom
  | sortAtom
  | rangeAtom
  | repeatAtom
  | members
  | plus
  | eq
  | eval
  deriving DecidableEq, Repr

namespace Op

/-- The operation's surface name. -/
def name : Op → String
  | .carAtom => "car-atom"
  | .cdrAtom => "cdr-atom"
  | .consAtom => "cons-atom"
  | .sizeAtom => "size-atom"
  | .sortAtom => "sort-atom"
  | .rangeAtom => "range-atom"
  | .repeatAtom => "repeat-atom"
  | .members => "members"
  | .plus => "+"
  | .eq => "=="
  | .eval => "eval"

/-- The operation named by a symbol, if any. -/
def ofName : String → Option Op
  | "car-atom" => some .carAtom
  | "cdr-atom" => some .cdrAtom
  | "cons-atom" => some .consAtom
  | "size-atom" => some .sizeAtom
  | "sort-atom" => some .sortAtom
  | "range-atom" => some .rangeAtom
  | "repeat-atom" => some .repeatAtom
  | "members" => some .members
  | "+" => some .plus
  | "==" => some .eq
  | "eval" => some .eval
  | _ => none

theorem name_of_ofName {s : String} {o : Op} (h : ofName s = some o) : o.name = s := by
  unfold ofName at h
  split at h <;> cases h <;> rfl

end Op

/-- Insertion of an atom into a list ordered by `lt`. -/
def insertBy (lt : Atom → Atom → Bool) (a : Atom) : List Atom → List Atom
  | [] => [a]
  | b :: bs => if lt a b then a :: b :: bs else b :: insertBy lt a bs

/-- Insertion sort by `lt`. -/
def sortBy (lt : Atom → Atom → Bool) : List Atom → List Atom
  | [] => []
  | a :: as => insertBy lt a (sortBy lt as)

/-- The order used by `sort-atom` in this fragment: symbols by spelling. -/
def symbolLt : Atom → Atom → Bool
  | .symbol s, .symbol t => decide (s < t)
  | _, _ => false

/-- The reduction of an operation on its argument values; `none` when the call
does not reduce (it then stands as a value: the call over its values). -/
def prim : Op → List Atom → Option Answers
  | .carAtom, [.expression (h :: _)] => some [h]
  | .cdrAtom, [.expression (_ :: t)] => some [.expression t]
  | .consAtom, [h, .expression t] => some [.expression (h :: t)]
  | .sizeAtom, [.expression xs] => some [num xs.length]
  | .sortAtom, [.expression xs] => some [.expression (sortBy symbolLt xs)]
  | .rangeAtom, [.grounded (.int n)] =>
      some [.expression ((List.range n.toNat).map fun k => num k)]
  | .repeatAtom, [.grounded (.int n), a] => some [.expression (List.replicate n.toNat a)]
  | .members, [.expression xs] => some xs
  | .plus, [.grounded (.int a), .grounded (.int b)] => some [num (a + b)]
  | .eq, [a, b] => some [if a = b then sym "True" else sym "False"]
  | _, _ => none

/-- A call that does not reduce: the operation over its argument values. -/
def stuck (o : Op) (vs : List Atom) : Atom := .expression (sym o.name :: vs)

/-! ## Code -/

/-- Elaborated MeTTa code. `superpose` and `foldl-atom` are kept as forms
because the disciplines give them different readings. -/
inductive Code where
  | lit (a : Atom)
  | var (x : String)
  | op (o : Op) (args : List Code)
  | tuple (items : List Code)
  | let_ (x : String) (bound body : Code)
  | quote (body : Code)
  | superpose (arg : Code)
  | foldl (list init : Code) (acc x : String) (body : Code)
  deriving Repr

mutual
/-- Code as data: the syntax as written. Quotation is sealed, so a variable
prints as itself. -/
def print : Code → Atom
  | .lit a => a
  | .var x => .var x
  | .op o args => .expression (sym o.name :: printList args)
  | .tuple items => .expression (printList items)
  | .let_ x e b => .expression [sym "let", .var x, print e, print b]
  | .quote b => .expression [sym "quote", print b]
  | .superpose a => .expression [sym "superpose", print a]
  | .foldl l i acc x b => .expression [sym "foldl-atom", print l, print i, .var acc, .var x, print b]

def printList : List Code → List Atom
  | [] => []
  | c :: cs => print c :: printList cs
end

mutual
/-- The syntax with let-bound variables replaced by their values: what a
substitution-based evaluator holds. -/
def printWith (env : Env) : Code → Atom
  | .lit a => a
  | .var x => (env.lookup x).getD (.var x)
  | .op o args => .expression (sym o.name :: printListWith env args)
  | .tuple items => .expression (printListWith env items)
  | .let_ x e b => .expression [sym "let", .var x, printWith env e, printWith env b]
  | .quote b => .expression [sym "quote", printWith env b]
  | .superpose a => .expression [sym "superpose", printWith env a]
  | .foldl l i acc x b =>
      .expression [sym "foldl-atom", printWith env l, printWith env i, .var acc, .var x, printWith env b]

def printListWith (env : Env) : List Code → List Atom
  | [] => []
  | c :: cs => printWith env c :: printListWith env cs
end

mutual
/-- Reading an atom as code: an expression headed by an operation's name is a
call; `let`, `quote`, `superpose` and `foldl-atom` are forms; every other
expression is a constructor application. -/
def parse : Atom → Code
  | .symbol s => .lit (.symbol s)
  | .grounded g => .lit (.grounded g)
  | .var x => .var x
  | .expression [.symbol "quote", b] => .quote (parse b)
  | .expression [.symbol "let", .var x, e, b] => .let_ x (parse e) (parse b)
  | .expression [.symbol "superpose", a] => .superpose (parse a)
  | .expression [.symbol "foldl-atom", l, i, .var acc, .var x, b] =>
      .foldl (parse l) (parse i) acc x (parse b)
  | .expression (.symbol s :: args) =>
      match Op.ofName s with
      | some o => .op o (parseList args)
      | none => .tuple (.lit (.symbol s) :: parseList args)
  | .expression items => .tuple (parseList items)

def parseList : List Atom → List Code
  | [] => []
  | a :: as => parse a :: parseList as
end

/-! ## Argument products -/

/-- Every combination of argument answers, left to right. -/
def product : List Answers → List (List Atom)
  | [] => [[]]
  | as :: rest => as.flatMap fun v => (product rest).map (v :: ·)

/-! ## Positional value modes -/

/-- Applying an operation to values. `eval` runs a value as code through
`run`; the other operations reduce or stand. -/
def applyV (run : Atom → Answers) : Op → List Atom → Answers
  | .eval, [v] => run v
  | o, vs => (prim o vs).getD [stuck o vs]

/-- One step of folding: every accumulator answer meets the next element. -/
def foldStep (body : Atom → Atom → Answers) (accs : Answers) (e : Atom) : Answers :=
  accs.flatMap fun a => body a e

mutual
/-- Evaluation under positional value modes. `run` evaluates data as code; it
is used only by `eval`. -/
def runV (run : Atom → Answers) : Code → Env → Answers
  | .lit a, _ => [a]
  | .var x, env => [(env.lookup x).getD (.var x)]
  | .op o args, env => (product (runArgsV run args env)).flatMap (applyV run o)
  | .tuple items, env => (product (runArgsV run items env)).map .expression
  | .let_ x e b, env => (runV run e env).flatMap fun v => runV run b ((x, v) :: env)
  | .quote b, _ => [print b]
  | .superpose a, env =>
      match a with
      | .tuple items => (runArgsV run items env).flatten
      | a' => (runV run a' env).flatMap fun v => applyV run .members [v]
  | .foldl l i acc x b, env =>
      (runV run l env).flatMap fun lv =>
        (runV run i env).flatMap fun iv =>
          match lv with
          | .expression xs =>
              xs.foldl (foldStep fun a e => runV run b ((acc, a) :: (x, e) :: env)) [iv]
          | other => [.expression [sym "foldl-atom", other, iv]]

def runArgsV (run : Atom → Answers) : List Code → Env → List Answers
  | [], _ => []
  | c :: cs, env => runV run c env :: runArgsV run cs env
end

/-- Evaluation with `n` levels of running data as code. -/
def ev : Nat → Code → Env → Answers
  | 0 => runV fun _ => []
  | n + 1 => runV fun a => ev n (parse a) []

/-- A source program, read and evaluated with `n` levels. -/
def evSrc (n : Nat) (a : Atom) : Answers := ev n (parse a) []

/-! ## Type-directed holding -/

/-- Calls whose declared result type is the meta-type `Expression`. -/
def returnsExpression : Code → Bool
  | .op .cdrAtom _ => true
  | .op .sortAtom _ => true
  | _ => false

/-- Whether a parameter holds its argument. The declared types are
`car-atom`, `cdr-atom`, `size-atom`, `sort-atom` : `(-> Expression _)`;
`cons-atom` : `(-> Atom Expression Atom)`; `eval` : `(-> Atom Atom)`;
`==` : `(-> $t $t Bool)`, whose type variable becomes `Expression` when an
argument is a call declared to return `Expression`. -/
def heHolds : Op → List Code → Nat → Bool
  | .carAtom, _, 0 => true
  | .cdrAtom, _, 0 => true
  | .sizeAtom, _, 0 => true
  | .sortAtom, _, 0 => true
  | .consAtom, _, _ => true
  | .eval, _, _ => true
  | .eq, args, _ => args.any returnsExpression
  | _, _, _ => false

/-- Whether a reduced call's result is evaluated again: every result except
those declared `Atom` (`car-atom`, `cons-atom`, `eval`). -/
def heReevaluates : Op → Bool
  | .carAtom => false
  | .consAtom => false
  | .eval => false
  | _ => true

/-- Applying an operation under type-directed holding. -/
def applyHE (run : Atom → Answers) (o : Op) (vs : List Atom) : Answers :=
  match o, vs with
  | .eval, [v] => run v
  | _, _ =>
      match prim o vs with
      | none => [stuck o vs]
      | some r => if heReevaluates o then r.flatMap run else r

mutual
/-- Evaluation under type-directed holding. `run` evaluates an atom as code;
it reads back let-bound values standing in evaluated positions, the parts
that `superpose` and `foldl-atom` take from held syntax, and reduced
results. -/
def runHE (run : Atom → Answers) : Code → Env → Answers
  | .lit a, _ => [a]
  | .var x, env =>
      match env.lookup x with
      | some v => run v
      | none => [.var x]
  | .op o args, env => (product (runArgsHE run o args args 0 env)).flatMap (applyHE run o)
  | .tuple items, env => (product (runListHE run items env)).map .expression
  | .let_ x e b, env => (runHE run e env).flatMap fun v => runHE run b ((x, v) :: env)
  | .quote b, env => [.expression [sym "quote", printWith env b]]
  | .superpose a, env =>
      match printWith env a with
      | .expression parts => parts.flatMap run
      | s => run s
  | .foldl l i acc x b, env =>
      (runHE run i env).flatMap fun iv =>
        match printWith env l with
        | .expression xs =>
            xs.foldl (foldStep fun a e => runHE run b ((acc, a) :: (x, e) :: env)) [iv]
        | other => [.expression [sym "foldl-atom", other, iv]]

def runArgsHE (run : Atom → Answers) (o : Op) (all : List Code) :
    List Code → Nat → Env → List Answers
  | [], _, _ => []
  | c :: cs, i, env =>
      (if heHolds o all i then [printWith env c] else runHE run c env) ::
        runArgsHE run o all cs (i + 1) env

def runListHE (run : Atom → Answers) : List Code → Env → List Answers
  | [], _ => []
  | c :: cs, env => runHE run c env :: runListHE run cs env
end

/-- Type-directed evaluation with `n` levels of reading back. -/
def evHE : Nat → Code → Env → Answers
  | 0 => runHE fun _ => []
  | n + 1 => runHE fun a => evHE n (parse a) []

/-- A source program under type-directed holding. -/
def evHESrc (n : Nat) (a : Atom) : Answers := evHE n (parse a) []

/-! ## The canonical programs -/

namespace Programs

def V (x : String) : Atom := .var x
def E (xs : List Atom) : Atom := .expression xs

/-- `(superpose (repeat-atom 3 a))` and its let-named form. -/
def superposeCall : Atom := E [sym "superpose", E [sym "repeat-atom", num 3, sym "a"]]
def superposeNamed : Atom :=
  E [sym "let", V "l", E [sym "repeat-atom", num 3, sym "a"], E [sym "superpose", V "l"]]

/-- `(foldl-atom (range-atom 4) 0 $acc $x (+ $acc $x))` and its let-named form. -/
def foldCall : Atom :=
  E [sym "foldl-atom", E [sym "range-atom", num 4], num 0, V "acc", V "x",
    E [sym "+", V "acc", V "x"]]
def foldNamed : Atom :=
  E [sym "let", V "l", E [sym "range-atom", num 4],
    E [sym "foldl-atom", V "l", num 0, V "acc", V "x", E [sym "+", V "acc", V "x"]]]

/-- `(== (sort-atom (b a)) (sort-atom (a b)))` and its let-named form. -/
def eqCall : Atom :=
  E [sym "==", E [sym "sort-atom", E [sym "b", sym "a"]], E [sym "sort-atom", E [sym "a", sym "b"]]]
def eqNamed : Atom :=
  E [sym "let", V "p", E [sym "sort-atom", E [sym "b", sym "a"]],
    E [sym "let", V "q", E [sym "sort-atom", E [sym "a", sym "b"]], E [sym "==", V "p", V "q"]]]

/-- `(car-atom (range-atom 3))` and its let-named form. -/
def carCall : Atom := E [sym "car-atom", E [sym "range-atom", num 3]]
def carNamed : Atom :=
  E [sym "let", V "l", E [sym "range-atom", num 3], E [sym "car-atom", V "l"]]

/-- `(+ (cons-atom + (1 2)) 1)` and `(let $x (cons-atom + (1 2)) (+ $x 1))`. -/
def plusCall : Atom := E [sym "+", E [sym "cons-atom", sym "+", E [num 1, num 2]], num 1]
def plusNamed : Atom :=
  E [sym "let", V "x", E [sym "cons-atom", sym "+", E [num 1, num 2]], E [sym "+", V "x", num 1]]

/-- `(superpose ((superpose (1 2)) 3))` and its let-named form. -/
def chooseCall : Atom :=
  E [sym "superpose", E [E [sym "superpose", E [num 1, num 2]], num 3]]
def chooseNamed : Atom :=
  E [sym "let", V "t", E [E [sym "superpose", E [num 1, num 2]], num 3],
    E [sym "superpose", V "t"]]

/-- `(eval (cons-atom + (1 2)))` and its let-named form. -/
def evalCall : Atom := E [sym "eval", E [sym "cons-atom", sym "+", E [num 1, num 2]]]
def evalNamed : Atom :=
  E [sym "let", V "x", E [sym "cons-atom", sym "+", E [num 1, num 2]], E [sym "eval", V "x"]]

/-- Three pairs in operations that upstream Hyperon Experimental defines. -/
def eqCdrCall : Atom :=
  E [sym "==", E [sym "cdr-atom", E [sym "x", sym "a"]], E [sym "cdr-atom", E [sym "y", sym "a"]]]
def eqCdrNamed : Atom :=
  E [sym "let", V "p", E [sym "cdr-atom", E [sym "x", sym "a"]],
    E [sym "let", V "q", E [sym "cdr-atom", E [sym "y", sym "a"]], E [sym "==", V "p", V "q"]]]
def carCdrCall : Atom := E [sym "car-atom", E [sym "cdr-atom", E [sym "a", sym "b", sym "c"]]]
def carCdrNamed : Atom :=
  E [sym "let", V "t", E [sym "cdr-atom", E [sym "a", sym "b", sym "c"]], E [sym "car-atom", V "t"]]
def superposeCdrCall : Atom :=
  E [sym "superpose", E [sym "cdr-atom", E [sym "a", sym "b", sym "c"]]]
def superposeCdrNamed : Atom :=
  E [sym "let", V "t", E [sym "cdr-atom", E [sym "a", sym "b", sym "c"]], E [sym "superpose", V "t"]]

end Programs

open Programs

/-! ## Type-directed holding: the five traps -/

theorem he_superpose : evHESrc 8 superposeCall = [sym "repeat-atom", num 3, sym "a"] ∧
    evHESrc 8 superposeNamed = [sym "a", sym "a", sym "a"] := by
  decide

theorem he_foldl : evHESrc 8 foldCall =
      [E [sym "+", E [sym "+", num 0, sym "range-atom"], num 4]] ∧
    evHESrc 8 foldNamed = [num 6] := by
  decide

theorem he_eq : evHESrc 8 eqCall = [sym "False"] ∧ evHESrc 8 eqNamed = [sym "True"] := by
  decide

theorem he_car : evHESrc 8 carCall = [sym "range-atom"] ∧ evHESrc 8 carNamed = [num 0] := by
  decide

theorem he_plus : evHESrc 8 plusCall = [E [sym "+", E [sym "+", num 1, num 2], num 1]] ∧
    evHESrc 8 plusNamed = [num 4] := by
  decide

/-- Under type-directed holding, naming an argument with `let` changes the
answers of `superpose`, `foldl-atom`, `==`, `car-atom` and `+`. -/
theorem he_traps :
    evHESrc 8 superposeCall ≠ evHESrc 8 superposeNamed ∧
    evHESrc 8 foldCall ≠ evHESrc 8 foldNamed ∧
    evHESrc 8 eqCall ≠ evHESrc 8 eqNamed ∧
    evHESrc 8 carCall ≠ evHESrc 8 carNamed ∧
    evHESrc 8 plusCall ≠ evHESrc 8 plusNamed := by
  decide

/-- The same traps in operations upstream Hyperon Experimental defines; each
pair is the answer upstream gives. -/
theorem he_traps_cdr :
    evHESrc 8 eqCdrCall = [sym "False"] ∧ evHESrc 8 eqCdrNamed = [sym "True"] ∧
    evHESrc 8 carCdrCall = [sym "cdr-atom"] ∧ evHESrc 8 carCdrNamed = [sym "b"] ∧
    evHESrc 8 superposeCdrCall = [sym "cdr-atom", E [sym "a", sym "b", sym "c"]] ∧
    evHESrc 8 superposeCdrNamed = [sym "b", sym "c"] := by
  decide

/-- Under positional value modes the three pairs agree. -/
theorem value_cdr :
    evSrc 8 eqCdrCall = [sym "True"] ∧ evSrc 8 eqCdrNamed = [sym "True"] ∧
    evSrc 8 carCdrCall = [sym "b"] ∧ evSrc 8 carCdrNamed = [sym "b"] ∧
    evSrc 8 superposeCdrCall = [sym "b", sym "c"] ∧
    evSrc 8 superposeCdrNamed = [sym "b", sym "c"] := by
  decide

/-! ## Positional value modes: the same programs -/

theorem value_superpose :
    evSrc 8 superposeCall = [sym "a", sym "a", sym "a"] ∧
    evSrc 8 superposeNamed = [sym "a", sym "a", sym "a"] := by
  decide

theorem value_foldl : evSrc 8 foldCall = [num 6] ∧ evSrc 8 foldNamed = [num 6] := by
  decide

theorem value_eq : evSrc 8 eqCall = [sym "True"] ∧ evSrc 8 eqNamed = [sym "True"] := by
  decide

theorem value_car : evSrc 8 carCall = [num 0] ∧ evSrc 8 carNamed = [num 0] := by
  decide

/-- A value is never run again: the constructed `(+ 1 2)` stays data in
both forms. -/
theorem value_plus :
    evSrc 8 plusCall = [E [sym "+", E [sym "+", num 1, num 2], num 1]] ∧
    evSrc 8 plusNamed = [E [sym "+", E [sym "+", num 1, num 2], num 1]] := by
  decide

/-- `eval` runs data as code on both routes. -/
theorem value_eval : evSrc 8 evalCall = [num 3] ∧ evSrc 8 evalNamed = [num 3] := by
  decide

/-! ## Choice is a control form; enumeration is a function -/

/-- `superpose` over a literal tuple chooses among the tuple's computations;
after naming, it enumerates the elements of each tuple value. The answers
differ as bags: `3` occurs once, then twice. -/
theorem choice_not_letTransparent :
    evSrc 8 chooseCall = [num 1, num 2, num 3] ∧
    evSrc 8 chooseNamed = [num 1, num 3, num 2, num 3] ∧
    evHESrc 8 chooseCall = [num 1, num 2, num 3] ∧
    evHESrc 8 chooseNamed = [num 1, num 3, num 2, num 3] := by
  decide


/-! ## Free variables and environment congruence -/

mutual
/-- Variables an evaluation reads from its environment. Quotation is sealed. -/
def fv : Code → List String
  | .lit _ => []
  | .var x => [x]
  | .op _ args => fvList args
  | .tuple items => fvList items
  | .let_ x e b => fv e ++ (fv b).filter (· != x)
  | .quote _ => []
  | .superpose a => fv a
  | .foldl l i acc x b => fv l ++ fv i ++ (fv b).filter (fun y => y != acc && y != x)

def fvList : List Code → List String
  | [] => []
  | c :: cs => fv c ++ fvList cs
end

/-- Two environments agree on a list of names. -/
def Agree (names : List String) (env₁ env₂ : Env) : Prop :=
  ∀ y ∈ names, env₁.lookup y = env₂.lookup y

theorem lookup_self (x : String) (v : Atom) (env : Env) : ((x, v) :: env).lookup x = some v := by
  simp [List.lookup]

theorem lookup_ne {x y : String} (h : y ≠ x) (v : Atom) (env : Env) :
    ((x, v) :: env).lookup y = env.lookup y := by
  have hb : (y == x) = false := by simp [h]
  simp [List.lookup, hb]

/-- Pushing the same binding onto agreeing environments keeps agreement. -/
theorem agree_cons {names : List String} {env₁ env₂ : Env} (k : String) (v : Atom)
    (h : ∀ y ∈ names, y ≠ k → env₁.lookup y = env₂.lookup y) :
    Agree names ((k, v) :: env₁) ((k, v) :: env₂) := by
  intro y hy
  by_cases hyk : y = k
  · subst hyk; simp
  · rw [lookup_ne hyk, lookup_ne hyk]; exact h y hy hyk

/-- `superpose` of anything but a literal tuple enumerates the elements of
its argument's values. -/
theorem runV_superpose_value (run : Atom → Answers) (a : Code) (env : Env)
    (ha : ∀ items, a ≠ .tuple items) :
    runV run (.superpose a) env = (runV run a env).flatMap fun v => applyV run .members [v] := by
  cases a with
  | tuple items => exact absurd rfl (ha items)
  | _ => rfl

mutual
/-- Evaluation reads only the free variables of the code. -/
theorem runV_congr (run : Atom → Answers) :
    ∀ (c : Code) (env₁ env₂ : Env), Agree (fv c) env₁ env₂ → runV run c env₁ = runV run c env₂
  | .lit _, _, _, _ => rfl
  | .var x, env₁, env₂, h => by
      simp only [runV]
      rw [h x (by simp [fv])]
  | .op o args, env₁, env₂, h => by
      simp only [runV]
      rw [runArgsV_congr run args env₁ env₂ (by simpa [fv] using h)]
  | .tuple items, env₁, env₂, h => by
      simp only [runV]
      rw [runArgsV_congr run items env₁ env₂ (by simpa [fv] using h)]
  | .let_ x e b, env₁, env₂, h => by
      simp only [runV]
      rw [runV_congr run e env₁ env₂ (fun y hy => h y (by simp [fv, hy]))]
      congr 1
      funext v
      apply runV_congr run b
      apply agree_cons
      intro y hy hyx
      exact h y (by simp [fv, hy, hyx])
  | .quote _, _, _, _ => rfl
  | .superpose (.tuple items), env₁, env₂, h => by
      simp only [runV]
      rw [runArgsV_congr run items env₁ env₂ (by simpa [fv] using h)]
  | .superpose (.lit _), _, _, _ => rfl
  | .superpose (.var y), env₁, env₂, h => by
      simp only [runV]
      rw [h y (by simp [fv])]
  | .superpose (.op o args), env₁, env₂, h => by
      rw [runV_superpose_value run _ env₁ (by intro _ h; cases h),
        runV_superpose_value run _ env₂ (by intro _ h; cases h),
        runV_congr run (.op o args) env₁ env₂ (by simpa [fv] using h)]
  | .superpose (.let_ y e b), env₁, env₂, h => by
      rw [runV_superpose_value run _ env₁ (by intro _ h; cases h),
        runV_superpose_value run _ env₂ (by intro _ h; cases h),
        runV_congr run (.let_ y e b) env₁ env₂ (by simpa [fv] using h)]
  | .superpose (.quote _), _, _, _ => rfl
  | .superpose (.superpose a), env₁, env₂, h => by
      rw [runV_superpose_value run _ env₁ (by intro _ h; cases h),
        runV_superpose_value run _ env₂ (by intro _ h; cases h),
        runV_congr run (.superpose a) env₁ env₂ (by simpa [fv] using h)]
  | .superpose (.foldl l i acc x b), env₁, env₂, h => by
      rw [runV_superpose_value run _ env₁ (by intro _ h; cases h),
        runV_superpose_value run _ env₂ (by intro _ h; cases h),
        runV_congr run (.foldl l i acc x b) env₁ env₂ (by simpa [fv] using h)]
  | .foldl l i acc x b, env₁, env₂, h => by
      simp only [runV]
      rw [runV_congr run l env₁ env₂ (fun y hy => h y (by simp [fv, hy])),
        runV_congr run i env₁ env₂ (fun y hy => h y (by simp [fv, hy]))]
      have hb : (fun a e => runV run b ((acc, a) :: (x, e) :: env₁)) =
          (fun a e => runV run b ((acc, a) :: (x, e) :: env₂)) := by
        funext a e
        apply runV_congr run b
        apply agree_cons
        intro y hy hya
        by_cases hyx : y = x
        · subst hyx; simp
        · rw [lookup_ne hyx, lookup_ne hyx]
          exact h y (by simp [fv, hy, hya, hyx])
      rw [hb]

theorem runArgsV_congr (run : Atom → Answers) :
    ∀ (cs : List Code) (env₁ env₂ : Env), Agree (fvList cs) env₁ env₂ →
      runArgsV run cs env₁ = runArgsV run cs env₂
  | [], _, _, _ => rfl
  | c :: cs, env₁, env₂, h => by
      simp only [runArgsV]
      rw [runV_congr run c env₁ env₂ (fun y hy => h y (by simp [fvList, hy])),
        runArgsV_congr run cs env₁ env₂ (fun y hy => h y (by simp [fvList, hy]))]
end

/-- A binding of a name the code does not read changes nothing. -/
theorem runV_cons_irrelevant (run : Atom → Answers) {c : Code} {x : String} (hx : x ∉ fv c)
    (v : Atom) (env : Env) : runV run c ((x, v) :: env) = runV run c env := by
  apply runV_congr
  intro y hy
  have hyx : y ≠ x := fun e => hx (e ▸ hy)
  exact lookup_ne hyx v env

theorem runArgsV_cons_irrelevant (run : Atom → Answers) {cs : List Code} {x : String}
    (hx : x ∉ fvList cs) (v : Atom) (env : Env) :
    runArgsV run cs ((x, v) :: env) = runArgsV run cs env := by
  apply runArgsV_congr
  intro y hy
  have hyx : y ≠ x := fun e => hx (e ▸ hy)
  exact lookup_ne hyx v env

theorem runArgsV_append (run : Atom → Answers) (pre post : List Code) (env : Env) :
    runArgsV run (pre ++ post) env = runArgsV run pre env ++ runArgsV run post env := by
  induction pre with
  | nil => rfl
  | cons c cs ih => simp [runArgsV, ih]

/-! ## Products of answer bags -/

theorem coe_flatMap_flatMap {α β γ : Type} (l : List α) (g : α → List β) (f : β → List γ) :
    (↑((l.flatMap g).flatMap f) : Multiset γ) = (↑l : Multiset α).bind fun a => ↑((g a).flatMap f) := by
  rw [List.flatMap_assoc, Multiset.coe_bind]

/-- Choosing one argument's answer first and the others after gives the same
bag as choosing left to right. -/
theorem product_middle (As Cs : List Answers) (B : Answers) (f : List Atom → Answers) :
    (↑((product (As ++ B :: Cs)).flatMap f) : Multiset Atom) =
      (↑B : Multiset Atom).bind fun b => ↑((product (As ++ [b] :: Cs)).flatMap f) := by
  induction As generalizing f with
  | nil =>
      simp only [List.nil_append, product]
      rw [coe_flatMap_flatMap]
      congr 1
      funext b
      simp
  | cons A As ih =>
      simp only [List.cons_append, product]
      rw [coe_flatMap_flatMap]
      simp only [List.flatMap_map]
      have step : ∀ a : Atom, (↑((product (As ++ B :: Cs)).flatMap fun x => f (a :: x)) : Multiset Atom) =
          (↑B : Multiset Atom).bind fun b => ↑((product (As ++ [b] :: Cs)).flatMap fun x => f (a :: x)) :=
        fun a => ih (fun x => f (a :: x))
      simp only [step]
      rw [Multiset.bind_bind]
      congr 1
      funext b
      rw [coe_flatMap_flatMap]
      simp only [List.flatMap_map]

/-! ## Positional value modes are let-transparent -/

/-- Naming any argument of any operation with `let` leaves the answer bag
unchanged, when the name is fresh for the other arguments. -/
theorem runV_letTransparent_op (run : Atom → Answers) (o : Op) (pre post : List Code)
    (E : Code) (x : String) (env : Env) (hpre : x ∉ fvList pre) (hpost : x ∉ fvList post) :
    (↑(runV run (.op o (pre ++ E :: post)) env) : Multiset Atom) =
      ↑(runV run (.let_ x E (.op o (pre ++ .var x :: post))) env) := by
  simp only [runV, runArgsV_append, runArgsV]
  rw [product_middle, ← Multiset.coe_bind]
  congr 1
  funext v
  rw [runArgsV_cons_irrelevant run hpre, runArgsV_cons_irrelevant run hpost, lookup_self]
  rfl

/-- The same law for constructor fields. -/
theorem runV_letTransparent_tuple (run : Atom → Answers) (pre post : List Code)
    (E : Code) (x : String) (env : Env) (hpre : x ∉ fvList pre) (hpost : x ∉ fvList post) :
    (↑(runV run (.tuple (pre ++ E :: post)) env) : Multiset Atom) =
      ↑(runV run (.let_ x E (.tuple (pre ++ .var x :: post))) env) := by
  simp only [runV, runArgsV_append, runArgsV]
  rw [List.map_eq_flatMap, product_middle, ← Multiset.coe_bind]
  congr 1
  funext v
  rw [runArgsV_cons_irrelevant run hpre, runArgsV_cons_irrelevant run hpost, lookup_self,
    List.map_eq_flatMap]
  rfl

/-- Enumeration of a value's elements is let-transparent: `superpose` of any
argument other than a literal tuple. -/
theorem runV_letTransparent_superpose (run : Atom → Answers) (E : Code) (x : String) (env : Env)
    (hE : ∀ items, E ≠ .tuple items) :
    runV run (.superpose E) env = runV run (.let_ x E (.superpose (.var x))) env := by
  cases E with
  | tuple items => exact absurd rfl (hE items)
  | _ => simp [runV]

/-- `foldl-atom`'s list is a value position: naming it changes nothing. -/
theorem runV_letTransparent_foldl (run : Atom → Answers) (E i b : Code) (acc y x : String)
    (env : Env) (hi : x ∉ fv i) (hb : x ∉ fv b) :
    runV run (.foldl E i acc y b) env = runV run (.let_ x E (.foldl (.var x) i acc y b)) env := by
  have body : ∀ (v a e : Atom), runV run b ((acc, a) :: (y, e) :: (x, v) :: env) =
      runV run b ((acc, a) :: (y, e) :: env) := by
    intro v a e
    apply runV_congr
    intro z hz
    have hzx : z ≠ x := fun h => hb (h ▸ hz)
    by_cases hza : z = acc
    · subst hza; simp
    · rw [lookup_ne hza, lookup_ne hza]
      by_cases hzy : z = y
      · subst hzy; simp
      · rw [lookup_ne hzy, lookup_ne hzy, lookup_ne hzx]
  simp only [runV, lookup_self, Option.getD_some, List.flatMap_singleton,
    runV_cons_irrelevant run hi, body]

/-- `eval` agrees on its inline and let-named routes. -/
theorem runV_eval_routes (run : Atom → Answers) (E : Code) (x : String) (env : Env) :
    (↑(runV run (.op .eval [E]) env) : Multiset Atom) =
      ↑(runV run (.let_ x E (.op .eval [.var x])) env) :=
  runV_letTransparent_op run .eval [] [] E x env (by simp [fvList]) (by simp [fvList])


/-! ## Quotation, reading and `eval` -/

/-- Reading and then printing gives back every atom: quotation is a section
of reading. -/
theorem print_parse (a : Atom) : print (parse a) = a := by
  refine parse.induct (motive_1 := fun a => print (parse a) = a)
    (motive_2 := fun as => printList (parseList as) = as) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ a
  · intro s; rfl
  · intro g; rfl
  · intro x; rfl
  · intro b ih; simp [parse, print, sym, ih]
  · intro x e b ihe ihb; simp [parse, print, sym, ihe, ihb]
  · intro a ih; simp [parse, print, sym, ih]
  · intro l i acc x b ihl ihi ihb; simp [parse, print, sym, ihl, ihi, ihb]
  · intro s args h1 h2 h3 h4 o ho ih
    rw [parse.eq_8 s args h1 h2 h3 h4, ho]
    simp [print, sym, Op.name_of_ofName ho, ih]
  · intro s args h1 h2 h3 h4 ho ih
    rw [parse.eq_8 s args h1 h2 h3 h4, ho]
    simp [print, printList, ih]
  · intro items h1 h2 h3 h4 h5 ih
    rw [parse.eq_9 items h1 h2 h3 h4 h5]
    simp [print, ih]
  · rfl
  · intro b bs ihb ihbs; simp [parseList, printList, ihb, ihbs]

/-- `eval` after `quote` runs the source program, one level of running lower. -/
theorem ev_eval_quote (n : Nat) (a : Atom) (env : Env) :
    ev (n + 1) (.op .eval [.quote (parse a)]) env = ev n (parse a) [] := by
  simp [ev, runV, runArgsV, product, applyV, print_parse]

/-- On a quoted quotation, `eval` removes exactly one level: the result is the
quoted atom itself, as data. -/
theorem ev_eval_requote (n : Nat) (a : Atom) (env : Env) :
    ev (n + 1) (.op .eval [.quote (.quote (parse a))]) env = [a] := by
  cases n <;> simp [ev, runV, runArgsV, product, applyV, print, parse, print_parse, sym]

/-- Quoting raises the level: a quotation's data never equals its body's. -/
theorem quote_raises_level (c : Code) : print (.quote c) ≠ print c := by
  intro h
  have hs := congrArg sizeOf h
  simp [print] at hs
  omega

/-! ## Admission: what a store receives -/

/-- What `add-atom` stores: its argument's syntax with let-bound variables
replaced by their values. -/
def stored (env : Env) (template : Code) : Atom := printWith env template

/-- A symbol taken out of a literal list by `car-atom` and stored through a
variable gives the same record as writing the symbol: in this calculus a value
is its atom, so the stored record does not depend on the route that produced
its parts. -/
theorem admission_route_independent :
    evSrc 4 (E [sym "car-atom", E [sym "the", sym "cat"]]) = [sym "the"] ∧
      stored [("w", sym "the")] (parse (E [sym "kv", V "w", num 1])) =
        print (parse (E [sym "kv", sym "the", num 1])) := by
  decide

/-! ## Why type-directed holding breaks let-naming -/

/-- At a position that holds both a call and a variable, the call is received
as syntax, while its let-named form receives each answer. The two agree
exactly when the operation cannot tell the syntax from its answers. -/
theorem runHE_held (run : Atom → Answers) (o : Op) (E : Code) (x : String) (env : Env)
    (hold : heHolds o [E] 0 = true) (holdVar : heHolds o [.var x] 0 = true) :
    runHE run (.op o [E]) env = applyHE run o [printWith env E] ∧
      runHE run (.let_ x E (.op o [.var x])) env =
        (runHE run E env).flatMap fun v => applyHE run o [v] := by
  constructor
  · simp [runHE, runArgsHE, hold, product]
  · simp [runHE, runArgsHE, holdVar, product, printWith]

/-- The mode of `==`'s parameters depends on the form of its arguments: a call
declared to return `Expression` holds both, variables do not. -/
theorem he_eq_mode_depends_on_argument :
    heHolds .eq [.op .sortAtom [.lit (sym "b")], .op .sortAtom [.lit (sym "a")]] 0 = true ∧
      heHolds .eq [.var "p", .var "q"] 0 = false := by
  decide
end Mettapedia.Languages.MeTTa.EvaluationControl.ArgumentModes

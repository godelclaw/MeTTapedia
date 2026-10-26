import Mettapedia.Languages.MeTTa.DeclarationFaces.Agreement

/-!
# Admission controls: natural numbers, polymorphic lists, and refused declarations

Each declaration is written as its MeTTa type declarations and equations would be read:
`(: Z Nat)`, `(: S (-> Nat Nat))`, `(: add (-> Nat Nat Nat))`, `(= (add Z $n) $n)`, and so on.
Admission is decided by computation (`decide`).

Positive controls: addition on natural numbers; `length` and `append` on lists of any element
sort, a parameterized datatype with polymorphic functions.

Negative controls, each refused with its reason:
* two equations `(= (pick) A)` style overlap: `(f Z) = A` and `(f $x) = B` (`overlapping_refused`);
* a missing case: `(pred (S $n)) = $n` alone (`missingCase_refused`);
* a call at the same argument: `(loop $x) = (loop $x)` (`loop_refused`);
* a call that is not on a proper part: `(half (S $n)) = (half (minus ...))` style, here
  `(down (S $n)) = (down (double $n))` (`nonStructural_refused`);
* a repeated variable: `(same $x $x) = T` (`nonlinear_refused`);
* an ill-sorted right side: `(bad $n) = Nil` at sort `Nat` (`untyped_refused`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.DeclarationFaces.Controls

open Tm

/-- `(: Nat Type)`, `(: Z Nat)`, `(: S (-> Nat Nat))`. -/
def natData : DataDecl String := ⟨"Nat", [], [("Z", []), ("S", [.app "Nat" []])]⟩

/-- `(: List (-> Type Type))`, `(: Nil (List $a))`, `(: Cons (-> $a (List $a) (List $a)))`. -/
def listData : DataDecl String :=
  ⟨"List", ["a"], [("Nil", []), ("Cons", [.var "a", .app "List" [.var "a"]])]⟩

/-- The sort `Nat`. -/
abbrev nat : Sort' := .app "Nat" []

/-- The sort `(List $a)`. -/
abbrev listOf (a : Sort') : Sort' := .app "List" [a]

/-- Numerals. -/
def num : Nat → Tm String
  | 0 => .app "Z" []
  | n + 1 => .app "S" [num n]

/-! ## Addition -/

/-- `(: add (-> Nat Nat Nat))`. -/
def addSig : Signature String := ⟨[natData], [⟨"add", [nat, nat], nat⟩]⟩

/-- `(= (add Z $n) $n)`, `(= (add (S $m) $n) (S (add $m $n)))`. -/
def addProgram : Program String :=
  [⟨.app "add" [.app "Z" [], .var "n"], .var "n"⟩,
   ⟨.app "add" [.app "S" [.var "m"], .var "n"], .app "S" [.app "add" [.var "m", .var "n"]]⟩]

/-- **Positive control**: addition is admitted. -/
theorem add_admitted : admit addSig addProgram = none := by decide

/-! ## Polymorphic lists -/

/-- `length` and `append` on lists of any element sort. -/
def listSig : Signature String :=
  ⟨[natData, listData],
   [⟨"length", [listOf (.var "a")], nat⟩,
    ⟨"append", [listOf (.var "a"), listOf (.var "a")], listOf (.var "a")⟩]⟩

/-- `(= (length Nil) Z)`, `(= (length (Cons $x $xs)) (S (length $xs)))`,
`(= (append Nil $ys) $ys)`, `(= (append (Cons $x $xs) $ys) (Cons $x (append $xs $ys)))`. -/
def listProgram : Program String :=
  [⟨.app "length" [.app "Nil" []], .app "Z" []⟩,
   ⟨.app "length" [.app "Cons" [.var "x", .var "xs"]], .app "S" [.app "length" [.var "xs"]]⟩,
   ⟨.app "append" [.app "Nil" [], .var "ys"], .var "ys"⟩,
   ⟨.app "append" [.app "Cons" [.var "x", .var "xs"], .var "ys"],
     .app "Cons" [.var "x", .app "append" [.var "xs", .var "ys"]]⟩]

/-- **Positive control**: polymorphic `length` and `append` are admitted. -/
theorem list_admitted : admit listSig listProgram = none := by decide

/-! ## Refused declarations -/

/-- One function on natural numbers. -/
def unarySig (f : String) : Signature String := ⟨[natData], [⟨f, [nat], nat⟩]⟩

/-- `(= (f Z) Z)`, `(= (f $x) (S Z))`: the two left sides share the instance `(f Z)`. -/
def overlapping : Program String :=
  [⟨.app "f" [num 0], num 0⟩, ⟨.app "f" [.var "x"], num 1⟩]

/-- **Negative control**: overlapping equations are refused, naming the pair. -/
theorem overlapping_refused :
    admit (unarySig "f") overlapping = some (.overlap overlapping[0] overlapping[1]) := by decide

/-- `(= (pred (S $n)) $n)` alone: no case for `Z`. -/
def predPartial : Program String := [⟨.app "pred" [.app "S" [.var "n"]], .var "n"⟩]

/-- **Negative control**: a missing case is refused, naming the function. -/
theorem missingCase_refused : admit (unarySig "pred") predPartial = some (.missingCase "pred") := by
  decide

/-- `(= (loop $x) (loop $x))`. -/
def loopProgram : Program String := [⟨.app "loop" [.var "x"], .app "loop" [.var "x"]⟩]

/-- **Negative control**: a call at the same argument is refused as not structural. -/
theorem loop_refused :
    admit (unarySig "loop") loopProgram = some (.notStructural loopProgram[0]) := by decide

/-- `pred` with both cases, and `(= (count (S $n)) (S (count (pred (S $n)))))`: it terminates, but
its recursive call is not on a proper part of its pattern. -/
def countSig : Signature String := ⟨[natData], [⟨"pred", [nat], nat⟩, ⟨"count", [nat], nat⟩]⟩

/-- The equations of `pred` and `count`. -/
def countProgram : Program String :=
  [⟨.app "pred" [num 0], num 0⟩,
   ⟨.app "pred" [.app "S" [.var "n"]], .var "n"⟩,
   ⟨.app "count" [num 0], num 0⟩,
   ⟨.app "count" [.app "S" [.var "n"]],
     .app "S" [.app "count" [.app "pred" [.app "S" [.var "n"]]]]⟩]

/-- **Negative control**: recursion through a computed argument is refused as not structural. -/
theorem nonStructural_refused :
    admit countSig countProgram = some (.notStructural countProgram[3]) := by decide

/-- `(: same (-> Nat Nat Nat))`, `(= (same $x $x) Z)`. -/
def sameSig : Signature String := ⟨[natData], [⟨"same", [nat, nat], nat⟩]⟩

/-- A repeated variable in a left side. -/
def sameProgram : Program String := [⟨.app "same" [.var "x", .var "x"], num 0⟩]

/-- **Negative control**: a repeated variable is refused. -/
theorem nonlinear_refused : admit sameSig sameProgram = some (.nonlinear sameProgram[0]) := by
  decide

/-- `(= (bad $n) Nil)` with `(: bad (-> Nat Nat))`. -/
def badProgram : Program String := [⟨.app "bad" [.var "n"], .app "Nil" []⟩]

/-- **Negative control**: a right side of the wrong sort is refused. -/
theorem untyped_refused :
    admit (⟨[natData, listData], [⟨"bad", [nat], nat⟩]⟩ : Signature String) badProgram =
      some (.untyped badProgram[0]) := by decide

/-! ## Lexicographic descent -/

/-- `(: ack (-> Nat Nat Nat))`. -/
def ackSig : Signature String := ⟨[natData], [⟨"ack", [nat, nat], nat⟩]⟩

/-- Ackermann's function: `(= (ack Z $n) (S $n))`, `(= (ack (S $m) Z) (ack $m (S Z)))`,
`(= (ack (S $m) (S $n)) (ack $m (ack (S $m) $n)))`. -/
def ackProgram : Program String :=
  [⟨.app "ack" [num 0, .var "n"], .app "S" [.var "n"]⟩,
   ⟨.app "ack" [.app "S" [.var "m"], num 0], .app "ack" [.var "m", num 1]⟩,
   ⟨.app "ack" [.app "S" [.var "m"], .app "S" [.var "n"]],
     .app "ack" [.var "m", .app "ack" [.app "S" [.var "m"], .var "n"]]⟩]

/-- **Negative**: Ackermann's function does not descend structurally at any one position. -/
theorem ack_not_structural :
    (firstNotDescending ackProgram (inferCertificate ackSig ackProgram)).isSome = true := by decide

/-- **Positive**: it descends lexicographically, along its first and then its second argument, and is
admitted. -/
theorem ack_admitted : admit ackSig ackProgram = none := by decide

/-- It runs: `(ack 2 1)` is `5`. -/
example : evalTm ackProgram 60 (.app "ack" [num 2, num 1]) = some [num 5] := by decide

/-- `even` and `odd` on natural numbers, into booleans. -/
def evenOddSig : Signature String :=
  ⟨[natData, ⟨"Bool", [], [("True", []), ("False", [])]⟩],
   [⟨"even", [nat], .app "Bool" []⟩, ⟨"odd", [nat], .app "Bool" []⟩]⟩

/-- `(= (even Z) True)`, `(= (even (S $n)) (odd $n))`, `(= (odd Z) False)`, `(= (odd (S $n)) (even $n))`. -/
def evenOddProgram : Program String :=
  [⟨.app "even" [num 0], .app "True" []⟩, ⟨.app "even" [.app "S" [.var "n"]], .app "odd" [.var "n"]⟩,
   ⟨.app "odd" [num 0], .app "False" []⟩, ⟨.app "odd" [.app "S" [.var "n"]], .app "even" [.var "n"]⟩]

/-- **Negative**: mutual recursion does not descend with ranks by declaration order. -/
theorem evenOdd_not_structural :
    (firstNotDescending evenOddProgram (inferCertificate evenOddSig evenOddProgram)).isSome = true := by
  decide

/-- **Positive**: with ranks by strongly connected component, `even` and `odd` descend together, and
the declaration is admitted. -/
theorem evenOdd_admitted : admit evenOddSig evenOddProgram = none := by decide

/-- It runs: `(even 3)` is `False`. -/
example : evalTm evenOddProgram 10 (.app "even" [num 3]) = some [.app "False" []] := by decide

/-! ## Runs: the operational face -/

/-- Lists of numerals. -/
def listOfNums : List Nat → Tm String
  | [] => .app "Nil" []
  | n :: ns => .app "Cons" [num n, listOfNums ns]

/-- **Run**: `(add 2 3)` evaluates to the single result `5`. -/
example : evalTm addProgram 20 (.app "add" [num 2, num 3]) = some [num 5] := by decide

/-- **Run**: `(length (append (Cons 0 Nil) (Cons 1 (Cons 2 Nil))))` evaluates to `3`. -/
example : evalTm listProgram 30
    (.app "length" [.app "append" [listOfNums [0], listOfNums [1, 2]]]) = some [num 3] := by
  decide

/-- The admitted addition, as a value of `Admitted`. -/
theorem add_adm : Admitted addSig addProgram := admit_sound add_admitted

/-- **The main theorem at an instance**: `(add 2 3)` has normal form `5`, which the evaluator,
every strategy and the model all give. -/
theorem add_two_three_faces :
    add_adm.normalForm (.app "add" [num 2, num 3]) = num 5 := by
  have h := (add_adm.evalTm_result (.app "add" [num 2, num 3])).2 20 _
    (by decide : evalTm addProgram 20 (.app "add" [num 2, num 3]) = some [num 5])
  simpa using h.symm

/-! ## The scope is part of the statement -/

/-- `(= (add $n Z) Z)`: an ordinary rule added to the same space as the admitted addition. -/
def collidingRule : Equation String := ⟨.app "add" [.var "n", num 0], num 0⟩

/-- **Negative control (collision)**: the scope with the added rule is refused as an overlap. -/
theorem collision_refused :
    admit addSig (addProgram ++ [collidingRule]) =
      some (.overlap addProgram[0] collidingRule) := by decide

/-- **Negative control (collision)**: in the enlarged scope, `(add 1 0)` has the results `1`, `1`
and `0`: the added rule gives `0`, and inside `(S (add Z Z))` both the admitted equation and the
added rule match, so `1` comes twice. In the admitted scope it has the one result `1`. -/
theorem collision_two_results :
    evalTm (addProgram ++ [collidingRule]) 20 (.app "add" [num 1, num 0]) =
      some [num 1, num 1, num 0] ∧
      evalTm addProgram 20 (.app "add" [num 1, num 0]) = some [num 1] := by decide

/-- `(: double (-> Nat Nat))`, `(= (double $n) (add $n $n))`, over a scope that also defines
`add`. -/
def doubleSig : Signature String := ⟨[natData], [⟨"add", [nat, nat], nat⟩, ⟨"double", [nat], nat⟩]⟩

/-- The equation of `double`, written once. -/
def doubleEquation : Equation String := ⟨.app "double" [.var "n"], .app "add" [.var "n", .var "n"]⟩

/-- A second, different definition of `add`: `(= (add Z $n) $n)`, `(= (add (S $m) $n) (S $m))`. -/
def otherAdd : Program String :=
  [⟨.app "add" [num 0, .var "n"], .var "n"⟩,
   ⟨.app "add" [.app "S" [.var "m"], .var "n"], .app "S" [.var "m"]⟩]

/-- Both scopes are admitted. -/
theorem double_scopes_admitted :
    admit doubleSig (addProgram ++ [doubleEquation]) = none ∧
      admit doubleSig (otherAdd ++ [doubleEquation]) = none := by decide

/-- **Dependencies (stale definitions)**: the same equation of `double` means different things in
the two scopes: `(double 2)` is `4` in one and `2` in the other. A result about `double` is a result
about its scope, including the definitions it depends on. -/
theorem double_depends_on_scope :
    evalTm (addProgram ++ [doubleEquation]) 20 (.app "double" [num 2]) = some [num 4] ∧
      evalTm (otherAdd ++ [doubleEquation]) 20 (.app "double" [num 2]) = some [num 2] := by
  decide

/-! ## Refused declarations still run -/

/-- **A non-structural but terminating declaration still runs**: `count` is refused by the theory
(`nonStructural_refused`) while evaluation computes `(count 3)` to `3`. -/
example : evalTm countProgram 40 (.app "count" [num 3]) = some [num 3] := by decide

/-- **A missing case leaves inert data**: `(pred Z)` matches no equation, and evaluation returns it
unchanged, as data, not as an error; `(pred 2)` computes. -/
example : evalTm predPartial 10 (.app "pred" [num 0]) = some [.app "pred" [num 0]] ∧
    evalTm predPartial 10 (.app "pred" [num 2]) = some [num 1] := by decide

/-- Two interpretations of `pred` on normal forms that differ only at `Z`. -/
def predAt (z : Tm String) : String → List (Tm String) → Tm String
  | _, [.app "S" [v]] => v
  | _, _ => z

/-- Both interpretations satisfy the one equation of the partial `pred`. -/
theorem predAt_equation (z : Tm String) (ρ : String → Tm String) :
    interp predPartial (predAt z) ρ predPartial[0].lhs = interp predPartial (predAt z) ρ predPartial[0].rhs := by
  have defined : predPartial.Defines "pred" := ⟨predPartial[0], by simp [predPartial], rfl⟩
  have undefinedS : ¬ predPartial.Defines "S" := by
    rintro ⟨e, he, h⟩
    simp only [predPartial, List.mem_singleton] at he
    subst he
    simp [head?] at h
  show interp predPartial (predAt z) ρ (.app "pred" [.app "S" [.var "n"]]) =
    interp predPartial (predAt z) ρ (.var "n")
  rw [interp_app, if_pos defined, List.map_cons, List.map_nil, interp_app, if_neg undefinedS]
  simp [predAt]

/-- **A missing case is a partial function extensionally**: the equations do not determine the
value at the missing case; two interpretations satisfying them differ at `(pred Z)`. -/
theorem partial_not_determined :
    predAt (num 0) "pred" [num 0] ≠ predAt (num 1) "pred" [num 0] := by decide

/-! ## A divergent declaration: strategies disagree on termination -/

/-- `(= (const $x $y) $x)`, `(= loop loop)`. -/
def lazyProgram : Program String :=
  [⟨.app "const" [.var "x", .var "y"], .var "x"⟩, ⟨.app "loop" [], .app "loop" []⟩]

/-- `(: const (-> Nat Nat Nat))`, `(: loop Nat)`. -/
def lazySig : Signature String := ⟨[natData], [⟨"const", [nat, nat], nat⟩, ⟨"loop", [], nat⟩]⟩

/-- **Negative control**: `loop` is refused as not structural. -/
theorem lazy_refused : admit lazySig lazyProgram = some (.notStructural lazyProgram[1]) := by
  decide

theorem loop_step : RootStep lazyProgram (.app "loop" []) (.app "loop" []) := by
  have := RootStep.rule (P := lazyProgram) (e := ⟨.app "loop" [], .app "loop" []⟩) Tm.var
    (by simp [lazyProgram])
  simpa using this

/-- **The evaluator runs out of fuel on `loop` at every fuel**: the operational face runs a
refused declaration and reports exhaustion, not a value. -/
theorem loop_exhausts : ∀ n, evalTm lazyProgram n (.app "loop" []) = none := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      have results : rootResults lazyProgram (.app "loop" []) = [.app "loop" []] := by decide
      simp [evalTm, mapOpt, choices, results, ih]

/-- **Innermost evaluation of `(const Z loop)` never ends**: its only innermost step leads back to
itself. -/
theorem innermost_cycles :
    InnermostStep lazyProgram (.app "const" [num 0, .app "loop" []])
      (.app "const" [num 0, .app "loop" []]) := by
  have := InnermostStep.arg (P := lazyProgram) "const" [num 0, .app "loop" []] 1 (by simp)
    (.root (by simp) loop_step)
  simpa using this

/-- **Outermost evaluation of `(const Z loop)` ends at `Z`.** -/
theorem outermost_ends :
    OutermostStep lazyProgram (.app "const" [num 0, .app "loop" []]) (num 0) := by
  have := RootStep.rule (P := lazyProgram) (e := ⟨.app "const" [.var "x", .var "y"], .var "x"⟩)
    (fun x => if x = "x" then num 0 else .app "loop" []) (by simp [lazyProgram])
  exact .root (by simpa [num] using this)

end Mettapedia.Languages.MeTTa.DeclarationFaces.Controls

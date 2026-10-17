import Mettapedia.Languages.MeTTa.EquationKernel.Matching
import Mettapedia.Languages.MeTTa.EquationKernel.SpaceCheck
import Mettapedia.Languages.MeTTa.EquationKernel.Sealed
import Mettapedia.Languages.MeTTa.EquationKernel.Wire

/-!
# Worked examples and controls of the equation kernel

* `(= (inc $x) (S $x))` with `(inc (inc Z)) →* (S (S Z))`: an innermost
  trace, an outermost trace, a derivation with congruence and transitivity,
  three nested applications, and one derivation shared by two arguments.
* Two equal stored copies of `(= (coin) heads)` and one `(= (coin) tails)`:
  each copy is its own accepted citation, a third copy is refused, and
  reordering the program changes no verdict.
* Refusals: a forged citation, a copy index past the stored copies, a wrong
  substitution, a wrong site, a site outside the atom, a wrong target, a
  forward reference, a transitivity mismatch, an instantiated subject
  variable, and a captured variable (accepted by the core judgment as an
  instance, refused by the hygienic check).
* The sealed kernel derives the same claims and refuses the same steps;
  recording emits a certificate the checker accepts; minting refuses a bad
  certificate.

Every verdict is computed by the kernel's own definitions and checked by
`decide`. `controlsText` renders the same controls for the MeTTa checker,
with the expected verdicts computed by the Lean checker.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.EquationKernel.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.EquationKernel
open Mettapedia.Languages.MeTTa.EquationKernel.Wire

/-! ## Atoms -/

def sym (name : String) : Atom := .symbol name
def var (name : String) : Atom := .var name
def app (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)

def zero : Atom := sym "Z"
def succ (atom : Atom) : Atom := app "S" [atom]
def inc (atom : Atom) : Atom := app "inc" [atom]

/-! ## `(= (inc $x) (S $x))` -/

def incEquation : Atom := Atom.equality (inc (var "x")) (succ (var "x"))
def incProgram : List Atom := [incEquation]
def incCite : Citation := ⟨incEquation, 0⟩

/-- Innermost first: `(inc (inc Z)) → (inc (S Z)) → (S (S Z))`. -/
def incInner : List StepData :=
  [⟨incCite, [1], [("x", zero)]⟩, ⟨incCite, [], [("x", succ zero)]⟩]

/-- Outermost first: `(inc (inc Z)) → (S (inc Z)) → (S (S Z))`. -/
def incOuter : List StepData :=
  [⟨incCite, [], [("x", inc zero)]⟩, ⟨incCite, [1], [("x", zero)]⟩]

/-- The rewriting-logic proof term `trans (inc (e Z)) (e (S Z))`. -/
def incTerm : Certificate :=
  ⟨[.refl (inc zero), .step 0 incCite [] [("x", zero)], .congr [sym "inc"] 1 [],
    .refl (inc (succ zero)), .step 3 incCite [] [("x", succ zero)], .trans 2 4], 5⟩

/-- Three nested applications, innermost first. -/
def incThree : List StepData :=
  [⟨incCite, [1, 1], [("x", zero)]⟩, ⟨incCite, [1], [("x", succ zero)]⟩,
    ⟨incCite, [], [("x", succ (succ zero))]⟩]

def incClaim : Claim := (inc (inc zero), succ (succ zero))

example : replay incProgram (inc (inc zero)) incInner = some (succ (succ zero)) := by decide
example : replay incProgram (inc (inc zero)) incOuter = some (succ (succ zero)) := by decide
example : check incProgram (traceCertificate (inc (inc zero)) incInner) incClaim = true := by decide
example : check incProgram (traceCertificate (inc (inc zero)) incOuter) incClaim = true := by decide
example : check incProgram incTerm incClaim = true := by decide
example : check incProgram (traceCertificate (inc (inc (inc zero))) incThree)
    (inc (inc (inc zero)), succ (succ (succ zero))) = true := by decide

/-- The two halves of the innermost trace, composed. -/
def incFirstHalf : Certificate := traceCertificate (inc (inc zero)) (incInner.take 1)
def incSecondHalf : Certificate := traceCertificate (inc (succ zero)) (incInner.drop 1)

example : check incProgram (incFirstHalf.seq incSecondHalf) incClaim = true :=
  check_seq (middle := inc (succ zero)) (by decide) (by decide)

/-- One derivation of `(inc (inc Z)) →* (S (S Z))`, used in both arguments. -/
def incShared : Certificate :=
  Certificate.both (sym "pair") (traceCertificate (inc (inc zero)) incInner) (inc (inc zero))
    (succ (succ zero))

def pairClaim : Claim :=
  (.expression [sym "pair", inc (inc zero), inc (inc zero)],
    .expression [sym "pair", succ (succ zero), succ (succ zero)])

example : check incProgram incShared pairClaim = true := check_both _ (by decide)
example : incShared.rows.length = 6 := by decide

/-- The reached claim is a theorem of the judgment. -/
theorem inc_reaches : Reaches (spaceOf incProgram) (inc (inc zero)) (succ (succ zero)) :=
  check_sound (certificate := incTerm) (by decide)

/-! ## Equal stored copies count separately -/

def coin : Atom := app "coin" []
def coinHeads : Atom := Atom.equality coin (sym "heads")
def coinTails : Atom := Atom.equality coin (sym "tails")
def coinProgram : List Atom := [coinHeads, coinHeads, coinTails]
def coinReordered : List Atom := [coinTails, coinHeads, coinHeads]

def coinStep (equation : Atom) (copy : Nat) : Certificate :=
  traceCertificate coin [⟨⟨equation, copy⟩, [], []⟩]

example : check coinProgram (coinStep coinHeads 0) (coin, sym "heads") = true := by decide
example : check coinProgram (coinStep coinHeads 1) (coin, sym "heads") = true := by decide
example : check coinProgram (coinStep coinHeads 2) (coin, sym "heads") = false := by decide
example : check coinProgram (coinStep coinTails 0) (coin, sym "tails") = true := by decide
example : check coinProgram (coinStep coinTails 1) (coin, sym "tails") = false := by decide
example : check coinReordered (coinStep coinHeads 1) (coin, sym "heads") = true := by decide

/-- Two accepted citations reach `heads`, one reaches `tails`: the results
of one step at the root are the multiset `{heads, heads, tails}`. -/
example : ((occurrences coinProgram).filter fun citation =>
    check coinProgram (traceCertificate coin [⟨citation, [], []⟩]) (coin, sym "heads")).length = 2 := by
  rw [accepted_citations_length]
  decide

example : ((occurrences coinProgram).filter fun citation =>
    check coinProgram (traceCertificate coin [⟨citation, [], []⟩]) (coin, sym "tails")).length = 1 := by
  rw [accepted_citations_length]
  decide

example : (occurrences coinProgram).Perm (occurrences coinReordered) :=
  occurrences_perm (by decide)

/-! ## Refusals -/

/-- An equation that is not stored. -/
def forgedEquation : Atom := Atom.equality (inc (var "x")) (app "T" [var "x"])

example : check incProgram (traceCertificate (inc zero) [⟨⟨forgedEquation, 0⟩, [], [("x", zero)]⟩])
    (inc zero, app "T" [zero]) = false := by decide

/-- The stored equation exists once: copy `1` is not stored. -/
example : check incProgram (traceCertificate (inc zero) [⟨⟨incEquation, 1⟩, [], [("x", zero)]⟩])
    (inc zero, succ zero) = false := by decide

/-- Wrong substitution: the instance `(inc (S Z))` is not the subatom `(inc Z)`. -/
example : check incProgram (traceCertificate (inc (inc zero)) [⟨incCite, [1], [("x", succ zero)]⟩])
    (inc (inc zero), inc (succ (succ zero))) = false := by decide

/-- Wrong site: position `[0]` is the head symbol. -/
example : check incProgram (traceCertificate (inc (inc zero)) [⟨incCite, [0], [("x", zero)]⟩])
    (inc (inc zero), app "S" [zero]) = false := by decide

/-- A site outside the atom. -/
example : check incProgram (traceCertificate (inc (inc zero)) [⟨incCite, [2], [("x", zero)]⟩])
    (inc (inc zero), inc (inc zero)) = false := by decide

/-- A correct derivation does not certify another target. -/
example : check incProgram incTerm (inc (inc zero), succ zero) = false := by decide

/-- A reference to a later row. -/
example : check incProgram ⟨[.step 1 incCite [] [("x", zero)], .refl (inc zero)], 0⟩
    (inc zero, succ zero) = false := by decide

/-- Transitivity needs equal middle atoms. -/
example : check incProgram ⟨[.refl (inc zero), .refl (succ zero), .trans 0 1], 2⟩
    (inc zero, succ zero) = false := by decide

/-- The subject's variables are constants: `(g $z)` does not reach `B` by the
equation `(= (g A) B)`, while its instance `(g A)` does. -/
def rigidProgram : List Atom := [Atom.equality (app "g" [sym "A"]) (sym "B")]

example : check rigidProgram
    (traceCertificate (app "g" [var "z"]) [⟨⟨rigidProgram.head!, 0⟩, [], [("z", sym "A")]⟩])
    (app "g" [var "z"], sym "B") = false := by decide

example : check rigidProgram
    (traceCertificate (app "g" [sym "A"]) [⟨⟨rigidProgram.head!, 0⟩, [], []⟩])
    (app "g" [sym "A"], sym "B") = true := by decide

/-- `(= (f $x) (pair $x $y))`: `$y` occurs only on the right side. -/
def captureEquation : Atom := Atom.equality (app "f" [var "x"]) (app "pair" [var "x", var "y"])
def captureProgram : List Atom := [captureEquation]

/-- The instance that identifies the new variable with the subject's `$y`. -/
def captured : Certificate :=
  traceCertificate (app "f" [var "y"]) [⟨⟨captureEquation, 0⟩, [], [("x", var "y"), ("y", var "y")]⟩]

/-- The fresh instance. -/
def renamedApart : Certificate :=
  traceCertificate (app "f" [var "y"]) [⟨⟨captureEquation, 0⟩, [], [("x", var "y"), ("y", var "y1")]⟩]

example : check captureProgram captured (app "f" [var "y"], app "pair" [var "y", var "y"]) = true := by
  decide
example : checkHygienic captureProgram captured
    (app "f" [var "y"], app "pair" [var "y", var "y"]) = false := by decide
example : checkHygienic captureProgram renamedApart
    (app "f" [var "y"], app "pair" [var "y", var "y1"]) = true := by decide

/-! ## Builtins as declared facts

The kernel executes no grounded operation. A builtin's behaviour enters only
as stored equations over grounded values, cited like any other equation. -/

def int (value : Int) : Atom := .grounded (.int value)
def plusFact : Atom := Atom.equality (app "+" [int 1, int 2]) (int 3)
def factProgram : List Atom := [plusFact]
def plusStep : Certificate := traceCertificate (app "+" [int 1, int 2]) [⟨⟨plusFact, 0⟩, [], []⟩]

example : check factProgram plusStep (app "+" [int 1, int 2], int 3) = true := by decide
example : check factProgram plusStep (app "+" [int 1, int 2], int 4) = false := by decide
example : check [] plusStep (app "+" [int 1, int 2], int 3) = false := by decide

/-! ## The sealed kernel on the same examples -/

def sealedInner : Option (Theorem incProgram) :=
  ((Theorem.refl incProgram (inc (inc zero))).step incCite [1] [("x", zero)]).bind
    fun middle => middle.step incCite [] [("x", succ zero)]

example : sealedInner.map Theorem.claim = some incClaim := by decide

def sealedTerm : Option (Theorem incProgram) := do
  let inner ← (Theorem.refl incProgram (inc zero)).step incCite [] [("x", zero)]
  let outer ← (Theorem.refl incProgram (inc (succ zero))).step incCite [] [("x", succ zero)]
  (Theorem.congr [sym "inc"] inner []).trans outer

example : sealedTerm.map Theorem.claim = some incClaim := by decide

/-- The sealed step refuses the wrong substitution. -/
example : ((Theorem.refl incProgram (inc (inc zero))).step incCite [1] [("x", succ zero)]).map
    Theorem.claim = none := by decide

/-- Recording the innermost derivation emits a certificate the checker accepts. -/
def recordedInner : Option (Session incProgram × Nat) := do
  let (first, start) ← (Session.empty : Session incProgram).refl (inc (inc zero))
  let (second, middle) ← first.step start incCite [1] [("x", zero)]
  second.step middle incCite [] [("x", succ zero)]

example : (recordedInner.map fun (session, index) =>
    check incProgram (session.certificate index) incClaim) = some true := by decide

example : ((mint incProgram incTerm incClaim).map Theorem.claim) = some incClaim := by decide
example : ((mint incProgram incTerm (inc (inc zero), succ zero)).map Theorem.claim) = none := by decide

/-! ## Controls for the MeTTa checker -/

/-- One control: a name, a MeTTa expression and the expected value text. -/
structure Control where
  name : String
  expression : String
  expected : String

def verdictText (verdict : Bool) : String := if verdict then "True" else "False"

def checkControl (name : String) (program : List Atom) (certificate : Certificate) (claim : Claim) :
    Control :=
  ⟨name, "(ek:check " ++ programText program ++ " " ++ certificateText certificate ++ " " ++
    claimText claim ++ ")", verdictText (check program certificate claim)⟩

def hygienicControl (name : String) (program : List Atom) (certificate : Certificate)
    (claim : Claim) : Control :=
  ⟨name, "(ek:check-hygienic " ++ programText program ++ " " ++ certificateText certificate ++ " " ++
    claimText claim ++ ")", verdictText (checkHygienic program certificate claim)⟩

/-- The expected value of a sealed derivation's claim. -/
def claimOption (claim : Option Claim) : String :=
  match claim with
  | some claim => "(ek:some " ++ claimText claim ++ ")"
  | none => "ek:none"

/-- A script of sealed-rule calls. Its MeTTa text calls the kernel's rule
functions; its Lean meaning runs the same rules on `SealedTheorem`. -/
inductive Script where
  | refl (theory : List Atom) (atom : Atom)
  | step (premise : Script) (citation : Citation) (path : List Nat) (bindings : Bindings)
  | congr (left : List Atom) (premise : Script) (right : List Atom)
  | trans (first second : Script)
  | weaken (premise : Script) (theory : List Atom)

def Script.run : Script → Option SealedTheorem
  | .refl theory atom => some (SealedTheorem.refl theory atom)
  | .step premise citation path bindings => premise.run.bind fun sealed => sealed.step citation path bindings
  | .congr left premise right => premise.run.map fun sealed => SealedTheorem.congr left sealed right
  | .trans first second => first.run.bind fun earlier => second.run.bind fun later => earlier.trans later
  | .weaken premise theory => premise.run.bind fun sealed => sealed.weaken theory

def Script.text : Script → String
  | .refl theory atom => "(ek:lcf-refl " ++ programText theory ++ " " ++ atomText atom ++ ")"
  | .step premise citation path bindings =>
      "(ek:lcf-step " ++ premise.text ++ " " ++ citationText citation ++ " " ++ natListText path ++ " " ++
        bindingsText bindings ++ ")"
  | .congr left premise right =>
      "(ek:lcf-congr " ++ listText (atomText.atomsText left) ++ " " ++ premise.text ++ " " ++
        listText (atomText.atomsText right) ++ ")"
  | .trans first second => "(ek:lcf-trans " ++ first.text ++ " " ++ second.text ++ ")"
  | .weaken premise theory => "(ek:lcf-weaken " ++ premise.text ++ " " ++ programText theory ++ ")"

/-- The claim of a sealed script, as `ek:lcf-claim` reads it. -/
def scriptControl (name : String) (script : Script) : Control :=
  ⟨name, "(ek:lcf-claim " ++ script.text ++ ")", claimOption (script.run.map SealedTheorem.claim)⟩

/-- A trace as a sealed script: reflexivity, then one step per trace step. -/
def traceScript (program : List Atom) (source : Atom) (steps : List StepData) : Script :=
  steps.foldl (fun script step => .step script step.citation step.path step.bindings) (.refl program source)

def sealedControl (name : String) (program : List Atom) (source : Atom) (steps : List StepData) :
    Control :=
  scriptControl name (traceScript program source steps)

/-- A recorded script: the same rules threaded through a recording session;
the result is the checker's verdict on the emitted certificate. -/
def recordedScript (program : List Atom) (source target : Atom) (steps : List StepData) : String :=
  let bindings := steps.zipIdx.map fun (step, index) =>
    "((ek:recorded $s" ++ toString (index + 1) ++ " $t" ++ toString (index + 1) ++ ") (ek:rec-step $s" ++
      toString index ++ " $t" ++ toString index ++ " " ++ citationText step.citation ++ " " ++
      natListText step.path ++ " " ++ bindingsText step.bindings ++ "))"
  "(let* (((ek:recorded $s0 $t0) (ek:rec-refl (ek:rec-open " ++ programText program ++ ") " ++
    atomText source ++ ")) " ++ " ".intercalate bindings ++ ") (ek:check " ++ programText program ++
    " (ek:rec-certificate $s" ++ toString steps.length ++ " $t" ++ toString steps.length ++ ") " ++
    claimText (source, target) ++ "))"

def recordedControl (name : String) (program : List Atom) (source target : Atom)
    (steps : List StepData) : Control :=
  ⟨name, recordedScript program source target steps,
    verdictText (replay program source steps == some target)⟩

def mintControl (name : String) (program : List Atom) (certificate : Certificate) (claim : Claim) :
    Control :=
  ⟨name, "(ek:lcf-claim (ek:mint " ++ programText program ++ " " ++ certificateText certificate ++ " " ++
    claimText claim ++ "))", claimOption ((mint program certificate claim).map Theorem.claim)⟩

/-- A certificate check, rendered for both certificate containers. -/
structure CheckCase where
  name : String
  program : List Atom
  certificate : Certificate
  claim : Claim

def CheckCase.control (case_ : CheckCase) : Control :=
  checkControl case_.name case_.program case_.certificate case_.claim

def checkCases : List CheckCase :=
  [ ⟨"inc-inner", incProgram, traceCertificate (inc (inc zero)) incInner, incClaim⟩,
    ⟨"inc-outer", incProgram, traceCertificate (inc (inc zero)) incOuter, incClaim⟩,
    ⟨"inc-term", incProgram, incTerm, incClaim⟩,
    ⟨"inc-three", incProgram, traceCertificate (inc (inc (inc zero))) incThree,
      (inc (inc (inc zero)), succ (succ (succ zero)))⟩,
    ⟨"inc-seq", incProgram, incFirstHalf.seq incSecondHalf, incClaim⟩,
    ⟨"inc-shared", incProgram, incShared, pairClaim⟩,
    ⟨"coin-heads-0", coinProgram, coinStep coinHeads 0, (coin, sym "heads")⟩,
    ⟨"coin-heads-1", coinProgram, coinStep coinHeads 1, (coin, sym "heads")⟩,
    ⟨"coin-heads-2", coinProgram, coinStep coinHeads 2, (coin, sym "heads")⟩,
    ⟨"coin-tails-0", coinProgram, coinStep coinTails 0, (coin, sym "tails")⟩,
    ⟨"coin-tails-1", coinProgram, coinStep coinTails 1, (coin, sym "tails")⟩,
    ⟨"coin-reordered-heads-1", coinReordered, coinStep coinHeads 1, (coin, sym "heads")⟩,
    ⟨"coin-reordered-tails-0", coinReordered, coinStep coinTails 0, (coin, sym "tails")⟩,
    ⟨"refuse-forged-citation", incProgram,
      traceCertificate (inc zero) [⟨⟨forgedEquation, 0⟩, [], [("x", zero)]⟩], (inc zero, app "T" [zero])⟩,
    ⟨"refuse-missing-copy", incProgram,
      traceCertificate (inc zero) [⟨⟨incEquation, 1⟩, [], [("x", zero)]⟩], (inc zero, succ zero)⟩,
    ⟨"refuse-wrong-substitution", incProgram,
      traceCertificate (inc (inc zero)) [⟨incCite, [1], [("x", succ zero)]⟩],
      (inc (inc zero), inc (succ (succ zero)))⟩,
    ⟨"refuse-wrong-site", incProgram,
      traceCertificate (inc (inc zero)) [⟨incCite, [0], [("x", zero)]⟩], (inc (inc zero), app "S" [zero])⟩,
    ⟨"refuse-site-outside", incProgram,
      traceCertificate (inc (inc zero)) [⟨incCite, [2], [("x", zero)]⟩], (inc (inc zero), inc (inc zero))⟩,
    ⟨"refuse-wrong-target", incProgram, incTerm, (inc (inc zero), succ zero)⟩,
    ⟨"refuse-forward-reference", incProgram,
      ⟨[.step 1 incCite [] [("x", zero)], .refl (inc zero)], 0⟩, (inc zero, succ zero)⟩,
    ⟨"refuse-trans-mismatch", incProgram,
      ⟨[.refl (inc zero), .refl (succ zero), .trans 0 1], 2⟩, (inc zero, succ zero)⟩,
    ⟨"refuse-instantiated-subject", rigidProgram,
      traceCertificate (app "g" [var "z"]) [⟨⟨rigidProgram.head!, 0⟩, [], [("z", sym "A")]⟩],
      (app "g" [var "z"], sym "B")⟩,
    ⟨"rigid-instance", rigidProgram,
      traceCertificate (app "g" [sym "A"]) [⟨⟨rigidProgram.head!, 0⟩, [], []⟩], (app "g" [sym "A"], sym "B")⟩,
    ⟨"capture-core-instance", captureProgram, captured, (app "f" [var "y"], app "pair" [var "y", var "y"])⟩,
    ⟨"declared-fact", factProgram, plusStep, (app "+" [int 1, int 2], int 3)⟩,
    ⟨"refuse-undeclared-fact", factProgram, plusStep, (app "+" [int 1, int 2], int 4)⟩,
    ⟨"refuse-no-builtin-execution", [], plusStep, (app "+" [int 1, int 2], int 3)⟩ ]

/-! ## Theory scoping of sealed theorems -/

def atomA : Atom := sym "A"
def atomB : Atom := sym "B"
def atomC : Atom := sym "C"
def equationAB : Atom := Atom.equality atomA atomB
def equationBC : Atom := Atom.equality atomB atomC
def theoryAB : List Atom := [equationAB]
def theoryBC : List Atom := [equationBC]
def theoryABC : List Atom := [equationAB, equationBC]

def fromAB : Script := .step (.refl theoryAB atomA) ⟨equationAB, 0⟩ [] []

def theoryControls : List Control :=
  [ scriptControl "theory-step" fromAB,
    scriptControl "theory-refuse-foreign-step" (.step fromAB ⟨equationBC, 0⟩ [] []),
    scriptControl "theory-refuse-mixed-trans"
      (.trans fromAB (.step (.refl theoryBC atomB) ⟨equationBC, 0⟩ [] [])),
    scriptControl "theory-weakened-step" (.step (.weaken fromAB theoryABC) ⟨equationBC, 0⟩ [] []),
    scriptControl "theory-weakened-trans"
      (.trans (.weaken fromAB theoryABC) (.weaken (.step (.refl theoryBC atomB) ⟨equationBC, 0⟩ [] []) theoryABC)),
    scriptControl "theory-refuse-narrowing-weaken" (.weaken (.refl theoryABC atomA) theoryAB),
    scriptControl "theory-congr" (.congr [sym "f"] fromAB [atomC]) ]

example : (Script.step fromAB ⟨equationBC, 0⟩ [] []).run.map SealedTheorem.claim = none := by decide
example : (Script.step (.weaken fromAB theoryABC) ⟨equationBC, 0⟩ [] []).run.map SealedTheorem.claim =
    some (atomA, atomC) := by decide

def controls : List Control :=
  checkCases.map CheckCase.control ++
  [ hygienicControl "refuse-capture-hygienic" captureProgram captured
      (app "f" [var "y"], app "pair" [var "y", var "y"]),
    hygienicControl "renamed-apart-hygienic" captureProgram renamedApart
      (app "f" [var "y"], app "pair" [var "y", var "y1"]),
    sealedControl "sealed-inc-inner" incProgram (inc (inc zero)) incInner,
    sealedControl "sealed-inc-outer" incProgram (inc (inc zero)) incOuter,
    sealedControl "sealed-coin-heads-1" coinProgram coin [⟨⟨coinHeads, 1⟩, [], []⟩],
    sealedControl "sealed-refuse-coin-heads-2" coinProgram coin [⟨⟨coinHeads, 2⟩, [], []⟩],
    sealedControl "sealed-refuse-wrong-substitution" incProgram (inc (inc zero))
      [⟨incCite, [1], [("x", succ zero)]⟩],
    sealedControl "sealed-refuse-forged-citation" incProgram (inc zero)
      [⟨⟨forgedEquation, 0⟩, [], [("x", zero)]⟩],
    recordedControl "recorded-inc-inner" incProgram (inc (inc zero)) (succ (succ zero)) incInner,
    recordedControl "recorded-inc-three" incProgram (inc (inc (inc zero))) (succ (succ (succ zero)))
      incThree,
    mintControl "mint-inc-term" incProgram incTerm incClaim,
    mintControl "mint-refuse-wrong-target" incProgram incTerm (inc (inc zero), succ zero) ] ++
  theoryControls

/-- The same certificate checks with the certificate held as space atoms. -/
def spaceControlText (case_ : CheckCase) : String :=
  certificateFacts ("ctl-" ++ case_.name) case_.certificate ++
  "!(ek:control ctl-" ++ case_.name ++ " (eks:check " ++ programText case_.program ++ " &self ctl-" ++
    case_.name ++ " " ++ claimText case_.claim ++ ") " ++
    verdictText (check case_.program case_.certificate case_.claim) ++ ")\n"

/-- A derivation recorded into the space and then checked there: the
recorded log is the space form of its certificate. -/
def spaceRecordedText (name : String) (program : List Atom) (source target : Atom)
    (steps : List StepData) : String :=
  let bindings := steps.zipIdx.map fun (step, index) =>
    "((eks:recorded $s" ++ toString (index + 1) ++ " $t" ++ toString (index + 1) ++ ") (eks:rec-step $s" ++
      toString index ++ " $t" ++ toString index ++ " " ++ citationText step.citation ++ " " ++
      natListText step.path ++ " " ++ bindingsText step.bindings ++ "))"
  "!(ek:control ctl-rec-" ++ name ++ " (let* (((eks:recorded $s0 $t0) (eks:rec-refl (eks:rec-open &self " ++
    programText program ++ ") " ++ atomText source ++ ")) " ++ " ".intercalate bindings ++ " ($name (eks:rec-close $s" ++
    toString steps.length ++ " $t" ++ toString steps.length ++ "))) (eks:check " ++ programText program ++
    " &self $name " ++ claimText (source, target) ++ ")) " ++
    verdictText (replay program source steps == some target) ++ ")\n"

def spaceControlsText : String :=
  "; Generated by Mettapedia.Languages.MeTTa.EquationKernel.Controls; do not edit.\n" ++
  "; The check controls with each certificate held as atoms of the space.\n" ++
  "(= (ek:control $name $value $expected) (if (== $value $expected) (ek:pass $name) (ek:FAIL $name $value)))\n" ++
  String.join (checkCases.map spaceControlText) ++
  spaceRecordedText "inc-inner" incProgram (inc (inc zero)) (succ (succ zero)) incInner ++
  spaceRecordedText "inc-three" incProgram (inc (inc (inc zero))) (succ (succ (succ zero))) incThree ++
  spaceRecordedText "coin-heads-1" coinProgram coin (sym "heads") [⟨⟨coinHeads, 1⟩, [], []⟩]

def controlLine (control : Control) : String :=
  "!(ek:control ctl-" ++ control.name ++ " " ++ control.expression ++ " " ++ control.expected ++ ")"

def controlsText : String :=
  "; Generated by Mettapedia.Languages.MeTTa.EquationKernel.Controls; do not edit.\n" ++
  "; Each line prints (ek:pass ctl-name) or (ek:FAIL ctl-name value).\n" ++
  "(= (ek:control $name $value $expected) (if (== $value $expected) (ek:pass $name) (ek:FAIL $name $value)))\n" ++
  "\n".intercalate (controls.map controlLine) ++ "\n"

/-- The number of controls and how many expect acceptance. -/
example : controls.length = 46 := by decide
example : checkCases.length = 27 := by decide

/-! ## Compressed steps

A compressed step supplies its citation, position and right-only bindings;
the left-side bindings are computed. Omitting a right-only binding leaves the
variable's own name, which identifies it with a subject variable of the same
name: the core judgment accepts that instance and the hygienic check refuses
it. -/

def compressedControl (name : String) (program : List Atom) (claim : Claim) (citation : Citation)
    (path : List Nat) (extra : Bindings) : Control :=
  ⟨name, "(ek:mstep-claim " ++ programText program ++ " (ek:some " ++ claimText claim ++ ") " ++
    citationText citation ++ " " ++ natListText path ++ " " ++ bindingsText extra ++ ")",
    claimOption (compressedClaim? program [claim] 0 citation path extra)⟩

example : compressedClaim? incProgram [(inc (inc zero), inc (inc zero))] 0 incCite [1] [] =
    some (inc (inc zero), inc (succ zero)) := by decide

def compressedControls : List Control :=
  [ compressedControl "compressed-inc-inner" incProgram (inc (inc zero), inc (inc zero)) incCite [1] [],
    compressedControl "compressed-inc-root" incProgram (inc (inc zero), inc (succ zero)) incCite [] [],
    compressedControl "compressed-renamed-apart" captureProgram (app "f" [var "y"], app "f" [var "y"])
      ⟨captureEquation, 0⟩ [] [("y", var "y1")],
    compressedControl "compressed-omitted-right-only" captureProgram (app "f" [var "y"], app "f" [var "y"])
      ⟨captureEquation, 0⟩ [] [],
    compressedControl "compressed-refuse-wrong-site" incProgram (inc (inc zero), inc (inc zero)) incCite [0] [],
    compressedControl "compressed-refuse-missing-copy" coinProgram (coin, coin) ⟨coinHeads, 2⟩ [] [],
    compressedControl "compressed-coin-heads-1" coinProgram (coin, coin) ⟨coinHeads, 1⟩ [] [],
    compressedControl "compressed-refuse-forged-citation" incProgram (inc zero, inc zero)
      ⟨forgedEquation, 0⟩ [] [] ]

/-- A step whose site is a pattern with one hole variable. -/
def contextControl (name : String) (program : List Atom) (claim : Claim) (citation : Citation)
    (pattern : Atom) (hole : String) (extra : Bindings) : Control :=
  ⟨name, "(ek:cstep-claim " ++ programText program ++ " (ek:some " ++ claimText claim ++ ") " ++
    citationText citation ++ " " ++ atomText pattern ++ " " ++ quoteString hole ++ " " ++
    bindingsText extra ++ ")",
    claimOption (contextClaim? program [claim] 0 citation pattern hole extra)⟩

def pairAtom (first second : Atom) : Atom := app "pair" [first, second]

example : contextClaim? incProgram [(pairAtom (inc zero) (sym "W"), pairAtom (inc zero) (sym "W"))] 0 incCite
    (pairAtom (var "h") (var "k")) "h" [] =
    some (pairAtom (inc zero) (sym "W"), pairAtom (succ zero) (sym "W")) := by decide

def contextControls : List Control :=
  [ contextControl "site-inner" incProgram (inc (inc zero), inc (inc zero)) incCite (inc (var "h")) "h" [],
    contextControl "site-root" incProgram (inc (inc zero), inc (succ zero)) incCite (var "h") "h" [],
    contextControl "site-kept-argument-abstracted" incProgram
      (pairAtom (inc zero) (sym "W"), pairAtom (inc zero) (sym "W")) incCite (pairAtom (var "h") (var "k")) "h" [],
    contextControl "site-refuse-hole-twice" incProgram
      (pairAtom (inc zero) (inc zero), pairAtom (inc zero) (inc zero)) incCite (pairAtom (var "h") (var "h")) "h" [],
    contextControl "site-refuse-pattern-mismatch" incProgram (inc (inc zero), inc (inc zero)) incCite
      (succ (var "h")) "h" [],
    contextControl "site-refuse-focus-mismatch" incProgram (inc (succ zero), inc (succ zero)) incCite
      (inc (var "h")) "h" [],
    contextControl "site-renamed-apart" captureProgram (app "f" [var "y"], app "f" [var "y"])
      ⟨captureEquation, 0⟩ (var "h") "h" [("y", var "y1")] ]

def compressedControlsText : String :=
  "; Generated by Mettapedia.Languages.MeTTa.EquationKernel.Controls; do not edit.\n" ++
  "; Computed matching: compressed steps and sites given as patterns.\n" ++
  "(= (ek:control $name $value $expected) (if (== $value $expected) (ek:pass $name) (ek:FAIL $name $value)))\n" ++
  "\n".intercalate ((compressedControls ++ contextControls).map controlLine) ++ "\n"

/-! ## A mutation corpus

Each base certificate is perturbed one field at a time: references, stored
copies, cited equations, positions, bindings, kept arguments, the root and
the claim. The expected verdict of every mutant is computed by the Lean
checker, so the MeTTa checker is compared with it on accepted and refused
certificates alike. -/

def wrapAtom (atom : Atom) : Atom := app "wrap" [atom]

def mutateRow : Row → List Row
  | .refl atom => [.refl (wrapAtom atom), .refl zero]
  | .step prior citation path bindings =>
      [.step (prior + 1) citation path bindings,
        .step prior ⟨citation.equation, citation.copy + 1⟩ path bindings,
        .step prior ⟨forgedEquation, citation.copy⟩ path bindings,
        .step prior ⟨wrapAtom citation.equation, citation.copy⟩ path bindings,
        .step prior citation (path ++ [0]) bindings,
        .step prior citation (path.map (· + 1)) bindings,
        .step prior citation path.tail bindings,
        .step prior citation (0 :: path) bindings,
        .step prior citation path (bindings.map fun (name, value) => (name, wrapAtom value)),
        .step prior citation path (bindings.map fun (name, value) => (name ++ "'", value)),
        .step prior citation path [],
        .step prior citation path (("x", zero) :: bindings)]
  | .congr left inner right =>
      [.congr left (inner + 1) right, .congr (sym "extra" :: left) inner right,
        .congr left inner (sym "extra" :: right), .congr right inner left]
  | .trans first second =>
      [.trans second first, .trans (first + 1) second, .trans first (second + 1), .trans first first]

def certificateMutants (certificate : Certificate) : List Certificate :=
  (certificate.rows.zipIdx.flatMap fun (row, index) =>
      (mutateRow row).map fun mutated => ⟨certificate.rows.set index mutated, certificate.root⟩) ++
    [⟨certificate.rows, certificate.root + 1⟩, ⟨certificate.rows, certificate.root - 1⟩,
      ⟨certificate.rows.dropLast, certificate.root⟩, ⟨certificate.rows ++ [.refl zero], certificate.root⟩,
      ⟨certificate.rows.reverse, certificate.root⟩]

def claimMutants (claim : Claim) : List Claim :=
  [claim, (claim.1, wrapAtom claim.2), (wrapAtom claim.1, claim.2), (claim.2, claim.1)]

structure Base where
  name : String
  program : List Atom
  certificate : Certificate
  claim : Claim

def bases : List Base :=
  [ ⟨"inner", incProgram, traceCertificate (inc (inc zero)) incInner, incClaim⟩,
    ⟨"outer", incProgram, traceCertificate (inc (inc zero)) incOuter, incClaim⟩,
    ⟨"term", incProgram, incTerm, incClaim⟩,
    ⟨"three", incProgram, traceCertificate (inc (inc (inc zero))) incThree,
      (inc (inc (inc zero)), succ (succ (succ zero)))⟩,
    ⟨"shared", incProgram, incShared, pairClaim⟩,
    ⟨"coin", coinProgram, coinStep coinHeads 1, (coin, sym "heads")⟩,
    ⟨"capture", captureProgram, renamedApart, (app "f" [var "y"], app "pair" [var "y", var "y1"])⟩ ]

def mutantControls : List Control :=
  bases.flatMap fun base =>
    let certificates := base.certificate :: certificateMutants base.certificate
    (certificates.zipIdx.flatMap fun (certificate, index) =>
      (claimMutants base.claim).zipIdx.map fun (claim, claimIndex) =>
        checkControl (base.name ++ "-" ++ toString index ++ "-" ++ toString claimIndex) base.program
          certificate claim) ++
    (certificates.zipIdx.map fun (certificate, index) =>
      hygienicControl (base.name ++ "-hygienic-" ++ toString index) base.program certificate base.claim)

def mutantsText : String :=
  "; Generated by Mettapedia.Languages.MeTTa.EquationKernel.Controls; do not edit.\n" ++
  "; Mutants of the worked certificates, with verdicts computed by the Lean checker.\n" ++
  "(= (ek:control $name $value $expected) (if (== $value $expected) (ek:pass $name) (ek:FAIL $name $value)))\n" ++
  "\n".intercalate (mutantControls.map controlLine) ++ "\n"

/-! ## Axiom audit of the principal theorems -/

#print axioms derives_iff_reaches
#print axioms check_exact
#print axioms exists_check_iff_reaches
#print axioms check_seq
#print axioms check_congr
#print axioms check_both
#print axioms replay_append
#print axioms check_trace_iff
#print axioms check_perm
#print axioms accepted_citations_length
#print axioms occurrences_perm
#print axioms reaches_alphaVariant
#print axioms fresh_most_general
#print axioms checkFresh_exact
#print axioms narrowing_step
#print axioms no_unifier_without_renaming
#print axioms unifier_after_renaming
#print axioms Step.substitute
#print axioms mint_isSome_iff_check
#print axioms Session.check_certificate
#print axioms Session.step_claim
#print axioms nonempty_theorem_iff_exists_check
#print axioms nonempty_theorem_iff_reaches
#print axioms inc_reaches
#print axioms matchAtom_complete
#print axioms compressed_claim_sound
#print axioms compressed_step_complete
#print axioms contextClaim_sound
#print axioms contextClaim_complete
#print axioms check_eq_checkReference
#print axioms exists_trace_iff_reaches
#print axioms spaceCheck_sound
#print axioms spaceCheck_complete
#print axioms spaceCheck_table
#print axioms spaceCheck_table_restored
#print axioms spaceCheck_retry
#print axioms SealedTheorem.sound
#print axioms SealedTheorem.trans_theory
#print axioms SealedTheorem.weaken_theory
#print axioms nonempty_sealed_iff_exists_check

end Mettapedia.Languages.MeTTa.EquationKernel.Controls

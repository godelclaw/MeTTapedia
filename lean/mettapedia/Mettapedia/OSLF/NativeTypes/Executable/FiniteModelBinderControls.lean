import Mettapedia.OSLF.Framework.FiniteModelSearch

/-!
# Controls: finite-model certificates for λ, name passing and rho

Verdicts are about runs through object states (`ObjectState`: no explicit substitution, closed
collections, every bound variable in scope). Each language has a certificate written by hand and one
found by the cell-by-cell finder (`findCells`), which the kernel checks.

- **λ with β at the root** (`beta`: `App (Lam (λ. body)) arg ~> body[arg]`). An abstraction denotes
  the function from the value of its variable to the value of its body; a term is clean when it
  cannot produce `Err`. Every β step goes down, by the substitution lemma, so a clean term never
  reaches `Err` (`clean_never_errs`); `App (Lam (λ. Err)) Ok` reaches it in one step. A binder for
  two variables at once (`letTwo`) is checked the same way (`clean_let_never_errs`).
- **Name passing** (`comm`: `Out x y | In x (λ. P) ~> P[y]`). Names are public or secret; a process
  is safe when it never sends the secret on the public channel. A forwarder from the secret channel
  to the secret channel stays safe (`secret_forwarder_safe`), also inside a parallel composition whose
  components may step (`secret_forwarder_safe_in_context`); a forwarder to the public channel leaks in
  one step. A composition that turns a leak into a safe process fails the site check
  (`broken_sites`).
- **Rho with parallel composition as a bag** (`rhoComm`: `{x!(Q) | for (y <- x) P | rest} ~>
  {P[@Q/y] | rest}`). The output and the input meet anywhere in the bag, which is matched modulo
  permutation; the bag operation is a left-commutative join. A process that sends `0` and runs what it
  receives stays clean (`rho_safe_stays_clean`); sending `Err` instead does not. A join that is not
  left-commutative fails validity (`ordered_not_valid`).
- **Vectors** (`[x, y | rest] ~> [x | rest]`). Each collection kind has its own join; a vector's may
  keep its first argument, which no left-commutative join could, so dropping second elements never puts
  `Err` first (`head_stays_ok`).
- **Found by search.** Over two values, the finder assigns the cells of constructors, abstractions and
  bag operations that the check evaluates: it proves that the λ term never reaches `Err`
  (`twice_never_errs_by_search`), that the safe rho process never holds `Err` at the top of its bag
  (`rho_safe_never_holds_err`, a goal with a rest variable), and that the secret forwarder never leaks,
  at the root and anywhere in a top-level composition (`secret_forwarder_safe_by_search`,
  `secret_forwarder_never_leaks_in_context`), where the hand-written model needs four values. On the
  terms that do reach their goals it finds nothing.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Executable.FiniteModelControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.NonrecursiveReduction (rootReducts)
open Mettapedia.OSLF.Framework.FiniteModels
open Mettapedia.OSLF.Framework.BackwardSearch
open Mettapedia.OSLF.Framework.HerbrandBridge (languageSpan Goal)

/-! ## λ with β at the root -/

def termSort : TypeExpr := .base "Term"

def lambdaTerms : List GrammarRule := [
  { label := "Lam", category := "Term", params := [.abstraction "body" termSort],
    syntaxPattern := [.terminal "lam", .nonTerminal "body"] },
  { label := "App", category := "Term", params := [.simple "function" termSort, .simple "argument" termSort],
    syntaxPattern := [.nonTerminal "function", .nonTerminal "argument"] },
  { label := "Ok", category := "Term", params := [], syntaxPattern := [.terminal "ok"] },
  { label := "Err", category := "Term", params := [], syntaxPattern := [.terminal "err"] }]

def beta : RewriteRule :=
  { name := "Beta", typeContext := [("argument", termSort)], premises := [],
    left := .apply "App" [.apply "Lam" [.lambda none (.fvar "body")], .fvar "argument"],
    right := .subst (.fvar "body") (.fvar "argument") }

def lambdaCalculus : LanguageDef :=
  { name := "Lambda", types := ["Term"], terms := lambdaTerms, equations := [], rewrites := [beta] }

def lam (body : Pattern) : Pattern := .apply "Lam" [.lambda none body]
def app (function argument : Pattern) : Pattern := .apply "App" [function, argument]
def ok : Pattern := .apply "Ok" []
def err : Pattern := .apply "Err" []

inductive Cleanness where
  | clean
  | dirty
  deriving DecidableEq, Repr

/-- A term is clean when it cannot produce `Err`; an abstraction is clean when its body is clean on a
clean argument. -/
def cleanModel : FiniteModel Cleanness where
  junk := .dirty
  lam body := if body .clean == .clean then .clean else .dirty
  operation
    | "Lam", [body] => body
    | "App", [function, argument] => if function == .clean && argument == .clean then .clean else .dirty
    | "Ok", [] => .clean
    | _, _ => .dirty

/-- A dirty term may become clean; a clean one stays clean. -/
def cleanCertificate : Certificate Cleanness where
  elements := [.clean, .dirty]
  complete entry := by cases entry <;> simp
  model := cleanModel
  below first second := first == second || first == .dirty

def isDirty (entry : Cleanness) : Bool := entry == .dirty

/-- `(λx. (λy. y) x) ok`: two β steps to `ok`. -/
def twice : Pattern := app (lam (app (lam (.bvar 0)) (.bvar 0))) ok

#guard rootReducts lambdaCalculus twice == [app (lam (.bvar 0)) ok]
#guard rootReducts lambdaCalculus (app (lam (.bvar 0)) ok) == [ok]
#guard rootReducts lambdaCalculus (app (lam err) ok) == [err]

/-- **A clean term never reaches `Err`.** -/
theorem clean_never_errs : ¬ Reaches (between (languageSpan lambdaCalculus) ObjectState) (Goal [err]) twice :=
  cleanCertificate.cannotReach_of_check (accept := isDirty) (by decide +kernel)

-- `(λx. Err) ok` reaches `Err`; its value is dirty, and the certificate is silent.
#guard !cleanCertificate.cannotReach lambdaCalculus [err] isDirty (app (lam err) ok)

/-! ### Two variables bound at once -/

/-- `Let2 a b (λλ. body) ~> body[a, b]`: one binder for two variables, eliminated by two explicit
substitutions. -/
def letTwo : RewriteRule :=
  { name := "LetTwo", typeContext := [("first", termSort), ("second", termSort)], premises := [],
    left := .apply "Let2" [.fvar "first", .fvar "second", .multiLambda 2 [] (.fvar "body")],
    right := .subst (.subst (.fvar "body") (.fvar "second")) (.fvar "first") }

def letCalculus : LanguageDef :=
  { name := "LetTwo", types := ["Term"], terms := lambdaTerms ++ [
      { label := "Let2", category := "Term",
        params := [.simple "first" termSort, .simple "second" termSort,
          .multiAbstractionNamed ["x", "y"] "body" termSort],
        syntaxPattern := [.terminal "let", .nonTerminal "first", .nonTerminal "second", .nonTerminal "body"] }],
    equations := [], rewrites := [letTwo] }

def letTwoOf (first second body : Pattern) : Pattern := .apply "Let2" [first, second, .multiLambda 2 [] body]

/-- A two-variable abstraction is clean when its body is clean on clean arguments. -/
def letCleanModel : FiniteModel Cleanness :=
  { cleanModel with
    lamMulti := fun _ body => if body (fun _ => .clean) == .clean then .clean else .dirty
    operation := fun label arguments => match label, arguments with
      | "Let2", [first, second, body] =>
          if first == .clean && second == .clean && body == .clean then .clean else .dirty
      | label, arguments => cleanModel.operation label arguments }

def letCertificate : Certificate Cleanness := { cleanCertificate with model := letCleanModel }

-- `let ok ok (λx y. App y x)` steps to `App ok ok`, its body with both variables replaced.
#guard rootReducts letCalculus (letTwoOf ok ok (app (.bvar 0) (.bvar 1))) == [app ok ok]
#guard rootReducts letCalculus (letTwoOf ok ok err) == [err]

/-- **A clean two-variable let never reaches `Err`.** -/
theorem clean_let_never_errs :
    ¬ Reaches (between (languageSpan letCalculus) ObjectState) (Goal [err]) (letTwoOf ok ok (app (.bvar 0) (.bvar 1))) :=
  letCertificate.cannotReach_of_check (accept := isDirty) (by decide +kernel)

#guard !letCertificate.cannotReach letCalculus [err] isDirty (letTwoOf ok ok err)

/-! ## Name passing -/

def nameSort : TypeExpr := .base "Name"
def procSort : TypeExpr := .base "Proc"

def piTerms : List GrammarRule := [
  { label := "Nil", category := "Proc", params := [], syntaxPattern := [.terminal "0"] },
  { label := "Par", category := "Proc", params := [.simple "left" procSort, .simple "right" procSort],
    syntaxPattern := [.nonTerminal "left", .terminal "|", .nonTerminal "right"] },
  { label := "Out", category := "Proc", params := [.simple "channel" nameSort, .simple "payload" nameSort],
    syntaxPattern := [.nonTerminal "channel", .terminal "!", .nonTerminal "payload"] },
  { label := "In", category := "Proc", params := [.simple "channel" nameSort, .abstraction "body" procSort],
    syntaxPattern := [.nonTerminal "channel", .terminal "?", .nonTerminal "body"] },
  { label := "Pub", category := "Name", params := [], syntaxPattern := [.terminal "pub"] },
  { label := "Sec", category := "Name", params := [], syntaxPattern := [.terminal "sec"] }]

def comm : RewriteRule :=
  { name := "Comm", typeContext := [("x", nameSort), ("y", nameSort)], premises := [],
    left := .apply "Par" [.apply "Out" [.fvar "x", .fvar "y"], .apply "In" [.fvar "x", .lambda none (.fvar "P")]],
    right := .subst (.fvar "P") (.fvar "y") }

def namePassing : LanguageDef :=
  { name := "NamePassing", types := ["Name", "Proc"], terms := piTerms, equations := [], rewrites := [comm] }

def par (left right : Pattern) : Pattern := .apply "Par" [left, right]
def send (channel payload : Pattern) : Pattern := .apply "Out" [channel, payload]
def receive (channel body : Pattern) : Pattern := .apply "In" [channel, .lambda none body]
def pub : Pattern := .apply "Pub" []
def sec : Pattern := .apply "Sec" []

inductive Secrecy where
  | publicName
  | secretName
  | safe
  | leak
  deriving DecidableEq, Repr

def isName (entry : Secrecy) : Bool := entry == .publicName || entry == .secretName

/-- A process is safe when it never sends the secret on the public channel; an input is safe when its
body is safe whichever name arrives. -/
def secrecyModel : FiniteModel Secrecy where
  junk := .leak
  lam body := if body .publicName == .safe && body .secretName == .safe then .safe else .leak
  operation
    | "Pub", [] => .publicName
    | "Sec", [] => .secretName
    | "Nil", [] => .safe
    | "Out", [channel, payload] =>
        if isName channel && isName payload && !(channel == .publicName && payload == .secretName) then .safe else .leak
    | "In", [channel, body] => if isName channel then body else .leak
    | "Par", [left, right] => if left == .safe && right == .safe then .safe else .leak
    | _, _ => .leak

/-- A leaking process may become safe; a safe one stays safe. -/
def secrecyCertificate : Certificate Secrecy where
  elements := [.publicName, .secretName, .safe, .leak]
  complete entry := by cases entry <;> simp
  model := secrecyModel
  below first second := first == second || first == .leak

def isLeak (entry : Secrecy) : Bool := entry == .leak

/-- Receive on the secret channel, forward on the secret channel. -/
def secretForwarder : Pattern := par (send sec sec) (receive sec (send sec (.bvar 0)))

/-- Receive on the secret channel, forward on the public channel. -/
def leakyForwarder : Pattern := par (send sec sec) (receive sec (send pub (.bvar 0)))

#guard rootReducts namePassing secretForwarder == [send sec sec]
#guard rootReducts namePassing leakyForwarder == [send pub sec]

/-- **The secret forwarder never sends the secret on the public channel.** -/
theorem secret_forwarder_safe :
    ¬ Reaches (between (languageSpan namePassing) ObjectState) (Goal [send pub sec]) secretForwarder :=
  secrecyCertificate.cannotReach_of_check (accept := isLeak) (by decide +kernel)

-- The leaky forwarder does send it; its value is a leak, and the certificate is silent.
#guard !secrecyCertificate.cannotReach namePassing [send pub sec] isLeak leakyForwarder

/-! ### Steps inside parallel composition -/

/-- Either side of a parallel composition may step. -/
def piSites : List Site := [("Par", 2, 0), ("Par", 2, 1)]

def nilProcess : Pattern := .apply "Nil" []

/-- **Inside a parallel composition, the secret forwarder still never leaks**: the step happens in
the left component, and the composition respects the preorder. -/
theorem secret_forwarder_safe_in_context :
    ¬ Reaches (between (contextSpan namePassing piSites) ObjectState) (Goal [send pub sec])
      (par secretForwarder nilProcess) :=
  secrecyCertificate.cannotReachInContexts_of_check (accept := isLeak) (by decide +kernel)

#guard !secrecyCertificate.cannotReachInContexts namePassing piSites [send pub sec] isLeak (par leakyForwarder nilProcess)

/-- A composition that turns a leak on its left into a safe process does not respect the preorder. -/
def brokenSecrecy : Certificate Secrecy :=
  { secrecyCertificate with
    model := { secrecyModel with
      operation := fun label arguments => match label, arguments with
        | "Par", [left, right] =>
            if left == .leak then .safe else if left == .safe && right == .safe then .safe else .leak
        | label, arguments => secrecyModel.operation label arguments } }

theorem broken_sites : brokenSecrecy.sitesCheck piSites = false := by decide +kernel

/-! ## Reflection: a rho calculus with parallel composition as a bag -/

def rhoTerms : List GrammarRule := [
  { label := "Nil", category := "Proc", params := [], syntaxPattern := [.terminal "0"] },
  { label := "Err", category := "Proc", params := [], syntaxPattern := [.terminal "err"] },
  { label := "Par", category := "Proc", params := [.simple "processes" (.collection .hashBag procSort)],
    syntaxPattern := [.nonTerminal "processes"] },
  { label := "Out", category := "Proc", params := [.simple "channel" nameSort, .simple "payload" procSort],
    syntaxPattern := [.nonTerminal "channel", .terminal "!", .nonTerminal "payload"] },
  { label := "In", category := "Proc", params := [.simple "channel" nameSort, .abstraction "body" procSort],
    syntaxPattern := [.terminal "for", .nonTerminal "channel", .nonTerminal "body"] },
  { label := "Drop", category := "Proc", params := [.simple "name" nameSort], syntaxPattern := [.terminal "*"] },
  { label := "Quote", category := "Name", params := [.simple "process" procSort], syntaxPattern := [.terminal "@"] }]

/-- `{x!(Q) | for (y <- x) P | rest} ~> {P[@Q/y] | rest}`: the output and the input meet anywhere in
the bag; the rest of the bag is carried along. -/
def rhoComm : RewriteRule :=
  { name := "Comm", typeContext := [("x", nameSort), ("Q", procSort)], premises := [],
    left := .collection .hashBag
      [.apply "Out" [.fvar "x", .fvar "Q"], .apply "In" [.fvar "x", .lambda none (.fvar "P")]] (some "rest"),
    right := .collection .hashBag [.subst (.fvar "P") (.apply "Quote" [.fvar "Q"])] (some "rest") }

def rhoCalculus : LanguageDef :=
  { name := "Rho", types := ["Name", "Proc"], terms := rhoTerms, equations := [], rewrites := [rhoComm] }

def bag (processes : List Pattern) : Pattern := .collection .hashBag processes none
def output (channel payload : Pattern) : Pattern := .apply "Out" [channel, payload]
def input (channel body : Pattern) : Pattern := .apply "In" [channel, .lambda none body]
def quote (process : Pattern) : Pattern := .apply "Quote" [process]
def drop (name : Pattern) : Pattern := .apply "Drop" [name]
def nilRho : Pattern := .apply "Nil" []
def errRho : Pattern := .apply "Err" []

/-- A process is clean when it cannot produce `Err`; a name is as clean as the process it quotes; an
input is clean when its body is clean on a clean name; a bag is clean when all its processes are. -/
def rhoModel : FiniteModel Cleanness where
  junk := .dirty
  lam body := if body .clean == .clean then .clean else .dirty
  collectionUnit _ := .clean
  collectionJoin _ first second := if first == .clean && second == .clean then .clean else .dirty
  operation
    | "Nil", [] => .clean
    | "Quote", [process] => process
    | "Drop", [name] => name
    | "Out", [_, payload] => payload
    | "In", [_, body] => body
    | _, _ => .dirty

def rhoCertificate : Certificate Cleanness := { cleanCertificate with model := rhoModel }

/-- Send `0` on `@0`, receive it and run it; a third process stays alongside. -/
def rhoSafe : Pattern := bag [output (quote nilRho) nilRho, input (quote nilRho) (drop (.bvar 0)), nilRho]

/-- Send `Err` on `@0`, receive it and run it. -/
def rhoLeaky : Pattern := bag [output (quote nilRho) errRho, input (quote nilRho) (drop (.bvar 0))]

#guard rootReducts rhoCalculus rhoSafe == [bag [drop (quote nilRho), nilRho]]
#guard rootReducts rhoCalculus rhoLeaky == [bag [drop (quote errRho)]]

/-- **The safe rho process never reaches a process that can produce `Err`**: the communication rule
goes down the preorder for every way the bag can be split. -/
theorem rho_safe_stays_clean :
    ¬ Reaches (between (languageSpan rhoCalculus) ObjectState)
      (fun reached => isDirty (value rhoModel reached) = true) rhoSafe :=
  rhoCertificate.cannotReachAccepted_of_check (by decide +kernel)

#guard !rhoCertificate.cannotReachAccepted rhoCalculus isDirty rhoLeaky

/-- A bag operation that is not left-commutative fails validity: bags are matched modulo permutation. -/
def orderedRho : Certificate Cleanness :=
  { rhoCertificate with model := { rhoModel with collectionJoin := fun _ first _ => first } }

theorem ordered_not_valid : orderedRho.valid rhoCalculus = false := by decide +kernel

/-! ## Vectors: an ordered collection with its own join -/

/-- `[x, y | rest] ~> [x | rest]`: drop the second element of a queue. -/
def dropSecond : RewriteRule :=
  { name := "DropSecond", typeContext := [], premises := [],
    left := .collection .vec [.fvar "x", .fvar "y"] (some "rest"),
    right := .collection .vec [.fvar "x"] (some "rest") }

def queues : LanguageDef :=
  { name := "Queues", types := ["Term"], terms := lambdaTerms, equations := [], rewrites := [dropSecond] }

def queue (items : List Pattern) : Pattern := .collection .vec items none

/-- A queue is as clean as its first element: the join of vectors keeps the first argument, which no
left-commutative join could. -/
def headModel : FiniteModel Cleanness :=
  { cleanModel with
    collectionUnit := fun _ => .clean
    collectionJoin := fun kind first rest =>
      if kind == .vec then first else if first == .clean && rest == .clean then .clean else .dirty }

def headCertificate : Certificate Cleanness := { cleanCertificate with model := headModel }

/-- Every queue whose first element is `Err`. -/
def errFirst : Pattern := .collection .vec [err] (some "rest")

#guard rootReducts queues (queue [ok, err, err]) == [queue [ok, err]]

/-- **Dropping second elements never puts `Err` first** in a queue that starts with `Ok`. -/
theorem head_stays_ok :
    ¬ Reaches (between (languageSpan queues) ObjectState) (Goal [errFirst]) (queue [ok, err, err]) :=
  headCertificate.cannotReach_of_check (accept := isDirty) (by decide +kernel)

-- A queue whose join treats all elements alike sees the `Err` behind the head: the certificate is
-- silent.
#guard !({ cleanCertificate with model := rhoModel } : Certificate Cleanness).cannotReach queues [errFirst] isDirty
  (queue [ok, err, err])

/-! ## Certificates found by search -/

def twoValues : List (Fin 2) := [0, 1]
theorem twoValues_complete (entry : Fin 2) : entry ∈ twoValues := by fin_cases entry <;> simp [twoValues]

/-! ### λ -/

def lambdaSignature : Signature :=
  [.operation "Lam" 1, .operation "App" 2, .operation "Ok" 0, .operation "Err" 0, .abstraction]

/-- The cells the finder assigns for `twice`. -/
def lambdaCells : Cells (Fin 2) :=
  [((4, 3), 1), ((1, 3), 1), ((1, 1), 1), ((0, 1), 1), ((4, 1), 1), ((4, 0), 0), ((3, 0), 1), ((2, 0), 0),
    ((1, 2), 1), ((1, 0), 0), ((0, 0), 0), ((4, 2), 0)]

#guard findCells twoValues 1 lambdaSignature lambdaCalculus [] [err] twice == some lambdaCells

def lambdaSearched : Certificate (Fin 2) :=
  Certificate.ofCells twoValues twoValues_complete 1 lambdaSignature lambdaCells lambdaCalculus

/-- **No hand-written model**: the finder's cells prove that `twice` never reaches `Err`. -/
theorem twice_never_errs_by_search :
    ¬ Reaches (between (languageSpan lambdaCalculus) ObjectState) (Goal [err]) twice :=
  lambdaSearched.cannotReach_of_check (accept := lambdaSearched.goalAccept [err]) (by decide +kernel)

-- `(λx. Err) ok` reaches `Err`: the finder finds nothing.
#guard findCells twoValues 1 lambdaSignature lambdaCalculus [] [err] (app (lam err) ok) == none

/-! ### Rho, with a goal that has a rest variable -/

def rhoSignature : Signature :=
  [.operation "Nil" 0, .operation "Err" 0, .operation "Out" 2, .operation "In" 2, .operation "Drop" 1,
    .operation "Quote" 1, .abstraction, .collectionUnit .hashBag, .collectionJoin .hashBag]

/-- Every bag with `Err` at its top level, whatever else it holds. -/
def errInBag : Pattern := .collection .hashBag [errRho] (some "rest")

def rhoCells : Cells (Fin 2) :=
  [((2, 3), 0), ((3, 3), 1), ((3, 1), 0), ((2, 1), 0), ((5, 1), 0), ((2, 2), 0), ((6, 3), 1), ((6, 2), 0),
    ((3, 2), 1), ((6, 1), 1), ((8, 2), 1), ((8, 3), 1), ((8, 1), 1), ((1, 0), 1), ((8, 0), 0), ((7, 0), 0),
    ((3, 0), 0), ((6, 0), 0), ((4, 1), 0), ((4, 0), 0), ((2, 0), 0), ((5, 0), 0), ((0, 0), 0)]

#guard findCells twoValues 1 rhoSignature rhoCalculus [] [errInBag] rhoSafe == some rhoCells

def rhoSearched : Certificate (Fin 2) :=
  Certificate.ofCells twoValues twoValues_complete 1 rhoSignature rhoCells rhoCalculus

/-- **The safe rho process never holds `Err` at the top of its bag.** -/
theorem rho_safe_never_holds_err :
    ¬ Reaches (between (languageSpan rhoCalculus) ObjectState) (Goal [errInBag]) rhoSafe :=
  rhoSearched.cannotReach_of_check (accept := rhoSearched.goalAccept [errInBag]) (by decide +kernel)

/-- Receive on `@0` and continue as `Err`: one step puts `Err` at the top of the bag. -/
def rhoErrs : Pattern := bag [output (quote nilRho) nilRho, input (quote nilRho) errRho]

#guard rootReducts rhoCalculus rhoErrs == [bag [errRho]]
#guard findCells twoValues 1 rhoSignature rhoCalculus [] [errInBag] rhoErrs == none

/-! ### Name passing -/

def piSignature : Signature :=
  [.operation "Nil" 0, .operation "Par" 2, .operation "Out" 2, .operation "In" 2, .operation "Pub" 0,
    .operation "Sec" 0, .abstraction]

def piCells : Cells (Fin 2) :=
  [((2, 3), 0), ((1, 3), 1), ((3, 3), 1), ((1, 1), 0), ((3, 1), 0), ((6, 3), 1), ((6, 2), 1), ((1, 2), 1),
    ((3, 2), 1), ((6, 1), 1), ((2, 1), 1), ((4, 0), 1), ((1, 0), 0), ((3, 0), 0), ((6, 0), 0), ((2, 2), 0),
    ((2, 0), 0), ((5, 0), 0)]

#guard findCells twoValues 1 piSignature namePassing [] [send pub sec] secretForwarder == some piCells

def piSearched : Certificate (Fin 2) :=
  Certificate.ofCells twoValues twoValues_complete 1 piSignature piCells namePassing

/-- **The secret forwarder never leaks**, with two values where the hand-written model has four. -/
theorem secret_forwarder_safe_by_search :
    ¬ Reaches (between (languageSpan namePassing) ObjectState) (Goal [send pub sec]) secretForwarder :=
  piSearched.cannotReach_of_check (accept := piSearched.goalAccept [send pub sec]) (by decide +kernel)

#guard findCells twoValues 1 piSignature namePassing [] [send pub sec] leakyForwarder == none

/-- A leak at the top, or in either component of a top-level composition. -/
def leakNearTop : List Pattern :=
  [send pub sec, par (send pub sec) (.fvar "other"), par (.fvar "other") (send pub sec)]

def piContextCells : Cells (Fin 2) :=
  [((2, 3), 1), ((3, 3), 0), ((3, 1), 0), ((6, 3), 1), ((6, 2), 1), ((3, 2), 1), ((6, 1), 1), ((1, 2), 1),
    ((1, 3), 1), ((1, 1), 1), ((2, 1), 1), ((4, 0), 1), ((0, 0), 0), ((1, 0), 0), ((3, 0), 0), ((6, 0), 0),
    ((2, 2), 0), ((2, 0), 0), ((5, 0), 0)]

#guard findCells twoValues 1 piSignature namePassing piSites leakNearTop (par secretForwarder nilProcess) ==
  some piContextCells

def piContextSearched : Certificate (Fin 2) :=
  Certificate.ofCells twoValues twoValues_complete 1 piSignature piContextCells namePassing piSites

/-- **Inside a parallel composition whose components step, the secret forwarder never leaks**, at the top
or in either component. -/
theorem secret_forwarder_never_leaks_in_context :
    ¬ Reaches (between (contextSpan namePassing piSites) ObjectState) (Goal leakNearTop)
      (par secretForwarder nilProcess) :=
  piContextSearched.cannotReachInContexts_of_check (accept := piContextSearched.goalAccept leakNearTop)
    (by decide +kernel)

-- The leaky forwarder leaks inside the composition: the finder finds nothing.
#guard findCells twoValues 1 piSignature namePassing piSites leakNearTop (par leakyForwarder nilProcess) == none

end Mettapedia.OSLF.NativeTypes.Executable.FiniteModelControls

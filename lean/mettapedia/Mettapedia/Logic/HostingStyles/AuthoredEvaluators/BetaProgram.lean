import Mettapedia.Logic.HostingStyles.AuthoredEvaluators.ClimbProgram
import Mettapedia.Logic.HostingStyles.AuthoredEvaluators.BetaSpec

/-!
# One step of beta at every position is authored

`betaProgram` is an equation program of seventy-six equations: those of
contraction and sixty-one of its own.  It answers the run premise without
reading the space.  It contracts the subject, reads it back as a λΠ term,
lists the reducts of that term by one step of beta at any position, with
substitution and lifting on de Bruijn indices, and writes them as atoms.

* **On every relation and every list of inputs the program returns the
  answers of `betaAnswers`** (`betaPremise_computes`), so it halts on every
  query and its evaluator is authored (`betaAuthored`).
* Its evaluator respects the static equivalence
  (`betaAuthored_respectsStatics`): the program contracts what it reads.
* **Through one run rewrite it hosts the pure λΠ-calculus, with beta at every
  position** (`betaAuthored_hosts`): a term is hosted as the run of its atom
  at the empty space.
* That theory branches without bound along one reduction, so the matching
  evaluator does not host it, and no weak evaluator does
  (`beta_everywhere_authored`).

The pure λΠ-calculus is the theory of the rule-table evaluator at the empty
table.  With a table of declared rules, a step also rewrites by an instance of
a rule at any position; the program for that is not written here.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AuthoredEvaluators

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
open Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction (encodeOption encoded_comparison)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.Dedukti (Theory rewritingTheory)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Logic.HostingStyles.PrimeCandidate

/-! ## The data of the program -/

/-- **A number, as strokes.** -/
def tally : Nat → Term
  | 0 => .sym "Z"
  | count + 1 => call "S" [tally count]

theorem tally_injective : Function.Injective tally := by
  intro first
  induction first with
  | zero =>
      intro second same
      cases second with
      | zero => rfl
      | succ second => simp [tally, call] at same
  | succ first ih =>
      intro second same
      cases second with
      | zero => simp [tally, call] at same
      | succ second =>
          simp only [tally, call, Term.expr.injEq, List.cons.injEq, and_true, true_and] at same
          rw [ih same]

/-- **Positive**: two, as strokes. -/
theorem tally_two : tally 2 = call "S" [call "S" [.sym "Z"]] := rfl

/-- **Negative**: strokes are no numeral of the engine. -/
theorem tally_ne_natural (count : Nat) : tally count ≠ natural count := by
  cases count <;> simp [tally, call, natural]

/-- **What an atom is read back as, as data.** -/
def encodeAtomTerm : AtomTerm → Term
  | .atom raw => call "Atom" [encodePattern raw]
  | .var index => call "Var" [tally index]
  | .pi domain body => call "Pi" [encodeAtomTerm domain, encodeAtomTerm body]
  | .lam domain body => call "Lam" [encodeAtomTerm domain, encodeAtomTerm body]
  | .app function argument => call "App" [encodeAtomTerm function, encodeAtomTerm argument]

/-- A list of them, as cells. -/
def encodeAtomTerms (terms : List AtomTerm) : Term := cells (terms.map encodeAtomTerm)

/-- The two arguments of a pattern, as data. -/
def encodeTwo (parts : Option (Pattern × Pattern)) : Term :=
  encodeOption (fun both : Pattern × Pattern => pair (encodePattern both.1) (encodePattern both.2))
    parts

/-- The two parts of a payload, as data. -/
def encodeParts (parts : Option (AtomTerm × AtomTerm)) : Term :=
  encodeOption
    (fun both : AtomTerm × AtomTerm => pair (encodeAtomTerm both.1) (encodeAtomTerm both.2)) parts

/-- **Positive**: two arguments, as data. -/
theorem encodeTwo_some (left right : Pattern) :
    encodeTwo (some (left, right)) = present (pair (encodePattern left) (encodePattern right)) :=
  rfl

/-- **Negative**: none. -/
theorem encodeTwo_none : encodeTwo none = absent := rfl

/-- **Positive**: two parts, as data. -/
theorem encodeParts_some (first second : AtomTerm) :
    encodeParts (some (first, second)) =
      present (pair (encodeAtomTerm first) (encodeAtomTerm second)) := rfl

/-- **Negative**: none. -/
theorem encodeParts_none : encodeParts none = absent := rfl

/-- **Positive**: a variable, as data. -/
theorem encodeAtomTerm_var (index : Nat) : encodeAtomTerm (.var index) = call "Var" [tally index] :=
  rfl

/-- **Negative**: an atom and a variable are two data. -/
theorem encodeAtomTerm_atom_ne (raw : Pattern) (index : Nat) :
    encodeAtomTerm (.atom raw) ≠ encodeAtomTerm (.var index) := by
  simp [encodeAtomTerm, call]

/-- The unit atom, as a term of an equation. -/
def unitData : Term := call "apply" [encodeName "prime-unit", empty]

/-- The equation of two atoms, as a term of an equation. -/
def nodeData (left right : Term) : Term := call "apply" [encodeName "=", cell left (cell right empty)]

/-- **Positive**: on the data of two atoms it is the data of their
equation. -/
theorem nodeData_eq (left right : Pattern) :
    nodeData (encodePattern left) (encodePattern right) =
      encodePattern (equationAtom left right) := rfl

/-- **Negative**: the unit atom, as a term, is no equation. -/
theorem unitData_ne_nodeData (left right : Term) : unitData ≠ nodeData left right := by
  simp [unitData, nodeData, call, cell, empty]

/-- The three constructors of two parts. -/
inductive AtomTerm.Shape where
  | pi
  | lam
  | app

/-- The symbol of a shape. -/
def AtomTerm.Shape.symbol : AtomTerm.Shape → Term
  | .pi => .sym "Pi"
  | .lam => .sym "Lam"
  | .app => .sym "App"

/-- The term of a shape and two parts. -/
def AtomTerm.Shape.join : AtomTerm.Shape → AtomTerm → AtomTerm → AtomTerm
  | .pi, first, second => .pi first second
  | .lam, first, second => .lam first second
  | .app, first, second => .app first second

/-- **Positive**: the product of two parts. -/
theorem AtomTerm.Shape.join_pi (first second : AtomTerm) :
    AtomTerm.Shape.pi.join first second = .pi first second := rfl

/-- **Negative**: two shapes have two symbols. -/
theorem AtomTerm.Shape.symbol_pi_ne_app : AtomTerm.Shape.pi.symbol ≠ AtomTerm.Shape.app.symbol := by
  simp [AtomTerm.Shape.symbol]

/-! ## The program -/

/-- The equations of the program, after those of contraction. -/
def betaEquations : Program := [
  -- the premise
  ⟨"premise", "premise", [slot "relation", slot "inputs"],
    call "run-premise" [same (slot "relation") (encodeName "PrimeStep"), slot "inputs"]⟩,
  ⟨"run-two", "run-premise", [yes, cell (slot "space") (cell (slot "subject") empty)],
    call "write-all" [call "reducts" [call "read" [call "contract" [slot "subject"]]]]⟩,
  ⟨"run-other", "run-premise", [slot "t", slot "inputs"], empty⟩,
  -- the two arguments of a pattern
  ⟨"two-yes", "two", [call "apply" [slot "c", cell (slot "l") (cell (slot "r") empty)]],
    present (pair (slot "l") (slot "r"))⟩,
  ⟨"two-no", "two", [slot "other"], absent⟩,
  -- the number of a numeral
  ⟨"value-apply", "value", [call "apply" [slot "c", slot "args"]],
    call "value-step" [same (slot "c") (encodeName "="), slot "args"]⟩,
  ⟨"value-other", "value", [slot "other"], .sym "Z"⟩,
  ⟨"value-step", "value-step", [yes, cell (slot "first") (cell (slot "rest") empty)],
    call "S" [call "value" [slot "rest"]]⟩,
  ⟨"value-stop", "value-step", [slot "t", slot "args"], .sym "Z"⟩,
  -- reading an atom back
  ⟨"read", "read", [slot "p"], call "read-step" [call "two" [slot "p"], slot "p"]⟩,
  ⟨"read-node", "read-step", [present (pair (slot "tag") (slot "payload")), slot "p"],
    call "assemble" [call "value" [slot "tag"], call "read-parts" [call "two" [slot "payload"]],
      call "value" [slot "payload"], slot "p"]⟩,
  ⟨"read-leaf", "read-step", [slot "none", slot "p"], call "Atom" [slot "p"]⟩,
  ⟨"parts-yes", "read-parts", [present (pair (slot "a") (slot "b"))],
    present (pair (call "read" [slot "a"]) (call "read" [slot "b"]))⟩,
  ⟨"parts-no", "read-parts", [slot "none"], absent⟩,
  ⟨"assemble-var", "assemble", [tally 2, slot "parts", slot "k", slot "p"], call "Var" [slot "k"]⟩,
  ⟨"assemble-pi", "assemble", [tally 3, present (pair (slot "a") (slot "b")), slot "k", slot "p"],
    call "Pi" [slot "a", slot "b"]⟩,
  ⟨"assemble-lam", "assemble", [tally 4, present (pair (slot "a") (slot "b")), slot "k", slot "p"],
    call "Lam" [slot "a", slot "b"]⟩,
  ⟨"assemble-app", "assemble", [tally 5, present (pair (slot "a") (slot "b")), slot "k", slot "p"],
    call "App" [slot "a", slot "b"]⟩,
  ⟨"assemble-atom", "assemble", [slot "t", slot "parts", slot "k", slot "p"],
    call "Atom" [slot "p"]⟩,
  -- the order of numbers
  ⟨"lt-zero", "lt", [.sym "Z", call "S" [slot "c"]], yes⟩,
  ⟨"lt-step", "lt", [call "S" [slot "k"], call "S" [slot "c"]], call "lt" [slot "k", slot "c"]⟩,
  ⟨"lt-stop", "lt", [slot "k", slot "c"], no⟩,
  -- lifting
  ⟨"lift-var", "lift", [slot "c", call "Var" [slot "k"]],
    call "Var" [call "bump" [call "lt" [slot "k", slot "c"], slot "k"]]⟩,
  ⟨"lift-pi", "lift", [slot "c", call "Pi" [slot "a", slot "b"]],
    call "Pi" [call "lift" [slot "c", slot "a"], call "lift" [call "S" [slot "c"], slot "b"]]⟩,
  ⟨"lift-lam", "lift", [slot "c", call "Lam" [slot "a", slot "b"]],
    call "Lam" [call "lift" [slot "c", slot "a"], call "lift" [call "S" [slot "c"], slot "b"]]⟩,
  ⟨"lift-app", "lift", [slot "c", call "App" [slot "f", slot "a"]],
    call "App" [call "lift" [slot "c", slot "f"], call "lift" [slot "c", slot "a"]]⟩,
  ⟨"lift-atom", "lift", [slot "c", slot "other"], slot "other"⟩,
  ⟨"bump-keep", "bump", [yes, slot "k"], slot "k"⟩,
  ⟨"bump-up", "bump", [slot "t", slot "k"], call "S" [slot "k"]⟩,
  -- substitution
  ⟨"substitute-var", "substitute", [slot "j", slot "s", call "Var" [slot "k"]],
    call "pick" [same (slot "k") (slot "j"), call "lt" [slot "j", slot "k"], slot "k", slot "s"]⟩,
  ⟨"substitute-pi", "substitute", [slot "j", slot "s", call "Pi" [slot "a", slot "b"]],
    call "Pi" [call "substitute" [slot "j", slot "s", slot "a"],
      call "substitute" [call "S" [slot "j"], call "lift" [.sym "Z", slot "s"], slot "b"]]⟩,
  ⟨"substitute-lam", "substitute", [slot "j", slot "s", call "Lam" [slot "a", slot "b"]],
    call "Lam" [call "substitute" [slot "j", slot "s", slot "a"],
      call "substitute" [call "S" [slot "j"], call "lift" [.sym "Z", slot "s"], slot "b"]]⟩,
  ⟨"substitute-app", "substitute", [slot "j", slot "s", call "App" [slot "f", slot "a"]],
    call "App" [call "substitute" [slot "j", slot "s", slot "f"],
      call "substitute" [slot "j", slot "s", slot "a"]]⟩,
  ⟨"substitute-atom", "substitute", [slot "j", slot "s", slot "other"], slot "other"⟩,
  ⟨"pick-hit", "pick", [yes, slot "b", slot "k", slot "s"], slot "s"⟩,
  ⟨"pick-down", "pick", [slot "a", yes, call "S" [slot "k"], slot "s"], call "Var" [slot "k"]⟩,
  ⟨"pick-keep", "pick", [slot "a", slot "b", slot "k", slot "s"], call "Var" [slot "k"]⟩,
  -- the reducts
  ⟨"reducts-pi", "reducts", [call "Pi" [slot "a", slot "b"]],
    call "append" [call "left" [.sym "Pi", call "reducts" [slot "a"], slot "b"],
      call "right" [.sym "Pi", slot "a", call "reducts" [slot "b"]]]⟩,
  ⟨"reducts-lam", "reducts", [call "Lam" [slot "a", slot "b"]],
    call "append" [call "left" [.sym "Lam", call "reducts" [slot "a"], slot "b"],
      call "right" [.sym "Lam", slot "a", call "reducts" [slot "b"]]]⟩,
  ⟨"reducts-app", "reducts", [call "App" [slot "f", slot "a"]],
    call "append" [call "contractions" [slot "f", slot "a"],
      call "append" [call "left" [.sym "App", call "reducts" [slot "f"], slot "a"],
        call "right" [.sym "App", slot "f", call "reducts" [slot "a"]]]]⟩,
  ⟨"reducts-other", "reducts", [slot "other"], empty⟩,
  ⟨"contractions-beta", "contractions", [call "Lam" [slot "d", slot "b"], slot "a"],
    cell (call "substitute" [.sym "Z", slot "a", slot "b"]) empty⟩,
  ⟨"contractions-none", "contractions", [slot "f", slot "a"], empty⟩,
  ⟨"left-cons", "left", [slot "shape", cell (slot "x") (slot "xs"), slot "y"],
    cell (call "join" [slot "shape", slot "x", slot "y"])
      (call "left" [slot "shape", slot "xs", slot "y"])⟩,
  ⟨"left-nil", "left", [slot "shape", slot "xs", slot "y"], empty⟩,
  ⟨"right-cons", "right", [slot "shape", slot "y", cell (slot "x") (slot "xs")],
    cell (call "join" [slot "shape", slot "y", slot "x"])
      (call "right" [slot "shape", slot "y", slot "xs"])⟩,
  ⟨"right-nil", "right", [slot "shape", slot "y", slot "xs"], empty⟩,
  ⟨"join-pi", "join", [.sym "Pi", slot "x", slot "y"], call "Pi" [slot "x", slot "y"]⟩,
  ⟨"join-lam", "join", [.sym "Lam", slot "x", slot "y"], call "Lam" [slot "x", slot "y"]⟩,
  ⟨"join-app", "join", [slot "shape", slot "x", slot "y"], call "App" [slot "x", slot "y"]⟩,
  ⟨"append-cons", "append", [cell (slot "x") (slot "xs"), slot "ys"],
    cell (slot "x") (call "append" [slot "xs", slot "ys"])⟩,
  ⟨"append-nil", "append", [slot "xs", slot "ys"], slot "ys"⟩,
  -- writing
  ⟨"numeral-zero", "numeral", [.sym "Z"], unitData⟩,
  ⟨"numeral-succ", "numeral", [call "S" [slot "k"]],
    nodeData unitData (call "numeral" [slot "k"])⟩,
  ⟨"write-atom", "write", [call "Atom" [slot "p"]], slot "p"⟩,
  ⟨"write-var", "write", [call "Var" [slot "k"]],
    nodeData (call "numeral" [tally 2]) (call "numeral" [slot "k"])⟩,
  ⟨"write-pi", "write", [call "Pi" [slot "a", slot "b"]],
    nodeData (call "numeral" [tally 3]) (nodeData (call "write" [slot "a"]) (call "write" [slot "b"]))⟩,
  ⟨"write-lam", "write", [call "Lam" [slot "a", slot "b"]],
    nodeData (call "numeral" [tally 4]) (nodeData (call "write" [slot "a"]) (call "write" [slot "b"]))⟩,
  ⟨"write-app", "write", [call "App" [slot "f", slot "a"]],
    nodeData (call "numeral" [tally 5]) (nodeData (call "write" [slot "f"]) (call "write" [slot "a"]))⟩,
  ⟨"write-all-cons", "write-all", [cell (slot "x") (slot "xs")],
    cell (call "write" [slot "x"]) (call "write-all" [slot "xs"])⟩,
  ⟨"write-all-nil", "write-all", [slot "xs"], empty⟩]

/-- **The beta program.** -/
def betaProgram : Program := contractEquations ++ betaEquations

theorem betaProgram_length : betaProgram.length = 76 := rfl

local notation "P" => betaProgram
local notation "H" => sharedHost

theorem betaProgram_keepsCells : KeepsCells P H := keepsCells_dataEqualityHost (by rfl)

local notation "keeps" => betaProgram_keepsCells

instance : Constructs betaProgram "Cons" := ⟨by rfl, fun _ => rfl⟩
instance : Constructs betaProgram "apply" := ⟨by rfl, fun _ => rfl⟩
instance : Constructs betaProgram "Some" := ⟨by rfl, fun _ => rfl⟩
instance : Constructs betaProgram "Pair" := ⟨by rfl, fun _ => rfl⟩
instance : Constructs betaProgram "S" := ⟨by rfl, fun _ => rfl⟩
instance : Constructs betaProgram "Atom" := ⟨by rfl, fun _ => rfl⟩
instance : Constructs betaProgram "Var" := ⟨by rfl, fun _ => rfl⟩
instance : Constructs betaProgram "Pi" := ⟨by rfl, fun _ => rfl⟩
instance : Constructs betaProgram "Lam" := ⟨by rfl, fun _ => rfl⟩
instance : Constructs betaProgram "App" := ⟨by rfl, fun _ => rfl⟩

theorem betaEquations_apart :
    ∀ equation ∈ betaEquations, equation.head ∉ contractEquations.calledHeads := by
  decide +kernel

theorem beta_contract (pattern : Pattern) :
    Applies P H "contract" [encodePattern pattern] (encodePattern (contract pattern)) :=
  (Applies.append_iff contractEquations betaEquations sharedHost betaEquations_apart "contract"
    (by decide +kernel) _ _).mpr (contractEquations_computes pattern)

/-! ## Reading -/

theorem two_computes (pattern : Pattern) :
    Applies P H "two" [encodePattern pattern] (encodeTwo (twoArguments pattern)) := by
  cases pattern with
  | apply label arguments =>
      rcases arguments with _ | ⟨first, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩
      · by_equation
        engine keeps
      · by_equation
        engine keeps
      · by_equation
        engine keeps
      · by_equation
        engine keeps
  | _ =>
      by_equation
      engine keeps

theorem valueStep_computes (label : String) (arguments : List Pattern)
    (later : ∀ rest ∈ arguments,
      Applies P H "value" [encodePattern rest] (tally (numeralValue rest))) :
    Applies P H "value-step" [boolean (decide (label = "=")), encodePatterns arguments]
      (tally (if label = "=" then numeralValueList arguments else 0)) := by
  by_cases equation : label = "="
  · simp only [equation, decide_true, if_true, boolean]
    rcases arguments with _ | ⟨first, _ | ⟨rest, _ | ⟨third, more⟩⟩⟩
    · by_equation
      engine keeps
    · by_equation
      engine keeps
    · by_equation
      engine keeps using exact later rest (by simp)
    · by_equation
      engine keeps
  · simp only [equation, decide_false, if_false, boolean]
    by_equation
    engine keeps

/-- **The program counts the number of a numeral.** -/
theorem value_computes (pattern : Pattern) :
    Applies P H "value" [encodePattern pattern] (tally (numeralValue pattern)) := by
  induction pattern using Pattern.inductionOn with
  | happly label arguments ih =>
      by_equation
      engine keeps using exact valueStep_computes label arguments ih
  | _ =>
      by_equation
      engine keeps

theorem assemble_computes (tag : Nat) (parts : Option (AtomTerm × AtomTerm)) (index : Nat)
    (whole : Pattern) :
    Applies P H "assemble" [tally tag, encodeParts parts, tally index, encodePattern whole]
      (encodeAtomTerm (assemble tag parts index whole)) := by
  rcases tag with _ | _ | _ | _ | _ | _ | tag <;> rcases parts with _ | ⟨first, second⟩ <;>
    (by_equation
     engine keeps)

theorem readParts_computes (payload : Pattern)
    (later : ∀ left right, twoArguments payload = some (left, right) →
      Applies P H "read" [encodePattern left] (encodeAtomTerm (readAtom left)) ∧
        Applies P H "read" [encodePattern right] (encodeAtomTerm (readAtom right))) :
    Applies P H "read-parts" [encodeTwo (twoArguments payload)] (encodeParts (readParts payload)) := by
  rw [readParts_eq]
  cases found : twoArguments payload with
  | none =>
      by_equation
      engine keeps
  | some parts =>
      obtain ⟨left, right⟩ := parts
      obtain ⟨leftRead, rightRead⟩ := later left right found
      by_equation
      engine keeps using first
        | exact leftRead
        | exact rightRead

theorem readStep_computes (pattern : Pattern)
    (later : ∀ smaller : Pattern, sizeOf smaller < sizeOf pattern →
      Applies P H "read" [encodePattern smaller] (encodeAtomTerm (readAtom smaller))) :
    Applies P H "read-step" [encodeTwo (twoArguments pattern), encodePattern pattern]
      (encodeAtomTerm (readAtom pattern)) := by
  cases found : twoArguments pattern with
  | none =>
      rw [readAtom_of_none found]
      by_equation
      engine keeps
  | some parts =>
      obtain ⟨tag, payload⟩ := parts
      rw [readAtom_of_some found]
      have payloadSmaller := (twoArguments_sizeOf found).2
      by_equation
      engine keeps using first
        | exact value_computes tag
        | exact value_computes payload
        | exact two_computes payload
        | exact readParts_computes payload fun left right inner =>
            ⟨later left (by have := (twoArguments_sizeOf inner).1; omega),
              later right (by have := (twoArguments_sizeOf inner).2; omega)⟩
        | exact assemble_computes _ _ _ _

/-- **The program reads an atom back.** -/
theorem read_computes (pattern : Pattern) :
    Applies P H "read" [encodePattern pattern] (encodeAtomTerm (readAtom pattern)) := by
  generalize size : sizeOf pattern = bound
  induction bound using Nat.strong_induction_on generalizing pattern with
  | _ bound ih =>
      subst size
      by_equation
      engine keeps using first
        | exact two_computes pattern
        | exact readStep_computes pattern fun smaller less => ih _ less smaller rfl

/-! ## Lifting and substitution -/

theorem lt_computes : ∀ index cutoff : Nat,
    Applies P H "lt" [tally index, tally cutoff] (boolean (decide (index < cutoff)))
  | 0, 0 => by
      by_equation
      engine keeps
  | 0, cutoff + 1 => by
      rw [show decide (0 < cutoff + 1) = true by simp]
      by_equation
      engine keeps
  | index + 1, 0 => by
      rw [show decide (index + 1 < 0) = false by simp]
      by_equation
      engine keeps
  | index + 1, cutoff + 1 => by
      have later := lt_computes index cutoff
      rw [show decide (index + 1 < cutoff + 1) = decide (index < cutoff) by simp]
      by_equation
      engine keeps using exact later

theorem bump_computes (below : Bool) (index : Nat) :
    Applies P H "bump" [boolean below, tally index] (tally (if below then index else index + 1)) := by
  cases below
  · by_equation
    engine keeps
  · by_equation
    engine keeps

/-- **The program lifts.** -/
theorem lift_computes : ∀ (term : AtomTerm) (cutoff : Nat),
    Applies P H "lift" [tally cutoff, encodeAtomTerm term]
      (encodeAtomTerm (AtomTerm.lift cutoff term))
  | .atom raw, cutoff => by
      by_equation
      engine keeps
  | .var index, cutoff => by
      have bumped := bump_computes (decide (index < cutoff)) index
      rw [show (if decide (index < cutoff) = true then index else index + 1) =
        (if index < cutoff then index else index + 1) by simp] at bumped
      by_equation
      engine keeps using first
        | exact lt_computes index cutoff
        | exact bumped
  | .pi domain body, cutoff => by
      have domainLifted := lift_computes domain cutoff
      have bodyLifted := lift_computes body (cutoff + 1)
      by_equation
      engine keeps using first
        | exact domainLifted
        | exact bodyLifted
  | .lam domain body, cutoff => by
      have domainLifted := lift_computes domain cutoff
      have bodyLifted := lift_computes body (cutoff + 1)
      by_equation
      engine keeps using first
        | exact domainLifted
        | exact bodyLifted
  | .app function argument, cutoff => by
      have functionLifted := lift_computes function cutoff
      have argumentLifted := lift_computes argument cutoff
      by_equation
      engine keeps using first
        | exact functionLifted
        | exact argumentLifted

theorem pick_computes (index target : Nat) (replacement : AtomTerm) :
    Applies P H "pick"
      [boolean (decide (index = target)), boolean (decide (target < index)), tally index,
        encodeAtomTerm replacement]
      (encodeAtomTerm
        (if index = target then replacement
          else if target < index then .var (index - 1) else .var index)) := by
  by_cases hit : index = target
  · simp only [hit, decide_true, if_true, boolean]
    by_equation
    engine keeps
  · by_cases below : target < index
    · obtain ⟨previous, rfl⟩ : ∃ previous, index = previous + 1 := ⟨index - 1, by omega⟩
      simp only [hit, below, decide_true, decide_false, if_true, if_false, boolean,
        Nat.add_sub_cancel]
      by_equation
      engine keeps
    · simp only [hit, below, decide_false, if_false, boolean]
      by_equation
      engine keeps

/-- **The program substitutes.** -/
theorem subst_computes : ∀ (term : AtomTerm) (target : Nat) (replacement : AtomTerm),
    Applies P H "substitute" [tally target, encodeAtomTerm replacement, encodeAtomTerm term]
      (encodeAtomTerm (AtomTerm.subst target replacement term))
  | .atom raw, target, replacement => by
      by_equation
      engine keeps
  | .var index, target, replacement => by
      by_equation
      engine keeps using first
        | exact encoded_comparison tally tally_injective index target (by rfl)
        | exact lt_computes target index
        | exact pick_computes index target replacement
  | .pi domain body, target, replacement => by
      have domainDone := subst_computes domain target replacement
      have lifted := lift_computes replacement 0
      have bodyDone := subst_computes body (target + 1) (AtomTerm.lift 0 replacement)
      by_equation
      engine keeps using first
        | exact domainDone
        | exact lifted
        | exact bodyDone
  | .lam domain body, target, replacement => by
      have domainDone := subst_computes domain target replacement
      have lifted := lift_computes replacement 0
      have bodyDone := subst_computes body (target + 1) (AtomTerm.lift 0 replacement)
      by_equation
      engine keeps using first
        | exact domainDone
        | exact lifted
        | exact bodyDone
  | .app function argument, target, replacement => by
      have functionDone := subst_computes function target replacement
      have argumentDone := subst_computes argument target replacement
      by_equation
      engine keeps using first
        | exact functionDone
        | exact argumentDone

/-! ## The reducts -/

theorem join_computes (shape : AtomTerm.Shape) (left right : AtomTerm) :
    Applies P H "join" [shape.symbol, encodeAtomTerm left, encodeAtomTerm right]
      (encodeAtomTerm (shape.join left right)) := by
  cases shape
  · by_equation
    engine keeps
  · by_equation
    engine keeps
  · by_equation
    engine keeps

theorem left_computes (shape : AtomTerm.Shape) (fixed : AtomTerm) : ∀ moved : List AtomTerm,
    Applies P H "left" [shape.symbol, encodeAtomTerms moved, encodeAtomTerm fixed]
      (encodeAtomTerms (moved.map fun reduct => shape.join reduct fixed))
  | [] => by
      by_equation
      engine keeps
  | reduct :: rest => by
      have later := left_computes shape fixed rest
      by_equation
      engine keeps using first
        | exact join_computes shape reduct fixed
        | exact later

theorem right_computes (shape : AtomTerm.Shape) (fixed : AtomTerm) : ∀ moved : List AtomTerm,
    Applies P H "right" [shape.symbol, encodeAtomTerm fixed, encodeAtomTerms moved]
      (encodeAtomTerms (moved.map fun reduct => shape.join fixed reduct))
  | [] => by
      by_equation
      engine keeps
  | reduct :: rest => by
      have later := right_computes shape fixed rest
      by_equation
      engine keeps using first
        | exact join_computes shape fixed reduct
        | exact later

theorem append_computes (second : List AtomTerm) : ∀ first : List AtomTerm,
    Applies P H "append" [encodeAtomTerms first, encodeAtomTerms second]
      (encodeAtomTerms (first ++ second))
  | [] => by
      by_equation
      engine keeps
  | head :: tail => by
      have later := append_computes second tail
      by_equation
      engine keeps using exact later

theorem contractions_computes (function argument : AtomTerm) :
    Applies P H "contractions" [encodeAtomTerm function, encodeAtomTerm argument]
      (encodeAtomTerms (AtomTerm.contractions function argument)) := by
  cases function with
  | lam domain body =>
      by_equation
      engine keeps using exact subst_computes body 0 argument
  | _ =>
      by_equation
      engine keeps

theorem reductsPi_computes (domain body : AtomTerm)
    (inDomain : Applies P H "reducts" [encodeAtomTerm domain]
      (encodeAtomTerms (AtomTerm.reducts domain)))
    (inBody : Applies P H "reducts" [encodeAtomTerm body]
      (encodeAtomTerms (AtomTerm.reducts body))) :
    Applies P H "reducts" [encodeAtomTerm (.pi domain body)]
      (encodeAtomTerms (AtomTerm.reducts (.pi domain body))) := by
  by_equation
  engine keeps using first
    | exact inDomain
    | exact inBody
    | exact left_computes .pi body (AtomTerm.reducts domain)
    | exact right_computes .pi domain (AtomTerm.reducts body)
    | exact append_computes _ _

theorem reductsLam_computes (domain body : AtomTerm)
    (inDomain : Applies P H "reducts" [encodeAtomTerm domain]
      (encodeAtomTerms (AtomTerm.reducts domain)))
    (inBody : Applies P H "reducts" [encodeAtomTerm body]
      (encodeAtomTerms (AtomTerm.reducts body))) :
    Applies P H "reducts" [encodeAtomTerm (.lam domain body)]
      (encodeAtomTerms (AtomTerm.reducts (.lam domain body))) := by
  by_equation
  engine keeps using first
    | exact inDomain
    | exact inBody
    | exact left_computes .lam body (AtomTerm.reducts domain)
    | exact right_computes .lam domain (AtomTerm.reducts body)
    | exact append_computes _ _

theorem reductsApp_computes (function argument : AtomTerm)
    (inFunction : Applies P H "reducts" [encodeAtomTerm function]
      (encodeAtomTerms (AtomTerm.reducts function)))
    (inArgument : Applies P H "reducts" [encodeAtomTerm argument]
      (encodeAtomTerms (AtomTerm.reducts argument))) :
    Applies P H "reducts" [encodeAtomTerm (.app function argument)]
      (encodeAtomTerms (AtomTerm.reducts (.app function argument))) := by
  by_equation
  engine keeps using first
    | exact inFunction
    | exact inArgument
    | exact contractions_computes function argument
    | exact left_computes .app argument (AtomTerm.reducts function)
    | exact right_computes .app function (AtomTerm.reducts argument)
    | exact append_computes _ _

theorem reductsLeaf_computes (term : AtomTerm) (leaf : AtomTerm.reducts term = [])
    (shape : (∃ raw, term = .atom raw) ∨ ∃ index, term = .var index) :
    Applies P H "reducts" [encodeAtomTerm term] (encodeAtomTerms (AtomTerm.reducts term)) := by
  rw [leaf]
  rcases shape with ⟨raw, rfl⟩ | ⟨index, rfl⟩
  · by_equation
    engine keeps
  · by_equation
    engine keeps

/-- **The program lists the reducts by one step of beta at any position.** -/
theorem reducts_computes : ∀ term : AtomTerm,
    Applies P H "reducts" [encodeAtomTerm term] (encodeAtomTerms (AtomTerm.reducts term))
  | .atom raw => reductsLeaf_computes _ rfl (.inl ⟨raw, rfl⟩)
  | .var index => reductsLeaf_computes _ rfl (.inr ⟨index, rfl⟩)
  | .pi domain body =>
      reductsPi_computes domain body (reducts_computes domain) (reducts_computes body)
  | .lam domain body =>
      reductsLam_computes domain body (reducts_computes domain) (reducts_computes body)
  | .app function argument =>
      reductsApp_computes function argument (reducts_computes function)
        (reducts_computes argument)

/-! ## Writing -/

theorem numeral_computes : ∀ count : Nat,
    Applies P H "numeral" [tally count] (encodePattern (numeral count))
  | 0 => by
      by_equation
      engine keeps
  | count + 1 => by
      have later := numeral_computes count
      by_equation
      engine keeps using exact later

theorem writeLeaf_computes (term : AtomTerm)
    (shape : (∃ raw, term = .atom raw) ∨ ∃ index, term = .var index) :
    Applies P H "write" [encodeAtomTerm term] (encodePattern (AtomTerm.write term)) := by
  rcases shape with ⟨raw, rfl⟩ | ⟨index, rfl⟩
  · by_equation
    engine keeps
  · by_equation
    engine keeps using first
      | exact numeral_computes 2
      | exact numeral_computes index

theorem writePi_computes (domain body : AtomTerm)
    (domainWritten : Applies P H "write" [encodeAtomTerm domain]
      (encodePattern (AtomTerm.write domain)))
    (bodyWritten : Applies P H "write" [encodeAtomTerm body]
      (encodePattern (AtomTerm.write body))) :
    Applies P H "write" [encodeAtomTerm (.pi domain body)]
      (encodePattern (AtomTerm.write (.pi domain body))) := by
  by_equation
  engine keeps using first
    | exact numeral_computes 3
    | exact domainWritten
    | exact bodyWritten

theorem writeLam_computes (domain body : AtomTerm)
    (domainWritten : Applies P H "write" [encodeAtomTerm domain]
      (encodePattern (AtomTerm.write domain)))
    (bodyWritten : Applies P H "write" [encodeAtomTerm body]
      (encodePattern (AtomTerm.write body))) :
    Applies P H "write" [encodeAtomTerm (.lam domain body)]
      (encodePattern (AtomTerm.write (.lam domain body))) := by
  by_equation
  engine keeps using first
    | exact numeral_computes 4
    | exact domainWritten
    | exact bodyWritten

theorem writeApp_computes (function argument : AtomTerm)
    (functionWritten : Applies P H "write" [encodeAtomTerm function]
      (encodePattern (AtomTerm.write function)))
    (argumentWritten : Applies P H "write" [encodeAtomTerm argument]
      (encodePattern (AtomTerm.write argument))) :
    Applies P H "write" [encodeAtomTerm (.app function argument)]
      (encodePattern (AtomTerm.write (.app function argument))) := by
  by_equation
  engine keeps using first
    | exact numeral_computes 5
    | exact functionWritten
    | exact argumentWritten

/-- **The program writes what was read back.** -/
theorem write_computes : ∀ term : AtomTerm,
    Applies P H "write" [encodeAtomTerm term] (encodePattern (AtomTerm.write term))
  | .atom raw => writeLeaf_computes _ (.inl ⟨raw, rfl⟩)
  | .var index => writeLeaf_computes _ (.inr ⟨index, rfl⟩)
  | .pi domain body => writePi_computes domain body (write_computes domain) (write_computes body)
  | .lam domain body => writeLam_computes domain body (write_computes domain) (write_computes body)
  | .app function argument =>
      writeApp_computes function argument (write_computes function) (write_computes argument)

theorem writeAll_computes : ∀ terms : List AtomTerm,
    Applies P H "write-all" [encodeAtomTerms terms] (encodePatterns (terms.map AtomTerm.write))
  | [] => by
      by_equation
      engine keeps
  | term :: rest => by
      have later := writeAll_computes rest
      by_equation
      engine keeps using first
        | exact write_computes term
        | exact later

/-! ## The premise -/

/-- The answers of the program to a relation and a list of inputs. -/
def betaStepAnswers (relation : String) (inputs : List Pattern) : List Pattern :=
  if relation = "PrimeStep" then
    match inputs with
    | [_, subject] => betaAnswers (contract subject)
    | _ => []
  else []

/-- **Negative**: to a relation that is not the step of the run premise, no
answer. -/
theorem betaStepAnswers_other {relation : String} (other : relation ≠ "PrimeStep")
    (inputs : List Pattern) : betaStepAnswers relation inputs = [] := by
  simp [betaStepAnswers, other]

theorem betaRun_computes (relation : String) (inputs : List Pattern) :
    Applies P H "run-premise" [boolean (decide (relation = "PrimeStep")), encodePatterns inputs]
      (encodePatterns (betaStepAnswers relation inputs)) := by
  by_cases step : relation = "PrimeStep"
  · subst step
    rcases inputs with _ | ⟨space, _ | ⟨subject, _ | ⟨third, rest⟩⟩⟩
    · by_equation
      engine keeps
    · by_equation
      engine keeps
    · by_equation
      engine keeps using first
        | exact beta_contract subject
        | exact read_computes (contract subject)
        | exact reducts_computes (readAtom (contract subject))
        | exact writeAll_computes _
    · by_equation
      engine keeps
  · rw [betaStepAnswers_other step]
    simp only [step, decide_false, boolean]
    by_equation
    engine keeps

/-- **On every relation and every list of inputs the program returns its
answers.** -/
theorem betaPremise_computes (relation : String) (inputs : List Pattern) :
    Applies P H premiseHead (premiseArguments relation inputs)
      (encodePatterns (betaStepAnswers relation inputs)) := by
  show Applies P H "premise" [encodeName relation, encodePatterns inputs] _
  by_equation
  engine keeps using exact betaRun_computes relation inputs

theorem betaProgram_total : Total betaProgram := fun relation inputs =>
  ended_of_applies (betaPremise_computes relation inputs)

/-- **The authored evaluator of the beta program.** -/
def betaAuthored : AuthoredEvaluator := ⟨betaProgram, betaProgram_total⟩

theorem betaAuthored_answers (relation : String) (inputs : List Pattern) :
    betaAuthored.answers relation inputs = betaStepAnswers relation inputs :=
  betaAuthored.answers_of_applies (betaPremise_computes relation inputs)

theorem betaAuthored_run (space subject : Pattern) :
    betaAuthored.answers "PrimeStep" [space, subject] = betaAnswers (contract subject) := by
  rw [betaAuthored_answers]
  rfl

/-! ## Its evaluator respects the static equivalence -/

theorem betaStepAnswers_reads (relation : String) (first second : List Pattern)
    (same : first.map contract = second.map contract) :
    betaStepAnswers relation first = betaStepAnswers relation second := by
  unfold betaStepAnswers
  by_cases step : relation = "PrimeStep"
  · rw [if_pos step, if_pos step]
    rcases first with _ | ⟨space, _ | ⟨subject, _ | ⟨third, rest⟩⟩⟩ <;>
      rcases second with _ | ⟨otherSpace, _ | ⟨otherSubject, _ | ⟨fourth, more⟩⟩⟩ <;>
      simp_all
  · rw [if_neg step, if_neg step]

theorem betaAuthored_stableAt (relation : String) (arity : Nat) :
    betaAuthored.StableAt relation arity :=
  AuthoredEvaluator.stableAt_of_reads (fun first second same => by
    rw [betaAuthored_answers, betaAuthored_answers, betaStepAnswers_reads relation first second same])
    arity

/-- **The evaluator of the beta program respects the static equivalence.** -/
theorem betaAuthored_respectsStatics : RespectsStatics betaAuthored.evaluator probeWithSpace :=
  (respectsStatics_iff_stable_probe probeWithSpace_quoteDropOnly probeWithSpace_rewrites
    betaAuthored).mpr
    ⟨betaAuthored_stableAt _ _, betaAuthored_stableAt _ _, betaAuthored_stableAt _ _,
      betaAuthored_stableAt _ _⟩

/-! ## What it hosts -/

/-- **Through one run rewrite the beta program hosts the pure λΠ-calculus,
with beta at every position**, on terms: a term is read as the run of its
atom at the empty space. -/
theorem betaAuthored_hosts :
    HostedBy ((rewritingTheory (Theory.ofTable ∅)).gslt ()).termsAlone
      (contextTheory betaAuthored.evaluator spacePresentation) := by
  refine hostedBy_of_runAnswers betaAuthored.answersRunBy (emptySpace_wellSorted []) (by decide)
    (fun term : LF.Term => termAtom term) termAtom_closedAtom contract_termAtom
    termAtom_injective (fun _ _ same => same) ?_ ?_
  · intro (term : LF.Term) (next : LF.Term) step
    show termAtom next ∈ betaAuthored.answers "PrimeStep" [emptySpace, termAtom term]
    rw [betaAuthored_run, contract_termAtom]
    exact mem_betaAnswers_termAtom.mpr ⟨next, step, rfl⟩
  · intro written subject (term : LF.Term) result _ subjects found
    have listed : result ∈ betaAuthored.answers "PrimeStep" [written, subject] := found
    rw [betaAuthored_run, subjects] at listed
    obtain ⟨next, step, rfl⟩ := mem_betaAnswers_termAtom.mp listed
    exact ⟨next, step, contract_termAtom next⟩

/-- **One step of beta at every position is authored.**  An authored evaluator
that respects the static equivalence hosts, through one run rewrite, the pure
λΠ-calculus: the theory of the rule-table evaluator at the empty table.  That
theory branches without bound along one reduction, and the matching evaluator
does not host it. -/
theorem beta_everywhere_authored :
    ∃ A : AuthoredEvaluator, RespectsStatics A.evaluator probeWithSpace ∧
      HostedBy ((rewritingTheory (Theory.ofTable ∅)).gslt ()).termsAlone
        (contextTheory A.evaluator spacePresentation) ∧
      UnboundedBranching ((rewritingTheory (Theory.ofTable ∅)).gslt ()) ∧
      ¬ HostedBy ((rewritingTheory (Theory.ofTable ∅)).gslt ()).termsAlone matchingCandidate :=
  ⟨betaAuthored, betaAuthored_respectsStatics, betaAuthored_hosts,
    rewritingTheory_unboundedBranching _,
    not_hostedBy_matching_of_unboundedBranching (rewritingTheory_unboundedBranching _)⟩

/-- **Negative**: the answers of the beta program are not answers by stored
rules. -/
theorem beta_not_answersByStoredRules :
    ¬ AnswersByStoredRules fun space subject =>
      betaAuthored.answers "PrimeStep" [space, subject] := fun weak =>
  storedRules_not_hostedBy_rewritingTheory betaAuthored.answersRunBy weak (Theory.ofTable ∅)
    betaAuthored_hosts

/-! ## The evaluator of the program runs -/

#guard (betaAuthored.evaluator probeWithSpace
    [("subject", quoted (dropped (termAtom (.app (.lam (.con "A") (.var 0)) (.con "c"))))),
      ("space", emptySpace)] runPremise).map
      (fun bindings => applyBindings bindings (.fvar "answer")) ==
  [termAtom (.con "c")]

#guard (betaAuthored.evaluator probeWithSpace
    [("subject", termAtom (.app (.lam (.con "A") (.app (.var 0) (.var 0)))
      (.app (.lam (.con "A") (.var 0)) (.con "c")))), ("space", emptySpace)] runPremise).length == 2

#guard (betaAuthored.evaluator probeWithSpace
    [("subject", unitAtom), ("space", emptySpace)] runPremise).isEmpty

#print axioms read_computes
#print axioms lift_computes
#print axioms subst_computes
#print axioms reducts_computes
#print axioms write_computes
#print axioms betaPremise_computes
#print axioms betaAuthored
#print axioms betaAuthored_respectsStatics
#print axioms betaAuthored_hosts
#print axioms beta_everywhere_authored
#print axioms beta_not_answersByStoredRules

end Mettapedia.Logic.HostingStyles.AuthoredEvaluators

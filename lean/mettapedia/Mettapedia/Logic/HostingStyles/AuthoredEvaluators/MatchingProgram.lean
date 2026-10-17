import Mettapedia.Logic.HostingStyles.AuthoredEvaluators.EquationProofs

/-!
# The matching evaluator is authored

`matchingProgram` is an equation program of the shared engine, on the shared
host.  Called on the relation `PrimeStep` and two inputs, a space and a
subject, it

* contracts both (`contract`: the quotations of droppings are removed,
  innermost first),
* lists the atoms that the space stores (`stored`),
* and for each stored equation whose two sides read as first-order sides
  (`first-order`) matches the left side against the subject at its root
  (`match`, `merge`, `find`) and instantiates the right side (`instantiate`);
  a variable atom is a pattern variable, named by its index (`index-name`).

It uses one primitive of the host, the equality of two data.  Everything else
is done by its equations: eighty-eight of them.

## What is proved

* Each head computes its function on all patterns: `contract_computes`,
  `stored_computes`, `firstOrder_computes`, `match_computes`,
  `merge_computes`, `instantiate_computes`, `atomResult_computes`,
  `results_computes`.
* **On every relation and every list of inputs the program returns the
  answers of the matching evaluator** (`premise_computes`).  So it halts on
  every query (`matchingProgram_total`), and
* **its evaluator is the matching evaluator** (`matchingAuthored_evaluator`):
  the two are one function, on every language, all bindings and every
  premise.  The matching evaluator is authored
  (`matchingEvaluator_isAuthored`).
* The evaluator of the program runs: the checks at the end execute it on a
  space of two rules.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AuthoredEvaluators

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
open Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction (encodeOption)
open Mettapedia.GSLT.Dedukti.Language (metaName)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles

/-! ## The program -/

/-- The character of the names of pattern variables, as data. -/
def metaCharacter : Term := encodeCharacter 'x'

/-- The equations that contract a pattern. -/
def contractEquations : Program := [
  ⟨"contract-bvar", "contract", [call "bvar" [slot "n"]], call "bvar" [slot "n"]⟩,
  ⟨"contract-fvar", "contract", [call "fvar" [slot "x"]], call "fvar" [slot "x"]⟩,
  ⟨"contract-apply", "contract", [call "apply" [slot "c", slot "args"]],
    call "contract-root" [same (slot "c") (encodeName "prime-quote"), slot "c",
      call "contract-list" [slot "args"]]⟩,
  ⟨"contract-lambda", "contract", [call "lambda" [slot "b", slot "body"]],
    call "lambda" [slot "b", call "contract" [slot "body"]]⟩,
  ⟨"contract-multi", "contract", [call "multi-lambda" [slot "n", slot "bs", slot "body"]],
    call "multi-lambda" [slot "n", slot "bs", call "contract" [slot "body"]]⟩,
  ⟨"contract-subst", "contract", [call "subst" [slot "body", slot "repl"]],
    call "subst" [call "contract" [slot "body"], call "contract" [slot "repl"]]⟩,
  ⟨"contract-collection", "contract", [call "collection" [slot "k", slot "elems", slot "rest"]],
    call "collection" [slot "k", call "contract-list" [slot "elems"], slot "rest"]⟩,
  ⟨"contract-nil", "contract-list", [empty], empty⟩,
  ⟨"contract-cons", "contract-list", [cell (slot "p") (slot "ps")],
    cell (call "contract" [slot "p"]) (call "contract-list" [slot "ps"])⟩,
  ⟨"root-single", "contract-root", [yes, slot "c", cell (slot "first") empty],
    call "contract-quoted" [slot "first", slot "c"]⟩,
  ⟨"root-other", "contract-root", [slot "t", slot "c", slot "args"],
    call "apply" [slot "c", slot "args"]⟩,
  ⟨"quoted-apply", "contract-quoted",
    [call "apply" [slot "d", cell (slot "name") empty], slot "c"],
    call "contract-drop" [same (slot "d") (encodeName "prime-drop"), slot "c", slot "d",
      slot "name"]⟩,
  ⟨"quoted-other", "contract-quoted", [slot "first", slot "c"],
    call "apply" [slot "c", cell (slot "first") empty]⟩,
  ⟨"drop-yes", "contract-drop", [yes, slot "c", slot "d", slot "name"], slot "name"⟩,
  ⟨"drop-no", "contract-drop", [no, slot "c", slot "d", slot "name"],
    call "apply" [slot "c", cell (call "apply" [slot "d", cell (slot "name") empty]) empty]⟩]

/-- The equations that list the atoms stored in a space. -/
def storedEquations : Program := [
  ⟨"stored-apply", "stored", [call "apply" [slot "c", slot "args"]],
    call "stored-add" [same (slot "c") (encodeName "prime-space-add"), slot "args"]⟩,
  ⟨"stored-other", "stored", [slot "other"], empty⟩,
  ⟨"stored-add", "stored-add", [yes, cell (slot "atom") (cell (slot "rest") empty)],
    cell (slot "atom") (call "stored" [slot "rest"])⟩,
  ⟨"stored-none", "stored-add", [slot "t", slot "args"], empty⟩]

/-- The equations that build the name of a pattern variable from the index of
a variable atom. -/
def nameEquations : Program := [
  ⟨"index-one", "index-name", [cell (slot "index") empty], call "numeral-name" [slot "index"]⟩,
  ⟨"index-other", "index-name", [slot "other"], cell metaCharacter empty⟩,
  ⟨"numeral-apply", "numeral-name", [call "apply" [slot "c", slot "args"]],
    call "numeral-step" [same (slot "c") (encodeName "="), slot "args"]⟩,
  ⟨"numeral-other", "numeral-name", [slot "other"], cell metaCharacter empty⟩,
  ⟨"numeral-step", "numeral-step", [yes, cell (slot "first") (cell (slot "rest") empty)],
    cell metaCharacter (call "numeral-name" [slot "rest"])⟩,
  ⟨"numeral-stop", "numeral-step", [slot "t", slot "args"], cell metaCharacter empty⟩]

/-- The equations that decide whether a stored atom reads as a first-order
side. -/
def firstOrderEquations : Program := [
  ⟨"fo-bvar", "first-order", [call "bvar" [slot "n"]], yes⟩,
  ⟨"fo-fvar", "first-order", [call "fvar" [slot "x"]], yes⟩,
  ⟨"fo-apply", "first-order", [call "apply" [slot "c", slot "args"]],
    call "first-order-apply" [same (slot "c") (encodeName "prime-variable"), slot "args"]⟩,
  ⟨"fo-other", "first-order", [slot "other"], no⟩,
  ⟨"fo-variable", "first-order-apply", [yes, slot "args"], yes⟩,
  ⟨"fo-arguments", "first-order-apply", [no, slot "args"], call "first-order-list" [slot "args"]⟩,
  ⟨"fo-nil", "first-order-list", [empty], yes⟩,
  ⟨"fo-cons", "first-order-list", [cell (slot "p") (slot "ps")],
    call "both" [call "first-order" [slot "p"], call "first-order-list" [slot "ps"]]⟩,
  ⟨"both-yes", "both", [yes, slot "b"], slot "b"⟩,
  ⟨"both-no", "both", [no, slot "b"], no⟩]

/-- The equations that look a name up in bindings and merge two lists of
bindings. -/
def bindingEquations : Program := [
  ⟨"find-nil", "find", [empty, slot "name"], absent⟩,
  ⟨"find-cons", "find", [cell (pair (slot "key") (slot "value")) (slot "rest"), slot "name"],
    call "find-here" [same (slot "key") (slot "name"), slot "value", slot "rest", slot "name"]⟩,
  ⟨"find-yes", "find-here", [yes, slot "value", slot "rest", slot "name"], present (slot "value")⟩,
  ⟨"find-no", "find-here", [no, slot "value", slot "rest", slot "name"],
    call "find" [slot "rest", slot "name"]⟩,
  ⟨"merge-nil", "merge", [slot "acc", empty], present (slot "acc")⟩,
  ⟨"merge-cons", "merge", [slot "acc", cell (pair (slot "name") (slot "value")) (slot "rest")],
    call "merge-found" [call "find" [slot "acc", slot "name"], slot "acc", slot "name",
      slot "value", slot "rest"]⟩,
  ⟨"merge-new", "merge-found", [absent, slot "acc", slot "name", slot "value", slot "rest"],
    call "merge" [cell (pair (slot "name") (slot "value")) (slot "acc"), slot "rest"]⟩,
  ⟨"merge-old", "merge-found",
    [present (slot "existing"), slot "acc", slot "name", slot "value", slot "rest"],
    call "merge-same" [same (slot "existing") (slot "value"), slot "acc", slot "rest"]⟩,
  ⟨"merge-yes", "merge-same", [yes, slot "acc", slot "rest"],
    call "merge" [slot "acc", slot "rest"]⟩,
  ⟨"merge-no", "merge-same", [no, slot "acc", slot "rest"], absent⟩]

/-- The equations that match a stored atom, read as a left side, against a
subject. -/
def matchEquations : Program := [
  ⟨"match-bvar", "match", [call "bvar" [slot "n"], slot "t"],
    call "match-bvar" [slot "t", slot "n"]⟩,
  ⟨"match-fvar", "match", [call "fvar" [slot "x"], slot "t"],
    present (cell (pair (slot "x") (slot "t")) empty)⟩,
  ⟨"match-apply", "match", [call "apply" [slot "c", slot "args"], slot "t"],
    call "match-apply" [same (slot "c") (encodeName "prime-variable"), slot "c", slot "args",
      slot "t"]⟩,
  ⟨"match-other", "match", [slot "p", slot "t"], absent⟩,
  ⟨"bvar-bvar", "match-bvar", [call "bvar" [slot "m"], slot "n"],
    call "unit-if" [same (slot "n") (slot "m")]⟩,
  ⟨"bvar-other", "match-bvar", [slot "t", slot "n"], absent⟩,
  ⟨"unit-yes", "unit-if", [yes], present empty⟩,
  ⟨"unit-no", "unit-if", [no], absent⟩,
  ⟨"apply-variable", "match-apply", [yes, slot "c", slot "args", slot "t"],
    present (cell (pair (call "index-name" [slot "args"]) (slot "t")) empty)⟩,
  ⟨"apply-apply", "match-apply",
    [no, slot "c", slot "args", call "apply" [slot "d", slot "targs"]],
    call "match-labels" [same (slot "c") (slot "d"), slot "args", slot "targs"]⟩,
  ⟨"apply-other", "match-apply", [no, slot "c", slot "args", slot "t"], absent⟩,
  ⟨"labels-yes", "match-labels", [yes, slot "args", slot "targs"],
    call "match-args" [slot "args", slot "targs"]⟩,
  ⟨"labels-no", "match-labels", [no, slot "args", slot "targs"], absent⟩,
  ⟨"args-nil", "match-args", [empty, empty], present empty⟩,
  ⟨"args-cons", "match-args", [cell (slot "p") (slot "ps"), cell (slot "t") (slot "ts")],
    call "merge-option" [call "match" [slot "p", slot "t"],
      call "match-args" [slot "ps", slot "ts"]]⟩,
  ⟨"args-other", "match-args", [slot "ps", slot "ts"], absent⟩,
  ⟨"merge-both", "merge-option", [present (slot "hb"), present (slot "tb")],
    call "merge" [slot "hb", slot "tb"]⟩,
  ⟨"merge-neither", "merge-option", [slot "a", slot "b"], absent⟩]

/-- The equations that instantiate a stored atom, read as a right side. -/
def instantiateEquations : Program := [
  ⟨"inst-bvar", "instantiate", [slot "b", call "bvar" [slot "n"]], call "bvar" [slot "n"]⟩,
  ⟨"inst-fvar", "instantiate", [slot "b", call "fvar" [slot "x"]],
    call "bound-name" [slot "b", slot "x"]⟩,
  ⟨"inst-apply", "instantiate", [slot "b", call "apply" [slot "c", slot "args"]],
    call "instantiate-apply" [same (slot "c") (encodeName "prime-variable"), slot "b", slot "c",
      slot "args"]⟩,
  ⟨"inst-variable", "instantiate-apply", [yes, slot "b", slot "c", slot "args"],
    call "bound-name" [slot "b", call "index-name" [slot "args"]]⟩,
  ⟨"inst-arguments", "instantiate-apply", [no, slot "b", slot "c", slot "args"],
    call "apply" [slot "c", call "instantiate-list" [slot "b", slot "args"]]⟩,
  ⟨"inst-nil", "instantiate-list", [slot "b", empty], empty⟩,
  ⟨"inst-cons", "instantiate-list", [slot "b", cell (slot "p") (slot "ps")],
    cell (call "instantiate" [slot "b", slot "p"]) (call "instantiate-list" [slot "b", slot "ps"])⟩,
  ⟨"bound-name", "bound-name", [slot "b", slot "x"],
    call "bound-or" [call "find" [slot "b", slot "x"], slot "x"]⟩,
  ⟨"bound-some", "bound-or", [present (slot "value"), slot "x"], slot "value"⟩,
  ⟨"bound-none", "bound-or", [absent, slot "x"], call "fvar" [slot "x"]⟩]

/-- The equations that answer a subject from one stored atom, and from the
list of them. -/
def resultEquations : Program := [
  ⟨"atom-apply", "atom-result", [call "apply" [slot "c", slot "args"], slot "subject"],
    call "equation-result" [same (slot "c") (encodeName "="), slot "args", slot "subject"]⟩,
  ⟨"atom-other", "atom-result", [slot "atom", slot "subject"], absent⟩,
  ⟨"equation-sides", "equation-result",
    [yes, cell (slot "left") (cell (slot "right") empty), slot "subject"],
    call "guarded" [call "both" [call "first-order" [slot "left"],
      call "first-order" [slot "right"]], slot "left", slot "right", slot "subject"]⟩,
  ⟨"equation-other", "equation-result", [slot "t", slot "args", slot "subject"], absent⟩,
  ⟨"guarded-yes", "guarded", [yes, slot "left", slot "right", slot "subject"],
    call "instantiated" [call "match" [slot "left", slot "subject"], slot "right"]⟩,
  ⟨"guarded-no", "guarded", [no, slot "left", slot "right", slot "subject"], absent⟩,
  ⟨"instantiated-some", "instantiated", [present (slot "b"), slot "right"],
    present (call "instantiate" [slot "b", slot "right"])⟩,
  ⟨"instantiated-none", "instantiated", [absent, slot "right"], absent⟩,
  ⟨"results-nil", "results", [empty, slot "subject"], empty⟩,
  ⟨"results-cons", "results", [cell (slot "atom") (slot "atoms"), slot "subject"],
    call "push" [call "atom-result" [slot "atom", slot "subject"],
      call "results" [slot "atoms", slot "subject"]]⟩,
  ⟨"push-some", "push", [present (slot "r"), slot "rest"], cell (slot "r") (slot "rest")⟩,
  ⟨"push-none", "push", [absent, slot "rest"], slot "rest"⟩]

/-- The equations that answer a premise. -/
def premiseEquations : Program := [
  ⟨"premise", "premise", [slot "relation", slot "inputs"],
    call "run-premise" [same (slot "relation") (encodeName "PrimeStep"), slot "inputs"]⟩,
  ⟨"run-two", "run-premise", [yes, cell (slot "space") (cell (slot "subject") empty)],
    call "results" [call "stored" [call "contract" [slot "space"]],
      call "contract" [slot "subject"]]⟩,
  ⟨"run-other", "run-premise", [slot "t", slot "inputs"], empty⟩]

/-- The equations of the matching program after those of contraction. -/
def matchingRest : Program :=
  storedEquations ++ nameEquations ++ firstOrderEquations ++ bindingEquations ++
    matchEquations ++ instantiateEquations ++ resultEquations ++ premiseEquations

/-- **The matching program.** -/
def matchingProgram : Program := contractEquations ++ matchingRest

/-- It has eighty-eight equations. -/
theorem matchingProgram_length : matchingProgram.length = 88 := rfl

local notation "P" => matchingProgram
local notation "H" => sharedHost

/-- The tags of cells are constructors of the program. -/
theorem matchingProgram_keepsCells : KeepsCells P H := keepsCells_dataEqualityHost (by rfl)

local notation "keeps" => matchingProgram_keepsCells

/-! ## Contraction

The equations of contraction call no other head of the program, so what they
compute is proved for them alone, and holds in every program that adds
equations for other heads (`contract_computes`). -/

section Contraction

local notation "C" => contractEquations

/-- The tags of cells are constructors of the equations of contraction. -/
theorem contractEquations_keepsCells : KeepsCells contractEquations sharedHost :=
  keepsCells_dataEqualityHost (by rfl)

theorem contractDrop_computes (label inner : String) (name : Pattern) :
    Applies C H "contract-drop"
      [boolean (decide (inner = "prime-drop")), encodeName label, encodeName inner,
        encodePattern name]
      (encodePattern
        (if inner = "prime-drop" then name else .apply label [.apply inner [name]])) := by
  by_cases dropped : inner = "prime-drop"
  · simp only [dropped, decide_true, if_true, boolean]
    by_equation
    engine contractEquations_keepsCells
  · simp only [dropped, decide_false, if_false, boolean, encodePattern, encodePatterns]
    by_equation
    engine contractEquations_keepsCells

theorem contractQuoted_computes (first : Pattern) :
    Applies C H "contract-quoted" [encodePattern first, encodeName "prime-quote"]
      (encodePattern (contractRoot "prime-quote" [first])) := by
  cases first with
  | apply inner inside =>
      rcases inside with _ | ⟨name, _ | ⟨other, more⟩⟩
      · by_equation
        engine contractEquations_keepsCells
      · by_equation
        engine contractEquations_keepsCells using exact contractDrop_computes "prime-quote" inner name
      · by_equation
        engine contractEquations_keepsCells
  | _ =>
      by_equation
      engine contractEquations_keepsCells

theorem contractRoot_computes (label : String) (arguments : List Pattern) :
    Applies C H "contract-root"
      [boolean (decide (label = "prime-quote")), encodeName label, encodePatterns arguments]
      (encodePattern (contractRoot label arguments)) := by
  by_cases quoted : label = "prime-quote"
  · subst quoted
    rcases arguments with _ | ⟨first, _ | ⟨second, rest⟩⟩
    · by_equation
      engine contractEquations_keepsCells
    · by_equation
      engine contractEquations_keepsCells using exact contractQuoted_computes first
    · have several : contractRoot "prime-quote" (first :: second :: rest) =
          .apply "prime-quote" (first :: second :: rest) := by simp [contractRoot]
      rw [several]
      by_equation
      engine contractEquations_keepsCells
  · rw [contractRoot_of_ne quoted]
    simp only [quoted, decide_false, boolean]
    by_equation
    engine contractEquations_keepsCells

theorem contractList_computes :
    ∀ patterns : List Pattern,
      (∀ pattern ∈ patterns,
        Applies C H "contract" [encodePattern pattern] (encodePattern (contract pattern))) →
      Applies C H "contract-list" [encodePatterns patterns]
        (encodePatterns (contractList patterns))
  | [], _ => by
      by_equation
      engine contractEquations_keepsCells
  | pattern :: patterns, each => by
      by_equation
      engine contractEquations_keepsCells using first
        | exact each pattern (List.mem_cons_self ..)
        | exact contractList_computes patterns fun other member =>
            each other (List.mem_cons_of_mem _ member)

/-- **The equations of contraction contract a pattern.** -/
theorem contractEquations_computes (pattern : Pattern) :
    Applies C H "contract" [encodePattern pattern] (encodePattern (contract pattern)) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      by_equation
      engine contractEquations_keepsCells
  | hfvar name =>
      by_equation
      engine contractEquations_keepsCells
  | happly label arguments ih =>
      by_equation
      engine contractEquations_keepsCells using first
        | exact contractList_computes arguments ih
        | exact contractRoot_computes label (contractList arguments)
  | hlambda binder body ih =>
      by_equation
      engine contractEquations_keepsCells using exact ih
  | hmultiLambda arity binders body ih =>
      by_equation
      engine contractEquations_keepsCells using exact ih
  | hsubst body replacement ihBody ihReplacement =>
      by_equation
      engine contractEquations_keepsCells using first
        | exact ihBody
        | exact ihReplacement
  | hcollection kind elements rest ih =>
      by_equation
      engine contractEquations_keepsCells using exact contractList_computes elements ih

end Contraction

/-- The other equations of the matching program define no head that the
equations of contraction call. -/
theorem matchingRest_apart :
    ∀ equation ∈ matchingRest, equation.head ∉ contractEquations.calledHeads := by
  decide +kernel

/-- **The program contracts a pattern.** -/
theorem contract_computes (pattern : Pattern) :
    Applies P H "contract" [encodePattern pattern] (encodePattern (contract pattern)) :=
  (Applies.append_iff contractEquations matchingRest sharedHost matchingRest_apart "contract"
    (by decide +kernel) _ _).mpr (contractEquations_computes pattern)

/-! ## Stored atoms -/

theorem storedAdd_computes (label : String) (arguments : List Pattern)
    (later : ∀ rest ∈ arguments,
      Applies P H "stored" [encodePattern rest] (encodePatterns (storedAtoms rest))) :
    Applies P H "stored-add"
      [boolean (decide (label = "prime-space-add")), encodePatterns arguments]
      (encodePatterns (if label = "prime-space-add" then storedAtomsList arguments else [])) := by
  by_cases added : label = "prime-space-add"
  · simp only [added, decide_true, if_true, boolean]
    rcases arguments with _ | ⟨atom, _ | ⟨rest, _ | ⟨third, more⟩⟩⟩
    · by_equation
      engine keeps
    · by_equation
      engine keeps
    · by_equation
      engine keeps using exact later rest (by simp)
    · by_equation
      engine keeps
  · simp only [added, decide_false, if_false, boolean]
    by_equation
    engine keeps

/-- **The program lists the atoms that a space stores.** -/
theorem stored_computes (space : Pattern) :
    Applies P H "stored" [encodePattern space] (encodePatterns (storedAtoms space)) := by
  induction space using Pattern.inductionOn with
  | happly label arguments ih =>
      by_equation
      engine keeps using exact storedAdd_computes label arguments ih
  | _ =>
      by_equation
      engine keeps

/-! ## The names of pattern variables -/

/-- The name of the pattern variable of an index, as data. -/
def metaCells (index : Nat) : Term := cells (List.replicate (index + 1) metaCharacter)

theorem metaCells_eq (index : Nat) : metaCells index = encodeName (metaName index) :=
  (encodeName_metaName index).symm

theorem numeralStep_computes (label : String) (arguments : List Pattern)
    (later : ∀ rest ∈ arguments,
      Applies P H "numeral-name" [encodePattern rest] (metaCells (numeralValue rest))) :
    Applies P H "numeral-step" [boolean (decide (label = "=")), encodePatterns arguments]
      (metaCells (if label = "=" then numeralValueList arguments else 0)) := by
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

theorem numeralName_computes (pattern : Pattern) :
    Applies P H "numeral-name" [encodePattern pattern] (metaCells (numeralValue pattern)) := by
  induction pattern using Pattern.inductionOn with
  | happly label arguments ih =>
      by_equation
      engine keeps using exact numeralStep_computes label arguments ih
  | _ =>
      by_equation
      engine keeps

/-- **The program builds the name of the pattern variable of a variable
atom.** -/
theorem indexName_computes (arguments : List Pattern) :
    Applies P H "index-name" [encodePatterns arguments]
      (encodeName (metaName (indexOf arguments))) := by
  rw [← metaCells_eq]
  rcases arguments with _ | ⟨index, _ | ⟨second, rest⟩⟩
  · by_equation
    engine keeps
  · by_equation
    engine keeps using exact numeralName_computes index
  · by_equation
    engine keeps

/-! ## First-order sides -/

theorem both_computes (first second : Bool) :
    Applies P H "both" [boolean first, boolean second] (boolean (first && second)) := by
  cases first
  · by_equation
    engine keeps
  · by_equation
    engine keeps

theorem firstOrderList_computes :
    ∀ patterns : List Pattern,
      (∀ pattern ∈ patterns,
        Applies P H "first-order" [encodePattern pattern] (boolean (firstOrder pattern))) →
      Applies P H "first-order-list" [encodePatterns patterns]
        (boolean (firstOrderList patterns))
  | [], _ => by
      by_equation
      engine keeps
  | pattern :: patterns, each => by
      by_equation
      engine keeps using first
        | exact each pattern (List.mem_cons_self ..)
        | exact firstOrderList_computes patterns fun other member =>
            each other (List.mem_cons_of_mem _ member)
        | exact both_computes _ _

theorem firstOrderApply_computes (label : String) (arguments : List Pattern)
    (each : ∀ pattern ∈ arguments,
      Applies P H "first-order" [encodePattern pattern] (boolean (firstOrder pattern))) :
    Applies P H "first-order-apply"
      [boolean (decide (label = "prime-variable")), encodePatterns arguments]
      (boolean (if label = "prime-variable" then true else firstOrderList arguments)) := by
  by_cases isVariable : label = "prime-variable"
  · simp only [isVariable, decide_true, if_true, boolean]
    by_equation
    engine keeps
  · simp only [isVariable, decide_false, if_false]
    by_equation
    engine keeps using exact firstOrderList_computes arguments each

/-- **The program decides whether a stored atom reads as a first-order
side.** -/
theorem firstOrder_computes (pattern : Pattern) :
    Applies P H "first-order" [encodePattern pattern] (boolean (firstOrder pattern)) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      by_equation
      engine keeps
  | hfvar name =>
      by_equation
      engine keeps
  | happly label arguments ih =>
      by_equation
      engine keeps using exact firstOrderApply_computes label arguments ih
  | _ =>
      by_equation
      engine keeps

/-! ## Bindings -/

theorem findHere_computes (key name : String) (value : Pattern) (rest : Bindings)
    (later : Applies P H "find" [encodeBindings rest, encodeName name]
      (encodeOption encodePattern (lookupValue rest name))) :
    Applies P H "find-here"
      [boolean (decide (key = name)), encodePattern value, encodeBindings rest, encodeName name]
      (encodeOption encodePattern (if key = name then some value else lookupValue rest name)) := by
  by_cases found : key = name
  · simp only [found, decide_true, if_true, boolean]
    by_equation
    engine keeps
  · simp only [found, decide_false, if_false, boolean]
    by_equation
    engine keeps using exact later

/-- **The program looks a name up in bindings.** -/
theorem find_computes (name : String) :
    ∀ bindings : Bindings,
      Applies P H "find" [encodeBindings bindings, encodeName name]
        (encodeOption encodePattern (lookupValue bindings name))
  | [] => by
      by_equation
      engine keeps
  | (key, value) :: rest => by
      by_equation
      engine keeps using exact findHere_computes key name value rest (find_computes name rest)

theorem mergeSame_computes (existing value : Pattern) (bindings rest : Bindings)
    (kept : Applies P H "merge" [encodeBindings bindings, encodeBindings rest]
      (encodeOption encodeBindings (mergeBindings bindings rest))) :
    Applies P H "merge-same"
      [boolean (decide (existing = value)), encodeBindings bindings, encodeBindings rest]
      (encodeOption encodeBindings
        (if existing = value then mergeBindings bindings rest else none)) := by
  by_cases equal : existing = value
  · simp only [equal, decide_true, if_true, boolean]
    by_equation
    engine keeps using exact kept
  · simp only [equal, decide_false, if_false, boolean]
    by_equation
    engine keeps

theorem mergeFound_computes (found : Option Pattern) (bindings : Bindings) (name : String)
    (value : Pattern) (rest : Bindings)
    (fresh : Applies P H "merge" [encodeBindings ((name, value) :: bindings), encodeBindings rest]
      (encodeOption encodeBindings (mergeBindings ((name, value) :: bindings) rest)))
    (kept : Applies P H "merge" [encodeBindings bindings, encodeBindings rest]
      (encodeOption encodeBindings (mergeBindings bindings rest))) :
    Applies P H "merge-found"
      [encodeOption encodePattern found, encodeBindings bindings, encodeName name,
        encodePattern value, encodeBindings rest]
      (encodeOption encodeBindings
        (match found with
          | none => mergeBindings ((name, value) :: bindings) rest
          | some existing => if existing = value then mergeBindings bindings rest else none)) := by
  cases found with
  | none =>
      by_equation
      engine keeps using exact fresh
  | some existing =>
      by_equation
      engine keeps using exact mergeSame_computes existing value bindings rest kept

/-- **The program merges two lists of bindings.** -/
theorem merge_computes :
    ∀ addition bindings : Bindings,
      Applies P H "merge" [encodeBindings bindings, encodeBindings addition]
        (encodeOption encodeBindings (mergeBindings bindings addition))
  | [], bindings => by
      by_equation
      engine keeps
  | (name, value) :: rest, bindings => by
      rw [mergeBindings_cons]
      by_equation
      engine keeps using first
        | exact find_computes name bindings
        | exact mergeFound_computes _ bindings name value rest
            (merge_computes rest ((name, value) :: bindings)) (merge_computes rest bindings)

/-! ## Matching -/

theorem unitIf_computes (condition : Prop) [Decidable condition] :
    Applies P H "unit-if" [boolean (decide condition)]
      (encodeOption encodeBindings (if condition then some [] else none)) := by
  by_cases holds : condition
  · simp only [holds, decide_true, if_true, boolean]
    by_equation
    engine keeps
  · simp only [holds, decide_false, if_false, boolean]
    by_equation
    engine keeps

theorem matchBvar_computes (index : Nat) (subject : Pattern) :
    Applies P H "match-bvar" [encodePattern subject, natural index]
      (encodeOption encodeBindings (ruleMatch (.bvar index) subject)) := by
  cases subject with
  | bvar other =>
      by_equation
      engine keeps using exact unitIf_computes (index = other)
  | _ =>
      by_equation
      engine keeps

theorem mergeOption_computes (head tail : Option Bindings) :
    Applies P H "merge-option"
      [encodeOption encodeBindings head, encodeOption encodeBindings tail]
      (encodeOption encodeBindings
        (head.bind fun first => tail.bind fun second => mergeBindings first second)) := by
  cases head with
  | none =>
      by_equation
      engine keeps
  | some first =>
      cases tail with
      | none =>
          by_equation
          engine keeps
      | some second =>
          by_equation
          engine keeps using exact merge_computes second first

theorem matchArgs_computes :
    ∀ patterns subjects : List Pattern,
      (∀ pattern ∈ patterns, ∀ subject,
        Applies P H "match" [encodePattern pattern, encodePattern subject]
          (encodeOption encodeBindings (ruleMatch pattern subject))) →
      Applies P H "match-args" [encodePatterns patterns, encodePatterns subjects]
        (encodeOption encodeBindings (ruleMatchList patterns subjects))
  | [], [], _ => by
      by_equation
      engine keeps
  | [], _ :: _, _ => by
      by_equation
      engine keeps
  | _ :: _, [], _ => by
      by_equation
      engine keeps
  | pattern :: patterns, subject :: subjects, each => by
      by_equation
      engine keeps using first
        | exact each pattern (List.mem_cons_self ..) subject
        | exact matchArgs_computes patterns subjects fun other member =>
            each other (List.mem_cons_of_mem _ member)
        | exact mergeOption_computes _ _

theorem matchLabels_computes (label other : String) (arguments subjects : List Pattern)
    (lists : Applies P H "match-args" [encodePatterns arguments, encodePatterns subjects]
      (encodeOption encodeBindings (ruleMatchList arguments subjects))) :
    Applies P H "match-labels"
      [boolean (decide (label = other)), encodePatterns arguments, encodePatterns subjects]
      (encodeOption encodeBindings
        (if label = other then ruleMatchList arguments subjects else none)) := by
  by_cases equal : label = other
  · simp only [equal, decide_true, if_true, boolean]
    by_equation
    engine keeps using exact lists
  · simp only [equal, decide_false, if_false, boolean]
    by_equation
    engine keeps

theorem ruleMatch_apply {label : String} (other : label ≠ "prime-variable")
    (arguments : List Pattern) (subject : Pattern) :
    ruleMatch (.apply label arguments) subject =
      match subject with
      | .apply head subjects => if label = head then ruleMatchList arguments subjects else none
      | _ => none := by
  cases subject <;> simp [ruleMatch, other]

theorem matchApply_computes (label : String) (arguments : List Pattern) (subject : Pattern)
    (lists : ∀ subjects,
      Applies P H "match-args" [encodePatterns arguments, encodePatterns subjects]
        (encodeOption encodeBindings (ruleMatchList arguments subjects))) :
    Applies P H "match-apply"
      [boolean (decide (label = "prime-variable")), encodeName label, encodePatterns arguments,
        encodePattern subject]
      (encodeOption encodeBindings (ruleMatch (.apply label arguments) subject)) := by
  by_cases isVariable : label = "prime-variable"
  · have matched : ruleMatch (.apply label arguments) subject =
        some [(metaName (indexOf arguments), subject)] := by simp [ruleMatch, isVariable]
    rw [matched]
    simp only [isVariable, decide_true, boolean, if_true]
    by_equation
    engine keeps using exact indexName_computes arguments
  · rw [ruleMatch_apply isVariable]
    simp only [isVariable, decide_false, boolean]
    cases subject with
    | apply other subjects =>
        by_equation
        engine keeps using exact matchLabels_computes label other arguments subjects (lists subjects)
    | _ =>
        by_equation
        engine keeps

/-- **The program matches a stored atom, read as a left side, against a
subject.** -/
theorem match_computes (pattern : Pattern) :
    ∀ subject : Pattern,
      Applies P H "match" [encodePattern pattern, encodePattern subject]
        (encodeOption encodeBindings (ruleMatch pattern subject)) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro subject
      by_equation
      engine keeps using exact matchBvar_computes index subject
  | hfvar name =>
      intro subject
      by_equation
      engine keeps
  | happly label arguments ih =>
      intro subject
      by_equation
      engine keeps using exact matchApply_computes label arguments subject fun subjects =>
        matchArgs_computes arguments subjects ih
  | _ =>
      intro subject
      by_equation
      engine keeps

/-! ## Instances -/

theorem boundOr_computes (found : Option Pattern) (name : String) :
    Applies P H "bound-or" [encodeOption encodePattern found, encodeName name]
      (encodePattern (found.getD (.fvar name))) := by
  cases found with
  | none =>
      by_equation
      engine keeps
  | some value =>
      by_equation
      engine keeps

theorem boundName_computes (bindings : Bindings) (name : String) :
    Applies P H "bound-name" [encodeBindings bindings, encodeName name]
      (encodePattern (boundOr bindings name)) := by
  by_equation
  engine keeps using first
    | exact find_computes name bindings
    | exact boundOr_computes _ name

theorem instantiateList_computes (bindings : Bindings) :
    ∀ patterns : List Pattern, firstOrderList patterns = true →
      (∀ pattern ∈ patterns, firstOrder pattern = true →
        Applies P H "instantiate" [encodeBindings bindings, encodePattern pattern]
          (encodePattern (ruleInstance bindings pattern))) →
      Applies P H "instantiate-list" [encodeBindings bindings, encodePatterns patterns]
        (encodePatterns (ruleInstanceList bindings patterns))
  | [], _, _ => by
      by_equation
      engine keeps
  | pattern :: patterns, exact, each => by
      simp only [firstOrderList, Bool.and_eq_true] at exact
      by_equation
      engine keeps using first
        | exact each pattern (List.mem_cons_self ..) exact.1
        | exact instantiateList_computes bindings patterns exact.2 fun other member =>
            each other (List.mem_cons_of_mem _ member)

theorem instantiateApply_computes (bindings : Bindings) (label : String)
    (arguments : List Pattern) (exact : firstOrder (.apply label arguments) = true)
    (each : ∀ pattern ∈ arguments, firstOrder pattern = true →
      Applies P H "instantiate" [encodeBindings bindings, encodePattern pattern]
        (encodePattern (ruleInstance bindings pattern))) :
    Applies P H "instantiate-apply"
      [boolean (decide (label = "prime-variable")), encodeBindings bindings, encodeName label,
        encodePatterns arguments]
      (encodePattern (ruleInstance bindings (.apply label arguments))) := by
  by_cases isVariable : label = "prime-variable"
  · have instance_ : ruleInstance bindings (.apply label arguments) =
        boundOr bindings (metaName (indexOf arguments)) := by simp [ruleInstance, isVariable]
    rw [instance_]
    simp only [isVariable, decide_true, boolean, if_true]
    by_equation
    engine keeps using first
      | exact indexName_computes arguments
      | exact boundName_computes bindings _
  · have instance_ : ruleInstance bindings (.apply label arguments) =
        .apply label (ruleInstanceList bindings arguments) := by simp [ruleInstance, isVariable]
    rw [firstOrder, if_neg isVariable] at exact
    rw [instance_]
    simp only [isVariable, decide_false, boolean]
    by_equation
    engine keeps using exact instantiateList_computes bindings arguments exact each

/-- **The program instantiates a stored atom that reads as a first-order
right side.** -/
theorem instantiate_computes (bindings : Bindings) (pattern : Pattern) :
    firstOrder pattern = true →
      Applies P H "instantiate" [encodeBindings bindings, encodePattern pattern]
        (encodePattern (ruleInstance bindings pattern)) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro _
      by_equation
      engine keeps
  | hfvar name =>
      intro _
      by_equation
      engine keeps using exact boundName_computes bindings name
  | happly label arguments ih =>
      intro exact
      by_equation
      engine keeps using exact instantiateApply_computes bindings label arguments exact ih
  | hlambda binder body _ => intro exact; simp [firstOrder] at exact
  | hmultiLambda arity binders body _ => intro exact; simp [firstOrder] at exact
  | hsubst body replacement _ _ => intro exact; simp [firstOrder] at exact
  | hcollection kind elements rest _ => intro exact; simp [firstOrder] at exact

/-! ## The answers of a stored atom, and of a space -/

theorem instantiated_computes (found : Option Bindings) (right : Pattern)
    (exact : firstOrder right = true) :
    Applies P H "instantiated" [encodeOption encodeBindings found, encodePattern right]
      (encodeOption encodePattern (found.map fun bindings => ruleInstance bindings right)) := by
  cases found with
  | none =>
      by_equation
      engine keeps
  | some bindings =>
      by_equation
      engine keeps using exact instantiate_computes bindings right exact

theorem guarded_computes (left right subject : Pattern) :
    Applies P H "guarded"
      [boolean (firstOrder left && firstOrder right), encodePattern left, encodePattern right,
        encodePattern subject]
      (encodeOption encodePattern
        (if (firstOrder left && firstOrder right) = true then
          (ruleMatch left subject).map fun bindings => ruleInstance bindings right
        else none)) := by
  cases sides : (firstOrder left && firstOrder right)
  · by_equation
    engine keeps
  · simp only [Bool.and_eq_true] at sides
    by_equation
    engine keeps using first
      | exact match_computes left subject
      | exact instantiated_computes _ right sides.2

theorem atomResult_apply_of_ne {label : String} (other : label ≠ "=") (arguments : List Pattern)
    (subject : Pattern) : atomResult subject (.apply label arguments) = none := by
  simp [atomResult, other]

theorem equationResult_computes (label : String) (arguments : List Pattern) (subject : Pattern) :
    Applies P H "equation-result"
      [boolean (decide (label = "=")), encodePatterns arguments, encodePattern subject]
      (encodeOption encodePattern (atomResult subject (.apply label arguments))) := by
  by_cases equation : label = "="
  · subst equation
    rcases arguments with _ | ⟨left, _ | ⟨right, _ | ⟨third, rest⟩⟩⟩
    · by_equation
      engine keeps
    · by_equation
      engine keeps
    · by_equation
      engine keeps using first
        | exact firstOrder_computes _
        | exact both_computes _ _
        | exact guarded_computes left right subject
    · by_equation
      engine keeps
  · rw [atomResult_apply_of_ne equation]
    simp only [equation, decide_false, boolean]
    by_equation
    engine keeps

/-- **The program answers a subject from one stored atom.** -/
theorem atomResult_computes (atom subject : Pattern) :
    Applies P H "atom-result" [encodePattern atom, encodePattern subject]
      (encodeOption encodePattern (atomResult subject atom)) := by
  cases atom with
  | apply label arguments =>
      by_equation
      engine keeps using exact equationResult_computes label arguments subject
  | _ =>
      by_equation
      engine keeps

theorem push_computes (found : Option Pattern) (rest : List Pattern) :
    Applies P H "push" [encodeOption encodePattern found, encodePatterns rest]
      (encodePatterns (found.toList ++ rest)) := by
  cases found with
  | none =>
      by_equation
      engine keeps
  | some result =>
      by_equation
      engine keeps

/-- **The program answers a subject from a list of stored atoms.** -/
theorem results_computes (subject : Pattern) :
    ∀ atoms : List Pattern,
      Applies P H "results" [encodePatterns atoms, encodePattern subject]
        (encodePatterns (atoms.filterMap (atomResult subject)))
  | [] => by
      by_equation
      engine keeps
  | atom :: atoms => by
      have unfolded : (atom :: atoms).filterMap (atomResult subject) =
          (atomResult subject atom).toList ++ atoms.filterMap (atomResult subject) := by
        rw [List.filterMap_cons]
        cases atomResult subject atom <;> rfl
      rw [unfolded]
      by_equation
      engine keeps using first
        | exact atomResult_computes atom subject
        | exact results_computes subject atoms
        | exact push_computes _ _

/-! ## The premise -/

theorem runPremise_computes (relation : String) (inputs : List Pattern) :
    Applies P H "run-premise"
      [boolean (decide (relation = "PrimeStep")), encodePatterns inputs]
      (encodePatterns (matchingAnswers relation inputs)) := by
  by_cases step : relation = "PrimeStep"
  · subst step
    rcases inputs with _ | ⟨space, _ | ⟨subject, _ | ⟨third, rest⟩⟩⟩
    · by_equation
      engine keeps
    · by_equation
      engine keeps
    · rw [matchingAnswers_run, matchResults_eq_filterMap]
      by_equation
      engine keeps using first
        | exact contract_computes _
        | exact stored_computes _
        | exact results_computes _ _
    · by_equation
      engine keeps
  · have empty : matchingAnswers relation inputs = [] := by simp [matchingAnswers, step]
    rw [empty]
    simp only [step, decide_false, boolean]
    by_equation
    engine keeps

/-- **On every relation and every list of inputs the program returns the
answers of the matching evaluator.** -/
theorem premise_computes (relation : String) (inputs : List Pattern) :
    Applies P H premiseHead (premiseArguments relation inputs)
      (encodePatterns (matchingAnswers relation inputs)) := by
  show Applies P H "premise" [encodeName relation, encodePatterns inputs] _
  by_equation
  engine keeps using exact runPremise_computes relation inputs

/-- The program halts on every query. -/
theorem matchingProgram_total : Total matchingProgram := fun relation inputs =>
  ended_of_applies (premise_computes relation inputs)

/-- **The authored evaluator of the matching program.** -/
def matchingAuthored : AuthoredEvaluator := ⟨matchingProgram, matchingProgram_total⟩

theorem matchingAuthored_answers (relation : String) (inputs : List Pattern) :
    matchingAuthored.answers relation inputs = matchingAnswers relation inputs :=
  matchingAuthored.answers_of_applies (premise_computes relation inputs)

/-- **The evaluator of the matching program is the matching evaluator**: one
function, on every language, all bindings and every premise. -/
theorem matchingAuthored_evaluator : matchingAuthored.evaluator = matchingEvaluator := by
  funext lang bindings premise
  rw [AuthoredEvaluator.evaluator_apply, matchingEvaluator_apply]
  cases premise with
  | relationQuery relation arguments =>
      show (match queryShape arguments with
        | some (inputs, answer) =>
            (matchingAuthored.answers relation (inputs.map (applyBindings bindings))).map
              fun result => (answer, result) :: bindings
        | none => []) = match queryShape arguments with
        | some (inputs, answer) =>
            (matchingAnswers relation (inputs.map (applyBindings bindings))).map
              fun result => (answer, result) :: bindings
        | none => []
      cases queryShape arguments with
      | none => rfl
      | some shape => simp only [matchingAuthored_answers]
  | _ => rfl

/-- **The matching evaluator is authored.** -/
theorem matchingEvaluator_isAuthored : IsAuthored matchingEvaluator :=
  ⟨matchingAuthored, matchingAuthored_evaluator⟩

/-- Its answers are stable, so it respects the static equivalence of the probe
with a space: the criterion of `respectsStatics_iff_stable_probe`, met. -/
theorem matchingAuthored_stableAt (relation : String) (arity : Nat) :
    matchingAuthored.StableAt relation arity := by
  intro first second _ same result found
  rw [matchingAuthored_answers] at found ⊢
  refine ⟨result, ?_, rfl⟩
  unfold matchingAnswers at found ⊢
  by_cases step : relation = "PrimeStep"
  · rw [if_pos step] at found ⊢
    rcases first with _ | ⟨space, _ | ⟨subject, _ | ⟨third, rest⟩⟩⟩
    · cases found
    · cases found
    · rcases second with _ | ⟨otherSpace, _ | ⟨otherSubject, _ | ⟨fourth, more⟩⟩⟩
      · cases same
      · simp at same
      · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at same
        show result ∈ matchResults (contract otherSpace) (contract otherSubject)
        rw [← same.1, ← same.2]
        exact found
      · simp at same
    · cases found
  · rw [if_neg step] at found
    cases found

/-! ## The evaluator of the program runs -/

/-- A space of two rules: `x ⟶ (x = x)` and `unit ⟶ unit`. -/
def exampleSpace : Pattern :=
  spaceOfAtoms
    [.apply "=" [variableAtom (numeral 0),
        .apply "=" [variableAtom (numeral 0), variableAtom (numeral 0)]],
      .apply "=" [unitAtom, unitAtom]]

/-- The bindings of the run rewrite on a run in that space. -/
def exampleBindings (subject : Pattern) : Bindings :=
  [("subject", subject), ("space", exampleSpace)]

#guard matchingAuthored.evaluator probeWithSpace (exampleBindings unitAtom) runPremise ==
  matchingEvaluator probeWithSpace (exampleBindings unitAtom) runPremise

#guard (matchingAuthored.evaluator probeWithSpace (exampleBindings unitAtom) runPremise).length == 2

#guard matchingAuthored.evaluator probeWithSpace
    (exampleBindings (quoted (dropped (numeral 2)))) runPremise ==
  matchingEvaluator probeWithSpace (exampleBindings (quoted (dropped (numeral 2)))) runPremise

#guard (matchingAuthored.evaluator probeWithSpace
    (exampleBindings (quoted (dropped (numeral 2)))) runPremise).map
      (fun bindings => applyBindings bindings (.fvar "answer")) ==
  [.apply "=" [numeral 2, numeral 2]]

#guard (matchingAuthored.evaluator probeWithSpace [("subject", unitAtom), ("space", emptySpace)]
  runPremise).isEmpty

#print axioms contract_computes
#print axioms stored_computes
#print axioms indexName_computes
#print axioms firstOrder_computes
#print axioms find_computes
#print axioms merge_computes
#print axioms match_computes
#print axioms instantiate_computes
#print axioms atomResult_computes
#print axioms results_computes
#print axioms premise_computes
#print axioms matchingProgram_total
#print axioms matchingAuthored
#print axioms matchingAuthored_answers
#print axioms matchingAuthored_evaluator
#print axioms matchingEvaluator_isAuthored
#print axioms matchingAuthored_stableAt

end Mettapedia.Logic.HostingStyles.AuthoredEvaluators

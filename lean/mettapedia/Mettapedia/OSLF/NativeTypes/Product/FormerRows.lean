import Mettapedia.OSLF.NativeTypes.Product.LanguageRows
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.JudgmentControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ManySortedControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ExploredControls

/-!
# The acceptance matrix grown to formers × languages

For each language the executable reads from a file, the formulas of every former its signature supports, asked at the
language's sample terms as the executable asks them (`answerWith`):

- the connectives, the step modalities forward and back, counting, and the fixed points, for every language;
- `built` and `everyBuilt` for each constructor; `typed`, `untyped`, `someOf` and `everyOf` for each sort;
- `split`, `everySplit`, `empty`, `nonEmpty`, `single` and `everySingle` for each collection kind;
- `body`, `everyBody`, `bound` and `notBound` for languages with binders.

The expected answer of a row is the library's (`formerRows`); the executable checks that the languages read from
files answer the same. Every row's text reads back as its formula and term (`#guard`), and the coverage of each former
by proved and refuted rows is reported (`coverage`).
-/

namespace Mettapedia.OSLF.NativeTypes.Product

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.GeneratedLogic

/-- A term read from its text; a term that does not read is a constant naming the failure, caught by `#guard`. -/
def termOf (text : String) : Pattern :=
  match readPattern text with
  | .ok term => term
  | .error _ => .apply "unreadable" []

/-- The constructors of a language with their numbers of arguments. -/
def constructorsOf (language : LanguageDef) : List (String × ℕ) :=
  language.terms.map fun rule => (rule.label, rule.params.length)

/-- The collection kinds a language's constructors take. -/
def collectionKindsOf (language : LanguageDef) : List CollType :=
  (language.terms.flatMap fun rule => rule.params.filterMap fun param =>
    match param with
    | .simple _ (.collection kind _) => some kind
    | _ => none).dedup

/-- Whether a language's constructors bind. -/
def bindsOf (language : LanguageDef) : Bool :=
  language.terms.any fun rule => rule.params.any fun param =>
    match param with
    | .simple _ _ => false
    | _ => true

/-- A list of the same formula. -/
def repeatFormula (formula : Formula 0) : ℕ → Formulas 0
  | 0 => .nil
  | count + 1 => .cons formula (repeatFormula formula count)

/-- **The formulas of every former a language's signature supports**, each with its former's name. -/
def featureFormulas (language : LanguageDef) (sample : Pattern) : List (String × Formula 0) :=
  [("top", .top), ("bot", .bot), ("and", .and (.possibly .any .top) (.necessarily .any .bot)),
   ("or", .or (.necessarily .any .bot) (.possibly .any (.necessarily .any .bot))),
   ("dia", .possibly .any .top), ("box", .necessarily .any .bot),
   ("before", .sometimeBefore .any .top), ("alwaysBefore", .alwaysBefore .any .bot),
   ("atLeast", .atLeast 2 .forward .any .top), ("allButFewer", .allButFewer 1 .forward .any (.necessarily .any .bot)),
   ("mu", .mu (.or (.necessarily .any .bot) (.possibly .any (.var 0)))),
   ("nu", .nu (.and (.possibly .any .top) (.necessarily .any (.var 0)))),
   ("is", .is sample), ("isNot", .isNot sample)] ++
  (constructorsOf language).flatMap (fun (label, arity) =>
    [("built", .built label (repeatFormula .top arity)), ("everyBuilt", .everyBuilt label (repeatFormula .bot arity))]) ++
  (language.types.map (·.name)).flatMap (fun sort =>
    [("typed", .typed (.base sort)), ("untyped", .untyped (.base sort)),
     ("someOf", .someOf (.base sort) (.necessarily .any .bot)), ("everyOf", .everyOf (.base sort) (.possibly .any .top))]) ++
  (collectionKindsOf language).flatMap (fun kind =>
    [("split", .split kind (.nonEmpty kind) (.nonEmpty kind)), ("everySplit", .everySplit kind (.empty kind) (.empty kind)),
     ("empty", .empty kind), ("nonEmpty", .nonEmpty kind), ("single", .single kind .top),
     ("everySingle", .everySingle kind .bot)]) ++
  (if bindsOf language then
    [("body", .body .top), ("everyBody", .everyBody .bot), ("bound", .bound 0), ("notBound", .notBound 0)]
  else [])

/-- A language of the grid: its file, the language, its sample terms, premise fuel and budget. -/
abbrev GridLanguage := String × LanguageDef × List Pattern × ℕ × ℕ

def gridLanguages : List GridLanguage :=
  [("Halting.module", Executable.Explored.CounterAbstractions.halting,
     ["(Counter Zero)", "(Counter (Succ (Succ Zero)))", "Halted"].map termOf, 2, 4),
   ("Coins.module", JudgmentControls.coins, ["Toss", "H", "(Show H)"].map termOf, 2, 4),
   ("Courier.module", ManySorted.Controls.courier, ["(Fwd A Nil)", "(Send A Nil)", "A"].map termOf, 2, 4),
   ("Levels.module", Executable.FiniteModelControls.levels, ["High", "Mid", "Low"].map termOf, 2, 4),
   ("Spinner.module", ExploredControls.spinner, ["Loop", "(Grow Z)"].map termOf, 2, 3),
   ("Lambda.module", lambdaCalc,
     [InstanceControls.app InstanceControls.identity InstanceControls.identity, InstanceControls.identity,
      InstanceControls.omega], 2, 4),
   ("TinyML.module", tinyML,
     ["(If (Inject BoolT) (Inject BoolF) (Inject BoolT))", "(Inject BoolT)", "(Fst (Inject (PairV BoolT BoolF)))"].map termOf,
     2, 4),
   ("Petri.module", GeneratedLogic.PetriControls.petriCore,
     [GeneratedLogic.PetriControls.ab, GeneratedLogic.PetriControls.ad, GeneratedLogic.PetriControls.cd], 2, 4),
   ("Peano.module", peano, [numeral 2, sum], 8, 8)]

/-- The rows of one language: every feature formula at every sample term, with the library's answer. -/
def gridRows : GridLanguage → List (String × LanguageRow)
  | (file, language, terms, fuel, budget) =>
    terms.flatMap fun term =>
      (featureFormulas language term).map fun (former, formula) =>
        (former, (file, language, formula, term, budget,
          Verdicts.answerSummary (answerWith { fuel := fuel } language formula term budget), fuel))

/-- **The grid's rows**, each with the former it exercises. -/
def formerGrid : List (String × LanguageRow) := gridLanguages.flatMap gridRows

def formerRows : List LanguageRow := formerGrid.map (·.2)

/-- The grid as the executable's matrix rows. -/
def formerMatrixRows : List MatrixRow := formerRows.map LanguageRow.matrixRow

/-- **Coverage**: for each former, its proved, refuted and open rows. -/
def coverage : List (String × ℕ × ℕ × ℕ) :=
  let formers := (formerGrid.map (·.1)).dedup
  formers.map fun former =>
    let answers := (formerGrid.filter (·.1 == former)).map fun (_, row) => row.2.2.2.2.2.1
    (former, (answers.filter (·.startsWith "P")).length, (answers.filter (·.startsWith "R")).length,
      (answers.filter (· == "open")).length)

#guard formerRows.all fun (_, _, formula, term, _, _, _) => readsBack formula term
#guard (gridLanguages.flatMap fun (_, _, terms, _, _) => terms).all (· != .apply "unreadable" [])

#eval (formerRows.length, coverage)

end Mettapedia.OSLF.NativeTypes.Product

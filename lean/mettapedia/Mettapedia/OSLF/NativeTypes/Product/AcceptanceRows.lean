import Mettapedia.OSLF.NativeTypes.GeneratedLogic.AcceptanceMatrix
import Mettapedia.OSLF.NativeTypes.Product.Query

/-!
# The acceptance matrix as the executable's rows

The rows of the acceptance matrix (`AcceptanceMatrix.lambdaRows`, `aliasRows`, `unwrapRows`) as lines of the
executable's matrix: the language's module file, the formula and the term as text, the budget, the expected answer in
brief, and the settings. The executable reads the languages from their files and answers each row with `answerWith`:
the library's search, and then the certified deciders for what the search leaves open. Its answer refines the
library's row (`refines`): the same where the row is decided, and possibly decided where the row is open.

- Every row's text reads back as its formula and term (`readsBack`, checked for all rows).
- The rows modulo equations need the canonical forms of the two languages, which the executable does not have; the
  rows as written run from files.
-/

namespace Mettapedia.OSLF.NativeTypes.Product

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.GeneratedLogic
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.AcceptanceMatrix

/-- A row of the executable's matrix: file, formula, term, budget, expected answer, settings. -/
abbrev MatrixRow := String × String × String × ℕ × String × List String

/-- A row as a line of a matrix file. -/
def MatrixRow.line : MatrixRow → String
  | (file, formula, term, budget, expected, settings) =>
    " | ".intercalate ([file, formula, term, toString budget, expected] ++
      (if settings.isEmpty then [] else [" ".intercalate settings]))

/-- Whether a formula and a term read back from their texts. -/
def readsBack (formula : Formula 0) (term : Pattern) : Bool :=
  (match readFormula [] (formulaText formula) with
    | .ok read => read == formula
    | .error _ => false) &&
  (match readPattern (patternText term) with
    | .ok read => read == term
    | .error _ => false)

/-- **The executable's answer refines the library's row**: the same where the row is decided, and possibly decided where
it is open, since the executable also consults certified deciders for what the search leaves open. -/
def refines (expected exe : String) : Bool := exe == expected || (expected == "open" && exe != "open")

/-- The executable's answer in brief, for a language with settings. -/
def exeSummary (fuel : ℕ) (language : LanguageDef) (formula : Formula 0) (term : Pattern) (budget : ℕ) : String :=
  Verdicts.answerSummary (answerWith { fuel := fuel } language formula term budget)

/-- **The λ grid's rows**: full β, premise fuel three, the finder's hints over two values. -/
def lambdaMatrixRows : List MatrixRow :=
  lambdaRows.map fun (term, formula, _) =>
    ("FullLambda.module", formulaText formula, patternText term, lambdaRounds,
      exeSummary lambdaFuel Mettapedia.OSLF.NativeTypes.Executable.FiniteModelControls.fullLambda formula term lambdaRounds,
      [s!"fuel={lambdaFuel}", "hints=1"])

/-- The languages as the executable's files write them: under their own names, so that neither these nor the files'
readings are the certified languages, and both are answered as written. -/
def aliasedFile : LanguageDef := { CanonicalRegionControls.aliased with «name» := "AliasedAsWritten" }
def wrappedFile : LanguageDef := { CanonicalUnwrapControls.wrapped with «name» := "WrappedAsWritten" }

/-- **The rows of the grid modulo `A = B`, as written.** -/
def aliasMatrixRows : List MatrixRow :=
  aliasRows.map fun (term, formula, _, _) =>
    ("Aliased.module", formulaText formula, patternText term, 2,
      exeSummary 2 aliasedFile formula term 2, ["fuel=2", "hints=1"])

/-- **The rows of the grid modulo `Wrap x = x`, as written.** -/
def unwrapMatrixRows : List MatrixRow :=
  Unwrap.unwrapRows.map fun (term, formula, _, _) =>
    ("Wrapped.module", formulaText formula, patternText term, 2,
      exeSummary 2 wrappedFile formula term 2, ["fuel=2", "hints=1"])

/-- All the acceptance rows the executable runs. -/
def acceptanceMatrixRows : List MatrixRow := lambdaMatrixRows ++ aliasMatrixRows ++ unwrapMatrixRows

#guard lambdaRows.all fun (term, formula, expected) =>
  refines expected (exeSummary lambdaFuel Mettapedia.OSLF.NativeTypes.Executable.FiniteModelControls.fullLambda formula term
    lambdaRounds)
#guard aliasRows.all fun (term, formula, _, asWritten) =>
  refines asWritten (exeSummary 2 aliasedFile formula term 2)
#guard Unwrap.unwrapRows.all fun (term, formula, _, asWritten) =>
  refines asWritten (exeSummary 2 wrappedFile formula term 2)

#guard lambdaRows.all fun (term, formula, _) => readsBack formula term
#guard aliasRows.all fun (term, formula, _, _) => readsBack formula term
#guard Unwrap.unwrapRows.all fun (term, formula, _, _) => readsBack formula term

end Mettapedia.OSLF.NativeTypes.Product

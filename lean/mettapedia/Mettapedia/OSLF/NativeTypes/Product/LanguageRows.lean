import Mettapedia.OSLF.NativeTypes.Product.AcceptanceRows
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.InstanceControls
import Mettapedia.OSLF.NativeTypes.Instances.Dedukti.FrontDoorControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PetriControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.AmbientControls

/-!
# The instance languages' rows for the executable

The tree's authored languages, asked as the executable asks them (`answerWith`), with the answers the library's own
controls prove with the kernel:

- **the λ-calculus** with β at the root (`InstanceControls`): the identity applied to itself ends at the identity,
  every run from `Ω` goes on forever, and the constant function discards `Ω`;
- **TinyML** (`InstanceControls`): a conditional on `true`, forcing a thunk, a projection, and a conditional on a
  function that is stuck;
- **a Petri net** modulo its bag laws (`PetriControls`): `{A, B}` steps and `{A, D}` does not, some run from `{A, B}`
  reaches a stuck marking, and every marking it reaches is one of three; the executable gives the bag language its
  canonical forms;
- **the π-calculus** and **mobile ambients** modulo their flattening algebras (`PiControls`, `AmbientControls`): a
  communication ends at inaction, the replicated forwarder runs forever, entering ends inside the other ambient and
  not the other way round, and an ambient beside the wrong sibling is stuck; the product's answer gives these
  languages the canonical forms their own theorems certify (`certifiedFormsOf`). Their files do not yet carry the
  flattening algebras, so these rows run in the library (`fileRows`);
- **Peano arithmetic in the λΠ-calculus modulo** (`Dedukti.Controls`): `2` has no step, `2 + 3` steps, and it ends at
  `5`; the congruences reach the depth of these terms with premise fuel eight.

Each row's text reads back as its formula and term, and the library answers each row as written (`#guard`).
-/

namespace Mettapedia.OSLF.NativeTypes.Product

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.GeneratedLogic
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.InstanceControls (endsAt forever steps identity omega constant app
  lam inject yes no thunkBody)

/-- A language row: the language's file, the language, the formula, the term, the budget, the expected answer in
brief, and the premise fuel. -/
abbrev LanguageRow := String × LanguageDef × Formula 0 × Pattern × ℕ × String × ℕ

def LanguageRow.matrixRow : LanguageRow → MatrixRow
  | (file, _, formula, term, budget, expected, fuel) =>
    (file, formulaText formula, patternText term, budget, expected, [s!"fuel={fuel}", "hints=1"])

/-- The library's answer to a row, as the executable computes it. -/
def LanguageRow.answer : LanguageRow → Answer
  | (_, language, formula, term, budget, _, fuel) => answerWith { fuel := fuel } language formula term budget

def LanguageRow.agrees (row : LanguageRow) : Bool := asExpected row.2.2.2.2.2.1 row.answer

def lambdaCalc : LanguageDef := Mettapedia.OSLF.Framework.LambdaInstance.lambdaCalc
def tinyML : LanguageDef := Mettapedia.OSLF.Framework.TinyMLInstance.tinyML
def peano : LanguageDef :=
  Mettapedia.GSLT.Dedukti.Language.dkLanguage Instances.Dedukti.Controls.names
    Mettapedia.GSLT.Dedukti.PeanoFiber.peanoRules

def numeral (n : ℕ) : Pattern :=
  Mettapedia.GSLT.Dedukti.Language.encode (Mettapedia.GSLT.Dedukti.PeanoFiber.numeral n)

def sum : Pattern :=
  Mettapedia.GSLT.Dedukti.Language.encode
    (Mettapedia.GSLT.Dedukti.PeanoFiber.plus (Mettapedia.GSLT.Dedukti.PeanoFiber.numeral 2)
      (Mettapedia.GSLT.Dedukti.PeanoFiber.numeral 3))

def lambdaLanguageRows : List LanguageRow :=
  [("Lambda.module", lambdaCalc, endsAt identity, app identity identity, 4, "P closed", 2),
   ("Lambda.module", lambdaCalc, forever, omega, 4, "P closed", 2),
   ("Lambda.module", lambdaCalc, endsAt (lam omega), app constant omega, 6, "P closed", 2),
   ("Lambda.module", lambdaCalc, steps, identity, 4, "R closed", 2)]

def tinyMLRows : List LanguageRow :=
  [("TinyML.module", tinyML, endsAt (inject no), .apply "If" [inject yes, inject no, inject yes], 4, "P closed", 2),
   ("TinyML.module", tinyML, .possibly .any (.is thunkBody), inject (.apply "Thunk" [thunkBody]), 6,
     "P exploration", 2),
   ("TinyML.module", tinyML, endsAt (inject yes), inject (.apply "Thunk" [thunkBody]), 6, "R closed", 2),
   ("TinyML.module", tinyML, endsAt (inject yes), .apply "Fst" [inject (.apply "PairV" [yes, no])], 4, "P closed", 2),
   ("TinyML.module", tinyML, steps,
     .apply "If" [inject (.apply "Lam" [.lambda none (inject (.bvar 0))]), inject yes, inject no], 8,
     "R closed", 2)]

def peanoRows : List LanguageRow :=
  [("Peano.module", peano, .necessarily .any .bot, numeral 2, 8, "P closed", 8),
   ("Peano.module", peano, .possibly .any .top, sum, 8, "P exploration", 8),
   ("Peano.module", peano, .necessarily .any .bot, sum, 8, "R exploration", 8),
   ("Peano.module", peano, Instances.Dedukti.Controls.endsAt (numeral 5), sum, 8, "P closed", 8)]

def petriRows : List LanguageRow :=
  [("Petri.module", PetriControls.petriCore, PetriControls.steps, PetriControls.ab, 4, "P exploration", 2),
   ("Petri.module", PetriControls.petriCore, PetriControls.steps, PetriControls.ad, 4, "R canonical", 2),
   ("Petri.module", PetriControls.petriCore, PetriControls.reachesDeadlock, PetriControls.ab, 6, "P canonical", 2),
   ("Petri.module", PetriControls.petriCore, PetriControls.onlyThreeMarkings, PetriControls.ab, 6, "P canonical", 2),
   ("Petri.module", PetriControls.petriCore, .is PetriControls.ab, PetriControls.ba, 4, "P canonical", 2)]

def piCalc : LanguageDef := Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance.piCalc

def piRows : List LanguageRow :=
  [("Pi.module", piCalc, PiControls.endsAt PiControls.zero,
     PiControls.par [PiControls.input PiControls.zero PiControls.zero, PiControls.output PiControls.zero PiControls.zero],
     4, "P canonical", 3),
   ("Pi.module", piCalc, PiControls.endsAt PiControls.zero,
     PiControls.par [PiControls.par [PiControls.input PiControls.zero PiControls.zero, PiControls.zero],
       PiControls.output PiControls.zero PiControls.zero], 4, "P canonical", 3),
   ("Pi.module", piCalc, PiControls.forever, PiControls.forwarder, 4, "P canonical", 3)]

def ambientCalc : LanguageDef := Mettapedia.Languages.ProcessCalculi.Ambient.Mobile.ambientCalc

def ambientRows : List LanguageRow :=
  [("Ambient.module", ambientCalc,
     AmbientControls.endsAt (AmbientControls.amb AmbientControls.b (AmbientControls.amb AmbientControls.a AmbientControls.zero)),
     AmbientControls.par [AmbientControls.amb AmbientControls.a (AmbientControls.enter AmbientControls.b AmbientControls.zero),
       AmbientControls.amb AmbientControls.b AmbientControls.zero], 3, "P canonical", 6),
   ("Ambient.module", ambientCalc,
     AmbientControls.endsAt (AmbientControls.amb AmbientControls.a (AmbientControls.amb AmbientControls.b AmbientControls.zero)),
     AmbientControls.par [AmbientControls.amb AmbientControls.a (AmbientControls.enter AmbientControls.b AmbientControls.zero),
       AmbientControls.amb AmbientControls.b AmbientControls.zero], 3, "R canonical", 6),
   ("Ambient.module", ambientCalc, AmbientControls.steps,
     AmbientControls.par [AmbientControls.amb AmbientControls.a (AmbientControls.enter AmbientControls.b AmbientControls.zero),
       AmbientControls.amb AmbientControls.c AmbientControls.zero], 3, "R canonical", 6)]

/-- The instance languages' rows. -/
def languageRows : List LanguageRow :=
  lambdaLanguageRows ++ tinyMLRows ++ petriRows ++ piRows ++ ambientRows ++ peanoRows

/-- **The rows the executable runs from files**: the languages whose files read back as languages with the same
steps. The π-calculus and mobile ambients read back from their files with elaborated binding specifications and
without their flattening algebras, which module files do not write, so their certified forms do not apply to the
files' languages; their rows run in the library. -/
def fileRows : List LanguageRow := lambdaLanguageRows ++ tinyMLRows ++ petriRows ++ peanoRows

/-- The instance languages' file rows as the executable's matrix rows. -/
def languageMatrixRows : List MatrixRow := fileRows.map LanguageRow.matrixRow

/-- The instance languages written as files. -/
def instanceLanguages : List (String × LanguageDef) :=
  [("Lambda", lambdaCalc), ("TinyML", tinyML), ("Petri", { GeneratedLogic.PetriControls.petriCore with «name» := "Petri" }),
   ("Peano", peano)]

#guard languageRows.all LanguageRow.agrees
#guard languageRows.all fun (_, _, formula, term, _, _, _) => readsBack formula term

end Mettapedia.OSLF.NativeTypes.Product

import Mettapedia.Languages.MeTTa.PeTTa.ProgramQuotation
import Mettapedia.Languages.MeTTa.PeTTa.Eval

/-!
# The authored portable HOL Light MeTTa checker

The declarations below quote the actual library sources. They do not replace
any checker operation by a native HOL primitive. Source reading is the named
boundary of ProgramQuotation; execution uses the existing PeTTa semantics.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa

open Mettapedia.Languages.MeTTa.PeTTa
open SpaceSemantics (Program)
open scoped ProgramQuotation

def dataSource : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../metta/hol_light/data.metta"
    sha256 "58b381dd871ccf1e4424d986d7da964cb7cb5606ec2da77a693a76946a2f5020"

def syntaxSource : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../metta/hol_light/syntax.metta"
    sha256 "f5eeac80d3afcb344360695a8bc979c7ba87c69055f62e1cf20399a5c39bdb35"

def kernelSource : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../metta/hol_light/kernel.metta"
    sha256 "2e1f1eac49a84a341fe330dac94cfae7870e9e3578ca66e2971eb08aaf7f85aa"

def definitionsSource : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../metta/hol_light/definitions.metta"
    sha256 "4a508e14121e56801eca6de16601e6e8462d7198648347a25919503e4c4c19f1"

def derivedSource : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../metta/hol_light/derived.metta"
    sha256 "4f1a892496d2308e8b13399cc9f9e47011730e9f0dc98ec2a394fc0e455869e5"

def profileSource : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../metta/hol_light/profile.metta"
    sha256 "ec5f7504a50823155ec4c3985262dbcd513755caaa42cc91065fc1dafb677296"

def receiveSource : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../metta/hol_light/receive.metta"
    sha256 "8c84769e4964af17b904f6a9b7c0a7988cdf775f8dc5bed3da4450dd628a1c94"

def program : Program :=
  ((((((dataSource.program).append syntaxSource.program).append kernelSource.program).append definitionsSource.program).append derivedSource.program).append profileSource.program).append receiveSource.program

/-- All source modules supply equations and declarations without initializing
an ambient HOL theory or injecting a cached theorem. -/
theorem no_source_initializers :
    program.initializers = [] ∧ program.facts = [] := by
  decide

/-- The ground checker has one authored inference dispatcher. -/
theorem unique_infer :
    (program.equations.filter (fun row => row.head == "hol-light:infer")).length = 1 := by
  decide

/-- Unrecognized constructors remain ordinary data in this program. -/
theorem object_constructors_are_inert :
    ["Var", "Const", "Comb", "Abs", "Tyvar", "Tyapp", "HOL:Free", "HOL:Bound", "HOL:C",
      "HOL:Lam", "HOL:App", "HOL:Cons", "HOL:Nil", "HOL:Entry", "HOL:Thm", "HOL:Receipt"].all
      (fun head => !(Eval.ioHead head || StdLib.known head ||
        program.equations.any (fun row => row.head == head))) = true := by
  decide

end Mettapedia.Languages.HOLLight.MeTTa

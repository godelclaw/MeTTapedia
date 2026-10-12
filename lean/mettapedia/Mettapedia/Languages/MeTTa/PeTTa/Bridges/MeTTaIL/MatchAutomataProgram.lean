import Mettapedia.Languages.MeTTa.PeTTa.ProgramQuotation
import Mettapedia.Languages.MeTTa.PeTTa.PureData

/-!
# Retained MeTTa source for the two subterm matching machines

The source package is shared by the bottom-up and position-derivative
realizations. Its equations are retained verbatim as constructor data. The
quotation reader is the existing named boundary; source pins and equation
inventory checks do not themselves prove execution correspondence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataProgram

open SpaceSemantics (Program Equation)
open scoped ProgramQuotation

def source : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../metta/gslt/lib/gslt_match_automata.metta"
    sha256 "0f9c96f826e2916231ffa7dfc72a871e87baa758beae9675f39acf08d79fae51"

def program : Program := source.program

/-- Named lookup is independent of the physical position of an equation. -/
def equations (head : String) : List Equation :=
  program.equations.filter (fun equation => equation.head == head)

def equation? (head : String) : Option Equation := (equations head).head?

theorem equation_heads_unique : (program.equations.map (·.head)).Nodup := by decide +kernel

theorem no_initializers : program.initializers = [] := by decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataProgram

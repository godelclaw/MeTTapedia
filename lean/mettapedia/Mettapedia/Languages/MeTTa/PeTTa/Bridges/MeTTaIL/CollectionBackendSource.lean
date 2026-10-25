import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleExecutionProgram

/-! # Shared post-match continuation source -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionMatcherBackendExecution

open scoped ProgramQuotation

def source : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../metta/gslt/lib/gslt_collection_backend.metta"
    sha256 "f84721542634893db493c69002d0b2689ca04ed4ac633981f34f62c15d3c5b03"


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionMatcherBackendExecution

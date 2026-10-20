import Mettapedia.Languages.MeTTa.PeTTa.ProgramQuotation
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.BridgeEval
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.FiniteMuCalculusWire

/-!
# Pinned finite fixed-point evaluator source

The library is parsed from the actual MeTTa file and checked for the shared
PeTTa bridge interface. This records program identity and supported calls;
it is not an execution correspondence theorem for the finite strategy.
`NaturalCounterExecution` supplies that correspondence for the selected
counter recurrence workload, including the complete result and source meaning.
The differential gate uses typed generated wire values. Its finite-index and
carrier rejection controls do not certify an unrestricted raw-value decoder;
in particular, the supplied budget is a generated natural allowance.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.FiniteMuCalculusRuntime

open scoped ProgramQuotation

def source : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../metta/gslt/lib/gslt_native_fixed_points.metta"
    sha256 "e34a15624b3f5b725d0a646b4870708f747bc60de94d8c344d65e8aa7de12030"

def library : BridgeKit.Library := ⟨⟨[], [], [], [], []⟩, source.program, ["native:mu:"]⟩

theorem library_checked : library.check = true := by decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.FiniteMuCalculusRuntime

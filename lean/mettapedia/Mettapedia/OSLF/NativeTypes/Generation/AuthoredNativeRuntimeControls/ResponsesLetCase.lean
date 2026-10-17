import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeExamples

/-! Runtime controls for ResponsesLetCase. -/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.ResponsesLetCase

def fixtureIndex : Nat := 2

set_option stderrAsMessages false in
#eval Mettapedia.OSLF.NativeTypes.Generation.AuthoredPipeline.Controls.runResponsesFixture fixtureIndex

end Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.ResponsesLetCase

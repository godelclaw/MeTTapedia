import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeExamples

/-! Runtime controls for ResponsesMachine. -/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.ResponsesMachine

def fixtureIndex : Nat := 1

set_option stderrAsMessages false in
#eval Mettapedia.OSLF.NativeTypes.Generation.AuthoredPipeline.Controls.runResponsesFixture fixtureIndex

end Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.ResponsesMachine

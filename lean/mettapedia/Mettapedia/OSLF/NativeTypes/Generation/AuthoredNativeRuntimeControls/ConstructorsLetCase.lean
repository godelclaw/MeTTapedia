import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeExamples

/-! Runtime controls for ConstructorsLetCase. -/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.ConstructorsLetCase

def fixtureIndex : Nat := 2

set_option stderrAsMessages false in
#eval Mettapedia.OSLF.NativeTypes.Generation.AuthoredPipeline.Controls.runConstructorsFixture fixtureIndex

end Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.ConstructorsLetCase

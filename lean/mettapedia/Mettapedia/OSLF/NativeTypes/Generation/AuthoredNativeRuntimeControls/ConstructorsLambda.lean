import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeExamples

/-! Runtime controls for ConstructorsLambda. -/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.ConstructorsLambda

def fixtureIndex : Nat := 0

set_option stderrAsMessages false in
#eval Mettapedia.OSLF.NativeTypes.Generation.AuthoredPipeline.Controls.runConstructorsFixture fixtureIndex

end Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.ConstructorsLambda

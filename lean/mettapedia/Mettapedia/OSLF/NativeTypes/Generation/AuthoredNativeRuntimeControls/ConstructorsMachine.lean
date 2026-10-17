import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeExamples

/-! Runtime controls for ConstructorsMachine. -/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.ConstructorsMachine

def fixtureIndex : Nat := 1

set_option stderrAsMessages false in
#eval Mettapedia.OSLF.NativeTypes.Generation.AuthoredPipeline.Controls.runConstructorsFixture fixtureIndex

end Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.ConstructorsMachine

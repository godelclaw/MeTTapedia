import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeExamples

/-! Runtime controls for CubeBatch14. -/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.CubeBatch14

def batchIndex : Nat := 14

def check : IO Unit :=
  Mettapedia.OSLF.NativeTypes.Generation.AuthoredPipeline.Controls.runCubeFixturesBatch batchIndex

end Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.CubeBatch14

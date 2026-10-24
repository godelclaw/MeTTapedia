import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeExamples

/-! Runtime controls for CubeBatch16. -/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.CubeBatch16

def batchIndex : Nat := 16

def check : IO Unit :=
  Mettapedia.OSLF.NativeTypes.Generation.AuthoredPipeline.Controls.runCubeFixturesBatch batchIndex

end Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.CubeBatch16

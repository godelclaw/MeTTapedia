import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeExamples

/-! Runtime controls for CubeBatch15. -/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.CubeBatch15

def batchIndex : Nat := 15

def check : IO Unit :=
  Mettapedia.OSLF.NativeTypes.Generation.AuthoredPipeline.Controls.runCubeFixturesBatch batchIndex

end Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.CubeBatch15

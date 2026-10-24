import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeExamples

/-! Runtime controls for CubeBatch12. -/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.CubeBatch12

def batchIndex : Nat := 12

def check : IO Unit :=
  Mettapedia.OSLF.NativeTypes.Generation.AuthoredPipeline.Controls.runCubeFixturesBatch batchIndex

end Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.CubeBatch12

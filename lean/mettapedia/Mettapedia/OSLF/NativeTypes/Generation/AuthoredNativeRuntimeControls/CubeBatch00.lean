import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeExamples

/-! Runtime controls for CubeBatch00. -/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.CubeBatch00

def batchIndex : Nat := 0

def check : IO Unit :=
  Mettapedia.OSLF.NativeTypes.Generation.AuthoredPipeline.Controls.runCubeFixturesBatch batchIndex

end Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.CubeBatch00

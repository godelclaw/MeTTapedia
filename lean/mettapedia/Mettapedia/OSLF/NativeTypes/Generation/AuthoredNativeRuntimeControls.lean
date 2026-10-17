import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.ConstructorsLambda
import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.ResponsesLambda
import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.ProjectionsLambda
import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.ConstructorsMachine
import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.ResponsesMachine
import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.ProjectionsMachine
import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.ConstructorsLetCase
import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.ResponsesLetCase
import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.ProjectionsLetCase
import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.CubeBatch00
import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.CubeBatch01
import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.CubeBatch02
import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.CubeBatch03
import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.CubeBatch04
import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.CubeBatch05
import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.CubeBatch06
import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.CubeBatch07
import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.CubeBatch08
import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.CubeBatch09
import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.CubeBatch10
import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.CubeBatch11
import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.CubeBatch12
import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.CubeBatch13
import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.CubeBatch14
import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.CubeBatch15
import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.CubeBatch16
import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.CubeBatch17
import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.CubeBatch18
import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.CubeBatch19
import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.CubeCoverage
import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.Vocabulary
import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.Answers
import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.PrimaryReceipts
import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls.AdditionalReceipts

/-!
# Complete bounded runtime controls for authored native generation

Every imported control executes assertions through the same public installation.
The finite registry covers each original fixture and every scheduled cube slice.
The runtime coverage control compares the concatenated slices with the generated
catalogue, refusing any future catalogue that cannot fit the schedule.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls

open Mettapedia.OSLF.NativeTypes.Generation.AuthoredPipeline.Controls

def constructorFixtureIndices : List Nat :=
  [ConstructorsLambda.fixtureIndex, ConstructorsMachine.fixtureIndex, ConstructorsLetCase.fixtureIndex]

def responseFixtureIndices : List Nat :=
  [ResponsesLambda.fixtureIndex, ResponsesMachine.fixtureIndex, ResponsesLetCase.fixtureIndex]

def projectionFixtureIndices : List Nat :=
  [ProjectionsLambda.fixtureIndex, ProjectionsMachine.fixtureIndex, ProjectionsLetCase.fixtureIndex]

def cubeIndices : List Nat :=
  [CubeBatch00.batchIndex,
   CubeBatch01.batchIndex,
   CubeBatch02.batchIndex,
   CubeBatch03.batchIndex,
   CubeBatch04.batchIndex,
   CubeBatch05.batchIndex,
   CubeBatch06.batchIndex,
   CubeBatch07.batchIndex,
   CubeBatch08.batchIndex,
   CubeBatch09.batchIndex,
   CubeBatch10.batchIndex,
   CubeBatch11.batchIndex,
   CubeBatch12.batchIndex,
   CubeBatch13.batchIndex,
   CubeBatch14.batchIndex,
   CubeBatch15.batchIndex,
   CubeBatch16.batchIndex,
   CubeBatch17.batchIndex,
   CubeBatch18.batchIndex,
   CubeBatch19.batchIndex]

theorem constructors_complete : constructorFixtureIndices = List.range fixtures.length := by decide

theorem responses_complete : responseFixtureIndices = List.range fixtures.length := by decide

theorem projections_complete : projectionFixtureIndices = List.range fixtures.length := by decide

theorem cube_batches_complete : cubeIndices = cubeBatchIndices := by decide

end Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeRuntimeControls

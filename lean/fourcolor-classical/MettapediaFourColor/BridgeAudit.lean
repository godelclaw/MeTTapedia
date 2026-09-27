import MettapediaFourColor.HypermapDictionary
import MettapediaFourColor.Config4Reconstruction
import MettapediaFourColor.ClassicalAssembly
import MettapediaFourColor.GraphColoringBridge
import MettapediaFourColor.PeriodicHubcap
import MettapediaFourColor.PlaneDrawing
import FourColor.Present7Chk85
import FourColor.Bulk.Cfg.Hyb218

#print axioms Mettapedia.GraphTheory.Hypermap.Reference.planar_iff
#print axioms FourColor.Config4Reconstruction.repair
#print axioms FourColor.ClassicalAssembly.fourColorTheorem_of_checks
#print axioms FourColor.SimpleGraphBridge.colorable_of_checks
#print axioms FourColor.Bulk.Hyb218.reducible
#print axioms FourColor.f7_4555
#print axioms FourColor.PeriodicHubcap.succeeds
#print axioms Mettapedia.Topology.NearestRegions.isConnected_region
#print axioms FourColor.CompactPlaneMap.Sites.adjacent_of_contact
#print axioms FourColor.PlaneDrawing.colorable

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let prefixes : List Name := [`FourColor, `MettapediaFourColor, `Mettapedia, `Foundation]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if prefixes.any (·.isPrefixOf name) && !name.isInternal then
      count := count + 1
      for axiomName in (← liftCoreM <| collectAxioms name) do
        unless allowed.contains axiomName do
          throwError m!"Unexpected axiom in {name}: {axiomName}"
  logInfo m!"Audited {count} imported public declarations; only the three permitted axioms."

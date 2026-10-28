import Lean.Util.CollectAxioms
import Mettapedia.Coalgebra.StreamFinality
import Mettapedia.Coalgebra.StreamGSLT
import Mettapedia.Coalgebra.FiniteViewObserver
import Mettapedia.Coalgebra.CoherentPrefixTower
import Mettapedia.Coalgebra.GrowingPrefixTower
import Mettapedia.Coalgebra.CoherentFiniteViewSystem
import Mettapedia.Coalgebra.ComputationalTrinity
import Mettapedia.Coalgebra.FiniteViewComputationalTrinity
import Mettapedia.Coalgebra.GuardedFinality
import Mettapedia.Coalgebra.GuardedFiniteViewSystem
import Mettapedia.Coalgebra.InitialFinal.WellFounded
import Mettapedia.Coalgebra.InitialFinal.Recursive
import Mettapedia.Coalgebra.InitialFinal.QPFMeet
import Mettapedia.Coalgebra.InitialFinal.Instances
import Mettapedia.Coalgebra.InitialFinal.Controls

/-!
# Coalgebra

Universal properties, behavioral semantics, and operational GSLT bridges for
coalgebraic structures.
-/

-- Check the imported finite-observation core, including private proof dependencies.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for index in [:env.header.moduleNames.size] do
    unless env.header.moduleNames[index]!.getPrefix == `Mettapedia.Coalgebra do continue
    let data := env.header.moduleData[index]!
    for name in (data.constNames ++ data.extraConstNames).toList.eraseDups do
      if (env.checked.get.find? name).isNone then continue
      for dependency in (← collectAxioms name) do
        unless allowed.contains dependency do
          throwError "Nonstandard axiom dependency in {name}: {dependency}"
      count := count + 1
  logInfo m!"Coalgebra finite-observation core: {count} declarations audited"

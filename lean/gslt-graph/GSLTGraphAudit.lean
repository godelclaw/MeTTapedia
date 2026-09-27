import Mettapedia.GraphTheory.Representation.ColoringTransport
import Mettapedia.GraphTheory.Representation.MatrixOperationalTranslation
import Mettapedia.GraphTheory.FourColor.VertexConstructionGSLT
import Mettapedia.GraphTheory.FourColor.SourceConstructionGSLT
import Mettapedia.GraphTheory.FourColor.VertexConstructionLiftBoundary
import Mettapedia.OSLF.MeTTaIL.PremiseRouteSemantics
import Mettapedia.GSLT.Core.OperationalPathFibration

/-! Axiom audit of the graph representation and colouring-route library. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if ((`Mettapedia).isPrefixOf name || (`Foundation).isPrefixOf name) && !name.isInternal then
      count := count + 1
      for axiomName in (← liftCoreM <| collectAxioms name) do
        unless allowed.contains axiomName do
          throwError m!"Unexpected axiom in {name}: {axiomName}"
  logInfo m!"Audited {count} imported library declarations; only the three permitted axioms."

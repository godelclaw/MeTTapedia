import Mettapedia.GSLT.Logic.ObserverRefinement
import Mettapedia.GSLT.Core.SemanticImplementation
import Mettapedia.OSLF.Framework.HennessyMilnerNativeTypes
import Mettapedia.CognitiveArchitecture.Consciousness.TraceAndImplementation
import Mettapedia.GSLT.Weighting.QuantumJump
import Mettapedia.CognitiveArchitecture.GodelClaw.GlobalWorkspace
import Lean.Util.CollectAxioms
import Lean.Compiler.Old

open Lean Elab Command

run_cmd do
  let env ← getEnv
  for name in env.header.moduleNames do
    if name.toString.startsWith "Mettapedia." then
      logInfo m!"LOCAL-MODULE {name}"

import Mettapedia.CategoryTheory.SliceObservation
import Mettapedia.CategoryTheory.SliceObservationControls
import Mettapedia.GraphTheory.Representation.SliceSemantics
import Mettapedia.GraphTheory.Representation.CostModel
import Mettapedia.GraphTheory.Representation.MatrixSemantics
import Mettapedia.GraphTheory.Representation.EdgeListToMatrixModule
import Mettapedia.GraphTheory.Representation
import Mettapedia.Algebra.SplitComplex
import Mettapedia.ProbabilityTheory.OptimalTransport.FiniteCoupling
import Mettapedia.ProbabilityTheory.OptimalTransport
import Mettapedia.UniversalAI.UniversalHyperprior.DyadicRealization
import Mettapedia.UniversalAI.UniversalHyperprior.DyadicDivisionControls
import Mettapedia.GraphTheory.Representation.EdgeListToMatrixCost
import Mettapedia.GraphTheory.Representation.FrontierAffine
import Mettapedia.UniversalAI.UniversalHyperprior
import Mettapedia.UniversalAI
import Mettapedia.UniversalAI.UniversalHyperprior.DyadicApproximationControls
import Mettapedia.Algebra.QuadraticPresentation
import Mettapedia.Algebra.QuadraticPolynomialPresentation
import Mettapedia.Algebra.TwoDimClassification
import Mettapedia.UniversalAI.UniversalHyperprior.DyadicApproximation
import Mettapedia.GraphTheory.Representation.MatrixBridge
import Mettapedia.GraphTheory.HamiltonianDegree
import Lean.Util.CollectAxioms
import Lean.Compiler.Old

open Lean Elab Command

run_cmd do
  let modules := #[
    `Mettapedia.CategoryTheory.SliceObservation,
    `Mettapedia.CategoryTheory.SliceObservationControls,
    `Mettapedia.GraphTheory.Representation.SliceSemantics,
    `Mettapedia.GraphTheory.Representation.CostModel,
    `Mettapedia.GraphTheory.Representation.MatrixSemantics,
    `Mettapedia.GraphTheory.Representation.EdgeListToMatrixModule,
    `Mettapedia.GraphTheory.Representation,
    `Mettapedia.Algebra.SplitComplex,
    `Mettapedia.ProbabilityTheory.OptimalTransport.FiniteCoupling,
    `Mettapedia.ProbabilityTheory.OptimalTransport,
    `Mettapedia.UniversalAI.UniversalHyperprior.DyadicRealization,
    `Mettapedia.UniversalAI.UniversalHyperprior.DyadicDivisionControls,
    `Mettapedia.GraphTheory.Representation.EdgeListToMatrixCost,
    `Mettapedia.GraphTheory.Representation.FrontierAffine,
    `Mettapedia.UniversalAI.UniversalHyperprior,
    `Mettapedia.UniversalAI,
    `Mettapedia.UniversalAI.UniversalHyperprior.DyadicApproximationControls,
    `Mettapedia.Algebra.QuadraticPresentation,
    `Mettapedia.Algebra.QuadraticPolynomialPresentation,
    `Mettapedia.Algebra.TwoDimClassification,
    `Mettapedia.UniversalAI.UniversalHyperprior.DyadicApproximation,
    `Mettapedia.GraphTheory.Representation.MatrixBridge,
    `Mettapedia.GraphTheory.HamiltonianDegree]
  let allowed := #[``propext, ``Quot.sound, ``Classical.choice]
  let env ← getEnv
  for moduleName in env.header.moduleNames do
    if moduleName.toString.startsWith "Mettapedia." then
      logInfo m!"LOCAL-MODULE {moduleName}"
  let mut total := 0
  let mut theorems := 0
  let mut compilerOnly := 0
  for moduleName in modules do
    let some index := env.header.moduleNames.toList.idxOf? moduleName
      | throwError "missing audited module {moduleName}"
    let data := env.header.moduleData[index]!
    for declName in (data.constNames ++ data.extraConstNames).toList.eraseDups do
      let some info := env.checked.get.find? declName | do
        unless data.extraConstNames.contains declName do
          throwError "unavailable kernel declaration {declName}"
        compilerOnly := compilerOnly + 1
        continue
      if info matches .axiomInfo _ then throwError "new axiom {declName}"
      if info.isUnsafe then throwError "unsafe source declaration {declName}"
      if info.isPartial then
        let some parentName := Compiler.isUnsafeRecName? declName
          | throwError "partial source declaration {declName}"
        let some (.defnInfo parent) := env.checked.get.find? parentName
          | throwError "runtime helper has no kernel definition {declName}"
        unless parent.safety == .safe && parent.type == info.type do
          throwError "runtime helper lacks a safe matching kernel definition {declName}"
        compilerOnly := compilerOnly + 1
        logInfo m!"COMPILER-RECURSION {declName}: safe parent {parentName}"
        continue
      let referenced := info.type.getUsedConstants ++
        (match info with
          | .defnInfo value => value.value.getUsedConstants
          | .thmInfo value => value.value.getUsedConstants
          | .opaqueInfo value => value.value.getUsedConstants
          | _ => #[])
      for reference in referenced do
        if let some dependency := env.checked.get.find? reference then
          if dependency.isUnsafe || dependency.isPartial then
            throwError "kernel declaration uses runtime-only code {declName}: {reference}"
      let dependencies ← liftCoreM <| collectAxioms declName
      for dependency in dependencies do
        unless allowed.contains dependency do
          throwError "unpermitted dependency {declName}: {dependency}"
      total := total + 1
      if info matches .thmInfo _ then theorems := theorems + 1
      logInfo m!"AUDIT {declName}: {dependencies.toList}"
  logInfo m!"SUMMARY: {modules.size} modules, {total} kernel declarations, {theorems} theorems, {compilerOnly} compiler-only names"

import Mettapedia.GSLT.LanguageDef.ModuleFormat.RegexSelectionPayload
import Mettapedia.GSLT.LanguageDef.ModuleFormat.RegexSyntaxAuthoring
import Mettapedia.GSLT.LanguageDef.RegexSelectionEquationExecution
import Mettapedia.GSLT.LanguageDef.RegexRepetitionEquationExecution
import Mettapedia.GSLT.LanguageDef.RegexSelectionRecognition
import Mettapedia.GSLT.LanguageDef.RegexSelectionGraph
import Mettapedia.Computability.RegularLanguages.RegexPikeVM
import Mettapedia.Computability.RegularLanguages.RegexIteration
import Mettapedia.Computability.RegularLanguages.RegexTraceRendering
import Mettapedia.Computability.RegularLanguages.RegexMemoizedSearch
import Mettapedia.Computability.RegularLanguages.RegexUniformFutures
import Mettapedia.Computability.RegularLanguages.RegexClosureComposition
import Mettapedia.Computability.RegularLanguages.RegexPikeSelection
import Mettapedia.Computability.RegularLanguages.RegexPikeCoverage
import Mettapedia.Computability.RegularLanguages.RegexPikePrefix
import Mettapedia.Computability.RegularLanguages.RegexPrefixRigidity
import Mettapedia.Computability.RegularLanguages.RegexPikeOrder
import Mettapedia.Computability.RegularLanguages.RegexPikePriority
import Mettapedia.Computability.RegularLanguages.RegexEpsilonFirstArrival
import Mettapedia.Computability.RegularLanguages.RegexPriorityCycleCut
import Mettapedia.Computability.RegularLanguages.RegexPhaseComparison
import Mettapedia.Computability.RegularLanguages.RegexPikeCandidate
import Mettapedia.Computability.RegularLanguages.RegexPikeCorrespondence
import Mettapedia.Computability.RegularLanguages.RegexPublicSearch
import Mettapedia.Computability.RegularLanguages.RegexPikePublicSearch
import Mettapedia.GSLT.LanguageDef.RegexSourceCorrespondence
import Mettapedia.GSLT.LanguageDef.RegexSourceAuthored
import Mettapedia.GSLT.LanguageDef.RegexSourcePike
import Mettapedia.GSLT.LanguageDef.RegexSourceProjection
import Mettapedia.GSLT.LanguageDef.RegexCaptureObservation
import Mettapedia.GSLT.LanguageDef.RegexSourceObservation
import Mettapedia.GSLT.LanguageDef.RegexScalarSyntax
import Mettapedia.GSLT.LanguageDef.RegexScalarSyntaxControls
import Mettapedia.GSLT.LanguageDef.RegexTextIngress
import Mettapedia.GSLT.LanguageDef.RegexExtendedSyntax
import Mettapedia.GSLT.LanguageDef.RegexClassInterpretation
import Mettapedia.GSLT.LanguageDef.RegexClassMaterialization
import Mettapedia.GSLT.LanguageDef.ModuleFormat.RegexClassAuthoring
import Mettapedia.GSLT.LanguageDef.RegexUnicodeProjection
import Mettapedia.GSLT.LanguageDef.RegexUnicodePipeline
import Mettapedia.GSLT.LanguageDef.RegexDecimalValues
import Mettapedia.GSLT.LanguageDef.RegexReplacementTemplate
import Mettapedia.GSLT.LanguageDef.RegexClassSyntax
import Mettapedia.GSLT.LanguageDef.RegexClassLexing
import Mettapedia.GSLT.LanguageDef.ModuleFormat.RegexExtendedAuthoring
import Mettapedia.GSLT.LanguageDef.RegexDependentObservation
import Mettapedia.GSLT.LanguageDef.RegexLookaroundObservation
import Mettapedia.GSLT.LanguageDef.RegexObservationTrace
import Mettapedia.GSLT.LanguageDef.RegexRankedObservation
import Mettapedia.GSLT.LanguageDef.RegexExtendedCompilerSemantics
import Mettapedia.GSLT.LanguageDef.RegexExtendedEquationExecution
import Mettapedia.GSLT.LanguageDef.RegexExtendedAccumulatorExecution
import Mettapedia.GSLT.LanguageDef.RegexExtendedLoweringExecution
import Mettapedia.GSLT.LanguageDef.RegexExtendedConservativity
import Mettapedia.GSLT.LanguageDef.RegexDependentProjection
import Mettapedia.GSLT.LanguageDef.RegexDependentAuthored
import Mettapedia.GSLT.LanguageDef.RegexOrdinaryReachability
import Mettapedia.GSLT.LanguageDef.RegexObservationKernel
import Mettapedia.GSLT.LanguageDef.RegexObservationTransport
import Mettapedia.GSLT.LanguageDef.RegexExtendedGraph
import Mettapedia.GSLT.LanguageDef.RegexExtendedKernel
import Mettapedia.GSLT.LanguageDef.RegexObservationInvariant
import Mettapedia.GSLT.LanguageDef.RegexExtendedCaptureLayout
import Mettapedia.GSLT.LanguageDef.RegexPackedSelectionScan
import Mettapedia.GSLT.LanguageDef.RegexRelationMultiplicity
import Mettapedia.GSLT.LanguageDef.RegexLiteralAuthored
import Mettapedia.GSLT.Parsing.DeterministicActionCorridor

/-!
# Authored regex compilation and ordered observations

The compiler's finite `LanguageDef` has equivalent structured and `languageDef!`
presentations. Executing its extracted equations yields the independently
specified symbolic graph. For source patterns with an assertion-free regular
erasure, graph reachability preserves and reflects the independent language.
Counted source forms normalize through authored equations before compilation;
source layout survives zero counts separately from executable capture writes.

The independent source-occurrence machine preserves and reflects compiled
graph traces and selected captures. Uniform-future and prefix-history laws
track register snapshots, and closure composition retains the shared memo.
Earliest-start search is realized by the proved memoized DFS; nonoverlapping
iteration transports scalar positions to UTF-8 byte boundaries. Completed
Pike absence excludes every finite accepting trace. Its selected full thread
is exactly the independently least simple execution, and therefore agrees
with memoized DFS. Actual authored returned artifacts realize independent
source selected captures; capture-span validity follows from source control
flow and chronological register updates. Physical CST projection has a
separate attributed source judgment.

The dependent profile has its own independently authorized source operations.
Actual authored output earns unique occurrence addresses, closed targets,
finite relocation and a descending observation-call certificate. Source and
relocated code yield the same intrinsic nested observation, including capture
contents and body choice words. The kernel is independent of the particular
valid rank certificate; unused declared slots, including interior holes left
by zero counts, remain unchanged through nested observations. This profile's
full-configuration cycle discipline is distinct from the regular point-simple
Pike discipline. Native byte parsing, extraction optimizations and refinement
of the C implementation remain separate from these reference theorems.
-/

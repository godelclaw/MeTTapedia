import Mettapedia.GraphTheory.Representation.Basic
import Mettapedia.GraphTheory.Representation.SliceSemantics
import Mettapedia.GraphTheory.Representation.EdgeList
import Mettapedia.GraphTheory.Representation.AdjacencyMatrix
import Mettapedia.GraphTheory.Representation.AdjacencyRows
import Mettapedia.GraphTheory.Representation.NeighborFinsets
import Mettapedia.GraphTheory.Representation.IncidenceMatrix
import Mettapedia.GraphTheory.Representation.CSR
import Mettapedia.GraphTheory.Representation.RotationSystem
import Mettapedia.GraphTheory.Representation.Transformations
import Mettapedia.GraphTheory.Representation.RepresentationGSLT
import Mettapedia.GraphTheory.Representation.EdgeListToMatrixGSLT
import Mettapedia.GraphTheory.Representation.EdgeListToMatrixLanguageDef
import Mettapedia.GraphTheory.Representation.EdgeListToMatrixModule
import Mettapedia.GraphTheory.Representation.EdgeListToMatrixCost
import Mettapedia.GraphTheory.Representation.SemanticTransport
import Mettapedia.GraphTheory.Representation.CostModel
import Mettapedia.GraphTheory.Representation.CostedRepresentationGSLT
import Mettapedia.GraphTheory.Representation.RevisionQuery
import Mettapedia.GraphTheory.Representation.RevisionPortfolio
import Mettapedia.GraphTheory.Representation.MatrixBridge
import Mettapedia.GraphTheory.Representation.MatrixSemantics
import Mettapedia.GraphTheory.Representation.FrontierAffine
import Mettapedia.GraphTheory.Representation.NeighborTraversal
import Mettapedia.GraphTheory.Representation.SparseFrontier
import Mettapedia.GraphTheory.Representation.MaterializedSparseFrontier
import Mettapedia.GraphTheory.Representation.SparseFrontierControls
import Mettapedia.GraphTheory.Representation.WeightedSparseFrontier
import Mettapedia.GraphTheory.Representation.SparseTraversalModule
import Mettapedia.GraphTheory.Representation.ArraySparseFrontier
import Mettapedia.GraphTheory.Representation.SparseBackendChoice
import Mettapedia.GraphTheory.Representation.Hypergraph
import Mettapedia.GraphTheory.Representation.Metagraph
import Mettapedia.GraphTheory.Representation.DistinctionBridge
import Mettapedia.GraphTheory.Representation.WorldModelGSLT
import Mettapedia.GraphTheory.Representation.SemanticInvariant
import Mettapedia.GraphTheory.Representation.SemanticRevisionGSLT
import Mettapedia.GraphTheory.Representation.HigherGraphSemanticGSLT
import Mettapedia.GraphTheory.Representation.MultiView
import Mettapedia.GraphTheory.Representation.MigrationExamples

/-!
# Graph representation and behavioral portfolio

Umbrella import for ordinary graph layouts, slice-category and standard-matrix semantics,
hypergraphs, labeled metagraphs, OSLF distinction graphs, revision/query world
models, exact resource accounts, sound refinement rules, their transformation
specifications, and detailed operational GSLTs where small-step machines have
been proved. The matrix materialization language also has an independently
authored module quotation and a checked canonical text/UTF-8 transport.
Ordered neighbor enumeration connects sparse row and CSR folds to the same
matrix frontiers and walk counts. Shared fold paths retain exact entry visits
and finalization, and the module's constructed matrix feeds those sparse queries.
Weighted sparse operators retain repeated coefficients through composition;
an authored traversal module, indexed array lowering and amortized backend
choice connect their operational and matrix meanings.
-/

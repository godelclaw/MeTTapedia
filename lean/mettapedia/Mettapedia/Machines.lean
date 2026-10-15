import Mettapedia.Machines.SourceSnapshot
import Mettapedia.Machines.ReadCertifiedQueryReuse
import Mettapedia.Machines.Cursor.ProducerOccurrenceLog
import Mettapedia.Machines.Cursor.SharedFactorCost
import Mettapedia.Machines.Cursor.SharedFactorMachine
import Mettapedia.Machines.Cursor.SuffixForwarding
import Mettapedia.Machines.Cursor.ForwardedTableStore
import Mettapedia.Machines.Cursor.TermPathPostingRefinement
import Mettapedia.Machines.Cursor.KeyedPostingChains
import Mettapedia.Machines.Cursor.SharedFactor
import Mettapedia.Machines.ConeDuality
import Mettapedia.Machines.BranchLocalNeed
import Mettapedia.Machines.DepthFirstStack
import Mettapedia.Machines.RevisionedOccurrenceStore
import Mettapedia.Machines.RevisionDependencySet
import Mettapedia.Machines.FunctionalCorrespondence
import Mettapedia.Machines.MachineSubstrate
import Mettapedia.Machines.MachineRefinement
import Mettapedia.Machines.ProductiveCoreAdapters
import Mettapedia.Machines.ProductiveFunctionalMachines
import Mettapedia.Machines.ProductiveCoreOrdered
import Mettapedia.Machines.Refocusing
import Mettapedia.Machines.CategoricalAbstractMachine
import Mettapedia.Machines.OccurrenceMachine
import Mettapedia.Machines.OccurrenceCone
import Mettapedia.Machines.ReceiptReachability
import Mettapedia.Machines.RunObservation
import Mettapedia.Machines.TraceObservationBoundary
import Mettapedia.Machines.OSLFConeBridge

/-!
# Abstract-machine foundations

Shared term substrates, distinct evaluation controls, reachability cones,
refinement contracts for deterministic abstract machines, and
occurrence-preserving finite branching with explicit completion and
interruption observations for nondeterministic answer streams, together with
constructive boundaries on what flattened traces can reconstruct and exact
guards for causal-receipt reachability.

Deterministic control cores instantiate the common event-machine interface
through ordered operational occurrences. Bare missing transitions remain
stuck; answer cores use their checked answer observer. Exact finite traces,
residuals and work accounts connect those instances to the existing CEK and
Krivine machines without assuming source termination.

Kinded refocusing uses paths of licensed frames and an explicit focus. Its
source-step observer preserves residuals and instruction costs; local search
credits exclude endless administration while allowing computational divergence.
Authored MeTTaIL frames connect its stacks to the existing context representation.

The historical categorical abstract machine supplies a compiled-code instance
with independent source evaluation, instruction transitions and executable
readback. Its strict and neutral profiles retain their distinct instruction
rules; compiled answers require both an empty code sequence and an empty stack.
-/

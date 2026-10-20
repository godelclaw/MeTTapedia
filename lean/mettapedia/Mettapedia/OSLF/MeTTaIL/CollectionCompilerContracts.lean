import Mettapedia.OSLF.MeTTaIL.CollectionExecutionAdmission
import Mettapedia.OSLF.MeTTaIL.CollectionMatcherCompatibility
import Mettapedia.OSLF.MeTTaIL.CollectionMatcherBackend
import Mettapedia.OSLF.MeTTaIL.EquationalScopedMatching
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedCollectionCodec

/-!
# Collection compiler contract inventory

This inventory is executable metadata. `derived` capabilities are established
by the current admission or execution theorems. `certificate` capabilities are
accepted only through a separately proved language profile. `unsupported`
capabilities keep an admission obligation and are not silently approximated.
-/

namespace Mettapedia.OSLF.MeTTaIL.CollectionCompilerContracts

inductive Status where
  | derived
  | certificate
  | unsupported
  deriving DecidableEq, Repr

inductive Capability where
  | authoredModuleAndBinding
  | finiteBagMultiplicity
  | finiteSetReuseAndOverlap
  | recursiveLeanMatching
  | recursiveReceiptSemantics
  | ordinaryPresentationSoundness
  | ordinaryMatcherBackendAdapter
  | arrangedRootRuntime
  | planOrderedRootRuntime
  | receiptReplayAndResumption
  | typedResidualContextTransport
  | finiteSetContextEnumeration
  | repeatedCaptureComparison
  | modelNormalizationCoherence
  | dynamicPremiseProvider
  | scopeExtrusion
  | recursiveMeTTaMatching
  | emittedSetContextEnumeration
  | matchingInsideSetPremises
  | matchingInsideSetEquations
  | completeMachineEmission
  deriving DecidableEq, Repr

def status : Capability → Status
  | .authoredModuleAndBinding => .derived
  | .finiteBagMultiplicity => .derived
  | .finiteSetReuseAndOverlap => .derived
  | .recursiveLeanMatching => .derived
  | .recursiveReceiptSemantics => .derived
  | .ordinaryPresentationSoundness => .derived
  | .ordinaryMatcherBackendAdapter => .derived
  | .arrangedRootRuntime => .derived
  | .planOrderedRootRuntime => .derived
  | .receiptReplayAndResumption => .derived
  | .typedResidualContextTransport => .derived
  | .finiteSetContextEnumeration => .derived
  | .repeatedCaptureComparison => .certificate
  | .modelNormalizationCoherence => .certificate
  | .dynamicPremiseProvider => .certificate
  | .scopeExtrusion => .certificate
  | .recursiveMeTTaMatching => .unsupported
  | .emittedSetContextEnumeration => .unsupported
  | .matchingInsideSetPremises => .unsupported
  | .matchingInsideSetEquations => .unsupported
  | .completeMachineEmission => .unsupported

def all : List Capability :=
  [.authoredModuleAndBinding, .finiteBagMultiplicity, .finiteSetReuseAndOverlap,
   .recursiveLeanMatching, .recursiveReceiptSemantics, .ordinaryPresentationSoundness,
   .ordinaryMatcherBackendAdapter,
   .arrangedRootRuntime,
   .planOrderedRootRuntime,
   .receiptReplayAndResumption,
   .typedResidualContextTransport, .finiteSetContextEnumeration, .repeatedCaptureComparison,
   .modelNormalizationCoherence, .dynamicPremiseProvider, .scopeExtrusion,
   .recursiveMeTTaMatching, .emittedSetContextEnumeration,
   .matchingInsideSetPremises, .matchingInsideSetEquations, .completeMachineEmission]

def inventory : List (Capability × Status) := all.map fun capability => (capability, status capability)

example : all.Nodup := by decide
example : status .finiteSetReuseAndOverlap = .derived := rfl
example : status .modelNormalizationCoherence = .certificate := rfl
example : status .completeMachineEmission = .unsupported := rfl

end Mettapedia.OSLF.MeTTaIL.CollectionCompilerContracts

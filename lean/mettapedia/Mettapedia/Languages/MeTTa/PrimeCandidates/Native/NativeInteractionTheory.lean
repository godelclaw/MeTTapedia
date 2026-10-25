import Mettapedia.GSLT.LanguageDef.GradedLanguageDef
import Mettapedia.GSLT.Core.GradedSelectionIrreducibility
import Mettapedia.Languages.MeTTa.PrimeCandidates.Native.NativeInteractionFibration
import Mettapedia.Languages.MeTTa.PrimeCandidates.Native.NativeInteractionEffectAnalysis
import Mettapedia.Languages.MeTTa.PrimeCandidates.Native.NativeFibredCost
import Mettapedia.Languages.MeTTa.PrimeCandidates.Native.NativeFibredScheduleObservation
import Mettapedia.Languages.MeTTa.PrimeCandidates.Native.NativeInteractionObservation
import Mettapedia.Languages.MeTTa.PrimeCandidates.Native.NativeInteractionPolicies
import Mettapedia.Languages.MeTTa.PrimeCandidates.Native.NativeInteractionSeam
import Mettapedia.Languages.MeTTa.PrimeCandidates.Native.NativeFibredInteractionExample
import Mettapedia.Languages.MeTTa.PrimeCandidates.Native.GradualExecutionPlan
import Mettapedia.Languages.MeTTa.PrimeCandidates.Native.GradualDemandCost
import Mettapedia.Languages.MeTTa.PrimeCandidates.Native.NativeInteractionSyntax
import Mettapedia.Languages.MeTTa.PrimeCandidates.Native.NativeTypedProtocolExample
import Mettapedia.Languages.MeTTa.PrimeCandidates.Native.NativeQuotationAdequacy
import Mettapedia.Languages.MeTTa.PrimeCandidates.Native.NativeGradualQuotation

/-!
# candidate-native interaction theory

Intentional import gate for the candidate-native interaction stack:

* graded language construction and resolver semantics;
* crisp/graded selection separation at fixed observation granularity;
* structural non-collapse of MeTTa Native into rho syntax;
* exact occurrence-preserving interaction computations;
* capability-indexed observation of inhabited interaction fibres, with
  chronological provenance and explicitly lossy scheduler views;
* work/span accounting over chronological paths and concurrent schedules;
* proof-relevant product fibres and occurrence/resource separation licenses;
* dependent compilation of exact separation licenses into indexed concurrent
  schedules, with failed analysis producing no parallel authority;
* distinct work, span, evidence, propensity, and coalition policy readouts;
* deterministic partial endpoint interpretations;
* compile-time MeTTa expression quotations into native runtime endpoints;
* proof-producing typed quotations for a dependent native protocol fragment;
* source-preserving raw, exact, and demand-checked quotation plans with
  suspended unknown evidence and structured cached rejection;
* structural native renderer/parser inversion and checked PeTTa rendering;
* one source-to-kernel protocol joining typed endpoints, exact interaction,
  revision authority, provenance, and work/span;
* raw, typed, and demand-checked plans over one non-gating raw execution path;
* demand-sensitive work/span where undemanded and cached checks add no
  evaluation work, while the first explicit demand adds one serial unit;
* dependent, revisioned, and fibred worked examples.

Importing this module does not ratify authored syntax or claim a CeTTa runtime
implementation.  It gates the Lean semantic theory and its executable
examples as one build target.
-/

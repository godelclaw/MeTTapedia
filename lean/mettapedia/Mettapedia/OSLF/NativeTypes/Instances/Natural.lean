import Mettapedia.OSLF.NativeTypes.Instances.Natural.Authored
import Mettapedia.OSLF.NativeTypes.Instances.Natural.RepresentationControls
import Mettapedia.OSLF.NativeTypes.Instances.Natural.CoherentControls
import Mettapedia.OSLF.NativeTypes.Instances.Natural.AuthoredBoundaryControls
import Mettapedia.OSLF.NativeTypes.Instances.Natural.Backend
import Mettapedia.OSLF.NativeTypes.Instances.Natural.ExactArithmeticControls
import Mettapedia.OSLF.NativeTypes.Instances.Natural.ProviderControls
import Mettapedia.OSLF.NativeTypes.Instances.Natural.RetainedCounterControls
import Mettapedia.OSLF.Bridges.TypeTheory.AuthoredNaturalCounter
import Mettapedia.OSLF.Bridges.TypeTheory.AuthoredNaturalAdmissionControls
import Mettapedia.TypeTheory.NaturalDependentRepresentations

/-!
# Authored naturals, dependent families and native behaviour

This entrypoint joins four established interfaces:

* `.module` declarations and their actual counter/iota execution;
* dependent natural/vector signatures and their formation boundary;
* initial successor algebras for inductive, material and surreal naturals;
* native modal queries, finite parity checking and infinite-path transport.

Constructor isomorphisms preserve dependent elimination and both directions of
modal observation. Parity preserves the supported future queries through exact
outgoing coverage; it is not a replacement for a dependent index. Selected
material and surreal inverses remain semantic, while queries execute on the
retained inductive indices and their complete two-state observation.

The concrete authored natural eliminator rows bind to the existing positive,
typed iota schemas. Coherent dependent transport carries vector append and its
result-length observations. The admitted finite-word successor uses the shared
fallback contract and agrees with the actual authored counter transition,
including overflow. Its Lean qualification does not certify a CeTTa C backend.

The exact-integer coGSLT and external-call contracts supply a representation
boundary for natural addition, multiplication and guarded subtraction. A signed
fast path retains its word; fallback retains its provider carrier. Successful
values justify native natural requests without assuming resource availability.
Two-sided service additionally requires availability. The C/GMP differential
gate is separate from these Lean proofs and preserves that trust boundary.

The retained-provider span now carries its actual successful calls into the
same parity/Büchi checker. Exact infinite-path transport additionally requires
availability on retained values; a partial-provider counterexample separates
that obligation from arithmetic correctness.
-/

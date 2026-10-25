import Mettapedia.TypeTheory.ObserverErasure
import Mettapedia.GraphTheory.Walk.ModeCellProofThinnessBoundary

/-!
# Observers of walks on the path graph

Erasing which walk witnesses reachability retains the endpoint observer and not
the edge-count observer: the direct walk and the detour from vertex zero to
vertex two have two and four edges. Retaining the edge count restores that
observer and everything computed from it.

The raw native syntax has the same observer boundary: exact reconstruction
transports every proof observer to accepted terms, whereas endpoint erasure
still loses length.  The transport reuses the generic equivalence law for
observer factorization.
-/

set_option autoImplicit false

namespace Mettapedia.GraphTheory.Walk.ObserverLicences

open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.TypeTheory.ObserverErasure

open Mettapedia.GraphTheory.Walk
open Mettapedia.GraphTheory.Walk.Examples
open Mettapedia.GraphTheory.Walk.ModeCellProofThinnessBoundary
open Mettapedia.GraphTheory.Walk.ProofTheory
open Mettapedia.TypeTheory.LocallyThinCellReflection

/-- Encoding as an accepted native term preserves every proof observer. -/
theorem accepted_encoding_retains_observer {n : Nat}
    (graph : SimpleGraph (Fin n)) [DecidableRel graph.Adj]
    (start finish : Fin n) {Output : Type*}
    (observe : NativeProof graph start finish → Output) :
    Factors (NativeProof.acceptedEquiv graph start finish) observe :=
  ⟨observe ∘ (NativeProof.acceptedEquiv graph start finish).symm,
    fun proof => by simp⟩

/-- Which walk witnesses reachability from vertex zero to vertex two. -/
abbrev Witness := NativeProof pathGraph vertex0 vertex2

/-- The endpoint observer: the walk ends at vertex two. -/
def endpoint (_ : Witness) : Unit := ()

/-- Erasing the walk retains the endpoint observer. -/
theorem endpoint_factors : Factors (reflect (Cell := Witness)) endpoint :=
  ⟨fun _ => (), fun _ => rfl⟩

/-- Erasing the walk does not retain the edge-count observer: the direct walk
and the detour reach the same endpoint with two and four edges. -/
theorem proofLength_not_factors : ¬ Factors (reflect (Cell := Witness)) proofLength :=
  (factorsThrough_iff_factors proofLength).not.mp
    proof_length_does_not_factor_through_thin_reflection

/-- Keeping the edge count alongside the erasure restores the edge-count
observer and everything computed from it, such as a bound on the work. -/
theorem boundedWork_factors_when_retained :
    Factors (fun w : Witness => (reflect w, proofLength w))
      (fun w => decide (proofLength w ≤ 3)) :=
  (factors_retain (reflect (Cell := Witness)) proofLength).post (fun n => decide (n ≤ 3))

/-- All raw native terms at this endpoint fibre, with no canonical-image
restriction in the carrier. -/
abbrev AcceptedWitness :=
  {term : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern //
    NativeTypeTheory.NativeWalk pathGraph pathGraph SimpleGraph.Hom.id vertex0 vertex2 term}

/-- Exact edge count recovered from an arbitrary accepted native term. -/
noncomputable def acceptedLength : AcceptedWitness → Nat :=
  proofLength ∘ (NativeProof.acceptedEquiv pathGraph vertex0 vertex2).symm

@[simp] theorem acceptedLength_encoding (proof : Witness) :
    acceptedLength (NativeProof.acceptedEquiv pathGraph vertex0 vertex2 proof) =
      proofLength proof := by
  simp [acceptedLength]

/-- The endpoint-only observer survives the same erasure on raw native terms. -/
theorem accepted_endpoint_factors :
    Factors
      (reflect ∘ (NativeProof.acceptedEquiv pathGraph vertex0 vertex2).symm)
      (endpoint ∘ (NativeProof.acceptedEquiv pathGraph vertex0 vertex2).symm) :=
  (factors_precomp_equiv_iff
    (NativeProof.acceptedEquiv pathGraph vertex0 vertex2).symm reflect endpoint).2
    endpoint_factors

/-- Exact native reconstruction preserves the original length obstruction;
it does not identify walks merely because they reach the same endpoint. -/
theorem acceptedLength_not_factors :
    ¬ Factors
      (reflect ∘ (NativeProof.acceptedEquiv pathGraph vertex0 vertex2).symm)
      acceptedLength :=
  (not_factors_precomp_equiv_iff
    (NativeProof.acceptedEquiv pathGraph vertex0 vertex2).symm reflect proofLength).2
    proofLength_not_factors

theorem accepted_direct_and_detour_lengths :
    acceptedLength (NativeProof.acceptedEquiv pathGraph vertex0 vertex2 directProof) = 2 ∧
      acceptedLength (NativeProof.acceptedEquiv pathGraph vertex0 vertex2 detourProof) = 4 := by
  simp

#print axioms accepted_encoding_retains_observer
#print axioms acceptedLength_encoding
#print axioms accepted_endpoint_factors
#print axioms acceptedLength_not_factors
#print axioms accepted_direct_and_detour_lengths
#print axioms endpoint_factors
#print axioms proofLength_not_factors
#print axioms boundedWork_factors_when_retained

end Mettapedia.GraphTheory.Walk.ObserverLicences

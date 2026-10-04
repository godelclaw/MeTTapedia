import MettapediaFourColor.StripSixConnection
import Mettapedia.GraphTheory.Kempe.NeighborRelease

/-! # A neighbour-controlled continuation of the port-six branch

In the second boundary form, the original zero/one switch can release port
three rather than port six. Its old zero-coloured neighbours must all be
switched, and no old one-coloured neighbour may be switched. The resulting
singleton zero/three switch and a common core formula reconstruct the
source. These are explicit old-state conditions, not a universal supply law.
-/

namespace FourColor.StripSixRelease

open SimpleGraph Color StripResponseSummary StripSourceExtension
open Mettapedia.GraphTheory.FourColor.KempeChainCertificate

def switchedPorts : List (Fin 11) := [0,1,2,6,10]
def middle : Boundary := ![c1,c0,c1,c3,c2,c3,c0,c2,c1,c3,c0]
def boundary (i : Fin 11) : Color := if i = 3 then c0 else middle i
def coreColour : Fin 8 → Color := ![c3,c0,c3,c1,c2,c2,c1,c3]

theorem input_ready : ∀ i, StripSixConnection.input true i ∈ StripSingletonRepair.before i := by
  decide +kernel
theorem active_ports : ∀ i, i ∉ switchedPorts →
    (StripSixConnection.input true i = c0 ∨ StripSixConnection.input true i = c1) → i = 8 := by
  decide +kernel
theorem middle_check : ∀ i,
    (if i ∈ switchedPorts then Equiv.swap c0 c1 (StripSixConnection.input true i)
      else StripSixConnection.input true i) = middle i := by decide +kernel
theorem core_valid : ValidCore boundary coreColour := by
  unfold ValidCore
  decide +kernel

variable {V : Type*} {G : SimpleGraph V} [DecidableEq V]
  (C : G.Coloring Color) (ports : Fin 11 → V)
  (embedding : ∀ i j, TriangleStripAnchors.input0099.graph.Adj (port i) (port j) →
    G.Adj (ports i) (ports j))
  (initial : ∀ i, C (ports i) = StripSixConnection.input true i)
  (K : (C.bicoloredSubgraph c0 c1).ConnectedComponent)
  (m1 : ports 1 ∈ C.kempeComponentSet c0 c1 K)
  (m6 : ports 6 ∈ C.kempeComponentSet c0 c1 K)
  (n8 : ports 8 ∉ C.kempeComponentSet c0 c1 K)

include embedding initial m1 m6 n8 in
theorem first_members (i : Fin 11) :
    ports i ∈ C.kempeComponentSet c0 c1 K ↔ i ∈ switchedPorts := by
  have ready : ∀ j, C (ports j) ∈ StripSingletonRepair.before j := by
    intro j; rw [initial]; exact input_ready j
  constructor
  · intro h
    by_contra outside
    have active := C.mem_bicoloredSet_of_mem_kempeComponentSet h
    rw [initial] at active
    have eq := active_ports i outside active
    exact n8 (eq ▸ h)
  · intro h
    simp only [switchedPorts,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl
    · exact StripSingletonRepair.forced C ports K ready m1 embedding 0 (by decide)
    · exact m1
    · exact StripSingletonRepair.forced C ports K ready m1 embedding 2 (by decide)
    · exact m6
    · exact StripSingletonRepair.forced C ports K ready m1 embedding 10 (by decide)

include embedding initial m1 m6 n8 in
theorem first_values (i : Fin 11) : (C.swapOnKempeComponent c0 c1 K) (ports i) = middle i := by
  classical
  change (if ports i ∈ C.kempeComponentSet c0 c1 K then
    Equiv.swap c0 c1 (C (ports i)) else C (ports i)) = _
  simpa only [first_members C ports embedding initial K m1 m6 n8,initial] using middle_check i

include embedding initial m1 m6 n8 in
theorem repair (injective : Function.Injective ports)
    (exits : ∀ y, G.Adj (ports 3) y → C y = c0 → y ∈ C.kempeComponentSet c0 c1 K)
    (no_entry : ∀ y ∈ C.kempeComponentSet c0 c1 K, G.Adj (ports 3) y → C y ≠ c1) :
    ∃ D : G.Coloring Color, ∃ h : History C D, h.length = 2 ∧
      ∃ k : TriangleStripAnchors.input0099.graph.Coloring Color,
        ∀ i, k (port i) = D (ports i) := by
  classical
  have colour : C (ports 3) = c3 := initial 3
  let second := KempeNeighborRelease.second C c0 c1 c3 K (ports 3) colour
    (by decide) (by decide) (by decide) exits no_entry
  let D := second.swap
  have values (i : Fin 11) : D (ports i) = boundary i := by
    rw [show D (ports i) = if ports i = ports 3 then c0 else
      (C.swapOnKempeComponent c0 c1 K) (ports i) from
        KempeNeighborRelease.endpoint C c0 c1 c3 K (ports 3) colour
          (by decide) (by decide) (by decide) exits no_entry (ports i)]
    simp only [injective.eq_iff,first_values C ports embedding initial K m1 m6 n8,boundary]
  have actual : ValidCore (fun i => D (ports i)) coreColour := by
    simpa only [values] using core_valid
  let k := colouring (fun i => D (ports i)) coreColour
    (fun i j edge => D.valid (embedding i j edge)) actual
  refine ⟨D,KempeNeighborRelease.history C c0 c1 c3 K (ports 3) colour
    (by decide) (by decide) (by decide) exits no_entry,rfl,k,?_⟩
  intro i
  exact colour_port (fun j => D (ports j)) coreColour i

end FourColor.StripSixRelease

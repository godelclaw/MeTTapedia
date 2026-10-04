import MettapediaFourColor.StripSixConnection
import Mettapedia.GraphTheory.Kempe.ComponentDetach
import Mettapedia.GraphTheory.Kempe.SeparatedChains

/-!
# A silent detachment repairs either port-six boundary form

A zero/three switch away from the boundary removes every active exit of a
connected two/three set meeting the boundary only at port seven. No new
active exit is introduced. The set then becomes a physical component whose
switch admits a common source reconstruction. Both boundary forms use the
same argument, with no bound on the exterior, first component or chain size.
-/

namespace FourColor.StripSixDetachment

open SimpleGraph Color StripResponseSummary StripSourceExtension
open Mettapedia.GraphTheory.FourColor.KempeChainCertificate

def boundary (s : Bool) (i : Fin 11) : Color :=
  if i = 7 then c3 else StripSixConnection.input s i

def coreColour (s : Bool) : Fin 8 → Color :=
  ![c2,c3,c1,c0,c2,if s then c2 else c3,c0,if s then c3 else c2]

theorem core_valid : ∀ s, ValidCore (boundary s) (coreColour s) := by
  unfold ValidCore
  decide +kernel

/-- Old-state exit information supplies the next component, rather than
assuming a prechecked successful continuation. -/
theorem repair {W : Type*} {H : SimpleGraph W}
    (C : H.Coloring Color) (ports : Fin 11 → W)
    (embedding : ∀ i j, TriangleStripAnchors.input0099.graph.Adj (port i) (port j) →
      H.Adj (ports i) (ports j))
    (s : Bool) (initial : ∀ i, C (ports i) = StripSixConnection.input s i)
    (K : (C.bicoloredSubgraph c3 c0).ConnectedComponent)
    (silent : ∀ i, ports i ∉ C.kempeComponentSet c3 c0 K)
    (chain : List W) (connected : chain.IsChain H.Adj)
    (at7 : ports 7 ∈ chain)
    (active : ∀ x ∈ chain, C x = c3 ∨ C x = c2)
    (boundary_only : ∀ i, ports i ∈ chain ↔ i = 7)
    (apart : ∀ x ∈ chain, x ∉ C.kempeComponentSet c3 c0 K)
    (exits : ∀ x ∈ chain, ∀ y, y ∉ chain → H.Adj x y →
      (C y = c3 ∨ C y = c2) → y ∈ C.kempeComponentSet c3 c0 K)
    (no_entry : ∀ x ∈ chain, ∀ y ∈ C.kempeComponentSet c3 c0 K,
      H.Adj x y → C y ≠ c0) :
    ∃ D : H.Coloring Color, ∃ h : History C D, h.length = 2 ∧
      ∃ k : TriangleStripAnchors.input0099.graph.Coloring Color,
        ∀ i, k (port i) = D (ports i) := by
  classical
  let M := C.swapOnKempeComponent c3 c0 K
  let S : Set W := {x | x ∈ chain}
  have disjoint : Disjoint S (C.kempeComponentSet c3 c0 K) :=
    Set.disjoint_left.mpr apart
  have retained := KempeComponentDetach.active_after_swap C c3 c0 c2 K S disjoint active
  have closed := KempeComponentDetach.closed_after_swap C c3 c0 c2 K S
    (by decide) (by decide) exits no_entry
  let T : KempeSeparatedChains.Certificate M c3 c2 :=
    ⟨chain,ports 7,at7,connected,retained,closed⟩
  have middle (i : Fin 11) : M (ports i) = StripSixConnection.input s i :=
    (C.swapOnKempeComponent_apply_of_not_mem (silent i)).trans (initial i)
  have values (i : Fin 11) : T.swap (ports i) = boundary s i := by
    rw [T.swap_apply]
    change (if ports i ∈ chain then Equiv.swap c3 c2 (M (ports i)) else M (ports i)) = _
    simp only [boundary_only,middle]
    by_cases hi : i = 7
    · subst i
      cases s <;> simp [boundary,StripSixConnection.input]
    · simp [hi,boundary]
  have core : ValidCore (fun i => T.swap (ports i)) (coreColour s) := by
    simpa only [values] using core_valid s
  let k := colouring (fun i => T.swap (ports i)) _
    (fun i j edge => T.swap.valid (embedding i j edge)) core
  exact ⟨T.swap,.cons (.switch C c3 c0 K) (.cons T.step (.refl _)),rfl,
    k,fun i => colour_port (fun j => T.swap (ports j)) _ i⟩

end FourColor.StripSixDetachment

import MettapediaFourColor.StripSixConnection
import Mettapedia.GraphTheory.Kempe.SeparatedChains
import Mettapedia.GraphTheory.Kempe.Symm

/-! # Two switches of one colour pair reconstruct the port-six patch

The one/two component through port six is retained as an actual exterior
component. If it avoids ports four and ten, an isolated port-one switch
and a switch of that component admit a fixed core colouring. The component
is transported through the first switch by preservation of the bicoloured
vertex set. Exterior size and component size are unrestricted.
-/

namespace FourColor.StripSixSamePair

open SimpleGraph Color StripResponseSummary StripSourceExtension
open Mettapedia.GraphTheory.FourColor.KempeChainCertificate

def boundary : Boundary := ![c0,c2,c0,c3,c2,c3,c2,c1,c2,c3,c1]
def coreColour : Fin 8 → Color := ![c0,c3,c0,c1,c1,c1,c2,c3]

theorem core_valid : ValidCore boundary coreColour := by
  unfold ValidCore
  decide +kernel

/-- The singleton and the retained component give an actual two-step
history and a compatible colouring of the complete decoded source. -/
theorem repair {V : Type*} {G : SimpleGraph V}
    (C : G.Coloring Color) (ports : Fin 11 → V)
    (injective : Function.Injective ports)
    (embedding : ∀ i j, TriangleStripAnchors.input0099.graph.Adj (port i) (port j) →
      G.Adj (ports i) (ports j))
    (initial : ∀ i, C (ports i) = StripSixConnection.input true i)
    (missing : ∀ v, G.Adj (ports 1) v → C v ≠ c2)
    (K : (C.bicoloredSubgraph c1 c2).ConnectedComponent)
    (m6 : ports 6 ∈ C.kempeComponentSet c1 c2 K)
    (n4 : ports 4 ∉ C.kempeComponentSet c1 c2 K)
    (n10 : ports 10 ∉ C.kempeComponentSet c1 c2 K) :
    ∃ D : G.Coloring Color, ∃ h : History C D, h.length = 2 ∧
      ∃ k : TriangleStripAnchors.input0099.graph.Coloring Color,
        ∀ i, k (port i) = D (ports i) := by
  classical
  have c1 : C (ports 1) = Color.c1 := initial 1
  let S : KempeSeparatedChains.Certificate C Color.c1 c2 := {
    vertices := [ports 1]
    root := ports 1
    root_mem := by simp
    connected := by simp
    active := by
      intro x hx
      have eq : x = ports 1 := by simpa using hx
      exact Or.inl (eq ▸ c1)
    closed := by
      intro x hx y edge active
      have eq : x = ports 1 := by simpa using hx
      subst x
      rcases active with h | h
      · exact (C.valid edge (c1.trans h.symm)).elim
      · exact (missing y edge h).elim }
  have n1 : ports 1 ∉ C.kempeComponentSet Color.c1 c2 K := by
    rintro ⟨active,eq⟩
    have same : S.component = K := eq
    have belong : ports 6 ∈ C.kempeComponentSet Color.c1 c2 S.component := by
      rw [same]; exact m6
    have impossible : (6 : Fin 11) = 1 :=
      injective (by simpa [S] using (S.component_mem (ports 6)).mp belong)
    exact (by decide : (6 : Fin 11) ≠ 1) impossible
  have m7 : ports 7 ∈ C.kempeComponentSet Color.c1 c2 K :=
    C.mem_kempeComponentSet_of_adj m6 (embedding 6 7 (by decide +kernel))
      (Or.inr (initial 7))
  have m8 : ports 8 ∈ C.kempeComponentSet Color.c1 c2 K :=
    C.mem_kempeComponentSet_of_adj m7 (embedding 7 8 (by decide +kernel))
      (Or.inl (initial 8))
  have inactive (i : Fin 11) (h1 : StripSixConnection.input true i ≠ Color.c1)
      (h2 : StripSixConnection.input true i ≠ c2) :
      ports i ∉ C.kempeComponentSet Color.c1 c2 K := by
    intro h
    have a := C.mem_bicoloredSet_of_mem_kempeComponentSet h
    rw [initial] at a
    exact a.elim h1 h2
  have footprint : ∀ i, ports i ∈ C.kempeComponentSet Color.c1 c2 K ↔
      i = 6 ∨ i = 7 ∨ i = 8 := by
    intro i
    fin_cases i <;> simp [n1,n4,n10,m6,m7,m8,
      inactive 0 (by decide) (by decide), inactive 2 (by decide) (by decide),
      inactive 3 (by decide) (by decide), inactive 5 (by decide) (by decide),
      inactive 9 (by decide) (by decide)]
  obtain ⟨L,transport⟩ := C.exists_kempeComponentSet_eq_of_bicoloredSet_eq S.swap
    (C.bicoloredSet_swapOnKempeComponent Color.c1 c2 S.component).symm K
  let D := S.swap.swapOnKempeComponent Color.c1 c2 L
  have end_values (i : Fin 11) : D (ports i) = boundary i := by
    change (if ports i ∈ S.swap.kempeComponentSet Color.c1 c2 L then
      Equiv.swap Color.c1 c2 (S.swap (ports i)) else S.swap (ports i)) = _
    rw [transport,footprint,S.swap_apply]
    have at1 : ports i ∈ S.vertices ↔ i = 1 := by
      simpa [S] using injective.eq_iff
    simp only [at1,initial]
    fin_cases i <;> decide
  have actual : ValidCore (fun i => D (ports i)) coreColour := by
    simpa only [end_values] using core_valid
  let k := colouring (fun i => D (ports i)) coreColour
    (fun i j edge => D.valid (embedding i j edge)) actual
  refine ⟨D,.cons S.step (.cons (.switch S.swap Color.c1 c2 L) (.refl D)),rfl,k,?_⟩
  intro i
  change completeColour (fun j => D (ports j)) coreColour (port i) = _
  exact colour_port _ _ i

end FourColor.StripSixSamePair

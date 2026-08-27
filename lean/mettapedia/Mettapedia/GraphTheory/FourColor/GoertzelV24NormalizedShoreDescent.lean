import Mettapedia.GraphTheory.FourColor.GoertzelV24NormalizedSeamState
import Mettapedia.GraphTheory.FourColor.GoertzelV24ShoreStateDescent

/-!
# Shore descent with the exact normalized receipt

This is the consumer-facing assembly of the two preceding interfaces.  The
varying-width state is no longer an abstract `SeamType`: at width `j` it is
literally the normalized hub permutation together with the finite realizable
Tait-word support.  Cardinality phasing then gives the explicit raw bound.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24NormalizedShoreDescent

open GoertzelV24FiniteTreeInterfacePumping
open GoertzelV24FiniteTreeInterfacePumping.DecompTree
open GoertzelV24NormalizedSeamState
open GoertzelV24ShoreDescentMaterial
open GoertzelV24ShoreStateDescent
open GoertzelV24SphereCutMaterial
open scoped Classical

universe u

/-- The exact normalized receipt at some literal width `j ≤ k`. -/
abbrev StateAtBound (k : Nat) :=
  Σ j : Fin (k + 1), State.{u} (j : Nat)

/-- Exact raw number of varying-width normalized receipts. -/
theorem card_stateAtBound (k : Nat) :
    Fintype.card (StateAtBound.{u} k) =
      ∑ j : Fin (k + 1), Nat.factorial (j : Nat) * 2 ^ (3 ^ (j : Nat)) := by
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro j _
  exact card_state.{u} (j : Nat)

variable {E V : Type u} [Fintype E] [DecidableEq E]
  [Fintype V] [DecidableEq V]

/-- **The exact finite-state shore bound.**  The only remaining local premise
is now the physical fact that equal normalized receipts at nested shores,
together with a strict slab vertex, yield a smaller target instance. -/
theorem vertexCount_le_of_cardPhasedNormalizedShore
    {Inst : Type*} {size vertexCount : Inst → ℕ}
    {Target : Inst → Prop} {X : Inst} {k w : ℕ}
    (state : Finset E → StateAtBound.{u} k)
    (incident : V → E → Prop) {tree : DecompTree (Finset E)}
    (hstrict : StrictShoreTree tree)
    (hedge : ∀ edge : E, ∃ vertex : V, incident vertex edge)
    (hcubic : ∀ vertex : V,
      (Finset.univ.filter fun edge => incident vertex edge).card ≤ 3)
    (hmiddle : ∀ p : List (Finset E), OnPath tree p →
      ∀ i : Fin p.length,
        (middleVertices incident (p.get i)).card ≤ w)
    (hvertices : vertexCount X ≤ 2 * nodeCount tree)
    (hsplice : ∀ outer inner : Finset E, inner ⊆ outer →
      state outer = state inner →
      (∃ vertex : V,
        (∃ edge ∈ outer \ inner, incident vertex edge) ∧
          ∀ edge, incident vertex edge → edge ∈ outer \ inner) →
      ∃ Y, Target Y ∧ size Y < size X)
    (hmin : ∀ Y, Target Y → size X ≤ size Y) :
    vertexCount X ≤
      2 * (2 ^ ((6 * w + 1) *
        (∑ j : Fin (k + 1),
          Nat.factorial (j : Nat) * 2 ^ (3 ^ (j : Nat)))) - 1) := by
  rw [← card_stateAtBound.{u} k]
  exact vertexCount_le_of_cardPhasedShore state incident w hstrict hedge
    hcubic hmiddle hvertices hsplice hmin

end GoertzelV24NormalizedShoreDescent

end Mettapedia.GraphTheory.FourColor

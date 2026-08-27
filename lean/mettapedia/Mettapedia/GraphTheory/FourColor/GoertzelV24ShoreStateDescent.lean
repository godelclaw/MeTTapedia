import Mettapedia.GraphTheory.FourColor.GoertzelV24ShoreDescentMaterial
import Mettapedia.GraphTheory.FourColor.GoertzelV24SphereCutDescent
import Mathlib.Data.List.GetD

/-!
# Cardinality-phased finite-state descent on edge shores

The strict-material argument can be packaged without adding node depth to a
decomposition tree.  Tag the exact state of an edge shore `S` by
`S.card % (6 * w + 1)`.  Two strictly nested shores with the same tag differ
by at least `6 * w + 1` edges, so the cubic slab lemma supplies a vertex lying
strictly between them.  This makes the augmented state a function of the shore
itself and leaves only the local physical splice as a caller obligation.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ShoreStateDescent

open GoertzelV24FiniteTreeInterfacePumping
open GoertzelV24FiniteTreeInterfacePumping.DecompTree
open GoertzelV24ShoreDescentMaterial
open GoertzelV24SphereCutDescent
open GoertzelV24SphereCutMaterial
open scoped Classical

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The shore-cardinality phase used to force a large strict slab. -/
def shoreCardPhase (w : ℕ) (shore : Finset E) : Fin (6 * w + 1) :=
  ⟨shore.card % (6 * w + 1), Nat.mod_lt _ (by omega)⟩

/-- An exact shore state augmented by its cardinality phase. -/
def cardPhasedState {Q : Type*} (w : ℕ) (state : Finset E → Q)
    (shore : Finset E) : Fin (6 * w + 1) × Q :=
  (shoreCardPhase w shore, state shore)

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Equal cardinality phases on two strictly nested shores force enough slab
edges for the cubic material lemma. -/
theorem exists_strict_slab_vertex_of_cardPhaseRepeat
    (incident : V → E → Prop) (w : ℕ) {inner outer : Finset E}
    (hstrict : inner ⊂ outer)
    (hedge : ∀ edge : E, ∃ vertex : V, incident vertex edge)
    (hcubic : ∀ vertex : V,
      (Finset.univ.filter fun edge => incident vertex edge).card ≤ 3)
    (hmiddleInner : (middleVertices incident inner).card ≤ w)
    (hmiddleOuter : (middleVertices incident outer).card ≤ w)
    (hphase : shoreCardPhase w inner = shoreCardPhase w outer) :
    ∃ vertex : V,
      (∃ edge ∈ outer \ inner, incident vertex edge) ∧
        ∀ edge, incident vertex edge → edge ∈ outer \ inner := by
  have hcard : inner.card < outer.card := Finset.card_lt_card hstrict
  have hmod : inner.card % (6 * w + 1) = outer.card % (6 * w + 1) :=
    congrArg Fin.val hphase
  have hperiod : 6 * w + 1 ≤ outer.card - inner.card :=
    period_le_sub_of_mod_eq hcard hmod
  apply exists_strict_slab_vertex_of_cubic incident inner outer w hedge hcubic
    hmiddleInner hmiddleOuter
  rw [Finset.card_sdiff_of_subset hstrict.1]
  omega

/-- **Cardinality-phased shore descent.**

On a strict edge-shore decomposition with width-`w` middle sets, a repeated
augmented state gives exactly the strict slab vertex required by the local
splice.  Minimality therefore bounds the vertex count by the number of
augmented states. -/
theorem vertexCount_le_of_cardPhasedShore
    {Q Inst : Type*} [Fintype Q]
    {size vertexCount : Inst → ℕ} {Target : Inst → Prop} {X : Inst}
    (state : Finset E → Q) (incident : V → E → Prop) (w : ℕ)
    {tree : DecompTree (Finset E)}
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
      2 * (2 ^ ((6 * w + 1) * Fintype.card Q) - 1) := by
  let augmented : Finset E → Fin (6 * w + 1) × Q :=
    cardPhasedState w state
  have hbound : vertexCount X ≤
      2 * (2 ^ Fintype.card (Fin (6 * w + 1) × Q) - 1) := by
    apply vertexCount_le_of_minimal (state := augmented)
      (tree := fun _ => tree) hvertices
    · intro p hpath i j hij heq
      have hslab := card_slab_of_onPath hpath hstrict j.isLt hij
      rw [List.getD_eq_get p ∅ i, List.getD_eq_get p ∅ j] at hslab
      have hne : p.get j ≠ p.get i := by
        intro hequal
        rw [hequal] at hslab
        simp at hslab
        omega
      have hproper : p.get j ⊂ p.get i :=
        Finset.ssubset_iff_subset_ne.mpr ⟨hslab.1, hne⟩
      have hphase :
          shoreCardPhase w (p.get i) = shoreCardPhase w (p.get j) :=
        congrArg Prod.fst heq
      have hstate : state (p.get i) = state (p.get j) :=
        congrArg Prod.snd heq
      apply hsplice (p.get i) (p.get j) hproper.1 hstate
      exact exists_strict_slab_vertex_of_cardPhaseRepeat incident w hproper
        hedge hcubic (hmiddle p hpath j) (hmiddle p hpath i) hphase.symm
    · exact hmin
  simpa only [Fintype.card_prod, Fintype.card_fin] using hbound

/-- The preceding bound specialized to the exact varying-width seam-and-support
state used by the sphere-cut descent. -/
theorem vertexCount_le_of_cardPhasedTypedShore
    {Inst : Type*} {size vertexCount : Inst → ℕ}
    {Target : Inst → Prop} {X : Inst} {k w : ℕ}
    {SeamType : ℕ → Type} [∀ j, Fintype (SeamType j)]
    (state : Finset E → TypedStateAtBound k SeamType)
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
          Fintype.card (SeamType j) * 2 ^ (3 ^ (j : ℕ)))) - 1) := by
  rw [← card_typedStateAtBound]
  exact vertexCount_le_of_cardPhasedShore state incident w hstrict hedge
    hcubic hmiddle hvertices hsplice hmin

end GoertzelV24ShoreStateDescent

end Mettapedia.GraphTheory.FourColor

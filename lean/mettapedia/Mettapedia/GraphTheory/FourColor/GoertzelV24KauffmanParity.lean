import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeSwitchSquare

/-!
# The formation curve count and its parity under a Kempe switch

For a Tait colouring `C` of a cubic graph, the formation curve count is the
total number of two-colour circuits,

    Δ(C) = N_ab(C) + N_ac(C) + N_bc(C),

each two-colour subgraph being `2`-regular, so that its components are
circuits.  The published parity lemma says a switch on one two-colour circuit
preserves `Δ` modulo two.

That statement splits cleanly into two halves at the switched pair.

* **The switched pair is unchanged.**  Switching the two colours on one
  `(a,b)`-component leaves the `(a,b)`-subgraph isomorphic to itself, so
  `N_ab` is literally invariant.  This half is proved here, from the
  isomorphism already available in the development together with the bijection
  of connected components induced by a graph isomorphism.
* **The two cross pairs change together, evenly.**  The switch does move
  `N_ac` and `N_bc` individually.  The source's proof shows their *sum* changes
  by an even amount, and that is where its topological input sits: the
  idemposition parity formula `(L-R)/2 + B`, resting on the even-intersection
  property of two Jordan curves in the sphere.  No combinatorial Jordan curve
  or planar separation theorem is available here, so this half is recorded as
  `CrossCurveParityPrinciple` and used as an explicit hypothesis.

The parity lemma is then proved from the two halves, and the arithmetic core of
Kauffman's equivalence argument — five is odd, four is even, parity is
preserved — is proved outright.

Planarity is essential to the missing half, not to the proved one: the
one-edge-deleted Petersen formation changes its curve count from five to four
under a simple operation, so any statement of the missing principle that omits
the spherical hypothesis is false.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24KauffmanParity

open SimpleGraph

variable {V α : Type*} {G : SimpleGraph V}

/-- The number of two-colour circuits on a pair of colours: the components of
the induced subgraph on the vertices carrying either colour. -/
noncomputable def bicoloredComponentCount (C : G.Coloring α) (a b : α) : ℕ :=
  Nat.card ((C.bicoloredSubgraph a b).ConnectedComponent)

/-- **The switched pair is unchanged.**  A switch on one `(a,b)`-component
leaves the `(a,b)`-subgraph isomorphic to itself, hence leaves the number of
`(a,b)`-circuits literally invariant. -/
theorem bicoloredComponentCount_swapOnKempeComponent [DecidableEq α]
    (C : G.Coloring α) (a b : α)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent) :
    bicoloredComponentCount (C.swapOnKempeComponent a b K) a b =
      bicoloredComponentCount C a b :=
  Nat.card_congr
    (SimpleGraph.Iso.connectedComponentEquiv
      (SimpleGraph.Coloring.bicoloredSubgraphIsoSwapOnKempeComponent C a b K))

/-- The formation curve count: the total number of two-colour circuits over the
three colour pairs. -/
noncomputable def formationCurveCount (C : G.Coloring α) (a b c : α) : ℕ :=
  bicoloredComponentCount C a b + bicoloredComponentCount C a c +
    bicoloredComponentCount C b c

/-- The formation parity. -/
noncomputable def formationParity (C : G.Coloring α) (a b c : α) : ℕ :=
  formationCurveCount C a b c % 2

/-- **The missing half**, stated exactly.  A switch on one `(a,b)`-component
changes the two cross counts `N_ac` and `N_bc` individually, but changes their
sum by an even amount.

This is the topological content of the source's proof — the idemposition parity
formula and the even-intersection property of two Jordan curves in the sphere —
and it is the only part of the parity lemma not proved here.  It is false
without a spherical hypothesis, which is why the principle is stated for a
fixed graph rather than for all graphs. -/
def CrossCurveParityPrinciple [DecidableEq α] (G : SimpleGraph V) (a b c : α) :
    Prop :=
  ∀ (C : G.Coloring α) (K : (C.bicoloredSubgraph a b).ConnectedComponent),
    (bicoloredComponentCount (C.swapOnKempeComponent a b K) a c +
        bicoloredComponentCount (C.swapOnKempeComponent a b K) b c) % 2 =
      (bicoloredComponentCount C a c + bicoloredComponentCount C b c) % 2

/-- **The parity lemma, from its two halves.**  The switched pair's count is
invariant and the two cross counts move together evenly, so the total is
preserved modulo two. -/
theorem formationParity_swapOnKempeComponent [DecidableEq α]
    {a b c : α} (hcross : CrossCurveParityPrinciple G a b c)
    (C : G.Coloring α) (K : (C.bicoloredSubgraph a b).ConnectedComponent) :
    formationParity (C.swapOnKempeComponent a b K) a b c =
      formationParity C a b c := by
  have hsame := bicoloredComponentCount_swapOnKempeComponent C a b K
  have hcrosssum := hcross C K
  unfold formationParity formationCurveCount
  omega

/-- **The arithmetic core of Kauffman's equivalence.**  A prime uncolourable
trail would present a curve count of five with same-colour contexts and of four
with different-colour contexts, reached from one another by a simple operation
that preserves parity.  Five is odd and four is even, so no such pair exists. -/
theorem not_five_and_four_of_parity {a b c : α} {C C' : G.Coloring α}
    (hparity : formationParity C a b c = formationParity C' a b c)
    (hfive : formationCurveCount C a b c = 5)
    (hfour : formationCurveCount C' a b c = 4) : False := by
  unfold formationParity at hparity
  rw [hfive, hfour] at hparity
  omega

/-- The same contradiction reached through a switch, which is how the source
passes between the two presentations. -/
theorem not_five_and_four_of_swap [DecidableEq α] {a b c : α}
    (hcross : CrossCurveParityPrinciple G a b c)
    (C : G.Coloring α) (K : (C.bicoloredSubgraph a b).ConnectedComponent)
    (hfive : formationCurveCount C a b c = 5)
    (hfour : formationCurveCount (C.swapOnKempeComponent a b K) a b c = 4) :
    False :=
  not_five_and_four_of_parity
    (formationParity_swapOnKempeComponent hcross C K).symm hfive hfour

end GoertzelV24KauffmanParity

end Mettapedia.GraphTheory.FourColor

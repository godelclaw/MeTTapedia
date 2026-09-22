import Mettapedia.GraphTheory.CrossFreeLaminarChain
import Mettapedia.GraphTheory.FourColor.GoertzelV24BoundedInterfaceObligation
import Mettapedia.GraphTheory.FourColor.GoertzelV24ConnectedShoreLiteralNode
import Mettapedia.GraphTheory.FourColor.GoertzelV24FacialBondLaminarity

/-!
# From laminar bonds to a nested chain: what is still missing, exactly

`GoertzelV24FacialBondLaminarity` proves that facial bonds at distinct sites
of one global pairing have **cross-free** face sets, and
`GoertzelV24BoundedInterfaceObligation` states the high-width obligation as the
existence of a long **strictly nested** chain of certified shores.  Between the
two sits a purely combinatorial question: does a cross-free family contain a
long chain?

It does not.  `CrossFreeLaminarChain.singletonFamily_chain_length_le_one`
exhibits, for every size, a pairwise disjoint — hence cross-free — family of
distinct nonempty proper sets whose longest strictly nested chain has length
one, and `singletonFamily_chain_length_le_two_of_orient` shows the bound stays
at two even when every member is allowed to be re-read by its complementary
shore.  Laminarity alone therefore contributes nothing towards the obligation,
and the concentric and side-by-side extremes really are both permitted.

This file supplies the exact missing ingredient and proves it sufficient.  What
turns a cross-free family into a chain is two *points*: one lying inside every
member and one lying outside every member.

The outside point is free, and `orientAwayBond` produces it.  A bond has no
preferred side — `complementBond` shows the complementary shore is again a bond
of the same site — so reading every bond by whichever shore misses one fixed
base face costs nothing and already removes the complement-shaped disjunct:
`laminarPair_orientAwayBond_faces` upgrades cross-freeness to genuine
laminarity for such a family.

The inside point is the whole content: in a laminar family the members through
a fixed point are automatically a chain, of length equal to that point's depth.
`exists_strictNested_orientedBondFaces_of_common_face` is the resulting
face-level extraction, whose only unsupplied hypothesis is one face lying
inside every bond.

So the obligation `LongNestedShoreSupply` is replaced here by
`CommonEdgeLaminarShoreSupply`: more than `phasedStateBound k w` pairwise
laminar, pairwise distinct certified shores sharing **one ambient edge**.  No
ordering is asserted and no chain is named; the supplier must produce a family
and a single edge.  `longNestedShoreSupply_of_commonEdgeLaminarShoreSupply`
proves this suffices, and
`rawBranchDecompositionSupply_of_commonEdgeLaminarShoreSupply` carries it to
the consumer the assembly already uses.

`exists_commonEdge_of_strictLiteralShoreChain` proves the converse, so the
exchange is exact rather than a weakening: a chain always supplies such an
edge.  The value of the trade is in the shape, not the strength — a fixed
point is a local geometric datum a bond construction can aim at, whereas an
ordering is not.

Nothing here supplies the edge or the face.  That is the open problem, stated
now as a depth statement about one point rather than as an ordering.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24BondDepthObligation

open Mettapedia.GraphTheory.CrossFreeLaminarChain
open GoertzelV24BoundedInterfaceObligation
open GoertzelV24ConnectedEdgeShoreMajority
open GoertzelV24FacialBondLaminarity
open GoertzelV24FaceOrbitIncidence
open GoertzelV24MajorityShoreStateDescent
open GoertzelV24OrderedMeshResidualSiteFacialBond
open GoertzelV24SphericalReductiveAssembly
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## Face level: the bonds of one pairing -/

/-- **Chain extraction from the bond family.**  Residual-site facial bonds of
one global pairing whose alternating carriers are pairwise disjoint, whose face
sets are pairwise distinct, and which all separate one fixed pair of faces, are
a strictly nested chain after one reindexing.

Only the two faces are extra input; cross-freeness is exactly what
`bond_faces_laminar_of_disjoint_carriers` already provides. -/
theorem exists_strictNested_bondFaces_of_separated_pair
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    {sigma : MatchingParity.Pairing V} {count : Nat}
    {first second : Fin count → V}
    (bonds : ∀ i : Fin count,
      ProperAlternatingSiteFacialBondWitness rotation sigma (first i) (second i))
    (hdisjoint : ∀ i j : Fin count, i ≠ j →
      Disjoint (bonds i).site.carrier (bonds j).site.carrier)
    (hdistinct : ∀ i j : Fin count, i ≠ j → (bonds i).faces ≠ (bonds j).faces)
    (inside outside : OrbitFace rotation.toRotationSystem)
    (hinside : ∀ i : Fin count, inside ∈ (bonds i).faces)
    (houtside : ∀ i : Fin count, outside ∉ (bonds i).faces) :
    ∃ reindex : Fin count → Fin count,
      ∀ i j : Fin count, i < j →
        (bonds (reindex j)).faces ⊂ (bonds (reindex i)).faces := by
  classical
  have hinj : Function.Injective fun i : Fin count => (bonds i).faces := by
    intro i j heq
    by_contra hne
    exact hdistinct i j hne heq
  refine exists_strictChain_reindex_of_total
    (fun i : Fin count => (bonds i).faces) hinj ?_
  intro i j
  by_cases hij : i = j
  · exact Or.inl (by rw [hij])
  · exact subset_or_subset_of_crossFreePair_of_separates
      (bond_faces_laminar_of_disjoint_carriers rotation minimal
        (bonds i) (bonds j) (hdisjoint i j hij))
      (hinside i) (hinside j) (houtside i) (houtside j)

/-! ## Orienting a bond family away from one base face -/

/-- The complementary shore of a facial bond is again a facial bond of the
same site.  The separator condition is symmetric in the two shores and the two
connectivity conditions simply swap, so a bond carries no preferred side. -/
def complementBond {rotation : Data G} {sigma : MatchingParity.Pairing V}
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second) :
    ProperAlternatingSiteFacialBondWitness rotation sigma first second where
  site := bond.site
  faces := Finset.univ \ bond.faces
  cycle_separates_faces := by
    intro dart
    rw [bond.cycle_separates_faces dart]
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]
    tauto
  selected_faces_connected := by
    have hset :
        {face | face ∈ Finset.univ \ bond.faces} = {face | face ∉ bond.faces} := by
      ext face; simp
    rw [hset]
    exact bond.complement_faces_connected
  complement_faces_connected := by
    have hset :
        {face | face ∉ Finset.univ \ bond.faces} = {face | face ∈ bond.faces} := by
      ext face; simp
    rw [hset]
    exact bond.selected_faces_connected

/-- Read a bond by whichever of its two shores misses a fixed base face.  This
is the whole of the outside-point hypothesis: it costs one arbitrary choice of
face and no geometry. -/
def orientAwayBond {rotation : Data G} {sigma : MatchingParity.Pairing V}
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (base : OrbitFace rotation.toRotationSystem) :
    ProperAlternatingSiteFacialBondWitness rotation sigma first second := by
  classical
  exact if base ∈ bond.faces then complementBond bond else bond

@[simp] theorem orientAwayBond_site {rotation : Data G}
    {sigma : MatchingParity.Pairing V} {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (base : OrbitFace rotation.toRotationSystem) :
    (orientAwayBond bond base).site = bond.site := by
  classical
  by_cases h : base ∈ bond.faces <;> simp [orientAwayBond, h, complementBond]

/-- The base face lies outside every oriented bond, by construction. -/
theorem base_notMem_orientAwayBond_faces {rotation : Data G}
    {sigma : MatchingParity.Pairing V} {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (base : OrbitFace rotation.toRotationSystem) :
    base ∉ (orientAwayBond bond base).faces := by
  classical
  by_cases h : base ∈ bond.faces
  · simp [orientAwayBond, h, complementBond]
  · simpa [orientAwayBond, h] using h

/-- **The free half, constructively.**  Two bonds with disjoint carriers,
both read away from one fixed base face, are laminar: the complement-shaped
disjunct is gone.  Only a face inside both is still missing. -/
theorem laminarPair_orientAwayBond_faces
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    {sigma : MatchingParity.Pairing V} {firstOne secondOne firstTwo secondTwo : V}
    (bondOne : ProperAlternatingSiteFacialBondWitness rotation sigma
      firstOne secondOne)
    (bondTwo : ProperAlternatingSiteFacialBondWitness rotation sigma
      firstTwo secondTwo)
    (base : OrbitFace rotation.toRotationSystem)
    (hdisjoint : Disjoint bondOne.site.carrier bondTwo.site.carrier) :
    LaminarPair (orientAwayBond bondOne base).faces
      (orientAwayBond bondTwo base).faces := by
  refine laminarPair_of_crossFreePair_of_notMem
    (bond_faces_laminar_of_disjoint_carriers rotation minimal
      (orientAwayBond bondOne base) (orientAwayBond bondTwo base) ?_)
    (base_notMem_orientAwayBond_faces bondOne base)
    (base_notMem_orientAwayBond_faces bondTwo base)
  simpa only [orientAwayBond_site] using hdisjoint

/-- **The face-level extraction, with only the inside face left to supply.**
Bonds with pairwise disjoint carriers, read away from one base face, with
pairwise distinct shores and one face inside all of them, form a strictly
nested chain after one reindexing. -/
theorem exists_strictNested_orientedBondFaces_of_common_face
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    {sigma : MatchingParity.Pairing V} {count : Nat}
    {first second : Fin count → V}
    (bonds : ∀ i : Fin count,
      ProperAlternatingSiteFacialBondWitness rotation sigma (first i) (second i))
    (base : OrbitFace rotation.toRotationSystem)
    (hdisjoint : ∀ i j : Fin count, i ≠ j →
      Disjoint (bonds i).site.carrier (bonds j).site.carrier)
    (hdistinct : ∀ i j : Fin count, i ≠ j →
      (orientAwayBond (bonds i) base).faces ≠ (orientAwayBond (bonds j) base).faces)
    (inside : OrbitFace rotation.toRotationSystem)
    (hinside : ∀ i : Fin count, inside ∈ (orientAwayBond (bonds i) base).faces) :
    ∃ reindex : Fin count → Fin count,
      ∀ i j : Fin count, i < j →
        (orientAwayBond (bonds (reindex j)) base).faces ⊂
          (orientAwayBond (bonds (reindex i)) base).faces := by
  classical
  have hinj : Function.Injective
      fun i : Fin count => (orientAwayBond (bonds i) base).faces := by
    intro i j heq
    by_contra hne
    exact hdistinct i j hne heq
  refine exists_strictChain_reindex_of_total
    (fun i : Fin count => (orientAwayBond (bonds i) base).faces) hinj ?_
  intro i j
  by_cases hij : i = j
  · exact Or.inl (by rw [hij])
  · exact subset_or_subset_of_laminarPair_of_mem
      (laminarPair_orientAwayBond_faces rotation minimal (bonds i) (bonds j)
        base (hdisjoint i j hij))
      (hinside i) (hinside j)

/-! ## Shore level: the obligation, restated as a depth statement -/

/-- A certified shore is nonempty: its majority side is witnessed by a vertex
seeing at least two of its edges. -/
theorem shore_nonempty {rotation : Data G} {k w : Nat}
    (node : LiteralShoreNode rotation k w) : node.shore.Nonempty := by
  classical
  obtain ⟨vertex, hvertex⟩ := node.majorityNonempty
  have hpos : 0 < (shoreIncidentEdges G node.shore vertex).card := by
    have : 2 ≤ (shoreIncidentEdges G node.shore vertex).card := hvertex
    omega
  obtain ⟨edge, hedge⟩ := Finset.card_pos.mp hpos
  exact ⟨edge, ((mem_shoreIncidentEdges_iff node.shore vertex edge).mp hedge).2⟩

/-- **The depth form of the high-width obligation.**  Above `N` vertices every
graph-backed vertex-minimal Tait counterexample carries more than
`phasedStateBound k w` certified shores at boundary width `k` and middle width
`w` that are pairwise laminar, pairwise distinct, and all contain one fixed
ambient edge.

The family is unordered and no chain is asserted: the supplier must produce a
set of shores and a single edge lying in all of them. -/
def CommonEdgeLaminarShoreSupply (k w N : Nat) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (rotation : Data G),
    GraphBackedVertexMinimalTaitCounterexample rotation →
      N < Fintype.card V →
        ∃ count : Nat, ∃ nodes : Fin count → LiteralShoreNode rotation k w,
          ∃ inside : G.edgeSet,
            phasedStateBound k w < count ∧
            (∀ i j : Fin count, i ≠ j → (nodes i).shore ≠ (nodes j).shore) ∧
            (∀ i j : Fin count,
              LaminarPair (nodes i).shore (nodes j).shore) ∧
            (∀ i : Fin count, inside ∈ (nodes i).shore)

/-- The same statement with the complement-symmetric disjunction the spherical
bond argument actually produces, plus one edge outside every shore. -/
def CommonEdgePairCrossFreeShoreSupply (k w N : Nat) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (rotation : Data G),
    GraphBackedVertexMinimalTaitCounterexample rotation →
      N < Fintype.card V →
        ∃ count : Nat, ∃ nodes : Fin count → LiteralShoreNode rotation k w,
          ∃ inside outside : G.edgeSet,
            phasedStateBound k w < count ∧
            (∀ i j : Fin count, i ≠ j → (nodes i).shore ≠ (nodes j).shore) ∧
            (∀ i j : Fin count,
              CrossFreePair (nodes i).shore (nodes j).shore) ∧
            (∀ i : Fin count, inside ∈ (nodes i).shore) ∧
            (∀ i : Fin count, outside ∉ (nodes i).shore)

/-- One edge outside every shore reduces the cross-free form to the laminar
form.  This is the cheap half of the passage, and it is the half an orientation
convention supplies. -/
theorem commonEdgeLaminarShoreSupply_of_crossFree (k w N : Nat)
    (supply : CommonEdgePairCrossFreeShoreSupply.{u} k w N) :
    CommonEdgeLaminarShoreSupply.{u} k w N := by
  intro V _ _ G _ rotation minimal hlarge
  obtain ⟨count, nodes, inside, outside, hcount, hdistinct, hcross, hin, hout⟩ :=
    supply rotation minimal hlarge
  refine ⟨count, nodes, inside, hcount, hdistinct, ?_, hin⟩
  intro i j
  exact laminarPair_of_crossFreePair_of_notMem (hcross i j) (hout i) (hout j)

/-- **The obligation reduction.**  A laminar family of distinct certified
shores sharing one edge is a strictly nested chain of the same length, so the
depth form implies the chain form. -/
theorem longNestedShoreSupply_of_commonEdgeLaminarShoreSupply (k w N : Nat)
    (supply : CommonEdgeLaminarShoreSupply.{u} k w N) :
    LongNestedShoreSupply.{u} k w N := by
  intro V _ _ G _ rotation minimal hlarge
  obtain ⟨count, nodes, inside, hcount, hdistinct, hlam, hinside⟩ :=
    supply rotation minimal hlarge
  have hinj : Function.Injective fun i : Fin count => (nodes i).shore := by
    intro i j heq
    by_contra hne
    exact hdistinct i j hne heq
  obtain ⟨reindex, hreindex⟩ :=
    exists_strictChain_reindex_of_total
      (fun i : Fin count => (nodes i).shore) hinj (by
        intro i j
        exact subset_or_subset_of_laminarPair_of_mem (hlam i j)
          (hinside i) (hinside j))
  exact ⟨count, fun i => nodes (reindex i),
    fun i j hij => hreindex i j hij, hcount⟩

/-- Composed with the existing width supplier, the depth form reaches the
consumer the spherical assembly already uses. -/
theorem rawBranchDecompositionSupply_of_commonEdgeLaminarShoreSupply
    (k w N : Nat) (supply : CommonEdgeLaminarShoreSupply.{u} k w N) :
    RawBranchDecompositionSupply.{u} N :=
  rawBranchDecompositionSupply_of_longNestedShoreSupply k w N
    (longNestedShoreSupply_of_commonEdgeLaminarShoreSupply k w N supply)

/-! ## The exchange is exact -/

/-- **The converse.**  A strictly nested chain of certified shores always
supplies an edge lying in every one of them.  Together with
`longNestedShoreSupply_of_commonEdgeLaminarShoreSupply` this shows the common
edge is not a strengthening smuggled into the obligation: it is precisely what
a chain is. -/
theorem exists_commonEdge_of_strictLiteralShoreChain
    {rotation : Data G} {k w count : Nat} (hpos : 0 < count)
    (nodes : Fin count → LiteralShoreNode rotation k w)
    (hstrict : ∀ i j : Fin count, i < j → (nodes j).shore ⊂ (nodes i).shore) :
    ∃ inside : G.edgeSet, ∀ i : Fin count, inside ∈ (nodes i).shore :=
  exists_mem_of_strictChain hpos (fun i => (nodes i).shore) hstrict
    (shore_nonempty (nodes ⟨count - 1, by omega⟩))

/-- A strictly nested chain of certified shores is in particular a laminar
family, so the chain form implies every ingredient of the depth form except
the count. -/
theorem laminarPair_of_strictLiteralShoreChain
    {rotation : Data G} {k w count : Nat}
    (nodes : Fin count → LiteralShoreNode rotation k w)
    (hstrict : ∀ i j : Fin count, i < j → (nodes j).shore ⊂ (nodes i).shore)
    (i j : Fin count) :
    LaminarPair (nodes i).shore (nodes j).shore :=
  laminarPair_of_strictChain (fun i => (nodes i).shore) hstrict i j

/-- The chain form implies the depth form.  With the previous theorem the two
obligations are equivalent, and the content of the open problem is a single
edge of large depth. -/
theorem commonEdgeLaminarShoreSupply_of_longNestedShoreSupply (k w N : Nat)
    (supply : LongNestedShoreSupply.{u} k w N) :
    CommonEdgeLaminarShoreSupply.{u} k w N := by
  intro V _ _ G _ rotation minimal hlarge
  obtain ⟨count, nodes, hstrict, hcount⟩ := supply rotation minimal hlarge
  have hpos : 0 < count := by omega
  obtain ⟨inside, hinside⟩ :=
    exists_commonEdge_of_strictLiteralShoreChain hpos nodes hstrict
  refine ⟨count, nodes, inside, hcount, ?_, ?_, hinside⟩
  · intro i j hij
    rcases lt_trichotomy i j with h | h | h
    · exact ((hstrict i j h).ne).symm
    · exact absurd h hij
    · exact (hstrict j i h).ne
  · exact laminarPair_of_strictLiteralShoreChain nodes hstrict

end

end GoertzelV24BondDepthObligation

end Mettapedia.GraphTheory.FourColor

import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationFaceFragments
import Mettapedia.GraphTheory.FourColor.GoertzelV24SquareGraphComposition

/-!
# Occurrence-sensitive face update across one corridor Cell

The capped face-progress coordinate of the source transfer state is attached
to occurrences on an actual face cycle.  When an old prefix is enlarged by
one literal Cell, the regional position carrier changes, so its induced graph
cannot be composed directly with the Cell graph.  This file puts both induced
graphs on the common ambient carrier of all cyclic positions of the face.

Under the concrete coverage condition saying that every retained face step
belongs wholly to the prefix or wholly to the Cell, the graph for the union is
their supremum.  Reachability between shared occurrences is consequently the
closure of whole-fragment moves in the two factors.  This is the face analogue
of the relational connectivity update; it does not assert a functional
profile update or perform the later cap-at-five arithmetic.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24TerminalProfileFaceUpdate

open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24RotationFaceFragments
open SimpleGraph

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- The face-cycle graph restricted to a regional edge set, but retained on
the common ambient carrier of all cyclic positions. Positions outside the
region are isolated. -/
def faceRegionalAmbientPositionGraph
    (RS : RotationSystem V E) (root : RS.D) (region : Finset E) :
    SimpleGraph (Fin (RS.faceOrbit root).card) where
  Adj left right :=
    (faceCyclePositionGraph RS root).Adj left right ∧
      faceCycleEdge RS root left ∈ region ∧
      faceCycleEdge RS root right ∈ region
  symm := ⟨by
    rintro left right ⟨hadj, hleft, hright⟩
    exact ⟨hadj.symm, hright, hleft⟩⟩
  loopless := ⟨by
    intro position hadj
    exact hadj.1.ne rfl⟩

@[simp]
theorem faceRegionalAmbientPositionGraph_adj
    (RS : RotationSystem V E) (root : RS.D) (region : Finset E)
    (left right : Fin (RS.faceOrbit root).card) :
    (faceRegionalAmbientPositionGraph RS root region).Adj left right ↔
      (faceCyclePositionGraph RS root).Adj left right ∧
        faceCycleEdge RS root left ∈ region ∧
        faceCycleEdge RS root right ∈ region :=
  Iff.rfl

/-- Every face-cycle adjacency retained by the union of two regions is
already wholly retained by one factor.  Consecutive prefix/Cell geometry must
discharge this literal coverage condition. -/
def RegionalFaceAdjacencyCovered
    (RS : RotationSystem V E) (root : RS.D)
    (leftRegion rightRegion : Finset E) : Prop :=
  ∀ {left right : Fin (RS.faceOrbit root).card},
    (faceCyclePositionGraph RS root).Adj left right →
    faceCycleEdge RS root left ∈ leftRegion ∪ rightRegion →
    faceCycleEdge RS root right ∈ leftRegion ∪ rightRegion →
    (faceCycleEdge RS root left ∈ leftRegion ∧
        faceCycleEdge RS root right ∈ leftRegion) ∨
      (faceCycleEdge RS root left ∈ rightRegion ∧
        faceCycleEdge RS root right ∈ rightRegion)

/-- Under literal face-adjacency coverage, restriction to a union of regions
is exactly the supremum of their two ambient regional face graphs. -/
theorem faceRegionalAmbientPositionGraph_union_eq_sup_of_adjacencyCovered
    (RS : RotationSystem V E) (root : RS.D)
    (leftRegion rightRegion : Finset E)
    (hcovered : RegionalFaceAdjacencyCovered RS root
      leftRegion rightRegion) :
    faceRegionalAmbientPositionGraph RS root (leftRegion ∪ rightRegion) =
      faceRegionalAmbientPositionGraph RS root leftRegion ⊔
        faceRegionalAmbientPositionGraph RS root rightRegion := by
  ext left right
  change
    ((faceCyclePositionGraph RS root).Adj left right ∧
        faceCycleEdge RS root left ∈ leftRegion ∪ rightRegion ∧
        faceCycleEdge RS root right ∈ leftRegion ∪ rightRegion) ↔
      (((faceCyclePositionGraph RS root).Adj left right ∧
          faceCycleEdge RS root left ∈ leftRegion ∧
          faceCycleEdge RS root right ∈ leftRegion) ∨
        ((faceCyclePositionGraph RS root).Adj left right ∧
          faceCycleEdge RS root left ∈ rightRegion ∧
          faceCycleEdge RS root right ∈ rightRegion))
  constructor
  · rintro ⟨hadj, hleft, hright⟩
    rcases hcovered hadj hleft hright with hprefix | hcell
    · exact Or.inl ⟨hadj, hprefix⟩
    · exact Or.inr ⟨hadj, hcell⟩
  · rintro (hprefix | hcell)
    · exact ⟨hprefix.1, Finset.mem_union_left _ hprefix.2.1,
        Finset.mem_union_left _ hprefix.2.2⟩
    · exact ⟨hcell.1, Finset.mem_union_right _ hcell.2.1,
        Finset.mem_union_right _ hcell.2.2⟩

/-- Inclusion of the changing regional-position carrier into the common
ambient cyclic-position carrier. -/
def faceRegionalPositionEmbedding
    (RS : RotationSystem V E) (root : RS.D) (region : Finset E) :
    FaceRegionalPosition RS root region ↪
      Fin (RS.faceOrbit root).card :=
  ⟨Subtype.val, Subtype.val_injective⟩

/-- The common-carrier regional graph is exactly the mapped copy of the
existing induced graph used to define regional face fragments. -/
theorem faceRegionalPositionGraph_map_eq_ambient
    (RS : RotationSystem V E) (root : RS.D) (region : Finset E) :
    (faceRegionalPositionGraph RS root region).map
        (faceRegionalPositionEmbedding RS root region) =
      faceRegionalAmbientPositionGraph RS root region := by
  ext left right
  constructor
  · intro hadj
    rcases (SimpleGraph.map_adj
      (faceRegionalPositionEmbedding RS root region)
      (faceRegionalPositionGraph RS root region) left right).1 hadj with
      ⟨left', right', hadj', hleft, hright⟩
    subst left
    subst right
    exact ⟨hadj',
      (mem_faceRegionalPositions_iff RS root region left'.1).1 left'.2,
      (mem_faceRegionalPositions_iff RS root region right'.1).1 right'.2⟩
  · rintro ⟨hadj, hleft, hright⟩
    exact (SimpleGraph.map_adj
      (faceRegionalPositionEmbedding RS root region)
      (faceRegionalPositionGraph RS root region) left right).2
        ⟨⟨left, (mem_faceRegionalPositions_iff RS root region left).2 hleft⟩,
          ⟨right, (mem_faceRegionalPositions_iff RS root region right).2 hright⟩,
          hadj, rfl, rfl⟩

/-- Regional-fragment reachability is neither weakened nor strengthened by
moving to the common ambient cyclic-position carrier. -/
theorem faceRegionalPositionGraph_reachable_iff_ambient
    (RS : RotationSystem V E) (root : RS.D) (region : Finset E)
    (left right : FaceRegionalPosition RS root region) :
    (faceRegionalPositionGraph RS root region).Reachable left right ↔
      (faceRegionalAmbientPositionGraph RS root region).Reachable
        left.1 right.1 := by
  rw [← faceRegionalPositionGraph_map_eq_ambient]
  exact (reachable_map_embedding_iff
    (faceRegionalPositionGraph RS root region)
    (faceRegionalPositionEmbedding RS root region) left right).symm

/-- A nontrivial component switch between the prefix and Cell face graphs can
occur only at a cyclic occurrence whose underlying edge belongs to both
regions. -/
theorem faceRegionalAmbientPositionGraph_switch_mem_inter
    (RS : RotationSystem V E) (root : RS.D)
    (leftRegion rightRegion : Finset E)
    {left middle right : Fin (RS.faceOrbit root).card}
    (hleftMiddle : left ≠ middle) (hmiddleRight : middle ≠ right)
    (hleft : (faceRegionalAmbientPositionGraph RS root leftRegion).Reachable
      left middle)
    (hright : (faceRegionalAmbientPositionGraph RS root rightRegion).Reachable
      middle right) :
    faceCycleEdge RS root middle ∈ leftRegion ∩ rightRegion := by
  let leftGraph := faceRegionalAmbientPositionGraph RS root leftRegion
  let rightGraph := faceRegionalAmbientPositionGraph RS root rightRegion
  have hleftSupport : middle ∈ leftGraph.support :=
    SimpleGraph.mem_support_of_reachable hleftMiddle.symm hleft.symm
  have hrightSupport : middle ∈ rightGraph.support :=
    SimpleGraph.mem_support_of_reachable hmiddleRight hright
  rcases (SimpleGraph.mem_support leftGraph).1 hleftSupport with
    ⟨leftNeighbor, hleftAdj⟩
  rcases (SimpleGraph.mem_support rightGraph).1 hrightSupport with
    ⟨rightNeighbor, hrightAdj⟩
  exact Finset.mem_inter.2 ⟨hleftAdj.2.1, hrightAdj.2.1⟩

/-- Face-fragment connectivity after adjoining one Cell is the closure of
whole-fragment moves in the old prefix and in the Cell, with switches confined
to their shared cyclic occurrences.  The positions retain face occurrences,
so this remains sound when a facial walk traverses one edge twice. -/
theorem faceRegionalAmbientPositionGraph_union_reachable_iff_componentClosure
    (RS : RotationSystem V E) (root : RS.D)
    (leftRegion rightRegion : Finset E)
    (hcovered : RegionalFaceAdjacencyCovered RS root
      leftRegion rightRegion)
    {start finish : Fin (RS.faceOrbit root).card}
    (hstart : faceCycleEdge RS root start ∈ leftRegion ∩ rightRegion)
    (hfinish : faceCycleEdge RS root finish ∈ leftRegion ∩ rightRegion) :
    (faceRegionalAmbientPositionGraph RS root
      (leftRegion ∪ rightRegion)).Reachable start finish ↔
      Relation.ReflTransGen
        (fun left right :
            Subtype (fun position =>
              faceCycleEdge RS root position ∈ leftRegion ∩ rightRegion) =>
          (faceRegionalAmbientPositionGraph RS root leftRegion).Reachable
              left.1 right.1 ∨
            (faceRegionalAmbientPositionGraph RS root rightRegion).Reachable
              left.1 right.1)
        ⟨start, hstart⟩ ⟨finish, hfinish⟩ := by
  rw [faceRegionalAmbientPositionGraph_union_eq_sup_of_adjacencyCovered
    RS root leftRegion rightRegion hcovered]
  exact reachable_sup_iff_subtype_componentClosure
    (faceRegionalAmbientPositionGraph RS root leftRegion)
    (faceRegionalAmbientPositionGraph RS root rightRegion)
    (fun position =>
      faceCycleEdge RS root position ∈ leftRegion ∩ rightRegion)
    start finish hstart hfinish
    (faceRegionalAmbientPositionGraph_switch_mem_inter
      RS root leftRegion rightRegion)

/-- The endpoint-complete facial update.  A new regional fragment can begin
or end away from the shared cut, so its two queried cyclic occurrences are
included in the closure carrier while every genuine switch between prefix and
Cell fragments remains confined to a shared occurrence. -/
theorem faceRegionalAmbientPositionGraph_union_reachable_iff_componentClosureWithEndpoints
    (RS : RotationSystem V E) (root : RS.D)
    (leftRegion rightRegion : Finset E)
    (hcovered : RegionalFaceAdjacencyCovered RS root
      leftRegion rightRegion)
    (start finish : Fin (RS.faceOrbit root).card) :
    (faceRegionalAmbientPositionGraph RS root
      (leftRegion ∪ rightRegion)).Reachable start finish ↔
      Relation.ReflTransGen
        (fun left right : Subtype (fun position =>
            faceCycleEdge RS root position ∈ leftRegion ∩ rightRegion ∨
              position = start ∨ position = finish) =>
          (faceRegionalAmbientPositionGraph RS root leftRegion).Reachable
              left.1 right.1 ∨
            (faceRegionalAmbientPositionGraph RS root rightRegion).Reachable
              left.1 right.1)
        ⟨start, Or.inr (Or.inl rfl)⟩
        ⟨finish, Or.inr (Or.inr rfl)⟩ := by
  rw [faceRegionalAmbientPositionGraph_union_eq_sup_of_adjacencyCovered
    RS root leftRegion rightRegion hcovered]
  apply reachable_sup_iff_subtype_componentClosure
    (faceRegionalAmbientPositionGraph RS root leftRegion)
    (faceRegionalAmbientPositionGraph RS root rightRegion)
    (fun position =>
      faceCycleEdge RS root position ∈ leftRegion ∩ rightRegion ∨
        position = start ∨ position = finish)
    start finish
    (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
  intro left middle right hleftMiddle hmiddleRight hleft hright
  exact Or.inl (faceRegionalAmbientPositionGraph_switch_mem_inter
    RS root leftRegion rightRegion hleftMiddle hmiddleRight hleft hright)

/-- The abstract closure equation identifies the literal connected fragment
of the enlarged region, not merely reachability in an auxiliary ambient
graph.  Thus a named union fragment can be recovered from the two factor
fragment relations even when either queried occurrence lies away from the
shared seam. -/
theorem mem_faceRegionalFragmentPositions_connectedComponentMk_union_iff_componentClosure
    (RS : RotationSystem V E) (root : RS.D)
    (leftRegion rightRegion : Finset E)
    (hcovered : RegionalFaceAdjacencyCovered RS root
      leftRegion rightRegion)
    (anchor position : Fin (RS.faceOrbit root).card)
    (hanchor : faceCycleEdge RS root anchor ∈ leftRegion ∪ rightRegion)
    (hposition : faceCycleEdge RS root position ∈ leftRegion ∪ rightRegion) :
    let anchorRegional : FaceRegionalPosition RS root
        (leftRegion ∪ rightRegion) :=
      ⟨anchor, (mem_faceRegionalPositions_iff RS root
        (leftRegion ∪ rightRegion) anchor).2 hanchor⟩
    position ∈ faceRegionalFragmentPositions RS root
        (leftRegion ∪ rightRegion)
        ((faceRegionalPositionGraph RS root (leftRegion ∪ rightRegion)).connectedComponentMk
          anchorRegional) ↔
      Relation.ReflTransGen
        (fun left right : Subtype (fun occurrence =>
            faceCycleEdge RS root occurrence ∈ leftRegion ∩ rightRegion ∨
              occurrence = anchor ∨ occurrence = position) =>
          (faceRegionalAmbientPositionGraph RS root leftRegion).Reachable
              left.1 right.1 ∨
            (faceRegionalAmbientPositionGraph RS root rightRegion).Reachable
              left.1 right.1)
        ⟨anchor, Or.inr (Or.inl rfl)⟩
        ⟨position, Or.inr (Or.inr rfl)⟩ := by
  dsimp only
  let anchorRegional : FaceRegionalPosition RS root
      (leftRegion ∪ rightRegion) :=
    ⟨anchor, (mem_faceRegionalPositions_iff RS root
      (leftRegion ∪ rightRegion) anchor).2 hanchor⟩
  let positionRegional : FaceRegionalPosition RS root
      (leftRegion ∪ rightRegion) :=
    ⟨position, (mem_faceRegionalPositions_iff RS root
      (leftRegion ∪ rightRegion) position).2 hposition⟩
  constructor
  · intro hmember
    rcases (mem_faceRegionalFragmentPositions_iff RS root
      (leftRegion ∪ rightRegion)
      ((faceRegionalPositionGraph RS root (leftRegion ∪ rightRegion)).connectedComponentMk
        anchorRegional) position).1 hmember with
      ⟨candidate, hcandidate, hvalue⟩
    have hcandidateEq : candidate = positionRegional :=
      Subtype.ext hvalue
    subst candidate
    have hcomponent :
        (faceRegionalPositionGraph RS root
            (leftRegion ∪ rightRegion)).connectedComponentMk positionRegional =
          (faceRegionalPositionGraph RS root
            (leftRegion ∪ rightRegion)).connectedComponentMk anchorRegional :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hcandidate
    have hregional :
        (faceRegionalPositionGraph RS root
          (leftRegion ∪ rightRegion)).Reachable
          anchorRegional positionRegional :=
      (SimpleGraph.ConnectedComponent.exact hcomponent).symm
    have hambient :
        (faceRegionalAmbientPositionGraph RS root
          (leftRegion ∪ rightRegion)).Reachable anchor position :=
      (faceRegionalPositionGraph_reachable_iff_ambient RS root
        (leftRegion ∪ rightRegion) anchorRegional positionRegional).1
          hregional
    exact (faceRegionalAmbientPositionGraph_union_reachable_iff_componentClosureWithEndpoints
      RS root leftRegion rightRegion hcovered anchor position).1 hambient
  · intro hclosure
    have hambient :
        (faceRegionalAmbientPositionGraph RS root
          (leftRegion ∪ rightRegion)).Reachable anchor position :=
      (faceRegionalAmbientPositionGraph_union_reachable_iff_componentClosureWithEndpoints
        RS root leftRegion rightRegion hcovered anchor position).2 hclosure
    have hregional :
        (faceRegionalPositionGraph RS root
          (leftRegion ∪ rightRegion)).Reachable
          anchorRegional positionRegional :=
      (faceRegionalPositionGraph_reachable_iff_ambient RS root
        (leftRegion ∪ rightRegion) anchorRegional positionRegional).2
          hambient
    have hcomponent :
        (faceRegionalPositionGraph RS root
            (leftRegion ∪ rightRegion)).connectedComponentMk positionRegional =
          (faceRegionalPositionGraph RS root
            (leftRegion ∪ rightRegion)).connectedComponentMk anchorRegional :=
      SimpleGraph.ConnectedComponent.sound hregional.symm
    apply (mem_faceRegionalFragmentPositions_iff RS root
      (leftRegion ∪ rightRegion)
      ((faceRegionalPositionGraph RS root (leftRegion ∪ rightRegion)).connectedComponentMk
        anchorRegional) position).2
    exact ⟨positionRegional,
      (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).2 hcomponent, rfl⟩

end

end GoertzelV24TerminalProfileFaceUpdate

end Mettapedia.GraphTheory.FourColor

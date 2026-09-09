import Mettapedia.GraphTheory.FourColor.KempeRestriction
import Mettapedia.GraphTheory.FourColor.SeparatedPairDeletion

/-!
# Compatibility of two deletion Kempe orbits

For separated adjacent-pair deletions, agreement between representatives
of two specified Kempe orbits is equivalent to an ambient Tait colouring
whose two restrictions lie in those orbits. Individual extendability of
each orbit is not simultaneous extendability. Forgetting the specified
orbits makes compatibility exactly ambient Tait colourability.

These are semantic equivalences, not a supplier of compatible orbits and
not a new wall-exclusion premise. They identify what a repair argument on
selected deletion colourings would have to construct.
-/

namespace Mettapedia.GraphTheory.FourColor.DeletionOrbitCompatibility

open SimpleGraph GoertzelV24LocalSwapKempeGeneration
open GoertzelV24AdjacentPairBoundary GoertzelV24AdjacentPairInsertion
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24AdjacentPairColoringAtlas
open GoertzelV24AdjacentPairCommonCoreDisagreementResidue
open GoertzelV24AdjacentPairCommonCoreKempeBoundary
open GoertzelV24KempeComponentEmbeddingBoundary SeparatedPairDeletion

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

noncomputable section
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The two restrictions of one ambient colouring agree on the overlap. -/
theorem common_restrictions_eq (source target : AdjacentPairData G)
    (c : G.EdgeColoring Color) :
    firstDeletionCommonCoreColoring (third := target.firstVertex)
        (fourth := target.secondVertex) (c.pullbackEmbedding (retainedGraphEmbedding source)) =
      secondDeletionCommonCoreColoring (first := source.firstVertex)
        (second := source.secondVertex) (c.pullbackEmbedding (retainedGraphEmbedding target)) := by
  apply DFunLike.ext _ _
  rintro ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ a b => rfl

omit [Fintype V] [DecidableRel G.Adj] in
private theorem mapped_edge_retained (data : AdjacentPairData G)
    (e : (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex).edgeSet) :
    IsRetainedAmbientEdge data (retainedEdgeToAmbientEdge data e) := by
  apply isRetainedAmbientEdge_of_deleted_vertices_not_mem
  · intro h
    obtain ⟨v, _, hv⟩ := Sym2.mem_map.mp (Sym2.mem_toFinset.mp h)
    exact v.property.1 hv
  · intro h
    obtain ⟨v, _, hv⟩ := Sym2.mem_map.mp (Sym2.mem_toFinset.mp h)
    exact v.property.2 hv

/-- A glued atlas restricts to the original colouring on every patch. -/
theorem glued_restrict {I : Type*} (family : PairDeletionColoringFamily (G := G) I)
    (cover : family.CoversEdges) (adjacent : family.CoversAdjacentEdges)
    (agree : family.PairwiseAgrees) (i : I) :
    (family.gluedColoring cover adjacent agree).pullbackEmbedding
      (retainedGraphEmbedding (family.data i)) = family.coloring i := by
  apply DFunLike.ext _ _
  intro e
  have hr := mapped_edge_retained (family.data i) e
  have h := family.gluedColorFunction_eq_ambientColor cover agree i
    (retainedEdgeToAmbientEdge (family.data i) e) hr
  change family.gluedColorFunction cover
      (retainedEdgeToAmbientEdge (family.data i) e) = _
  rw [h]
  change family.coloring i (ambientEdgeToRetainedEdge (family.data i)
    (retainedEdgeToAmbientEdge (family.data i) e) hr) = _
  congr 1
  apply (retainedGraphEmbedding (family.data i)).mapEdgeSet.injective
  exact retainedEdgeToAmbientEdge_ambientEdgeToRetainedEdge _ _ hr

/-- Separation plus literal overlap agreement constructs an ambient
colouring with both prescribed restrictions, not merely some colouring. -/
theorem exists_extension_of_agreement (source target : AdjacentPairData G)
    (left : (DeletedAdjacentPairGraph G source.firstVertex source.secondVertex).EdgeColoring Color)
    (right : (DeletedAdjacentPairGraph G target.firstVertex target.secondVertex).EdgeColoring Color)
    (hl : IsTaitEdgeColoring _ left) (hr : IsTaitEdgeColoring _ right)
    (sep : Separated source target)
    (agree : firstDeletionCommonCoreColoring (third := target.firstVertex)
        (fourth := target.secondVertex) left =
      secondDeletionCommonCoreColoring (first := source.firstVertex)
        (second := source.secondVertex) right) :
    ∃ c : G.EdgeColoring Color, IsTaitEdgeColoring G c ∧
      c.pullbackEmbedding (retainedGraphEmbedding source) = left ∧
      c.pullbackEmbedding (retainedGraphEmbedding target) = right := by
  let family := twoPatchFamily source target left right hl hr
  have cover : family.CoversEdges := by
    intro e
    rcases retained_or_retained source target sep e with hs | ht
    · exact ⟨false, hs⟩
    · exact ⟨true, ht⟩
  have adjacent : family.CoversAdjacentEdges := by
    intro e f hadj
    rcases adjacent_retained_or_retained source target sep e f hadj with hs | ht
    · exact ⟨false, hs⟩
    · exact ⟨true, ht⟩
  have coherent : family.PairwiseAgrees := by
    intro i j e hi hj
    have h := coloring_eq_on_common_retained_edge source target left right
    cases i <;> cases j
    · rfl
    · exact h e hi hj ((commonRestrictionAgreementBit_eq_true_iff _ _ _ _).mpr agree)
    · exact (h e hj hi ((commonRestrictionAgreementBit_eq_true_iff _ _ _ _).mpr agree)).symm
    · rfl
  exact ⟨family.gluedColoring cover adjacent coherent,
    family.gluedColoring_isTait cover adjacent coherent,
    glued_restrict family cover adjacent coherent false,
    glued_restrict family cover adjacent coherent true⟩

variable (source target : AdjacentPairData G)
  (leftBase : (DeletedAdjacentPairGraph G source.firstVertex source.secondVertex).EdgeColoring Color)
  (rightBase : (DeletedAdjacentPairGraph G target.firstVertex target.secondVertex).EdgeColoring Color)

/-- Representatives in these two specified orbits can agree literally. -/
def Compatible : Prop :=
  ∃ left right, TaitKempeReachable leftBase left ∧ TaitKempeReachable rightBase right ∧
    firstDeletionCommonCoreColoring (third := target.firstVertex)
        (fourth := target.secondVertex) left =
      secondDeletionCommonCoreColoring (first := source.firstVertex)
        (second := source.secondVertex) right

/-- One ambient colouring simultaneously meets both specified orbits. -/
def SimultaneouslyExtendable : Prop :=
  ∃ c : G.EdgeColoring Color, IsTaitEdgeColoring G c ∧
    TaitKempeReachable leftBase (c.pullbackEmbedding (retainedGraphEmbedding source)) ∧
    TaitKempeReachable rightBase (c.pullbackEmbedding (retainedGraphEmbedding target))

/-- Exact orbit-choice boundary: separate extendability cannot replace the
single ambient witness on the right-hand side of this equivalence. -/
theorem compatible_iff_simultaneouslyExtendable
    (hl : IsTaitEdgeColoring _ leftBase) (hr : IsTaitEdgeColoring _ rightBase)
    (sep : Separated source target) :
    Compatible source target leftBase rightBase ↔
      SimultaneouslyExtendable source target leftBase rightBase := by
  constructor
  · rintro ⟨left, right, reachL, reachR, agree⟩
    obtain ⟨c, hc, hcl, hcr⟩ := exists_extension_of_agreement source target left right
      (isTaitEdgeColoring_of_taitKempeReachable hl reachL)
      (isTaitEdgeColoring_of_taitKempeReachable hr reachR) sep agree
    exact ⟨c, hc, hcl.symm ▸ reachL, hcr.symm ▸ reachR⟩
  · rintro ⟨c, _, hl, hr⟩
    exact ⟨_, _, hl, hr, common_restrictions_eq source target c⟩

/-- Once one ambient colouring meets both deletion orbits, every valid
Kempe descendant of it meets the same two orbits. -/
theorem simultaneous_membership_of_ambient_reachable
    {c d : G.EdgeColoring Color} (hc : IsTaitEdgeColoring G c)
    (hl : TaitKempeReachable leftBase (c.pullbackEmbedding (retainedGraphEmbedding source)))
    (hr : TaitKempeReachable rightBase (c.pullbackEmbedding (retainedGraphEmbedding target)))
    (path : TaitKempeReachable c d) :
    TaitKempeReachable leftBase (d.pullbackEmbedding (retainedGraphEmbedding source)) ∧
    TaitKempeReachable rightBase (d.pullbackEmbedding (retainedGraphEmbedding target)) :=
  ⟨hl.trans (KempeRestriction.reachable_pullback (retainedGraphEmbedding source) hc path),
    hr.trans (KempeRestriction.reachable_pullback (retainedGraphEmbedding target) hc path)⟩

/-- Allowing arbitrary choices of deletion orbits makes their compatibility
exactly the original ambient Tait-colourability problem. -/
theorem exists_compatible_iff_taitColorable (sep : Separated source target) :
    (∃ leftBase rightBase, IsTaitEdgeColoring _ leftBase ∧ IsTaitEdgeColoring _ rightBase ∧
      Compatible source target leftBase rightBase) ↔
    ∃ c : G.EdgeColoring Color, IsTaitEdgeColoring G c := by
  constructor
  · rintro ⟨left, right, hl, hr, h⟩
    obtain ⟨c, hc, _, _⟩ :=
      (compatible_iff_simultaneouslyExtendable source target left right hl hr sep).mp h
    exact ⟨c, hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨_, _, isTaitEdgeColoring_pullbackEmbedding c (retainedGraphEmbedding source) hc,
      isTaitEdgeColoring_pullbackEmbedding c (retainedGraphEmbedding target) hc,
      _, _, .refl, .refl, common_restrictions_eq source target c⟩

end
end Mettapedia.GraphTheory.FourColor.DeletionOrbitCompatibility

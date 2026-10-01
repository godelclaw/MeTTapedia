import Mettapedia.GraphTheory.FourColor.PrismRungCoordinates

/-!
# Exact retained-dart recognition of prism rung sewing

The canonical opposite-pair splice of a prism rung is transported to a
literal capped ladder. Both seam edges and the parallel retained rungs
keep their dart identities; the correspondence also retains the rotations.
-/

namespace Mettapedia.GraphTheory.FourColor.PrismRungSplice

open PrismRungCoordinates
open GoertzelV24AdjacentPairBoundary GoertzelV24DeletedRegionRotationSplice
open GoertzelV24RotationCutDartDecomposition GoertzelV24OrderedCutRotationSplice
open GoertzelV24RetainedVertexRotationSplice GoertzelV24RotationSpliceConstructor
open GoertzelV24OrbitFaceCurvatureBulk GoertzelV24OrbitFaceTwoSided
open GoertzelV24FaceDualConnectedness GoertzelV24TwoEdgeCutMinimality

noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable (m : ℕ) [NeZero m] (hm : 2 ≤ m)

abbrev ordered := AdjacentSourceSplice.ordered (graphData m hm) (pair m hm)
  (graph_cubic m hm) (graph_rotation m hm)
abbrev root := (ordered m hm).rootedRotationSystem (graphData m hm)
abbrev keep := deletedRegionKeep (ordered m hm).deletedVertices
abbrev smaller := AdjacentSourceSplice.smaller (graphData m hm) (pair m hm)
  (graph_cubic m hm) (graph_rotation m hm)

theorem keep_iff (v : Vertex m) : keep m hm v ↔ CappedLadderEndReduction.Retained m v := by
  change v ∉ ({0,lastVertex m} : Finset (Vertex m)) ↔ 0 < v.val ∧ v.val < 2*m+1
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
  have hv := v.is_lt
  have hz : v = 0 ↔ v.val = 0 := Fin.ext_iff
  have hl : v = lastVertex m ↔ v.val = 2*m+1 := Fin.ext_iff
  rw [hz,hl]
  omega

def vertexEquiv : CappedLadderRotation.Vertex m ≃ RetainedVertex (keep m hm) where
  toFun v := ⟨CappedLadderEndReduction.embed m v,
    (keep_iff m hm _).mpr (CappedLadderEndReduction.embed_retained m v)⟩
  invFun v := CappedLadderEndReduction.project m v.1
  left_inv := CappedLadderEndReduction.project_embed m
  right_inv v := by
    apply Subtype.ext
    exact CappedLadderEndReduction.embed_project m v.1 ((keep_iff m hm v.1).mp v.2)

def retainedEquiv : CappedLadderEndReduction.RetainedDart m ≃
    RetainedDart (root m hm) (keep m hm) where
  toFun d := ⟨dartEquiv m hm d.1,(keep_iff m hm d.1.1).mpr d.2⟩
  invFun d := ⟨(dartEquiv m hm).symm d.1,by
    apply (keep_iff m hm _).mp
    have hv := congrArg (fun a : (graph m).Dart => a.fst)
      ((dartEquiv m hm).apply_symm_apply d.1)
    have hk : keep m hm d.1.fst := d.2
    rw [← hv] at hk
    exact hk⟩
  left_inv d := by apply Subtype.ext; exact (dartEquiv m hm).left_inv d.1
  right_inv d := by apply Subtype.ext; exact (dartEquiv m hm).right_inv d.1

def partsEquiv := retainedDartEquivMatchedParts (root m hm) (keep m hm)
  (orderedCut ((ordered m hm).leftCrossing .join12_30))
  (orderedCut ((ordered m hm).rightCrossing .join12_30))
  ((ordered m hm).boundaryCover (graphData m hm) .join12_30)
  ((ordered m hm).pairedCuts_disjoint .join12_30)

/-- Every smaller ladder dart is one actual retained original prism dart. -/
def spliceDartEquiv : CappedLadderRotation.Dart m ≃ (smaller m hm).D :=
  ((CappedLadderEndReduction.retainedDartEquiv m).trans (retainedEquiv m hm)).trans
    (partsEquiv m hm)

def underlying : (smaller m hm).D → (graph m).Dart :=
  matchedPartUnderlyingDart (root m hm) (keep m hm)
    (orderedCut ((ordered m hm).leftCrossing .join12_30))
    (orderedCut ((ordered m hm).rightCrossing .join12_30))

theorem underlying_injective : Function.Injective (underlying m hm) :=
  matchedPartUnderlyingDart_injective (root m hm) (keep m hm) _ _
    ((ordered m hm).boundaryCover (graphData m hm) .join12_30)
    ((ordered m hm).pairedCuts_disjoint .join12_30)

theorem underlying_equiv (d : CappedLadderRotation.Dart m) :
    underlying m hm (spliceDartEquiv m hm d) =
      dartEquiv m hm (CappedLadderEndReduction.embedDart m d) :=
  matchedPartUnderlyingDart_equiv (root m hm) (keep m hm) _ _
    ((ordered m hm).boundaryCover (graphData m hm) .join12_30)
    ((ordered m hm).pairedCuts_disjoint .join12_30) _

theorem vertex_commute (d : CappedLadderRotation.Dart m) :
    vertexEquiv m hm ((CappedLadderRotation.source m).vertOf d) =
      (smaller m hm).vertOf (spliceDartEquiv m hm d) := by
  apply Subtype.ext
  change (CappedLadderEndReduction.embedDart m d).1 =
    (underlying m hm (spliceDartEquiv m hm d)).fst
  rw [underlying_equiv]
  rfl

theorem rho_commute (d : CappedLadderRotation.Dart m) :
    spliceDartEquiv m hm ((CappedLadderRotation.source m).rho d) =
      (smaller m hm).rho (spliceDartEquiv m hm d) := by
  apply underlying_injective m hm
  rw [underlying_equiv]
  have hr := matchedPartUnderlyingDart_rho (root m hm) (keep m hm) _ _
    ((ordered m hm).boundaryCover (graphData m hm) .join12_30)
    ((ordered m hm).pairedCuts_disjoint .join12_30) (spliceDartEquiv m hm d)
  change underlying m hm ((smaller m hm).rho (spliceDartEquiv m hm d)) =
    (graphData m hm).vertexRotation (underlying m hm (spliceDartEquiv m hm d)) at hr
  rw [hr,underlying_equiv]
  exact (graph_rho m hm (CappedLadderEndReduction.embedDart m d)).symm

/-- Sew only the four half-darts exposed by the named prism rung. -/
def sewnFlip (d : Dart m) : Dart m :=
  if d.1.val = 1 ∧ d.2 = 0 then (ports m 2,1)
  else if d.1.val = 2*m ∧ d.2 = 1 then (ports m 1,0)
  else if d.1.val = m ∧ d.2 = 1 then (ports m 3,0)
  else if d.1.val = m+1 ∧ d.2 = 0 then (ports m 0,1)
  else alpha m d

theorem sewnFlip_eq_end (d : Dart m) (hd : CappedLadderEndReduction.Retained m d.1) :
    sewnFlip m d = CappedLadderEndReduction.sewnFlip m d := by
  rcases d with ⟨v,i⟩
  have hv := v.is_lt
  have hnz : v ≠ 0 := by
    intro h
    have he := congrArg Fin.val h
    change v.val = 0 at he
    change 0 < v.val ∧ v.val < 2*m+1 at hd
    omega
  change 0 < v.val ∧ v.val < 2*m+1 at hd
  fin_cases i <;>
    dsimp [sewnFlip,CappedLadderEndReduction.sewnFlip,
      PrismRungCoordinates.alpha,PrismRungCoordinates.flip,
      CappedLadderRotation.alpha,CappedLadderRotation.flip] <;>
    simp only [Fin.reduceEq,and_true,and_false,ite_false] <;> split_ifs
  all_goals apply Prod.ext
  all_goals first
    | rfl
    | (apply Fin.ext
       simp only [ports_val,prev_val,next_val]
       try dsimp only
       try simp only [Fin.val_sub_one_of_ne_zero hnz]
       try norm_num [ports_val] at *
       try (change _ = (v.val+(1 % (2*(m+1)))) % (2*(m+1)))
       try rw [Nat.mod_eq_of_lt (show 1 < 2*(m+1) by omega),
         Nat.mod_eq_of_lt (show v.val+1 < 2*(m+1) by omega)]
       try split_ifs
       all_goals first | contradiction | omega)

include hm in
theorem sewnFlip_embed (d : CappedLadderRotation.Dart m) :
    sewnFlip m (CappedLadderEndReduction.embedDart m d) =
      CappedLadderEndReduction.embedDart m ((CappedLadderRotation.source m).alpha d) :=
  (sewnFlip_eq_end m _ (CappedLadderEndReduction.embed_retained m d.1)).trans
    (CappedLadderEndReduction.sewnFlip_embed m d)

/-- The four original exposed half-darts, in canonical cyclic port order. -/
def exposed (i : Fin 4) : Dart m :=
  ![(ports m 0,1),(ports m 1,0),(ports m 2,1),(ports m 3,0)] i

theorem exposed_fst (i : Fin 4) : (exposed m i).1 = ports m i := by
  fin_cases i <;> rfl

theorem exposed_unique (i : Fin 4) (d : (graph m).Dart)
    (hf : d.fst = ports m i) (hn : ¬keep m hm d.snd) :
    d = dartEquiv m hm (exposed m i) := by
  obtain ⟨⟨v,j⟩,rfl⟩ := (dartEquiv m hm).surjective d
  change v = ports m i at hf
  subst v
  change ¬keep m hm ((source m).alpha (ports m i,j)).1 at hn
  rw [keep_iff] at hn
  change ¬(0 < ((source m).alpha (ports m i,j)).1.val ∧
    ((source m).alpha (ports m i,j)).1.val < 2*m+1) at hn
  apply congrArg (dartEquiv m hm)
  fin_cases i <;> fin_cases j <;> first
    | rfl
    | (exfalso
       dsimp [PrismRungCoordinates.alpha,PrismRungCoordinates.flip] at hn
       simp only [prev_val,next_val,Fin.val_rev,ports_val] at hn
       try norm_num [ports_val] at hn
       try split_ifs at hn
       all_goals first | contradiction | omega)

theorem left_underlying (j : Fin 2) :
    underlying m hm ((ordered m hm).reductionLeftSeamDart (graphData m hm) .join12_30 j) =
      dartEquiv m hm (exposed m (SquareReductionSide.join12_30.leftPort j)) := by
  apply exposed_unique m hm
  · have h := (ordered m hm).leftBoundaryDart_vertex (graphData m hm) .join12_30 j
    have hp : (ordered m hm).portVertex = ports m := funext (rotation_ports m hm)
    change (underlying m hm ((ordered m hm).reductionLeftSeamDart (graphData m hm) .join12_30 j)).fst = (ordered m hm).portVertex _ at h
    rw [hp] at h
    exact h
  · exact (orderedBoundaryDart (root m hm) (keep m hm)
      ((ordered m hm).leftCrossing .join12_30)
      ((ordered m hm).leftCrosses (graphData m hm) .join12_30) j).1.2

theorem right_underlying (j : Fin 2) :
    underlying m hm ((ordered m hm).reductionRightSeamDart (graphData m hm) .join12_30 j) =
      dartEquiv m hm (exposed m (SquareReductionSide.join12_30.rightPort j)) := by
  apply exposed_unique m hm
  · have h := (ordered m hm).rightBoundaryDart_vertex (graphData m hm) .join12_30 j
    have hp : (ordered m hm).portVertex = ports m := funext (rotation_ports m hm)
    change (underlying m hm ((ordered m hm).reductionRightSeamDart (graphData m hm) .join12_30 j)).fst = (ordered m hm).portVertex _ at h
    rw [hp] at h
    exact h
  · exact (orderedBoundaryDart (root m hm) (keep m hm)
      ((ordered m hm).rightCrossing .join12_30)
      ((ordered m hm).rightCrosses (graphData m hm) .join12_30) j).1.2

theorem exposed_removed (i : Fin 4) :
    ¬keep m hm ((source m).alpha (exposed m i)).1 := by
  rw [keep_iff]
  fin_cases i <;>
    dsimp [exposed,PrismRungCoordinates.alpha,PrismRungCoordinates.flip] <;>
    simp only [CappedLadderEndReduction.Retained,prev_val,next_val,ports_val] <;>
    norm_num <;> split_ifs <;> omega

include hm in
theorem sewn_exposed_left (j : Fin 2) :
    sewnFlip m (exposed m (SquareReductionSide.join12_30.leftPort j)) =
      exposed m (SquareReductionSide.join12_30.rightPort j) := by
  have h : m ≠ 2*m := by omega
  fin_cases j <;> simp [SquareReductionSide.leftPort,SquareReductionSide.rightPort,
    SquareReductionSide.join01_23,SquareReductionSide.join12_30,
    exposed,sewnFlip,ports_val,h] <;> omega

include hm in
theorem sewn_exposed_right (j : Fin 2) :
    sewnFlip m (exposed m (SquareReductionSide.join12_30.rightPort j)) =
      exposed m (SquareReductionSide.join12_30.leftPort j) := by
  have h : m+1 ≠ 1 := by omega
  fin_cases j <;> simp [SquareReductionSide.leftPort,SquareReductionSide.rightPort,
    SquareReductionSide.join01_23,SquareReductionSide.join12_30,
    exposed,sewnFlip,ports_val,h] <;> omega

theorem sewnFlip_retains_intact (d : Dart m)
    (ha : keep m hm ((source m).alpha d).1) : sewnFlip m d = alpha m d := by
  have hex (i : Fin 4) : d ≠ exposed m i := by
    intro he
    exact exposed_removed m hm i (he ▸ ha)
  have h1 : ¬(d.1.val = 1 ∧ d.2 = 0) := by
    rintro ⟨hv,hi⟩
    apply hex 1
    apply Prod.ext
    · apply Fin.ext
      exact hv
    · exact hi
  have h2 : ¬(d.1.val = 2*m ∧ d.2 = 1) := by
    rintro ⟨hv,hi⟩
    apply hex 2
    apply Prod.ext
    · apply Fin.ext
      exact hv
    · exact hi
  have h3 : ¬(d.1.val = m ∧ d.2 = 1) := by
    rintro ⟨hv,hi⟩
    apply hex 0
    apply Prod.ext
    · apply Fin.ext
      exact hv
    · exact hi
  have h4 : ¬(d.1.val = m+1 ∧ d.2 = 0) := by
    rintro ⟨hv,hi⟩
    apply hex 3
    apply Prod.ext
    · apply Fin.ext
      exact hv
    · exact hi
  simp only [sewnFlip,h1,h2,h3,h4,ite_false]

/-- The actual splice flip retains old internal darts and sews precisely
the four exposed rail darts in the canonical opposite pairing. -/
theorem underlying_alpha (d : (smaller m hm).D) :
    underlying m hm ((smaller m hm).alpha d) = dartEquiv m hm
      (sewnFlip m ((dartEquiv m hm).symm (underlying m hm d))) := by
  rcases d with internal | left | right
  · change ((root m hm).alpha internal.1.1) = dartEquiv m hm
      (sewnFlip m ((dartEquiv m hm).symm internal.1.1))
    rw [sewnFlip_retains_intact m hm _ (by
      have he := (dartEquiv m hm).apply_symm_apply internal.1.1
      have ha := internal.2
      change keep m hm internal.1.1.snd at ha
      rw [← he] at ha
      exact ha)]
    exact (dartEquiv_alpha m hm _).trans (congrArg (fun d : (graph m).Dart => d.symm)
      ((dartEquiv m hm).apply_symm_apply internal.1.1)) |>.symm
  · obtain ⟨j,rfl⟩ := orderedBoundaryDart_surjective (root m hm) (keep m hm)
      ((ordered m hm).leftCrossing .join12_30)
      ((ordered m hm).leftCrosses (graphData m hm) .join12_30) left
    change underlying m hm ((smaller m hm).alpha
      ((ordered m hm).reductionLeftSeamDart (graphData m hm) .join12_30 j)) =
        dartEquiv m hm (sewnFlip m ((dartEquiv m hm).symm
          (underlying m hm ((ordered m hm).reductionLeftSeamDart (graphData m hm) .join12_30 j))))
    rw [(ordered m hm).reductionRotationSystem_alpha_leftSeamDart,
      left_underlying,right_underlying,Equiv.symm_apply_apply,sewn_exposed_left m hm]
  · obtain ⟨j,rfl⟩ := orderedBoundaryDart_surjective (root m hm) (keep m hm)
      ((ordered m hm).rightCrossing .join12_30)
      ((ordered m hm).rightCrosses (graphData m hm) .join12_30) right
    change underlying m hm ((smaller m hm).alpha
      ((ordered m hm).reductionRightSeamDart (graphData m hm) .join12_30 j)) =
        dartEquiv m hm (sewnFlip m ((dartEquiv m hm).symm
          (underlying m hm ((ordered m hm).reductionRightSeamDart (graphData m hm) .join12_30 j))))
    rw [(ordered m hm).reductionRotationSystem_alpha_rightSeamDart,
      right_underlying,left_underlying,Equiv.symm_apply_apply,sewn_exposed_right m hm]

/-- Recognition preserves the actual edge involution, including parallels. -/
theorem alpha_commute (d : CappedLadderRotation.Dart m) :
    spliceDartEquiv m hm ((CappedLadderRotation.source m).alpha d) =
      (smaller m hm).alpha (spliceDartEquiv m hm d) := by
  apply underlying_injective m hm
  rw [underlying_equiv,underlying_alpha,underlying_equiv,Equiv.symm_apply_apply,
    sewnFlip_embed m hm]

/-- One inherited face reaches every actual retained source vertex. -/
def spanningFace : DualTruncateSpanningFace.SpanningFace (smaller m hm) where
  seed := spliceDartEquiv m hm (CappedLadderRotation.spanningFace m).seed
  covers v := by
    obtain ⟨x,rfl⟩ := (vertexEquiv m hm).surjective v
    obtain ⟨d,hd,hs⟩ := (CappedLadderRotation.spanningFace m).covers x
    refine ⟨spliceDartEquiv m hm d,?_,?_⟩
    · rw [← vertex_commute,hd]
    · exact (RotationSystemExactTransport.sameFace_iff _ _ (spliceDartEquiv m hm)
        (alpha_commute m hm) (rho_commute m hm) _ _).mp hs

/-- Two-sided faces follow from the exact involution and rotation transport. -/
theorem twoSided : OrbitFacesTwoSided (smaller m hm) :=
  RotationSystemExactTransport.twoSided (CappedLadderRotation.source m) (smaller m hm)
    (spliceDartEquiv m hm) (alpha_commute m hm) (rho_commute m hm)
    (CappedLadderRotation.twoSided m)

theorem spherical : OrbitSphericalCubicMapData (smaller m hm) :=
  RotationSystemExactTransport.spherical (CappedLadderRotation.source m) (smaller m hm)
    (spliceDartEquiv m hm) (vertexEquiv m hm) (alpha_commute m hm) (vertex_commute m hm)
    (rho_commute m hm) (CappedLadderRotation.spherical m)

theorem connected : (rotationPrimalGraph (smaller m hm)).Connected :=
  (RotationSystemExactTransport.primalIso (CappedLadderRotation.source m) (smaller m hm)
    (spliceDartEquiv m hm) (vertexEquiv m hm) (alpha_commute m hm)
    (vertex_commute m hm)).connected_iff.mp (CappedLadderRotation.connected m)

/-- Each new seam is parallel to a genuine retained rung. This assertion
is used only for connectivity; the preceding dart equivalence keeps both
edge identities separate. -/
theorem sewn_original_adjacent (d : Dart m) :
    (graph m).Adj d.1 (sewnFlip m d).1 := by
  unfold sewnFlip
  split_ifs with h1 h2 h3 h4
  all_goals first
    | exact ⟨d,rfl,rfl⟩
    | (refine ⟨(d.1,2),rfl,?_⟩
       change d.1.rev = _
       apply Fin.ext
       simp only [Fin.val_rev,ports_val]
       norm_num
       have hv := d.1.is_lt
       omega)

/-- Removing the rung leaves a connected genuine original exterior. -/
theorem retained_connected :
    (GoertzelV24CyclicBoundaryClosure.SideGraph (graph m) (keep m hm)).Connected := by
  letI : Nonempty (RetainedVertex (keep m hm)) := ⟨vertexEquiv m hm 0⟩
  have mapped : ∀ v w, (rotationPrimalGraph (smaller m hm)).Adj v w →
      (GoertzelV24CyclicBoundaryClosure.SideGraph (graph m) (keep m hm)).Adj v w := by
    rintro v w ⟨d,rfl,rfl⟩
    change (graph m).Adj (underlying m hm d).fst
      (underlying m hm ((smaller m hm).alpha d)).fst
    rw [underlying_alpha,dartEquiv_fst]
    have hv := congrArg (fun a : (graph m).Dart => a.fst)
      ((dartEquiv m hm).apply_symm_apply (underlying m hm d))
    change ((dartEquiv m hm).symm (underlying m hm d)).1 = (underlying m hm d).fst at hv
    rw [← hv]
    exact sewn_original_adjacent m ((dartEquiv m hm).symm (underlying m hm d))
  refine ⟨?_⟩
  intro v w
  exact GoertzelV24RotationEdgeBridge.reachable_map_of_adj_eq_or_adj id
    (fun _ _ h => Or.inr (mapped _ _ h)) ((connected m hm) v w)

end
end Mettapedia.GraphTheory.FourColor.PrismRungSplice

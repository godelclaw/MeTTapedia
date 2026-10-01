import Mettapedia.GraphTheory.FourColor.TwoCellCycleObstruction
import Mettapedia.GraphTheory.FourColor.SourcePatchKempe
import Mettapedia.GraphTheory.FourColor.TwoCellBoundaryChoiceRepair

/-!
# A physical repair of the obstructed two-cell exterior

The original fifty-vertex exterior cannot extend unchanged through its
ten-vertex patch. A saturated red-purple region of seventeen actual edges
changes its last two boundary observations together. The new source endpoint
choices then differ, and reconstruct a genuine colouring of the original
sixty-vertex map. Neither a complete source-colouring certificate nor the
classical Four Colour theorem supplies the witness.

This example consumes the uniform partial-source and physical-side Kempe
preservation laws. Availability of such a repair in every relevant exterior,
a smaller embedded operation, and occurrence coverage remain separate tasks.
-/

namespace Mettapedia.GraphTheory.FourColor.TwoCellPhysicalKempeRepair

open TwoCellCycleObstruction DualTruncateColoring DualTruncateCornerSemantics
open DualTruncateOpenPatch DualTruncateConstructionGSLT
open GoertzelV24HexagonPairingTargetAwareBoundary GoertzelV24PortTangleCommonKempeWeb

noncomputable section

def sourceOutside (v : Fin 20) : Prop := ¬selected v
def targetOutside (d : source.D) : Prop := ¬keep d
instance : DecidablePred sourceOutside := by unfold sourceOutside; infer_instance
instance : DecidablePred targetOutside := by unfold targetOutside; infer_instance
def sourceMask (v : Fin 20) : Prop := v = 3 ∨ v = 4 ∨ v = 17 ∨ v = 19
instance : DecidablePred sourceMask := by unfold sourceMask; infer_instance

def edgeMask : Edge source → Prop
  | .inl e => e = 5 ∨ e = 9 ∨ e = 27 ∨ e = 28 ∨ e = 29
  | .inr d => d = (0,2) ∨ d = (2,1) ∨ d = (3,1) ∨ d = (3,2) ∨
      d = (4,0) ∨ d = (4,1) ∨ d = (5,0) ∨ d = (16,1) ∨
      d = (17,1) ∨ d = (18,0) ∨ d = (18,1) ∨ d = (19,1)
instance : DecidablePred edgeMask := by intro e; cases e <;> unfold edgeMask <;> infer_instance

def repairedExterior : Fin 20 → Color :=
  SourcePatchKempe.switched exteriorColour .redPurple sourceMask

def switchedField : Edge source → Color :=
  RotationPatchKempe.switched base .redPurple edgeMask

theorem source_exterior_proper :
    SourcePatchKempe.ExteriorProper source sourceOutside exteriorColour := by
  unfold SourcePatchKempe.ExteriorProper
  decide +kernel

/-- The selected source vertices are saturated in the actual exterior
bichromatic graph. This is a geometric mask check, not a complete colouring. -/
theorem source_region :
    SourcePatchKempe.Region source sourceOutside exteriorColour .redPurple sourceMask := by
  constructor
  · unfold pairActiveColor Color.twoColor
    decide +kernel
  · unfold pairActiveColor Color.twoColor
    decide +kernel

theorem repaired_source_exterior_proper :
    SourcePatchKempe.ExteriorProper source sourceOutside repairedExterior :=
  SourcePatchKempe.switched_exterior source sourceOutside exteriorColour
    source_exterior_proper .redPurple sourceMask source_region

theorem repaired_pins : repairedExterior 10 = blue ∧ repairedExterior 19 = purple ∧
    repairedExterior 2 = blue ∧ repairedExterior 8 = red := by decide +kernel

/-- The two choices share their edge; they are checked jointly. -/
theorem joint_choices :
    TwoCellBoundaryChoice.Compatible (repairedExterior 10) (repairedExterior 19)
      (repairedExterior 2) (repairedExterior 8) red purple := by
  rcases repaired_pins with ⟨h10,h19,h2,h8⟩
  rw [h10,h19,h2,h8]
  simpa only [show blue + red = purple from by decide +kernel] using
    TwoCellBoundaryChoice.repair_one_pin blue red (by decide) (by decide) (by decide)

def sourceColour (v : Fin 20) : Color :=
  if v = 0 then red else if v = 1 then purple else repairedExterior v

@[simp] theorem sourceColour_zero : sourceColour 0 = red := by simp [sourceColour]
@[simp] theorem sourceColour_one : sourceColour 1 = purple := by simp [sourceColour]

theorem selected_iff (v : Fin 20) : selected v ↔ v = 0 ∨ v = 1 := by
  revert v
  decide +kernel

theorem sourceColour_exterior (v : Fin 20) (hv : sourceOutside v) :
    sourceColour v = repairedExterior v := by
  have h0 : v ≠ 0 := fun h => hv ((selected_iff v).2 (Or.inl h))
  have h1 : v ≠ 1 := fun h => hv ((selected_iff v).2 (Or.inr h))
  simp [sourceColour,h0,h1]

theorem sourceColour_nonzero (v : Fin 20) : sourceColour v ≠ 0 := by
  by_cases hv : selected v
  · rcases (selected_iff v).1 hv with rfl | rfl <;> simp [red,purple]
  · rw [sourceColour_exterior v hv]
    exact repaired_source_exterior_proper.1 v hv

theorem neighbours_zero : ∀ i : Fin 3,
    source.vertOf (source.alpha (0,i)) = (![1,10,19] i : Fin 20) := by decide +kernel

theorem neighbours_one : ∀ i : Fin 3,
    source.vertOf (source.alpha (1,i)) = (![0,2,8] i : Fin 20) := by decide +kernel

theorem endpoint_zero (d : source.D) (hd : source.vertOf d = 0) :
    sourceColour (source.vertOf d) ≠ sourceColour (source.vertOf (source.alpha d)) := by
  rcases d with ⟨v,i⟩
  change v = 0 at hd
  subst v
  rw [neighbours_zero]
  fin_cases i
  · simpa using joint_choices.2.2.2.2.2.2
  · change sourceColour 0 ≠ sourceColour 10
    rw [sourceColour_zero, sourceColour_exterior 10 (by decide)]
    exact joint_choices.2.2.1
  · change sourceColour 0 ≠ sourceColour 19
    rw [sourceColour_zero, sourceColour_exterior 19 (by decide)]
    exact joint_choices.2.2.2.1

theorem endpoint_one (d : source.D) (hd : source.vertOf d = 1) :
    sourceColour (source.vertOf d) ≠ sourceColour (source.vertOf (source.alpha d)) := by
  rcases d with ⟨v,i⟩
  change v = 1 at hd
  subst v
  rw [neighbours_one]
  fin_cases i
  · simpa using joint_choices.2.2.2.2.2.2.symm
  · change sourceColour 1 ≠ sourceColour 2
    rw [sourceColour_one, sourceColour_exterior 2 (by decide)]
    exact joint_choices.2.2.2.2.1
  · change sourceColour 1 ≠ sourceColour 8
    rw [sourceColour_one, sourceColour_exterior 8 (by decide)]
    exact joint_choices.2.2.2.2.2.1

/-- Exterior preservation and the single joint endpoint contract supply all
source inequalities. No full source word is checked as a certificate. -/
theorem sourceColour_proper (d : source.D) :
    sourceColour (source.vertOf d) ≠ sourceColour (source.vertOf (source.alpha d)) := by
  by_cases hv : selected (source.vertOf d)
  · rcases (selected_iff _).1 hv with h0 | h1
    · exact endpoint_zero d h0
    · exact endpoint_one d h1
  · by_cases hw : selected (source.vertOf (source.alpha d))
    · have hrev : sourceColour (source.vertOf (source.alpha d)) ≠
          sourceColour (source.vertOf (source.alpha (source.alpha d))) := by
        rcases (selected_iff _).1 hw with h0 | h1
        · exact endpoint_zero (source.alpha d) h0
        · exact endpoint_one (source.alpha d) h1
      simpa only [source.alpha_involutive] using hrev.symm
    · rw [sourceColour_exterior _ hv, sourceColour_exterior _ hw]
      exact repaired_source_exterior_proper.2 d hv hw

def sourceWitness : ThreeVertexColoring source where
  colour := sourceColour
  nonzero := sourceColour_nonzero
  proper := sourceColour_proper

def targetColouring : target.EdgeColoring Color := DualTruncateColoring.colouring source sourceWitness

theorem target_tait : target.IsTaitEdgeColoring targetColouring :=
  DualTruncateColoring.colouring_nonzero source sourceWitness

def starField (c : Fin 20 → Color) (d : source.D) (i : Fin 3) : Color :=
  if i = 0 then c (source.vertOf d) + c (source.vertOf (source.alpha d))
  else if i = 1 then c (source.vertOf (source.alpha d)) else c (source.vertOf d)

theorem edgeColour_star (c : Fin 20 → Color) (d : source.D) (i : Fin 3) :
    edgeColour source c (target.edgeOf (d,i)) = starField c d i := by
  fin_cases i
  · exact star_colour_zero source c d
  · exact star_colour_one source c d
  · exact star_colour_two source c d

theorem exterior_local : RotationPatchKempe.LocalProper target targetOutside base := by
  constructor
  · rintro ⟨d,i⟩ hd
    exact (exterior_stars d hd).1 i
  · rintro ⟨d,i⟩ ⟨e,j⟩ hd hv hn
    change d = e at hv
    subst e
    exact fun h => hn (Prod.ext rfl ((exterior_stars d hd).2 h))

/-- The seventeen actual edges are a saturated physical red-purple region.
All equations are checked on the original incidences. -/
theorem physical_region : RotationPatchKempe.Region target targetOutside base .redPurple edgeMask := by
  constructor
  · rintro ⟨d,i⟩ hd hm
    change pairActiveColor .redPurple (base (target.edgeOf (d,i)))
    rw [show base = edgeColour source exteriorColour from rfl, edgeColour_star]
    revert d i
    unfold pairActiveColor Color.twoColor
    decide +kernel
  · rintro ⟨d,i⟩ ⟨e,j⟩ hd hv hi hj
    change d = e at hv
    subst e
    change pairActiveColor .redPurple (edgeColour source exteriorColour (target.edgeOf (d,i))) at hi
    change pairActiveColor .redPurple (edgeColour source exteriorColour (target.edgeOf (d,j))) at hj
    rw [edgeColour_star] at hi hj
    revert d i j
    unfold pairActiveColor Color.twoColor
    decide +kernel

theorem switched_exterior_proper :
    GoertzelV24PortTangleGluing.PortTangle.IsProper
      (RotationPatchKempe.colouring target targetOutside switchedField) :=
  RotationPatchKempe.switched_proper target targetOutside base exterior_local
    .redPurple edgeMask physical_region

/-- Exact effect of the physical operation: the reconstructed colouring
agrees on every exterior incidence, including all original cut edges. -/
theorem reconstructs_physical_switch : Extends source keep switchedField targetColouring := by
  intro d hd i
  change edgeColour source sourceColour (target.edgeOf (d,i)) =
    RotationPatchKempe.switched base .redPurple edgeMask (target.edgeOf (d,i))
  unfold RotationPatchKempe.switched
  rw [edgeColour_star]
  change starField sourceColour d i =
    if edgeMask (target.edgeOf (d,i)) then
      Color.swap red purple (edgeColour source exteriorColour (target.edgeOf (d,i)))
    else edgeColour source exteriorColour (target.edgeOf (d,i))
  rw [edgeColour_star]
  revert d i
  decide +kernel

theorem switched_boundary_word :
    (fun p => switchedField (target.edgeOf (boundaryOutside p))) =
      ![blue,blue,red,red,blue,blue,purple,purple] := by
  have he (p : Fin 8) : ¬keep (target.vertOf (boundaryOutside p)) :=
    (ports_are_actual_cut (boundaryOutside p)).2 ⟨p,rfl⟩ |>.1
  funext p
  rw [← reconstructs_physical_switch _ (he p) (boundaryOutside p).2]
  change edgeColour source sourceColour (target.edgeOf (boundaryOutside p)) = _
  rw [edgeColour_star]
  revert p
  decide +kernel

theorem selected_edges_count : (Finset.univ.filter edgeMask).card = 17 := by decide +kernel

/-- Every selected edge is an actual exterior or cut edge. -/
theorem selected_visible (e : Edge source) (he : edgeMask e) :
    VisibleEdge source keep e := by
  revert e
  unfold VisibleEdge
  decide +kernel

theorem selected_changed (e : Edge source) (he : edgeMask e) : switchedField e ≠ base e := by
  rcases selected_visible e he with ⟨x,hx,hout⟩
  have hactive := physical_region.active x hout (hx.symm ▸ he)
  rw [hx] at hactive
  change base e = red ∨ base e = purple at hactive
  change RotationPatchKempe.switched base .redPurple edgeMask e ≠ base e
  simp only [RotationPatchKempe.switched, ite_eq_left he]
  rcases hactive with h | h <;> rw [h] <;> decide +kernel

theorem unselected_unchanged (e : Edge source) (he : ¬edgeMask e) : switchedField e = base e := by
  exact ite_eq_right he

/-- The actual history ends in a genuine full-map witness. Its exterior is
the proper switched field, rather than the originally obstructed field. -/
theorem successful_repair :
    ∃ t : target.EdgeColoring Color, target.IsTaitEdgeColoring t ∧
      Extends source keep switchedField t ∧
      GoertzelV24PortTangleGluing.PortTangle.IsProper
        (RotationPatchKempe.colouring target targetOutside switchedField) :=
  ⟨targetColouring,target_tait,reconstructs_physical_switch,switched_exterior_proper⟩

open TubeSlab.VertexTransfer VertexCodeSourceGeometry SourceVertexCodeTrace VertexConstructionGSLT

/-- The repaired whole-map witness lifts through every faithful complete
GSLT construction sweep. -/
theorem every_complete_sweep (order : List source.D) (hn : order.Nodup)
    (he : order ≠ []) (hcover : ∀ d, visited order d) :
    VertexConstructionGSLT.colouring.Supports
      (route (encodeClosed (cubic source) (rotationCyclic source)
        order hn he hcover).trace) Fin.elim0 Fin.elim0 :=
  supported_encoded_route source sourceWitness order hn he hcover

end
end Mettapedia.GraphTheory.FourColor.TwoCellPhysicalKempeRepair

import Mettapedia.GraphTheory.FourColor.DualTruncateForestCollapse
import Mettapedia.GraphTheory.FourColor.DualTruncateOpenPatchExample

/-!
# A separated two-cell patch with an exact source-colouring fibre

The cube source vertices zero and one select ten actual target vertices.
Every compatible extension of the supplied exterior is represented by two
source colour choices. The supplied interior values are zero, so the input
is only an exterior contract, not a complete target or source colouring.
The exact forest law replaces the eleven interior edge-colour variables
by two source variables and retains all three compatible witnesses.
-/

namespace Mettapedia.GraphTheory.FourColor.DualTruncateForestExample

open DualTruncateColoring DualTruncateCornerSemantics DualTruncateOpenPatch
open DualTruncateForestCollapse GoertzelV24FaceDualConnectedness

noncomputable section

abbrev source := DualTruncateCoupledExample.source
abbrev target := rotation source

def selected (v : Fin 8) : Prop := v.val < 2
def keep : source.D → Prop := vertexRegion source selected

instance : DecidablePred selected := by unfold selected; infer_instance
instance : DecidablePred keep := by unfold keep vertexRegion selected; infer_instance

/-- Only exterior source values are supplied. -/
def exteriorColour (v : Fin 8) : Color :=
  if selected v then 0 else DualTruncateOpenPatchExample.baseColour v

def base : Edge source → Color := edgeColour source exteriorColour

theorem simple_source : SimpleSource source := by unfold SimpleSource; decide +kernel
theorem separated : Separated source selected := by unfold Separated; decide +kernel

theorem forest : ((rotationPrimalGraph source).induce {v | selected v}).IsAcyclic := by
  apply SimpleGraph.IsAcyclic.of_card_le_two
  rw [ENat.card_eq_coe_fintype_card, Fintype.card_subtype]
  change ((Finset.univ.filter selected).card : ℕ∞) ≤ 2
  have hc : (Finset.univ.filter selected).card = 2 := by decide +kernel
  rw [hc]
  exact le_rfl

theorem exterior_stars (d : source.D) (hd : ¬keep d) : Star source base d := by
  have h : (fun i : Fin 3 => base (target.edgeOf (d,i))) =
      (fun i => if i = 0 then exteriorColour (source.vertOf d) +
        exteriorColour (source.vertOf (source.alpha d))
      else if i = 1 then exteriorColour (source.vertOf (source.alpha d))
      else exteriorColour (source.vertOf d)) := by
    funext i
    fin_cases i
    · exact star_colour_zero source exteriorColour d
    · exact star_colour_one source exteriorColour d
    · exact star_colour_two source exteriorColour d
  unfold DualTruncateCornerSemantics.Star
  change (∀ i, (fun i : Fin 3 => base (target.edgeOf (d,i))) i ≠ 0) ∧
    Function.Injective (fun i : Fin 3 => base (target.edgeOf (d,i)))
  rw [h]
  clear h
  revert d
  decide +kernel

theorem paired : PairedExterior source selected base exteriorColour := by
  intro d _
  exact star_colour_two source exteriorColour d

/-- An actual extension and its source choices are inverse representations. -/
def fibreEquiv :
    {t : target.EdgeColoring Color // target.IsTaitEdgeColoring t ∧
      Extends source keep base t} ≃ SourceFibre source selected exteriorColour :=
  extensionSourceEquiv source selected simple_source separated
    DualTruncateGeometryExample.source_cubic DualTruncateGeometryExample.source_rotationCyclic
    forest base exterior_stars exteriorColour paired

theorem reconstruct_same
    (t : {t : target.EdgeColoring Color // target.IsTaitEdgeColoring t ∧
      Extends source keep base t}) : fibreEquiv.symm (fibreEquiv t) = t :=
  fibreEquiv.symm_apply_apply t

def assignmentColour (x : Fin 2 → Color) (v : Fin 8) : Color :=
  if h : selected v then x ⟨v.val,h⟩ else exteriorColour v

abbrev Assignments := {x : Fin 2 → Color //
  (∀ v, assignmentColour x v ≠ 0) ∧
  ∀ d : source.D, assignmentColour x (source.vertOf d) ≠
    assignmentColour x (source.vertOf (source.alpha d))}

def selectedVertex (i : Fin 2) : Fin 8 := ⟨i.val,by omega⟩

theorem assignment_of_source (s : SourceFibre source selected exteriorColour) :
    assignmentColour (fun i => s.val.colour (selectedVertex i)) = s.val.colour := by
  funext v
  unfold assignmentColour
  split
  · congr 1
  · exact (s.property v (by assumption)).symm

def assignmentEquiv : SourceFibre source selected exteriorColour ≃ Assignments where
  toFun s := ⟨fun i => s.val.colour (selectedVertex i),by
    rw [assignment_of_source]
    exact ⟨s.val.nonzero,s.val.proper⟩⟩
  invFun x := ⟨⟨assignmentColour x.val,x.property.1,x.property.2⟩,by
    intro v hv
    simp only [assignmentColour, dite_eq_right hv]⟩
  left_inv s := by
    apply Subtype.ext
    apply source_ext source
    exact assignment_of_source s
  right_inv x := by
    apply Subtype.ext
    funext i
    change assignmentColour x.val (selectedVertex i) = x.val i
    have hs : selected (selectedVertex i) := i.isLt
    simp only [assignmentColour, dite_eq_left hs]
    rfl

theorem assignment_count : Fintype.card Assignments = 3 := by
  rw [Fintype.card_subtype]
  decide +kernel

/-- The exact fibre count follows from two-variable computation and the
uniform forest law; no target colouring table is supplied. -/
theorem extension_count_three :
    Nat.card {t : target.EdgeColoring Color // target.IsTaitEdgeColoring t ∧
      Extends source keep base t} = 3 := by
  rw [Nat.card_congr fibreEquiv, Nat.card_congr assignmentEquiv,
    Nat.card_eq_fintype_card,assignment_count]

theorem selected_source_variables : (Finset.univ.filter selected).card = 2 := by decide +kernel
theorem selected_target_vertices : (Finset.univ.filter keep).card = 10 := by decide +kernel
theorem exterior_target_vertices : (Finset.univ.filter (fun d => ¬keep d)).card = 14 := by
  decide +kernel
theorem internal_polygon_variables :
    (Finset.univ.filter (fun d : source.D => keep d ∧ keep (source.phi.symm d))).card = 6 := by
  decide +kernel
theorem internal_cross_variables :
    (Finset.univ.filter (fun e : Fin 12 => keep (DualTruncateCoupledExample.code.representative e))).card = 5 := by
  decide +kernel

open TubeSlab.VertexTransfer VertexCodeSourceGeometry SourceVertexCodeTrace
open VertexConstructionGSLT

theorem every_complete_sweep (s : SourceFibre source selected exteriorColour)
    (order : List source.D) (hn : order.Nodup) (he : order ≠ [])
    (hcover : ∀ d, visited order d) :
    VertexConstructionGSLT.colouring.Supports
      (route (encodeClosed (cubic source) (DualTruncateConstructionGSLT.rotationCyclic source)
        order hn he hcover).trace) Fin.elim0 Fin.elim0 :=
  DualTruncateOpenPatch.every_complete_sweep source (vertexRegion_closed source selected)
    exterior_stars (source_summary source selected base exteriorColour paired s)
    order hn he hcover

end
end Mettapedia.GraphTheory.FourColor.DualTruncateForestExample

import Mettapedia.GraphTheory.FourColor.PaddedCycleCapReplacement

/-!
# A strict padded-cap reduction for every even number of sectors

Evenness closes the constant-list branch of the common cyclic colouring
law. Every smaller colouring therefore reconstructs, with every exterior
colour fixed. The same geometric replacement removes exactly six vertices
per sector, with no finite boundary-colouring table.
-/

namespace Mettapedia.GraphTheory.FourColor.PaddedCycleCap

open GoertzelV24OpenTangleComposition SerialTangleSmallCutTransfer
open OpenTangleClosedWitness OpenTangleWitnessComposition
open GoertzelV24TwoEdgeCutMinimality
open Mettapedia.GSLT.LooseRelationEquipment

noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (m : ℕ) [NeZero m] (hm : 2 ≤ m) (heven : Even m)
include heven

theorem accepts_of_even {w : Boundary m → Color} {s : Fin m → Color}
    (h : CycleWitness m w s) : (tangle m hm).AcceptsBoundaryWords Empty.elim w := by
  obtain ⟨q,hq,havoid⟩ := CyclicColourAvoidance.exists_cycle_of_even heven
    (fun i => w (i,false)) (fun i => h.boundary_nonzero _)
  exact ⟨colouringOf m w s q, colouringOf_isTait m hm h hq havoid,
    funext (fun e => e.elim), rfl⟩

/-- All smaller cycle witnesses lift, including monochromatic boundaries. -/
theorem reconstruct_even (x : Empty → Color) (w : Fin (m*2) → Color)
    (h : (CycleCap.cap (m*2) (by omega)).AcceptsBoundaryWords x w) :
    (indexedCap m hm).AcceptsBoundaryWords x w := by
  have hx : x = Empty.elim := by funext e; exact nomatch e
  subst x
  apply (indexed_accepts m hm w).mpr
  obtain ⟨seam,hc,ht,hw,hs⟩ := (CycleSeamTransfer.accepts_iff_marked (by omega) w).mp h
  have ha := CycleSeamTransfer.edges_valid (by omega) ht
  have he := (CycleSeamTransfer.spokes_edges (by omega) ht).trans hw
  apply accepts_of_even m hm heven
    (s := fun i => CycleSeamTransfer.edges hc (portIndex m (i,false)))
  simpa [he] using cycleWitness_of_edges m ha

/-- Exact witness transport, defined on the entire smaller relation. -/
def evenCell : Cell id id (colourRelation (CycleCap.cap (m*2) (by omega)))
    (colourRelation (indexedCap m hm)) where
  map := fun {x w} witness => Classical.choice <|
    (nonempty_colourRelation_iff _ x w).mpr <|
      reconstruct_even m hm heven x w ⟨witness.val,witness.property⟩

def evenInContext {A B : Type}
    (before : Loose A (Empty → Color)) (after : Loose (Fin (m*2) → Color) B) :
    Cell id id (comp (comp before (colourRelation (CycleCap.cap (m*2) (by omega)))) after)
      (comp (comp before (colourRelation (indexedCap m hm))) after) :=
  Cell.hcomp (Cell.hcomp (Cell.id before) (evenCell m hm heven)) (Cell.id after)

theorem evenInContext_exterior {A B : Type}
    (before : Loose A (Empty → Color)) (after : Loose (Fin (m*2) → Color) B)
    {x : A} {z : B}
    (w : comp (comp before (colourRelation (CycleCap.cap (m*2) (by omega)))) after x z) :
    let changed := (evenInContext m hm heven before after).map w
    changed.1 = w.1 ∧ changed.2.1.1 = w.2.1.1 ∧
      changed.2.1.2.1 = w.2.1.2.1 ∧ changed.2.2 = w.2.2 := by
  exact ⟨rfl,rfl,rfl,rfl⟩

variable {V I B : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I] [Fintype B] [DecidableEq B]
  (outside : OpenTangleData V I B) (seam : B ≃ Empty ⊕ Fin (m*2))

/-- The reconstruction retains every exterior edge colour. -/
theorem even_closed_reconstruct
    (c : (sewn outside (CycleCap.cap (m*2) (by omega)) seam).EdgeColoring Color)
    (hc : (sewn outside (CycleCap.cap (m*2) (by omega)) seam).IsTaitEdgeColoring c) :
    ∃ old : (sewn outside (indexedCap m hm) seam).EdgeColoring Color,
      (sewn outside (indexedCap m hm) seam).IsTaitEdgeColoring old ∧
      ∀ d, old ((sewn outside (indexedCap m hm) seam).edgeOf (composeDartEquiv (.inl d))) =
        c ((sewn outside (CycleCap.cap (m*2) (by omega)) seam).edgeOf
          (composeDartEquiv (.inl d))) :=
  OpenTangleClosedWitness.replace outside (CycleCap.cap (m*2) (by omega)) seam
    (indexedCap m hm) (reconstruct_even m hm heven) c hc

/-- One strict reduction scheme for all even `m ≥ 2`, in arbitrary exteriors. -/
theorem strict_even_reduction
    (h : BridgelessSphericalCubicMapData (sewn outside (indexedCap m hm) seam)) :
    Fintype.card (V ⊕ Fin (m*2)) < Fintype.card (V ⊕ Vertex m) ∧
      BridgelessSphericalCubicMapData
        (sewn outside (CycleCap.cap (m*2) (by omega)) seam) ∧
      (RotationSystemTaitColorable (sewn outside (CycleCap.cap (m*2) (by omega)) seam) →
        RotationSystemTaitColorable (sewn outside (indexedCap m hm) seam)) := by
  refine ⟨replacement_strict m, replacement_class m hm outside seam h, ?_⟩
  rintro ⟨c,hc⟩
  obtain ⟨old,hold,_⟩ := even_closed_reconstruct m hm heven outside seam c hc
  exact ⟨old,hold⟩

end
end Mettapedia.GraphTheory.FourColor.PaddedCycleCap

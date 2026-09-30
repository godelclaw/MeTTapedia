import Mettapedia.GraphTheory.FourColor.PaddedCycleCapSource
import Mettapedia.GraphTheory.FourColor.OpenTangleClosedWitness
import Mettapedia.GraphTheory.FourColor.OpenTangleWitnessComposition

/-!
# Padded-cap reconstruction in a fixed exterior

The boundary word must be nonconstant. Under this explicit guard, the
replacement acts on genuine colouring witnesses and fixes every exterior
dart. GSLT relation composition keeps the same interface word and exterior
witnesses. Neither planarity of the replacement nor escape from a constant
boundary is assumed as a consequence of this transport theorem.
-/

namespace Mettapedia.GraphTheory.FourColor.PaddedCycleCap

open GoertzelV24OpenTangleComposition SerialTangleSmallCutTransfer
open OpenTangleClosedWitness OpenTangleWitnessComposition
open Mettapedia.GSLT.LooseRelationEquipment

noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (m : ℕ) [NeZero m] (hm : 2 ≤ m)

/-- A genuine smaller-cycle witness, on the proved domain of reconstruction. -/
def guardedCycle : Loose (Empty → Color) (Fin (m*2) → Color) :=
  fun x w => {c : colourRelation (CycleCap.cap (m*2) (by omega)) x w //
    ¬ ∃ a, ∀ i, w i = a}

def reconstructCell : Cell id id (guardedCycle m hm) (colourRelation (indexedCap m hm)) where
  map := fun {x w} witness => Classical.choice <|
    (nonempty_colourRelation_iff _ x w).mpr <|
      reconstruct_indexed m hm x w ⟨witness.val.val, witness.val.property⟩ witness.property

/-- Horizontal composition retains both actual exterior witnesses and both
shared boundary choices. The nonconstant guard is part of the source witness. -/
def reconstructInContext {A B : Type}
    (before : Loose A (Empty → Color)) (after : Loose (Fin (m*2) → Color) B) :
    Cell id id (comp (comp before (guardedCycle m hm)) after)
      (comp (comp before (colourRelation (indexedCap m hm))) after) :=
  Cell.hcomp (Cell.hcomp (Cell.id before) (reconstructCell m hm)) (Cell.id after)

theorem reconstructInContext_exterior {A B : Type}
    (before : Loose A (Empty → Color)) (after : Loose (Fin (m*2) → Color) B)
    {x : A} {z : B} (w : comp (comp before (guardedCycle m hm)) after x z) :
    let changed := (reconstructInContext m hm before after).map w
    changed.1 = w.1 ∧ changed.2.1.1 = w.2.1.1 ∧
      changed.2.1.2.1 = w.2.1.2.1 ∧ changed.2.2 = w.2.2 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

variable {V I B : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I] [Fintype B] [DecidableEq B]
  (outside : OpenTangleData V I B) (seam : B ≃ Empty ⊕ Fin (m*2))

/-- Reconstruct the original cap from a smaller closed-map colouring whose
interface is nonconstant. Every exterior edge colour is unchanged. -/
theorem reconstruct_closed
    (c : (sewn outside (CycleCap.cap (m*2) (by omega)) seam).EdgeColoring Color)
    (hc : (sewn outside (CycleCap.cap (m*2) (by omega)) seam).IsTaitEdgeColoring c)
    (hn : ¬ ∃ a, ∀ b, c ((sewn outside (CycleCap.cap (m*2) (by omega)) seam).edgeOf
      (composeDartEquiv (.inl (.inr b)))) = a) :
    ∃ old : (sewn outside (indexedCap m hm) seam).EdgeColoring Color,
      (sewn outside (indexedCap m hm) seam).IsTaitEdgeColoring old ∧
      ∀ d, old ((sewn outside (indexedCap m hm) seam).edgeOf (composeDartEquiv (.inl d))) =
        c ((sewn outside (CycleCap.cap (m*2) (by omega)) seam).edgeOf
          (composeDartEquiv (.inl d))) := by
  obtain ⟨l,r,hl,hr,hmatch,hout⟩ :=
    OpenTangleClosedWitness.restrict outside (CycleCap.cap (m*2) (by omega)) seam c hc
  have hnr : ¬ ∃ a, ∀ i, (CycleCap.cap (m*2) (by omega)).rightBoundaryColor r i = a := by
    rintro ⟨a,ha⟩
    apply hn
    refine ⟨a, fun b => ?_⟩
    rw [← hout (.inr b), hmatch b]
    rcases h : seam b with e | i
    · exact nomatch e
    · exact ha i
  obtain ⟨s,hs,hx,hy⟩ := reconstruct_indexed m hm _ _ ⟨r,hr,rfl,rfl⟩ hnr
  have hb (p : Empty ⊕ Fin (m*2)) : s (.inr p) = r (.inr p) := by
    rcases p with e | i
    · exact nomatch e
    · exact congrFun hy i
  obtain ⟨old,hold,he⟩ := OpenTangleClosedWitness.glue outside (indexedCap m hm) seam
    l s hl hs (fun b => (hmatch b).trans (hb (seam b)).symm)
  exact ⟨old,hold,fun d => (he d).trans (hout d)⟩

omit [NeZero m] [DecidableEq V] in
/-- Counts the entire sewn graph. No exterior vertices are introduced. -/
theorem closed_vertex_loss :
    Fintype.card (V ⊕ Vertex m) = Fintype.card (V ⊕ Fin (m*2)) + 6*m := by
  simp [Vertex]
  omega

end
end Mettapedia.GraphTheory.FourColor.PaddedCycleCap

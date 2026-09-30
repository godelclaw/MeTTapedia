import Mettapedia.GraphTheory.FourColor.PaddedCycleCapReplacement
import Mettapedia.GraphTheory.FourColor.Compositional.ConstantBoundaryKempeRepair
import Mettapedia.GraphTheory.FourColor.Compositional.CyclicBoundaryReflection

/-!
# Padded-cap reduction with a coupled physical exterior repair

At every width, a nonconstant smaller-cycle boundary already reconstructs.
For a constant boundary, an adjacent physical Kempe component repairs both
the exterior and the cycle together. Noncrossing of the physical exterior
matching is an explicit hypothesis; the spherical cyclic-shore theorem below
supplies it on its geometric domain. Exterior colours may change in this
branch. The replacement still removes exactly six vertices per sector.
-/

namespace Mettapedia.GraphTheory.FourColor.PaddedCycleCap

open GoertzelV24OpenTangleComposition SerialTangleSmallCutTransfer
open OpenTangleClosedWitness
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24PortTangleGluing GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24PortTangleCutParity
open GoertzelV24CompositeSeamCubic OpenTangleVertexReflection
open Compositional Compositional.BoundaryKempeSwitch Compositional.CyclicBoundaryMatching
open Mettapedia.GSLT.LooseRelationEquipment

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
variable (m : ℕ) [NeZero m] (hm : 2 ≤ m)
  {V I B : Type u} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
  [Fintype B] [DecidableEq B]
  (outside : OpenTangleData V I B) (seam : B ≃ Empty ⊕ Fin (m*2))

/-- The same ordered ports read on the exterior side of the seam. -/
def capCoordinates : Fin (m*2) ≃ B where
  toFun i := seam.symm (.inr i)
  invFun b := (seam b).elim Empty.elim id
  left_inv := by intro i; simp
  right_inv := by
    intro b
    rcases h : seam b with e | i
    · exact nomatch e
    · simpa only [h, Sum.elim_inr, id_eq] using seam.symm_apply_apply b

/-- The physical matching must use the actual cyclic boundary coordinates.
This is a geometric condition on every exterior colouring, not an assumed
colour-richness invariant. -/
def PhysicalNoncrossing : Prop :=
  ∀ (hcubic : IsCubic (ofOpenTangleData outside))
    (coloring : Coloring (ofOpenTangleData outside)) (hproper : IsProper coloring) pair,
    IsNoncrossingMatching (physicalMateInCoordinates (capCoordinates m seam)
      (ofOpenTangleData outside) hcubic coloring hproper pair)

/-- Every smaller closed-map colouring reconstructs on the stated physical
noncrossing domain. The constant branch changes one actual exterior component
and its shared cycle edge before cap reconstruction. -/
theorem closed_reconstruct_of_physical_noncrossing
    (hcubic : OpenIsCubic outside) (hplanar : PhysicalNoncrossing m outside seam)
    (c : (sewn outside (CycleCap.cap (m*2) (by omega)) seam).EdgeColoring Color)
    (hc : (sewn outside (CycleCap.cap (m*2) (by omega)) seam).IsTaitEdgeColoring c) :
    RotationSystemTaitColorable (sewn outside (indexedCap m hm) seam) := by
  classical
  obtain ⟨l,r,hl,hr,hmatch,_⟩ :=
    OpenTangleClosedWitness.restrict outside (CycleCap.cap (m*2) (by omega)) seam c hc
  let w := (CycleCap.cap (m*2) (by omega)).rightBoundaryColor r
  have hsource : (CycleCap.cap (m*2) (by omega)).AcceptsBoundaryWords Empty.elim w := by
    refine ⟨r,hr,?_,rfl⟩
    funext e
    exact Empty.elim e
  by_cases hn : ∃ a, ∀ i, w i = a
  · obtain ⟨a,ha⟩ := hn
    let coloring : Coloring (ofOpenTangleData outside) := ⟨l,hl.1⟩
    have hproper : IsProper coloring := ⟨hl.2.2,fun _ _ => hl.2.1⟩
    have hconstant (j) : coloring.color (.inr (capCoordinates m seam j)) = a := by
      have he := hmatch (capCoordinates m seam j)
      simpa [coloring, capCoordinates, ← ha j, w,
        TwoSidedOpenTangleData.rightBoundaryColor] using he
    have hportCubic := isCubic_ofOpenTangleData outside hcubic
    obtain ⟨d,i,changed,hchanged,hd0,hda,hword⟩ :=
      ConstantBoundaryKempeRepair.repair (by omega) (capCoordinates m seam)
        (ofOpenTangleData outside) hportCubic coloring hproper hconstant
        (hplanar hportCubic coloring hproper)
    have ha0 : a ≠ 0 := by simpa only [hconstant] using hproper.1 (.inr (capCoordinates m seam 0))
    have hsourceConstant :
        (CycleCap.cap (m*2) (by omega)).AcceptsBoundaryWords Empty.elim (fun _ => a) := by
      have hw : w = fun _ => a := funext ha
      simpa only [hw] using hsource
    have hcycle := CycleAdjacentBoundaryRepair.accepts_adjacent (by omega)
      ha0 hd0 hda hsourceConstant i
    have hnonconstant := CycleAdjacentBoundaryRepair.word_nonconstant (by omega) i hda
    obtain ⟨s,hs,_,hy⟩ := reconstruct_indexed m hm Empty.elim
      (CycleAdjacentBoundaryRepair.word i a d) hcycle hnonconstant
    have hl' : IsColor outside changed.color :=
      ⟨changed.invariant,fun {_ _} => hchanged.2 _ _,hchanged.1⟩
    have hmatch' (b) : changed.color (.inr b) = s (.inr (seam b)) := by
      obtain ⟨j,rfl⟩ := (capCoordinates m seam).surjective b
      have he := congrFun hy j
      simpa [capCoordinates, TwoSidedOpenTangleData.rightBoundaryColor] using
        (hword j).trans he.symm
    obtain ⟨old,hold,_⟩ := OpenTangleClosedWitness.glue outside (indexedCap m hm) seam
      changed.color s hl' hs hmatch'
    exact ⟨old,hold⟩
  · obtain ⟨s,hs,_,hy⟩ := reconstruct_indexed m hm Empty.elim w hsource hn
    have hb (p : Empty ⊕ Fin (m*2)) : s (.inr p) = r (.inr p) := by
      rcases p with e | i
      · exact nomatch e
      · exact congrFun hy i
    obtain ⟨old,hold,_⟩ := OpenTangleClosedWitness.glue outside (indexedCap m hm) seam
      l s hl hs (fun b => (hmatch b).trans (hb (seam b)).symm)
    exact ⟨old,hold⟩

/-- One strict family reduction at all widths on the physical noncrossing
domain, with a genuine closed-colouring reconstruction. -/
theorem strict_reduction_of_physical_noncrossing
    (hplanar : PhysicalNoncrossing m outside seam)
    (h : BridgelessSphericalCubicMapData (sewn outside (indexedCap m hm) seam)) :
    Fintype.card (V ⊕ Fin (m*2)) < Fintype.card (V ⊕ Vertex m) ∧
      BridgelessSphericalCubicMapData (sewn outside (CycleCap.cap (m*2) (by omega)) seam) ∧
      (RotationSystemTaitColorable (sewn outside (CycleCap.cap (m*2) (by omega)) seam) →
        RotationSystemTaitColorable (sewn outside (indexedCap m hm) seam)) := by
  refine ⟨replacement_strict m, replacement_class m hm outside seam h, ?_⟩
  rintro ⟨c,hc⟩
  exact closed_reconstruct_of_physical_noncrossing m hm outside seam
    (exterior_isCubic outside _ seam h.spherical.cubic)
    hplanar c hc

/-- Genuine closed-map colourings as a witness relation. The interface is
closed; the cap and its exterior are retained together inside each witness. -/
def closedTaitRelation {W E : Type u} [Fintype W] [DecidableEq W]
    [Fintype E] [DecidableEq E] (RS : RotationSystem W E) :
    Loose PUnit.{u+1} PUnit.{u+1} :=
  fun _ _ => {c : RS.EdgeColoring Color // RS.IsTaitEdgeColoring c}

/-- The coupled repair is a map of actual joint witnesses at a closed
interface. The cap's exterior belongs to this witness and may be recoloured. -/
def physicalClosedCell (hcubic : OpenIsCubic outside)
    (hplanar : PhysicalNoncrossing m outside seam) :
    Cell id id (closedTaitRelation (sewn outside (CycleCap.cap (m*2) (by omega)) seam))
      (closedTaitRelation (sewn outside (indexedCap m hm) seam)) where
  map w :=
    let repaired := closed_reconstruct_of_physical_noncrossing m hm outside seam
      hcubic hplanar w.val w.property
    ⟨Classical.choose repaired, Classical.choose_spec repaired⟩

def physicalClosedInContext (hcubic : OpenIsCubic outside)
    (hplanar : PhysicalNoncrossing m outside seam) {A Z : Type u}
    (before : Loose A PUnit.{u+1}) (after : Loose PUnit.{u+1} Z) :
    Cell id id (comp (comp before
      (closedTaitRelation (sewn outside (CycleCap.cap (m*2) (by omega)) seam))) after)
      (comp (comp before (closedTaitRelation (sewn outside (indexedCap m hm) seam))) after) :=
  Cell.hcomp (Cell.hcomp (Cell.id before)
    (physicalClosedCell m hm outside seam hcubic hplanar)) (Cell.id after)

/-- Only the cap/exterior joint witness is changed. Separate surrounding
GSLT witnesses and their outer observations remain exactly the same. -/
theorem physicalClosedInContext_outer (hcubic : OpenIsCubic outside)
    (hplanar : PhysicalNoncrossing m outside seam) {A Z : Type u}
    (before : Loose A PUnit.{u+1}) (after : Loose PUnit.{u+1} Z) {x : A} {z : Z}
    (w : comp (comp before
      (closedTaitRelation (sewn outside (CycleCap.cap (m*2) (by omega)) seam))) after x z) :
    let changed := (physicalClosedInContext m hm outside seam hcubic hplanar before after).map w
    changed.1 = w.1 ∧ changed.2.1.1 = w.2.1.1 ∧
      changed.2.1.2.1 = w.2.1.2.1 ∧ changed.2.2 = w.2.2 := by
  exact ⟨rfl,rfl,rfl,rfl⟩

end
end Mettapedia.GraphTheory.FourColor.PaddedCycleCap

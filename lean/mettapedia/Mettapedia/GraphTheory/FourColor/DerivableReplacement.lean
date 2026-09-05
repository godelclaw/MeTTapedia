import Mettapedia.GraphTheory.FourColor.CyclicNoncrossing
import Mettapedia.GraphTheory.FourColor.GoertzelV24TargetAwareSupportReplacement

/-!
# Replacement by a piece whose words derive into the removed piece's support

The closed-count bridge says a sewn instance is colourable iff some seam word
lies in both sides' supports.  If every seam word of a replacement piece is
*derivable* (by Kempe switches of the outside, which planarity makes physical)
into the removed piece's support, then non-colourability of the original sewn
instance transfers to the instance sewn with the replacement
(`not_composeRotationSystem_taitColorable_of_derivable`).  This is the
colourability half of "an accepted reducibility certificate excludes the
configuration"; the validity of the replaced instance as a spherical cubic map
is the other half.
-/

namespace Mettapedia.GraphTheory.FourColor
namespace KempeDerivation

open Compositional.BoundaryKempeSwitch Compositional.CyclicBoundaryMatching
open Compositional.CyclicNoncrossing
open GoertzelV24ClosedCountReplacement GoertzelV24PhysicalClosedCountBridge
open GoertzelV24CyclicBondBoundary
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexagonPairingTargetAwareBoundary
open GoertzelV24OpenTangleComposition
open GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24PortTangleCommonKempeWeb
open GoertzelV24PortTangleCutParity
open GoertzelV24PortTangleGluing
open GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24PortTanglePhysicalKempeClosure
open GoertzelV24RawNooseCountPumping
open GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24VertexSideOpenTangle
open GoertzelV24VertexSidePrimalKempeTrail
open SimpleGraph
open SimpleGraphDartRotation

universe u

/-! ## The two closings of an open tangle carry the same colourings -/

section Transfer

variable {V I L : Type u} (left : OpenTangleData V I L)

/-- a colouring of the left closing, read on the open tangle -/
def ofClosed (c : Coloring (leftClosedPortTangle left)) : Coloring (ofOpenTangleData left) where
  color
    | Sum.inl i => c.color (Sum.inl i)
    | Sum.inr l => c.color (Sum.inr (Sum.inr l))
  invariant d := c.invariant d

/-- a colouring of the open tangle, read on the left closing -/
def toClosed (c : Coloring (ofOpenTangleData left)) : Coloring (leftClosedPortTangle left) where
  color
    | Sum.inl i => c.color (Sum.inl i)
    | Sum.inr (Sum.inl e) => PEmpty.elim e
    | Sum.inr (Sum.inr l) => c.color (Sum.inr l)
  invariant d := c.invariant d

theorem ofClosed_isProper (c : Coloring (leftClosedPortTangle left)) (h : IsProper c) :
    IsProper (ofClosed left c) := by
  refine ⟨fun d => ?_, fun d e hv hne => ?_⟩
  · rcases d with i | l
    · exact h.1 (Sum.inl i)
    · exact h.1 (Sum.inr (Sum.inr l))
  · rcases d with i | l <;> rcases e with j | m
    · exact h.2 _ _ hv (fun heq => hne (by cases heq; rfl))
    · exact h.2 (Sum.inl i) (Sum.inr (Sum.inr m)) hv (by simp)
    · exact h.2 (Sum.inr (Sum.inr l)) (Sum.inl j) hv (by simp)
    · exact h.2 _ _ hv (fun heq => hne (by cases heq; rfl))

theorem toClosed_isProper (c : Coloring (ofOpenTangleData left)) (h : IsProper c) :
    IsProper (toClosed left c) := by
  refine ⟨fun d => ?_, fun d d' hv hne => ?_⟩
  · rcases d with i | e | l
    · exact h.1 (Sum.inl i)
    · exact e.elim
    · exact h.1 (Sum.inr l)
  · rcases d with i | e | l <;> rcases d' with j | e' | m
    · exact h.2 _ _ hv (fun heq => hne (by cases heq; rfl))
    · exact e'.elim
    · exact h.2 (Sum.inl i) (Sum.inr m) hv (by simp)
    · exact e.elim
    · exact e.elim
    · exact e.elim
    · exact h.2 (Sum.inr l) (Sum.inl j) hv (by simp)
    · exact e'.elim
    · exact h.2 _ _ hv (fun heq => hne (by cases heq; rfl))

/-- **the outer support of the left closing is the support of the open tangle** -/
theorem mem_outerSupport_iff (y : L → Color) :
    y ∈ outerSupport (leftClosedPortTangle left) ↔ Nonempty (Col (ofOpenTangleData left) y) := by
  constructor
  · rintro ⟨⟨c, hproper, hword⟩⟩
    refine ⟨⟨ofClosed left c, ofClosed_isProper left c hproper, ?_⟩⟩
    funext l
    exact congrFun hword (Sum.inr l)
  · rintro ⟨⟨c, hproper, hword⟩⟩
    refine ⟨⟨toClosed left c, toClosed_isProper left c hproper, ?_⟩⟩
    funext p
    rcases p with e | l
    · exact e.elim
    · exact congrFun hword l

end Transfer

/-! ## Words in coordinates -/

section Words

variable {n : Nat} {L : Type u}

/-- the words of a set of seam words, in coordinates -/
def wordsOf (order : Fin n ≃ L) (S : Set (CutWord L)) : Set (Word n) :=
  {w | (fun l => w (order.symm l)) ∈ S}

end Words

/-! ## Derivable replacement -/

section Replacement

variable {V₁ : Type u} [Fintype V₁] [DecidableEq V₁]
  {G : SimpleGraph V₁} [DecidableRel G.Adj]

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

theorem mem_supportInCoordinates_of_outerSupport (graphData : Data G) (keep : V₁ → Prop)
    (outer : RetainedDart graphData.toRotationSystem keep) {n : Nat}
    (order : Fin n ≃ BoundaryDart graphData.toRotationSystem keep) (w : Word n)
    (h : (fun l => (w (order.symm l)).1) ∈
      outerSupport (leftClosedPortTangle (ofVertexSide graphData.toRotationSystem keep outer))) :
    w ∈ supportInCoordinates order (vertexSidePortTangle graphData keep outer) :=
  (mem_outerSupport_iff _ _).mp h

theorem mem_outerSupport_of_supportInCoordinates (graphData : Data G) (keep : V₁ → Prop)
    (outer : RetainedDart graphData.toRotationSystem keep) {n : Nat}
    (order : Fin n ≃ BoundaryDart graphData.toRotationSystem keep) (w : Word n)
    (h : w ∈ supportInCoordinates order (vertexSidePortTangle graphData keep outer)) :
    (fun l => (w (order.symm l)).1) ∈
      outerSupport (leftClosedPortTangle (ofVertexSide graphData.toRotationSystem keep outer)) :=
  (mem_outerSupport_iff _ _).mpr h

/-- **Derivable replacement preserves non-colourability of the sewn instance.**  Cut a spherical
cubic map along a vertex side with facial cyclic boundary coordinates; if every seam word of a
replacement piece derives into the removed piece's support, and the map is not Tait-colourable,
then neither is the map sewn from the outside and the replacement. -/
theorem not_composeRotationSystem_taitColorable_of_derivable
    (graphData : Data G)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (hsphere : OrbitSphericalCubicMapData graphData.toRotationSystem)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (keep : V₁ → Prop)
    (hcomplementConnected : (G.induce {vertex | ¬keep vertex}).Connected)
    {n : Nat} (hn : 2 ≤ n)
    (order : Fin n ≃ BoundaryDart graphData.toRotationSystem keep)
    (hsuccessor : order.permCongr (finRotate n) =
      retainedRegionBoundarySuccessor graphData.toRotationSystem keep)
    (outer : RetainedDart graphData.toRotationSystem keep)
    {Y J R : Type u} [Fintype Y] [DecidableEq Y] [Fintype J] [DecidableEq J]
      [Fintype R] [DecidableEq R]
    (right : OpenTangleData Y J R) (matching : BoundaryDart graphData.toRotationSystem keep ≃ R)
    {Y' J' R' : Type u} [Fintype Y'] [DecidableEq Y'] [Fintype J'] [DecidableEq J']
      [Fintype R'] [DecidableEq R']
    (right' : OpenTangleData Y' J' R')
    (matching' : BoundaryDart graphData.toRotationSystem keep ≃ R')
    (hder : ∀ w ∈ wordsOf order (taitInnerSupport (rightClosedPortTangle right' matching')),
      Derivable (wordsOf order (taitInnerSupport (rightClosedPortTangle right matching))) w)
    (hzero : ¬ ∃ coloring : ((ofVertexSide graphData.toRotationSystem keep outer).composeRotationSystem
        right matching).EdgeColoring Color,
      ((ofVertexSide graphData.toRotationSystem keep outer).composeRotationSystem
        right matching).IsTaitEdgeColoring coloring) :
    ¬ ∃ coloring : ((ofVertexSide graphData.toRotationSystem keep outer).composeRotationSystem
        right' matching').EdgeColoring Color,
      ((ofVertexSide graphData.toRotationSystem keep outer).composeRotationSystem
        right' matching').IsTaitEdgeColoring coloring := by
  intro hcolorable
  set left := ofVertexSide graphData.toRotationSystem keep outer
  have hclosed : ClosedColorable (leftClosedPortTangle left) (rightClosedPortTangle right' matching') :=
    (closedColorable_iff_composeRotationSystem_taitColorable left right' matching').2 hcolorable
  obtain ⟨y, hyOuter, hyInner⟩ := (closedColorable_iff _ _).1 hclosed
  obtain ⟨taitWord, htait, hforget⟩ := exists_cutWord_of_mem_innerSupport _ hyInner
  let w : Word n := fun i => taitWord (order i)
  have hwCap : w ∈ wordsOf order (taitInnerSupport (rightClosedPortTangle right' matching')) := by
    show (fun l => w (order.symm l)) ∈ taitInnerSupport (rightClosedPortTangle right' matching')
    have : (fun l => w (order.symm l)) = taitWord := by
      funext l; simp [w]
    rw [this]; exact htait
  have hwSupp : w ∈ supportInCoordinates order (vertexSidePortTangle graphData keep outer) := by
    apply mem_supportInCoordinates_of_outerSupport
    have : (fun l => (w (order.symm l)).1) = y := by
      funext l; rw [← hforget]; simp [w, cutWordColor]
    rw [this]; exact hyOuter
  obtain ⟨w', hw'Disk, hw'Supp⟩ := exists_mem_target_of_derivable_vertexSide graphData htwoSided
    hdual hconnected hsphere hcubic hrotation keep hcomplementConnected hn order hsuccessor outer
    (hder w hwCap) hwSupp
  apply hzero
  apply (closedColorable_iff_composeRotationSystem_taitColorable left right matching).1
  rw [closedColorable_iff]
  refine ⟨fun l => (w' (order.symm l)).1, mem_outerSupport_of_supportInCoordinates graphData keep
    outer order w' hw'Supp, ?_⟩
  exact hw'Disk

end Replacement

end KempeDerivation
end Mettapedia.GraphTheory.FourColor

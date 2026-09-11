import Mettapedia.GraphTheory.FourColor.OpenTangleBoundaryConnectivity
import Mettapedia.GraphTheory.FourColor.VertexSideEulerMass

/-!
# Connectivity and Euler characteristic from boundary records

For proper vertex sides the boundary connectivity partition already
determines the component count, hence the Euler mass. No separate
unbounded integer or redundant component-count field is needed. Equal
connectivity and face-return records preserve connectedness and Euler
characteristic under the actual sewing constructor. Bridgelessness is
not asserted by these two records.
-/

namespace Mettapedia.GraphTheory.FourColor.VertexSideStructuralReplacement

open GoertzelV24FaceDualConnectedness GoertzelV24RotationCutDartDecomposition
open GoertzelV24OpenTangleComposition GoertzelV24CompositeSeamMultigraph
open VertexSideCappedComponents OpenTangleBoundaryConnectivity
open GoertzelV24OrbitFaceCurvatureBulk

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Surjective maps with the same kernel have equally many target points.
Reuse the standard kernel-quotient equivalence; no enumeration is needed. -/
theorem card_eq_of_same_kernel {A B C : Type*} [Fintype B] [Fintype C]
    (f : A → B) (g : A → C) (hf : Function.Surjective f) (hg : Function.Surjective g)
    (h : ∀ a b, f a = f b ↔ g a = g b) : Fintype.card B = Fintype.card C := by
  have hk : Setoid.ker f = Setoid.ker g := Setoid.ext h
  have hfc := Nat.card_congr (Setoid.quotientKerEquivOfSurjective f hf)
  have hgc := Nat.card_congr (Setoid.quotientKerEquivOfSurjective g hg)
  rw [hk] at hfc
  simpa only [Nat.card_eq_fintype_card] using hfc.symm.trans hgc

variable {V E V' E' K : Type*}
  [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  [Fintype V'] [DecidableEq V'] [Fintype E'] [DecidableEq E']

theorem code_ofVertexSide_iff (RS : RotationSystem V E) (side : V → Prop)
    (outer : RetainedDart RS side) (coords : BoundaryDart RS side ≃ K) (a b : K) :
    code (OpenTangleData.ofVertexSide RS side outer) coords a b = true ↔
      boundaryComponent RS side (coords.symm a) = boundaryComponent RS side (coords.symm b) := by
  rw [code_eq_true, sideReach_iff_induce_reachable]
  exact SimpleGraph.ConnectedComponent.eq.symm

/-- Equal boundary partitions of proper actual sides determine their
component counts, even across different ambient graph carriers. -/
theorem components_eq_of_code (RS : RotationSystem V E) (RS' : RotationSystem V' E')
    (hconn : (rotationPrimalGraph RS).Connected) (hconn' : (rotationPrimalGraph RS').Connected)
    (side : V → Prop) (side' : V' → Prop) (hproper : ∃ v, ¬ side v) (hproper' : ∃ v, ¬ side' v)
    (outer : RetainedDart RS side) (outer' : RetainedDart RS' side')
    (oc : BoundaryDart RS side ≃ K) (nc : BoundaryDart RS' side' ≃ K)
    (heq : code (OpenTangleData.ofVertexSide RS side outer) oc =
      code (OpenTangleData.ofVertexSide RS' side' outer') nc) :
    Fintype.card (SideGraph RS side).ConnectedComponent =
      Fintype.card (SideGraph RS' side').ConnectedComponent := by
  apply card_eq_of_same_kernel
    (fun a => boundaryComponent RS side (oc.symm a))
    (fun a => boundaryComponent RS' side' (nc.symm a))
    ((boundaryComponent_surjective RS hconn side hproper).comp oc.symm.surjective)
    ((boundaryComponent_surjective RS' hconn' side' hproper').comp nc.symm.surjective)
  intro a b
  have hc := congrFun (congrFun heq a) b
  exact (code_ofVertexSide_iff RS side outer oc a b).symm.trans
    ((congrArg (fun x : Bool => x = true) hc).to_iff.trans
      (code_ofVertexSide_iff RS' side' outer' nc a b))

variable {X I L M : Type*} [Fintype X] [DecidableEq X] [Fintype I] [DecidableEq I]
  [Fintype L] [DecidableEq L] [Fintype K] [Fintype M]

/-- The two established structural conditions, derived from literal
finite boundary records in every fixed exterior. This is not a claim
of full admissibility: bridge-freeness remains separate. -/
theorem replacement_euler_and_connected (RS : RotationSystem V E) (RS' : RotationSystem V' E')
    (hsphere : OrbitSphericalCubicMapData RS) (hsphere' : OrbitSphericalCubicMapData RS')
    (hconn : (rotationPrimalGraph RS).Connected) (hconn' : (rotationPrimalGraph RS').Connected)
    (hrot : VertexRotationCyclic RS) (hrot' : VertexRotationCyclic RS')
    (side : V → Prop) (side' : V' → Prop) (hproper : ∃ v, ¬ side v) (hproper' : ∃ v, ¬ side' v)
    (outer : RetainedDart RS side) (outer' : RetainedDart RS' side')
    (oc : BoundaryDart RS side ≃ K) (nc : BoundaryDart RS' side' ≃ K)
    (oo : M → Option (InternalDart RS side ⊕ BoundaryDart RS side))
    (no : M → Option (InternalDart RS' side' ⊕ BoundaryDart RS' side'))
    (hcode : code (OpenTangleData.ofVertexSide RS side outer) oc =
      code (OpenTangleData.ofVertexSide RS' side' outer') nc)
    (hface : NamedOpenFace.record (OpenTangleData.ofVertexSide RS side outer) oc oo =
      NamedOpenFace.record (OpenTangleData.ofVertexSide RS' side' outer') nc no)
    (left : OpenTangleData X I L) (outside : L ≃ K) :
    OpenTangleRewireFaces.compositeEuler left (OpenTangleData.ofVertexSide RS side outer)
        (outside.trans oc.symm) =
      OpenTangleRewireFaces.compositeEuler left (OpenTangleData.ofVertexSide RS' side' outer')
        (outside.trans nc.symm) ∧
    ((rotationPrimalGraph (left.composeRotationSystem (OpenTangleData.ofVertexSide RS side outer)
        (outside.trans oc.symm))).Connected ↔
      (rotationPrimalGraph (left.composeRotationSystem (OpenTangleData.ofVertexSide RS' side' outer')
        (outside.trans nc.symm))).Connected) := by
  constructor
  · exact VertexSideEulerMass.replacement_euler RS RS' hsphere hsphere' hconn hconn' hrot hrot'
      side side' outer outer'
      (components_eq_of_code RS RS' hconn hconn' side side' hproper hproper' outer outer' oc nc hcode)
      oc nc oo no hface left outside
  · exact OpenTangleBoundaryConnectivity.replacement_connected left _ _
      (visible_ofVertexSide RS side outer hconn hproper)
      (visible_ofVertexSide RS' side' outer' hconn' hproper') oc nc outside hcode

end
end Mettapedia.GraphTheory.FourColor.VertexSideStructuralReplacement

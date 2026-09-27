import Mettapedia.GraphTheory.FourColor.FaceBoundaryJunctions
import Mettapedia.GraphTheory.FourColor.OrderedEdgePath

/-!
# The new edges of a facial event form an actual simple path

The ordered exposed boundary arc gives a path with the original edge and
vertex identifiers. Its final vertex is included in the injectivity proof;
the two ends are distinct. Consequently its proper edge colourings have
exactly the consecutive inequalities of an ordinary path.
-/

namespace Mettapedia.GraphTheory.FourColor.FaceExposedPath

open Equiv Equiv.Perm
open GoertzelV24FaceOrbitIncidence GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation FaceRegionDegree EdgeShoreRotation
open PlanePatchCurvature FaceRegionShelling FaceRegionComplement
open FaceRegionBoundary FaceRegionPatch FaceRegionStepBoundary
open PhysicalForkCodeCut PhysicalForkCodeFaces PermutationSingleExitArc
open FaceExposedBoundary

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (data : Data G)
variable {S R : Region data} (e : Event S R)
variable (outer : Dart data.toRotationSystem (edges data.toRotationSystem R.faces))
variable (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
variable (ho : dartOrbitFace data.toRotationSystem outer.val ∉ R.faces)

local notation "New" => toMap data.toRotationSystem (edges data.toRotationSystem R.faces) outer

variable (b : Arc
  (toMap data.toRotationSystem (edges data.toRotationSystem R.faces) outer).phi
  (exposedDarts data e outer))

theorem power_on_outer (n : ℕ) : ((New).phi ^ n) b.first ∈ outerDarts New := by
  induction n with
  | zero => simpa using ((mem_exposedDarts data e outer b.first).mp b.first_mem).1
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply]
    exact (outer_phi_iff (RS := New) _).mpr ih

def arcEdge (i : Fin b.length) : exposedEdges data e :=
  ⟨data.toRotationSystem.edgeOf (((New).phi ^ i.val) b.first).val,
    ((mem_exposedDarts data e outer _).mp (b.mem i.isLt)).2⟩

include ambient ho in
theorem arcEdge_bijective : Function.Bijective (arcEdge data e outer b) := by
  constructor
  · intro i j hij
    apply b.injective
    apply outer_edges_injective data ambient R outer ho
      (power_on_outer data e outer b i.val) (power_on_outer data e outer b j.val)
    exact congrArg Subtype.val hij
  · intro x
    have hx := (congrArg (fun A : Finset G.edgeSet => x.val ∈ A)
      (exposed_edge_image data e outer ambient ho)).mpr x.property
    obtain ⟨d, hd, hdx⟩ := Finset.mem_image.mp hx
    have hd' := (congrArg (fun A : Finset (New).D => d ∈ A) b.exact).mp hd
    obtain ⟨i, hi, hid⟩ := Finset.mem_image.mp hd'
    refine ⟨⟨i, Finset.mem_range.mp hi⟩, Subtype.ext ?_⟩
    change data.toRotationSystem.edgeOf (((New).phi ^ i) b.first).val = x.val
    rw [hid]
    exact hdx

/-- The path is enumerated in the actual new boundary order. -/
def path : OrderedEdgePath.Path data.toRotationSystem.endpoints (exposedEdges data e) where
  length := b.length
  positive := b.positive
  vertex := fun i => data.toRotationSystem.vertOf (((New).phi ^ i.val) b.first).val
  vertex_injective := by
    intro i j hij
    apply b.extended_injective
    apply FaceRegionBoundary.outer_simple outer
      (cubic3_of _ ambient.spherical.cubic ambient.vertexRotationCyclic) ho
      (power_on_outer data e outer b i.val) (power_on_outer data e outer b j.val)
    exact Subtype.ext hij
  edge := Equiv.ofBijective (arcEdge data e outer b) (arcEdge_bijective data e outer ambient ho b)
  endpoints := by
    intro i
    change data.toRotationSystem.endpoints (data.toRotationSystem.edgeOf (((New).phi ^ i.val) b.first).val) =
      {data.toRotationSystem.vertOf (((New).phi ^ i.val) b.first).val,
        data.toRotationSystem.vertOf (((New).phi ^ (i.val + 1)) b.first).val}
    rw [data.toRotationSystem.endpoints_eq_pair_of_mem (data.toRotationSystem.mem_dartsOn.mpr rfl)]
    congr 1
    congr 1
    rw [pow_succ', Perm.mul_apply]
    exact (congrArg Subtype.val ((New).vert_phi_eq_vert_alpha _)).symm

theorem path_length : (path data e outer ambient ho b).length = (exposedEdges data e).card := by
  exact b.length_eq_card.trans (exposed_darts_card data e outer ambient ho)

/-- This is a consequence of the geometric arc, with no colouring supplier. -/
theorem proper_iff (c : G.edgeSet → Fin 3) :
    GoertzelV24ForkInterfaceSupport.Proper data.toRotationSystem.endpoints (exposedEdges data e) c ↔
      (path data e outer ambient ho b).Consecutive c :=
  (path data e outer ambient ho b).proper_iff c

end
end Mettapedia.GraphTheory.FourColor.FaceExposedPath

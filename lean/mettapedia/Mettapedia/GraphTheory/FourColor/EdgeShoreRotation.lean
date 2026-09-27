import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeEuler
import Mettapedia.GraphTheory.FourColor.PermutationFirstReturnRestriction
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedCutFaceOrbit

/-!
# A retained edge shore as an actual rotation system

The fork semantics already restricts edge flips and takes first return of
the vertex rotation. Here that same presentation becomes a `RotationSystem`
on exactly the retained edges and their touched vertices. Its primal graph,
face permutation and Euler equation are identified with the existing shore
semantics. This supplies the carrier for extracting plane patches without
assuming a new embedding or replacing the cyclic orders.
-/

namespace Mettapedia.GraphTheory.FourColor.EdgeShoreRotation

open Equiv Equiv.Perm
open GoertzelV24FaceDualConnectedness GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceCurvatureBulk GoertzelV24FaceOrbitPartitionBridge
open GoertzelV24OrderedCutFaceReturnProfile PermutationFirstReturnRestriction
open EdgeShoreFaceForkFold PhysicalForkCodeFaces PhysicalForkCodeCut PhysicalForkCodeEuler

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (RS : RotationSystem V E) (S : Finset E)

abbrev Dart := {d : RS.D // InShore RS.edgeOf S d}
abbrev Vertex := {v : V // v ∈ touched RS S}

def vertex (d : Dart RS S) : Vertex RS S :=
  ⟨RS.vertOf d.val, mem_touched.mpr ⟨d.val, rfl, d.property⟩⟩

def edge (d : Dart RS S) : S := ⟨RS.edgeOf d.val, d.property⟩

def edgeFiberEquiv (e : S) : {d : Dart RS S // edge RS S d = e} ≃
    {d : RS.D // RS.edgeOf d = e.val} where
  toFun d := ⟨d.val.val, congrArg Subtype.val d.property⟩
  invFun d := ⟨⟨d.val, by
    change RS.edgeOf d.val ∈ S
    rw [d.property]
    exact e.property⟩, Subtype.ext d.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- No isolated or discarded vertex is left in the new map. The outer
dart chooses a face; it makes no claim that this face is simple. -/
abbrev toMap (outer : Dart RS S) : RotationSystem (Vertex RS S) S where
  D := Dart RS S
  edgeOf := edge RS S
  vertOf := vertex RS S
  alpha := shoreEdge RS.alpha RS.edgeOf RS.edge_alpha S
  rho := shoreRot RS.rho RS.edgeOf S
  alpha_involutive d := Subtype.ext (RS.alpha_involutive d.val)
  alpha_fixfree d h := RS.alpha_fixfree d.val (congrArg Subtype.val h)
  edge_alpha d := Subtype.ext (RS.edge_alpha d.val)
  edge_fiber_two e := by
    have hc := Fintype.card_congr (edgeFiberEquiv RS S e)
    rw [Fintype.card_subtype, Fintype.card_subtype] at hc
    exact hc.trans (RS.edge_fiber_two e.val)
  vert_rho d := Subtype.ext (vertOf_nextHit RS (InShore RS.edgeOf S) d)
  outer := outer
  no_self_loops d h := RS.no_self_loops d.val (congrArg Subtype.val h)

variable {RS S}

theorem phi_eq (outer : Dart RS S) :
    (toMap RS S outer).phi = shoreFace RS.rho RS.alpha RS.edgeOf RS.edge_alpha S := rfl

/-- The actual map and the fork semantics have precisely the same primal
edges, including any parallel edge identifiers. -/
theorem primal_eq (outer : Dart RS S) :
    rotationPrimalGraph (toMap RS S outer) =
      (shoreGraph RS S).induce (touched RS S : Set V) := by
  ext u v
  constructor
  · rintro ⟨d, hu, hv⟩
    exact ⟨d.val, d.property, congrArg Subtype.val hu, congrArg Subtype.val hv⟩
  · rintro ⟨d, hd, hu, hv⟩
    exact ⟨⟨d, hd⟩, Subtype.ext hu, Subtype.ext hv⟩

private theorem walk_touched {u v : V} (p : (shoreGraph RS S).Walk u v)
    (hu : u ∈ touched RS S) : ∀ x ∈ p.support, x ∈ touched RS S := by
  induction p with
  | nil => simpa using hu
  | @cons u v w hadj p ih =>
    intro x hx
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hu
    · obtain ⟨d, hd, _, hv⟩ := hadj
      have hv' : v ∈ touched RS S := hv ▸ alpha_touched hd
      exact ih hv' x hx

theorem connected (outer : Dart RS S) (hS : ShoreConnected RS S) :
    (rotationPrimalGraph (toMap RS S outer)).Connected := by
  rw [primal_eq]
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨vertex RS S outer, ?_⟩
  intro v
  obtain ⟨p⟩ := hS (RS.vertOf outer.val) v.val (vertex RS S outer).property v.property
  exact ⟨p.induce _ (walk_touched p (vertex RS S outer).property)⟩

theorem rotationCyclic (outer : Dart RS S) (hr : VertexRotationCyclic RS) :
    VertexRotationCyclic (toMap RS S outer) := by
  intro d e h
  apply (nextHitPerm_sameCycle_iff RS.rho (InShore RS.edgeOf S) d e).mpr
  exact hr d.val e.val (congrArg Subtype.val h)

/-- Planarity passes to this literal edge restriction using the previously
proved shore Euler theorem. The Euler equation is not an input field. -/
theorem euler (outer : Dart RS S) (hs : OrbitSphericalCubicMapData RS)
    (hc : (rotationPrimalGraph RS).Connected) (hr : VertexRotationCyclic RS)
    (hS : ShoreConnected RS S) :
    (Fintype.card (Vertex RS S) : ℤ) - Fintype.card S +
      Fintype.card (OrbitFace (toMap RS S outer)) = 2 := by
  have hh := shore_euler hs hc hr S hS ⟨RS.edgeOf outer.val, outer.property⟩
  rw [Fintype.card_coe, Fintype.card_coe, card_orbitFace_eq_faceCycleLengths_card]
  change ((touched RS S).card : ℤ) - S.card +
    (shoreFace RS.rho RS.alpha RS.edgeOf RS.edge_alpha S).partition.parts.card = 2
  omega

/-- Retaining the successor edge leaves this facial step unchanged. This
is the local fact used to preserve every face wholly inside a cut patch. -/
theorem phi_step (outer d : Dart RS S) (hnext : RS.edgeOf (RS.phi d.val) ∈ S) :
    ((toMap RS S outer).phi d).val = RS.phi d.val := by
  exact nextHit_apply_of_step RS.rho (InShore RS.edgeOf S)
    (shoreEdge RS.alpha RS.edgeOf RS.edge_alpha S d) hnext

/-- Every step of a fully retained original face is unchanged. -/
theorem phi_pow_of_full_face (outer d : Dart RS S)
    (hfull : ∀ e, RS.phi.SameCycle d.val e → RS.edgeOf e ∈ S) (n : ℕ) :
    (((toMap RS S outer).phi ^ n) d).val = (RS.phi ^ n) d.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply]
    rw [phi_step, ih, pow_succ', Perm.mul_apply]
    rw [ih]
    apply hfull
    exact (Perm.sameCycle_apply_right).mpr
      ((Perm.sameCycle_pow_right).mpr (Perm.SameCycle.refl RS.phi d.val))

/-- A fully retained face has exactly the same number of dart occurrences
in the new map. Neither simplicity nor connectedness is needed here. -/
theorem face_length_of_full_face (outer d : Dart RS S)
    (hfull : ∀ e, RS.phi.SameCycle d.val e → RS.edgeOf e ∈ S) :
    (orbitFaceDarts (toMap RS S outer) (dartOrbitFace (toMap RS S outer) d)).card =
      (orbitFaceDarts RS (dartOrbitFace RS d.val)).card := by
  rw [orbitFaceDarts_dartOrbitFace_eq_faceOrbit,
    orbitFaceDarts_dartOrbitFace_eq_faceOrbit]
  apply GoertzelV24OrderedCutFaceOrbit.card_sameCycle_eq_of_injective_map_apply
    (toMap RS S outer).phi RS.phi Subtype.val Subtype.val_injective d
  intro e he
  obtain ⟨n, rfl⟩ := he.exists_nat_pow_eq
  apply phi_step
  rw [phi_pow_of_full_face outer d hfull]
  apply hfull
  exact (Perm.sameCycle_apply_right).mpr
    ((Perm.sameCycle_pow_right).mpr (Perm.SameCycle.refl RS.phi d.val))

/-- The original vertex fibre is restricted to exactly the retained edges. -/
def vertexFiberEquiv (outer : Dart RS S) (v : Vertex RS S) :
    {d : (toMap RS S outer).D // (toMap RS S outer).vertOf d = v} ≃
      {d : RS.D // RS.vertOf d = v.val ∧ RS.edgeOf d ∈ S} where
  toFun d := ⟨d.val.val, congrArg Subtype.val d.property, d.val.property⟩
  invFun d := ⟨⟨d.val, d.property.2⟩, Subtype.ext d.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem degree_eq (outer : Dart RS S) (v : Vertex RS S) :
    ((toMap RS S outer).dartsAt v).card =
      ((RS.dartsAt v.val).filter fun d => RS.edgeOf d ∈ S).card := by
  have hc := Fintype.card_congr (vertexFiberEquiv outer v)
  simpa [Fintype.card_subtype, RotationSystem.dartsAt, Finset.filter_filter] using hc

end
end Mettapedia.GraphTheory.FourColor.EdgeShoreRotation

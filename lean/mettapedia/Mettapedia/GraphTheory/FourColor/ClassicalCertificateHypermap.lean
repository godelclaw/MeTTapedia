import Mathlib.Data.Setoid.Basic
import Mettapedia.GraphTheory.FourColor.GoertzelV24FaceDualConnectedness
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceCurvatureBulk

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateHypermap

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceCurvatureBulk

/-- A finite hypermap in the symmetric permutation presentation.  The
triangular identity says that crossing an edge, advancing around a face, and
then advancing around a vertex returns to the original dart. -/
structure FiniteHypermap (D : Type*) [Fintype D] [DecidableEq D] where
  edge : Equiv.Perm D
  node : Equiv.Perm D
  face : Equiv.Perm D
  triangle : ∀ dart, node (face (edge dart)) = dart

namespace FiniteHypermap

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The orbit type of a finite permutation. -/
abbrev Orbit (permutation : Equiv.Perm D) :=
  Quotient (Equiv.Perm.SameCycle.setoid permutation)

noncomputable instance orbitFintype (permutation : Equiv.Perm D) :
    Fintype (Orbit permutation) :=
  Fintype.ofFinite (Orbit permutation)

/-- The standard Euler characteristic of a finite hypermap. -/
noncomputable def eulerCharacteristic (H : FiniteHypermap D) : Int :=
  (Fintype.card (Orbit H.node) : Int) -
    Fintype.card (Orbit H.edge) + Fintype.card (Orbit H.face)

omit [DecidableEq D] in
/-- An invariant of a permutation is constant on each permutation orbit. -/
theorem invariant_of_sameCycle
    (permutation : Equiv.Perm D) (value : D → β)
    (hinvariant : ∀ dart, value (permutation dart) = value dart)
    {left right : D} (hsame : permutation.SameCycle left right) :
    value left = value right := by
  obtain ⟨power, hpower⟩ := hsame.exists_nat_pow_eq
  have hpow : ∀ (n : Nat) (dart : D),
      value ((permutation ^ n) dart) = value dart := by
    intro n
    induction n with
    | zero => intro dart; rfl
    | succ n ih =>
        intro dart
        rw [pow_succ, Equiv.Perm.mul_apply]
        exact (ih (permutation dart)).trans (hinvariant dart)
  exact (hpow power left).symm.trans (congrArg value hpower)

/-- If the fibers of a surjection are precisely the cycles of a permutation,
its codomain is canonically equivalent to the orbit quotient. -/
noncomputable def orbitEquivOfFiber
    (permutation : Equiv.Perm D) (value : D → β)
    (hsurjective : Function.Surjective value)
    (hfiber : ∀ left right,
      permutation.SameCycle left right ↔ value left = value right) :
    Orbit permutation ≃ β :=
  (Quotient.congrRight hfiber).trans
    (Setoid.quotientKerEquivOfSurjective value hsurjective)

/-- The two cyclic rotations of the triangular identity. -/
theorem face_edge_node (H : FiniteHypermap D) (dart : D) :
    H.face (H.edge (H.node dart)) = dart := by
  apply H.node.injective
  exact H.triangle (H.node dart)

theorem edge_node_face (H : FiniteHypermap D) (dart : D) :
    H.edge (H.node (H.face dart)) = dart := by
  have htriangle := H.triangle (H.edge.symm dart)
  apply_fun H.edge at htriangle
  simpa using htriangle

end FiniteHypermap

end ClassicalCertificateHypermap

namespace RotationSystem

open ClassicalCertificateHypermap
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceCurvatureBulk

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-- Every rotation system determines a finite hypermap.  The hypermap vertex
permutation is the inverse stored vertex rotation, while its face permutation
is the existing face successor. -/
def toFiniteHypermap (RS : RotationSystem V E) : FiniteHypermap RS.D where
  edge := RS.alpha
  node := RS.rho.symm
  face := RS.phi
  triangle := by
    intro dart
    simp [RotationSystem.phi_apply, RS.alpha_involutive]

@[simp] theorem toFiniteHypermap_edge (RS : RotationSystem V E) :
    RS.toFiniteHypermap.edge = RS.alpha :=
  rfl

@[simp] theorem toFiniteHypermap_node (RS : RotationSystem V E) :
    RS.toFiniteHypermap.node = RS.rho.symm :=
  rfl

@[simp] theorem toFiniteHypermap_face (RS : RotationSystem V E) :
    RS.toFiniteHypermap.face = RS.phi :=
  rfl

/-- Hypermap edge cycles are exactly the stored two-dart edge fibers. -/
theorem toFiniteHypermap_edge_sameCycle_iff
    (RS : RotationSystem V E) (left right : RS.D) :
    RS.toFiniteHypermap.edge.SameCycle left right ↔
      RS.edgeOf left = RS.edgeOf right := by
  constructor
  · intro hsame
    exact FiniteHypermap.invariant_of_sameCycle RS.alpha RS.edgeOf
      RS.edge_alpha (by simpa using hsame)
  · intro hedge
    rcases RS.edge_fiber_two_cases (e := RS.edgeOf left)
        (d := left) (y := right) rfl hedge.symm with hsame | hopposite
    · subst right
      exact Equiv.Perm.SameCycle.rfl
    · subst right
      exact ⟨1, by simp⟩

/-- Under the genuine cyclic-rotation condition, hypermap vertex cycles are
exactly the stored vertex fibers. -/
theorem toFiniteHypermap_node_sameCycle_iff
    (RS : RotationSystem V E) (hrotation : VertexRotationCyclic RS)
    (left right : RS.D) :
    RS.toFiniteHypermap.node.SameCycle left right ↔
      RS.vertOf left = RS.vertOf right := by
  constructor
  · intro hsame
    have hrho : RS.rho.SameCycle left right := by
      change (RS.rho⁻¹).SameCycle left right at hsame
      exact Equiv.Perm.SameCycle.of_inv hsame
    exact FiniteHypermap.invariant_of_sameCycle RS.rho RS.vertOf
      RS.vert_rho hrho
  · intro hvertex
    have hrho := hrotation left right hvertex
    change (RS.rho⁻¹).SameCycle left right
    exact Equiv.Perm.SameCycle.inv hrho

theorem edgeOf_surjective (RS : RotationSystem V E) :
    Function.Surjective RS.edgeOf := by
  intro edge
  obtain ⟨dart, hdart⟩ := RS.dartsOn_nonempty edge
  exact ⟨dart, (RS.mem_dartsOn).1 hdart⟩

theorem vertOf_surjective_of_isCubic
    (RS : RotationSystem V E) (hcubic : RS.IsCubic) :
    Function.Surjective RS.vertOf := by
  intro vertex
  exact exists_dart_vertOf_eq_of_isCubic RS hcubic vertex

/-- The edge-orbit quotient of the associated hypermap is canonically the
rotation system's edge type. -/
noncomputable def finiteHypermapEdgeOrbitEquiv
    (RS : RotationSystem V E) :
    FiniteHypermap.Orbit RS.toFiniteHypermap.edge ≃ E :=
  FiniteHypermap.orbitEquivOfFiber RS.toFiniteHypermap.edge RS.edgeOf
    RS.edgeOf_surjective RS.toFiniteHypermap_edge_sameCycle_iff

/-- The vertex-orbit quotient of a cubic cyclic rotation system is
canonically its vertex type. -/
noncomputable def finiteHypermapNodeOrbitEquiv
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS) :
    FiniteHypermap.Orbit RS.toFiniteHypermap.node ≃ V :=
  FiniteHypermap.orbitEquivOfFiber RS.toFiniteHypermap.node RS.vertOf
    (RS.vertOf_surjective_of_isCubic hcubic)
    (RS.toFiniteHypermap_node_sameCycle_iff hrotation)

/-- The associated hypermap has exactly the graph-theoretic Euler
characteristic already carried by the rotation system. -/
theorem finiteHypermap_eulerCharacteristic_eq
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS) :
    RS.toFiniteHypermap.eulerCharacteristic =
      (Fintype.card V : Int) - Fintype.card E +
        Fintype.card (OrbitFace RS) := by
  unfold FiniteHypermap.eulerCharacteristic
  rw [Fintype.card_congr (RS.finiteHypermapNodeOrbitEquiv hcubic hrotation),
    Fintype.card_congr RS.finiteHypermapEdgeOrbitEquiv]
  rfl

/-- A spherical cubic rotation system becomes an Euler-characteristic-two
finite hypermap without any additional planarity premise. -/
theorem finiteHypermap_eulerCharacteristic_eq_two
    (RS : RotationSystem V E) (hsphere : OrbitSphericalCubicMapData RS)
    (hrotation : VertexRotationCyclic RS) :
    RS.toFiniteHypermap.eulerCharacteristic = 2 := by
  rw [RS.finiteHypermap_eulerCharacteristic_eq hsphere.cubic hrotation]
  exact hsphere.euler

end RotationSystem

end Mettapedia.GraphTheory.FourColor

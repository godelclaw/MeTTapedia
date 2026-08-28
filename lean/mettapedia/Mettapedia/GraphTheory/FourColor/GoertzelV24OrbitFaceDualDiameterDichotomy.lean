import Mettapedia.GraphTheory.FourColor.GoertzelV24BoundedDegreePath
import Mettapedia.GraphTheory.FourColor.GoertzelV24DeletionComponents
import Mettapedia.GraphTheory.FourColor.GoertzelV24DualDiameterDichotomy
import Mettapedia.GraphTheory.FourColor.GoertzelV24FaceDualConnectedness

/-!
# The dual-diameter dichotomy for quotient faces

This file applies the bounded-degree Moore estimate to the full quotient
facial dual of a rotation system.  It is deliberately only a geometric
extraction theorem: it produces a long face or a long induced dual geodesic,
not a corridor or a repeated transfer profile.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OrbitFaceDualDiameterDichotomy

open GoertzelV24BoundedDegreePath
open GoertzelV24DualDiameterDichotomy
open GoertzelV24DeletionComponents
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24SeparatedGeodesicLocality

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-- The full simple facial dual of the quotient faces of a rotation system. -/
noncomputable abbrev fullOrbitFaceDual (RS : RotationSystem V E) :
    SimpleGraph (AmbientFace (Finset.univ : Finset (OrbitFace RS))) :=
  interiorDualGraph (orbitFaceBoundary RS)
    (Finset.univ : Finset (OrbitFace RS))

/-- **Bounded-face geodesic or a long face.**

For a connected cubic rotation system with cyclic vertex rotations, if the
number of quotient faces exceeds the Moore threshold, then either some face
has more than `B` distinct boundary edges or the full facial dual contains an
induced geodesic of at least `L` edges.

No corridor conclusion is included: exposing a pumpable primal strip from the
dual geodesic is a separate geometric theorem. -/
theorem exists_long_face_or_geodesic
    (RS : RotationSystem V E)
    (hcubic : RS.IsCubic)
    (hprimal : (rotationPrimalGraph RS).Connected)
    (hrotation : VertexRotationCyclic RS)
    (B L : ℕ)
    (hlarge : mooreBound B L < Fintype.card (OrbitFace RS)) :
    (∃ face : OrbitFace RS, B < (orbitFaceBoundary RS face).card) ∨
      ∃ start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS)),
        ∃ path : (fullOrbitFaceDual RS).Walk start finish,
          path.IsPath ∧
            path.length = (fullOrbitFaceDual RS).dist start finish ∧
            L ≤ path.length := by
  classical
  by_cases hface : ∀ face : OrbitFace RS,
      (orbitFaceBoundary RS face).card ≤ B
  · right
    have hconnected : (fullOrbitFaceDual RS).Connected :=
      orbitFaceInteriorDual_connected RS hcubic hprimal hrotation
    have hdegree : ∀ face, (fullOrbitFaceDual RS).degree face ≤ B := by
      intro face
      exact (interiorDualGraph_degree_le_faceBoundary_card
        (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS))
        (orbitFace_totalIncidenceCount_le_two RS) face).trans
          (hface face.1)
    let root : AmbientFace (Finset.univ : Finset (OrbitFace RS)) :=
      orbitFaceVertex RS RS.outer
    have hcard : mooreBound B L <
        Fintype.card (AmbientFace (Finset.univ : Finset (OrbitFace RS))) := by
      simpa using hlarge
    obtain ⟨finish, hdist⟩ :=
      exists_dist_ge_of_connected hconnected hdegree root hcard
    obtain ⟨path, hpath, hgeodesic⟩ :=
      hconnected.exists_path_of_dist root finish
    refine ⟨root, finish, path, hpath, hgeodesic, ?_⟩
    rwa [← hgeodesic] at hdist
  · left
    push Not at hface
    exact hface

/-- **Avoiding finitely many marked quotient faces.**

Under the bounded-face branch, deleting `S` leaves at most
`1 + |S| * (B - 1)` live components.  If the full dual is larger than the
corresponding Moore bound, one component contains a shortest path of at least
`L` edges.  The path is shortest in the deleted dual; no claim is made that it
is shortest before the marked faces are removed. -/
theorem exists_marked_face_avoiding_geodesic
    (RS : RotationSystem V E)
    (hcubic : RS.IsCubic)
    (hprimal : (rotationPrimalGraph RS).Connected)
    (hrotation : VertexRotationCyclic RS)
    (B L : ℕ) (hB : 1 ≤ B) (hL : 1 ≤ L)
    (hface : ∀ face : OrbitFace RS,
      (orbitFaceBoundary RS face).card ≤ B)
    (S : Finset (AmbientFace (Finset.univ : Finset (OrbitFace RS))))
    (hlarge : S.card + (1 + S.card * (B - 1)) * mooreBound B L <
      Fintype.card (OrbitFace RS)) :
    ∃ start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS)),
      start ∉ S ∧ finish ∉ S ∧
        ∃ path :
          (deleteFaces (fullOrbitFaceDual RS) (↑S : Set _)).Walk start finish,
          path.IsPath ∧
            path.length =
              (deleteFaces (fullOrbitFaceDual RS) (↑S : Set _)).dist start finish ∧
            L ≤ path.length := by
  classical
  have hconnected : (fullOrbitFaceDual RS).Connected :=
    orbitFaceInteriorDual_connected RS hcubic hprimal hrotation
  have hdegree : ∀ face, (fullOrbitFaceDual RS).degree face ≤ B := by
    intro face
    exact (interiorDualGraph_degree_le_faceBoundary_card
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))
      (orbitFace_totalIncidenceCount_le_two RS) face).trans
        (hface face.1)
  have hcard : S.card + (1 + S.card * (B - 1)) * mooreBound B L <
      Fintype.card (AmbientFace (Finset.univ : Finset (OrbitFace RS))) := by
    simpa using hlarge
  obtain ⟨start, finish, hstart, hfinish, hreach, hdist⟩ :=
    GoertzelV24DeletionComponents.exists_avoiding_geodesic
      hconnected hB hL hdegree S hcard
  obtain ⟨path, hpath, hgeodesic⟩ := hreach.exists_path_of_dist
  refine ⟨start, finish, hstart, hfinish, path, hpath, hgeodesic, ?_⟩
  rwa [← hgeodesic] at hdist

end GoertzelV24OrbitFaceDualDiameterDichotomy

end Mettapedia.GraphTheory.FourColor

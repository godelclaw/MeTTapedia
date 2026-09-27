import Mettapedia.GraphTheory.FourColor.ConnectedBipartitionGrowth
import Mettapedia.GraphTheory.FourColor.FaceDualNoCutVertex
import Mettapedia.GraphTheory.FourColor.FaceRegionCurvature
import Mettapedia.GSLT.Core.ProofRelevantPresentation

/-!
# Operational refinement of nested facial regions

The states are actual face subsets with both sides connected in the actual
facial dual. An event adds one original face, retaining its identity and an
attachment edge in the dual. Every nested pair of states admits a route of
these events. Its length is exactly the number of added faces.

Every state realizes as the literal retained-edge plane patch, with its
complete original mixed-vertex contour. Thus the route supplies geometric
face additions, including changes of contour width. It supplies neither a
bound on that width nor compatible colourings along the route.
-/

namespace Mettapedia.GraphTheory.FourColor.FaceRegionShelling

open GoertzelV24FaceOrbitIncidence GoertzelV24PrimalCycleFacialBond
open GoertzelV24TwoEdgeCutMinimality SimpleGraphDartRotation
open FaceRegionDegree EdgeShoreRotation PlanePatchCurvature
open Mettapedia.GSLT Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.ProofRelevantPresentation

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (data : Data G)

/-- A facial side together with connectedness of both shores. -/
structure Region where
  faces : Finset (OrbitFace data.toRotationSystem)
  inside : ((orbitFaceDualGraph data).induce (faces : Set _)).Connected
  outside : ((orbitFaceDualGraph data).induce (faces : Set _)ᶜ).Connected

variable {data}

@[ext] theorem Region.ext {S R : Region data} (h : S.faces = R.faces) : S = R := by
  cases S
  cases R
  cases h
  rfl

theorem Region.nonempty (S : Region data) : S.faces.Nonempty := by
  obtain ⟨f⟩ := S.inside.nonempty
  exact ⟨f.val, f.property⟩

theorem Region.ne_univ (S : Region data) : S.faces ≠ Finset.univ := by
  obtain ⟨f⟩ := S.outside.nonempty
  intro h
  have hf : f.val ∉ S.faces := f.property
  simp [h] at hf

/-- One adjacent original face is added; the endpoints certify both sides. -/
structure Event (S R : Region data) where
  face : OrbitFace data.toRotationSystem
  fresh : face ∉ S.faces
  target : R.faces = insert face S.faces
  attachment : ∃ a ∈ S.faces, (orbitFaceDualGraph data).Adj face a

theorem Event.subset {S R : Region data} (e : Event S R) : S.faces ⊆ R.faces := by
  rw [e.target]
  exact Finset.subset_insert _ _

theorem Event.card {S R : Region data} (e : Event S R) : R.faces.card = S.faces.card + 1 := by
  rw [e.target, Finset.card_insert_of_notMem e.fresh]

variable (data)

/-- The uncoloured operational theory of complete facial regions. -/
def theory : GSLT where
  Term := Region data
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun S R => Nonempty (Event S R)
  rewrites_resp_left := by
    intro S S' R equal event
    subst S'
    exact ⟨R, event, rfl⟩
  rewrites_resp_right := by
    intro S R R' event equal
    subst R'
    exact event

def presentation : StepPresentation (theory data) where
  Evidence := Event
  erases_iff := fun _ _ => Iff.rfl

variable (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)

include ambient

/-- A proper nested pair has a one-face successor still inside its target. -/
theorem exists_event_between (S R : Region data) (hSR : S.faces ⊂ R.faces) :
    ∃ T : Region data, Nonempty (Event S T) ∧ T.faces ⊆ R.faces := by
  obtain ⟨f, hfR, hfS, ha, hc, hcc⟩ := ConnectedBipartitionGrowth.exists_connected_insert
    (orbitFaceDualGraph data) (FaceDualNoCutVertex.delete_face_connected data ambient)
    S.inside S.outside R.inside R.outside (by exact_mod_cast hSR)
  let T : Region data := ⟨insert f S.faces,
    by rw [Finset.coe_insert]; exact hc,
    by rw [Finset.coe_insert]; exact hcc⟩
  exact ⟨T, ⟨⟨f, hfS, rfl, ha⟩⟩, Finset.insert_subset hfR hSR.subset⟩

/-- Every nested pair is connected by an authored route of face additions.
No intermediate patch or choice of face ordering is a hypothesis. -/
theorem exists_route (S R : Region data) (hSR : S.faces ⊆ R.faces) :
    Nonempty (Route (Event (data := data)) S R) := by
  classical
  generalize hn : R.faces.card - S.faces.card = n
  induction n using Nat.strong_induction_on generalizing S with
  | h n ih =>
    by_cases he : S.faces = R.faces
    · have hsame : S = R := Region.ext he
      subst R
      exact ⟨.refl S⟩
    · have hproper := Finset.ssubset_iff_subset_ne.mpr ⟨hSR, he⟩
      obtain ⟨T, ⟨e⟩, hTR⟩ := exists_event_between data ambient S R hproper
      have hlt : R.faces.card - T.faces.card < n := by
        have hc := e.card
        have hs := Finset.card_lt_card hproper
        omega
      obtain ⟨rest⟩ := ih (R.faces.card - T.faces.card) hlt T hTR rfl
      exact ⟨.cons e rest⟩

omit ambient
variable {data}

/-- Every route is monotone on the original face identifiers. -/
theorem route_subset {S R : Region data} (p : Route Event S R) : S.faces ⊆ R.faces := by
  induction p with
  | refl => exact Finset.Subset.refl _
  | cons e rest ih => exact e.subset.trans ih

/-- A geometric route has one step per added face, with no hidden moves. -/
theorem route_length {S R : Region data} (p : Route Event S R) :
    p.length + S.faces.card = R.faces.card := by
  induction p with
  | refl => simp [Route.length]
  | cons e rest ih =>
    have hc := e.card
    simp only [Route.length]
    omega

include ambient in
/-- Each operational state supplies an actual patch and its complete
boundary, not an assumed disk realization. -/
theorem Region.realizes (S : Region data) :
    ∃ outer : Dart data.toRotationSystem (edges data.toRotationSystem S.faces),
      dartOrbitFace data.toRotationSystem outer.val ∉ S.faces ∧
      Patch (toMap data.toRotationSystem (edges data.toRotationSystem S.faces) outer) ∧
      ∀ v : Vertex data.toRotationSystem (edges data.toRotationSystem S.faces),
        v ∈ boundaryVertices
          (toMap data.toRotationSystem (edges data.toRotationSystem S.faces) outer) ↔
          FaceDistanceFrontiers.Mixed (SphericalDistanceContours.vertexFaces data)
            (S.faces : Set _) v.val := by
  obtain ⟨f⟩ := S.outside.nonempty
  obtain ⟨outer, ho, _⟩ := FaceRegionConnectivity.exists_outer_dart data S.faces ambient
    S.nonempty ⟨f.val, f.property⟩
  exact ⟨outer, ho, FaceRegionPatch.patch data S.faces ambient outer ho S.inside S.outside,
    FaceRegionPatch.boundaryVertices_iff_mixed data S.faces ambient outer ho S.inside S.outside⟩

end
end Mettapedia.GraphTheory.FourColor.FaceRegionShelling

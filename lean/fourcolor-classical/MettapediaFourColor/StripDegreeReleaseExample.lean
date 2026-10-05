import MettapediaFourColor.StripDegreeRelease
import MettapediaFourColor.StripSixMixedExample

/-! # Degree-bounded release on an existing spherical source

The ambient degree five and one omitted core neighbour give exterior degree
at most four. The checked common corner supplies the local release theorem
for every exterior colouring in the stated joint branch, not only the saved
colouring. The existing source gluing reconstructs the whole sphere.
-/

namespace FourColor.StripDegreeReleaseExample

open SimpleGraph Color StripSixMixedExample
open Mettapedia.GraphTheory.FourColor.KempeChainCertificate

theorem exterior_degree : exterior.degree (port 2) ≤ 4 := by
  have bound := StripDegreeRelease.exterior_degree_lt reading.embedding (port 2)
    (sourceVertex 16) (by decide +kernel) (by decide +kernel)
  have ambient_degree : ambient.degree (reading.embedding (port 2)) = 5 := by
    rw [degree_eq]
    decide +kernel
  rw [ambient_degree] at bound
  omega

theorem common_corner : exterior.Adj (port 1) 20 ∧ exterior.Adj (port 2) 20 ∧
    (20 : Fin 33) ≠ port 3 := by decide +kernel

/-- Geometry supplies the release for every colouring in this branch. -/
theorem reconstructed (C : exterior.Coloring Color)
    (initial : ∀ i, C (port i) = StripSixConnection.input true i)
    (missing : ∀ v, exterior.Adj (port 1) v → C v ≠ c2)
    (K : (C.bicoloredSubgraph c0 c2).ConnectedComponent)
    (m2 : port 2 ∈ C.kempeComponentSet c0 c2 K)
    (m4 : port 4 ∈ C.kempeComponentSet c0 c2 K) :
    ∃ D : exterior.Coloring Color, ∃ h : History C D, h.length = 2 ∧
      ∃ whole : ambient.Coloring Color,
        ∀ v, whole (includeExterior v) = D v := by
  have injective : Function.Injective port := by
    intro i j h
    exact Fin.ext (congrArg (fun x : Fin 33 => x.val) h)
  obtain ⟨D,h,two,k,agree⟩ := StripDegreeRelease.repair C port injective port_edges
    initial exterior_degree 20 common_corner.1 common_corner.2.1 common_corner.2.2
    missing K m2 m4
  exact ⟨D,h,two,assemble D k agree⟩

theorem saved_reconstruction :
    ∃ D : exterior.Coloring Color, ∃ h : History (state 0) D, h.length = 2 ∧
      ∃ whole : ambient.Coloring Color,
        ∀ v, whole (includeExterior v) = D v :=
  reconstructed (state 0) initial_form missing_colour joint.component
    original_joint.2.2.2.1 original_joint.2.2.2.2.1

end FourColor.StripDegreeReleaseExample

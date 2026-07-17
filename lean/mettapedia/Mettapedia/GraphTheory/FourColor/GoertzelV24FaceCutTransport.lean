import Mettapedia.GraphTheory.FourColor.GoertzelV24FaceOrbitIncidence

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FaceCutTransport

open GoertzelV24FaceOrbitIncidence

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-- An exact face cut preserves its label when a dart's edge is outside the
cut. -/
theorem labels_eq_alpha_of_not_cut
    (RS : RotationSystem V E) {A : Type*}
    (labels : OrbitFace RS → A) (cut : E → Prop)
    (hexact : ∀ dart : RS.D,
      labels (dartOrbitFace RS dart) ≠
          labels (dartOrbitFace RS (RS.alpha dart)) ↔
        cut (RS.edgeOf dart))
    (dart : RS.D) (hnot : ¬cut (RS.edgeOf dart)) :
    labels (dartOrbitFace RS dart) =
      labels (dartOrbitFace RS (RS.alpha dart)) := by
  by_contra hne
  exact hnot ((hexact dart).1 hne)

/-- If a face arc starts by crossing a non-cut edge and then follows the
face permutation, its endpoint has the same cut label as its start. -/
theorem labels_eq_of_phi_iterate_alpha_eq_of_not_cut
    (RS : RotationSystem V E) {A : Type*}
    (labels : OrbitFace RS → A) (cut : E → Prop)
    (hexact : ∀ dart : RS.D,
      labels (dartOrbitFace RS dart) ≠
          labels (dartOrbitFace RS (RS.alpha dart)) ↔
        cut (RS.edgeOf dart))
    (start finish : RS.D) (steps : Nat)
    (hface : (RS.phi : RS.D → RS.D)^[steps] (RS.alpha start) = finish)
    (hnot : ¬cut (RS.edgeOf start)) :
    labels (dartOrbitFace RS start) =
      labels (dartOrbitFace RS finish) := by
  calc
    labels (dartOrbitFace RS start) =
        labels (dartOrbitFace RS (RS.alpha start)) :=
      labels_eq_alpha_of_not_cut RS labels cut hexact start hnot
    _ = labels (dartOrbitFace RS
          ((RS.phi : RS.D → RS.D)^[steps] (RS.alpha start))) :=
      congrArg labels
        (dartOrbitFace_phi_iterate_eq RS steps (RS.alpha start)).symm
    _ = labels (dartOrbitFace RS finish) := by rw [hface]

/-- At a vertex, one rotation step preserves the face-side label whenever
the rotated-from dart lies over an edge outside the exact cut. -/
theorem labels_eq_rho_of_not_cut
    (RS : RotationSystem V E) {A : Type*}
    (labels : OrbitFace RS → A) (cut : E → Prop)
    (hexact : ∀ dart : RS.D,
      labels (dartOrbitFace RS dart) ≠
          labels (dartOrbitFace RS (RS.alpha dart)) ↔
        cut (RS.edgeOf dart))
    (dart : RS.D) (hnot : ¬cut (RS.edgeOf dart)) :
    labels (dartOrbitFace RS dart) =
      labels (dartOrbitFace RS (RS.rho dart)) := by
  apply labels_eq_of_phi_iterate_alpha_eq_of_not_cut
    RS labels cut hexact dart (RS.rho dart) 1
  · change RS.phi (RS.alpha dart) = RS.rho dart
    rw [RotationSystem.phi_apply, RS.alpha_involutive]
  · exact hnot

/-- Two explicit face steps are the local form used by a cubic fusion
site. -/
theorem labels_eq_of_phi_sq_alpha_eq_of_not_cut
    (RS : RotationSystem V E) {A : Type*}
    (labels : OrbitFace RS → A) (cut : E → Prop)
    (hexact : ∀ dart : RS.D,
      labels (dartOrbitFace RS dart) ≠
          labels (dartOrbitFace RS (RS.alpha dart)) ↔
        cut (RS.edgeOf dart))
    (start finish : RS.D)
    (hface : RS.phi (RS.phi (RS.alpha start)) = finish)
    (hnot : ¬cut (RS.edgeOf start)) :
    labels (dartOrbitFace RS start) =
      labels (dartOrbitFace RS finish) := by
  apply labels_eq_of_phi_iterate_alpha_eq_of_not_cut
    RS labels cut hexact start finish 2
  · simpa [Function.iterate_succ_apply] using hface
  · exact hnot

end GoertzelV24FaceCutTransport

end Mettapedia.GraphTheory.FourColor

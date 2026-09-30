import Mettapedia.GraphTheory.FourColor.DualTruncateInverse
import Mettapedia.GraphTheory.FourColor.DualTruncateMapGeometry

/-!
# Geometry and colouring consumed after inverse recognition

The unmarked target hexagons become cubic source vertices. Exact dart
transport and the actual face equivalence recover Euler and connectivity.
The source has one third as many vertices as the target. This size decrease
does not change source vertex-colouring into a Tait-to-Tait reduction.

The recovered source's cut, simple-degree and noncomplete hypotheses remain
explicit in the structural colouring consumer; target coverage is separate.
-/

namespace Mettapedia.GraphTheory.FourColor.DualTruncateInverseGeometry

open DualTruncateInverse DualTruncateColoring
open GoertzelV24FaceOrbitIncidence GoertzelV24FaceDualConnectedness
open GoertzelV24OrbitFaceCurvatureBulk GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationEdgeBridge GoertzelV24TwoEdgeCutMinimality
open TubeSlab.VertexTransfer VertexCodeSourceGeometry SourceVertexCodeTrace
open VertexConstructionGSLT

noncomputable section
attribute [local instance] Classical.propDecidable

universe u
variable {W F : Type u} [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F]
  (T : RotationSystem.{u,u,u} W F) (d : Data T)
  (htwo : OrbitFacesTwoSided T)

/-- Unmarked faces of length six force source valence three. -/
theorem source_cubic
    (hhex : ∀ x : T.D, ¬d.marked (dartOrbitFace T x) → (T.faceOrbit x).card = 6) :
    (source T d htwo).IsCubic := by
  intro v
  obtain ⟨w, rfl⟩ := Quotient.exists_rep v
  have hm : ¬d.marked (dartOrbitFace T (d.frame.dart (w, 0))) := by
    rw [d.mark]
    change (0 : Fin 3) ≠ 2
    decide
  have hc := RotationSystemExactTransport.faceOrbit_card
    (rotation (source T d htwo)) T d.frame.dart
    (adapter_alpha T d htwo) (adapter_rho T d htwo) (w, 0)
  rw [DualTruncateFaceGeometry.faceOrbit_zero_card
    (source T d htwo) (source_rotationCyclic T d htwo)] at hc
  rw [hhex _ hm] at hc
  change 2 * ((source T d htwo).dartsAt (Quotient.mk _ w)).card = 6 at hc
  omega

/-- The recovered source's actual quotient-face Euler equals the target's. -/
theorem source_spherical
    (hhex : ∀ x : T.D, ¬d.marked (dartOrbitFace T x) → (T.faceOrbit x).card = 6)
    (hsphere : OrbitSphericalCubicMapData T) :
    OrbitSphericalCubicMapData (source T d htwo) where
  cubic := source_cubic T d htwo hhex
  euler := by
    let S := source T d htwo
    have hf := Fintype.card_congr (RotationSystemExactTransport.faceEquiv
      (rotation S) T d.frame.dart (adapter_alpha T d htwo) (adapter_rho T d htwo))
    have he : Fintype.card (Edge S) = Fintype.card F := by
      have hd : Fintype.card (rotation S).D = Fintype.card T.D :=
        Fintype.card_congr d.frame.dart
      have ha := (rotation S).card_darts_eq_twice_card_edges
      have hb := T.card_darts_eq_twice_card_edges
      rw [ha, hb] at hd
      omega
    calc
      (Fintype.card (SourceVertex T d) : ℤ) - Fintype.card (SourceEdge T d) +
          Fintype.card (OrbitFace S) =
          (Fintype.card W : ℤ) - Fintype.card (Edge S) +
            Fintype.card (OrbitFace (rotation S)) :=
        (DualTruncateFaceGeometry.euler_preserved S (source_cubic T d htwo hhex)
          (source_rotationCyclic T d htwo)).symm
      _ = 2 := by rw [he, hf]; exact hsphere.euler

/-- Source vertices are actual rotation orbits. Target paths descend through
alpha crossings; polygon edges descend through the source face permutation. -/
theorem source_connected (hconn : (rotationPrimalGraph T).Connected) :
    (rotationPrimalGraph (source T d htwo)).Connected := by
  let S := source T d htwo
  have hexp : (rotationPrimalGraph (rotation S)).Connected :=
    (RotationSystemExactTransport.primalIso (rotation S) T d.frame.dart
      (Equiv.refl W) (adapter_alpha T d htwo) (adapter_vertex T d htwo)).connected_iff.mpr
      hconn
  have hmap : ∀ ⦃x y : W⦄, (rotationPrimalGraph (rotation S)).Adj x y →
      S.vertOf x = S.vertOf y ∨ (rotationPrimalGraph S).Adj (S.vertOf x) (S.vertOf y) := by
    rintro x y ⟨⟨w, i⟩, rfl, rfl⟩
    fin_cases i
    · exact Or.inr ⟨w, rfl, rfl⟩
    · right
      change (rotationPrimalGraph S).Adj (S.vertOf w) (S.vertOf (S.phi w))
      exact ⟨w, rfl, (S.vert_phi_eq_vert_alpha w).symm⟩
    · right
      change (rotationPrimalGraph S).Adj (S.vertOf w) (S.vertOf (S.phi.symm w))
      have hadj : (rotationPrimalGraph S).Adj (S.vertOf (S.phi.symm w)) (S.vertOf w) :=
        ⟨S.phi.symm w, rfl, DualTruncateColoring.vert_alpha_phi_symm S w⟩
      exact hadj.symm
  refine { preconnected := ?_, nonempty := ⟨S.vertOf S.outer⟩ }
  intro x y
  obtain ⟨a, rfl⟩ := Quotient.exists_rep x
  obtain ⟨b, rfl⟩ := Quotient.exists_rep y
  exact reachable_map_of_adj_eq_or_adj S.vertOf hmap (hexp a b)

include htwo in
theorem source_size
    (hhex : ∀ x : T.D, ¬d.marked (dartOrbitFace T x) → (T.faceOrbit x).card = 6) :
    Fintype.card W = 3 * Fintype.card (SourceVertex T d) :=
  (source T d htwo).card_darts_eq_three_times_card_vertices
    (source_cubic T d htwo hhex)

include htwo in
/-- A genuine size decrease, with the source constraint still stated exactly. -/
theorem source_strictly_smaller
    (hhex : ∀ x : T.D, ¬d.marked (dartOrbitFace T x) → (T.faceOrbit x).card = 6) :
    Fintype.card (SourceVertex T d) < Fintype.card W := by
  have hs := source_size T d htwo hhex
  have hp : 0 < Fintype.card W := Fintype.card_pos_iff.mpr ⟨T.vertOf T.outer⟩
  omega

/-- The inverse adapter transports the reconstructed source witness into
an actual target edge colouring. -/
theorem tait (c : ThreeVertexColoring (source T d htwo)) :
    RotationSystemTaitColorable T :=
  DualTruncateConstructionGSLT.tait_relabelled (source T d htwo) T d.frame.dart
    (Equiv.refl W) (adapter_alpha T d htwo) (adapter_vertex T d htwo) c

theorem structural_tait
    (hregular : (rotationPrimalGraph (source T d htwo)).IsRegularOfDegree 3)
    (hcyclic : CyclicEdgeConnectivityAtLeast (rotationPrimalGraph (source T d htwo)) 4)
    (hconn : (rotationPrimalGraph T).Connected)
    (hnot : ¬∀ x y : SourceVertex T d, x ≠ y →
      (rotationPrimalGraph (source T d htwo)).Adj x y) :
    RotationSystemTaitColorable T := by
  obtain ⟨c⟩ := DualTruncateCyclicSource.source (source T d htwo) hregular hcyclic
    (source_connected T d htwo hconn) hnot
  exact tait T d htwo c

theorem every_complete_sweep (c : ThreeVertexColoring (source T d htwo))
    (order : List W) (hn : order.Nodup) (he : order ≠ [])
    (hcover : ∀ w, visited order w) :
    VertexConstructionGSLT.colouring.Supports
      (route (encodeClosed
        (RotationSystemExactTransport.cubic (rotation (source T d htwo)) T d.frame.dart
          (Equiv.refl W) (adapter_vertex T d htwo) (DualTruncateColoring.cubic _))
        (RotationSystemExactTransport.rotationCyclic (rotation (source T d htwo)) T d.frame.dart
          (Equiv.refl W) (adapter_vertex T d htwo) (adapter_rho T d htwo)
          (DualTruncateConstructionGSLT.rotationCyclic _)) order hn he hcover).trace)
      Fin.elim0 Fin.elim0 :=
  DualTruncateConstructionGSLT.supported_relabelled_route (source T d htwo) T d.frame.dart
    (Equiv.refl W) (adapter_alpha T d htwo) (adapter_vertex T d htwo)
    (adapter_rho T d htwo) c order hn he hcover

/-- Recognition starts with actual target faces. The frame and source are
constructed from their unique marked corners, with no earlier source input. -/
theorem recognized_source (hsphere : OrbitSphericalCubicMapData T)
    (hrotation : VertexRotationCyclic T)
    (c : DualTruncateFaceCoverFrame.Cover T)
    (hconn : (rotationPrimalGraph T).Connected)
    (hhex : ∀ x : T.D, ¬c.marked (dartOrbitFace T x) → (T.faceOrbit x).card = 6) :
    let d := DualTruncateInverse.fromCover T hsphere.cubic hrotation c
    OrbitSphericalCubicMapData (source T d htwo) ∧
      (rotationPrimalGraph (source T d htwo)).Connected ∧
      Fintype.card W = 3 * Fintype.card (SourceVertex T d) ∧
      Fintype.card (SourceVertex T d) < Fintype.card W := by
  let d := DualTruncateInverse.fromCover T hsphere.cubic hrotation c
  exact ⟨source_spherical T d htwo hhex hsphere, source_connected T d htwo hconn,
    source_size T d htwo hhex, source_strictly_smaller T d htwo hhex⟩

end
end Mettapedia.GraphTheory.FourColor.DualTruncateInverseGeometry

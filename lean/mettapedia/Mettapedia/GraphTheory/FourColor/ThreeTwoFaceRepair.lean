import Mettapedia.GraphTheory.FourColor.ThreeTwoFaceTransfer
import Mettapedia.GraphTheory.FourColor.ThreeContactKempeRepair
import Mettapedia.GraphTheory.FourColor.KempeChainCertificate

/-!
# Rebuilding colourings through a short facial pair

For the adjacent-contact pair exposing three edges and then two, every
proper original colouring can be revised by at most one physical Kempe
switch and then extended through both events. The witnesses preserve
the revised original assignment and agree on the intermediate patch.
-/

namespace Mettapedia.GraphTheory.FourColor.ThreeTwoFaceRepair

open GoertzelV24FaceOrbitIncidence GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation FaceRegionDegree EdgeShoreRotation
open FaceRegionShelling FaceRegionComplement PhysicalForkCodeCut
open FacePairColourExtension
open GoertzelV24ForkInterfaceSupport IncidenceKempeSwitch
open KempeChainCertificate Mettapedia.GSLT.Ultrainfinite

noncomputable section
attribute [local instance] Classical.propDecidable
set_option autoImplicit false

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (data : Data G)
variable (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)

include ambient

/-- The contact pattern supplies a reconstruction for every old witness.
The one-switch witness is on the actual old patch, and both subsequent
colourings use the original edge identities. -/
theorem extends_after_at_most_one_switch {S R T : Region data}
    (e : Event S R) (f : Event R T)
    (hn : (exposedEdges data e).card = 3) (hnT : (exposedEdges data f).card = 2)
    {u v w : V}
    (hu : u ∈ touched data.toRotationSystem (edges data.toRotationSystem S.faces))
    (hw : w ∈ touched data.toRotationSystem (edges data.toRotationSystem S.faces))
    {x y z : G.edgeSet} (hx : x ∈ exposedEdges data e)
    (hux : u ∈ data.toRotationSystem.endpoints x) (hvx : v ∈ data.toRotationSystem.endpoints x)
    (hy : y ∈ exposedEdges data f) (hwy : w ∈ data.toRotationSystem.endpoints y)
    (hz : z ∈ exposedEdges data f) (hvz : v ∈ data.toRotationSystem.endpoints z)
    (a : G.edgeSet → Fin 3)
    (ha : Proper data.toRotationSystem.endpoints (edges data.toRotationSystem S.faces) a) :
    let C := colouring data.toRotationSystem.endpoints (edges data.toRotationSystem S.faces) a ha
    ∃ D : (graph data.toRotationSystem.endpoints
        (edges data.toRotationSystem S.faces)).Coloring (Fin 3),
      (∃ history : History C D, history.length ≤ 1) ∧
      ∃ b c : G.edgeSet → Fin 3,
        Proper data.toRotationSystem.endpoints (edges data.toRotationSystem R.faces) b ∧
        (∀ x ∈ edges data.toRotationSystem S.faces, b x = D x) ∧
        Proper data.toRotationSystem.endpoints (edges data.toRotationSystem T.faces) c ∧
        (∀ x ∈ edges data.toRotationSystem R.faces, c x = b x) := by
  dsimp only
  let C := colouring data.toRotationSystem.endpoints (edges data.toRotationSystem S.faces) a ha
  obtain ⟨t, _, htu, htw, huw, criterion⟩ :=
    ThreeTwoFaceTransfer.exists_exact_criterion data ambient e f hn hnT
      hu hw hx hux hvx hy hwy hz hvz
  obtain ⟨r, s, q, hr, hs, hq, _⟩ := criterion C (proper _ _ C)
  obtain ⟨D, hswitch, r', s', q', hr', hs', hq', hgood⟩ :=
    exists_compatible_three_contacts C
      (fun x => (data.toRotationSystem.endpoints_card_two x).le)
      (Ne.symm htu) huw htw r s q hr hs hq
  obtain ⟨rd, sd, qd, hrd, hsd, hqd, hext⟩ := criterion D (proper _ _ D)
  have her : rd = r' := (hr' rd).mp ((hrd rd).mpr rfl)
  have hes : sd = s' := (hs' sd).mp ((hsd sd).mpr rfl)
  have heq : qd = q' := (hq' qd).mp ((hqd qd).mpr rfl)
  rw [her, hes, heq] at hext
  refine ⟨D, ?_, hext.mpr hgood⟩
  rcases hswitch with rfl | ⟨r, s, K, rfl⟩
  · exact ⟨.refl C, Nat.zero_le 1⟩
  · exact ⟨.cons (.switch C r s K) (.refl _), Nat.le_refl 1⟩

/-- The paired operation preserves existence of a colouring in both
directions, allowing reconstruction to revise the old witness. -/
theorem colourable_iff {S R T : Region data} (e : Event S R) (f : Event R T)
    (hn : (exposedEdges data e).card = 3) (hnT : (exposedEdges data f).card = 2)
    {u v w : V}
    (hu : u ∈ touched data.toRotationSystem (edges data.toRotationSystem S.faces))
    (hw : w ∈ touched data.toRotationSystem (edges data.toRotationSystem S.faces))
    {x y z : G.edgeSet} (hx : x ∈ exposedEdges data e)
    (hux : u ∈ data.toRotationSystem.endpoints x) (hvx : v ∈ data.toRotationSystem.endpoints x)
    (hy : y ∈ exposedEdges data f) (hwy : w ∈ data.toRotationSystem.endpoints y)
    (hz : z ∈ exposedEdges data f) (hvz : v ∈ data.toRotationSystem.endpoints z) :
    (∃ a : G.edgeSet → Fin 3,
      Proper data.toRotationSystem.endpoints (edges data.toRotationSystem S.faces) a) ↔
    (∃ c : G.edgeSet → Fin 3,
      Proper data.toRotationSystem.endpoints (edges data.toRotationSystem T.faces) c) := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨_, _, _, c, _, _, hc, _⟩ :=
      extends_after_at_most_one_switch data ambient e f hn hnT
        hu hw hx hux hvx hy hwy hz hvz a ha
    exact ⟨c, hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, proper_of_subset ((retained_subset data e).trans (retained_subset data f)) hc⟩

end
end Mettapedia.GraphTheory.FourColor.ThreeTwoFaceRepair

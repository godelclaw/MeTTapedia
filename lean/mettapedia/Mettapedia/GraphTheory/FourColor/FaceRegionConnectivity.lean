import Mettapedia.GraphTheory.FourColor.FaceRegionDegree

/-!
# A connected facial region constructs a connected spherical edge map

Walks in selected faces and across shared edges connect all touched vertices.
Together with literal edge restriction this derives connectedness, cyclic
vertex rotations and Euler characteristic two for the actual patch carrier.
It applies in particular to the deep face components of the distance-contour
construction. Simplicity and identification of its outer boundary remain
separate from this result.
-/

namespace Mettapedia.GraphTheory.FourColor.FaceRegionConnectivity

open GoertzelV24FaceOrbitIncidence GoertzelV24FaceDualConnectedness
open GoertzelV24PrimalCycleFacialBond GoertzelV24TwoEdgeCutMinimality
open PhysicalForkCodeEuler PhysicalForkCodeCut PhysicalForkCodeFaces
open FaceRegionDegree EdgeShoreRotation FaceDistanceFrontiers

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (RS : RotationSystem V E) (R : Finset (OrbitFace RS))

/-- Every retained face is a connected walk in the retained primal graph. -/
theorem face_reachable (d e : RS.D) (hd : dartOrbitFace RS d ∈ R)
    (he : RS.phi.SameCycle d e) :
    (shoreGraph RS (edges RS R)).Reachable (RS.vertOf d) (RS.vertOf e) := by
  obtain ⟨n, rfl⟩ := he.exists_nat_pow_eq
  clear he
  induction n with
  | zero => exact .refl _
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    apply ih.trans
    apply _root_.SimpleGraph.Adj.reachable
    refine ⟨(RS.phi ^ n) d, (edge_mem_iff RS R _).mpr (Or.inl ?_), rfl, ?_⟩
    · have hf : dartOrbitFace RS ((RS.phi ^ n) d) = dartOrbitFace RS d :=
        Quotient.sound ((Equiv.Perm.sameCycle_pow_right).mpr
          (Equiv.Perm.SameCycle.refl RS.phi d)).symm
      exact hf ▸ hd
    · exact (RS.vert_phi_eq_vert_alpha _).symm

theorem same_face_reachable (d e : RS.D) (hd : dartOrbitFace RS d ∈ R)
    (he : dartOrbitFace RS d = dartOrbitFace RS e) :
    (shoreGraph RS (edges RS R)).Reachable (RS.vertOf d) (RS.vertOf e) :=
  face_reachable RS R d e hd (Quotient.exact he)

/-- Crossing a shared edge connects any chosen occurrences on its two
selected faces. No assumption of unique shared edges is required. -/
theorem shared_edge_reachable {f g : OrbitFace RS} (hf : f ∈ R) (hg : g ∈ R)
    {edge : E} (he : edge ∈ orbitFaceBoundary RS f) (he' : edge ∈ orbitFaceBoundary RS g)
    (d e : RS.D) (hd : dartOrbitFace RS d = f) (heq : dartOrbitFace RS e = g) :
    (shoreGraph RS (edges RS R)).Reachable (RS.vertOf d) (RS.vertOf e) := by
  obtain ⟨a, ha, hae⟩ := (mem_orbitFaceBoundary_iff RS f edge).mp he
  obtain ⟨b, hb, hbe⟩ := (mem_orbitFaceBoundary_iff RS g edge).mp he'
  have haf := (mem_orbitFaceDarts_iff RS f a).mp ha
  have hbg := (mem_orbitFaceDarts_iff RS g b).mp hb
  apply (same_face_reachable RS R d a (hd ▸ hf) (hd.trans haf.symm)).trans
  have hab : (shoreGraph RS (edges RS R)).Reachable (RS.vertOf a) (RS.vertOf b) := by
    rcases RS.edge_fiber_two_cases hae hbe with rfl | rfl
    · exact .refl _
    · exact _root_.SimpleGraph.Adj.reachable
        ⟨a, (edge_mem_iff RS R a).mpr (Or.inl (haf ▸ hf)), rfl, rfl⟩
  exact hab.trans (same_face_reachable RS R b e (hbg ▸ hg) (hbg.trans heq.symm))

section Graph

open SimpleGraphDartRotation
variable {G : _root_.SimpleGraph V} [DecidableRel G.Adj]
variable (data : Data G) (F : Finset (OrbitFace data.toRotationSystem))

/-- Connectivity of the selected facial dual supplies connectivity of
the entire retained primal edge set, not merely a chosen set of columns. -/
theorem shore_connected
    (hF : ((orbitFaceDualGraph data).induce (F : Set _)).Connected) :
    ShoreConnected data.toRotationSystem (edges data.toRotationSystem F) := by
  have liftWalk {f g : {f // f ∈ F}}
      (p : ((orbitFaceDualGraph data).induce (F : Set _)).Walk f g) :
      ∀ d e : data.toRotationSystem.D,
        dartOrbitFace data.toRotationSystem d = f.val →
        dartOrbitFace data.toRotationSystem e = g.val →
        (shoreGraph data.toRotationSystem (edges data.toRotationSystem F)).Reachable
          (data.toRotationSystem.vertOf d) (data.toRotationSystem.vertOf e) := by
    induction p with
    | @nil f =>
      intro d e hd he
      exact same_face_reachable _ _ d e (hd ▸ f.property) (hd.trans he.symm)
    | @cons f g h hadj p ih =>
      intro d e hd he
      obtain ⟨m, hm⟩ := exists_dartOrbitFace_eq data.toRotationSystem g.val
      obtain ⟨_, edge, _, hef, heg⟩ := hadj
      exact (shared_edge_reachable _ _ f.property g.property hef heg d m hd hm).trans
        (ih m e hm he)
  intro u v hu hv
  obtain ⟨d, hd, hdf⟩ := (touched_iff _ _ u).mp hu
  obtain ⟨e, he, hef⟩ := (touched_iff _ _ v).mp hv
  obtain ⟨p⟩ := hF ⟨_, hdf⟩ ⟨_, hef⟩
  rw [← hd, ← he]
  exact liftWalk p d e rfl rfl

/-- The source class gives the actual retained map its spherical Euler
equation and local cyclic rotations. Cubicity of this patch is not claimed. -/
theorem retained_geometry
    (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
    (hF : ((orbitFaceDualGraph data).induce (F : Set _)).Connected)
    (outer : Dart data.toRotationSystem (edges data.toRotationSystem F)) :
    (rotationPrimalGraph (toMap data.toRotationSystem (edges data.toRotationSystem F) outer)).Connected ∧
      VertexRotationCyclic (toMap data.toRotationSystem (edges data.toRotationSystem F) outer) ∧
      ((Fintype.card (Vertex data.toRotationSystem (edges data.toRotationSystem F)) : ℤ) -
        Fintype.card (edges data.toRotationSystem F) +
        Fintype.card (OrbitFace (toMap data.toRotationSystem (edges data.toRotationSystem F) outer)) = 2) ∧
      ∀ v, ((toMap data.toRotationSystem (edges data.toRotationSystem F) outer).dartsAt v).card = 2 ∨
        ((toMap data.toRotationSystem (edges data.toRotationSystem F) outer).dartsAt v).card = 3 := by
  have hc := shore_connected data F hF
  exact ⟨connected outer hc, rotationCyclic outer ambient.vertexRotationCyclic,
    euler outer ambient.spherical ambient.primalConnected ambient.vertexRotationCyclic hc,
    degree_two_or_three (cubic3_of _ ambient.spherical.cubic ambient.vertexRotationCyclic) outer⟩

/-- A nonempty proper face region has an actual boundary dart with the
unselected face on its own side. This chooses the outer side of the patch. -/
theorem exists_outer_dart
    (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
    (hne : F.Nonempty) (hproper : ∃ f, f ∉ F) :
    ∃ d : Dart data.toRotationSystem (edges data.toRotationSystem F),
      dartOrbitFace data.toRotationSystem d.val ∉ F ∧
      dartOrbitFace data.toRotationSystem (data.toRotationSystem.alpha d.val) ∈ F := by
  obtain ⟨f, hf⟩ := hne
  obtain ⟨g, hg⟩ := hproper
  obtain ⟨p⟩ := orbitFaceDualGraph_connected data ambient f g
  obtain ⟨c, _, hc, hc'⟩ := p.exists_boundary_dart (F : Set _) hf hg
  obtain ⟨_, edge, _, he, he'⟩ := c.adj
  obtain ⟨a, ha, hae⟩ := (mem_orbitFaceBoundary_iff _ _ edge).mp he
  obtain ⟨b, hb, hbe⟩ := (mem_orbitFaceBoundary_iff _ _ edge).mp he'
  have haf := (mem_orbitFaceDarts_iff _ _ a).mp ha
  have hbg := (mem_orbitFaceDarts_iff _ _ b).mp hb
  have hfa : dartOrbitFace data.toRotationSystem a ∈ F := haf ▸ hc
  have hfb : dartOrbitFace data.toRotationSystem b ∉ F := hbg ▸ hc'
  have hab : b = data.toRotationSystem.alpha a := by
    rcases data.toRotationSystem.edge_fiber_two_cases hae hbe with heq | heq
    · exact (hfb (heq ▸ hfa)).elim
    · exact heq
  have hba : dartOrbitFace data.toRotationSystem (data.toRotationSystem.alpha b) ∈ F := by
    rw [hab, data.toRotationSystem.alpha_involutive]
    exact hfa
  exact ⟨⟨b, (edge_mem_iff _ _ b).mpr (Or.inr hba)⟩, hfb, hba⟩

/-- The distance-region constructor supplies both a connected retained
map and an exterior-oriented boundary dart, without an extra cap supplier. -/
theorem deep_region_map
    (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
    (root far : OrbitFace data.toRotationSystem) (depth : ℕ)
    (hdepth : depth < (orbitFaceDualGraph data).dist root far) :
    let F := Finset.univ.filter fun f => f ∈ deepRegion (orbitFaceDualGraph data) root far depth
    ∃ outer : Dart data.toRotationSystem (edges data.toRotationSystem F),
      dartOrbitFace data.toRotationSystem outer.val ∉ F ∧
      ShoreConnected data.toRotationSystem (edges data.toRotationSystem F) := by
  let F := Finset.univ.filter fun f => f ∈ deepRegion (orbitFaceDualGraph data) root far depth
  have hF : (F : Set _) = deepRegion (orbitFaceDualGraph data) root far depth := by
    ext f
    simp [F]
  have hconn : ((orbitFaceDualGraph data).induce (F : Set _)).Connected := by
    rw [hF]
    exact deepRegion_connected _ root far depth hdepth
  have hne : F.Nonempty := ⟨far, by
    change far ∈ (F : Set _)
    rw [hF]
    exact far_mem _ root far hdepth⟩
  have hproper : ∃ f, f ∉ F := by
    refine ⟨root, ?_⟩
    intro h
    have hm : root ∈ deepRegion (orbitFaceDualGraph data) root far depth := hF ▸ h
    have hh := dist_gt_of_mem _ root far hm
    simp at hh
  obtain ⟨outer, ho, _⟩ := exists_outer_dart data F ambient hne hproper
  exact ⟨outer, ho, shore_connected data F hconn⟩

end Graph
end
end Mettapedia.GraphTheory.FourColor.FaceRegionConnectivity

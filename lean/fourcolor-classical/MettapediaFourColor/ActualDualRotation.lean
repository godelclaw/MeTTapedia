import MettapediaFourColor.ExceptionalCoreCollision
import Mettapedia.GraphTheory.FourColor.GoertzelV24DualRotationSystem
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationSystemPrimalGraphBacking
import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFaces
import Mettapedia.GraphTheory.FourColor.GoertzelV24PrimalCycleFacialBond

/-!
# The simple facial dual with its actual rotation

The existing dual rotation keeps the primal darts and exchanges vertex and
face permutations. Unique shared primal edges make its simple-graph backing
faithful. The adjacency bridge identifies this graph with the full facial
dual used by the coverage layer. Cubic primal rotations yield triangular
dual faces through the same dart equivalence.
-/

namespace FourColor.ActualDualRotation

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open GoertzelV24FaceDualConnectedness GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceTwoSided GoertzelV24RotationSystemPrimalGraphBacking
open ExceptionalCoreOrientation ExceptionalOverlap

noncomputable section

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  (RS : RotationSystem V E) (two : OrbitFacesTwoSided RS)

abbrev dual := GoertzelV24DualRotationSystem.rotationSystem RS two

theorem mem_dual_endpoints (e : E) (f : OrbitFace RS) :
    f ∈ (dual RS two).endpoints e ↔ e ∈ orbitFaceBoundary RS f := by
  rw [RotationSystem.mem_endpoints_iff, mem_orbitFaceBoundary_iff]
  constructor
  · rintro ⟨d, hd, hf⟩
    exact ⟨d, (mem_orbitFaceDarts_iff RS f d).mpr hf,
      (dual RS two).mem_dartsOn.mp hd⟩
  · rintro ⟨d, hf, hd⟩
    exact ⟨d, (dual RS two).mem_dartsOn.mpr hd,
      (mem_orbitFaceDarts_iff RS f d).mp hf⟩

theorem shared_of_boundaries {a b : OrbitFace RS} (ne : a ≠ b) {e : E}
    (ha : e ∈ orbitFaceBoundary RS a) (hb : e ∈ orbitFaceBoundary RS b) :
    e ∈ sharedInteriorEdges (orbitFaceBoundary RS) Finset.univ a b := by
  apply (mem_sharedInteriorEdges_iff _ _).mpr
  refine ⟨?_, ha, hb⟩
  apply (mem_interiorEdgeSupport_iff _ _).mpr
  refine ⟨Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, ha⟩, ?_⟩
  exact totalIncidenceCount_eq_two_of_mem_faceBoundary_of_mem_faceBoundary_of_ne
    (orbitFaceBoundary RS) Finset.univ (orbitFace_incidence_le_two RS)
      (Finset.mem_univ a) (Finset.mem_univ b) ne ha hb

theorem dual_endpoints_injective
    (unique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS) Finset.univ) :
    Function.Injective (dual RS two).endpoints := by
  intro e f eq
  obtain ⟨d, hd⟩ := (dual RS two).dartsOn_nonempty e
  let a := dartOrbitFace RS d
  let b := dartOrbitFace RS (RS.alpha d)
  have ends := (dual RS two).endpoints_eq_pair_of_mem hd
  have hea : a ∈ (dual RS two).endpoints e := by
    rw [ends]; exact Finset.mem_insert_self _ _
  have heb : b ∈ (dual RS two).endpoints e := by
    rw [ends]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hfa : a ∈ (dual RS two).endpoints f := eq ▸ hea
  have hfb : b ∈ (dual RS two).endpoints f := eq ▸ heb
  apply Finset.card_le_one.mp (unique a (Finset.mem_univ _) b (Finset.mem_univ _) (two d))
  · exact shared_of_boundaries RS (two d)
      ((mem_dual_endpoints RS two e a).mp hea) ((mem_dual_endpoints RS two e b).mp heb)
  · exact shared_of_boundaries RS (two d)
      ((mem_dual_endpoints RS two f a).mp hfa) ((mem_dual_endpoints RS two f b).mp hfb)

/-- Equality of adjacency retains actual source darts in the reverse direction. -/
theorem dual_adj_iff {a b : OrbitFace RS} :
    (rotationPrimalGraph (dual RS two)).Adj a b ↔
      (interiorDualGraph (orbitFaceBoundary RS) Finset.univ).Adj
        ⟨a, Finset.mem_univ _⟩ ⟨b, Finset.mem_univ _⟩ := by
  constructor
  · rintro ⟨d, rfl, rfl⟩
    exact interiorDualGraph_adj_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
      _ _ (orbitFace_incidence_le_two RS) (two d)
      (edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS d)
      (by
        change RS.edgeOf d ∈ orbitFaceBoundary RS (dartOrbitFace RS (RS.alpha d))
        rw [← RS.edge_alpha d]
        exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS (RS.alpha d))
  · rintro ⟨ne, e, _, ha, hb⟩
    obtain ⟨d, hd, hde⟩ := (mem_orbitFaceBoundary_iff RS a e).mp ha
    obtain ⟨f, hf, hfe⟩ := (mem_orbitFaceBoundary_iff RS b e).mp hb
    have da := (mem_orbitFaceDarts_iff RS a d).mp hd
    have fb := (mem_orbitFaceDarts_iff RS b f).mp hf
    rcases RS.edge_fiber_two_cases hde hfe with eq | eq
    · exact (ne (da.symm.trans (eq ▸ fb))).elim
    · exact ⟨d, da, eq ▸ fb⟩

variable (unique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS) Finset.univ)

abbrev graph := rotationPrimalGraph (dual RS two)

def data : Data (graph RS two) :=
  graphData (dual RS two) (dual_endpoints_injective RS two unique)

abbrev darts : RS.D ≃ (graph RS two).Dart :=
  primalDartEquiv (dual RS two) (dual_endpoints_injective RS two unique)

@[simp] theorem darts_fst (d : RS.D) : (darts RS two unique d).fst = dartOrbitFace RS d := rfl
@[simp] theorem darts_snd (d : RS.D) :
    (darts RS two unique d).snd = dartOrbitFace RS (RS.alpha d) := rfl

theorem data_step (d : RS.D) :
    (data RS two unique).vertexRotation (darts RS two unique d) =
      darts RS two unique (RS.phi d) :=
  (primalDartEquiv_rho (dual RS two) _ d).symm

theorem data_face_step (d : RS.D) :
    (data RS two unique).vertexRotation (darts RS two unique d).symm =
      darts RS two unique (RS.rho d) := by
  exact (primalDartEquiv_phi (dual RS two) _ d).symm.trans
    (congrArg (darts RS two unique)
      (GoertzelV24DualRotationSystem.rotationSystem_phi RS two d))

/-- The face orbit becomes a single actual dual vertex-rotation cycle. -/
theorem cyclic : (data RS two unique).IsVertexwiseCyclic := by
  let : Fintype (graph RS two).Dart := Fintype.ofEquiv RS.D (darts RS two unique)
  intro v
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro d hd
    exact ((data RS two unique).vertexRotation_fst d).trans hd
  · exact (data RS two unique).vertexRotation.injective.injOn
  · intro d hd
    refine ⟨(data RS two unique).vertexRotation.symm d, ?_,
      (data RS two unique).vertexRotation.apply_symm_apply d⟩
    have h := (data RS two unique).vertexRotation_fst
      ((data RS two unique).vertexRotation.symm d)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm.trans hd
  · intro x hx y hy
    obtain ⟨x, rfl⟩ := (darts RS two unique).surjective x
    obtain ⟨y, rfl⟩ := (darts RS two unique).surjective y
    exact (GoertzelV24OrderedCutFaceReturnProfile.permCongr_sameCycle_iff
      (darts RS two unique) RS.phi x y).mpr (Quotient.exact (hx.trans hy.symm))

/-- Cubicity and the actual primal rotation prove dual triangular closure. -/
theorem triangular (cubic : RS.IsCubic) (cyclic : VertexRotationCyclic RS) :
    Triangular (data RS two unique) := by
  intro d
  obtain ⟨d, rfl⟩ := (darts RS two unique).surjective d
  rw [data_face_step, data_face_step, data_face_step]
  rw [(PhysicalForkCodeFaces.cubic3_of RS cubic cyclic).cube]

/-- The triangle around a primal vertex is a dual facial triangle. -/
theorem corner_at_vertex (cubic : RS.IsCubic) (cyclic : VertexRotationCyclic RS)
    (d : RS.D) :
    Corner (data RS two unique) (dartOrbitFace RS d)
      (dartOrbitFace RS (RS.rho (RS.rho d))) (dartOrbitFace RS (RS.rho d)) := by
  let u := darts RS two unique (RS.alpha (RS.rho (RS.rho d)))
  let v := darts RS two unique d
  have hf : u.fst = dartOrbitFace RS d := by
    change dartOrbitFace RS (RS.alpha (RS.rho (RS.rho d))) = _
    rw [dartOrbitFace_alpha_eq_dartOrbitFace_rho,
      (PhysicalForkCodeFaces.cubic3_of RS cubic cyclic).cube]
  have hs : u.snd = dartOrbitFace RS (RS.rho (RS.rho d)) := by
    exact congrArg (dartOrbitFace RS) (RS.alpha_involutive _)
  have vf : v.fst = dartOrbitFace RS d := rfl
  have vs : v.snd = dartOrbitFace RS (RS.rho d) :=
    dartOrbitFace_alpha_eq_dartOrbitFace_rho RS d
  have hu : (data RS two unique).vertexRotation u = v := by
    rw [data_step]
    change darts RS two unique (RS.rho (RS.alpha (RS.alpha (RS.rho (RS.rho d))))) = _
    rw [RS.alpha_involutive, (PhysicalForkCodeFaces.cubic3_of RS cubic cyclic).cube]
  have ua : (graph RS two).Adj (dartOrbitFace RS d)
      (dartOrbitFace RS (RS.rho (RS.rho d))) := by simpa only [hf, hs] using u.adj
  have va : (graph RS two).Adj (dartOrbitFace RS d)
      (dartOrbitFace RS (RS.rho d)) := by simpa only [vf, vs] using v.adj
  refine ⟨ua, va, ?_⟩
  have eu : (⟨(_, _), ua⟩ : (graph RS two).Dart) = u := by
    apply SimpleGraph.Dart.ext; exact Prod.ext hf.symm hs.symm
  have ev : (⟨(_, _), va⟩ : (graph RS two).Dart) = v := by
    apply SimpleGraph.Dart.ext; exact Prod.ext vf.symm vs.symm
  exact (congrArg (data RS two unique).vertexRotation eu).trans (hu.trans ev.symm)

/-- Every face on an edge incident with a cubic vertex is one of its three
actual cyclic face readings. This includes both sides of that edge. -/
theorem face_mem_vertex_triangle (cubic : PhysicalForkCodeFaces.Cubic3 RS)
    (d : RS.D) {e : E} {f : OrbitFace RS}
    (incident : RS.vertOf d ∈ RS.endpoints e)
    (boundary : e ∈ orbitFaceBoundary RS f) :
    f ∈ ({dartOrbitFace RS d, dartOrbitFace RS (RS.rho d),
      dartOrbitFace RS (RS.rho (RS.rho d))} : Finset (OrbitFace RS)) := by
  obtain ⟨i, hi, hv⟩ := (RS.mem_endpoints_iff).mp incident
  obtain ⟨t, ht, he⟩ := (mem_orbitFaceBoundary_iff RS f e).mp boundary
  have hf := (mem_orbitFaceDarts_iff RS f t).mp ht
  rcases RS.edge_fiber_two_cases (RS.mem_dartsOn.mp hi) he with eq | eq
  · subst t
    rcases cubic.fiber d i hv with rfl | rfl | rfl
    all_goals rw [← hf]; simp
  · subst t
    rw [dartOrbitFace_alpha_eq_dartOrbitFace_rho] at hf
    rcases cubic.fiber d i hv with rfl | rfl | rfl
    all_goals rw [← hf]; simp [cubic.cube]

/-- Relabelling the three distinct vertices of a facial triangle preserves
one of its two possible orientations. -/
theorem corner_of_three_members {W : Type*} [DecidableEq W]
    {H : SimpleGraph W} [H.LocallyFinite] (rotation : Data H)
    (tri : Triangular rotation) {x y z a b c : W}
    (h : Corner rotation x y z)
    (ha : a ∈ ({x, y, z} : Finset W)) (hb : b ∈ ({x, y, z} : Finset W))
    (hc : c ∈ ({x, y, z} : Finset W))
    (ab : a ≠ b) (bc : b ≠ c) (ca : c ≠ a) :
    Corner rotation a b c ∨ Corner rotation a c b := by
  have h' := Corner.rotate rotation tri h
  have h'' := Corner.rotate rotation tri h'
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hc
  rcases ha with rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl
  all_goals first
    | exact (ab rfl).elim
    | exact (bc rfl).elim
    | exact (ca rfl).elim
    | exact Or.inl h
    | exact Or.inr h
    | exact Or.inl h'
    | exact Or.inr h'
    | exact Or.inl h''
    | exact Or.inr h''

end
end FourColor.ActualDualRotation

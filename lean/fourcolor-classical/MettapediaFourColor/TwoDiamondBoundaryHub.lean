import MettapediaFourColor.TwoDiamondCycleReplacement
import MettapediaFourColor.SourceTaitInverse
import Mettapedia.GraphTheory.FourColor.OpenTangleBoundaryHub

/-!
# The ordered hub for an arbitrary diamond exterior

The twenty-vertex disk is capped by one eight-valent boundary vertex for
reference Kempe semantics. The cap preserves spherical geometry and literal
exterior cofaciality, including when the exterior is disconnected. It is not
the smaller cubic map used by induction; that map is the eight-cycle.
-/

namespace FourColor.TwoDiamondBoundaryHub

open Mettapedia.GraphTheory.FourColor
open GoertzelV24OpenTangleComposition GoertzelV24CompositeSeamCubic
open GoertzelV24CompositeSeamMultigraph OpenTangleVertexReflection
open GoertzelV24TwoEdgeCutMinimality GoertzelV24FaceDualConnectedness
open GoertzelV24OrbitFaceTwoSided GoertzelV24FaceOrbitIncidence
open OpenTangleReplacementEuler OpenTangleRewireFaces
open TwoDiamondCycleReplacement

noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u
variable {V I B : Type u} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I] [Fintype B] [DecidableEq B]
  (outside : OpenTangleData V I B) (seam : B ≃ Fin 8)

abbrev cap := OpenTangleBoundaryHub.hub 8
abbrev capped := outside.composeRotationSystem cap seam

theorem same_return : OpenTanglePortReplacement.returnCode TwoDiamondTangle.piece =
    OpenTanglePortReplacement.returnCode cap :=
  TwoDiamondTangle.piece_returnCode.trans (OpenTangleBoundaryHub.boundary_return 8).symm

theorem euler
    (h : BridgelessSphericalCubicMapData (original outside seam)) :
    compositeEuler outside cap seam = 2 := by
  have he := (OpenTanglePortReplacement.euler_eq_iff_mass _ _ same_return outside seam).mpr
    (TwoDiamondTangle.piece_eulerMass.trans
      (OpenTangleBoundaryHub.euler_mass 8 (by decide)).symm)
  rw [← he]
  exact h.spherical.euler

theorem structural
    (h : BridgelessSphericalCubicMapData (original outside seam)) :
    (rotationPrimalGraph (capped outside seam)).Connected ∧
      GoertzelV24RotationEdgeBridge.EdgeBridgeFree (capped outside seam) :=
  (OpenTangleInternalReplacement.replacement_structural outside
    TwoDiamondTangle.piece cap seam seam
    ⟨TwoDiamondTangle.piece_connected, TwoDiamondTangle.piece_bridgeless⟩
    (OpenTangleBoundaryHub.connected_bridgeless 8)).mp
      ⟨h.primalConnected, h.edgeBridgeFree⟩

theorem rotation_cyclic
    (h : BridgelessSphericalCubicMapData (original outside seam)) :
    VertexRotationCyclic (capped outside seam) :=
  vertexRotationCyclic_composeRotationSystem outside cap seam
    (exterior_rotationCyclic outside _ seam h.vertexRotationCyclic)
    (OpenTangleBoundaryHub.rotation_cyclic 8 (by decide))

theorem vertex_covered
    (h : BridgelessSphericalCubicMapData (original outside seam)) :
    Function.Surjective (capped outside seam).vertOf := by
  rintro (v | v)
  · have hc := exterior_isCubic outside _ seam h.spherical.cubic v
    obtain ⟨d, hd⟩ := Finset.card_pos.mp (show 0 < (openDartsAt outside v).card by omega)
    refine ⟨composeDartEquiv (.inl d), ?_⟩
    change (outside.composeData cap seam).vertOf (composeDartEquiv (.inl d)) = _
    rw [OpenTangleData.composeData_vertOf_composeDartEquiv]
    exact congrArg Sum.inl (Finset.mem_filter.mp hd).2
  · exact ⟨composeDartEquiv (.inr (.inr 0)), congrArg Sum.inr (Subsingleton.elim _ _)⟩

theorem planar
    (h : BridgelessSphericalCubicMapData (original outside seam)) :
    (SourceConstruction.sourceMap (capped outside seam)).Planar :=
  SourceConstruction.sourceMap_planar_of_vertexCovered
    (vertex_covered outside seam h) (rotation_cyclic outside seam h)
    (structural outside seam h).1 (euler outside seam h)

/-- The port-return record preserves all literal exterior cofaciality. -/
theorem exterior_faces (a b : I ⊕ B) :
    (original outside seam).phi.SameCycle
      (composeDartEquiv (.inl a)) (composeDartEquiv (.inl b)) ↔
    (capped outside seam).phi.SameCycle
      (composeDartEquiv (.inl a)) (composeDartEquiv (.inl b)) :=
  OpenTanglePortReplacement.exterior_sameCycle_iff _ _ same_return outside seam a b

theorem rho_left (d : I ⊕ B) :
    (capped outside seam).rho (composeDartEquiv (.inl d)) =
      composeDartEquiv (.inl (outside.rho d)) := by
  change (outside.composeData cap seam).rho _ = _
  rw [OpenTangleData.composeData_rho_apply]
  simp

theorem original_rho_left (d : I ⊕ B) :
    (original outside seam).rho (composeDartEquiv (.inl d)) =
      composeDartEquiv (.inl (outside.rho d)) := by
  change (outside.composeData TwoDiamondTangle.piece seam).rho _ = _
  rw [OpenTangleData.composeData_rho_apply]
  simp

/-- Every cap edge has an exterior end. The exact face-return record therefore
transfers two-sidedness without asserting global cubicity of the cap. -/
theorem two_sided
    (h : BridgelessSphericalCubicMapData (original outside seam)) :
    OrbitFacesTwoSided (capped outside seam) := by
  have ht := GoertzelV24BridgelessFaceTwoSided.BridgelessSphericalCubicMapData.orbitFacesTwoSided
    (original outside seam) h
  have left (d : I ⊕ B) :
      dartOrbitFace (capped outside seam) (composeDartEquiv (.inl d)) ≠
      dartOrbitFace (capped outside seam)
        ((capped outside seam).alpha (composeDartEquiv (.inl d))) := by
    intro he
    have hs := (Quotient.exact he).apply_right
    simp only [RotationSystem.phi_apply, RotationSystem.alpha_involutive,
      rho_left] at hs
    have ho := (exterior_faces outside seam d (outside.rho d)).mpr hs
    rw [← original_rho_left] at ho
    apply ht (composeDartEquiv (.inl d))
    apply Quotient.sound
    have step : (original outside seam).phi.SameCycle
        ((original outside seam).alpha (composeDartEquiv (.inl d)))
        ((original outside seam).rho (composeDartEquiv (.inl d))) := by
      simpa only [RotationSystem.phi_apply, RotationSystem.alpha_involutive] using
        (Equiv.Perm.SameCycle.refl (original outside seam).phi
          ((original outside seam).alpha (composeDartEquiv (.inl d)))).apply_right
    exact ho.trans step.symm
  intro d
  obtain ⟨(d | (e | i)), rfl⟩ := composeDartEquiv.surjective d
  · exact left d
  · exact nomatch e
  · intro he
    apply left (.inr (seam.symm i))
    have hf := congrArg (dartOrbitFace (capped outside seam))
      ((capped outside seam).alpha_involutive (composeDartEquiv (.inr (.inr i))))
    change dartOrbitFace (capped outside seam) (composeDartEquiv (.inr (.inr i))) =
      dartOrbitFace (capped outside seam) (composeDartEquiv (.inl (.inr (seam.symm i)))) at he
    exact he.symm.trans hf.symm

/-- The ordered boundary is the complete node of the new hub. -/
def ring : List (capped outside seam).D :=
  List.ofFn (fun i : Fin 8 => composeDartEquiv (.inr (.inr i)))

@[simp] theorem mirror_node (d : (capped outside seam).D) :
    (SourceConstruction.sourceMap (capped outside seam)).mirror.node d =
      (capped outside seam).rho d := by
  change (((capped outside seam).rho⁻¹)⁻¹) d = _
  rw [inv_inv]

@[simp] theorem rho_hub (i : Fin 8) :
    (capped outside seam).rho (.inr (.inr i)) =
      .inr (.inr (finRotate 8 i)) := by
  change (outside.composeData cap seam).rho _ = _
  rw [OpenTangleData.composeData_rho_apply]
  simp

theorem outside_three
    (h : BridgelessSphericalCubicMapData (original outside seam)) (d : I ⊕ B) :
    outside.rho (outside.rho (outside.rho d)) = d := by
  have ht := SourceConstruction.rho_three h.spherical.cubic h.vertexRotationCyclic
    (composeDartEquiv (.inl d))
  simp only [original_rho_left] at ht
  exact Sum.inl.inj (composeDartEquiv.injective ht)

private theorem outside_ne
    (h : BridgelessSphericalCubicMapData (original outside seam)) (d : I ⊕ B) :
    outside.rho d ≠ d := by
  intro he
  apply VertexCodeCyclicEncoder.rot_ne h.spherical.cubic h.vertexRotationCyclic
    (⟨composeDartEquiv (.inl d), rfl⟩ : VertexCodeCyclicEncoder.At
      (original outside seam) ((original outside seam).vertOf (composeDartEquiv (.inl d))))
  apply Subtype.ext
  change (original outside seam).rho (composeDartEquiv (.inl d)) = _
  rw [original_rho_left, he]

private theorem outside_of_not_mem_ring {d : (capped outside seam).D}
    (hd : d ∉ ring outside seam) : ∃ a : I ⊕ B, d = composeDartEquiv (.inl a) := by
  obtain ⟨(a | (e | i)), rfl⟩ := composeDartEquiv.surjective d
  · exact ⟨a, rfl⟩
  · exact nomatch e
  · exact (hd (List.mem_ofFn.mpr ⟨i, rfl⟩)).elim

theorem reference_geometry
    (h : BridgelessSphericalCubicMapData (original outside seam)) :
    (SourceConstruction.sourceMap (capped outside seam)).mirror.UcyclePlanarPlainQuasicubic
      (ring outside seam) := by
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · apply (Hypermap.plain_mirror _).mpr
    exact ⟨(capped outside seam).alpha_involutive, (capped outside seam).alpha_fixfree⟩
  · constructor
    · intro d hd
      obtain ⟨a, rfl⟩ := outside_of_not_mem_ring outside seam hd
      simp only [mirror_node, rho_left, outside_three outside seam h]
    · intro d hd he
      obtain ⟨a, rfl⟩ := outside_of_not_mem_ring outside seam hd
      simp only [mirror_node, rho_left] at he
      exact outside_ne outside seam h a (Sum.inl.inj (composeDartEquiv.injective he))
  · simp_rw [mirror_node]
    let f : Fin 8 → (capped outside seam).D := fun i => composeDartEquiv (.inr (.inr i))
    have hc : IsCyclicChain (fun i j : Fin 8 => j = finRotate 8 i) (List.finRange 8) := by
      unfold IsCyclicChain
      decide +kernel
    have rel (i j : Fin 8) (he : j = finRotate 8 i) :
        f j = (capped outside seam).rho (f i) := by
      subst j
      exact (rho_hub outside seam i).symm
    change IsCyclicChain _ (List.ofFn f)
    rw [List.ofFn_eq_map]
    constructor
    · exact List.isChain_map_of_isChain f rel hc.1
    · intro a ha b hb
      simp only [List.getLast?_map, Option.mem_def, Option.map_eq_some_iff] at ha
      simp only [List.head?_map, Option.mem_def, Option.map_eq_some_iff] at hb
      obtain ⟨i, hi, rfl⟩ := ha
      obtain ⟨j, hj, rfl⟩ := hb
      exact rel i j (hc.2 i hi j hj)
  · rw [ring, List.nodup_ofFn]
    intro i j he
    exact Sum.inr.inj (Sum.inr.inj (composeDartEquiv.injective he))
  · exact (Hypermap.planar_mirror _).mpr (planar outside seam h)

/-- The reference Kempe theorem applies to the actual capped exterior,
without an exterior-connectivity hypothesis or a colour catalogue. -/
theorem reference_closed
    (h : BridgelessSphericalCubicMapData (original outside seam)) :
    KempeClosed ((SourceConstruction.sourceMap (capped outside seam)).mirror.RingTrace
      (ring outside seam)) :=
  Hypermap.Kempe_map _ _ (reference_geometry outside seam h)

end
end FourColor.TwoDiamondBoundaryHub

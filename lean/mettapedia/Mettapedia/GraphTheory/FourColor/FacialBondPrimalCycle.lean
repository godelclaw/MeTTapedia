import Mettapedia.GraphTheory.FourColor.GoertzelV24PrimalCycleFacialBond
import Mettapedia.GraphTheory.FourColor.GoertzelV24FaceSeparation
import Mettapedia.GraphTheory.FourColor.GoertzelV24WalkCycleParity

/-!
# The complete frontier of a facial bond is a primal cycle

This is the converse needed when contours are constructed as components in
the facial dual, rather than supplied as primal cycles. Sphericity makes
every binary cycle a facial boundary. A nonzero such boundary supported in
a dual bond must be the entire bond: its face coefficients are constant on
each of the two connected sides. Cubicity then extracts a simple cycle and
support minimality proves that it is the complete frontier.

The theorem does not bound the length of that cycle or construct a linkage.
-/

namespace Mettapedia.GraphTheory.FourColor.FacialBondPrimalCycle

open SimpleGraph SimpleGraphDartRotation
open GoertzelV24PrimalCycleFacialBond GoertzelV24KauffmanFacePotential
open GoertzelV24FaceBoundaryLinearAlgebra GoertzelV24FaceOrbitIncidence
open GoertzelV24FaceSeparation GoertzelV24OrbitFaceTwoSided
open GoertzelV24OrbitFaceCycleSpaceEquality GoertzelV24WalkCycleParity
open GoertzelV24PrimalCycleSpace GoertzelV24FaceDualConnectedness
open GoertzelV24SimpleGraphTaitBridge GoertzelV24TwoEdgeCutMinimality

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- A smaller facial boundary cannot change its coefficient along an edge
internal to either side of the containing cut. -/
theorem indicator_eq_of_adj_of_support_subset
    (data : Data G) (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (S T : Finset (OrbitFace data.toRotationSystem))
    (hsub : ∀ e : G.edgeSet,
      orbitFaceBoundaryLinearMap data.toRotationSystem (faceSetIndicator data T) e ≠ 0 →
      orbitFaceBoundaryLinearMap data.toRotationSystem (faceSetIndicator data S) e ≠ 0)
    {f g : OrbitFace data.toRotationSystem}
    (hadj : (orbitFaceDualGraph data).Adj f g) (hside : f ∈ S ↔ g ∈ S) :
    faceSetIndicator data T f = faceSetIndicator data T g := by
  rcases exists_shared_edge_faceSetBoundary_apply data htwo S hadj with
    ⟨e, hf, hg, he⟩
  have hzero : orbitFaceBoundaryLinearMap data.toRotationSystem
      (faceSetIndicator data S) e = 0 := by
    rw [he]
    by_cases h : f ∈ S
    · simp [faceSetIndicator, h, hside.mp h, zmod2_add_self]
    · have h' : g ∉ S := fun hg => h (hside.mpr hg)
      simp [faceSetIndicator, h, h']
  have hsmall : orbitFaceBoundaryLinearMap data.toRotationSystem
      (faceSetIndicator data T) e = 0 := by
    by_contra h
    exact hsub e h hzero
  rw [faceSetBoundary_apply_eq_of_shared_face_pair data htwo T hadj.ne e hf hg] at hsmall
  simpa only [CharTwo.neg_eq] using (add_eq_zero_iff_eq_neg.mp hsmall)

/-- Coefficients of a supported facial boundary are constant on any
connected region wholly on one side of the containing cut. -/
theorem indicator_eq_of_connected_region
    (data : Data G) (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (S T : Finset (OrbitFace data.toRotationSystem))
    (hsub : ∀ e : G.edgeSet,
      orbitFaceBoundaryLinearMap data.toRotationSystem (faceSetIndicator data T) e ≠ 0 →
      orbitFaceBoundaryLinearMap data.toRotationSystem (faceSetIndicator data S) e ≠ 0)
    (region : Set (OrbitFace data.toRotationSystem))
    (hconn : ((orbitFaceDualGraph data).induce region).Connected)
    (hside : ∀ f ∈ region, ∀ g ∈ region, f ∈ S ↔ g ∈ S)
    {f g : OrbitFace data.toRotationSystem} (hf : f ∈ region) (hg : g ∈ region) :
    faceSetIndicator data T f = faceSetIndicator data T g := by
  obtain ⟨walk⟩ := hconn (⟨f, hf⟩ : region) ⟨g, hg⟩
  have along : ∀ {u v : region},
      ((orbitFaceDualGraph data).induce region).Walk u v →
      faceSetIndicator data T u.val = faceSetIndicator data T v.val := by
    intro u v path
    induction path with
    | nil => rfl
    | @cons u v w hadj tail ih =>
      exact (indicator_eq_of_adj_of_support_subset data htwo S T hsub hadj
        (hside u.val u.property v.val v.property)).trans ih
  exact along walk

/-- A nonzero facial boundary contained in a facial bond has exactly the
same nonzero support. This part is purely cut algebra, on any two-sided map. -/
theorem boundary_support_eq_of_bond
    (data : Data G) (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (S T : Finset (OrbitFace data.toRotationSystem))
    (hS : ((orbitFaceDualGraph data).induce {f | f ∈ S}).Connected)
    (hSc : ((orbitFaceDualGraph data).induce {f | f ∉ S}).Connected)
    (hsub : ∀ e : G.edgeSet,
      orbitFaceBoundaryLinearMap data.toRotationSystem (faceSetIndicator data T) e ≠ 0 →
      orbitFaceBoundaryLinearMap data.toRotationSystem (faceSetIndicator data S) e ≠ 0)
    (anchor : G.edgeSet)
    (ha : orbitFaceBoundaryLinearMap data.toRotationSystem
      (faceSetIndicator data T) anchor ≠ 0) :
    ∀ e : G.edgeSet,
      orbitFaceBoundaryLinearMap data.toRotationSystem (faceSetIndicator data T) e ≠ 0 ↔
      orbitFaceBoundaryLinearMap data.toRotationSystem (faceSetIndicator data S) e ≠ 0 := by
  obtain ⟨⟨inside, hin⟩⟩ := hS.nonempty
  obtain ⟨⟨outside, hout⟩⟩ := hSc.nonempty
  have hinconst : ∀ f ∈ S,
      faceSetIndicator data T f = faceSetIndicator data T inside := by
    intro f hf
    exact indicator_eq_of_connected_region data htwo S T hsub {f | f ∈ S} hS
      (by intro f hf g hg; exact iff_of_true hf hg) hf hin
  have houtconst : ∀ f ∉ S,
      faceSetIndicator data T f = faceSetIndicator data T outside := by
    intro f hf
    exact indicator_eq_of_connected_region data htwo S T hsub {f | f ∉ S} hSc
      (by intro f hf g hg; exact iff_of_false hf hg) hf hout
  have hvalues : ∀ f, faceSetIndicator data T f =
      if f ∈ S then faceSetIndicator data T inside else faceSetIndicator data T outside := by
    intro f
    split_ifs with hf
    · exact hinconst f hf
    · exact houtconst f hf
  have hdiff : faceSetIndicator data T inside ≠ faceSetIndicator data T outside := by
    intro heq
    obtain ⟨d, hd⟩ := data.toRotationSystem.dartsOn_nonempty anchor
    have hedge := data.toRotationSystem.mem_dartsOn.mp hd
    apply ha
    rw [← hedge, orbitFaceBoundaryLinearMap_apply_edgeOf _ htwo,
      hvalues (dartOrbitFace data.toRotationSystem d),
      hvalues (dartOrbitFace data.toRotationSystem (data.toRotationSystem.alpha d)), heq]
    simp only [ite_self, CharTwo.add_self_eq_zero]
  intro e
  refine ⟨hsub e, ?_⟩
  intro he
  obtain ⟨d, hd⟩ := data.toRotationSystem.dartsOn_nonempty e
  have hedge := data.toRotationSystem.mem_dartsOn.mp hd
  rw [← hedge, mem_image_iff_separates _ htwo] at he ⊢
  rw [hvalues (dartOrbitFace data.toRotationSystem d),
    hvalues (dartOrbitFace data.toRotationSystem (data.toRotationSystem.alpha d))]
  by_cases hl : dartOrbitFace data.toRotationSystem d ∈ S <;>
    by_cases hr : dartOrbitFace data.toRotationSystem (data.toRotationSystem.alpha d) ∈ S
  · exact (he (by simp only [faceSetIndicator, if_pos hl, if_pos hr])).elim
  · simpa only [if_pos hl, if_neg hr] using hdiff
  · simpa only [if_neg hl, if_pos hr] using hdiff.symm
  · exact (he (by simp only [faceSetIndicator, if_neg hl, if_neg hr])).elim

/-- On the spherical cubic carrier, the complete edge boundary of two
connected facial sides is one simple primal cycle. No contour is supplied. -/
theorem exists_cycle_of_facial_bond
    (data : Data G)
    (hclass : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (S : Finset (OrbitFace data.toRotationSystem))
    (hS : ((orbitFaceDualGraph data).induce {f | f ∈ S}).Connected)
    (hSc : ((orbitFaceDualGraph data).induce {f | f ∉ S}).Connected) :
    ∃ (root : V) (cycle : G.Walk root root), cycle.IsCycle ∧
      ∀ e : G.edgeSet, e.val ∈ cycle.edges ↔
        orbitFaceBoundaryLinearMap data.toRotationSystem (faceSetIndicator data S) e ≠ 0 := by
  let boundary := orbitFaceBoundaryLinearMap data.toRotationSystem (faceSetIndicator data S)
  have hcycleSpace : boundary ∈ f2CycleSpace G :=
    range_orbitFaceBoundaryLinearMap_le_f2CycleSpace data htwo ⟨_, rfl⟩
  have hcubic := incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
    data hclass.spherical.cubic
  have hdual := orbitFaceInteriorDual_connected data.toRotationSystem
    hclass.spherical.cubic hclass.primalConnected hclass.vertexRotationCyclic
  obtain ⟨anchor, ha⟩ : ∃ e : G.edgeSet, boundary e ≠ 0 := by
    by_contra! hzero
    have hz : faceSetIndicator data S ∈ LinearMap.ker
        (orbitFaceBoundaryLinearMap data.toRotationSystem) := by
      rw [LinearMap.mem_ker]
      exact funext hzero
    have hc := (mem_ker_orbitFaceBoundaryLinearMap_iff_constant
      data.toRotationSystem htwo hdual _).mp hz
    obtain ⟨⟨inside, hin⟩⟩ := hS.nonempty
    obtain ⟨⟨outside, hout⟩⟩ := hSc.nonempty
    change inside ∈ S at hin
    change outside ∉ S at hout
    have hbad := hc inside outside
    simp [faceSetIndicator, hin, hout] at hbad
  obtain ⟨root, cycle, hcycle, hanchor, hsupport⟩ :=
    exists_isCycle_through_of_scalar_ne_zero boundary
      (fun v => scalarVertexKirchhoffSum_eq_zero_of_mem_f2CycleSpace hcycleSpace v)
      hcubic anchor ha
  obtain ⟨T, hT⟩ := exists_faceSetBoundary_eq_of_mem_f2CycleSpace data hclass htwo
    (walkEdgeParity_mem_f2CycleSpace_of_closed cycle)
  have hparity : ∀ e : G.edgeSet, walkEdgeParity cycle e ≠ 0 ↔ e.val ∈ cycle.edges := by
    intro e
    constructor
    · intro h
      by_contra hn
      exact h (walkEdgeParity_apply_eq_zero_of_not_mem_edges cycle e hn)
    · intro h
      rw [walkEdgeParity_apply_eq_one_of_isTrail_of_mem_edges hcycle.isTrail e h]
      exact one_ne_zero
  have hsub : ∀ e : G.edgeSet,
      orbitFaceBoundaryLinearMap data.toRotationSystem (faceSetIndicator data T) e ≠ 0 →
      orbitFaceBoundaryLinearMap data.toRotationSystem (faceSetIndicator data S) e ≠ 0 := by
    intro e he
    rw [hT] at he
    exact hsupport e ((hparity e).mp he)
  have hTa : orbitFaceBoundaryLinearMap data.toRotationSystem
      (faceSetIndicator data T) anchor ≠ 0 := by
    rw [hT]
    exact (hparity anchor).mpr hanchor
  refine ⟨root, cycle, hcycle, ?_⟩
  intro e
  have hexact := boundary_support_eq_of_bond data htwo S T hS hSc hsub anchor hTa e
  rw [hT, hparity] at hexact
  exact hexact

end
end Mettapedia.GraphTheory.FourColor.FacialBondPrimalCycle

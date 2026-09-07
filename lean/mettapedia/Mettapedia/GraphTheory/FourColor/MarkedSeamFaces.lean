import Mettapedia.GraphTheory.FourColor.MarkedCotreeSeam

/-!
# Designated face orbits survive the actual marked seam

The sewn map retains whole vertex stars, not just individual named edges.
Its ambient dart map is injective and intertwines vertex rotation. Together
with the marked edge-partner law, this preserves each fully marked facial
orbit, including its cyclic order and length. No global closure of the
marked family under vertex rotation is required.
-/

namespace Mettapedia.GraphTheory.FourColor.MarkedCotreeSeam.SeamPair

open SimpleGraph SimpleGraphDartRotation
open GoertzelV24RotationCutDartDecomposition GoertzelV24OpenTangleComposition
open GoertzelV24ConnectedEdgeShoreMajority GoertzelV24MajorityShoreNormalizedState
open GoertzelV24ConnectedEdgeShoreStructuralData
open GoertzelV24MajorityShorePhysicalReplacement

noncomputable section
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {M : Type v}
local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq
variable {rotation : Data G} {marks : Finset V} {mark : M → G.Dart} {w : ℕ}

/-- Undo the sewn carrier reassociation and the two internal/boundary splits. -/
def retainedEquiv (pair : SeamPair rotation marks mark w) : pair.candidate.D ≃
    RetainedDart rotation.toRotationSystem (majorityDeletedKeep G pair.outer.shore) ⊕
    RetainedDart rotation.toRotationSystem (majorityRetainedKeep G pair.inner.shore) :=
  composeDartEquiv.symm.trans (Equiv.sumCongr
    (retainedDartEquivInternalSumBoundary _ _).symm
    (retainedDartEquivInternalSumBoundary _ _).symm)

theorem ambientDart_eq_retained (pair : SeamPair rotation marks mark w)
    (d : pair.candidate.D) : pair.ambientDart d =
      Sum.elim Subtype.val Subtype.val (pair.retainedEquiv d) := by
  rcases d with (d | d) | (d | d) <;> rfl

/-- Nested shores make the two surviving carriers disjoint in the ambient map. -/
theorem ambientDart_injective (pair : SeamPair rotation marks mark w) :
    Function.Injective pair.ambientDart := by
  intro d e h
  apply pair.retainedEquiv.injective
  rw [pair.ambientDart_eq_retained, pair.ambientDart_eq_retained] at h
  generalize pair.retainedEquiv d = x at h ⊢
  generalize pair.retainedEquiv e = y at h ⊢
  rcases x with x | x <;> rcases y with y | y
  · exact congrArg Sum.inl (Subtype.ext h)
  · have hx := (majorityDeletedKeep_iff pair.outer.shore x.val.fst).mp x.property
    have hy := majorityVertexSide_mono pair.nested.1
      ((majorityRetainedKeep_iff pair.inner.shore y.val.fst).mp y.property)
    change x.val = y.val at h
    rw [h] at hx
    exact False.elim (hx hy)
  · have hy := (majorityDeletedKeep_iff pair.outer.shore y.val.fst).mp y.property
    have hx := majorityVertexSide_mono pair.nested.1
      ((majorityRetainedKeep_iff pair.inner.shore x.val.fst).mp x.property)
    change x.val = y.val at h
    rw [h] at hx
    exact False.elim (hy hx)
  · exact congrArg Sum.inr (Subtype.ext h)

theorem ambientDart_compose_left (pair : SeamPair rotation marks mark w)
    (d : InternalDart rotation.toRotationSystem (majorityDeletedKeep G pair.outer.shore) ⊕
      BoundaryDart rotation.toRotationSystem (majorityDeletedKeep G pair.outer.shore)) :
    pair.ambientDart (composeDartEquiv (Sum.inl d)) =
      ((retainedDartEquivInternalSumBoundary _ _).symm d).val := by
  cases d <;> rfl

theorem ambientDart_compose_right (pair : SeamPair rotation marks mark w)
    (d : InternalDart rotation.toRotationSystem (majorityRetainedKeep G pair.inner.shore) ⊕
      BoundaryDart rotation.toRotationSystem (majorityRetainedKeep G pair.inner.shore)) :
    pair.ambientDart (composeDartEquiv (Sum.inr d)) =
      ((retainedDartEquivInternalSumBoundary _ _).symm d).val := by
  cases d <;> rfl

/-- Sewing changes edge partners, never the rotation of a surviving vertex. -/
theorem ambientDart_rho (pair : SeamPair rotation marks mark w)
    (d : pair.candidate.D) :
    pair.ambientDart (pair.candidate.rho d) =
      rotation.toRotationSystem.rho (pair.ambientDart d) := by
  change pair.ambientDart ((OpenTangleData.composeData _ _ pair.matching).rho d) = _
  rw [OpenTangleData.composeData_rho_apply]
  obtain ⟨x, rfl⟩ := composeDartEquiv.surjective d
  simp only [Equiv.symm_apply_apply]
  rcases x with x | x
  · change pair.ambientDart (composeDartEquiv (Sum.inl
        ((OpenTangleData.ofVertexSide _ _ pair.outer.outsideOuter).rho x))) = _
    rw [pair.ambientDart_compose_left, OpenTangleData.ofVertexSide_rho_underlying,
      retainedRho_val, pair.ambientDart_compose_left]
  · change pair.ambientDart (composeDartEquiv (Sum.inr
        ((OpenTangleData.ofVertexSide _ _ pair.inner.innerOuter).rho x))) = _
    rw [pair.ambientDart_compose_right, OpenTangleData.ofVertexSide_rho_underlying,
      retainedRho_val, pair.ambientDart_compose_right]

/-- A named dart keeps its actual facial successor when its edge partner is
also named. Its successor need not belong to the entire marked family. -/
theorem ambientDart_phi_mark (pair : SeamPair rotation marks mark w)
    (hclosed : ∀ m, ∃ m', rotation.toRotationSystem.alpha (mark m) = mark m')
    (d : pair.candidate.D) (m : M) (hd : pair.ambientDart d = mark m) :
    pair.ambientDart (pair.candidate.phi d) =
      rotation.toRotationSystem.phi (pair.ambientDart d) := by
  change pair.ambientDart (pair.candidate.rho (pair.candidate.alpha d)) = _
  rw [pair.ambientDart_rho, pair.candidate_alpha_mark hclosed d m hd]
  rfl

/-- Facial iteration commutes on a designated orbit. Only that orbit must
be covered by the edge-reversal-closed named family. -/
theorem ambientDart_phi_pow (pair : SeamPair rotation marks mark w)
    (hclosed : ∀ m, ∃ m', rotation.toRotationSystem.alpha (mark m) = mark m')
    (root : pair.candidate.D)
    (hface : ∀ e ∈ rotation.toRotationSystem.faceOrbit (pair.ambientDart root),
      ∃ m, mark m = e) (n : ℕ) :
    pair.ambientDart ((pair.candidate.phi ^ n) root) =
      (rotation.toRotationSystem.phi ^ n) (pair.ambientDart root) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    obtain ⟨m, hm⟩ := hface ((rotation.toRotationSystem.phi ^ n) (pair.ambientDart root))
      (rotation.toRotationSystem.mem_faceOrbit.mpr
        (Equiv.Perm.SameCycle.refl _ _).pow_right)
    simp only [pow_succ', Equiv.Perm.mul_apply]
    rw [pair.ambientDart_phi_mark hclosed _ m (ih.trans hm.symm), ih]

/-- The retained designated face neither splits nor merges with another
face: ambient naming reflects as well as preserves its orbit relation. -/
theorem sameCycle_iff (pair : SeamPair rotation marks mark w)
    (hclosed : ∀ m, ∃ m', rotation.toRotationSystem.alpha (mark m) = mark m')
    (root : pair.candidate.D)
    (hface : ∀ e ∈ rotation.toRotationSystem.faceOrbit (pair.ambientDart root),
      ∃ m, mark m = e) (d : pair.candidate.D) :
    pair.candidate.phi.SameCycle root d ↔
      rotation.toRotationSystem.phi.SameCycle (pair.ambientDart root) (pair.ambientDart d) := by
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    rw [pair.ambientDart_phi_pow hclosed root hface]
    exact (Equiv.Perm.SameCycle.refl _ _).pow_right
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    refine ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast]
    apply pair.ambientDart_injective
    rw [pair.ambientDart_phi_pow hclosed root hface, hn]

/-- The complete oriented face, not merely a subset of its edges, survives. -/
theorem faceOrbit_image (pair : SeamPair rotation marks mark w)
    (hclosed : ∀ m, ∃ m', rotation.toRotationSystem.alpha (mark m) = mark m')
    (root : pair.candidate.D)
    (hface : ∀ e ∈ rotation.toRotationSystem.faceOrbit (pair.ambientDart root),
      ∃ m, mark m = e) :
    (pair.candidate.faceOrbit root).image pair.ambientDart =
      rotation.toRotationSystem.faceOrbit (pair.ambientDart root) := by
  classical
  ext e
  constructor
  · rintro h
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp h
    exact rotation.toRotationSystem.mem_faceOrbit.mpr
      ((pair.sameCycle_iff hclosed root hface d).mp (pair.candidate.mem_faceOrbit.mp hd))
  · intro h
    obtain ⟨n, hn⟩ := (rotation.toRotationSystem.mem_faceOrbit.mp h).exists_nat_pow_eq
    exact Finset.mem_image.mpr ⟨(pair.candidate.phi ^ n) root,
      pair.candidate.mem_faceOrbit.mpr (Equiv.Perm.SameCycle.refl _ _).pow_right,
      (pair.ambientDart_phi_pow hclosed root hface n).trans hn⟩

/-- Exact facial length preservation follows from the injective dart map. -/
theorem faceOrbit_card (pair : SeamPair rotation marks mark w)
    (hclosed : ∀ m, ∃ m', rotation.toRotationSystem.alpha (mark m) = mark m')
    (root : pair.candidate.D)
    (hface : ∀ e ∈ rotation.toRotationSystem.faceOrbit (pair.ambientDart root),
      ∃ m, mark m = e) :
    (pair.candidate.faceOrbit root).card =
      (rotation.toRotationSystem.faceOrbit (pair.ambientDart root)).card := by
  classical
  rw [← pair.faceOrbit_image hclosed root hface]
  exact (Finset.card_image_of_injective _ pair.ambientDart_injective).symm

/-- Endpoint marking supplies the root itself; the physical face orbit,
its length and its rooted cyclic sequence are then preserved. -/
theorem designated_face_survives (pair : SeamPair rotation marks mark w)
    (hmarks : ∀ m, (mark m).fst ∈ marks)
    (hclosed : ∀ m, ∃ m', rotation.toRotationSystem.alpha (mark m) = mark m')
    (root : G.Dart)
    (hface : ∀ e ∈ rotation.toRotationSystem.faceOrbit root, ∃ m, mark m = e) :
    ∃ d : pair.candidate.D, pair.ambientDart d = root ∧
      (pair.candidate.faceOrbit d).image pair.ambientDart = rotation.toRotationSystem.faceOrbit root ∧
      (pair.candidate.faceOrbit d).card = (rotation.toRotationSystem.faceOrbit root).card ∧
      ∀ n : ℕ, pair.ambientDart ((pair.candidate.phi ^ n) d) =
        (rotation.toRotationSystem.phi ^ n) root := by
  obtain ⟨m, hm⟩ := hface root (rotation.toRotationSystem.mem_faceOrbit_self root)
  obtain ⟨d, hd⟩ := pair.mark_survives hmarks m
  have hd' : pair.ambientDart d = root := hd.trans hm
  have hf : ∀ e ∈ rotation.toRotationSystem.faceOrbit (pair.ambientDart d),
      ∃ m, mark m = e := by simpa only [hd'] using hface
  refine ⟨d, hd', ?_, ?_, ?_⟩
  · simpa only [hd'] using pair.faceOrbit_image hclosed d hf
  · simpa only [hd'] using pair.faceOrbit_card hclosed d hf
  · intro n
    simpa only [hd'] using pair.ambientDart_phi_pow hclosed d hf n

end
end Mettapedia.GraphTheory.FourColor.MarkedCotreeSeam.SeamPair

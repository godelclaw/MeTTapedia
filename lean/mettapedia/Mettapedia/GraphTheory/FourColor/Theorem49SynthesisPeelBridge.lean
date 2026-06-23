import Mettapedia.GraphTheory.FourColor.Theorem49SynthesisCore

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- Route-independent synthesis constructor from the single algebraic hypothesis that every
selected-boundary-zero annihilator of the Definition 4.8 family vanishes. All remaining fields of
`Theorem49BoundaryRootSynthesis` are then obtained by the generic projected-source algebra. -/
theorem theorem49BoundaryRootSynthesis_of_boundaryZeroAnnihilatorTrivial
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (C₀ : G.EdgeColoring Color)
    (htrivial : BoundaryZeroAnnihilatorTrivialForEmbedding emb C₀) :
    Theorem49BoundaryRootSynthesis emb C₀ := by
  have hboundary :
      ∀ v ∈ selectedBoundaryInteriorEdgeEndpointVertices emb,
        ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces,
          v ∉ (e : Sym2 V) :=
    selectedBoundaryInteriorEdgeEndpointVertices_avoids_selectedBoundarySupport emb
  have htargetLeProjectedGeneratorFamilySpan :
      theorem49BoundaryZeroKirchhoffSubspace emb
          (selectedBoundaryInteriorEdgeEndpointVertices emb) ≤
        Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C₀) := by
    rw [span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_boundaryZeroAnnihilatorTrivial
      emb C₀ htrivial]
    exact
      theorem49BoundaryZeroKirchhoffSubspace_le_planarBoundaryZeroSubmodule
        emb (selectedBoundaryInteriorEdgeEndpointVertices emb)
  have hprojectedGeneratorRepresentation :
      ∀ {z : G.edgeSet → Color},
        z ∈ theorem49BoundaryZeroKirchhoffSubspace emb
            (selectedBoundaryInteriorEdgeEndpointVertices emb) →
          ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
            (terms : Set (G.edgeSet → Color)) ⊆
                projectedKempeClosureGeneratorFamily emb C₀ ∧
              coeff.support ⊆ terms ∧
                ∑ y ∈ terms, coeff y • y = z := by
    intro z hz
    exact
      exists_projectedKempeClosureGeneratorFamily_finset_sum_of_mem_span_projectedKempeClosureGeneratorFamily
        (htargetLeProjectedGeneratorFamilySpan hz)
  have hrawGeneratorProjectionRepresentation :
      ∀ {z : G.edgeSet → Color},
        z ∈ theorem49BoundaryZeroKirchhoffSubspace emb
            (selectedBoundaryInteriorEdgeEndpointVertices emb) →
          ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
            (terms : Set (G.edgeSet → Color)) ⊆
                kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
              coeff.support ⊆ terms ∧
                (∑ y ∈ terms, coeff y • y) ∈
                    kirchhoffSubmodule G
                      (selectedBoundaryInteriorEdgeEndpointVertices emb) ∧
                  boundaryZeroProjection
                    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                      (∑ y ∈ terms, coeff y • y) = z := by
    intro z hz
    rcases
      exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_projectedKempeClosureGeneratorSubspace
        ((theorem49BoundaryZeroKirchhoffSubspace_le_projectedKempeClosureGeneratorSubspace_of_boundaryZeroAnnihilatorTrivial
          emb C₀ htrivial (selectedBoundaryInteriorEdgeEndpointVertices emb)) hz) with
      ⟨coeff, terms, hterms, hsupport, hproj⟩
    refine ⟨coeff, terms, hterms, hsupport, ?_, hproj⟩
    have hprojKirch :
        boundaryZeroProjection
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
            (∑ y ∈ terms, coeff y • y) ∈
          kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb) := by
      rw [hproj]
      exact hz.1
    exact
      (boundaryZeroProjection_mem_kirchhoffSubmodule_iff_of_boundary_avoids_vertices
        (G := G)
        (boundary := selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
        (vertices := selectedBoundaryInteriorEdgeEndpointVertices emb)
        (x := ∑ y ∈ terms, coeff y • y) hboundary).1 hprojKirch
  have hrawSourcePreimage :
      ∀ {z : G.edgeSet → Color},
        z ∈ theorem49BoundaryZeroKirchhoffSubspace emb
            (selectedBoundaryInteriorEdgeEndpointVertices emb) →
          ∃ y ∈ kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
              kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb),
            boundaryZeroProjection
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) y = z := by
    intro z hz
    rcases hrawGeneratorProjectionRepresentation hz with
      ⟨coeff, terms, hterms, hsupport, hkirch, hproj⟩
    let raw : G.edgeSet → Color := ∑ y ∈ terms, coeff y • y
    have hrawSpan :
        raw ∈ kempeClosureGeneratorSubspace emb.faceBoundary C₀ := by
      have hrawSpan' :
          raw ∈ Submodule.span F2 (kempeClosureGeneratorFamily emb.faceBoundary C₀) :=
        (Submodule.mem_span_iff_exists_finset_subset
          (R := F2) (s := kempeClosureGeneratorFamily emb.faceBoundary C₀) (x := raw)).2
          ⟨coeff, terms, hterms, hsupport, rfl⟩
      simpa [kempeClosureGeneratorSubspace, raw] using hrawSpan'
    exact ⟨raw, ⟨hrawSpan, hkirch⟩, by simpa [raw] using hproj⟩
  have htargetEqRawSourceImage :
      theorem49BoundaryZeroKirchhoffSubspace emb
          (selectedBoundaryInteriorEdgeEndpointVertices emb) =
        Submodule.map
          (boundaryZeroProjection
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
          (kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
            kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) := by
    ext z
    constructor
    · intro hz
      rcases hrawSourcePreimage hz with ⟨y, hy, hyproj⟩
      exact ⟨y, hy, hyproj⟩
    · rintro ⟨y, hy, rfl⟩
      exact
        (boundaryZeroProjection_mem_theorem49BoundaryZeroKirchhoffSubspace_iff_of_selectedBoundary_avoids_vertices
          (G := G) (emb := emb)
          (vertices := selectedBoundaryInteriorEdgeEndpointVertices emb)
          (x := y) hboundary).2 hy.2
  have hrawKirchhoffRepresentative :
      ∀ {x : G.edgeSet → Color},
        x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb) →
          ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
            (terms : Set (G.edgeSet → Color)) ⊆
                kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
              coeff.support ⊆ terms ∧
                (∑ y ∈ terms, coeff y • y) ∈
                    kirchhoffSubmodule G
                      (selectedBoundaryInteriorEdgeEndpointVertices emb) ∧
                  boundaryZeroProjection
                    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                      (∑ y ∈ terms, coeff y • y) =
                    boundaryZeroProjection
                      (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) x := by
    intro x hx
    have hz :
        boundaryZeroProjection
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) x ∈
          theorem49BoundaryZeroKirchhoffSubspace emb
            (selectedBoundaryInteriorEdgeEndpointVertices emb) :=
      (boundaryZeroProjection_mem_theorem49BoundaryZeroKirchhoffSubspace_iff_of_selectedBoundary_avoids_vertices
        (G := G) (emb := emb)
        (vertices := selectedBoundaryInteriorEdgeEndpointVertices emb)
        (x := x) hboundary).2 hx
    exact hrawGeneratorProjectionRepresentation hz
  have hrawBoundaryKernelDecomposition :
      ∀ {x : G.edgeSet → Color},
        x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb) →
          ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color))
              (boundaryError : G.edgeSet → Color),
            (terms : Set (G.edgeSet → Color)) ⊆
                kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
              coeff.support ⊆ terms ∧
                (∑ y ∈ terms, coeff y • y) ∈
                    kirchhoffSubmodule G
                      (selectedBoundaryInteriorEdgeEndpointVertices emb) ∧
                  boundaryError ∈
                      kirchhoffSubmodule G
                        (selectedBoundaryInteriorEdgeEndpointVertices emb) ⊓
                        LinearMap.ker
                          (boundaryZeroProjection
                            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
                    (∑ y ∈ terms, coeff y • y) + boundaryError = x ∧
                      boundaryZeroProjection
                        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                          (∑ y ∈ terms, coeff y • y) =
                        boundaryZeroProjection
                          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) x := by
    intro x hx
    rcases hrawKirchhoffRepresentative hx with
      ⟨coeff, terms, hterms, hsupport, hkirch, hproj⟩
    let raw : G.edgeSet → Color := ∑ y ∈ terms, coeff y • y
    refine
      ⟨coeff, terms, raw + x, hterms, hsupport, hkirch, ?_, ?_, ?_⟩
    · constructor
      · exact
          (kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)).add_mem
            hkirch hx
      · exact
          (boundaryZeroProjection_eq_zero_iff_mem_boundarySupportedSubmodule
            (boundary := selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
            (x := raw + x)).2
            (add_mem_boundarySupportedSubmodule_of_boundaryZeroProjection_eq
              (boundary := selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
              (x := x) (y := raw) (by simpa [raw] using hproj))
    · simpa [raw] using chain_add_self_add raw x
    · simpa [raw] using hproj
  have hpointwise :
      ∀ {z : theorem49BoundaryZeroKirchhoffSubspace emb
          (selectedBoundaryInteriorEdgeEndpointVertices emb)},
        (∀ p ∈ projectedKempeClosureGeneratorSubspace emb C₀,
          chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) = 0) ↔
          z = 0 := by
    intro z
    constructor
    · intro hzero
      have hboundaryZero :
          ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces,
            (z : G.edgeSet → Color) e = 0 :=
        boundaryZero_of_mem_theorem49BoundaryZeroKirchhoffSubspace z.property
      have horth :
          ((z : theorem49BoundaryZeroKirchhoffSubspace emb
              (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
            G.edgeSet → Color) ∈
            (chainDotBilinForm G.edgeSet).orthogonal
              (projectedKempeClosureGeneratorSubspace emb C₀) := by
        intro p hp
        exact hzero p hp
      have hgen :
          AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C₀
            ((z : theorem49BoundaryZeroKirchhoffSubspace emb
              (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
              G.edgeSet → Color) :=
        (mem_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_iff_annihilatesKempeClosureGeneratorFamily
          (G := G) (emb := emb) (C₀ := C₀)
          (z := ((z : theorem49BoundaryZeroKirchhoffSubspace emb
            (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
            G.edgeSet → Color))
          (theorem49BoundaryZeroKirchhoffSubspace_le_planarBoundaryZeroSubmodule
            emb (selectedBoundaryInteriorEdgeEndpointVertices emb) z.property)).1 horth
      apply Subtype.ext
      funext e
      exact
        htrivial
          ((z : theorem49BoundaryZeroKirchhoffSubspace emb
            (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
            G.edgeSet → Color)
          hboundaryZero hgen e
    · intro hz p _hp
      rw [hz]
      exact (chainDotBilinForm G.edgeSet p).map_zero
  have hpairingKer :
      LinearMap.ker
          (theorem49BoundaryZeroKirchhoffSubspaceProjectedGeneratorPairingMap
            (G := G) emb C₀ (selectedBoundaryInteriorEdgeEndpointVertices emb)) =
        ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    exact
      (hpointwise (z := z)).1
        (by
          intro p hp
          let p' : projectedKempeClosureGeneratorSubspace emb C₀ := ⟨p, hp⟩
          have hmap :
              theorem49BoundaryZeroKirchhoffSubspaceProjectedGeneratorPairingMap
                  (G := G) emb C₀ (selectedBoundaryInteriorEdgeEndpointVertices emb) z = 0 := hz
          have hcoord := congrArg
            (fun f : projectedKempeClosureGeneratorSubspace emb C₀ →ₗ[F2] F2 => f p') hmap
          simpa [theorem49BoundaryZeroKirchhoffSubspaceProjectedGeneratorPairingMap, p'] using
            hcoord)
  have hfinrankLe :
      Module.finrank F2
          (theorem49BoundaryZeroKirchhoffSubspace emb
            (selectedBoundaryInteriorEdgeEndpointVertices emb)) ≤
        Module.finrank F2 (projectedKempeClosureGeneratorSubspace emb C₀) := by
    let L :=
      theorem49BoundaryZeroKirchhoffSubspaceProjectedGeneratorPairingMap
        (G := G) emb C₀ (selectedBoundaryInteriorEdgeEndpointVertices emb)
    have hinj : Function.Injective L := (LinearMap.ker_eq_bot).1 hpairingKer
    have hleDual :
        Module.finrank F2
            (theorem49BoundaryZeroKirchhoffSubspace emb
              (selectedBoundaryInteriorEdgeEndpointVertices emb)) ≤
          Module.finrank F2 (projectedKempeClosureGeneratorSubspace emb C₀ →ₗ[F2] F2) :=
      LinearMap.finrank_le_finrank_of_injective (f := L) hinj
    simpa [L, Module.Dual] using
      hleDual.trans_eq
        (Subspace.dual_finrank_eq
          (K := F2) (V := projectedKempeClosureGeneratorSubspace emb C₀))
  refine
    { target_eq_boundaryProjectionImage := ?_
      pointwise_separation := ?_
      pairing_ker_eq_bot := ?_
      finrank_le_projectedGeneratorSubspace := ?_
      target_eq_projectedGeneratorSource := ?_
      target_le_projectedGeneratorSubspace := ?_
      target_le_projectedGeneratorFamilySpan := ?_
      target_eq_rawSourceImage := ?_
      projectedGeneratorRepresentation := ?_
      rawGeneratorProjectionRepresentation := ?_
      rawSourcePreimage := ?_
      rawKirchhoffRepresentative := ?_
      rawBoundaryKernelDecomposition := ?_ }
  · exact
      theorem49BoundaryZeroKirchhoffSubspace_selectedBoundaryInteriorVertices_eq_map_boundaryZeroProjection_kirchhoffSubmodule
        (G := G) emb (interiorEdgeEndpointSupport emb)
  · intro z
    exact hpointwise (z := z)
  · exact hpairingKer
  · exact hfinrankLe
  · change
      theorem49BoundaryZeroKirchhoffSubspace emb
          (selectedBoundaryInteriorEdgeEndpointVertices emb) =
        kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb) ⊓
          projectedKempeClosureGeneratorSubspace emb C₀
    rw [theorem49BoundaryZeroKirchhoffSubspace,
      projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_boundaryZeroAnnihilatorTrivial
        emb C₀ htrivial]
  · exact
      theorem49BoundaryZeroKirchhoffSubspace_le_projectedKempeClosureGeneratorSubspace_of_boundaryZeroAnnihilatorTrivial
        emb C₀ htrivial
        (selectedBoundaryInteriorEdgeEndpointVertices emb)
  · exact htargetLeProjectedGeneratorFamilySpan
  · exact htargetEqRawSourceImage
  · intro z hz
    exact hprojectedGeneratorRepresentation hz
  · intro z hz
    exact hrawGeneratorProjectionRepresentation hz
  · intro z hz
    exact hrawSourcePreimage hz
  · intro x hx
    exact hrawKirchhoffRepresentative hx
  · intro x hx
    exact hrawBoundaryKernelDecomposition hx

/-- The boundary-aware attached certificate surface already discharges the non-geometric Theorem
4.9 hypothesis: every selected-boundary-zero annihilator of the Definition 4.8 family vanishes. -/
theorem boundaryZeroAnnihilatorTrivialForEmbedding_of_planarBoundaryAttachedRootedFacePeelCertificate
    {G : SimpleGraph V}
    (data : PlanarBoundaryAttachedRootedFacePeelCertificate G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    BoundaryZeroAnnihilatorTrivialForEmbedding data.embedding C₀ := by
  intro z hzeroBoundary hgen e
  exact
    zero_on_allEdges_of_boundary_zero_and_planarBoundaryAttachedRootedFacePeelCertificate_of_annihilatesKempeClosureGeneratorFamily
      (data := data) (C₀ := C₀) (C := C₀) (htait := hC₀)
      (hC := G.mem_edgeKempeClosure_self C₀) (z := z)
      (hzeroBoundary := hzeroBoundary) (hgen := hgen) e

/-- The attached rooted face-peel certificate surface already reaches the full current Theorem 4.9
synthesis package. This isolates the remaining route burden upstream of certificate construction. -/
theorem theorem49BoundaryRootSynthesis_of_planarBoundaryAttachedRootedFacePeelCertificate
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (data : PlanarBoundaryAttachedRootedFacePeelCertificate G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootSynthesis data.embedding C₀ :=
  theorem49BoundaryRootSynthesis_of_boundaryZeroAnnihilatorTrivial
    (G := G) (emb := data.embedding) C₀
    (boundaryZeroAnnihilatorTrivialForEmbedding_of_planarBoundaryAttachedRootedFacePeelCertificate
      data C₀ hC₀)

/-- The boundary-aware height-ordered peel surface already induces the attached rooted
certificate on the same embedding. This pushes the theorem-4.9 synthesis boundary up to the
height-sorted witness-cover interface, with no explicit parent map or annulus decomposition
needed. -/
noncomputable def
    PlanarBoundaryHeightOrderedFacePeelWitnessData.toPlanarBoundaryAttachedRootedFacePeelCertificate
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb) :
    PlanarBoundaryAttachedRootedFacePeelCertificate G := by
  exact
    { embedding := emb
      certificate := data.toBoundaryRootedFacePeelCertificate }

/-- The boundary-aware height-ordered peel surface already reaches the full current Theorem 4.9
synthesis package. Once the annulus route produces a height-sorted witness-cover package, no
further theorem-4.9 algebra remains. -/
theorem theorem49BoundaryRootSynthesis_of_planarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootSynthesis emb C₀ := by
  simpa [PlanarBoundaryHeightOrderedFacePeelWitnessData.toPlanarBoundaryAttachedRootedFacePeelCertificate] using
    theorem49BoundaryRootSynthesis_of_planarBoundaryAttachedRootedFacePeelCertificate
      (G := G)
      (PlanarBoundaryHeightOrderedFacePeelWitnessData.toPlanarBoundaryAttachedRootedFacePeelCertificate
        data)
      C₀ hC₀

/-- The finite collar-layer witness-cover surface also already reaches the full current Theorem
4.9 synthesis package, via its canonical height-sorted witness-cover lowering. This moves the
positive route boundary earlier than any explicit remainder bookkeeping. -/
theorem theorem49BoundaryRootSynthesis_of_planarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryCollarLayerFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootSynthesis emb C₀ := by
  exact
    theorem49BoundaryRootSynthesis_of_planarBoundaryHeightOrderedFacePeelWitnessData
      (G := G) data.toHeightOrderedFacePeelWitnessData C₀ hC₀

end Mettapedia.GraphTheory.FourColor

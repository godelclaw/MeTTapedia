import Mettapedia.GraphTheory.FourColor.Theorem49InteriorVertices
import Mettapedia.GraphTheory.FourColor.Theorem49InteriorVerticesAnnulusConstruction
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusGeometry
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusConstructionSpanning
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusRootInteriorDual

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- The subtype of graph edges used by the Theorem 4.9 boundary/Kirchhoff linear algebra. -/
abbrev Theorem49EdgeCarrier (G : SimpleGraph V) : Type _ := ↑G.edgeSet

/-- Edge-coloring vectors over the Theorem 4.9 edge carrier. -/
abbrev Theorem49EdgeSpace (G : SimpleGraph V) : Type _ := Theorem49EdgeCarrier G → Color

/-- The selected interior-edge endpoint vertices used by the v23 boundary-root route. -/
noncomputable abbrev Theorem49BoundaryVertices {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) : Finset V :=
  selectedBoundaryInteriorEdgeEndpointVertices emb

/-- The selected boundary support used by the v23 boundary-root route. -/
abbrev Theorem49BoundarySupport {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) : Finset (Theorem49EdgeCarrier G) :=
  selectedBoundarySupport emb.faceBoundary emb.faces emb.faces

/-- The selected-boundary erasure map on v23 edge-coloring vectors. -/
abbrev Theorem49BoundaryProjection {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) :
    Theorem49EdgeSpace G →ₗ[F2] Theorem49EdgeSpace G :=
  boundaryZeroProjection (Theorem49BoundarySupport emb)

/-- The purified Kirchhoff submodule used by the v23 boundary-root route. -/
noncomputable abbrev Theorem49BoundaryKirchhoffSubmodule {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)]
    (emb : PlaneEmbeddingWithBoundary G) : Submodule F2 (Theorem49EdgeSpace G) :=
  kirchhoffSubmodule G (Theorem49BoundaryVertices emb)

/-- The concrete boundary-zero Kirchhoff target used by the v23 boundary-root route. -/
noncomputable abbrev Theorem49BoundaryTarget {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)]
    (emb : PlaneEmbeddingWithBoundary G) : Submodule F2 (Theorem49EdgeSpace G) :=
  theorem49BoundaryZeroKirchhoffSubspace emb (Theorem49BoundaryVertices emb)

/-- Raw Definition 4.8 generator family used by the v23 boundary-root route. -/
abbrev Theorem49RawGeneratorFamily {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color) :
    Set (Theorem49EdgeSpace G) :=
  kempeClosureGeneratorFamily emb.faceBoundary C₀

/-- Raw Definition 4.8 generator span used before imposing the Kirchhoff condition. -/
noncomputable abbrev Theorem49RawGeneratorSubspace {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color) :
    Submodule F2 (Theorem49EdgeSpace G) :=
  kempeClosureGeneratorSubspace emb.faceBoundary C₀

/-- Projected Definition 4.8 generator family used by the v23 boundary-root route. -/
abbrev Theorem49ProjectedGeneratorFamily {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color) :
    Set (Theorem49EdgeSpace G) :=
  projectedKempeClosureGeneratorFamily emb C₀

/-- Projected Definition 4.8 generator subspace used by the v23 boundary-root route. -/
noncomputable abbrev Theorem49ProjectedGeneratorSubspace {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color) :
    Submodule F2 (Theorem49EdgeSpace G) :=
  projectedKempeClosureGeneratorSubspace emb C₀

/-- Dual space of projected Definition 4.8 generators used by the quotient pairing route. -/
abbrev Theorem49ProjectedGeneratorDual {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color) : Type _ :=
  Theorem49ProjectedGeneratorSubspace emb C₀ →ₗ[F2] F2

/-- The projected-generator pairing map on the concrete v23 boundary-zero Kirchhoff target. -/
noncomputable abbrev Theorem49TargetPairingMap {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color) :
    Theorem49BoundaryTarget emb →ₗ[F2] Theorem49ProjectedGeneratorDual emb C₀ :=
  theorem49BoundaryZeroKirchhoffSubspaceProjectedGeneratorPairingMap
    (G := G) emb C₀ (Theorem49BoundaryVertices emb)

/-- Kirchhoff-valid raw Definition 4.8 source chains for the v23 boundary-root route. -/
noncomputable abbrev Theorem49RawSource {G : SimpleGraph V} [Fintype (Theorem49EdgeCarrier G)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color) :
    Submodule F2 (Theorem49EdgeSpace G) :=
  Theorem49RawGeneratorSubspace emb C₀ ⊓
    Theorem49BoundaryKirchhoffSubmodule emb

/-- Selected-boundary projection kernel inside the purified v23 Kirchhoff submodule. -/
noncomputable abbrev Theorem49BoundaryKernel {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)]
    (emb : PlaneEmbeddingWithBoundary G) :
    Submodule F2 (Theorem49BoundaryKirchhoffSubmodule emb) :=
  LinearMap.ker ((Theorem49BoundaryProjection emb).domRestrict
    (Theorem49BoundaryKirchhoffSubmodule emb))

/-- Kirchhoff-valid raw source, viewed inside the purified v23 Kirchhoff submodule. -/
noncomputable abbrev Theorem49RawSourceInKirchhoff {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color) :
    Submodule F2 (Theorem49BoundaryKirchhoffSubmodule emb) :=
  Submodule.comap (Theorem49BoundaryKirchhoffSubmodule emb).subtype
    (Theorem49RawSource emb C₀)

/-- The purified v23 Kirchhoff quotient modulo selected-boundary projection errors. -/
noncomputable abbrev Theorem49BoundaryQuotient {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)]
    (emb : PlaneEmbeddingWithBoundary G) : Type _ :=
  Theorem49BoundaryKirchhoffSubmodule emb ⧸ Theorem49BoundaryKernel emb

/-- The raw Definition 4.8 source quotient modulo selected-boundary projection errors. -/
noncomputable abbrev Theorem49RawSourceQuotient {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color) : Type _ :=
  Theorem49RawSource emb C₀ ⧸
    LinearMap.ker ((Theorem49BoundaryProjection emb).domRestrict (Theorem49RawSource emb C₀))

/-- A route-level synthesis of the currently proved Theorem 4.9 endpoint over the selected-
boundary-purified interior-edge endpoint carrier. The carrier is the already-established
`selectedBoundaryInteriorEdgeEndpointVertices`; this package deliberately adds no new carrier
construction.

The fields collect the algebraic consequences needed downstream: boundary-erased image, pointwise
separation, projected-generator spanning, kernel-zero and finite-dimensional forms, and the
corrected raw-source quotient/decomposition. -/
structure Theorem49BoundaryRootSynthesis {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)] [FiniteDimensional F2 (Theorem49EdgeSpace G)]
    (emb : PlaneEmbeddingWithBoundary G)
    (C₀ : G.EdgeColoring Color) : Prop where
  target_eq_boundaryProjectionImage :
    Theorem49BoundaryTarget emb =
      Submodule.map (Theorem49BoundaryProjection emb) (Theorem49BoundaryKirchhoffSubmodule emb)
  pointwise_separation :
    ∀ z : Theorem49BoundaryTarget emb,
      (∀ p ∈ Theorem49ProjectedGeneratorSubspace emb C₀,
        chainDotBilinForm G.edgeSet p (z : Theorem49EdgeSpace G) = 0) ↔
        z = 0
  pairing_ker_eq_bot :
    LinearMap.ker (Theorem49TargetPairingMap emb C₀) = ⊥
  finrank_le_projectedGeneratorSubspace :
    Module.finrank F2 (Theorem49BoundaryTarget emb) ≤
      Module.finrank F2 (Theorem49ProjectedGeneratorSubspace emb C₀)
  target_eq_projectedGeneratorSource :
    Theorem49BoundaryTarget emb =
      Theorem49BoundaryKirchhoffSubmodule emb ⊓
        Theorem49ProjectedGeneratorSubspace emb C₀
  target_le_projectedGeneratorSubspace :
    Theorem49BoundaryTarget emb ≤
      Theorem49ProjectedGeneratorSubspace emb C₀
  target_le_projectedGeneratorFamilySpan :
    Theorem49BoundaryTarget emb ≤
      Submodule.span F2 (Theorem49ProjectedGeneratorFamily emb C₀)
  target_eq_rawSourceImage :
    Theorem49BoundaryTarget emb =
      Submodule.map (Theorem49BoundaryProjection emb) (Theorem49RawSource emb C₀)
  projectedGeneratorRepresentation :
    ∀ {z : Theorem49EdgeSpace G},
      z ∈ Theorem49BoundaryTarget emb →
        ∃ (coeff : (Theorem49EdgeSpace G) → F2) (terms : Finset (Theorem49EdgeSpace G)),
          (terms : Set (Theorem49EdgeSpace G)) ⊆
              Theorem49ProjectedGeneratorFamily emb C₀ ∧
            coeff.support ⊆ terms ∧
              ∑ y ∈ terms, coeff y • y = z
  rawGeneratorProjectionRepresentation :
    ∀ {z : Theorem49EdgeSpace G},
      z ∈ Theorem49BoundaryTarget emb →
        ∃ (coeff : (Theorem49EdgeSpace G) → F2) (terms : Finset (Theorem49EdgeSpace G)),
          (terms : Set (Theorem49EdgeSpace G)) ⊆
              Theorem49RawGeneratorFamily emb C₀ ∧
            coeff.support ⊆ terms ∧
              (∑ y ∈ terms, coeff y • y) ∈
                  Theorem49BoundaryKirchhoffSubmodule emb ∧
                Theorem49BoundaryProjection emb (∑ y ∈ terms, coeff y • y) = z
  rawSourcePreimage :
    ∀ {z : Theorem49EdgeSpace G},
      z ∈ Theorem49BoundaryTarget emb →
        ∃ y ∈ Theorem49RawSource emb C₀, Theorem49BoundaryProjection emb y = z
  rawKirchhoffRepresentative :
    ∀ {x : Theorem49EdgeSpace G},
      x ∈ Theorem49BoundaryKirchhoffSubmodule emb →
        ∃ (coeff : (Theorem49EdgeSpace G) → F2) (terms : Finset (Theorem49EdgeSpace G)),
          (terms : Set (Theorem49EdgeSpace G)) ⊆
              Theorem49RawGeneratorFamily emb C₀ ∧
            coeff.support ⊆ terms ∧
              (∑ y ∈ terms, coeff y • y) ∈
                  Theorem49BoundaryKirchhoffSubmodule emb ∧
                Theorem49BoundaryProjection emb (∑ y ∈ terms, coeff y • y) =
                  Theorem49BoundaryProjection emb x
  rawBoundaryKernelDecomposition :
    ∀ {x : Theorem49EdgeSpace G},
      x ∈ Theorem49BoundaryKirchhoffSubmodule emb →
        ∃ (coeff : (Theorem49EdgeSpace G) → F2) (terms : Finset (Theorem49EdgeSpace G))
            (boundaryError : Theorem49EdgeSpace G),
          (terms : Set (Theorem49EdgeSpace G)) ⊆
              Theorem49RawGeneratorFamily emb C₀ ∧
            coeff.support ⊆ terms ∧
              (∑ y ∈ terms, coeff y • y) ∈
                  Theorem49BoundaryKirchhoffSubmodule emb ∧
                boundaryError ∈
                    Theorem49BoundaryKirchhoffSubmodule emb ⊓
                      LinearMap.ker (Theorem49BoundaryProjection emb) ∧
                  (∑ y ∈ terms, coeff y • y) + boundaryError = x ∧
                    Theorem49BoundaryProjection emb (∑ y ∈ terms, coeff y • y) =
                      Theorem49BoundaryProjection emb x

/-- At any completed theorem-4.9 synthesis surface, the whole purified Kirchhoff submodule
splits as raw Definition 4.8 Kempe-source chains plus selected-boundary-kernel errors.  This is
the submodule-level form of the finite raw quotient/error decomposition field: every Kirchhoff
chain is the sum of a Kirchhoff-valid raw generator-family combination and an error killed by the
selected-boundary projection, and both summands stay inside the purified Kirchhoff submodule. -/
theorem Theorem49BoundaryRootSynthesis.kirchhoffSubmodule_eq_rawSource_sup_boundaryKernel
    {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)] [FiniteDimensional F2 (Theorem49EdgeSpace G)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀) :
    Theorem49BoundaryKirchhoffSubmodule emb =
      Theorem49RawSource emb C₀ ⊔
        (Theorem49BoundaryKirchhoffSubmodule emb ⊓
          LinearMap.ker (Theorem49BoundaryProjection emb)) := by
  apply le_antisymm
  · intro x hx
    rcases h.rawBoundaryKernelDecomposition hx with
      ⟨coeff, terms, boundaryError, hterms, hsupport, hkirch, herror, hsum, _hproj⟩
    let raw : Theorem49EdgeSpace G := ∑ y ∈ terms, coeff y • y
    have hrawSpan :
        raw ∈ Theorem49RawGeneratorSubspace emb C₀ := by
      have hrawSpan' :
          raw ∈ Submodule.span F2 (Theorem49RawGeneratorFamily emb C₀) :=
        (Submodule.mem_span_iff_exists_finset_subset
          (R := F2) (s := Theorem49RawGeneratorFamily emb C₀) (x := raw)).2
          ⟨coeff, terms, hterms, hsupport, rfl⟩
      simpa [kempeClosureGeneratorSubspace, raw] using hrawSpan'
    have hrawLeft :
        raw ∈ Theorem49RawSource emb C₀ := by
      exact ⟨hrawSpan, by simpa [raw] using hkirch⟩
    exact
      (Submodule.mem_sup).2
        ⟨raw, hrawLeft, boundaryError, herror, by simpa [raw] using hsum⟩
  · exact sup_le inf_le_right inf_le_left

/-- Quotient form of the raw-source/error decomposition.  Inside the purified Kirchhoff
submodule, quotienting by the selected-boundary kernel error makes the Kirchhoff-valid raw
Definition 4.8 source span all quotient classes. -/
theorem Theorem49BoundaryRootSynthesis.rawSource_mkQ_eq_top
    {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)] [FiniteDimensional F2 (Theorem49EdgeSpace G)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀) :
    Submodule.map (Submodule.mkQ (Theorem49BoundaryKernel emb))
        (Theorem49RawSourceInKirchhoff emb C₀) =
      ⊤ := by
  let boundary : Finset (Theorem49EdgeCarrier G) :=
    selectedBoundarySupport emb.faceBoundary emb.faces emb.faces
  let K : Submodule F2 (Theorem49EdgeSpace G) :=
    Theorem49BoundaryKirchhoffSubmodule emb
  let R : Submodule F2 (Theorem49EdgeSpace G) :=
    Theorem49RawSource emb C₀
  let BQ : Submodule F2 K :=
    LinearMap.ker ((boundaryZeroProjection boundary).domRestrict K)
  let RQ : Submodule F2 K := Submodule.comap K.subtype R
  change Submodule.map (Submodule.mkQ BQ) RQ = ⊤
  rw [Submodule.map_mkQ_eq_top]
  apply le_antisymm
  · exact le_top
  · intro x _hx
    have hxSup :
        (x : Theorem49EdgeSpace G) ∈
          R ⊔ (K ⊓ LinearMap.ker (boundaryZeroProjection boundary)) := by
      have hxK :
          (x : Theorem49EdgeSpace G) ∈
            Theorem49BoundaryKirchhoffSubmodule emb := by
        change (x : Theorem49EdgeSpace G) ∈ K
        exact x.property
      change
        (x : Theorem49EdgeSpace G) ∈
          Theorem49RawSource emb C₀ ⊔
            (Theorem49BoundaryKirchhoffSubmodule emb ⊓
              LinearMap.ker (Theorem49BoundaryProjection emb))
      rw [← h.kirchhoffSubmodule_eq_rawSource_sup_boundaryKernel]
      exact hxK
    rcases (Submodule.mem_sup).1 hxSup with ⟨raw, hraw, boundaryError, herror, hsum⟩
    have hrawK : raw ∈ K := hraw.2
    have herrorK : boundaryError ∈ K := herror.1
    have herrorBQ : (⟨boundaryError, herrorK⟩ : K) ∈ BQ := by
      change boundaryZeroProjection boundary boundaryError = 0
      exact herror.2
    have hrawRQ : (⟨raw, hrawK⟩ : K) ∈ RQ := by
      change raw ∈ R
      exact hraw
    exact
      (Submodule.mem_sup).2
        ⟨⟨boundaryError, herrorK⟩, herrorBQ, ⟨raw, hrawK⟩, hrawRQ,
          Subtype.ext (by
            change boundaryError + raw = (x : Theorem49EdgeSpace G)
            rw [add_comm]
            exact hsum)⟩

/-- Dimension consequence of the raw quotient surjectivity: the selected-boundary quotient of the
purified Kirchhoff submodule has dimension bounded by the Kirchhoff-valid raw Definition 4.8
source submodule inside it. -/
theorem Theorem49BoundaryRootSynthesis.finrank_quotient_le_rawSource
    {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)] [FiniteDimensional F2 (Theorem49EdgeSpace G)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀) :
    Module.finrank F2
        (Theorem49BoundaryKirchhoffSubmodule emb ⧸ Theorem49BoundaryKernel emb) ≤
      Module.finrank F2 (Theorem49RawSourceInKirchhoff emb C₀) := by
  have htop :
      Submodule.map (Submodule.mkQ (Theorem49BoundaryKernel emb))
          (Theorem49RawSourceInKirchhoff emb C₀) = ⊤ :=
    h.rawSource_mkQ_eq_top
  calc
    Module.finrank F2
        (Theorem49BoundaryKirchhoffSubmodule emb ⧸ Theorem49BoundaryKernel emb)
        = Module.finrank F2
            (⊤ : Submodule F2
              (Theorem49BoundaryKirchhoffSubmodule emb ⧸ Theorem49BoundaryKernel emb)) := by
          rw [finrank_top]
    _ = Module.finrank F2
          (Submodule.map (Submodule.mkQ (Theorem49BoundaryKernel emb))
            (Theorem49RawSourceInKirchhoff emb C₀)) := by
          rw [htop]
    _ ≤ Module.finrank F2 (Theorem49RawSourceInKirchhoff emb C₀) :=
          Submodule.finrank_map_le
            (Submodule.mkQ (Theorem49BoundaryKernel emb))
            (Theorem49RawSourceInKirchhoff emb C₀)

/-- Target-dimension consequence of the corrected raw-source image: the concrete boundary-zero
Kirchhoff target has dimension bounded by the Kirchhoff-valid raw Definition 4.8 source submodule
that maps onto it. -/
theorem Theorem49BoundaryRootSynthesis.finrank_target_le_rawSource
    {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)] [FiniteDimensional F2 (Theorem49EdgeSpace G)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀) :
    Module.finrank F2 (Theorem49BoundaryTarget emb) ≤
      Module.finrank F2 (Theorem49RawSource emb C₀) := by
  rw [h.target_eq_rawSourceImage]
  exact Submodule.finrank_map_le (Theorem49BoundaryProjection emb) (Theorem49RawSource emb C₀)

/-- First-isomorphism form carried by the synthesis surface itself: the purified Kirchhoff
submodule modulo the selected-boundary projection kernel is linearly equivalent to the concrete
boundary-zero Kirchhoff target. -/
noncomputable def Theorem49BoundaryRootSynthesis.boundaryProjectionQuotientEquivTarget
    {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)] [FiniteDimensional F2 (Theorem49EdgeSpace G)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀) :
    Theorem49BoundaryQuotient emb ≃ₗ[F2] Theorem49BoundaryTarget emb :=
  (boundaryZeroProjectionKirchhoffQuotientEquivImage
      (G := G)
      (Theorem49BoundarySupport emb)
      (Theorem49BoundaryVertices emb)).trans
    (LinearEquiv.ofEq _ _ h.target_eq_boundaryProjectionImage.symm)

/-- The synthesis-surface quotient equivalence sends the quotient class of a purified Kirchhoff
chain to its selected-boundary-erased chain in the concrete theorem-4.9 target. -/
theorem Theorem49BoundaryRootSynthesis.boundaryProjectionQuotientEquivTarget_apply_mk
    {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)] [FiniteDimensional F2 (Theorem49EdgeSpace G)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀)
    (x : Theorem49BoundaryKirchhoffSubmodule emb) :
    ((h.boundaryProjectionQuotientEquivTarget (Submodule.Quotient.mk x) :
        Theorem49BoundaryTarget emb) :
        Theorem49EdgeSpace G) =
      Theorem49BoundaryProjection emb (x : Theorem49EdgeSpace G) := by
  rw [Theorem49BoundaryRootSynthesis.boundaryProjectionQuotientEquivTarget]
  simp [boundaryZeroProjectionKirchhoffQuotientEquivImage_apply_mk]

/-- The projected-generator pairing map transported from the concrete theorem-4.9 target to the
purified Kirchhoff quotient.  It pairs a quotient class with projected Definition 4.8 generators
after selected-boundary erasure. -/
noncomputable def Theorem49BoundaryRootSynthesis.kirchhoffQuotientProjectedGeneratorPairingMap
    {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)] [FiniteDimensional F2 (Theorem49EdgeSpace G)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀) :
    Theorem49BoundaryQuotient emb →ₗ[F2] Theorem49ProjectedGeneratorDual emb C₀ :=
  (Theorem49TargetPairingMap emb C₀).comp h.boundaryProjectionQuotientEquivTarget.toLinearMap

/-- On a quotient class represented by a purified Kirchhoff chain, the quotient pairing map is
computed by selected-boundary erasure followed by the chain-dot pairing with a projected
Definition 4.8 generator. -/
theorem Theorem49BoundaryRootSynthesis.kirchhoffQuotientProjectedGeneratorPairingMap_apply_mk
    {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)] [FiniteDimensional F2 (Theorem49EdgeSpace G)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀)
    (x : Theorem49BoundaryKirchhoffSubmodule emb)
    (p : Theorem49ProjectedGeneratorSubspace emb C₀) :
    h.kirchhoffQuotientProjectedGeneratorPairingMap (Submodule.Quotient.mk x) p =
      chainDotBilinForm G.edgeSet (p : Theorem49EdgeSpace G)
        (Theorem49BoundaryProjection emb (x : Theorem49EdgeSpace G)) := by
  rw [Theorem49BoundaryRootSynthesis.kirchhoffQuotientProjectedGeneratorPairingMap]
  change
    chainDotBilinForm G.edgeSet (p : Theorem49EdgeSpace G)
        ((h.boundaryProjectionQuotientEquivTarget (Submodule.Quotient.mk x) :
          Theorem49BoundaryTarget emb) :
          Theorem49EdgeSpace G) =
      chainDotBilinForm G.edgeSet (p : Theorem49EdgeSpace G)
        (Theorem49BoundaryProjection emb (x : Theorem49EdgeSpace G))
  rw [Theorem49BoundaryRootSynthesis.boundaryProjectionQuotientEquivTarget_apply_mk]

/-- The quotient-level projected-generator pairing has trivial kernel at any completed
theorem-4.9 synthesis surface. -/
theorem Theorem49BoundaryRootSynthesis.ker_kirchhoffQuotientProjectedGeneratorPairingMap_eq_bot
    {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)] [FiniteDimensional F2 (Theorem49EdgeSpace G)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀) :
    LinearMap.ker h.kirchhoffQuotientProjectedGeneratorPairingMap = ⊥ := by
  apply le_antisymm
  · intro q hq
    have hz_mem :
        h.boundaryProjectionQuotientEquivTarget q ∈
          LinearMap.ker (Theorem49TargetPairingMap emb C₀) := by
      change Theorem49TargetPairingMap emb C₀ (h.boundaryProjectionQuotientEquivTarget q) = 0
      change
        (Theorem49TargetPairingMap emb C₀).comp
            h.boundaryProjectionQuotientEquivTarget.toLinearMap q = 0 at hq
      exact hq
    have hz_zero : h.boundaryProjectionQuotientEquivTarget q = 0 := by
      have hz_bot :
          h.boundaryProjectionQuotientEquivTarget q ∈
            (⊥ : Submodule F2 (Theorem49BoundaryTarget emb)) := by
        rw [← h.pairing_ker_eq_bot]
        exact hz_mem
      simpa using hz_bot
    have hq_zero : q = 0 :=
      h.boundaryProjectionQuotientEquivTarget.injective (by simpa using hz_zero)
    simpa using hq_zero
  · exact bot_le

/-- Quotient-level nondegeneracy in linear-map form: the projected-generator pairing map
vanishes on a purified Kirchhoff quotient class exactly when that quotient class is zero. -/
theorem Theorem49BoundaryRootSynthesis.kirchhoffQuotientProjectedGeneratorPairingMap_eq_zero_iff
    {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)] [FiniteDimensional F2 (Theorem49EdgeSpace G)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀)
    (q : Theorem49BoundaryQuotient emb) :
    h.kirchhoffQuotientProjectedGeneratorPairingMap q = 0 ↔ q = 0 := by
  constructor
  · intro hq
    have hqKer : q ∈ LinearMap.ker h.kirchhoffQuotientProjectedGeneratorPairingMap := hq
    have hqBot :
        q ∈ (⊥ : Submodule F2 (Theorem49BoundaryQuotient emb)) := by
      simpa [h.ker_kirchhoffQuotientProjectedGeneratorPairingMap_eq_bot] using hqKer
    simpa using hqBot
  · intro hq
    simp [hq]

/-- Any nonzero purified Kirchhoff quotient class is detected by evaluating the quotient-level
pairing map at some projected Definition 4.8 generator. -/
theorem Theorem49BoundaryRootSynthesis.exists_projectedGenerator_pairingMap_ne_zero_of_ne_zero_kirchhoffQuotientClass
    {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)] [FiniteDimensional F2 (Theorem49EdgeSpace G)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀)
    (q : Theorem49BoundaryQuotient emb)
    (hq : q ≠ 0) :
    ∃ p : Theorem49ProjectedGeneratorSubspace emb C₀,
      h.kirchhoffQuotientProjectedGeneratorPairingMap q p ≠ 0 := by
  have hmap_ne : h.kirchhoffQuotientProjectedGeneratorPairingMap q ≠ 0 := by
    intro hzero
    exact hq ((h.kirchhoffQuotientProjectedGeneratorPairingMap_eq_zero_iff q).1 hzero)
  by_contra hnone
  apply hmap_ne
  ext p
  by_contra hp
  exact hnone ⟨p, hp⟩

/-- Dimension consequence of the quotient-level projected-generator pairing: once the pairing
map on the purified Kirchhoff quotient has trivial kernel, the quotient dimension is bounded by
the projected Definition 4.8 generator subspace itself. -/
theorem Theorem49BoundaryRootSynthesis.finrank_kirchhoffQuotient_le_projectedGeneratorSubspace
    {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)] [FiniteDimensional F2 (Theorem49EdgeSpace G)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀) :
    Module.finrank F2 (Theorem49BoundaryQuotient emb) ≤
      Module.finrank F2 (Theorem49ProjectedGeneratorSubspace emb C₀) := by
  let L := h.kirchhoffQuotientProjectedGeneratorPairingMap
  have hker : LinearMap.ker L = ⊥ := by
    simpa [L] using h.ker_kirchhoffQuotientProjectedGeneratorPairingMap_eq_bot
  have hinj : Function.Injective L := (LinearMap.ker_eq_bot).1 hker
  have hleDual :
      Module.finrank F2 (Theorem49BoundaryQuotient emb) ≤
        Module.finrank F2 (Theorem49ProjectedGeneratorDual emb C₀) :=
    LinearMap.finrank_le_finrank_of_injective (f := L) hinj
  simpa [L, Module.Dual] using
    hleDual.trans_eq
      (Subspace.dual_finrank_eq
        (K := F2) (V := Theorem49ProjectedGeneratorSubspace emb C₀))

/-- The image of the quotient-level projected-generator pairing map has exactly the dimension
of the purified Kirchhoff quotient.  This identifies the quotient with a concrete subspace of
the dual of the projected Definition 4.8 generator subspace. -/
theorem Theorem49BoundaryRootSynthesis.finrank_range_kirchhoffQuotientProjectedGeneratorPairingMap
    {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)] [FiniteDimensional F2 (Theorem49EdgeSpace G)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀) :
    Module.finrank F2 (LinearMap.range h.kirchhoffQuotientProjectedGeneratorPairingMap) =
      Module.finrank F2 (Theorem49BoundaryQuotient emb) := by
  let L := h.kirchhoffQuotientProjectedGeneratorPairingMap
  have hker : LinearMap.ker L = ⊥ := by
    simpa [L] using h.ker_kirchhoffQuotientProjectedGeneratorPairingMap_eq_bot
  have hinj : Function.Injective L := (LinearMap.ker_eq_bot).1 hker
  simpa [L] using (LinearMap.finrank_range_of_inj (f := L) hinj)

/-- The purified Kirchhoff quotient is linearly equivalent to the image of its quotient-level
projected-generator pairing map.  This makes the pairing-map image the concrete dual-subspace
model of the quotient/error surface. -/
noncomputable def Theorem49BoundaryRootSynthesis.kirchhoffQuotientEquivPairingMapRange
    {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)] [FiniteDimensional F2 (Theorem49EdgeSpace G)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀) :
    Theorem49BoundaryQuotient emb ≃ₗ[F2]
      LinearMap.range h.kirchhoffQuotientProjectedGeneratorPairingMap := by
  let L := h.kirchhoffQuotientProjectedGeneratorPairingMap
  have hker : LinearMap.ker L = ⊥ := by
    simpa [L] using h.ker_kirchhoffQuotientProjectedGeneratorPairingMap_eq_bot
  exact LinearEquiv.ofInjective L ((LinearMap.ker_eq_bot).1 hker)

/-- The range equivalence sends a purified quotient class to the corresponding
projected-generator functional in the pairing-map image. -/
theorem Theorem49BoundaryRootSynthesis.kirchhoffQuotientEquivPairingMapRange_apply
    {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)] [FiniteDimensional F2 (Theorem49EdgeSpace G)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀)
    (q : Theorem49BoundaryQuotient emb) :
    (h.kirchhoffQuotientEquivPairingMapRange q : Theorem49ProjectedGeneratorDual emb C₀) =
      h.kirchhoffQuotientProjectedGeneratorPairingMap q := by
  rw [Theorem49BoundaryRootSynthesis.kirchhoffQuotientEquivPairingMapRange]
  rfl

/-- On quotient classes represented by purified Kirchhoff chains, the range equivalence is still
computed by selected-boundary erasure followed by the chain-dot pairing with projected
Definition 4.8 generators. -/
theorem Theorem49BoundaryRootSynthesis.kirchhoffQuotientEquivPairingMapRange_apply_mk
    {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)] [FiniteDimensional F2 (Theorem49EdgeSpace G)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀)
    (x : Theorem49BoundaryKirchhoffSubmodule emb)
    (p : Theorem49ProjectedGeneratorSubspace emb C₀) :
    (h.kirchhoffQuotientEquivPairingMapRange (Submodule.Quotient.mk x) :
        Theorem49ProjectedGeneratorDual emb C₀) p =
      chainDotBilinForm G.edgeSet (p : Theorem49EdgeSpace G)
        (Theorem49BoundaryProjection emb (x : Theorem49EdgeSpace G)) := by
  rw [Theorem49BoundaryRootSynthesis.kirchhoffQuotientEquivPairingMapRange_apply]
  exact h.kirchhoffQuotientProjectedGeneratorPairingMap_apply_mk x p

/-- Raw-source first-isomorphism form carried by the synthesis surface: the Kirchhoff-valid raw
Definition 4.8 source submodule modulo the selected-boundary projection kernel is linearly
equivalent to the concrete boundary-zero Kirchhoff target. -/
noncomputable def Theorem49BoundaryRootSynthesis.rawSourceQuotientEquivTarget
    {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)] [FiniteDimensional F2 (Theorem49EdgeSpace G)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀) :
    Theorem49RawSourceQuotient emb C₀ ≃ₗ[F2] Theorem49BoundaryTarget emb :=
  (boundaryZeroProjectionSubmoduleQuotientEquivImage
      (Theorem49BoundarySupport emb)
      (Theorem49RawSource emb C₀)).trans
    (LinearEquiv.ofEq _ _ h.target_eq_rawSourceImage.symm)

/-- The raw-source quotient equivalence sends the class of a Kirchhoff-valid raw source chain to
its selected-boundary-erased chain in the concrete theorem-4.9 target. -/
theorem Theorem49BoundaryRootSynthesis.rawSourceQuotientEquivTarget_apply_mk
    {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)] [FiniteDimensional F2 (Theorem49EdgeSpace G)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀)
    (x : Theorem49RawSource emb C₀) :
    ((h.rawSourceQuotientEquivTarget (Submodule.Quotient.mk x) :
        Theorem49BoundaryTarget emb) :
        Theorem49EdgeSpace G) =
      Theorem49BoundaryProjection emb (x : Theorem49EdgeSpace G) := by
  rw [Theorem49BoundaryRootSynthesis.rawSourceQuotientEquivTarget]
  simp [boundaryZeroProjectionSubmoduleQuotientEquivImage_apply_mk]

/-- The raw-source quotient and the purified Kirchhoff quotient are linearly equivalent at any
completed synthesis surface.  This is the inclusion of the raw Definition 4.8 source modulo
selected-boundary error, expressed through the common concrete theorem-4.9 target. -/
noncomputable def Theorem49BoundaryRootSynthesis.rawSourceQuotientEquivKirchhoffQuotient
    {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)] [FiniteDimensional F2 (Theorem49EdgeSpace G)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀) :
    Theorem49RawSourceQuotient emb C₀ ≃ₗ[F2] Theorem49BoundaryQuotient emb :=
  h.rawSourceQuotientEquivTarget.trans h.boundaryProjectionQuotientEquivTarget.symm

/-- Under the quotient bridge from the raw source quotient to the purified Kirchhoff quotient, a
raw Kirchhoff-valid source representative is sent to the same chain regarded as a purified
Kirchhoff quotient representative. -/
theorem Theorem49BoundaryRootSynthesis.rawSourceQuotientEquivKirchhoffQuotient_apply_mk
    {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)] [FiniteDimensional F2 (Theorem49EdgeSpace G)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀)
    (x : Theorem49RawSource emb C₀) :
    h.rawSourceQuotientEquivKirchhoffQuotient (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (⟨(x : Theorem49EdgeSpace G), x.property.2⟩ :
          Theorem49BoundaryKirchhoffSubmodule emb) := by
  apply h.boundaryProjectionQuotientEquivTarget.injective
  apply Subtype.ext
  simp [Theorem49BoundaryRootSynthesis.rawSourceQuotientEquivKirchhoffQuotient,
    Theorem49BoundaryRootSynthesis.rawSourceQuotientEquivTarget_apply_mk,
    Theorem49BoundaryRootSynthesis.boundaryProjectionQuotientEquivTarget_apply_mk]

/-- The raw Definition 4.8 source quotient has the same concrete pairing-map image model as the
purified Kirchhoff quotient.  This is the direct quotient/error-to-dual-subspace bridge: a raw
Kirchhoff-valid source class modulo selected-boundary error is represented as a functional in the
image of the quotient-level projected-generator pairing map. -/
noncomputable def Theorem49BoundaryRootSynthesis.rawSourceQuotientEquivPairingMapRange
    {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)] [FiniteDimensional F2 (Theorem49EdgeSpace G)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀) :
    Theorem49RawSourceQuotient emb C₀ ≃ₗ[F2]
      LinearMap.range h.kirchhoffQuotientProjectedGeneratorPairingMap :=
  h.rawSourceQuotientEquivKirchhoffQuotient.trans h.kirchhoffQuotientEquivPairingMapRange

/-- On raw-source quotient classes, the direct image model is computed by selected-boundary
erasure followed by the chain-dot pairing with projected Definition 4.8 generators. -/
theorem Theorem49BoundaryRootSynthesis.rawSourceQuotientEquivPairingMapRange_apply_mk
    {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)] [FiniteDimensional F2 (Theorem49EdgeSpace G)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀)
    (x : Theorem49RawSource emb C₀)
    (p : Theorem49ProjectedGeneratorSubspace emb C₀) :
    (h.rawSourceQuotientEquivPairingMapRange (Submodule.Quotient.mk x) :
        Theorem49ProjectedGeneratorDual emb C₀) p =
      chainDotBilinForm G.edgeSet (p : Theorem49EdgeSpace G)
        (Theorem49BoundaryProjection emb (x : Theorem49EdgeSpace G)) := by
  simpa [Theorem49BoundaryRootSynthesis.rawSourceQuotientEquivPairingMapRange,
    Theorem49BoundaryRootSynthesis.rawSourceQuotientEquivKirchhoffQuotient_apply_mk]
    using
      (h.kirchhoffQuotientEquivPairingMapRange_apply_mk
        (⟨(x : Theorem49EdgeSpace G), x.property.2⟩ :
          Theorem49BoundaryKirchhoffSubmodule emb) p)

/-- The raw Definition 4.8 source quotient has exactly the dimension of the concrete
pairing-map image.  This is the finite-dimensional shadow of the direct raw-source
quotient/error-to-dual-subspace model. -/
theorem Theorem49BoundaryRootSynthesis.finrank_rawSourceQuotient_eq_pairingMapRange
    {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)] [FiniteDimensional F2 (Theorem49EdgeSpace G)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀) :
    Module.finrank F2 (Theorem49RawSourceQuotient emb C₀) =
      Module.finrank F2 (LinearMap.range h.kirchhoffQuotientProjectedGeneratorPairingMap) := by
  simpa using h.rawSourceQuotientEquivPairingMapRange.finrank_eq

/-- The raw Definition 4.8 source quotient is bounded by the projected Definition 4.8 generator
subspace.  Unlike the earlier ambient raw-source bound, this consequence factors through the
pairing-map image and the purified quotient's nondegenerate projected-generator pairing. -/
theorem Theorem49BoundaryRootSynthesis.finrank_rawSourceQuotient_le_projectedGeneratorSubspace
    {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)] [FiniteDimensional F2 (Theorem49EdgeSpace G)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀) :
    Module.finrank F2 (Theorem49RawSourceQuotient emb C₀) ≤
      Module.finrank F2 (Theorem49ProjectedGeneratorSubspace emb C₀) := by
  calc
    Module.finrank F2 (Theorem49RawSourceQuotient emb C₀)
        = Module.finrank F2
            (LinearMap.range h.kirchhoffQuotientProjectedGeneratorPairingMap) :=
          h.finrank_rawSourceQuotient_eq_pairingMapRange
    _ = Module.finrank F2
          (Theorem49BoundaryQuotient emb) :=
          h.finrank_range_kirchhoffQuotientProjectedGeneratorPairingMap
    _ ≤ Module.finrank F2 (Theorem49ProjectedGeneratorSubspace emb C₀) :=
          h.finrank_kirchhoffQuotient_le_projectedGeneratorSubspace

/-- Every purified Kirchhoff quotient class has a finite raw Definition 4.8 generator-sum
representative.  The representative is a Kirchhoff-valid raw source chain, and it represents the
same class modulo the selected-boundary projection kernel as the original purified Kirchhoff
chain. -/
theorem Theorem49BoundaryRootSynthesis.exists_rawGeneratorSum_for_kirchhoffQuotientClass
    {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)] [FiniteDimensional F2 (Theorem49EdgeSpace G)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀)
    (x : Theorem49BoundaryKirchhoffSubmodule emb) :
    ∃ (raw : Theorem49RawSource emb C₀)
        (coeff : (Theorem49EdgeSpace G) → F2) (terms : Finset (Theorem49EdgeSpace G)),
      (terms : Set (Theorem49EdgeSpace G)) ⊆
          Theorem49RawGeneratorFamily emb C₀ ∧
        coeff.support ⊆ terms ∧
          (∑ y ∈ terms, coeff y • y) = (raw : Theorem49EdgeSpace G) ∧
            (Submodule.Quotient.mk
                (⟨(raw : Theorem49EdgeSpace G), raw.property.2⟩ :
                  Theorem49BoundaryKirchhoffSubmodule emb) :
              Theorem49BoundaryQuotient emb) =
              Submodule.Quotient.mk x := by
  rcases h.rawKirchhoffRepresentative x.property with
    ⟨coeff, terms, hterms, hsupport, hrawKirch, hproj⟩
  let rawChain : Theorem49EdgeSpace G := ∑ y ∈ terms, coeff y • y
  have hrawSpan :
      rawChain ∈ Theorem49RawGeneratorSubspace emb C₀ := by
    have hrawSpan' :
        rawChain ∈ Submodule.span F2 (Theorem49RawGeneratorFamily emb C₀) :=
      (Submodule.mem_span_iff_exists_finset_subset
        (R := F2) (s := Theorem49RawGeneratorFamily emb C₀)
        (x := rawChain)).2
        ⟨coeff, terms, hterms, hsupport, rfl⟩
    simpa [kempeClosureGeneratorSubspace, rawChain] using hrawSpan'
  let raw : Theorem49RawSource emb C₀ :=
    ⟨rawChain, hrawSpan, by simpa [rawChain] using hrawKirch⟩
  refine ⟨raw, coeff, terms, hterms, hsupport, by simp [raw, rawChain], ?_⟩
  exact
    (boundaryZeroProjectionSubmoduleQuotient_mk_eq_mk_iff
      (boundary := selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
      (S := kirchhoffSubmodule G
        (selectedBoundaryInteriorEdgeEndpointVertices emb))).2
      (by simpa [raw, rawChain] using hproj)

/-- Quotient-class form of the theorem-4.9 separation endpoint: a purified Kirchhoff quotient
class is zero exactly when its selected-boundary-erased representative pairs to zero with every
projected Definition 4.8 generator. -/
theorem Theorem49BoundaryRootSynthesis.kirchhoffQuotientClass_eq_zero_iff_projectedGenerator_orthogonal
    {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)] [FiniteDimensional F2 (Theorem49EdgeSpace G)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀)
    (x : Theorem49BoundaryKirchhoffSubmodule emb) :
    (Submodule.Quotient.mk x : Theorem49BoundaryQuotient emb) = 0 ↔
      ∀ p ∈ Theorem49ProjectedGeneratorSubspace emb C₀,
        chainDotBilinForm G.edgeSet p
          (Theorem49BoundaryProjection emb (x : Theorem49EdgeSpace G)) = 0 := by
  let q : Theorem49BoundaryQuotient emb := Submodule.Quotient.mk x
  let z : Theorem49BoundaryTarget emb :=
    h.boundaryProjectionQuotientEquivTarget q
  constructor
  · intro hq p hp
    have hz : z = 0 := by
      simp [z, q, hq]
    have horth := (h.pointwise_separation z).2 hz
    simpa [z, q,
      Theorem49BoundaryRootSynthesis.boundaryProjectionQuotientEquivTarget_apply_mk]
      using horth p hp
  · intro horth
    have horthTarget :
        ∀ p ∈ Theorem49ProjectedGeneratorSubspace emb C₀,
          chainDotBilinForm G.edgeSet p (z : Theorem49EdgeSpace G) = 0 := by
      intro p hp
      simpa [z, q,
        Theorem49BoundaryRootSynthesis.boundaryProjectionQuotientEquivTarget_apply_mk]
        using horth p hp
    have hz : z = 0 := (h.pointwise_separation z).1 horthTarget
    apply h.boundaryProjectionQuotientEquivTarget.injective
    simpa [z, q] using hz

/-- Nonzero purified Kirchhoff quotient classes are detected by a projected Definition 4.8
generator after selected-boundary erasure. -/
theorem Theorem49BoundaryRootSynthesis.exists_projectedGenerator_chainDot_ne_zero_of_ne_zero_kirchhoffQuotientClass
    {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)] [FiniteDimensional F2 (Theorem49EdgeSpace G)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀)
    (x : Theorem49BoundaryKirchhoffSubmodule emb)
    (hx : (Submodule.Quotient.mk x : Theorem49BoundaryQuotient emb) ≠ 0) :
    ∃ p ∈ Theorem49ProjectedGeneratorSubspace emb C₀,
      chainDotBilinForm G.edgeSet p
        (Theorem49BoundaryProjection emb (x : Theorem49EdgeSpace G)) ≠ 0 := by
  by_contra hnone
  have horth :
      ∀ p ∈ Theorem49ProjectedGeneratorSubspace emb C₀,
        chainDotBilinForm G.edgeSet p
          (Theorem49BoundaryProjection emb (x : Theorem49EdgeSpace G)) = 0 := by
    intro p hp
    by_contra hne
    exact hnone ⟨p, hp, hne⟩
  exact hx
    ((h.kirchhoffQuotientClass_eq_zero_iff_projectedGenerator_orthogonal x).2 horth)

/-- A raw-source quotient class vanishes exactly when the same representative, viewed in the
purified Kirchhoff quotient, vanishes. -/
theorem Theorem49BoundaryRootSynthesis.rawSourceQuotientClass_eq_zero_iff_kirchhoffQuotientClass_eq_zero
    {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)] [FiniteDimensional F2 (Theorem49EdgeSpace G)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀)
    (x : Theorem49RawSource emb C₀) :
    (Submodule.Quotient.mk x : Theorem49RawSourceQuotient emb C₀) = 0 ↔
      (Submodule.Quotient.mk
        (⟨(x : Theorem49EdgeSpace G), x.property.2⟩ :
          Theorem49BoundaryKirchhoffSubmodule emb) :
        Theorem49BoundaryQuotient emb) = 0 := by
  constructor
  · intro hxZero
    have hmap :
        h.rawSourceQuotientEquivKirchhoffQuotient (Submodule.Quotient.mk x) = 0 :=
      (LinearEquiv.map_eq_zero_iff h.rawSourceQuotientEquivKirchhoffQuotient).2 hxZero
    simpa [Theorem49BoundaryRootSynthesis.rawSourceQuotientEquivKirchhoffQuotient_apply_mk]
      using hmap
  · intro hxKirchZero
    have hmap :
        h.rawSourceQuotientEquivKirchhoffQuotient (Submodule.Quotient.mk x) = 0 := by
      simpa [Theorem49BoundaryRootSynthesis.rawSourceQuotientEquivKirchhoffQuotient_apply_mk]
        using hxKirchZero
    exact (LinearEquiv.map_eq_zero_iff h.rawSourceQuotientEquivKirchhoffQuotient).1 hmap

/-- Raw-source quotient-class separation: a Kirchhoff-valid raw Definition 4.8 source class
modulo selected-boundary error is zero exactly when its selected-boundary-erased representative
pairs trivially with every projected Definition 4.8 generator. -/
theorem Theorem49BoundaryRootSynthesis.rawSourceQuotientClass_eq_zero_iff_projectedGenerator_orthogonal
    {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)] [FiniteDimensional F2 (Theorem49EdgeSpace G)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀)
    (x : Theorem49RawSource emb C₀) :
    (Submodule.Quotient.mk x : Theorem49RawSourceQuotient emb C₀) = 0 ↔
      ∀ p ∈ Theorem49ProjectedGeneratorSubspace emb C₀,
        chainDotBilinForm G.edgeSet p
          (Theorem49BoundaryProjection emb (x : Theorem49EdgeSpace G)) = 0 := by
  let xKirch : Theorem49BoundaryKirchhoffSubmodule emb :=
    ⟨(x : Theorem49EdgeSpace G), x.property.2⟩
  have hiff :=
    h.kirchhoffQuotientClass_eq_zero_iff_projectedGenerator_orthogonal xKirch
  have hbridge :=
    h.rawSourceQuotientClass_eq_zero_iff_kirchhoffQuotientClass_eq_zero x
  constructor
  · intro hxZero
    have hxKirchZero :
        (Submodule.Quotient.mk xKirch : Theorem49BoundaryQuotient emb) = 0 := by
      simpa [xKirch] using hbridge.1 hxZero
    simpa [xKirch] using hiff.1 hxKirchZero
  · intro horth
    have hxKirchZero :
        (Submodule.Quotient.mk xKirch : Theorem49BoundaryQuotient emb) = 0 := by
      exact hiff.2 (by simpa [xKirch] using horth)
    exact hbridge.2 (by simpa [xKirch] using hxKirchZero)

/-- Nonzero raw-source quotient classes are detected by some projected Definition 4.8 generator
after selected-boundary erasure. -/
theorem Theorem49BoundaryRootSynthesis.exists_projectedGenerator_chainDot_ne_zero_of_ne_zero_rawSourceQuotientClass
    {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)] [FiniteDimensional F2 (Theorem49EdgeSpace G)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀)
    (x : Theorem49RawSource emb C₀)
    (hx : (Submodule.Quotient.mk x : Theorem49RawSourceQuotient emb C₀) ≠ 0) :
    ∃ p ∈ Theorem49ProjectedGeneratorSubspace emb C₀,
      chainDotBilinForm G.edgeSet p
        (Theorem49BoundaryProjection emb (x : Theorem49EdgeSpace G)) ≠ 0 := by
  by_contra hnone
  have horth :
      ∀ p ∈ Theorem49ProjectedGeneratorSubspace emb C₀,
        chainDotBilinForm G.edgeSet p
          (Theorem49BoundaryProjection emb (x : Theorem49EdgeSpace G)) = 0 := by
    intro p hp
    by_contra hne
    exact hnone ⟨p, hp, hne⟩
  exact hx
    ((h.rawSourceQuotientClass_eq_zero_iff_projectedGenerator_orthogonal x).2 horth)

/-- A nonzero purified Kirchhoff quotient class has a finite raw generator-sum representative
that is itself detected by a projected Definition 4.8 generator.  This combines the
representative endpoint with quotient-level separation, so downstream arguments can work with a
raw finite source representative without losing the nonzero projected-pairing witness. -/
theorem Theorem49BoundaryRootSynthesis.exists_rawGeneratorSum_and_projectedGenerator_chainDot_ne_zero_of_ne_zero_kirchhoffQuotientClass
    {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)] [FiniteDimensional F2 (Theorem49EdgeSpace G)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀)
    (x : Theorem49BoundaryKirchhoffSubmodule emb)
    (hx : (Submodule.Quotient.mk x : Theorem49BoundaryQuotient emb) ≠ 0) :
    ∃ (raw : Theorem49RawSource emb C₀)
        (coeff : (Theorem49EdgeSpace G) → F2) (terms : Finset (Theorem49EdgeSpace G))
        (p : Theorem49EdgeSpace G),
      (terms : Set (Theorem49EdgeSpace G)) ⊆
          Theorem49RawGeneratorFamily emb C₀ ∧
        coeff.support ⊆ terms ∧
          (∑ y ∈ terms, coeff y • y) = (raw : Theorem49EdgeSpace G) ∧
            (Submodule.Quotient.mk
                (⟨(raw : Theorem49EdgeSpace G), raw.property.2⟩ :
                  Theorem49BoundaryKirchhoffSubmodule emb) :
              Theorem49BoundaryQuotient emb) =
              Submodule.Quotient.mk x ∧
            p ∈ Theorem49ProjectedGeneratorSubspace emb C₀ ∧
              chainDotBilinForm G.edgeSet p
                (Theorem49BoundaryProjection emb (raw : Theorem49EdgeSpace G)) ≠ 0 := by
  rcases h.exists_rawGeneratorSum_for_kirchhoffQuotientClass x with
    ⟨raw, coeff, terms, hterms, hsupport, hsum, hquot⟩
  have hrawQuotient_ne_zero :
      (Submodule.Quotient.mk
          (⟨(raw : Theorem49EdgeSpace G), raw.property.2⟩ :
            Theorem49BoundaryKirchhoffSubmodule emb) :
        Theorem49BoundaryQuotient emb) ≠ 0 := by
    intro hzero
    exact hx (by simpa [hquot] using hzero)
  rcases
    h.exists_projectedGenerator_chainDot_ne_zero_of_ne_zero_kirchhoffQuotientClass
      (⟨(raw : Theorem49EdgeSpace G), raw.property.2⟩ :
        Theorem49BoundaryKirchhoffSubmodule emb)
      hrawQuotient_ne_zero with
    ⟨p, hp, hdetect⟩
  exact ⟨raw, coeff, terms, p, hterms, hsupport, hsum, hquot, hp, hdetect⟩

/-- A nonzero raw-source quotient class has a finite raw generator-sum representative that is
detected after selected-boundary erasure by a projected Definition 4.8 generator.  This is the
raw-source quotient version of the purified Kirchhoff representative theorem, with the quotient
bridge discharged inside the statement. -/
theorem Theorem49BoundaryRootSynthesis.exists_rawGeneratorSum_and_projectedGenerator_chainDot_ne_zero_of_ne_zero_rawSourceQuotientClass
    {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)] [FiniteDimensional F2 (Theorem49EdgeSpace G)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀)
    (x : Theorem49RawSource emb C₀)
    (hx : (Submodule.Quotient.mk x : Theorem49RawSourceQuotient emb C₀) ≠ 0) :
    ∃ (raw : Theorem49RawSource emb C₀)
        (coeff : (Theorem49EdgeSpace G) → F2) (terms : Finset (Theorem49EdgeSpace G))
        (p : Theorem49EdgeSpace G),
      (terms : Set (Theorem49EdgeSpace G)) ⊆
          Theorem49RawGeneratorFamily emb C₀ ∧
        coeff.support ⊆ terms ∧
          (∑ y ∈ terms, coeff y • y) = (raw : Theorem49EdgeSpace G) ∧
            (Submodule.Quotient.mk raw : Theorem49RawSourceQuotient emb C₀) =
              Submodule.Quotient.mk x ∧
            p ∈ Theorem49ProjectedGeneratorSubspace emb C₀ ∧
              chainDotBilinForm G.edgeSet p
                (Theorem49BoundaryProjection emb (raw : Theorem49EdgeSpace G)) ≠ 0 := by
  let xKirch : Theorem49BoundaryKirchhoffSubmodule emb :=
    ⟨(x : Theorem49EdgeSpace G), x.property.2⟩
  have hxKirch :
      (Submodule.Quotient.mk xKirch : Theorem49BoundaryQuotient emb) ≠ 0 := by
    intro hxKirchZero
    apply hx
    apply h.rawSourceQuotientEquivKirchhoffQuotient.injective
    simpa [xKirch,
      Theorem49BoundaryRootSynthesis.rawSourceQuotientEquivKirchhoffQuotient_apply_mk]
      using hxKirchZero
  rcases
    h.exists_rawGeneratorSum_and_projectedGenerator_chainDot_ne_zero_of_ne_zero_kirchhoffQuotientClass
      xKirch hxKirch with
    ⟨raw, coeff, terms, p, hterms, hsupport, hsum, hkirchQuot, hp, hdetect⟩
  have hrawQuot :
      (Submodule.Quotient.mk raw : Theorem49RawSourceQuotient emb C₀) =
          Submodule.Quotient.mk x := by
    apply h.rawSourceQuotientEquivKirchhoffQuotient.injective
    simpa [xKirch,
      Theorem49BoundaryRootSynthesis.rawSourceQuotientEquivKirchhoffQuotient_apply_mk]
      using hkirchQuot
  exact ⟨raw, coeff, terms, p, hterms, hsupport, hsum, hrawQuot, hp, hdetect⟩

/-- A nonzero concrete theorem-4.9 target has a finite raw Definition 4.8 generator-sum
representative and is detected by a projected Definition 4.8 generator.  This combines the raw
projection representation field with pointwise projected-generator separation, so downstream
arguments can consume a nonzero boundary-zero Kirchhoff target without separately choosing a raw
representative and then proving a detector. -/
theorem Theorem49BoundaryRootSynthesis.exists_rawGeneratorSum_and_projectedGenerator_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace
    {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)] [FiniteDimensional F2 (Theorem49EdgeSpace G)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀)
    (z : Theorem49BoundaryTarget emb)
    (hz : z ≠ 0) :
    ∃ (coeff : (Theorem49EdgeSpace G) → F2) (terms : Finset (Theorem49EdgeSpace G))
        (p : Theorem49EdgeSpace G),
      (terms : Set (Theorem49EdgeSpace G)) ⊆
          Theorem49RawGeneratorFamily emb C₀ ∧
        coeff.support ⊆ terms ∧
          (∑ y ∈ terms, coeff y • y) ∈
              Theorem49BoundaryKirchhoffSubmodule emb ∧
            Theorem49BoundaryProjection emb
                (∑ y ∈ terms, coeff y • y) =
              (z : Theorem49EdgeSpace G) ∧
            p ∈ Theorem49ProjectedGeneratorSubspace emb C₀ ∧
              chainDotBilinForm G.edgeSet p (z : Theorem49EdgeSpace G) ≠ 0 := by
  rcases h.rawGeneratorProjectionRepresentation z.property with
    ⟨coeff, terms, hterms, hsupport, hkirch, hproj⟩
  have hdetector :
      ∃ p ∈ Theorem49ProjectedGeneratorSubspace emb C₀,
        chainDotBilinForm G.edgeSet p (z : Theorem49EdgeSpace G) ≠ 0 := by
    by_contra hnone
    have horth :
        ∀ p ∈ Theorem49ProjectedGeneratorSubspace emb C₀,
          chainDotBilinForm G.edgeSet p (z : Theorem49EdgeSpace G) = 0 := by
      intro p hp
      by_contra hne
      exact hnone ⟨p, hp, hne⟩
    exact hz ((h.pointwise_separation z).1 horth)
  rcases hdetector with ⟨p, hp, hpair⟩
  exact ⟨coeff, terms, p, hterms, hsupport, hkirch, hproj, hp, hpair⟩

/-- A nonzero concrete theorem-4.9 target forces genuinely nonempty raw and projected
Definition 4.8 data.  The finite raw generator-family representative cannot be the empty sum,
because its selected-boundary erasure is the nonzero target, and the projected detector cannot be
the zero chain because its chain-dot pairing with that target is nonzero. -/
theorem Theorem49BoundaryRootSynthesis.exists_nonempty_rawGeneratorSum_and_nonzero_projectedGenerator_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace
    {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)] [FiniteDimensional F2 (Theorem49EdgeSpace G)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀)
    (z : Theorem49BoundaryTarget emb)
    (hz : z ≠ 0) :
    ∃ (coeff : (Theorem49EdgeSpace G) → F2) (terms : Finset (Theorem49EdgeSpace G))
        (p : Theorem49EdgeSpace G),
      terms.Nonempty ∧
        (terms : Set (Theorem49EdgeSpace G)) ⊆
            Theorem49RawGeneratorFamily emb C₀ ∧
          coeff.support ⊆ terms ∧
            (∑ y ∈ terms, coeff y • y) ∈
                Theorem49BoundaryKirchhoffSubmodule emb ∧
              Theorem49BoundaryProjection emb
                  (∑ y ∈ terms, coeff y • y) =
                (z : Theorem49EdgeSpace G) ∧
              p ∈ Theorem49ProjectedGeneratorSubspace emb C₀ ∧
                p ≠ 0 ∧
                  chainDotBilinForm G.edgeSet p (z : Theorem49EdgeSpace G) ≠ 0 := by
  rcases
    h.exists_rawGeneratorSum_and_projectedGenerator_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace
      z hz with
    ⟨coeff, terms, p, hterms, hsupport, hkirch, hproj, hp, hpair⟩
  have htermsNonempty : terms.Nonempty := by
    by_contra hnot
    have htermsEmpty : terms = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnot
    apply hz
    apply Subtype.ext
    simpa [htermsEmpty] using hproj.symm
  have hpNonzero : p ≠ 0 := by
    intro hpZero
    exact hpair (by simp [hpZero])
  exact
    ⟨coeff, terms, p, htermsNonempty, hterms, hsupport, hkirch, hproj, hp,
      hpNonzero, hpair⟩

/-- A nonzero concrete theorem-4.9 target can be represented by a genuinely nonzero raw
Definition 4.8 generator-family combination.  In particular, the coefficient support is nonempty;
the nonempty term-set theorem alone only says that the chosen ambient finite set is nonempty. -/
theorem Theorem49BoundaryRootSynthesis.exists_nonzero_rawGeneratorSum_and_nonempty_coeffSupport_and_nonzero_projectedGenerator_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace
    {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)] [FiniteDimensional F2 (Theorem49EdgeSpace G)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀)
    (z : Theorem49BoundaryTarget emb)
    (hz : z ≠ 0) :
    ∃ (coeff : (Theorem49EdgeSpace G) → F2) (terms : Finset (Theorem49EdgeSpace G))
        (p : Theorem49EdgeSpace G),
      terms.Nonempty ∧
        coeff.support.Nonempty ∧
          (terms : Set (Theorem49EdgeSpace G)) ⊆
              Theorem49RawGeneratorFamily emb C₀ ∧
            coeff.support ⊆ terms ∧
              (∑ y ∈ terms, coeff y • y) ∈
                  Theorem49BoundaryKirchhoffSubmodule emb ∧
                (∑ y ∈ terms, coeff y • y) ≠ 0 ∧
                  Theorem49BoundaryProjection emb
                      (∑ y ∈ terms, coeff y • y) =
                    (z : Theorem49EdgeSpace G) ∧
                  p ∈ Theorem49ProjectedGeneratorSubspace emb C₀ ∧
                    p ≠ 0 ∧
                      chainDotBilinForm G.edgeSet p (z : Theorem49EdgeSpace G) ≠ 0 := by
  rcases
    h.exists_nonempty_rawGeneratorSum_and_nonzero_projectedGenerator_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace
      z hz with
    ⟨coeff, terms, p, htermsNonempty, hterms, hsupport, hkirch, hproj, hp,
      hpNonzero, hpair⟩
  let raw : Theorem49EdgeSpace G := ∑ y ∈ terms, coeff y • y
  have hrawNonzero : raw ≠ 0 := by
    intro hrawZero
    apply hz
    apply Subtype.ext
    simpa [raw, hrawZero] using hproj.symm
  have hcoeffSupportNonempty : coeff.support.Nonempty := by
    have hcoeffNonzero : coeff ≠ 0 := by
      intro hcoeffZero
      apply hrawNonzero
      simp [raw, hcoeffZero]
    simpa using (Function.support_nonempty_iff.mpr hcoeffNonzero)
  exact
    ⟨coeff, terms, p, htermsNonempty, hcoeffSupportNonempty, hterms, hsupport, hkirch,
      by simpa [raw] using hrawNonzero, hproj, hp, hpNonzero, hpair⟩

/-- A nonzero concrete theorem-4.9 target has an actual raw Definition 4.8 generator term
appearing with nonzero coefficient in a finite raw representative.  This is the term-level
payload of the support-sensitive non-vacuity theorem: the nonzero coefficient support is not just
abstractly inhabited, but contains a generator-family chain used by the raw representative. -/
theorem Theorem49BoundaryRootSynthesis.exists_rawGenerator_with_nonzero_coeff_and_nonzero_projectedGenerator_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace
    {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)] [FiniteDimensional F2 (Theorem49EdgeSpace G)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀)
    (z : Theorem49BoundaryTarget emb)
    (hz : z ≠ 0) :
    ∃ (coeff : (Theorem49EdgeSpace G) → F2) (terms : Finset (Theorem49EdgeSpace G))
        (y p : Theorem49EdgeSpace G),
      (terms : Set (Theorem49EdgeSpace G)) ⊆
          Theorem49RawGeneratorFamily emb C₀ ∧
        coeff.support ⊆ terms ∧
          y ∈ coeff.support ∧
            y ∈ terms ∧
              y ∈ Theorem49RawGeneratorFamily emb C₀ ∧
                coeff y ≠ 0 ∧
                  (∑ x ∈ terms, coeff x • x) ∈
                      Theorem49BoundaryKirchhoffSubmodule emb ∧
                    (∑ x ∈ terms, coeff x • x) ≠ 0 ∧
                      Theorem49BoundaryProjection emb
                          (∑ x ∈ terms, coeff x • x) =
                        (z : Theorem49EdgeSpace G) ∧
                      p ∈ Theorem49ProjectedGeneratorSubspace emb C₀ ∧
                        p ≠ 0 ∧
                          chainDotBilinForm G.edgeSet p (z : Theorem49EdgeSpace G) ≠ 0 := by
  rcases
    h.exists_nonzero_rawGeneratorSum_and_nonempty_coeffSupport_and_nonzero_projectedGenerator_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace
      z hz with
    ⟨coeff, terms, p, _htermsNonempty, hcoeffSupportNonempty, hterms, hsupport, hkirch,
      hrawNonzero, hproj, hp, hpNonzero, hpair⟩
  rcases hcoeffSupportNonempty with ⟨y, hySupport⟩
  have hyTerms : y ∈ terms := hsupport hySupport
  have hyFamily : y ∈ Theorem49RawGeneratorFamily emb C₀ := hterms hyTerms
  have hcoeffYNonzero : coeff y ≠ 0 := by
    simpa [Function.mem_support] using hySupport
  exact
    ⟨coeff, terms, y, p, hterms, hsupport, hySupport, hyTerms, hyFamily,
      hcoeffYNonzero, hkirch, hrawNonzero, hproj, hp, hpNonzero, hpair⟩

/-- A nonzero concrete theorem-4.9 target has a nonzero raw Definition 4.8 generator term
appearing with nonzero coefficient in a finite raw representative. This removes the remaining
degeneracy in the term-level witness: the support term is not just formally present, it is a
nonzero chain in the ambient edge-coloring vector space. -/
theorem Theorem49BoundaryRootSynthesis.exists_nonzero_rawGenerator_with_nonzero_coeff_and_nonzero_projectedGenerator_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace
    {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)] [FiniteDimensional F2 (Theorem49EdgeSpace G)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀)
    (z : Theorem49BoundaryTarget emb)
    (hz : z ≠ 0) :
    ∃ (coeff : (Theorem49EdgeSpace G) → F2) (terms : Finset (Theorem49EdgeSpace G))
        (y p : Theorem49EdgeSpace G),
      (terms : Set (Theorem49EdgeSpace G)) ⊆
          Theorem49RawGeneratorFamily emb C₀ ∧
        coeff.support ⊆ terms ∧
          y ∈ coeff.support ∧
            y ∈ terms ∧
              y ∈ Theorem49RawGeneratorFamily emb C₀ ∧
                y ≠ 0 ∧
                  coeff y ≠ 0 ∧
                    (∑ x ∈ terms, coeff x • x) ∈
                        Theorem49BoundaryKirchhoffSubmodule emb ∧
                      (∑ x ∈ terms, coeff x • x) ≠ 0 ∧
                        Theorem49BoundaryProjection emb
                            (∑ x ∈ terms, coeff x • x) =
                          (z : Theorem49EdgeSpace G) ∧
                        p ∈ Theorem49ProjectedGeneratorSubspace emb C₀ ∧
                          p ≠ 0 ∧
                            chainDotBilinForm G.edgeSet p (z : Theorem49EdgeSpace G) ≠ 0 := by
  rcases
    h.exists_rawGenerator_with_nonzero_coeff_and_nonzero_projectedGenerator_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace
      z hz with
    ⟨coeff, terms, y₀, p, hterms, hsupport, hy₀Support, _hy₀Terms, _hy₀Family,
      _hy₀Coeff, hkirch, hrawNonzero, hproj, hp, hpNonzero, hpair⟩
  have hnonzeroSupport : ∃ y, y ∈ coeff.support ∧ y ≠ 0 := by
    by_contra hnone
    apply hrawNonzero
    refine Finset.sum_eq_zero ?_
    intro x hxTerms
    by_cases hxSupport : x ∈ coeff.support
    · have hxZero : x = 0 := by
        by_contra hxNonzero
        exact hnone ⟨x, hxSupport, hxNonzero⟩
      simp [hxZero]
    · have hcoeffZero : coeff x = 0 := by
        have hcoeffNotNonzero : ¬ coeff x ≠ 0 := by
          simpa [Function.mem_support] using hxSupport
        exact not_ne_iff.mp hcoeffNotNonzero
      simp [hcoeffZero]
  rcases hnonzeroSupport with ⟨y, hySupport, hyNonzero⟩
  have hyTerms : y ∈ terms := hsupport hySupport
  have hyFamily : y ∈ Theorem49RawGeneratorFamily emb C₀ := hterms hyTerms
  have hcoeffYNonzero : coeff y ≠ 0 := by
    simpa [Function.mem_support] using hySupport
  exact
    ⟨coeff, terms, y, p, hterms, hsupport, hySupport, hyTerms, hyFamily, hyNonzero,
      hcoeffYNonzero, hkirch, hrawNonzero, hproj, hp, hpNonzero, hpair⟩

/-- A nonzero concrete theorem-4.9 target has a raw Definition 4.8 generator term whose
selected-boundary erasure is itself nonzero. This is the boundary-facing term-level payload of the
finite raw representative: the nonzero target cannot be produced entirely from support terms that
vanish under `boundaryZeroProjection`. -/
theorem Theorem49BoundaryRootSynthesis.exists_rawGenerator_with_nonzero_boundaryZeroProjection_and_nonzero_coeff_and_nonzero_projectedGenerator_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace
    {G : SimpleGraph V}
    [Fintype (Theorem49EdgeCarrier G)] [FiniteDimensional F2 (Theorem49EdgeSpace G)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀)
    (z : Theorem49BoundaryTarget emb)
    (hz : z ≠ 0) :
    ∃ (coeff : (Theorem49EdgeSpace G) → F2) (terms : Finset (Theorem49EdgeSpace G))
        (y p : Theorem49EdgeSpace G),
      (terms : Set (Theorem49EdgeSpace G)) ⊆
          Theorem49RawGeneratorFamily emb C₀ ∧
        coeff.support ⊆ terms ∧
          y ∈ coeff.support ∧
            y ∈ terms ∧
              y ∈ Theorem49RawGeneratorFamily emb C₀ ∧
                Theorem49BoundaryProjection emb y ≠ 0 ∧
                  y ≠ 0 ∧
                    coeff y ≠ 0 ∧
                      (∑ x ∈ terms, coeff x • x) ∈
                          Theorem49BoundaryKirchhoffSubmodule emb ∧
                        (∑ x ∈ terms, coeff x • x) ≠ 0 ∧
                          Theorem49BoundaryProjection emb
                              (∑ x ∈ terms, coeff x • x) =
                            (z : Theorem49EdgeSpace G) ∧
                          p ∈ Theorem49ProjectedGeneratorSubspace emb C₀ ∧
                            p ≠ 0 ∧
                              chainDotBilinForm G.edgeSet p (z : Theorem49EdgeSpace G) ≠ 0 := by
  rcases
    h.exists_nonzero_rawGenerator_with_nonzero_coeff_and_nonzero_projectedGenerator_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace
      z hz with
    ⟨coeff, terms, _y₀, p, hterms, hsupport, _hy₀Support, _hy₀Terms, _hy₀Family,
      _hy₀Nonzero, _hy₀Coeff, hkirch, hrawNonzero, hproj, hp, hpNonzero, hpair⟩
  have hnonzeroBoundarySupport :
      ∃ y, y ∈ coeff.support ∧
        Theorem49BoundaryProjection emb y ≠ 0 := by
    by_contra hnone
    have hprojRawZero :
        Theorem49BoundaryProjection emb (∑ x ∈ terms, coeff x • x) = 0 := by
      calc
        Theorem49BoundaryProjection emb (∑ x ∈ terms, coeff x • x) =
            ∑ x ∈ terms,
              coeff x • Theorem49BoundaryProjection emb x := by
          simp [Theorem49BoundaryProjection]
        _ = 0 := by
          refine Finset.sum_eq_zero ?_
          intro x hxTerms
          by_cases hxSupport : x ∈ coeff.support
          · have hxProjZero : Theorem49BoundaryProjection emb x = 0 := by
              by_contra hxProjNonzero
              exact hnone ⟨x, hxSupport, hxProjNonzero⟩
            simp [hxProjZero]
          · have hcoeffZero : coeff x = 0 := by
              have hcoeffNotNonzero : ¬ coeff x ≠ 0 := by
                simpa [Function.mem_support] using hxSupport
              exact not_ne_iff.mp hcoeffNotNonzero
            simp [hcoeffZero]
    have hzVectorZero : (z : Theorem49EdgeSpace G) = 0 := by
      simpa [hproj] using hprojRawZero
    exact hz (Subtype.ext hzVectorZero)
  rcases hnonzeroBoundarySupport with ⟨y, hySupport, hyProjectionNonzero⟩
  have hyTerms : y ∈ terms := hsupport hySupport
  have hyFamily : y ∈ Theorem49RawGeneratorFamily emb C₀ := hterms hyTerms
  have hyNonzero : y ≠ 0 := by
    intro hyZero
    apply hyProjectionNonzero
    simp [hyZero]
  have hcoeffYNonzero : coeff y ≠ 0 := by
    simpa [Function.mem_support] using hySupport
  exact
    ⟨coeff, terms, y, p, hterms, hsupport, hySupport, hyTerms, hyFamily,
      hyProjectionNonzero, hyNonzero, hcoeffYNonzero, hkirch, hrawNonzero,
      hproj, hp, hpNonzero, hpair⟩


end Mettapedia.GraphTheory.FourColor

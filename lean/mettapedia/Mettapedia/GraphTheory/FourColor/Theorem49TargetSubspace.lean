import Mettapedia.GraphTheory.FourColor.Theorem49KempeGeneratorSpan

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- The finite set of graph edges incident to a vertex, viewed in the current `edgeSet` type. -/
def incidentEdgeFinset (G : SimpleGraph V) [Fintype G.edgeSet] (v : V) :
    Finset G.edgeSet :=
  Finset.univ.filter fun e => v ∈ (e : Sym2 V)

/-- The unoriented `𝔽₂²` Kirchhoff sum of a chain at a vertex.  Over `𝔽₂`, orientations are
irrelevant, so this is the natural cycle-space boundary operator for the current color algebra. -/
def vertexKirchhoffSum (G : SimpleGraph V) [Fintype G.edgeSet]
    (x : G.edgeSet → Color) (v : V) : Color :=
  Finset.sum (incidentEdgeFinset G v) fun e => x e

def scalarVertexKirchhoffSum (G : SimpleGraph V) [Fintype G.edgeSet]
    (x : G.edgeSet → F2) (v : V) : F2 :=
  Finset.sum (incidentEdgeFinset G v) fun e => x e

/-- Chains satisfying the Kirchhoff condition at the selected vertices.  The v23 proof applies
this to the interior vertices of the annular triangulation; that vertex set is not yet part of
`PlaneEmbeddingWithBoundary`, so it is explicit here. -/
def kirchhoffSubmodule (G : SimpleGraph V) [Fintype G.edgeSet]
    (vertices : Finset V) : Submodule F2 (G.edgeSet → Color) where
  carrier := {x | ∀ v ∈ vertices, vertexKirchhoffSum G x v = 0}
  zero_mem' := by
    intro v hv
    unfold vertexKirchhoffSum
    simp
  add_mem' := by
    intro x y hx hy v hv
    unfold vertexKirchhoffSum
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib]
    have hxv := hx v hv
    have hyv := hy v hv
    unfold vertexKirchhoffSum at hxv hyv
    rw [hxv, hyv]
    simp
  smul_mem' := by
    intro a x hx v hv
    unfold vertexKirchhoffSum
    simp only [Pi.smul_apply]
    rw [← Finset.smul_sum]
    have hxv := hx v hv
    unfold vertexKirchhoffSum at hxv
    rw [hxv]
    simp

theorem mem_kirchhoffSubmodule {G : SimpleGraph V} [Fintype G.edgeSet]
    {vertices : Finset V} {x : G.edgeSet → Color} :
    x ∈ kirchhoffSubmodule G vertices ↔
      ∀ v ∈ vertices, vertexKirchhoffSum G x v = 0 :=
  Iff.rfl

theorem eq_zero_of_vertexKirchhoffSum_eq_zero_of_incident_rest_zero
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (x : G.edgeSet → Color) {v : V} {e : G.edgeSet}
    (he : e ∈ incidentEdgeFinset G v)
    (hrest : ∀ e' ∈ incidentEdgeFinset G v, e' ≠ e → x e' = 0)
    (hkirch : vertexKirchhoffSum G x v = 0) :
    x e = 0 := by
  unfold vertexKirchhoffSum at hkirch
  have hsum : (∑ e' ∈ incidentEdgeFinset G v, x e') = x e := by
    rw [Finset.sum_eq_single e]
    · intro e' he' hne
      exact hrest e' he' hne
    · intro heNot
      exact False.elim (heNot he)
  rwa [hsum] at hkirch

theorem eq_zero_of_mem_kirchhoffSubmodule_of_incident_rest_zero
    {G : SimpleGraph V} [Fintype G.edgeSet] {vertices : Finset V}
    {x : G.edgeSet → Color} (hx : x ∈ kirchhoffSubmodule G vertices)
    {v : V} (hv : v ∈ vertices) {e : G.edgeSet}
    (he : e ∈ incidentEdgeFinset G v)
    (hrest : ∀ e' ∈ incidentEdgeFinset G v, e' ≠ e → x e' = 0) :
    x e = 0 :=
  eq_zero_of_vertexKirchhoffSum_eq_zero_of_incident_rest_zero
    x he hrest (hx v hv)

theorem exists_nonzero_mem_linearMap_ker_of_finrank_lt
    {K X Y : Type*} [Field K]
    [AddCommGroup X] [Module K X] [FiniteDimensional K X]
    [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y]
    (constraints : X →ₗ[K] Y)
    (hconstraints : Module.finrank K Y < Module.finrank K X) :
    ∃ x : X, x ∈ LinearMap.ker constraints ∧ x ≠ 0 := by
  exact Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt
      (f := constraints) hconstraints)

theorem exists_nonzero_f2ScalarChain_mem_ker_of_finrank_lt_card
    {E Y : Type*} [Fintype E]
    [AddCommGroup Y] [Module F2 Y] [FiniteDimensional F2 Y]
    (constraints : (E → F2) →ₗ[F2] Y)
    (hconstraints : Module.finrank F2 Y < Fintype.card E) :
    ∃ x : E → F2, x ∈ LinearMap.ker constraints ∧ x ≠ 0 := by
  refine exists_nonzero_mem_linearMap_ker_of_finrank_lt constraints ?_
  simpa [Module.finrank_pi] using hconstraints

def redScalarColorChain {E : Type*} (x : E → F2) : E → Color :=
  fun e => x e • red

theorem redScalarColorChain_ne_zero_of_ne_zero {E : Type*} {x : E → F2}
    (hx : x ≠ 0) :
    redScalarColorChain x ≠ 0 := by
  intro hzero
  apply hx
  funext e
  have hvalue := congrFun hzero e
  have hfirst := congrArg Prod.fst hvalue
  simpa [redScalarColorChain, red] using hfirst

theorem redScalarColorChain_apply_eq_zero_of_scalar_eq_zero {E : Type*}
    {x : E → F2} {e : E} (hx : x e = 0) :
    redScalarColorChain x e = 0 := by
  simp [redScalarColorChain, red, hx]

theorem vertexKirchhoffSum_redScalarColorChain_eq_zero_of_scalarVertexKirchhoffSum_eq_zero
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (x : G.edgeSet → F2) (v : V)
    (hx : scalarVertexKirchhoffSum G x v = 0) :
    vertexKirchhoffSum G (redScalarColorChain x) v = 0 := by
  unfold vertexKirchhoffSum scalarVertexKirchhoffSum at *
  have hsum :
      (∑ e ∈ incidentEdgeFinset G v, redScalarColorChain x e) =
        (((∑ e ∈ incidentEdgeFinset G v, x e), 0) : Color) := by
    classical
    unfold redScalarColorChain
    refine Finset.induction_on (incidentEdgeFinset G v) ?base ?step
    · rfl
    · intro e edges heNot ih
      rw [Finset.sum_insert heNot, Finset.sum_insert heNot, ih]
      ext <;> simp [red]
  rw [hsum, hx]
  rfl

theorem redScalarColorChain_mem_kirchhoffSubmodule
    {G : SimpleGraph V} [Fintype G.edgeSet] {vertices : Finset V}
    {x : G.edgeSet → F2}
    (hx : ∀ v ∈ vertices, scalarVertexKirchhoffSum G x v = 0) :
    redScalarColorChain x ∈ kirchhoffSubmodule G vertices := by
  intro v hv
  exact
    vertexKirchhoffSum_redScalarColorChain_eq_zero_of_scalarVertexKirchhoffSum_eq_zero
      x v (hx v hv)

/-- Chains vanishing on a specified boundary support. -/
def boundaryZeroSubmodule {E : Type*} [DecidableEq E] (boundary : Finset E) :
    Submodule F2 (E → Color) where
  carrier := {x | ∀ e ∈ boundary, x e = 0}
  zero_mem' := by
    intro e he
    rfl
  add_mem' := by
    intro x y hx hy e he
    simp [hx e he, hy e he]
  smul_mem' := by
    intro a x hx e he
    simp [hx e he]

theorem mem_boundaryZeroSubmodule {E : Type*} [DecidableEq E]
    {boundary : Finset E} {x : E → Color} :
    x ∈ boundaryZeroSubmodule boundary ↔ ∀ e ∈ boundary, x e = 0 :=
  Iff.rfl

theorem redScalarColorChain_mem_boundaryZeroSubmodule {E : Type*}
    [DecidableEq E] {boundary : Finset E} {x : E → F2}
    (hx : ∀ e ∈ boundary, x e = 0) :
    redScalarColorChain x ∈ boundaryZeroSubmodule boundary := by
  intro e he
  exact redScalarColorChain_apply_eq_zero_of_scalar_eq_zero (hx e he)

theorem boundaryZeroSubmodule_le_of_subset {E : Type*} [DecidableEq E]
    {boundary₁ boundary₂ : Finset E} (hsubset : boundary₂ ⊆ boundary₁) :
    boundaryZeroSubmodule boundary₁ ≤ boundaryZeroSubmodule boundary₂ := by
  intro x hx e he
  exact hx e (hsubset he)

/-- Boundary-zero chains for a fixed plane embedding with boundary. -/
def planarBoundaryZeroSubmodule {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) :
    Submodule F2 (G.edgeSet → Color) :=
  boundaryZeroSubmodule
    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)

theorem redScalarColorChain_mem_planarBoundaryZeroSubmodule
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {x : G.edgeSet → F2}
    (hx :
      ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, x e = 0) :
    redScalarColorChain x ∈ planarBoundaryZeroSubmodule emb :=
  redScalarColorChain_mem_boundaryZeroSubmodule hx

theorem boundaryZero_of_mem_planarBoundaryZeroSubmodule {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G} {z : G.edgeSet → Color}
    (hz : z ∈ planarBoundaryZeroSubmodule emb) :
    ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0 :=
  hz

theorem eq_zero_of_mem_planarBoundaryZeroSubmodule_of_control_or_boundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (z : G.edgeSet → Color)
    (hzBoundary : z ∈ planarBoundaryZeroSubmodule emb)
    (control : Finset G.edgeSet)
    (hcontrol : ∀ e ∈ control, z e = 0)
    (hcover : ∀ e : G.edgeSet,
      e ∈ control ∨
        e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) :
    z = 0 := by
  funext e
  rcases hcover e with hcontrolled | hboundary
  · exact hcontrol e hcontrolled
  · exact boundaryZero_of_mem_planarBoundaryZeroSubmodule hzBoundary e hboundary

theorem edge_mem_selectedBoundarySupport_or_interiorEdgeSupport
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G)
    (e : G.edgeSet) :
    e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
      e ∈ interiorEdgeSupport emb.faceBoundary emb.faces := by
  have hall :
      ∀ e : G.edgeSet, totalIncidenceCount emb.faceBoundary emb.faces e ≤ 2 := by
    intro e
    change (emb.faces.filter fun f => e ∈ emb.faceBoundary f).card ≤ 2
    exact emb.totalFaceIncidenceCount_le_two e
  have hmem :
      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∪
        interiorEdgeSupport emb.faceBoundary emb.faces := by
    rw [← biUnion_eq_selectedBoundarySupport_union_interiorEdgeSupport_of_totalIncidenceCount_le_two
      emb.faceBoundary emb.faces hall]
    exact emb.edge_mem_faceSupport e
  exact Finset.mem_union.1 hmem

theorem eq_zero_of_mem_planarBoundaryZeroSubmodule_of_interiorEdgeSupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (z : G.edgeSet → Color)
    (hzBoundary : z ∈ planarBoundaryZeroSubmodule emb)
    (hinterior :
      ∀ e ∈ interiorEdgeSupport emb.faceBoundary emb.faces, z e = 0) :
    z = 0 := by
  refine eq_zero_of_mem_planarBoundaryZeroSubmodule_of_control_or_boundary
    z hzBoundary (interiorEdgeSupport emb.faceBoundary emb.faces) hinterior ?_
  intro e
  rcases edge_mem_selectedBoundarySupport_or_interiorEdgeSupport emb e with
    hboundary | hinterior
  · exact Or.inr hboundary
  · exact Or.inl hinterior

/-- The concrete v23-shaped target side available from the current interfaces: Kirchhoff at an
explicit vertex set and zero on the selected boundary edges.  Instantiating `vertices` with the
interior vertices is the next upstream data obligation. -/
def theorem49BoundaryZeroKirchhoffSubspace {G : SimpleGraph V} [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G) (vertices : Finset V) :
    Submodule F2 (G.edgeSet → Color) :=
  kirchhoffSubmodule G vertices ⊓ planarBoundaryZeroSubmodule emb

theorem theorem49BoundaryZeroKirchhoffSubspace_empty_vertices_eq_planarBoundaryZeroSubmodule
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G) :
    theorem49BoundaryZeroKirchhoffSubspace emb (∅ : Finset V) =
      planarBoundaryZeroSubmodule emb := by
  ext z
  constructor
  · intro hz
    exact hz.2
  · intro hz
    exact ⟨(by intro v hv; simp at hv), hz⟩

theorem redScalarColorChain_mem_theorem49BoundaryZeroKirchhoffSubspace
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G} {vertices : Finset V}
    {x : G.edgeSet → F2}
    (hkirchhoff : ∀ v ∈ vertices, scalarVertexKirchhoffSum G x v = 0)
    (hboundary :
      ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, x e = 0) :
    redScalarColorChain x ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices :=
  ⟨redScalarColorChain_mem_kirchhoffSubmodule hkirchhoff,
    redScalarColorChain_mem_planarBoundaryZeroSubmodule hboundary⟩

abbrev theorem49BoundaryZeroKirchhoffScalarConstraintSpace
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G) (vertices : Finset V)
    (control : Finset G.edgeSet) : Type _ :=
  (((e : {e : G.edgeSet // e ∈ control}) → F2) ×
    ((e : {e : G.edgeSet //
      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces}) → F2) ×
    ((v : {v : V // v ∈ vertices}) → F2))

theorem theorem49BoundaryZeroKirchhoffScalarConstraintSpace_finrank_eq
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G) (vertices : Finset V)
    (control : Finset G.edgeSet) :
    Module.finrank F2
      (theorem49BoundaryZeroKirchhoffScalarConstraintSpace emb vertices control) =
      control.card +
        Fintype.card {e : G.edgeSet //
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces} +
        Fintype.card {v : V // v ∈ vertices} := by
  unfold theorem49BoundaryZeroKirchhoffScalarConstraintSpace
  rw [Module.finrank_prod, Module.finrank_prod]
  rw [Module.finrank_pi, Module.finrank_pi, Module.finrank_pi]
  simp [Nat.add_assoc]

theorem theorem49BoundaryZeroKirchhoffScalarConstraintSpace_finrank_lt_of_card_sum_lt
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G) (vertices : Finset V)
    (control : Finset G.edgeSet)
    (hcard :
      control.card +
        Fintype.card {e : G.edgeSet //
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces} +
        Fintype.card {v : V // v ∈ vertices} <
        Fintype.card G.edgeSet) :
    Module.finrank F2
      (theorem49BoundaryZeroKirchhoffScalarConstraintSpace emb vertices control) <
      Fintype.card G.edgeSet := by
  rw [theorem49BoundaryZeroKirchhoffScalarConstraintSpace_finrank_eq]
  exact hcard

noncomputable def theorem49BoundaryZeroKirchhoffScalarConstraintMap
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G) (vertices : Finset V)
    (control : Finset G.edgeSet) :
    (G.edgeSet → F2) →ₗ[F2]
      theorem49BoundaryZeroKirchhoffScalarConstraintSpace emb vertices control where
  toFun x :=
    (fun e => x e.1,
      (fun e => x e.1),
      (fun v => scalarVertexKirchhoffSum G x v.1))
  map_add' x y := by
    ext e <;> simp [scalarVertexKirchhoffSum, Finset.sum_add_distrib]
  map_smul' a x := by
    ext e
    · rfl
    · rfl
    · unfold scalarVertexKirchhoffSum
      simp only [Pi.smul_apply]
      rw [← Finset.smul_sum]
      rfl

theorem exists_redScalarColorChain_mem_theorem49BoundaryZeroKirchhoffSubspace_of_constraintMap_finrank_lt
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G) (vertices : Finset V)
    (control : Finset G.edgeSet)
    (hconstraints :
      Module.finrank F2
        (theorem49BoundaryZeroKirchhoffScalarConstraintSpace emb vertices control) <
        Fintype.card G.edgeSet) :
    ∃ z : G.edgeSet → Color,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices ∧
      (∀ e ∈ control, z e = 0) ∧ z ≠ 0 := by
  rcases exists_nonzero_f2ScalarChain_mem_ker_of_finrank_lt_card
      (theorem49BoundaryZeroKirchhoffScalarConstraintMap emb vertices control)
      hconstraints with ⟨x, hxker, hxne⟩
  have hmap :
      theorem49BoundaryZeroKirchhoffScalarConstraintMap emb vertices control x = 0 :=
    hxker
  have hcontrol : ∀ e ∈ control, x e = 0 := by
    intro e he
    have hcoord := congrFun (congrArg Prod.fst hmap) ⟨e, he⟩
    simpa [theorem49BoundaryZeroKirchhoffScalarConstraintMap] using hcoord
  have hboundary :
      ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, x e = 0 := by
    intro e he
    have hcoord := congrFun (congrArg Prod.fst (congrArg Prod.snd hmap)) ⟨e, he⟩
    simpa [theorem49BoundaryZeroKirchhoffScalarConstraintMap] using hcoord
  have hkirchhoff : ∀ v ∈ vertices, scalarVertexKirchhoffSum G x v = 0 := by
    intro v hv
    have hcoord := congrFun (congrArg Prod.snd (congrArg Prod.snd hmap)) ⟨v, hv⟩
    simpa [theorem49BoundaryZeroKirchhoffScalarConstraintMap] using hcoord
  exact
    ⟨redScalarColorChain x,
      redScalarColorChain_mem_theorem49BoundaryZeroKirchhoffSubspace
        hkirchhoff hboundary,
      (by
        intro e he
        exact redScalarColorChain_apply_eq_zero_of_scalar_eq_zero (hcontrol e he)),
      redScalarColorChain_ne_zero_of_ne_zero hxne⟩

theorem exists_redScalarColorChain_mem_theorem49BoundaryZeroKirchhoffSubspace_of_card_sum_lt
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G) (vertices : Finset V)
    (control : Finset G.edgeSet)
    (hcard :
      control.card +
        Fintype.card {e : G.edgeSet //
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces} +
        Fintype.card {v : V // v ∈ vertices} <
        Fintype.card G.edgeSet) :
    ∃ z : G.edgeSet → Color,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices ∧
      (∀ e ∈ control, z e = 0) ∧ z ≠ 0 := by
  exact
    exists_redScalarColorChain_mem_theorem49BoundaryZeroKirchhoffSubspace_of_constraintMap_finrank_lt
      emb vertices control
      (theorem49BoundaryZeroKirchhoffScalarConstraintSpace_finrank_lt_of_card_sum_lt
        emb vertices control hcard)

theorem not_forall_eq_zero_on_control_of_theorem49BoundaryZeroKirchhoffSubspace_of_card_sum_lt
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G) (vertices : Finset V)
    (control : Finset G.edgeSet)
    (hcard :
      control.card +
        Fintype.card {e : G.edgeSet //
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces} +
        Fintype.card {v : V // v ∈ vertices} <
        Fintype.card G.edgeSet) :
    ¬ (∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices →
      (∀ e ∈ control, z e = 0) →
      z = 0) := by
  rintro hcontrolForcesZero
  rcases exists_redScalarColorChain_mem_theorem49BoundaryZeroKirchhoffSubspace_of_card_sum_lt
      emb vertices control hcard with
    ⟨z, hz, hcontrol, hzNonzero⟩
  exact hzNonzero (hcontrolForcesZero hz hcontrol)

theorem edge_card_le_control_card_add_boundary_card_add_vertex_card_of_theorem49BoundaryZeroKirchhoffSubspace_control
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G) (vertices : Finset V)
    (control : Finset G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices →
        (∀ e ∈ control, z e = 0) →
        z = 0) :
    Fintype.card G.edgeSet ≤
      control.card +
        Fintype.card {e : G.edgeSet //
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces} +
        Fintype.card {v : V // v ∈ vertices} := by
  by_contra hnotLowerBound
  exact
    (not_forall_eq_zero_on_control_of_theorem49BoundaryZeroKirchhoffSubspace_of_card_sum_lt
      emb vertices control (Nat.lt_of_not_ge hnotLowerBound))
      hcontrol

theorem exists_mem_planarBoundaryZeroSubmodule_of_control_card_add_boundary_card_lt
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G) (control : Finset G.edgeSet)
    (hcard :
      control.card +
        Fintype.card {e : G.edgeSet //
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces} <
        Fintype.card G.edgeSet) :
    ∃ z : G.edgeSet → Color,
      z ∈ planarBoundaryZeroSubmodule emb ∧
      (∀ e ∈ control, z e = 0) ∧ z ≠ 0 := by
  have hcardTarget :
      control.card +
        Fintype.card {e : G.edgeSet //
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces} +
        Fintype.card {v : V // v ∈ (∅ : Finset V)} <
        Fintype.card G.edgeSet := by
    simpa using hcard
  rcases exists_redScalarColorChain_mem_theorem49BoundaryZeroKirchhoffSubspace_of_card_sum_lt
      emb (∅ : Finset V) control hcardTarget with
    ⟨z, hz, hcontrol, hzNonzero⟩
  have hsubspace :
      theorem49BoundaryZeroKirchhoffSubspace emb (∅ : Finset V) =
        planarBoundaryZeroSubmodule emb :=
    theorem49BoundaryZeroKirchhoffSubspace_empty_vertices_eq_planarBoundaryZeroSubmodule emb
  have hzBoundary : z ∈ planarBoundaryZeroSubmodule emb := by
    simpa [hsubspace] using hz
  exact ⟨z, hzBoundary, hcontrol, hzNonzero⟩

theorem not_forall_eq_zero_on_control_of_planarBoundaryZeroSubmodule_of_control_card_add_boundary_card_lt
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G) (control : Finset G.edgeSet)
    (hcard :
      control.card +
        Fintype.card {e : G.edgeSet //
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces} <
        Fintype.card G.edgeSet) :
    ¬ (∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule emb →
      (∀ e ∈ control, z e = 0) →
      z = 0) := by
  rintro hcontrolForcesZero
  rcases exists_mem_planarBoundaryZeroSubmodule_of_control_card_add_boundary_card_lt
      emb control hcard with
    ⟨z, hz, hcontrol, hzNonzero⟩
  exact hzNonzero (hcontrolForcesZero hz hcontrol)

theorem edge_card_le_control_card_add_boundary_card_of_planarBoundaryZeroSubmodule_control
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G) (control : Finset G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ control, z e = 0) →
        z = 0) :
    Fintype.card G.edgeSet ≤
      control.card +
        Fintype.card {e : G.edgeSet //
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces} := by
  by_contra hnotLowerBound
  exact
    (not_forall_eq_zero_on_control_of_planarBoundaryZeroSubmodule_of_control_card_add_boundary_card_lt
      emb control (Nat.lt_of_not_ge hnotLowerBound))
      hcontrol

theorem theorem49BoundaryZeroKirchhoffSubspace_le_planarBoundaryZeroSubmodule
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G) (vertices : Finset V) :
    theorem49BoundaryZeroKirchhoffSubspace emb vertices ≤ planarBoundaryZeroSubmodule emb :=
  inf_le_right

theorem theorem49BoundaryZeroKirchhoffSubspace_control_of_planarBoundaryZeroSubmodule_control
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G) (vertices : Finset V)
    (control : Finset G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ control, z e = 0) →
        z = 0) :
    ∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices →
      (∀ e ∈ control, z e = 0) →
      z = 0 := by
  intro z hz hvanish
  exact hcontrol
    ((theorem49BoundaryZeroKirchhoffSubspace_le_planarBoundaryZeroSubmodule
      emb vertices) hz)
    hvanish

theorem theorem49BoundaryZeroKirchhoffSubspace_nonzeroCoverage_of_planarBoundaryZeroSubmodule_nonzeroCoverage
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G) (vertices : Finset V)
    (control : Finset G.edgeSet)
    (hcoverage :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
        ∃ e : G.edgeSet, e ∈ control ∧ z e ≠ 0) :
    ∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices →
      z ≠ 0 →
      ∃ e : G.edgeSet, e ∈ control ∧ z e ≠ 0 := by
  intro z hz hzNonzero
  exact hcoverage
    ((theorem49BoundaryZeroKirchhoffSubspace_le_planarBoundaryZeroSubmodule
      emb vertices) hz)
    hzNonzero

theorem boundaryZero_of_mem_theorem49BoundaryZeroKirchhoffSubspace
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G} {vertices : Finset V} {z : G.edgeSet → Color}
    (hz : z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices) :
    ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0 :=
  boundaryZero_of_mem_planarBoundaryZeroSubmodule hz.2

theorem kirchhoff_of_mem_theorem49BoundaryZeroKirchhoffSubspace
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G} {vertices : Finset V} {z : G.edgeSet → Color}
    (hz : z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices) :
    ∀ v ∈ vertices, vertexKirchhoffSum G z v = 0 :=
  hz.1

theorem eq_zero_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_incident_rest_zero
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G} {vertices : Finset V}
    {z : G.edgeSet → Color}
    (hz : z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices)
    {v : V} (hv : v ∈ vertices) {e : G.edgeSet}
    (he : e ∈ incidentEdgeFinset G v)
    (hrest : ∀ e' ∈ incidentEdgeFinset G v, e' ≠ e → z e' = 0) :
    z e = 0 :=
  eq_zero_of_mem_kirchhoffSubmodule_of_incident_rest_zero
    hz.1 hv he hrest

theorem eq_zero_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_interiorEdgeSupport
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G} {vertices : Finset V}
    (z : G.edgeSet → Color)
    (hz : z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices)
    (hinterior :
      ∀ e ∈ interiorEdgeSupport emb.faceBoundary emb.faces, z e = 0) :
    z = 0 :=
  eq_zero_of_mem_planarBoundaryZeroSubmodule_of_interiorEdgeSupport z
    (theorem49BoundaryZeroKirchhoffSubspace_le_planarBoundaryZeroSubmodule
      emb vertices hz)
    hinterior

theorem eq_zero_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_interiorEdgeSupport_control_or_kirchhoffStar
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G} {vertices : Finset V}
    (z : G.edgeSet → Color)
    (hz : z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices)
    (control : Finset G.edgeSet)
    (hcontrol : ∀ e ∈ control, z e = 0)
    (hcover :
      ∀ e ∈ interiorEdgeSupport emb.faceBoundary emb.faces,
        e ∈ control ∨
          ∃ v ∈ vertices,
            e ∈ incidentEdgeFinset G v ∧
              ∀ e' ∈ incidentEdgeFinset G v, e' ≠ e →
                e' ∈ control ∨
                  e' ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) :
    z = 0 := by
  refine eq_zero_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_interiorEdgeSupport
    z hz ?_
  intro e heInterior
  rcases hcover e heInterior with hcontrolled | ⟨v, hv, heIncident, hrest⟩
  · exact hcontrol e hcontrolled
  · exact
      eq_zero_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_incident_rest_zero
        hz hv heIncident
        (by
          intro e' he' hne
          rcases hrest e' he' hne with hcontrolled | hboundary
          · exact hcontrol e' hcontrolled
          · exact boundaryZero_of_mem_theorem49BoundaryZeroKirchhoffSubspace
              hz e' hboundary)

theorem exists_nonzero_color_ne (c : Color) : ∃ γ : Color, γ ≠ 0 ∧ γ ≠ c := by
  by_cases hc : c = red
  · refine ⟨blue, blue_ne_zero, ?_⟩
    rw [hc]
    intro h
    exact red_ne_blue h.symm
  · exact ⟨red, red_ne_zero, fun h => hc h.symm⟩

/-- A face generator touching a selected boundary edge is not boundary-zero.  This is the
formal warning that the raw all-face simplified generator family cannot be used directly as a
subspace of the v23 `W0(H)` target. -/
theorem polarizedFaceGenerator_not_mem_planarBoundaryZeroSubmodule_of_mem_selectedBoundarySupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (C : G.EdgeColoring Color) {f : emb.Face} {e : G.edgeSet} {γ : Color}
    (heBoundary : e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (heFace : e ∈ emb.faceBoundary f) (hγ0 : γ ≠ 0) :
    polarizedFaceGenerator C (C e) (C e + γ) (emb.faceBoundary f) ∉
      planarBoundaryZeroSubmodule emb := by
  intro hmem
  have hzero := boundaryZero_of_mem_planarBoundaryZeroSubmodule hmem e heBoundary
  have hvalue :
      polarizedFaceGenerator C (C e) (C e + γ) (emb.faceBoundary f) e = γ := by
    rw [polarizedFaceGenerator_eq_indicatorChain_of_add_pair]
    exact indicatorChain_apply_of_mem γ
      ((mem_boundaryBicoloredEdges_iff C (C e) (C e + γ)).2 ⟨heFace, Or.inl rfl⟩)
  rw [hvalue] at hzero
  exact hγ0 hzero

theorem polarizedFaceGenerator_mem_kempeClosureGeneratorSubspace
    {G : SimpleGraph V} {F : Type*} {faceBoundary : F → Finset G.edgeSet}
    {C₀ C : G.EdgeColoring Color} {f : F} {a b : Color}
    (hC : C ∈ G.EdgeKempeClosure C₀) (hab : ValidColorPair a b) :
    polarizedFaceGenerator C a b (faceBoundary f) ∈
      kempeClosureGeneratorSubspace faceBoundary C₀ :=
  Submodule.subset_span ⟨C, hC, f, a, b, hab, rfl⟩

/-- The raw simplified Kempe-closure generator span cannot be contained in the selected-boundary
zero subspace as soon as it contains a face generator touching a selected boundary edge.  A later
Theorem 4.9 target must therefore use the purified/difference-space source from v23, or restrict
the generator family before asking for containment in `W0(H)`. -/
theorem not_kempeClosureGeneratorSubspace_le_planarBoundaryZeroSubmodule_of_mem_selectedBoundarySupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {f : emb.Face} {e : G.edgeSet}
    (heBoundary : e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (heFace : e ∈ emb.faceBoundary f) :
    ¬ kempeClosureGeneratorSubspace emb.faceBoundary C₀ ≤ planarBoundaryZeroSubmodule emb := by
  intro hle
  rcases exists_nonzero_color_ne (C₀ e) with ⟨γ, hγ0, hγne⟩
  have hvalid : ValidColorPair (C₀ e) (C₀ e + γ) :=
    validColorPair_edgeColor_add_generator C₀ e (hC₀ e) hγ0 hγne
  have hgen :
      polarizedFaceGenerator C₀ (C₀ e) (C₀ e + γ) (emb.faceBoundary f) ∈
        kempeClosureGeneratorSubspace emb.faceBoundary C₀ :=
    polarizedFaceGenerator_mem_kempeClosureGeneratorSubspace
      (SimpleGraph.mem_edgeKempeClosure_self C₀) hvalid
  exact
    polarizedFaceGenerator_not_mem_planarBoundaryZeroSubmodule_of_mem_selectedBoundarySupport
      C₀ heBoundary heFace hγ0 (hle hgen)

theorem not_kempeClosureGeneratorSubspace_le_boundaryZeroKirchhoffSubspace_of_mem_selectedBoundarySupport
    {G : SimpleGraph V} [Fintype G.edgeSet] {emb : PlaneEmbeddingWithBoundary G}
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {f : emb.Face} {e : G.edgeSet} {vertices : Finset V}
    (heBoundary : e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (heFace : e ∈ emb.faceBoundary f) :
    ¬ kempeClosureGeneratorSubspace emb.faceBoundary C₀ ≤
      theorem49BoundaryZeroKirchhoffSubspace emb vertices := by
  intro hle
  exact
    not_kempeClosureGeneratorSubspace_le_planarBoundaryZeroSubmodule_of_mem_selectedBoundarySupport
      C₀ hC₀ heBoundary heFace
      (fun x hx =>
        theorem49BoundaryZeroKirchhoffSubspace_le_planarBoundaryZeroSubmodule emb vertices
          (hle hx))

theorem not_exists_vertices_kempeClosureGeneratorSubspace_le_boundaryZeroKirchhoffSubspace_of_mem_selectedBoundarySupport
    {G : SimpleGraph V} [Fintype G.edgeSet] {emb : PlaneEmbeddingWithBoundary G}
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {f : emb.Face} {e : G.edgeSet}
    (heBoundary : e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (heFace : e ∈ emb.faceBoundary f) :
    ¬ ∃ vertices : Finset V,
      kempeClosureGeneratorSubspace emb.faceBoundary C₀ ≤
        theorem49BoundaryZeroKirchhoffSubspace emb vertices := by
  rintro ⟨vertices, hle⟩
  exact
    not_kempeClosureGeneratorSubspace_le_boundaryZeroKirchhoffSubspace_of_mem_selectedBoundarySupport
      C₀ hC₀ heBoundary heFace hle

/-- The Kempe-generator span constructor specialized to a target already known to lie inside the
selected-boundary-zero submodule. -/
noncomputable def Theorem49SubmoduleDualityData.ofKempeGeneratorSubspaceLeBoundaryZero
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    [Fintype G.edgeSet]
    (differenceSubspace : Submodule F2 (G.edgeSet → Color))
    (hleGenerator : kempeClosureGeneratorSubspace emb.faceBoundary C₀ ≤ differenceSubspace)
    (hleBoundary : differenceSubspace ≤ planarBoundaryZeroSubmodule emb) :
    Theorem49SubmoduleDualityData emb C₀ :=
  Theorem49SubmoduleDualityData.ofKempeGeneratorSubspace
    differenceSubspace hleGenerator (by
      intro z hz
      exact boundaryZero_of_mem_planarBoundaryZeroSubmodule (hleBoundary hz))

/-- Theorem 4.9 with the target side named as the boundary-zero Kirchhoff subspace.  The containment
hypothesis is intentionally explicit: the obstruction above shows that the current raw all-face
simplified generator span does not satisfy it when boundary-face generators are present. -/
theorem theorem49_kempeGeneratorSubspace_eq_boundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V)
    (hleGenerator :
      kempeClosureGeneratorSubspace emb.faceBoundary C₀ ≤
        theorem49BoundaryZeroKirchhoffSubspace emb vertices) :
    kempeClosureGeneratorSubspace emb.faceBoundary C₀ =
      theorem49BoundaryZeroKirchhoffSubspace emb vertices :=
  theorem49_submodule_spanning_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    emb data C₀ hC₀
    (Theorem49SubmoduleDualityData.ofKempeGeneratorSubspaceLeBoundaryZero
      (theorem49BoundaryZeroKirchhoffSubspace emb vertices)
      hleGenerator
      (theorem49BoundaryZeroKirchhoffSubspace_le_planarBoundaryZeroSubmodule emb vertices))

end Mettapedia.GraphTheory.FourColor

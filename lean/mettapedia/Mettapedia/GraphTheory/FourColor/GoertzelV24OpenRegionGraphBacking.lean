import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionRotation
import Mettapedia.GraphTheory.FourColor.GoertzelV24FaceDualConnectedness
import Mettapedia.GraphTheory.FourColor.SimpleGraphRotationSystem

/-!
# Graph backing for a literal open region

`GoertzelV24OpenRegionRotation` constructs the dart permutation of a literal
opened vertex region.  Cell--3, however, is stated over a `SimpleGraph` with
degree-one boundary stubs.  This file supplies the carrier bridge: the
computed primal graph of the opened rotation has exactly the same oriented
darts as the opened rotation itself.

This is generic rotation-system plumbing.  It does not choose the Cell--3
region, divide its boundary into the two ordered interfaces, construct its two
hole faces, or prove Euler/planarity data.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OpenRegionGraphBacking

open GoertzelV24FaceDualConnectedness
open GoertzelV24OpenRegionRotation
open GoertzelV24RotationSpliceConstructor
open SimpleGraphDartRotation

-- The open-region instance is proposition-generic and would otherwise also
-- match the ambient edge subtype `G.edgeSet`.  The ordinary subtype instance
-- is definitionally the one used by `Data.toRotationSystem`.

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- The actual simple primal graph computed from a literal open-region
rotation. -/
abbrev PrimalGraph (RS : RotationSystem V E) (keep : V → Prop)
    (outer : GoertzelV24OpenRegionRotation.Dart RS keep) :
    SimpleGraph (GoertzelV24OpenRegionRotation.Vertex RS keep) :=
  rotationPrimalGraph
    (GoertzelV24OpenRegionRotation.rotationSystem RS keep outer)

/-- Read one opened dart as the correspondingly oriented dart of the
computed primal graph. -/
def toPrimalDart (RS : RotationSystem V E) (keep : V → Prop)
    (outer : GoertzelV24OpenRegionRotation.Dart RS keep)
    (dart : GoertzelV24OpenRegionRotation.Dart RS keep) :
    (PrimalGraph RS keep outer).Dart :=
  ⟨((GoertzelV24OpenRegionRotation.rotationSystem RS keep outer).vertOf dart,
      (GoertzelV24OpenRegionRotation.rotationSystem RS keep outer).vertOf
        ((GoertzelV24OpenRegionRotation.rotationSystem RS keep outer).alpha dart)),
    ⟨dart, rfl, rfl⟩⟩

@[simp] theorem toPrimalDart_fst
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : GoertzelV24OpenRegionRotation.Dart RS keep)
    (dart : GoertzelV24OpenRegionRotation.Dart RS keep) :
    (toPrimalDart RS keep outer dart).fst =
      (GoertzelV24OpenRegionRotation.rotationSystem RS keep outer).vertOf dart :=
  rfl

@[simp] theorem toPrimalDart_snd
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : GoertzelV24OpenRegionRotation.Dart RS keep)
    (dart : GoertzelV24OpenRegionRotation.Dart RS keep) :
    (toPrimalDart RS keep outer dart).snd =
      (GoertzelV24OpenRegionRotation.rotationSystem RS keep outer).vertOf
        ((GoertzelV24OpenRegionRotation.rotationSystem RS keep outer).alpha dart) :=
  rfl

/-- Distinct literal-open darts have distinct ordered endpoint pairs.  The
fresh boundary vertex remembers the exact exposed ambient half-dart, while
two retained endpoints determine the original graph dart because the ambient
carrier is a simple graph-backed rotation. -/
theorem toPrimalDart_injective
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : SimpleGraphDartRotation.Data G) (keep : V → Prop)
    (outer : GoertzelV24OpenRegionRotation.Dart
      data.toRotationSystem keep) :
    Function.Injective (toPrimalDart data.toRotationSystem keep outer) := by
  intro left right heq
  have hfst := congrArg (fun dart => dart.toProd.1) heq
  have hsnd := congrArg (fun dart => dart.toProd.2) heq
  change
    (GoertzelV24OpenRegionRotation.rotationSystem
      data.toRotationSystem keep outer).vertOf left =
      (GoertzelV24OpenRegionRotation.rotationSystem
        data.toRotationSystem keep outer).vertOf right at hfst
  change
    (GoertzelV24OpenRegionRotation.rotationSystem
      data.toRotationSystem keep outer).vertOf
        ((GoertzelV24OpenRegionRotation.rotationSystem
          data.toRotationSystem keep outer).alpha left) =
      (GoertzelV24OpenRegionRotation.rotationSystem
        data.toRotationSystem keep outer).vertOf
        ((GoertzelV24OpenRegionRotation.rotationSystem
          data.toRotationSystem keep outer).alpha right) at hsnd
  rcases left with left | left <;> rcases right with right | right
  · by_cases hleft : keep (data.toRotationSystem.vertOf
        (data.toRotationSystem.alpha left.1))
    · by_cases hright : keep (data.toRotationSystem.vertOf
          (data.toRotationSystem.alpha right.1))
      · have hfst : left.1.fst = right.1.fst := by
          simpa [toPrimalDart_fst] using hfst
        have hsnd : left.1.snd = right.1.snd := by
          rw [GoertzelV24OpenRegionRotation.rotationSystem_alpha_old_of_internal
              data.toRotationSystem keep outer left hleft,
            GoertzelV24OpenRegionRotation.rotationSystem_alpha_old_of_internal
              data.toRotationSystem keep outer right hright] at hsnd
          simpa [toPrimalDart_snd] using hsnd
        apply congrArg Sum.inl
        apply Subtype.ext
        exact SimpleGraph.Dart.ext _ _ (Prod.ext hfst hsnd)
      · exfalso
        rw [GoertzelV24OpenRegionRotation.rotationSystem_alpha_old_of_internal
              data.toRotationSystem keep outer left hleft,
            GoertzelV24OpenRegionRotation.rotationSystem_alpha_old_of_boundary
              data.toRotationSystem keep outer right hright] at hsnd
        simpa [toPrimalDart_snd] using hsnd
    · by_cases hright : keep (data.toRotationSystem.vertOf
          (data.toRotationSystem.alpha right.1))
      · exfalso
        rw [GoertzelV24OpenRegionRotation.rotationSystem_alpha_old_of_boundary
              data.toRotationSystem keep outer left hleft,
            GoertzelV24OpenRegionRotation.rotationSystem_alpha_old_of_internal
              data.toRotationSystem keep outer right hright] at hsnd
        simpa [toPrimalDart_snd] using hsnd
      · rw [GoertzelV24OpenRegionRotation.rotationSystem_alpha_old_of_boundary
              data.toRotationSystem keep outer left hleft,
            GoertzelV24OpenRegionRotation.rotationSystem_alpha_old_of_boundary
              data.toRotationSystem keep outer right hright] at hsnd
        change
          (Sum.inr (⟨left, hleft⟩ :
              GoertzelV24RotationCutDartDecomposition.BoundaryDart
                data.toRotationSystem keep) :
            GoertzelV24OpenRegionRotation.Vertex
              data.toRotationSystem keep) =
          Sum.inr ⟨right, hright⟩ at hsnd
        exact congrArg Sum.inl
          (congrArg Subtype.val (Sum.inr.inj hsnd))
  · exfalso
    simpa [toPrimalDart_fst] using hfst
  · exfalso
    simpa [toPrimalDart_fst] using hfst
  · have hboundary : left = right := by
      simpa [toPrimalDart_fst] using hfst
    exact congrArg Sum.inr hboundary

/-- Every oriented dart of the computed primal graph comes from an opened
dart. -/
theorem toPrimalDart_surjective
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : GoertzelV24OpenRegionRotation.Dart RS keep) :
    Function.Surjective (toPrimalDart RS keep outer) := by
  intro dart
  rcases dart.adj with ⟨source, hsource, htarget⟩
  refine ⟨source, ?_⟩
  exact SimpleGraph.Dart.ext _ _ (Prod.ext hsource htarget)

/-- Exact dart-carrier equivalence between a graph-backed ambient opening
and the simple primal graph computed from it. -/
def primalDartEquiv
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : SimpleGraphDartRotation.Data G) (keep : V → Prop)
    (outer : GoertzelV24OpenRegionRotation.Dart
      data.toRotationSystem keep) :
    GoertzelV24OpenRegionRotation.Dart data.toRotationSystem keep ≃
      (PrimalGraph data.toRotationSystem keep outer).Dart :=
  Equiv.ofBijective (toPrimalDart data.toRotationSystem keep outer)
    ⟨toPrimalDart_injective data keep outer,
      toPrimalDart_surjective data.toRotationSystem keep outer⟩

@[simp] theorem primalDartEquiv_apply
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : SimpleGraphDartRotation.Data G) (keep : V → Prop)
    (outer dart : GoertzelV24OpenRegionRotation.Dart
      data.toRotationSystem keep) :
    primalDartEquiv data keep outer dart =
      toPrimalDart data.toRotationSystem keep outer dart :=
  rfl

@[simp] theorem primalDartEquiv_fst
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : SimpleGraphDartRotation.Data G) (keep : V → Prop)
    (outer dart : GoertzelV24OpenRegionRotation.Dart
      data.toRotationSystem keep) :
    (primalDartEquiv data keep outer dart).fst =
      (GoertzelV24OpenRegionRotation.rotationSystem
        data.toRotationSystem keep outer).vertOf dart :=
  rfl

@[simp] theorem primalDartEquiv_symm_fst
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : SimpleGraphDartRotation.Data G) (keep : V → Prop)
    (outer : GoertzelV24OpenRegionRotation.Dart
      data.toRotationSystem keep)
    (dart : (PrimalGraph data.toRotationSystem keep outer).Dart) :
    (GoertzelV24OpenRegionRotation.rotationSystem
      data.toRotationSystem keep outer).vertOf
        ((primalDartEquiv data keep outer).symm dart) = dart.fst := by
  rw [← primalDartEquiv_fst data keep outer,
    Equiv.apply_symm_apply]

/-- Reversing a computed graph dart is exactly the transported literal-open
edge flip. -/
@[simp] theorem primalDartEquiv_alpha
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : SimpleGraphDartRotation.Data G) (keep : V → Prop)
    (outer dart : GoertzelV24OpenRegionRotation.Dart
      data.toRotationSystem keep) :
    primalDartEquiv data keep outer
        ((GoertzelV24OpenRegionRotation.rotationSystem
          data.toRotationSystem keep outer).alpha dart) =
      (primalDartEquiv data keep outer dart).symm := by
  apply SimpleGraph.Dart.ext
  apply Prod.ext
  · rfl
  · exact congrArg
      (GoertzelV24OpenRegionRotation.rotationSystem
        data.toRotationSystem keep outer).vertOf
      ((GoertzelV24OpenRegionRotation.rotationSystem
        data.toRotationSystem keep outer).alpha_involutive dart)

/-- Bare graph-backed rotation data on the simple graph computed from a
literal open region.  The cyclic order is transported, not postulated. -/
def graphData
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : SimpleGraphDartRotation.Data G) (keep : V → Prop)
    (outer : GoertzelV24OpenRegionRotation.Dart
      data.toRotationSystem keep) :
    SimpleGraphDartRotation.Data
      (PrimalGraph data.toRotationSystem keep outer) where
  vertexRotation :=
    (primalDartEquiv data keep outer).permCongr
      (GoertzelV24OpenRegionRotation.rotationSystem
        data.toRotationSystem keep outer).rho
  vertexRotation_fst := by
    intro dart
    change
      (primalDartEquiv data keep outer
        ((GoertzelV24OpenRegionRotation.rotationSystem
          data.toRotationSystem keep outer).rho
          ((primalDartEquiv data keep outer).symm dart))).fst = dart.fst
    rw [primalDartEquiv_fst,
      (GoertzelV24OpenRegionRotation.rotationSystem
        data.toRotationSystem keep outer).vert_rho,
      primalDartEquiv_symm_fst]
  outer := primalDartEquiv data keep outer outer

@[simp] theorem graphData_vertexRotation
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : SimpleGraphDartRotation.Data G) (keep : V → Prop)
    (outer : GoertzelV24OpenRegionRotation.Dart
      data.toRotationSystem keep)
    (dart : (PrimalGraph data.toRotationSystem keep outer).Dart) :
    (graphData data keep outer).vertexRotation dart =
      primalDartEquiv data keep outer
        ((GoertzelV24OpenRegionRotation.rotationSystem
          data.toRotationSystem keep outer).rho
          ((primalDartEquiv data keep outer).symm dart)) :=
  rfl

/-- The dart equivalence commutes with the literal and graph-backed vertex
rotations. -/
@[simp] theorem primalDartEquiv_rho
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : SimpleGraphDartRotation.Data G) (keep : V → Prop)
    (outer dart : GoertzelV24OpenRegionRotation.Dart
      data.toRotationSystem keep) :
    primalDartEquiv data keep outer
        ((GoertzelV24OpenRegionRotation.rotationSystem
          data.toRotationSystem keep outer).rho dart) =
      (graphData data keep outer).vertexRotation
        (primalDartEquiv data keep outer dart) := by
  rw [graphData_vertexRotation, Equiv.symm_apply_apply]

/-- Consequently the equivalence preserves facial steps, which is the
load-bearing compatibility for transporting quotient faces and facial-dual
crosscuts onto the computed simple graph. -/
@[simp] theorem primalDartEquiv_phi
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : SimpleGraphDartRotation.Data G) (keep : V → Prop)
    (outer dart : GoertzelV24OpenRegionRotation.Dart
      data.toRotationSystem keep) :
    primalDartEquiv data keep outer
        ((GoertzelV24OpenRegionRotation.rotationSystem
          data.toRotationSystem keep outer).phi dart) =
      (graphData data keep outer).vertexRotation
        (primalDartEquiv data keep outer dart).symm := by
  change primalDartEquiv data keep outer
      ((GoertzelV24OpenRegionRotation.rotationSystem
        data.toRotationSystem keep outer).rho
        ((GoertzelV24OpenRegionRotation.rotationSystem
          data.toRotationSystem keep outer).alpha dart)) =
    (graphData data keep outer).vertexRotation
      (primalDartEquiv data keep outer dart).symm
  rw [← primalDartEquiv_alpha data keep outer,
    ← primalDartEquiv_rho data keep outer]

/-- Opening a vertex region preserves the fact that every vertex rotation is
one cycle.  Retained vertices inherit their complete ambient dart fiber;
fresh boundary vertices have a singleton fiber. -/
theorem openRotation_vertexRotationCyclic
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : GoertzelV24OpenRegionRotation.Dart RS keep)
    (hcyclic : VertexRotationCyclic RS) :
    VertexRotationCyclic
      (GoertzelV24OpenRegionRotation.rotationSystem RS keep outer) := by
  intro left right hvertex
  rcases left with left | left <;> rcases right with right | right
  · have hambient : RS.rho.SameCycle left.1 right.1 := by
      apply hcyclic left.1 right.1
      exact congrArg Subtype.val (Sum.inl.inj hvertex)
    have hretained :
        (GoertzelV24RotationCutDartDecomposition.retainedRho RS keep).SameCycle
          left right :=
      Equiv.Perm.SameCycle.subtypePerm hambient
    rcases hretained with ⟨power, hpower⟩
    refine ⟨power, ?_⟩
    change
      ((Equiv.sumCongr
        (GoertzelV24RotationCutDartDecomposition.retainedRho RS keep)
        (Equiv.refl _)) ^ power) (Sum.inl left) = Sum.inl right
    have hmap := MonoidHom.map_zpow (Equiv.Perm.sumCongrHom _ _)
      (GoertzelV24RotationCutDartDecomposition.retainedRho RS keep,
        (1 : Equiv.Perm
          (GoertzelV24RotationCutDartDecomposition.BoundaryDart RS keep)))
      power
    calc
      _ = ((Equiv.Perm.sumCongrHom _ _)
          ((GoertzelV24RotationCutDartDecomposition.retainedRho RS keep,
            (1 : Equiv.Perm
              (GoertzelV24RotationCutDartDecomposition.BoundaryDart RS keep))) ^
            power)) (Sum.inl left) :=
        congrArg (fun permutation => permutation (Sum.inl left)) hmap.symm
      _ = Sum.inl
          (((GoertzelV24RotationCutDartDecomposition.retainedRho RS keep) ^
            power) left) := by simp
      _ = Sum.inl right := congrArg Sum.inl hpower
  · change Sum.inl _ = Sum.inr _ at hvertex
    exact (Sum.inl_ne_inr hvertex).elim
  · change Sum.inr _ = Sum.inl _ at hvertex
    exact (Sum.inr_ne_inl hvertex).elim
  · have hboundary : left = right := Sum.inr.inj hvertex
    subst right
    exact Equiv.Perm.SameCycle.rfl

/-- The graph-backed presentation inherits the same cyclic order at every
computed primal vertex.  This is the cyclic-rotation field required by the
later annular-cellulation package; connectedness and the two distinguished
hole faces remain source-specific formation obligations. -/
theorem graphData_hasCyclicVertexRotations
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : SimpleGraphDartRotation.Data G) (keep : V → Prop)
    (outer : GoertzelV24OpenRegionRotation.Dart
      data.toRotationSystem keep)
    (hcyclic : VertexRotationCyclic data.toRotationSystem) :
    ∀ vertex,
      (graphData data keep outer).vertexRotation.IsCycleOn
        {dart : (PrimalGraph data.toRotationSystem keep outer).Dart |
          dart.fst = vertex} := by
  intro vertex
  constructor
  · exact (graphData data keep outer).vertexRotation.bijOn fun dart => by
      change
        ((graphData data keep outer).vertexRotation dart).fst = vertex ↔
          dart.fst = vertex
      rw [(graphData data keep outer).vertexRotation_fst]
  · intro left hleft right hright
    have hopen := openRotation_vertexRotationCyclic
      data.toRotationSystem keep outer hcyclic
      ((primalDartEquiv data keep outer).symm left)
      ((primalDartEquiv data keep outer).symm right) (by
        rw [primalDartEquiv_symm_fst, primalDartEquiv_symm_fst]
        exact hleft.trans hright.symm)
    rcases hopen with ⟨power, hpower⟩
    refine ⟨power, ?_⟩
    change
      (((primalDartEquiv data keep outer).permCongr
        (GoertzelV24OpenRegionRotation.rotationSystem
          data.toRotationSystem keep outer).rho) ^ power) left = right
    have hmap := MonoidHom.map_zpow
      (primalDartEquiv data keep outer).permCongrHom.toMonoidHom
      (GoertzelV24OpenRegionRotation.rotationSystem
        data.toRotationSystem keep outer).rho power
    calc
      _ = ((primalDartEquiv data keep outer).permCongr
          ((GoertzelV24OpenRegionRotation.rotationSystem
            data.toRotationSystem keep outer).rho ^ power)) left :=
        congrArg (fun permutation => permutation left) hmap.symm
      _ = primalDartEquiv data keep outer
          (((GoertzelV24OpenRegionRotation.rotationSystem
            data.toRotationSystem keep outer).rho ^ power)
            ((primalDartEquiv data keep outer).symm left)) := rfl
      _ = primalDartEquiv data keep outer
          ((primalDartEquiv data keep outer).symm right) :=
        congrArg (primalDartEquiv data keep outer) hpower
      _ = right := (primalDartEquiv data keep outer).apply_symm_apply right

/-- Retained ambient adjacency is retained by the literal opening.  This is
the graph-level inclusion used to transport paths inside the chosen region. -/
theorem primalGraph_adj_retained
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : GoertzelV24OpenRegionRotation.Dart RS keep)
    {left right : GoertzelV24OpenRegionRotation.RetainedVertex keep}
    (hadj : ((rotationPrimalGraph RS).induce {vertex | keep vertex}).Adj
      left right) :
    (PrimalGraph RS keep outer).Adj (Sum.inl left) (Sum.inl right) := by
  change (rotationPrimalGraph RS).Adj left.1 right.1 at hadj
  rw [rotationPrimalGraph_adj_iff] at hadj
  rw [rotationPrimalGraph_adj_iff]
  rcases hadj with ⟨dart, hleft, hright⟩
  have hkeepLeft : keep (RS.vertOf dart) := by
    simpa [hleft] using left.2
  have hkeepRight : keep (RS.vertOf (RS.alpha dart)) := by
    simpa [hright] using right.2
  refine ⟨Sum.inl ⟨dart, hkeepLeft⟩, ?_, ?_⟩
  · exact congrArg Sum.inl (Subtype.ext hleft)
  · rw [GoertzelV24OpenRegionRotation.rotationSystem_alpha_old_of_internal
      RS keep outer ⟨dart, hkeepLeft⟩ hkeepRight]
    exact congrArg Sum.inl (Subtype.ext hright)

/-- The transparent inclusion of the retained induced graph into the literal
open primal graph. -/
def retainedPrimalHom
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : GoertzelV24OpenRegionRotation.Dart RS keep) :
    ((rotationPrimalGraph RS).induce {vertex | keep vertex}) →g
      PrimalGraph RS keep outer where
  toFun := Sum.inl
  map_rel' := fun {_ _} hadj => primalGraph_adj_retained RS keep outer hadj

@[simp] theorem retainedPrimalHom_apply
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : GoertzelV24OpenRegionRotation.Dart RS keep)
    (vertex : GoertzelV24OpenRegionRotation.RetainedVertex keep) :
    retainedPrimalHom RS keep outer vertex = Sum.inl vertex :=
  rfl

/-- Every fresh boundary vertex is joined to the retained endpoint of the
ambient half-dart that created it. -/
theorem primalGraph_adj_boundary_retained
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : GoertzelV24OpenRegionRotation.Dart RS keep)
    (boundary : GoertzelV24RotationCutDartDecomposition.BoundaryDart RS keep) :
    (PrimalGraph RS keep outer).Adj (Sum.inr boundary)
      (Sum.inl
        (⟨RS.vertOf boundary.1.1, boundary.1.2⟩ :
          GoertzelV24OpenRegionRotation.RetainedVertex keep)) := by
  rw [rotationPrimalGraph_adj_iff]
  refine ⟨Sum.inr boundary, rfl, ?_⟩
  rw [GoertzelV24OpenRegionRotation.rotationSystem_alpha_stub]
  rfl

/-- Opening a connected retained region by attaching one fresh leaf at each
exposed half-edge preserves connectedness.  This supplies the connectedness
field needed by a later concrete annular-cellulation constructor; choosing the
Cell--3 region and proving that its two hole faces are the intended ones remain
source-specific obligations. -/
theorem primalGraph_connected_of_retained
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : GoertzelV24OpenRegionRotation.Dart RS keep)
    (hconnected :
      ((rotationPrimalGraph RS).induce {vertex | keep vertex}).Connected) :
    (PrimalGraph RS keep outer).Connected := by
  letI : Nonempty (GoertzelV24OpenRegionRotation.RetainedVertex keep) :=
    hconnected.nonempty
  let root : GoertzelV24OpenRegionRotation.RetainedVertex keep :=
    Classical.choice (inferInstance :
      Nonempty (GoertzelV24OpenRegionRotation.RetainedVertex keep))
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨Sum.inl root, ?_⟩
  intro vertex
  rcases vertex with retained | boundary
  · exact (hconnected root retained).map (retainedPrimalHom RS keep outer)
  · let anchor : GoertzelV24OpenRegionRotation.RetainedVertex keep :=
      ⟨RS.vertOf boundary.1.1, boundary.1.2⟩
    have hanchor :
        (PrimalGraph RS keep outer).Reachable (Sum.inl root) (Sum.inl anchor) :=
      (hconnected root anchor).map (retainedPrimalHom RS keep outer)
    exact hanchor.trans
      (primalGraph_adj_boundary_retained RS keep outer boundary).symm.reachable

end

end GoertzelV24OpenRegionGraphBacking

end Mettapedia.GraphTheory.FourColor

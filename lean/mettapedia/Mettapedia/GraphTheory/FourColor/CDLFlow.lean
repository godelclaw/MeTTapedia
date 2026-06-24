import Mettapedia.GraphTheory.FourColor.KempeCycles
import Mettapedia.GraphTheory.FourColor.RotationDiskData
import Mettapedia.GraphTheory.FourColor.Theorem49TargetSubspace

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-!
# CDL-style flow layer for the Goertzel 4CP route

The latest benxiv 4CP manuscript phrases the new route in terms of
`F2^2`-flows and a local CDL-goodness condition.  This file gives that
language a small Lean surface over the existing FourColor color algebra and
Kirchhoff-incidence API.
-/

/-- An `F2^2` graph flow: the incident edge-values sum to zero at every vertex. -/
def IsGraphFlow (G : SimpleGraph V) [Fintype G.edgeSet] (x : G.edgeSet → Color) : Prop :=
  ∀ v : V, vertexKirchhoffSum G x v = 0

/-- Local CDL-goodness for the canonical cubic-vertex gadget: the incident edge
triple is not the all-zero pattern.  On cubic graphs this is the manuscript's
"not CDL-bad at the vertex" condition. -/
def IsCDLGoodAtVertex (G : SimpleGraph V) [Fintype G.edgeSet]
    (x : G.edgeSet → Color) (v : V) : Prop :=
  ∃ e ∈ incidentEdgeFinset G v, x e ≠ 0

/-- A CDL-good flow on all vertices.  For disk patches, later files should use
the same local predicate restricted to the patch's interior vertices. -/
def IsCDLGoodFlow (G : SimpleGraph V) [Fintype G.edgeSet]
    (x : G.edgeSet → Color) : Prop :=
  IsGraphFlow G x ∧ ∀ v : V, IsCDLGoodAtVertex G x v

/-- A nowhere-zero graph flow.  On a bridgeless cubic graph, this is the
flow-side form of a Tait coloring used by the manuscript. -/
def IsNowhereZeroFlow (G : SimpleGraph V) [Fintype G.edgeSet]
    (x : G.edgeSet → Color) : Prop :=
  IsGraphFlow G x ∧ ∀ e : G.edgeSet, x e ≠ 0

/-- The finite set of edges where a flow/chain takes the zero color.  The
manuscript's nowhere-zero flow surface is equivalently the case where this set
is empty. -/
def zeroEdgeFinset (G : SimpleGraph V) [Fintype G.edgeSet]
    (x : G.edgeSet → Color) : Finset G.edgeSet :=
  Finset.univ.filter fun e => x e = 0

/-- The manuscript's zero-edge defect count `Z(x)`. -/
def zeroEdgeCount (G : SimpleGraph V) [Fintype G.edgeSet]
    (x : G.edgeSet → Color) : Nat :=
  (zeroEdgeFinset G x).card

/-- The same zero-edge set, but viewed in the ambient `Sym2 V` edge type. -/
def zeroEdgeSym2Finset (G : SimpleGraph V) [Fintype G.edgeSet]
    (x : G.edgeSet → Color) : Finset (Sym2 V) :=
  (zeroEdgeFinset G x).map
    (Function.Embedding.subtype (fun e : Sym2 V => e ∈ G.edgeSet))

/-- The graph consisting exactly of the zero-valued edges of a chain.  This is
the graph-theoretic object behind the manuscript's zero pattern `Z(x)`. -/
abbrev zeroEdgeGraph (G : SimpleGraph V) [Fintype G.edgeSet]
    (x : G.edgeSet → Color) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (zeroEdgeSym2Finset G x : Set (Sym2 V))

/-- The zero-valued edges incident to a vertex.  This is the finite set whose
cardinality is the manuscript's local statistic `k_v(x)`. -/
def zeroIncidentEdgeFinset (G : SimpleGraph V) [Fintype G.edgeSet]
    (x : G.edgeSet → Color) (v : V) : Finset G.edgeSet :=
  (incidentEdgeFinset G v).filter fun e => x e = 0

/-- The manuscript's local statistic `k_v(x)`: the number of zero-valued edges
incident to `v`. -/
def zeroIncidentEdgeCount (G : SimpleGraph V) [Fintype G.edgeSet]
    (x : G.edgeSet → Color) (v : V) : Nat :=
  (zeroIncidentEdgeFinset G x v).card

/-- Vertices incident to at least one zero-valued edge. -/
def zeroIncidentVertexFinset (G : SimpleGraph V) [Fintype V] [Fintype G.edgeSet]
    (x : G.edgeSet → Color) : Finset V :=
  Finset.univ.filter fun v => 0 < zeroIncidentEdgeCount G x v

/-- The manuscript's defect statistic `I(x)`: vertices touched by zero edges. -/
def zeroIncidentVertexCount (G : SimpleGraph V) [Fintype V] [Fintype G.edgeSet]
    (x : G.edgeSet → Color) : Nat :=
  (zeroIncidentVertexFinset G x).card

/-- The manuscript's clustering statistic `C(x) = ∑_v max(0, k_v(x)-1)`.
Natural-number subtraction implements the truncated maximum. -/
def zeroClusteringCount (G : SimpleGraph V) [Fintype V] [Fintype G.edgeSet]
    (x : G.edgeSet → Color) : Nat :=
  Finset.univ.sum fun v => zeroIncidentEdgeCount G x v - 1

/-- The manuscript's cheap defect score `D₀(x)=100 Z(x)+10 I(x)+C(x)`. -/
def zeroDefectD0 (G : SimpleGraph V) [Fintype V] [Fintype G.edgeSet]
    (x : G.edgeSet → Color) : Nat :=
  100 * zeroEdgeCount G x + 10 * zeroIncidentVertexCount G x + zeroClusteringCount G x

theorem zeroDefectD0_lt_of_one_zero_removed_and_side_budget
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {x y : G.edgeSet → Color} {dI dC : Nat}
    (hZ : zeroEdgeCount G y + 1 ≤ zeroEdgeCount G x)
    (hI : zeroIncidentVertexCount G y ≤ zeroIncidentVertexCount G x + dI)
    (hC : zeroClusteringCount G y ≤ zeroClusteringCount G x + dC)
    (hbudget : 10 * dI + dC < 100) :
    zeroDefectD0 G y < zeroDefectD0 G x := by
  unfold zeroDefectD0
  omega

/-- Add a fixed nonzero color on a selected finite edge support.  In the
manuscript this is the abstract `x + g · 1_C` one-step move; cycle and patch
conditions are supplied separately by the caller. -/
def cdlOneStepMoveOn (G : SimpleGraph V) [Fintype G.edgeSet]
    (C : Finset G.edgeSet) (g : Color) (x : G.edgeSet → Color) :
    G.edgeSet → Color :=
  fun e => if e ∈ C then x e + g else x e

/-- A support is Kirchhoff-neutral when it meets the incident edge set of every
vertex in even cardinality.  Cycle supports satisfy this condition; patch files
can prove it from their concrete cycle data. -/
def IsKirchhoffNeutralMoveSupport (G : SimpleGraph V) [Fintype G.edgeSet]
    (C : Finset G.edgeSet) : Prop :=
  ∀ v : V, Even ((incidentEdgeFinset G v).filter fun e => e ∈ C).card

theorem isKirchhoffNeutralMoveSupport_of_even_inter_incidentEdgeFinset
    {G : SimpleGraph V} [Fintype G.edgeSet] {C : Finset G.edgeSet}
    (hC : ∀ v : V, Even (C ∩ incidentEdgeFinset G v).card) :
    IsKirchhoffNeutralMoveSupport G C := by
  intro v
  have hfilter :
      (incidentEdgeFinset G v).filter (fun e => e ∈ C) =
        C ∩ incidentEdgeFinset G v := by
    ext e
    simp [and_comm]
  rw [hfilter]
  exact hC v

theorem isKirchhoffNeutralMoveSupport_of_even_incidentEdgeFinset_inter
    {G : SimpleGraph V} [Fintype G.edgeSet] {C : Finset G.edgeSet}
    (hC : ∀ v : V, Even (incidentEdgeFinset G v ∩ C).card) :
    IsKirchhoffNeutralMoveSupport G C := by
  apply isKirchhoffNeutralMoveSupport_of_even_inter_incidentEdgeFinset
  intro v
  rw [Finset.inter_comm]
  exact hC v

theorem isKirchhoffNeutralMoveSupport_of_even_inter_incident
    {G : SimpleGraph V} [Fintype G.edgeSet] {C : Finset G.edgeSet}
    (incident : V → Finset G.edgeSet)
    (hincident : ∀ v : V, incident v = incidentEdgeFinset G v)
    (hC : ∀ v : V, Even (C ∩ incident v).card) :
    IsKirchhoffNeutralMoveSupport G C := by
  apply isKirchhoffNeutralMoveSupport_of_even_inter_incidentEdgeFinset
  intro v
  simpa [hincident v] using hC v

theorem isKirchhoffNeutralMoveSupport_of_even_incident_inter
    {G : SimpleGraph V} [Fintype G.edgeSet] {C : Finset G.edgeSet}
    (incident : V → Finset G.edgeSet)
    (hincident : ∀ v : V, incident v = incidentEdgeFinset G v)
    (hC : ∀ v : V, Even (incident v ∩ C).card) :
    IsKirchhoffNeutralMoveSupport G C := by
  apply isKirchhoffNeutralMoveSupport_of_even_inter_incident
    (incident := incident) hincident
  intro v
  rw [Finset.inter_comm]
  exact hC v

theorem isKirchhoffNeutralMoveSupport_of_isKempeCycle_incident
    {G : SimpleGraph V} [Fintype G.edgeSet] {x : G.edgeSet → Color}
    {C : Finset G.edgeSet} {α β : Color}
    (incident : V → Finset G.edgeSet)
    (hincident : ∀ v : V, incident v = incidentEdgeFinset G v)
    (hC : IsKempeCycle incident x C α β) :
    IsKirchhoffNeutralMoveSupport G C := by
  apply isKirchhoffNeutralMoveSupport_of_even_inter_incident incident hincident
  intro v
  have hfilter :
      (C ∩ incident v).filter (fun e => x e = α ∨ x e = β) =
        C ∩ incident v :=
    kempeSubgraph_filter_incidence_eq incident x C α β hC.1 v
  rw [← hfilter]
  exact kempeCycle_even_at incident x C α β hC v

theorem isKirchhoffNeutralMoveSupport_of_isKempeCycle
    {G : SimpleGraph V} [Fintype G.edgeSet] {x : G.edgeSet → Color}
    {C : Finset G.edgeSet} {α β : Color}
    (hC : IsKempeCycle (incidentEdgeFinset G) x C α β) :
    IsKirchhoffNeutralMoveSupport G C :=
  isKirchhoffNeutralMoveSupport_of_isKempeCycle_incident
    (incident := incidentEdgeFinset G) (fun _ => rfl) hC

theorem isKirchhoffNeutralMoveSupport_of_rotationDiskData_internalFace
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    (D : RotationDiskData V G.edgeSet)
    (hincident : ∀ v : V, D.asZeroBoundary.incident v = incidentEdgeFinset G v)
    {f : Finset G.edgeSet} (hf : f ∈ D.rotation.internalFaces) :
    IsKirchhoffNeutralMoveSupport G f := by
  apply isKirchhoffNeutralMoveSupport_of_even_incident_inter
    (incident := D.asZeroBoundary.incident) hincident
  exact D.face_cycle_parity hf

theorem isKirchhoffNeutralMoveSupport_empty
    {G : SimpleGraph V} [Fintype G.edgeSet] :
    IsKirchhoffNeutralMoveSupport G ∅ := by
  intro v
  simp

theorem isKirchhoffNeutralMoveSupport_union_of_disjoint
    {G : SimpleGraph V} [Fintype G.edgeSet] {C D : Finset G.edgeSet}
    (hC : IsKirchhoffNeutralMoveSupport G C)
    (hD : IsKirchhoffNeutralMoveSupport G D)
    (hdisj : Disjoint C D) :
    IsKirchhoffNeutralMoveSupport G (C ∪ D) := by
  intro v
  let IC := (incidentEdgeFinset G v).filter fun e => e ∈ C
  let ID := (incidentEdgeFinset G v).filter fun e => e ∈ D
  have hfilter :
      ((incidentEdgeFinset G v).filter fun e => e ∈ C ∪ D).card =
        IC.card + ID.card := by
    have hsets :
        (incidentEdgeFinset G v).filter (fun e => e ∈ C ∪ D) = IC ∪ ID := by
      ext e
      simp [IC, ID, and_or_left]
    have hdisj_filter : Disjoint IC ID := by
      rw [Finset.disjoint_left]
      intro e heC heD
      have heCmem : e ∈ C := by
        have hpair : e ∈ incidentEdgeFinset G v ∧ e ∈ C := by
          simpa [IC] using heC
        exact hpair.2
      have heDmem : e ∈ D := by
        have hpair : e ∈ incidentEdgeFinset G v ∧ e ∈ D := by
          simpa [ID] using heD
        exact hpair.2
      exact (Finset.disjoint_left.mp hdisj) heCmem heDmem
    rw [hsets, Finset.card_union_of_disjoint hdisj_filter]
  rw [hfilter]
  exact (hC v).add (hD v)

@[simp] theorem cdlOneStepMoveOn_apply_mem {G : SimpleGraph V} [Fintype G.edgeSet]
    {C : Finset G.edgeSet} {g : Color} {x : G.edgeSet → Color} {e : G.edgeSet}
    (he : e ∈ C) :
    cdlOneStepMoveOn G C g x e = x e + g := by
  simp [cdlOneStepMoveOn, he]

@[simp] theorem cdlOneStepMoveOn_apply_not_mem {G : SimpleGraph V} [Fintype G.edgeSet]
    {C : Finset G.edgeSet} {g : Color} {x : G.edgeSet → Color} {e : G.edgeSet}
    (he : e ∉ C) :
    cdlOneStepMoveOn G C g x e = x e := by
  simp [cdlOneStepMoveOn, he]

theorem cdlOneStepMoveOn_apply_mem_eq_zero_iff
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {C : Finset G.edgeSet} {g : Color} {x : G.edgeSet → Color} {e : G.edgeSet}
    (he : e ∈ C) :
    cdlOneStepMoveOn G C g x e = 0 ↔ x e = g := by
  rw [cdlOneStepMoveOn_apply_mem he, add_eq_zero_iff_eq]

theorem cdlOneStepMoveOn_apply_not_mem_eq_zero_iff
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {C : Finset G.edgeSet} {g : Color} {x : G.edgeSet → Color} {e : G.edgeSet}
    (he : e ∉ C) :
    cdlOneStepMoveOn G C g x e = 0 ↔ x e = 0 := by
  rw [cdlOneStepMoveOn_apply_not_mem he]

theorem cdlOneStepMoveOn_apply_mem_ne_zero_of_eq_zero
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {C : Finset G.edgeSet} {g : Color} {x : G.edgeSet → Color} {e : G.edgeSet}
    (hg : g ≠ 0) (he : e ∈ C) (hx : x e = 0) :
    cdlOneStepMoveOn G C g x e ≠ 0 := by
  rw [cdlOneStepMoveOn_apply_mem he, hx]
  simpa using hg

theorem cdlOneStepMoveOn_apply_mem_eq_zero_of_eq_color
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {C : Finset G.edgeSet} {g : Color} {x : G.edgeSet → Color} {e : G.edgeSet}
    (he : e ∈ C) (hx : x e = g) :
    cdlOneStepMoveOn G C g x e = 0 := by
  rw [cdlOneStepMoveOn_apply_mem he, hx, color_add_self]

theorem zeroEdgeFinset_cdlOneStepMoveOn_eq
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {C : Finset G.edgeSet} {g : Color} {x : G.edgeSet → Color} :
    zeroEdgeFinset G (cdlOneStepMoveOn G C g x) =
      (zeroEdgeFinset G x).filter (fun e => e ∉ C) ∪ C.filter (fun e => x e = g) := by
  ext e
  by_cases heC : e ∈ C
  · simp [zeroEdgeFinset, cdlOneStepMoveOn, heC, add_eq_zero_iff_eq]
  · simp [zeroEdgeFinset, cdlOneStepMoveOn, heC]

theorem zeroEdgeCount_cdlOneStepMoveOn_eq
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {C : Finset G.edgeSet} {g : Color} {x : G.edgeSet → Color} :
    zeroEdgeCount G (cdlOneStepMoveOn G C g x) =
      ((zeroEdgeFinset G x).filter (fun e => e ∉ C)).card +
        (C.filter (fun e => x e = g)).card := by
  rw [zeroEdgeCount, zeroEdgeFinset_cdlOneStepMoveOn_eq]
  rw [Finset.card_union_of_disjoint]
  rw [Finset.disjoint_left]
  intro e heZero heC
  exact (Finset.mem_filter.mp heZero).2 (Finset.mem_filter.mp heC).1

theorem isCDLGoodAtVertex_cdlOneStepMoveOn_iff
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {C : Finset G.edgeSet} {g : Color} {x : G.edgeSet → Color} {v : V} :
    IsCDLGoodAtVertex G (cdlOneStepMoveOn G C g x) v ↔
      ∃ e ∈ incidentEdgeFinset G v, if e ∈ C then x e ≠ g else x e ≠ 0 := by
  constructor
  · rintro ⟨e, heinc, hne⟩
    refine ⟨e, heinc, ?_⟩
    by_cases heC : e ∈ C
    · simp [heC]
      intro hx
      exact hne (cdlOneStepMoveOn_apply_mem_eq_zero_of_eq_color heC hx)
    · simp [heC]
      intro hx
      exact hne (by rw [cdlOneStepMoveOn_apply_not_mem heC, hx])
  · rintro ⟨e, heinc, hwitness⟩
    refine ⟨e, heinc, ?_⟩
    by_cases heC : e ∈ C
    · have hx : x e ≠ g := by simpa [heC] using hwitness
      intro hzero
      exact hx ((cdlOneStepMoveOn_apply_mem_eq_zero_iff heC).mp hzero)
    · have hx : x e ≠ 0 := by simpa [heC] using hwitness
      intro hzero
      exact hx ((cdlOneStepMoveOn_apply_not_mem_eq_zero_iff heC).mp hzero)

theorem isCDLGoodAtVertex_cdlOneStepMoveOn_of_outside_witness
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {C : Finset G.edgeSet} {g : Color} {x : G.edgeSet → Color} {v : V}
    (h : ∃ e ∈ incidentEdgeFinset G v, e ∉ C ∧ x e ≠ 0) :
    IsCDLGoodAtVertex G (cdlOneStepMoveOn G C g x) v := by
  apply isCDLGoodAtVertex_cdlOneStepMoveOn_iff.mpr
  rcases h with ⟨e, heinc, heC, hx⟩
  exact ⟨e, heinc, by simpa [heC] using hx⟩

theorem isCDLGoodAtVertex_cdlOneStepMoveOn_of_inside_witness
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {C : Finset G.edgeSet} {g : Color} {x : G.edgeSet → Color} {v : V}
    (h : ∃ e ∈ incidentEdgeFinset G v, e ∈ C ∧ x e ≠ g) :
    IsCDLGoodAtVertex G (cdlOneStepMoveOn G C g x) v := by
  apply isCDLGoodAtVertex_cdlOneStepMoveOn_iff.mpr
  rcases h with ⟨e, heinc, heC, hx⟩
  exact ⟨e, heinc, by simpa [heC] using hx⟩

theorem not_isCDLGoodAtVertex_cdlOneStepMoveOn_iff
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {C : Finset G.edgeSet} {g : Color} {x : G.edgeSet → Color} {v : V} :
    ¬ IsCDLGoodAtVertex G (cdlOneStepMoveOn G C g x) v ↔
      ∀ e ∈ incidentEdgeFinset G v, if e ∈ C then x e = g else x e = 0 := by
  rw [isCDLGoodAtVertex_cdlOneStepMoveOn_iff]
  constructor
  · intro h e heinc
    by_cases heC : e ∈ C
    · by_contra hne
      exact h ⟨e, heinc, by simpa [heC] using hne⟩
    · by_contra hne
      exact h ⟨e, heinc, by simpa [heC] using hne⟩
  · intro h hgood
    rcases hgood with ⟨e, heinc, hwitness⟩
    specialize h e heinc
    by_cases heC : e ∈ C
    · have hx : x e ≠ g := by simpa [heC] using hwitness
      exact hx (by simpa [heC] using h)
    · have hx : x e ≠ 0 := by simpa [heC] using hwitness
      exact hx (by simpa [heC] using h)

theorem vertexKirchhoffSum_cdlOneStepMoveOn_eq
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (C : Finset G.edgeSet) (g : Color) (x : G.edgeSet → Color) (v : V) :
    vertexKirchhoffSum G (cdlOneStepMoveOn G C g x) v =
      vertexKirchhoffSum G x v +
        ((incidentEdgeFinset G v).filter fun e => e ∈ C).card • g := by
  unfold vertexKirchhoffSum
  calc
    ∑ e ∈ incidentEdgeFinset G v, cdlOneStepMoveOn G C g x e
        = ∑ e ∈ incidentEdgeFinset G v, (x e + if e ∈ C then g else 0) := by
          refine Finset.sum_congr rfl ?_
          intro e _he
          by_cases heC : e ∈ C <;> simp [cdlOneStepMoveOn, heC]
    _ = (∑ e ∈ incidentEdgeFinset G v, x e) +
          ∑ e ∈ incidentEdgeFinset G v, (if e ∈ C then g else 0) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ e ∈ incidentEdgeFinset G v, x e) +
          ∑ e ∈ (incidentEdgeFinset G v).filter (fun e => e ∈ C), g := by
          congr 1
          rw [← Finset.sum_filter]
    _ = (∑ e ∈ incidentEdgeFinset G v, x e) +
          ((incidentEdgeFinset G v).filter fun e => e ∈ C).card • g := by
          rw [sum_const]

theorem isGraphFlow_cdlOneStepMoveOn_of_kirchhoffNeutral
    {G : SimpleGraph V} [Fintype G.edgeSet] {C : Finset G.edgeSet}
    {g : Color} {x : G.edgeSet → Color}
    (hx : IsGraphFlow G x) (hC : IsKirchhoffNeutralMoveSupport G C) :
    IsGraphFlow G (cdlOneStepMoveOn G C g x) := by
  intro v
  rw [vertexKirchhoffSum_cdlOneStepMoveOn_eq]
  rw [hx v, nsmul_even_eq_zero (hC v)]
  simp

/-- A permitted manuscript one-step move on a selected edge support.  This
records the target assignment, the nonzero move color, and the two semantic
checks that are not automatic for an arbitrary support: Kirchhoff and CDL
goodness. -/
structure IsAllowedD0OneStepMoveOn (G : SimpleGraph V) [Fintype G.edgeSet]
    (C : Finset G.edgeSet) (g : Color) (x y : G.edgeSet → Color) : Prop where
  color_ne_zero : g ≠ 0
  target_eq : y = cdlOneStepMoveOn G C g x
  target_flow : IsGraphFlow G y
  target_good : ∀ v : V, IsCDLGoodAtVertex G y v

theorem isAllowedD0OneStepMoveOn_of_kirchhoffNeutral
    {G : SimpleGraph V} [Fintype G.edgeSet] {C : Finset G.edgeSet}
    {g : Color} {x : G.edgeSet → Color}
    (hg : g ≠ 0) (hx : IsGraphFlow G x)
    (hC : IsKirchhoffNeutralMoveSupport G C)
    (hgood : ∀ v : V, IsCDLGoodAtVertex G (cdlOneStepMoveOn G C g x) v) :
    IsAllowedD0OneStepMoveOn G C g x (cdlOneStepMoveOn G C g x) where
  color_ne_zero := hg
  target_eq := rfl
  target_flow := isGraphFlow_cdlOneStepMoveOn_of_kirchhoffNeutral hx hC
  target_good := hgood

theorem isAllowedD0OneStepMoveOn_of_kirchhoffNeutral_and_vertex_witnesses
    {G : SimpleGraph V} [Fintype G.edgeSet] {C : Finset G.edgeSet}
    {g : Color} {x : G.edgeSet → Color}
    (hg : g ≠ 0) (hx : IsGraphFlow G x)
    (hC : IsKirchhoffNeutralMoveSupport G C)
    (hgood :
      ∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
        if e ∈ C then x e ≠ g else x e ≠ 0) :
    IsAllowedD0OneStepMoveOn G C g x (cdlOneStepMoveOn G C g x) := by
  apply isAllowedD0OneStepMoveOn_of_kirchhoffNeutral hg hx hC
  intro v
  exact isCDLGoodAtVertex_cdlOneStepMoveOn_iff.mpr (hgood v)

theorem isAllowedD0OneStepMoveOn_of_kirchhoffNeutral_and_outside_witnesses
    {G : SimpleGraph V} [Fintype G.edgeSet] {C : Finset G.edgeSet}
    {g : Color} {x : G.edgeSet → Color}
    (hg : g ≠ 0) (hx : IsGraphFlow G x)
    (hC : IsKirchhoffNeutralMoveSupport G C)
    (hgood : ∀ v : V, ∃ e ∈ incidentEdgeFinset G v, e ∉ C ∧ x e ≠ 0) :
    IsAllowedD0OneStepMoveOn G C g x (cdlOneStepMoveOn G C g x) := by
  apply isAllowedD0OneStepMoveOn_of_kirchhoffNeutral hg hx hC
  intro v
  exact isCDLGoodAtVertex_cdlOneStepMoveOn_of_outside_witness (hgood v)

theorem isAllowedD0OneStepMoveOn_iff_target_good_of_kirchhoffNeutral
    {G : SimpleGraph V} [Fintype G.edgeSet] {C : Finset G.edgeSet}
    {g : Color} {x : G.edgeSet → Color}
    (hg : g ≠ 0) (hx : IsGraphFlow G x)
    (hC : IsKirchhoffNeutralMoveSupport G C) :
    IsAllowedD0OneStepMoveOn G C g x (cdlOneStepMoveOn G C g x) ↔
      ∀ v : V, IsCDLGoodAtVertex G (cdlOneStepMoveOn G C g x) v := by
  constructor
  · exact fun h => h.target_good
  · exact isAllowedD0OneStepMoveOn_of_kirchhoffNeutral hg hx hC

theorem not_isAllowedD0OneStepMoveOn_iff_exists_bad_vertex_of_kirchhoffNeutral
    {G : SimpleGraph V} [Fintype G.edgeSet] {C : Finset G.edgeSet}
    {g : Color} {x : G.edgeSet → Color}
    (hg : g ≠ 0) (hx : IsGraphFlow G x)
    (hC : IsKirchhoffNeutralMoveSupport G C) :
    ¬ IsAllowedD0OneStepMoveOn G C g x (cdlOneStepMoveOn G C g x) ↔
      ∃ v : V, ¬ IsCDLGoodAtVertex G (cdlOneStepMoveOn G C g x) v := by
  rw [isAllowedD0OneStepMoveOn_iff_target_good_of_kirchhoffNeutral hg hx hC]
  constructor
  · intro h
    by_contra hbad
    apply h
    intro v
    by_contra hv
    exact hbad ⟨v, hv⟩
  · rintro ⟨v, hv⟩ hgood
    exact hv (hgood v)

theorem not_isAllowedD0OneStepMoveOn_iff_exists_vertex_forced_zero_of_kirchhoffNeutral
    {G : SimpleGraph V} [Fintype G.edgeSet] {C : Finset G.edgeSet}
    {g : Color} {x : G.edgeSet → Color}
    (hg : g ≠ 0) (hx : IsGraphFlow G x)
    (hC : IsKirchhoffNeutralMoveSupport G C) :
    ¬ IsAllowedD0OneStepMoveOn G C g x (cdlOneStepMoveOn G C g x) ↔
      ∃ v : V, ∀ e ∈ incidentEdgeFinset G v,
        if e ∈ C then x e = g else x e = 0 := by
  rw [not_isAllowedD0OneStepMoveOn_iff_exists_bad_vertex_of_kirchhoffNeutral hg hx hC]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, (not_isCDLGoodAtVertex_cdlOneStepMoveOn_iff.mp hv)⟩
  · rintro ⟨v, hv⟩
    exact ⟨v, (not_isCDLGoodAtVertex_cdlOneStepMoveOn_iff.mpr hv)⟩

theorem isAllowedD0OneStepMoveOn_of_isKempeCycle_and_vertex_witnesses
    {G : SimpleGraph V} [Fintype G.edgeSet] {C : Finset G.edgeSet}
    {g : Color} {x : G.edgeSet → Color} {α β : Color}
    (hg : g ≠ 0) (hx : IsGraphFlow G x)
    (hC : IsKempeCycle (incidentEdgeFinset G) x C α β)
    (hgood :
      ∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
        if e ∈ C then x e ≠ g else x e ≠ 0) :
    IsAllowedD0OneStepMoveOn G C g x (cdlOneStepMoveOn G C g x) := by
  exact isAllowedD0OneStepMoveOn_of_kirchhoffNeutral_and_vertex_witnesses
    hg hx (isKirchhoffNeutralMoveSupport_of_isKempeCycle hC) hgood

theorem isAllowedD0OneStepMoveOn_of_isKempeCycle_and_outside_witnesses
    {G : SimpleGraph V} [Fintype G.edgeSet] {C : Finset G.edgeSet}
    {g : Color} {x : G.edgeSet → Color} {α β : Color}
    (hg : g ≠ 0) (hx : IsGraphFlow G x)
    (hC : IsKempeCycle (incidentEdgeFinset G) x C α β)
    (hgood : ∀ v : V, ∃ e ∈ incidentEdgeFinset G v, e ∉ C ∧ x e ≠ 0) :
    IsAllowedD0OneStepMoveOn G C g x (cdlOneStepMoveOn G C g x) := by
  exact isAllowedD0OneStepMoveOn_of_kirchhoffNeutral_and_outside_witnesses
    hg hx (isKirchhoffNeutralMoveSupport_of_isKempeCycle hC) hgood

theorem isAllowedD0OneStepMoveOn_of_rotationDiskData_internalFace_and_vertex_witnesses
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    (D : RotationDiskData V G.edgeSet)
    (hincident : ∀ v : V, D.asZeroBoundary.incident v = incidentEdgeFinset G v)
    {f : Finset G.edgeSet} (hf : f ∈ D.rotation.internalFaces)
    {g : Color} {x : G.edgeSet → Color}
    (hg : g ≠ 0) (hx : IsGraphFlow G x)
    (hgood :
      ∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
        if e ∈ f then x e ≠ g else x e ≠ 0) :
    IsAllowedD0OneStepMoveOn G f g x (cdlOneStepMoveOn G f g x) := by
  exact isAllowedD0OneStepMoveOn_of_kirchhoffNeutral_and_vertex_witnesses
    hg hx
    (isKirchhoffNeutralMoveSupport_of_rotationDiskData_internalFace D hincident hf) hgood

theorem isAllowedD0OneStepMoveOn_of_rotationDiskData_internalFace_and_outside_witnesses
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    (D : RotationDiskData V G.edgeSet)
    (hincident : ∀ v : V, D.asZeroBoundary.incident v = incidentEdgeFinset G v)
    {f : Finset G.edgeSet} (hf : f ∈ D.rotation.internalFaces)
    {g : Color} {x : G.edgeSet → Color}
    (hg : g ≠ 0) (hx : IsGraphFlow G x)
    (hgood : ∀ v : V, ∃ e ∈ incidentEdgeFinset G v, e ∉ f ∧ x e ≠ 0) :
    IsAllowedD0OneStepMoveOn G f g x (cdlOneStepMoveOn G f g x) := by
  exact isAllowedD0OneStepMoveOn_of_kirchhoffNeutral_and_outside_witnesses
    hg hx
    (isKirchhoffNeutralMoveSupport_of_rotationDiskData_internalFace D hincident hf) hgood

/-- Manuscript-facing `D₀` local minimum for a finite family of permitted move
supports.  A patch-specific file can instantiate `moveSupports` with its finite
cycle list and then discharge `IsAllowedD0OneStepMoveOn` for each target. -/
structure IsD0LocalMinimumForMoveSupports (G : SimpleGraph V)
    [Fintype V] [Fintype G.edgeSet] (moveSupports : Finset (Finset G.edgeSet))
    (x : G.edgeSet → Color) : Prop where
  source_flow : IsGraphFlow G x
  source_good : ∀ v : V, IsCDLGoodAtVertex G x v
  has_zero : 0 < zeroEdgeCount G x
  d0_le_of_allowed_move :
    ∀ ⦃C : Finset G.edgeSet⦄, C ∈ moveSupports →
    ∀ ⦃g : Color⦄ ⦃y : G.edgeSet → Color⦄,
      IsAllowedD0OneStepMoveOn G C g x y →
        zeroDefectD0 G x ≤ zeroDefectD0 G y

/-- Projection lemma for the defining local-minimum inequality. -/
theorem zeroDefectD0_le_of_isD0LocalMinimumForMoveSupports
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x y : G.edgeSet → Color}
    {C : Finset G.edgeSet} {g : Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hC : C ∈ moveSupports) (hmove : IsAllowedD0OneStepMoveOn G C g x y) :
    zeroDefectD0 G x ≤ zeroDefectD0 G y :=
  hmin.d0_le_of_allowed_move hC hmove

/-- Any permitted one-step move that strictly lowers `D₀` refutes local
minimality for the selected move-support family. -/
theorem not_isD0LocalMinimumForMoveSupports_of_allowed_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x y : G.edgeSet → Color}
    {C : Finset G.edgeSet} {g : Color}
    (hC : C ∈ moveSupports) (hmove : IsAllowedD0OneStepMoveOn G C g x y)
    (hdesc : zeroDefectD0 G y < zeroDefectD0 G x) :
    ¬ IsD0LocalMinimumForMoveSupports G moveSupports x := by
  intro hmin
  exact not_lt_of_ge (hmin.d0_le_of_allowed_move hC hmove) hdesc

theorem not_isD0LocalMinimumForMoveSupports_of_allowed_side_budget_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x y : G.edgeSet → Color}
    {C : Finset G.edgeSet} {g : Color} {dI dC : Nat}
    (hCmem : C ∈ moveSupports) (hmove : IsAllowedD0OneStepMoveOn G C g x y)
    (hZ : zeroEdgeCount G y + 1 ≤ zeroEdgeCount G x)
    (hI : zeroIncidentVertexCount G y ≤ zeroIncidentVertexCount G x + dI)
    (hC : zeroClusteringCount G y ≤ zeroClusteringCount G x + dC)
    (hbudget : 10 * dI + dC < 100) :
    ¬ IsD0LocalMinimumForMoveSupports G moveSupports x := by
  exact not_isD0LocalMinimumForMoveSupports_of_allowed_descent hCmem hmove
    (zeroDefectD0_lt_of_one_zero_removed_and_side_budget hZ hI hC hbudget)

theorem zeroDefectD0_le_of_isD0LocalMinimumForMoveSupports_of_isKempeCycle
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet} {g α β : Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hCmem : C ∈ moveSupports) (hg : g ≠ 0)
    (hC : IsKempeCycle (incidentEdgeFinset G) x C α β)
    (hgood :
      ∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
        if e ∈ C then x e ≠ g else x e ≠ 0) :
    zeroDefectD0 G x ≤ zeroDefectD0 G (cdlOneStepMoveOn G C g x) := by
  exact zeroDefectD0_le_of_isD0LocalMinimumForMoveSupports hmin hCmem
    (isAllowedD0OneStepMoveOn_of_isKempeCycle_and_vertex_witnesses
      hg hmin.source_flow hC hgood)

theorem not_isD0LocalMinimumForMoveSupports_of_isKempeCycle_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet} {g α β : Color}
    (hCmem : C ∈ moveSupports) (hg : g ≠ 0)
    (hC : IsKempeCycle (incidentEdgeFinset G) x C α β)
    (hgood :
      ∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
        if e ∈ C then x e ≠ g else x e ≠ 0)
    (hdesc : zeroDefectD0 G (cdlOneStepMoveOn G C g x) < zeroDefectD0 G x) :
    ¬ IsD0LocalMinimumForMoveSupports G moveSupports x := by
  intro hmin
  exact not_lt_of_ge
    (zeroDefectD0_le_of_isD0LocalMinimumForMoveSupports_of_isKempeCycle
      hmin hCmem hg hC hgood)
    hdesc

theorem not_isD0LocalMinimumForMoveSupports_of_isKempeCycle_side_budget_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet} {g α β : Color} {dI dC : Nat}
    (hCmem : C ∈ moveSupports) (hg : g ≠ 0)
    (hC : IsKempeCycle (incidentEdgeFinset G) x C α β)
    (hgood :
      ∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
        if e ∈ C then x e ≠ g else x e ≠ 0)
    (hZ : zeroEdgeCount G (cdlOneStepMoveOn G C g x) + 1 ≤ zeroEdgeCount G x)
    (hI :
      zeroIncidentVertexCount G (cdlOneStepMoveOn G C g x) ≤
        zeroIncidentVertexCount G x + dI)
    (hCluster :
      zeroClusteringCount G (cdlOneStepMoveOn G C g x) ≤
        zeroClusteringCount G x + dC)
    (hbudget : 10 * dI + dC < 100) :
    ¬ IsD0LocalMinimumForMoveSupports G moveSupports x := by
  intro hmin
  exact (not_isD0LocalMinimumForMoveSupports_of_allowed_side_budget_descent hCmem
    (isAllowedD0OneStepMoveOn_of_isKempeCycle_and_vertex_witnesses
      hg hmin.source_flow hC hgood)
    hZ hI hCluster hbudget) hmin

theorem zeroDefectD0_le_of_isD0LocalMinimumForMoveSupports_of_rotationDiskData_internalFace
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (D : RotationDiskData V G.edgeSet)
    (hincident : ∀ v : V, D.asZeroBoundary.incident v = incidentEdgeFinset G v)
    {f : Finset G.edgeSet} (hf : f ∈ D.rotation.internalFaces)
    (hfmem : f ∈ moveSupports) {g : Color} (hg : g ≠ 0)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hgood :
      ∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
        if e ∈ f then x e ≠ g else x e ≠ 0) :
    zeroDefectD0 G x ≤ zeroDefectD0 G (cdlOneStepMoveOn G f g x) := by
  exact zeroDefectD0_le_of_isD0LocalMinimumForMoveSupports hmin hfmem
    (isAllowedD0OneStepMoveOn_of_rotationDiskData_internalFace_and_vertex_witnesses
      D hincident hf hg hmin.source_flow hgood)

theorem not_isD0LocalMinimumForMoveSupports_of_rotationDiskData_internalFace_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (D : RotationDiskData V G.edgeSet)
    (hincident : ∀ v : V, D.asZeroBoundary.incident v = incidentEdgeFinset G v)
    {f : Finset G.edgeSet} (hf : f ∈ D.rotation.internalFaces)
    (hfmem : f ∈ moveSupports) {g : Color} (hg : g ≠ 0)
    (hgood :
      ∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
        if e ∈ f then x e ≠ g else x e ≠ 0)
    (hdesc : zeroDefectD0 G (cdlOneStepMoveOn G f g x) < zeroDefectD0 G x) :
    ¬ IsD0LocalMinimumForMoveSupports G moveSupports x := by
  intro hmin
  exact not_lt_of_ge
    (zeroDefectD0_le_of_isD0LocalMinimumForMoveSupports_of_rotationDiskData_internalFace
      D hincident hf hfmem hg hmin hgood)
    hdesc

theorem
    not_isD0LocalMinimumForMoveSupports_of_rotationDiskData_internalFace_side_budget_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (D : RotationDiskData V G.edgeSet)
    (hincident : ∀ v : V, D.asZeroBoundary.incident v = incidentEdgeFinset G v)
    {f : Finset G.edgeSet} (hf : f ∈ D.rotation.internalFaces)
    (hfmem : f ∈ moveSupports) {g : Color} {dI dC : Nat} (hg : g ≠ 0)
    (hgood :
      ∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
        if e ∈ f then x e ≠ g else x e ≠ 0)
    (hZ : zeroEdgeCount G (cdlOneStepMoveOn G f g x) + 1 ≤ zeroEdgeCount G x)
    (hI :
      zeroIncidentVertexCount G (cdlOneStepMoveOn G f g x) ≤
        zeroIncidentVertexCount G x + dI)
    (hCluster :
      zeroClusteringCount G (cdlOneStepMoveOn G f g x) ≤
        zeroClusteringCount G x + dC)
    (hbudget : 10 * dI + dC < 100) :
    ¬ IsD0LocalMinimumForMoveSupports G moveSupports x := by
  intro hmin
  exact (not_isD0LocalMinimumForMoveSupports_of_allowed_side_budget_descent hfmem
    (isAllowedD0OneStepMoveOn_of_rotationDiskData_internalFace_and_vertex_witnesses
      D hincident hf hg hmin.source_flow hgood)
    hZ hI hCluster hbudget) hmin

/-- The zero-edge set is a matching in the manuscript's local sense: no vertex
is incident to two or more zero-valued edges. -/
def ZeroEdgesFormMatching (G : SimpleGraph V) [Fintype G.edgeSet]
    (x : G.edgeSet → Color) : Prop :=
  ∀ v : V, zeroIncidentEdgeCount G x v ≤ 1

omit [DecidableEq V] in
theorem zeroEdgeFinset_eq_empty_iff {G : SimpleGraph V} [Fintype G.edgeSet]
    {x : G.edgeSet → Color} :
    zeroEdgeFinset G x = ∅ ↔ ∀ e : G.edgeSet, x e ≠ 0 := by
  simp [zeroEdgeFinset, Finset.filter_eq_empty_iff]

omit [DecidableEq V] in
theorem zeroEdgeCount_eq_zero_iff {G : SimpleGraph V} [Fintype G.edgeSet]
    {x : G.edgeSet → Color} :
    zeroEdgeCount G x = 0 ↔ ∀ e : G.edgeSet, x e ≠ 0 := by
  rw [zeroEdgeCount, Finset.card_eq_zero, zeroEdgeFinset_eq_empty_iff]

omit [DecidableEq V] in
theorem zeroEdgeSym2Finset_card {G : SimpleGraph V} [Fintype G.edgeSet]
    {x : G.edgeSet → Color} :
    (zeroEdgeSym2Finset G x).card = zeroEdgeCount G x := by
  simp [zeroEdgeSym2Finset, zeroEdgeCount]

omit [DecidableEq V] in
theorem zeroEdgeGraph_edgeSet {G : SimpleGraph V} [Fintype G.edgeSet]
    {x : G.edgeSet → Color} :
    (zeroEdgeGraph G x).edgeSet = (zeroEdgeSym2Finset G x : Set (Sym2 V)) := by
  rw [zeroEdgeGraph, SimpleGraph.edgeSet_fromEdgeSet]
  ext e
  simp [zeroEdgeSym2Finset, zeroEdgeFinset]
  intro hG _hx
  exact G.not_isDiag_of_mem_edgeSet hG

noncomputable def zeroEdgeGraphEdgeEquiv (G : SimpleGraph V) [Fintype G.edgeSet]
    (x : G.edgeSet → Color) :
    (zeroEdgeGraph G x).edgeSet ≃ {e : G.edgeSet // x e = 0} where
  toFun e := by
    have hz : ∃ h : e.1 ∈ G.edgeSet, x ⟨e.1, h⟩ = 0 := by
      have hez : e.1 ∈ zeroEdgeSym2Finset G x := by
        have hezdiag : e.1 ∈ (zeroEdgeSym2Finset G x : Set (Sym2 V)) ∧
            ¬ e.1.IsDiag := by
          simpa [zeroEdgeGraph, SimpleGraph.edgeSet_fromEdgeSet] using e.2
        exact hezdiag.1
      rcases Finset.mem_map.mp hez with ⟨eg, heg, h_eq⟩
      have hG : e.1 ∈ G.edgeSet := by
        simp [← h_eq, eg.2]
      have hxeg : x eg = 0 := by simpa [zeroEdgeFinset] using heg
      have heg_eq : (⟨e.1, hG⟩ : G.edgeSet) = eg := by
        apply Subtype.ext
        exact h_eq.symm
      exact ⟨hG, by simpa [heg_eq] using hxeg⟩
    exact ⟨⟨e.1, hz.choose⟩, hz.choose_spec⟩
  invFun e :=
    ⟨e.1.1, by
      rw [zeroEdgeGraph, SimpleGraph.edgeSet_fromEdgeSet]
      constructor
      · rw [zeroEdgeSym2Finset]
        exact Finset.mem_map.mpr ⟨e.1, by simpa [zeroEdgeFinset] using e.2, rfl⟩
      · exact G.not_isDiag_of_mem_edgeSet e.1.2⟩
  left_inv e := by
    ext
    rfl
  right_inv e := by
    ext
    rfl

omit [DecidableEq V] in
@[simp] theorem zeroEdgeGraphEdgeEquiv_coe (G : SimpleGraph V) [Fintype G.edgeSet]
    (x : G.edgeSet → Color) (e : (zeroEdgeGraph G x).edgeSet) :
    ((zeroEdgeGraphEdgeEquiv G x e).1 : Sym2 V) = (e : Sym2 V) := rfl

theorem zeroEdgeSym2Finset_disjoint_diagSet {G : SimpleGraph V}
    [Fintype V] [Fintype G.edgeSet] {x : G.edgeSet → Color} :
    Disjoint (zeroEdgeSym2Finset G x) Sym2.diagSet.toFinset := by
  rw [Finset.disjoint_left]
  intro e he hdiag
  rw [Set.mem_toFinset] at hdiag
  rw [zeroEdgeSym2Finset] at he
  rcases Finset.mem_map.mp he with ⟨eg, _heg, heg_eq⟩
  rw [← heg_eq] at hdiag
  exact G.not_isDiag_of_mem_edgeSet eg.2 hdiag

/-- Handshake form for the zero pattern: the sum of degrees in the zero-edge
graph is twice the manuscript's zero-edge count `Z(x)`. -/
theorem zeroEdgeGraph_sum_degrees_eq_two_mul_zeroEdgeCount
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet] {x : G.edgeSet → Color} :
    ∑ v, (zeroEdgeGraph G x).degree v = 2 * zeroEdgeCount G x := by
  classical
  rw [SimpleGraph.sum_degrees_eq_twice_card_edges]
  simp [SimpleGraph.edgeFinset]
  rw [Finset.sdiff_eq_self_of_disjoint zeroEdgeSym2Finset_disjoint_diagSet]
  rw [zeroEdgeSym2Finset_card]

theorem zeroEdgeGraph_incidentEdgeFinset_card
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {x : G.edgeSet → Color} (v : V) :
    (incidentEdgeFinset (zeroEdgeGraph G x) v).card = zeroIncidentEdgeCount G x v := by
  classical
  let E := zeroEdgeGraphEdgeEquiv G x
  rw [zeroIncidentEdgeCount]
  refine Finset.card_bij (fun e _he => (E e).1) ?_ ?_ ?_
  · intro e he
    have hv : v ∈ (e : Sym2 V) := by simpa [incidentEdgeFinset] using he
    have hEcoe : ((E e).1 : Sym2 V) = (e : Sym2 V) := by
      change ((zeroEdgeGraphEdgeEquiv G x e).1 : Sym2 V) = (e : Sym2 V)
      simp
    have hinc : (E e).1 ∈ incidentEdgeFinset G v := by
      simpa [incidentEdgeFinset, hEcoe] using hv
    exact by simp [zeroIncidentEdgeFinset, hinc, (E e).2]
  · intro e1 _he1 e2 _he2 h
    apply Subtype.ext
    have hsymE := congrArg (fun e : G.edgeSet => (e : Sym2 V)) h
    have h1 : ((E e1).1 : Sym2 V) = (e1 : Sym2 V) := by
      change ((zeroEdgeGraphEdgeEquiv G x e1).1 : Sym2 V) = (e1 : Sym2 V)
      simp
    have h2 : ((E e2).1 : Sym2 V) = (e2 : Sym2 V) := by
      change ((zeroEdgeGraphEdgeEquiv G x e2).1 : Sym2 V) = (e2 : Sym2 V)
      simp
    exact h1.symm.trans (hsymE.trans h2)
  · intro e he
    have he_pair : e ∈ incidentEdgeFinset G v ∧ x e = 0 := by
      simpa [zeroIncidentEdgeFinset] using he
    let ez : (zeroEdgeGraph G x).edgeSet :=
      ⟨e.1, by
        rw [zeroEdgeGraph, SimpleGraph.edgeSet_fromEdgeSet]
        constructor
        · rw [zeroEdgeSym2Finset]
          exact Finset.mem_map.mpr ⟨e, by simpa [zeroEdgeFinset] using he_pair.2, rfl⟩
        · exact G.not_isDiag_of_mem_edgeSet e.2⟩
    have hez : ez ∈ incidentEdgeFinset (zeroEdgeGraph G x) v := by
      have hv : v ∈ (e : Sym2 V) := by simpa [incidentEdgeFinset] using he_pair.1
      simpa [incidentEdgeFinset, ez] using hv
    refine ⟨ez, hez, ?_⟩
    apply Subtype.ext
    change ((zeroEdgeGraphEdgeEquiv G x ez).1 : Sym2 V) = (e : Sym2 V)
    simp [ez]

theorem zeroIncidentEdgeFinset_eq_empty_iff {G : SimpleGraph V} [Fintype G.edgeSet]
    {x : G.edgeSet → Color} {v : V} :
    zeroIncidentEdgeFinset G x v = ∅ ↔
      ∀ e ∈ incidentEdgeFinset G v, x e ≠ 0 := by
  simp [zeroIncidentEdgeFinset, Finset.filter_eq_empty_iff]

theorem zeroIncidentEdgeCount_eq_zero_iff {G : SimpleGraph V} [Fintype G.edgeSet]
    {x : G.edgeSet → Color} {v : V} :
    zeroIncidentEdgeCount G x v = 0 ↔
      ∀ e ∈ incidentEdgeFinset G v, x e ≠ 0 := by
  rw [zeroIncidentEdgeCount, Finset.card_eq_zero, zeroIncidentEdgeFinset_eq_empty_iff]

theorem zeroIncidentVertexCount_eq_zero_iff {G : SimpleGraph V}
    [Fintype V] [Fintype G.edgeSet] {x : G.edgeSet → Color} :
    zeroIncidentVertexCount G x = 0 ↔
      ∀ v : V, zeroIncidentEdgeCount G x v = 0 := by
  simp [zeroIncidentVertexCount, zeroIncidentVertexFinset, Finset.card_eq_zero]

/-- If the global zero-edge defect is zero, then no vertex is incident to a
zero edge. -/
theorem zeroIncidentVertexCount_eq_zero_of_zeroEdgeCount_eq_zero {G : SimpleGraph V}
    [Fintype V] [Fintype G.edgeSet] {x : G.edgeSet → Color}
    (hZ : zeroEdgeCount G x = 0) :
    zeroIncidentVertexCount G x = 0 := by
  rw [zeroIncidentVertexCount_eq_zero_iff]
  intro v
  rw [zeroIncidentEdgeCount_eq_zero_iff]
  intro e _he
  exact (zeroEdgeCount_eq_zero_iff.mp hZ) e

/-- If no vertex is touched by a zero edge, then the global zero-edge defect is
zero.  The endpoint witness is supplied by `Sym2.out`. -/
theorem zeroEdgeCount_eq_zero_of_zeroIncidentVertexCount_eq_zero {G : SimpleGraph V}
    [Fintype V] [Fintype G.edgeSet] {x : G.edgeSet → Color}
    (hI : zeroIncidentVertexCount G x = 0) :
    zeroEdgeCount G x = 0 := by
  rw [zeroEdgeCount_eq_zero_iff]
  intro e
  let v : V := (e : Sym2 V).out.1
  have he_inc : e ∈ incidentEdgeFinset G v := by
    have hv : v ∈ (e : Sym2 V) := Sym2.out_fst_mem (e : Sym2 V)
    simp [incidentEdgeFinset, hv]
  have hk : zeroIncidentEdgeCount G x v = 0 :=
    (zeroIncidentVertexCount_eq_zero_iff.mp hI) v
  exact (zeroIncidentEdgeCount_eq_zero_iff.mp hk) e he_inc

/-- `I(x)=0` is equivalent to `Z(x)=0`: no vertex is touched by a zero edge
exactly when there are no zero edges. -/
theorem zeroIncidentVertexCount_eq_zero_iff_zeroEdgeCount_eq_zero {G : SimpleGraph V}
    [Fintype V] [Fintype G.edgeSet] {x : G.edgeSet → Color} :
    zeroIncidentVertexCount G x = 0 ↔ zeroEdgeCount G x = 0 := by
  constructor
  · exact zeroEdgeCount_eq_zero_of_zeroIncidentVertexCount_eq_zero
  · exact zeroIncidentVertexCount_eq_zero_of_zeroEdgeCount_eq_zero

/-- If the global zero-edge defect is zero, then the zero-clustering defect is
zero. -/
theorem zeroClusteringCount_eq_zero_of_zeroEdgeCount_eq_zero {G : SimpleGraph V}
    [Fintype V] [Fintype G.edgeSet] {x : G.edgeSet → Color}
    (hZ : zeroEdgeCount G x = 0) :
    zeroClusteringCount G x = 0 := by
  unfold zeroClusteringCount
  apply Finset.sum_eq_zero
  intro v _hv
  have hk : zeroIncidentEdgeCount G x v = 0 := by
    rw [zeroIncidentEdgeCount_eq_zero_iff]
    intro e _he
    exact (zeroEdgeCount_eq_zero_iff.mp hZ) e
  simp [hk]

/-- The clustering defect is zero exactly when the zero-edge set forms a
matching. -/
theorem zeroClusteringCount_eq_zero_iff_zeroEdgesFormMatching
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet] {x : G.edgeSet → Color} :
    zeroClusteringCount G x = 0 ↔ ZeroEdgesFormMatching G x := by
  simp [ZeroEdgesFormMatching, zeroClusteringCount, Nat.sub_eq_zero_iff_le]

/-- If no vertex is touched by a zero edge, then the zero-clustering defect is
zero. -/
theorem zeroClusteringCount_eq_zero_of_zeroIncidentVertexCount_eq_zero
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet] {x : G.edgeSet → Color}
    (hI : zeroIncidentVertexCount G x = 0) :
    zeroClusteringCount G x = 0 :=
  zeroClusteringCount_eq_zero_of_zeroEdgeCount_eq_zero
    (zeroEdgeCount_eq_zero_of_zeroIncidentVertexCount_eq_zero hI)

/-- A nowhere-zero flow is exactly a graph flow whose zero-edge set is empty. -/
theorem isNowhereZeroFlow_iff_isGraphFlow_and_zeroEdgeFinset_eq_empty
    {G : SimpleGraph V} [Fintype G.edgeSet] {x : G.edgeSet → Color} :
    IsNowhereZeroFlow G x ↔ IsGraphFlow G x ∧ zeroEdgeFinset G x = ∅ := by
  rw [zeroEdgeFinset_eq_empty_iff]
  rfl

/-- A nowhere-zero flow is exactly a graph flow with zero zero-edge defect
count. -/
theorem isNowhereZeroFlow_iff_isGraphFlow_and_zeroEdgeCount_eq_zero
    {G : SimpleGraph V} [Fintype G.edgeSet] {x : G.edgeSet → Color} :
    IsNowhereZeroFlow G x ↔ IsGraphFlow G x ∧ zeroEdgeCount G x = 0 := by
  rw [zeroEdgeCount_eq_zero_iff]
  rfl

/-- Manuscript-facing name for cubic graphs: every vertex has Mathlib degree
`3`. -/
def IsCubic (G : SimpleGraph V) [G.LocallyFinite] : Prop :=
  G.IsRegularOfDegree 3

/-- Existence of a Tait edge coloring of `G`. -/
def HasTaitEdgeColoring (G : SimpleGraph V) [Fintype G.edgeSet] : Prop :=
  ∃ C : G.EdgeColoring Color, IsTaitEdgeColoring G C

/-- Existence of a nowhere-zero `F₂²` graph flow on `G`. -/
def HasNowhereZeroFlow (G : SimpleGraph V) [Fintype G.edgeSet] : Prop :=
  ∃ x : G.edgeSet → Color, IsNowhereZeroFlow G x

/-- Existence of a flow that is both CDL-good and nowhere-zero.  The
nowhere-zero conjunct is deliberate: canonical CDL-goodness alone only rules
out the all-zero local triple. -/
def HasCDLGoodNowhereZeroFlow (G : SimpleGraph V) [Fintype G.edgeSet] : Prop :=
  ∃ x : G.edgeSet → Color, IsCDLGoodFlow G x ∧ IsNowhereZeroFlow G x

/-- A named cubic incidence package: the incident edges at `v` are exactly
`e1`, `e2`, and `e3`, with no duplicates. -/
def IsIncidentEdgeTriple (G : SimpleGraph V) [Fintype G.edgeSet] (v : V)
    (e1 e2 e3 : G.edgeSet) : Prop :=
  incidentEdgeFinset G v = {e1, e2, e3} ∧ e1 ≠ e2 ∧ e1 ≠ e3 ∧ e2 ≠ e3

/-- A lightweight cubic-incidence hypothesis: every vertex has its incident
edge-set explicitly enumerated by three distinct edges. -/
def HasCubicIncidentEdgeTriples (G : SimpleGraph V) [Fintype G.edgeSet] : Prop :=
  ∀ v : V, ∃ e1 e2 e3 : G.edgeSet, IsIncidentEdgeTriple G v e1 e2 e3

/-- Local Kirchhoff law for the three incident edge-values at a cubic vertex. -/
def IsLocalKirchhoffTriple (a b c : Color) : Prop :=
  a + b + c = 0

/-- The canonical local CDL-bad pattern: all three incident values are zero. -/
def IsLocalCDLBadTriple (a b c : Color) : Prop :=
  a = 0 ∧ b = 0 ∧ c = 0

/-- The canonical local CDL-good condition: the incident triple is not all-zero. -/
def IsLocalCDLGoodTriple (a b c : Color) : Prop :=
  a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0

/-- The local nowhere-zero condition needed by a Tait-flow interpretation. -/
def IsLocalNowhereZeroTriple (a b c : Color) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0

/-- Local Tait condition for a cubic vertex: the three incident colors are
nonzero and pairwise distinct. -/
def IsLocalTaitTriple (a b c : Color) : Prop :=
  IsLocalNowhereZeroTriple a b c ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c

theorem isGraphFlow_iff {G : SimpleGraph V} [Fintype G.edgeSet]
    {x : G.edgeSet → Color} :
    IsGraphFlow G x ↔ ∀ v : V, vertexKirchhoffSum G x v = 0 :=
  Iff.rfl

theorem incidentEdgeFinset_nonempty_of_hasCubicIncidentEdgeTriples {G : SimpleGraph V}
    [Fintype G.edgeSet] (hG : HasCubicIncidentEdgeTriples G) (v : V) :
    (incidentEdgeFinset G v).Nonempty := by
  rcases hG v with ⟨e1, _e2, _e3, hincident⟩
  refine ⟨e1, ?_⟩
  rw [hincident.1]
  simp

theorem hasCubicIncidentEdgeTriples_of_incidentEdgeFinset_card_eq_three
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3) :
    HasCubicIncidentEdgeTriples G := by
  intro v
  rcases Finset.card_eq_three.mp (hcard v) with ⟨e1, e2, e3, h12, h13, h23, hset⟩
  exact ⟨e1, e2, e3, hset, h12, h13, h23⟩

theorem incidentEdgeFinset_card_eq_three_of_hasCubicIncidentEdgeTriples
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (hG : HasCubicIncidentEdgeTriples G) (v : V) :
    (incidentEdgeFinset G v).card = 3 := by
  rcases hG v with ⟨e1, e2, e3, hset, h12, h13, h23⟩
  rw [hset]
  simp [h12, h13, h23]

theorem hasCubicIncidentEdgeTriples_iff_incidentEdgeFinset_card_eq_three
    {G : SimpleGraph V} [Fintype G.edgeSet] :
    HasCubicIncidentEdgeTriples G ↔ ∀ v : V, (incidentEdgeFinset G v).card = 3 := by
  constructor
  · exact incidentEdgeFinset_card_eq_three_of_hasCubicIncidentEdgeTriples
  · exact hasCubicIncidentEdgeTriples_of_incidentEdgeFinset_card_eq_three

/-- The local incident-edge finset used by the `F₂²` Kirchhoff layer has the
same cardinality as Mathlib's graph degree. -/
theorem incidentEdgeFinset_card_eq_degree {G : SimpleGraph V} [Fintype G.edgeSet]
    (v : V) [Fintype (G.neighborSet v)] :
    (incidentEdgeFinset G v).card = G.degree v := by
  have hmap :
      (incidentEdgeFinset G v).map
          (Function.Embedding.subtype (fun e : Sym2 V => e ∈ G.edgeSet)) =
        G.incidenceFinset v := by
    rw [SimpleGraph.incidenceFinset_eq_filter]
    ext e
    simp [incidentEdgeFinset, and_comm]
  calc
    (incidentEdgeFinset G v).card =
        ((incidentEdgeFinset G v).map
          (Function.Embedding.subtype (fun e : Sym2 V => e ∈ G.edgeSet))).card := by
      simp
    _ = (G.incidenceFinset v).card := by rw [hmap]
    _ = G.degree v := by simp

/-- Summing the manuscript's local zero-incidence counts `k_v(x)` counts every
zero edge twice. -/
theorem sum_zeroIncidentEdgeCount_eq_two_mul_zeroEdgeCount
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet] {x : G.edgeSet → Color} :
    ∑ v, zeroIncidentEdgeCount G x v = 2 * zeroEdgeCount G x := by
  rw [← zeroEdgeGraph_sum_degrees_eq_two_mul_zeroEdgeCount]
  apply Finset.sum_congr rfl
  intro v _hv
  rw [← zeroEdgeGraph_incidentEdgeFinset_card]
  rw [incidentEdgeFinset_card_eq_degree]

/-- If the zero edges form a matching, the number of vertices touched by zero
edges is the sum of the local zero-incidence counts. -/
theorem zeroIncidentVertexCount_eq_sum_zeroIncidentEdgeCount_of_zeroEdgesFormMatching
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet] {x : G.edgeSet → Color}
    (hmatch : ZeroEdgesFormMatching G x) :
    zeroIncidentVertexCount G x = ∑ v, zeroIncidentEdgeCount G x v := by
  rw [zeroIncidentVertexCount, zeroIncidentVertexFinset]
  symm
  calc
    ∑ v, zeroIncidentEdgeCount G x v =
        ∑ v, if 0 < zeroIncidentEdgeCount G x v then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro v _hv
      by_cases hvpos : 0 < zeroIncidentEdgeCount G x v
      · have hk : zeroIncidentEdgeCount G x v = 1 :=
          Nat.le_antisymm (hmatch v) (Nat.succ_le_of_lt hvpos)
        simp [hk]
      · have hk : zeroIncidentEdgeCount G x v = 0 := Nat.eq_zero_of_not_pos hvpos
        simp [hk]
    _ = (Finset.univ.filter fun v => 0 < zeroIncidentEdgeCount G x v).card := by
      rw [Finset.card_filter]

/-- Manuscript count form for matching zero patterns: `I(x)=2 Z(x)`. -/
theorem zeroIncidentVertexCount_eq_two_mul_zeroEdgeCount_of_zeroEdgesFormMatching
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet] {x : G.edgeSet → Color}
    (hmatch : ZeroEdgesFormMatching G x) :
    zeroIncidentVertexCount G x = 2 * zeroEdgeCount G x := by
  rw [zeroIncidentVertexCount_eq_sum_zeroIncidentEdgeCount_of_zeroEdgesFormMatching hmatch,
    sum_zeroIncidentEdgeCount_eq_two_mul_zeroEdgeCount]

/-- Since `C(x)=0` is equivalent to the zero-edge set being a matching, zero
clustering also yields the manuscript count `I(x)=2 Z(x)`. -/
theorem zeroIncidentVertexCount_eq_two_mul_zeroEdgeCount_of_zeroClusteringCount_eq_zero
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet] {x : G.edgeSet → Color}
    (hC : zeroClusteringCount G x = 0) :
    zeroIncidentVertexCount G x = 2 * zeroEdgeCount G x :=
  zeroIncidentVertexCount_eq_two_mul_zeroEdgeCount_of_zeroEdgesFormMatching
    (zeroClusteringCount_eq_zero_iff_zeroEdgesFormMatching.mp hC)

/-- Under a matching zero pattern, the cheap defect collapses to `120 Z(x)`. -/
theorem zeroDefectD0_eq_120_mul_zeroEdgeCount_of_zeroEdgesFormMatching
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet] {x : G.edgeSet → Color}
    (hmatch : ZeroEdgesFormMatching G x) :
    zeroDefectD0 G x = 120 * zeroEdgeCount G x := by
  unfold zeroDefectD0
  rw [zeroIncidentVertexCount_eq_two_mul_zeroEdgeCount_of_zeroEdgesFormMatching hmatch,
    (zeroClusteringCount_eq_zero_iff_zeroEdgesFormMatching.mpr hmatch)]
  omega

/-- Since `C(x)=0` is equivalent to matching zeros, zero clustering also
collapses the cheap defect to `120 Z(x)`. -/
theorem zeroDefectD0_eq_120_mul_zeroEdgeCount_of_zeroClusteringCount_eq_zero
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet] {x : G.edgeSet → Color}
    (hC : zeroClusteringCount G x = 0) :
    zeroDefectD0 G x = 120 * zeroEdgeCount G x :=
  zeroDefectD0_eq_120_mul_zeroEdgeCount_of_zeroEdgesFormMatching
    (zeroClusteringCount_eq_zero_iff_zeroEdgesFormMatching.mp hC)

/-- A graph with Mathlib degree `3` at every vertex has the explicit cubic
incident triples needed by the local Tait-flow bridge. -/
theorem hasCubicIncidentEdgeTriples_of_degree_eq_three
    {G : SimpleGraph V} [Fintype G.edgeSet] [G.LocallyFinite]
    (hdegree : ∀ v : V, G.degree v = 3) :
    HasCubicIncidentEdgeTriples G := by
  apply hasCubicIncidentEdgeTriples_of_incidentEdgeFinset_card_eq_three
  intro v
  rw [incidentEdgeFinset_card_eq_degree, hdegree v]

/-- Regular cubic graphs in Mathlib's sense have the explicit cubic incident
triples needed by the local Tait-flow bridge. -/
theorem hasCubicIncidentEdgeTriples_of_isRegularOfDegree_three
    {G : SimpleGraph V} [Fintype G.edgeSet] [G.LocallyFinite]
    (hregular : G.IsRegularOfDegree 3) :
    HasCubicIncidentEdgeTriples G :=
  hasCubicIncidentEdgeTriples_of_degree_eq_three hregular.degree_eq

/-- Cubic graphs in the manuscript-facing sense have explicit cubic incident
triples. -/
theorem hasCubicIncidentEdgeTriples_of_isCubic
    {G : SimpleGraph V} [Fintype G.edgeSet] [G.LocallyFinite]
    (hG : IsCubic G) :
    HasCubicIncidentEdgeTriples G :=
  hasCubicIncidentEdgeTriples_of_isRegularOfDegree_three hG

theorem isLocalCDLGoodTriple_iff_not_bad {a b c : Color} :
    IsLocalCDLGoodTriple a b c ↔ ¬ IsLocalCDLBadTriple a b c := by
  constructor
  · intro hgood hbad
    rcases hbad with ⟨ha, hb, hc⟩
    rcases hgood with ha_ne | hb_ne | hc_ne
    · exact ha_ne ha
    · exact hb_ne hb
    · exact hc_ne hc
  · intro hnot
    by_cases ha : a = 0
    · by_cases hb : b = 0
      · by_cases hc : c = 0
        · exact False.elim (hnot ⟨ha, hb, hc⟩)
        · exact Or.inr (Or.inr hc)
      · exact Or.inr (Or.inl hb)
    · exact Or.inl ha

theorem localKirchhoff_zero_same (c : Color) :
    IsLocalKirchhoffTriple 0 c c := by
  simp [IsLocalKirchhoffTriple]

theorem localCDLGood_zero_same_of_ne_zero {c : Color} (hc : c ≠ 0) :
    IsLocalCDLGoodTriple 0 c c := by
  exact Or.inr (Or.inl hc)

theorem not_localNowhereZero_zero_left (b c : Color) :
    ¬ IsLocalNowhereZeroTriple 0 b c := by
  intro h
  exact h.1 rfl

theorem isLocalNowhereZeroTriple_of_tait {a b c : Color}
    (h : IsLocalTaitTriple a b c) :
    IsLocalNowhereZeroTriple a b c :=
  h.1

/-- Over `F₂²`, a local Tait triple at a cubic vertex automatically satisfies
Kirchhoff's law.  This is the local algebra behind the manuscript's Tait-flow
translation. -/
theorem isLocalKirchhoffTriple_of_tait {a b c : Color}
    (h : IsLocalTaitTriple a b c) :
    IsLocalKirchhoffTriple a b c := by
  rcases h with ⟨hnz, hab, hac, hbc⟩
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero a hnz.1 with rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero b hnz.2.1 with rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero c hnz.2.2 with rfl | rfl | rfl <;>
    simp [IsLocalKirchhoffTriple, red, blue, purple] at *

/-- Over `F2^2`, the local Kirchhoff law plus nowhere-zero values forces the
three colors at a cubic vertex to be pairwise distinct. -/
theorem isLocalTaitTriple_of_kirchhoff_nowhereZero {a b c : Color}
    (hK : IsLocalKirchhoffTriple a b c)
    (hnz : IsLocalNowhereZeroTriple a b c) :
    IsLocalTaitTriple a b c := by
  refine ⟨hnz, ?_, ?_, ?_⟩
  · intro hab
    have hsum : a + b + c = 0 := by
      simpa [IsLocalKirchhoffTriple] using hK
    have hc0 : c = 0 := by
      have hsum' : a + a + c = 0 := by
        simpa [hab] using hsum
      simpa [color_add_self] using hsum'
    exact hnz.2.2 hc0
  · intro hac
    have hsum : a + b + c = 0 := by
      simpa [IsLocalKirchhoffTriple] using hK
    have hsum' : c + b + c = 0 := by
      simpa [hac] using hsum
    have hb0 : b = 0 := by
      calc
        b = 0 + b := by simp
        _ = (c + c) + b := by rw [color_add_self]
        _ = c + b + c := by abel
        _ = 0 := hsum'
    exact hnz.2.1 hb0
  · intro hbc
    have hsum : a + b + c = 0 := by
      simpa [IsLocalKirchhoffTriple] using hK
    have hsum' : a + c + c = 0 := by
      simpa [hbc] using hsum
    have ha0 : a = 0 := by
      calc
        a = a + 0 := by simp
        _ = a + (c + c) := by rw [color_add_self]
        _ = a + c + c := by abel
        _ = 0 := hsum'
    exact hnz.1 ha0

/-- Graph-level local form of the Tait-flow direction: at a cubic vertex whose
incident edge-set is explicitly enumerated, a nowhere-zero graph flow produces
a local Tait triple on those three edges. -/
theorem isLocalTaitTriple_of_nowhereZeroFlow_at_incidentTriple {G : SimpleGraph V}
    [Fintype G.edgeSet] {x : G.edgeSet → Color} {v : V} {e1 e2 e3 : G.edgeSet}
    (hincident : IsIncidentEdgeTriple G v e1 e2 e3)
    (hx : IsNowhereZeroFlow G x) :
    IsLocalTaitTriple (x e1) (x e2) (x e3) := by
  apply isLocalTaitTriple_of_kirchhoff_nowhereZero
  · have hv := hx.1 v
    unfold vertexKirchhoffSum at hv
    rw [hincident.1] at hv
    simpa [IsLocalKirchhoffTriple, hincident.2.1, hincident.2.2.1, hincident.2.2.2,
      add_assoc] using hv
  · exact ⟨hx.2 e1, hx.2 e2, hx.2 e3⟩

/-- Graph-level local form of the Tait-coloring direction: at a cubic vertex
whose incident edge-set is explicitly enumerated, an edge coloring using only
nonzero `F₂²` colors produces three nonzero, pairwise distinct local values. -/
theorem isLocalTaitTriple_of_taitEdgeColoring_at_incidentTriple {G : SimpleGraph V}
    [Fintype G.edgeSet] {C : G.EdgeColoring Color} {v : V} {e1 e2 e3 : G.edgeSet}
    (hincident : IsIncidentEdgeTriple G v e1 e2 e3)
    (hC : IsTaitEdgeColoring G C) :
    IsLocalTaitTriple (C e1) (C e2) (C e3) := by
  have he1_mem : e1 ∈ incidentEdgeFinset G v := by
    rw [hincident.1]
    simp
  have he2_mem : e2 ∈ incidentEdgeFinset G v := by
    rw [hincident.1]
    simp
  have he3_mem : e3 ∈ incidentEdgeFinset G v := by
    rw [hincident.1]
    simp
  have he1v : v ∈ (e1 : Sym2 V) := by
    simpa [incidentEdgeFinset] using he1_mem
  have he2v : v ∈ (e2 : Sym2 V) := by
    simpa [incidentEdgeFinset] using he2_mem
  have he3v : v ∈ (e3 : Sym2 V) := by
    simpa [incidentEdgeFinset] using he3_mem
  have h12 : C e1 ≠ C e2 := by
    exact C.valid ((SimpleGraph.lineGraph_adj_iff_exists).2
      ⟨hincident.2.1, ⟨v, he1v, he2v⟩⟩)
  have h13 : C e1 ≠ C e3 := by
    exact C.valid ((SimpleGraph.lineGraph_adj_iff_exists).2
      ⟨hincident.2.2.1, ⟨v, he1v, he3v⟩⟩)
  have h23 : C e2 ≠ C e3 := by
    exact C.valid ((SimpleGraph.lineGraph_adj_iff_exists).2
      ⟨hincident.2.2.2, ⟨v, he2v, he3v⟩⟩)
  exact ⟨⟨hC e1, hC e2, hC e3⟩, h12, h13, h23⟩

/-- A Tait edge coloring induces the local Kirchhoff equation at an explicitly
enumerated cubic vertex. -/
theorem isLocalKirchhoffTriple_of_taitEdgeColoring_at_incidentTriple {G : SimpleGraph V}
    [Fintype G.edgeSet] {C : G.EdgeColoring Color} {v : V} {e1 e2 e3 : G.edgeSet}
    (hincident : IsIncidentEdgeTriple G v e1 e2 e3)
    (hC : IsTaitEdgeColoring G C) :
    IsLocalKirchhoffTriple (C e1) (C e2) (C e3) := by
  exact isLocalKirchhoffTriple_of_tait
    (isLocalTaitTriple_of_taitEdgeColoring_at_incidentTriple hincident hC)

/-- Vertex-sum form of the local Tait-flow translation: if the incident
edge-set at `v` is exactly `e1,e2,e3`, then a Tait edge coloring has zero
Kirchhoff sum at `v`. -/
theorem vertexKirchhoffSum_eq_zero_of_taitEdgeColoring_at_incidentTriple
    {G : SimpleGraph V} [Fintype G.edgeSet] {C : G.EdgeColoring Color}
    {v : V} {e1 e2 e3 : G.edgeSet}
    (hincident : IsIncidentEdgeTriple G v e1 e2 e3)
    (hC : IsTaitEdgeColoring G C) :
    vertexKirchhoffSum G C v = 0 := by
  unfold vertexKirchhoffSum
  rw [hincident.1]
  simpa [IsLocalKirchhoffTriple, hincident.2.1, hincident.2.2.1, hincident.2.2.2,
    add_assoc] using
    (isLocalKirchhoffTriple_of_taitEdgeColoring_at_incidentTriple hincident hC)

/-- Graph-level Tait-flow direction, phrased with the explicit cubic-incidence
package used by the local API: a Tait edge coloring satisfies Kirchhoff's law
at every vertex. -/
theorem isGraphFlow_of_taitEdgeColoring_of_hasCubicIncidentEdgeTriples
    {G : SimpleGraph V} [Fintype G.edgeSet] {C : G.EdgeColoring Color}
    (hG : HasCubicIncidentEdgeTriples G) (hC : IsTaitEdgeColoring G C) :
    IsGraphFlow G C := by
  intro v
  rcases hG v with ⟨e1, e2, e3, hincident⟩
  exact vertexKirchhoffSum_eq_zero_of_taitEdgeColoring_at_incidentTriple hincident hC

/-- A Tait edge coloring is a nowhere-zero `F₂²` graph flow once every vertex
has the expected cubic incident triple. -/
theorem isNowhereZeroFlow_of_taitEdgeColoring_of_hasCubicIncidentEdgeTriples
    {G : SimpleGraph V} [Fintype G.edgeSet] {C : G.EdgeColoring Color}
    (hG : HasCubicIncidentEdgeTriples G) (hC : IsTaitEdgeColoring G C) :
    IsNowhereZeroFlow G C := by
  exact ⟨isGraphFlow_of_taitEdgeColoring_of_hasCubicIncidentEdgeTriples hG hC, hC⟩

/-- Converse local-to-global edge-coloring step: in a nowhere-zero `F₂²` flow
on a graph with explicit cubic incident triples, adjacent line-graph vertices
(i.e. incident graph edges) have distinct values. -/
theorem edge_values_ne_of_nowhereZeroFlow_of_hasCubicIncidentEdgeTriples
    {G : SimpleGraph V} [Fintype G.edgeSet] {x : G.edgeSet → Color}
    (hG : HasCubicIncidentEdgeTriples G) (hx : IsNowhereZeroFlow G x)
    {e f : G.edgeSet} (hadj : G.lineGraph.Adj e f) :
    x e ≠ x f := by
  rcases (SimpleGraph.lineGraph_adj_iff_exists).1 hadj with ⟨hef, v, hev, hfv⟩
  rcases hG v with ⟨e1, e2, e3, hincident⟩
  have he_mem : e ∈ incidentEdgeFinset G v := by
    simpa [incidentEdgeFinset] using hev
  have hf_mem : f ∈ incidentEdgeFinset G v := by
    simpa [incidentEdgeFinset] using hfv
  rw [hincident.1] at he_mem hf_mem
  have htrip := isLocalTaitTriple_of_nowhereZeroFlow_at_incidentTriple hincident hx
  rcases htrip with ⟨_hnz, h12, h13, h23⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at he_mem hf_mem
  rcases he_mem with rfl | rfl | rfl
  · rcases hf_mem with rfl | rfl | rfl
    · exact (hef rfl).elim
    · exact h12
    · exact h13
  · rcases hf_mem with rfl | rfl | rfl
    · exact fun h => h12 h.symm
    · exact (hef rfl).elim
    · exact h23
  · rcases hf_mem with rfl | rfl | rfl
    · exact fun h => h13 h.symm
    · exact fun h => h23 h.symm
    · exact (hef rfl).elim

/-- Package a nowhere-zero `F₂²` flow as a proper edge coloring. -/
def edgeColoringOfNowhereZeroFlow
    {G : SimpleGraph V} [Fintype G.edgeSet] (x : G.edgeSet → Color)
    (hG : HasCubicIncidentEdgeTriples G) (hx : IsNowhereZeroFlow G x) :
    G.EdgeColoring Color :=
  SimpleGraph.Coloring.mk x
    (fun hadj => edge_values_ne_of_nowhereZeroFlow_of_hasCubicIncidentEdgeTriples hG hx hadj)

/-- The edge coloring obtained from a nowhere-zero `F₂²` flow is Tait: all
edge-values are nonzero. -/
theorem isTaitEdgeColoring_edgeColoringOfNowhereZeroFlow
    {G : SimpleGraph V} [Fintype G.edgeSet] {x : G.edgeSet → Color}
    (hG : HasCubicIncidentEdgeTriples G) (hx : IsNowhereZeroFlow G x) :
    IsTaitEdgeColoring G (edgeColoringOfNowhereZeroFlow x hG hx) := by
  intro e
  exact hx.2 e

/-- Nowhere-zero `F₂²` flows produce Tait edge colorings under the explicit
cubic-incidence hypothesis. -/
theorem exists_taitEdgeColoring_of_nowhereZeroFlow_of_hasCubicIncidentEdgeTriples
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (hG : HasCubicIncidentEdgeTriples G) (x : G.edgeSet → Color)
    (hx : IsNowhereZeroFlow G x) :
    ∃ C : G.EdgeColoring Color, IsTaitEdgeColoring G C := by
  exact ⟨edgeColoringOfNowhereZeroFlow x hG hx,
    isTaitEdgeColoring_edgeColoringOfNowhereZeroFlow hG hx⟩

/-- Existence-level Tait/flow reformulation for the explicit cubic-incidence
API: Tait edge colorings are equivalent to nowhere-zero `F₂²` graph flows. -/
theorem exists_taitEdgeColoring_iff_exists_nowhereZeroFlow_of_hasCubicIncidentEdgeTriples
    {G : SimpleGraph V} [Fintype G.edgeSet] (hG : HasCubicIncidentEdgeTriples G) :
    (∃ C : G.EdgeColoring Color, IsTaitEdgeColoring G C) ↔
      ∃ x : G.edgeSet → Color, IsNowhereZeroFlow G x := by
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, isNowhereZeroFlow_of_taitEdgeColoring_of_hasCubicIncidentEdgeTriples hG hC⟩
  · rintro ⟨x, hx⟩
    exact exists_taitEdgeColoring_of_nowhereZeroFlow_of_hasCubicIncidentEdgeTriples hG x hx

/-- Tait/flow reformulation using the finite incidence-cardinality form of
cubicity. -/
theorem exists_taitEdgeColoring_iff_exists_nowhereZeroFlow_of_incidentEdgeFinset_card_eq_three
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3) :
    (∃ C : G.EdgeColoring Color, IsTaitEdgeColoring G C) ↔
      ∃ x : G.edgeSet → Color, IsNowhereZeroFlow G x := by
  exact exists_taitEdgeColoring_iff_exists_nowhereZeroFlow_of_hasCubicIncidentEdgeTriples
    (hasCubicIncidentEdgeTriples_of_incidentEdgeFinset_card_eq_three hcard)

/-- Tait/flow reformulation for graphs whose Mathlib degree is `3` at every
vertex. -/
theorem exists_taitEdgeColoring_iff_exists_nowhereZeroFlow_of_degree_eq_three
    {G : SimpleGraph V} [Fintype G.edgeSet] [G.LocallyFinite]
    (hdegree : ∀ v : V, G.degree v = 3) :
    (∃ C : G.EdgeColoring Color, IsTaitEdgeColoring G C) ↔
      ∃ x : G.edgeSet → Color, IsNowhereZeroFlow G x := by
  exact exists_taitEdgeColoring_iff_exists_nowhereZeroFlow_of_hasCubicIncidentEdgeTriples
    (hasCubicIncidentEdgeTriples_of_degree_eq_three hdegree)

/-- Tait/flow reformulation for regular cubic graphs in Mathlib's sense. -/
theorem exists_taitEdgeColoring_iff_exists_nowhereZeroFlow_of_isRegularOfDegree_three
    {G : SimpleGraph V} [Fintype G.edgeSet] [G.LocallyFinite]
    (hregular : G.IsRegularOfDegree 3) :
    (∃ C : G.EdgeColoring Color, IsTaitEdgeColoring G C) ↔
      ∃ x : G.edgeSet → Color, IsNowhereZeroFlow G x := by
  exact exists_taitEdgeColoring_iff_exists_nowhereZeroFlow_of_degree_eq_three
    hregular.degree_eq

/-- Manuscript-facing Tait/flow reformulation for cubic graphs. -/
theorem hasTaitEdgeColoring_iff_hasNowhereZeroFlow_of_isCubic
    {G : SimpleGraph V} [Fintype G.edgeSet] [G.LocallyFinite]
    (hG : IsCubic G) :
    HasTaitEdgeColoring G ↔ HasNowhereZeroFlow G := by
  simpa [HasTaitEdgeColoring, HasNowhereZeroFlow, IsCubic] using
    exists_taitEdgeColoring_iff_exists_nowhereZeroFlow_of_isRegularOfDegree_three
      (G := G) hG

/-- The canonical CDL-good local condition is weaker than local nowhere-zero:
the Kirchhoff triple `(0, red, red)` is CDL-good and sums to zero, but still
has a zero edge-value. -/
theorem localCDLGoodKirchhoff_not_nowhereZero_red :
    IsLocalKirchhoffTriple 0 red red ∧
      IsLocalCDLGoodTriple 0 red red ∧
      ¬ IsLocalNowhereZeroTriple 0 red red := by
  exact
    ⟨localKirchhoff_zero_same red,
      localCDLGood_zero_same_of_ne_zero red_ne_zero,
      not_localNowhereZero_zero_left red red⟩

theorem exists_localCDLGoodKirchhoff_not_nowhereZero :
    ∃ a b c : Color,
      IsLocalKirchhoffTriple a b c ∧
        IsLocalCDLGoodTriple a b c ∧
        ¬ IsLocalNowhereZeroTriple a b c := by
  exact ⟨0, red, red, localCDLGoodKirchhoff_not_nowhereZero_red⟩

/-- Thus the local implication from canonical CDL-good Kirchhoff triples to
nowhere-zero triples is false without an additional hypothesis. -/
theorem not_forall_localCDLGoodKirchhoff_implies_nowhereZero :
    ¬ (∀ a b c : Color,
      IsLocalKirchhoffTriple a b c →
      IsLocalCDLGoodTriple a b c →
      IsLocalNowhereZeroTriple a b c) := by
  intro h
  exact localCDLGoodKirchhoff_not_nowhereZero_red.2.2
    (h 0 red red
      localCDLGoodKirchhoff_not_nowhereZero_red.1
      localCDLGoodKirchhoff_not_nowhereZero_red.2.1)

theorem isGraphFlow_of_mem_kirchhoffSubmodule_univ {G : SimpleGraph V}
    [Fintype V] [Fintype G.edgeSet] {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G Finset.univ) :
    IsGraphFlow G x := by
  intro v
  exact hx v (by simp)

theorem mem_kirchhoffSubmodule_univ_of_isGraphFlow {G : SimpleGraph V}
    [Fintype V] [Fintype G.edgeSet] {x : G.edgeSet → Color}
    (hx : IsGraphFlow G x) :
    x ∈ kirchhoffSubmodule G Finset.univ := by
  intro v _hv
  exact hx v

theorem isCDLGoodAtVertex_of_nowhereZero {G : SimpleGraph V} [Fintype G.edgeSet]
    {x : G.edgeSet → Color} {v : V}
    (hincident : (incidentEdgeFinset G v).Nonempty)
    (hnz : ∀ e : G.edgeSet, x e ≠ 0) :
    IsCDLGoodAtVertex G x v := by
  rcases hincident with ⟨e, he⟩
  exact ⟨e, he, hnz e⟩

theorem isCDLGoodFlow_of_nowhereZeroFlow {G : SimpleGraph V} [Fintype G.edgeSet]
    {x : G.edgeSet → Color}
    (hincident : ∀ v : V, (incidentEdgeFinset G v).Nonempty)
    (hx : IsNowhereZeroFlow G x) :
    IsCDLGoodFlow G x := by
  exact ⟨hx.1, fun v => isCDLGoodAtVertex_of_nowhereZero (hincident v) hx.2⟩

/-- For the canonical all-zero-bad CDL gadget, a Tait edge coloring is a
CDL-good flow under the same explicit cubic-incidence hypothesis. -/
theorem isCDLGoodFlow_of_taitEdgeColoring_of_hasCubicIncidentEdgeTriples
    {G : SimpleGraph V} [Fintype G.edgeSet] {C : G.EdgeColoring Color}
    (hG : HasCubicIncidentEdgeTriples G) (hC : IsTaitEdgeColoring G C) :
    IsCDLGoodFlow G C := by
  exact isCDLGoodFlow_of_nowhereZeroFlow
    (incidentEdgeFinset_nonempty_of_hasCubicIncidentEdgeTriples hG)
    (isNowhereZeroFlow_of_taitEdgeColoring_of_hasCubicIncidentEdgeTriples hG hC)

/-- The CDL formulation used here keeps the nonzero condition explicit:
Tait edge colorings are equivalent to flows that are both CDL-good and
nowhere-zero.  This deliberately does not identify CDL-goodness alone with
nowhere-zero. -/
theorem
    exists_taitEdgeColoring_iff_exists_cdlGood_nowhereZeroFlow_of_hasCubicIncidentEdgeTriples
    {G : SimpleGraph V} [Fintype G.edgeSet] (hG : HasCubicIncidentEdgeTriples G) :
    (∃ C : G.EdgeColoring Color, IsTaitEdgeColoring G C) ↔
      ∃ x : G.edgeSet → Color, IsCDLGoodFlow G x ∧ IsNowhereZeroFlow G x := by
  constructor
  · rintro ⟨C, hC⟩
    have hx := isNowhereZeroFlow_of_taitEdgeColoring_of_hasCubicIncidentEdgeTriples hG hC
    exact ⟨C, isCDLGoodFlow_of_taitEdgeColoring_of_hasCubicIncidentEdgeTriples hG hC, hx⟩
  · rintro ⟨x, _hgood, hx⟩
    exact exists_taitEdgeColoring_of_nowhereZeroFlow_of_hasCubicIncidentEdgeTriples hG x hx

/-- CDL-safe Tait/flow reformulation using finite incidence cardinality: the
flow side includes both CDL-goodness and nowhere-zeroness. -/
theorem
    exists_taitEdgeColoring_iff_exists_cdlGood_nowhereZeroFlow_of_incidentEdgeFinset_card_eq_three
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3) :
    (∃ C : G.EdgeColoring Color, IsTaitEdgeColoring G C) ↔
      ∃ x : G.edgeSet → Color, IsCDLGoodFlow G x ∧ IsNowhereZeroFlow G x := by
  exact exists_taitEdgeColoring_iff_exists_cdlGood_nowhereZeroFlow_of_hasCubicIncidentEdgeTriples
    (hasCubicIncidentEdgeTriples_of_incidentEdgeFinset_card_eq_three hcard)

/-- CDL-safe Tait/flow reformulation for graphs whose Mathlib degree is `3` at
every vertex. -/
theorem exists_taitEdgeColoring_iff_exists_cdlGood_nowhereZeroFlow_of_degree_eq_three
    {G : SimpleGraph V} [Fintype G.edgeSet] [G.LocallyFinite]
    (hdegree : ∀ v : V, G.degree v = 3) :
    (∃ C : G.EdgeColoring Color, IsTaitEdgeColoring G C) ↔
      ∃ x : G.edgeSet → Color, IsCDLGoodFlow G x ∧ IsNowhereZeroFlow G x := by
  exact exists_taitEdgeColoring_iff_exists_cdlGood_nowhereZeroFlow_of_hasCubicIncidentEdgeTriples
    (hasCubicIncidentEdgeTriples_of_degree_eq_three hdegree)

/-- CDL-safe Tait/flow reformulation for regular cubic graphs in Mathlib's
sense. -/
theorem
    exists_taitEdgeColoring_iff_exists_cdlGood_nowhereZeroFlow_of_isRegularOfDegree_three
    {G : SimpleGraph V} [Fintype G.edgeSet] [G.LocallyFinite]
    (hregular : G.IsRegularOfDegree 3) :
    (∃ C : G.EdgeColoring Color, IsTaitEdgeColoring G C) ↔
      ∃ x : G.edgeSet → Color, IsCDLGoodFlow G x ∧ IsNowhereZeroFlow G x := by
  exact exists_taitEdgeColoring_iff_exists_cdlGood_nowhereZeroFlow_of_degree_eq_three
    hregular.degree_eq

/-- On cubic graphs, the CDL-safe flow predicate is equivalent to a
nowhere-zero flow. -/
theorem hasCDLGoodNowhereZeroFlow_iff_hasNowhereZeroFlow_of_isCubic
    {G : SimpleGraph V} [Fintype G.edgeSet] [G.LocallyFinite]
    (hG : IsCubic G) :
    HasCDLGoodNowhereZeroFlow G ↔ HasNowhereZeroFlow G := by
  constructor
  · rintro ⟨x, _hgood, hx⟩
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x,
      isCDLGoodFlow_of_nowhereZeroFlow
        (incidentEdgeFinset_nonempty_of_hasCubicIncidentEdgeTriples
          (hasCubicIncidentEdgeTriples_of_isCubic hG)) hx,
      hx⟩

/-- Manuscript-facing form: a CDL-good nowhere-zero flow is a CDL-good flow
whose zero-edge set is empty.  This keeps the empty-zero-set condition explicit,
instead of treating CDL-goodness alone as if it were nowhere-zero. -/
theorem hasCDLGoodNowhereZeroFlow_iff_exists_cdlGoodFlow_zeroEdgeFinset_eq_empty
    {G : SimpleGraph V} [Fintype G.edgeSet] :
    HasCDLGoodNowhereZeroFlow G ↔
      ∃ x : G.edgeSet → Color, IsCDLGoodFlow G x ∧ zeroEdgeFinset G x = ∅ := by
  constructor
  · rintro ⟨x, hgood, hx⟩
    exact ⟨x, hgood, zeroEdgeFinset_eq_empty_iff.mpr hx.2⟩
  · rintro ⟨x, hgood, hzero⟩
    exact ⟨x, hgood,
      (isNowhereZeroFlow_iff_isGraphFlow_and_zeroEdgeFinset_eq_empty).mpr
        ⟨hgood.1, hzero⟩⟩

/-- Count form of the safe CDL/Tait flow surface: the CDL-good flow has zero
zero-edge defect. -/
theorem hasCDLGoodNowhereZeroFlow_iff_exists_cdlGoodFlow_zeroEdgeCount_eq_zero
    {G : SimpleGraph V} [Fintype G.edgeSet] :
    HasCDLGoodNowhereZeroFlow G ↔
      ∃ x : G.edgeSet → Color, IsCDLGoodFlow G x ∧ zeroEdgeCount G x = 0 := by
  constructor
  · rintro ⟨x, hgood, hx⟩
    exact ⟨x, hgood, zeroEdgeCount_eq_zero_iff.mpr hx.2⟩
  · rintro ⟨x, hgood, hzero⟩
    exact ⟨x, hgood,
      (isNowhereZeroFlow_iff_isGraphFlow_and_zeroEdgeCount_eq_zero).mpr
        ⟨hgood.1, hzero⟩⟩

/-- Manuscript-facing safe CDL/Tait reformulation for cubic graphs. -/
theorem hasTaitEdgeColoring_iff_hasCDLGoodNowhereZeroFlow_of_isCubic
    {G : SimpleGraph V} [Fintype G.edgeSet] [G.LocallyFinite]
    (hG : IsCubic G) :
    HasTaitEdgeColoring G ↔ HasCDLGoodNowhereZeroFlow G := by
  simpa [HasTaitEdgeColoring, HasCDLGoodNowhereZeroFlow, IsCubic] using
    exists_taitEdgeColoring_iff_exists_cdlGood_nowhereZeroFlow_of_isRegularOfDegree_three
      (G := G) hG

theorem zeroChain_isGraphFlow (G : SimpleGraph V) [Fintype G.edgeSet] :
    IsGraphFlow G (zeroChain : G.edgeSet → Color) := by
  intro v
  simp [vertexKirchhoffSum, zeroChain]

theorem not_isCDLGoodAtVertex_zeroChain (G : SimpleGraph V) [Fintype G.edgeSet]
    (v : V) :
    ¬ IsCDLGoodAtVertex G (zeroChain : G.edgeSet → Color) v := by
  intro h
  rcases h with ⟨e, _he, hne⟩
  exact hne rfl

theorem zeroChain_not_isCDLGoodFlow_of_nonempty_incident (G : SimpleGraph V)
    [Fintype G.edgeSet]
    (hincident : ∃ v : V, (incidentEdgeFinset G v).Nonempty) :
    ¬ IsCDLGoodFlow G (zeroChain : G.edgeSet → Color) := by
  intro hgood
  rcases hincident with ⟨v, _hv⟩
  exact not_isCDLGoodAtVertex_zeroChain G v (hgood.2 v)

end Mettapedia.GraphTheory.FourColor

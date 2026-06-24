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

theorem zeroEdgeCount_eq_outside_support_add_inside_support
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {C : Finset G.edgeSet} {x : G.edgeSet → Color} :
    zeroEdgeCount G x =
      ((zeroEdgeFinset G x).filter (fun e => e ∉ C)).card +
        ((zeroEdgeFinset G x).filter (fun e => e ∈ C)).card := by
  rw [zeroEdgeCount]
  have hdisj :
      Disjoint ((zeroEdgeFinset G x).filter (fun e => e ∉ C))
        ((zeroEdgeFinset G x).filter (fun e => e ∈ C)) := by
    rw [Finset.disjoint_left]
    intro e heOutside heInside
    exact (Finset.mem_filter.mp heOutside).2 (Finset.mem_filter.mp heInside).2
  have hunion :
      (zeroEdgeFinset G x).filter (fun e => e ∉ C) ∪
        (zeroEdgeFinset G x).filter (fun e => e ∈ C) =
          zeroEdgeFinset G x := by
    ext e
    by_cases heC : e ∈ C <;> simp [heC]
  calc
    (zeroEdgeFinset G x).card =
        ((zeroEdgeFinset G x).filter (fun e => e ∉ C) ∪
          (zeroEdgeFinset G x).filter (fun e => e ∈ C)).card := by
          rw [hunion]
    _ = ((zeroEdgeFinset G x).filter (fun e => e ∉ C)).card +
          ((zeroEdgeFinset G x).filter (fun e => e ∈ C)).card := by
          rw [Finset.card_union_of_disjoint hdisj]

theorem zeroEdgeCount_cdlOneStepMoveOn_add_one_le_of_support_zero_surplus
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {C : Finset G.edgeSet} {g : Color} {x : G.edgeSet → Color}
    (h :
      (C.filter (fun e => x e = g)).card + 1 ≤
        ((zeroEdgeFinset G x).filter (fun e => e ∈ C)).card) :
    zeroEdgeCount G (cdlOneStepMoveOn G C g x) + 1 ≤ zeroEdgeCount G x := by
  rw [zeroEdgeCount_cdlOneStepMoveOn_eq,
    zeroEdgeCount_eq_outside_support_add_inside_support (C := C)]
  omega

theorem zeroEdgeCount_cdlOneStepMoveOn_add_one_le_of_erases_zero_and_creates_no_zero
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {C : Finset G.edgeSet} {g : Color} {x : G.edgeSet → Color}
    (herase : ∃ e ∈ C, x e = 0)
    (hnew : ∀ e ∈ C, x e ≠ g) :
    zeroEdgeCount G (cdlOneStepMoveOn G C g x) + 1 ≤ zeroEdgeCount G x := by
  apply zeroEdgeCount_cdlOneStepMoveOn_add_one_le_of_support_zero_surplus
  have hnew_empty : C.filter (fun e => x e = g) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    exact hnew
  rw [hnew_empty]
  rw [Finset.card_empty, zero_add]
  rcases herase with ⟨e, heC, hx⟩
  have hzero : e ∈ zeroEdgeFinset G x := by
    rw [zeroEdgeFinset]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ e, hx⟩
  have hinside : e ∈ (zeroEdgeFinset G x).filter (fun e => e ∈ C) :=
    Finset.mem_filter.mpr ⟨hzero, heC⟩
  exact Nat.succ_le_of_lt
    (Finset.card_pos.mpr ⟨e, hinside⟩)

theorem zeroEdgeFinset_cdlOneStepMoveOn_eq_filter_not_mem_of_creates_no_zero
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {C : Finset G.edgeSet} {g : Color} {x : G.edgeSet → Color}
    (hnew : ∀ e ∈ C, x e ≠ g) :
    zeroEdgeFinset G (cdlOneStepMoveOn G C g x) =
      (zeroEdgeFinset G x).filter (fun e => e ∉ C) := by
  rw [zeroEdgeFinset_cdlOneStepMoveOn_eq]
  have hnew_empty : C.filter (fun e => x e = g) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    exact hnew
  rw [hnew_empty, Finset.union_empty]

theorem zeroIncidentEdgeFinset_cdlOneStepMoveOn_subset_of_creates_no_zero
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {C : Finset G.edgeSet} {g : Color} {x : G.edgeSet → Color}
    (hnew : ∀ e ∈ C, x e ≠ g) (v : V) :
    zeroIncidentEdgeFinset G (cdlOneStepMoveOn G C g x) v ⊆
      zeroIncidentEdgeFinset G x v := by
  intro e he
  have htarget :
      e ∈ incidentEdgeFinset G v ∧ cdlOneStepMoveOn G C g x e = 0 := by
    simpa [zeroIncidentEdgeFinset] using he
  by_cases heC : e ∈ C
  · have hxg : x e = g :=
      (cdlOneStepMoveOn_apply_mem_eq_zero_iff heC).mp htarget.2
    exact False.elim ((hnew e heC) hxg)
  · have hx0 : x e = 0 :=
      (cdlOneStepMoveOn_apply_not_mem_eq_zero_iff heC).mp htarget.2
    exact Finset.mem_filter.mpr ⟨htarget.1, hx0⟩

theorem zeroIncidentEdgeCount_cdlOneStepMoveOn_le_of_creates_no_zero
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {C : Finset G.edgeSet} {g : Color} {x : G.edgeSet → Color}
    (hnew : ∀ e ∈ C, x e ≠ g) (v : V) :
    zeroIncidentEdgeCount G (cdlOneStepMoveOn G C g x) v ≤
      zeroIncidentEdgeCount G x v := by
  rw [zeroIncidentEdgeCount, zeroIncidentEdgeCount]
  exact Finset.card_le_card
    (zeroIncidentEdgeFinset_cdlOneStepMoveOn_subset_of_creates_no_zero hnew v)

theorem zeroIncidentVertexFinset_cdlOneStepMoveOn_subset_of_creates_no_zero
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {C : Finset G.edgeSet} {g : Color} {x : G.edgeSet → Color}
    (hnew : ∀ e ∈ C, x e ≠ g) :
    zeroIncidentVertexFinset G (cdlOneStepMoveOn G C g x) ⊆
      zeroIncidentVertexFinset G x := by
  intro v hv
  have hvpos :
      0 < zeroIncidentEdgeCount G (cdlOneStepMoveOn G C g x) v := by
    simpa [zeroIncidentVertexFinset] using hv
  have hle :
      zeroIncidentEdgeCount G (cdlOneStepMoveOn G C g x) v ≤
        zeroIncidentEdgeCount G x v :=
    zeroIncidentEdgeCount_cdlOneStepMoveOn_le_of_creates_no_zero hnew v
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, lt_of_lt_of_le hvpos hle⟩

theorem zeroIncidentVertexCount_cdlOneStepMoveOn_le_of_creates_no_zero
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {C : Finset G.edgeSet} {g : Color} {x : G.edgeSet → Color}
    (hnew : ∀ e ∈ C, x e ≠ g) :
    zeroIncidentVertexCount G (cdlOneStepMoveOn G C g x) ≤
      zeroIncidentVertexCount G x := by
  rw [zeroIncidentVertexCount, zeroIncidentVertexCount]
  exact Finset.card_le_card
    (zeroIncidentVertexFinset_cdlOneStepMoveOn_subset_of_creates_no_zero hnew)

theorem zeroClusteringCount_cdlOneStepMoveOn_le_of_creates_no_zero
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {C : Finset G.edgeSet} {g : Color} {x : G.edgeSet → Color}
    (hnew : ∀ e ∈ C, x e ≠ g) :
    zeroClusteringCount G (cdlOneStepMoveOn G C g x) ≤
      zeroClusteringCount G x := by
  unfold zeroClusteringCount
  apply Finset.sum_le_sum
  intro v _hv
  exact Nat.sub_le_sub_right
    (zeroIncidentEdgeCount_cdlOneStepMoveOn_le_of_creates_no_zero hnew v) 1

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

theorem exists_support_edge_color_of_isCDLGoodAtVertex_and_forced_zero_move
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {C : Finset G.edgeSet} {g : Color} {x : G.edgeSet → Color} {v : V}
    (hgood : IsCDLGoodAtVertex G x v)
    (hforced :
      ∀ e ∈ incidentEdgeFinset G v, if e ∈ C then x e = g else x e = 0) :
    ∃ e ∈ incidentEdgeFinset G v, e ∈ C ∧ x e = g := by
  rcases hgood with ⟨e, heinc, hxne⟩
  by_cases heC : e ∈ C
  · exact ⟨e, heinc, heC, by simpa [heC] using hforced e heinc⟩
  · have hx0 : x e = 0 := by
      simpa [heC] using hforced e heinc
    exact False.elim (hxne hx0)

theorem incident_support_card_eq_two_of_isCDLGoodAtVertex_and_forced_zero_move
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {C : Finset G.edgeSet} {g : Color} {x : G.edgeSet → Color} {v : V}
    (hcard : (incidentEdgeFinset G v).card = 3)
    (hC : IsKirchhoffNeutralMoveSupport G C)
    (hgood : IsCDLGoodAtVertex G x v)
    (hforced :
      ∀ e ∈ incidentEdgeFinset G v, if e ∈ C then x e = g else x e = 0) :
    ((incidentEdgeFinset G v).filter fun e => e ∈ C).card = 2 := by
  rcases
    exists_support_edge_color_of_isCDLGoodAtVertex_and_forced_zero_move
      hgood hforced with ⟨e, heinc, heC, _hx⟩
  have hpos : 0 < ((incidentEdgeFinset G v).filter fun e => e ∈ C).card := by
    exact Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨heinc, heC⟩⟩
  have hle :
      ((incidentEdgeFinset G v).filter fun e => e ∈ C).card ≤ 3 := by
    have hle_filter :
        ((incidentEdgeFinset G v).filter fun e => e ∈ C).card ≤
          (incidentEdgeFinset G v).card :=
      Finset.card_filter_le _ _
    omega
  rcases hC v with ⟨k, hk⟩
  omega

theorem exists_outside_zero_incident_edge_of_cubic_two_support_forced_zero_move
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {C : Finset G.edgeSet} {g : Color} {x : G.edgeSet → Color} {v : V}
    (hcard : (incidentEdgeFinset G v).card = 3)
    (htwo : ((incidentEdgeFinset G v).filter fun e => e ∈ C).card = 2)
    (hforced :
      ∀ e ∈ incidentEdgeFinset G v, if e ∈ C then x e = g else x e = 0) :
    ∃ e ∈ incidentEdgeFinset G v, e ∉ C ∧ x e = 0 := by
  have houtside_card :
      ((incidentEdgeFinset G v).filter fun e => e ∉ C).card = 1 := by
    have hsplit :=
      Finset.card_filter_add_card_filter_not
        (s := incidentEdgeFinset G v) (p := fun e => e ∈ C)
    omega
  have houtside_nonempty :
      ((incidentEdgeFinset G v).filter fun e => e ∉ C).Nonempty := by
    exact Finset.card_pos.mp (by omega)
  rcases houtside_nonempty with ⟨e, he⟩
  have hedata : e ∈ incidentEdgeFinset G v ∧ e ∉ C := by
    simpa using Finset.mem_filter.mp he
  have hx : x e = 0 := by
    simpa [hedata.2] using hforced e hedata.1
  exact ⟨e, hedata.1, hedata.2, hx⟩

theorem zeroIncidentEdgeCount_eq_one_of_cubic_two_support_forced_zero_move
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {C : Finset G.edgeSet} {g : Color} {x : G.edgeSet → Color} {v : V}
    (hg : g ≠ 0)
    (hcard : (incidentEdgeFinset G v).card = 3)
    (htwo : ((incidentEdgeFinset G v).filter fun e => e ∈ C).card = 2)
    (hforced :
      ∀ e ∈ incidentEdgeFinset G v, if e ∈ C then x e = g else x e = 0) :
    zeroIncidentEdgeCount G x v = 1 := by
  have hzero_set :
      zeroIncidentEdgeFinset G x v =
        (incidentEdgeFinset G v).filter fun e => e ∉ C := by
    ext e
    constructor
    · intro he
      have hedata : e ∈ incidentEdgeFinset G v ∧ x e = 0 := by
        simpa [zeroIncidentEdgeFinset] using he
      refine Finset.mem_filter.mpr ⟨hedata.1, ?_⟩
      intro heC
      have hxg : x e = g := by
        simpa [heC] using hforced e hedata.1
      have hg0 : g = 0 := by
        rw [← hxg, hedata.2]
      exact hg hg0
    · intro he
      have hedata : e ∈ incidentEdgeFinset G v ∧ e ∉ C := by
        simpa using Finset.mem_filter.mp he
      have hx : x e = 0 := by
        simpa [hedata.2] using hforced e hedata.1
      exact Finset.mem_filter.mpr ⟨hedata.1, hx⟩
  have houtside_card :
      ((incidentEdgeFinset G v).filter fun e => e ∉ C).card = 1 := by
    have hsplit :=
      Finset.card_filter_add_card_filter_not
        (s := incidentEdgeFinset G v) (p := fun e => e ∈ C)
    omega
  rw [zeroIncidentEdgeCount, hzero_set, houtside_card]

theorem zeroClusteringLocalTerm_eq_zero_of_zeroIncidentEdgeCount_eq_one
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {x : G.edgeSet → Color} {v : V}
    (hcount : zeroIncidentEdgeCount G x v = 1) :
    zeroIncidentEdgeCount G x v - 1 = 0 := by
  omega

theorem zeroClusteringLocalTerm_eq_zero_of_cubic_two_support_forced_zero_move
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {C : Finset G.edgeSet} {g : Color} {x : G.edgeSet → Color} {v : V}
    (hg : g ≠ 0)
    (hcard : (incidentEdgeFinset G v).card = 3)
    (htwo : ((incidentEdgeFinset G v).filter fun e => e ∈ C).card = 2)
    (hforced :
      ∀ e ∈ incidentEdgeFinset G v, if e ∈ C then x e = g else x e = 0) :
    zeroIncidentEdgeCount G x v - 1 = 0 :=
  zeroClusteringLocalTerm_eq_zero_of_zeroIncidentEdgeCount_eq_one
    (zeroIncidentEdgeCount_eq_one_of_cubic_two_support_forced_zero_move
      hg hcard htwo hforced)

theorem zeroIncidentVertexFinset_mem_of_zeroIncidentEdgeCount_eq_one
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {x : G.edgeSet → Color} {v : V}
    (hcount : zeroIncidentEdgeCount G x v = 1) :
    v ∈ zeroIncidentVertexFinset G x := by
  simp [zeroIncidentVertexFinset, hcount]

theorem zeroIncidentVertexCount_pos_of_exists_zeroIncidentEdgeCount_eq_one
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {x : G.edgeSet → Color}
    (hcount : ∃ v : V, zeroIncidentEdgeCount G x v = 1) :
    0 < zeroIncidentVertexCount G x := by
  rcases hcount with ⟨v, hv⟩
  unfold zeroIncidentVertexCount
  exact Finset.card_pos.mpr
    ⟨v, zeroIncidentVertexFinset_mem_of_zeroIncidentEdgeCount_eq_one hv⟩

theorem zeroIncidentVertexCount_pos_of_cubic_two_support_forced_zero_move
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {C : Finset G.edgeSet} {g : Color} {x : G.edgeSet → Color} {v : V}
    (hg : g ≠ 0)
    (hcard : (incidentEdgeFinset G v).card = 3)
    (htwo : ((incidentEdgeFinset G v).filter fun e => e ∈ C).card = 2)
    (hforced :
      ∀ e ∈ incidentEdgeFinset G v, if e ∈ C then x e = g else x e = 0) :
    0 < zeroIncidentVertexCount G x :=
  zeroIncidentVertexCount_pos_of_exists_zeroIncidentEdgeCount_eq_one
    ⟨v, zeroIncidentEdgeCount_eq_one_of_cubic_two_support_forced_zero_move
      hg hcard htwo hforced⟩

/-- A local cubic obstruction forced by a failed basic color move at a D₀ local
minimum.  It packages the pieces used by the manuscript's cheap defect:
one zero edge at the vertex, no local clustering contribution there, a globally
nonempty incident-zero vertex set, and an explicit outside zero edge. -/
def HasCubicD0BasicColorObstructionAt (G : SimpleGraph V)
    [Fintype V] [Fintype G.edgeSet] (x : G.edgeSet → Color)
    (C : Finset G.edgeSet) (v : V) (g : Color) : Prop :=
  g ≠ 0 ∧
    zeroIncidentEdgeCount G x v = 1 ∧
    zeroIncidentEdgeCount G x v - 1 = 0 ∧
    0 < zeroIncidentVertexCount G x ∧
    ∃ e : G.edgeSet,
      e ∈ incidentEdgeFinset G v ∧ e ∉ C ∧ x e = 0 ∧
        ∀ e' ∈ incidentEdgeFinset G v,
          if e' ∈ C then x e' = g else x e' = 0

theorem hasCubicD0BasicColorObstructionAt_of_cubic_two_support_forced_zero_move
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {C : Finset G.edgeSet} {g : Color} {x : G.edgeSet → Color} {v : V}
    (hg : g ≠ 0)
    (hcard : (incidentEdgeFinset G v).card = 3)
    (htwo : ((incidentEdgeFinset G v).filter fun e => e ∈ C).card = 2)
    (hforced :
      ∀ e ∈ incidentEdgeFinset G v, if e ∈ C then x e = g else x e = 0) :
    HasCubicD0BasicColorObstructionAt G x C v g := by
  refine ⟨hg,
    zeroIncidentEdgeCount_eq_one_of_cubic_two_support_forced_zero_move
      hg hcard htwo hforced,
    zeroClusteringLocalTerm_eq_zero_of_cubic_two_support_forced_zero_move
      hg hcard htwo hforced,
    zeroIncidentVertexCount_pos_of_cubic_two_support_forced_zero_move
      hg hcard htwo hforced,
    ?_⟩
  rcases
    exists_outside_zero_incident_edge_of_cubic_two_support_forced_zero_move
      hcard htwo hforced with ⟨e, heinc, heC, hx⟩
  exact ⟨e, heinc, heC, hx, hforced⟩

/-- The forced incident-neighborhood equation stored in a cubic D₀ basic-color
obstruction. -/
theorem forced_incident_colors_of_hasCubicD0BasicColorObstructionAt
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {C : Finset G.edgeSet} {g : Color} {x : G.edgeSet → Color} {v : V}
    (hobst : HasCubicD0BasicColorObstructionAt G x C v g) :
    ∀ e ∈ incidentEdgeFinset G v, if e ∈ C then x e = g else x e = 0 := by
  rcases hobst with
    ⟨_hg, _hcount, _hclustering, _hincident, _e, _heinc, _heC, _hx, hforced⟩
  exact hforced

theorem incident_support_color_eq_of_hasCubicD0BasicColorObstructionAt
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {C : Finset G.edgeSet} {g : Color} {x : G.edgeSet → Color} {v : V}
    (hobst : HasCubicD0BasicColorObstructionAt G x C v g)
    {e : G.edgeSet} (heinc : e ∈ incidentEdgeFinset G v) (heC : e ∈ C) :
    x e = g := by
  simpa [heC] using
    forced_incident_colors_of_hasCubicD0BasicColorObstructionAt hobst e heinc

theorem incident_outside_color_eq_zero_of_hasCubicD0BasicColorObstructionAt
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {C : Finset G.edgeSet} {g : Color} {x : G.edgeSet → Color} {v : V}
    (hobst : HasCubicD0BasicColorObstructionAt G x C v g)
    {e : G.edgeSet} (heinc : e ∈ incidentEdgeFinset G v) (heC : e ∉ C) :
    x e = 0 := by
  simpa [heC] using
    forced_incident_colors_of_hasCubicD0BasicColorObstructionAt hobst e heinc

/-- In a cubic D₀ basic-color obstruction, the incident zero edges are exactly
the incident edges outside the proposed support. -/
theorem zeroIncidentEdgeFinset_eq_incident_filter_not_mem_of_hasCubicD0BasicColorObstructionAt
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {C : Finset G.edgeSet} {g : Color} {x : G.edgeSet → Color} {v : V}
    (hobst : HasCubicD0BasicColorObstructionAt G x C v g) :
    zeroIncidentEdgeFinset G x v =
      (incidentEdgeFinset G v).filter fun e => e ∉ C := by
  rcases hobst with
    ⟨hg, _hcount, _hclustering, _hincident, _e, _heinc, _heC, _hx, hforced⟩
  ext e
  by_cases heinc : e ∈ incidentEdgeFinset G v
  · by_cases heC : e ∈ C
    · have hxg : x e = g := by simpa [heC] using hforced e heinc
      simp [zeroIncidentEdgeFinset, heinc, heC, hxg, hg]
    · have hx0 : x e = 0 := by simpa [heC] using hforced e heinc
      simp [zeroIncidentEdgeFinset, heinc, heC, hx0]
  · simp [zeroIncidentEdgeFinset, heinc]

theorem incident_outside_filter_card_eq_one_of_hasCubicD0BasicColorObstructionAt
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {C : Finset G.edgeSet} {g : Color} {x : G.edgeSet → Color} {v : V}
    (hobst : HasCubicD0BasicColorObstructionAt G x C v g) :
    ((incidentEdgeFinset G v).filter fun e => e ∉ C).card = 1 := by
  have hzeroeq :=
    zeroIncidentEdgeFinset_eq_incident_filter_not_mem_of_hasCubicD0BasicColorObstructionAt
      hobst
  rcases hobst with ⟨_hg, hcount, _hclustering, _hincident, _e, _heinc, _heC,
    _hx, _hforced⟩
  rw [← hzeroeq]
  simpa [zeroIncidentEdgeCount] using hcount

/-- In a cubic obstruction, exactly two incident edges lie in the proposed
support. -/
theorem incident_support_filter_card_eq_two_of_hasCubicD0BasicColorObstructionAt
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {C : Finset G.edgeSet} {g : Color} {x : G.edgeSet → Color} {v : V}
    (hcard : (incidentEdgeFinset G v).card = 3)
    (hobst : HasCubicD0BasicColorObstructionAt G x C v g) :
    ((incidentEdgeFinset G v).filter fun e => e ∈ C).card = 2 := by
  have hout :
      ((incidentEdgeFinset G v).filter fun e => e ∉ C).card = 1 :=
    incident_outside_filter_card_eq_one_of_hasCubicD0BasicColorObstructionAt
      hobst
  have hsum :=
    Finset.card_filter_add_card_filter_not
      (s := incidentEdgeFinset G v) (p := fun e : G.edgeSet => e ∈ C)
  rw [hout, hcard] at hsum
  omega

theorem incident_outside_edge_unique_of_hasCubicD0BasicColorObstructionAt
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {C : Finset G.edgeSet} {g : Color} {x : G.edgeSet → Color} {v : V}
    (hobst : HasCubicD0BasicColorObstructionAt G x C v g)
    {e e' : G.edgeSet}
    (heinc : e ∈ incidentEdgeFinset G v) (heC : e ∉ C)
    (heinc' : e' ∈ incidentEdgeFinset G v) (heC' : e' ∉ C) :
    e = e' := by
  have hout :
      ((incidentEdgeFinset G v).filter fun e => e ∉ C).card = 1 :=
    incident_outside_filter_card_eq_one_of_hasCubicD0BasicColorObstructionAt
      hobst
  rcases Finset.card_eq_one.mp hout with ⟨a, ha⟩
  have he_mem : e ∈ (incidentEdgeFinset G v).filter (fun e => e ∉ C) := by
    simp [heinc, heC]
  have he_mem' : e' ∈ (incidentEdgeFinset G v).filter (fun e => e ∉ C) := by
    simp [heinc', heC']
  rw [ha] at he_mem he_mem'
  simp at he_mem he_mem'
  exact he_mem.trans he_mem'.symm

/-- In a cubic D₀ basic-color obstruction, the local zero-incidence set at the
obstructed vertex is a singleton: the unique incident edge outside the proposed
support. -/
theorem
    exists_zeroIncidentEdgeFinset_eq_singleton_of_hasCubicD0BasicColorObstructionAt
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {C : Finset G.edgeSet} {g : Color} {x : G.edgeSet → Color} {v : V}
    (hobst : HasCubicD0BasicColorObstructionAt G x C v g) :
    ∃ e : G.edgeSet,
      zeroIncidentEdgeFinset G x v = {e} ∧
        e ∈ incidentEdgeFinset G v ∧ e ∉ C ∧ x e = 0 := by
  have hzeroeq :
      zeroIncidentEdgeFinset G x v =
        (incidentEdgeFinset G v).filter fun e => e ∉ C :=
    zeroIncidentEdgeFinset_eq_incident_filter_not_mem_of_hasCubicD0BasicColorObstructionAt
      hobst
  have houtside :
      ((incidentEdgeFinset G v).filter fun e => e ∉ C).card = 1 :=
    incident_outside_filter_card_eq_one_of_hasCubicD0BasicColorObstructionAt
      hobst
  rcases hobst with
    ⟨_hg, _hcount, _hclustering, _hincident, e, heinc, heC, hx,
      _hforced⟩
  rcases Finset.card_eq_one.mp houtside with ⟨a, ha⟩
  have he_mem : e ∈ (incidentEdgeFinset G v).filter (fun e => e ∉ C) := by
    simp [heinc, heC]
  rw [ha] at he_mem
  simp at he_mem
  have hfilter :
      ((incidentEdgeFinset G v).filter fun e => e ∉ C) = {e} := by
    simpa [he_mem] using ha
  exact ⟨e, by rw [hzeroeq, hfilter], heinc, heC, hx⟩

/-- Concrete star form of a cubic D₀ basic-color obstruction: at the obstructed
vertex there are two distinct support edges, both colored by the proposed move
color `g`, and one distinct outside edge colored zero. -/
theorem
    exists_support_pair_and_outside_zero_of_hasCubicD0BasicColorObstructionAt
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {C : Finset G.edgeSet} {g : Color} {x : G.edgeSet → Color} {v : V}
    (hcard : (incidentEdgeFinset G v).card = 3)
    (hobst : HasCubicD0BasicColorObstructionAt G x C v g) :
    ∃ e₁ e₂ e₀ : G.edgeSet,
      e₁ ≠ e₂ ∧ e₁ ≠ e₀ ∧ e₂ ≠ e₀ ∧
        e₁ ∈ incidentEdgeFinset G v ∧ e₂ ∈ incidentEdgeFinset G v ∧
          e₀ ∈ incidentEdgeFinset G v ∧
            e₁ ∈ C ∧ e₂ ∈ C ∧ e₀ ∉ C ∧
              x e₁ = g ∧ x e₂ = g ∧ x e₀ = 0 := by
  have hsupport :
      ((incidentEdgeFinset G v).filter fun e => e ∈ C).card = 2 :=
    incident_support_filter_card_eq_two_of_hasCubicD0BasicColorObstructionAt
      hcard hobst
  have houtside :
      ((incidentEdgeFinset G v).filter fun e => e ∉ C).card = 1 :=
    incident_outside_filter_card_eq_one_of_hasCubicD0BasicColorObstructionAt
      hobst
  rcases Finset.card_eq_two.mp hsupport with ⟨e₁, e₂, h12, hsupp⟩
  rcases Finset.card_eq_one.mp houtside with ⟨e₀, hout⟩
  have he₁mem : e₁ ∈ (incidentEdgeFinset G v).filter (fun e => e ∈ C) := by
    rw [hsupp]
    simp [h12]
  have he₂mem : e₂ ∈ (incidentEdgeFinset G v).filter (fun e => e ∈ C) := by
    rw [hsupp]
    simp
  have he₀mem : e₀ ∈ (incidentEdgeFinset G v).filter (fun e => e ∉ C) := by
    rw [hout]
    simp
  rcases Finset.mem_filter.mp he₁mem with ⟨he₁inc, he₁C⟩
  rcases Finset.mem_filter.mp he₂mem with ⟨he₂inc, he₂C⟩
  rcases Finset.mem_filter.mp he₀mem with ⟨he₀inc, he₀C⟩
  have h10 : e₁ ≠ e₀ := by
    intro h
    exact he₀C (by simpa [h] using he₁C)
  have h20 : e₂ ≠ e₀ := by
    intro h
    exact he₀C (by simpa [h] using he₂C)
  exact ⟨e₁, e₂, e₀, h12, h10, h20,
    he₁inc, he₂inc, he₀inc, he₁C, he₂C, he₀C,
    incident_support_color_eq_of_hasCubicD0BasicColorObstructionAt
      hobst he₁inc he₁C,
    incident_support_color_eq_of_hasCubicD0BasicColorObstructionAt
      hobst he₂inc he₂C,
    incident_outside_color_eq_zero_of_hasCubicD0BasicColorObstructionAt
      hobst he₀inc he₀C⟩

/-- Exact cubic-star partition for a cubic D₀ basic-color obstruction: the
three incident edges are precisely the two support edges of color `g` and the
unique outside zero edge. -/
theorem
    exists_incidentEdgeFinset_eq_support_pair_insert_outside_zero_of_hasCubicD0BasicColorObstructionAt
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {C : Finset G.edgeSet} {g : Color} {x : G.edgeSet → Color} {v : V}
    (hcard : (incidentEdgeFinset G v).card = 3)
    (hobst : HasCubicD0BasicColorObstructionAt G x C v g) :
    ∃ e₁ e₂ e₀ : G.edgeSet,
      e₁ ≠ e₂ ∧ e₁ ≠ e₀ ∧ e₂ ≠ e₀ ∧
        incidentEdgeFinset G v = {e₁, e₂, e₀} ∧
          e₁ ∈ C ∧ e₂ ∈ C ∧ e₀ ∉ C ∧
            x e₁ = g ∧ x e₂ = g ∧ x e₀ = 0 := by
  rcases
    exists_support_pair_and_outside_zero_of_hasCubicD0BasicColorObstructionAt
      hcard hobst with
    ⟨e₁, e₂, e₀, h12, h10, h20, he₁inc, he₂inc, he₀inc, he₁C, he₂C,
      he₀C, hx₁, hx₂, hx₀⟩
  let star : Finset G.edgeSet := {e₁, e₂, e₀}
  have hstar_subset : star ⊆ incidentEdgeFinset G v := by
    intro e he
    simp only [star, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact he₁inc
    · exact he₂inc
    · exact he₀inc
  have hstar_card : star.card = 3 := by
    simp [star, h12, h10, h20]
  have hcard_le : (incidentEdgeFinset G v).card ≤ star.card := by
    rw [hcard, hstar_card]
  have hstar_eq : incidentEdgeFinset G v = star :=
    (Finset.eq_of_subset_of_card_le hstar_subset hcard_le).symm
  exact ⟨e₁, e₂, e₀, h12, h10, h20, hstar_eq, he₁C, he₂C, he₀C,
    hx₁, hx₂, hx₀⟩

theorem not_isCDLGoodAtVertex_cdlOneStepMoveOn_of_hasCubicD0BasicColorObstructionAt
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {C : Finset G.edgeSet} {g : Color} {x : G.edgeSet → Color} {v : V}
    (hobst : HasCubicD0BasicColorObstructionAt G x C v g) :
    ¬ IsCDLGoodAtVertex G (cdlOneStepMoveOn G C g x) v := by
  rcases hobst with ⟨_hg, _hcount, _hclustering, _hincident, _e, _heinc, _heC, _hx,
    hforced⟩
  exact not_isCDLGoodAtVertex_cdlOneStepMoveOn_iff.mpr hforced

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

theorem not_isAllowedD0OneStepMoveOn_of_hasCubicD0BasicColorObstructionAt
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {C : Finset G.edgeSet} {g : Color} {x : G.edgeSet → Color} {v : V}
    (hx : IsGraphFlow G x)
    (hC : IsKirchhoffNeutralMoveSupport G C)
    (hobst : HasCubicD0BasicColorObstructionAt G x C v g) :
    ¬ IsAllowedD0OneStepMoveOn G C g x (cdlOneStepMoveOn G C g x) := by
  rcases hobst with ⟨hg, _hcount, _hclustering, _hincident, _e, _heinc, _heC, _hx,
    hforced⟩
  rw [not_isAllowedD0OneStepMoveOn_iff_exists_vertex_forced_zero_of_kirchhoffNeutral
    hg hx hC]
  exact ⟨v, hforced⟩

theorem zeroEdgeFinset_nonempty_of_hasCubicD0BasicColorObstructionAt
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {C : Finset G.edgeSet} {g : Color} {x : G.edgeSet → Color} {v : V}
    (hobst : HasCubicD0BasicColorObstructionAt G x C v g) :
    (zeroEdgeFinset G x).Nonempty := by
  rcases hobst with ⟨_hg, _hcount, _hclustering, _hincident, e, _heinc, _heC, hx,
    _hforced⟩
  exact ⟨e, by simp [zeroEdgeFinset, hx]⟩

theorem zeroEdgeCount_pos_of_hasCubicD0BasicColorObstructionAt
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {C : Finset G.edgeSet} {g : Color} {x : G.edgeSet → Color} {v : V}
    (hobst : HasCubicD0BasicColorObstructionAt G x C v g) :
    0 < zeroEdgeCount G x := by
  rw [zeroEdgeCount]
  exact Finset.card_pos.mpr
    (zeroEdgeFinset_nonempty_of_hasCubicD0BasicColorObstructionAt hobst)

omit [DecidableEq V] in
theorem zeroEdgeCount_pos_of_exists_edge_eq_zero
    {G : SimpleGraph V} [Fintype G.edgeSet] {x : G.edgeSet → Color}
    (hzero : ∃ e : G.edgeSet, x e = 0) :
    0 < zeroEdgeCount G x := by
  rcases hzero with ⟨e, he⟩
  unfold zeroEdgeCount
  exact Finset.card_pos.mpr ⟨e, by simp [zeroEdgeFinset, he]⟩

theorem zeroDefectD0_pos_of_hasCubicD0BasicColorObstructionAt
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {C : Finset G.edgeSet} {g : Color} {x : G.edgeSet → Color} {v : V}
    (hobst : HasCubicD0BasicColorObstructionAt G x C v g) :
    0 < zeroDefectD0 G x := by
  have hZ : 0 < zeroEdgeCount G x :=
    zeroEdgeCount_pos_of_hasCubicD0BasicColorObstructionAt hobst
  unfold zeroDefectD0
  omega

theorem not_isNowhereZeroFlow_of_hasCubicD0BasicColorObstructionAt
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {C : Finset G.edgeSet} {g : Color} {x : G.edgeSet → Color} {v : V}
    (hobst : HasCubicD0BasicColorObstructionAt G x C v g) :
    ¬ IsNowhereZeroFlow G x := by
  rcases hobst with ⟨_hg, _hcount, _hclustering, _hincident, e, _heinc, _heC, hx,
    _hforced⟩
  intro hflow
  exact hflow.2 e hx

theorem zeroDefectD0_pos_of_exists_hasCubicD0BasicColorObstructionAt
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {C : Finset G.edgeSet} {x : G.edgeSet → Color}
    (hobst :
      (∃ v : V, HasCubicD0BasicColorObstructionAt G x C v red) ∨
        (∃ v : V, HasCubicD0BasicColorObstructionAt G x C v blue) ∨
          (∃ v : V, HasCubicD0BasicColorObstructionAt G x C v purple)) :
    0 < zeroDefectD0 G x := by
  rcases hobst with hred | hblue | hpurple
  · rcases hred with ⟨_v, hobst⟩
    exact zeroDefectD0_pos_of_hasCubicD0BasicColorObstructionAt hobst
  · rcases hblue with ⟨_v, hobst⟩
    exact zeroDefectD0_pos_of_hasCubicD0BasicColorObstructionAt hobst
  · rcases hpurple with ⟨_v, hobst⟩
    exact zeroDefectD0_pos_of_hasCubicD0BasicColorObstructionAt hobst

theorem zeroDefectD0_pos_of_exists_edge_eq_zero
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet] {x : G.edgeSet → Color}
    (hzero : ∃ e : G.edgeSet, x e = 0) :
    0 < zeroDefectD0 G x := by
  have hZ : 0 < zeroEdgeCount G x :=
    zeroEdgeCount_pos_of_exists_edge_eq_zero hzero
  unfold zeroDefectD0
  omega

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

theorem
    not_isD0LocalMinimumForMoveSupports_of_allowed_erases_zero_no_new_zero_side_budget_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet} {g : Color} {dI dC : Nat}
    (hCmem : C ∈ moveSupports)
    (hmove : IsAllowedD0OneStepMoveOn G C g x (cdlOneStepMoveOn G C g x))
    (herase : ∃ e ∈ C, x e = 0)
    (hnew : ∀ e ∈ C, x e ≠ g)
    (hI :
      zeroIncidentVertexCount G (cdlOneStepMoveOn G C g x) ≤
        zeroIncidentVertexCount G x + dI)
    (hC :
      zeroClusteringCount G (cdlOneStepMoveOn G C g x) ≤
        zeroClusteringCount G x + dC)
    (hbudget : 10 * dI + dC < 100) :
    ¬ IsD0LocalMinimumForMoveSupports G moveSupports x := by
  exact not_isD0LocalMinimumForMoveSupports_of_allowed_side_budget_descent
    hCmem hmove
    (zeroEdgeCount_cdlOneStepMoveOn_add_one_le_of_erases_zero_and_creates_no_zero
      herase hnew)
    hI hC hbudget

theorem not_isD0LocalMinimumForMoveSupports_of_allowed_erases_zero_no_new_zero_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet} {g : Color}
    (hCmem : C ∈ moveSupports)
    (hmove : IsAllowedD0OneStepMoveOn G C g x (cdlOneStepMoveOn G C g x))
    (herase : ∃ e ∈ C, x e = 0)
    (hnew : ∀ e ∈ C, x e ≠ g) :
    ¬ IsD0LocalMinimumForMoveSupports G moveSupports x := by
  exact
    not_isD0LocalMinimumForMoveSupports_of_allowed_erases_zero_no_new_zero_side_budget_descent
      (dI := 0) (dC := 0) hCmem hmove herase hnew
      (by
        exact Nat.le_trans
          (zeroIncidentVertexCount_cdlOneStepMoveOn_le_of_creates_no_zero hnew)
          (Nat.le_add_right _ _))
      (by
        exact Nat.le_trans
          (zeroClusteringCount_cdlOneStepMoveOn_le_of_creates_no_zero hnew)
          (Nat.le_add_right _ _))
      (by norm_num)

theorem exists_created_zero_of_isD0LocalMinimumForMoveSupports_of_allowed_erases_zero
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet} {g : Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hCmem : C ∈ moveSupports)
    (hmove : IsAllowedD0OneStepMoveOn G C g x (cdlOneStepMoveOn G C g x))
    (herase : ∃ e ∈ C, x e = 0) :
    ∃ e ∈ C, x e = g := by
  by_contra hnone
  have hnew : ∀ e ∈ C, x e ≠ g := by
    intro e heC hxg
    exact hnone ⟨e, heC, hxg⟩
  exact
    (not_isD0LocalMinimumForMoveSupports_of_allowed_erases_zero_no_new_zero_descent
      hCmem hmove herase hnew) hmin

theorem
    not_isD0LocalMinimumForMoveSupports_of_allowed_erases_incident_zero_no_new_zero_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet} {g : Color} {v : V}
    (hCmem : C ∈ moveSupports)
    (hmove : IsAllowedD0OneStepMoveOn G C g x (cdlOneStepMoveOn G C g x))
    (heraseAt : ∃ e ∈ C, e ∈ incidentEdgeFinset G v ∧ x e = 0)
    (hnew : ∀ e ∈ C, x e ≠ g) :
    ¬ IsD0LocalMinimumForMoveSupports G moveSupports x := by
  rcases heraseAt with ⟨e, heC, _heinc, hzero⟩
  exact
    not_isD0LocalMinimumForMoveSupports_of_allowed_erases_zero_no_new_zero_descent
      hCmem hmove ⟨e, heC, hzero⟩ hnew

theorem exists_created_zero_of_isD0LocalMinimumForMoveSupports_of_allowed_erases_incident_zero
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet} {g : Color} {v : V}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hCmem : C ∈ moveSupports)
    (hmove : IsAllowedD0OneStepMoveOn G C g x (cdlOneStepMoveOn G C g x))
    (heraseAt : ∃ e ∈ C, e ∈ incidentEdgeFinset G v ∧ x e = 0) :
    ∃ e ∈ C, x e = g := by
  by_contra hnone
  have hnew : ∀ e ∈ C, x e ≠ g := by
    intro e heC hxg
    exact hnone ⟨e, heC, hxg⟩
  exact
    (not_isD0LocalMinimumForMoveSupports_of_allowed_erases_incident_zero_no_new_zero_descent
      hCmem hmove heraseAt hnew) hmin

theorem support_card_ge_four_of_contains_zero_red_blue_purple
    {E : Type*} [DecidableEq E] {C : Finset E} {x : E → Color}
    (hzero : ∃ e ∈ C, x e = 0)
    (hred : ∃ e ∈ C, x e = red)
    (hblue : ∃ e ∈ C, x e = blue)
    (hpurple : ∃ e ∈ C, x e = purple) :
    4 ≤ C.card := by
  rcases hzero with ⟨e0, he0C, he0⟩
  rcases hred with ⟨er, herC, her⟩
  rcases hblue with ⟨eb, hebC, heb⟩
  rcases hpurple with ⟨ep, hepC, hep⟩
  have h0r : e0 ≠ er := by
    intro h
    have : red = 0 := by
      rw [← her, ← h, he0]
    exact red_ne_zero this
  have h0b : e0 ≠ eb := by
    intro h
    have : blue = 0 := by
      rw [← heb, ← h, he0]
    exact blue_ne_zero this
  have h0p : e0 ≠ ep := by
    intro h
    have : purple = 0 := by
      rw [← hep, ← h, he0]
    exact purple_ne_zero this
  have hrb : er ≠ eb := by
    intro h
    have : red = blue := by
      rw [← her, h, heb]
    exact red_ne_blue this
  have hrp : er ≠ ep := by
    intro h
    have : red = purple := by
      rw [← her, h, hep]
    exact red_ne_purple this
  have hbp : eb ≠ ep := by
    intro h
    have : blue = purple := by
      rw [← heb, h, hep]
    exact blue_ne_purple this
  have hsubset : ({e0, er, eb, ep} : Finset E) ⊆ C := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact he0C
    · exact herC
    · exact hebC
    · exact hepC
  have hcard : ({e0, er, eb, ep} : Finset E).card = 4 := by
    simp [h0r, h0b, h0p, hrb, hrp, hbp]
  have hle := Finset.card_le_card hsubset
  omega

theorem moveSupport_card_ge_four_of_d0LocalMinimum_basic_color_moves
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hCmem : C ∈ moveSupports)
    (hred :
      IsAllowedD0OneStepMoveOn G C red x (cdlOneStepMoveOn G C red x))
    (hblue :
      IsAllowedD0OneStepMoveOn G C blue x (cdlOneStepMoveOn G C blue x))
    (hpurple :
      IsAllowedD0OneStepMoveOn G C purple x (cdlOneStepMoveOn G C purple x))
    (herase : ∃ e ∈ C, x e = 0) :
    4 ≤ C.card := by
  exact support_card_ge_four_of_contains_zero_red_blue_purple
    herase
    (exists_created_zero_of_isD0LocalMinimumForMoveSupports_of_allowed_erases_zero
      hmin hCmem hred herase)
    (exists_created_zero_of_isD0LocalMinimumForMoveSupports_of_allowed_erases_zero
      hmin hCmem hblue herase)
    (exists_created_zero_of_isD0LocalMinimumForMoveSupports_of_allowed_erases_zero
      hmin hCmem hpurple herase)

theorem
    moveSupport_card_ge_four_of_d0LocalMinimum_basic_color_moves_erases_incident_zero
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet} {v : V}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hCmem : C ∈ moveSupports)
    (hred :
      IsAllowedD0OneStepMoveOn G C red x (cdlOneStepMoveOn G C red x))
    (hblue :
      IsAllowedD0OneStepMoveOn G C blue x (cdlOneStepMoveOn G C blue x))
    (hpurple :
      IsAllowedD0OneStepMoveOn G C purple x (cdlOneStepMoveOn G C purple x))
    (heraseAt : ∃ e ∈ C, e ∈ incidentEdgeFinset G v ∧ x e = 0) :
    4 ≤ C.card := by
  rcases heraseAt with ⟨e0, he0C, he0inc, he0zero⟩
  exact support_card_ge_four_of_contains_zero_red_blue_purple
    ⟨e0, he0C, he0zero⟩
    (exists_created_zero_of_isD0LocalMinimumForMoveSupports_of_allowed_erases_incident_zero
      hmin hCmem hred ⟨e0, he0C, he0inc, he0zero⟩)
    (exists_created_zero_of_isD0LocalMinimumForMoveSupports_of_allowed_erases_incident_zero
      hmin hCmem hblue ⟨e0, he0C, he0inc, he0zero⟩)
    (exists_created_zero_of_isD0LocalMinimumForMoveSupports_of_allowed_erases_incident_zero
      hmin hCmem hpurple ⟨e0, he0C, he0inc, he0zero⟩)

theorem not_isD0LocalMinimumForMoveSupports_of_basic_color_moves_small_support
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet}
    (hCmem : C ∈ moveSupports)
    (hred :
      IsAllowedD0OneStepMoveOn G C red x (cdlOneStepMoveOn G C red x))
    (hblue :
      IsAllowedD0OneStepMoveOn G C blue x (cdlOneStepMoveOn G C blue x))
    (hpurple :
      IsAllowedD0OneStepMoveOn G C purple x (cdlOneStepMoveOn G C purple x))
    (herase : ∃ e ∈ C, x e = 0)
    (hsmall : C.card ≤ 3) :
    ¬ IsD0LocalMinimumForMoveSupports G moveSupports x := by
  intro hmin
  have hfour : 4 ≤ C.card :=
    moveSupport_card_ge_four_of_d0LocalMinimum_basic_color_moves
      hmin hCmem hred hblue hpurple herase
  omega

theorem
    not_isD0LocalMinimumForMoveSupports_of_basic_color_moves_small_support_erases_incident_zero
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet} {v : V}
    (hCmem : C ∈ moveSupports)
    (hred :
      IsAllowedD0OneStepMoveOn G C red x (cdlOneStepMoveOn G C red x))
    (hblue :
      IsAllowedD0OneStepMoveOn G C blue x (cdlOneStepMoveOn G C blue x))
    (hpurple :
      IsAllowedD0OneStepMoveOn G C purple x (cdlOneStepMoveOn G C purple x))
    (heraseAt : ∃ e ∈ C, e ∈ incidentEdgeFinset G v ∧ x e = 0)
    (hsmall : C.card ≤ 3) :
    ¬ IsD0LocalMinimumForMoveSupports G moveSupports x := by
  intro hmin
  have hfour : 4 ≤ C.card :=
    moveSupport_card_ge_four_of_d0LocalMinimum_basic_color_moves_erases_incident_zero
      hmin hCmem hred hblue hpurple heraseAt
  omega

theorem exists_failed_basic_color_move_of_d0LocalMinimum_small_support
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hCmem : C ∈ moveSupports)
    (herase : ∃ e ∈ C, x e = 0)
    (hsmall : C.card ≤ 3) :
    ¬ IsAllowedD0OneStepMoveOn G C red x (cdlOneStepMoveOn G C red x) ∨
      ¬ IsAllowedD0OneStepMoveOn G C blue x (cdlOneStepMoveOn G C blue x) ∨
        ¬ IsAllowedD0OneStepMoveOn G C purple x
          (cdlOneStepMoveOn G C purple x) := by
  by_cases hred :
      IsAllowedD0OneStepMoveOn G C red x (cdlOneStepMoveOn G C red x)
  · by_cases hblue :
        IsAllowedD0OneStepMoveOn G C blue x (cdlOneStepMoveOn G C blue x)
    · by_cases hpurple :
          IsAllowedD0OneStepMoveOn G C purple x
            (cdlOneStepMoveOn G C purple x)
      · exact False.elim
          ((not_isD0LocalMinimumForMoveSupports_of_basic_color_moves_small_support
            hCmem hred hblue hpurple herase hsmall) hmin)
      · exact Or.inr (Or.inr hpurple)
    · exact Or.inr (Or.inl hblue)
  · exact Or.inl hred

theorem exists_failed_basic_color_move_of_d0LocalMinimum_small_support_erases_incident_zero
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet} {v : V}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hCmem : C ∈ moveSupports)
    (heraseAt : ∃ e ∈ C, e ∈ incidentEdgeFinset G v ∧ x e = 0)
    (hsmall : C.card ≤ 3) :
    ¬ IsAllowedD0OneStepMoveOn G C red x (cdlOneStepMoveOn G C red x) ∨
      ¬ IsAllowedD0OneStepMoveOn G C blue x (cdlOneStepMoveOn G C blue x) ∨
        ¬ IsAllowedD0OneStepMoveOn G C purple x
          (cdlOneStepMoveOn G C purple x) := by
  by_cases hred :
      IsAllowedD0OneStepMoveOn G C red x (cdlOneStepMoveOn G C red x)
  · by_cases hblue :
        IsAllowedD0OneStepMoveOn G C blue x (cdlOneStepMoveOn G C blue x)
    · by_cases hpurple :
          IsAllowedD0OneStepMoveOn G C purple x
            (cdlOneStepMoveOn G C purple x)
      · exact False.elim
          ((not_isD0LocalMinimumForMoveSupports_of_basic_color_moves_small_support_erases_incident_zero
            hCmem hred hblue hpurple heraseAt hsmall) hmin)
      · exact Or.inr (Or.inr hpurple)
    · exact Or.inr (Or.inl hblue)
  · exact Or.inl hred

theorem exists_forced_zero_basic_color_move_of_d0LocalMinimum_kirchhoffNeutral_small_support
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hCmem : C ∈ moveSupports)
    (hC : IsKirchhoffNeutralMoveSupport G C)
    (herase : ∃ e ∈ C, x e = 0)
    (hsmall : C.card ≤ 3) :
    (∃ v : V, ∀ e ∈ incidentEdgeFinset G v,
      if e ∈ C then x e = red else x e = 0) ∨
      (∃ v : V, ∀ e ∈ incidentEdgeFinset G v,
        if e ∈ C then x e = blue else x e = 0) ∨
        (∃ v : V, ∀ e ∈ incidentEdgeFinset G v,
          if e ∈ C then x e = purple else x e = 0) := by
  rcases
    exists_failed_basic_color_move_of_d0LocalMinimum_small_support
      hmin hCmem herase hsmall with hred | hblue | hpurple
  · exact Or.inl
      ((not_isAllowedD0OneStepMoveOn_iff_exists_vertex_forced_zero_of_kirchhoffNeutral
        red_ne_zero hmin.source_flow hC).mp hred)
  · exact Or.inr (Or.inl
      ((not_isAllowedD0OneStepMoveOn_iff_exists_vertex_forced_zero_of_kirchhoffNeutral
        blue_ne_zero hmin.source_flow hC).mp hblue))
  · exact Or.inr (Or.inr
      ((not_isAllowedD0OneStepMoveOn_iff_exists_vertex_forced_zero_of_kirchhoffNeutral
        purple_ne_zero hmin.source_flow hC).mp hpurple))

theorem
    exists_forced_zero_basic_color_move_of_d0LocalMinimum_kirchhoffNeutral_small_support_erases_incident_zero
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet} {v : V}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hCmem : C ∈ moveSupports)
    (hC : IsKirchhoffNeutralMoveSupport G C)
    (heraseAt : ∃ e ∈ C, e ∈ incidentEdgeFinset G v ∧ x e = 0)
    (hsmall : C.card ≤ 3) :
    (∃ v : V, ∀ e ∈ incidentEdgeFinset G v,
      if e ∈ C then x e = red else x e = 0) ∨
      (∃ v : V, ∀ e ∈ incidentEdgeFinset G v,
        if e ∈ C then x e = blue else x e = 0) ∨
        (∃ v : V, ∀ e ∈ incidentEdgeFinset G v,
          if e ∈ C then x e = purple else x e = 0) := by
  rcases
    exists_failed_basic_color_move_of_d0LocalMinimum_small_support_erases_incident_zero
      hmin hCmem heraseAt hsmall with hred | hblue | hpurple
  · exact Or.inl
      ((not_isAllowedD0OneStepMoveOn_iff_exists_vertex_forced_zero_of_kirchhoffNeutral
        red_ne_zero hmin.source_flow hC).mp hred)
  · exact Or.inr (Or.inl
      ((not_isAllowedD0OneStepMoveOn_iff_exists_vertex_forced_zero_of_kirchhoffNeutral
        blue_ne_zero hmin.source_flow hC).mp hblue))
  · exact Or.inr (Or.inr
      ((not_isAllowedD0OneStepMoveOn_iff_exists_vertex_forced_zero_of_kirchhoffNeutral
        purple_ne_zero hmin.source_flow hC).mp hpurple))

theorem
    exists_source_support_witness_for_basic_color_obstruction_of_d0LocalMinimum_kirchhoffNeutral_small_support
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hCmem : C ∈ moveSupports)
    (hC : IsKirchhoffNeutralMoveSupport G C)
    (herase : ∃ e ∈ C, x e = 0)
    (hsmall : C.card ≤ 3) :
    (∃ v : V, ∃ e : G.edgeSet,
      e ∈ incidentEdgeFinset G v ∧ e ∈ C ∧ x e = red ∧
        ∀ e' ∈ incidentEdgeFinset G v,
          if e' ∈ C then x e' = red else x e' = 0) ∨
      (∃ v : V, ∃ e : G.edgeSet,
        e ∈ incidentEdgeFinset G v ∧ e ∈ C ∧ x e = blue ∧
          ∀ e' ∈ incidentEdgeFinset G v,
            if e' ∈ C then x e' = blue else x e' = 0) ∨
        (∃ v : V, ∃ e : G.edgeSet,
          e ∈ incidentEdgeFinset G v ∧ e ∈ C ∧ x e = purple ∧
            ∀ e' ∈ incidentEdgeFinset G v,
              if e' ∈ C then x e' = purple else x e' = 0) := by
  rcases
    exists_forced_zero_basic_color_move_of_d0LocalMinimum_kirchhoffNeutral_small_support
      hmin hCmem hC herase hsmall with hred | hblue | hpurple
  · rcases hred with ⟨v, hforced⟩
    rcases
      exists_support_edge_color_of_isCDLGoodAtVertex_and_forced_zero_move
        (hmin.source_good v) hforced with ⟨e, heinc, heC, hx⟩
    exact Or.inl ⟨v, e, heinc, heC, hx, hforced⟩
  · rcases hblue with ⟨v, hforced⟩
    rcases
      exists_support_edge_color_of_isCDLGoodAtVertex_and_forced_zero_move
        (hmin.source_good v) hforced with ⟨e, heinc, heC, hx⟩
    exact Or.inr (Or.inl ⟨v, e, heinc, heC, hx, hforced⟩)
  · rcases hpurple with ⟨v, hforced⟩
    rcases
      exists_support_edge_color_of_isCDLGoodAtVertex_and_forced_zero_move
        (hmin.source_good v) hforced with ⟨e, heinc, heC, hx⟩
    exact Or.inr (Or.inr ⟨v, e, heinc, heC, hx, hforced⟩)

theorem
    exists_cubic_two_support_edges_for_basic_color_obstruction_of_d0LocalMinimum_kirchhoffNeutral_small_support
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hCmem : C ∈ moveSupports)
    (hC : IsKirchhoffNeutralMoveSupport G C)
    (herase : ∃ e ∈ C, x e = 0)
    (hsmall : C.card ≤ 3) :
    (∃ v : V,
      ((incidentEdgeFinset G v).filter fun e => e ∈ C).card = 2 ∧
        ∀ e ∈ incidentEdgeFinset G v,
          if e ∈ C then x e = red else x e = 0) ∨
      (∃ v : V,
        ((incidentEdgeFinset G v).filter fun e => e ∈ C).card = 2 ∧
          ∀ e ∈ incidentEdgeFinset G v,
            if e ∈ C then x e = blue else x e = 0) ∨
        (∃ v : V,
          ((incidentEdgeFinset G v).filter fun e => e ∈ C).card = 2 ∧
            ∀ e ∈ incidentEdgeFinset G v,
              if e ∈ C then x e = purple else x e = 0) := by
  rcases
    exists_forced_zero_basic_color_move_of_d0LocalMinimum_kirchhoffNeutral_small_support
      hmin hCmem hC herase hsmall with hred | hblue | hpurple
  · rcases hred with ⟨v, hforced⟩
    exact Or.inl ⟨v,
      incident_support_card_eq_two_of_isCDLGoodAtVertex_and_forced_zero_move
        (hcard v) hC (hmin.source_good v) hforced,
      hforced⟩
  · rcases hblue with ⟨v, hforced⟩
    exact Or.inr (Or.inl ⟨v,
      incident_support_card_eq_two_of_isCDLGoodAtVertex_and_forced_zero_move
        (hcard v) hC (hmin.source_good v) hforced,
      hforced⟩)
  · rcases hpurple with ⟨v, hforced⟩
    exact Or.inr (Or.inr ⟨v,
      incident_support_card_eq_two_of_isCDLGoodAtVertex_and_forced_zero_move
        (hcard v) hC (hmin.source_good v) hforced,
      hforced⟩)

theorem
    exists_cubic_outside_zero_edge_for_basic_color_obstruction_of_d0LocalMinimum_kirchhoffNeutral_small_support
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hCmem : C ∈ moveSupports)
    (hC : IsKirchhoffNeutralMoveSupport G C)
    (herase : ∃ e ∈ C, x e = 0)
    (hsmall : C.card ≤ 3) :
    (∃ v : V, ∃ e : G.edgeSet,
      e ∈ incidentEdgeFinset G v ∧ e ∉ C ∧ x e = 0 ∧
        ∀ e' ∈ incidentEdgeFinset G v,
          if e' ∈ C then x e' = red else x e' = 0) ∨
      (∃ v : V, ∃ e : G.edgeSet,
        e ∈ incidentEdgeFinset G v ∧ e ∉ C ∧ x e = 0 ∧
          ∀ e' ∈ incidentEdgeFinset G v,
            if e' ∈ C then x e' = blue else x e' = 0) ∨
        (∃ v : V, ∃ e : G.edgeSet,
          e ∈ incidentEdgeFinset G v ∧ e ∉ C ∧ x e = 0 ∧
            ∀ e' ∈ incidentEdgeFinset G v,
              if e' ∈ C then x e' = purple else x e' = 0) := by
  rcases
    exists_cubic_two_support_edges_for_basic_color_obstruction_of_d0LocalMinimum_kirchhoffNeutral_small_support
      hcard hmin hCmem hC herase hsmall with hred | hblue | hpurple
  · rcases hred with ⟨v, htwo, hforced⟩
    rcases
      exists_outside_zero_incident_edge_of_cubic_two_support_forced_zero_move
        (hcard v) htwo hforced with ⟨e, heinc, heC, hx⟩
    exact Or.inl ⟨v, e, heinc, heC, hx, hforced⟩
  · rcases hblue with ⟨v, htwo, hforced⟩
    rcases
      exists_outside_zero_incident_edge_of_cubic_two_support_forced_zero_move
        (hcard v) htwo hforced with ⟨e, heinc, heC, hx⟩
    exact Or.inr (Or.inl ⟨v, e, heinc, heC, hx, hforced⟩)
  · rcases hpurple with ⟨v, htwo, hforced⟩
    rcases
      exists_outside_zero_incident_edge_of_cubic_two_support_forced_zero_move
        (hcard v) htwo hforced with ⟨e, heinc, heC, hx⟩
    exact Or.inr (Or.inr ⟨v, e, heinc, heC, hx, hforced⟩)

theorem
    exists_cubic_zeroIncidentEdgeCount_eq_one_for_basic_color_obstruction_of_d0LocalMinimum_kirchhoffNeutral_small_support
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hCmem : C ∈ moveSupports)
    (hC : IsKirchhoffNeutralMoveSupport G C)
    (herase : ∃ e ∈ C, x e = 0)
    (hsmall : C.card ≤ 3) :
    (∃ v : V, zeroIncidentEdgeCount G x v = 1 ∧
      ∀ e ∈ incidentEdgeFinset G v,
        if e ∈ C then x e = red else x e = 0) ∨
      (∃ v : V, zeroIncidentEdgeCount G x v = 1 ∧
        ∀ e ∈ incidentEdgeFinset G v,
          if e ∈ C then x e = blue else x e = 0) ∨
        (∃ v : V, zeroIncidentEdgeCount G x v = 1 ∧
          ∀ e ∈ incidentEdgeFinset G v,
            if e ∈ C then x e = purple else x e = 0) := by
  rcases
    exists_cubic_two_support_edges_for_basic_color_obstruction_of_d0LocalMinimum_kirchhoffNeutral_small_support
      hcard hmin hCmem hC herase hsmall with hred | hblue | hpurple
  · rcases hred with ⟨v, htwo, hforced⟩
    exact Or.inl ⟨v,
      zeroIncidentEdgeCount_eq_one_of_cubic_two_support_forced_zero_move
        red_ne_zero (hcard v) htwo hforced,
      hforced⟩
  · rcases hblue with ⟨v, htwo, hforced⟩
    exact Or.inr (Or.inl ⟨v,
      zeroIncidentEdgeCount_eq_one_of_cubic_two_support_forced_zero_move
        blue_ne_zero (hcard v) htwo hforced,
      hforced⟩)
  · rcases hpurple with ⟨v, htwo, hforced⟩
    exact Or.inr (Or.inr ⟨v,
      zeroIncidentEdgeCount_eq_one_of_cubic_two_support_forced_zero_move
        purple_ne_zero (hcard v) htwo hforced,
      hforced⟩)

theorem
    exists_cubic_zeroClusteringLocalTerm_eq_zero_for_basic_color_obstruction_of_d0LocalMinimum_kirchhoffNeutral_small_support
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hCmem : C ∈ moveSupports)
    (hC : IsKirchhoffNeutralMoveSupport G C)
    (herase : ∃ e ∈ C, x e = 0)
    (hsmall : C.card ≤ 3) :
    (∃ v : V, zeroIncidentEdgeCount G x v = 1 ∧
      zeroIncidentEdgeCount G x v - 1 = 0 ∧
      ∀ e ∈ incidentEdgeFinset G v,
        if e ∈ C then x e = red else x e = 0) ∨
      (∃ v : V, zeroIncidentEdgeCount G x v = 1 ∧
        zeroIncidentEdgeCount G x v - 1 = 0 ∧
        ∀ e ∈ incidentEdgeFinset G v,
          if e ∈ C then x e = blue else x e = 0) ∨
        (∃ v : V, zeroIncidentEdgeCount G x v = 1 ∧
          zeroIncidentEdgeCount G x v - 1 = 0 ∧
          ∀ e ∈ incidentEdgeFinset G v,
            if e ∈ C then x e = purple else x e = 0) := by
  rcases
    exists_cubic_zeroIncidentEdgeCount_eq_one_for_basic_color_obstruction_of_d0LocalMinimum_kirchhoffNeutral_small_support
      hcard hmin hCmem hC herase hsmall with hred | hblue | hpurple
  · rcases hred with ⟨v, hcount, hforced⟩
    exact Or.inl ⟨v, hcount,
      zeroClusteringLocalTerm_eq_zero_of_zeroIncidentEdgeCount_eq_one hcount,
      hforced⟩
  · rcases hblue with ⟨v, hcount, hforced⟩
    exact Or.inr (Or.inl ⟨v, hcount,
      zeroClusteringLocalTerm_eq_zero_of_zeroIncidentEdgeCount_eq_one hcount,
      hforced⟩)
  · rcases hpurple with ⟨v, hcount, hforced⟩
    exact Or.inr (Or.inr ⟨v, hcount,
      zeroClusteringLocalTerm_eq_zero_of_zeroIncidentEdgeCount_eq_one hcount,
      hforced⟩)

theorem
    zeroIncidentVertexCount_pos_of_basic_color_obstruction_of_d0LocalMinimum_kirchhoffNeutral_small_support
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hCmem : C ∈ moveSupports)
    (hC : IsKirchhoffNeutralMoveSupport G C)
    (herase : ∃ e ∈ C, x e = 0)
    (hsmall : C.card ≤ 3) :
    0 < zeroIncidentVertexCount G x := by
  rcases
    exists_cubic_zeroIncidentEdgeCount_eq_one_for_basic_color_obstruction_of_d0LocalMinimum_kirchhoffNeutral_small_support
      hcard hmin hCmem hC herase hsmall with hred | hblue | hpurple
  · rcases hred with ⟨v, hcount, _hforced⟩
    exact zeroIncidentVertexCount_pos_of_exists_zeroIncidentEdgeCount_eq_one ⟨v, hcount⟩
  · rcases hblue with ⟨v, hcount, _hforced⟩
    exact zeroIncidentVertexCount_pos_of_exists_zeroIncidentEdgeCount_eq_one ⟨v, hcount⟩
  · rcases hpurple with ⟨v, hcount, _hforced⟩
    exact zeroIncidentVertexCount_pos_of_exists_zeroIncidentEdgeCount_eq_one ⟨v, hcount⟩

theorem
    exists_hasCubicD0BasicColorObstructionAt_for_basic_color_obstruction_of_d0LocalMinimum_kirchhoffNeutral_small_support
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hCmem : C ∈ moveSupports)
    (hC : IsKirchhoffNeutralMoveSupport G C)
    (herase : ∃ e ∈ C, x e = 0)
    (hsmall : C.card ≤ 3) :
    (∃ v : V, HasCubicD0BasicColorObstructionAt G x C v red) ∨
      (∃ v : V, HasCubicD0BasicColorObstructionAt G x C v blue) ∨
        (∃ v : V, HasCubicD0BasicColorObstructionAt G x C v purple) := by
  rcases
    exists_cubic_two_support_edges_for_basic_color_obstruction_of_d0LocalMinimum_kirchhoffNeutral_small_support
      hcard hmin hCmem hC herase hsmall with hred | hblue | hpurple
  · rcases hred with ⟨v, htwo, hforced⟩
    exact Or.inl ⟨v,
      hasCubicD0BasicColorObstructionAt_of_cubic_two_support_forced_zero_move
        red_ne_zero (hcard v) htwo hforced⟩
  · rcases hblue with ⟨v, htwo, hforced⟩
    exact Or.inr (Or.inl ⟨v,
      hasCubicD0BasicColorObstructionAt_of_cubic_two_support_forced_zero_move
        blue_ne_zero (hcard v) htwo hforced⟩)
  · rcases hpurple with ⟨v, htwo, hforced⟩
    exact Or.inr (Or.inr ⟨v,
      hasCubicD0BasicColorObstructionAt_of_cubic_two_support_forced_zero_move
        purple_ne_zero (hcard v) htwo hforced⟩)

theorem
    zeroDefectD0_pos_of_basic_color_obstruction_of_d0LocalMinimum_kirchhoffNeutral_small_support
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hCmem : C ∈ moveSupports)
    (hC : IsKirchhoffNeutralMoveSupport G C)
    (herase : ∃ e ∈ C, x e = 0)
    (hsmall : C.card ≤ 3) :
    0 < zeroDefectD0 G x :=
  zeroDefectD0_pos_of_exists_hasCubicD0BasicColorObstructionAt
    (exists_hasCubicD0BasicColorObstructionAt_for_basic_color_obstruction_of_d0LocalMinimum_kirchhoffNeutral_small_support
      hcard hmin hCmem hC herase hsmall)

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

theorem
    not_isD0LocalMinimumForMoveSupports_of_isKempeCycle_erases_zero_no_new_zero_side_budget_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet} {g α β : Color} {dI dC : Nat}
    (hCmem : C ∈ moveSupports) (hg : g ≠ 0)
    (hC : IsKempeCycle (incidentEdgeFinset G) x C α β)
    (hgood :
      ∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
        if e ∈ C then x e ≠ g else x e ≠ 0)
    (herase : ∃ e ∈ C, x e = 0)
    (hnew : ∀ e ∈ C, x e ≠ g)
    (hI :
      zeroIncidentVertexCount G (cdlOneStepMoveOn G C g x) ≤
        zeroIncidentVertexCount G x + dI)
    (hCluster :
      zeroClusteringCount G (cdlOneStepMoveOn G C g x) ≤
        zeroClusteringCount G x + dC)
    (hbudget : 10 * dI + dC < 100) :
    ¬ IsD0LocalMinimumForMoveSupports G moveSupports x := by
  intro hmin
  exact
    (not_isD0LocalMinimumForMoveSupports_of_allowed_erases_zero_no_new_zero_side_budget_descent
      hCmem
      (isAllowedD0OneStepMoveOn_of_isKempeCycle_and_vertex_witnesses
        hg hmin.source_flow hC hgood)
      herase hnew hI hCluster hbudget) hmin

theorem exists_created_zero_of_isD0LocalMinimumForMoveSupports_of_isKempeCycle_erases_zero
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet} {g α β : Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hCmem : C ∈ moveSupports) (hg : g ≠ 0)
    (hC : IsKempeCycle (incidentEdgeFinset G) x C α β)
    (hgood :
      ∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
        if e ∈ C then x e ≠ g else x e ≠ 0)
    (herase : ∃ e ∈ C, x e = 0) :
    ∃ e ∈ C, x e = g :=
  exists_created_zero_of_isD0LocalMinimumForMoveSupports_of_allowed_erases_zero
    hmin hCmem
    (isAllowedD0OneStepMoveOn_of_isKempeCycle_and_vertex_witnesses
      hg hmin.source_flow hC hgood)
    herase

theorem
    exists_created_zero_of_isD0LocalMinimumForMoveSupports_of_isKempeCycle_erases_incident_zero
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet} {g α β : Color} {v : V}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hCmem : C ∈ moveSupports) (hg : g ≠ 0)
    (hC : IsKempeCycle (incidentEdgeFinset G) x C α β)
    (hgood :
      ∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
        if e ∈ C then x e ≠ g else x e ≠ 0)
    (heraseAt : ∃ e ∈ C, e ∈ incidentEdgeFinset G v ∧ x e = 0) :
    ∃ e ∈ C, x e = g :=
  exists_created_zero_of_isD0LocalMinimumForMoveSupports_of_allowed_erases_incident_zero
    hmin hCmem
    (isAllowedD0OneStepMoveOn_of_isKempeCycle_and_vertex_witnesses
      hg hmin.source_flow hC hgood)
    heraseAt

theorem not_isD0LocalMinimumForMoveSupports_of_isKempeCycle_basic_color_moves_small_support
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet} {α β : Color}
    (hCmem : C ∈ moveSupports)
    (hC : IsKempeCycle (incidentEdgeFinset G) x C α β)
    (hredgood :
      ∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
        if e ∈ C then x e ≠ red else x e ≠ 0)
    (hbluegood :
      ∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
        if e ∈ C then x e ≠ blue else x e ≠ 0)
    (hpurplegood :
      ∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
        if e ∈ C then x e ≠ purple else x e ≠ 0)
    (herase : ∃ e ∈ C, x e = 0)
    (hsmall : C.card ≤ 3) :
    ¬ IsD0LocalMinimumForMoveSupports G moveSupports x := by
  intro hmin
  exact
    (not_isD0LocalMinimumForMoveSupports_of_basic_color_moves_small_support
      hCmem
      (isAllowedD0OneStepMoveOn_of_isKempeCycle_and_vertex_witnesses
        red_ne_zero hmin.source_flow hC hredgood)
      (isAllowedD0OneStepMoveOn_of_isKempeCycle_and_vertex_witnesses
        blue_ne_zero hmin.source_flow hC hbluegood)
      (isAllowedD0OneStepMoveOn_of_isKempeCycle_and_vertex_witnesses
        purple_ne_zero hmin.source_flow hC hpurplegood)
      herase hsmall) hmin

theorem
    not_isD0LocalMinimumForMoveSupports_of_isKempeCycle_basic_color_moves_small_support_erases_incident_zero
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet} {α β : Color} {v : V}
    (hCmem : C ∈ moveSupports)
    (hC : IsKempeCycle (incidentEdgeFinset G) x C α β)
    (hredgood :
      ∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
        if e ∈ C then x e ≠ red else x e ≠ 0)
    (hbluegood :
      ∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
        if e ∈ C then x e ≠ blue else x e ≠ 0)
    (hpurplegood :
      ∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
        if e ∈ C then x e ≠ purple else x e ≠ 0)
    (heraseAt : ∃ e ∈ C, e ∈ incidentEdgeFinset G v ∧ x e = 0)
    (hsmall : C.card ≤ 3) :
    ¬ IsD0LocalMinimumForMoveSupports G moveSupports x := by
  intro hmin
  exact
    (not_isD0LocalMinimumForMoveSupports_of_basic_color_moves_small_support_erases_incident_zero
      hCmem
      (isAllowedD0OneStepMoveOn_of_isKempeCycle_and_vertex_witnesses
        red_ne_zero hmin.source_flow hC hredgood)
      (isAllowedD0OneStepMoveOn_of_isKempeCycle_and_vertex_witnesses
        blue_ne_zero hmin.source_flow hC hbluegood)
      (isAllowedD0OneStepMoveOn_of_isKempeCycle_and_vertex_witnesses
        purple_ne_zero hmin.source_flow hC hpurplegood)
      heraseAt hsmall) hmin

theorem exists_failed_basic_color_witness_of_d0LocalMinimum_isKempeCycle_small_support
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet} {α β : Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hCmem : C ∈ moveSupports)
    (hC : IsKempeCycle (incidentEdgeFinset G) x C α β)
    (herase : ∃ e ∈ C, x e = 0)
    (hsmall : C.card ≤ 3) :
    ¬ (∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
        if e ∈ C then x e ≠ red else x e ≠ 0) ∨
      ¬ (∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
          if e ∈ C then x e ≠ blue else x e ≠ 0) ∨
        ¬ (∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
            if e ∈ C then x e ≠ purple else x e ≠ 0) := by
  by_cases hredgood :
      ∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
        if e ∈ C then x e ≠ red else x e ≠ 0
  · by_cases hbluegood :
        ∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
          if e ∈ C then x e ≠ blue else x e ≠ 0
    · by_cases hpurplegood :
          ∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
            if e ∈ C then x e ≠ purple else x e ≠ 0
      · exact False.elim
          ((not_isD0LocalMinimumForMoveSupports_of_isKempeCycle_basic_color_moves_small_support
            hCmem hC hredgood hbluegood hpurplegood herase hsmall) hmin)
      · exact Or.inr (Or.inr hpurplegood)
    · exact Or.inr (Or.inl hbluegood)
  · exact Or.inl hredgood

theorem
    exists_failed_basic_color_witness_of_d0LocalMinimum_isKempeCycle_small_support_erases_incident_zero
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet} {α β : Color} {v : V}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hCmem : C ∈ moveSupports)
    (hC : IsKempeCycle (incidentEdgeFinset G) x C α β)
    (heraseAt : ∃ e ∈ C, e ∈ incidentEdgeFinset G v ∧ x e = 0)
    (hsmall : C.card ≤ 3) :
    ¬ (∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
        if e ∈ C then x e ≠ red else x e ≠ 0) ∨
      ¬ (∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
          if e ∈ C then x e ≠ blue else x e ≠ 0) ∨
        ¬ (∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
            if e ∈ C then x e ≠ purple else x e ≠ 0) := by
  by_cases hredgood :
      ∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
        if e ∈ C then x e ≠ red else x e ≠ 0
  · by_cases hbluegood :
        ∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
          if e ∈ C then x e ≠ blue else x e ≠ 0
    · by_cases hpurplegood :
          ∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
            if e ∈ C then x e ≠ purple else x e ≠ 0
      · exact False.elim
          ((not_isD0LocalMinimumForMoveSupports_of_isKempeCycle_basic_color_moves_small_support_erases_incident_zero
            hCmem hC hredgood hbluegood hpurplegood heraseAt hsmall) hmin)
      · exact Or.inr (Or.inr hpurplegood)
    · exact Or.inr (Or.inl hbluegood)
  · exact Or.inl hredgood

theorem exists_forced_zero_basic_color_move_of_d0LocalMinimum_isKempeCycle_small_support
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet} {α β : Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hCmem : C ∈ moveSupports)
    (hC : IsKempeCycle (incidentEdgeFinset G) x C α β)
    (herase : ∃ e ∈ C, x e = 0)
    (hsmall : C.card ≤ 3) :
    (∃ v : V, ∀ e ∈ incidentEdgeFinset G v,
      if e ∈ C then x e = red else x e = 0) ∨
      (∃ v : V, ∀ e ∈ incidentEdgeFinset G v,
        if e ∈ C then x e = blue else x e = 0) ∨
        (∃ v : V, ∀ e ∈ incidentEdgeFinset G v,
          if e ∈ C then x e = purple else x e = 0) :=
  exists_forced_zero_basic_color_move_of_d0LocalMinimum_kirchhoffNeutral_small_support
    hmin hCmem (isKirchhoffNeutralMoveSupport_of_isKempeCycle hC) herase hsmall

theorem
    exists_forced_zero_basic_color_move_of_d0LocalMinimum_isKempeCycle_small_support_erases_incident_zero
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet} {α β : Color} {v : V}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hCmem : C ∈ moveSupports)
    (hC : IsKempeCycle (incidentEdgeFinset G) x C α β)
    (heraseAt : ∃ e ∈ C, e ∈ incidentEdgeFinset G v ∧ x e = 0)
    (hsmall : C.card ≤ 3) :
    (∃ v : V, ∀ e ∈ incidentEdgeFinset G v,
      if e ∈ C then x e = red else x e = 0) ∨
      (∃ v : V, ∀ e ∈ incidentEdgeFinset G v,
        if e ∈ C then x e = blue else x e = 0) ∨
        (∃ v : V, ∀ e ∈ incidentEdgeFinset G v,
          if e ∈ C then x e = purple else x e = 0) :=
  exists_forced_zero_basic_color_move_of_d0LocalMinimum_kirchhoffNeutral_small_support_erases_incident_zero
    hmin hCmem (isKirchhoffNeutralMoveSupport_of_isKempeCycle hC) heraseAt hsmall

theorem
    exists_source_support_witness_for_basic_color_obstruction_of_d0LocalMinimum_isKempeCycle_small_support
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet} {α β : Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hCmem : C ∈ moveSupports)
    (hC : IsKempeCycle (incidentEdgeFinset G) x C α β)
    (herase : ∃ e ∈ C, x e = 0)
    (hsmall : C.card ≤ 3) :
    (∃ v : V, ∃ e : G.edgeSet,
      e ∈ incidentEdgeFinset G v ∧ e ∈ C ∧ x e = red ∧
        ∀ e' ∈ incidentEdgeFinset G v,
          if e' ∈ C then x e' = red else x e' = 0) ∨
      (∃ v : V, ∃ e : G.edgeSet,
        e ∈ incidentEdgeFinset G v ∧ e ∈ C ∧ x e = blue ∧
          ∀ e' ∈ incidentEdgeFinset G v,
            if e' ∈ C then x e' = blue else x e' = 0) ∨
        (∃ v : V, ∃ e : G.edgeSet,
          e ∈ incidentEdgeFinset G v ∧ e ∈ C ∧ x e = purple ∧
            ∀ e' ∈ incidentEdgeFinset G v,
              if e' ∈ C then x e' = purple else x e' = 0) :=
  exists_source_support_witness_for_basic_color_obstruction_of_d0LocalMinimum_kirchhoffNeutral_small_support
    hmin hCmem (isKirchhoffNeutralMoveSupport_of_isKempeCycle hC) herase hsmall

theorem
    exists_cubic_two_support_edges_for_basic_color_obstruction_of_d0LocalMinimum_isKempeCycle_small_support
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet} {α β : Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hCmem : C ∈ moveSupports)
    (hC : IsKempeCycle (incidentEdgeFinset G) x C α β)
    (herase : ∃ e ∈ C, x e = 0)
    (hsmall : C.card ≤ 3) :
    (∃ v : V,
      ((incidentEdgeFinset G v).filter fun e => e ∈ C).card = 2 ∧
        ∀ e ∈ incidentEdgeFinset G v,
          if e ∈ C then x e = red else x e = 0) ∨
      (∃ v : V,
        ((incidentEdgeFinset G v).filter fun e => e ∈ C).card = 2 ∧
          ∀ e ∈ incidentEdgeFinset G v,
            if e ∈ C then x e = blue else x e = 0) ∨
        (∃ v : V,
          ((incidentEdgeFinset G v).filter fun e => e ∈ C).card = 2 ∧
            ∀ e ∈ incidentEdgeFinset G v,
              if e ∈ C then x e = purple else x e = 0) :=
  exists_cubic_two_support_edges_for_basic_color_obstruction_of_d0LocalMinimum_kirchhoffNeutral_small_support
    hcard hmin hCmem (isKirchhoffNeutralMoveSupport_of_isKempeCycle hC) herase hsmall

theorem
    exists_cubic_outside_zero_edge_for_basic_color_obstruction_of_d0LocalMinimum_isKempeCycle_small_support
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet} {α β : Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hCmem : C ∈ moveSupports)
    (hC : IsKempeCycle (incidentEdgeFinset G) x C α β)
    (herase : ∃ e ∈ C, x e = 0)
    (hsmall : C.card ≤ 3) :
    (∃ v : V, ∃ e : G.edgeSet,
      e ∈ incidentEdgeFinset G v ∧ e ∉ C ∧ x e = 0 ∧
        ∀ e' ∈ incidentEdgeFinset G v,
          if e' ∈ C then x e' = red else x e' = 0) ∨
      (∃ v : V, ∃ e : G.edgeSet,
        e ∈ incidentEdgeFinset G v ∧ e ∉ C ∧ x e = 0 ∧
          ∀ e' ∈ incidentEdgeFinset G v,
            if e' ∈ C then x e' = blue else x e' = 0) ∨
        (∃ v : V, ∃ e : G.edgeSet,
          e ∈ incidentEdgeFinset G v ∧ e ∉ C ∧ x e = 0 ∧
            ∀ e' ∈ incidentEdgeFinset G v,
              if e' ∈ C then x e' = purple else x e' = 0) :=
  exists_cubic_outside_zero_edge_for_basic_color_obstruction_of_d0LocalMinimum_kirchhoffNeutral_small_support
    hcard hmin hCmem (isKirchhoffNeutralMoveSupport_of_isKempeCycle hC) herase hsmall

theorem
    exists_cubic_zeroIncidentEdgeCount_eq_one_for_basic_color_obstruction_of_d0LocalMinimum_isKempeCycle_small_support
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet} {α β : Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hCmem : C ∈ moveSupports)
    (hC : IsKempeCycle (incidentEdgeFinset G) x C α β)
    (herase : ∃ e ∈ C, x e = 0)
    (hsmall : C.card ≤ 3) :
    (∃ v : V, zeroIncidentEdgeCount G x v = 1 ∧
      ∀ e ∈ incidentEdgeFinset G v,
        if e ∈ C then x e = red else x e = 0) ∨
      (∃ v : V, zeroIncidentEdgeCount G x v = 1 ∧
        ∀ e ∈ incidentEdgeFinset G v,
          if e ∈ C then x e = blue else x e = 0) ∨
        (∃ v : V, zeroIncidentEdgeCount G x v = 1 ∧
          ∀ e ∈ incidentEdgeFinset G v,
            if e ∈ C then x e = purple else x e = 0) :=
  exists_cubic_zeroIncidentEdgeCount_eq_one_for_basic_color_obstruction_of_d0LocalMinimum_kirchhoffNeutral_small_support
    hcard hmin hCmem (isKirchhoffNeutralMoveSupport_of_isKempeCycle hC) herase hsmall

theorem
    exists_cubic_zeroClusteringLocalTerm_eq_zero_for_basic_color_obstruction_of_d0LocalMinimum_isKempeCycle_small_support
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet} {α β : Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hCmem : C ∈ moveSupports)
    (hC : IsKempeCycle (incidentEdgeFinset G) x C α β)
    (herase : ∃ e ∈ C, x e = 0)
    (hsmall : C.card ≤ 3) :
    (∃ v : V, zeroIncidentEdgeCount G x v = 1 ∧
      zeroIncidentEdgeCount G x v - 1 = 0 ∧
      ∀ e ∈ incidentEdgeFinset G v,
        if e ∈ C then x e = red else x e = 0) ∨
      (∃ v : V, zeroIncidentEdgeCount G x v = 1 ∧
        zeroIncidentEdgeCount G x v - 1 = 0 ∧
        ∀ e ∈ incidentEdgeFinset G v,
          if e ∈ C then x e = blue else x e = 0) ∨
        (∃ v : V, zeroIncidentEdgeCount G x v = 1 ∧
          zeroIncidentEdgeCount G x v - 1 = 0 ∧
          ∀ e ∈ incidentEdgeFinset G v,
            if e ∈ C then x e = purple else x e = 0) :=
  exists_cubic_zeroClusteringLocalTerm_eq_zero_for_basic_color_obstruction_of_d0LocalMinimum_kirchhoffNeutral_small_support
    hcard hmin hCmem (isKirchhoffNeutralMoveSupport_of_isKempeCycle hC) herase hsmall

theorem
    zeroIncidentVertexCount_pos_of_basic_color_obstruction_of_d0LocalMinimum_isKempeCycle_small_support
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet} {α β : Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hCmem : C ∈ moveSupports)
    (hC : IsKempeCycle (incidentEdgeFinset G) x C α β)
    (herase : ∃ e ∈ C, x e = 0)
    (hsmall : C.card ≤ 3) :
    0 < zeroIncidentVertexCount G x :=
  zeroIncidentVertexCount_pos_of_basic_color_obstruction_of_d0LocalMinimum_kirchhoffNeutral_small_support
    hcard hmin hCmem (isKirchhoffNeutralMoveSupport_of_isKempeCycle hC) herase hsmall

theorem
    exists_hasCubicD0BasicColorObstructionAt_for_basic_color_obstruction_of_d0LocalMinimum_isKempeCycle_small_support
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet} {α β : Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hCmem : C ∈ moveSupports)
    (hC : IsKempeCycle (incidentEdgeFinset G) x C α β)
    (herase : ∃ e ∈ C, x e = 0)
    (hsmall : C.card ≤ 3) :
    (∃ v : V, HasCubicD0BasicColorObstructionAt G x C v red) ∨
      (∃ v : V, HasCubicD0BasicColorObstructionAt G x C v blue) ∨
        (∃ v : V, HasCubicD0BasicColorObstructionAt G x C v purple) :=
  exists_hasCubicD0BasicColorObstructionAt_for_basic_color_obstruction_of_d0LocalMinimum_kirchhoffNeutral_small_support
    hcard hmin hCmem (isKirchhoffNeutralMoveSupport_of_isKempeCycle hC) herase hsmall

theorem
    zeroDefectD0_pos_of_basic_color_obstruction_of_d0LocalMinimum_isKempeCycle_small_support
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet} {α β : Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hCmem : C ∈ moveSupports)
    (hC : IsKempeCycle (incidentEdgeFinset G) x C α β)
    (herase : ∃ e ∈ C, x e = 0)
    (hsmall : C.card ≤ 3) :
    0 < zeroDefectD0 G x :=
  zeroDefectD0_pos_of_basic_color_obstruction_of_d0LocalMinimum_kirchhoffNeutral_small_support
    hcard hmin hCmem (isKirchhoffNeutralMoveSupport_of_isKempeCycle hC) herase hsmall

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

theorem
    not_isD0LocalMinimumForMoveSupports_of_rotationDiskData_internalFace_erases_zero_no_new_zero_side_budget_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (D : RotationDiskData V G.edgeSet)
    (hincident : ∀ v : V, D.asZeroBoundary.incident v = incidentEdgeFinset G v)
    {f : Finset G.edgeSet} (hf : f ∈ D.rotation.internalFaces)
    (hfmem : f ∈ moveSupports) {g : Color} {dI dC : Nat} (hg : g ≠ 0)
    (hgood :
      ∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
        if e ∈ f then x e ≠ g else x e ≠ 0)
    (herase : ∃ e ∈ f, x e = 0)
    (hnew : ∀ e ∈ f, x e ≠ g)
    (hI :
      zeroIncidentVertexCount G (cdlOneStepMoveOn G f g x) ≤
        zeroIncidentVertexCount G x + dI)
    (hCluster :
      zeroClusteringCount G (cdlOneStepMoveOn G f g x) ≤
        zeroClusteringCount G x + dC)
    (hbudget : 10 * dI + dC < 100) :
    ¬ IsD0LocalMinimumForMoveSupports G moveSupports x := by
  intro hmin
  exact
    (not_isD0LocalMinimumForMoveSupports_of_allowed_erases_zero_no_new_zero_side_budget_descent
      hfmem
      (isAllowedD0OneStepMoveOn_of_rotationDiskData_internalFace_and_vertex_witnesses
        D hincident hf hg hmin.source_flow hgood)
      herase hnew hI hCluster hbudget) hmin

theorem
    exists_created_zero_of_isD0LocalMinimumForMoveSupports_of_rotationDiskData_internalFace_erases_zero
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (D : RotationDiskData V G.edgeSet)
    (hincident : ∀ v : V, D.asZeroBoundary.incident v = incidentEdgeFinset G v)
    {f : Finset G.edgeSet} (hf : f ∈ D.rotation.internalFaces)
    (hfmem : f ∈ moveSupports) {g : Color} (hg : g ≠ 0)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hgood :
      ∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
        if e ∈ f then x e ≠ g else x e ≠ 0)
    (herase : ∃ e ∈ f, x e = 0) :
    ∃ e ∈ f, x e = g :=
  exists_created_zero_of_isD0LocalMinimumForMoveSupports_of_allowed_erases_zero
    hmin hfmem
    (isAllowedD0OneStepMoveOn_of_rotationDiskData_internalFace_and_vertex_witnesses
      D hincident hf hg hmin.source_flow hgood)
    herase

theorem
    exists_created_zero_of_isD0LocalMinimumForMoveSupports_of_rotationDiskData_internalFace_erases_incident_zero
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (D : RotationDiskData V G.edgeSet)
    (hincident : ∀ v : V, D.asZeroBoundary.incident v = incidentEdgeFinset G v)
    {f : Finset G.edgeSet} (hf : f ∈ D.rotation.internalFaces)
    (hfmem : f ∈ moveSupports) {g : Color} (hg : g ≠ 0)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hgood :
      ∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
        if e ∈ f then x e ≠ g else x e ≠ 0)
    {v : V} (heraseAt : ∃ e ∈ f, e ∈ incidentEdgeFinset G v ∧ x e = 0) :
    ∃ e ∈ f, x e = g :=
  exists_created_zero_of_isD0LocalMinimumForMoveSupports_of_allowed_erases_incident_zero
    hmin hfmem
    (isAllowedD0OneStepMoveOn_of_rotationDiskData_internalFace_and_vertex_witnesses
      D hincident hf hg hmin.source_flow hgood)
    heraseAt

theorem
    not_isD0LocalMinimumForMoveSupports_of_rotationDiskData_internalFace_basic_color_moves_small_support
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (D : RotationDiskData V G.edgeSet)
    (hincident : ∀ v : V, D.asZeroBoundary.incident v = incidentEdgeFinset G v)
    {f : Finset G.edgeSet} (hf : f ∈ D.rotation.internalFaces)
    (hfmem : f ∈ moveSupports)
    (hredgood :
      ∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
        if e ∈ f then x e ≠ red else x e ≠ 0)
    (hbluegood :
      ∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
        if e ∈ f then x e ≠ blue else x e ≠ 0)
    (hpurplegood :
      ∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
        if e ∈ f then x e ≠ purple else x e ≠ 0)
    (herase : ∃ e ∈ f, x e = 0)
    (hsmall : f.card ≤ 3) :
    ¬ IsD0LocalMinimumForMoveSupports G moveSupports x := by
  intro hmin
  exact
    (not_isD0LocalMinimumForMoveSupports_of_basic_color_moves_small_support
      hfmem
      (isAllowedD0OneStepMoveOn_of_rotationDiskData_internalFace_and_vertex_witnesses
        D hincident hf red_ne_zero hmin.source_flow hredgood)
      (isAllowedD0OneStepMoveOn_of_rotationDiskData_internalFace_and_vertex_witnesses
        D hincident hf blue_ne_zero hmin.source_flow hbluegood)
      (isAllowedD0OneStepMoveOn_of_rotationDiskData_internalFace_and_vertex_witnesses
        D hincident hf purple_ne_zero hmin.source_flow hpurplegood)
      herase hsmall) hmin

theorem
    not_isD0LocalMinimumForMoveSupports_of_rotationDiskData_internalFace_basic_color_moves_small_support_erases_incident_zero
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (D : RotationDiskData V G.edgeSet)
    (hincident : ∀ v : V, D.asZeroBoundary.incident v = incidentEdgeFinset G v)
    {f : Finset G.edgeSet} (hf : f ∈ D.rotation.internalFaces)
    (hfmem : f ∈ moveSupports)
    (hredgood :
      ∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
        if e ∈ f then x e ≠ red else x e ≠ 0)
    (hbluegood :
      ∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
        if e ∈ f then x e ≠ blue else x e ≠ 0)
    (hpurplegood :
      ∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
        if e ∈ f then x e ≠ purple else x e ≠ 0)
    {v : V} (heraseAt : ∃ e ∈ f, e ∈ incidentEdgeFinset G v ∧ x e = 0)
    (hsmall : f.card ≤ 3) :
    ¬ IsD0LocalMinimumForMoveSupports G moveSupports x := by
  intro hmin
  exact
    (not_isD0LocalMinimumForMoveSupports_of_basic_color_moves_small_support_erases_incident_zero
      hfmem
      (isAllowedD0OneStepMoveOn_of_rotationDiskData_internalFace_and_vertex_witnesses
        D hincident hf red_ne_zero hmin.source_flow hredgood)
      (isAllowedD0OneStepMoveOn_of_rotationDiskData_internalFace_and_vertex_witnesses
        D hincident hf blue_ne_zero hmin.source_flow hbluegood)
      (isAllowedD0OneStepMoveOn_of_rotationDiskData_internalFace_and_vertex_witnesses
        D hincident hf purple_ne_zero hmin.source_flow hpurplegood)
      heraseAt hsmall) hmin

theorem
    exists_failed_basic_color_witness_of_d0LocalMinimum_rotationDiskData_internalFace_small_support
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (D : RotationDiskData V G.edgeSet)
    (hincident : ∀ v : V, D.asZeroBoundary.incident v = incidentEdgeFinset G v)
    {f : Finset G.edgeSet} (hf : f ∈ D.rotation.internalFaces)
    (hfmem : f ∈ moveSupports)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (herase : ∃ e ∈ f, x e = 0)
    (hsmall : f.card ≤ 3) :
    ¬ (∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
        if e ∈ f then x e ≠ red else x e ≠ 0) ∨
      ¬ (∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
          if e ∈ f then x e ≠ blue else x e ≠ 0) ∨
        ¬ (∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
            if e ∈ f then x e ≠ purple else x e ≠ 0) := by
  by_cases hredgood :
      ∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
        if e ∈ f then x e ≠ red else x e ≠ 0
  · by_cases hbluegood :
        ∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
          if e ∈ f then x e ≠ blue else x e ≠ 0
    · by_cases hpurplegood :
          ∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
            if e ∈ f then x e ≠ purple else x e ≠ 0
      · exact False.elim
          ((not_isD0LocalMinimumForMoveSupports_of_rotationDiskData_internalFace_basic_color_moves_small_support
            D hincident hf hfmem hredgood hbluegood hpurplegood herase hsmall) hmin)
      · exact Or.inr (Or.inr hpurplegood)
    · exact Or.inr (Or.inl hbluegood)
  · exact Or.inl hredgood

theorem
    exists_failed_basic_color_witness_of_d0LocalMinimum_rotationDiskData_internalFace_small_support_erases_incident_zero
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (D : RotationDiskData V G.edgeSet)
    (hincident : ∀ v : V, D.asZeroBoundary.incident v = incidentEdgeFinset G v)
    {f : Finset G.edgeSet} (hf : f ∈ D.rotation.internalFaces)
    (hfmem : f ∈ moveSupports)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    {v : V} (heraseAt : ∃ e ∈ f, e ∈ incidentEdgeFinset G v ∧ x e = 0)
    (hsmall : f.card ≤ 3) :
    ¬ (∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
        if e ∈ f then x e ≠ red else x e ≠ 0) ∨
      ¬ (∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
          if e ∈ f then x e ≠ blue else x e ≠ 0) ∨
        ¬ (∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
            if e ∈ f then x e ≠ purple else x e ≠ 0) := by
  by_cases hredgood :
      ∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
        if e ∈ f then x e ≠ red else x e ≠ 0
  · by_cases hbluegood :
        ∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
          if e ∈ f then x e ≠ blue else x e ≠ 0
    · by_cases hpurplegood :
          ∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
            if e ∈ f then x e ≠ purple else x e ≠ 0
      · exact False.elim
          ((not_isD0LocalMinimumForMoveSupports_of_rotationDiskData_internalFace_basic_color_moves_small_support_erases_incident_zero
            D hincident hf hfmem hredgood hbluegood hpurplegood heraseAt hsmall) hmin)
      · exact Or.inr (Or.inr hpurplegood)
    · exact Or.inr (Or.inl hbluegood)
  · exact Or.inl hredgood

theorem
    exists_forced_zero_basic_color_move_of_d0LocalMinimum_rotationDiskData_internalFace_small_support
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (D : RotationDiskData V G.edgeSet)
    (hincident : ∀ v : V, D.asZeroBoundary.incident v = incidentEdgeFinset G v)
    {f : Finset G.edgeSet} (hf : f ∈ D.rotation.internalFaces)
    (hfmem : f ∈ moveSupports)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (herase : ∃ e ∈ f, x e = 0)
    (hsmall : f.card ≤ 3) :
    (∃ v : V, ∀ e ∈ incidentEdgeFinset G v,
      if e ∈ f then x e = red else x e = 0) ∨
      (∃ v : V, ∀ e ∈ incidentEdgeFinset G v,
        if e ∈ f then x e = blue else x e = 0) ∨
        (∃ v : V, ∀ e ∈ incidentEdgeFinset G v,
          if e ∈ f then x e = purple else x e = 0) :=
  exists_forced_zero_basic_color_move_of_d0LocalMinimum_kirchhoffNeutral_small_support
    hmin hfmem (isKirchhoffNeutralMoveSupport_of_rotationDiskData_internalFace
      D hincident hf) herase hsmall

theorem
    exists_forced_zero_basic_color_move_of_d0LocalMinimum_rotationDiskData_internalFace_small_support_erases_incident_zero
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (D : RotationDiskData V G.edgeSet)
    (hincident : ∀ v : V, D.asZeroBoundary.incident v = incidentEdgeFinset G v)
    {f : Finset G.edgeSet} (hf : f ∈ D.rotation.internalFaces)
    (hfmem : f ∈ moveSupports)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    {v : V} (heraseAt : ∃ e ∈ f, e ∈ incidentEdgeFinset G v ∧ x e = 0)
    (hsmall : f.card ≤ 3) :
    (∃ v : V, ∀ e ∈ incidentEdgeFinset G v,
      if e ∈ f then x e = red else x e = 0) ∨
      (∃ v : V, ∀ e ∈ incidentEdgeFinset G v,
        if e ∈ f then x e = blue else x e = 0) ∨
        (∃ v : V, ∀ e ∈ incidentEdgeFinset G v,
          if e ∈ f then x e = purple else x e = 0) :=
  exists_forced_zero_basic_color_move_of_d0LocalMinimum_kirchhoffNeutral_small_support_erases_incident_zero
    hmin hfmem (isKirchhoffNeutralMoveSupport_of_rotationDiskData_internalFace
      D hincident hf) heraseAt hsmall

theorem
    exists_source_support_witness_for_basic_color_obstruction_of_d0LocalMinimum_rotationDiskData_internalFace_small_support
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (D : RotationDiskData V G.edgeSet)
    (hincident : ∀ v : V, D.asZeroBoundary.incident v = incidentEdgeFinset G v)
    {f : Finset G.edgeSet} (hf : f ∈ D.rotation.internalFaces)
    (hfmem : f ∈ moveSupports)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (herase : ∃ e ∈ f, x e = 0)
    (hsmall : f.card ≤ 3) :
    (∃ v : V, ∃ e : G.edgeSet,
      e ∈ incidentEdgeFinset G v ∧ e ∈ f ∧ x e = red ∧
        ∀ e' ∈ incidentEdgeFinset G v,
          if e' ∈ f then x e' = red else x e' = 0) ∨
      (∃ v : V, ∃ e : G.edgeSet,
        e ∈ incidentEdgeFinset G v ∧ e ∈ f ∧ x e = blue ∧
          ∀ e' ∈ incidentEdgeFinset G v,
            if e' ∈ f then x e' = blue else x e' = 0) ∨
        (∃ v : V, ∃ e : G.edgeSet,
          e ∈ incidentEdgeFinset G v ∧ e ∈ f ∧ x e = purple ∧
            ∀ e' ∈ incidentEdgeFinset G v,
              if e' ∈ f then x e' = purple else x e' = 0) :=
  exists_source_support_witness_for_basic_color_obstruction_of_d0LocalMinimum_kirchhoffNeutral_small_support
    hmin hfmem (isKirchhoffNeutralMoveSupport_of_rotationDiskData_internalFace
      D hincident hf) herase hsmall

theorem
    exists_cubic_two_support_edges_for_basic_color_obstruction_of_d0LocalMinimum_rotationDiskData_internalFace_small_support
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (D : RotationDiskData V G.edgeSet)
    (hincident : ∀ v : V, D.asZeroBoundary.incident v = incidentEdgeFinset G v)
    {f : Finset G.edgeSet} (hf : f ∈ D.rotation.internalFaces)
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hfmem : f ∈ moveSupports)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (herase : ∃ e ∈ f, x e = 0)
    (hsmall : f.card ≤ 3) :
    (∃ v : V,
      ((incidentEdgeFinset G v).filter fun e => e ∈ f).card = 2 ∧
        ∀ e ∈ incidentEdgeFinset G v,
          if e ∈ f then x e = red else x e = 0) ∨
      (∃ v : V,
        ((incidentEdgeFinset G v).filter fun e => e ∈ f).card = 2 ∧
          ∀ e ∈ incidentEdgeFinset G v,
            if e ∈ f then x e = blue else x e = 0) ∨
        (∃ v : V,
          ((incidentEdgeFinset G v).filter fun e => e ∈ f).card = 2 ∧
            ∀ e ∈ incidentEdgeFinset G v,
              if e ∈ f then x e = purple else x e = 0) :=
  exists_cubic_two_support_edges_for_basic_color_obstruction_of_d0LocalMinimum_kirchhoffNeutral_small_support
    hcard hmin hfmem (isKirchhoffNeutralMoveSupport_of_rotationDiskData_internalFace
      D hincident hf) herase hsmall

theorem
    exists_cubic_outside_zero_edge_for_basic_color_obstruction_of_d0LocalMinimum_rotationDiskData_internalFace_small_support
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (D : RotationDiskData V G.edgeSet)
    (hincident : ∀ v : V, D.asZeroBoundary.incident v = incidentEdgeFinset G v)
    {f : Finset G.edgeSet} (hf : f ∈ D.rotation.internalFaces)
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hfmem : f ∈ moveSupports)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (herase : ∃ e ∈ f, x e = 0)
    (hsmall : f.card ≤ 3) :
    (∃ v : V, ∃ e : G.edgeSet,
      e ∈ incidentEdgeFinset G v ∧ e ∉ f ∧ x e = 0 ∧
        ∀ e' ∈ incidentEdgeFinset G v,
          if e' ∈ f then x e' = red else x e' = 0) ∨
      (∃ v : V, ∃ e : G.edgeSet,
        e ∈ incidentEdgeFinset G v ∧ e ∉ f ∧ x e = 0 ∧
          ∀ e' ∈ incidentEdgeFinset G v,
            if e' ∈ f then x e' = blue else x e' = 0) ∨
        (∃ v : V, ∃ e : G.edgeSet,
          e ∈ incidentEdgeFinset G v ∧ e ∉ f ∧ x e = 0 ∧
            ∀ e' ∈ incidentEdgeFinset G v,
              if e' ∈ f then x e' = purple else x e' = 0) :=
  exists_cubic_outside_zero_edge_for_basic_color_obstruction_of_d0LocalMinimum_kirchhoffNeutral_small_support
    hcard hmin hfmem (isKirchhoffNeutralMoveSupport_of_rotationDiskData_internalFace
      D hincident hf) herase hsmall

theorem
    exists_cubic_zeroIncidentEdgeCount_eq_one_for_basic_color_obstruction_of_d0LocalMinimum_rotationDiskData_internalFace_small_support
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (D : RotationDiskData V G.edgeSet)
    (hincident : ∀ v : V, D.asZeroBoundary.incident v = incidentEdgeFinset G v)
    {f : Finset G.edgeSet} (hf : f ∈ D.rotation.internalFaces)
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hfmem : f ∈ moveSupports)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (herase : ∃ e ∈ f, x e = 0)
    (hsmall : f.card ≤ 3) :
    (∃ v : V, zeroIncidentEdgeCount G x v = 1 ∧
      ∀ e ∈ incidentEdgeFinset G v,
        if e ∈ f then x e = red else x e = 0) ∨
      (∃ v : V, zeroIncidentEdgeCount G x v = 1 ∧
        ∀ e ∈ incidentEdgeFinset G v,
          if e ∈ f then x e = blue else x e = 0) ∨
        (∃ v : V, zeroIncidentEdgeCount G x v = 1 ∧
          ∀ e ∈ incidentEdgeFinset G v,
            if e ∈ f then x e = purple else x e = 0) :=
  exists_cubic_zeroIncidentEdgeCount_eq_one_for_basic_color_obstruction_of_d0LocalMinimum_kirchhoffNeutral_small_support
    hcard hmin hfmem (isKirchhoffNeutralMoveSupport_of_rotationDiskData_internalFace
      D hincident hf) herase hsmall

theorem
    exists_cubic_zeroClusteringLocalTerm_eq_zero_for_basic_color_obstruction_of_d0LocalMinimum_rotationDiskData_internalFace_small_support
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (D : RotationDiskData V G.edgeSet)
    (hincident : ∀ v : V, D.asZeroBoundary.incident v = incidentEdgeFinset G v)
    {f : Finset G.edgeSet} (hf : f ∈ D.rotation.internalFaces)
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hfmem : f ∈ moveSupports)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (herase : ∃ e ∈ f, x e = 0)
    (hsmall : f.card ≤ 3) :
    (∃ v : V, zeroIncidentEdgeCount G x v = 1 ∧
      zeroIncidentEdgeCount G x v - 1 = 0 ∧
      ∀ e ∈ incidentEdgeFinset G v,
        if e ∈ f then x e = red else x e = 0) ∨
      (∃ v : V, zeroIncidentEdgeCount G x v = 1 ∧
        zeroIncidentEdgeCount G x v - 1 = 0 ∧
        ∀ e ∈ incidentEdgeFinset G v,
          if e ∈ f then x e = blue else x e = 0) ∨
        (∃ v : V, zeroIncidentEdgeCount G x v = 1 ∧
          zeroIncidentEdgeCount G x v - 1 = 0 ∧
          ∀ e ∈ incidentEdgeFinset G v,
            if e ∈ f then x e = purple else x e = 0) :=
  exists_cubic_zeroClusteringLocalTerm_eq_zero_for_basic_color_obstruction_of_d0LocalMinimum_kirchhoffNeutral_small_support
    hcard hmin hfmem (isKirchhoffNeutralMoveSupport_of_rotationDiskData_internalFace
      D hincident hf) herase hsmall

theorem
    zeroIncidentVertexCount_pos_of_basic_color_obstruction_of_d0LocalMinimum_rotationDiskData_internalFace_small_support
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (D : RotationDiskData V G.edgeSet)
    (hincident : ∀ v : V, D.asZeroBoundary.incident v = incidentEdgeFinset G v)
    {f : Finset G.edgeSet} (hf : f ∈ D.rotation.internalFaces)
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hfmem : f ∈ moveSupports)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (herase : ∃ e ∈ f, x e = 0)
    (hsmall : f.card ≤ 3) :
    0 < zeroIncidentVertexCount G x :=
  zeroIncidentVertexCount_pos_of_basic_color_obstruction_of_d0LocalMinimum_kirchhoffNeutral_small_support
    hcard hmin hfmem (isKirchhoffNeutralMoveSupport_of_rotationDiskData_internalFace
      D hincident hf) herase hsmall

theorem
    exists_hasCubicD0BasicColorObstructionAt_for_basic_color_obstruction_of_d0LocalMinimum_rotationDiskData_internalFace_small_support
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (D : RotationDiskData V G.edgeSet)
    (hincident : ∀ v : V, D.asZeroBoundary.incident v = incidentEdgeFinset G v)
    {f : Finset G.edgeSet} (hf : f ∈ D.rotation.internalFaces)
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hfmem : f ∈ moveSupports)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (herase : ∃ e ∈ f, x e = 0)
    (hsmall : f.card ≤ 3) :
    (∃ v : V, HasCubicD0BasicColorObstructionAt G x f v red) ∨
      (∃ v : V, HasCubicD0BasicColorObstructionAt G x f v blue) ∨
        (∃ v : V, HasCubicD0BasicColorObstructionAt G x f v purple) :=
  exists_hasCubicD0BasicColorObstructionAt_for_basic_color_obstruction_of_d0LocalMinimum_kirchhoffNeutral_small_support
    hcard hmin hfmem (isKirchhoffNeutralMoveSupport_of_rotationDiskData_internalFace
      D hincident hf) herase hsmall

theorem
    zeroDefectD0_pos_of_basic_color_obstruction_of_d0LocalMinimum_rotationDiskData_internalFace_small_support
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (D : RotationDiskData V G.edgeSet)
    (hincident : ∀ v : V, D.asZeroBoundary.incident v = incidentEdgeFinset G v)
    {f : Finset G.edgeSet} (hf : f ∈ D.rotation.internalFaces)
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hfmem : f ∈ moveSupports)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (herase : ∃ e ∈ f, x e = 0)
    (hsmall : f.card ≤ 3) :
    0 < zeroDefectD0 G x :=
  zeroDefectD0_pos_of_basic_color_obstruction_of_d0LocalMinimum_kirchhoffNeutral_small_support
    hcard hmin hfmem (isKirchhoffNeutralMoveSupport_of_rotationDiskData_internalFace
      D hincident hf) herase hsmall

/-- The zero-edge set is a matching in the manuscript's local sense: no vertex
is incident to two or more zero-valued edges. -/
def ZeroEdgesFormMatching (G : SimpleGraph V) [Fintype G.edgeSet]
    (x : G.edgeSet → Color) : Prop :=
  ∀ v : V, zeroIncidentEdgeCount G x v ≤ 1

/-- A local obstruction to the matching-zero property: at least two zero edges
meet at one vertex.  This is the local neighborhood that the manuscript says
must be repaired by finite/local analysis. -/
def HasClusteredZeroVertex (G : SimpleGraph V) [Fintype G.edgeSet]
    (x : G.edgeSet → Color) : Prop :=
  ∃ v : V, 2 ≤ zeroIncidentEdgeCount G x v

/-- A permitted one-step `D₀` repair: the move erases at least one existing
zero and creates no new zero on its support.  This names the local repair
obligation used in the manuscript's matching-zero route. -/
def HasD0DescentRepair (G : SimpleGraph V) [Fintype G.edgeSet]
    (moveSupports : Finset (Finset G.edgeSet)) (x : G.edgeSet → Color) :
    Prop :=
  ∃ C ∈ moveSupports, ∃ g : Color,
    IsAllowedD0OneStepMoveOn G C g x (cdlOneStepMoveOn G C g x) ∧
      (∃ e ∈ C, x e = 0) ∧
        ∀ e ∈ C, x e ≠ g

/-- Vertex-local `D₀` repair: the move erases a zero edge incident to the
specified vertex and creates no new zero on its support. -/
def HasD0DescentRepairAt (G : SimpleGraph V) [Fintype G.edgeSet]
    (moveSupports : Finset (Finset G.edgeSet)) (x : G.edgeSet → Color)
    (v : V) : Prop :=
  ∃ C ∈ moveSupports, ∃ g : Color,
    IsAllowedD0OneStepMoveOn G C g x (cdlOneStepMoveOn G C g x) ∧
      (∃ e ∈ C, e ∈ incidentEdgeFinset G v ∧ x e = 0) ∧
        ∀ e ∈ C, x e ≠ g

/-- Patch/local-combinatorics hypothesis for the manuscript's matching-zeros
step: every non-matching zero pattern admits a permitted one-step repair that
erases an existing zero and creates no new zero on its support.  Theorems below
show that this is exactly the repair fact needed to force matching zeros at
`D₀` local minima. -/
def EveryNonmatchingZeroPatternHasD0Descent (G : SimpleGraph V)
    [Fintype V] [Fintype G.edgeSet] (moveSupports : Finset (Finset G.edgeSet))
    (x : G.edgeSet → Color) : Prop :=
  ¬ ZeroEdgesFormMatching G x →
    HasD0DescentRepair G moveSupports x

/-- Vertex-local version of the finite repair hypothesis: every clustered-zero
vertex supplies a permitted one-step repair that erases an existing zero and
creates no new zero on its support. -/
def EveryClusteredZeroVertexHasD0Descent (G : SimpleGraph V)
    [Fintype V] [Fintype G.edgeSet] (moveSupports : Finset (Finset G.edgeSet))
    (x : G.edgeSet → Color) : Prop :=
  ∀ v : V, 2 ≤ zeroIncidentEdgeCount G x v →
    HasD0DescentRepairAt G moveSupports x v

/-- A Kirchhoff-neutral support with CDL-good target witnesses gives the
vertex-local repair obligation used by the manuscript's matching-zero route. -/
theorem hasD0DescentRepairAt_of_kirchhoffNeutral_and_vertex_witnesses
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet} {g : Color} {v : V}
    (hCmem : C ∈ moveSupports) (hg : g ≠ 0) (hx : IsGraphFlow G x)
    (hC : IsKirchhoffNeutralMoveSupport G C)
    (hgood :
      ∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
        if e ∈ C then x e ≠ g else x e ≠ 0)
    (heraseAt : ∃ e ∈ C, e ∈ incidentEdgeFinset G v ∧ x e = 0)
    (hnew : ∀ e ∈ C, x e ≠ g) :
    HasD0DescentRepairAt G moveSupports x v :=
  ⟨C, hCmem, g,
    isAllowedD0OneStepMoveOn_of_kirchhoffNeutral_and_vertex_witnesses
      hg hx hC hgood,
    heraseAt, hnew⟩

/-- A concrete Kempe-cycle move gives the vertex-local repair obligation used
by the manuscript's matching-zero route, provided it erases an incident zero
and creates no new zero on its support. -/
theorem hasD0DescentRepairAt_of_isKempeCycle_and_vertex_witnesses
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet} {α β g : Color} {v : V}
    (hCmem : C ∈ moveSupports) (hg : g ≠ 0) (hx : IsGraphFlow G x)
    (hC : IsKempeCycle (incidentEdgeFinset G) x C α β)
    (hgood :
      ∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
        if e ∈ C then x e ≠ g else x e ≠ 0)
    (heraseAt : ∃ e ∈ C, e ∈ incidentEdgeFinset G v ∧ x e = 0)
    (hnew : ∀ e ∈ C, x e ≠ g) :
    HasD0DescentRepairAt G moveSupports x v :=
  hasD0DescentRepairAt_of_kirchhoffNeutral_and_vertex_witnesses
    hCmem hg hx (isKirchhoffNeutralMoveSupport_of_isKempeCycle hC) hgood
    heraseAt hnew

/-- A concrete rotation-disk internal face gives the same vertex-local repair
obligation once it is an allowed CDL-good move and creates no new zero. -/
theorem hasD0DescentRepairAt_of_rotationDiskData_internalFace_and_vertex_witnesses
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    (D : RotationDiskData V G.edgeSet)
    (hincident : ∀ v : V, D.asZeroBoundary.incident v = incidentEdgeFinset G v)
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {f : Finset G.edgeSet} (hf : f ∈ D.rotation.internalFaces)
    (hfmem : f ∈ moveSupports) {g : Color}
    (hg : g ≠ 0) (hx : IsGraphFlow G x)
    (hgood :
      ∀ v : V, ∃ e ∈ incidentEdgeFinset G v,
        if e ∈ f then x e ≠ g else x e ≠ 0)
    {v : V} (heraseAt : ∃ e ∈ f, e ∈ incidentEdgeFinset G v ∧ x e = 0)
    (hnew : ∀ e ∈ f, x e ≠ g) :
    HasD0DescentRepairAt G moveSupports x v :=
  hasD0DescentRepairAt_of_kirchhoffNeutral_and_vertex_witnesses
    hfmem hg hx
    (isKirchhoffNeutralMoveSupport_of_rotationDiskData_internalFace
      D hincident hf)
    hgood heraseAt hnew

/-- Kirchhoff-neutral local repair data at every clustered-zero vertex is exactly
enough to instantiate the vertex-local repair hypothesis. -/
theorem everyClusteredZeroVertexHasD0Descent_of_kirchhoffNeutral_vertex_repairs
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hx : IsGraphFlow G x)
    (hrepair :
      ∀ v : V, 2 ≤ zeroIncidentEdgeCount G x v →
        ∃ C ∈ moveSupports, ∃ g : Color,
          g ≠ 0 ∧
            IsKirchhoffNeutralMoveSupport G C ∧
              (∀ w : V, ∃ e ∈ incidentEdgeFinset G w,
                if e ∈ C then x e ≠ g else x e ≠ 0) ∧
                (∃ e ∈ C, e ∈ incidentEdgeFinset G v ∧ x e = 0) ∧
                  ∀ e ∈ C, x e ≠ g) :
    EveryClusteredZeroVertexHasD0Descent G moveSupports x := by
  intro v hv
  rcases hrepair v hv with
    ⟨C, hCmem, g, hg, hC, hgood, heraseAt, hnew⟩
  exact hasD0DescentRepairAt_of_kirchhoffNeutral_and_vertex_witnesses
    hCmem hg hx hC hgood heraseAt hnew

/-- Kempe-cycle local data at every clustered-zero vertex is exactly enough to
instantiate the vertex-local repair hypothesis. -/
theorem everyClusteredZeroVertexHasD0Descent_of_kempeCycle_vertex_repairs
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hx : IsGraphFlow G x)
    (hrepair :
      ∀ v : V, 2 ≤ zeroIncidentEdgeCount G x v →
        ∃ C ∈ moveSupports, ∃ α β g : Color,
          g ≠ 0 ∧
            IsKempeCycle (incidentEdgeFinset G) x C α β ∧
              (∀ w : V, ∃ e ∈ incidentEdgeFinset G w,
                if e ∈ C then x e ≠ g else x e ≠ 0) ∧
                (∃ e ∈ C, e ∈ incidentEdgeFinset G v ∧ x e = 0) ∧
                  ∀ e ∈ C, x e ≠ g) :
    EveryClusteredZeroVertexHasD0Descent G moveSupports x := by
  apply everyClusteredZeroVertexHasD0Descent_of_kirchhoffNeutral_vertex_repairs hx
  intro v hv
  rcases hrepair v hv with
    ⟨C, hCmem, α, β, g, hg, hC, hgood, heraseAt, hnew⟩
  exact ⟨C, hCmem, g, hg,
    isKirchhoffNeutralMoveSupport_of_isKempeCycle hC,
    hgood, heraseAt, hnew⟩

/-- Rotation-disk local data at every clustered-zero vertex is exactly enough
to instantiate the vertex-local repair hypothesis. -/
theorem everyClusteredZeroVertexHasD0Descent_of_rotationDiskData_internalFace_repairs
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    (D : RotationDiskData V G.edgeSet)
    (hincident : ∀ v : V, D.asZeroBoundary.incident v = incidentEdgeFinset G v)
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hx : IsGraphFlow G x)
    (hrepair :
      ∀ v : V, 2 ≤ zeroIncidentEdgeCount G x v →
        ∃ f ∈ moveSupports, f ∈ D.rotation.internalFaces ∧
          ∃ g : Color,
            g ≠ 0 ∧
              (∀ w : V, ∃ e ∈ incidentEdgeFinset G w,
                if e ∈ f then x e ≠ g else x e ≠ 0) ∧
                (∃ e ∈ f, e ∈ incidentEdgeFinset G v ∧ x e = 0) ∧
                  ∀ e ∈ f, x e ≠ g) :
    EveryClusteredZeroVertexHasD0Descent G moveSupports x := by
  apply everyClusteredZeroVertexHasD0Descent_of_kirchhoffNeutral_vertex_repairs hx
  intro v hv
  rcases hrepair v hv with
    ⟨f, hfmem, hf, g, hg, hgood, heraseAt, hnew⟩
  exact ⟨f, hfmem, g, hg,
    isKirchhoffNeutralMoveSupport_of_rotationDiskData_internalFace
      D hincident hf,
    hgood, heraseAt, hnew⟩

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

theorem zeroIncidentEdgeCount_pos_iff_exists_incident_zero {G : SimpleGraph V}
    [Fintype G.edgeSet] {x : G.edgeSet → Color} {v : V} :
    0 < zeroIncidentEdgeCount G x v ↔
      ∃ e ∈ incidentEdgeFinset G v, x e = 0 := by
  constructor
  · intro hpos
    by_contra hnone
    have hzero : zeroIncidentEdgeCount G x v = 0 := by
      rw [zeroIncidentEdgeCount_eq_zero_iff]
      intro e he_inc he_zero
      exact hnone ⟨e, he_inc, he_zero⟩
    omega
  · rintro ⟨e, he_inc, he_zero⟩
    by_contra hnotpos
    have hcount : zeroIncidentEdgeCount G x v = 0 := by
      omega
    exact (zeroIncidentEdgeCount_eq_zero_iff.mp hcount e he_inc) he_zero

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

/-- Negating the matching-zero property is exactly the presence of a clustered
zero vertex. -/
theorem not_zeroEdgesFormMatching_iff_hasClusteredZeroVertex
    {G : SimpleGraph V} [Fintype G.edgeSet] {x : G.edgeSet → Color} :
    ¬ ZeroEdgesFormMatching G x ↔ HasClusteredZeroVertex G x := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro v
    by_contra hvle
    have hvcluster : 2 ≤ zeroIncidentEdgeCount G x v := by
      omega
    exact hnone ⟨v, hvcluster⟩
  · rintro ⟨v, hvcluster⟩ hmatch
    have hvle := hmatch v
    omega

/-- Matching zeros are equivalently the absence of a clustered zero vertex. -/
theorem zeroEdgesFormMatching_iff_not_hasClusteredZeroVertex
    {G : SimpleGraph V} [Fintype G.edgeSet] {x : G.edgeSet → Color} :
    ZeroEdgesFormMatching G x ↔ ¬ HasClusteredZeroVertex G x := by
  rw [← not_zeroEdgesFormMatching_iff_hasClusteredZeroVertex]
  exact not_not.symm

/-- Under a matching zero pattern, a vertex has exactly one incident zero edge
iff there is an explicit incident zero edge. -/
theorem zeroIncidentEdgeCount_eq_one_iff_exists_incident_zero_of_zeroEdgesFormMatching
    {G : SimpleGraph V} [Fintype G.edgeSet] {x : G.edgeSet → Color}
    (hmatch : ZeroEdgesFormMatching G x) (v : V) :
    zeroIncidentEdgeCount G x v = 1 ↔
      ∃ e ∈ incidentEdgeFinset G v, x e = 0 := by
  constructor
  · intro hcount
    exact zeroIncidentEdgeCount_pos_iff_exists_incident_zero.mp (by omega)
  · intro hzero
    have hpos :
        0 < zeroIncidentEdgeCount G x v :=
      zeroIncidentEdgeCount_pos_iff_exists_incident_zero.mpr hzero
    have hle : zeroIncidentEdgeCount G x v ≤ 1 := hmatch v
    omega

/-- Positive clustering is exactly the presence of a vertex incident to at
least two zero edges. -/
theorem zeroClusteringCount_pos_iff_hasClusteredZeroVertex
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet] {x : G.edgeSet → Color} :
    0 < zeroClusteringCount G x ↔ HasClusteredZeroVertex G x := by
  rw [← not_zeroEdgesFormMatching_iff_hasClusteredZeroVertex,
    ← zeroClusteringCount_eq_zero_iff_zeroEdgesFormMatching]
  exact Nat.pos_iff_ne_zero

/-- A vertex-local repair is, in particular, a global zero-erasing/no-new-zero
repair. -/
theorem hasD0DescentRepair_of_hasD0DescentRepairAt
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {v : V} :
    HasD0DescentRepairAt G moveSupports x v →
      HasD0DescentRepair G moveSupports x := by
  rintro ⟨C, hCmem, g, hmove, heraseAt, hnew⟩
  rcases heraseAt with ⟨e, heC, _hev, hzero⟩
  exact ⟨C, hCmem, g, hmove, ⟨e, heC, hzero⟩, hnew⟩

/-- A `D₀` local minimum blocks the manuscript's
zero-erasing/no-new-zero one-step repair obligation. -/
theorem not_hasD0DescentRepair_of_isD0LocalMinimumForMoveSupports
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x) :
    ¬ HasD0DescentRepair G moveSupports x := by
  rintro ⟨C, hCmem, g, hmove, herase, hnew⟩
  exact
    (not_isD0LocalMinimumForMoveSupports_of_allowed_erases_zero_no_new_zero_descent
      hCmem hmove herase hnew) hmin

/-- A `D₀` local minimum blocks every vertex-local zero-erasing/no-new-zero
repair. -/
theorem not_hasD0DescentRepairAt_of_isD0LocalMinimumForMoveSupports
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {v : V}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x) :
    ¬ HasD0DescentRepairAt G moveSupports x v := by
  intro hrepair
  exact (not_hasD0DescentRepair_of_isD0LocalMinimumForMoveSupports hmin)
    (hasD0DescentRepair_of_hasD0DescentRepairAt hrepair)

/-- Concrete obstruction form for a proposed neutral local repair: at a `D₀`
local minimum, a neutral support that erases an incident zero and creates no
new zero cannot also remain CDL-good.  Its failure is witnessed by a vertex
whose whole incident neighborhood is forced to zero after the move. -/
theorem exists_forced_zero_vertex_of_isD0LocalMinimumForMoveSupports_kirchhoffNeutral_erases_incident_zero_creates_no_zero
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet} {g : Color} {v : V}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hCmem : C ∈ moveSupports) (hg : g ≠ 0)
    (hC : IsKirchhoffNeutralMoveSupport G C)
    (heraseAt : ∃ e ∈ C, e ∈ incidentEdgeFinset G v ∧ x e = 0)
    (hnew : ∀ e ∈ C, x e ≠ g) :
    ∃ w : V, ∀ e ∈ incidentEdgeFinset G w,
      if e ∈ C then x e = g else x e = 0 := by
  have hnotAllowed :
      ¬ IsAllowedD0OneStepMoveOn G C g x (cdlOneStepMoveOn G C g x) := by
    intro hmove
    exact (not_hasD0DescentRepairAt_of_isD0LocalMinimumForMoveSupports
      (v := v) hmin)
      ⟨C, hCmem, g, hmove, heraseAt, hnew⟩
  exact
    (not_isAllowedD0OneStepMoveOn_iff_exists_vertex_forced_zero_of_kirchhoffNeutral
      hg hmin.source_flow hC).mp hnotAllowed

/-- Kempe-cycle specialization of the forced-zero obstruction. -/
theorem exists_forced_zero_vertex_of_isD0LocalMinimumForMoveSupports_isKempeCycle_erases_incident_zero_creates_no_zero
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet} {α β g : Color} {v : V}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hCmem : C ∈ moveSupports) (hg : g ≠ 0)
    (hC : IsKempeCycle (incidentEdgeFinset G) x C α β)
    (heraseAt : ∃ e ∈ C, e ∈ incidentEdgeFinset G v ∧ x e = 0)
    (hnew : ∀ e ∈ C, x e ≠ g) :
    ∃ w : V, ∀ e ∈ incidentEdgeFinset G w,
      if e ∈ C then x e = g else x e = 0 :=
  exists_forced_zero_vertex_of_isD0LocalMinimumForMoveSupports_kirchhoffNeutral_erases_incident_zero_creates_no_zero
    hmin hCmem hg (isKirchhoffNeutralMoveSupport_of_isKempeCycle hC)
    heraseAt hnew

/-- Rotation-disk internal-face specialization of the forced-zero obstruction. -/
theorem
    exists_forced_zero_vertex_of_isD0LocalMinimumForMoveSupports_rotationDiskData_internalFace_erases_incident_zero_creates_no_zero
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    (D : RotationDiskData V G.edgeSet)
    (hincident : ∀ v : V, D.asZeroBoundary.incident v = incidentEdgeFinset G v)
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {f : Finset G.edgeSet} {g : Color} {v : V}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hfmem : f ∈ moveSupports) (hf : f ∈ D.rotation.internalFaces)
    (hg : g ≠ 0)
    (heraseAt : ∃ e ∈ f, e ∈ incidentEdgeFinset G v ∧ x e = 0)
    (hnew : ∀ e ∈ f, x e ≠ g) :
    ∃ w : V, ∀ e ∈ incidentEdgeFinset G w,
      if e ∈ f then x e = g else x e = 0 :=
  exists_forced_zero_vertex_of_isD0LocalMinimumForMoveSupports_kirchhoffNeutral_erases_incident_zero_creates_no_zero
    hmin hfmem hg
    (isKirchhoffNeutralMoveSupport_of_rotationDiskData_internalFace
      D hincident hf)
    heraseAt hnew

/-- Cubic obstruction packaged from a failed proposed neutral local repair.  In
the cubic case, the forced-zero bad vertex has exactly two support edges and one
outside zero edge, hence it is an explicit `HasCubicD0BasicColorObstructionAt`. -/
theorem
    exists_hasCubicD0BasicColorObstructionAt_of_isD0LocalMinimumForMoveSupports_kirchhoffNeutral_erases_incident_zero_creates_no_zero
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet} {g : Color} {v : V}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hCmem : C ∈ moveSupports) (hg : g ≠ 0)
    (hC : IsKirchhoffNeutralMoveSupport G C)
    (heraseAt : ∃ e ∈ C, e ∈ incidentEdgeFinset G v ∧ x e = 0)
    (hnew : ∀ e ∈ C, x e ≠ g) :
    ∃ w : V, HasCubicD0BasicColorObstructionAt G x C w g := by
  rcases
    exists_forced_zero_vertex_of_isD0LocalMinimumForMoveSupports_kirchhoffNeutral_erases_incident_zero_creates_no_zero
      hmin hCmem hg hC heraseAt hnew with ⟨w, hforced⟩
  have htwo :
      ((incidentEdgeFinset G w).filter fun e => e ∈ C).card = 2 :=
    incident_support_card_eq_two_of_isCDLGoodAtVertex_and_forced_zero_move
      (hcard w) hC (hmin.source_good w) hforced
  exact ⟨w,
    hasCubicD0BasicColorObstructionAt_of_cubic_two_support_forced_zero_move
      hg (hcard w) htwo hforced⟩

/-- Kempe-cycle specialization of the cubic obstruction packaged from a failed
proposed local repair. -/
theorem
    exists_hasCubicD0BasicColorObstructionAt_of_isD0LocalMinimumForMoveSupports_isKempeCycle_erases_incident_zero_creates_no_zero
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet} {α β g : Color} {v : V}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hCmem : C ∈ moveSupports) (hg : g ≠ 0)
    (hC : IsKempeCycle (incidentEdgeFinset G) x C α β)
    (heraseAt : ∃ e ∈ C, e ∈ incidentEdgeFinset G v ∧ x e = 0)
    (hnew : ∀ e ∈ C, x e ≠ g) :
    ∃ w : V, HasCubicD0BasicColorObstructionAt G x C w g :=
  exists_hasCubicD0BasicColorObstructionAt_of_isD0LocalMinimumForMoveSupports_kirchhoffNeutral_erases_incident_zero_creates_no_zero
    hcard hmin hCmem hg (isKirchhoffNeutralMoveSupport_of_isKempeCycle hC)
    heraseAt hnew

/-- Rotation-disk internal-face specialization of the cubic obstruction packaged
from a failed proposed local repair. -/
theorem
    exists_hasCubicD0BasicColorObstructionAt_of_isD0LocalMinimumForMoveSupports_rotationDiskData_internalFace_erases_incident_zero_creates_no_zero
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    (D : RotationDiskData V G.edgeSet)
    (hincident : ∀ v : V, D.asZeroBoundary.incident v = incidentEdgeFinset G v)
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {f : Finset G.edgeSet} {g : Color} {v : V}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hfmem : f ∈ moveSupports) (hf : f ∈ D.rotation.internalFaces)
    (hg : g ≠ 0)
    (heraseAt : ∃ e ∈ f, e ∈ incidentEdgeFinset G v ∧ x e = 0)
    (hnew : ∀ e ∈ f, x e ≠ g) :
    ∃ w : V, HasCubicD0BasicColorObstructionAt G x f w g :=
  exists_hasCubicD0BasicColorObstructionAt_of_isD0LocalMinimumForMoveSupports_kirchhoffNeutral_erases_incident_zero_creates_no_zero
    hcard hmin hfmem hg
    (isKirchhoffNeutralMoveSupport_of_rotationDiskData_internalFace
      D hincident hf)
    heraseAt hnew

/-- Second-step local hypothesis for the blocker left by a failed proposed
`D₀` repair: every cubic basic-color obstruction admits a vertex-local
zero-erasing/no-new-zero repair. -/
def EveryCubicD0BasicColorObstructionHasD0Descent (G : SimpleGraph V)
    [Fintype V] [Fintype G.edgeSet] (moveSupports : Finset (Finset G.edgeSet))
    (x : G.edgeSet → Color) : Prop :=
  ∀ (C : Finset G.edgeSet) (v : V) (g : Color),
    HasCubicD0BasicColorObstructionAt G x C v g →
      HasD0DescentRepairAt G moveSupports x v

/-- Concrete-star version of the second-step local repair hypothesis: every
three-edge obstruction star (two support edges of color `g`, one outside zero
edge) admits a vertex-local zero-erasing/no-new-zero repair. -/
def EveryCubicD0BasicColorObstructionStarHasD0Descent (G : SimpleGraph V)
    [Fintype V] [Fintype G.edgeSet] (moveSupports : Finset (Finset G.edgeSet))
    (x : G.edgeSet → Color) : Prop :=
  ∀ (C : Finset G.edgeSet) (v : V) (g : Color)
    (e₁ e₂ e₀ : G.edgeSet),
    e₁ ≠ e₂ → e₁ ≠ e₀ → e₂ ≠ e₀ →
      incidentEdgeFinset G v = {e₁, e₂, e₀} →
        e₁ ∈ C → e₂ ∈ C → e₀ ∉ C →
          x e₁ = g → x e₂ = g → x e₀ = 0 →
            HasD0DescentRepairAt G moveSupports x v

/-- To discharge the abstract second-step cubic-obstruction repair hypothesis,
it is enough to repair every concrete three-edge obstruction star: two support
edges of color `g` and the unique outside zero edge. -/
theorem
    everyCubicD0BasicColorObstructionHasD0Descent_of_cubic_star_repairs
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hrepair :
      EveryCubicD0BasicColorObstructionStarHasD0Descent G moveSupports x) :
    EveryCubicD0BasicColorObstructionHasD0Descent G moveSupports x := by
  intro C v g hobst
  rcases
    exists_incidentEdgeFinset_eq_support_pair_insert_outside_zero_of_hasCubicD0BasicColorObstructionAt
      (hcard v) hobst with
    ⟨e₁, e₂, e₀, h12, h10, h20, hstar, he₁C, he₂C, he₀C, hx₁,
      hx₂, hx₀⟩
  exact hrepair C v g e₁ e₂ e₀ h12 h10 h20 hstar he₁C he₂C he₀C
    hx₁ hx₂ hx₀

/-- First-step local candidate for the two-step `D₀` route: at every
clustered-zero vertex there is a Kirchhoff-neutral support that erases an
incident zero and creates no new zero on its support.  Unlike
`EveryClusteredZeroVertexHasD0Descent`, this does not assume the first step is
already CDL-good; the cubic obstruction theorem below records the exact
second-step repair obligation left when CDL-goodness fails. -/
def EveryClusteredZeroVertexHasNeutralD0Candidate (G : SimpleGraph V)
    [Fintype V] [Fintype G.edgeSet] (moveSupports : Finset (Finset G.edgeSet))
    (x : G.edgeSet → Color) : Prop :=
  ∀ v : V, 2 ≤ zeroIncidentEdgeCount G x v →
    ∃ C ∈ moveSupports, ∃ g : Color,
      g ≠ 0 ∧ IsKirchhoffNeutralMoveSupport G C ∧
        (∃ e ∈ C, e ∈ incidentEdgeFinset G v ∧ x e = 0) ∧
          ∀ e ∈ C, x e ≠ g

/-- Kempe-cycle source form for the first-step local candidate. -/
def EveryClusteredZeroVertexHasKempeD0Candidate (G : SimpleGraph V)
    [Fintype V] [Fintype G.edgeSet] (moveSupports : Finset (Finset G.edgeSet))
    (x : G.edgeSet → Color) : Prop :=
  ∀ v : V, 2 ≤ zeroIncidentEdgeCount G x v →
    ∃ C ∈ moveSupports, ∃ α β g : Color,
      g ≠ 0 ∧ IsKempeCycle (incidentEdgeFinset G) x C α β ∧
        (∃ e ∈ C, e ∈ incidentEdgeFinset G v ∧ x e = 0) ∧
          ∀ e ∈ C, x e ≠ g

/-- Rotation-disk internal-face source form for the first-step local
candidate. -/
def EveryClusteredZeroVertexHasRotationDiskD0Candidate (G : SimpleGraph V)
    [Fintype V] [Fintype G.edgeSet] (D : RotationDiskData V G.edgeSet)
    (moveSupports : Finset (Finset G.edgeSet)) (x : G.edgeSet → Color) : Prop :=
  ∀ v : V, 2 ≤ zeroIncidentEdgeCount G x v →
    ∃ f ∈ moveSupports, f ∈ D.rotation.internalFaces ∧
      ∃ g : Color,
        g ≠ 0 ∧
          (∃ e ∈ f, e ∈ incidentEdgeFinset G v ∧ x e = 0) ∧
            ∀ e ∈ f, x e ≠ g

/-- Kempe-cycle candidates are Kirchhoff-neutral candidates. -/
theorem everyClusteredZeroVertexHasNeutralD0Candidate_of_kempeD0Candidate
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hcandidate : EveryClusteredZeroVertexHasKempeD0Candidate G moveSupports x) :
    EveryClusteredZeroVertexHasNeutralD0Candidate G moveSupports x := by
  intro v hv
  rcases hcandidate v hv with
    ⟨C, hCmem, α, β, g, hg, hC, heraseAt, hnew⟩
  exact ⟨C, hCmem, g, hg,
    isKirchhoffNeutralMoveSupport_of_isKempeCycle hC,
    heraseAt, hnew⟩

/-- Rotation-disk internal-face candidates are Kirchhoff-neutral candidates. -/
theorem everyClusteredZeroVertexHasNeutralD0Candidate_of_rotationDiskD0Candidate
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    (D : RotationDiskData V G.edgeSet)
    (hincident : ∀ v : V, D.asZeroBoundary.incident v = incidentEdgeFinset G v)
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hcandidate :
      EveryClusteredZeroVertexHasRotationDiskD0Candidate G D moveSupports x) :
    EveryClusteredZeroVertexHasNeutralD0Candidate G moveSupports x := by
  intro v hv
  rcases hcandidate v hv with ⟨f, hfmem, hf, g, hg, heraseAt, hnew⟩
  exact ⟨f, hfmem, g, hg,
    isKirchhoffNeutralMoveSupport_of_rotationDiskData_internalFace
      D hincident hf,
    heraseAt, hnew⟩

/-- Diagnostic form of the two-step route: if clustered zeros survive at a
`D₀` local minimum despite first-step neutral candidates, then one of the
candidate moves exposes a cubic basic-color obstruction with no vertex-local
zero-erasing/no-new-zero repair. -/
theorem
    exists_unrepaired_hasCubicD0BasicColorObstructionAt_of_isD0LocalMinimumForMoveSupports_of_hasClusteredZeroVertex_and_neutral_candidates
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hcluster : HasClusteredZeroVertex G x)
    (hcandidate : EveryClusteredZeroVertexHasNeutralD0Candidate G moveSupports x) :
    ∃ (C : Finset G.edgeSet) (w : V) (g : Color),
      HasCubicD0BasicColorObstructionAt G x C w g ∧
        ¬ HasD0DescentRepairAt G moveSupports x w := by
  rcases hcluster with ⟨v, hvcluster⟩
  rcases hcandidate v hvcluster with
    ⟨C, hCmem, g, hg, hC, heraseAt, hnew⟩
  rcases
    exists_hasCubicD0BasicColorObstructionAt_of_isD0LocalMinimumForMoveSupports_kirchhoffNeutral_erases_incident_zero_creates_no_zero
      hcard hmin hCmem hg hC heraseAt hnew with
    ⟨w, hobst⟩
  exact ⟨C, w, g, hobst,
    not_hasD0DescentRepairAt_of_isD0LocalMinimumForMoveSupports hmin⟩

/-- Concrete-star diagnostic form of the two-step route: a surviving clustered
zero at a `D₀` local minimum with first-step neutral candidates exposes an
unrepaired three-edge cubic obstruction star.  This is the local object that
the remaining finite repair/refutation analysis must eliminate. -/
theorem
    exists_unrepaired_cubic_star_of_isD0LocalMinimumForMoveSupports_of_hasClusteredZeroVertex_and_neutral_candidates
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hcluster : HasClusteredZeroVertex G x)
    (hcandidate : EveryClusteredZeroVertexHasNeutralD0Candidate G moveSupports x) :
    ∃ (C : Finset G.edgeSet) (w : V) (g : Color) (e₁ e₂ e₀ : G.edgeSet),
      e₁ ≠ e₂ ∧ e₁ ≠ e₀ ∧ e₂ ≠ e₀ ∧
        incidentEdgeFinset G w = {e₁, e₂, e₀} ∧
          e₁ ∈ C ∧ e₂ ∈ C ∧ e₀ ∉ C ∧
            x e₁ = g ∧ x e₂ = g ∧ x e₀ = 0 ∧
              ¬ HasD0DescentRepairAt G moveSupports x w := by
  rcases
    exists_unrepaired_hasCubicD0BasicColorObstructionAt_of_isD0LocalMinimumForMoveSupports_of_hasClusteredZeroVertex_and_neutral_candidates
      hcard hmin hcluster hcandidate with
    ⟨C, w, g, hobst, hnorepair⟩
  rcases
    exists_incidentEdgeFinset_eq_support_pair_insert_outside_zero_of_hasCubicD0BasicColorObstructionAt
      (hcard w) hobst with
    ⟨e₁, e₂, e₀, h12, h10, h20, hstar, he₁C, he₂C, he₀C, hx₁,
      hx₂, hx₀⟩
  exact ⟨C, w, g, e₁, e₂, e₀, h12, h10, h20, hstar, he₁C, he₂C,
    he₀C, hx₁, hx₂, hx₀, hnorepair⟩

/-- Numeric form of the diagnostic obstruction theorem. -/
theorem
    exists_unrepaired_hasCubicD0BasicColorObstructionAt_of_isD0LocalMinimumForMoveSupports_of_zeroClusteringCount_pos_and_neutral_candidates
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hCpos : 0 < zeroClusteringCount G x)
    (hcandidate : EveryClusteredZeroVertexHasNeutralD0Candidate G moveSupports x) :
    ∃ (C : Finset G.edgeSet) (w : V) (g : Color),
      HasCubicD0BasicColorObstructionAt G x C w g ∧
        ¬ HasD0DescentRepairAt G moveSupports x w :=
  exists_unrepaired_hasCubicD0BasicColorObstructionAt_of_isD0LocalMinimumForMoveSupports_of_hasClusteredZeroVertex_and_neutral_candidates
    hcard hmin ((zeroClusteringCount_pos_iff_hasClusteredZeroVertex).mp hCpos)
    hcandidate

/-- Kempe-cycle source form of the diagnostic obstruction theorem. -/
theorem
    exists_unrepaired_hasCubicD0BasicColorObstructionAt_of_isD0LocalMinimumForMoveSupports_of_hasClusteredZeroVertex_and_kempe_candidates
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hcluster : HasClusteredZeroVertex G x)
    (hcandidate : EveryClusteredZeroVertexHasKempeD0Candidate G moveSupports x) :
    ∃ (C : Finset G.edgeSet) (w : V) (g : Color),
      HasCubicD0BasicColorObstructionAt G x C w g ∧
        ¬ HasD0DescentRepairAt G moveSupports x w :=
  exists_unrepaired_hasCubicD0BasicColorObstructionAt_of_isD0LocalMinimumForMoveSupports_of_hasClusteredZeroVertex_and_neutral_candidates
    hcard hmin hcluster
    (everyClusteredZeroVertexHasNeutralD0Candidate_of_kempeD0Candidate
      hcandidate)

/-- Rotation-disk source form of the diagnostic obstruction theorem. -/
theorem
    exists_unrepaired_hasCubicD0BasicColorObstructionAt_of_isD0LocalMinimumForMoveSupports_of_hasClusteredZeroVertex_and_rotationDisk_candidates
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    (D : RotationDiskData V G.edgeSet)
    (hincident : ∀ v : V, D.asZeroBoundary.incident v = incidentEdgeFinset G v)
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hcluster : HasClusteredZeroVertex G x)
    (hcandidate :
      EveryClusteredZeroVertexHasRotationDiskD0Candidate G D moveSupports x) :
    ∃ (C : Finset G.edgeSet) (w : V) (g : Color),
      HasCubicD0BasicColorObstructionAt G x C w g ∧
        ¬ HasD0DescentRepairAt G moveSupports x w :=
  exists_unrepaired_hasCubicD0BasicColorObstructionAt_of_isD0LocalMinimumForMoveSupports_of_hasClusteredZeroVertex_and_neutral_candidates
    hcard hmin hcluster
    (everyClusteredZeroVertexHasNeutralD0Candidate_of_rotationDiskD0Candidate
      D hincident hcandidate)

/-- A `D₀` local minimum cannot contain a repairable cubic basic-color
obstruction.  This is the precise second-step obligation exposed by the
forced-zero analysis. -/
theorem
    not_exists_hasCubicD0BasicColorObstructionAt_of_isD0LocalMinimumForMoveSupports_of_cubicObstruction_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hrepair : EveryCubicD0BasicColorObstructionHasD0Descent G moveSupports x) :
    ¬ ∃ (C : Finset G.edgeSet) (v : V) (g : Color),
      HasCubicD0BasicColorObstructionAt G x C v g := by
  rintro ⟨C, v, g, hobst⟩
  exact (not_hasD0DescentRepairAt_of_isD0LocalMinimumForMoveSupports
    (v := v) hmin) (hrepair C v g hobst)

/-- If every cubic basic-color obstruction has a second-step repair, then a
neutral support at a `D₀` local minimum cannot erase an incident zero while
creating no new zero.  Otherwise the first step leaves exactly such a repairable
cubic obstruction. -/
theorem
    not_exists_kirchhoffNeutral_erases_incident_zero_creates_no_zero_of_isD0LocalMinimumForMoveSupports_of_cubicObstruction_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hrepair : EveryCubicD0BasicColorObstructionHasD0Descent G moveSupports x) :
    ¬ ∃ C ∈ moveSupports, ∃ g : Color, ∃ v : V,
      g ≠ 0 ∧ IsKirchhoffNeutralMoveSupport G C ∧
        (∃ e ∈ C, e ∈ incidentEdgeFinset G v ∧ x e = 0) ∧
          ∀ e ∈ C, x e ≠ g := by
  rintro ⟨C, hCmem, g, v, hg, hC, heraseAt, hnew⟩
  rcases
    exists_hasCubicD0BasicColorObstructionAt_of_isD0LocalMinimumForMoveSupports_kirchhoffNeutral_erases_incident_zero_creates_no_zero
      hcard hmin hCmem hg hC heraseAt hnew with ⟨w, hobst⟩
  exact (not_exists_hasCubicD0BasicColorObstructionAt_of_isD0LocalMinimumForMoveSupports_of_cubicObstruction_descent
    hmin hrepair) ⟨C, w, g, hobst⟩

/-- Kempe-cycle version of the second-step obstruction theorem. -/
theorem
    not_exists_isKempeCycle_erases_incident_zero_creates_no_zero_of_isD0LocalMinimumForMoveSupports_of_cubicObstruction_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hrepair : EveryCubicD0BasicColorObstructionHasD0Descent G moveSupports x) :
    ¬ ∃ C ∈ moveSupports, ∃ α β g : Color, ∃ v : V,
      g ≠ 0 ∧ IsKempeCycle (incidentEdgeFinset G) x C α β ∧
        (∃ e ∈ C, e ∈ incidentEdgeFinset G v ∧ x e = 0) ∧
          ∀ e ∈ C, x e ≠ g := by
  intro hbad
  apply
    not_exists_kirchhoffNeutral_erases_incident_zero_creates_no_zero_of_isD0LocalMinimumForMoveSupports_of_cubicObstruction_descent
      hcard hmin hrepair
  rcases hbad with ⟨C, hCmem, α, β, g, v, hg, hC, heraseAt, hnew⟩
  exact ⟨C, hCmem, g, v, hg,
    isKirchhoffNeutralMoveSupport_of_isKempeCycle hC, heraseAt, hnew⟩

/-- Rotation-disk internal-face version of the second-step obstruction theorem. -/
theorem
    not_exists_rotationDiskData_internalFace_erases_incident_zero_creates_no_zero_of_isD0LocalMinimumForMoveSupports_of_cubicObstruction_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    (D : RotationDiskData V G.edgeSet)
    (hincident : ∀ v : V, D.asZeroBoundary.incident v = incidentEdgeFinset G v)
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hrepair : EveryCubicD0BasicColorObstructionHasD0Descent G moveSupports x) :
    ¬ ∃ f ∈ moveSupports, f ∈ D.rotation.internalFaces ∧
      ∃ g : Color, ∃ v : V,
        g ≠ 0 ∧
          (∃ e ∈ f, e ∈ incidentEdgeFinset G v ∧ x e = 0) ∧
            ∀ e ∈ f, x e ≠ g := by
  intro hbad
  apply
    not_exists_kirchhoffNeutral_erases_incident_zero_creates_no_zero_of_isD0LocalMinimumForMoveSupports_of_cubicObstruction_descent
      hcard hmin hrepair
  rcases hbad with ⟨f, hfmem, hf, g, v, hg, heraseAt, hnew⟩
  exact ⟨f, hfmem, g, v, hg,
    isKirchhoffNeutralMoveSupport_of_rotationDiskData_internalFace
      D hincident hf,
    heraseAt, hnew⟩

/-- Two-step matching-zero route: first-step neutral candidates at clustered
vertices, plus second-step repairs for the cubic obstructions they can leave
behind, exclude clustered zero vertices at a `D₀` local minimum. -/
theorem
    not_hasClusteredZeroVertex_of_isD0LocalMinimumForMoveSupports_of_neutral_candidates_and_cubicObstruction_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hcandidate : EveryClusteredZeroVertexHasNeutralD0Candidate G moveSupports x)
    (hrepair : EveryCubicD0BasicColorObstructionHasD0Descent G moveSupports x) :
    ¬ HasClusteredZeroVertex G x := by
  rintro ⟨v, hvcluster⟩
  rcases hcandidate v hvcluster with
    ⟨C, hCmem, g, hg, hC, heraseAt, hnew⟩
  exact
    (not_exists_kirchhoffNeutral_erases_incident_zero_creates_no_zero_of_isD0LocalMinimumForMoveSupports_of_cubicObstruction_descent
      hcard hmin hrepair)
      ⟨C, hCmem, g, v, hg, hC, heraseAt, hnew⟩

/-- Star-checkable form of the two-step route: first-step neutral candidates
plus repairs for every concrete cubic obstruction star exclude clustered zeros
at a `D₀` local minimum. -/
theorem
    not_hasClusteredZeroVertex_of_isD0LocalMinimumForMoveSupports_of_neutral_candidates_and_cubic_star_repairs
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hcandidate : EveryClusteredZeroVertexHasNeutralD0Candidate G moveSupports x)
    (hrepair :
      EveryCubicD0BasicColorObstructionStarHasD0Descent G moveSupports x) :
    ¬ HasClusteredZeroVertex G x :=
  not_hasClusteredZeroVertex_of_isD0LocalMinimumForMoveSupports_of_neutral_candidates_and_cubicObstruction_descent
    hcard hmin hcandidate
    (everyCubicD0BasicColorObstructionHasD0Descent_of_cubic_star_repairs
      hcard hrepair)

/-- Matching-zero form of the two-step neutral-candidate route. -/
theorem
    zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_neutral_candidates_and_cubicObstruction_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hcandidate : EveryClusteredZeroVertexHasNeutralD0Candidate G moveSupports x)
    (hrepair : EveryCubicD0BasicColorObstructionHasD0Descent G moveSupports x) :
    ZeroEdgesFormMatching G x :=
  zeroEdgesFormMatching_iff_not_hasClusteredZeroVertex.mpr
    (not_hasClusteredZeroVertex_of_isD0LocalMinimumForMoveSupports_of_neutral_candidates_and_cubicObstruction_descent
      hcard hmin hcandidate hrepair)

/-- Matching-zero form with the remaining second-step obligation reduced to
concrete cubic star repairs. -/
theorem
    zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_neutral_candidates_and_cubic_star_repairs
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hcandidate : EveryClusteredZeroVertexHasNeutralD0Candidate G moveSupports x)
    (hrepair :
      EveryCubicD0BasicColorObstructionStarHasD0Descent G moveSupports x) :
    ZeroEdgesFormMatching G x :=
  zeroEdgesFormMatching_iff_not_hasClusteredZeroVertex.mpr
    (not_hasClusteredZeroVertex_of_isD0LocalMinimumForMoveSupports_of_neutral_candidates_and_cubic_star_repairs
      hcard hmin hcandidate hrepair)

/-- Kempe-cycle source form with the second-step obligation reduced to concrete
cubic star repairs. -/
theorem
    zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_kempe_candidates_and_cubic_star_repairs
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hcandidate : EveryClusteredZeroVertexHasKempeD0Candidate G moveSupports x)
    (hrepair :
      EveryCubicD0BasicColorObstructionStarHasD0Descent G moveSupports x) :
    ZeroEdgesFormMatching G x :=
  zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_neutral_candidates_and_cubic_star_repairs
    hcard hmin
    (everyClusteredZeroVertexHasNeutralD0Candidate_of_kempeD0Candidate
      hcandidate)
    hrepair

/-- Rotation-disk internal-face source form with the second-step obligation
reduced to concrete cubic star repairs. -/
theorem
    zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_rotationDisk_candidates_and_cubic_star_repairs
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    (D : RotationDiskData V G.edgeSet)
    (hincident : ∀ v : V, D.asZeroBoundary.incident v = incidentEdgeFinset G v)
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hcandidate :
      EveryClusteredZeroVertexHasRotationDiskD0Candidate G D moveSupports x)
    (hrepair :
      EveryCubicD0BasicColorObstructionStarHasD0Descent G moveSupports x) :
    ZeroEdgesFormMatching G x :=
  zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_neutral_candidates_and_cubic_star_repairs
    hcard hmin
    (everyClusteredZeroVertexHasNeutralD0Candidate_of_rotationDiskD0Candidate
      D hincident hcandidate)
    hrepair

/-- Kempe-cycle source form of the two-step matching-zero route. -/
theorem
    zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_kempe_candidates_and_cubicObstruction_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hcandidate : EveryClusteredZeroVertexHasKempeD0Candidate G moveSupports x)
    (hrepair : EveryCubicD0BasicColorObstructionHasD0Descent G moveSupports x) :
    ZeroEdgesFormMatching G x :=
  zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_neutral_candidates_and_cubicObstruction_descent
    hcard hmin
    (everyClusteredZeroVertexHasNeutralD0Candidate_of_kempeD0Candidate
      hcandidate)
    hrepair

/-- Rotation-disk internal-face source form of the two-step matching-zero route. -/
theorem
    zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_rotationDisk_candidates_and_cubicObstruction_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    (D : RotationDiskData V G.edgeSet)
    (hincident : ∀ v : V, D.asZeroBoundary.incident v = incidentEdgeFinset G v)
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hcandidate :
      EveryClusteredZeroVertexHasRotationDiskD0Candidate G D moveSupports x)
    (hrepair : EveryCubicD0BasicColorObstructionHasD0Descent G moveSupports x) :
    ZeroEdgesFormMatching G x :=
  zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_neutral_candidates_and_cubicObstruction_descent
    hcard hmin
    (everyClusteredZeroVertexHasNeutralD0Candidate_of_rotationDiskD0Candidate
      D hincident hcandidate)
    hrepair

/-- Refutation-facing form of the two-step route: a state with clustered zero
support cannot be a `D₀` local minimum once every clustered vertex has a
first-step neutral candidate and every cubic obstruction left by such a
candidate has a second-step repair. -/
theorem
    not_isD0LocalMinimumForMoveSupports_of_hasClusteredZeroVertex_and_neutral_candidates_and_cubicObstruction_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hcluster : HasClusteredZeroVertex G x)
    (hcandidate : EveryClusteredZeroVertexHasNeutralD0Candidate G moveSupports x)
    (hrepair : EveryCubicD0BasicColorObstructionHasD0Descent G moveSupports x) :
    ¬ IsD0LocalMinimumForMoveSupports G moveSupports x := by
  intro hmin
  exact
    (not_hasClusteredZeroVertex_of_isD0LocalMinimumForMoveSupports_of_neutral_candidates_and_cubicObstruction_descent
      hcard hmin hcandidate hrepair) hcluster

/-- Numeric refutation-facing form of the two-step route: positive zero
clustering rules out `D₀` local minimality under the neutral-candidate plus
cubic-obstruction repair hypotheses. -/
theorem
    not_isD0LocalMinimumForMoveSupports_of_zeroClusteringCount_pos_and_neutral_candidates_and_cubicObstruction_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hCpos : 0 < zeroClusteringCount G x)
    (hcandidate : EveryClusteredZeroVertexHasNeutralD0Candidate G moveSupports x)
    (hrepair : EveryCubicD0BasicColorObstructionHasD0Descent G moveSupports x) :
    ¬ IsD0LocalMinimumForMoveSupports G moveSupports x :=
  not_isD0LocalMinimumForMoveSupports_of_hasClusteredZeroVertex_and_neutral_candidates_and_cubicObstruction_descent
    hcard ((zeroClusteringCount_pos_iff_hasClusteredZeroVertex).mp hCpos)
    hcandidate hrepair

/-- Kempe-cycle source form of the two-step local-minimum refutation. -/
theorem
    not_isD0LocalMinimumForMoveSupports_of_hasClusteredZeroVertex_and_kempe_candidates_and_cubicObstruction_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hcluster : HasClusteredZeroVertex G x)
    (hcandidate : EveryClusteredZeroVertexHasKempeD0Candidate G moveSupports x)
    (hrepair : EveryCubicD0BasicColorObstructionHasD0Descent G moveSupports x) :
    ¬ IsD0LocalMinimumForMoveSupports G moveSupports x :=
  not_isD0LocalMinimumForMoveSupports_of_hasClusteredZeroVertex_and_neutral_candidates_and_cubicObstruction_descent
    hcard hcluster
    (everyClusteredZeroVertexHasNeutralD0Candidate_of_kempeD0Candidate
      hcandidate)
    hrepair

/-- Kempe-cycle source form with the manuscript statistic `C(x)>0`. -/
theorem
    not_isD0LocalMinimumForMoveSupports_of_zeroClusteringCount_pos_and_kempe_candidates_and_cubicObstruction_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hCpos : 0 < zeroClusteringCount G x)
    (hcandidate : EveryClusteredZeroVertexHasKempeD0Candidate G moveSupports x)
    (hrepair : EveryCubicD0BasicColorObstructionHasD0Descent G moveSupports x) :
    ¬ IsD0LocalMinimumForMoveSupports G moveSupports x :=
  not_isD0LocalMinimumForMoveSupports_of_zeroClusteringCount_pos_and_neutral_candidates_and_cubicObstruction_descent
    hcard hCpos
    (everyClusteredZeroVertexHasNeutralD0Candidate_of_kempeD0Candidate
      hcandidate)
    hrepair

/-- Rotation-disk source form of the two-step local-minimum refutation. -/
theorem
    not_isD0LocalMinimumForMoveSupports_of_hasClusteredZeroVertex_and_rotationDisk_candidates_and_cubicObstruction_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    (D : RotationDiskData V G.edgeSet)
    (hincident : ∀ v : V, D.asZeroBoundary.incident v = incidentEdgeFinset G v)
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hcluster : HasClusteredZeroVertex G x)
    (hcandidate :
      EveryClusteredZeroVertexHasRotationDiskD0Candidate G D moveSupports x)
    (hrepair : EveryCubicD0BasicColorObstructionHasD0Descent G moveSupports x) :
    ¬ IsD0LocalMinimumForMoveSupports G moveSupports x :=
  not_isD0LocalMinimumForMoveSupports_of_hasClusteredZeroVertex_and_neutral_candidates_and_cubicObstruction_descent
    hcard hcluster
    (everyClusteredZeroVertexHasNeutralD0Candidate_of_rotationDiskD0Candidate
      D hincident hcandidate)
    hrepair

/-- Rotation-disk source form with the manuscript statistic `C(x)>0`. -/
theorem
    not_isD0LocalMinimumForMoveSupports_of_zeroClusteringCount_pos_and_rotationDisk_candidates_and_cubicObstruction_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    (D : RotationDiskData V G.edgeSet)
    (hincident : ∀ v : V, D.asZeroBoundary.incident v = incidentEdgeFinset G v)
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hCpos : 0 < zeroClusteringCount G x)
    (hcandidate :
      EveryClusteredZeroVertexHasRotationDiskD0Candidate G D moveSupports x)
    (hrepair : EveryCubicD0BasicColorObstructionHasD0Descent G moveSupports x) :
    ¬ IsD0LocalMinimumForMoveSupports G moveSupports x :=
  not_isD0LocalMinimumForMoveSupports_of_zeroClusteringCount_pos_and_neutral_candidates_and_cubicObstruction_descent
    hcard hCpos
    (everyClusteredZeroVertexHasNeutralD0Candidate_of_rotationDiskD0Candidate
      D hincident hcandidate)
    hrepair

/-- The vertex-local repair hypothesis implies the global nonmatching repair
hypothesis, because every nonmatching zero pattern has a clustered zero
vertex. -/
theorem everyNonmatchingZeroPatternHasD0Descent_of_clusteredZeroVertex_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hrepair : EveryClusteredZeroVertexHasD0Descent G moveSupports x) :
    EveryNonmatchingZeroPatternHasD0Descent G moveSupports x := by
  intro hnonmatch
  rcases not_zeroEdgesFormMatching_iff_hasClusteredZeroVertex.mp hnonmatch with
    ⟨v, hvcluster⟩
  exact hasD0DescentRepair_of_hasD0DescentRepairAt (hrepair v hvcluster)

/-- Abstract matching-zeros theorem: once patch-local combinatorics supplies a
zero-erasing/no-new-zero repair for every non-matching zero pattern, `D₀`
local minimality forces the zero pattern to be a matching. -/
theorem zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_nonmatching_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hrepair : EveryNonmatchingZeroPatternHasD0Descent G moveSupports x) :
    ZeroEdgesFormMatching G x := by
  by_contra hnonmatch
  exact (not_hasD0DescentRepair_of_isD0LocalMinimumForMoveSupports hmin)
    (hrepair hnonmatch)

/-- Vertex-local form of the abstract matching-zeros theorem.  This is the
form closest to the manuscript's local-neighborhood phrasing: if every vertex
with two incident zero edges admits a zero-erasing/no-new-zero repair, then a
`D₀` local minimum has matching zero support. -/
theorem zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_clusteredZeroVertex_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hrepair : EveryClusteredZeroVertexHasD0Descent G moveSupports x) :
    ZeroEdgesFormMatching G x :=
  zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_nonmatching_descent
    hmin (everyNonmatchingZeroPatternHasD0Descent_of_clusteredZeroVertex_descent
      hrepair)

/-- Kirchhoff-neutral form of the matching-zero theorem: if every clustered-zero
vertex has a concrete zero-erasing/no-new-zero neutral support repair, then
every `D₀` local minimum has matching zero support. -/
theorem
    zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_kirchhoffNeutral_vertex_repairs
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hrepair :
      ∀ v : V, 2 ≤ zeroIncidentEdgeCount G x v →
        ∃ C ∈ moveSupports, ∃ g : Color,
          g ≠ 0 ∧
            IsKirchhoffNeutralMoveSupport G C ∧
              (∀ w : V, ∃ e ∈ incidentEdgeFinset G w,
                if e ∈ C then x e ≠ g else x e ≠ 0) ∧
                (∃ e ∈ C, e ∈ incidentEdgeFinset G v ∧ x e = 0) ∧
                  ∀ e ∈ C, x e ≠ g) :
    ZeroEdgesFormMatching G x :=
  zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_clusteredZeroVertex_descent
    hmin
    (everyClusteredZeroVertexHasD0Descent_of_kirchhoffNeutral_vertex_repairs
      hmin.source_flow hrepair)

/-- Kempe-cycle form of the matching-zero theorem: if every clustered-zero
vertex has a concrete zero-erasing/no-new-zero Kempe repair, then every `D₀`
local minimum has matching zero support. -/
theorem zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_kempeCycle_vertex_repairs
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hrepair :
      ∀ v : V, 2 ≤ zeroIncidentEdgeCount G x v →
        ∃ C ∈ moveSupports, ∃ α β g : Color,
          g ≠ 0 ∧
            IsKempeCycle (incidentEdgeFinset G) x C α β ∧
              (∀ w : V, ∃ e ∈ incidentEdgeFinset G w,
                if e ∈ C then x e ≠ g else x e ≠ 0) ∧
                (∃ e ∈ C, e ∈ incidentEdgeFinset G v ∧ x e = 0) ∧
                  ∀ e ∈ C, x e ≠ g) :
    ZeroEdgesFormMatching G x :=
  zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_clusteredZeroVertex_descent
    hmin
    (everyClusteredZeroVertexHasD0Descent_of_kempeCycle_vertex_repairs
      hmin.source_flow hrepair)

/-- Rotation-disk internal-face form of the matching-zero theorem.  This is the
same repair principle phrased in the patch/face language used by the v23 route. -/
theorem
    zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_rotationDiskData_internalFace_repairs
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    (D : RotationDiskData V G.edgeSet)
    (hincident : ∀ v : V, D.asZeroBoundary.incident v = incidentEdgeFinset G v)
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hrepair :
      ∀ v : V, 2 ≤ zeroIncidentEdgeCount G x v →
        ∃ f ∈ moveSupports, f ∈ D.rotation.internalFaces ∧
          ∃ g : Color,
            g ≠ 0 ∧
              (∀ w : V, ∃ e ∈ incidentEdgeFinset G w,
                if e ∈ f then x e ≠ g else x e ≠ 0) ∧
                (∃ e ∈ f, e ∈ incidentEdgeFinset G v ∧ x e = 0) ∧
                  ∀ e ∈ f, x e ≠ g) :
    ZeroEdgesFormMatching G x :=
  zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_clusteredZeroVertex_descent
    hmin
    (everyClusteredZeroVertexHasD0Descent_of_rotationDiskData_internalFace_repairs
      D hincident hmin.source_flow hrepair)

/-- Vertex-count form of the abstract matching-zeros theorem. -/
theorem zeroIncidentEdgeCount_le_one_of_isD0LocalMinimumForMoveSupports_of_nonmatching_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hrepair : EveryNonmatchingZeroPatternHasD0Descent G moveSupports x)
    (v : V) :
    zeroIncidentEdgeCount G x v ≤ 1 :=
  (zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_nonmatching_descent
    hmin hrepair) v

/-- Vertex-local repair form: each vertex is incident to at most one zero edge
at a repaired `D₀` local minimum. -/
theorem zeroIncidentEdgeCount_le_one_of_isD0LocalMinimumForMoveSupports_of_clusteredZeroVertex_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hrepair : EveryClusteredZeroVertexHasD0Descent G moveSupports x)
    (v : V) :
    zeroIncidentEdgeCount G x v ≤ 1 :=
  (zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_clusteredZeroVertex_descent
    hmin hrepair) v

/-- Case-analysis form of the abstract matching-zeros theorem: each vertex has
zero or one incident zero edge. -/
theorem zeroIncidentEdgeCount_eq_zero_or_eq_one_of_isD0LocalMinimumForMoveSupports_of_nonmatching_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hrepair : EveryNonmatchingZeroPatternHasD0Descent G moveSupports x)
    (v : V) :
    zeroIncidentEdgeCount G x v = 0 ∨ zeroIncidentEdgeCount G x v = 1 := by
  have hle :
      zeroIncidentEdgeCount G x v ≤ 1 :=
    zeroIncidentEdgeCount_le_one_of_isD0LocalMinimumForMoveSupports_of_nonmatching_descent
      hmin hrepair v
  omega

/-- Vertex-local repair form: each vertex has zero or one incident zero edge. -/
theorem zeroIncidentEdgeCount_eq_zero_or_eq_one_of_isD0LocalMinimumForMoveSupports_of_clusteredZeroVertex_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hrepair : EveryClusteredZeroVertexHasD0Descent G moveSupports x)
    (v : V) :
    zeroIncidentEdgeCount G x v = 0 ∨ zeroIncidentEdgeCount G x v = 1 := by
  have hle :
      zeroIncidentEdgeCount G x v ≤ 1 :=
    zeroIncidentEdgeCount_le_one_of_isD0LocalMinimumForMoveSupports_of_clusteredZeroVertex_descent
      hmin hrepair v
  omega

/-- If a repaired `D₀` local minimum has an explicit zero edge incident to a
vertex, then that vertex has exactly one incident zero edge. -/
theorem zeroIncidentEdgeCount_eq_one_of_isD0LocalMinimumForMoveSupports_of_nonmatching_descent_of_exists_incident_zero
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hrepair : EveryNonmatchingZeroPatternHasD0Descent G moveSupports x)
    {v : V} (hzero : ∃ e ∈ incidentEdgeFinset G v, x e = 0) :
    zeroIncidentEdgeCount G x v = 1 :=
  (zeroIncidentEdgeCount_eq_one_iff_exists_incident_zero_of_zeroEdgesFormMatching
    (zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_nonmatching_descent
      hmin hrepair) v).mpr hzero

/-- Vertex-local repair form: an explicit incident zero forces exactly one
incident zero edge at that vertex. -/
theorem zeroIncidentEdgeCount_eq_one_of_isD0LocalMinimumForMoveSupports_of_clusteredZeroVertex_descent_of_exists_incident_zero
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hrepair : EveryClusteredZeroVertexHasD0Descent G moveSupports x)
    {v : V} (hzero : ∃ e ∈ incidentEdgeFinset G v, x e = 0) :
    zeroIncidentEdgeCount G x v = 1 :=
  (zeroIncidentEdgeCount_eq_one_iff_exists_incident_zero_of_zeroEdgesFormMatching
    (zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_clusteredZeroVertex_descent
      hmin hrepair) v).mpr hzero

/-- No-cluster form of the abstract matching-zeros theorem. -/
theorem not_hasClusteredZeroVertex_of_isD0LocalMinimumForMoveSupports_of_nonmatching_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hrepair : EveryNonmatchingZeroPatternHasD0Descent G moveSupports x) :
    ¬ HasClusteredZeroVertex G x :=
  zeroEdgesFormMatching_iff_not_hasClusteredZeroVertex.mp
    (zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_nonmatching_descent
      hmin hrepair)

/-- Vertex-local repair form: repaired `D₀` local minima have no clustered
zero vertices. -/
theorem not_hasClusteredZeroVertex_of_isD0LocalMinimumForMoveSupports_of_clusteredZeroVertex_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hrepair : EveryClusteredZeroVertexHasD0Descent G moveSupports x) :
    ¬ HasClusteredZeroVertex G x :=
  zeroEdgesFormMatching_iff_not_hasClusteredZeroVertex.mp
    (zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_clusteredZeroVertex_descent
      hmin hrepair)

/-- Refutation form: under the vertex-local repair hypothesis, a flow with a
clustered zero vertex cannot be a `D₀` local minimum. -/
theorem not_isD0LocalMinimumForMoveSupports_of_hasClusteredZeroVertex_and_clusteredZeroVertex_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hcluster : HasClusteredZeroVertex G x)
    (hrepair : EveryClusteredZeroVertexHasD0Descent G moveSupports x) :
    ¬ IsD0LocalMinimumForMoveSupports G moveSupports x := by
  intro hmin
  have hmatch :
      ZeroEdgesFormMatching G x :=
    zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_clusteredZeroVertex_descent
      hmin hrepair
  exact (not_zeroEdgesFormMatching_iff_hasClusteredZeroVertex.mpr hcluster) hmatch

/-- Numeric refutation form: under the vertex-local repair hypothesis, positive
clustering excludes `D₀` local minimality. -/
theorem not_isD0LocalMinimumForMoveSupports_of_zeroClusteringCount_pos_and_clusteredZeroVertex_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hCpos : 0 < zeroClusteringCount G x)
    (hrepair : EveryClusteredZeroVertexHasD0Descent G moveSupports x) :
    ¬ IsD0LocalMinimumForMoveSupports G moveSupports x :=
  not_isD0LocalMinimumForMoveSupports_of_hasClusteredZeroVertex_and_clusteredZeroVertex_descent
    ((zeroClusteringCount_pos_iff_hasClusteredZeroVertex).mp hCpos) hrepair

/-- Obstruction form for the global repair hypothesis: a nonmatching `D₀`
local minimum is a counterexample to the manuscript's nonmatching repair
principle. -/
theorem not_everyNonmatchingZeroPatternHasD0Descent_of_isD0LocalMinimumForMoveSupports
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hnonmatch : ¬ ZeroEdgesFormMatching G x) :
    ¬ EveryNonmatchingZeroPatternHasD0Descent G moveSupports x := by
  intro hrepair
  exact (not_hasD0DescentRepair_of_isD0LocalMinimumForMoveSupports hmin)
    (hrepair hnonmatch)

/-- At a `D₀` local minimum, failure of the global nonmatching-repair
hypothesis is equivalent to nonmatching zero support. -/
theorem not_everyNonmatchingZeroPatternHasD0Descent_iff_not_zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x) :
    ¬ EveryNonmatchingZeroPatternHasD0Descent G moveSupports x ↔
      ¬ ZeroEdgesFormMatching G x := by
  constructor
  · intro hnot hmatch
    exact hnot (fun hnonmatch => False.elim (hnonmatch hmatch))
  · exact not_everyNonmatchingZeroPatternHasD0Descent_of_isD0LocalMinimumForMoveSupports
      hmin

/-- At a `D₀` local minimum, the global nonmatching-repair hypothesis is
equivalent to matching zero support. -/
theorem everyNonmatchingZeroPatternHasD0Descent_iff_zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x) :
    EveryNonmatchingZeroPatternHasD0Descent G moveSupports x ↔
      ZeroEdgesFormMatching G x := by
  constructor
  · exact zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_nonmatching_descent
      hmin
  · intro hmatch hnonmatch
    exact False.elim (hnonmatch hmatch)

/-- At a `D₀` local minimum, failure of the global nonmatching-repair
hypothesis is equivalent to the presence of clustered zero support. -/
theorem not_everyNonmatchingZeroPatternHasD0Descent_iff_hasClusteredZeroVertex_of_isD0LocalMinimumForMoveSupports
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x) :
    ¬ EveryNonmatchingZeroPatternHasD0Descent G moveSupports x ↔
      HasClusteredZeroVertex G x :=
  (not_everyNonmatchingZeroPatternHasD0Descent_iff_not_zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports
    hmin).trans not_zeroEdgesFormMatching_iff_hasClusteredZeroVertex

/-- Numeric form: at a `D₀` local minimum, failure of the global
nonmatching-repair hypothesis is equivalent to positive zero clustering. -/
theorem not_everyNonmatchingZeroPatternHasD0Descent_iff_zeroClusteringCount_pos_of_isD0LocalMinimumForMoveSupports
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x) :
    ¬ EveryNonmatchingZeroPatternHasD0Descent G moveSupports x ↔
      0 < zeroClusteringCount G x :=
  (not_everyNonmatchingZeroPatternHasD0Descent_iff_hasClusteredZeroVertex_of_isD0LocalMinimumForMoveSupports
    hmin).trans zeroClusteringCount_pos_iff_hasClusteredZeroVertex.symm

/-- Obstruction form for the vertex-local repair hypothesis: a clustered-zero
`D₀` local minimum is a counterexample to the manuscript's clustered-vertex
repair principle. -/
theorem not_everyClusteredZeroVertexHasD0Descent_of_isD0LocalMinimumForMoveSupports
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hcluster : HasClusteredZeroVertex G x) :
    ¬ EveryClusteredZeroVertexHasD0Descent G moveSupports x := by
  rcases hcluster with ⟨v, hvcluster⟩
  intro hrepair
  exact
    (not_hasD0DescentRepairAt_of_isD0LocalMinimumForMoveSupports
      (v := v) hmin) (hrepair v hvcluster)

/-- Numeric obstruction form for the vertex-local repair hypothesis. -/
theorem not_everyClusteredZeroVertexHasD0Descent_of_isD0LocalMinimumForMoveSupports_of_zeroClusteringCount_pos
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hCpos : 0 < zeroClusteringCount G x) :
    ¬ EveryClusteredZeroVertexHasD0Descent G moveSupports x :=
  not_everyClusteredZeroVertexHasD0Descent_of_isD0LocalMinimumForMoveSupports
    hmin ((zeroClusteringCount_pos_iff_hasClusteredZeroVertex).mp hCpos)

/-- Failure of the vertex-local repair hypothesis is exactly the existence of
a clustered zero vertex where the zero-erasing/no-new-zero repair is absent. -/
theorem not_everyClusteredZeroVertexHasD0Descent_iff_exists_clusteredZeroVertex_without_d0DescentRepair
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color} :
    ¬ EveryClusteredZeroVertexHasD0Descent G moveSupports x ↔
      ∃ v : V, 2 ≤ zeroIncidentEdgeCount G x v ∧
        ¬ HasD0DescentRepairAt G moveSupports x v := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro v hvcluster
    by_contra hnorepair
    exact hnone ⟨v, hvcluster, hnorepair⟩
  · rintro ⟨v, hvcluster, hnorepair⟩ hrepair
    exact hnorepair (hrepair v hvcluster)

/-- At a `D₀` local minimum, failure of the vertex-local repair hypothesis is
equivalent to the presence of clustered zero support. -/
theorem not_everyClusteredZeroVertexHasD0Descent_iff_hasClusteredZeroVertex_of_isD0LocalMinimumForMoveSupports
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x) :
    ¬ EveryClusteredZeroVertexHasD0Descent G moveSupports x ↔
      HasClusteredZeroVertex G x := by
  constructor
  · intro hnot
    rcases
      not_everyClusteredZeroVertexHasD0Descent_iff_exists_clusteredZeroVertex_without_d0DescentRepair.mp
        hnot with
      ⟨v, hvcluster, _hnorepair⟩
    exact ⟨v, hvcluster⟩
  · exact not_everyClusteredZeroVertexHasD0Descent_of_isD0LocalMinimumForMoveSupports hmin

/-- Numeric form: at a `D₀` local minimum, the vertex-local repair hypothesis
fails exactly when the zero-clustering statistic is positive. -/
theorem not_everyClusteredZeroVertexHasD0Descent_iff_zeroClusteringCount_pos_of_isD0LocalMinimumForMoveSupports
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x) :
    ¬ EveryClusteredZeroVertexHasD0Descent G moveSupports x ↔
      0 < zeroClusteringCount G x :=
  (not_everyClusteredZeroVertexHasD0Descent_iff_hasClusteredZeroVertex_of_isD0LocalMinimumForMoveSupports
    hmin).trans zeroClusteringCount_pos_iff_hasClusteredZeroVertex.symm

/-- At a `D₀` local minimum, the vertex-local repair hypothesis is equivalent
to matching zero support. -/
theorem everyClusteredZeroVertexHasD0Descent_iff_zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x) :
    EveryClusteredZeroVertexHasD0Descent G moveSupports x ↔
      ZeroEdgesFormMatching G x := by
  constructor
  · exact zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_clusteredZeroVertex_descent
      hmin
  · intro hmatch v hvcluster
    exact False.elim
      ((zeroEdgesFormMatching_iff_not_hasClusteredZeroVertex.mp hmatch)
        ⟨v, hvcluster⟩)

/-- Obstruction form at a chosen clustered zero vertex: a `D₀` local minimum
cannot have the zero-erasing/no-new-zero repair used by the matching-zero
descent theorem available at that vertex. -/
theorem not_exists_d0DescentRepair_at_clusteredZeroVertex_of_isD0LocalMinimumForMoveSupports
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color} {v : V}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (_hvcluster : 2 ≤ zeroIncidentEdgeCount G x v) :
    ¬ HasD0DescentRepairAt G moveSupports x v :=
  not_hasD0DescentRepairAt_of_isD0LocalMinimumForMoveSupports hmin

/-- Manuscript-facing obstruction form: if a `D₀` local minimum has clustered
zeros, then some clustered vertex has no zero-erasing/no-new-zero repair in the
selected move family. -/
theorem exists_clusteredZeroVertex_without_d0DescentRepair_of_isD0LocalMinimumForMoveSupports
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hcluster : HasClusteredZeroVertex G x) :
    ∃ v : V, 2 ≤ zeroIncidentEdgeCount G x v ∧
      ¬ HasD0DescentRepairAt G moveSupports x v := by
  rcases hcluster with ⟨v, hvcluster⟩
  exact
    ⟨v, hvcluster,
      not_exists_d0DescentRepair_at_clusteredZeroVertex_of_isD0LocalMinimumForMoveSupports
        hmin hvcluster⟩

/-- Numeric obstruction form: positive clustering at a `D₀` local minimum
exhibits a clustered vertex where the zero-erasing/no-new-zero repair fails. -/
theorem exists_clusteredZeroVertex_without_d0DescentRepair_of_isD0LocalMinimumForMoveSupports_of_zeroClusteringCount_pos
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hCpos : 0 < zeroClusteringCount G x) :
    ∃ v : V, 2 ≤ zeroIncidentEdgeCount G x v ∧
      ¬ HasD0DescentRepairAt G moveSupports x v :=
  exists_clusteredZeroVertex_without_d0DescentRepair_of_isD0LocalMinimumForMoveSupports
    hmin ((zeroClusteringCount_pos_iff_hasClusteredZeroVertex).mp hCpos)

/-- Count form of the abstract matching-zeros theorem: the clustering statistic
vanishes at repaired `D₀` local minima. -/
theorem zeroClusteringCount_eq_zero_of_isD0LocalMinimumForMoveSupports_of_nonmatching_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hrepair : EveryNonmatchingZeroPatternHasD0Descent G moveSupports x) :
    zeroClusteringCount G x = 0 :=
  zeroClusteringCount_eq_zero_iff_zeroEdgesFormMatching.mpr
    (zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_nonmatching_descent
      hmin hrepair)

/-- Vertex-local repair form: clustering vanishes at `D₀` local minima. -/
theorem zeroClusteringCount_eq_zero_of_isD0LocalMinimumForMoveSupports_of_clusteredZeroVertex_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hrepair : EveryClusteredZeroVertexHasD0Descent G moveSupports x) :
    zeroClusteringCount G x = 0 :=
  zeroClusteringCount_eq_zero_iff_zeroEdgesFormMatching.mpr
    (zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_clusteredZeroVertex_descent
      hmin hrepair)

/-- Concrete neutral-repair form of the manuscript clustering identity `C(x)=0`. -/
theorem
    zeroClusteringCount_eq_zero_of_isD0LocalMinimumForMoveSupports_of_kirchhoffNeutral_vertex_repairs
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hrepair :
      ∀ v : V, 2 ≤ zeroIncidentEdgeCount G x v →
        ∃ C ∈ moveSupports, ∃ g : Color,
          g ≠ 0 ∧
            IsKirchhoffNeutralMoveSupport G C ∧
              (∀ w : V, ∃ e ∈ incidentEdgeFinset G w,
                if e ∈ C then x e ≠ g else x e ≠ 0) ∧
                (∃ e ∈ C, e ∈ incidentEdgeFinset G v ∧ x e = 0) ∧
                  ∀ e ∈ C, x e ≠ g) :
    zeroClusteringCount G x = 0 :=
  zeroClusteringCount_eq_zero_iff_zeroEdgesFormMatching.mpr
    (zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_kirchhoffNeutral_vertex_repairs
      hmin hrepair)

/-- Two-step neutral-candidate form of the manuscript clustering identity
`C(x)=0`. -/
theorem
    zeroClusteringCount_eq_zero_of_isD0LocalMinimumForMoveSupports_of_neutral_candidates_and_cubicObstruction_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hcandidate : EveryClusteredZeroVertexHasNeutralD0Candidate G moveSupports x)
    (hrepair : EveryCubicD0BasicColorObstructionHasD0Descent G moveSupports x) :
    zeroClusteringCount G x = 0 :=
  zeroClusteringCount_eq_zero_iff_zeroEdgesFormMatching.mpr
    (zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_neutral_candidates_and_cubicObstruction_descent
      hcard hmin hcandidate hrepair)

/-- Kempe-cycle source form of the two-step clustering identity. -/
theorem
    zeroClusteringCount_eq_zero_of_isD0LocalMinimumForMoveSupports_of_kempe_candidates_and_cubicObstruction_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hcandidate : EveryClusteredZeroVertexHasKempeD0Candidate G moveSupports x)
    (hrepair : EveryCubicD0BasicColorObstructionHasD0Descent G moveSupports x) :
    zeroClusteringCount G x = 0 :=
  zeroClusteringCount_eq_zero_iff_zeroEdgesFormMatching.mpr
    (zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_kempe_candidates_and_cubicObstruction_descent
      hcard hmin hcandidate hrepair)

/-- Rotation-disk source form of the two-step clustering identity. -/
theorem
    zeroClusteringCount_eq_zero_of_isD0LocalMinimumForMoveSupports_of_rotationDisk_candidates_and_cubicObstruction_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    (D : RotationDiskData V G.edgeSet)
    (hincident : ∀ v : V, D.asZeroBoundary.incident v = incidentEdgeFinset G v)
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hcandidate :
      EveryClusteredZeroVertexHasRotationDiskD0Candidate G D moveSupports x)
    (hrepair : EveryCubicD0BasicColorObstructionHasD0Descent G moveSupports x) :
    zeroClusteringCount G x = 0 :=
  zeroClusteringCount_eq_zero_iff_zeroEdgesFormMatching.mpr
    (zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_rotationDisk_candidates_and_cubicObstruction_descent
      D hincident hcard hmin hcandidate hrepair)

/-- Star-repair form of the manuscript clustering identity `C(x)=0`. -/
theorem
    zeroClusteringCount_eq_zero_of_isD0LocalMinimumForMoveSupports_of_neutral_candidates_and_cubic_star_repairs
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hcandidate : EveryClusteredZeroVertexHasNeutralD0Candidate G moveSupports x)
    (hrepair :
      EveryCubicD0BasicColorObstructionStarHasD0Descent G moveSupports x) :
    zeroClusteringCount G x = 0 :=
  zeroClusteringCount_eq_zero_iff_zeroEdgesFormMatching.mpr
    (zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_neutral_candidates_and_cubic_star_repairs
      hcard hmin hcandidate hrepair)

/-- Kempe-cycle source form of the star-repair clustering identity. -/
theorem
    zeroClusteringCount_eq_zero_of_isD0LocalMinimumForMoveSupports_of_kempe_candidates_and_cubic_star_repairs
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hcandidate : EveryClusteredZeroVertexHasKempeD0Candidate G moveSupports x)
    (hrepair :
      EveryCubicD0BasicColorObstructionStarHasD0Descent G moveSupports x) :
    zeroClusteringCount G x = 0 :=
  zeroClusteringCount_eq_zero_iff_zeroEdgesFormMatching.mpr
    (zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_kempe_candidates_and_cubic_star_repairs
      hcard hmin hcandidate hrepair)

/-- Rotation-disk source form of the star-repair clustering identity. -/
theorem
    zeroClusteringCount_eq_zero_of_isD0LocalMinimumForMoveSupports_of_rotationDisk_candidates_and_cubic_star_repairs
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    (D : RotationDiskData V G.edgeSet)
    (hincident : ∀ v : V, D.asZeroBoundary.incident v = incidentEdgeFinset G v)
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hcandidate :
      EveryClusteredZeroVertexHasRotationDiskD0Candidate G D moveSupports x)
    (hrepair :
      EveryCubicD0BasicColorObstructionStarHasD0Descent G moveSupports x) :
    zeroClusteringCount G x = 0 :=
  zeroClusteringCount_eq_zero_iff_zeroEdgesFormMatching.mpr
    (zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_rotationDisk_candidates_and_cubic_star_repairs
      D hincident hcard hmin hcandidate hrepair)

/-- If no vertex is touched by a zero edge, then the zero-clustering defect is
zero. -/
theorem zeroClusteringCount_eq_zero_of_zeroIncidentVertexCount_eq_zero
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet] {x : G.edgeSet → Color}
    (hI : zeroIncidentVertexCount G x = 0) :
    zeroClusteringCount G x = 0 :=
  zeroClusteringCount_eq_zero_of_zeroEdgeCount_eq_zero
    (zeroEdgeCount_eq_zero_of_zeroIncidentVertexCount_eq_zero hI)

/-- The cheap defect `D₀` vanishes exactly when the zero-edge count vanishes.
The incident and clustering terms are then forced to vanish as well. -/
theorem zeroDefectD0_eq_zero_iff_zeroEdgeCount_eq_zero
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet] {x : G.edgeSet → Color} :
    zeroDefectD0 G x = 0 ↔ zeroEdgeCount G x = 0 := by
  constructor
  · intro hD
    unfold zeroDefectD0 at hD
    omega
  · intro hZ
    unfold zeroDefectD0
    rw [hZ, zeroIncidentVertexCount_eq_zero_of_zeroEdgeCount_eq_zero hZ,
      zeroClusteringCount_eq_zero_of_zeroEdgeCount_eq_zero hZ]

/-- Positivity of the cheap defect is exactly positivity of the zero-edge
count.  Thus `D₀` is a faithful defect for nowhere-zero flows, despite its
extra incident and clustering terms. -/
theorem zeroDefectD0_pos_iff_zeroEdgeCount_pos
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet] {x : G.edgeSet → Color} :
    0 < zeroDefectD0 G x ↔ 0 < zeroEdgeCount G x := by
  constructor
  · intro hD
    have hDne : zeroDefectD0 G x ≠ 0 := Nat.ne_of_gt hD
    have hZne : zeroEdgeCount G x ≠ 0 := by
      intro hZ
      exact hDne ((zeroDefectD0_eq_zero_iff_zeroEdgeCount_eq_zero).mpr hZ)
    exact Nat.pos_of_ne_zero hZne
  · intro hZ
    have hZne : zeroEdgeCount G x ≠ 0 := Nat.ne_of_gt hZ
    have hDne : zeroDefectD0 G x ≠ 0 := by
      intro hD
      exact hZne ((zeroDefectD0_eq_zero_iff_zeroEdgeCount_eq_zero).mp hD)
    exact Nat.pos_of_ne_zero hDne

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

/-- Manuscript-facing form: a nowhere-zero graph flow is exactly a graph flow
with cheap defect `D₀=0`. -/
theorem isNowhereZeroFlow_iff_isGraphFlow_and_zeroDefectD0_eq_zero
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet] {x : G.edgeSet → Color} :
    IsNowhereZeroFlow G x ↔ IsGraphFlow G x ∧ zeroDefectD0 G x = 0 := by
  rw [isNowhereZeroFlow_iff_isGraphFlow_and_zeroEdgeCount_eq_zero,
    zeroDefectD0_eq_zero_iff_zeroEdgeCount_eq_zero]

/-- For an already-valid graph flow, failure to be nowhere-zero is exactly
positive cheap defect.  This is the formal bridge behind minimizing `D₀`. -/
theorem not_isNowhereZeroFlow_iff_zeroDefectD0_pos_of_isGraphFlow
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet] {x : G.edgeSet → Color}
    (hx : IsGraphFlow G x) :
    ¬ IsNowhereZeroFlow G x ↔ 0 < zeroDefectD0 G x := by
  rw [isNowhereZeroFlow_iff_isGraphFlow_and_zeroDefectD0_eq_zero]
  simp [hx, Nat.pos_iff_ne_zero]

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

/-- Indicator-sum form of the manuscript's touched-vertex statistic `I(x)`. -/
theorem zeroIncidentVertexCount_eq_sum_zeroIncidentIndicator
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet] {x : G.edgeSet → Color} :
    zeroIncidentVertexCount G x =
      ∑ v, if 0 < zeroIncidentEdgeCount G x v then 1 else 0 := by
  rw [zeroIncidentVertexCount, zeroIncidentVertexFinset, Finset.card_filter]

/-- The local identity behind the manuscript's statistics: for each vertex,
the touched-vertex indicator plus the clustering penalty recovers the local
zero-incidence count. -/
theorem zeroIncidentIndicator_add_zeroClusteringLocalTerm_eq_zeroIncidentEdgeCount
    {G : SimpleGraph V} [Fintype G.edgeSet] {x : G.edgeSet → Color} (v : V) :
    (if 0 < zeroIncidentEdgeCount G x v then 1 else 0) +
        (zeroIncidentEdgeCount G x v - 1) =
      zeroIncidentEdgeCount G x v := by
  by_cases hpos : 0 < zeroIncidentEdgeCount G x v
  · simp [hpos]
    omega
  · have hzero : zeroIncidentEdgeCount G x v = 0 :=
      Nat.eq_zero_of_not_pos hpos
    simp [hzero]

/-- Global form of the local counting identity: touched zero vertices plus
zero clustering count every zero edge twice. -/
theorem zeroIncidentVertexCount_add_zeroClusteringCount_eq_two_mul_zeroEdgeCount
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet] {x : G.edgeSet → Color} :
    zeroIncidentVertexCount G x + zeroClusteringCount G x =
      2 * zeroEdgeCount G x := by
  rw [← sum_zeroIncidentEdgeCount_eq_two_mul_zeroEdgeCount,
    zeroIncidentVertexCount_eq_sum_zeroIncidentIndicator, zeroClusteringCount,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _hv
  exact zeroIncidentIndicator_add_zeroClusteringLocalTerm_eq_zeroIncidentEdgeCount v

/-- If the zero edges form a matching, the number of vertices touched by zero
edges is the sum of the local zero-incidence counts. -/
theorem zeroIncidentVertexCount_eq_sum_zeroIncidentEdgeCount_of_zeroEdgesFormMatching
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet] {x : G.edgeSet → Color}
    (hmatch : ZeroEdgesFormMatching G x) :
    zeroIncidentVertexCount G x = ∑ v, zeroIncidentEdgeCount G x v := by
  rw [zeroIncidentVertexCount_eq_sum_zeroIncidentIndicator]
  calc
    ∑ v, (if 0 < zeroIncidentEdgeCount G x v then 1 else 0) =
        ∑ v, zeroIncidentEdgeCount G x v := by
      apply Finset.sum_congr rfl
      intro v _hv
      by_cases hvpos : 0 < zeroIncidentEdgeCount G x v
      · have hk : zeroIncidentEdgeCount G x v = 1 :=
          Nat.le_antisymm (hmatch v) (Nat.succ_le_of_lt hvpos)
        simp [hk]
      · have hk : zeroIncidentEdgeCount G x v = 0 := Nat.eq_zero_of_not_pos hvpos
        simp [hk]

/-- Manuscript count form for matching zero patterns: `I(x)=2 Z(x)`. -/
theorem zeroIncidentVertexCount_eq_two_mul_zeroEdgeCount_of_zeroEdgesFormMatching
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet] {x : G.edgeSet → Color}
    (hmatch : ZeroEdgesFormMatching G x) :
    zeroIncidentVertexCount G x = 2 * zeroEdgeCount G x := by
  rw [zeroIncidentVertexCount_eq_sum_zeroIncidentEdgeCount_of_zeroEdgesFormMatching hmatch,
    sum_zeroIncidentEdgeCount_eq_two_mul_zeroEdgeCount]

/-- Conversely, the manuscript count identity `I(x)=2Z(x)` forces the zero
edges to form a matching. -/
theorem zeroEdgesFormMatching_of_zeroIncidentVertexCount_eq_two_mul_zeroEdgeCount
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet] {x : G.edgeSet → Color}
    (hI : zeroIncidentVertexCount G x = 2 * zeroEdgeCount G x) :
    ZeroEdgesFormMatching G x := by
  rw [← zeroClusteringCount_eq_zero_iff_zeroEdgesFormMatching]
  have hcount :=
    zeroIncidentVertexCount_add_zeroClusteringCount_eq_two_mul_zeroEdgeCount
      (G := G) (x := x)
  rw [hI] at hcount
  omega

/-- The manuscript's matching-zero condition is equivalent to the count
identity `I(x)=2Z(x)`. -/
theorem zeroEdgesFormMatching_iff_zeroIncidentVertexCount_eq_two_mul_zeroEdgeCount
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet] {x : G.edgeSet → Color} :
    ZeroEdgesFormMatching G x ↔
      zeroIncidentVertexCount G x = 2 * zeroEdgeCount G x :=
  ⟨zeroIncidentVertexCount_eq_two_mul_zeroEdgeCount_of_zeroEdgesFormMatching,
    zeroEdgesFormMatching_of_zeroIncidentVertexCount_eq_two_mul_zeroEdgeCount⟩

/-- Since `C(x)=0` is equivalent to the zero-edge set being a matching, zero
clustering also yields the manuscript count `I(x)=2 Z(x)`. -/
theorem zeroIncidentVertexCount_eq_two_mul_zeroEdgeCount_of_zeroClusteringCount_eq_zero
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet] {x : G.edgeSet → Color}
    (hC : zeroClusteringCount G x = 0) :
    zeroIncidentVertexCount G x = 2 * zeroEdgeCount G x :=
  zeroIncidentVertexCount_eq_two_mul_zeroEdgeCount_of_zeroEdgesFormMatching
    (zeroClusteringCount_eq_zero_iff_zeroEdgesFormMatching.mp hC)

/-- The manuscript's two numeric forms of matching zero support are
equivalent: no clustering exactly when `I(x)=2Z(x)`. -/
theorem zeroClusteringCount_eq_zero_iff_zeroIncidentVertexCount_eq_two_mul_zeroEdgeCount
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet] {x : G.edgeSet → Color} :
    zeroClusteringCount G x = 0 ↔
      zeroIncidentVertexCount G x = 2 * zeroEdgeCount G x := by
  rw [zeroClusteringCount_eq_zero_iff_zeroEdgesFormMatching,
    zeroEdgesFormMatching_iff_zeroIncidentVertexCount_eq_two_mul_zeroEdgeCount]

/-- At a `D₀` local minimum, the global nonmatching-repair hypothesis is
equivalent to vanishing zero clustering. -/
theorem everyNonmatchingZeroPatternHasD0Descent_iff_zeroClusteringCount_eq_zero_of_isD0LocalMinimumForMoveSupports
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x) :
    EveryNonmatchingZeroPatternHasD0Descent G moveSupports x ↔
      zeroClusteringCount G x = 0 :=
  (everyNonmatchingZeroPatternHasD0Descent_iff_zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports
    hmin).trans zeroClusteringCount_eq_zero_iff_zeroEdgesFormMatching.symm

/-- At a `D₀` local minimum, the vertex-local repair hypothesis is equivalent
to vanishing zero clustering. -/
theorem everyClusteredZeroVertexHasD0Descent_iff_zeroClusteringCount_eq_zero_of_isD0LocalMinimumForMoveSupports
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x) :
    EveryClusteredZeroVertexHasD0Descent G moveSupports x ↔
      zeroClusteringCount G x = 0 :=
  (everyClusteredZeroVertexHasD0Descent_iff_zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports
    hmin).trans zeroClusteringCount_eq_zero_iff_zeroEdgesFormMatching.symm

/-- At a `D₀` local minimum, the global nonmatching-repair hypothesis is
equivalent to the manuscript count identity `I(x)=2Z(x)`. -/
theorem everyNonmatchingZeroPatternHasD0Descent_iff_zeroIncidentVertexCount_eq_two_mul_zeroEdgeCount_of_isD0LocalMinimumForMoveSupports
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x) :
    EveryNonmatchingZeroPatternHasD0Descent G moveSupports x ↔
      zeroIncidentVertexCount G x = 2 * zeroEdgeCount G x :=
  (everyNonmatchingZeroPatternHasD0Descent_iff_zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports
    hmin).trans zeroEdgesFormMatching_iff_zeroIncidentVertexCount_eq_two_mul_zeroEdgeCount

/-- At a `D₀` local minimum, the vertex-local repair hypothesis is equivalent
to the manuscript count identity `I(x)=2Z(x)`. -/
theorem everyClusteredZeroVertexHasD0Descent_iff_zeroIncidentVertexCount_eq_two_mul_zeroEdgeCount_of_isD0LocalMinimumForMoveSupports
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x) :
    EveryClusteredZeroVertexHasD0Descent G moveSupports x ↔
      zeroIncidentVertexCount G x = 2 * zeroEdgeCount G x :=
  (everyClusteredZeroVertexHasD0Descent_iff_zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports
    hmin).trans zeroEdgesFormMatching_iff_zeroIncidentVertexCount_eq_two_mul_zeroEdgeCount

/-- Manuscript count form of the abstract matching-zeros theorem: at repaired
`D₀` local minima, `I(x)=2Z(x)`. -/
theorem
    zeroIncidentVertexCount_eq_two_mul_zeroEdgeCount_of_isD0LocalMinimumForMoveSupports_of_nonmatching_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hrepair : EveryNonmatchingZeroPatternHasD0Descent G moveSupports x) :
    zeroIncidentVertexCount G x = 2 * zeroEdgeCount G x :=
  zeroIncidentVertexCount_eq_two_mul_zeroEdgeCount_of_zeroEdgesFormMatching
    (zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_nonmatching_descent
      hmin hrepair)

/-- Vertex-local repair form of the manuscript count identity `I(x)=2Z(x)`. -/
theorem
    zeroIncidentVertexCount_eq_two_mul_zeroEdgeCount_of_isD0LocalMinimumForMoveSupports_of_clusteredZeroVertex_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hrepair : EveryClusteredZeroVertexHasD0Descent G moveSupports x) :
    zeroIncidentVertexCount G x = 2 * zeroEdgeCount G x :=
  zeroIncidentVertexCount_eq_two_mul_zeroEdgeCount_of_zeroEdgesFormMatching
    (zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_clusteredZeroVertex_descent
      hmin hrepair)

/-- Concrete neutral-repair form of the manuscript count identity `I(x)=2Z(x)`. -/
theorem
    zeroIncidentVertexCount_eq_two_mul_zeroEdgeCount_of_isD0LocalMinimumForMoveSupports_of_kirchhoffNeutral_vertex_repairs
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hrepair :
      ∀ v : V, 2 ≤ zeroIncidentEdgeCount G x v →
        ∃ C ∈ moveSupports, ∃ g : Color,
          g ≠ 0 ∧
            IsKirchhoffNeutralMoveSupport G C ∧
              (∀ w : V, ∃ e ∈ incidentEdgeFinset G w,
                if e ∈ C then x e ≠ g else x e ≠ 0) ∧
                (∃ e ∈ C, e ∈ incidentEdgeFinset G v ∧ x e = 0) ∧
                  ∀ e ∈ C, x e ≠ g) :
    zeroIncidentVertexCount G x = 2 * zeroEdgeCount G x :=
  zeroIncidentVertexCount_eq_two_mul_zeroEdgeCount_of_zeroEdgesFormMatching
    (zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_kirchhoffNeutral_vertex_repairs
      hmin hrepair)

/-- Two-step neutral-candidate form of the manuscript count identity
`I(x)=2Z(x)`. -/
theorem
    zeroIncidentVertexCount_eq_two_mul_zeroEdgeCount_of_isD0LocalMinimumForMoveSupports_of_neutral_candidates_and_cubicObstruction_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hcandidate : EveryClusteredZeroVertexHasNeutralD0Candidate G moveSupports x)
    (hrepair : EveryCubicD0BasicColorObstructionHasD0Descent G moveSupports x) :
    zeroIncidentVertexCount G x = 2 * zeroEdgeCount G x :=
  zeroIncidentVertexCount_eq_two_mul_zeroEdgeCount_of_zeroEdgesFormMatching
    (zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_neutral_candidates_and_cubicObstruction_descent
      hcard hmin hcandidate hrepair)

/-- Kempe-cycle source form of the two-step count identity `I(x)=2Z(x)`. -/
theorem
    zeroIncidentVertexCount_eq_two_mul_zeroEdgeCount_of_isD0LocalMinimumForMoveSupports_of_kempe_candidates_and_cubicObstruction_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hcandidate : EveryClusteredZeroVertexHasKempeD0Candidate G moveSupports x)
    (hrepair : EveryCubicD0BasicColorObstructionHasD0Descent G moveSupports x) :
    zeroIncidentVertexCount G x = 2 * zeroEdgeCount G x :=
  zeroIncidentVertexCount_eq_two_mul_zeroEdgeCount_of_zeroEdgesFormMatching
    (zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_kempe_candidates_and_cubicObstruction_descent
      hcard hmin hcandidate hrepair)

/-- Rotation-disk source form of the two-step count identity `I(x)=2Z(x)`. -/
theorem
    zeroIncidentVertexCount_eq_two_mul_zeroEdgeCount_of_isD0LocalMinimumForMoveSupports_of_rotationDisk_candidates_and_cubicObstruction_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    (D : RotationDiskData V G.edgeSet)
    (hincident : ∀ v : V, D.asZeroBoundary.incident v = incidentEdgeFinset G v)
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hcandidate :
      EveryClusteredZeroVertexHasRotationDiskD0Candidate G D moveSupports x)
    (hrepair : EveryCubicD0BasicColorObstructionHasD0Descent G moveSupports x) :
    zeroIncidentVertexCount G x = 2 * zeroEdgeCount G x :=
  zeroIncidentVertexCount_eq_two_mul_zeroEdgeCount_of_zeroEdgesFormMatching
    (zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_rotationDisk_candidates_and_cubicObstruction_descent
      D hincident hcard hmin hcandidate hrepair)

/-- Star-repair form of the two-step count identity `I(x)=2Z(x)`. -/
theorem
    zeroIncidentVertexCount_eq_two_mul_zeroEdgeCount_of_isD0LocalMinimumForMoveSupports_of_neutral_candidates_and_cubic_star_repairs
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hcandidate : EveryClusteredZeroVertexHasNeutralD0Candidate G moveSupports x)
    (hrepair :
      EveryCubicD0BasicColorObstructionStarHasD0Descent G moveSupports x) :
    zeroIncidentVertexCount G x = 2 * zeroEdgeCount G x :=
  zeroIncidentVertexCount_eq_two_mul_zeroEdgeCount_of_zeroEdgesFormMatching
    (zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_neutral_candidates_and_cubic_star_repairs
      hcard hmin hcandidate hrepair)

/-- Kempe-cycle source form of the star-repair count identity `I(x)=2Z(x)`. -/
theorem
    zeroIncidentVertexCount_eq_two_mul_zeroEdgeCount_of_isD0LocalMinimumForMoveSupports_of_kempe_candidates_and_cubic_star_repairs
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hcandidate : EveryClusteredZeroVertexHasKempeD0Candidate G moveSupports x)
    (hrepair :
      EveryCubicD0BasicColorObstructionStarHasD0Descent G moveSupports x) :
    zeroIncidentVertexCount G x = 2 * zeroEdgeCount G x :=
  zeroIncidentVertexCount_eq_two_mul_zeroEdgeCount_of_zeroEdgesFormMatching
    (zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_kempe_candidates_and_cubic_star_repairs
      hcard hmin hcandidate hrepair)

/-- Rotation-disk source form of the star-repair count identity `I(x)=2Z(x)`. -/
theorem
    zeroIncidentVertexCount_eq_two_mul_zeroEdgeCount_of_isD0LocalMinimumForMoveSupports_of_rotationDisk_candidates_and_cubic_star_repairs
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    (D : RotationDiskData V G.edgeSet)
    (hincident : ∀ v : V, D.asZeroBoundary.incident v = incidentEdgeFinset G v)
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hcandidate :
      EveryClusteredZeroVertexHasRotationDiskD0Candidate G D moveSupports x)
    (hrepair :
      EveryCubicD0BasicColorObstructionStarHasD0Descent G moveSupports x) :
    zeroIncidentVertexCount G x = 2 * zeroEdgeCount G x :=
  zeroIncidentVertexCount_eq_two_mul_zeroEdgeCount_of_zeroEdgesFormMatching
    (zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_rotationDisk_candidates_and_cubic_star_repairs
      D hincident hcard hmin hcandidate hrepair)

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

/-- The cheap-defect collapse `D₀(x)=120Z(x)` is exactly the matching-zero
condition. -/
theorem zeroDefectD0_eq_120_mul_zeroEdgeCount_iff_zeroEdgesFormMatching
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet] {x : G.edgeSet → Color} :
    zeroDefectD0 G x = 120 * zeroEdgeCount G x ↔
      ZeroEdgesFormMatching G x := by
  constructor
  · intro hD
    rw [← zeroClusteringCount_eq_zero_iff_zeroEdgesFormMatching]
    have hcount :=
      zeroIncidentVertexCount_add_zeroClusteringCount_eq_two_mul_zeroEdgeCount
        (G := G) (x := x)
    unfold zeroDefectD0 at hD
    omega
  · exact zeroDefectD0_eq_120_mul_zeroEdgeCount_of_zeroEdgesFormMatching

/-- Equivalent numeric form of the cheap-defect collapse: `D₀=120Z` exactly
when zero clustering vanishes. -/
theorem zeroDefectD0_eq_120_mul_zeroEdgeCount_iff_zeroClusteringCount_eq_zero
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet] {x : G.edgeSet → Color} :
    zeroDefectD0 G x = 120 * zeroEdgeCount G x ↔
      zeroClusteringCount G x = 0 :=
  zeroDefectD0_eq_120_mul_zeroEdgeCount_iff_zeroEdgesFormMatching.trans
    zeroClusteringCount_eq_zero_iff_zeroEdgesFormMatching.symm

/-- At a `D₀` local minimum, the global nonmatching-repair hypothesis is
equivalent to the cheap-defect collapse `D₀(x)=120Z(x)`. -/
theorem everyNonmatchingZeroPatternHasD0Descent_iff_zeroDefectD0_eq_120_mul_zeroEdgeCount_of_isD0LocalMinimumForMoveSupports
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x) :
    EveryNonmatchingZeroPatternHasD0Descent G moveSupports x ↔
      zeroDefectD0 G x = 120 * zeroEdgeCount G x :=
  (everyNonmatchingZeroPatternHasD0Descent_iff_zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports
    hmin).trans zeroDefectD0_eq_120_mul_zeroEdgeCount_iff_zeroEdgesFormMatching.symm

/-- At a `D₀` local minimum, the vertex-local repair hypothesis is equivalent
to the cheap-defect collapse `D₀(x)=120Z(x)`. -/
theorem everyClusteredZeroVertexHasD0Descent_iff_zeroDefectD0_eq_120_mul_zeroEdgeCount_of_isD0LocalMinimumForMoveSupports
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x) :
    EveryClusteredZeroVertexHasD0Descent G moveSupports x ↔
      zeroDefectD0 G x = 120 * zeroEdgeCount G x :=
  (everyClusteredZeroVertexHasD0Descent_iff_zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports
    hmin).trans zeroDefectD0_eq_120_mul_zeroEdgeCount_iff_zeroEdgesFormMatching.symm

/-- Cheap-defect form of the abstract matching-zeros theorem: at repaired `D₀`
local minima, `D₀(x)=120Z(x)`. -/
theorem zeroDefectD0_eq_120_mul_zeroEdgeCount_of_isD0LocalMinimumForMoveSupports_of_nonmatching_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hrepair : EveryNonmatchingZeroPatternHasD0Descent G moveSupports x) :
    zeroDefectD0 G x = 120 * zeroEdgeCount G x :=
  zeroDefectD0_eq_120_mul_zeroEdgeCount_of_zeroEdgesFormMatching
    (zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_nonmatching_descent
      hmin hrepair)

/-- Vertex-local repair form of the cheap-defect collapse `D₀(x)=120Z(x)`. -/
theorem zeroDefectD0_eq_120_mul_zeroEdgeCount_of_isD0LocalMinimumForMoveSupports_of_clusteredZeroVertex_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hrepair : EveryClusteredZeroVertexHasD0Descent G moveSupports x) :
    zeroDefectD0 G x = 120 * zeroEdgeCount G x :=
  zeroDefectD0_eq_120_mul_zeroEdgeCount_of_zeroEdgesFormMatching
    (zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_clusteredZeroVertex_descent
      hmin hrepair)

/-- Two-step neutral-candidate form of the cheap-defect collapse
`D₀(x)=120Z(x)`. -/
theorem
    zeroDefectD0_eq_120_mul_zeroEdgeCount_of_isD0LocalMinimumForMoveSupports_of_neutral_candidates_and_cubicObstruction_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hcandidate : EveryClusteredZeroVertexHasNeutralD0Candidate G moveSupports x)
    (hrepair : EveryCubicD0BasicColorObstructionHasD0Descent G moveSupports x) :
    zeroDefectD0 G x = 120 * zeroEdgeCount G x :=
  zeroDefectD0_eq_120_mul_zeroEdgeCount_of_zeroEdgesFormMatching
    (zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_neutral_candidates_and_cubicObstruction_descent
      hcard hmin hcandidate hrepair)

/-- Kempe-cycle source form of the two-step cheap-defect collapse. -/
theorem
    zeroDefectD0_eq_120_mul_zeroEdgeCount_of_isD0LocalMinimumForMoveSupports_of_kempe_candidates_and_cubicObstruction_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hcandidate : EveryClusteredZeroVertexHasKempeD0Candidate G moveSupports x)
    (hrepair : EveryCubicD0BasicColorObstructionHasD0Descent G moveSupports x) :
    zeroDefectD0 G x = 120 * zeroEdgeCount G x :=
  zeroDefectD0_eq_120_mul_zeroEdgeCount_of_zeroEdgesFormMatching
    (zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_kempe_candidates_and_cubicObstruction_descent
      hcard hmin hcandidate hrepair)

/-- Rotation-disk source form of the two-step cheap-defect collapse. -/
theorem
    zeroDefectD0_eq_120_mul_zeroEdgeCount_of_isD0LocalMinimumForMoveSupports_of_rotationDisk_candidates_and_cubicObstruction_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    (D : RotationDiskData V G.edgeSet)
    (hincident : ∀ v : V, D.asZeroBoundary.incident v = incidentEdgeFinset G v)
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hcandidate :
      EveryClusteredZeroVertexHasRotationDiskD0Candidate G D moveSupports x)
    (hrepair : EveryCubicD0BasicColorObstructionHasD0Descent G moveSupports x) :
    zeroDefectD0 G x = 120 * zeroEdgeCount G x :=
  zeroDefectD0_eq_120_mul_zeroEdgeCount_of_zeroEdgesFormMatching
    (zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_rotationDisk_candidates_and_cubicObstruction_descent
      D hincident hcard hmin hcandidate hrepair)

/-- Star-repair form of the two-step cheap-defect collapse `D₀(x)=120Z(x)`. -/
theorem
    zeroDefectD0_eq_120_mul_zeroEdgeCount_of_isD0LocalMinimumForMoveSupports_of_neutral_candidates_and_cubic_star_repairs
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hcandidate : EveryClusteredZeroVertexHasNeutralD0Candidate G moveSupports x)
    (hrepair :
      EveryCubicD0BasicColorObstructionStarHasD0Descent G moveSupports x) :
    zeroDefectD0 G x = 120 * zeroEdgeCount G x :=
  zeroDefectD0_eq_120_mul_zeroEdgeCount_of_zeroEdgesFormMatching
    (zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_neutral_candidates_and_cubic_star_repairs
      hcard hmin hcandidate hrepair)

/-- Kempe-cycle source form of the star-repair cheap-defect collapse. -/
theorem
    zeroDefectD0_eq_120_mul_zeroEdgeCount_of_isD0LocalMinimumForMoveSupports_of_kempe_candidates_and_cubic_star_repairs
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hcandidate : EveryClusteredZeroVertexHasKempeD0Candidate G moveSupports x)
    (hrepair :
      EveryCubicD0BasicColorObstructionStarHasD0Descent G moveSupports x) :
    zeroDefectD0 G x = 120 * zeroEdgeCount G x :=
  zeroDefectD0_eq_120_mul_zeroEdgeCount_of_zeroEdgesFormMatching
    (zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_kempe_candidates_and_cubic_star_repairs
      hcard hmin hcandidate hrepair)

/-- Rotation-disk source form of the star-repair cheap-defect collapse. -/
theorem
    zeroDefectD0_eq_120_mul_zeroEdgeCount_of_isD0LocalMinimumForMoveSupports_of_rotationDisk_candidates_and_cubic_star_repairs
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    (D : RotationDiskData V G.edgeSet)
    (hincident : ∀ v : V, D.asZeroBoundary.incident v = incidentEdgeFinset G v)
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hcandidate :
      EveryClusteredZeroVertexHasRotationDiskD0Candidate G D moveSupports x)
    (hrepair :
      EveryCubicD0BasicColorObstructionStarHasD0Descent G moveSupports x) :
    zeroDefectD0 G x = 120 * zeroEdgeCount G x :=
  zeroDefectD0_eq_120_mul_zeroEdgeCount_of_zeroEdgesFormMatching
    (zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_rotationDisk_candidates_and_cubic_star_repairs
      D hincident hcard hmin hcandidate hrepair)

/-- A nonempty matching zero pattern has cheap defect at least `120`, because
matching zeros force `D₀=120Z`. -/
theorem le_zeroDefectD0_of_zeroEdgesFormMatching_and_zeroEdgeCount_pos
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet] {x : G.edgeSet → Color}
    (hmatch : ZeroEdgesFormMatching G x) (hZ : 0 < zeroEdgeCount G x) :
    120 ≤ zeroDefectD0 G x := by
  rw [zeroDefectD0_eq_120_mul_zeroEdgeCount_of_zeroEdgesFormMatching hmatch]
  omega

/-- Local-minimum blocker scale under the abstract matching-zeros repair
principle: every repaired `D₀` local minimum has positive matching-zero defect,
hence `D₀≥120`. -/
theorem le_zeroDefectD0_of_isD0LocalMinimumForMoveSupports_of_nonmatching_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hrepair : EveryNonmatchingZeroPatternHasD0Descent G moveSupports x) :
    120 ≤ zeroDefectD0 G x :=
  le_zeroDefectD0_of_zeroEdgesFormMatching_and_zeroEdgeCount_pos
    (zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_nonmatching_descent
      hmin hrepair)
    hmin.has_zero

/-- Vertex-local repair form: every such `D₀` local minimum has positive
matching-zero defect at scale at least `120`. -/
theorem le_zeroDefectD0_of_isD0LocalMinimumForMoveSupports_of_clusteredZeroVertex_descent
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hrepair : EveryClusteredZeroVertexHasD0Descent G moveSupports x) :
    120 ≤ zeroDefectD0 G x :=
  le_zeroDefectD0_of_zeroEdgesFormMatching_and_zeroEdgeCount_pos
    (zeroEdgesFormMatching_of_isD0LocalMinimumForMoveSupports_of_clusteredZeroVertex_descent
      hmin hrepair)
    hmin.has_zero

/-- A matching zero pattern with an explicit zero edge is already at the first
positive cheap-defect scale `120`. -/
theorem le_zeroDefectD0_of_zeroEdgesFormMatching_and_exists_edge_eq_zero
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet] {x : G.edgeSet → Color}
    (hmatch : ZeroEdgesFormMatching G x) (hzero : ∃ e : G.edgeSet, x e = 0) :
    120 ≤ zeroDefectD0 G x :=
  le_zeroDefectD0_of_zeroEdgesFormMatching_and_zeroEdgeCount_pos hmatch
    (zeroEdgeCount_pos_of_exists_edge_eq_zero hzero)

/-- Equivalent form using positivity of the cheap defect itself. -/
theorem le_zeroDefectD0_of_zeroEdgesFormMatching_and_zeroDefectD0_pos
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet] {x : G.edgeSet → Color}
    (hmatch : ZeroEdgesFormMatching G x) (hD : 0 < zeroDefectD0 G x) :
    120 ≤ zeroDefectD0 G x :=
  le_zeroDefectD0_of_zeroEdgesFormMatching_and_zeroEdgeCount_pos hmatch
    ((zeroDefectD0_pos_iff_zeroEdgeCount_pos).mp hD)

/-- Cubic basic-color obstructions are nonempty matching-zero blockers with
cheap defect at least `120`, once the matching-zero hypothesis is available. -/
theorem le_zeroDefectD0_of_hasCubicD0BasicColorObstructionAt_and_zeroEdgesFormMatching
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {C : Finset G.edgeSet} {g : Color} {x : G.edgeSet → Color} {v : V}
    (hobst : HasCubicD0BasicColorObstructionAt G x C v g)
    (hmatch : ZeroEdgesFormMatching G x) :
    120 ≤ zeroDefectD0 G x :=
  le_zeroDefectD0_of_zeroEdgesFormMatching_and_zeroEdgeCount_pos hmatch
    (zeroEdgeCount_pos_of_hasCubicD0BasicColorObstructionAt hobst)

/-- Existence form for the three basic nonzero colors. -/
theorem le_zeroDefectD0_of_exists_hasCubicD0BasicColorObstructionAt_and_zeroEdgesFormMatching
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {C : Finset G.edgeSet} {x : G.edgeSet → Color}
    (hobst :
      (∃ v : V, HasCubicD0BasicColorObstructionAt G x C v red) ∨
        (∃ v : V, HasCubicD0BasicColorObstructionAt G x C v blue) ∨
          (∃ v : V, HasCubicD0BasicColorObstructionAt G x C v purple))
    (hmatch : ZeroEdgesFormMatching G x) :
    120 ≤ zeroDefectD0 G x :=
  le_zeroDefectD0_of_zeroEdgesFormMatching_and_zeroDefectD0_pos hmatch
    (zeroDefectD0_pos_of_exists_hasCubicD0BasicColorObstructionAt hobst)

/-- Route-specific form: under the matching-zero hypothesis, a small
Kirchhoff-neutral basic color obstruction at a `D₀` local minimum is already a
`D₀≥120` blocker. -/
theorem
    le_zeroDefectD0_of_basic_color_obstruction_of_d0LocalMinimum_kirchhoffNeutral_small_support_and_zeroEdgesFormMatching
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hCmem : C ∈ moveSupports)
    (hC : IsKirchhoffNeutralMoveSupport G C)
    (herase : ∃ e ∈ C, x e = 0)
    (hsmall : C.card ≤ 3)
    (hmatch : ZeroEdgesFormMatching G x) :
    120 ≤ zeroDefectD0 G x :=
  le_zeroDefectD0_of_exists_hasCubicD0BasicColorObstructionAt_and_zeroEdgesFormMatching
    (exists_hasCubicD0BasicColorObstructionAt_for_basic_color_obstruction_of_d0LocalMinimum_kirchhoffNeutral_small_support
      hcard hmin hCmem hC herase hsmall)
    hmatch

/-- Kempe-cycle source form of the local-minimum blocker lower bound. -/
theorem
    le_zeroDefectD0_of_basic_color_obstruction_of_d0LocalMinimum_isKempeCycle_small_support_and_zeroEdgesFormMatching
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {C : Finset G.edgeSet} {α β : Color}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hCmem : C ∈ moveSupports)
    (hC : IsKempeCycle (incidentEdgeFinset G) x C α β)
    (herase : ∃ e ∈ C, x e = 0)
    (hsmall : C.card ≤ 3)
    (hmatch : ZeroEdgesFormMatching G x) :
    120 ≤ zeroDefectD0 G x :=
  le_zeroDefectD0_of_basic_color_obstruction_of_d0LocalMinimum_kirchhoffNeutral_small_support_and_zeroEdgesFormMatching
    hcard hmin hCmem (isKirchhoffNeutralMoveSupport_of_isKempeCycle hC) herase
    hsmall hmatch

/-- Rotation-disk internal-face source form of the local-minimum blocker lower
bound. -/
theorem
    le_zeroDefectD0_of_basic_color_obstruction_of_d0LocalMinimum_rotationDiskData_internalFace_small_support_and_zeroEdgesFormMatching
    {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    (D : RotationDiskData V G.edgeSet)
    (hincident : ∀ v : V, D.asZeroBoundary.incident v = incidentEdgeFinset G v)
    {moveSupports : Finset (Finset G.edgeSet)} {x : G.edgeSet → Color}
    {f : Finset G.edgeSet}
    (hcard : ∀ v : V, (incidentEdgeFinset G v).card = 3)
    (hmin : IsD0LocalMinimumForMoveSupports G moveSupports x)
    (hfmem : f ∈ moveSupports)
    (hf : f ∈ D.rotation.internalFaces)
    (herase : ∃ e ∈ f, x e = 0)
    (hsmall : f.card ≤ 3)
    (hmatch : ZeroEdgesFormMatching G x) :
    120 ≤ zeroDefectD0 G x :=
  le_zeroDefectD0_of_basic_color_obstruction_of_d0LocalMinimum_kirchhoffNeutral_small_support_and_zeroEdgesFormMatching
    hcard hmin hfmem
    (isKirchhoffNeutralMoveSupport_of_rotationDiskData_internalFace D hincident hf)
    herase hsmall hmatch

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

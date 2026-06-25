import Mettapedia.GraphTheory.FourColor.CAP5BoundaryWord
import Mettapedia.GraphTheory.FourColor.BoundaryChains
import Mettapedia.GraphTheory.FourColor.GoertzelDefinition48

open scoped BigOperators

open SimpleGraph

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*}

/-!
Graph-facing CAP5 boundary bridges.

This file connects the local CAP5 boundary-word layer to the manuscript's Tait edge-coloring
interface, without adding graph geometry assumptions.
-/

/-- A normalized ordered presentation of a five-edge CAP5 boundary support.  The support set is
kept in the type so finite benchmarks can prove once that their selected boundary support is
exactly the five indexed edges, then reuse the graph-facing CAP5 boundary lemmas without
threading the same `Fin 5` image equality through every theorem. -/
structure CAP5BoundaryEdgeEnumeration {E : Type*} [DecidableEq E] (support : Finset E) where
  boundaryEdge : Fin 5 → E
  injective : Function.Injective boundaryEdge
  support_eq : support = Finset.univ.map ⟨boundaryEdge, injective⟩

namespace CAP5BoundaryEdgeEnumeration

variable {E : Type*} [DecidableEq E] {support : Finset E}

/-- Build the normalized support directly from an indexed five-edge boundary map. -/
def ofBoundaryEdge (boundaryEdge : Fin 5 → E) (hinj : Function.Injective boundaryEdge) :
    CAP5BoundaryEdgeEnumeration (Finset.univ.map ⟨boundaryEdge, hinj⟩) where
  boundaryEdge := boundaryEdge
  injective := hinj
  support_eq := rfl

@[simp] theorem ofBoundaryEdge_boundaryEdge
    (boundaryEdge : Fin 5 → E) (hinj : Function.Injective boundaryEdge) :
    (ofBoundaryEdge boundaryEdge hinj).boundaryEdge = boundaryEdge :=
  rfl

@[simp] theorem mem_support_iff (enum : CAP5BoundaryEdgeEnumeration support) {e : E} :
    e ∈ support ↔ ∃ i : Fin 5, enum.boundaryEdge i = e := by
  constructor
  · intro h
    have hmap : e ∈ Finset.univ.map ⟨enum.boundaryEdge, enum.injective⟩ := by
      simpa [enum.support_eq] using h
    simpa using hmap
  · intro h
    have hmap : e ∈ Finset.univ.map ⟨enum.boundaryEdge, enum.injective⟩ := by
      simpa using h
    simpa [enum.support_eq] using hmap

@[simp] theorem card_support (enum : CAP5BoundaryEdgeEnumeration support) :
    support.card = 5 := by
  rw [enum.support_eq]
  simp

theorem incident_eq_map {U : Type*} {D : ZeroBoundaryData U E} {v : U}
    (enum : CAP5BoundaryEdgeEnumeration (D.incident v)) :
    D.incident v = Finset.univ.map ⟨enum.boundaryEdge, enum.injective⟩ :=
  enum.support_eq

theorem boundaryEdge_mem_support (enum : CAP5BoundaryEdgeEnumeration support) (i : Fin 5) :
    enum.boundaryEdge i ∈ support :=
  enum.mem_support_iff.2 ⟨i, rfl⟩

theorem support_subset_iff (enum : CAP5BoundaryEdgeEnumeration support) {s : Finset E} :
    support ⊆ s ↔ ∀ i : Fin 5, enum.boundaryEdge i ∈ s := by
  constructor
  · intro h i
    exact h (enum.boundaryEdge_mem_support i)
  · intro h e he
    rcases enum.mem_support_iff.1 he with ⟨i, rfl⟩
    exact h i

theorem forall_support_iff (enum : CAP5BoundaryEdgeEnumeration support) {p : E → Prop} :
    (∀ e ∈ support, p e) ↔ ∀ i : Fin 5, p (enum.boundaryEdge i) := by
  constructor
  · intro h i
    exact h (enum.boundaryEdge i) (enum.boundaryEdge_mem_support i)
  · intro h e he
    rcases enum.mem_support_iff.1 he with ⟨i, rfl⟩
    exact h i

theorem exists_support_iff (enum : CAP5BoundaryEdgeEnumeration support) {p : E → Prop} :
    (∃ e ∈ support, p e) ↔ ∃ i : Fin 5, p (enum.boundaryEdge i) := by
  constructor
  · rintro ⟨e, he, hp⟩
    rcases enum.mem_support_iff.1 he with ⟨i, rfl⟩
    exact ⟨i, hp⟩
  · rintro ⟨i, hp⟩
    exact ⟨enum.boundaryEdge i, enum.boundaryEdge_mem_support i, hp⟩

end CAP5BoundaryEdgeEnumeration

/-- Restricting a Tait edge-coloring to five CAP5 boundary edges gives a nonzero CAP5 boundary
word. -/
theorem cap5BoundaryWordOfEdges_isNonzero_of_isTaitEdgeColoring
    {G : SimpleGraph V} (boundaryEdge : Fin 5 → G.edgeSet)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C) :
    CAP5BoundaryWordIsNonzero (cap5BoundaryWordOfEdges boundaryEdge C) :=
  cap5BoundaryWordOfEdges_isNonzero_of_forall_nonzero boundaryEdge C
    (fun i => hC (boundaryEdge i))

/-- If the five CAP5 boundary edges enumerate a zero-boundary incidence set, the restricted
CAP5 boundary word has zero total color sum.  This is the graph-side cut equation in the
boundary-word language. -/
theorem cap5BoundaryWordOfEdges_sum_eq_zero_of_isZeroBoundary_at
    {U E : Type*} {D : ZeroBoundaryData U E} {v : U}
    (boundaryEdge : Fin 5 → E) (C : E → Color)
    (hinj : Function.Injective boundaryEdge)
    (hincident : D.incident v = Finset.univ.map ⟨boundaryEdge, hinj⟩)
    (hzero : D.isZeroBoundary C) :
    (∑ i : Fin 5, cap5BoundaryWordOfEdges boundaryEdge C i) = 0 := by
  have hv := hzero v
  rw [hincident] at hv
  simpa [cap5BoundaryWordOfEdges] using hv

/-- Membership in the full zero-boundary set gives the CAP5 cut equation whenever the five
boundary edges enumerate a vertex-incidence set. -/
theorem cap5BoundaryWordOfEdges_sum_eq_zero_of_mem_zeroBoundarySet_at
    {U E : Type*} {D : ZeroBoundaryData U E} {v : U}
    (boundaryEdge : Fin 5 → E) (C : E → Color)
    (hinj : Function.Injective boundaryEdge)
    (hincident : D.incident v = Finset.univ.map ⟨boundaryEdge, hinj⟩)
    (hzero : C ∈ D.zeroBoundarySet) :
    (∑ i : Fin 5, cap5BoundaryWordOfEdges boundaryEdge C i) = 0 :=
  cap5BoundaryWordOfEdges_sum_eq_zero_of_isZeroBoundary_at boundaryEdge C hinj
    hincident hzero.1

namespace CAP5BoundaryEdgeEnumeration

variable {E : Type*} [DecidableEq E]

/-- Enumeration form of the graph-side CAP5 cut equation. -/
theorem cap5BoundaryWord_sum_eq_zero_of_isZeroBoundary_at
    {U : Type*} {D : ZeroBoundaryData U E} {v : U}
    (enum : CAP5BoundaryEdgeEnumeration (D.incident v)) (C : E → Color)
    (hzero : D.isZeroBoundary C) :
    (∑ i : Fin 5, cap5BoundaryWordOfEdges enum.boundaryEdge C i) = 0 :=
  cap5BoundaryWordOfEdges_sum_eq_zero_of_isZeroBoundary_at enum.boundaryEdge C
    enum.injective enum.incident_eq_map hzero

/-- Enumeration form of the full-zero-boundary-set CAP5 cut equation. -/
theorem cap5BoundaryWord_sum_eq_zero_of_mem_zeroBoundarySet_at
    {U : Type*} {D : ZeroBoundaryData U E} {v : U}
    (enum : CAP5BoundaryEdgeEnumeration (D.incident v)) (C : E → Color)
    (hzero : C ∈ D.zeroBoundarySet) :
    (∑ i : Fin 5, cap5BoundaryWordOfEdges enum.boundaryEdge C i) = 0 :=
  enum.cap5BoundaryWord_sum_eq_zero_of_isZeroBoundary_at C hzero.1

end CAP5BoundaryEdgeEnumeration

/-- Graph-facing CAP5 parity: a Tait edge coloring whose five CAP5 boundary edges enumerate a
zero-boundary incidence set has odd red/blue/purple boundary counts. -/
theorem cap5BoundaryWordOfEdges_hasOddColorCounts_of_isTaitEdgeColoring_of_isZeroBoundary_at
    {U : Type*} {G : SimpleGraph V} {D : ZeroBoundaryData U G.edgeSet} {v : U}
    (boundaryEdge : Fin 5 → G.edgeSet) (C : G.EdgeColoring Color)
    (hC : IsTaitEdgeColoring G C)
    (hinj : Function.Injective boundaryEdge)
    (hincident : D.incident v = Finset.univ.map ⟨boundaryEdge, hinj⟩)
    (hzero : D.isZeroBoundary C) :
    CAP5BoundaryWordHasOddColorCounts (cap5BoundaryWordOfEdges boundaryEdge C) :=
  cap5BoundaryWordHasOddColorCounts_of_nonzero_of_sum_eq_zero
    (cap5BoundaryWordOfEdges_isNonzero_of_isTaitEdgeColoring boundaryEdge C hC)
    (cap5BoundaryWordOfEdges_sum_eq_zero_of_isZeroBoundary_at boundaryEdge C hinj hincident hzero)

/-- Full-zero-boundary-set variant of the graph-facing CAP5 parity theorem. -/
theorem cap5BoundaryWordOfEdges_hasOddColorCounts_of_isTaitEdgeColoring_of_mem_zeroBoundarySet_at
    {U : Type*} {G : SimpleGraph V} {D : ZeroBoundaryData U G.edgeSet} {v : U}
    (boundaryEdge : Fin 5 → G.edgeSet) (C : G.EdgeColoring Color)
    (hC : IsTaitEdgeColoring G C)
    (hinj : Function.Injective boundaryEdge)
    (hincident : D.incident v = Finset.univ.map ⟨boundaryEdge, hinj⟩)
    (hzero : (C : G.edgeSet → Color) ∈ D.zeroBoundarySet) :
    CAP5BoundaryWordHasOddColorCounts (cap5BoundaryWordOfEdges boundaryEdge C) :=
  cap5BoundaryWordOfEdges_hasOddColorCounts_of_isTaitEdgeColoring_of_isZeroBoundary_at
    boundaryEdge C hC hinj hincident hzero.1

/-- Graph-facing CAP5 block classifier: under the Tait and zero-boundary cut hypotheses, the
induced CAP5 boundary word is either a good `(3,1,1)` block or a bad `(2,1,1,1)` block. -/
theorem cap5BoundaryWordOfEdges_coloredBlock311_or_coloredBlock2111_of_isTaitEdgeColoring_of_isZeroBoundary_at
    {U : Type*} {G : SimpleGraph V} {D : ZeroBoundaryData U G.edgeSet} {v : U}
    (boundaryEdge : Fin 5 → G.edgeSet) (C : G.EdgeColoring Color)
    (hC : IsTaitEdgeColoring G C)
    (hinj : Function.Injective boundaryEdge)
    (hincident : D.incident v = Finset.univ.map ⟨boundaryEdge, hinj⟩)
    (hzero : D.isZeroBoundary C) :
    CAP5BoundaryWordHasColoredBlock311 (cap5BoundaryWordOfEdges boundaryEdge C) ∨
      CAP5BoundaryWordHasColoredBlock2111 (cap5BoundaryWordOfEdges boundaryEdge C) :=
  cap5BoundaryWord_coloredBlock311_or_coloredBlock2111_of_nonzero_of_odd
    (cap5BoundaryWordOfEdges_isNonzero_of_isTaitEdgeColoring boundaryEdge C hC)
    (cap5BoundaryWordOfEdges_hasOddColorCounts_of_isTaitEdgeColoring_of_isZeroBoundary_at
      boundaryEdge C hC hinj hincident hzero)

/-- Full-zero-boundary-set variant of the graph-facing CAP5 block classifier. -/
theorem cap5BoundaryWordOfEdges_coloredBlock311_or_coloredBlock2111_of_isTaitEdgeColoring_of_mem_zeroBoundarySet_at
    {U : Type*} {G : SimpleGraph V} {D : ZeroBoundaryData U G.edgeSet} {v : U}
    (boundaryEdge : Fin 5 → G.edgeSet) (C : G.EdgeColoring Color)
    (hC : IsTaitEdgeColoring G C)
    (hinj : Function.Injective boundaryEdge)
    (hincident : D.incident v = Finset.univ.map ⟨boundaryEdge, hinj⟩)
    (hzero : (C : G.edgeSet → Color) ∈ D.zeroBoundarySet) :
    CAP5BoundaryWordHasColoredBlock311 (cap5BoundaryWordOfEdges boundaryEdge C) ∨
      CAP5BoundaryWordHasColoredBlock2111 (cap5BoundaryWordOfEdges boundaryEdge C) :=
  cap5BoundaryWordOfEdges_coloredBlock311_or_coloredBlock2111_of_isTaitEdgeColoring_of_isZeroBoundary_at
    boundaryEdge C hC hinj hincident hzero.1

/-- Graph-facing CAP5 nonextension criterion under the manuscript cut hypotheses: failure to
extend is exactly the bad `(2,1,1,1)` case. -/
theorem cap5BoundaryWordOfEdges_not_extendsAcrossCycle_iff_coloredBlock2111_of_isTaitEdgeColoring_of_isZeroBoundary_at
    {U : Type*} {G : SimpleGraph V} {D : ZeroBoundaryData U G.edgeSet} {v : U}
    (boundaryEdge : Fin 5 → G.edgeSet) (C : G.EdgeColoring Color)
    (hC : IsTaitEdgeColoring G C)
    (hinj : Function.Injective boundaryEdge)
    (hincident : D.incident v = Finset.univ.map ⟨boundaryEdge, hinj⟩)
    (hzero : D.isZeroBoundary C) :
    ¬ CAP5WordExtendsAcrossCycle (cap5BoundaryWordOfEdges boundaryEdge C) ↔
      CAP5BoundaryWordHasColoredBlock2111 (cap5BoundaryWordOfEdges boundaryEdge C) :=
  not_cap5_extendsAcrossCycle_iff_coloredBlock2111_of_nonzero_of_odd
    (cap5BoundaryWordOfEdges_isNonzero_of_isTaitEdgeColoring boundaryEdge C hC)
    (cap5BoundaryWordOfEdges_hasOddColorCounts_of_isTaitEdgeColoring_of_isZeroBoundary_at
      boundaryEdge C hC hinj hincident hzero)

/-- Full-zero-boundary-set variant of the graph-facing CAP5 nonextension criterion. -/
theorem cap5BoundaryWordOfEdges_not_extendsAcrossCycle_iff_coloredBlock2111_of_isTaitEdgeColoring_of_mem_zeroBoundarySet_at
    {U : Type*} {G : SimpleGraph V} {D : ZeroBoundaryData U G.edgeSet} {v : U}
    (boundaryEdge : Fin 5 → G.edgeSet) (C : G.EdgeColoring Color)
    (hC : IsTaitEdgeColoring G C)
    (hinj : Function.Injective boundaryEdge)
    (hincident : D.incident v = Finset.univ.map ⟨boundaryEdge, hinj⟩)
    (hzero : (C : G.edgeSet → Color) ∈ D.zeroBoundarySet) :
    ¬ CAP5WordExtendsAcrossCycle (cap5BoundaryWordOfEdges boundaryEdge C) ↔
      CAP5BoundaryWordHasColoredBlock2111 (cap5BoundaryWordOfEdges boundaryEdge C) :=
  cap5BoundaryWordOfEdges_not_extendsAcrossCycle_iff_coloredBlock2111_of_isTaitEdgeColoring_of_isZeroBoundary_at
    boundaryEdge C hC hinj hincident hzero.1

/-- If a CAP5 boundary edge is one of the distinguished zero-boundary edges, its boundary-word
color is forced to zero by membership in the full zero-boundary set. -/
theorem cap5BoundaryWordOfEdges_eq_zero_of_mem_zeroBoundarySet_boundaryEdge
    {U E : Type*} {D : ZeroBoundaryData U E}
    (boundaryEdge : Fin 5 → E) (C : E → Color)
    (hzero : C ∈ D.zeroBoundarySet) {i : Fin 5}
    (hi : boundaryEdge i ∈ D.boundaryEdges) :
    cap5BoundaryWordOfEdges boundaryEdge C i = 0 :=
  hzero.2 (boundaryEdge i) hi

/-- A Tait-colored CAP5 boundary cannot put all five boundary edges into the distinguished
zero-boundary edge set. -/
theorem not_forall_boundaryEdge_mem_boundaryEdges_of_isTaitEdgeColoring_of_mem_zeroBoundarySet
    {U : Type*} {G : SimpleGraph V} {D : ZeroBoundaryData U G.edgeSet}
    (boundaryEdge : Fin 5 → G.edgeSet) (C : G.EdgeColoring Color)
    (hC : IsTaitEdgeColoring G C) (hzero : (C : G.edgeSet → Color) ∈ D.zeroBoundarySet) :
    ¬ ∀ i : Fin 5, boundaryEdge i ∈ D.boundaryEdges := by
  intro hboundary
  have hzero0 :
      cap5BoundaryWordOfEdges boundaryEdge C 0 = 0 :=
    cap5BoundaryWordOfEdges_eq_zero_of_mem_zeroBoundarySet_boundaryEdge boundaryEdge
      (C : G.edgeSet → Color) hzero (hboundary 0)
  have hnonzero : cap5BoundaryWordOfEdges boundaryEdge C 0 ≠ 0 :=
    cap5BoundaryWordOfEdges_isNonzero_of_isTaitEdgeColoring boundaryEdge C hC 0
  exact hnonzero hzero0

namespace CAP5BoundaryEdgeEnumeration

/-- Enumeration form of CAP5 boundary nonzero-ness for Tait edge colorings. -/
theorem cap5BoundaryWord_isNonzero_of_isTaitEdgeColoring
    [DecidableEq V] {G : SimpleGraph V} {support : Finset G.edgeSet}
    (enum : CAP5BoundaryEdgeEnumeration support)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C) :
    CAP5BoundaryWordIsNonzero (cap5BoundaryWordOfEdges enum.boundaryEdge C) :=
  cap5BoundaryWordOfEdges_isNonzero_of_isTaitEdgeColoring enum.boundaryEdge C hC

/-- Enumeration form of graph-facing CAP5 parity. -/
theorem cap5BoundaryWord_hasOddColorCounts_of_isTaitEdgeColoring_of_isZeroBoundary_at
    {U : Type*} [DecidableEq V] {G : SimpleGraph V}
    {D : ZeroBoundaryData U G.edgeSet} {v : U}
    (enum : CAP5BoundaryEdgeEnumeration (D.incident v)) (C : G.EdgeColoring Color)
    (hC : IsTaitEdgeColoring G C) (hzero : D.isZeroBoundary C) :
    CAP5BoundaryWordHasOddColorCounts (cap5BoundaryWordOfEdges enum.boundaryEdge C) :=
  cap5BoundaryWordOfEdges_hasOddColorCounts_of_isTaitEdgeColoring_of_isZeroBoundary_at
    enum.boundaryEdge C hC enum.injective enum.incident_eq_map hzero

/-- Enumeration form of the full-zero-boundary-set CAP5 parity theorem. -/
theorem cap5BoundaryWord_hasOddColorCounts_of_isTaitEdgeColoring_of_mem_zeroBoundarySet_at
    {U : Type*} [DecidableEq V] {G : SimpleGraph V}
    {D : ZeroBoundaryData U G.edgeSet} {v : U}
    (enum : CAP5BoundaryEdgeEnumeration (D.incident v)) (C : G.EdgeColoring Color)
    (hC : IsTaitEdgeColoring G C)
    (hzero : (C : G.edgeSet → Color) ∈ D.zeroBoundarySet) :
    CAP5BoundaryWordHasOddColorCounts (cap5BoundaryWordOfEdges enum.boundaryEdge C) :=
  enum.cap5BoundaryWord_hasOddColorCounts_of_isTaitEdgeColoring_of_isZeroBoundary_at C hC
    hzero.1

/-- Enumeration form of the graph-facing CAP5 block classifier. -/
theorem cap5BoundaryWord_coloredBlock311_or_coloredBlock2111_of_isTaitEdgeColoring_of_isZeroBoundary_at
    {U : Type*} [DecidableEq V] {G : SimpleGraph V}
    {D : ZeroBoundaryData U G.edgeSet} {v : U}
    (enum : CAP5BoundaryEdgeEnumeration (D.incident v)) (C : G.EdgeColoring Color)
    (hC : IsTaitEdgeColoring G C) (hzero : D.isZeroBoundary C) :
    CAP5BoundaryWordHasColoredBlock311 (cap5BoundaryWordOfEdges enum.boundaryEdge C) ∨
      CAP5BoundaryWordHasColoredBlock2111 (cap5BoundaryWordOfEdges enum.boundaryEdge C) :=
  cap5BoundaryWordOfEdges_coloredBlock311_or_coloredBlock2111_of_isTaitEdgeColoring_of_isZeroBoundary_at
    enum.boundaryEdge C hC enum.injective enum.incident_eq_map hzero

/-- Enumeration form of the full-zero-boundary-set CAP5 block classifier. -/
theorem cap5BoundaryWord_coloredBlock311_or_coloredBlock2111_of_isTaitEdgeColoring_of_mem_zeroBoundarySet_at
    {U : Type*} [DecidableEq V] {G : SimpleGraph V}
    {D : ZeroBoundaryData U G.edgeSet} {v : U}
    (enum : CAP5BoundaryEdgeEnumeration (D.incident v)) (C : G.EdgeColoring Color)
    (hC : IsTaitEdgeColoring G C)
    (hzero : (C : G.edgeSet → Color) ∈ D.zeroBoundarySet) :
    CAP5BoundaryWordHasColoredBlock311 (cap5BoundaryWordOfEdges enum.boundaryEdge C) ∨
      CAP5BoundaryWordHasColoredBlock2111 (cap5BoundaryWordOfEdges enum.boundaryEdge C) :=
  enum.cap5BoundaryWord_coloredBlock311_or_coloredBlock2111_of_isTaitEdgeColoring_of_isZeroBoundary_at
    C hC hzero.1

/-- Enumeration form of the graph-facing CAP5 nonextension criterion. -/
theorem cap5BoundaryWord_not_extendsAcrossCycle_iff_coloredBlock2111_of_isTaitEdgeColoring_of_isZeroBoundary_at
    {U : Type*} [DecidableEq V] {G : SimpleGraph V}
    {D : ZeroBoundaryData U G.edgeSet} {v : U}
    (enum : CAP5BoundaryEdgeEnumeration (D.incident v)) (C : G.EdgeColoring Color)
    (hC : IsTaitEdgeColoring G C) (hzero : D.isZeroBoundary C) :
    ¬ CAP5WordExtendsAcrossCycle (cap5BoundaryWordOfEdges enum.boundaryEdge C) ↔
      CAP5BoundaryWordHasColoredBlock2111 (cap5BoundaryWordOfEdges enum.boundaryEdge C) :=
  cap5BoundaryWordOfEdges_not_extendsAcrossCycle_iff_coloredBlock2111_of_isTaitEdgeColoring_of_isZeroBoundary_at
    enum.boundaryEdge C hC enum.injective enum.incident_eq_map hzero

/-- Enumeration form of the full-zero-boundary-set CAP5 nonextension criterion. -/
theorem cap5BoundaryWord_not_extendsAcrossCycle_iff_coloredBlock2111_of_isTaitEdgeColoring_of_mem_zeroBoundarySet_at
    {U : Type*} [DecidableEq V] {G : SimpleGraph V}
    {D : ZeroBoundaryData U G.edgeSet} {v : U}
    (enum : CAP5BoundaryEdgeEnumeration (D.incident v)) (C : G.EdgeColoring Color)
    (hC : IsTaitEdgeColoring G C)
    (hzero : (C : G.edgeSet → Color) ∈ D.zeroBoundarySet) :
    ¬ CAP5WordExtendsAcrossCycle (cap5BoundaryWordOfEdges enum.boundaryEdge C) ↔
      CAP5BoundaryWordHasColoredBlock2111 (cap5BoundaryWordOfEdges enum.boundaryEdge C) :=
  enum.cap5BoundaryWord_not_extendsAcrossCycle_iff_coloredBlock2111_of_isTaitEdgeColoring_of_isZeroBoundary_at
    C hC hzero.1

/-- Pulling an indexed support through a boundary enumeration and then restricting back to
boundary positions recovers the original indexed support. -/
theorem cap5BoundarySupportOfEdges_map
    {E : Type*} [DecidableEq E] {support : Finset E}
    (enum : CAP5BoundaryEdgeEnumeration support)
    (T : Finset (Fin 5)) :
    cap5BoundarySupportOfEdges enum.boundaryEdge
      (T.map ⟨enum.boundaryEdge, enum.injective⟩) = T := by
  apply Finset.ext
  intro i
  constructor
  · intro hi
    rw [mem_cap5BoundarySupportOfEdges_iff] at hi
    rcases Finset.mem_map.1 hi with ⟨j, hj, hji⟩
    have hji' : j = i := enum.injective hji
    simpa [hji'] using hj
  · intro hi
    rw [mem_cap5BoundarySupportOfEdges_iff]
    exact Finset.mem_map.2 ⟨i, hi, rfl⟩

/-- If a boundary coloring is the canonical bad CAP5 word and an edge set restricts to the
support of a finite repair type, switching that edge set repairs the boundary word. -/
theorem cap5BoundaryWord_switch_extendsAcrossCycle_of_badBoundaryWord_of_repairTypeSupport
    {E : Type*} [DecidableEq E] {support : Finset E}
    (enum : CAP5BoundaryEdgeEnumeration support)
    (C : E → Color) (S : Finset E) (τ : CAP5RepairType)
    (hword : cap5BoundaryWordOfEdges enum.boundaryEdge C = cap5BadBoundaryWord2111)
    (hsupport : cap5BoundarySupportOfEdges enum.boundaryEdge S = τ.support) :
    CAP5WordExtendsAcrossCycle
      (cap5BoundaryWordOfEdges enum.boundaryEdge
        (switch (τ.colorPair).1 (τ.colorPair).2 (S : Set E) C)) := by
  rw [cap5BoundaryWordOfEdges_switch_eq_boundarySwap, hsupport, hword]
  simpa [CAP5RepairType.apply] using τ.apply_bad_extendsAcrossCycle

/-- Repair-type support image form of the edge-level CAP5 repair bridge.  A concrete finite
sample can use the image of `τ.support` under its boundary enumeration as the actual graph-edge
switch support. -/
theorem cap5BoundaryWord_switch_extendsAcrossCycle_of_badBoundaryWord_of_repairType
    {E : Type*} [DecidableEq E] {support : Finset E}
    (enum : CAP5BoundaryEdgeEnumeration support)
    (C : E → Color) (τ : CAP5RepairType)
    (hword : cap5BoundaryWordOfEdges enum.boundaryEdge C = cap5BadBoundaryWord2111) :
    CAP5WordExtendsAcrossCycle
      (cap5BoundaryWordOfEdges enum.boundaryEdge
        (switch (τ.colorPair).1 (τ.colorPair).2
          ((τ.support.map ⟨enum.boundaryEdge, enum.injective⟩ : Finset E) : Set E) C)) := by
  exact cap5BoundaryWord_switch_extendsAcrossCycle_of_badBoundaryWord_of_repairTypeSupport enum
    C (τ.support.map ⟨enum.boundaryEdge, enum.injective⟩) τ hword
    (cap5BoundarySupportOfEdges_map enum τ.support)

/-- Canonical finite five-edge boundary enumeration used by the CAP5 boundary generator smoke
tests.  It deliberately has no graph-embedding content: it only checks the boundary-word
classification layer that a later graph generator consumes. -/
def canonicalFinFive :
    CAP5BoundaryEdgeEnumeration (Finset.univ : Finset (Fin 5)) where
  boundaryEdge := fun i => i
  injective := fun _ _ h => h
  support_eq := by
    ext i
    simp

@[simp] theorem canonicalFinFive_boundaryEdge (i : Fin 5) :
    canonicalFinFive.boundaryEdge i = i :=
  rfl

/-- Canonical good `(3,1,1)` boundary-edge coloring for the finite CAP5 boundary sample. -/
def canonicalGoodColoring : Fin 5 → Color :=
  cap5GoodBoundaryWord311

/-- Canonical bad `(2,1,1,1)` boundary-edge coloring for the finite CAP5 boundary sample. -/
def canonicalBadColoring : Fin 5 → Color :=
  cap5BadBoundaryWord2111

@[simp] theorem canonicalGoodBoundaryWord :
    cap5BoundaryWordOfEdges canonicalFinFive.boundaryEdge canonicalGoodColoring =
      cap5GoodBoundaryWord311 := by
  funext i
  rfl

@[simp] theorem canonicalBadBoundaryWord :
    cap5BoundaryWordOfEdges canonicalFinFive.boundaryEdge canonicalBadColoring =
      cap5BadBoundaryWord2111 := by
  funext i
  rfl

/-- The canonical finite good sample is in the CAP5 extendable bin. -/
theorem canonicalGoodBoundaryWord_extendsAcrossCycle :
    CAP5WordExtendsAcrossCycle
      (cap5BoundaryWordOfEdges canonicalFinFive.boundaryEdge canonicalGoodColoring) := by
  rw [canonicalGoodBoundaryWord]
  exact cap5GoodBoundaryWord311_extendsAcrossCycle

/-- The canonical finite good sample has the good colored block shape. -/
theorem canonicalGoodBoundaryWord_hasColoredBlock311 :
    CAP5BoundaryWordHasColoredBlock311
      (cap5BoundaryWordOfEdges canonicalFinFive.boundaryEdge canonicalGoodColoring) := by
  rw [canonicalGoodBoundaryWord]
  exact (cap5_extendsAcrossCycle_iff_coloredBlock311).mp
    cap5GoodBoundaryWord311_extendsAcrossCycle

/-- The canonical finite bad sample is in the CAP5 nonextendable bin. -/
theorem not_canonicalBadBoundaryWord_extendsAcrossCycle :
    ¬ CAP5WordExtendsAcrossCycle
      (cap5BoundaryWordOfEdges canonicalFinFive.boundaryEdge canonicalBadColoring) := by
  rw [canonicalBadBoundaryWord]
  exact not_cap5BadBoundaryWord2111_extendsAcrossCycle

/-- The canonical finite bad sample has the bad colored block shape. -/
theorem canonicalBadBoundaryWord_hasColoredBlock2111 :
    CAP5BoundaryWordHasColoredBlock2111
      (cap5BoundaryWordOfEdges canonicalFinFive.boundaryEdge canonicalBadColoring) := by
  rw [canonicalBadBoundaryWord]
  refine ⟨red, blue, purple, isTaitColorTriple_red_blue_purple, 0, ?_⟩
  funext i
  fin_cases i <;> rfl

/-- Every finite repair type repairs the canonical bad finite sample into the extendable bin. -/
theorem canonicalBadBoundaryWord_repairType_extendsAcrossCycle
    (τ : CAP5RepairType) :
    CAP5WordExtendsAcrossCycle
      (τ.apply (cap5BoundaryWordOfEdges canonicalFinFive.boundaryEdge canonicalBadColoring)) := by
  rw [canonicalBadBoundaryWord]
  exact τ.apply_bad_extendsAcrossCycle

/-- Edge-level support form of the canonical bad finite sample: switching the canonical
repair-type support on the five boundary edges repairs the bad boundary word. -/
theorem canonicalBadBoundaryWord_switch_repairType_extendsAcrossCycle
    (τ : CAP5RepairType) :
    CAP5WordExtendsAcrossCycle
      (cap5BoundaryWordOfEdges canonicalFinFive.boundaryEdge
        (switch (τ.colorPair).1 (τ.colorPair).2 (τ.support : Set (Fin 5))
          canonicalBadColoring)) := by
  exact cap5BoundaryWord_switch_extendsAcrossCycle_of_badBoundaryWord_of_repairTypeSupport
    canonicalFinFive canonicalBadColoring τ.support τ canonicalBadBoundaryWord (by
      apply Finset.ext
      intro i
      simp [cap5BoundarySupportOfEdges])

end CAP5BoundaryEdgeEnumeration

end Mettapedia.GraphTheory.FourColor

import Mettapedia.GraphTheory.FourColor.GoertzelV24Rotor
import Mettapedia.GraphTheory.FourColor.GoertzelV24SquareProfile

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The three exterior edges of a facial triangle, in `x,y,z` order. -/
abbrev RotorBoundaryWord := Fin 3 -> Color

/-- The three triangle edges, in `xy,xz,yz` order. -/
abbrev RotorInternalColoring := Fin 3 -> Color

/-- Three portal nodes followed by the three triangle-edge nodes. -/
abbrev RotorLocalNode := Fin 6

def rotorPortalNode (i : Fin 3) : RotorLocalNode :=
  ⟨i.val, by omega⟩

def rotorInternalNode (i : Fin 3) : RotorLocalNode :=
  ⟨i.val + 3, by omega⟩

def RotorUndirectedEdge (u v p q : RotorLocalNode) : Prop :=
  (u = p ∧ v = q) ∨ (u = q ∧ v = p)
  deriving Decidable

/-- The color carried by one node of the six-edge rotor line graph. -/
def rotorLocalNodeColor
    (w : RotorBoundaryWord) (x : RotorInternalColoring) :
    RotorLocalNode -> Color := fun u =>
  if h : u.val < 3 then w ⟨u.val, h⟩ else x ⟨u.val - 3, by omega⟩

/-- Incidence adjacency of the six edges around a triangle: at each corner,
the three incident graph edges form a triangle in the edge-line graph. -/
def RotorLineIncident (u v : RotorLocalNode) : Prop :=
  RotorUndirectedEdge u v (rotorPortalNode 0) (rotorInternalNode 0) ∨
  RotorUndirectedEdge u v (rotorPortalNode 0) (rotorInternalNode 1) ∨
  RotorUndirectedEdge u v (rotorInternalNode 0) (rotorInternalNode 1) ∨
  RotorUndirectedEdge u v (rotorPortalNode 1) (rotorInternalNode 0) ∨
  RotorUndirectedEdge u v (rotorPortalNode 1) (rotorInternalNode 2) ∨
  RotorUndirectedEdge u v (rotorInternalNode 0) (rotorInternalNode 2) ∨
  RotorUndirectedEdge u v (rotorPortalNode 2) (rotorInternalNode 1) ∨
  RotorUndirectedEdge u v (rotorPortalNode 2) (rotorInternalNode 2) ∨
  RotorUndirectedEdge u v (rotorInternalNode 1) (rotorInternalNode 2)
  deriving Decidable

/-- The tracked-color subgraph of the actual six-edge triangle line graph. -/
def RotorLineAdjProp (w : RotorBoundaryWord) (x : RotorInternalColoring)
    (a b : Color) (u v : RotorLocalNode) : Prop :=
  RotorLineIncident u v ∧
    IsTrackedColor a b (rotorLocalNodeColor w x u) ∧
    IsTrackedColor a b (rotorLocalNodeColor w x v)
  deriving Decidable

def RotorLineAdj (w : RotorBoundaryWord) (x : RotorInternalColoring)
    (a b : Color) (u v : RotorLocalNode) : Bool :=
  decide (RotorLineAdjProp w x a b u v)

theorem rotorLineAdj_symm (w : RotorBoundaryWord)
    (x : RotorInternalColoring) (a b : Color) (u v : RotorLocalNode) :
    RotorLineAdj w x a b u v = RotorLineAdj w x a b v u := by
  apply Bool.decide_congr
  unfold RotorLineAdjProp RotorLineIncident RotorUndirectedEdge
  aesop

theorem rotorLineAdj_self (w : RotorBoundaryWord)
    (x : RotorInternalColoring) (a b : Color) (u : RotorLocalNode) :
    RotorLineAdj w x a b u u = false := by
  simp only [RotorLineAdj, decide_eq_false_iff_not]
  fin_cases u <;>
    simp [RotorLineAdjProp, RotorLineIncident, RotorUndirectedEdge,
      rotorPortalNode, rotorInternalNode]

def rotorLineGraph (w : RotorBoundaryWord) (x : RotorInternalColoring)
    (a b : Color) : SimpleGraph RotorLocalNode where
  Adj u v := RotorLineAdj w x a b u v = true
  symm := ⟨by
    intro u v huv
    rw [rotorLineAdj_symm w x a b u v] at huv
    exact huv⟩
  loopless := ⟨by
    intro u huu
    rw [rotorLineAdj_self w x a b u] at huu
    contradiction⟩

abbrev RotorTrackedProfile := Fin 3 -> Fin 3 -> Bool

/-- Portal connectivity computed from the actual six-edge triangle line
graph for one tracked color pair. -/
def rotorLineTrackedProfile (w : RotorBoundaryWord)
    (x : RotorInternalColoring) (a b : Color) : RotorTrackedProfile :=
  fun i j =>
    decide (IsTrackedColor a b (w i)) &&
    decide (IsTrackedColor a b (w j)) &&
    decide (rotorPortalNode j ∈
      finsetReachWithin (RotorLineAdj w x a b) (rotorPortalNode i) 6)

/-- The computed rotor profile is ordinary reachability in the local
tracked-color edge-line graph. -/
theorem rotorLineTrackedProfile_eq_true_iff
    (w : RotorBoundaryWord) (x : RotorInternalColoring)
    (a b : Color) (i j : Fin 3) :
    rotorLineTrackedProfile w x a b i j = true ↔
      IsTrackedColor a b (w i) ∧ IsTrackedColor a b (w j) ∧
      (rotorLineGraph w x a b).Reachable
        (rotorPortalNode i) (rotorPortalNode j) := by
  unfold rotorLineTrackedProfile
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  have hreach :
      rotorPortalNode j ∈
          finsetReachWithin (RotorLineAdj w x a b) (rotorPortalNode i) 6 ↔
        (rotorLineGraph w x a b).Reachable
          (rotorPortalNode i) (rotorPortalNode j) := by
    simpa using mem_finsetReachWithin_card_iff_reachable
      (rotorLineGraph w x a b) (RotorLineAdj w x a b)
      (by intros; rfl) (rotorPortalNode i) (rotorPortalNode j)
  rw [hreach]
  tauto

theorem rotorLineTrackedProfile_symmetric
    (w : RotorBoundaryWord) (x : RotorInternalColoring)
    (a b : Color) (i j : Fin 3) :
    rotorLineTrackedProfile w x a b i j =
      rotorLineTrackedProfile w x a b j i := by
  rw [Bool.eq_iff_iff, rotorLineTrackedProfile_eq_true_iff,
    rotorLineTrackedProfile_eq_true_iff]
  constructor
  · rintro ⟨hi, hj, hij⟩
    exact ⟨hj, hi, hij.symm⟩
  · rintro ⟨hj, hi, hji⟩
    exact ⟨hi, hj, hji.symm⟩

/-- At a contracted cubic vertex, every pair of active incident edges lies in
one component of the tracked edge-line graph. -/
def contractedVertexTrackedProfile
    (w : RotorBoundaryWord) (a b : Color) : RotorTrackedProfile :=
  fun i j =>
    decide (IsTrackedColor a b (w i)) &&
    decide (IsTrackedColor a b (w j))

theorem contractedVertexTrackedProfile_symmetric
    (w : RotorBoundaryWord) (a b : Color) (i j : Fin 3) :
    contractedVertexTrackedProfile w a b i j =
      contractedVertexTrackedProfile w a b j i := by
  simp [contractedVertexTrackedProfile, Bool.and_comm]

/-- Computed local properness for the six rotor edges. It states nonzero
colors and pairwise distinct colors at each of the three triangle corners. -/
def RotorLocalTait
    (w : RotorBoundaryWord) (x : RotorInternalColoring) : Prop :=
  (∀ i, w i ≠ 0) ∧ (∀ i, x i ≠ 0) ∧
  (w 0 ≠ x 0 ∧ w 0 ≠ x 1 ∧ x 0 ≠ x 1) ∧
  (w 1 ≠ x 0 ∧ w 1 ≠ x 2 ∧ x 0 ≠ x 2) ∧
  (w 2 ≠ x 1 ∧ w 2 ≠ x 2 ∧ x 1 ≠ x 2)
  deriving Decidable

private theorem rotorLineProfile_eq_contractedVertexProfile_check :
    ∀ w : RotorBoundaryWord, ∀ x : RotorInternalColoring,
      ∀ a b : Color,
      ¬ RotorLocalTait w x ∨ a = 0 ∨ b = 0 ∨ a = b ∨
        rotorLineTrackedProfile w x a b =
          contractedVertexTrackedProfile w a b := by
  decide

/-- Finite rotor kernel: every locally proper nonzero coloring of a facial
triangle has exactly the tracked portal profile of the contracted cubic
vertex, for every genuine pair of tracked colors. -/
theorem rotorLineProfile_eq_contractedVertexProfile
    (w : RotorBoundaryWord) (x : RotorInternalColoring)
    (a b : Color) (hLocal : RotorLocalTait w x)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    rotorLineTrackedProfile w x a b =
      contractedVertexTrackedProfile w a b := by
  rcases rotorLineProfile_eq_contractedVertexProfile_check w x a b with
    hbad | ha0 | hb0 | hab0 | h
  · exact False.elim (hbad hLocal)
  · exact False.elim (ha ha0)
  · exact False.elim (hb hb0)
  · exact False.elim (hab hab0)
  · exact h

/-- A local portal profile embedded in a finite common interface. -/
def finitePortalProfileOnInterface {P B : Type*}
    (localProfile : P -> P -> Bool) : Sum P B -> Sum P B -> Bool :=
  fun u v => match u, v with
  | .inl i, .inl j => localProfile i j
  | _, _ => false

def BooleanProfile.Symmetric {N : Type*}
    (profile : N -> N -> Bool) : Prop :=
  ∀ u v, profile u v = profile v u

def finitePortalLinked {P B : Type*}
    (external : Sum P B -> Sum P B -> Bool)
    (localProfile : P -> P -> Bool) (u v : Sum P B) : Bool :=
  external u v || finitePortalProfileOnInterface (B := B) localProfile u v

def finitePortalAdj {P B : Type*} [DecidableEq P] [DecidableEq B]
    (external : Sum P B -> Sum P B -> Bool)
    (localProfile : P -> P -> Bool) (u v : Sum P B) : Bool :=
  decide (u ≠ v) && finitePortalLinked external localProfile u v

theorem finitePortalLinked_symm {P B : Type*}
    (external : Sum P B -> Sum P B -> Bool)
    (localProfile : P -> P -> Bool)
    (hext : BooleanProfile.Symmetric external)
    (hloc : BooleanProfile.Symmetric localProfile) (u v : Sum P B) :
    finitePortalLinked external localProfile u v =
      finitePortalLinked external localProfile v u := by
  unfold finitePortalLinked
  cases u with
  | inl i =>
      cases v with
      | inl j =>
          simp only [finitePortalProfileOnInterface]
          rw [hext, hloc]
      | inr y =>
          simp only [finitePortalProfileOnInterface, Bool.or_false]
          rw [hext]
  | inr x =>
      cases v with
      | inl j =>
          simp only [finitePortalProfileOnInterface, Bool.or_false]
          rw [hext]
      | inr y =>
          simp only [finitePortalProfileOnInterface, Bool.or_false]
          rw [hext]

def finitePortalGraph {P B : Type*} [DecidableEq P] [DecidableEq B]
    (external : Sum P B -> Sum P B -> Bool)
    (localProfile : P -> P -> Bool)
    (hext : BooleanProfile.Symmetric external)
    (hloc : BooleanProfile.Symmetric localProfile) : SimpleGraph (Sum P B) where
  Adj u v := finitePortalAdj external localProfile u v = true
  symm := ⟨by
    intro u v huv
    unfold finitePortalAdj at huv ⊢
    rw [finitePortalLinked_symm external localProfile hext hloc u v] at huv
    simpa [ne_comm] using huv⟩
  loopless := ⟨by
    intro u huu
    simp [finitePortalAdj] at huu⟩

/-- Finite closure of the union of an exterior interface relation and a local
portal relation. This is the compositional meaning of a local profile. -/
def composeFinitePortalProfile {P B : Type*}
    [Fintype P] [DecidableEq P] [Fintype B] [DecidableEq B]
    (external : Sum P B -> Sum P B -> Bool)
    (localProfile : P -> P -> Bool) : Sum P B -> Sum P B -> Bool :=
  let local' := finitePortalProfileOnInterface (B := B) localProfile
  let linked := fun u v => external u v || local' u v
  let adj := fun u v => decide (u ≠ v) && linked u v
  fun u v => linked u u && linked v v &&
    decide (v ∈ finsetReachWithin adj u (Fintype.card (Sum P B)))

/-- Finite portal composition is ordinary reachability in the graph formed by
the union of the exterior and local component relations. -/
theorem composeFinitePortalProfile_eq_true_iff
    {P B : Type*} [Fintype P] [DecidableEq P]
    [Fintype B] [DecidableEq B]
    (external : Sum P B -> Sum P B -> Bool)
    (localProfile : P -> P -> Bool)
    (hext : BooleanProfile.Symmetric external)
    (hloc : BooleanProfile.Symmetric localProfile) (u v : Sum P B) :
    composeFinitePortalProfile external localProfile u v = true ↔
      finitePortalLinked external localProfile u u = true ∧
      finitePortalLinked external localProfile v v = true ∧
      (finitePortalGraph external localProfile hext hloc).Reachable u v := by
  unfold composeFinitePortalProfile
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  change
    ((finitePortalLinked external localProfile u u = true ∧
        finitePortalLinked external localProfile v v = true) ∧
      v ∈ finsetReachWithin (finitePortalAdj external localProfile) u
        (Fintype.card (Sum P B))) ↔ _
  have hreach :
      v ∈ finsetReachWithin (finitePortalAdj external localProfile) u
          (Fintype.card (Sum P B)) ↔
        (finitePortalGraph external localProfile hext hloc).Reachable u v := by
    simpa using mem_finsetReachWithin_card_iff_reachable
      (finitePortalGraph external localProfile hext hloc)
      (finitePortalAdj external localProfile) (by intros; rfl) u v
  rw [hreach]
  tauto

theorem composeFinitePortalProfile_congr_local
    {P B : Type*} [Fintype P] [DecidableEq P]
    [Fintype B] [DecidableEq B]
    (external : Sum P B -> Sum P B -> Bool)
    {localProfile replacementProfile : P -> P -> Bool}
    (hprofile : localProfile = replacementProfile) :
    composeFinitePortalProfile external localProfile =
      composeFinitePortalProfile external replacementProfile := by
  rw [hprofile]

namespace RotationSystem

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]
variable (RS : RotationSystem V E)

namespace FacialTriangleData

def boundaryWord (T : @FacialTriangleData V E)
    (C : E -> Color) : RotorBoundaryWord := fun i =>
  if i = 0 then C T.outerX else if i = 1 then C T.outerY else C T.outerZ

def internalColoring (T : @FacialTriangleData V E)
    (C : E -> Color) : RotorInternalColoring := fun i =>
  if i = 0 then C T.xy else if i = 1 then C T.xz else C T.yz

end FacialTriangleData

/-- The computed local rotor premises follow from the rotation-system
incidence equalities, cubicity, and the actual Tait coloring. -/
theorem facialTriangle_rotorLocalTait
    (T : @FacialTriangleData V E) (hT : T.WellFormed RS)
    (hCubic : RS.IsCubic)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C) :
    RotorLocalTait (T.boundaryWord C) (T.internalColoring C) := by
  have hdistinct := RS.facialTriangle_incidentEdgeDistinctness T hT hCubic
  have hxOuterMem : T.outerX ∈ RS.incidentEdges T.x := by rw [hT.2.1]; simp
  have hxXYMem : T.xy ∈ RS.incidentEdges T.x := by rw [hT.2.1]; simp
  have hxXZMem : T.xz ∈ RS.incidentEdges T.x := by rw [hT.2.1]; simp
  have hyOuterMem : T.outerY ∈ RS.incidentEdges T.y := by rw [hT.2.2.1]; simp
  have hyXYMem : T.xy ∈ RS.incidentEdges T.y := by rw [hT.2.2.1]; simp
  have hyYZMem : T.yz ∈ RS.incidentEdges T.y := by rw [hT.2.2.1]; simp
  have hzOuterMem : T.outerZ ∈ RS.incidentEdges T.z := by rw [hT.2.2.2.1]; simp
  have hzXZMem : T.xz ∈ RS.incidentEdges T.z := by rw [hT.2.2.2.1]; simp
  have hzYZMem : T.yz ∈ RS.incidentEdges T.z := by rw [hT.2.2.2.1]; simp
  have hx01 : C T.outerX ≠ C T.xy := C.valid
    (RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
      hdistinct.1.1 hxOuterMem hxXYMem)
  have hx02 : C T.outerX ≠ C T.xz := C.valid
    (RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
      hdistinct.1.2.1 hxOuterMem hxXZMem)
  have hx12 : C T.xy ≠ C T.xz := C.valid
    (RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
      hdistinct.1.2.2 hxXYMem hxXZMem)
  have hy01 : C T.outerY ≠ C T.xy := C.valid
    (RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
      hdistinct.2.1.1 hyOuterMem hyXYMem)
  have hy02 : C T.outerY ≠ C T.yz := C.valid
    (RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
      hdistinct.2.1.2.1 hyOuterMem hyYZMem)
  have hy12 : C T.xy ≠ C T.yz := C.valid
    (RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
      hdistinct.2.1.2.2 hyXYMem hyYZMem)
  have hz01 : C T.outerZ ≠ C T.xz := C.valid
    (RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
      hdistinct.2.2.1 hzOuterMem hzXZMem)
  have hz02 : C T.outerZ ≠ C T.yz := C.valid
    (RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
      hdistinct.2.2.2.1 hzOuterMem hzYZMem)
  have hz12 : C T.xz ≠ C T.yz := C.valid
    (RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
      hdistinct.2.2.2.2 hzXZMem hzYZMem)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · simpa [FacialTriangleData.boundaryWord] using hC T.outerX
    · simpa [FacialTriangleData.boundaryWord] using hC T.outerY
    · simpa [FacialTriangleData.boundaryWord] using hC T.outerZ
  · intro i
    fin_cases i
    · simpa [FacialTriangleData.internalColoring] using hC T.xy
    · simpa [FacialTriangleData.internalColoring] using hC T.xz
    · simpa [FacialTriangleData.internalColoring] using hC T.yz
  · simpa [FacialTriangleData.boundaryWord,
      FacialTriangleData.internalColoring] using ⟨hx01, hx02, hx12⟩
  · simpa [FacialTriangleData.boundaryWord,
      FacialTriangleData.internalColoring] using ⟨hy01, hy02, hy12⟩
  · simpa [FacialTriangleData.boundaryWord,
      FacialTriangleData.internalColoring] using ⟨hz01, hz02, hz12⟩

/-- Rotation-system rotor profile theorem: the profile is computed from the
stored coloring of the six named edges, and its equality with contraction is
derived rather than included in the facial-triangle data. -/
theorem facialTriangle_rotorProfile_eq_contractedVertexProfile
    (T : @FacialTriangleData V E) (hT : T.WellFormed RS)
    (hCubic : RS.IsCubic)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (a b : Color) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    rotorLineTrackedProfile (T.boundaryWord C) (T.internalColoring C) a b =
      contractedVertexTrackedProfile (T.boundaryWord C) a b := by
  exact rotorLineProfile_eq_contractedVertexProfile _ _ a b
    (RS.facialTriangle_rotorLocalTait T hT hCubic C hC) ha hb hab

/-- The actual rotor profile remains interchangeable with the contracted
vertex after gluing any finite exterior connectivity profile. -/
theorem facialTriangle_composedRotorProfile_eq_contractedVertexProfile
    (T : @FacialTriangleData V E) (hT : T.WellFormed RS)
    (hCubic : RS.IsCubic)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (a b : Color) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    {B : Type*} [Fintype B] [DecidableEq B]
    (external : Sum (Fin 3) B -> Sum (Fin 3) B -> Bool) :
    composeFinitePortalProfile external
        (rotorLineTrackedProfile
          (T.boundaryWord C) (T.internalColoring C) a b) =
      composeFinitePortalProfile external
        (contractedVertexTrackedProfile (T.boundaryWord C) a b) := by
  apply composeFinitePortalProfile_congr_local
  exact RS.facialTriangle_rotorProfile_eq_contractedVertexProfile
    T hT hCubic C hC a b ha hb hab

end RotationSystem

end Mettapedia.GraphTheory.FourColor

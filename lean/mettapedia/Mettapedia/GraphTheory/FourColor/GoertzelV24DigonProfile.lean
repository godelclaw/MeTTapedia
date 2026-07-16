import Mettapedia.GraphTheory.FourColor.GoertzelV24Digon
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotorProfile

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

abbrev DigonBoundaryWord := Fin 2 -> Color
abbrev DigonInternalColoring := Fin 2 -> Color
abbrev DigonLocalNode := Fin 4

def digonPortalNode (i : Fin 2) : DigonLocalNode :=
  ⟨i.val, by omega⟩

def digonInternalNode (i : Fin 2) : DigonLocalNode :=
  ⟨i.val + 2, by omega⟩

def DigonUndirectedEdge (u v p q : DigonLocalNode) : Prop :=
  (u = p ∧ v = q) ∨ (u = q ∧ v = p)
  deriving Decidable

def digonLocalNodeColor
    (w : DigonBoundaryWord) (x : DigonInternalColoring) :
    DigonLocalNode -> Color := fun u =>
  if h : u.val < 2 then w ⟨u.val, h⟩ else x ⟨u.val - 2, by omega⟩

/-- Incidence adjacency of two parallel edges and the two exterior portal
edges. Each endpoint contributes one three-edge clique in the line graph. -/
def DigonLineIncident (u v : DigonLocalNode) : Prop :=
  DigonUndirectedEdge u v (digonPortalNode 0) (digonInternalNode 0) ∨
  DigonUndirectedEdge u v (digonPortalNode 0) (digonInternalNode 1) ∨
  DigonUndirectedEdge u v (digonPortalNode 1) (digonInternalNode 0) ∨
  DigonUndirectedEdge u v (digonPortalNode 1) (digonInternalNode 1) ∨
  DigonUndirectedEdge u v (digonInternalNode 0) (digonInternalNode 1)
  deriving Decidable

def DigonLineAdjProp (w : DigonBoundaryWord) (x : DigonInternalColoring)
    (a b : Color) (u v : DigonLocalNode) : Prop :=
  DigonLineIncident u v ∧
    IsTrackedColor a b (digonLocalNodeColor w x u) ∧
    IsTrackedColor a b (digonLocalNodeColor w x v)
  deriving Decidable

def DigonLineAdj (w : DigonBoundaryWord) (x : DigonInternalColoring)
    (a b : Color) (u v : DigonLocalNode) : Bool :=
  decide (DigonLineAdjProp w x a b u v)

theorem digonLineAdj_symm (w : DigonBoundaryWord)
    (x : DigonInternalColoring) (a b : Color) (u v : DigonLocalNode) :
    DigonLineAdj w x a b u v = DigonLineAdj w x a b v u := by
  apply Bool.decide_congr
  unfold DigonLineAdjProp DigonLineIncident DigonUndirectedEdge
  aesop

theorem digonLineAdj_self (w : DigonBoundaryWord)
    (x : DigonInternalColoring) (a b : Color) (u : DigonLocalNode) :
    DigonLineAdj w x a b u u = false := by
  simp only [DigonLineAdj, decide_eq_false_iff_not]
  fin_cases u <;>
    simp [DigonLineAdjProp, DigonLineIncident, DigonUndirectedEdge,
      digonPortalNode, digonInternalNode]

def digonLineGraph (w : DigonBoundaryWord) (x : DigonInternalColoring)
    (a b : Color) : SimpleGraph DigonLocalNode where
  Adj u v := DigonLineAdj w x a b u v = true
  symm := ⟨by
    intro u v huv
    rw [digonLineAdj_symm w x a b u v] at huv
    exact huv⟩
  loopless := ⟨by
    intro u huu
    rw [digonLineAdj_self w x a b u] at huu
    contradiction⟩

abbrev DigonTrackedProfile := Fin 2 -> Fin 2 -> Bool

def digonLineTrackedProfile (w : DigonBoundaryWord)
    (x : DigonInternalColoring) (a b : Color) : DigonTrackedProfile :=
  fun i j =>
    decide (IsTrackedColor a b (w i)) &&
    decide (IsTrackedColor a b (w j)) &&
    decide (digonPortalNode j ∈
      finsetReachWithin (DigonLineAdj w x a b) (digonPortalNode i) 4)

theorem digonLineTrackedProfile_eq_true_iff
    (w : DigonBoundaryWord) (x : DigonInternalColoring)
    (a b : Color) (i j : Fin 2) :
    digonLineTrackedProfile w x a b i j = true ↔
      IsTrackedColor a b (w i) ∧ IsTrackedColor a b (w j) ∧
      (digonLineGraph w x a b).Reachable
        (digonPortalNode i) (digonPortalNode j) := by
  unfold digonLineTrackedProfile
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  have hreach :
      digonPortalNode j ∈
          finsetReachWithin (DigonLineAdj w x a b) (digonPortalNode i) 4 ↔
        (digonLineGraph w x a b).Reachable
          (digonPortalNode i) (digonPortalNode j) := by
    simpa using mem_finsetReachWithin_card_iff_reachable
      (digonLineGraph w x a b) (DigonLineAdj w x a b)
      (by intros; rfl) (digonPortalNode i) (digonPortalNode j)
  rw [hreach]
  tauto

theorem digonLineTrackedProfile_symmetric
    (w : DigonBoundaryWord) (x : DigonInternalColoring)
    (a b : Color) (i j : Fin 2) :
    digonLineTrackedProfile w x a b i j =
      digonLineTrackedProfile w x a b j i := by
  rw [Bool.eq_iff_iff, digonLineTrackedProfile_eq_true_iff,
    digonLineTrackedProfile_eq_true_iff]
  constructor
  · rintro ⟨hi, hj, hij⟩
    exact ⟨hj, hi, hij.symm⟩
  · rintro ⟨hj, hi, hji⟩
    exact ⟨hi, hj, hji.symm⟩

def suppressedDigonTrackedProfile
    (w : DigonBoundaryWord) (a b : Color) : DigonTrackedProfile :=
  fun i j =>
    decide (IsTrackedColor a b (w i)) &&
    decide (IsTrackedColor a b (w j))

/-- Computed local Tait condition at both endpoints of the digon. -/
def DigonLocalTait
    (w : DigonBoundaryWord) (x : DigonInternalColoring) : Prop :=
  (∀ i, w i ≠ 0) ∧ (∀ i, x i ≠ 0) ∧
  (w 0 ≠ x 0 ∧ w 0 ≠ x 1 ∧ x 0 ≠ x 1) ∧
  (w 1 ≠ x 0 ∧ w 1 ≠ x 1 ∧ x 0 ≠ x 1)
  deriving Decidable

private theorem digonLineProfile_eq_suppressedProfile_check :
    ∀ w : DigonBoundaryWord, ∀ x : DigonInternalColoring,
      ∀ a b : Color,
      ¬ DigonLocalTait w x ∨ a = 0 ∨ b = 0 ∨ a = b ∨
        digonLineTrackedProfile w x a b =
          suppressedDigonTrackedProfile w a b := by
  decide

/-- Every locally proper digon coloring has the portal profile of the single
edge produced by suppression. -/
theorem digonLineProfile_eq_suppressedProfile
    (w : DigonBoundaryWord) (x : DigonInternalColoring)
    (a b : Color) (hLocal : DigonLocalTait w x)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    digonLineTrackedProfile w x a b =
      suppressedDigonTrackedProfile w a b := by
  rcases digonLineProfile_eq_suppressedProfile_check w x a b with
    hbad | ha0 | hb0 | hab0 | h
  · exact False.elim (hbad hLocal)
  · exact False.elim (ha ha0)
  · exact False.elim (hb hb0)
  · exact False.elim (hab hab0)
  · exact h

/-- Boundary condition under which a digon has proper internal extensions. -/
def DigonBoundaryWord.Compatible (w : DigonBoundaryWord) : Prop :=
  w 0 = w 1 ∧ w 0 ≠ 0
  deriving Decidable

def digonExtensions (w : DigonBoundaryWord) : Finset DigonInternalColoring :=
  Finset.univ.filter fun x => DigonLocalTait w x

private theorem digonExtensions_card_eq_two_check :
    ∀ w : DigonBoundaryWord,
      ¬ w.Compatible ∨ (digonExtensions w).card = 2 := by
  decide

/-- A compatible fixed digon boundary has exactly the two internal colorings
obtained by exchanging the other two colors. -/
theorem digonExtensions_card_eq_two
    (w : DigonBoundaryWord) (hw : w.Compatible) :
    (digonExtensions w).card = 2 := by
  exact (digonExtensions_card_eq_two_check w).resolve_left
    (not_not_intro hw)

def digonExtensionProfileMultiset
    (w : DigonBoundaryWord) (a b : Color) : Multiset DigonTrackedProfile :=
  (digonExtensions w).val.map fun x => digonLineTrackedProfile w x a b

def suppressedDigonProfileMultiset
    (w : DigonBoundaryWord) (a b : Color) : Multiset DigonTrackedProfile :=
  {suppressedDigonTrackedProfile w a b,
    suppressedDigonTrackedProfile w a b}

private theorem digonProfileMultiplicityTwo_check :
    ∀ w : DigonBoundaryWord, ∀ a b : Color,
      ¬ w.Compatible ∨ a = 0 ∨ b = 0 ∨ a = b ∨
        digonExtensionProfileMultiset w a b =
          suppressedDigonProfileMultiset w a b := by
  decide

/-- Exact digon routing census: suppression removes a factor of two from
every tracked connectivity profile, with no profile distortion. -/
theorem digonProfileMultiplicityTwo
    (w : DigonBoundaryWord) (a b : Color)
    (hw : w.Compatible) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    digonExtensionProfileMultiset w a b =
      suppressedDigonProfileMultiset w a b := by
  rcases digonProfileMultiplicityTwo_check w a b with
    hbad | ha0 | hb0 | hab0 | h
  · exact False.elim (hbad hw)
  · exact False.elim (ha ha0)
  · exact False.elim (hb hb0)
  · exact False.elim (hab hab0)
  · exact h

namespace RotationSystem

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]
variable (RS : RotationSystem V E)

/-- Two parallel edges together with the exterior edge at each cubic
endpoint. All validity conditions are kept in `WellFormed`. -/
structure DigonPatchData where
  u : V
  v : V
  e : E
  f : E
  outerU : E
  outerV : E

namespace DigonPatchData

def WellFormed (D : @DigonPatchData V E) : Prop :=
  D.u ≠ D.v ∧ RS.AreParallelEdges D.e D.f ∧
  RS.incidentEdges D.u = {D.outerU, D.e, D.f} ∧
  RS.incidentEdges D.v = {D.outerV, D.e, D.f}

def boundaryWord (D : @DigonPatchData V E)
    (C : E -> Color) : DigonBoundaryWord := fun i =>
  if i = 0 then C D.outerU else C D.outerV

def internalColoring (D : @DigonPatchData V E)
    (C : E -> Color) : DigonInternalColoring := fun i =>
  if i = 0 then C D.e else C D.f

end DigonPatchData

omit [Fintype E] in
private theorem digon_triple_pairwise_ne
    {a b c : E} (hcard : ({a, b, c} : Finset E).card = 3) :
    a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  have hab : a ≠ b := by
    intro h
    subst b
    have hle : ({a, c} : Finset E).card ≤ 2 := Finset.card_le_two
    have : ({a, c} : Finset E).card = 3 := by simpa using hcard
    omega
  have hac : a ≠ c := by
    intro h
    subst c
    have hle : ({b, a} : Finset E).card ≤ 2 := Finset.card_le_two
    have : ({b, a} : Finset E).card = 3 := by simpa using hcard
    omega
  have hbc : b ≠ c := by
    intro h
    subst c
    have hle : ({a, b} : Finset E).card ≤ 2 := Finset.card_le_two
    have : ({a, b} : Finset E).card = 3 := by simpa using hcard
    omega
  exact ⟨hab, hac, hbc⟩

/-- Actual cubic digon data induces the computed local Tait condition. -/
theorem digonPatch_localTait
    (D : @DigonPatchData V E) (hD : D.WellFormed RS)
    (hCubic : RS.IsCubic)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C) :
    DigonLocalTait (D.boundaryWord C) (D.internalColoring C) := by
  have huCard : ({D.outerU, D.e, D.f} : Finset E).card = 3 := by
    rw [← hD.2.2.1]
    exact RS.incidentEdges_card_eq_three_of_isCubic hCubic D.u
  have hvCard : ({D.outerV, D.e, D.f} : Finset E).card = 3 := by
    rw [← hD.2.2.2]
    exact RS.incidentEdges_card_eq_three_of_isCubic hCubic D.v
  have huDistinct := digon_triple_pairwise_ne huCard
  have hvDistinct := digon_triple_pairwise_ne hvCard
  have huOuter : D.outerU ∈ RS.incidentEdges D.u := by rw [hD.2.2.1]; simp
  have huE : D.e ∈ RS.incidentEdges D.u := by rw [hD.2.2.1]; simp
  have huF : D.f ∈ RS.incidentEdges D.u := by rw [hD.2.2.1]; simp
  have hvOuter : D.outerV ∈ RS.incidentEdges D.v := by rw [hD.2.2.2]; simp
  have hvE : D.e ∈ RS.incidentEdges D.v := by rw [hD.2.2.2]; simp
  have hvF : D.f ∈ RS.incidentEdges D.v := by rw [hD.2.2.2]; simp
  have hu01 : C D.outerU ≠ C D.e := C.valid
    (RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
      huDistinct.1 huOuter huE)
  have hu02 : C D.outerU ≠ C D.f := C.valid
    (RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
      huDistinct.2.1 huOuter huF)
  have hEF : C D.e ≠ C D.f := C.valid
    (RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
      huDistinct.2.2 huE huF)
  have hv01 : C D.outerV ≠ C D.e := C.valid
    (RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
      hvDistinct.1 hvOuter hvE)
  have hv02 : C D.outerV ≠ C D.f := C.valid
    (RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
      hvDistinct.2.1 hvOuter hvF)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · simpa [DigonPatchData.boundaryWord] using hC D.outerU
    · simpa [DigonPatchData.boundaryWord] using hC D.outerV
  · intro i
    fin_cases i
    · simpa [DigonPatchData.internalColoring] using hC D.e
    · simpa [DigonPatchData.internalColoring] using hC D.f
  · simpa [DigonPatchData.boundaryWord,
      DigonPatchData.internalColoring] using ⟨hu01, hu02, hEF⟩
  · simpa [DigonPatchData.boundaryWord,
      DigonPatchData.internalColoring] using ⟨hv01, hv02, hEF⟩

private theorem digonLocalTait_boundaryCompatible_check :
    ∀ w : DigonBoundaryWord, ∀ x : DigonInternalColoring,
      ¬ DigonLocalTait w x ∨ w.Compatible := by
  decide

theorem digonBoundary_compatible
    (D : @DigonPatchData V E) (hD : D.WellFormed RS)
    (hCubic : RS.IsCubic)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C) :
    (D.boundaryWord C).Compatible := by
  have hLocal := RS.digonPatch_localTait D hD hCubic C hC
  exact (digonLocalTait_boundaryCompatible_check
    (D.boundaryWord C) (D.internalColoring C)).resolve_left
      (not_not_intro hLocal)

theorem digonPatch_profile_eq_suppressedProfile
    (D : @DigonPatchData V E) (hD : D.WellFormed RS)
    (hCubic : RS.IsCubic)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (a b : Color) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    digonLineTrackedProfile
        (D.boundaryWord C) (D.internalColoring C) a b =
      suppressedDigonTrackedProfile (D.boundaryWord C) a b := by
  exact digonLineProfile_eq_suppressedProfile _ _ a b
    (RS.digonPatch_localTait D hD hCubic C hC) ha hb hab

theorem digonPatch_composedProfile_eq_suppressedProfile
    (D : @DigonPatchData V E) (hD : D.WellFormed RS)
    (hCubic : RS.IsCubic)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (a b : Color) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    {B : Type*} [Fintype B] [DecidableEq B]
    (external : Sum (Fin 2) B -> Sum (Fin 2) B -> Bool) :
    composeFinitePortalProfile external
        (digonLineTrackedProfile
          (D.boundaryWord C) (D.internalColoring C) a b) =
      composeFinitePortalProfile external
        (suppressedDigonTrackedProfile (D.boundaryWord C) a b) := by
  apply composeFinitePortalProfile_congr_local
  exact RS.digonPatch_profile_eq_suppressedProfile
    D hD hCubic C hC a b ha hb hab

end RotationSystem

end Mettapedia.GraphTheory.FourColor

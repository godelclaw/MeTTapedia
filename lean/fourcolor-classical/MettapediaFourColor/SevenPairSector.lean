import MettapediaFourColor.SevenPairSectorData
import MettapediaFourColor.PuncturedPairCharge

/-!
# A joint seven-pair sector forces a further high vertex

The two centres share the same facial reading and signed edge transfer.
In the stated degree profile the second centre receives at least eleven
net units if the three marked outer vertices are low. Its initial charge
is minus ten, so it cannot be flat. This is a geometric subclass, not a
classification of every flat pair. Distant patch labels may coincide.
-/

namespace FourColor.SevenPairSector

set_option maxRecDepth 65536
set_option linter.style.setOption false
set_option maxHeartbeats 0

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open NearLinearCharge NearLinearRuleData RuleTraversal
open ExceptionalOverlap ExceptionalCoreOrientation
open SevenPairSectorData hiding Turn Step State

abbrev Label := SevenPairSectorData.Point
open scoped BigOperators

local instance (r : Fin 84) : NeZero (size r) :=
  ⟨by have := (headers r).1; omega⟩

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] (rotation : Data G)

/-- One shared facial chart, with no global injectivity assumption. -/
structure Reading where
  vertex : Label → V
  faces : ∀ i, Corner rotation (vertex (face i).1)
    (vertex (face i).2.1) (vertex (face i).2.2)

variable {rotation} (x : Reading rotation) (tri : Triangular rotation)

include tri

namespace Reading

theorem corner {a b c : Label} (h : SevenPairSectorData.Turn a b c) :
    Corner rotation (x.vertex a) (x.vertex b) (x.vertex c) := by
  obtain ⟨i, h | h | h⟩ := turn_faces h
  · simpa only [h] using x.faces i
  · simpa only [h] using Corner.rotate rotation tri (Corner.rotate rotation tri (x.faces i))
  · simpa only [h] using Corner.rotate rotation tri (x.faces i)

theorem edge {a b : Label} (h : Edge a b) : G.Adj (x.vertex a) (x.vertex b) := by
  have direct {u v : Label} (ht : tipCode u v ≠ 0) :
      G.Adj (x.vertex u) (x.vertex v) := by
    have hf := x.faces (witness u v)
    rcases witness_sound u v ht with he | he | he
    · have hh : Corner rotation (x.vertex u) (x.vertex v) (x.vertex (tip u v)) := by
        simpa only [he] using hf
      exact hh.choose
    · have hh : Corner rotation (x.vertex v) (x.vertex (tip u v)) (x.vertex u) := by
        simpa only [he] using hf
      exact hh.choose_spec.choose.symm
    · have hh : Corner rotation (x.vertex (tip u v)) (x.vertex u) (x.vertex v) := by
        simpa only [he] using hf
      exact (Corner.rotate rotation tri hh).choose
  rcases h with h | h
  · exact direct h
  · exact (direct h).symm

def dart (a b : Label) (h : Edge a b) : G.Dart :=
  ⟨(x.vertex a,x.vertex b),x.edge tri h⟩

theorem turn {a b c : Label} (h : SevenPairSectorData.Turn a b c)
    (hab : Edge a b) (hac : Edge a c) :
    rotation.vertexRotation (x.dart tri a b hab) = x.dart tri a c hac :=
  (x.corner tri h).choose_spec.choose_spec

theorem step {p q : SevenPairSectorData.State} (op : Move)
    (hp : Edge p.1 p.2) (hq : Edge q.1 q.2) (h : SevenPairSectorData.Step op p q) :
    move rotation op (x.dart tri p.1 p.2 hp) = x.dart tri q.1 q.2 hq := by
  rcases p with ⟨a,b⟩
  rcases q with ⟨c,d⟩
  cases op with
  | flip => obtain ⟨rfl,rfl⟩ := h; rfl
  | next => obtain ⟨rfl,h⟩ := h; exact x.turn tri h hp hq
  | previous =>
      obtain ⟨rfl,h⟩ := h
      apply rotation.vertexRotation.injective
      change rotation.vertexRotation (rotation.vertexRotation.symm _) = _
      rw [Equiv.apply_symm_apply]
      exact (x.turn tri h hq hp).symm

/-- A checked finite path transports through the one actual chart. -/
theorem path {r : Fin 84} (p : SevenPairSectorData.State) (hp : Edge p.1 p.2)
    (trace : Trace r) (qs : List SevenPairSectorData.State) (h : Valid p trace qs) :
    ∃ he : Edge (finish p qs).1 (finish p qs).2,
      execute rotation (x.dart tri p.1 p.2 hp) trace =
        x.dart tri (finish p qs).1 (finish p qs).2 he := by
  induction trace generalizing p qs with
  | nil =>
      cases qs with
      | nil => exact ⟨hp,rfl⟩
      | cons => exact False.elim h
  | cons head tail ih =>
      cases qs with
      | nil => exact False.elim h
      | cons q qs =>
          obtain ⟨hq,hs,ht⟩ := h
          obtain ⟨he,eq⟩ := ih q hq qs ht
          refine ⟨he,?_⟩
          change execute rotation (move rotation head.1 (x.dart tri p.1 p.2 hp)) tail = _
          rw [x.step tri head.1 hp hq hs]
          exact eq

def occurrence {r : Fin 84} (m : Vertex r → Label) (hm : RuleMap r m)
    (hd : ∀ i, lower r i ≤ G.degree (x.vertex (m i)) ∧
      (upper r i = 0 ∨ G.degree (x.vertex (m i)) ≤ upper r i)) : Occurrence rotation r where
  vertex i := x.vertex (m i)
  edge i j h := x.edge tri (hm.1 i j h)
  degree := hd
  turn i j k hij hik ht := x.turn tri (hm.2 i j k ht) (hm.1 i j hij) (hm.1 i k hik)

end Reading

/-- Degrees actually consumed by the shared source-rule argument. -/
def observed : Finset Label := {0,1,2,3,4,5,6,7,8,9,13,14,15,16,20}

/-- Six of the original chart degrees remain completely unrestricted. -/
def Profile : Prop := ∀ i : Label, i ∈ observed → G.degree (x.vertex i) = degree i

omit tri in
private theorem blocked_observed : ∀ r : Fin 84, r ≠ 15 →
    (blockedEnd r).1 ∈ observed := by
  intro r
  fin_cases r <;> decide +kernel

variable (profile : Profile x)

include profile

/-- The second centre can send charge back only through oriented source rule 009_1.
All other rules are rejected by a checked path to a contradictory retained degree. -/
theorem outgoing_only {r : Fin 84}
    (h : Applies rotation r (x.vertex 1) (x.vertex 0)) : r = 15 := by
  classical
  by_contra ne
  obtain ⟨a,hs,ht⟩ := h
  let d := x.dart tri 1 0 (by decide +kernel)
  have ce := RuleMatcher.candidate_eq rotation d a hs ht
  have checked := blocked_valid r ne
  obtain ⟨he,hpath⟩ := x.path tri (1,0) (by decide +kernel)
    (RuleTraversalData.trace r (blockedVertex r)) (blockedPath r) checked.1
  have observed := congrArg (fun e : G.Dart => e.fst) hpath
  change RuleMatcher.candidate rotation r d (blockedVertex r) =
    x.vertex (finish (1,0) (blockedPath r)).1 at observed
  rw [ce,checked.2.1] at observed
  have hd := a.degree (blockedVertex r)
  rw [observed,profile _ (blocked_observed r ne)] at hd
  exact checked.2.2.2 hd

theorem outgoing_le_one : sent rotation (x.vertex 1) (x.vertex 0) ≤ 1 := by
  classical
  have hb (r : Fin 84) :
      (if Applies rotation r (x.vertex 1) (x.vertex 0) then (amount r : ℤ) else 0) ≤
      if r = 15 then (1 : ℤ) else 0 := by
    split_ifs with h eq
    · subst r; decide +kernel
    · exact False.elim (eq (outgoing_only x tri profile h))
    · norm_num
    · rfl
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun r _ => hb r)
  simpa [sent] using hh

private theorem applies0 :
    Applies rotation 15 (x.vertex 0) (x.vertex 1) := by
  refine ⟨x.occurrence tri map0 map0_valid ?_, rfl, rfl⟩
  intro i
  fin_cases i
  · change 7 ≤ G.degree (x.vertex 0) ∧
      (7 = 0 ∨ G.degree (x.vertex 0) ≤ 7)
    rw [profile 0 (by decide)]
    decide +kernel
  · change 7 ≤ G.degree (x.vertex 1) ∧
      (0 = 0 ∨ G.degree (x.vertex 1) ≤ 0)
    rw [profile 1 (by decide)]
    decide +kernel
  · change 5 ≤ G.degree (x.vertex 7) ∧
      (6 = 0 ∨ G.degree (x.vertex 7) ≤ 6)
    rw [profile 7 (by decide)]
    decide +kernel
  · change 5 ≤ G.degree (x.vertex 6) ∧
      (6 = 0 ∨ G.degree (x.vertex 6) ≤ 6)
    rw [profile 6 (by decide)]
    decide +kernel
  · change 5 ≤ G.degree (x.vertex 5) ∧
      (5 = 0 ∨ G.degree (x.vertex 5) ≤ 5)
    rw [profile 5 (by decide)]
    decide +kernel

private theorem applies1 :
    Applies rotation 17 (x.vertex 0) (x.vertex 1) := by
  refine ⟨x.occurrence tri map1 map1_valid ?_, rfl, rfl⟩
  intro i
  fin_cases i
  · change 7 ≤ G.degree (x.vertex 0) ∧
      (7 = 0 ∨ G.degree (x.vertex 0) ≤ 7)
    rw [profile 0 (by decide)]
    decide +kernel
  · change 7 ≤ G.degree (x.vertex 1) ∧
      (0 = 0 ∨ G.degree (x.vertex 1) ≤ 0)
    rw [profile 1 (by decide)]
    decide +kernel
  · change 5 ≤ G.degree (x.vertex 2) ∧
      (5 = 0 ∨ G.degree (x.vertex 2) ≤ 5)
    rw [profile 2 (by decide)]
    decide +kernel
  · change 5 ≤ G.degree (x.vertex 7) ∧
      (6 = 0 ∨ G.degree (x.vertex 7) ≤ 6)
    rw [profile 7 (by decide)]
    decide +kernel
  · change 5 ≤ G.degree (x.vertex 6) ∧
      (6 = 0 ∨ G.degree (x.vertex 6) ≤ 6)
    rw [profile 6 (by decide)]
    decide +kernel
  · change 5 ≤ G.degree (x.vertex 13) ∧
      (5 = 0 ∨ G.degree (x.vertex 13) ≤ 5)
    rw [profile 13 (by decide)]
    decide +kernel

private theorem applies2 :
    Applies rotation 46 (x.vertex 0) (x.vertex 1) := by
  refine ⟨x.occurrence tri map2 map2_valid ?_, rfl, rfl⟩
  intro i
  fin_cases i
  · change 7 ≤ G.degree (x.vertex 0) ∧
      (7 = 0 ∨ G.degree (x.vertex 0) ≤ 7)
    rw [profile 0 (by decide)]
    decide +kernel
  · change 7 ≤ G.degree (x.vertex 1) ∧
      (0 = 0 ∨ G.degree (x.vertex 1) ≤ 0)
    rw [profile 1 (by decide)]
    decide +kernel
  · change 5 ≤ G.degree (x.vertex 2) ∧
      (5 = 0 ∨ G.degree (x.vertex 2) ≤ 5)
    rw [profile 2 (by decide)]
    decide +kernel
  · change 6 ≤ G.degree (x.vertex 3) ∧
      (6 = 0 ∨ G.degree (x.vertex 3) ≤ 6)
    rw [profile 3 (by decide)]
    decide +kernel
  · change 6 ≤ G.degree (x.vertex 4) ∧
      (6 = 0 ∨ G.degree (x.vertex 4) ≤ 6)
    rw [profile 4 (by decide)]
    decide +kernel
  · change 5 ≤ G.degree (x.vertex 5) ∧
      (5 = 0 ∨ G.degree (x.vertex 5) ≤ 5)
    rw [profile 5 (by decide)]
    decide +kernel

private theorem applies3 :
    Applies rotation 0 (x.vertex 2) (x.vertex 1) := by
  refine ⟨x.occurrence tri map3 map3_valid ?_, rfl, rfl⟩
  intro i
  fin_cases i
  · change 5 ≤ G.degree (x.vertex 2) ∧
      (5 = 0 ∨ G.degree (x.vertex 2) ≤ 5)
    rw [profile 2 (by decide)]
    decide +kernel
  · change 5 ≤ G.degree (x.vertex 1) ∧
      (0 = 0 ∨ G.degree (x.vertex 1) ≤ 0)
    rw [profile 1 (by decide)]
    decide +kernel

private theorem applies4 :
    Applies rotation 1 (x.vertex 8) (x.vertex 1) := by
  refine ⟨x.occurrence tri map4 map4_valid ?_, rfl, rfl⟩
  intro i
  fin_cases i
  · change 5 ≤ G.degree (x.vertex 8) ∧
      (6 = 0 ∨ G.degree (x.vertex 8) ≤ 6)
    rw [profile 8 (by decide)]
    decide +kernel
  · change 7 ≤ G.degree (x.vertex 1) ∧
      (0 = 0 ∨ G.degree (x.vertex 1) ≤ 0)
    rw [profile 1 (by decide)]
    decide +kernel
  · change 5 ≤ G.degree (x.vertex 16) ∧
      (5 = 0 ∨ G.degree (x.vertex 16) ≤ 5)
    rw [profile 16 (by decide)]
    decide +kernel

private theorem applies5 :
    Applies rotation 2 (x.vertex 8) (x.vertex 1) := by
  refine ⟨x.occurrence tri map5 map5_valid ?_, rfl, rfl⟩
  intro i
  fin_cases i
  · change 5 ≤ G.degree (x.vertex 8) ∧
      (6 = 0 ∨ G.degree (x.vertex 8) ≤ 6)
    rw [profile 8 (by decide)]
    decide +kernel
  · change 7 ≤ G.degree (x.vertex 1) ∧
      (0 = 0 ∨ G.degree (x.vertex 1) ≤ 0)
    rw [profile 1 (by decide)]
    decide +kernel
  · change 5 ≤ G.degree (x.vertex 2) ∧
      (5 = 0 ∨ G.degree (x.vertex 2) ≤ 5)
    rw [profile 2 (by decide)]
    decide +kernel

private theorem applies6 :
    Applies rotation 0 (x.vertex 16) (x.vertex 1) := by
  refine ⟨x.occurrence tri map6 map6_valid ?_, rfl, rfl⟩
  intro i
  fin_cases i
  · change 5 ≤ G.degree (x.vertex 16) ∧
      (5 = 0 ∨ G.degree (x.vertex 16) ≤ 5)
    rw [profile 16 (by decide)]
    decide +kernel
  · change 5 ≤ G.degree (x.vertex 1) ∧
      (0 = 0 ∨ G.degree (x.vertex 1) ≤ 0)
    rw [profile 1 (by decide)]
    decide +kernel

private theorem applies7 :
    Applies rotation 2 (x.vertex 15) (x.vertex 1) := by
  refine ⟨x.occurrence tri map7 map7_valid ?_, rfl, rfl⟩
  intro i
  fin_cases i
  · change 5 ≤ G.degree (x.vertex 15) ∧
      (6 = 0 ∨ G.degree (x.vertex 15) ≤ 6)
    rw [profile 15 (by decide)]
    decide +kernel
  · change 7 ≤ G.degree (x.vertex 1) ∧
      (0 = 0 ∨ G.degree (x.vertex 1) ≤ 0)
    rw [profile 1 (by decide)]
    decide +kernel
  · change 5 ≤ G.degree (x.vertex 16) ∧
      (5 = 0 ∨ G.degree (x.vertex 16) ≤ 5)
    rw [profile 16 (by decide)]
    decide +kernel

private theorem applies8 :
    Applies rotation 6 (x.vertex 14) (x.vertex 1) := by
  refine ⟨x.occurrence tri map8 map8_valid ?_, rfl, rfl⟩
  intro i
  fin_cases i
  · change 5 ≤ G.degree (x.vertex 14) ∧
      (6 = 0 ∨ G.degree (x.vertex 14) ≤ 6)
    rw [profile 14 (by decide)]
    decide +kernel
  · change 6 ≤ G.degree (x.vertex 1) ∧
      (0 = 0 ∨ G.degree (x.vertex 1) ≤ 0)
    rw [profile 1 (by decide)]
    decide +kernel
  · change 5 ≤ G.degree (x.vertex 7) ∧
      (6 = 0 ∨ G.degree (x.vertex 7) ≤ 6)
    rw [profile 7 (by decide)]
    decide +kernel
  · change 5 ≤ G.degree (x.vertex 20) ∧
      (6 = 0 ∨ G.degree (x.vertex 20) ≤ 6)
    rw [profile 20 (by decide)]
    decide +kernel
  · change 5 ≤ G.degree (x.vertex 13) ∧
      (5 = 0 ∨ G.degree (x.vertex 13) ≤ 5)
    rw [profile 13 (by decide)]
    decide +kernel

private theorem applies9 (h22 : G.degree (x.vertex 22) = 5) :
    Applies rotation 3 (x.vertex 14) (x.vertex 1) := by
  refine ⟨x.occurrence tri map9 map9_valid ?_, rfl, rfl⟩
  intro i
  fin_cases i
  · change 5 ≤ G.degree (x.vertex 14) ∧
      (6 = 0 ∨ G.degree (x.vertex 14) ≤ 6)
    rw [profile 14 (by decide)]
    decide +kernel
  · change 5 ≤ G.degree (x.vertex 1) ∧
      (0 = 0 ∨ G.degree (x.vertex 1) ≤ 0)
    rw [profile 1 (by decide)]
    decide +kernel
  · change 5 ≤ G.degree (x.vertex 15) ∧
      (6 = 0 ∨ G.degree (x.vertex 15) ≤ 6)
    rw [profile 15 (by decide)]
    decide +kernel
  · change 5 ≤ G.degree (x.vertex 22) ∧
      (5 = 0 ∨ G.degree (x.vertex 22) ≤ 5)
    rw [h22]
    decide

private theorem applies10 (h22 : G.degree (x.vertex 22) = 6)
    (h21 : 5 ≤ G.degree (x.vertex 21) ∧ G.degree (x.vertex 21) ≤ 6)
    (h23 : 5 ≤ G.degree (x.vertex 23) ∧ G.degree (x.vertex 23) ≤ 6) :
    Applies rotation 11 (x.vertex 14) (x.vertex 1) := by
  refine ⟨x.occurrence tri map10 map10_valid ?_, rfl, rfl⟩
  intro i
  fin_cases i
  · change 6 ≤ G.degree (x.vertex 14) ∧
      (6 = 0 ∨ G.degree (x.vertex 14) ≤ 6)
    rw [profile 14 (by decide)]
    decide +kernel
  · change 7 ≤ G.degree (x.vertex 1) ∧
      (0 = 0 ∨ G.degree (x.vertex 1) ≤ 0)
    rw [profile 1 (by decide)]
    decide +kernel
  · change 6 ≤ G.degree (x.vertex 15) ∧
      (6 = 0 ∨ G.degree (x.vertex 15) ≤ 6)
    rw [profile 15 (by decide)]
    decide +kernel
  · change 6 ≤ G.degree (x.vertex 22) ∧
      (6 = 0 ∨ G.degree (x.vertex 22) ≤ 6)
    rw [h22]
    decide
  · change 5 ≤ G.degree (x.vertex 23) ∧
      (6 = 0 ∨ G.degree (x.vertex 23) ≤ 6)
    have := h23
    omega
  · change 5 ≤ G.degree (x.vertex 21) ∧
      (6 = 0 ∨ G.degree (x.vertex 21) ≤ 6)
    have := h21
    omega
  · change 5 ≤ G.degree (x.vertex 16) ∧
      (5 = 0 ∨ G.degree (x.vertex 16) ≤ 5)
    rw [profile 16 (by decide)]
    decide +kernel

private theorem incoming_base :
    3 ≤ sent rotation (x.vertex 0) (x.vertex 1) ∧
    2 ≤ sent rotation (x.vertex 2) (x.vertex 1) ∧
    2 ≤ sent rotation (x.vertex 8) (x.vertex 1) ∧
    2 ≤ sent rotation (x.vertex 16) (x.vertex 1) ∧
    1 ≤ sent rotation (x.vertex 15) (x.vertex 1) ∧
    1 ≤ sent rotation (x.vertex 14) (x.vertex 1) := by
  have bound {a b : V} (rs : Finset (Fin 84))
      (h : ∀ r ∈ rs, Applies rotation r a b) (k : ℤ)
      (hk : (∑ r ∈ rs, (amount r : ℤ)) = k) : k ≤ sent rotation a b := by
    have h := RuleFanCharge.sent_lower rs h
    rwa [hk] at h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply bound {15,17,46} _ 3 (by decide +kernel)
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl
    · exact applies0 x tri profile
    · exact applies1 x tri profile
    · exact applies2 x tri profile
  · apply bound {0} _ 2 (by decide +kernel)
    intro r hr
    rw [Finset.mem_singleton] at hr
    subst r
    exact applies3 x tri profile
  · apply bound {1,2} _ 2 (by decide +kernel)
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact applies4 x tri profile
    · exact applies5 x tri profile
  · apply bound {0} _ 2 (by decide +kernel)
    intro r hr
    rw [Finset.mem_singleton] at hr
    subst r
    exact applies6 x tri profile
  · apply bound {2} _ 1 (by decide +kernel)
    intro r hr
    rw [Finset.mem_singleton] at hr
    subst r
    exact applies7 x tri profile
  · apply bound {6} _ 1 (by decide +kernel)
    intro r hr
    rw [Finset.mem_singleton] at hr
    subst r
    exact applies8 x tri profile

/-- One further unit is forced at the shared six-edge. The five-tip branch
uses rule 003_1; the six-tip branch uses rule 007_1 on the same geometry. -/
theorem incoming_two
    (h21 : 5 ≤ G.degree (x.vertex 21) ∧ G.degree (x.vertex 21) ≤ 6)
    (h22 : 5 ≤ G.degree (x.vertex 22) ∧ G.degree (x.vertex 22) ≤ 6)
    (h23 : 5 ≤ G.degree (x.vertex 23) ∧ G.degree (x.vertex 23) ≤ 6) :
    2 ≤ sent rotation (x.vertex 14) (x.vertex 1) := by
  by_cases five : G.degree (x.vertex 22) = 5
  · have hh := RuleFanCharge.sent_lower (rotation := rotation) {3,6} (by
      intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · exact applies9 x tri profile five
      · exact applies8 x tri profile)
    have hk : (∑ r ∈ ({3,6} : Finset (Fin 84)), (amount r : ℤ)) = 2 := by decide +kernel
    rwa [hk] at hh
  · have hh := RuleFanCharge.sent_lower (rotation := rotation) {6,11} (by
      intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · exact applies8 x tri profile
      · exact applies10 x tri profile (by omega) h21 h23)
    have hk : (∑ r ∈ ({6,11} : Finset (Fin 84)), (amount r : ℤ)) = 2 := by decide +kernel
    rwa [hk] at hh

/-- Cyclic order at the second centre, retaining the common high neighbour. -/
def rim : Fin 7 → Label := ![0,7,14,15,16,8,2]

variable [Fintype V]

/-- The seven facially ordered neighbours are distinct in the actual map. -/
theorem rim_injective (cyclic : rotation.IsVertexwiseCyclic) :
    Function.Injective (fun i : Fin 7 => x.vertex (rim i)) := by
  classical
  apply ExceptionalCoreLocalInjectivity.corner_chain_injective rotation cyclic (x.vertex 1)
    (by decide) (fun i => x.vertex (rim i))
  · intro i
    exact x.edge tri (by fin_cases i <;> decide +kernel)
  · intro i hi
    apply x.corner tri
    have h : ∀ i : Fin 6, SevenPairSectorData.Turn 1
        (rim ⟨i.val,Nat.lt_trans i.isLt (by decide : 6 < 7)⟩)
        (rim ⟨i.val+1,Nat.succ_lt_succ i.isLt⟩) := by decide +kernel
    exact h ⟨i,by omega⟩
  · rw [profile 1 (by decide)]
    decide +kernel

/-- In this retained sector three low outer degrees force positive charge.
The argument uses the shared high-edge outflow bound, not independent budgets. -/
theorem positive (cyclic : rotation.IsVertexwiseCyclic)
    (h21 : 5 ≤ G.degree (x.vertex 21) ∧ G.degree (x.vertex 21) ≤ 6)
    (h22 : 5 ≤ G.degree (x.vertex 22) ∧ G.degree (x.vertex 22) ≤ 6)
    (h23 : 5 ≤ G.degree (x.vertex 23) ∧ G.degree (x.vertex 23) ≤ 6) :
    1 ≤ finalCharge rotation (x.vertex 1) := by
  classical
  let ns := fun i : Fin 7 => x.vertex (rim i)
  have inj : Function.Injective ns := rim_injective x tri profile cyclic
  have adjacent (i : Fin 7) : G.Adj (x.vertex 1) (ns i) :=
    x.edge tri (by fin_cases i <;> decide +kernel)
  have centre : G.degree (x.vertex 1) = 7 := profile 1 (by decide)
  have low (i : Fin 7) (h : i ≠ 0) : G.degree (ns i) ≤ 6 := by
    have hh : ∀ i : Fin 7, i ≠ 0 → rim i ∈ observed ∧ degree (rim i) ≤ 6 := by
      decide +kernel
    rw [show ns i = x.vertex (rim i) from rfl,profile _ (hh i h).1]
    exact (hh i h).2
  have sub : Finset.univ.image ns ⊆ G.neighborFinset (x.vertex 1) := by
    intro w hw
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hw
    exact (G.mem_neighborFinset _ _).mpr (adjacent i)
  have cover : Finset.univ.image ns = G.neighborFinset (x.vertex 1) := by
    apply Finset.eq_of_subset_of_card_le sub
    rw [Finset.card_image_of_injective _ inj,Finset.card_univ]
    change G.degree (x.vertex 1) ≤ 7
    omega
  have hz (i : Fin 7) (h : i ≠ 0) : sent rotation (x.vertex 1) (ns i) = 0 :=
    RulePairCharge.high_to_low_zero (by omega) (low i h)
  obtain ⟨a,b,c,d,e,_⟩ := incoming_base x tri profile
  have f := incoming_two x tri profile h21 h22 h23
  have out := outgoing_le_one x tri profile
  have bounds (i : Fin 7) : (![2,0,2,1,2,2,2] : Fin 7 → ℤ) i ≤
      net rotation (ns i) (x.vertex 1) := by
    fin_cases i
    · change 2 ≤ sent rotation (x.vertex 0) (x.vertex 1) -
        sent rotation (x.vertex 1) (x.vertex 0)
      omega
    all_goals rw [net,hz _ (by decide),sub_zero]
    · exact sent_nonneg rotation _ _
    · exact f
    · exact e
    · exact d
    · exact c
    · exact b
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => bounds i)
  have total : (∑ i : Fin 7, (![2,0,2,1,2,2,2] : Fin 7 → ℤ) i) = 11 := by decide +kernel
  rw [total] at hs
  have same : (∑ w ∈ Finset.univ.image ns, net rotation w (x.vertex 1)) =
      ∑ i : Fin 7, net rotation (ns i) (x.vertex 1) :=
    Finset.sum_image (fun i _ j _ h => inj h)
  have eq : (∑ w ∈ Finset.univ.image ns, net rotation w (x.vertex 1)) =
      ∑ w : V, net rotation w (x.vertex 1) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro w _ outside
    have no : ¬ G.Adj (x.vertex 1) w := by
      intro h
      apply outside
      rw [cover]
      exact (G.mem_neighborFinset _ _).mpr h
    rw [net, sent_eq_zero_of_not_adj rotation (fun h => no h.symm),
      sent_eq_zero_of_not_adj rotation no,sub_self]
  rw [same] at eq
  unfold finalCharge
  rw [centre,← eq]
  norm_num
  omega

/-- Flatness supplies a further high vertex at one of three precise shared positions. -/
theorem flat_has_high (cyclic : rotation.IsVertexwiseCyclic)
    (lower : ∀ i : Label, i ∈ ({21,22,23} : Finset Label) → 5 ≤ G.degree (x.vertex i))
    (flat : finalCharge rotation (x.vertex 1) = 0) :
    ∃ i ∈ ({21,22,23} : Finset Label), 7 ≤ G.degree (x.vertex i) := by
  by_contra no
  have bound (i : Label) (hi : i ∈ ({21,22,23} : Finset Label)) :
      5 ≤ G.degree (x.vertex i) ∧ G.degree (x.vertex i) ≤ 6 := by
    refine ⟨lower i hi, ?_⟩
    have : ¬ 7 ≤ G.degree (x.vertex i) := fun h => no ⟨i,hi,h⟩
    omega
  have h := positive x tri profile cyclic (bound 21 (by decide))
    (bound 22 (by decide)) (bound 23 (by decide))
  omega

end FourColor.SevenPairSector

namespace FourColor.ActualSevenPairSector

set_option maxRecDepth 65536
set_option linter.style.setOption false
set_option maxHeartbeats 0

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open GoertzelV24TwoEdgeCutMinimality NearLinearCharge LocalCoverageAssembly
open MinimalExceptionalEmbedding (graph rotation)
open SevenPairSector
open SevenPairSectorData hiding Turn Step State

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  (original : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample original)
  (x : Reading (rotation original minimal)) (profile : Profile x)

private theorem outer_adj (i : Label) (hi : i ∈ ({21,22,23} : Finset Label)) :
    (graph original minimal).Adj (x.vertex 15) (x.vertex i) := by
  exact x.edge (MinimalExceptionalEmbedding.triangular original minimal)
    ((by decide +kernel : ∀ i : Label, i ∈ ({21,22,23} : Finset Label) → Edge 15 i) i hi)

include profile in
/-- A chord to the first centre would make a nonfacial triangle. -/
theorem first_nonadjacent : ¬ (graph original minimal).Adj (x.vertex 15) (x.vertex 0) := by
  let tri := MinimalExceptionalEmbedding.triangular original minimal
  intro h
  have a := x.edge tri (by decide +kernel : Edge 1 0)
  have b := x.edge tri (by decide +kernel : Edge 15 1)
  rcases MinimalExceptionalEmbedding.triangle_facial original minimal a h.symm b with h | h
  · have known := x.corner tri (by decide +kernel : SevenPairSectorData.Turn 1 14 15)
    have eq := congrArg (fun e : (graph original minimal).Dart => e.snd)
      ((rotation original minimal).vertexRotation.injective
        (known.choose_spec.choose_spec.trans h.choose_spec.choose_spec.symm))
    have degrees := congrArg (fun v => (graph original minimal).degree v) eq
    rw [profile 14 (by decide),profile 0 (by decide)] at degrees
    change (6 : Nat) = 7 at degrees
    omega
  · have known := x.corner tri (by decide +kernel : SevenPairSectorData.Turn 1 15 16)
    have eq := congrArg (fun e : (graph original minimal).Dart => e.snd)
      (known.choose_spec.choose_spec.symm.trans h.choose_spec.choose_spec)
    have degrees := congrArg (fun v => (graph original minimal).degree v) eq
    rw [profile 16 (by decide),profile 0 (by decide)] at degrees
    change (5 : Nat) = 7 at degrees
    omega

include profile in
private theorem outer_ne_second (i : Label) (hi : i ∈ ({21,22,23} : Finset Label)) :
    x.vertex i ≠ x.vertex 1 := by
  classical
  let tri := MinimalExceptionalEmbedding.triangular original minimal
  let ns : Fin 6 → _ := fun j => x.vertex ((![1,14,22,23,21,16] : Fin 6 → Label) j)
  have inj : Function.Injective ns := by
    apply ExceptionalCoreLocalInjectivity.corner_chain_injective
      (rotation original minimal) (MinimalExceptionalEmbedding.cyclic original minimal)
      (x.vertex 15) (by decide) ns
    · intro j
      exact x.edge tri (by fin_cases j <;> decide +kernel)
    · intro j hj
      exact x.corner tri ((by decide +kernel : ∀ j : Fin 5,
        SevenPairSectorData.Turn 15
          ((![1,14,22,23,21,16] : Fin 6 → Label)
            ⟨j.val,Nat.lt_trans j.isLt (by decide : 5 < 6)⟩)
          ((![1,14,22,23,21,16] : Fin 6 → Label)
            ⟨j.val+1,Nat.succ_lt_succ j.isLt⟩)) ⟨j,by omega⟩)
    · rw [profile 15 (by decide)]
      decide +kernel
  simp only [Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl
  · intro h
    have : (4 : Fin 6) = 0 := inj (show ns 4 = ns 0 from h)
    contradiction
  · intro h
    have : (2 : Fin 6) = 0 := inj (show ns 2 = ns 0 from h)
    contradiction
  · intro h
    have : (3 : Fin 6) = 0 := inj (show ns 3 = ns 0 from h)
    contradiction

include profile in
/-- The continuation is a genuine further high vertex, seen within radius two
of the same second centre. It may have arbitrary degree above six. -/
theorem further_high (flat : finalCharge (rotation original minimal) (x.vertex 1) = 0) :
    ∃ w, w ≠ x.vertex 0 ∧ w ≠ x.vertex 1 ∧
      7 ≤ (graph original minimal).degree w ∧
      w ∈ closedBall (graph original minimal) (x.vertex 1) 2 := by
  let tri := MinimalExceptionalEmbedding.triangular original minimal
  have lower (i : Label) (hi : i ∈ ({21,22,23} : Finset Label)) :
      5 ≤ (graph original minimal).degree (x.vertex i) :=
    PuncturedPairCharge.neighbor_lower original minimal _ _ (outer_adj original minimal x i hi)
  obtain ⟨i,hi,high⟩ := SevenPairSector.flat_has_high x tri profile
    (MinimalExceptionalEmbedding.cyclic original minimal) lower flat
  refine ⟨x.vertex i,?_,outer_ne_second original minimal x profile i hi,high,?_⟩
  · intro eq
    exact first_nonadjacent original minimal x profile
      (eq ▸ outer_adj original minimal x i hi)
  · let p : (graph original minimal).Walk (x.vertex 1) (x.vertex i) :=
      .cons (x.edge tri (by decide +kernel : Edge 1 15))
        (.cons (outer_adj original minimal x i hi) .nil)
    simpa [closedBall,p] using p.edist_le

include profile in
/-- The original paired fan receives the further centre in its retained radius-five domain. -/
theorem pair_continuation {d : (graph original minimal).Dart}
    (p : RuleFanSevenCluster.Pair original minimal d)
    (first : x.vertex 0 = p.first) (second : x.vertex 1 = p.second)
    (upper : OnBall (graph original minimal) d.snd 5
      (fun w => (graph original minimal).degree w ≤ 7)) :
    ∃ w, w ≠ p.first ∧ w ≠ p.second ∧ (graph original minimal).degree w = 7 ∧
      w ∈ closedBall (graph original minimal) p.second 2 ∧
      w ∈ closedBall (graph original minimal) d.snd 5 := by
  obtain ⟨w,ne0,ne1,high,near⟩ := further_high original minimal x profile
    (by simpa only [second] using p.second_flat)
  rw [first] at ne0
  rw [second] at ne1 near
  have full := ball_recenter (graph original minimal) p.second_near near
  refine ⟨w,ne0,ne1,?_,near,full⟩
  exact Nat.le_antisymm (upper w full) high

end
end FourColor.ActualSevenPairSector

import Mettapedia.GraphTheory.FourColor.KempeEdgeRequest

/-!
# A matching closure requiring exactly three physical switches

The retained graph has thirty vertices and forty-three edges. Two disjoint
missing edges complete the cubic incidence graph. A prescribed colouring
has no extension after zero, one or two physical component switches, but
an explicit three-switch GSLT history extends. Certificates describe actual
saturated chains; no arbitrary edge subset is treated as a Kempe component.
-/

namespace Mettapedia.GraphTheory.FourColor.MatchingCapThreeSwitch

open GoertzelV24ForkInterfaceSupport IncidenceKempeSwitch KempeChainCertificate
open Mettapedia.GSLT.Ultrainfinite

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

abbrev Vertex := Fin 30
abbrev Edge := Fin 45

def inc : Edge → Finset Vertex :=
  ![{0,1}, {0,2}, {0,3}, {1,4}, {1,5}, {2,6}, {2,7}, {3,8}, {3,9}, {4,9}, {4,10}, {5,6}, {5,11}, {6,12}, {7,8}, {7,13}, {8,14}, {9,15}, {10,16}, {10,17}, {11,17}, {11,18}, {12,18}, {12,19}, {13,19}, {13,20}, {14,20}, {14,21}, {15,16}, {15,21}, {16,22}, {17,23}, {18,24}, {19,25}, {20,26}, {21,27}, {22,23}, {22,28}, {23,24}, {24,29}, {25,26}, {25,29}, {26,27}, {27,28}, {28,29}]

def old : Finset Edge := Finset.univ \ {13, 24}

def baseAssignment : Edge → Fin 3 :=
  ![0,1,2,2,1,0,2,1,0,1,0,2,0,0,0,1,2,2,1,2,1,2,1,0,0,0,1,0,0,1,2,0,0,2,2,2,1,0,2,1,1,0,0,1,2]

theorem cubic_incidence :
    (∀ x : Edge, (inc x).card = 2) ∧
      ∀ v : Vertex, (Finset.univ.filter fun x => v ∈ inc x).card = 3 := by decide +kernel

theorem base_proper : Proper inc old baseAssignment := by decide +kernel

def base : (graph inc old).Coloring (Fin 3) := colouring inc old baseAssignment base_proper

def Extends (a : Edge → Fin 3) : Prop :=
  ∃ d : Edge → Fin 3, Proper inc Finset.univ d ∧ ∀ x ∈ old, d x = a x

/-- The five nontrivial components of the original colouring, together
with index zero for unchanged retained edges. -/
private def firstPair : Fin 6 → Fin 3 × Fin 3 :=
  ![(0,0), (0,1), (0,1), (0,2), (1,2), (1,2)]

private def firstChain : Fin 6 → List Edge :=
  ![[], [5,1,0,4,12,20,31,36,37,43,42,40,41,39,32,22,23], [7,8,9,10,18,28,29,27,26,25,15,14], [23,33,41,44,37,30,28,17,8,2,0,3,10,19,31,38,32,21,12,11,5,6,14,16,27,35,42,34,25], [15,6,1,2,7,16,26,34,40,33], [11,4,3,9,17,29,35,43,44,39,38,36,30,18,19,20,21,22]]

private def layer (t : Fin 6) (x : Edge) : Fin 3 :=
  if x ∈ firstChain t then Equiv.swap (firstPair t).1 (firstPair t).2 (baseAssignment x)
  else baseAssignment x

private def baseChain (r s : Fin 3) (x : Edge) : List Edge :=
  if r = s then [x]
  else if (r = 0 ∨ s = 0) ∧ (r = 1 ∨ s = 1) then
    if x ∈ firstChain 1 then firstChain 1 else firstChain 2
  else if (r = 0 ∨ s = 0) ∧ (r = 2 ∨ s = 2) then firstChain 3
  else if x ∈ firstChain 4 then firstChain 4 else firstChain 5

private theorem base_chain_certificate : ∀ r s x, x ∈ old →
    (baseAssignment x = r ∨ baseAssignment x = s) →
    x ∈ baseChain r s x ∧ (baseChain r s x).IsChain (graph inc old).Adj ∧
      (∀ y ∈ baseChain r s x, y ∈ old ∧ (baseAssignment y = r ∨ baseAssignment y = s)) ∧
      (∀ y ∈ baseChain r s x, ∀ z, (graph inc old).Adj y z →
        (baseAssignment z = r ∨ baseAssignment z = s) → z ∈ baseChain r s x) := by
  decide +kernel

private theorem base_switch_certificate : ∀ r s x, x ∈ old →
    (baseAssignment x = r ∨ baseAssignment x = s) →
    ∃ t, ∀ y ∈ old,
      (if y ∈ baseChain r s x then Equiv.swap r s (baseAssignment y) else baseAssignment y) =
        layer t y := by decide +kernel

private theorem first_switch (r s : Fin 3)
    (K : (base.bicoloredSubgraph r s).ConnectedComponent) :
    ∃ t, ∀ y ∈ old, base.swapOnKempeComponent r s K y = layer t y := by
  classical
  by_cases htouch : ∃ x ∈ old, x ∈ base.kempeComponentSet r s K
  · obtain ⟨x, hx, hxK⟩ := htouch
    have ha := base.mem_bicoloredSet_of_mem_kempeComponentSet hxK
    obtain ⟨hxc, hc, hca, hcc⟩ := base_chain_certificate r s x hx ha
    obtain ⟨t, ht⟩ := base_switch_certificate r s x hx ha
    refine ⟨t, ?_⟩
    intro y hy
    rw [base.swap_apply_of_chain r s K _ hc (fun z hz => (hca z hz).2) hcc hxc hxK y]
    exact ht y hy
  · refine ⟨0, ?_⟩
    intro y hy
    rw [base.swapOnKempeComponent_apply_of_not_mem (fun h => htouch ⟨y, hy, h⟩)]
    rfl

private def requestLeft : Fin 6 → Fin 3 :=
  ![1, 0, 1, 1, 1, 2]

private def requestRight : Fin 6 → Fin 3 :=
  ![2, 2, 2, 0, 2, 1]

private def blockChain : Fin 6 → List Edge :=
  ![[11,4,3,9,17,29,35,43,44,39,38,36,30,18,19,20,21,22], [11,4,3,10,19,20,21,22], [11,4,3,10,19,20,21,22], [11,4,3,9,17,29,35,43,44,39,38,36,30,18,19,20,21,22], [11,4,3,9,17,29,35,43,44,39,38,36,30,18,19,20,21,22], [11,4,3,9,17,29,35,43,44,39,38,36,30,18,19,20,21,22]]

private def leftEdge : Fin 6 → Edge :=
  ![11, 11, 11, 11, 11, 11]

private def rightEdge : Fin 6 → Edge :=
  ![22, 22, 22, 22, 22, 22]

private theorem missing_certificate : ∀ t,
    requestLeft t ≠ requestRight t ∧
      (∀ q, q ∉ profile inc old (layer t) 6 ↔ q = requestLeft t) ∧
      (∀ q, q ∉ profile inc old (layer t) 12 ↔ q = requestRight t) := by decide +kernel

private theorem contact_certificate : ∀ t,
    leftEdge t ∈ old ∧ rightEdge t ∈ old ∧
      (6 : Vertex) ∈ inc (leftEdge t) ∧ (12 : Vertex) ∈ inc (rightEdge t) ∧
      leftEdge t ∈ blockChain t ∧ rightEdge t ∈ blockChain t := by decide +kernel

set_option synthInstance.maxSize 1024 in
private theorem blocking_certificate : ∀ t a b,
    ((a = requestLeft t ∧ b = requestRight t) ∨ (a = requestRight t ∧ b = requestLeft t)) →
    (blockChain t).IsChain (graph inc old).Adj ∧
      (∀ x ∈ blockChain t, x ∈ old ∧ (layer t x = a ∨ layer t x = b)) ∧
      (∀ x ∈ blockChain t, ∀ y, (graph inc old).Adj x y →
        (layer t y = a ∨ layer t y = b) → y ∈ blockChain t) := by decide +kernel

private theorem layer_missing (C : (graph inc old).Coloring (Fin 3)) (t : Fin 6)
    (hC : ∀ x ∈ old, C x = layer t x) :
    (∀ q, q ∉ profile inc old C 6 ↔ q = requestLeft t) ∧
      (∀ q, q ∉ profile inc old C 12 ↔ q = requestRight t) := by
  rw [EdgeColouringGluing.profile_congr inc old C (layer t) hC]
  exact (missing_certificate t).2

private theorem layer_no_extension (C : (graph inc old).Coloring (Fin 3)) (t : Fin 6)
    (hC : ∀ x ∈ old, C x = layer t x) : ¬ Extends C := by
  obtain ⟨hm, hn⟩ := layer_missing C t hC
  exact MatchingEdgeClosure.no_extension_of_distinct_requests
    (by decide : (13 : Edge) ∈ (Finset.univ : Finset Edge)) (by decide : (13 : Edge) ∉ old)
    (Finset.subset_univ _) (by decide : (6 : Vertex) ∈ inc 13) (by decide : (12 : Vertex) ∈ inc 13)
    C (requestLeft t) (requestRight t) (missing_certificate t).1 hm hn

private theorem layer_switch_no_extension (C : (graph inc old).Coloring (Fin 3)) (t : Fin 6)
    (hC : ∀ x ∈ old, C x = layer t x) (r s : Fin 3)
    (K : (C.bicoloredSubgraph r s).ConnectedComponent) :
    ¬ Extends (C.swapOnKempeComponent r s K) := by
  classical
  have hcontact (a b : Fin 3) (L : (C.bicoloredSubgraph a b).ConnectedComponent)
      (hp : (a = requestLeft t ∧ b = requestRight t) ∨
        (a = requestRight t ∧ b = requestLeft t)) :
      Touches C a b L 6 ↔ Touches C a b L 12 := by
    obtain ⟨hc, ha, hclosed⟩ := blocking_certificate t a b hp
    obtain ⟨hx, hy, hu, hv, hxc, hyc⟩ := contact_certificate t
    apply touches_iff_of_chain C a b L (blockChain t) hc _ _ hx hy hu hv hxc hyc
    · intro x hxb
      rw [hC x (ha x hxb).1]
      exact (ha x hxb).2
    · intro x hxb y hxy hya
      rw [hC y hxy.2.2.1] at hya
      exact hclosed x hxb y hxy hya
  obtain ⟨hm, hn⟩ := layer_missing C t hC
  exact MatchingEdgeClosure.no_extension_of_distinct_requests
    (by decide : (13 : Edge) ∈ (Finset.univ : Finset Edge)) (by decide : (13 : Edge) ∉ old)
    (Finset.subset_univ _) (by decide : (6 : Vertex) ∈ inc 13) (by decide : (12 : Vertex) ∈ inc 13)
    (C.swapOnKempeComponent r s K) _ _
    (switched_requests_distinct C _ _ (missing_certificate t).1 hcontact r s K)
    (missing_switch C r s K hm) (missing_switch C r s K hn)

/-- Every history of at most two literal component switches fails to
extend the prescribed old colouring across the matching cap. -/
theorem no_repair_with_two_switches {D : (graph inc old).Coloring (Fin 3)}
    (p : History base D) (hlen : p.length ≤ 2) : ¬ Extends D := by
  cases p with
  | refl => exact layer_no_extension base 0 (fun _ _ => rfl)
  | cons step rest =>
    cases step with
    | switch r s K =>
      obtain ⟨t, ht⟩ := first_switch r s K
      cases rest with
      | refl => exact layer_no_extension _ t ht
      | cons step rest =>
        cases step with
        | switch a b L =>
          cases rest with
          | refl => exact layer_switch_no_extension _ t ht a b L
          | cons step rest => simp only [Route.length] at hlen; omega

private def repairAssignment1 : Edge → Fin 3 :=
  ![0,1,2,1,2,0,2,1,0,2,0,1,0,0,0,1,2,1,2,1,2,1,2,0,0,0,1,0,0,2,1,0,0,2,2,1,2,0,1,2,1,0,0,2,1]

private theorem repairProper1 : Proper inc old repairAssignment1 := by decide +kernel

private def repairColouring1 : (graph inc old).Coloring (Fin 3) :=
  colouring inc old repairAssignment1 repairProper1

private def repairAssignment2 : Edge → Fin 3 :=
  ![0,1,2,1,2,0,2,1,0,2,0,1,0,0,0,1,2,1,2,1,2,1,0,2,0,0,1,0,0,2,1,0,2,0,2,1,2,0,1,0,1,2,0,2,1]

private theorem repairProper2 : Proper inc old repairAssignment2 := by decide +kernel

private def repairColouring2 : (graph inc old).Coloring (Fin 3) :=
  colouring inc old repairAssignment2 repairProper2

private def repairAssignment3 : Edge → Fin 3 :=
  ![0,2,1,2,1,0,1,2,0,1,0,2,0,0,0,2,1,2,2,1,2,1,0,2,0,0,2,0,0,1,1,0,2,0,1,2,2,0,1,0,2,1,0,1,2]

private theorem repairProper3 : Proper inc old repairAssignment3 := by decide +kernel

private def repairColouring3 : (graph inc old).Coloring (Fin 3) :=
  colouring inc old repairAssignment3 repairProper3

def finalAssignment : Edge → Fin 3 :=
  ![0,2,1,2,1,0,1,2,0,1,0,2,0,1,0,2,1,2,2,1,2,1,0,2,1,0,2,0,0,1,1,0,2,0,1,2,2,0,1,0,2,1,0,1,2]

theorem final_proper : Proper inc Finset.univ finalAssignment := by decide +kernel

noncomputable section

private def repairComponent1 : (base.bicoloredSubgraph 1 2).ConnectedComponent :=
  (base.bicoloredSubgraph 1 2).connectedComponentMk ⟨11, Or.inr rfl⟩

private theorem repairSwitch1 :
    base.swapOnKempeComponent 1 2 repairComponent1 = repairColouring1 := by
  apply DFunLike.ext
  intro x
  rw [base.swap_apply_of_chain 1 2 repairComponent1 [11,4,3,9,17,29,35,43,44,39,38,36,30,18,19,20,21,22]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide : (11 : Edge) ∈ [11,4,3,9,17,29,35,43,44,39,38,36,30,18,19,20,21,22])
    (base.mem_kempeComponentSet_self (Or.inr rfl))]
  revert x
  decide +kernel

private def repairComponent2 : (repairColouring1.bicoloredSubgraph 0 2).ConnectedComponent :=
  (repairColouring1.bicoloredSubgraph 0 2).connectedComponentMk ⟨22, Or.inr rfl⟩

private theorem repairSwitch2 :
    repairColouring1.swapOnKempeComponent 0 2 repairComponent2 = repairColouring2 := by
  apply DFunLike.ext
  intro x
  rw [repairColouring1.swap_apply_of_chain 0 2 repairComponent2 [22,23,33,41,39,32]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide : (22 : Edge) ∈ [22,23,33,41,39,32])
    (repairColouring1.mem_kempeComponentSet_self (Or.inr rfl))]
  revert x
  decide +kernel

private def repairComponent3 : (repairColouring2.bicoloredSubgraph 1 2).ConnectedComponent :=
  (repairColouring2.bicoloredSubgraph 1 2).connectedComponentMk ⟨11, Or.inl rfl⟩

private theorem repairSwitch3 :
    repairColouring2.swapOnKempeComponent 1 2 repairComponent3 = repairColouring3 := by
  apply DFunLike.ext
  intro x
  rw [repairColouring2.swap_apply_of_chain 1 2 repairComponent3 [11,4,3,9,17,29,35,43,44,41,40,34,26,16,7,2,1,6,15]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide : (11 : Edge) ∈ [11,4,3,9,17,29,35,43,44,41,40,34,26,16,7,2,1,6,15])
    (repairColouring2.mem_kempeComponentSet_self (Or.inl rfl))]
  revert x
  decide +kernel

/-- Three switches, with their actual components retained, attain a
colouring extended by the displayed proper colouring of all forty-five edges. -/
theorem repaired_history_extends :
    ∃ D : (graph inc old).Coloring (Fin 3),
      (∃ history : History base D, history.length = 3) ∧ Extends D := by
  have h1 : Step base repairColouring1 := by
    rw [← repairSwitch1]
    exact .switch _ 1 2 repairComponent1
  have h2 : Step repairColouring1 repairColouring2 := by
    rw [← repairSwitch2]
    exact .switch _ 0 2 repairComponent2
  have h3 : Step repairColouring2 repairColouring3 := by
    rw [← repairSwitch3]
    exact .switch _ 1 2 repairComponent3
  exact ⟨repairColouring3, ⟨.cons h1 (.cons h2 (.cons h3 (.refl _))), rfl⟩,
    finalAssignment, final_proper, by decide +kernel⟩

/-- The lower and upper bounds refer to the same original witness and
physical GSLT history type. -/
theorem minimum_repair_length :
    (∀ (D : (graph inc old).Coloring (Fin 3)) (p : History base D),
      Extends D → 3 ≤ p.length) ∧
    ∃ D : (graph inc old).Coloring (Fin 3),
      (∃ p : History base D, p.length = 3) ∧ Extends D := by
  refine ⟨?_, repaired_history_extends⟩
  intro D p h
  by_contra hlen
  exact no_repair_with_two_switches p (by omega) h

end
end Mettapedia.GraphTheory.FourColor.MatchingCapThreeSwitch

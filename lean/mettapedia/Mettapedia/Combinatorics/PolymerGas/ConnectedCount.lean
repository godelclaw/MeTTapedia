import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Counting connected vertex sets

A connected set of `n` vertices containing a specified root admits a closed
covering walk of length at most `2 * (n - 1)`. If every vertex has degree at
most `Δ`, the number of such sets is at most `(Δ + 1) ^ (2 * n)`.
The bound does not depend on the size of the ambient graph.
-/

set_option autoImplicit false
noncomputable section

open Finset

namespace Mettapedia.Combinatorics.PolymerGas

namespace ConnectedCount
namespace Walk

def insertLeafAtSupport {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {root y leaf : V} (p : G.Walk root root)
    (hy : y ∈ p.support) (hyl : G.Adj y leaf) :
    G.Walk root root :=
  (((p.takeUntil y hy).append (hyl.toWalk)).append (hyl.symm.toWalk)).append
    (p.dropUntil y hy)

theorem insertLeafAtSupport_length {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {root y leaf : V} (p : G.Walk root root)
    (hy : y ∈ p.support) (hyl : G.Adj y leaf) :
    (insertLeafAtSupport p hy hyl).length = p.length + 2 := by
  have hsplit := congrArg SimpleGraph.Walk.length (SimpleGraph.Walk.take_spec p hy)
  simp only [SimpleGraph.Walk.length_append] at hsplit
  simp [insertLeafAtSupport]
  omega

theorem support_subset_insertLeafAtSupport
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {root y leaf : V} (p : G.Walk root root)
    (hy : y ∈ p.support) (hyl : G.Adj y leaf) :
    p.support ⊆ (insertLeafAtSupport p hy hyl).support := by
  intro z hz
  have hsplit :
      z ∈ (p.takeUntil y hy).support ∨ z ∈ (p.dropUntil y hy).support := by
    rw [← SimpleGraph.Walk.mem_support_append_iff]
    simpa using hz
  rcases hsplit with hzLeft | hzRight
  · simp [insertLeafAtSupport, hzLeft]
  · simp [insertLeafAtSupport, hzRight]

theorem leaf_mem_insertLeafAtSupport
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {root y leaf : V} (p : G.Walk root root)
    (hy : y ∈ p.support) (hyl : G.Adj y leaf) :
    leaf ∈ (insertLeafAtSupport p hy hyl).support := by
  simp [insertLeafAtSupport]

theorem rotate_length {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {root u : V} (p : G.Walk u u) (hroot : root ∈ p.support) :
    (p.rotate root hroot).length = p.length :=
  SimpleGraph.Walk.length_rotate p root hroot

end Walk

theorem fintype_card_compl_singleton_set
    {V : Type*} [Fintype V] [DecidableEq V] (v : V) :
    Fintype.card ({v}ᶜ : Set V) = Fintype.card V - 1 := by
  rw [Fintype.card_subtype]
  change (Finset.univ.filter fun x : V => x ≠ v).card =
    Fintype.card V - 1
  rw [show (Finset.univ.filter fun x : V => x ≠ v) =
      (Finset.univ.erase v) by
    ext x
    simp]
  exact Finset.card_erase_of_mem (by simp)

universe u

theorem Connected.exists_closedWalk_cover_length_le
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hconn : G.Connected) (root : V) :
    ∃ p : G.Walk root root,
      (∀ x : V, x ∈ p.support) ∧
        p.length ≤ 2 * (Fintype.card V - 1) := by
  classical
  have hmain :
      ∀ n : ℕ, ∀ (V : Type u) [Fintype V] [DecidableEq V]
          (G : SimpleGraph V),
        Fintype.card V = n → G.Connected → ∀ root : V,
          ∃ p : G.Walk root root,
            (∀ x : V, x ∈ p.support) ∧
              p.length ≤ 2 * (Fintype.card V - 1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro V _ _ G hcard hconn root
        by_cases hcardOne : Fintype.card V = 1
        · have : Subsingleton V :=
            Fintype.card_le_one_iff_subsingleton.mp (by omega)
          refine ⟨SimpleGraph.Walk.nil, ?_, ?_⟩
          · intro x
            have hx : x = root := Subsingleton.elim x root
            subst x
            simp
          · simp
        · have : Nonempty V := hconn.nonempty
          have hpos : 0 < Fintype.card V := Fintype.card_pos
          have hcardGt : 1 < Fintype.card V := by omega
          have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp hcardGt
          rcases hconn.exists_preconnected_induce_compl_singleton_of_finite with
            ⟨v, hpre⟩
          rcases hconn.preconnected.exists_adj_of_nontrivial v with ⟨y, hvy⟩
          by_cases hvroot : v = root
          · subst v
            let S : Set V := {root}ᶜ
            let H := G.induce S
            have hyS : y ∈ S := by
              show y ≠ root
              exact hvy.ne.symm
            let ySub : S := ⟨y, hyS⟩
            have : Nonempty S := ⟨ySub⟩
            have hconnSub : H.Connected := by
              exact ⟨by simpa [H, S] using hpre⟩
            have hcardS : Fintype.card S = Fintype.card V - 1 := by
              simpa [S] using fintype_card_compl_singleton_set root
            have hcardSLt : Fintype.card S < n := by
              rw [← hcard]
              rw [hcardS]
              omega
            rcases ih (Fintype.card S) hcardSLt S H rfl hconnSub ySub with
              ⟨pSub, hcoverSub, hlenSub⟩
            let pLift : G.Walk y y :=
              pSub.map (SimpleGraph.Embedding.induce S).toHom
            have hcoverLift : ∀ x : V, x ∈ S → x ∈ pLift.support := by
              intro x hx
              have hxSub : (⟨x, hx⟩ : S) ∈ pSub.support :=
                hcoverSub ⟨x, hx⟩
              change x ∈
                (pSub.map (SimpleGraph.Embedding.induce S).toHom).support
              rw [SimpleGraph.Walk.support_map]
              simpa using
                (List.mem_map_of_mem (f := fun z : S => (z : V)) hxSub)
            have hyLift : y ∈ pLift.support := hcoverLift y hyS
            let pIns :=
              ConnectedCount.Walk.insertLeafAtSupport pLift hyLift hvy.symm
            have hrootIns : root ∈ pIns.support := by
              simpa [pIns] using
                ConnectedCount.Walk.leaf_mem_insertLeafAtSupport
                  pLift hyLift hvy.symm
            refine ⟨pIns.rotate root hrootIns, ?_, ?_⟩
            · intro x
              rw [SimpleGraph.Walk.mem_support_rotate_iff pIns root hrootIns]
              by_cases hxroot : x = root
              · subst x
                exact hrootIns
              · exact
                  ConnectedCount.Walk.support_subset_insertLeafAtSupport
                    pLift hyLift hvy.symm
                    (hcoverLift x (by
                      show x ≠ root
                      exact hxroot))
            · have hlenLift : pLift.length = pSub.length := by
                exact SimpleGraph.Walk.length_map _ _
              have hlenIns : pIns.length = pLift.length + 2 := by
                simpa [pIns] using
                  ConnectedCount.Walk.insertLeafAtSupport_length
                    pLift hyLift hvy.symm
              calc
                (pIns.rotate root hrootIns).length = pIns.length :=
                  ConnectedCount.Walk.rotate_length pIns hrootIns
                _ = pLift.length + 2 := hlenIns
                _ = pSub.length + 2 := by omega
                _ ≤ 2 * (Fintype.card S - 1) + 2 := by omega
                _ ≤ 2 * (Fintype.card V - 1) := by
                  rw [hcardS]
                  omega
          · let S : Set V := {v}ᶜ
            let H := G.induce S
            have hrootS : root ∈ S := by
              show root ≠ v
              intro h
              exact hvroot h.symm
            have hyS : y ∈ S := by
              show y ≠ v
              exact hvy.ne.symm
            let rootSub : S := ⟨root, hrootS⟩
            have : Nonempty S := ⟨rootSub⟩
            have hconnSub : H.Connected := by
              exact ⟨by simpa [H, S] using hpre⟩
            have hcardS : Fintype.card S = Fintype.card V - 1 := by
              simpa [S] using fintype_card_compl_singleton_set v
            have hcardSLt : Fintype.card S < n := by
              rw [← hcard]
              rw [hcardS]
              omega
            rcases ih (Fintype.card S) hcardSLt S H rfl hconnSub rootSub with
              ⟨pSub, hcoverSub, hlenSub⟩
            let pLift : G.Walk root root :=
              pSub.map (SimpleGraph.Embedding.induce S).toHom
            have hcoverLift : ∀ x : V, x ∈ S → x ∈ pLift.support := by
              intro x hx
              have hxSub : (⟨x, hx⟩ : S) ∈ pSub.support :=
                hcoverSub ⟨x, hx⟩
              change x ∈
                (pSub.map (SimpleGraph.Embedding.induce S).toHom).support
              rw [SimpleGraph.Walk.support_map]
              simpa using
                (List.mem_map_of_mem (f := fun z : S => (z : V)) hxSub)
            have hyLift : y ∈ pLift.support := hcoverLift y hyS
            let pIns :=
              ConnectedCount.Walk.insertLeafAtSupport pLift hyLift hvy.symm
            refine ⟨pIns, ?_, ?_⟩
            · intro x
              by_cases hxv : x = v
              · subst x
                simpa [pIns] using
                  ConnectedCount.Walk.leaf_mem_insertLeafAtSupport
                    pLift hyLift hvy.symm
              · exact
                  ConnectedCount.Walk.support_subset_insertLeafAtSupport
                    pLift hyLift hvy.symm
                    (hcoverLift x (by
                      show x ≠ v
                      exact hxv))
            · have hlenLift : pLift.length = pSub.length := by
                exact SimpleGraph.Walk.length_map _ _
              have hlenIns : pIns.length = pLift.length + 2 := by
                simpa [pIns] using
                  ConnectedCount.Walk.insertLeafAtSupport_length
                    pLift hyLift hvy.symm
              calc
                pIns.length = pLift.length + 2 := hlenIns
                _ = pSub.length + 2 := by omega
                _ ≤ 2 * (Fintype.card S - 1) + 2 := by omega
                _ ≤ 2 * (Fintype.card V - 1) := by
                  rw [hcardS]
                  omega
  exact hmain (Fintype.card V) V G rfl hconn root

end ConnectedCount


variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Vertex sets visited by walks of at most `m` steps, with stationary steps
allowed so that all encodings have the same length. -/
def walkSupportSets (G : SimpleGraph V) [DecidableRel G.Adj] :
    ℕ → V → Finset (Finset V)
  | 0, v => {{v}}
  | m + 1, v => (insert v (G.neighborFinset v)).biUnion fun w =>
      (walkSupportSets G m w).image (insert v)

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem singleton_mem_walkSupportSets (m : ℕ) (v : V) :
    {v} ∈ walkSupportSets G m v := by
  induction m with
  | zero => simp [walkSupportSets]
  | succ m ih =>
    apply mem_biUnion.mpr
    refine ⟨v, mem_insert_self _ _, ?_⟩
    exact mem_image.mpr ⟨{v}, ih, by simp⟩

theorem support_mem_walkSupportSets {u v : V} (p : G.Walk u v) (m : ℕ)
    (hlen : p.length ≤ m) : p.support.toFinset ∈ walkSupportSets G m u := by
  induction m generalizing u v with
  | zero =>
    cases p <;> simp_all [walkSupportSets]
  | succ m ih =>
    cases p with
    | nil => exact singleton_mem_walkSupportSets G (m + 1) u
    | @cons u w v huw q =>
      apply mem_biUnion.mpr
      refine ⟨w, mem_insert_of_mem ((G.mem_neighborFinset u w).mpr huw), ?_⟩
      exact mem_image.mpr ⟨q.support.toFinset, ih q (by simpa using hlen), by simp⟩

theorem card_walkSupportSets_le {Δ : ℕ} (hdeg : ∀ v, G.degree v ≤ Δ)
    (m : ℕ) (v : V) : (walkSupportSets G m v).card ≤ (Δ + 1) ^ m := by
  induction m generalizing v with
  | zero => simp [walkSupportSets]
  | succ m ih =>
    calc
      (walkSupportSets G (m + 1) v).card
          ≤ (insert v (G.neighborFinset v)).card * (Δ + 1) ^ m := by
        apply card_biUnion_le_card_mul
        intro w _
        exact card_image_le.trans (ih w)
      _ ≤ (Δ + 1) * (Δ + 1) ^ m := by
        apply Nat.mul_le_mul_right
        calc (insert v (G.neighborFinset v)).card ≤ (G.neighborFinset v).card + 1 :=
              card_insert_le _ _
          _ ≤ Δ + 1 := Nat.add_le_add_right (hdeg v) 1
      _ = (Δ + 1) ^ (m + 1) := by rw [pow_succ']

/-- Nonempty connected vertex sets of a fixed cardinality containing a root. -/
def rootedConnectedSets (root : V) (n : ℕ) : Finset (Finset V) :=
  univ.filter fun S => root ∈ S ∧ S.card = n ∧ (G.induce (S : Set V)).Connected

theorem connected_mem_walkSupportSets {S : Finset V} {root : V}
    (hroot : root ∈ S) (hconn : (G.induce (S : Set V)).Connected) :
    S ∈ walkSupportSets G (2 * S.card) root := by
  classical
  obtain ⟨p, hcover, hlen⟩ :=
    ConnectedCount.Connected.exists_closedWalk_cover_length_le hconn ⟨root, hroot⟩
  let q := p.map (SimpleGraph.Embedding.induce (S : Set V)).toHom
  have hq : q.support.toFinset = S := by
    ext x
    simp only [List.mem_toFinset, q, SimpleGraph.Walk.support_map, List.mem_map]
    constructor
    · rintro ⟨y, _, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, hcover _, rfl⟩
  rw [← hq]
  apply support_mem_walkSupportSets G q
  have hlenq : q.length = p.length := SimpleGraph.Walk.length_map _ _
  have hcard : Fintype.card (S : Set V) = S.card := Fintype.card_coe S
  rw [hq]
  omega

/-- An exponential bound for connected sets through one vertex, uniform in the
number of vertices of the graph. -/
theorem card_rootedConnectedSets_le {Δ : ℕ} (hdeg : ∀ v, G.degree v ≤ Δ)
    (root : V) (n : ℕ) : (rootedConnectedSets G root n).card ≤ (Δ + 1) ^ (2 * n) := by
  classical
  refine (card_le_card (t := walkSupportSets G (2 * n) root) ?_).trans
    (card_walkSupportSets_le G hdeg _ _)
  intro S hS
  obtain ⟨_, hroot, hcard, hconn⟩ := mem_filter.mp hS
  simpa only [hcard] using connected_mem_walkSupportSets G hroot hconn

#print axioms ConnectedCount.Connected.exists_closedWalk_cover_length_le
#print axioms card_rootedConnectedSets_le

end Mettapedia.Combinatorics.PolymerGas

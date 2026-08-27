import Mettapedia.GraphTheory.FourColor.GoertzelV24SeparatedGeodesicLocality
import Mettapedia.GraphTheory.FourColor.GoertzelV24DualDiameterDichotomy

/-!
# Components after deleting vertices

Deleting one vertex from a connected graph cannot shatter it: every piece that
survives still touches the deleted vertex, so the number of pieces is bounded by
its degree.  Iterating, deleting `h` vertices of degree at most `B` leaves at
most `1 + h(B-1)` pieces.

The one graph-level fact is that **every component of `G - v` contains a
neighbour of `v`**, and it is a walk induction: follow a walk from `x` to `v`
and stop at the last vertex before `v` is first reached.

Pieces are tracked by *representatives* rather than by a component type, because
the component type changes with the deleted set and comparing across two
different graphs is exactly the awkward step.  A representative set covers when
every surviving vertex reaches one of its members, and it is a transversal when
distinct members lie in distinct pieces.  Transversality is what buys the sharp
constant: deleting one more vertex retires the representative of that vertex's
own piece and installs at most `B` new ones, a net gain of `B - 1`.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24DeletionComponents

open GoertzelV24SeparatedGeodesicLocality
open GoertzelV24DualDiameterDichotomy

variable {V : Type*} {G : SimpleGraph V}

/-- **Every component of `G - v` contains a neighbour of `v`.**

Stated relative to an already-deleted set `S`: a walk from `x` to `v` that avoids
`S` yields a neighbour of `v` reachable from `x` once `v` is deleted as well. -/
theorem exists_adj_reachable {S : Set V} {v x : V} (hxv : x ≠ v)
    (p : (deleteFaces G S).Walk x v) :
    ∃ w : V, G.Adj w v ∧ (deleteFaces G (insert v S)).Reachable x w := by
  induction p with
  | nil => exact absurd rfl hxv
  | @cons a b c hadj q ih =>
      obtain ⟨hGadj, ha, hb⟩ := hadj
      by_cases hbv : b = c
      · subst hbv
        exact ⟨a, hGadj, SimpleGraph.Reachable.refl a⟩
      · obtain ⟨w, hw, hreach⟩ := ih hbv
        refine ⟨w, hw, ?_⟩
        refine SimpleGraph.Reachable.trans ?_ hreach
        refine SimpleGraph.Adj.reachable ⟨hGadj, ?_, ?_⟩
        · rintro (rfl | hcon)
          · exact hxv rfl
          · exact ha hcon
        · rintro (rfl | hcon)
          · exact hbv rfl
          · exact hb hcon

/-- Deleting nothing changes nothing. -/
theorem deleteFaces_empty : deleteFaces G (∅ : Set V) = G := by
  ext u v
  simp [deleteFaces]

/-- The same fact without a pre-deleted set: every vertex other than `v` reaches
a neighbour of `v` in `G - v`. -/
theorem exists_adj_reachable_of_connected (hconn : G.Connected) {v x : V} (hxv : x ≠ v) :
    ∃ w : V, G.Adj w v ∧ (deleteFaces G ({v} : Set V)).Reachable x w := by
  obtain ⟨p⟩ := hconn x v
  have hp : (deleteFaces G (∅ : Set V)).Walk x v := deleteFaces_empty ▸ p
  simpa using exists_adj_reachable (S := (∅ : Set V)) hxv hp

/-! ## Counting the pieces by representatives -/

/-- A vertex that cannot reach `v` keeps all its reachability once `v` is
deleted: every walk out of it already avoids `v`. -/
theorem reachable_delete_insert {S : Set V} {v : V} : ∀ {x s : V},
    (deleteFaces G S).Walk x s → ¬ (deleteFaces G S).Reachable x v →
    (deleteFaces G (insert v S)).Reachable x s := by
  intro x s p
  induction p with
  | nil => intro _; exact SimpleGraph.Reachable.refl _
  | @cons a b c hadj q ih =>
      intro hnr
      have hbv : ¬ (deleteFaces G S).Reachable b v := fun hcon =>
        hnr ((SimpleGraph.Adj.reachable hadj).trans hcon)
      have hstep : (deleteFaces G (insert v S)).Adj a b := by
        obtain ⟨hG, ha, hb⟩ := hadj
        refine ⟨hG, ?_, ?_⟩
        · rintro (rfl | hcon)
          · exact hnr (SimpleGraph.Reachable.refl _)
          · exact ha hcon
        · rintro (rfl | hcon)
          · exact hbv (SimpleGraph.Reachable.refl _)
          · exact hb hcon
      exact (SimpleGraph.Adj.reachable hstep).trans (ih hbv)

variable (G)

/-- A representative set covers when every survivor reaches one of its members. -/
def Covers (S : Set V) (reps : Finset V) : Prop :=
  ∀ x : V, x ∉ S → ∃ r ∈ reps, (deleteFaces G S).Reachable x r

/-- A representative set is a transversal when distinct members lie in distinct
pieces. -/
def Transversal (S : Set V) (reps : Finset V) : Prop :=
  ∀ r ∈ reps, ∀ r' ∈ reps, (deleteFaces G S).Reachable r r' → r = r'

variable {G}

/-- Any covering set contains a covering transversal: while two members lie in
one piece, discard one. -/
theorem exists_transversal [DecidableEq V] (S : Set V) :
    ∀ cover : Finset V, Covers G S cover →
      ∃ t, t ⊆ cover ∧ Covers G S t ∧ Transversal G S t := by
  intro cover
  induction cover using Finset.strongInduction with
  | _ cover ih =>
    intro hcov
    by_cases hbad : ∃ r ∈ cover, ∃ r' ∈ cover, r ≠ r' ∧ (deleteFaces G S).Reachable r r'
    · obtain ⟨r, hr, r', hr', hne, hreach⟩ := hbad
      have hsub : cover.erase r' ⊂ cover := Finset.erase_ssubset hr'
      have hcov' : Covers G S (cover.erase r') := by
        intro x hx
        obtain ⟨s, hs, hxs⟩ := hcov x hx
        by_cases hsr : s = r'
        · subst hsr
          exact ⟨r, Finset.mem_erase.2 ⟨hne, hr⟩, hxs.trans hreach.symm⟩
        · exact ⟨s, Finset.mem_erase.2 ⟨hsr, hs⟩, hxs⟩
      obtain ⟨t, hts, htcov, httr⟩ := ih _ hsub hcov'
      exact ⟨t, hts.trans (Finset.erase_subset _ _), htcov, httr⟩
    · refine ⟨cover, subset_rfl, hcov, ?_⟩
      intro r hr r' hr' hreach
      by_contra hne
      exact hbad ⟨r, hr, r', hr', hne, hreach⟩

/-- **Deleting `h` vertices of degree at most `B` leaves at most `1 + h(B-1)`
pieces.**  Each deletion retires the representative of the deleted vertex's own
piece and installs at most `B` new ones. -/
theorem exists_covering_transversal [DecidableEq V] [Fintype V] [DecidableRel G.Adj]
    (hconn : G.Connected) {B : ℕ} (hB : 1 ≤ B) (hdeg : ∀ v : V, G.degree v ≤ B) :
    ∀ S : Finset V, ∃ t : Finset V, Covers G (↑S) t ∧ Transversal G (↑S) t ∧
      t.card ≤ 1 + S.card * (B - 1) := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty =>
      obtain ⟨x₀⟩ := hconn.nonempty
      refine ⟨{x₀}, ?_, ?_, by simp⟩
      · intro x _
        refine ⟨x₀, Finset.mem_singleton_self _, ?_⟩
        have := hconn x x₀
        simpa [deleteFaces_empty] using this
      · intro r hr r' hr' _
        rw [Finset.mem_singleton] at hr hr'
        exact hr.trans hr'.symm
  | @insert v S hvS ih =>
      obtain ⟨t, hcov, htr, hcard⟩ := ih
      have hvnot : v ∉ (↑S : Set V) := by simpa using hvS
      obtain ⟨r₀, hr₀, hvr₀⟩ := hcov v hvnot
      -- the new candidate set
      refine ?_
      have hcover : Covers G (↑(insert v S)) ((t.erase r₀) ∪ G.neighborFinset v) := by
        intro x hx
        have hxS : x ∉ (↑S : Set V) := fun hcon => hx (by simp [hcon])
        have hxv : x ≠ v := fun hcon => hx (by simp [hcon])
        obtain ⟨s, hs, hxs⟩ := hcov x hxS
        by_cases hreachv : (deleteFaces G (↑S)).Reachable x v
        · -- x is in v's piece: it reaches a neighbour of v
          obtain ⟨p⟩ := hreachv
          obtain ⟨w, hw, hwreach⟩ := exists_adj_reachable (S := (↑S : Set V)) hxv p
          refine ⟨w, Finset.mem_union_right _ (by simpa using hw.symm), ?_⟩
          simpa [Finset.coe_insert, Set.insert_comm] using hwreach
        · -- x's piece avoids v entirely, so its old representative survives
          have hsr : s ≠ r₀ := by
            rintro rfl
            exact hreachv (hxs.trans hvr₀.symm)
          obtain ⟨p⟩ := hxs
          refine ⟨s, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hsr, hs⟩), ?_⟩
          have := reachable_delete_insert (v := v) p hreachv
          simpa [Finset.coe_insert] using this
      obtain ⟨t', hsub, hcov', htr'⟩ :=
        exists_transversal (G := G) (↑(insert v S)) _ hcover
      refine ⟨t', hcov', htr', ?_⟩
      have hle : t'.card ≤ ((t.erase r₀) ∪ G.neighborFinset v).card :=
        Finset.card_le_card hsub
      have hun : ((t.erase r₀) ∪ G.neighborFinset v).card ≤
          (t.erase r₀).card + (G.neighborFinset v).card := Finset.card_union_le _ _
      have herase : (t.erase r₀).card = t.card - 1 := Finset.card_erase_of_mem hr₀
      have hnb : (G.neighborFinset v).card ≤ B := by
        rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hdeg v
      have hins : (insert v S).card = S.card + 1 := Finset.card_insert_of_notMem hvS
      have hpos : 1 ≤ t.card := Finset.card_pos.2 ⟨r₀, hr₀⟩
      rw [hins]
      have hmul : (S.card + 1) * (B - 1) = S.card * (B - 1) + (B - 1) := by ring
      omega

/-! ## The S-avoiding geodesic -/

section Avoiding

open scoped Classical

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Deleting vertices only removes edges, so degrees do not grow. -/
theorem degree_deleteFaces_le (S : Set V) (v : V) :
    (deleteFaces G S).degree v ≤ G.degree v := by
  apply Finset.card_le_card
  intro x hx
  simp only [SimpleGraph.mem_neighborFinset] at hx ⊢
  exact hx.1

/-- A vertex of the deleted set is isolated, so its component is a single
point. -/
theorem ball_deleteFaces_of_mem {S : Set V} {r : V} (hr : r ∈ S) :
    ball (deleteFaces G S) r = {r} := by
  ext v
  simp only [mem_ball, Finset.mem_singleton]
  constructor
  · rintro ⟨p⟩
    cases p with
    | nil => rfl
    | cons hadj _ => exact absurd hr hadj.2.1
  · rintro rfl
    exact SimpleGraph.Reachable.refl _

/-- **The `S`-avoiding geodesic.**  Delete `h` faces from a large connected dual
of degree at most `B`.  At most `1 + h(B-1)` pieces survive, so one of them has
more than the Moore threshold many vertices, and the dichotomy produces a
geodesic of at least `L` edges inside it.

No claim is made that the geodesic is geodesic in the undeleted dual: it is
shortest in `G` with `S` removed, which is exactly what the corridor extraction
consumes. -/
theorem exists_avoiding_geodesic (hconn : G.Connected) {B L : ℕ}
    (hB : 1 ≤ B) (hL : 1 ≤ L) (hdeg : ∀ v : V, G.degree v ≤ B) (S : Finset V)
    (hcard : S.card + (1 + S.card * (B - 1)) * mooreBound B L < Fintype.card V) :
    ∃ r v : V, r ∉ S ∧ v ∉ S ∧
      (deleteFaces G (↑S : Set V)).Reachable r v ∧
      L ≤ (deleteFaces G (↑S : Set V)).dist r v := by
  obtain ⟨t, hcov, -, htcard⟩ :=
    exists_covering_transversal (G := G) hconn hB hdeg S
  -- every survivor lies in the component of some representative
  have hsub : (Finset.univ \ S) ⊆ t.biUnion (fun r => ball (deleteFaces G (↑S : Set V)) r) := by
    intro x hx
    have hxS : x ∉ (↑S : Set V) := by
      simpa using (Finset.mem_sdiff.1 hx).2
    obtain ⟨r, hr, hxr⟩ := hcov x hxS
    exact Finset.mem_biUnion.2 ⟨r, hr, mem_ball.2 hxr.symm⟩
  have hlive : Fintype.card V - S.card ≤
      ∑ r ∈ t, (ball (deleteFaces G (↑S : Set V)) r).card := by
    have h1 := le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
    rwa [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ] at h1
  -- so some component is bigger than the Moore threshold
  have hbig : ∃ r ∈ t, mooreBound B L < (ball (deleteFaces G (↑S : Set V)) r).card := by
    by_contra hno
    push_neg at hno
    have hsum : ∑ r ∈ t, (ball (deleteFaces G (↑S : Set V)) r).card ≤
        t.card * mooreBound B L := by
      calc ∑ r ∈ t, (ball (deleteFaces G (↑S : Set V)) r).card
          ≤ ∑ _r ∈ t, mooreBound B L := Finset.sum_le_sum fun r hr => hno r hr
        _ = t.card * mooreBound B L := by simp [Finset.sum_const, smul_eq_mul]
    have hmono : t.card * mooreBound B L ≤ (1 + S.card * (B - 1)) * mooreBound B L :=
      Nat.mul_le_mul_right _ htcard
    omega
  obtain ⟨r, -, hrbig⟩ := hbig
  obtain ⟨v, hreach, hdist⟩ :=
    exists_dist_ge_of_mooreBound_lt
      (G := deleteFaces G (↑S : Set V))
      (fun u => le_trans (degree_deleteFaces_le (↑S : Set V) u) (hdeg u)) r hrbig
  -- the root is not deleted: a deleted vertex is isolated
  have hrS : r ∉ S := by
    intro hcon
    rw [ball_deleteFaces_of_mem (by simpa using hcon)] at hrbig
    simp only [Finset.card_singleton] at hrbig
    have : 1 ≤ mooreBound B L := by simp [mooreBound]
    omega
  have hvS : v ∉ S := by
    intro hcon
    have hrv : r = v := by
      have := ball_deleteFaces_of_mem (G := G) (S := (↑S : Set V)) (by simpa using hcon)
      have hmem : r ∈ ball (deleteFaces G (↑S : Set V)) v := mem_ball.2 hreach.symm
      rw [this] at hmem
      simpa using hmem
    subst hrv
    exact hrS hcon
  exact ⟨r, v, hrS, hvS, hreach, hdist⟩

end Avoiding

end GoertzelV24DeletionComponents

end Mettapedia.GraphTheory.FourColor

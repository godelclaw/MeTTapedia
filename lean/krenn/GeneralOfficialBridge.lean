import Mathlib
import OfficialKrennDefinitions
import MatchingSum
import Gauge

/-!
# The official statement, at every vertex count

The official conjecture defines its perfect-matching sum by a recursion on a list
of vertices, always peeling the first one.  The general library defines the same
sum over a subset of an arbitrary vertex type.  This file identifies them, for
every vertex count and every dimension, so that the general machinery applies to
the official statement rather than to a paraphrase of it.

Two things have to be arranged.  The official weight is a function of an *ordered*
edge together with two colours, while the library weights unordered pairs of
coloured vertices; so the official weight is lifted to an unordered pair by
reading it in the direction its vertices prescribe.  And the official recursion
peels the head of a list, which is the deletion recursion at the smallest
remaining vertex.
-/

namespace GeneralOfficialBridge

open MonochromaticQuantumGraph Amplitude MatchingSum

variable {N D : Nat}

/-- The official weight read on an unordered pair of coloured vertices.  The pair
is oriented by its vertices; the colours break a tie that no matching edge ever
produces, since an edge never joins a vertex to itself. -/
noncomputable def symWeight (W : WeightsN N D ℂ) : Sym2 (Fin N × Fin D) → ℂ :=
  Sym2.lift ⟨fun p q =>
      if p.1 < q.1 then W (mkEdge p.1 q.1 p.2 q.2)
      else if q.1 < p.1 then W (mkEdge q.1 p.1 q.2 p.2)
      else if p.2 ≤ q.2 then W (mkEdge p.1 q.1 p.2 q.2)
      else W (mkEdge q.1 p.1 q.2 p.2), by
    intro p q
    dsimp only
    rcases lt_trichotomy p.1 q.1 with h | h | h
    · rw [if_pos h, if_neg (asymm h), if_pos h]
    · have h1 : ¬ p.1 < q.1 := by rw [h]; exact lt_irrefl _
      have h2 : ¬ q.1 < p.1 := by rw [h]; exact lt_irrefl _
      rw [if_neg h1, if_neg h2, if_neg h2, if_neg h1]
      rcases lt_trichotomy p.2 q.2 with hc | hc | hc
      · rw [if_pos (le_of_lt hc), if_neg (not_le.mpr hc)]
      · rw [h, hc]
      · rw [if_neg (not_le.mpr hc), if_pos (le_of_lt hc)]
    · rw [if_neg (asymm h), if_pos h, if_pos h]⟩

/-- On an edge whose endpoints increase, the lifted weight is the official one
read in that direction. -/
theorem symWeight_of_lt (W : WeightsN N D ℂ) (ι : Fin N → Fin D) {v u : Fin N}
    (h : v < u) :
    symWeight W (Sym2.map (paint ι) s(v, u)) = W (mkEdge v u (ι v) (ι u)) := by
  have hmap : Sym2.map (paint ι) s(v, u) = s((v, ι v), (u, ι u)) := rfl
  rw [hmap, symWeight, Sym2.lift_mk]
  dsimp only
  rw [if_pos h]

/-! ### The official vertex list -/

/-- The official vertex list is strictly increasing. -/
theorem vertices_pairwise : ∀ N : Nat, (vertices N).Pairwise (· < ·)
  | 0 => List.Pairwise.nil
  | N + 1 => by
    rw [vertices, List.pairwise_cons]
    refine ⟨fun b hb => ?_, ?_⟩
    · obtain ⟨a, -, rfl⟩ := List.mem_map.mp hb
      exact a.succ_pos
    · exact List.pairwise_map.mpr
        ((vertices_pairwise N).imp (fun h => Fin.succ_lt_succ_iff.mpr h))

/-- Every vertex appears in the official vertex list. -/
theorem mem_vertices : ∀ (N : Nat) (x : Fin N), x ∈ vertices N
  | 0, x => absurd x.isLt (by omega)
  | N + 1, x => by
    rw [vertices]
    rcases Fin.eq_zero_or_eq_succ x with rfl | ⟨y, rfl⟩
    · simp
    · exact List.mem_cons_of_mem _ (List.mem_map_of_mem (mem_vertices N y))

/-- The official vertex list exhausts the vertices. -/
theorem toFinset_vertices (N : Nat) : (vertices N).toFinset = Finset.univ :=
  Finset.eq_univ_of_forall (fun x => List.mem_toFinset.mpr (mem_vertices N x))

/-! ### The official sum is the library's

The official recursion peels the head of an increasing list, which is the deletion
recursion at the smallest remaining vertex.  Everything else is bookkeeping: an
increasing list has no repeats, so erasing from it matches erasing from the
corresponding vertex set, and a sum over a list without repeats is a sum over that
set.
-/

/-- Erasing from a list without repeats matches erasing from its vertex set. -/
theorem toFinset_erase {α : Type*} [DecidableEq α] {l : List α} (hl : l.Nodup) (a : α) :
    (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  rw [List.mem_toFinset, Finset.mem_erase, List.mem_toFinset, hl.mem_erase_iff]

/-- **The official matching sum is the library's**, for every increasing list of
vertices. -/
theorem pmSumList_eq_pmSum (W : WeightsN N D ℂ) (ι : Fin N → Fin D) :
    ∀ (n : Nat) (L : List (Fin N)), L.length ≤ n → L.Pairwise (· < ·) →
      pmSumList W ι L = pmSum (symWeight W) ι L.toFinset := by
  intro n
  induction n with
  | zero =>
    intro L hlen _
    rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)]
    simp [pmSumList, pmSumListAux]
  | succ n ih =>
    rintro (_ | ⟨v, _ | ⟨u, us⟩⟩) hlen hpw
    · simp [pmSumList, pmSumListAux]
    · rw [show pmSumList W ι [v] = 0 from rfl]
      refine (pmSum_of_odd _ _ ?_).symm
      simp
    · -- the head is smaller than everything after it
      obtain ⟨hv, hrest⟩ := List.pairwise_cons.mp hpw
      have hnd : (v :: u :: us).Nodup := hpw.imp (fun h => ne_of_lt h)
      have hvnot : v ∉ u :: us := fun h => absurd (hv v h) (lt_irrefl v)
      have hndvs : (u :: us).Nodup := hnd.of_cons
      -- unfold one step of the official recursion
      have hunfold : pmSumList W ι (v :: u :: us)
          = ((u :: us).map (fun w =>
              W (mkEdge v w (ι v) (ι w)) * pmSumList W ι ((u :: us).erase w))).sum := by
        rw [pmSumList]
        have hlen' : (v :: u :: us).length = us.length + 2 := by simp
        rw [hlen']
        refine congrArg List.sum (List.map_congr_left (fun w hw => ?_))
        have : ((u :: us).erase w).length = us.length := by
          rw [List.length_erase_of_mem hw]
          simp
        rw [pmSumList, this]
      rw [hunfold]
      -- and one step of the library recursion
      have hvmem : v ∈ (v :: u :: us).toFinset := by simp
      rw [pmSum_expand (symWeight W) ι hvmem]
      have herase : ((v :: u :: us).toFinset).erase v = (u :: us).toFinset := by
        rw [List.toFinset_cons, Finset.erase_insert (by simpa using hvnot)]
      rw [herase]
      rw [← List.sum_toFinset _ hndvs]
      refine Finset.sum_congr rfl (fun w hw => ?_)
      rw [List.mem_toFinset] at hw
      rw [symWeight_of_lt W ι (hv w hw), ← toFinset_erase hndvs]
      congr 1
      refine ih ((u :: us).erase w) ?_ (hpw.of_cons.sublist List.erase_sublist |>.imp id)
      rw [List.length_erase_of_mem hw]
      simp at hlen ⊢
      omega

/-- **The official perfect-matching sum is the amplitude**, at every vertex count
and every dimension. -/
theorem pmSumN_eq_amplitude (W : WeightsN N D ℂ) (ι : Fin N → Fin D) :
    pmSumN N D W ι = amplitude (symWeight W) ι := by
  rw [pmSumN, pmSumList,
    show pmSumListAux W ι (vertices N).length (vertices N) = pmSumList W ι (vertices N) from rfl,
    pmSumList_eq_pmSum W ι (vertices N).length (vertices N) le_rfl (vertices_pairwise N),
    toFinset_vertices, pmSum_univ]

/-- **The official equation system, in the library's language.**  A weight system
solves the official equations exactly when its amplitude is one on the officially
constant colourings and zero on all the others — at every vertex count and every
dimension.

This is what puts the general matching library behind the official statement
rather than behind a paraphrase of it. -/
theorem eqSystemN_iff_amplitude (W : WeightsN N D ℂ) :
    EqSystemN N D W ↔
      ∀ ι : Fin N → Fin D,
        amplitude (symWeight W) ι = if allEqual ι then (1 : ℂ) else 0 := by
  constructor
  · intro h ι
    rw [← pmSumN_eq_amplitude]
    exact h ι
  · intro h ι
    rw [pmSumN_eq_amplitude]
    exact h ι

/-- A chain of equalities makes every pair equal. -/
private theorem chain_eq_forall {α β : Type*} {f : α → β} :
    ∀ (L : List α), List.IsChain (fun v w => f v = f w) L →
      ∀ x ∈ L, ∀ y ∈ L, f x = f y
  | [] => fun _ x hx => by simp at hx
  | [a] => fun _ x hx y hy => by
      rw [List.mem_singleton] at hx hy
      rw [hx, hy]
  | a :: b :: t => fun h x hx y hy => by
      rw [List.isChain_cons_cons] at h
      obtain ⟨hab, hrest⟩ := h
      have hb : ∀ z ∈ b :: t, f z = f b :=
        fun z hz => chain_eq_forall (b :: t) hrest z hz b List.mem_cons_self
      rcases List.mem_cons.mp hx with rfl | hx'
      · rcases List.mem_cons.mp hy with rfl | hy'
        · rfl
        · rw [hab, hb y hy']
      · rcases List.mem_cons.mp hy with rfl | hy'
        · rw [hb x hx', ← hab]
        · rw [hb x hx', hb y hy']

/-- A constant colouring makes every list a chain. -/
private theorem isChain_of_const {α β : Type*} {f : α → β} (hf : ∀ x y, f x = f y) :
    ∀ L : List α, List.IsChain (fun v w => f v = f w) L
  | [] => by simp
  | [_] => by simp
  | a :: b :: t => List.isChain_cons_cons.mpr ⟨hf a b, isChain_of_const hf (b :: t)⟩

/-- A colouring is officially constant exactly when it is constant. -/
theorem allEqual_iff_const (ι : Fin N → Fin D) :
    allEqual ι ↔ ∀ x y : Fin N, ι x = ι y := by
  constructor
  · exact fun h x y => chain_eq_forall _ h x (mem_vertices N x) y (mem_vertices N y)
  · exact fun h => isChain_of_const h _

/-- **The official equation system, read as a statement about the amplitude.**  A
weight system solves the official equations exactly when its amplitude is one on
the constant colourings and zero on all the others. -/
theorem eqSystemN_iff_amplitude_const (W : WeightsN N D ℂ) :
    EqSystemN N D W ↔
      ∀ ι : Fin N → Fin D,
        amplitude (symWeight W) ι = if (∀ x y : Fin N, ι x = ι y) then (1 : ℂ) else 0 := by
  rw [eqSystemN_iff_amplitude]
  exact forall_congr' (fun ι => by rw [if_congr (allEqual_iff_const ι) rfl rfl])

/-! ### The official conjecture, reduced to descent

The general library reduces the conjecture, for every vertex count, to a single
descent hypothesis together with the six-vertex base case.  With the amplitude
bridge in place that reduction can be stated about the official equation system
itself.
-/

open Amplitude KrennGu

/-- **An official solution is a GHZ configuration.**  The equations force the
amplitude to one on the constant colourings, hence nonzero, and to zero on all
the others. -/
theorem isGHZ_of_eqSystemN {M : ℕ} (W : WeightsN M 3 ℂ) (h : EqSystemN M 3 W) :
    IsGHZ (symWeight W) := by
  rw [eqSystemN_iff_amplitude_const] at h
  constructor
  · intro k
    have hcond : ∀ x y : Fin M, Amplitude.const k x = Amplitude.const k y := fun _ _ => rfl
    rw [h (Amplitude.const k), if_pos hcond]
    exact one_ne_zero
  · intro c hc
    have hcond : ¬ (∀ x y : Fin M, c x = c y) := by
      intro hconst
      refine hc ?_
      rcases isEmpty_or_nonempty (Fin M) with hemp | hne
      · exact ⟨0, fun v => (hemp.false v).elim⟩
      · obtain ⟨x⟩ := hne
        exact ⟨c x, fun v => hconst v x⟩
    rw [h c, if_neg hcond]

/-- **An official solution makes the vertex count solvable.** -/
theorem solvable_of_eqSystemN {n : ℕ} (h : ∃ W : WeightsN (2 * n) 3 ℂ, EqSystemN (2 * n) 3 W) :
    Solvable n := by
  obtain ⟨W, hW⟩ := h
  exact ⟨symWeight W, isGHZ_of_eqSystemN W hW⟩

/-- **The official conjecture follows from descent and the six-vertex base case**,
at every vertex count.  This is the whole conjecture, in the exact terms of the
official statement, resting on one hypothesis about arbitrary even vertex sets. -/
theorem official_conjecture_of_descent (hd : Descent) (hb : BaseSix) :
    ∀ n : ℕ, 3 ≤ n → ¬ ∃ W : WeightsN (2 * n) 3 ℂ, EqSystemN (2 * n) 3 W :=
  fun n hn h => conjecture_of_descent hd hb n hn (solvable_of_eqSystemN h)

/-- Contrapositive form: an official solution at any vertex count above four,
together with descent, produces one of the six-vertex GHZ configurations that the
base case denies. -/
theorem baseSix_of_official {n : ℕ} (hd : Descent) (hn : 3 ≤ n)
    (h : ∃ W : WeightsN (2 * n) 3 ℂ, EqSystemN (2 * n) 3 W) :
    Solvable 3 :=
  six_of_descent hd hn (solvable_of_eqSystemN h)

/-! ### The two statements are the same statement

The bridge so far reads an official solution as a GHZ configuration.  With the
gauge normalisation available the converse holds too, so the library's own
solvability predicate and the official equation system have exactly the same
solutions.
-/

/-- An unordered weight read as an official one. -/
def officialOf (W' : Sym2 (Fin N × Fin D) → ℂ) : WeightsN N D ℂ :=
  fun e => W' s((e.u, e.i), (e.v, e.j))

/-- Reading an unordered weight as an official one and lifting it back is the
identity: every branch of the orientation agrees, because the pair is unordered. -/
theorem symWeight_officialOf (W' : Sym2 (Fin N × Fin D) → ℂ) :
    symWeight (officialOf W') = W' := by
  funext e
  induction e using Sym2.ind with
  | _ p q =>
    rw [symWeight, Sym2.lift_mk]
    dsimp only [officialOf]
    split_ifs
    · rfl
    · exact congrArg W' Sym2.eq_swap
    · rfl
    · exact congrArg W' Sym2.eq_swap

/-- On a nonempty vertex set, monochromatic means constant. -/
theorem monochromatic_iff_const {V C : Type*} [Nonempty V] (c : V → C) :
    Monochromatic c ↔ ∀ x y : V, c x = c y := by
  constructor
  · rintro ⟨k, hk⟩ x y
    rw [hk, hk]
  · intro h
    obtain ⟨x⟩ := ‹Nonempty V›
    exact ⟨c x, fun v => h v x⟩

/-- A normalised GHZ configuration solves the official equations. -/
theorem eqSystemN_officialOf [NeZero N] (W' : Sym2 (Fin N × Fin 3) → ℂ)
    (h1 : ∀ k : Fin 3, amplitude W' (Amplitude.const k) = 1)
    (h2 : ∀ c : Fin N → Fin 3, ¬ Monochromatic c → amplitude W' c = 0) :
    EqSystemN N 3 (officialOf W') := by
  have : Nonempty (Fin N) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩⟩
  rw [eqSystemN_iff_amplitude_const]
  intro ι
  rw [symWeight_officialOf]
  by_cases hc : ∀ x y : Fin N, ι x = ι y
  · rw [if_pos hc]
    obtain ⟨x⟩ := ‹Nonempty (Fin N)›
    have : ι = Amplitude.const (ι x) := funext (fun v => hc v x)
    rw [this]
    exact h1 (ι x)
  · rw [if_neg hc]
    exact h2 ι (fun hm => hc ((monochromatic_iff_const ι).mp hm))

/-- **Solvability and the official equations have the same solutions**, at every
positive vertex count.  The library's predicate asks only that the monochromatic
amplitudes be nonzero; the official system asks that they be one.  Gauge freedom
makes the two demands equivalent. -/
theorem solvable_iff_eqSystemN {n : ℕ} (hn : 0 < n) :
    Solvable n ↔ ∃ W : WeightsN (2 * n) 3 ℂ, EqSystemN (2 * n) 3 W := by
  have hpos : 0 < 2 * n := by omega
  have : NeZero (2 * n) := ⟨by omega⟩
  have : Nonempty (Fin (2 * n)) := ⟨⟨0, hpos⟩⟩
  constructor
  · rintro ⟨W, hW⟩
    obtain ⟨W', h1, h2⟩ := Gauge.exists_normalized W hW
    exact ⟨officialOf W', eqSystemN_officialOf W' h1 h2⟩
  · exact solvable_of_eqSystemN

/-- **The library's base case is the official six-vertex statement**, not merely a
consequence of it. -/
theorem baseSix_iff : BaseSix ↔ ¬ ∃ W : WeightsN 6 3 ℂ, EqSystemN 6 3 W := by
  have h := solvable_iff_eqSystemN (n := 3) (by omega)
  rw [show (2 * 3 : ℕ) = 6 from rfl] at h
  exact not_congr h

end GeneralOfficialBridge

import Mathlib.Combinatorics.SimpleGraph.Matching
import Mettapedia.GraphTheory.FourColor.GoertzelV24PermutationOrbitSurgery

/-!
# Orbit-count parity under a finite list of transpositions

Multiplying a finite permutation by one nontrivial transposition either
splits one orbit or merges two orbits.  In either case the number of orbits
changes parity.  Iterating gives the finite ribbon-surgery parity law used
by the Tutte--Kauffman face-potential argument: after `n` edge gluings, the
new boundary-orbit count differs from the original face-orbit count by `n`
modulo two.

This statement is purely finite permutation algebra.  It does not assume a
surface or a planar embedding.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24PermutationOrbitParity

open Equiv Equiv.Perm
open GoertzelV24PermutationOrbitSurgery

variable {D : Type*} [Fintype D] [DecidableEq D]

noncomputable section

/-- Successively multiply a permutation on the left by the transpositions
listed in `pairs`. -/
def leftSwapFold : List (D × D) → Perm D → Perm D
  | [], permutation => permutation
  | pair :: pairs, permutation =>
      leftSwapFold pairs (swap pair.1 pair.2 * permutation)

@[simp]
theorem leftSwapFold_nil (permutation : Perm D) :
    leftSwapFold [] permutation = permutation :=
  rfl

@[simp]
theorem leftSwapFold_cons (pair : D × D) (pairs : List (D × D))
    (permutation : Perm D) :
    leftSwapFold (pair :: pairs) permutation =
      leftSwapFold pairs (swap pair.1 pair.2 * permutation) :=
  rfl

/-- Every nontrivial transposition flips the parity of the permutation's
orbit count, independently of whether it performs a split or a merge. -/
theorem orbitCount_swap_mul_mod_two (permutation : Perm D) {left right : D}
    (hne : left ≠ right) :
    orbitCount (swap left right * permutation) % 2 =
      (orbitCount permutation + 1) % 2 := by
  by_cases hsame : permutation.SameCycle left right
  · rw [orbitCount_swap_mul_of_sameCycle permutation hne hsame]
  · have hmerge := orbitCount_swap_mul_of_not_sameCycle permutation hne hsame
    omega

/-- A list of `n` nontrivial transpositions changes orbit-count parity by
`n`.  No disjointness or surface hypothesis is needed. -/
theorem orbitCount_leftSwapFold_mod_two
    (pairs : List (D × D)) (permutation : Perm D)
    (hne : ∀ pair ∈ pairs, pair.1 ≠ pair.2) :
    orbitCount (leftSwapFold pairs permutation) % 2 =
      (orbitCount permutation + pairs.length) % 2 := by
  induction pairs generalizing permutation with
  | nil => simp
  | cons pair pairs inductionHypothesis =>
      have hpair : pair.1 ≠ pair.2 := hne pair (by simp)
      have htail : ∀ tailPair ∈ pairs, tailPair.1 ≠ tailPair.2 := by
        intro tailPair htailPair
        exact hne tailPair (by simp [htailPair])
      rw [leftSwapFold_cons,
        inductionHypothesis
          (swap pair.1 pair.2 * permutation) htail]
      have hflip := orbitCount_swap_mul_mod_two permutation hpair
      simp only [List.length_cons]
      calc
        (orbitCount (swap pair.1 pair.2 * permutation) + pairs.length) % 2 =
            (orbitCount (swap pair.1 pair.2 * permutation) % 2 +
              pairs.length % 2) % 2 := Nat.add_mod _ _ _
        _ = ((orbitCount permutation + 1) % 2 +
              pairs.length % 2) % 2 := by rw [hflip]
        _ = (orbitCount permutation + 1 + pairs.length) % 2 :=
          (Nat.add_mod _ _ _).symm
        _ = (orbitCount permutation + (pairs.length + 1)) % 2 := by
          congr 1
          omega

/-- The successive left transpositions factor from any initial permutation.
This elementary normalization is useful when the transpositions describe a
geometric gluing involution and the initial permutation describes the
unglued face boundaries. -/
theorem leftSwapFold_eq_mul (pairs : List (D × D)) (permutation : Perm D) :
    leftSwapFold pairs permutation = leftSwapFold pairs 1 * permutation := by
  induction pairs generalizing permutation with
  | nil => simp
  | cons pair pairs inductionHypothesis =>
      calc
        leftSwapFold (pair :: pairs) permutation =
            leftSwapFold pairs (swap pair.1 pair.2 * permutation) := rfl
        _ = leftSwapFold pairs 1 *
              (swap pair.1 pair.2 * permutation) :=
          inductionHypothesis _
        _ = (leftSwapFold pairs 1 * swap pair.1 pair.2) * permutation := by
          rw [mul_assoc]
        _ = leftSwapFold pairs (swap pair.1 pair.2) * permutation := by
          exact congrArg (fun value => value * permutation)
            (inductionHypothesis (swap pair.1 pair.2)).symm
        _ = leftSwapFold (pair :: pairs) 1 * permutation := by simp

/-- A point avoided by every recorded transposition is fixed by the gluing
permutation. -/
theorem leftSwapFold_one_apply_of_avoids
    (pairs : List (D × D)) (point : D)
    (havoids : ∀ pair ∈ pairs, point ≠ pair.1 ∧ point ≠ pair.2) :
    leftSwapFold pairs 1 point = point := by
  induction pairs with
  | nil => simp
  | cons pair pairs inductionHypothesis =>
      have hhead := havoids pair List.mem_cons_self
      have htail : ∀ tailPair ∈ pairs,
          point ≠ tailPair.1 ∧ point ≠ tailPair.2 := by
        intro tailPair htailPair
        exact havoids tailPair (List.mem_cons_of_mem _ htailPair)
      rw [leftSwapFold_cons, leftSwapFold_eq_mul]
      simp only [mul_one, Perm.mul_apply,
        swap_apply_of_ne_of_ne hhead.1 hhead.2]
      exact inductionHypothesis htail

/-- If one listed transposition is endpoint-disjoint from all the others,
the gluing permutation exchanges its two endpoints. -/
theorem leftSwapFold_one_apply_of_isolated_pair
    (pairs : List (D × D)) (hnodup : pairs.Nodup)
    (pair : D × D) (hpair : pair ∈ pairs)
    (hisolated : ∀ other ∈ pairs, other ≠ pair →
      pair.1 ≠ other.1 ∧ pair.1 ≠ other.2 ∧
      pair.2 ≠ other.1 ∧ pair.2 ≠ other.2) :
    leftSwapFold pairs 1 pair.1 = pair.2 ∧
      leftSwapFold pairs 1 pair.2 = pair.1 := by
  induction pairs with
  | nil => simp at hpair
  | cons head tail inductionHypothesis =>
      rcases List.mem_cons.mp hpair with heq | htail
      · subst head
        have hpairNotTail : pair ∉ tail := (List.nodup_cons.mp hnodup).1
        have htailAvoidsLeft : ∀ other ∈ tail,
            pair.2 ≠ other.1 ∧ pair.2 ≠ other.2 := by
          intro other hother
          have hne : other ≠ pair := by
            intro heq; subst other; exact hpairNotTail hother
          exact (hisolated other (List.mem_cons_of_mem _ hother) hne).2.2
        have htailAvoidsRight : ∀ other ∈ tail,
            pair.1 ≠ other.1 ∧ pair.1 ≠ other.2 := by
          intro other hother
          have hne : other ≠ pair := by
            intro heq; subst other; exact hpairNotTail hother
          have hsep := hisolated other (List.mem_cons_of_mem _ hother) hne
          exact ⟨hsep.1, hsep.2.1⟩
        constructor
        · rw [leftSwapFold_cons, leftSwapFold_eq_mul]
          simp only [mul_one, Perm.mul_apply, swap_apply_left]
          exact leftSwapFold_one_apply_of_avoids tail pair.2 htailAvoidsLeft
        · rw [leftSwapFold_cons, leftSwapFold_eq_mul]
          simp only [mul_one, Perm.mul_apply, swap_apply_right]
          exact leftSwapFold_one_apply_of_avoids tail pair.1 htailAvoidsRight
      · have hheadNe : head ≠ pair := by
          intro heq; subst head
          exact (List.nodup_cons.mp hnodup).1 htail
        have hheadAvoid := hisolated head List.mem_cons_self hheadNe
        have htailNodup : tail.Nodup := (List.nodup_cons.mp hnodup).2
        have htailIsolated : ∀ other ∈ tail, other ≠ pair →
            pair.1 ≠ other.1 ∧ pair.1 ≠ other.2 ∧
            pair.2 ≠ other.1 ∧ pair.2 ≠ other.2 := by
          intro other hother hne
          exact hisolated other (List.mem_cons_of_mem _ hother) hne
        have hIH := inductionHypothesis htailNodup htail htailIsolated
        constructor
        · rw [leftSwapFold_cons, leftSwapFold_eq_mul]
          simp only [mul_one, Perm.mul_apply,
            swap_apply_of_ne_of_ne hheadAvoid.1 hheadAvoid.2.1]
          exact hIH.1
        · rw [leftSwapFold_cons, leftSwapFold_eq_mul]
          simp only [mul_one, Perm.mul_apply,
            swap_apply_of_ne_of_ne hheadAvoid.2.2.1 hheadAvoid.2.2.2]
          exact hIH.2

/-! ## Permutation cycles as graph components -/

/-- A coherent successor on a finite degree-at-most-two graph forces every
supported vertex to have degree exactly two.  The no-two-cycle condition
ensures that successor and predecessor are the two distinct neighbours. -/
theorem isCycles_of_perm_adj_of_sq_ne_of_degree_le_two
    {W : Type*} [Fintype W] [DecidableEq W]
    (graph : SimpleGraph W) (perm : Perm W)
    (hadj : ∀ vertex, graph.Adj vertex (perm vertex))
    (hsquare : ∀ vertex, perm (perm vertex) ≠ vertex)
    (hdegree : ∀ vertex, (graph.neighborSet vertex).ncard ≤ 2) :
    graph.IsCycles := by
  intro vertex _hnonempty
  have hprevAdj : graph.Adj vertex (perm.symm vertex) := by
    have hraw := hadj (perm.symm vertex)
    simpa using hraw.symm
  have hnextPrev : perm vertex ≠ perm.symm vertex := by
    intro heq
    have happly := congrArg perm heq
    simp only [perm.apply_symm_apply] at happly
    exact hsquare vertex happly
  have hsubset : ({perm vertex, perm.symm vertex} : Set W) ⊆
      graph.neighborSet vertex := by
    intro neighbor hneighbor
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hneighbor
    rcases hneighbor with rfl | rfl
    · exact hadj vertex
    · exact hprevAdj
  have hlower : 2 ≤ (graph.neighborSet vertex).ncard := by
    calc
      2 = ({perm vertex, perm.symm vertex} : Set W).ncard := by
        simp [hnextPrev]
      _ ≤ (graph.neighborSet vertex).ncard := Set.ncard_le_ncard hsubset
  have hupper := hdegree vertex
  omega

/-- In a finite graph of cycles, a coherent successor with no two-cycles has
exactly the graph's connected components as its permutation cycles. -/
theorem sameCycle_iff_reachable_of_isCycles_of_adj_of_sq_ne
    {W : Type*} [Fintype W] [DecidableEq W]
    (graph : SimpleGraph W) (perm : Perm W)
    (hcycles : graph.IsCycles)
    (hadj : ∀ vertex, graph.Adj vertex (perm vertex))
    (hsquare : ∀ vertex, perm (perm vertex) ≠ vertex)
    (first second : W) :
    perm.SameCycle first second ↔ graph.Reachable first second := by
  have hprevAdj : ∀ vertex, graph.Adj vertex (perm.symm vertex) := by
    intro vertex
    have hraw := hadj (perm.symm vertex)
    simpa using hraw.symm
  have hnextPrev : ∀ vertex, perm vertex ≠ perm.symm vertex := by
    intro vertex heq
    have happly := congrArg perm heq
    simp only [perm.apply_symm_apply] at happly
    exact hsquare vertex happly
  have adjacent_sameCycle : ∀ {left right}, graph.Adj left right →
      perm.SameCycle left right := by
    intro left right hedge
    by_cases hnext : right = perm left
    · subst right
      exact (Perm.sameCycle_apply_right).2
        (Perm.SameCycle.refl perm left)
    · have hother := (hcycles.existsUnique_ne_adj (hadj left)).unique
        ⟨Ne.symm hnext, hedge⟩
        ⟨hnextPrev left, hprevAdj left⟩
      subst right
      exact (Perm.sameCycle_symm_apply_right).2
        (Perm.SameCycle.refl perm left)
  constructor
  · intro hsame
    rcases hsame.exists_nat_pow_eq with ⟨steps, hsteps⟩
    have hreach : ∀ steps : Nat,
        graph.Reachable first ((perm ^ steps) first) := by
      intro steps
      induction steps with
      | zero => simpa using SimpleGraph.Reachable.refl (G := graph) first
      | succ steps ih =>
          rw [pow_succ', Perm.mul_apply]
          exact ih.trans (hadj ((perm ^ steps) first)).reachable
    simpa [hsteps] using hreach steps
  · intro hreach
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
    induction hreach with
    | refl => exact Perm.SameCycle.refl perm first
    | tail hpath hedge inductionHypothesis =>
        exact inductionHypothesis.trans (adjacent_sameCycle hedge)

/-- Map a permutation orbit to the graph component containing any of its
representatives, provided the two equivalence relations agree. -/
def permOrbitToConnectedComponent
    {W : Type*} [Fintype W] [DecidableEq W]
    (graph : SimpleGraph W) (perm : Perm W)
    (hrelation : ∀ first second,
      perm.SameCycle first second ↔ graph.Reachable first second) :
    Quotient (Perm.SameCycle.setoid perm) → graph.ConnectedComponent :=
  Quotient.lift (fun vertex => graph.connectedComponentMk vertex) (by
    intro first second hsame
    exact SimpleGraph.ConnectedComponent.sound
      ((hrelation first second).1 hsame))

theorem permOrbitToConnectedComponent_injective
    {W : Type*} [Fintype W] [DecidableEq W]
    (graph : SimpleGraph W) (perm : Perm W)
    (hrelation : ∀ first second,
      perm.SameCycle first second ↔ graph.Reachable first second) :
    Function.Injective
      (permOrbitToConnectedComponent graph perm hrelation) := by
  intro left right heq
  induction left, right using Quotient.inductionOn₂ with
  | _ left right =>
      apply Quotient.sound
      exact (hrelation left right).2
        (SimpleGraph.ConnectedComponent.exact heq)

theorem permOrbitToConnectedComponent_surjective
    {W : Type*} [Fintype W] [DecidableEq W]
    (graph : SimpleGraph W) (perm : Perm W)
    (hrelation : ∀ first second,
      perm.SameCycle first second ↔ graph.Reachable first second) :
    Function.Surjective
      (permOrbitToConnectedComponent graph perm hrelation) := by
  intro component
  induction component using SimpleGraph.ConnectedComponent.ind with
  | _ vertex =>
      exact ⟨Quotient.mk _ vertex, rfl⟩

/-- Equality of cycle relation and reachability gives a canonical equivalence
between permutation orbits and graph components. -/
def permOrbitEquivConnectedComponent
    {W : Type*} [Fintype W] [DecidableEq W]
    (graph : SimpleGraph W) (perm : Perm W)
    (hrelation : ∀ first second,
      perm.SameCycle first second ↔ graph.Reachable first second) :
    Quotient (Perm.SameCycle.setoid perm) ≃ graph.ConnectedComponent :=
  Equiv.ofBijective (permOrbitToConnectedComponent graph perm hrelation)
    ⟨permOrbitToConnectedComponent_injective graph perm hrelation,
      permOrbitToConnectedComponent_surjective graph perm hrelation⟩

/-- Hence the finite permutation orbit count is literally the number of
connected components. -/
theorem orbitCount_eq_natCard_connectedComponent
    {W : Type*} [Fintype W] [DecidableEq W]
    (graph : SimpleGraph W) (perm : Perm W)
    (hrelation : ∀ first second,
      perm.SameCycle first second ↔ graph.Reachable first second) :
    orbitCount perm = Nat.card graph.ConnectedComponent := by
  unfold orbitCount
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_congr
    (permOrbitEquivConnectedComponent graph perm hrelation)

end

end GoertzelV24PermutationOrbitParity

end Mettapedia.GraphTheory.FourColor

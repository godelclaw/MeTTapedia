import Mettapedia.GraphTheory.FourColor.GoertzelV24NoncrossingSweepPigeonhole
import Mathlib.Data.List.Pairwise

/-!
# Noncrossing matchings give literal LIFO sweep states

This file supplies the geometric half of the elementary length--depth
alternative used in the long-boundary branch.  Arcs are listed by increasing
left endpoint.  Noncrossing then forces the right endpoints of the arcs open
at any cut to occur in the reverse order, so their labels form a stack.

The final theorem combines this fact with the exact finite-state collision
theorem in `GoertzelV24NoncrossingSweepPigeonhole`.  It is deliberately only
an ordered-boundary theorem: constructing these matchings from a target
zero-Count map remains part of M1.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24NoncrossingSweepLifo

open GoertzelV24NoncrossingSweepPigeonhole
open scoped BigOperators

universe u v

/-- A labelled arc between two positions of a finite linear order. -/
structure LabeledArc (K : Type u) (n : Nat) where
  left : Fin n
  right : Fin n
  label : K

namespace LabeledArc

/-- The cut lies after the left end and no later than the right end. -/
def IsOpenAt (arc : LabeledArc K n) (cut : Fin n) : Prop :=
  arc.left < cut ∧ cut ≤ arc.right

end LabeledArc

/-- A noncrossing partial matching, written in increasing order of left
endpoints.  `endpointDisjoint` says literally that two distinct arcs share no
boundary position. -/
structure NoncrossingMatching (K : Type u) (n : Nat) where
  arcs : List (LabeledArc K n)
  proper : ∀ arc ∈ arcs, arc.left < arc.right
  leftOrdered : arcs.Pairwise fun first later => first.left < later.left
  endpointDisjoint : arcs.Pairwise fun first later =>
    first.left ≠ later.left ∧ first.left ≠ later.right ∧
      first.right ≠ later.left ∧ first.right ≠ later.right
  noncrossing : arcs.Pairwise fun first later =>
    ¬(first.left < later.left ∧ later.left < first.right ∧
      first.right < later.right)

namespace NoncrossingMatching

/-- The arcs open at one cut, still in increasing order of left endpoint. -/
def openArcs (matching : NoncrossingMatching K n) (cut : Fin n) :
    List (LabeledArc K n) :=
  matching.arcs.filter fun arc => decide (arc.left < cut ∧ cut ≤ arc.right)

/-- The literal stack at a cut, top first.  Reversing the left-endpoint order
puts the most recently opened arc at the head. -/
def stackAt (matching : NoncrossingMatching K n) (cut : Fin n) : List K :=
  (matching.openArcs cut).reverse.map LabeledArc.label

/-- Open arcs are properly nested: later opening means earlier closing. -/
theorem openArcs_pairwise_right_decreasing
    (matching : NoncrossingMatching K n) (cut : Fin n) :
    (matching.openArcs cut).Pairwise fun first later =>
      later.right < first.right := by
  let opened := matching.openArcs cut
  have hleft : opened.Pairwise fun first later => first.left < later.left := by
    exact matching.leftOrdered.filter _
  have hendpoints : opened.Pairwise fun first later =>
      first.left ≠ later.left ∧ first.left ≠ later.right ∧
        first.right ≠ later.left ∧ first.right ≠ later.right := by
    exact matching.endpointDisjoint.filter _
  have hnoncrossing : opened.Pairwise fun first later =>
      ¬(first.left < later.left ∧ later.left < first.right ∧
        first.right < later.right) := by
    exact matching.noncrossing.filter _
  rw [List.pairwise_iff_get]
  intro i j hij
  have hleftij := hleft.rel_get_of_lt hij
  have hendpointsij := hendpoints.rel_get_of_lt hij
  have hnoncrossingij := hnoncrossing.rel_get_of_lt hij
  have hiMem : opened.get i ∈ opened := opened.get_mem i
  have hjMem : opened.get j ∈ opened := opened.get_mem j
  have hiOpen : (opened.get i).IsOpenAt cut := by
    simpa [opened, openArcs, LabeledArc.IsOpenAt] using
      (List.mem_filter.mp hiMem).2
  have hjOpen : (opened.get j).IsOpenAt cut := by
    simpa [opened, openArcs, LabeledArc.IsOpenAt] using
      (List.mem_filter.mp hjMem).2
  have hjLeft_lt_hiRight : (opened.get j).left < (opened.get i).right :=
    lt_of_lt_of_le hjOpen.1 hiOpen.2
  by_contra hnot
  have hiRight_le_hjRight : (opened.get i).right ≤ (opened.get j).right :=
    le_of_not_gt hnot
  have hiRight_lt_hjRight : (opened.get i).right < (opened.get j).right :=
    lt_of_le_of_ne hiRight_le_hjRight hendpointsij.2.2.2
  exact hnoncrossingij ⟨hleftij, hjLeft_lt_hiRight, hiRight_lt_hjRight⟩

end NoncrossingMatching

/-- A finite collection of noncrossing matching families together with the
local alphabet letter recorded at every cut position. -/
structure SweepData (A : Type u) (K : Type v) (r n : Nat) where
  letter : Fin n → A
  family : Fin r → NoncrossingMatching K n

namespace SweepData

/-- The raw human-readable sweep record at one cut. -/
def rawState (data : SweepData A K r n) (cut : Fin n) :
    A × (Fin r → List K) :=
  ⟨data.letter cut, fun family => (data.family family).stackAt cut⟩

/-- Encode a shallow raw sweep record in the exact finite carrier. -/
def codedState (data : SweepData A K r n) (D : Nat)
    (hbounded : ∀ family cut, ((data.family family).stackAt cut).length ≤ D)
    (cut : Fin n) : SweepState A K r D :=
  ⟨data.letter cut, fun family =>
    boundedListEquivStackCode K D
      ⟨(data.family family).stackAt cut, hbounded family cut⟩⟩

/-- Equality of finite codes is literal equality of the local letter and of
every labelled stack. -/
theorem rawState_eq_of_codedState_eq
    (data : SweepData A K r n) (D : Nat)
    (hbounded : ∀ family cut, ((data.family family).stackAt cut).length ≤ D)
    {first second : Fin n}
    (heq : data.codedState D hbounded first =
      data.codedState D hbounded second) :
    data.rawState first = data.rawState second := by
  apply Prod.ext
  · exact congrArg (fun state : SweepState A K r D => state.1) heq
  · funext family
    have hcode := congrFun
      (congrArg (fun state : SweepState A K r D => state.2) heq) family
    have hinv := congrArg
      (fun code => ((boundedListEquivStackCode K D).symm code).1) hcode
    exact hinv

/-- **Noncrossing length--depth alternative.**  If the number of cut
positions exceeds the exact number of bounded stack states, then either one
family is deeper than `D`, or two distinct cuts have identical literal sweep
records. -/
theorem exists_deep_family_or_distinct_eq_rawState
    [Fintype A] [DecidableEq A] [Fintype K] [DecidableEq K]
    (data : SweepData A K r n) (D : Nat)
    (hmany :
      Fintype.card A *
          (∑ d : Fin (D + 1), Fintype.card K ^ (d : Nat)) ^ r < n) :
    (∃ family cut, D < ((data.family family).stackAt cut).length) ∨
      ∃ first second : Fin n,
        first ≠ second ∧ data.rawState first = data.rawState second := by
  by_cases hdeep :
      ∃ family cut, D < ((data.family family).stackAt cut).length
  · exact Or.inl hdeep
  · right
    have hbounded :
        ∀ family cut, ((data.family family).stackAt cut).length ≤ D := by
      intro family cut
      apply Nat.le_of_not_gt
      intro hlt
      exact hdeep ⟨family, cut, hlt⟩
    obtain ⟨first, second, hne, heq⟩ :=
      exists_distinct_eq_sweepState r D n (data.codedState D hbounded) hmany
    exact ⟨first, second, hne,
      data.rawState_eq_of_codedState_eq D hbounded heq⟩

end SweepData

end GoertzelV24NoncrossingSweepLifo

end Mettapedia.GraphTheory.FourColor

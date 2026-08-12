import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Pigeonhole
import Mettapedia.GraphTheory.FourColor.GoertzelV24CorridorTransferWord

/-!
# Reachable-set pumping for heterogeneous transfer words

A realized source corridor is a word `M₁ ⋯ Mₙ` of possibly different finite
profile relations.  Repeating one profile along one path is not enough for
reductive descent: every accepting path of the shortened word must lift
through the deleted middle.

The correct finite state for that quantifier is the whole set of profiles
reachable after a prefix.  If two cuts have the same reachable set, deleting
the word between them preserves every later acceptance predicate.  Since a
finite profile carrier has only finitely many subsets, a sufficiently long
heterogeneous word has two such cuts.  No determinism, homogeneous matrix
power, or diagonal self-loop is assumed.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24CorridorTransferWordReachablePumping

open GoertzelV24CorridorTransferWord

universe u

noncomputable section

/-- All profiles reachable through one heterogeneous word from the displayed
finite initial support. -/
noncomputable def transferWordReachableSet
    {Profile : Type u} [Fintype Profile] [DecidableEq Profile]
    (steps : List (Profile → Profile → Prop))
    (initial : Finset Profile) : Finset Profile := by
  classical
  exact Finset.univ.filter fun finish =>
    ∃ start ∈ initial, ExactTransferWord steps start finish

/-- Membership exposes an actual initial profile and exact path. -/
theorem mem_transferWordReachableSet_iff
    {Profile : Type u} [Fintype Profile] [DecidableEq Profile]
    (steps : List (Profile → Profile → Prop))
    (initial : Finset Profile) (finish : Profile) :
    finish ∈ transferWordReachableSet steps initial ↔
      ∃ start ∈ initial, ExactTransferWord steps start finish := by
  classical
  simp [transferWordReachableSet]

/-- Acceptance is equivalently a reachable profile satisfying the terminal
predicate. -/
theorem transferWordAccepts_iff_exists_mem_reachableSet
    {Profile : Type u} [Fintype Profile] [DecidableEq Profile]
    (steps : List (Profile → Profile → Prop))
    (initial : Finset Profile) (isAccepting : Profile → Prop) :
    TransferWordAccepts steps initial isAccepting ↔
      ∃ finish ∈ transferWordReachableSet steps initial,
        isAccepting finish := by
  constructor
  · rintro ⟨start, hstart, finish, hpath, haccepting⟩
    exact ⟨finish,
      (mem_transferWordReachableSet_iff steps initial finish).2
        ⟨start, hstart, hpath⟩,
      haccepting⟩
  · rintro ⟨finish, hfinish, haccepting⟩
    rcases (mem_transferWordReachableSet_iff steps initial finish).1 hfinish with
      ⟨start, hstart, hpath⟩
    exact ⟨start, hstart, finish, hpath, haccepting⟩

/-- If inserting a middle word leaves the whole reachable set after the
prefix unchanged, every acceptance of the shortened word lifts through that
middle.  The profile before the middle may change; only its exit profile,
which feeds the fixed right context, is retained. -/
theorem transferWordAccepts_insert_of_reachableSet_eq
    {Profile : Type u} [Fintype Profile] [DecidableEq Profile]
    (left middle right : List (Profile → Profile → Prop))
    (initial : Finset Profile) (isAccepting : Profile → Prop)
    (hreachable : transferWordReachableSet left initial =
      transferWordReachableSet (left ++ middle) initial)
    (hshort : TransferWordAccepts (left ++ right) initial isAccepting) :
    TransferWordAccepts (left ++ middle ++ right) initial isAccepting := by
  rcases hshort with ⟨start, hstart, finish, hpath, haccepting⟩
  rcases (exactTransferWord_append_iff left right start finish).1 hpath with
    ⟨seam, hleft, hright⟩
  have hseamLeft : seam ∈ transferWordReachableSet left initial :=
    (mem_transferWordReachableSet_iff left initial seam).2
      ⟨start, hstart, hleft⟩
  have hseamMiddle :
      seam ∈ transferWordReachableSet (left ++ middle) initial := by
    rw [← hreachable]
    exact hseamLeft
  rcases (mem_transferWordReachableSet_iff
      (left ++ middle) initial seam).1 hseamMiddle with
    ⟨newStart, hnewStart, hleftMiddle⟩
  refine ⟨newStart, hnewStart, finish, ?_, haccepting⟩
  exact (exactTransferWord_append_iff (left ++ middle) right
    newStart finish).2 ⟨seam, hleftMiddle, hright⟩

/-- Reductive polarity: rejection of the original word survives deletion of
a middle segment whenever the two surrounding prefix reachable sets agree. -/
theorem not_transferWordAccepts_erase_of_reachableSet_eq
    {Profile : Type u} [Fintype Profile] [DecidableEq Profile]
    (left middle right : List (Profile → Profile → Prop))
    (initial : Finset Profile) (isAccepting : Profile → Prop)
    (hreachable : transferWordReachableSet left initial =
      transferWordReachableSet (left ++ middle) initial)
    (hfull : ¬ TransferWordAccepts
      (left ++ middle ++ right) initial isAccepting) :
    ¬ TransferWordAccepts (left ++ right) initial isAccepting := by
  intro hshort
  exact hfull (transferWordAccepts_insert_of_reachableSet_eq
    left middle right initial isAccepting hreachable hshort)

/-- Reachable states after a numbered prefix of a heterogeneous word. -/
noncomputable def transferWordPrefixReachableSet
    {Profile : Type u} [Fintype Profile] [DecidableEq Profile]
    (steps : List (Profile → Profile → Prop))
    (initial : Finset Profile) (cut : Nat) : Finset Profile :=
  transferWordReachableSet (steps.take cut) initial

/-- More prefix positions than finite reachable-profile sets force two
ordered cuts with exactly the same whole reachable set. -/
theorem exists_equal_transferWordPrefixReachableSets
    {Profile : Type u} [Fintype Profile] [DecidableEq Profile]
    (steps : List (Profile → Profile → Prop))
    (initial : Finset Profile)
    (hlarge : Fintype.card (Finset Profile) < steps.length + 1) :
    ∃ first second : Fin (steps.length + 1),
      first.val < second.val ∧
        transferWordPrefixReachableSet steps initial first.val =
          transferWordPrefixReachableSet steps initial second.val := by
  let states : Fin (steps.length + 1) → Finset Profile := fun cut =>
    transferWordPrefixReachableSet steps initial cut.val
  have hcard : Fintype.card (Finset Profile) <
      Fintype.card (Fin (steps.length + 1)) := by
    simpa using hlarge
  rcases Fintype.exists_ne_map_eq_of_card_lt states hcard with
    ⟨first, second, hne, heq⟩
  have hval : first.val ≠ second.val := by
    intro hval
    exact hne (Fin.ext hval)
  rcases lt_or_gt_of_ne hval with hfirst | hsecond
  · exact ⟨first, second, hfirst, heq⟩
  · exact ⟨second, first, hsecond, heq.symm⟩

/-- Explicit powerset form of the same pigeonhole threshold. -/
theorem exists_equal_transferWordPrefixReachableSets_of_two_pow
    {Profile : Type u} [Fintype Profile] [DecidableEq Profile]
    (steps : List (Profile → Profile → Prop))
    (initial : Finset Profile)
    (hlarge : 2 ^ Fintype.card Profile < steps.length + 1) :
    ∃ first second : Fin (steps.length + 1),
      first.val < second.val ∧
        transferWordPrefixReachableSet steps initial first.val =
          transferWordPrefixReachableSet steps initial second.val := by
  apply exists_equal_transferWordPrefixReachableSets steps initial
  simpa [Fintype.card_finset] using hlarge

private theorem take_eq_take_append_drop_take
    {α : Type*} (items : List α) {first second : Nat}
    (horder : first ≤ second) :
    items.take second =
      items.take first ++ (items.drop first).take (second - first) := by
  have hadd : first + (second - first) = second := Nat.add_sub_of_le horder
  calc
    items.take second = items.take (first + (second - first)) :=
      congrArg (items.take ·) hadd.symm
    _ = items.take first ++ (items.drop first).take (second - first) :=
      List.take_add

/-- Pigeonhole packaged as an actual nonempty removable middle word.  The
prefix before and after that middle have identical reachable-profile sets. -/
theorem exists_transferWordReachableSetPump
    {Profile : Type u} [Fintype Profile] [DecidableEq Profile]
    (steps : List (Profile → Profile → Prop))
    (initial : Finset Profile)
    (hlarge : Fintype.card (Finset Profile) < steps.length + 1) :
    ∃ left middle right : List (Profile → Profile → Prop),
      steps = left ++ middle ++ right ∧
        middle ≠ [] ∧
          transferWordReachableSet left initial =
            transferWordReachableSet (left ++ middle) initial := by
  rcases exists_equal_transferWordPrefixReachableSets steps initial hlarge with
    ⟨first, second, horder, heq⟩
  let left := steps.take first.val
  let middle := (steps.drop first.val).take (second.val - first.val)
  let right := steps.drop second.val
  have hfirstLe : first.val ≤ second.val := Nat.le_of_lt horder
  have htake : steps.take second.val = left ++ middle := by
    exact take_eq_take_append_drop_take steps hfirstLe
  have hword : steps = left ++ middle ++ right := by
    calc
      steps = steps.take second.val ++ steps.drop second.val :=
        (List.take_append_drop second.val steps).symm
      _ = left ++ middle ++ right := by rw [htake]
  have hsecondLe : second.val ≤ steps.length := by
    have hlt := second.isLt
    omega
  have hmiddleLength : middle.length = second.val - first.val := by
    apply List.length_take_of_le
    simp only [List.length_drop]
    omega
  have hmiddle : middle ≠ [] := by
    intro hempty
    have hzero : middle.length = 0 := by simp [hempty]
    omega
  refine ⟨left, middle, right, hword, hmiddle, ?_⟩
  change transferWordPrefixReachableSet steps initial first.val =
    transferWordReachableSet (left ++ middle) initial
  rw [← htake]
  exact heq

/-- Every sufficiently long rejected heterogeneous transfer word has a
strictly shorter rejected word obtained by deleting one concrete middle
segment.  This is the finite-powerset fallback for the source's L2 pumping
step; geometric realization of the shortened word is a separate use-site
obligation. -/
theorem exists_strictlyShorter_rejected_transferWord
    {Profile : Type u} [Fintype Profile] [DecidableEq Profile]
    (steps : List (Profile → Profile → Prop))
    (initial : Finset Profile) (isAccepting : Profile → Prop)
    (hlarge : Fintype.card (Finset Profile) < steps.length + 1)
    (hfull : ¬ TransferWordAccepts steps initial isAccepting) :
    ∃ shorter : List (Profile → Profile → Prop),
      shorter.length < steps.length ∧
        ¬ TransferWordAccepts shorter initial isAccepting := by
  rcases exists_transferWordReachableSetPump steps initial hlarge with
    ⟨left, middle, right, hword, hmiddle, hreachable⟩
  let shorter := left ++ right
  have hfull' : ¬ TransferWordAccepts
      (left ++ middle ++ right) initial isAccepting := by
    simpa [← hword] using hfull
  have hshort : ¬ TransferWordAccepts shorter initial isAccepting := by
    exact not_transferWordAccepts_erase_of_reachableSet_eq
      left middle right initial isAccepting hreachable hfull'
  refine ⟨shorter, ?_, hshort⟩
  have hmiddleLength : 0 < middle.length := by
    apply Nat.pos_of_ne_zero
    intro hzero
    exact hmiddle (List.length_eq_zero_iff.mp hzero)
  have hlength := congrArg List.length hword
  simp only [List.length_append] at hlength
  simp only [shorter, List.length_append]
  omega

end

end GoertzelV24CorridorTransferWordReachablePumping

end Mettapedia.GraphTheory.FourColor

import Mettapedia.GraphTheory.FourColor.GoertzelV24CorridorTransferWordReachablePumping

/-!
# Verified mode compression for heterogeneous reachable-set pumping

The source corridor is a heterogeneous word of finite support relations.  Its
reductive pumping argument depends on equality of complete reachable-profile
sets, not merely on equality of one selected profile.  The unrestricted
powerset of a conservative profile carrier is therefore only a fallback
bound.

This module gives the smaller, certificate-facing replacement.  A mode
compression has an encoder and decoder which are inverse only on an explicit
class of admissible reachable sets.  If every prefix reachable set of a word
is admissible, pigeonhole is performed on the finite mode carrier.  Equality
of modes then reconstructs equality of the complete reachable sets, so the
existing deletion theorem applies unchanged.

No particular mode table is assumed here.  A source-specific implementation
must still prove that its literal initial state and heterogeneous letters keep
every prefix reachable set admissible.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ReachableSetModeCompression

open GoertzelV24CorridorTransferWord
open GoertzelV24CorridorTransferWordReachablePumping

universe u v

noncomputable section

/-- A finite presentation which is lossless on a declared class of reachable
profile sets.  It need not encode arbitrary subsets injectively. -/
structure ReachableSetModeCompression
    (Profile : Type u) (Mode : Type v) where
  encode : Finset Profile → Mode
  decode : Mode → Finset Profile
  admissible : Finset Profile → Prop
  decode_encode : ∀ {states : Finset Profile},
    admissible states → decode (encode states) = states

/-- Equal mode codes reconstruct equal admissible reachable sets. -/
theorem ReachableSetModeCompression.eq_of_encode_eq
    {Profile : Type u} {Mode : Type v}
    (compression : ReachableSetModeCompression Profile Mode)
    {left right : Finset Profile}
    (hleft : compression.admissible left)
    (hright : compression.admissible right)
    (hcode : compression.encode left = compression.encode right) :
    left = right := by
  calc
    left = compression.decode (compression.encode left) :=
      (compression.decode_encode hleft).symm
    _ = compression.decode (compression.encode right) :=
      congrArg compression.decode hcode
    _ = right := compression.decode_encode hright

/-- More prefix positions than verified reachable-set modes force two ordered
cuts with exactly the same complete reachable set. -/
theorem exists_equal_transferWordPrefixReachableSets_of_modeCompression
    {Profile : Type u} {Mode : Type v}
    [Fintype Profile] [DecidableEq Profile] [Fintype Mode]
    (compression : ReachableSetModeCompression Profile Mode)
    (steps : List (Profile → Profile → Prop))
    (initial : Finset Profile)
    (hadmissible : ∀ cut : Fin (steps.length + 1),
      compression.admissible
        (transferWordPrefixReachableSet steps initial cut.val))
    (hlarge : Fintype.card Mode < steps.length + 1) :
    ∃ first second : Fin (steps.length + 1),
      first.val < second.val ∧
        transferWordPrefixReachableSet steps initial first.val =
          transferWordPrefixReachableSet steps initial second.val := by
  let modeAt : Fin (steps.length + 1) → Mode := fun cut =>
    compression.encode
      (transferWordPrefixReachableSet steps initial cut.val)
  have hcard : Fintype.card Mode < Fintype.card (Fin (steps.length + 1)) := by
    simpa using hlarge
  rcases Fintype.exists_ne_map_eq_of_card_lt modeAt hcard with
    ⟨first, second, hne, hmode⟩
  have hvalue : first.val ≠ second.val := by
    intro heq
    exact hne (Fin.ext heq)
  have hsets :
      transferWordPrefixReachableSet steps initial first.val =
        transferWordPrefixReachableSet steps initial second.val := by
    apply compression.eq_of_encode_eq
      (hadmissible first) (hadmissible second)
    exact hmode
  rcases lt_or_gt_of_ne hvalue with hfirst | hsecond
  · exact ⟨first, second, hfirst, hsets⟩
  · exact ⟨second, first, hsecond, hsets.symm⟩

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

/-- A verified finite mode presentation packages the repeated prefix sets as
one concrete nonempty removable middle word. -/
theorem exists_transferWordReachableSetPump_of_modeCompression
    {Profile : Type u} {Mode : Type v}
    [Fintype Profile] [DecidableEq Profile] [Fintype Mode]
    (compression : ReachableSetModeCompression Profile Mode)
    (steps : List (Profile → Profile → Prop))
    (initial : Finset Profile)
    (hadmissible : ∀ cut : Fin (steps.length + 1),
      compression.admissible
        (transferWordPrefixReachableSet steps initial cut.val))
    (hlarge : Fintype.card Mode < steps.length + 1) :
    ∃ left middle right : List (Profile → Profile → Prop),
      steps = left ++ middle ++ right ∧
        middle ≠ [] ∧
          transferWordReachableSet left initial =
            transferWordReachableSet (left ++ middle) initial := by
  rcases exists_equal_transferWordPrefixReachableSets_of_modeCompression
      compression steps initial hadmissible hlarge with
    ⟨first, second, horder, heq⟩
  let left := steps.take first.val
  let middle := (steps.drop first.val).take (second.val - first.val)
  let right := steps.drop second.val
  have hfirstLe : first.val ≤ second.val := Nat.le_of_lt horder
  have htake : steps.take second.val = left ++ middle :=
    take_eq_take_append_drop_take steps hfirstLe
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

/-- Rejection of a sufficiently long heterogeneous word survives deletion of
a concrete middle segment once its prefix reachable sets have a verified
finite mode presentation. -/
theorem exists_strictlyShorter_rejected_transferWord_of_modeCompression
    {Profile : Type u} {Mode : Type v}
    [Fintype Profile] [DecidableEq Profile] [Fintype Mode]
    (compression : ReachableSetModeCompression Profile Mode)
    (steps : List (Profile → Profile → Prop))
    (initial : Finset Profile) (isAccepting : Profile → Prop)
    (hadmissible : ∀ cut : Fin (steps.length + 1),
      compression.admissible
        (transferWordPrefixReachableSet steps initial cut.val))
    (hlarge : Fintype.card Mode < steps.length + 1)
    (hfull : ¬ TransferWordAccepts steps initial isAccepting) :
    ∃ shorter : List (Profile → Profile → Prop),
      shorter.length < steps.length ∧
        ¬ TransferWordAccepts shorter initial isAccepting := by
  rcases exists_transferWordReachableSetPump_of_modeCompression
      compression steps initial hadmissible hlarge with
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

end GoertzelV24ReachableSetModeCompression

end Mettapedia.GraphTheory.FourColor

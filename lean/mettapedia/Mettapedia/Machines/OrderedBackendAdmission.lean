import Mathlib.Data.Multiset.Basic
import Mathlib.Data.List.GetD
import Mathlib.Tactic

/-!
# Ordered observers require an order-bearing realization

An unordered representation identifies permutations. It cannot implement FIFO
or LIFO observation on every input containing two different elements. This is
a representation premise: an implementation may store additional order data
and then establish a stronger realization. It is not an impossibility claim
about the PathMap data structure itself.

The capability table models the currently admitted sequence adapters and the
current unordered adapter. Refusal precedes installation and leaves the
original state intact. Native C availability, truthful capability declarations,
ownership and mutation implementation remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OrderedBackendAdmission

variable {Value State : Type*}

def PermutationInvariant (encode : List Value → State) : Prop :=
  ∀ left right, left.Perm right → encode left = encode right

def Represents (encode : List Value → State) (read : State → Option Value)
    (observe : List Value → Option Value) : Prop :=
  ∀ values, read (encode values) = observe values

theorem no_unordered_fifo (encode : List Value → State) (read : State → Option Value)
    (invariant : PermutationInvariant encode) {first second : Value}
    (different : first ≠ second) : ¬ Represents encode read List.head? := by
  intro represented
  have same := invariant [first, second] [second, first] (List.Perm.swap _ _ [])
  have left := represented [first, second]
  have right := represented [second, first]
  rw [same] at left
  have equal : some first = some second := by simpa using left.symm.trans right
  exact different (Option.some.inj equal)

theorem no_unordered_lifo (encode : List Value → State) (read : State → Option Value)
    (invariant : PermutationInvariant encode) {first second : Value}
    (different : first ≠ second) : ¬ Represents encode read List.getLast? := by
  intro represented
  have same := invariant [first, second] [second, first] (List.Perm.swap _ _ [])
  have left := represented [first, second]
  have right := represented [second, first]
  rw [same] at left
  have equal : some second = some first := by simpa using left.symm.trans right
  exact different (Option.some.inj equal).symm

def bagEncode (values : List Value) : Multiset Value := values

theorem bagEncode_permutation_invariant : PermutationInvariant (bagEncode (Value := Value)) := by
  intro left right permuted
  exact Quot.sound permuted

theorem no_fifo_from_bag (read : Multiset Value → Option Value)
    {first second : Value} (different : first ≠ second) :
    ¬ Represents bagEncode read List.head? :=
  no_unordered_fifo bagEncode read bagEncode_permutation_invariant different

theorem faithful_readback_is_injective (encode : List Value → State)
    (decode : State → List Value) (faithful : ∀ values, decode (encode values) = values) :
    Function.Injective encode := by
  intro left right same
  calc
    left = decode (encode left) := (faithful left).symm
    _ = decode (encode right) := congrArg decode same
    _ = right := faithful right

inductive Kind where
  | atom
  | hash
  | queue
  | stack
  deriving DecidableEq, Repr

inductive Engine where
  | native
  | nativeCandidates
  | unordered
  deriving DecidableEq, Repr

def Kind.ordered : Kind → Bool
  | .queue | .stack => true
  | .atom | .hash => false

def Engine.orderBearing : Engine → Bool
  | .native | .nativeCandidates => true
  | .unordered => false

def accepts (kind : Kind) (engine : Engine) : Bool :=
  !kind.ordered || engine.orderBearing

theorem accepted_ordered_has_realization {kind : Kind} {engine : Engine}
    (ordered : kind.ordered = true) (accepted : accepts kind engine = true) :
    engine.orderBearing = true := by
  simpa [accepts, ordered] using accepted

theorem unordered_refuses_ordered {kind : Kind} (ordered : kind.ordered = true) :
    accepts kind .unordered = false := by simp [accepts, ordered, Engine.orderBearing]

theorem both_sequence_realizations_admit_every_kind (kind : Kind) :
    accepts kind .native = true ∧ accepts kind .nativeCandidates = true := by
  simp [accepts, Engine.orderBearing]

structure Storage (Value : Type*) where
  kind : Kind
  engine : Engine
  rows : List Value

def install (storage : Storage Value) (requested : Engine) : Bool × Storage Value :=
  if accepts storage.kind requested then (true, {storage with engine := requested})
  else (false, storage)

theorem refused_install_preserves_state (storage : Storage Value) (requested : Engine)
    (refused : accepts storage.kind requested = false) :
    install storage requested = (false, storage) := by simp [install, refused]

theorem accepted_install_preserves_kind_and_rows (storage : Storage Value) (requested : Engine)
    (accepted : accepts storage.kind requested = true) :
    (install storage requested).1 = true ∧
    (install storage requested).2.kind = storage.kind ∧
    (install storage requested).2.rows = storage.rows ∧
    (install storage requested).2.engine = requested := by simp [install, accepted]

namespace Controls

theorem same_bag_has_different_fifo :
    bagEncode ([0, 1] : List Nat) = bagEncode [1, 0] ∧
    ([0, 1] : List Nat).head? ≠ [1, 0].head? := by
  constructor
  · exact bagEncode_permutation_invariant _ _ (List.Perm.swap _ _ [])
  · decide

theorem same_bag_has_different_lifo :
    bagEncode ([0, 1] : List Nat) = bagEncode [1, 0] ∧
    ([0, 1] : List Nat).getLast? ≠ [1, 0].getLast? := by
  constructor
  · exact bagEncode_permutation_invariant _ _ (List.Perm.swap _ _ [])
  · decide

theorem refused_queue_switch_keeps_sequence :
    install (Storage.mk .queue .native ([2, 1] : List Nat)) .unordered =
      (false, Storage.mk .queue .native [2, 1]) := by rfl

theorem accepted_sequence_switch_keeps_sequence :
    install (Storage.mk .queue .native ([2, 1] : List Nat)) .nativeCandidates =
      (true, Storage.mk .queue .nativeCandidates [2, 1]) := by rfl

end Controls

end Mettapedia.Machines.OrderedBackendAdmission

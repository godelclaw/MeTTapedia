import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence.LaneSpecialization
import Mathlib.Data.List.Perm.Basic

/-!
# Storage order: what the sequence lanes observe of a store

The Prime lane observes the bag of answers (settled decision §11). The HE and PeTTa lanes keep
their atoms in a list and answer in the order of that list. This module makes that order a
stated parameter and proves `match` over it an instance of the one `transform`.

## Removal disciplines

A list store appends on `add-atom` (`appendAtom`), which as a bag adds one copy (`appendAtom_bag`). It removes an atom at a position in one of two
ways (`Discipline`): by **shifting** the rest down (`List.eraseIdx`), or by moving the **last**
atom into the freed position (`swapRemove`). The two give the same bag (`removeAt_bag`), so the
bag lane cannot tell them apart, and different lists (`Controls.swap_vs_shift`), so a sequence
lane can. A specialization under storage order therefore has to say which discipline the lane's
store uses.

## `match` in storage order is `every (read p)` read by position

An **event** of a sequence lane is an answer tagged with the position of the occurrence its row
picked (`PosEv`). The **storage-order policy** lists a bag of events by position
(`storageOrder`), so it reads a bag the way an HE or PeTTa store enumerates. The rows of the
one-row-per-match transform over the positions of a list store (`matchEach`, the form of `match`
in `Equivalence.LaneSpecialization`) give exactly the events of each position's answers
(`instEvents_eq`). With a **unitary** matcher (at most one answer per stored atom, which
syntactic unification is), reading those events in storage order is the lane's native `match`
(`storageOrder_instEvents`). For every matcher, the bag of the native `match` is Prime's `match`
over the same positions (`seqMatch_bag`). So `match` specializes the transform under the
storage-order lane (`seq_match_specializes`) and, through the bag, under the bag lane
(`StorageLane.Specializes.toBag`).

The unitary hypothesis is needed: two answers from one stored atom have the same position, and the
position does not say which comes first (`Controls.position_does_not_order_answers`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.LaneSpecializations

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence.Lanes

universe u v w

/-! ## List stores and removal disciplines -/

section Disciplines

variable {T : Type u}

/-- `add-atom` on a list store: the atom goes last. -/
def appendAtom (xs : List T) (a : T) : List T := xs ++ [a]

/-- As a bag, appending is the bag lane's `add-atom`: one more copy. -/
theorem appendAtom_bag (xs : List T) (a : T) :
    (appendAtom xs a : Multiset T) = (xs : Multiset T) + {a} := by
  unfold appendAtom
  rw [← Multiset.coe_add]
  rfl

/-- Remove the atom at a position by moving the last atom into its place. -/
def swapRemove (xs : List T) (i : ℕ) : List T :=
  match xs.getLast? with
  | none => xs
  | some z =>
      if i + 1 < xs.length then xs.dropLast.set i z
      else if i + 1 = xs.length then xs.dropLast
      else xs

/-- How a list store closes the gap left by a removal. -/
inductive Discipline where
  /-- Shift the later atoms down one position: order is kept. -/
  | shift
  /-- Move the last atom into the freed position. -/
  | swapLast
  deriving DecidableEq, Repr

/-- Remove the atom at a position under a discipline. -/
def removeAt : Discipline → List T → ℕ → List T
  | .shift, xs, i => xs.eraseIdx i
  | .swapLast, xs, i => swapRemove xs i

theorem swapRemove_perm_eraseIdx (xs : List T) (i : ℕ) : (swapRemove xs i).Perm (xs.eraseIdx i) := by
  unfold swapRemove
  cases last : xs.getLast? with
  | none =>
      have : xs = [] := List.getLast?_eq_none_iff.mp last
      subst this
      simp
  | some z =>
      have split : xs.dropLast ++ [z] = xs := List.dropLast_append_getLast? z (by simp [last])
      have len : xs.length = xs.dropLast.length + 1 := by
        conv_lhs => rw [← split]
        simp
      simp only
      split_ifs with lt eq
      · have lt' : i < xs.dropLast.length := by omega
        conv_rhs => rw [← split]
        rw [List.eraseIdx_append_of_lt_length lt']
        exact (List.set_perm_cons_eraseIdx lt' z).trans (List.perm_append_singleton _ _).symm
      · have eq' : xs.dropLast.length ≤ i := by omega
        conv_rhs => rw [← split]
        rw [List.eraseIdx_append_of_length_le eq']
        have : i - (xs.length - 1) = 0 := by omega
        simp [this]
      · rw [List.eraseIdx_of_length_le (by omega)]

/-- **The two disciplines leave the same bag.** -/
theorem removeAt_bag (d d' : Discipline) (xs : List T) (i : ℕ) :
    (removeAt d xs i : Multiset T) = (removeAt d' xs i : Multiset T) := by
  have toShift : ∀ e : Discipline, (removeAt e xs i : Multiset T) = (xs.eraseIdx i : Multiset T) := by
    intro e
    cases e with
    | shift => rfl
    | swapLast => exact Multiset.coe_eq_coe.mpr (swapRemove_perm_eraseIdx xs i)
  rw [toShift d, toShift d']

end Disciplines

/-! ## Events in storage order -/

section StorageOrder

variable {T : Type u} [LinearOrder T]

/-- An event of a sequence lane: an answer with the position of the occurrence its row picked. -/
abbrev PosEv (T : Type u) := Lex (ℕ × T)

/-- **The storage-order policy**: list a bag of events by position. The order on answers breaks
ties only, and there are none when every position contributes at most one event. -/
def storageOrder (b : Multiset (PosEv T)) : List T := (b.sort (· ≤ ·)).map fun e => (ofLex e).2

/-- Events listed position by position from per-position answer lists. -/
def blockEvents (answersAt : ℕ → List T) (n : ℕ) : List (PosEv T) :=
  (List.range n).flatMap fun o => (answersAt o).map fun t => toLex (o, t)

theorem blockEvents_sorted {answersAt : ℕ → List T} (short : ∀ o, (answersAt o).length ≤ 1)
    (n : ℕ) : (blockEvents answersAt n).Pairwise (· ≤ ·) := by
  unfold blockEvents
  rw [List.pairwise_flatMap]
  refine ⟨fun o _ => ?_, ?_⟩
  · have := short o
    cases h : answersAt o with
    | nil => simp
    | cons t rest =>
        cases rest with
        | nil => simp
        | cons _ _ => rw [h] at this; simp at this
  · refine (List.pairwise_lt_range).imp fun {a b} lt => ?_
    intro x xIn y yIn
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp xIn
    obtain ⟨t', -, rfl⟩ := List.mem_map.mp yIn
    exact le_of_lt (Prod.Lex.lt_iff.mpr (Or.inl (by simpa using lt)))

theorem storageOrder_blockEvents {answersAt : ℕ → List T} (short : ∀ o, (answersAt o).length ≤ 1)
    (n : ℕ) :
    storageOrder (blockEvents answersAt n : Multiset (PosEv T)) =
      (List.range n).flatMap answersAt := by
  unfold storageOrder
  rw [Multiset.coe_sort, List.mergeSort_eq_self _ (by simpa using blockEvents_sorted short n)]
  unfold blockEvents
  rw [List.map_flatMap]
  congr 1
  funext o
  simp [List.map_map, Function.comp_def]

end StorageOrder

/-! ## `match` over a list store -/

section MatchInstance

variable {V : Type u} {T : Type v} {P : Type w} [LinearOrder T] [Inhabited T]
  (L : TermLayer V T P) (m : Matcher V T P)

/-- The answers one stored atom gives: the template atom under each matcher answer, in the
matcher's order. -/
def answersOf (p tp : P) (a : T) : List T := (m p (fun _ => none) a).filterMap fun τ => L.inst τ tp

/-- **The sequence lanes' native `match`**: the stored atoms in storage order, each with its
answers in the matcher's order. -/
def seqMatch (xs : List T) (p tp : P) : List T := xs.flatMap (answersOf L m p tp)

/-- The label at a position of a list store. -/
def posLabel (xs : List T) (o : ℕ) : T := xs.getD o default

/-- The events of a row of `match`: its kept position, with each label it makes. -/
def rowEvents : Subst V T × List (Pick ℕ T) → Multiset (PosEv T)
  | (_, [Pick.keep o, Pick.make ls]) => ls.map fun t => toLex (o, t)
  | _ => 0

/-- **The events of the transform** `matchEach p [tp]` over the positions of a list store. -/
def instEvents (xs : List T) (p tp : P) : Multiset (PosEv T) :=
  ((matchEach p [tp]).rows L m (posLabel xs) (Finset.range xs.length)).bind rowEvents

omit [LinearOrder T] [Inhabited T] in
theorem filterMap_eq_flatMap_toList {α β : Type*} (f : α → Option β) (l : List α) :
    l.filterMap f = l.flatMap fun a => (f a).toList := by
  induction l with
  | nil => rfl
  | cons a rest ih => cases h : f a <;> simp [h, ih]

omit [LinearOrder T] [Inhabited T] in
theorem readRows_rowEvents (tp : P) (o : ℕ) (τ : Subst V T) :
    (readRows (O := ℕ) L [tp] o τ).bind rowEvents =
      (((L.inst τ tp).toList.map fun t => toLex (o, t) : List (PosEv T)) : Multiset (PosEv T)) := by
  unfold readRows instTemplate
  cases h : L.inst τ tp <;> simp [h, rowEvents]

omit [LinearOrder T] in
/-- **The transform's events are each position's answers, tagged with the position.** -/
theorem instEvents_eq (xs : List T) (p tp : P) :
    instEvents L m xs p tp =
      (blockEvents (fun o => answersOf L m p tp (posLabel xs o)) xs.length : Multiset (PosEv T)) := by
  unfold instEvents Transform.rows matchEach
  simp only
  rw [rows_read, Multiset.bind_assoc]
  have each : ∀ o, ((↑(m p (fun _ => none) (posLabel xs o)) : Multiset (Subst V T)).bind
      (readRows (O := ℕ) L [tp] o)).bind rowEvents =
      (((answersOf L m p tp (posLabel xs o)).map fun t => toLex (o, t) : List (PosEv T)) :
        Multiset (PosEv T)) := by
    intro o
    rw [Multiset.bind_assoc]
    simp only [readRows_rowEvents]
    rw [Multiset.coe_bind]
    congr 1
    unfold answersOf
    rw [filterMap_eq_flatMap_toList, List.map_flatMap]
  simp only [each]
  unfold blockEvents
  rw [Finset.range_val, Multiset.range, Multiset.coe_bind]

omit [LinearOrder T] in
theorem flatMap_range_posLabel {β : Type*} (f : T → List β) (xs : List T) :
    (List.range xs.length).flatMap (fun o => f (posLabel xs o)) = xs.flatMap f := by
  have same : (List.range xs.length).map (posLabel xs) = xs := by
    refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
    simp [posLabel, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂]
  conv_rhs => rw [← same]
  rw [List.flatMap_map]

omit [LinearOrder T] [Inhabited T] in
theorem answersOf_short (unitary : Matcher.Unitary m) (p tp : P) (a : T) :
    (answersOf L m p tp a).length ≤ 1 :=
  (List.length_filterMap_le _ _).trans (unitary p _ a)

/-- **In storage order, the transform's events are the native `match`**, for a unitary matcher. -/
theorem storageOrder_instEvents (unitary : Matcher.Unitary m) (xs : List T) (p tp : P) :
    storageOrder (instEvents L m xs p tp) = seqMatch L m xs p tp := by
  rw [instEvents_eq, storageOrder_blockEvents (fun o => answersOf_short L m unitary p tp _),
    flatMap_range_posLabel]
  rfl

omit [LinearOrder T] in
/-- **As a bag, the native `match` of a list store is Prime's `match`** over its positions, for
every matcher. -/
theorem seqMatch_bag (xs : List T) (p tp : P) :
    (seqMatch L m xs p tp : Multiset T) =
      primeMatch L m (posLabel xs) (Finset.range xs.length) p [tp] := by
  have each : ∀ o, (↑(m p (fun _ => none) (posLabel xs o)) : Multiset (Subst V T)).bind
      (instBag L [tp]) = (answersOf L m p tp (posLabel xs o) : Multiset T) := by
    intro o
    have inst : ∀ τ, instBag L [tp] τ = (((L.inst τ tp).toList : List T) : Multiset T) := by
      intro τ
      unfold instBag instTemplate
      cases h : L.inst τ tp <;> simp [h]
    simp only [inst]
    rw [Multiset.coe_bind]
    unfold answersOf
    rw [filterMap_eq_flatMap_toList]
  unfold primeMatch seqMatch
  simp only [each]
  rw [Finset.range_val, Multiset.range, Multiset.coe_bind, flatMap_range_posLabel]

/-- **A storage-order lane** (HE, PeTTa): it reads the bag of events by position and observes the
whole list. -/
def storageLane (Ctx : Type*) : Lane Ctx (PosEv T) (List T) (List T) := ⟨fun _ b => storageOrder b, id⟩

/-- **`match` specializes the transform under the storage-order lane**, for a unitary matcher. -/
theorem seq_match_specializes (unitary : Matcher.Unitary m) (p tp : P) :
    (storageLane (T := T) (List T)).Specializes (fun xs => seqMatch L m xs p tp)
      (fun xs => instEvents L m xs p tp) :=
  fun xs => (storageOrder_instEvents L m unitary xs p tp).symm

variable {L m}

omit [Inhabited T] in
/-- The bag of a storage-ordered list of events is the bag of their answers. -/
theorem storageOrder_bag (b : Multiset (PosEv T)) :
    (storageOrder b : Multiset T) = b.map fun e => (ofLex e).2 := by
  unfold storageOrder
  rw [← Multiset.map_coe, Multiset.sort_eq]

omit [Inhabited T] in
/-- **A storage-order specialization gives a bag specialization.** -/
theorem StorageLane.Specializes.toBag {Ctx : Type*} {native : Ctx → List T}
    {inst : Ctx → Multiset (PosEv T)} (h : (storageLane (T := T) Ctx).Specializes native inst) :
    (bagLane Ctx T).Specializes (asBag native) fun ctx => (inst ctx).map fun e => (ofLex e).2 := by
  intro ctx
  have := congrArg (fun l : List T => (l : Multiset T)) (h ctx)
  simp only [storageLane, id] at this
  rw [storageOrder_bag] at this
  exact this

end MatchInstance

/-! ## Controls -/

namespace Controls

/-- **Same bag, different lists**: removing the second of four atoms. -/
theorem swap_vs_shift :
    removeAt .swapLast [0, 1, 2, 3] 1 = [0, 3, 2] ∧ removeAt .shift [0, 1, 2, 3] 1 = [0, 2, 3] ∧
      (removeAt .swapLast [0, 1, 2, 3] 1 : Multiset ℕ) = (removeAt .shift [0, 1, 2, 3] 1 : Multiset ℕ) :=
  ⟨by decide, by decide, removeAt_bag _ _ _ _⟩

/-- **The position does not order the answers of one stored atom.** Two answers at position 0,
listed by the matcher as `2` then `1`, are read by storage order as `1` then `2`: when one stored
atom has two answers, storage order says nothing about their order. -/
theorem position_does_not_order_answers :
    storageOrder ((([toLex (0, 2), toLex (0, 1)] : List (PosEv ℕ))) : Multiset (PosEv ℕ)) = [1, 2] ∧
      ([2, 1] : List ℕ) ≠ [1, 2] := by
  refine ⟨?_, by decide⟩
  have perm : ((([toLex (0, 2), toLex (0, 1)] : List (PosEv ℕ))) : Multiset (PosEv ℕ)) =
      (([toLex (0, 1), toLex (0, 2)] : List (PosEv ℕ)) : Multiset (PosEv ℕ)) :=
    Multiset.coe_eq_coe.mpr (List.Perm.swap _ _ _)
  rw [perm]
  unfold storageOrder
  rw [Multiset.coe_sort, List.mergeSort_eq_self]
  · rfl
  · rw [List.pairwise_pair]
    exact Prod.Lex.le_iff.mpr (Or.inr ⟨rfl, by decide⟩)

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.LaneSpecializations

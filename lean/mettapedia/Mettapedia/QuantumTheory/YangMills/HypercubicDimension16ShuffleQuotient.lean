import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16LocalWordCarrier
import Mathlib.Data.Vector.Basic

/-!
# Semantic quotient of global derivative shuffles

A global derivative word interleaves the ordered derivative axes belonging to
different field factors.  The local-word data retain, for each field owner,
the corresponding axis subword in its original order.  This module proves
that the resulting semantic quotient is exactly the family of local words:
the localization map is surjective, and concatenation in field-label order is
a right inverse.

An adjacent interchange of entries with different owners preserves every
local subword.  Conversely, a head-matching induction proves that any two
global words with the same owner-local subwords are connected by such
literal adjacent interchanges.  Hence the equivalence closure of the sparse
shuffle generators is exactly the semantic kernel; no counting surrogate is
used in this identification.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16ShuffleQuotient

open V14HypercubicFDCensus
open HypercubicDimension16AlphaReduction
open HypercubicDimension16RelationEquivariance
open HypercubicRawFDDimension16Census

abbrev OwnedAxis (fieldCount : ℕ) := Fin fieldCount × Axis

/-- A fixed-length global owner--axis word. -/
abbrev GlobalOwnedAxisWord (fieldCount derivativeCount : ℕ) :=
  List.Vector (OwnedAxis fieldCount) derivativeCount

/-- One ordered axis list per field owner, with prescribed total length. -/
abbrev LocalAxisWordFamily (fieldCount derivativeCount : ℕ) :=
  { words : Fin fieldCount → List Axis //
    ∑ owner, (words owner).length = derivativeCount }

/-! ## Localization and its exact right inverse -/

/-- Stable projection of a tagged global list to one owner's axis subword. -/
def ownerAxisProjection {fieldCount : ℕ} (owner : Fin fieldCount) :
    List (OwnedAxis fieldCount) → List Axis
  | [] => []
  | entry :: rest =>
      if entry.1 = owner then
        entry.2 :: ownerAxisProjection owner rest
      else
        ownerAxisProjection owner rest

@[simp] theorem ownerAxisProjection_nil
    {fieldCount : ℕ} (owner : Fin fieldCount) :
    ownerAxisProjection owner [] = [] :=
  rfl

@[simp] theorem ownerAxisProjection_cons
    {fieldCount : ℕ} (owner : Fin fieldCount)
    (entry : OwnedAxis fieldCount) (rest : List (OwnedAxis fieldCount)) :
    ownerAxisProjection owner (entry :: rest) =
      if entry.1 = owner then
        entry.2 :: ownerAxisProjection owner rest
      else ownerAxisProjection owner rest :=
  rfl

@[simp] theorem ownerAxisProjection_append
    {fieldCount : ℕ} (owner : Fin fieldCount)
    (left right : List (OwnedAxis fieldCount)) :
    ownerAxisProjection owner (left ++ right) =
      ownerAxisProjection owner left ++ ownerAxisProjection owner right := by
  induction left with
  | nil => rfl
  | cons entry rest ih =>
      simp only [List.cons_append, ownerAxisProjection_cons, ih]
      split <;> rfl

theorem sum_ownerAxisProjection_length
    {fieldCount : ℕ} (entries : List (OwnedAxis fieldCount)) :
    (∑ owner, (ownerAxisProjection owner entries).length) =
      entries.length := by
  classical
  induction entries with
  | nil => simp
  | cons entry rest ih =>
      calc
        (∑ owner,
            (ownerAxisProjection owner (entry :: rest)).length) =
            ∑ owner,
              ((if entry.1 = owner then 1 else 0) +
                (ownerAxisProjection owner rest).length) := by
              apply Finset.sum_congr rfl
              intro owner _
              by_cases howner : entry.1 = owner <;>
                simp [ownerAxisProjection, howner, Nat.add_comm]
        _ = (∑ owner, if entry.1 = owner then 1 else 0) +
              ∑ owner, (ownerAxisProjection owner rest).length := by
              rw [Finset.sum_add_distrib]
        _ = 1 + ∑ owner, (ownerAxisProjection owner rest).length := by
              simp
        _ = (entry :: rest).length := by
              simp [ih, Nat.add_comm]

/-- Forget only the interleaving between different owners. -/
def localize {fieldCount derivativeCount : ℕ}
    (word : GlobalOwnedAxisWord fieldCount derivativeCount) :
    LocalAxisWordFamily fieldCount derivativeCount :=
  ⟨fun owner => ownerAxisProjection owner word.toList, by
    rw [sum_ownerAxisProjection_length, word.toList_length]⟩

/-- Concatenate the local words in increasing field-label order. -/
def concatenateOwnerWords :
    (fieldCount : ℕ) →
      (Fin fieldCount → List Axis) → List (OwnedAxis fieldCount)
  | 0, _ => []
  | fieldCount + 1, words =>
      (words 0).map (fun axis => (0, axis)) ++
        (concatenateOwnerWords fieldCount (fun owner => words owner.succ)).map
          (fun entry => (entry.1.succ, entry.2))

theorem length_concatenateOwnerWords :
    ∀ {fieldCount : ℕ} (words : Fin fieldCount → List Axis),
      (concatenateOwnerWords fieldCount words).length =
        ∑ owner, (words owner).length := by
  intro fieldCount
  induction fieldCount with
  | zero =>
      intro words
      simp [concatenateOwnerWords]
  | succ fieldCount ih =>
      intro words
      simp only [concatenateOwnerWords, List.length_append, List.length_map,
        Fin.sum_univ_succ]
      rw [ih]

@[simp] theorem ownerAxisProjection_zero_tagZero
    {fieldCount : ℕ} (axes : List Axis) :
    ownerAxisProjection (0 : Fin (fieldCount + 1))
      (axes.map (fun axis => ((0 : Fin (fieldCount + 1)), axis))) = axes := by
  induction axes with
  | nil => rfl
  | cons axis axes ih =>
      simp [ih]

@[simp] theorem ownerAxisProjection_succ_tagZero
    {fieldCount : ℕ} (target : Fin fieldCount) (axes : List Axis) :
    ownerAxisProjection target.succ
      (axes.map (fun axis => ((0 : Fin (fieldCount + 1)), axis))) = [] := by
  induction axes with
  | nil => rfl
  | cons axis axes ih =>
      have hne : (0 : Fin (fieldCount + 1)) ≠ target.succ := by
        exact (Fin.succ_ne_zero target).symm
      simp [hne, ih]

@[simp] theorem ownerAxisProjection_zero_liftSucc
    {fieldCount : ℕ} (entries : List (OwnedAxis fieldCount)) :
    ownerAxisProjection (0 : Fin (fieldCount + 1))
      (entries.map (fun entry => (entry.1.succ, entry.2))) = [] := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      simp [ih]

@[simp] theorem ownerAxisProjection_succ_liftSucc
    {fieldCount : ℕ} (target : Fin fieldCount)
    (entries : List (OwnedAxis fieldCount)) :
    ownerAxisProjection target.succ
      (entries.map (fun entry => (entry.1.succ, entry.2))) =
        ownerAxisProjection target entries := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      simp only [List.map_cons, ownerAxisProjection_cons, Fin.succ_inj]
      split <;> simp_all

theorem ownerAxisProjection_concatenateOwnerWords :
    ∀ {fieldCount : ℕ} (words : Fin fieldCount → List Axis)
      (owner : Fin fieldCount),
      ownerAxisProjection owner
        (concatenateOwnerWords fieldCount words) = words owner := by
  intro fieldCount
  induction fieldCount with
  | zero =>
      intro words owner
      exact Fin.elim0 owner
  | succ fieldCount ih =>
      intro words owner
      cases owner using Fin.cases with
      | zero =>
          simp [concatenateOwnerWords]
      | succ owner =>
          simp [concatenateOwnerWords, ih]

/-- Canonical global representative obtained by owner-by-owner
concatenation. -/
def globalize {fieldCount derivativeCount : ℕ}
    (family : LocalAxisWordFamily fieldCount derivativeCount) :
    GlobalOwnedAxisWord fieldCount derivativeCount :=
  ⟨concatenateOwnerWords fieldCount family.1, by
    rw [length_concatenateOwnerWords, family.2]⟩

theorem localize_globalize {fieldCount derivativeCount : ℕ}
    (family : LocalAxisWordFamily fieldCount derivativeCount) :
    localize (globalize family) = family := by
  apply Subtype.ext
  funext owner
  exact ownerAxisProjection_concatenateOwnerWords family.1 owner

theorem localize_surjective {fieldCount derivativeCount : ℕ} :
    Function.Surjective
      (localize : GlobalOwnedAxisWord fieldCount derivativeCount →
        LocalAxisWordFamily fieldCount derivativeCount) := by
  intro family
  exact ⟨globalize family, localize_globalize family⟩

/-! ## Hypercubic and field-relabel equivariance -/

def GlobalOwnedAxisWord.hypercubicAct (h : Hypercubic4)
    {fieldCount derivativeCount : ℕ}
    (word : GlobalOwnedAxisWord fieldCount derivativeCount) :
    GlobalOwnedAxisWord fieldCount derivativeCount :=
  ⟨word.toList.map (fun entry => (entry.1, h.perm entry.2)), by
    simp [word.toList_length]⟩

def LocalAxisWordFamily.hypercubicAct (h : Hypercubic4)
    {fieldCount derivativeCount : ℕ}
    (family : LocalAxisWordFamily fieldCount derivativeCount) :
    LocalAxisWordFamily fieldCount derivativeCount :=
  ⟨fun owner => (family.1 owner).map h.perm, by
    simpa using family.2⟩

theorem ownerAxisProjection_map_hypercubic
    {fieldCount : ℕ} (h : Hypercubic4) (owner : Fin fieldCount)
    (entries : List (OwnedAxis fieldCount)) :
    ownerAxisProjection owner
        (entries.map (fun entry => (entry.1, h.perm entry.2))) =
      (ownerAxisProjection owner entries).map h.perm := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      simp only [List.map_cons, ownerAxisProjection_cons, ih]
      split <;> rfl

theorem localize_hypercubicAct
    {fieldCount derivativeCount : ℕ} (h : Hypercubic4)
    (word : GlobalOwnedAxisWord fieldCount derivativeCount) :
    localize (word.hypercubicAct h) =
      (localize word).hypercubicAct h := by
  apply Subtype.ext
  funext owner
  exact ownerAxisProjection_map_hypercubic h owner word.toList

def GlobalOwnedAxisWord.relabel
    {fieldCount derivativeCount : ℕ}
    (rename : Equiv.Perm (Fin fieldCount))
    (word : GlobalOwnedAxisWord fieldCount derivativeCount) :
    GlobalOwnedAxisWord fieldCount derivativeCount :=
  ⟨word.toList.map (fun entry => (rename entry.1, entry.2)), by
    simp [word.toList_length]⟩

def LocalAxisWordFamily.relabel
    {fieldCount derivativeCount : ℕ}
    (rename : Equiv.Perm (Fin fieldCount))
    (family : LocalAxisWordFamily fieldCount derivativeCount) :
    LocalAxisWordFamily fieldCount derivativeCount :=
  ⟨fun owner => family.1 (rename.symm owner), by
    exact (Equiv.sum_comp rename.symm
      (fun owner => (family.1 owner).length)).trans family.2⟩

theorem ownerAxisProjection_map_relabel
    {fieldCount : ℕ} (rename : Equiv.Perm (Fin fieldCount))
    (owner : Fin fieldCount) (entries : List (OwnedAxis fieldCount)) :
    ownerAxisProjection owner
        (entries.map (fun entry => (rename entry.1, entry.2))) =
      ownerAxisProjection (rename.symm owner) entries := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      simp only [List.map_cons, ownerAxisProjection_cons, ih]
      by_cases howner : entry.1 = rename.symm owner
      · simp [howner]
      · have hrenamed : rename entry.1 ≠ owner := by
          intro h
          apply howner
          simpa using congrArg rename.symm h
        simp [howner, hrenamed]

theorem localize_relabel
    {fieldCount derivativeCount : ℕ}
    (rename : Equiv.Perm (Fin fieldCount))
    (word : GlobalOwnedAxisWord fieldCount derivativeCount) :
    localize (word.relabel rename) = (localize word).relabel rename := by
  apply Subtype.ext
  funext owner
  exact ownerAxisProjection_map_relabel rename owner word.toList

theorem hypercubicAct_relabel_commute
    {fieldCount derivativeCount : ℕ} (h : Hypercubic4)
    (rename : Equiv.Perm (Fin fieldCount))
    (word : GlobalOwnedAxisWord fieldCount derivativeCount) :
    (word.relabel rename).hypercubicAct h =
      (word.hypercubicAct h).relabel rename := by
  apply List.Vector.eq
  simp [GlobalOwnedAxisWord.relabel, GlobalOwnedAxisWord.hypercubicAct,
    List.map_map]

/-! ## Finite dependent presentation of the local lists -/

structure LocalDerivativeLetter (derivativeBudget : ℕ) where
  derivativeCount : Fin (derivativeBudget + 1)
  derivativeAxis : Fin derivativeCount.1 → Axis
deriving DecidableEq, Fintype

@[ext] theorem LocalDerivativeLetter.ext
    {derivativeBudget : ℕ}
    (left right : LocalDerivativeLetter derivativeBudget)
    (hcount : left.derivativeCount = right.derivativeCount)
    (haxis : HEq left.derivativeAxis right.derivativeAxis) :
    left = right := by
  cases left
  cases right
  simp_all

abbrev LocalDerivativeWordFamily (fieldCount derivativeCount : ℕ) :=
  { letters : Fin fieldCount → LocalDerivativeLetter derivativeCount //
    ∑ owner, (letters owner).derivativeCount.1 = derivativeCount }

def localDerivativeLetterToList {derivativeBudget : ℕ}
    (letter : LocalDerivativeLetter derivativeBudget) :
    { axes : List Axis // axes.length ≤ derivativeBudget } :=
  ⟨List.ofFn letter.derivativeAxis, by
    simp
    exact Nat.le_of_lt_succ letter.derivativeCount.2⟩

def localDerivativeLetterOfList {derivativeBudget : ℕ}
    (axes : { axes : List Axis // axes.length ≤ derivativeBudget }) :
    LocalDerivativeLetter derivativeBudget where
  derivativeCount := ⟨axes.1.length, Nat.lt_succ_of_le axes.2⟩
  derivativeAxis := axes.1.get

def localDerivativeLetterEquivList (derivativeBudget : ℕ) :
    LocalDerivativeLetter derivativeBudget ≃
      { axes : List Axis // axes.length ≤ derivativeBudget } where
  toFun := localDerivativeLetterToList
  invFun := localDerivativeLetterOfList
  left_inv letter := by
    rcases letter with ⟨count, axes⟩
    apply LocalDerivativeLetter.ext
    · apply Fin.ext
      simp [localDerivativeLetterToList, localDerivativeLetterOfList]
    · apply (Fin.heq_fun_iff (by
        change (List.ofFn axes).length = count.1
        simp)).2
      intro position
      simp [localDerivativeLetterOfList, localDerivativeLetterToList]
  right_inv axes := by
    apply Subtype.ext
    exact List.ofFn_get axes.1

theorem localAxisWord_length_le {fieldCount derivativeCount : ℕ}
    (family : LocalAxisWordFamily fieldCount derivativeCount)
    (owner : Fin fieldCount) :
    (family.1 owner).length ≤ derivativeCount := by
  calc
    (family.1 owner).length ≤
        ∑ index, (family.1 index).length := by
      exact Finset.single_le_sum
        (s := Finset.univ)
        (f := fun index => (family.1 index).length)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ owner)
    _ = derivativeCount := family.2

def localAxisWordFamilyEquivDerivativeFamily
    (fieldCount derivativeCount : ℕ) :
    LocalAxisWordFamily fieldCount derivativeCount ≃
      LocalDerivativeWordFamily fieldCount derivativeCount where
  toFun family :=
    ⟨fun owner => localDerivativeLetterOfList
        ⟨family.1 owner, localAxisWord_length_le family owner⟩, by
      simpa [localDerivativeLetterOfList] using family.2⟩
  invFun family :=
    ⟨fun owner =>
        (localDerivativeLetterEquivList derivativeCount
          (family.1 owner)).1, by
      simpa [localDerivativeLetterEquivList,
        localDerivativeLetterToList] using family.2⟩
  left_inv family := by
    apply Subtype.ext
    funext owner
    change (localDerivativeLetterToList
      (localDerivativeLetterOfList
        ⟨family.1 owner, localAxisWord_length_le family owner⟩)).1 =
      family.1 owner
    exact congrArg Subtype.val
      ((localDerivativeLetterEquivList derivativeCount).apply_symm_apply
        ⟨family.1 owner, localAxisWord_length_le family owner⟩)
  right_inv family := by
    apply Subtype.ext
    funext owner
    exact (localDerivativeLetterEquivList derivativeCount).symm_apply_apply
      (family.1 owner)

noncomputable instance localAxisWordFamilyFintype
    (fieldCount derivativeCount : ℕ) :
    Fintype (LocalAxisWordFamily fieldCount derivativeCount) :=
  Fintype.ofEquiv (LocalDerivativeWordFamily fieldCount derivativeCount)
    (localAxisWordFamilyEquivDerivativeFamily fieldCount derivativeCount).symm

/-! ## The exact semantic quotient -/

def SemanticShuffleEquivalent {fieldCount derivativeCount : ℕ}
    (left right : GlobalOwnedAxisWord fieldCount derivativeCount) : Prop :=
  localize left = localize right

instance semanticShuffleSetoid (fieldCount derivativeCount : ℕ) :
    Setoid (GlobalOwnedAxisWord fieldCount derivativeCount) where
  r := SemanticShuffleEquivalent
  iseqv := by
    constructor
    · intro word
      rfl
    · intro left right h
      exact h.symm
    · intro left middle right hlm hmr
      exact hlm.trans hmr

abbrev SemanticShuffleQuotient (fieldCount derivativeCount : ℕ) :=
  Quotient (semanticShuffleSetoid fieldCount derivativeCount)

def semanticShuffleQuotientEquivLocal
    (fieldCount derivativeCount : ℕ) :
    SemanticShuffleQuotient fieldCount derivativeCount ≃
      LocalAxisWordFamily fieldCount derivativeCount where
  toFun := Quotient.lift localize (by
    intro left right h
    exact h)
  invFun family := Quotient.mk _ (globalize family)
  left_inv quotient := by
    refine Quotient.inductionOn quotient ?_
    intro word
    apply Quotient.sound
    change localize (globalize (localize word)) = localize word
    exact localize_globalize (localize word)
  right_inv := localize_globalize

noncomputable instance semanticShuffleQuotientFintype
    (fieldCount derivativeCount : ℕ) :
    Fintype (SemanticShuffleQuotient fieldCount derivativeCount) :=
  Fintype.ofEquiv (LocalAxisWordFamily fieldCount derivativeCount)
    (semanticShuffleQuotientEquivLocal fieldCount derivativeCount).symm

def oneOwnerLocalAxisWordEquivVector (derivativeCount : ℕ) :
    LocalAxisWordFamily 1 derivativeCount ≃
      List.Vector Axis derivativeCount where
  toFun family :=
    ⟨family.1 0, by
      simpa [Fin.sum_univ_succ] using family.2⟩
  invFun word :=
    ⟨fun _ => word.toList, by
      simp [word.toList_length]⟩
  left_inv family := by
    apply Subtype.ext
    funext owner
    fin_cases owner
    rfl
  right_inv word := by
    apply List.Vector.eq
    rfl

def oneOwnerLocalAxisWordEquiv (derivativeCount : ℕ) :
    LocalAxisWordFamily 1 derivativeCount ≃ (Fin derivativeCount → Axis) :=
  (oneOwnerLocalAxisWordEquivVector derivativeCount).trans
    (Equiv.vectorEquivFin Axis derivativeCount)

theorem card_oneOwnerLocalAxisWordFamily (derivativeCount : ℕ) :
    Fintype.card (LocalAxisWordFamily 1 derivativeCount) =
      4 ^ derivativeCount := by
  rw [Fintype.card_congr (oneOwnerLocalAxisWordEquiv derivativeCount),
    Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

theorem card_oneOwnerSemanticShuffleQuotient (derivativeCount : ℕ) :
    Fintype.card (SemanticShuffleQuotient 1 derivativeCount) =
      4 ^ derivativeCount := by
  rw [Fintype.card_congr
    (semanticShuffleQuotientEquivLocal 1 derivativeCount),
    card_oneOwnerLocalAxisWordFamily]

/-! ## Every literal adjacent different-owner swap is sound -/

def IsAdjacentDifferentOwnerSwap {fieldCount derivativeCount : ℕ}
    (left right : GlobalOwnedAxisWord fieldCount derivativeCount) : Prop :=
  ∃ (headEntries tailEntries : List (OwnedAxis fieldCount))
      (first second : OwnedAxis fieldCount),
    first.1 ≠ second.1 ∧
    left.toList = headEntries ++ first :: second :: tailEntries ∧
    right.toList = headEntries ++ second :: first :: tailEntries

theorem list_eq_take_two_drop {α : Type*} (entries : List α)
    (index : ℕ) (hnext : index + 1 < entries.length) :
    entries = entries.take index ++
      entries[index] :: entries[index + 1] :: entries.drop (index + 2) := by
  have hfirst : index < entries.length := by omega
  have hsecond : index + 1 < entries.length := hnext
  calc
    entries = entries.take (index + 2) ++ entries.drop (index + 2) :=
      (List.take_append_drop (index + 2) entries).symm
    _ = entries.take index ++
        entries[index] :: entries[index + 1] ::
          entries.drop (index + 2) := by
      rw [show index + 2 = (index + 1) + 1 by omega,
        List.take_succ_eq_append_getElem hsecond,
        List.take_succ_eq_append_getElem hfirst]
      simp

theorem list_ofFn_adjacent_swap {α : Type*} {count : ℕ}
    (entries : Fin count → α) (index : ℕ)
    (hnext : index + 1 < count) :
    List.ofFn (entries ∘ Equiv.swap
        (⟨index, by omega⟩ : Fin count)
        (⟨index + 1, hnext⟩ : Fin count)) =
      (List.ofFn entries).take index ++
        entries ⟨index + 1, hnext⟩ ::
          entries ⟨index, by omega⟩ ::
            (List.ofFn entries).drop (index + 2) := by
  apply List.ext_getElem
  · simp [List.length_take, List.length_drop]
    omega
  · intro position hleft hright
    simp only [List.getElem_ofFn, Function.comp_apply]
    by_cases hbefore : position < index
    · rw [List.getElem_append_left]
      · rw [List.getElem_take, List.getElem_ofFn]
        have hneFirst :
            (⟨position, by simpa using hleft⟩ : Fin count) ≠
              ⟨index, by omega⟩ := by
          intro heq
          have hval : position = index := by
            simpa using congrArg Fin.val heq
          omega
        have hneSecond :
            (⟨position, by simpa using hleft⟩ : Fin count) ≠
              ⟨index + 1, hnext⟩ := by
          intro heq
          have hval : position = index + 1 := by
            simpa using congrArg Fin.val heq
          omega
        rw [Equiv.swap_apply_of_ne_of_ne hneFirst hneSecond]
      · simp [List.length_take]
        omega
    · by_cases hatFirst : position = index
      · subst position
        have hindexLe : index ≤ count := by omega
        simp [List.length_take, Nat.min_eq_left hindexLe,
          Equiv.swap_apply_left]
      · by_cases hatSecond : position = index + 1
        · subst position
          have hindexLe : index ≤ count := by omega
          simp [List.length_take, Nat.min_eq_left hindexLe,
            Equiv.swap_apply_right]
        · rw [List.getElem_append_right]
          · have hindexLe : index ≤ count := by omega
            have htake :
                (List.take index (List.ofFn entries)).length = index := by
              simp [List.length_take, Nat.min_eq_left hindexLe]
            simp only [htake]
            have hoffset :
                position - index = position - (index + 2) + 2 := by
              omega
            simp only [hoffset]
            simp only [List.getElem_cons_succ, List.getElem_drop,
              List.getElem_ofFn]
            have hneFirst :
                (⟨position, by simpa using hleft⟩ : Fin count) ≠
                  ⟨index, by omega⟩ := by
              intro heq
              have hval : position = index := by
                simpa using congrArg Fin.val heq
              omega
            have hneSecond :
                (⟨position, by simpa using hleft⟩ : Fin count) ≠
                  ⟨index + 1, hnext⟩ := by
              intro heq
              have hval : position = index + 1 := by
                simpa using congrArg Fin.val heq
              omega
            rw [Equiv.swap_apply_of_ne_of_ne hneFirst hneSecond]
            congr 2
            omega
          · simp [List.length_take]
            omega

theorem orderedAdjacentSwap_isAdjacentDifferentOwnerSwap
    {fieldCount derivativeCount : ℕ}
    (word : GlobalOwnedAxisWord fieldCount derivativeCount)
    (left right : Fin derivativeCount)
    (hadjacent : left.1 + 1 = right.1)
    (hdifferent : (word.get left).1 ≠ (word.get right).1) :
    IsAdjacentDifferentOwnerSwap word
      (List.Vector.ofFn (word.get ∘ Equiv.swap left right)) := by
  have hnext : left.1 + 1 < derivativeCount := by
    rw [hadjacent]
    exact right.2
  refine ⟨word.toList.take left.1, word.toList.drop (left.1 + 2),
    word.get left, word.get right, hdifferent, ?_, ?_⟩
  · have hdecomposition :=
      list_eq_take_two_drop word.toList left.1 (by
        simpa [word.toList_length] using hnext)
    simpa [List.Vector.get_eq_get_toList, hadjacent] using hdecomposition
  · rw [List.Vector.toList_ofFn]
    have hswap := list_ofFn_adjacent_swap word.get left.1 hnext
    have hget : List.ofFn word.get = word.toList := by
      have hvector := congrArg List.Vector.toList
        (List.Vector.ofFn_get word)
      simpa only [List.Vector.toList_ofFn] using hvector
    rw [hget] at hswap
    simpa [hadjacent] using hswap

theorem adjacentSwap_isAdjacentDifferentOwnerSwap
    {fieldCount derivativeCount : ℕ}
    (word : GlobalOwnedAxisWord fieldCount derivativeCount)
    (left right : Fin derivativeCount)
    (hadjacent : left.1 + 1 = right.1 ∨ right.1 + 1 = left.1)
    (hdifferent : (word.get left).1 ≠ (word.get right).1) :
    IsAdjacentDifferentOwnerSwap word
      (List.Vector.ofFn (word.get ∘ Equiv.swap left right)) := by
  rcases hadjacent with hadjacent | hadjacent
  · exact orderedAdjacentSwap_isAdjacentDifferentOwnerSwap word left right
      hadjacent hdifferent
  · have hswap := orderedAdjacentSwap_isAdjacentDifferentOwnerSwap
      word right left hadjacent hdifferent.symm
    simpa [Equiv.swap_comm] using hswap

theorem ownerAxisProjection_swap_different
    {fieldCount : ℕ} (owner : Fin fieldCount)
    (first second : OwnedAxis fieldCount)
    (hdifferent : first.1 ≠ second.1)
    (suffix : List (OwnedAxis fieldCount)) :
    ownerAxisProjection owner (first :: second :: suffix) =
      ownerAxisProjection owner (second :: first :: suffix) := by
  by_cases hfirst : first.1 = owner
  · have hsecond : second.1 ≠ owner := by
      intro h
      exact hdifferent (hfirst.trans h.symm)
    simp [ownerAxisProjection, hfirst, hsecond]
  · by_cases hsecond : second.1 = owner
    · simp [ownerAxisProjection, hfirst, hsecond]
    · simp [ownerAxisProjection, hfirst, hsecond]

theorem adjacentDifferentOwnerSwap_semanticallyEquivalent
    {fieldCount derivativeCount : ℕ}
    {left right : GlobalOwnedAxisWord fieldCount derivativeCount}
    (hswap : IsAdjacentDifferentOwnerSwap left right) :
    SemanticShuffleEquivalent left right := by
  rcases hswap with
    ⟨headEntries, tailEntries, first, second, hdifferent, hleft, hright⟩
  apply Subtype.ext
  funext owner
  change ownerAxisProjection owner left.toList =
    ownerAxisProjection owner right.toList
  rw [hleft, hright, ownerAxisProjection_append,
    ownerAxisProjection_append]
  exact congrArg (ownerAxisProjection owner headEntries ++ ·)
    (ownerAxisProjection_swap_different owner first second
      hdifferent tailEntries)

/-! ## The literal generators span the full semantic kernel -/

/-- The list-level one-step relation generated by interchanging two adjacent
entries with different field owners. -/
def ListAdjacentDifferentOwnerSwap {fieldCount : ℕ}
    (left right : List (OwnedAxis fieldCount)) : Prop :=
  ∃ (headEntries tailEntries : List (OwnedAxis fieldCount))
      (first second : OwnedAxis fieldCount),
    first.1 ≠ second.1 ∧
    left = headEntries ++ first :: second :: tailEntries ∧
    right = headEntries ++ second :: first :: tailEntries

/-- Equivalence closure of the literal adjacent different-owner swaps. -/
abbrev ListShuffleGeneratedEquivalent {fieldCount : ℕ} :
    List (OwnedAxis fieldCount) → List (OwnedAxis fieldCount) → Prop :=
  Relation.EqvGen ListAdjacentDifferentOwnerSwap

theorem listShuffleGeneratedEquivalent_cons
    {fieldCount : ℕ} (entry : OwnedAxis fieldCount)
    {left right : List (OwnedAxis fieldCount)}
    (h : ListShuffleGeneratedEquivalent left right) :
    ListShuffleGeneratedEquivalent (entry :: left) (entry :: right) := by
  refine Relation.EqvGen.rec ?_ ?_ ?_ ?_ h
  · intro source target hstep
    rcases hstep with
      ⟨headEntries, tailEntries, first, second, hdifferent,
        hsource, htarget⟩
    apply Relation.EqvGen.rel
    exact ⟨entry :: headEntries, tailEntries, first, second, hdifferent,
      by simp [hsource], by simp [htarget]⟩
  · intro source
    exact Relation.EqvGen.refl _
  · intro source target _ ih
    exact Relation.EqvGen.symm _ _ ih
  · intro source middle target _ _ ih₁ ih₂
    exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- Bubble one entry to the right across a prefix whose owners are all
different from its owner.  Every step is a literal adjacent swap. -/
theorem listShuffleGeneratedEquivalent_moveHeadAcross
    {fieldCount : ℕ} (entry : OwnedAxis fieldCount) :
    ∀ (front suffix : List (OwnedAxis fieldCount)),
      (∀ current ∈ front, entry.1 ≠ current.1) →
      ListShuffleGeneratedEquivalent
        (entry :: front ++ suffix) (front ++ entry :: suffix) := by
  intro front
  induction front with
  | nil =>
      intro suffix _
      exact Relation.EqvGen.refl _
  | cons current rest ih =>
      intro suffix hdifferent
      have hfirst : entry.1 ≠ current.1 :=
        hdifferent current (by simp)
      have hrest : ∀ later ∈ rest, entry.1 ≠ later.1 := by
        intro later hlater
        exact hdifferent later (by simp [hlater])
      have hswap : ListShuffleGeneratedEquivalent
          (entry :: current :: rest ++ suffix)
          (current :: entry :: rest ++ suffix) := by
        apply Relation.EqvGen.rel
        exact ⟨[], rest ++ suffix, entry, current, hfirst, rfl, rfl⟩
      have hmove := listShuffleGeneratedEquivalent_cons current
        (ih suffix hrest)
      exact Relation.EqvGen.trans _ _ _ hswap hmove

theorem ownerAxisProjection_eq_nil_of_all_ne
    {fieldCount : ℕ} (owner : Fin fieldCount) :
    ∀ (entries : List (OwnedAxis fieldCount)),
      (∀ entry ∈ entries, entry.1 ≠ owner) →
      ownerAxisProjection owner entries = [] := by
  intro entries
  induction entries with
  | nil =>
      intro _
      rfl
  | cons entry entries ih =>
      intro hall
      have hentry : entry.1 ≠ owner := hall entry (by simp)
      have htail : ∀ later ∈ entries, later.1 ≠ owner := by
        intro later hlater
        exact hall later (by simp [hlater])
      simp [ownerAxisProjection, hentry, ih htail]

/-- If an owner's projection begins with a specified axis, the underlying
tagged entry can be extracted; every preceding entry has a different owner.
-/
theorem exists_extract_first_owner_axis
    {fieldCount : ℕ} (owner : Fin fieldCount) (axis : Axis) :
    ∀ (entries : List (OwnedAxis fieldCount)) (remainingAxes : List Axis),
      ownerAxisProjection owner entries = axis :: remainingAxes →
      ∃ (front suffix : List (OwnedAxis fieldCount)),
        entries = front ++ (owner, axis) :: suffix ∧
        (∀ entry ∈ front, entry.1 ≠ owner) ∧
        ownerAxisProjection owner suffix = remainingAxes := by
  intro entries
  induction entries with
  | nil =>
      intro remainingAxes hprojection
      simp at hprojection
  | cons entry entries ih =>
      intro remainingAxes hprojection
      by_cases howner : entry.1 = owner
      · have hcons :
            entry.2 :: ownerAxisProjection owner entries =
              axis :: remainingAxes := by
          simpa [ownerAxisProjection, howner] using hprojection
        have haxis : entry.2 = axis := List.cons.inj hcons |>.1
        have htail : ownerAxisProjection owner entries = remainingAxes :=
          List.cons.inj hcons |>.2
        have hentry : entry = (owner, axis) := by
          exact Prod.ext howner haxis
        exact ⟨[], entries, by simp [hentry], by simp, htail⟩
      · have htailProjection :
            ownerAxisProjection owner entries = axis :: remainingAxes := by
          simpa [ownerAxisProjection, howner] using hprojection
        rcases ih remainingAxes htailProjection with
          ⟨front, suffix, hentries, hfront, hsuffix⟩
        refine ⟨entry :: front, suffix, ?_, ?_, hsuffix⟩
        · simp [hentries]
        · intro current hcurrent
          simp only [List.mem_cons] at hcurrent
          rcases hcurrent with rfl | hcurrent
          · exact howner
          · exact hfront current hcurrent

/-- Equality of all owner-local projections is generated by literal adjacent
different-owner swaps.  The proof recursively matches the head entry against
the first occurrence of its owner in the other word. -/
theorem ownerAxisProjection_eq_listShuffleGeneratedEquivalent
    {fieldCount : ℕ} :
    ∀ (left right : List (OwnedAxis fieldCount)),
      (∀ owner, ownerAxisProjection owner left =
        ownerAxisProjection owner right) →
      ListShuffleGeneratedEquivalent left right := by
  intro left
  induction left with
  | nil =>
      intro right hprojection
      cases right with
      | nil => exact Relation.EqvGen.refl _
      | cons entry entries =>
          have himpossible := hprojection entry.1
          simp [ownerAxisProjection] at himpossible
  | cons entry entries ih =>
      intro right hprojection
      have hownerProjection :
          ownerAxisProjection entry.1 right =
            entry.2 :: ownerAxisProjection entry.1 entries := by
        simpa [ownerAxisProjection] using (hprojection entry.1).symm
      rcases exists_extract_first_owner_axis entry.1 entry.2 right
          (ownerAxisProjection entry.1 entries) hownerProjection with
        ⟨front, suffix, hright, hfront, hsuffix⟩
      have htailProjection : ∀ owner,
          ownerAxisProjection owner entries =
            ownerAxisProjection owner (front ++ suffix) := by
        intro owner
        by_cases hsame : entry.1 = owner
        · subst owner
          have hfrontNil := ownerAxisProjection_eq_nil_of_all_ne
            entry.1 front hfront
          simpa [ownerAxisProjection, hright, ownerAxisProjection_append,
            hfrontNil] using hprojection entry.1
        · simpa [ownerAxisProjection, hsame, hright,
            ownerAxisProjection_append] using hprojection owner
      have htail : ListShuffleGeneratedEquivalent entries
          (front ++ suffix) := ih (front ++ suffix) htailProjection
      have hcons : ListShuffleGeneratedEquivalent (entry :: entries)
          (entry :: front ++ suffix) :=
        listShuffleGeneratedEquivalent_cons entry htail
      have hmove : ListShuffleGeneratedEquivalent
          (entry :: front ++ suffix) (front ++ entry :: suffix) :=
        listShuffleGeneratedEquivalent_moveHeadAcross entry front suffix
          (by
            intro current hcurrent
            exact (hfront current hcurrent).symm)
      have hright' : front ++ entry :: suffix = right := by
        simpa using hright.symm
      exact Relation.EqvGen.trans _ _ _ hcons
        (hright' ▸ hmove)

/-- The generated word relation on fixed-length global words. -/
def GeneratedShuffleEquivalent {fieldCount derivativeCount : ℕ}
    (left right : GlobalOwnedAxisWord fieldCount derivativeCount) : Prop :=
  ListShuffleGeneratedEquivalent left.toList right.toList

theorem listShuffleGeneratedEquivalent_ownerAxisProjection
    {fieldCount : ℕ} {left right : List (OwnedAxis fieldCount)}
    (hgenerated : ListShuffleGeneratedEquivalent left right) (owner : Fin fieldCount) :
    ownerAxisProjection owner left = ownerAxisProjection owner right := by
  refine Relation.EqvGen.rec ?_ ?_ ?_ ?_ hgenerated
  · intro source target hstep
    rcases hstep with
      ⟨headEntries, tailEntries, first, second, hdifferent,
        hsource, htarget⟩
    rw [hsource, htarget, ownerAxisProjection_append,
      ownerAxisProjection_append]
    exact congrArg (ownerAxisProjection owner headEntries ++ ·)
      (ownerAxisProjection_swap_different owner first second
        hdifferent tailEntries)
  · intro source
    rfl
  · intro source target _ ih
    exact ih.symm
  · intro source middle target _ _ ih₁ ih₂
    exact ih₁.trans ih₂

/-- Exactness theorem: literal adjacent different-owner swaps generate
precisely equality of the owner-local derivative words. -/
theorem generatedShuffleEquivalent_iff_semanticShuffleEquivalent
    {fieldCount derivativeCount : ℕ}
    (left right : GlobalOwnedAxisWord fieldCount derivativeCount) :
    GeneratedShuffleEquivalent left right ↔
      SemanticShuffleEquivalent left right := by
  constructor
  · intro hgenerated
    apply Subtype.ext
    funext owner
    exact listShuffleGeneratedEquivalent_ownerAxisProjection hgenerated owner
  · intro hsemantic
    exact ownerAxisProjection_eq_listShuffleGeneratedEquivalent
      left.toList right.toList (by
        intro owner
        exact congrArg (fun family => family.1 owner) hsemantic)

instance generatedShuffleSetoid (fieldCount derivativeCount : ℕ) :
    Setoid (GlobalOwnedAxisWord fieldCount derivativeCount) where
  r := GeneratedShuffleEquivalent
  iseqv := by
    constructor
    · intro word
      exact Relation.EqvGen.refl _
    · intro left right h
      exact Relation.EqvGen.symm _ _ h
    · intro left middle right hlm hmr
      exact Relation.EqvGen.trans _ _ _ hlm hmr

abbrev GeneratedShuffleQuotient (fieldCount derivativeCount : ℕ) :=
  Quotient (generatedShuffleSetoid fieldCount derivativeCount)

/-- The quotient by the actual adjacent shuffle generators is exactly the
finite owner-local family. -/
def generatedShuffleQuotientEquivLocal
    (fieldCount derivativeCount : ℕ) :
    GeneratedShuffleQuotient fieldCount derivativeCount ≃
      LocalAxisWordFamily fieldCount derivativeCount where
  toFun := Quotient.lift localize (by
    intro left right hgenerated
    exact (generatedShuffleEquivalent_iff_semanticShuffleEquivalent
      left right).1 hgenerated)
  invFun family := Quotient.mk _ (globalize family)
  left_inv quotient := by
    refine Quotient.inductionOn quotient ?_
    intro word
    apply Quotient.sound
    exact (generatedShuffleEquivalent_iff_semanticShuffleEquivalent
      (globalize (localize word)) word).2
        (localize_globalize (localize word))
  right_inv := localize_globalize

noncomputable instance generatedShuffleQuotientFintype
    (fieldCount derivativeCount : ℕ) :
    Fintype (GeneratedShuffleQuotient fieldCount derivativeCount) :=
  Fintype.ofEquiv (LocalAxisWordFamily fieldCount derivativeCount)
    (generatedShuffleQuotientEquivLocal fieldCount derivativeCount).symm

/-! ## Equivalence with the existing ordered-word presentation -/

def orderedDerivativeWordEquivGlobal
    (fieldCount derivativeCount : ℕ) :
    OrderedDerivativeWord fieldCount derivativeCount ≃
      GlobalOwnedAxisWord fieldCount derivativeCount where
  toFun word := List.Vector.ofFn fun position =>
    (word.ownerAtPosition position, word.axisAtPosition position)
  invFun word :=
    { ownerAtPosition := fun position => (word.get position).1
      axisAtPosition := fun position => (word.get position).2 }
  left_inv word := by
    apply OrderedDerivativeWord.ext <;> funext position <;>
      simp [List.Vector.get_ofFn]
  right_inv word := by
    exact List.Vector.ofFn_get word

/-- The word-level operation underlying the existing sparse shuffle row. -/
def swapOrderedDerivativeWord {fieldCount derivativeCount : ℕ}
    (word : OrderedDerivativeWord fieldCount derivativeCount)
    (left right : Fin derivativeCount) :
    OrderedDerivativeWord fieldCount derivativeCount where
  ownerAtPosition := word.ownerAtPosition ∘ Equiv.swap left right
  axisAtPosition := word.axisAtPosition ∘ Equiv.swap left right

theorem orderedDerivativeWordEquivGlobal_swap
    {fieldCount derivativeCount : ℕ}
    (word : OrderedDerivativeWord fieldCount derivativeCount)
    (left right : Fin derivativeCount) :
    orderedDerivativeWordEquivGlobal fieldCount derivativeCount
        (swapOrderedDerivativeWord word left right) =
      List.Vector.ofFn
        ((orderedDerivativeWordEquivGlobal fieldCount derivativeCount word).get ∘
          Equiv.swap left right) := by
  change List.Vector.ofFn (fun position =>
      (word.ownerAtPosition ((Equiv.swap left right) position),
        word.axisAtPosition ((Equiv.swap left right) position))) =
    List.Vector.ofFn
      ((List.Vector.ofFn (fun position =>
        (word.ownerAtPosition position, word.axisAtPosition position))).get ∘
          Equiv.swap left right)
  apply congrArg List.Vector.ofFn
  funext position
  simp [List.Vector.get_ofFn]

theorem orderedDerivativeWord_adjacentSwap_semanticallyEquivalent
    {fieldCount derivativeCount : ℕ}
    (word : OrderedDerivativeWord fieldCount derivativeCount)
    (left right : Fin derivativeCount)
    (hadjacent : AreAdjacentDerivativePositions left right)
    (hdifferent : word.ownerAtPosition left ≠
      word.ownerAtPosition right) :
    SemanticShuffleEquivalent
      (orderedDerivativeWordEquivGlobal fieldCount derivativeCount word)
      (orderedDerivativeWordEquivGlobal fieldCount derivativeCount
        (swapOrderedDerivativeWord word left right)) := by
  have hdifferent' :
      ((orderedDerivativeWordEquivGlobal fieldCount derivativeCount word).get
          left).1 ≠
        ((orderedDerivativeWordEquivGlobal fieldCount derivativeCount word).get
          right).1 := by
    simpa [orderedDerivativeWordEquivGlobal, List.Vector.get_ofFn] using
      hdifferent
  have hswap := adjacentSwap_isAdjacentDifferentOwnerSwap
    (orderedDerivativeWordEquivGlobal fieldCount derivativeCount word)
    left right hadjacent hdifferent'
  rw [← orderedDerivativeWordEquivGlobal_swap] at hswap
  exact adjacentDifferentOwnerSwap_semanticallyEquivalent hswap

/-- Every derivative-shuffle row already present on the exact relation
carrier lies in the kernel of localization to owner-local words. -/
theorem derivativeShuffleSite_localize_eq
    {carrier : RelationCarrier} (site : DerivativeShuffleSite carrier) :
    localize
        (orderedDerivativeWordEquivGlobal carrier.1.1
          (dimension16DerivativeCount carrier.1)
          carrier.2.derivativeWord) =
      localize
        (orderedDerivativeWordEquivGlobal carrier.1.1
          (dimension16DerivativeCount carrier.1)
          (swapDerivativePositions carrier.2 site.left site.right).derivativeWord) := by
  change SemanticShuffleEquivalent
    (orderedDerivativeWordEquivGlobal carrier.1.1
      (dimension16DerivativeCount carrier.1) carrier.2.derivativeWord)
    (orderedDerivativeWordEquivGlobal carrier.1.1
      (dimension16DerivativeCount carrier.1)
      (swapOrderedDerivativeWord carrier.2.derivativeWord
        site.left site.right))
  exact orderedDerivativeWord_adjacentSwap_semanticallyEquivalent
    carrier.2.derivativeWord site.left site.right site.adjacent site.different

end HypercubicDimension16ShuffleQuotient
end YangMills
end QuantumTheory
end Mettapedia

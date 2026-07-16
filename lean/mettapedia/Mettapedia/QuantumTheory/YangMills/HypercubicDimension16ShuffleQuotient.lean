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
local subword.  Thus every such shuffle lies in the semantic kernel.  The
converse statement---that these adjacent shuffles generate the full semantic
kernel---is deliberately left separate; no row-span equality is inferred
here.
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

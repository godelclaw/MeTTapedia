import Mettapedia.GSLT.LanguageDef.WellSorted
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Finset.Functor
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.List.OfFn
import Mathlib.Data.Multiset.Functor
import Mathlib.Data.QPF.Univariate.Basic

/-!
# Collections as quotients of the list polynomial

An ordered collection is the polynomial whose head is a length and whose
directions are the positions `Fin` of that length. A bag keeps the same
polynomial and quotients by permutation, which is the multiset functor.
A set quotients further by duplicates, which is the finite-set functor.
Both functors are quotients of that polynomial in Mathlib's sense.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Poly.CollectionLanguage

/-- The list polynomial. The head is a length. Each direction is one position. -/
abbrev listPolynomial : PFunctor.{0, 0} :=
  ⟨Nat, Fin⟩

/-- Read a list-polynomial shape as the ordered list of its positions. -/
def listOfShape {α : Type} (shape : listPolynomial α) : List α :=
  List.ofFn shape.2

/-- The multiset presented by a list-polynomial shape. Order is forgotten. -/
def multisetAbs {α : Type} (shape : listPolynomial α) : Multiset α :=
  listOfShape shape

/-- One ordered representative of a multiset. The representative is the
quotient's chosen list, read position by position. -/
noncomputable def multisetRepr {α : Type} (elements : Multiset α) : listPolynomial α :=
  ⟨(Quotient.out elements).length, fun index => (Quotient.out elements).get index⟩

theorem multiset_abs_repr {α : Type} (elements : Multiset α) :
    multisetAbs (multisetRepr elements) = elements := by
  simp only [multisetAbs, multisetRepr, listOfShape]
  change (List.ofFn (List.get (Quotient.out elements)) : Multiset α) = elements
  rw [List.ofFn_get]
  exact Quotient.out_eq elements

theorem multiset_abs_map {α β : Type} (f : α → β) (shape : listPolynomial α) :
    multisetAbs (listPolynomial.map f shape) = f <$> multisetAbs shape := by
  cases shape with
  | mk length positions =>
      rw [PFunctor.map_eq]
      simp only [multisetAbs, listOfShape, Multiset.fmap_def, Function.comp_def]
      rw [List.ofFn_comp' positions f, ← Multiset.map_coe]

/-- The multiset functor is the list polynomial modulo permutation. -/
noncomputable instance multisetQPF : QPF.{0, 0, 0} Multiset where
  P := listPolynomial
  abs := multisetAbs
  repr := multisetRepr
  abs_repr := multiset_abs_repr
  abs_map := multiset_abs_map

open scoped Classical

/-- The finite set presented by a list-polynomial shape. Order and duplicates
are forgotten. -/
noncomputable def finsetAbs {α : Type} (shape : listPolynomial α) : Finset α :=
  (listOfShape shape).toFinset

/-- One ordered, duplicate-free representative of a finite set, read from the
underlying multiset's chosen list. -/
noncomputable def finsetRepr {α : Type} (elements : Finset α) : listPolynomial α :=
  ⟨(Quotient.out elements.val).length, fun index => (Quotient.out elements.val).get index⟩

theorem finset_abs_repr {α : Type} (elements : Finset α) :
    finsetAbs (finsetRepr elements) = elements := by
  simp only [finsetAbs, finsetRepr, listOfShape]
  change (List.ofFn (List.get (Quotient.out elements.val))).toFinset = elements
  rw [List.ofFn_get, ← List.toFinset_coe]
  have representative :
      (↑(Quotient.out elements.val) : Multiset α) = elements.val :=
    Quotient.out_eq elements.val
  rw [representative]
  exact Finset.val_toFinset elements

theorem finset_abs_map {α β : Type} (f : α → β) (shape : listPolynomial α) :
    finsetAbs (listPolynomial.map f shape) = f <$> finsetAbs shape := by
  cases shape with
  | mk length positions =>
      rw [PFunctor.map_eq]
      simp only [finsetAbs, listOfShape, Finset.fmap_def, Function.comp_def]
      rw [List.ofFn_comp' positions f, ← List.toFinset_coe, ← Multiset.map_coe,
        Multiset.toFinset_map, List.toFinset_coe]

/-- The finite-set functor is the list polynomial modulo permutation and
duplicates. -/
noncomputable instance finsetQPF : QPF.{0, 0, 0} Finset where
  P := listPolynomial
  abs := finsetAbs
  repr := finsetRepr
  abs_repr := finset_abs_repr
  abs_map := finset_abs_map

/-! ## A one-sorted bag algebra

The head is either a named atom or a length. A length's directions are the
positions of the list polynomial. Reading those positions as a multiset is
the quotient: order is forgotten, and nesting is not. -/

inductive Atom where
  | u
  | w
deriving DecidableEq

inductive CollShape (α : Type) where
  | atom (name : Atom)
  | bag (elements : Multiset α)

instance : Functor CollShape where
  map f
    | .atom name => .atom name
    | .bag elements => .bag (f <$> elements)

inductive CollHead where
  | atom (name : Atom)
  | length (n : Nat)

abbrev collChild : CollHead → Type
  | .atom _ => Empty
  | .length n => Fin n

abbrev collPolynomial : PFunctor.{0, 0} :=
  ⟨CollHead, collChild⟩

def collAbs {α : Type} : collPolynomial α → CollShape α
  | ⟨.atom name, _⟩ => .atom name
  | ⟨.length _, positions⟩ => .bag (List.ofFn positions)

noncomputable def collRepr {α : Type} : CollShape α → collPolynomial α
  | .atom name => ⟨.atom name, Empty.elim⟩
  | .bag elements =>
      ⟨.length (Quotient.out elements).length, fun index => (Quotient.out elements).get index⟩

theorem coll_abs_repr {α : Type} (shape : CollShape α) :
    collAbs (collRepr shape) = shape := by
  cases shape with
  | atom name => rfl
  | bag elements =>
      simp only [collAbs, collRepr]
      change CollShape.bag (List.ofFn (List.get (Quotient.out elements))) = CollShape.bag elements
      rw [List.ofFn_get]
      exact congrArg CollShape.bag (Quotient.out_eq elements)

theorem coll_abs_map {α β : Type} (f : α → β) (shape : collPolynomial α) :
    collAbs (collPolynomial.map f shape) = f <$> collAbs shape := by
  cases shape with
  | mk head positions =>
      rw [PFunctor.map_eq]
      cases head with
      | atom name => rfl
      | length n =>
          simp only [collAbs, Functor.map, Function.comp_def, Multiset.fmap_def]
          rw [List.ofFn_comp' positions f, ← Multiset.map_coe]

noncomputable instance collQPF : QPF.{0, 0, 0} CollShape where
  P := collPolynomial
  abs := collAbs
  repr := collRepr
  abs_repr := coll_abs_repr
  abs_map := coll_abs_map

/-- An atom, as a tree of the bag algebra. -/
noncomputable def atomTree (name : Atom) : QPF.Fix CollShape :=
  QPF.Fix.mk (.atom name)

/-- A bag of trees. The elements are a multiset, so order is not part of the tree. -/
noncomputable def bagTree (elements : Multiset (QPF.Fix CollShape)) : QPF.Fix CollShape :=
  QPF.Fix.mk (.bag elements)

theorem bagTree_injective {left right : Multiset (QPF.Fix CollShape)}
    (same : bagTree left = bagTree right) : left = right := by
  have destEqual := congrArg QPF.Fix.dest same
  unfold bagTree at destEqual
  rw [QPF.Fix.dest_mk, QPF.Fix.dest_mk] at destEqual
  simpa [CollShape.bag.injEq] using destEqual

/-- Swapping the two atoms in a bag does not change the tree. -/
theorem bag_swap_same :
    bagTree (↑([atomTree .u, atomTree .w] : List _)) =
      bagTree (↑([atomTree .w, atomTree .u] : List _)) := by
  apply congrArg bagTree
  exact Multiset.coe_eq_coe.mpr (List.Perm.swap (atomTree .w) (atomTree .u) [])

/-- A nested bag is not the bag of its contents. Flattening is not this functor. -/
theorem nested_bag_ne_flat :
    bagTree (↑([bagTree (↑([atomTree .u] : List _))] : List _)) ≠
      bagTree (↑([atomTree .u] : List _)) := by
  intro same
  have elements := bagTree_injective same
  have child : bagTree (↑([atomTree .u] : List _)) = atomTree .u :=
    List.singleton_perm_singleton.mp (Multiset.coe_eq_coe.mp elements)
  have destEqual := congrArg QPF.Fix.dest child
  unfold bagTree atomTree at destEqual
  rw [QPF.Fix.dest_mk, QPF.Fix.dest_mk] at destEqual
  cases destEqual

/-- A bag of one atom is not the empty bag. The unit is not deleted. -/
theorem singleton_bag_ne_empty :
    bagTree (↑([atomTree .u] : List _)) ≠ bagTree ∅ := by
  intro same
  have elements := bagTree_injective same
  have lengths := List.Perm.length_eq (Multiset.coe_eq_coe.mp elements)
  simp only [List.length_cons, List.length_nil] at lengths
  cases lengths

/-! ## Ordered collections keep the list polynomial

A `vec` node stores the positions in order. The same two atoms in opposite
orders are different trees. -/

inductive VecShape (α : Type) where
  | atom (name : Atom)
  | vec (elements : List α)

instance : Functor VecShape where
  map f
    | .atom name => .atom name
    | .vec elements => .vec (elements.map f)

inductive VecHead where
  | atom (name : Atom)
  | length (n : Nat)

abbrev vecChild : VecHead → Type
  | .atom _ => Empty
  | .length n => Fin n

abbrev vecPolynomial : PFunctor.{0, 0} :=
  ⟨VecHead, vecChild⟩

def vecAbs {α : Type} : vecPolynomial α → VecShape α
  | ⟨.atom name, _⟩ => .atom name
  | ⟨.length _, positions⟩ => .vec (List.ofFn positions)

def vecRepr {α : Type} : VecShape α → vecPolynomial α
  | .atom name => ⟨.atom name, Empty.elim⟩
  | .vec elements => ⟨.length elements.length, fun index => elements.get index⟩

theorem vec_abs_repr {α : Type} (shape : VecShape α) :
    vecAbs (vecRepr shape) = shape := by
  cases shape with
  | atom name => rfl
  | vec elements =>
      simp only [vecAbs, vecRepr]
      change VecShape.vec (List.ofFn (List.get elements)) = VecShape.vec elements
      rw [List.ofFn_get]

theorem vec_abs_map {α β : Type} (f : α → β) (shape : vecPolynomial α) :
    vecAbs (vecPolynomial.map f shape) = f <$> vecAbs shape := by
  cases shape with
  | mk head positions =>
      rw [PFunctor.map_eq]
      cases head with
      | atom name => rfl
      | length n =>
          simp only [vecAbs, Functor.map, Function.comp_def]
          rw [List.ofFn_comp' positions f]

instance vecQPF : QPF.{0, 0, 0} VecShape where
  P := vecPolynomial
  abs := vecAbs
  repr := vecRepr
  abs_repr := vec_abs_repr
  abs_map := vec_abs_map

def vecAtom (name : Atom) : QPF.Fix VecShape :=
  QPF.Fix.mk (.atom name)

def vecTree (elements : List (QPF.Fix VecShape)) : QPF.Fix VecShape :=
  QPF.Fix.mk (.vec elements)

theorem vecTree_injective {left right : List (QPF.Fix VecShape)}
    (same : vecTree left = vecTree right) : left = right := by
  have destEqual := congrArg QPF.Fix.dest same
  unfold vecTree at destEqual
  rw [QPF.Fix.dest_mk, QPF.Fix.dest_mk] at destEqual
  simpa [VecShape.vec.injEq] using destEqual

/-- The list polynomial does not identify a swap. -/
theorem vec_swap_distinct :
    vecTree [vecAtom .u, vecAtom .w] ≠ vecTree [vecAtom .w, vecAtom .u] := by
  intro same
  have elements := vecTree_injective same
  injection elements with first _
  have destEqual := congrArg QPF.Fix.dest first
  unfold vecAtom at destEqual
  rw [QPF.Fix.dest_mk, QPF.Fix.dest_mk] at destEqual
  injection destEqual with names
  cases names

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

def atomURule : GrammarRule :=
  { label := "U", category := "A", params := [], syntaxPattern := [] }

def atomWRule : GrammarRule :=
  { label := "W", category := "A", params := [], syntaxPattern := [] }

def hashBagRule : GrammarRule :=
  { label := "Bag", category := "A",
    params := [.simple "xs" (.collection .hashBag (.base "A"))], syntaxPattern := [] }

def vecRule : GrammarRule :=
  { label := "Vec", category := "A",
    params := [.simple "xs" (.collection .vec (.base "A"))], syntaxPattern := [] }

def collectionLanguage : LanguageDef :=
  { name := "Collections", types := [{ name := "A" }],
    terms := [atomURule, atomWRule, hashBagRule, vecRule],
    equations := [], rewrites := [] }

theorem not_bare_atom (rule : GrammarRule) (empty : rule.params = []) :
    ¬ UsesBareCollection rule := by
  intro used
  rcases used with ⟨_, _, _, shape⟩
  cases mode : rule.collectionRepresentation <;> simp [GrammarRule.bareParams, mode, empty] at shape

theorem atomU_typed :
    HasType collectionLanguage FreeTypeContext.empty [] (.apply "U" []) (.base "A") :=
  HasType.constructor (rule := atomURule) (by simp [collectionLanguage])
    (not_bare_atom atomURule rfl) ArgumentsHaveTypes.nil

theorem atomW_typed :
    HasType collectionLanguage FreeTypeContext.empty [] (.apply "W" []) (.base "A") :=
  HasType.constructor (rule := atomWRule) (by simp [collectionLanguage])
    (not_bare_atom atomWRule rfl) ArgumentsHaveTypes.nil

def orderedBag : Pattern :=
  .collection .hashBag [.apply "U" [], .apply "W" []] none

def swappedBag : Pattern :=
  .collection .hashBag [.apply "W" [], .apply "U" []] none

theorem bag_elements_typed :
    ElementsHaveType collectionLanguage FreeTypeContext.empty []
      [.apply "U" [], .apply "W" []] (.base "A") :=
  ElementsHaveType.cons atomU_typed
    (ElementsHaveType.cons atomW_typed (ElementsHaveType.nil [] (.base "A")))

theorem swapped_elements_typed :
    ElementsHaveType collectionLanguage FreeTypeContext.empty []
      [.apply "W" [], .apply "U" []] (.base "A") :=
  ElementsHaveType.cons atomW_typed
    (ElementsHaveType.cons atomU_typed (ElementsHaveType.nil [] (.base "A")))

theorem orderedBag_typed :
    HasType collectionLanguage FreeTypeContext.empty [] orderedBag (.base "A") :=
  HasType.collectionConstructor (rule := hashBagRule) (by simp [collectionLanguage]) rfl
    bag_elements_typed

theorem swappedBag_typed :
    HasType collectionLanguage FreeTypeContext.empty [] swappedBag (.base "A") :=
  HasType.collectionConstructor (rule := hashBagRule) (by simp [collectionLanguage]) rfl
    swapped_elements_typed

theorem orderedBag_isObject : isObjectPattern orderedBag = true := by
  simp [orderedBag, isObjectPattern, isObjectPatternList]

theorem ordered_ne_swapped : orderedBag ≠ swappedBag := by
  intro same
  injection same with _ elements _
  injection elements with first _
  injection first with label _
  exact absurd label (by decide)

def orderedVec : Pattern :=
  .collection .vec [.apply "U" [], .apply "W" []] none

def swappedVec : Pattern :=
  .collection .vec [.apply "W" [], .apply "U" []] none

theorem orderedVec_typed :
    HasType collectionLanguage FreeTypeContext.empty [] orderedVec (.base "A") :=
  HasType.collectionConstructor (rule := vecRule) (by simp [collectionLanguage]) rfl
    bag_elements_typed

theorem vec_patterns_distinct : orderedVec ≠ swappedVec := by
  intro same
  injection same with _ elements _
  injection elements with first _
  injection first with label _
  exact absurd label (by decide)

/-- A repeated element and a single element present the same finite set. -/
theorem finset_forgets_duplicate {α : Type} (value : α) :
    finsetAbs ⟨2, fun _ => value⟩ = finsetAbs ⟨1, fun _ => value⟩ := by
  simp only [finsetAbs, listOfShape]
  rw [List.ofFn_const 2 value, List.ofFn_const 1 value]
  rw [List.toFinset_replicate_of_ne_zero (Nat.succ_ne_zero 1)]
  rw [List.toFinset_replicate_of_ne_zero (Nat.succ_ne_zero 0)]

end Mettapedia.GSLT.Poly.CollectionLanguage

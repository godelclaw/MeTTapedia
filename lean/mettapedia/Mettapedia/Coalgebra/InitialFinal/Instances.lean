import Mettapedia.Coalgebra.InitialFinal.QPFMeet
import Mettapedia.Coalgebra.StreamFinality
import Mettapedia.GSLT.Core.NonFactorization
import Mettapedia.GSLT.Poly.CollectionLanguage

/-!
# Streams, lists, and finite collections

For the functor `Label × -`, the initial algebra is the empty type and the
final coalgebra is the stream coalgebra of `Mettapedia.Coalgebra.StreamFinality`.
A coalgebra is well-founded exactly when its carrier is empty. The behaviour of
a nonempty stream coalgebra therefore does not factor through the initial
algebra, in the sense of `Factors`.

For `1 + Label × -`, finite lists are the initial algebra and the final
coalgebra is the colist coalgebra. The meeting map sends a finite list to its
colist, and the accessible states of the final coalgebra are exactly those
colists.

For the multiset and finite-set quotients of the list polynomial, the meeting
map of a uniform quotient embeds the initial algebra into the final coalgebra,
and its image is the accessible part.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Coalgebra.InitialFinal

open CategoryTheory
open CategoryTheory.Endofunctor
open CategoryTheory.Limits
open Functor (supp)
open Mettapedia.Coalgebra.StreamFinality
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.Poly.CollectionLanguage
open scoped Classical

universe u

variable (Label : Type u)

/-- `Label × -` as an endofunctor of types. -/
abbrev productFunctor : Type u ⥤ Type u := ofTypeFunctor (Prod Label)

/-- The initial algebra is empty: `Label × PEmpty` has no elements. -/
def emptyProductAlgebra : Algebra (productFunctor Label) where
  a := PEmpty.{u + 1}
  str := ↾ fun pair => pair.2.elim

def emptyProductAlgebra_initial : IsInitial (emptyProductAlgebra Label) := by
  refine IsInitial.ofUniqueHom
    (fun A => {
      f := ↾ PEmpty.elim
      h := by
        apply ConcreteCategory.hom_ext
        intro x
        exact x.2.elim })
    (fun A m => by
      apply Algebra.Hom.ext
      apply ConcreteCategory.hom_ext
      intro x
      exact x.elim)

/-- Streams, as a coalgebra for `Label × -`. Head and tail are the structure. -/
def streamProductCoalgebra : Coalgebra (productFunctor Label) where
  V := Stream Label
  str := ↾ fun stream => (head stream, tail stream)

/-- Read a categorical coalgebra as a stream coalgebra. -/
def asStreamCoalgebra (V : Coalgebra (productFunctor Label)) :
    StreamFinality.Coalgebra Label where
  Carrier := V.V
  observe := fun state => (V.str state).1
  next := fun state => (V.str state).2

/-- Behaviour into streams. -/
def streamBehaviour (V : Coalgebra (productFunctor Label)) : V.V → Stream Label :=
  unfold (asStreamCoalgebra Label V)

theorem streamBehaviour_hom (V : Coalgebra (productFunctor Label)) :
    V.str ≫ (productFunctor Label).map (↾ streamBehaviour Label V) =
      (↾ streamBehaviour Label V) ≫ (streamProductCoalgebra Label).str := by
  apply ConcreteCategory.hom_ext
  intro state
  simp only [CategoryTheory.comp_apply, productFunctor, ofTypeFunctor_map, TypeCat.ofHom,
    TypeCat.Hom.hom, ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk, streamProductCoalgebra,
    streamBehaviour, asStreamCoalgebra]
  rfl

/-- Every coalgebra morphism into streams is the unfolding. -/
theorem streamProduct_hom_unique (V : Coalgebra (productFunctor Label))
    (φ : V ⟶ streamProductCoalgebra Label) :
    φ.f = ↾ streamBehaviour Label V := by
  apply ConcreteCategory.hom_ext
  intro state
  have hstream := hom_to_stream_eq_unfold (asStreamCoalgebra Label V)
    { toFun := φ.f
      observe_preserved := by
        intro s
        have happ := congrArg Prod.fst (ConcreteCategory.congr_hom φ.h s)
        have hleft :
            ((V.str ≫ (productFunctor Label).map φ.f) s).1 = (V.str s).1 := by
          simp only [productFunctor, ofTypeFunctor_map, TypeCat.ofHom, TypeCat.Hom.hom,
            ConcreteCategory.hom_ofHom, CategoryTheory.comp_apply]
          rfl
        have hright :
            ((φ.f ≫ (streamProductCoalgebra Label).str) s).1 =
              head ((φ.f : V.V → Stream Label) s) := by
          simp only [streamProductCoalgebra, TypeCat.ofHom, ConcreteCategory.hom_ofHom,
            TypeCat.Fun.coe_mk, CategoryTheory.comp_apply, head]
        calc
          head ((φ.f : V.V → Stream Label) s) =
              ((φ.f ≫ (streamProductCoalgebra Label).str) s).1 := hright.symm
          _ = ((V.str ≫ (productFunctor Label).map φ.f) s).1 := happ.symm
          _ = (V.str s).1 := hleft
          _ = (asStreamCoalgebra Label V).observe s := rfl
      next_preserved := by
        intro s
        have happ := congrArg Prod.snd (ConcreteCategory.congr_hom φ.h s)
        have hleft :
            ((V.str ≫ (productFunctor Label).map φ.f) s).2 =
              (φ.f : V.V → Stream Label) (V.str s).2 := by
          simp only [productFunctor, ofTypeFunctor_map, TypeCat.ofHom, TypeCat.Hom.hom,
            ConcreteCategory.hom_ofHom, CategoryTheory.comp_apply]
          rfl
        have hright :
            ((φ.f ≫ (streamProductCoalgebra Label).str) s).2 =
              tail ((φ.f : V.V → Stream Label) s) := by
          simp only [streamProductCoalgebra, TypeCat.ofHom, ConcreteCategory.hom_ofHom,
            TypeCat.Fun.coe_mk, CategoryTheory.comp_apply]
        calc
          tail ((φ.f : V.V → Stream Label) s) =
              ((φ.f ≫ (streamProductCoalgebra Label).str) s).2 := hright.symm
          _ = ((V.str ≫ (productFunctor Label).map φ.f) s).2 := happ.symm
          _ = (φ.f : V.V → Stream Label) (V.str s).2 := hleft
          _ = (φ.f : V.V → Stream Label) ((asStreamCoalgebra Label V).next s) := rfl }
  simpa [streamBehaviour] using congrFun hstream state

def streamProduct_terminal : IsTerminal (streamProductCoalgebra Label) := by
  refine IsTerminal.ofUniqueHom
    (fun V => {
      f := ↾ streamBehaviour Label V
      h := streamBehaviour_hom Label V })
    (fun V φ => by
      apply Coalgebra.Hom.ext
      exact streamProduct_hom_unique Label V φ)

/-- No state of a `Label × -` coalgebra has its structure in the image of the
empty inclusion, so the empty subset is always inductive. -/
theorem product_empty_inductive (V : Coalgebra (productFunctor Label)) :
    Inductive V ∅ := by
  intro state ⟨witness, _⟩
  exact witness.2.2.elim

theorem product_wellFounded_iff_empty (V : Coalgebra (productFunctor Label)) :
    IsWellFounded V ↔ IsEmpty V.V := by
  constructor
  · intro hwf
    refine ⟨fun state => ?_⟩
    exact (hwf ∅ (product_empty_inductive Label V) state)
  · intro hempty P _ state
    exact (hempty.false state).elim

/-- The stream coalgebra is not well-founded as soon as one label exists. -/
theorem streamProduct_not_wellFounded [Nonempty Label] :
    ¬ IsWellFounded (streamProductCoalgebra Label) := by
  intro hwf
  have hempty : IsEmpty (Stream Label) :=
    (product_wellFounded_iff_empty Label _).mp hwf
  exact hempty.false fun _ => Classical.choice ‹Nonempty Label›

/-- Behaviour of the streams does not factor through a map into the empty
initial algebra. -/
theorem stream_behaviour_not_through_initial [Nonempty Label] :
    ¬ ∃ fold : Stream Label → PEmpty.{u + 1},
        Factors fold (id : Stream Label → Stream Label) := by
  intro ⟨fold, _⟩
  exact (fold fun _ => Classical.choice ‹Nonempty Label›).elim

/-- The empty coalgebra is well-founded, and its behaviour factors through the
empty initial algebra. -/
def emptyProductCoalgebra : Coalgebra (productFunctor Label) where
  V := PEmpty.{u + 1}
  str := ↾ PEmpty.elim

theorem emptyProduct_wellFounded : IsWellFounded (emptyProductCoalgebra Label) :=
  (product_wellFounded_iff_empty Label _).mpr ⟨PEmpty.elim⟩

theorem emptyProduct_factors :
    Factors (PEmpty.elim : PEmpty.{u + 1} → PEmpty.{u + 1})
      (PEmpty.elim : PEmpty.{u + 1} → Stream Label) :=
  ⟨PEmpty.elim, fun state => state.elim⟩

/-! ## Finite lists inside colists -/

/-- One step of a list or a colist: stop, or a label and a tail. -/
abbrev listStep (Label : Type u) (α : Type u) : Type u := Option (Label × α)

instance : Functor (listStep Label) where
  map f
    | none => none
    | some (label, tail) => some (label, f tail)

instance : LawfulFunctor (listStep Label) where
  map_const := rfl
  id_map
    | none => rfl
    | some _ => rfl
  comp_map _ _
    | none => rfl
    | some _ => rfl

@[simp]
theorem listStep_map_none {α β : Type u} (f : α → β) :
    Functor.map (f := listStep Label) f (none : listStep Label α) = (none : listStep Label β) :=
  rfl

@[simp]
theorem listStep_map_some {α β : Type u} (f : α → β) (label : Label) (tail : α) :
    Functor.map (f := listStep Label) f (some (label, tail) : listStep Label α) =
      (some (label, f tail) : listStep Label β) :=
  rfl

/-- Heads of the polynomial `1 + Label × -`. -/
inductive ListHead (Label : Type u) where
  | stop
  | step (label : Label)

/-- A stop has no child. A step has one child. -/
abbrev listChild {Label : Type u} : ListHead Label → Type u
  | .stop => PEmpty.{u + 1}
  | .step _ => PUnit.{u + 1}

/-- The polynomial whose object is one step of a list. -/
abbrev listPolynomial (Label : Type u) : PFunctor.{u, u} :=
  ⟨ListHead Label, listChild⟩

def listAbs {Label : Type u} {α : Type u} :
    (listPolynomial Label).Obj α → listStep Label α
  | ⟨.stop, _⟩ => none
  | ⟨.step label, child⟩ => some (label, child PUnit.unit)

def listRepr {Label : Type u} {α : Type u} :
    listStep Label α → (listPolynomial Label).Obj α
  | none => ⟨.stop, PEmpty.elim⟩
  | some (label, tail) => ⟨.step label, fun _ => tail⟩

theorem list_abs_repr {Label : Type u} {α : Type u} (x : listStep Label α) :
    listAbs (listRepr x) = x := by
  cases x with
  | none => rfl
  | some _ => rfl

theorem list_abs_map {Label : Type u} {α β : Type u} (f : α → β)
    (shape : (listPolynomial Label).Obj α) :
    listAbs ((listPolynomial Label).map f shape) = f <$> listAbs shape := by
  rcases shape with ⟨head, _⟩
  cases head with
  | stop => rfl
  | step _ => rfl

instance : QPF (listStep Label) where
  P := listPolynomial Label
  abs := listAbs
  repr := listRepr
  abs_repr := list_abs_repr
  abs_map := list_abs_map

/-- Equal abstractions of `1 + Label × -` have the same child image. -/
theorem listStep_uniform : QPF.IsUniform (F := listStep Label) := by
  intro α head head' child child' h
  cases head with
  | stop =>
      cases head' with
      | stop =>
          ext x
          simp only [Set.mem_image, Set.mem_univ, true_and]
          constructor <;> rintro ⟨i, _⟩ <;> exact i.elim
      | step label' =>
          change (none : listStep Label α) = some (label', child' PUnit.unit) at h
          cases h
  | step label =>
      cases head' with
      | stop =>
          change some (label, child PUnit.unit) = (none : listStep Label α) at h
          cases h
      | step label' =>
          change some (label, child PUnit.unit) = some (label', child' PUnit.unit) at h
          obtain ⟨rfl, hchild⟩ := Prod.ext_iff.mp (Option.some_inj.mp h)
          ext x
          simp only [Set.mem_image, Set.mem_univ, true_and]
          constructor
          · rintro ⟨i, hi⟩
            cases i
            exact ⟨PUnit.unit, hchild.symm.trans hi⟩
          · rintro ⟨i, hi⟩
            cases i
            exact ⟨PUnit.unit, hchild.trans hi⟩

theorem listStep_supp_some {α : Type u} (label : Label) (tail : α) :
    tail ∈ supp (F := listStep Label) (some (label, tail)) := by
  have hsupp := QPF.supp_eq_of_isUniform (listStep_uniform Label) (ListHead.step label)
    (fun _ : PUnit.{u + 1} => tail)
  change supp (F := listStep Label) (some (label, tail)) =
    (fun _ : PUnit.{u + 1} => tail) '' Set.univ at hsupp
  rw [hsupp]
  exact ⟨PUnit.unit, Set.mem_univ _, rfl⟩

/-- Read a finite construction as a list. -/
def listOfFix : QPF.Fix (listStep Label) → List Label :=
  QPF.Fix.rec fun
    | none => []
    | some (label, tail) => label :: tail

/-- Build a finite construction from a list. -/
def fixOfList : List Label → QPF.Fix (listStep Label)
  | [] => QPF.Fix.mk none
  | label :: tail => QPF.Fix.mk (some (label, fixOfList tail))

theorem listOfFix_fixOfList (xs : List Label) :
    listOfFix Label (fixOfList Label xs) = xs := by
  induction xs with
  | nil =>
      unfold fixOfList listOfFix
      rw (config := { transparency := .default }) [QPF.Fix.rec_eq]
      rfl
  | cons label tail ih =>
      unfold fixOfList
      rw (config := { transparency := .default }) [listOfFix, QPF.Fix.rec_eq, listStep_map_some]
      exact congrArg (fun rest => label :: rest) ih

theorem fixOfList_listOfFix (x : QPF.Fix (listStep Label)) :
    fixOfList Label (listOfFix Label x) = x := by
  revert x
  apply QPF.Fix.ind
  intro y hy
  rw [QPF.liftp_iff_of_isUniform (listStep_uniform Label)] at hy
  rw (config := { transparency := .default }) [listOfFix, QPF.Fix.rec_eq]
  cases y with
  | none =>
      rw [listStep_map_none]
      unfold fixOfList
      rfl
  | some pair =>
      rcases pair with ⟨label, tail⟩
      have htail : fixOfList Label (listOfFix Label tail) = tail :=
        hy tail (listStep_supp_some Label label tail)
      unfold listOfFix at htail
      rw [listStep_map_some]
      unfold fixOfList
      rw [htail]

/-- The meeting map of `1 + Label × -` is injective. -/
theorem list_iota_injective : Function.Injective (iota (F := listStep Label)) :=
  iota_injective (listStep_uniform Label)

/-- A colist lies on a finite list exactly when it is accessible. -/
theorem list_meet (y : QPF.Cofix (listStep Label)) :
    (∃ xs : List Label, iota (F := listStep Label) (fixOfList Label xs) = y) ↔
      Acc (cofixChild (F := listStep Label)) y := by
  constructor
  · rintro ⟨xs, hx⟩
    rw [← hx]
    exact iota_accessible (listStep_uniform Label) (fixOfList Label xs)
  · intro hy
    obtain ⟨x, hx⟩ := (mem_image_iff_accessible (listStep_uniform Label) y).mpr hy
    exact ⟨listOfFix Label x, by rw [fixOfList_listOfFix, hx]⟩

/-! ## Bags and finite sets -/

omit Label in
theorem multiset_uniform : QPF.IsUniform (F := Multiset) := by
  intro α n n' positions positions' h
  change multisetAbs ⟨n, positions⟩ = multisetAbs ⟨n', positions'⟩ at h
  ext x
  have hlist : (List.ofFn positions : Multiset α) = List.ofFn positions' := by
    simpa [multisetAbs, listOfShape] using h
  rw (config := { transparency := .default }) [Set.mem_image, Set.mem_image]
  simp only [Set.mem_univ, true_and]
  rw (config := { transparency := .default }) [← List.mem_ofFn, ← List.mem_ofFn,
    ← Multiset.mem_coe, ← Multiset.mem_coe]
  exact Iff.of_eq (congrArg (fun elements => x ∈ elements) hlist)

omit Label in
theorem multiset_fix_embeds : Function.Injective (iota (F := Multiset)) :=
  iota_injective multiset_uniform

omit Label in
theorem multiset_image_iff_accessible (y : QPF.Cofix Multiset) :
    (∃ x : QPF.Fix Multiset, iota (F := Multiset) x = y) ↔
      Acc (cofixChild (F := Multiset)) y :=
  mem_image_iff_accessible multiset_uniform y

omit Label in
theorem finset_uniform : QPF.IsUniform (F := Finset) := by
  intro α n n' positions positions' h
  change finsetAbs ⟨n, positions⟩ = finsetAbs ⟨n', positions'⟩ at h
  ext x
  have hlist : (List.ofFn positions).toFinset = (List.ofFn positions').toFinset := by
    simpa [finsetAbs, listOfShape] using h
  rw (config := { transparency := .default }) [Set.mem_image, Set.mem_image]
  simp only [Set.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    have hx : x ∈ (List.ofFn positions).toFinset := by
      rw (config := { transparency := .default }) [List.mem_toFinset, List.mem_ofFn]
      exact ⟨i, hi⟩
    rw [hlist] at hx
    rw (config := { transparency := .default }) [List.mem_toFinset, List.mem_ofFn] at hx
    exact hx
  · rintro ⟨i, hi⟩
    have hx : x ∈ (List.ofFn positions').toFinset := by
      rw (config := { transparency := .default }) [List.mem_toFinset, List.mem_ofFn]
      exact ⟨i, hi⟩
    rw [← hlist] at hx
    rw (config := { transparency := .default }) [List.mem_toFinset, List.mem_ofFn] at hx
    exact hx

omit Label in
theorem finset_fix_embeds : Function.Injective (iota (F := Finset)) :=
  iota_injective finset_uniform

omit Label in
/-- Hereditarily finite sets are the accessible part of the finite-set coalgebra. -/
theorem finset_image_iff_accessible (y : QPF.Cofix Finset) :
    (∃ x : QPF.Fix Finset, iota (F := Finset) x = y) ↔
      Acc (cofixChild (F := Finset)) y :=
  mem_image_iff_accessible finset_uniform y

end Mettapedia.Coalgebra.InitialFinal


import Mettapedia.OSLF.MeTTaIL.WrapperLaws
import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# Composition distributing over an idempotent sum

Meredith's oriented processes extend parallel composition by an idempotent summation and an absorbing
chaos: composition is the multiplication of a commutative monoid over a bag, summation is a
semilattice over a set, composition distributes over summation, and chaos absorbs both (`Decl`). The
bag monad distributes over the set monad, and the composite's free algebras are sums of products: a
process is chaos, or a finite set of products, each a finite bag of atoms.

The canonical form computes that presentation bottom up (`normal`): every composition is multiplied
out over the sums it holds (`multiply`), every sum is flattened and loses its repetitions (`add`), and
the absorbing element absorbs both; products and sums are kept in canonical order, a product of one
atom is the atom and of none the unit, a sum of one product is the product.

Summation has no unit, so every sum of a process has a summand and the empty sum is not a process
(`plain`). The congruence of processes relates processes by moves between processes (`Congruent`):
every process is congruent to its canonical form (`congruent_normal`), every law keeps the canonical
form on every object term (`Move.normal_eq`), and so the canonical form decides the congruence
(`congruent_iff`). Moves through patterns that are not processes relate no further processes
(`congruent_iff_equal`). The canonical form gives the empty sum no products, as the free algebra
does; a law making it annihilate every composition would identify it with the absorbing element, and
then every process with that element, since the empty sum is the unit of summation through
flattening.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Distributive

open Syntax CanonicalBags PatternLexOrder

/-- A composition distributing over an idempotent sum, with an element absorbing both. -/
structure Decl where
  /-- The kind of the composition's collection, a bag. -/
  product : CollType
  /-- The composition's unit. -/
  unit : String
  /-- The kind of the summation's collection, a set. -/
  sum : CollType
  /-- The element absorbing both. -/
  absorbing : String
deriving Repr, DecidableEq

variable (decl : Decl)

/-- A product as a pattern: its atoms in canonical order; the unit when there are none, the atom
when there is one. -/
def productOf (atoms : List Pattern) : Pattern :=
  match sortLex atoms with
  | [] => .apply decl.unit []
  | [atom] => atom
  | sorted => .collection decl.product sorted none

/-- A sum as a pattern: its distinct products in canonical order; the empty sum when there are none,
the product when there is one. -/
def sumOf (products : List (List Pattern)) : Pattern :=
  match sortLex (products.map (productOf decl)).dedup with
  | [] => .collection decl.sum [] none
  | [product] => product
  | sorted => .collection decl.sum sorted none

/-- The atoms of a canonical product. -/
def atoms : Pattern → List Pattern
  | .apply label [] => if label = decl.unit then [] else [.apply label []]
  | .collection kind elements none => if kind = decl.product then elements else [.collection kind elements none]
  | other => [other]

/-- The products of a canonical form, each as its atoms; nothing for the absorbing element, and none
for the empty sum. -/
def products : Pattern → Option (List (List Pattern))
  | .apply label [] =>
      if label = decl.absorbing then none
      else if label = decl.unit then some [[]] else some [[.apply label []]]
  | .collection kind elements none =>
      if kind = decl.sum then some (elements.map (atoms decl))
      else if kind = decl.product then some [elements]
      else some [[.collection kind elements none]]
  | other => some [[other]]

/-- Every way of choosing one product of each factor, multiplied out. -/
def choices : List (List (List Pattern)) → List (List Pattern)
  | [] => [[]]
  | factor :: factors => factor.flatMap fun chosen => (choices factors).map (chosen ++ ·)

/-- The canonical form of a composition of canonical forms. -/
def multiply (items : List Pattern) : Pattern :=
  match items.mapM (products decl) with
  | none => .apply decl.absorbing []
  | some factors => sumOf decl (choices factors)

/-- The canonical form of a sum of canonical forms. -/
def add (items : List Pattern) : Pattern :=
  match items.mapM (products decl) with
  | none => .apply decl.absorbing []
  | some parts => sumOf decl parts.flatten

/-- **The canonical form**: bottom up, every collection in canonical order, every composition
multiplied out over the sums it holds, every sum flattened and without repetition, the absorbing
element absorbing both. -/
def normal : Pattern → Pattern
  | .bvar index => .bvar index
  | .fvar name => .fvar name
  | .apply label arguments => .apply label (arguments.map normal)
  | .lambda binder body => .lambda binder (normal body)
  | .multiLambda arity binders body => .multiLambda arity binders (normal body)
  | .subst body replacement => .subst (normal body) (normal replacement)
  | .collection kind elements rest =>
      match rest with
      | some name => .collection kind (arrange kind (elements.map normal)) (some name)
      | none =>
          if kind = decl.product then multiply decl (elements.map normal)
          else if kind = decl.sum then add decl (elements.map normal)
          else .collection kind (arrange kind (elements.map normal)) none
decreasing_by all_goals sizeOf_pattern_dec

/-! ## The laws -/

/-- What the canonical form needs of a declaration: the composition is a bag, since a set would make it
idempotent, the sum is an unordered collection other than it, and the unit is not the absorbing
element. -/
structure Decl.Valid : Prop where
  distinct : decl.product ≠ decl.sum
  productBag : decl.product = .hashBag
  sumUnordered : Unordered decl.sum = true
  unitAbsorbing : decl.unit ≠ decl.absorbing

theorem Decl.Valid.productUnordered (valid : decl.Valid) : Unordered decl.product = true := by
  rw [valid.productBag]; rfl

/-- The declared collection laws: the composition flattens with its unit, the sum flattens. -/
def laws : List CollectionLaws.Laws := [⟨decl.product, some decl.unit⟩, ⟨decl.sum, none⟩]

/-- One use of the laws beyond the collection algebra, in any context: a repeated summand is one
summand, the absorbing element absorbs a composition and a sum, and composition distributes over a
sum of at least two summands. -/
inductive Step : Pattern → Pattern → Prop where
  | repeated {before middle after : List Pattern} {element : Pattern} :
      Step (.collection decl.sum (before ++ element :: middle ++ element :: after) none)
        (.collection decl.sum (before ++ element :: middle ++ after) none)
  | absorbProduct {before after : List Pattern} :
      Step (.collection decl.product (before ++ .apply decl.absorbing [] :: after) none) (.apply decl.absorbing [])
  | absorbSum {before after : List Pattern} :
      Step (.collection decl.sum (before ++ .apply decl.absorbing [] :: after) none) (.apply decl.absorbing [])
  | distribute {before after summands : List Pattern} : 2 ≤ summands.length →
      Step (.collection decl.product (before ++ .collection decl.sum summands none :: after) none)
        (.collection decl.sum
          (summands.map fun summand => .collection decl.product (before ++ summand :: after) none) none)
  | apply {label : String} {before after : List Pattern} {argument changed : Pattern} :
      Step argument changed → Step (.apply label (before ++ argument :: after)) (.apply label (before ++ changed :: after))
  | lambda {binder : Option String} {body changed : Pattern} :
      Step body changed → Step (.lambda binder body) (.lambda binder changed)
  | multiLambda {arity : Nat} {binders : List String} {body changed : Pattern} :
      Step body changed → Step (.multiLambda arity binders body) (.multiLambda arity binders changed)
  | substBody {body changed replacement : Pattern} :
      Step body changed → Step (.subst body replacement) (.subst changed replacement)
  | substReplacement {body replacement changed : Pattern} :
      Step replacement changed → Step (.subst body replacement) (.subst body changed)
  | element {kind : CollType} {before after : List Pattern} {element changed : Pattern} {rest : Option String} :
      Step element changed →
      Step (.collection kind (before ++ element :: after) rest) (.collection kind (before ++ changed :: after) rest)

/-- A move of the model: a law of the declared collection algebra, one of its wrapper laws, or a
step. -/
def Move (left right : Pattern) : Prop :=
  LawStep (laws decl) left right ∨ Wrappers.WrapperStep (laws decl) left right ∨ Step decl left right

/-- Equality in the model. -/
abbrev Equal (left right : Pattern) : Prop := Relation.EqvGen (Move decl) left right

/-! ## Processes

The calculus's summation has no unit, so every sum has a summand and the empty sum is not a process
(`plain`). The congruence of processes relates processes by moves between processes (`Congruent`);
equality in the model (`Equal`) may also pass through patterns that are not processes. -/

mutual
  /-- A term without collection rests: an object term. -/
  def restFree : Pattern → Bool
    | .bvar _ => true
    | .fvar _ => true
    | .apply _ arguments => restFreeList arguments
    | .lambda _ body => restFree body
    | .multiLambda _ _ body => restFree body
    | .subst body replacement => restFree body && restFree replacement
    | .collection _ elements rest => rest.isNone && restFreeList elements

  /-- Every term of a list is an object term. -/
  def restFreeList : List Pattern → Bool
    | [] => true
    | pattern :: patterns => restFree pattern && restFreeList patterns
end

mutual
  /-- A process: an object term whose sums all have a summand. -/
  def plain (decl : Decl) : Pattern → Bool
    | .bvar _ => true
    | .fvar _ => true
    | .apply _ arguments => plainList decl arguments
    | .lambda _ body => plain decl body
    | .multiLambda _ _ body => plain decl body
    | .subst body replacement => plain decl body && plain decl replacement
    | .collection kind elements rest =>
        rest.isNone && !(decide (kind = decl.sum) && elements.isEmpty) && plainList decl elements

  /-- Every term of a list is a process. -/
  def plainList (decl : Decl) : List Pattern → Bool
    | [] => true
    | pattern :: patterns => plain decl pattern && plainList decl patterns
end

/-- A move between processes. -/
def MoveOn (left right : Pattern) : Prop := plain decl left = true ∧ plain decl right = true ∧ Move decl left right

/-- **The congruence of processes**: equality by moves between processes. -/
abbrev Congruent (left right : Pattern) : Prop := Relation.EqvGen (MoveOn decl) left right

variable {decl}

theorem restFreeList_iff : ∀ {items : List Pattern}, restFreeList items = true ↔ ∀ item ∈ items, restFree item = true
  | [] => by simp [restFreeList]
  | item :: items => by simp [restFreeList, restFreeList_iff]

theorem restFree_collection {kind : CollType} {elements : List Pattern} {rest : Option String}
    (isFree : restFree (.collection kind elements rest) = true) :
    rest = none ∧ ∀ element ∈ elements, restFree element = true := by
  simp only [restFree, Bool.and_eq_true, Option.isNone_iff_eq_none] at isFree
  exact ⟨isFree.1, restFreeList_iff.mp isFree.2⟩

theorem restFree_apply {label : String} {arguments : List Pattern} (isFree : restFree (.apply label arguments) = true) :
    ∀ argument ∈ arguments, restFree argument = true := by
  simp only [restFree] at isFree
  exact restFreeList_iff.mp isFree

theorem restFree_subst {body replacement : Pattern} (isFree : restFree (.subst body replacement) = true) :
    restFree body = true ∧ restFree replacement = true := by
  simpa [restFree] using isFree

theorem plainList_iff : ∀ {items : List Pattern}, plainList decl items = true ↔ ∀ item ∈ items, plain decl item = true
  | [] => by simp [plainList]
  | item :: items => by simp [plainList, plainList_iff]

theorem plain_collection {kind : CollType} {elements : List Pattern} {rest : Option String}
    (isPlain : plain decl (.collection kind elements rest) = true) :
    rest = none ∧ (kind = decl.sum → elements ≠ []) ∧ ∀ element ∈ elements, plain decl element = true := by
  simp only [plain, Bool.and_eq_true, Option.isNone_iff_eq_none, Bool.not_eq_eq_eq_not, Bool.not_true,
    Bool.and_eq_false_iff, decide_eq_false_iff_not, List.isEmpty_eq_false_iff] at isPlain
  obtain ⟨⟨rfl, nonempty⟩, elementsPlain⟩ := isPlain
  refine ⟨rfl, fun same => ?_, plainList_iff.mp elementsPlain⟩
  rcases nonempty with notSum | nonempty
  · exact absurd same notSum
  · exact nonempty

theorem plain_collection_iff {kind : CollType} {elements : List Pattern} :
    plain decl (.collection kind elements none) = true ↔
      (kind = decl.sum → elements ≠ []) ∧ ∀ element ∈ elements, plain decl element = true := by
  constructor
  · intro isPlain
    exact ⟨(plain_collection isPlain).2.1, (plain_collection isPlain).2.2⟩
  · rintro ⟨nonempty, each⟩
    simp only [plain, Option.isNone_none, Bool.true_and, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      Bool.and_eq_false_iff, decide_eq_false_iff_not, List.isEmpty_eq_false_iff]
    refine ⟨?_, plainList_iff.mpr each⟩
    by_cases same : kind = decl.sum
    · exact .inr (nonempty same)
    · exact .inl same

theorem plain_apply {label : String} {arguments : List Pattern} (isPlain : plain decl (.apply label arguments) = true) :
    ∀ argument ∈ arguments, plain decl argument = true := by
  simp only [plain] at isPlain
  exact plainList_iff.mp isPlain

theorem plain_apply_iff {label : String} {arguments : List Pattern} :
    plain decl (.apply label arguments) = true ↔ ∀ argument ∈ arguments, plain decl argument = true := by
  simp only [plain]
  exact plainList_iff

theorem plain_constant (label : String) : plain decl (.apply label []) = true := by simp [plain, plainList]

theorem restFree_of_plain : ∀ {pattern : Pattern}, plain decl pattern = true → restFree pattern = true
  | .bvar _, _ => rfl
  | .fvar _, _ => rfl
  | .apply _ arguments, isPlain => by
    simp only [restFree]
    exact restFreeList_iff.mpr fun argument member => restFree_of_plain (plain_apply isPlain argument member)
  | .lambda _ body, isPlain => by simp only [restFree]; exact restFree_of_plain (by simpa [plain] using isPlain)
  | .multiLambda _ _ body, isPlain => by simp only [restFree]; exact restFree_of_plain (by simpa [plain] using isPlain)
  | .subst body replacement, isPlain => by
    have parts : plain decl body = true ∧ plain decl replacement = true := by simpa [plain] using isPlain
    simp only [restFree, Bool.and_eq_true]
    exact ⟨restFree_of_plain parts.1, restFree_of_plain parts.2⟩
  | .collection kind elements rest, isPlain => by
    obtain ⟨rfl, _, elementsPlain⟩ := plain_collection isPlain
    simp only [restFree, Option.isNone_none, Bool.true_and]
    exact restFreeList_iff.mpr fun element member => restFree_of_plain (elementsPlain element member)
termination_by pattern => sizeOf pattern
decreasing_by
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; simp only [Pattern.apply.sizeOf_spec, Pattern.collection.sizeOf_spec]; omega)
    | (simp only [Pattern.lambda.sizeOf_spec, Pattern.multiLambda.sizeOf_spec, Pattern.subst.sizeOf_spec]; omega)

/-- Every element of `before ++ x :: after` holds when `x` and the rest do. -/
theorem forall_around {p : Pattern → Prop} {before after : List Pattern} {x : Pattern}
    (around : ∀ item ∈ before ++ after, p item) (here : p x) : ∀ item ∈ before ++ x :: after, p item := by
  intro item member
  rcases List.mem_append.mp member with inBefore | inRest
  · exact around item (List.mem_append_left _ inBefore)
  · rcases List.mem_cons.mp inRest with rfl | inAfter
    · exact here
    · exact around item (List.mem_append_right _ inAfter)

/-- Congruence is equality in the model. -/
theorem Congruent.equal {left right : Pattern} (related : Congruent decl left right) : Equal decl left right :=
  Relation.EqvGen.mono (fun _ _ move => move.2.2) _ _ related

theorem Congruent.lift {f : Pattern → Pattern} (plainLift : ∀ {a : Pattern}, plain decl a = true → plain decl (f a) = true)
    (lawLift : ∀ {a b : Pattern}, LawStep (laws decl) a b → LawStep (laws decl) (f a) (f b))
    (wrapperLift : ∀ {a b : Pattern}, Wrappers.WrapperStep (laws decl) a b →
      Wrappers.WrapperStep (laws decl) (f a) (f b))
    (stepLift : ∀ {a b : Pattern}, Step decl a b → Step decl (f a) (f b))
    {a b : Pattern} (related : Congruent decl a b) : Congruent decl (f a) (f b) := by
  induction related with
  | rel _ _ move =>
    obtain ⟨leftPlain, rightPlain, move⟩ := move
    refine .rel _ _ ⟨plainLift leftPlain, plainLift rightPlain, ?_⟩
    rcases move with lawMove | wrapped | stepped
    · exact .inl (lawLift lawMove)
    · exact .inr (.inl (wrapperLift wrapped))
    · exact .inr (.inr (stepLift stepped))
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

/-- Congruence at one element of a collection of processes. -/
theorem Congruent.element (kind : CollType) {before after : List Pattern}
    (around : ∀ item ∈ before ++ after, plain decl item = true) {a b : Pattern} (related : Congruent decl a b) :
    Congruent decl (.collection kind (before ++ a :: after) none) (.collection kind (before ++ b :: after) none) :=
  Congruent.lift (f := fun x => .collection kind (before ++ x :: after) none)
    (fun xPlain => plain_collection_iff.mpr ⟨fun _ => by simp, forall_around around xPlain⟩)
    (fun step => .element step) (fun step => .element step) (fun step => .element step) related

/-- Congruence of collections whose elements are images of one list, pointwise congruent. -/
theorem Congruent.mapPointwise {α : Type} (kind : CollType) (f g : α → Pattern) :
    ∀ (before : List Pattern) (items : List α), (∀ item ∈ before, plain decl item = true) →
      (∀ item ∈ items, plain decl (f item) = true ∧ plain decl (g item) = true) →
      (∀ item ∈ items, Congruent decl (f item) (g item)) →
      Congruent decl (.collection kind (before ++ items.map f) none) (.collection kind (before ++ items.map g) none)
  | _, [], _, _, _ => .refl _
  | before, item :: items, beforePlain, itemsPlain, each => by
    have first := Congruent.element (decl := decl) kind (before := before) (after := items.map f)
      (fun other member => by
        rcases List.mem_append.mp member with inBefore | inAfter
        · exact beforePlain other inBefore
        · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp inAfter
          exact (itemsPlain source (List.mem_cons_of_mem _ sourceMember)).1)
      (each item List.mem_cons_self)
    have later := Congruent.mapPointwise kind f g (before ++ [g item]) items
      (fun other member => by
        rcases List.mem_append.mp member with inBefore | inLast
        · exact beforePlain other inBefore
        · rw [List.mem_singleton] at inLast
          subst inLast
          exact (itemsPlain item List.mem_cons_self).2)
      (fun other member => itemsPlain other (List.mem_cons_of_mem _ member))
      (fun other member => each other (List.mem_cons_of_mem _ member))
    simp only [List.map_cons, List.append_assoc, List.singleton_append] at first later ⊢
    exact .trans _ _ _ first later

/-- Congruence at an argument of a constructor. -/
theorem Congruent.argument (label : String) {before after : List Pattern}
    (around : ∀ item ∈ before ++ after, plain decl item = true) {a b : Pattern} (related : Congruent decl a b) :
    Congruent decl (.apply label (before ++ a :: after)) (.apply label (before ++ b :: after)) :=
  Congruent.lift (f := fun x => .apply label (before ++ x :: after))
    (fun xPlain => plain_apply_iff.mpr (forall_around around xPlain))
    (fun step => .apply step) (fun step => .apply step) (fun step => .apply step) related

/-- Congruence at every argument of a constructor. -/
theorem Congruent.arguments (label : String) (g : Pattern → Pattern) :
    ∀ (before items : List Pattern), (∀ item ∈ before, plain decl item = true) →
      (∀ item ∈ items, plain decl item = true ∧ plain decl (g item) = true) →
      (∀ item ∈ items, Congruent decl item (g item)) →
      Congruent decl (.apply label (before ++ items)) (.apply label (before ++ items.map g))
  | before, [], _, _, _ => by simpa using Relation.EqvGen.refl _
  | before, item :: items, beforePlain, itemsPlain, each => by
    have first := Congruent.argument (decl := decl) label (before := before) (after := items)
      (fun other member => by
        rcases List.mem_append.mp member with inBefore | inAfter
        · exact beforePlain other inBefore
        · exact (itemsPlain other (List.mem_cons_of_mem _ inAfter)).1)
      (each item List.mem_cons_self)
    have later := Congruent.arguments label g (before ++ [g item]) items
      (fun other member => by
        rcases List.mem_append.mp member with inBefore | inLast
        · exact beforePlain other inBefore
        · rw [List.mem_singleton] at inLast
          subst inLast
          exact (itemsPlain item List.mem_cons_self).2)
      (fun other member => itemsPlain other (List.mem_cons_of_mem _ member))
      (fun other member => each other (List.mem_cons_of_mem _ member))
    simp only [List.append_assoc, List.singleton_append] at later
    exact .trans _ _ _ first later

/-! ## Single moves between processes -/

theorem lawFor_product : CollectionLaws.lawFor (laws decl) decl.product = some ⟨decl.product, some decl.unit⟩ := by
  simp [laws, CollectionLaws.lawFor]

theorem lawFor_sum (valid : decl.Valid) : CollectionLaws.lawFor (laws decl) decl.sum = some ⟨decl.sum, none⟩ := by
  simp [laws, CollectionLaws.lawFor, valid.distinct]

/-- A composition of processes is a process. -/
theorem plain_product (valid : decl.Valid) {elements : List Pattern} (each : ∀ item ∈ elements, plain decl item = true) :
    plain decl (.collection decl.product elements none) = true :=
  plain_collection_iff.mpr ⟨fun same => absurd same valid.distinct, each⟩

/-- A sum of processes with a summand is a process. -/
theorem plain_sum {elements : List Pattern} (nonempty : elements ≠ []) (each : ∀ item ∈ elements, plain decl item = true) :
    plain decl (.collection decl.sum elements none) = true :=
  plain_collection_iff.mpr ⟨fun _ => nonempty, each⟩

theorem flattenProduct (valid : decl.Valid) {before inner after : List Pattern}
    (around : ∀ item ∈ before ++ after, plain decl item = true) (innerPlain : ∀ item ∈ inner, plain decl item = true) :
    Congruent decl (.collection decl.product (before ++ .collection decl.product inner none :: after) none)
      (.collection decl.product (before ++ inner ++ after) none) := by
  refine .rel _ _ ⟨plain_product valid (forall_around around (plain_product valid innerPlain)),
    plain_product valid fun item member => ?_, .inl (.flatten lawFor_product)⟩
  rcases List.mem_append.mp member with inFirst | inAfter
  · rcases List.mem_append.mp inFirst with inBefore | inInner
    · exact around item (List.mem_append_left _ inBefore)
    · exact innerPlain item inInner
  · exact around item (List.mem_append_right _ inAfter)

theorem unitProduct (valid : decl.Valid) {before after : List Pattern}
    (around : ∀ item ∈ before ++ after, plain decl item = true) :
    Congruent decl (.collection decl.product (before ++ .apply decl.unit [] :: after) none)
      (.collection decl.product (before ++ after) none) :=
  .rel _ _ ⟨plain_product valid (forall_around around (plain_constant _)), plain_product valid around,
    .inl (.unit lawFor_product rfl)⟩

theorem flattenSum (valid : decl.Valid) {before inner after : List Pattern} (innerNonempty : inner ≠ [])
    (around : ∀ item ∈ before ++ after, plain decl item = true) (innerPlain : ∀ item ∈ inner, plain decl item = true) :
    Congruent decl (.collection decl.sum (before ++ .collection decl.sum inner none :: after) none)
      (.collection decl.sum (before ++ inner ++ after) none) := by
  refine .rel _ _ ⟨plain_sum (by simp) (forall_around around (plain_sum innerNonempty innerPlain)),
    plain_sum (by simp [innerNonempty]) fun item member => ?_, .inl (.flatten (lawFor_sum valid))⟩
  rcases List.mem_append.mp member with inFirst | inAfter
  · rcases List.mem_append.mp inFirst with inBefore | inInner
    · exact around item (List.mem_append_left _ inBefore)
    · exact innerPlain item inInner
  · exact around item (List.mem_append_right _ inAfter)

theorem singletonProduct (valid : decl.Valid) {element : Pattern} (elementPlain : plain decl element = true) :
    Congruent decl (.collection decl.product [element] none) element :=
  .rel _ _ ⟨plain_product valid (by simpa using elementPlain), elementPlain, .inr (.inl (.singleton lawFor_product))⟩

theorem emptyProduct (valid : decl.Valid) : Congruent decl (.collection decl.product [] none) (.apply decl.unit []) :=
  .rel _ _ ⟨plain_product valid (by simp), plain_constant _, .inr (.inl (.empty lawFor_product rfl))⟩

theorem singletonSum (valid : decl.Valid) {element : Pattern} (elementPlain : plain decl element = true) :
    Congruent decl (.collection decl.sum [element] none) element :=
  .rel _ _ ⟨plain_sum (by simp) (by simpa using elementPlain), elementPlain,
    .inr (.inl (.singleton (lawFor_sum valid)))⟩

theorem permute {kind : CollType} (unordered : Unordered kind = true) {elements permuted : List Pattern}
    (permutation : elements.Perm permuted) (isPlain : plain decl (.collection kind elements none) = true) :
    Congruent decl (.collection kind elements none) (.collection kind permuted none) := by
  obtain ⟨nonempty, each⟩ := plain_collection_iff.mp isPlain
  refine .rel _ _ ⟨isPlain, plain_collection_iff.mpr ⟨fun same empty => ?_,
    fun item member => each item (permutation.symm.subset member)⟩, .inl (.permute unordered permutation)⟩
  subst empty
  exact nonempty same (List.Perm.eq_nil permutation)

/-! ## The canonical form is sound -/

variable (decl) in
/-- A composition of the given processes. -/
abbrev prod (items : List Pattern) : Pattern := .collection decl.product items none

variable (decl) in
/-- A sum of compositions of the given processes. -/
abbrev sumForm (products : List (List Pattern)) : Pattern := .collection decl.sum (products.map (prod decl)) none

theorem atoms_cases (summand : Pattern) :
    (summand = .apply decl.unit [] ∧ atoms decl summand = []) ∨
      (∃ elements, summand = .collection decl.product elements none ∧ atoms decl summand = elements) ∨
      atoms decl summand = [summand] := by
  unfold atoms
  split
  · rename_i label
    split
    · rename_i unit; subst unit; exact .inl ⟨rfl, rfl⟩
    · exact .inr (.inr rfl)
  · rename_i kind elements
    split
    · rename_i same; subst same; exact .inr (.inl ⟨elements, rfl, rfl⟩)
    · exact .inr (.inr rfl)
  · exact .inr (.inr rfl)

theorem atoms_plain {summand : Pattern} (isPlain : plain decl summand = true) :
    ∀ atom ∈ atoms decl summand, plain decl atom = true := by
  rcases atoms_cases (decl := decl) summand with ⟨_, found⟩ | ⟨elements, rfl, found⟩ | found
  · rw [found]; simp
  · rw [found]; exact (plain_collection isPlain).2.2
  · rw [found]; simpa using isPlain

/-- A summand's atoms compose to it. -/
theorem atoms_sound (valid : decl.Valid) {before after : List Pattern}
    (around : ∀ item ∈ before ++ after, plain decl item = true) {summand : Pattern}
    (summandPlain : plain decl summand = true) :
    Congruent decl (prod decl (before ++ summand :: after)) (prod decl (before ++ atoms decl summand ++ after)) := by
  rcases atoms_cases (decl := decl) summand with ⟨rfl, found⟩ | ⟨elements, rfl, found⟩ | found
  · rw [found]; simpa using unitProduct valid around
  · rw [found]; exact flattenProduct valid around (plain_collection summandPlain).2.2
  · rw [found]; simpa using Relation.EqvGen.refl (r := MoveOn decl) (prod decl (before ++ summand :: after))

theorem summand_sound (valid : decl.Valid) {summand : Pattern} (summandPlain : plain decl summand = true) :
    Congruent decl summand (prod decl (atoms decl summand)) := by
  have composed := atoms_sound valid (before := []) (after := []) (by simp) summandPlain
  simp only [List.nil_append, List.append_nil] at composed
  exact .trans _ _ _ (.symm _ _ (singletonProduct valid summandPlain)) composed

theorem products_none {item : Pattern} : products decl item = none ↔ item = .apply decl.absorbing [] := by
  constructor
  · intro found
    unfold products at found
    split at found
    · rename_i label
      split at found
      · rename_i absorbing; subst absorbing; rfl
      · split at found <;> cases found
    · split at found
      · cases found
      · split at found <;> cases found
    · cases found
  · rintro rfl
    simp [products]

theorem products_cases {item : Pattern} {ps : List (List Pattern)} (found : products decl item = some ps) :
    (item = .apply decl.unit [] ∧ ps = [[]]) ∨
      (∃ summands, item = .collection decl.sum summands none ∧ ps = summands.map (atoms decl)) ∨
      (∃ elements, item = .collection decl.product elements none ∧ ps = [elements]) ∨
      ps = [[item]] := by
  unfold products at found
  split at found
  · rename_i label
    split at found
    · cases found
    · split at found
      · rename_i _ unit; subst unit; cases found; exact .inl ⟨rfl, rfl⟩
      · cases found; exact .inr (.inr (.inr rfl))
  · rename_i kind elements
    split at found
    · rename_i same; subst same; cases found; exact .inr (.inl ⟨elements, rfl, rfl⟩)
    · split at found
      · rename_i _ same; subst same; cases found; exact .inr (.inr (.inl ⟨elements, rfl, rfl⟩))
      · cases found; exact .inr (.inr (.inr rfl))
  · cases found; exact .inr (.inr (.inr rfl))

theorem products_plain {item : Pattern} {ps : List (List Pattern)} (found : products decl item = some ps)
    (isPlain : plain decl item = true) : ∀ chosen ∈ ps, ∀ atom ∈ chosen, plain decl atom = true := by
  rcases products_cases found with ⟨rfl, rfl⟩ | ⟨summands, rfl, rfl⟩ | ⟨elements, rfl, rfl⟩ | rfl
  · simp
  · intro chosen member atom inChosen
    obtain ⟨summand, summandMember, rfl⟩ := List.mem_map.mp member
    exact atoms_plain ((plain_collection isPlain).2.2 summand summandMember) atom inChosen
  · intro chosen member atom inChosen
    simp only [List.mem_singleton] at member
    subst member
    exact (plain_collection isPlain).2.2 atom inChosen
  · intro chosen member atom inChosen
    simp only [List.mem_singleton] at member inChosen ⊢
    subst member
    simp only [List.mem_singleton] at inChosen
    subst inChosen
    exact isPlain

theorem products_ne_nil {item : Pattern} {ps : List (List Pattern)} (found : products decl item = some ps)
    (notEmpty : item ≠ .collection decl.sum [] none) : ps ≠ [] := by
  rcases products_cases found with ⟨_, rfl⟩ | ⟨summands, rfl, rfl⟩ | ⟨_, _, rfl⟩ | rfl
  · simp
  · intro empty
    exact notEmpty (by simpa using empty)
  · simp
  · simp

/-- A process is not the empty sum. -/
theorem ne_empty_of_plain {item : Pattern} (isPlain : plain decl item = true) : item ≠ .collection decl.sum [] none := by
  rintro rfl
  exact (plain_collection isPlain).2.1 rfl rfl

theorem choices_ne_nil : ∀ {factors : List (List (List Pattern))}, (∀ factor ∈ factors, factor ≠ []) → choices factors ≠ []
  | [], _ => by simp [choices]
  | factor :: factors, nonempty => by
    obtain ⟨chosen, member⟩ := List.exists_mem_of_ne_nil factor (nonempty factor (by simp))
    obtain ⟨rest, restMember⟩ := List.exists_mem_of_ne_nil _ (choices_ne_nil (factors := factors)
      (fun other inOthers => nonempty other (List.mem_cons_of_mem _ inOthers)))
    intro empty
    have : chosen ++ rest ∈ choices (factor :: factors) := by
      simp only [choices, List.mem_flatMap, List.mem_map]
      exact ⟨chosen, member, rest, restMember, rfl⟩
    rw [empty] at this
    simp at this

theorem choices_plain : ∀ {factors : List (List (List Pattern))},
    (∀ factor ∈ factors, ∀ chosen ∈ factor, ∀ atom ∈ chosen, plain decl atom = true) →
      ∀ chosen ∈ choices factors, ∀ atom ∈ chosen, plain decl atom = true
  | [], _ => by simp [choices]
  | factor :: factors, each => by
    intro chosen member atom inChosen
    simp only [choices, List.mem_flatMap, List.mem_map] at member
    obtain ⟨first, firstMember, rest, restMember, rfl⟩ := member
    rcases List.mem_append.mp inChosen with inFirst | inRest
    · exact each factor List.mem_cons_self first firstMember atom inFirst
    · exact choices_plain (factors := factors) (fun other inOthers => each other (List.mem_cons_of_mem _ inOthers))
        rest restMember atom inRest

theorem plain_productOf (valid : decl.Valid) {chosen : List Pattern} (atomsPlain : ∀ atom ∈ chosen, plain decl atom = true) :
    plain decl (productOf decl chosen) = true := by
  have sorted := sortLex_perm chosen
  unfold productOf
  split
  · exact plain_constant _
  · rename_i atom single
    rw [single] at sorted
    exact atomsPlain atom (sorted.subset (by simp))
  · exact plain_product valid fun atom member => atomsPlain atom (sorted.subset member)

theorem plain_sumOf (valid : decl.Valid) {cs : List (List Pattern)} (nonempty : cs ≠ [])
    (atomsPlain : ∀ chosen ∈ cs, ∀ atom ∈ chosen, plain decl atom = true) : plain decl (sumOf decl cs) = true := by
  have memL : ∀ p, p ∈ sortLex (cs.map (productOf decl)).dedup ↔ ∃ c ∈ cs, productOf decl c = p := by
    intro p
    rw [(sortLex_perm _).mem_iff, List.mem_dedup, List.mem_map]
  have eachPlain : ∀ p ∈ sortLex (cs.map (productOf decl)).dedup, plain decl p = true := by
    intro p member
    obtain ⟨c, cMember, rfl⟩ := (memL p).mp member
    exact plain_productOf valid (atomsPlain c cMember)
  have Lnonempty : sortLex (cs.map (productOf decl)).dedup ≠ [] := by
    obtain ⟨c, cMember⟩ := List.exists_mem_of_ne_nil cs nonempty
    intro empty
    have inL := (memL (productOf decl c)).mpr ⟨c, cMember, rfl⟩
    rw [empty] at inL
    simp at inL
  unfold sumOf
  revert eachPlain Lnonempty
  generalize sortLex (cs.map (productOf decl)).dedup = sorted
  intro eachPlain Lnonempty
  match sorted, Lnonempty, eachPlain with
  | [p], _, eachPlain => exact eachPlain p (by simp)
  | p₁ :: p₂ :: rest, _, eachPlain => exact plain_sum (by simp) eachPlain

/-- A composition of atoms is a process. -/
theorem plain_prod (valid : decl.Valid) {chosen : List Pattern} (atomsPlain : ∀ atom ∈ chosen, plain decl atom = true) :
    plain decl (prod decl chosen) = true :=
  plain_product valid atomsPlain

/-- A sum of compositions of atoms, with a summand, is a process. -/
theorem plain_sumForm (valid : decl.Valid) {cs : List (List Pattern)} (nonempty : cs ≠ [])
    (atomsPlain : ∀ chosen ∈ cs, ∀ atom ∈ chosen, plain decl atom = true) : plain decl (sumForm decl cs) = true :=
  plain_sum (by simpa using nonempty) fun item member => by
    obtain ⟨chosen, chosenMember, rfl⟩ := List.mem_map.mp member
    exact plain_prod valid (atomsPlain chosen chosenMember)

/-- **One factor multiplied out**: a composition holding a process is the sum of the compositions
holding, instead, each of its products. -/
theorem products_sound (valid : decl.Valid) {before after : List Pattern}
    (around : ∀ item ∈ before ++ after, plain decl item = true) {item : Pattern} {ps : List (List Pattern)}
    (itemPlain : plain decl item = true) (found : products decl item = some ps) :
    Congruent decl (prod decl (before ++ item :: after)) (sumForm decl (ps.map fun chosen => before ++ chosen ++ after)) := by
  have aroundAt : ∀ chosen : List Pattern, (∀ atom ∈ chosen, plain decl atom = true) →
      ∀ atom ∈ before ++ chosen ++ after, plain decl atom = true := fun chosen chosenPlain atom member => by
    rcases List.mem_append.mp member with inFirst | inAfter
    · rcases List.mem_append.mp inFirst with inBefore | inChosen
      · exact around atom (List.mem_append_left _ inBefore)
      · exact chosenPlain atom inChosen
    · exact around atom (List.mem_append_right _ inAfter)
  rcases products_cases found with ⟨rfl, rfl⟩ | ⟨summands, rfl, rfl⟩ | ⟨elements, rfl, rfl⟩ | rfl
  · have removed := unitProduct valid around
    have wrapped := singletonSum valid (plain_prod valid around)
    simp only [List.map_cons, List.map_nil, sumForm, List.append_nil] at removed wrapped ⊢
    exact .trans _ _ _ removed (.symm _ _ wrapped)
  · obtain ⟨_, nonempty, summandsPlain⟩ := plain_collection itemPlain
    match summands, nonempty, summandsPlain with
    | [], nonempty, _ => exact absurd rfl (nonempty rfl)
    | [summand], _, summandsPlain =>
      have summandPlain := summandsPlain summand List.mem_cons_self
      have collapsed := Congruent.element decl.product around (singletonSum valid summandPlain)
      have spread := atoms_sound valid around summandPlain
      have wrapped := singletonSum valid (plain_prod valid (aroundAt _ (atoms_plain summandPlain)))
      simp only [List.map_cons, List.map_nil, sumForm, List.append_assoc] at collapsed spread wrapped ⊢
      exact .trans _ _ _ collapsed (.trans _ _ _ spread (.symm _ _ wrapped))
    | first :: second :: others, _, summandsPlain =>
      have distributed : Congruent decl
          (prod decl (before ++ .collection decl.sum (first :: second :: others) none :: after))
          (.collection decl.sum ((first :: second :: others).map fun summand => prod decl (before ++ summand :: after)) none) :=
        .rel _ _ ⟨plain_prod valid (forall_around around itemPlain),
          plain_sum (by simp) fun product member => by
            obtain ⟨summand, summandMember, rfl⟩ := List.mem_map.mp member
            exact plain_prod valid (forall_around around (summandsPlain summand summandMember)),
          .inr (.inr (.distribute (by simp)))⟩
      refine .trans _ _ _ distributed ?_
      have moved := Congruent.mapPointwise (decl := decl) decl.sum
        (fun summand => prod decl (before ++ summand :: after))
        (fun summand => prod decl (before ++ atoms decl summand ++ after)) [] (first :: second :: others) (by simp)
        (fun summand member => ⟨plain_prod valid (forall_around around (summandsPlain summand member)),
          plain_prod valid (aroundAt _ (atoms_plain (summandsPlain summand member)))⟩)
        (fun summand member => atoms_sound valid around (summandsPlain summand member))
      simpa [sumForm, List.map_map, Function.comp_def] using moved
  · have flat := flattenProduct valid around (plain_collection itemPlain).2.2
    have wrapped := singletonSum valid (plain_prod valid (aroundAt _ (plain_collection itemPlain).2.2))
    simp only [List.map_cons, List.map_nil, sumForm, List.append_assoc] at flat wrapped ⊢
    exact .trans _ _ _ flat (.symm _ _ wrapped)
  · have wrapped := singletonSum valid (plain_prod valid (forall_around around itemPlain))
    simp only [List.map_cons, List.map_nil, sumForm, List.append_assoc, List.singleton_append] at wrapped ⊢
    exact .symm _ _ wrapped

/-- Sums of sums of compositions flatten. -/
theorem flattenSums (valid : decl.Valid) :
    ∀ (before : List Pattern) (groups : List (List (List Pattern))) (after : List Pattern),
      (∀ item ∈ before ++ after, plain decl item = true) →
      (∀ group ∈ groups, group ≠ [] ∧ ∀ chosen ∈ group, ∀ atom ∈ chosen, plain decl atom = true) →
      Congruent decl (.collection decl.sum (before ++ groups.map (sumForm decl) ++ after) none)
        (.collection decl.sum (before ++ groups.flatten.map (prod decl) ++ after) none)
  | before, [], after, _, _ => by simpa using Relation.EqvGen.refl (r := MoveOn decl) _
  | before, group :: groups, after, around, each => by
    obtain ⟨groupNonempty, groupPlain⟩ := each group List.mem_cons_self
    have prodsPlain : ∀ item ∈ group.map (prod decl), plain decl item = true := fun item member => by
      obtain ⟨chosen, chosenMember, rfl⟩ := List.mem_map.mp member
      exact plain_prod valid (groupPlain chosen chosenMember)
    have restPlain : ∀ item ∈ groups.map (sumForm decl) ++ after, plain decl item = true := fun item member => by
      rcases List.mem_append.mp member with inGroups | inAfter
      · obtain ⟨other, otherMember, rfl⟩ := List.mem_map.mp inGroups
        obtain ⟨otherNonempty, otherPlain⟩ := each other (List.mem_cons_of_mem _ otherMember)
        exact plain_sumForm valid otherNonempty otherPlain
      · exact around item (List.mem_append_right _ inAfter)
    have flat := flattenSum valid (before := before) (inner := group.map (prod decl))
      (after := groups.map (sumForm decl) ++ after) (by simpa using groupNonempty)
      (fun item member => by
        rcases List.mem_append.mp member with inBefore | inRest
        · exact around item (List.mem_append_left _ inBefore)
        · exact restPlain item inRest)
      prodsPlain
    have later := flattenSums valid (before ++ group.map (prod decl)) groups after
      (fun item member => by
        rcases List.mem_append.mp member with inFirst | inAfter
        · rcases List.mem_append.mp inFirst with inBefore | inProds
          · exact around item (List.mem_append_left _ inBefore)
          · exact prodsPlain item inProds
        · exact around item (List.mem_append_right _ inAfter))
      (fun other member => each other (List.mem_cons_of_mem _ member))
    simp only [List.map_cons, List.flatten_cons, List.map_append, List.append_assoc, List.cons_append] at flat later ⊢
    exact .trans _ _ _ flat later

theorem mapM_none {α : Type} {f : Pattern → Option α} :
    ∀ {items : List Pattern}, items.mapM f = none → ∃ item ∈ items, f item = none
  | [], found => by simp at found
  | item :: items, found => by
    cases here : f item with
    | none => exact ⟨item, by simp, here⟩
    | some value =>
      cases later : items.mapM f with
      | none =>
        obtain ⟨other, member, missing⟩ := mapM_none later
        exact ⟨other, by simp [member], missing⟩
      | some values => simp [List.mapM_cons, here, later] at found

theorem mapM_cons_some {α : Type} {f : Pattern → Option α} {item : Pattern} {items : List Pattern}
    {values : List α} (found : (item :: items).mapM f = some values) :
    ∃ value rest, f item = some value ∧ items.mapM f = some rest ∧ values = value :: rest := by
  cases here : f item with
  | none => simp [List.mapM_cons, here] at found
  | some value =>
    cases later : items.mapM f with
    | none => simp [List.mapM_cons, here, later] at found
    | some rest =>
      simp only [List.mapM_cons, here, later, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq] at found
      exact ⟨value, rest, rfl, rfl, found.symm⟩

theorem mapM_mem {α : Type} {f : Pattern → Option α} :
    ∀ {items : List Pattern} {values : List α}, items.mapM f = some values → ∀ value ∈ values, ∃ item ∈ items, f item = some value
  | [], values, found => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at found
    subst found; simp
  | item :: items, values, found => by
    obtain ⟨first, rest, here, later, rfl⟩ := mapM_cons_some found
    intro value member
    rcases List.mem_cons.mp member with rfl | inRest
    · exact ⟨item, by simp, here⟩
    · obtain ⟨other, otherMember, otherFound⟩ := mapM_mem later value inRest
      exact ⟨other, by simp [otherMember], otherFound⟩

/-- **A composition multiplied out**: a composition is the sum of the compositions of one product of
each factor. -/
theorem multiply_out (valid : decl.Valid) : ∀ (items : List Pattern) {factors : List (List (List Pattern))},
    (∀ item ∈ items, plain decl item = true) → items.mapM (products decl) = some factors →
      ∀ (pre : List Pattern), (∀ atom ∈ pre, plain decl atom = true) →
        Congruent decl (prod decl (pre ++ items)) (sumForm decl ((choices factors).map (pre ++ ·)))
  | [], factors, _, found, pre, prePlain => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at found
    subst found
    have wrapped := singletonSum valid (plain_prod valid prePlain)
    simp only [choices, List.map_cons, List.map_nil, List.append_nil, sumForm] at wrapped ⊢
    exact .symm _ _ wrapped
  | item :: items, factors, itemsPlain, found, pre, prePlain => by
    obtain ⟨ps, fs, here, later, rfl⟩ := mapM_cons_some found
    have itemPlain := itemsPlain item List.mem_cons_self
    have restPlain : ∀ other ∈ items, plain decl other = true := fun other member =>
      itemsPlain other (List.mem_cons_of_mem _ member)
    have psPlain := products_plain here itemPlain
    have fsNonempty : ∀ factor ∈ fs, factor ≠ [] := fun factor member => by
      obtain ⟨other, otherMember, otherFound⟩ := mapM_mem later factor member
      exact products_ne_nil otherFound (ne_empty_of_plain (restPlain other otherMember))
    have fsPlain : ∀ factor ∈ fs, ∀ chosen ∈ factor, ∀ atom ∈ chosen, plain decl atom = true := fun factor member => by
      obtain ⟨other, otherMember, otherFound⟩ := mapM_mem later factor member
      exact products_plain otherFound (restPlain other otherMember)
    have preChosen : ∀ chosen ∈ ps, ∀ atom ∈ pre ++ chosen, plain decl atom = true := fun chosen member atom inAtom => by
      rcases List.mem_append.mp inAtom with inPre | inChosen
      · exact prePlain atom inPre
      · exact psPlain chosen member atom inChosen
    have first := products_sound valid (before := pre) (after := items)
      (fun other member => by
        rcases List.mem_append.mp member with inPre | inItems
        · exact prePlain other inPre
        · exact restPlain other inItems)
      itemPlain here
    have moved := Congruent.mapPointwise (decl := decl) decl.sum
      (fun chosen => prod decl (pre ++ chosen ++ items))
      (fun chosen => sumForm decl ((choices fs).map ((pre ++ chosen) ++ ·))) [] ps (by simp)
      (fun chosen member => ⟨plain_prod valid fun atom inAtom => by
          rcases List.mem_append.mp inAtom with inFirst | inItems
          · exact preChosen chosen member atom inFirst
          · exact restPlain atom inItems,
        plain_sumForm valid (by simpa using choices_ne_nil fsNonempty) fun combined combinedMember atom inAtom => by
          obtain ⟨rest, restMember, rfl⟩ := List.mem_map.mp combinedMember
          rcases List.mem_append.mp inAtom with inFirst | inRest
          · exact preChosen chosen member atom inFirst
          · exact choices_plain fsPlain rest restMember atom inRest⟩)
      (fun chosen member => by
        simpa [List.append_assoc] using multiply_out valid items restPlain later (pre ++ chosen)
          (preChosen chosen member))
    have flat := flattenSums valid [] (ps.map fun chosen => (choices fs).map ((pre ++ chosen) ++ ·)) [] (by simp)
      (fun group member => by
        obtain ⟨chosen, chosenMember, rfl⟩ := List.mem_map.mp member
        refine ⟨by simpa using choices_ne_nil fsNonempty, fun combined combinedMember atom inAtom => ?_⟩
        obtain ⟨rest, restMember, rfl⟩ := List.mem_map.mp combinedMember
        rcases List.mem_append.mp inAtom with inFirst | inRest
        · exact preChosen chosen chosenMember atom inFirst
        · exact choices_plain fsPlain rest restMember atom inRest)
    have shape : (choices (ps :: fs)).map (pre ++ ·) =
        (ps.map fun chosen => (choices fs).map ((pre ++ chosen) ++ ·)).flatten := by
      simp [choices, List.flatMap, List.map_flatten, List.map_map, Function.comp_def, List.append_assoc]
    rw [shape]
    simp only [List.nil_append, List.append_nil, List.map_map, Function.comp_def, sumForm] at first moved flat ⊢
    exact .trans _ _ _ first (.trans _ _ _ moved flat)

/-- A composition is its canonical product. -/
theorem prod_productOf (valid : decl.Valid) {items : List Pattern} (each : ∀ item ∈ items, plain decl item = true) :
    Congruent decl (prod decl items) (productOf decl items) := by
  have sorted := permute (decl := decl) valid.productUnordered (sortLex_perm items).symm (plain_prod valid each)
  refine .trans _ _ _ sorted ?_
  have inItems : ∀ item ∈ sortLex items, item ∈ items := fun item member => (sortLex_perm items).subset member
  unfold productOf
  split
  · rename_i empty; rw [empty]; exact emptyProduct valid
  · rename_i atom single
    rw [single]
    exact singletonProduct valid (each atom (inItems atom (by rw [single]; simp)))
  · exact .refl _

/-- A repeated summand goes. -/
theorem dedupSum (valid : decl.Valid) : ∀ (before items : List Pattern),
    (∀ item ∈ before ++ items, plain decl item = true) →
    Congruent decl (.collection decl.sum (before ++ items) none) (.collection decl.sum (before ++ items.dedup) none)
  | before, [], _ => by simpa using Relation.EqvGen.refl (r := MoveOn decl) _
  | before, item :: items, each => by
    have itemPlain := each item (by simp)
    by_cases member : item ∈ items
    · rw [List.dedup_cons_of_mem member]
      obtain ⟨middle, after, split⟩ := List.append_of_mem member
      have shortPlain : ∀ other ∈ before ++ items, plain decl other = true := fun other inOther => by
        rcases List.mem_append.mp inOther with inBefore | inItems
        · exact each other (List.mem_append_left _ inBefore)
        · exact each other (List.mem_append_right _ (List.mem_cons_of_mem _ inItems))
      rw [split] at shortPlain
      have longPlain : ∀ other ∈ before ++ item :: middle ++ item :: after, plain decl other = true :=
        fun other inOther => by
          rcases List.mem_append.mp inOther with inFirst | inLast
          · rcases List.mem_append.mp inFirst with inBefore | inMiddle
            · exact shortPlain other (List.mem_append_left _ inBefore)
            · rcases List.mem_cons.mp inMiddle with rfl | inMiddle
              · exact itemPlain
              · exact shortPlain other (List.mem_append_right _ (List.mem_append_left _ inMiddle))
          · rcases List.mem_cons.mp inLast with rfl | inAfter
            · exact itemPlain
            · exact shortPlain other (List.mem_append_right _ (List.mem_append_right _ (List.mem_cons_of_mem _ inAfter)))
      have removedPlain : ∀ other ∈ before ++ item :: middle ++ after, plain decl other = true := fun other inOther => by
        rcases List.mem_append.mp inOther with inFirst | inAfter
        · exact longPlain other (List.mem_append_left _ inFirst)
        · exact longPlain other (List.mem_append_right _ (List.mem_cons_of_mem _ inAfter))
      have removed : Congruent decl (.collection decl.sum (before ++ item :: middle ++ item :: after) none)
          (.collection decl.sum (before ++ item :: middle ++ after) none) :=
        .rel _ _ ⟨plain_sum (by simp) longPlain, plain_sum (by simp) removedPlain, .inr (.inr .repeated)⟩
      have permuted := permute (decl := decl) valid.sumUnordered
        (List.Perm.append_left before (List.perm_middle (a := item) (l₁ := middle) (l₂ := after)).symm)
        (plain_sum (by simp) (by simpa only [List.append_assoc, List.cons_append] using removedPlain))
      have later := dedupSum valid before items (by rw [split]; exact shortPlain)
      rw [split] at later ⊢
      simp only [List.append_assoc, List.cons_append] at removed permuted later ⊢
      exact .trans _ _ _ removed (.trans _ _ _ permuted later)
    · rw [List.dedup_cons_of_notMem member]
      have later := dedupSum valid (before ++ [item]) items (by simpa using each)
      simpa using later

/-- A sum of compositions is its canonical sum. -/
theorem sumForm_sumOf (valid : decl.Valid) {products' : List (List Pattern)} (nonempty : products' ≠ [])
    (each : ∀ chosen ∈ products', ∀ atom ∈ chosen, plain decl atom = true) :
    Congruent decl (sumForm decl products') (sumOf decl products') := by
  have canonicalPlain : ∀ item ∈ products'.map (productOf decl), plain decl item = true := fun item member => by
    obtain ⟨chosen, chosenMember, rfl⟩ := List.mem_map.mp member
    exact plain_productOf valid (each chosen chosenMember)
  have canonical := Congruent.mapPointwise (decl := decl) decl.sum (prod decl) (productOf decl) [] products' (by simp)
    (fun chosen member => ⟨plain_prod valid (each chosen member), plain_productOf valid (each chosen member)⟩)
    (fun chosen member => prod_productOf valid (each chosen member))
  have deduped := dedupSum (decl := decl) valid [] (products'.map (productOf decl)) (by simpa using canonicalPlain)
  have dedupNonempty : (products'.map (productOf decl)).dedup ≠ [] := by
    obtain ⟨chosen, chosenMember⟩ := List.exists_mem_of_ne_nil products' nonempty
    intro empty
    have inDedup : productOf decl chosen ∈ (products'.map (productOf decl)).dedup :=
      List.mem_dedup.mpr (List.mem_map.mpr ⟨chosen, chosenMember, rfl⟩)
    rw [empty] at inDedup
    simp at inDedup
  have sorted := permute (decl := decl) valid.sumUnordered (sortLex_perm (products'.map (productOf decl)).dedup).symm
    (plain_sum dedupNonempty fun item member => canonicalPlain item (List.mem_dedup.mp member))
  simp only [List.nil_append] at canonical deduped
  refine .trans _ _ _ canonical (.trans _ _ _ deduped (.trans _ _ _ sorted ?_))
  unfold sumOf
  split
  · rename_i empty; rw [empty]; exact .refl _
  · rename_i single heq
    rw [heq]
    exact singletonSum valid (canonicalPlain single (List.mem_dedup.mp
      ((sortLex_perm _).subset (by rw [heq]; simp))))
  · exact .refl _

/-- **A composition is its canonical form.** -/
theorem multiply_sound (valid : decl.Valid) {items : List Pattern} (each : ∀ item ∈ items, plain decl item = true) :
    Congruent decl (prod decl items) (multiply decl items) := by
  unfold multiply
  cases found : items.mapM (products decl) with
  | none =>
    obtain ⟨item, member, absorbing⟩ := mapM_none found
    rw [products_none] at absorbing
    subst absorbing
    obtain ⟨before, after, rfl⟩ := List.append_of_mem member
    exact .rel _ _ ⟨plain_prod valid each, plain_constant _, .inr (.inr .absorbProduct)⟩
  | some factors =>
    have out := multiply_out valid items each found [] (by simp)
    simp only [List.nil_append, List.map_id'] at out
    have factorsNonempty : ∀ factor ∈ factors, factor ≠ [] := fun factor member => by
      obtain ⟨item, itemMember, itemFound⟩ := mapM_mem found factor member
      exact products_ne_nil itemFound (ne_empty_of_plain (each item itemMember))
    have factorsPlain : ∀ factor ∈ factors, ∀ chosen ∈ factor, ∀ atom ∈ chosen, plain decl atom = true :=
      fun factor member => by
        obtain ⟨item, itemMember, itemFound⟩ := mapM_mem found factor member
        exact products_plain itemFound (each item itemMember)
    exact .trans _ _ _ out (sumForm_sumOf valid (choices_ne_nil factorsNonempty) (choices_plain factorsPlain))

/-- A summand of a sum is the sum of its products. -/
theorem summands_sound (valid : decl.Valid) {item : Pattern} {ps : List (List Pattern)}
    (itemPlain : plain decl item = true) (found : products decl item = some ps) : Congruent decl item (sumForm decl ps) := by
  rcases products_cases found with ⟨rfl, rfl⟩ | ⟨summands, rfl, rfl⟩ | ⟨elements, rfl, rfl⟩ | rfl
  · have wrapped := singletonSum valid (plain_prod valid (chosen := []) (by simp))
    simp only [List.map_cons, List.map_nil, sumForm] at wrapped ⊢
    exact .trans _ _ _ (.symm _ _ (emptyProduct valid)) (.symm _ _ wrapped)
  · have summandsPlain := (plain_collection itemPlain).2.2
    have moved := Congruent.mapPointwise (decl := decl) decl.sum (fun summand => summand)
      (fun summand => prod decl (atoms decl summand)) [] summands (by simp)
      (fun summand member => ⟨summandsPlain summand member, plain_prod valid (atoms_plain (summandsPlain summand member))⟩)
      (fun summand member => summand_sound valid (summandsPlain summand member))
    simpa [sumForm, List.map_map, Function.comp_def] using moved
  · have wrapped := singletonSum valid itemPlain
    simp only [List.map_cons, List.map_nil, sumForm] at wrapped ⊢
    exact .symm _ _ wrapped
  · have wrapped := singletonSum valid (plain_prod valid (chosen := [item]) (by simpa using itemPlain))
    simp only [List.map_cons, List.map_nil, sumForm] at wrapped ⊢
    exact .trans _ _ _ (.symm _ _ (singletonProduct valid itemPlain)) (.symm _ _ wrapped)

/-- A sum is the sum of the products of its summands. -/
theorem add_out (valid : decl.Valid) : ∀ (items : List Pattern) {parts : List (List (List Pattern))},
    (∀ item ∈ items, plain decl item = true) → items.mapM (products decl) = some parts →
      ∀ (before : List Pattern), (∀ item ∈ before, plain decl item = true) →
        Congruent decl (.collection decl.sum (before ++ items) none)
          (.collection decl.sum (before ++ parts.flatten.map (prod decl)) none)
  | [], parts, _, found, before, _ => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at found
    subst found
    simpa using Relation.EqvGen.refl (r := MoveOn decl) _
  | item :: items, parts, itemsPlain, found, before, beforePlain => by
    obtain ⟨ps, qs, here, later, rfl⟩ := mapM_cons_some found
    have itemPlain := itemsPlain item List.mem_cons_self
    have restPlain : ∀ other ∈ items, plain decl other = true := fun other member =>
      itemsPlain other (List.mem_cons_of_mem _ member)
    have psPlain := products_plain here itemPlain
    have prodsPlain : ∀ other ∈ ps.map (prod decl), plain decl other = true := fun other member => by
      obtain ⟨chosen, chosenMember, rfl⟩ := List.mem_map.mp member
      exact plain_prod valid (psPlain chosen chosenMember)
    have around : ∀ other ∈ before ++ items, plain decl other = true := fun other member => by
      rcases List.mem_append.mp member with inBefore | inItems
      · exact beforePlain other inBefore
      · exact restPlain other inItems
    have expanded := Congruent.element decl.sum around (summands_sound valid itemPlain here)
    have flat := flattenSum valid (before := before) (inner := ps.map (prod decl)) (after := items)
      (by simpa using products_ne_nil here (ne_empty_of_plain itemPlain)) around prodsPlain
    have rest := add_out valid items restPlain later (before ++ ps.map (prod decl)) (fun other member => by
      rcases List.mem_append.mp member with inBefore | inProds
      · exact beforePlain other inBefore
      · exact prodsPlain other inProds)
    simp only [List.flatten_cons, List.map_append, List.append_assoc, sumForm] at expanded flat rest ⊢
    exact .trans _ _ _ expanded (.trans _ _ _ flat rest)

/-- **A sum is its canonical form.** -/
theorem add_sound (valid : decl.Valid) {items : List Pattern} (nonempty : items ≠ [])
    (each : ∀ item ∈ items, plain decl item = true) :
    Congruent decl (.collection decl.sum items none) (add decl items) := by
  unfold add
  cases found : items.mapM (products decl) with
  | none =>
    obtain ⟨item, member, absorbing⟩ := mapM_none found
    rw [products_none] at absorbing
    subst absorbing
    obtain ⟨before, after, rfl⟩ := List.append_of_mem member
    exact .rel _ _ ⟨plain_sum nonempty each, plain_constant _, .inr (.inr .absorbSum)⟩
  | some parts =>
    have out := add_out valid items each found [] (by simp)
    simp only [List.nil_append] at out
    have partsPlain : ∀ chosen ∈ parts.flatten, ∀ atom ∈ chosen, plain decl atom = true := fun chosen member => by
      obtain ⟨part, partMember, chosenMember⟩ := List.mem_flatten.mp member
      obtain ⟨item, itemMember, itemFound⟩ := mapM_mem found part partMember
      exact products_plain itemFound (each item itemMember) chosen chosenMember
    have partsNonempty : parts.flatten ≠ [] := by
      obtain ⟨first, others, shape⟩ := List.exists_cons_of_ne_nil nonempty
      subst shape
      obtain ⟨part, rest, partFound, _, rfl⟩ := mapM_cons_some found
      obtain ⟨chosen, chosenMember⟩ := List.exists_mem_of_ne_nil part
        (products_ne_nil partFound (ne_empty_of_plain (each first List.mem_cons_self)))
      intro empty
      have inFlat : chosen ∈ (part :: rest).flatten := List.mem_flatten.mpr ⟨part, List.mem_cons_self, chosenMember⟩
      rw [empty] at inFlat
      simp at inFlat
    exact .trans _ _ _ out (sumForm_sumOf valid partsNonempty partsPlain)

/-! ## The free algebra

A canonical form denotes a finite set of finite multisets of atoms, or the absorbing element: the free
algebra of the composite monad. Composition multiplies pointwise and summation is union. -/

open scoped Pointwise

variable (decl) in
/-- A pattern that can be an atom of a product: not the absorbing element, not the unit, neither a
composition nor a sum. -/
def IsAtom (atom : Pattern) : Prop :=
  atom ≠ .apply decl.absorbing [] ∧ atom ≠ .apply decl.unit [] ∧
    (∀ elements, atom ≠ .collection decl.product elements none) ∧ (∀ elements, atom ≠ .collection decl.sum elements none)

variable (decl) in
/-- Products of atoms. -/
def Atoms (products : List (List Pattern)) : Prop := ∀ chosen ∈ products, ∀ atom ∈ chosen, IsAtom decl atom

/-- The presented products, as a set of multisets. -/
def presented (products : List (List Pattern)) : Finset (Multiset Pattern) :=
  (products.map fun chosen => (chosen : Multiset Pattern)).toFinset

theorem mem_presented {products : List (List Pattern)} {bag : Multiset Pattern} :
    bag ∈ presented products ↔ ∃ chosen ∈ products, (chosen : Multiset Pattern) = bag := by
  simp [presented, eq_comm]

theorem productOf_eq {left right : List Pattern} (same : (left : Multiset Pattern) = right) :
    productOf decl left = productOf decl right := by
  unfold productOf
  rw [sortLex_eq_of_perm (Multiset.coe_eq_coe.mp same)]

/-- **A canonical sum depends only on its presented products.** -/
theorem sumOf_eq {left right : List (List Pattern)} (same : presented left = presented right) :
    sumOf decl left = sumOf decl right := by
  have permuted : ((left.map (productOf decl)).dedup).Perm ((right.map (productOf decl)).dedup) := by
    rw [List.perm_ext_iff_of_nodup (List.nodup_dedup _) (List.nodup_dedup _)]
    intro product
    simp only [List.mem_dedup, List.mem_map]
    constructor
    · rintro ⟨chosen, member, rfl⟩
      have inRight : (chosen : Multiset Pattern) ∈ presented right := by
        rw [← same]; exact mem_presented.mpr ⟨chosen, member, rfl⟩
      obtain ⟨other, otherMember, sameBag⟩ := mem_presented.mp inRight
      exact ⟨other, otherMember, productOf_eq sameBag⟩
    · rintro ⟨chosen, member, rfl⟩
      have inLeft : (chosen : Multiset Pattern) ∈ presented left := by
        rw [same]; exact mem_presented.mpr ⟨chosen, member, rfl⟩
      obtain ⟨other, otherMember, sameBag⟩ := mem_presented.mp inLeft
      exact ⟨other, otherMember, productOf_eq sameBag⟩
  unfold sumOf
  rw [sortLex_eq_of_perm permuted]

theorem atoms_atom {atom : Pattern} (isAtom : IsAtom decl atom) : atoms decl atom = [atom] := by
  obtain ⟨_, notUnit, notProduct, _⟩ := isAtom
  match atom, notUnit, notProduct with
  | .apply label [], notUnit, _ =>
    have different : label ≠ decl.unit := fun same => notUnit (by rw [same])
    simp [atoms, different]
  | .collection kind elements none, _, notProduct =>
    have different : kind ≠ decl.product := fun same => notProduct elements (by rw [same])
    simp [atoms, different]
  | .apply _ (_ :: _), _, _ => simp [atoms]
  | .collection _ _ (some _), _, _ => simp [atoms]
  | .bvar _, _, _ => simp [atoms]
  | .fvar _, _, _ => simp [atoms]
  | .lambda _ _, _, _ => simp [atoms]
  | .multiLambda _ _ _, _, _ => simp [atoms]
  | .subst _ _, _, _ => simp [atoms]

theorem products_atom {atom : Pattern} (isAtom : IsAtom decl atom) : products decl atom = some [[atom]] := by
  obtain ⟨notAbsorbing, notUnit, notProduct, notSum⟩ := isAtom
  match atom, notAbsorbing, notUnit, notProduct, notSum with
  | .apply label [], notAbsorbing, notUnit, _, _ =>
    have notAbsorbing' : label ≠ decl.absorbing := fun same => notAbsorbing (by rw [same])
    have notUnit' : label ≠ decl.unit := fun same => notUnit (by rw [same])
    simp [products, notAbsorbing', notUnit']
  | .collection kind elements none, _, _, notProduct, notSum =>
    have notSum' : kind ≠ decl.sum := fun same => notSum elements (by rw [same])
    have notProduct' : kind ≠ decl.product := fun same => notProduct elements (by rw [same])
    simp [products, notSum', notProduct']
  | .apply _ (_ :: _), _, _, _, _ => simp [products]
  | .collection _ _ (some _), _, _, _, _ => simp [products]
  | .bvar _, _, _, _, _ => simp [products]
  | .fvar _, _, _, _, _ => simp [products]
  | .lambda _ _, _, _, _, _ => simp [products]
  | .multiLambda _ _ _, _, _, _, _ => simp [products]
  | .subst _ _, _, _, _, _ => simp [products]

theorem atoms_unit : atoms decl (.apply decl.unit []) = [] := by simp [atoms]

theorem products_unit (valid : decl.Valid) : products decl (.apply decl.unit []) = some [[]] := by
  simp [products, valid.unitAbsorbing]

/-- The atoms of a canonical product are the product's atoms. -/
theorem atoms_productOf {chosen : List Pattern} (atomic : ∀ atom ∈ chosen, IsAtom decl atom) :
    (atoms decl (productOf decl chosen) : Multiset Pattern) = chosen ∧
      ∀ atom ∈ atoms decl (productOf decl chosen), IsAtom decl atom := by
  have sorted := sortLex_perm chosen
  unfold productOf
  split
  · rename_i empty
    rw [empty] at sorted
    have none : chosen = [] := (List.Perm.nil_eq sorted).symm
    subst none
    rw [atoms_unit]
    exact ⟨rfl, by simp⟩
  · rename_i atom single
    rw [single] at sorted
    have member : atom ∈ chosen := sorted.subset (by simp)
    rw [atoms_atom (atomic atom member)]
    exact ⟨Multiset.coe_eq_coe.mpr sorted, by simpa using atomic atom member⟩
  · rename_i sortedList _ _
    have shape : atoms decl (.collection decl.product (sortLex chosen) none) = sortLex chosen := by simp [atoms]
    rw [shape]
    exact ⟨Multiset.coe_eq_coe.mpr sorted, fun atom member => atomic atom (sorted.subset member)⟩

/-- A canonical product presents one product, its atoms. -/
theorem products_productOf (valid : decl.Valid) {chosen : List Pattern} (atomic : ∀ atom ∈ chosen, IsAtom decl atom) :
    products decl (productOf decl chosen) = some [atoms decl (productOf decl chosen)] := by
  have sorted := sortLex_perm chosen
  unfold productOf
  split
  · rw [atoms_unit]; exact products_unit valid
  · rename_i atom single
    rw [single] at sorted
    have isAtom := atomic atom (sorted.subset (by simp))
    rw [atoms_atom isAtom]
    exact products_atom isAtom
  · simp [products, atoms, valid.distinct]

/-- **A canonical sum presents its products**: its products, as atoms, present what it was built
from. -/
theorem products_sumOf (valid : decl.Valid) {cs : List (List Pattern)} (atomic : Atoms decl cs) :
    ∃ ps, products decl (sumOf decl cs) = some ps ∧ presented ps = presented cs ∧ Atoms decl ps := by
  have memL : ∀ p, p ∈ sortLex (cs.map (productOf decl)).dedup ↔ ∃ c ∈ cs, productOf decl c = p := by
    intro p
    rw [(sortLex_perm _).mem_iff, List.mem_dedup, List.mem_map]
  have products_member : ∀ p ∈ sortLex (cs.map (productOf decl)).dedup,
      products decl p = some [atoms decl p] ∧ (∀ a ∈ atoms decl p, IsAtom decl a) := by
    intro p member
    obtain ⟨c, cMember, rfl⟩ := (memL p).mp member
    exact ⟨products_productOf valid (atomic c cMember), (atoms_productOf (atomic c cMember)).2⟩
  have presentedL : presented ((sortLex (cs.map (productOf decl)).dedup).map (atoms decl)) = presented cs := by
    ext bag
    simp only [mem_presented, List.mem_map]
    constructor
    · rintro ⟨_, ⟨p, member, rfl⟩, rfl⟩
      obtain ⟨c, cMember, rfl⟩ := (memL p).mp member
      exact ⟨c, cMember, ((atoms_productOf (atomic c cMember)).1).symm⟩
    · rintro ⟨c, cMember, rfl⟩
      exact ⟨atoms decl (productOf decl c), ⟨productOf decl c, (memL _).mpr ⟨c, cMember, rfl⟩, rfl⟩,
        (atoms_productOf (atomic c cMember)).1⟩
  have atomsL : Atoms decl ((sortLex (cs.map (productOf decl)).dedup).map (atoms decl)) := by
    intro chosen member atom inChosen
    obtain ⟨p, pMember, rfl⟩ := List.mem_map.mp member
    exact (products_member p pMember).2 atom inChosen
  refine ⟨(sortLex (cs.map (productOf decl)).dedup).map (atoms decl), ?_, presentedL, atomsL⟩
  unfold sumOf
  revert products_member
  generalize sortLex (cs.map (productOf decl)).dedup = sorted
  intro products_member
  match sorted, products_member with
  | [], _ => simp [products]
  | [p], products_member => simpa using (products_member p (by simp)).1
  | p₁ :: p₂ :: rest, _ => simp [products]

/-- Every way of choosing presents the pointwise sum of the factors. -/
theorem presented_choices : ∀ factors : List (List (List Pattern)),
    presented (choices factors) = (factors.map presented).sum
  | [] => by simp [choices, presented, Finset.singleton_zero]
  | factor :: factors => by
    rw [List.map_cons, List.sum_cons, ← presented_choices factors]
    ext bag
    simp only [choices, mem_presented, List.mem_flatMap, List.mem_map, Finset.mem_add]
    constructor
    · rintro ⟨_, ⟨chosen, member, rest, restMember, rfl⟩, rfl⟩
      exact ⟨chosen, ⟨chosen, member, rfl⟩, rest, ⟨rest, restMember, rfl⟩, by simp [← Multiset.coe_add]⟩
    · rintro ⟨_, ⟨chosen, member, rfl⟩, _, ⟨rest, restMember, rfl⟩, rfl⟩
      exact ⟨chosen ++ rest, ⟨chosen, member, rest, restMember, rfl⟩, by simp [← Multiset.coe_add]⟩

/-- A flattened list of products presents the union of what each presents. -/
theorem presented_flatten : ∀ parts : List (List (List Pattern)),
    presented parts.flatten = (parts.map presented).foldr (· ∪ ·) ∅
  | [] => by simp [presented]
  | part :: parts => by
    rw [List.flatten_cons, List.map_cons, List.foldr_cons, ← presented_flatten parts]
    simp [presented, List.map_append, List.toFinset_append]

variable (decl) in
/-- **A canonical form**: the absorbing element, or the canonical sum of its own products, which are
products of atoms. -/
def Canonical (form : Pattern) : Prop :=
  form = .apply decl.absorbing [] ∨ ∃ ps, products decl form = some ps ∧ Atoms decl ps ∧ sumOf decl ps = form

variable (decl) in
/-- What a canonical form denotes: nothing for the absorbing element, else its presented products. -/
def value (form : Pattern) : Option (Finset (Multiset Pattern)) := (products decl form).map presented

theorem value_absorbing : value decl (.apply decl.absorbing []) = none := by
  simp [value, products_none.mpr rfl]

/-- **A canonical form is determined by what it denotes.** -/
theorem Canonical.eq {left right : Pattern} (canonicalLeft : Canonical decl left)
    (canonicalRight : Canonical decl right) (same : value decl left = value decl right) : left = right := by
  rcases canonicalLeft with rfl | ⟨ps, foundLeft, _, rebuiltLeft⟩ <;>
    rcases canonicalRight with rfl | ⟨qs, foundRight, _, rebuiltRight⟩
  · rfl
  · simp [value, products_none.mpr rfl, foundRight] at same
  · simp [value, products_none.mpr rfl, foundLeft] at same
  · simp only [value, foundLeft, foundRight, Option.map_some, Option.some.injEq] at same
    rw [← rebuiltLeft, ← rebuiltRight]
    exact sumOf_eq same

/-- A canonical sum of products of atoms is canonical, and denotes its presented products. -/
theorem sumOf_canonical (valid : decl.Valid) {cs : List (List Pattern)} (atomic : Atoms decl cs) :
    Canonical decl (sumOf decl cs) ∧ value decl (sumOf decl cs) = some (presented cs) := by
  obtain ⟨ps, found, same, atomsPs⟩ := products_sumOf valid atomic
  exact ⟨.inr ⟨ps, found, atomsPs, sumOf_eq same⟩, by simp [value, found, same]⟩

theorem sortLex_singleton (pattern : Pattern) : sortLex [pattern] = [pattern] := rfl

theorem atom_canonical {atom : Pattern} (isAtom : IsAtom decl atom) : Canonical decl atom := by
  refine .inr ⟨[[atom]], products_atom isAtom, by simpa [Atoms] using isAtom, ?_⟩
  simp [sumOf, productOf, sortLex_singleton]

theorem unit_canonical (valid : decl.Valid) : Canonical decl (.apply decl.unit []) := by
  refine .inr ⟨[[]], products_unit valid, by simp [Atoms], ?_⟩
  simp [sumOf, productOf]
  rfl

/-- The empty sum is canonical: it is the zero. -/
theorem empty_canonical : Canonical decl (.collection decl.sum [] none) :=
  .inr ⟨[], by simp [products], by simp [Atoms], by simp [sumOf, sortLex]⟩

theorem mapM_value {items : List Pattern} :
    items.mapM (value decl) = (items.mapM (products decl)).map (·.map presented) := by
  induction items with
  | nil => simp
  | cons item items ih =>
    simp only [List.mapM_cons, ih, value]
    cases products decl item <;> cases items.mapM (products decl) <;> simp

theorem choices_atoms : ∀ {factors : List (List (List Pattern))}, (∀ factor ∈ factors, Atoms decl factor) →
    Atoms decl (choices factors)
  | [], _ => by simp [choices, Atoms]
  | factor :: factors, atomic => by
    intro chosen member atom inChosen
    simp only [choices, List.mem_flatMap, List.mem_map] at member
    obtain ⟨first, firstMember, rest, restMember, rfl⟩ := member
    rcases List.mem_append.mp inChosen with inFirst | inRest
    · exact atomic factor (by simp) first firstMember atom inFirst
    · exact choices_atoms (fun other inOthers => atomic other (by simp [inOthers])) rest restMember atom inRest

/-- The factors of canonical items are products of atoms. -/
theorem factors_of_canonical {items : List Pattern} (canonical : ∀ item ∈ items, Canonical decl item)
    {factors : List (List (List Pattern))} (found : items.mapM (products decl) = some factors) :
    ∀ factor ∈ factors, Atoms decl factor := by
  intro factor member
  obtain ⟨item, itemMember, itemFound⟩ := mapM_mem found factor member
  rcases canonical item itemMember with rfl | ⟨ps, psFound, atomic, _⟩
  · rw [products_none.mpr rfl] at itemFound; cases itemFound
  · rw [psFound] at itemFound; cases itemFound; exact atomic

/-- **Composition denotes the pointwise sum.** -/
theorem multiply_value (valid : decl.Valid) {items : List Pattern} (canonical : ∀ item ∈ items, Canonical decl item) :
    Canonical decl (multiply decl items) ∧
      value decl (multiply decl items) = (items.mapM (value decl)).map List.sum := by
  unfold multiply
  cases found : items.mapM (products decl) with
  | none => exact ⟨.inl rfl, by simp [value_absorbing, mapM_value, found]⟩
  | some factors =>
    have each := factors_of_canonical canonical found
    obtain ⟨canonicalSum, valueSum⟩ := sumOf_canonical valid (choices_atoms fun factor member => each factor member)
    refine ⟨canonicalSum, ?_⟩
    rw [valueSum, mapM_value, found]
    simp [presented_choices]

/-- **Summation denotes the union.** -/
theorem add_value (valid : decl.Valid) {items : List Pattern} (canonical : ∀ item ∈ items, Canonical decl item) :
    Canonical decl (add decl items) ∧
      value decl (add decl items) = (items.mapM (value decl)).map fun values => values.foldr (· ∪ ·) ∅ := by
  unfold add
  cases found : items.mapM (products decl) with
  | none => exact ⟨.inl rfl, by simp [value_absorbing, mapM_value, found]⟩
  | some parts =>
    have each := factors_of_canonical canonical found
    have atomic : Atoms decl parts.flatten := by
      intro chosen member atom inChosen
      obtain ⟨part, partMember, chosenMember⟩ := List.mem_flatten.mp member
      exact each part partMember chosen chosenMember atom inChosen
    obtain ⟨canonicalSum, valueSum⟩ := sumOf_canonical valid atomic
    refine ⟨canonicalSum, ?_⟩
    rw [valueSum, mapM_value, found]
    simp [presented_flatten]

/-! ## Canonical forms of object terms -/

theorem normal_bvar (index : Nat) : normal decl (.bvar index) = .bvar index := by rw [normal]
theorem normal_fvar (name : String) : normal decl (.fvar name) = .fvar name := by rw [normal]
theorem normal_apply (label : String) (arguments : List Pattern) :
    normal decl (.apply label arguments) = .apply label (arguments.map (normal decl)) := by rw [normal]
theorem normal_lambda (binder : Option String) (body : Pattern) :
    normal decl (.lambda binder body) = .lambda binder (normal decl body) := by rw [normal]
theorem normal_multiLambda (arity : Nat) (binders : List String) (body : Pattern) :
    normal decl (.multiLambda arity binders body) = .multiLambda arity binders (normal decl body) := by rw [normal]
theorem normal_subst (body replacement : Pattern) :
    normal decl (.subst body replacement) = .subst (normal decl body) (normal decl replacement) := by rw [normal]
theorem normal_collection (kind : CollType) (elements : List Pattern) :
    normal decl (.collection kind elements none) =
      if kind = decl.product then multiply decl (elements.map (normal decl))
      else if kind = decl.sum then add decl (elements.map (normal decl))
      else .collection kind (arrange kind (elements.map (normal decl))) none := by
  rw [normal.eq_def]

theorem isAtom_of_shape {pattern : Pattern}
    (notApply : ∀ label, pattern = .apply label [] → label ≠ decl.absorbing ∧ label ≠ decl.unit)
    (notProduct : ∀ elements, pattern ≠ .collection decl.product elements none)
    (notSum : ∀ elements, pattern ≠ .collection decl.sum elements none) : IsAtom decl pattern :=
  ⟨fun same => (notApply _ same).1 rfl, fun same => (notApply _ same).2 rfl, notProduct, notSum⟩

/-- **The canonical form of a plain term is canonical.** -/
theorem normal_canonical (valid : decl.Valid) (pattern : Pattern) (isFree : restFree pattern = true) :
    Canonical decl (normal decl pattern) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
    rw [normal_bvar]
    exact atom_canonical (isAtom_of_shape (fun _ same => by cases same) (fun _ same => by cases same)
      (fun _ same => by cases same))
  | hfvar name =>
    rw [normal_fvar]
    exact atom_canonical (isAtom_of_shape (fun _ same => by cases same) (fun _ same => by cases same)
      (fun _ same => by cases same))
  | happly label arguments _ =>
    rw [normal_apply]
    cases arguments with
    | nil =>
      by_cases absorbing : label = decl.absorbing
      · subst absorbing; exact .inl rfl
      · by_cases unit : label = decl.unit
        · subst unit; exact unit_canonical valid
        · exact atom_canonical (isAtom_of_shape
            (fun other same => by cases same; exact ⟨absorbing, unit⟩) (fun _ same => by cases same)
            (fun _ same => by cases same))
    | cons first others =>
      exact atom_canonical (isAtom_of_shape (fun _ same => by cases same) (fun _ same => by cases same)
        (fun _ same => by cases same))
  | hlambda binder body _ =>
    rw [normal_lambda]
    exact atom_canonical (isAtom_of_shape (fun _ same => by cases same) (fun _ same => by cases same)
      (fun _ same => by cases same))
  | hmultiLambda arity binders body _ =>
    rw [normal_multiLambda]
    exact atom_canonical (isAtom_of_shape (fun _ same => by cases same) (fun _ same => by cases same)
      (fun _ same => by cases same))
  | hsubst body replacement _ _ =>
    rw [normal_subst]
    exact atom_canonical (isAtom_of_shape (fun _ same => by cases same) (fun _ same => by cases same)
      (fun _ same => by cases same))
  | hcollection kind elements rest ih =>
    obtain ⟨rfl, elementsFree⟩ := restFree_collection isFree
    have each : ∀ item ∈ elements.map (normal decl), Canonical decl item := by
      intro item member
      obtain ⟨element, elementMember, rfl⟩ := List.mem_map.mp member
      exact ih element elementMember (elementsFree element elementMember)
    rw [normal_collection]
    split
    · exact (multiply_value valid each).1
    · split
      · exact (add_value valid each).1
      · rename_i notProduct notSum
        exact atom_canonical (isAtom_of_shape (fun _ same => by cases same)
          (fun _ same => by cases same; exact notProduct rfl) (fun _ same => by cases same; exact notSum rfl))

/-! ## The canonical form is idempotent -/

theorem sortLex_sortLex (patterns : List Pattern) : sortLex (sortLex patterns) = sortLex patterns :=
  sortLex_eq_of_perm (sortLex_perm patterns)

theorem normal_constant (label : String) : normal decl (.apply label []) = .apply label [] := by
  rw [normal_apply]; rfl

/-- The three shapes of a canonical product. -/
theorem productOf_cases (chosen : List Pattern) :
    (chosen = [] ∧ productOf decl chosen = .apply decl.unit []) ∨
      (∃ atom, chosen.Perm [atom] ∧ productOf decl chosen = atom) ∨
      (2 ≤ chosen.length ∧ productOf decl chosen = .collection decl.product (sortLex chosen) none) := by
  have sorted := sortLex_perm chosen
  unfold productOf
  split
  · rename_i empty
    rw [empty] at sorted
    exact .inl ⟨(List.Perm.nil_eq sorted).symm, rfl⟩
  · rename_i atom single
    rw [single] at sorted
    exact .inr (.inl ⟨atom, sorted.symm, rfl⟩)
  · rename_i notEmpty notSingle
    refine .inr (.inr ⟨?_, rfl⟩)
    rw [← sorted.length_eq]
    match found : sortLex chosen with
    | [] => exact absurd found notEmpty
    | [atom] => exact absurd found (notSingle atom)
    | _ :: _ :: _ => simp

theorem mapM_products_atoms : ∀ {chosen : List Pattern}, (∀ atom ∈ chosen, IsAtom decl atom) →
    chosen.mapM (products decl) = some (chosen.map fun atom => [[atom]])
  | [], _ => rfl
  | atom :: chosen, atomic => by
    have rest : chosen.mapM (products decl) = some (chosen.map fun atom => [[atom]]) :=
      mapM_products_atoms fun other member => atomic other (List.mem_cons_of_mem _ member)
    simp [List.mapM_cons, products_atom (atomic atom List.mem_cons_self), rest]

theorem choices_singletons : ∀ chosen : List Pattern, choices (chosen.map fun atom => [[atom]]) = [chosen]
  | [] => rfl
  | atom :: chosen => by simp [choices, choices_singletons chosen]

/-- Multiplying atoms is their canonical product. -/
theorem multiply_atoms {chosen : List Pattern} (atomic : ∀ atom ∈ chosen, IsAtom decl atom) :
    multiply decl chosen = productOf decl chosen := by
  unfold multiply
  rw [mapM_products_atoms atomic]
  simp only [choices_singletons]
  unfold sumOf
  simp [sortLex_singleton]

/-- **A canonical product of atoms that are their own canonical forms is its own canonical form.** -/
theorem normal_productOf {chosen : List Pattern} (atomic : ∀ atom ∈ chosen, IsAtom decl atom)
    (stable : ∀ atom ∈ chosen, normal decl atom = atom) : normal decl (productOf decl chosen) = productOf decl chosen := by
  rcases productOf_cases (decl := decl) chosen with ⟨_, found⟩ | ⟨atom, permutation, found⟩ | ⟨_, found⟩
  · rw [found]; exact normal_constant _
  · rw [found]; exact stable atom (permutation.symm.subset (by simp))
  · rw [found, normal_collection, if_pos rfl]
    have mapped : (sortLex chosen).map (normal decl) = sortLex chosen := by
      conv => rhs; rw [← List.map_id (sortLex chosen)]
      exact List.map_congr_left fun atom member => stable atom ((sortLex_perm chosen).subset member)
    rw [mapped, multiply_atoms (fun atom member => atomic atom ((sortLex_perm chosen).subset member)),
      productOf_eq (Multiset.coe_eq_coe.mpr (sortLex_perm chosen)), found]

/-- The three shapes of a canonical sum. -/
theorem sumOf_cases (cs : List (List Pattern)) :
    (cs = [] ∧ sumOf decl cs = .collection decl.sum [] none) ∨
      (∃ c ∈ cs, sumOf decl cs = productOf decl c) ∨
      (2 ≤ (sortLex (cs.map (productOf decl)).dedup).length ∧
        sumOf decl cs = .collection decl.sum (sortLex (cs.map (productOf decl)).dedup) none) := by
  have memL : ∀ p, p ∈ sortLex (cs.map (productOf decl)).dedup ↔ ∃ c ∈ cs, productOf decl c = p := by
    intro p
    rw [(sortLex_perm _).mem_iff, List.mem_dedup, List.mem_map]
  unfold sumOf
  split
  · rename_i empty
    refine .inl ⟨?_, rfl⟩
    match cs, empty with
    | [], _ => rfl
    | c :: _, empty =>
      have inL := (memL (productOf decl c)).mpr ⟨c, by simp, rfl⟩
      rw [empty] at inL
      simp at inL
  · rename_i product single
    obtain ⟨c, cMember, made⟩ := (memL product).mp (by rw [single]; simp)
    exact .inr (.inl ⟨c, cMember, made.symm⟩)
  · rename_i notEmpty notSingle
    refine .inr (.inr ⟨?_, rfl⟩)
    match found : sortLex (cs.map (productOf decl)).dedup with
    | [] => exact absurd found notEmpty
    | [product] => exact absurd found (notSingle product)
    | _ :: _ :: _ => simp

theorem mapM_products_productOf (valid : decl.Valid) :
    ∀ {products' : List Pattern}, (∀ product ∈ products', ∃ c, (∀ atom ∈ c, IsAtom decl atom) ∧ productOf decl c = product) →
      products'.mapM (products decl) = some (products'.map fun product => [atoms decl product])
  | [], _ => rfl
  | product :: products', made => by
    obtain ⟨c, atomic, rfl⟩ := made product List.mem_cons_self
    have rest : products'.mapM (products decl) = some (products'.map fun product => [atoms decl product]) :=
      mapM_products_productOf valid fun other member => made other (List.mem_cons_of_mem _ member)
    simp [List.mapM_cons, products_productOf valid atomic, rest]

/-- **A canonical sum of atoms that are their own canonical forms is its own canonical form.** -/
theorem normal_sumOf (valid : decl.Valid) {cs : List (List Pattern)} (atomic : Atoms decl cs)
    (stable : ∀ c ∈ cs, ∀ atom ∈ c, normal decl atom = atom) : normal decl (sumOf decl cs) = sumOf decl cs := by
  have memL : ∀ p, p ∈ sortLex (cs.map (productOf decl)).dedup ↔ ∃ c ∈ cs, productOf decl c = p := by
    intro p
    rw [(sortLex_perm _).mem_iff, List.mem_dedup, List.mem_map]
  rcases sumOf_cases (decl := decl) cs with ⟨rfl, found⟩ | ⟨c, cMember, found⟩ | ⟨long, found⟩
  · rw [found, normal_collection, if_neg (fun same => valid.distinct same.symm), if_pos rfl]
    simp [add, sumOf]
    rfl
  · rw [found]; exact normal_productOf (atomic c cMember) (stable c cMember)
  · rw [found, normal_collection, if_neg (fun same => valid.distinct same.symm), if_pos rfl]
    have stableL : ∀ p ∈ sortLex (cs.map (productOf decl)).dedup, normal decl p = p := fun p member => by
      obtain ⟨c, cMember, rfl⟩ := (memL p).mp member
      exact normal_productOf (atomic c cMember) (stable c cMember)
    have mapped : (sortLex (cs.map (productOf decl)).dedup).map (normal decl) = sortLex (cs.map (productOf decl)).dedup := by
      conv => rhs; rw [← List.map_id (sortLex (cs.map (productOf decl)).dedup)]
      exact List.map_congr_left stableL
    rw [mapped]
    unfold add
    rw [mapM_products_productOf valid fun p member => by
      obtain ⟨c, cMember, rfl⟩ := (memL p).mp member
      exact ⟨c, atomic c cMember, rfl⟩]
    simp only
    have flat : (List.map (fun product => [atoms decl product]) (sortLex (cs.map (productOf decl)).dedup)).flatten =
        (sortLex (cs.map (productOf decl)).dedup).map (atoms decl) := by
      induction (sortLex (cs.map (productOf decl)).dedup) with
      | nil => rfl
      | cons p rest ih => simp [ih]
    rw [flat]
    have remade : ((sortLex (cs.map (productOf decl)).dedup).map (atoms decl)).map (productOf decl) =
        sortLex (cs.map (productOf decl)).dedup := by
      rw [List.map_map]
      conv => rhs; rw [← List.map_id (sortLex (cs.map (productOf decl)).dedup)]
      refine List.map_congr_left fun p member => ?_
      obtain ⟨c, cMember, rfl⟩ := (memL p).mp member
      exact productOf_eq (atoms_productOf (atomic c cMember)).1
    have nodup : (sortLex (cs.map (productOf decl)).dedup).Nodup :=
      (sortLex_perm _).nodup_iff.mpr (List.nodup_dedup _)
    unfold sumOf
    rw [remade, List.dedup_eq_self.mpr nodup, sortLex_sortLex]
    revert long
    generalize sortLex (cs.map (productOf decl)).dedup = sorted
    intro long
    match sorted, long with
    | _ :: _ :: _, _ => rfl

theorem mem_choices_atom : ∀ {factors : List (List (List Pattern))} {chosen : List Pattern} {atom : Pattern},
    chosen ∈ choices factors → atom ∈ chosen → ∃ factor ∈ factors, ∃ c ∈ factor, atom ∈ c
  | [], chosen, atom, member, inChosen => by
    simp [choices] at member
    subst member
    simp at inChosen
  | factor :: factors, chosen, atom, member, inChosen => by
    simp only [choices, List.mem_flatMap, List.mem_map] at member
    obtain ⟨first, firstMember, rest, restMember, rfl⟩ := member
    rcases List.mem_append.mp inChosen with inFirst | inRest
    · exact ⟨factor, List.mem_cons_self, first, firstMember, inFirst⟩
    · obtain ⟨other, otherMember, c, cMember, inC⟩ := mem_choices_atom restMember inRest
      exact ⟨other, List.mem_cons_of_mem _ otherMember, c, cMember, inC⟩

/-- A canonical sum's products have the atoms it was built from. -/
theorem products_sumOf_atoms (valid : decl.Valid) {cs : List (List Pattern)} (atomic : Atoms decl cs)
    {ps : List (List Pattern)} (found : products decl (sumOf decl cs) = some ps) :
    ∀ chosen ∈ ps, ∀ atom ∈ chosen, ∃ c ∈ cs, atom ∈ c := by
  obtain ⟨ps', found', presentedSame, _⟩ := products_sumOf valid atomic
  rw [found] at found'
  cases found'
  intro chosen member atom inChosen
  have inPresented : (chosen : Multiset Pattern) ∈ presented cs := by
    rw [← presentedSame]; exact mem_presented.mpr ⟨chosen, member, rfl⟩
  obtain ⟨c, cMember, sameBag⟩ := mem_presented.mp inPresented
  exact ⟨c, cMember, (Multiset.mem_coe.mp (sameBag ▸ Multiset.mem_coe.mpr inChosen))⟩

/-- Arranging is idempotent. -/
theorem arrange_idem (kind : CollType) (items : List Pattern) : arrange kind (arrange kind items) = arrange kind items := by
  cases kind with
  | vec => rfl
  | hashBag => exact sortLex_eq_of_perm (sortLex_perm items)
  | hashSet =>
    rw [arrange_set, arrange_set]
    have sorted : sortLex (sortLex items).dedup = (sortLex items).dedup :=
      List.Perm.eq_of_pairwise' (sortLex_pairwise _) ((sortLex_pairwise items).sublist (List.dedup_sublist _))
        (sortLex_perm _)
    rw [sorted, List.dedup_idem]

/-- **The canonical form is idempotent**, and every atom of a canonical form is its own canonical
form. -/
theorem normal_stable (valid : decl.Valid) : ∀ (pattern : Pattern), restFree pattern = true →
    normal decl (normal decl pattern) = normal decl pattern ∧
      ∀ ps, products decl (normal decl pattern) = some ps → ∀ chosen ∈ ps, ∀ atom ∈ chosen, normal decl atom = atom := by
  intro pattern
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
    intro _
    rw [normal_bvar]
    refine ⟨normal_bvar index, fun ps found chosen member atom inChosen => ?_⟩
    simp [products] at found
    subst found
    simp at member
    subst member
    simp at inChosen
    subst inChosen
    exact normal_bvar index
  | hfvar name =>
    intro _
    rw [normal_fvar]
    refine ⟨normal_fvar name, fun ps found chosen member atom inChosen => ?_⟩
    simp [products] at found
    subst found
    simp at member
    subst member
    simp at inChosen
    subst inChosen
    exact normal_fvar name
  | happly label arguments ih =>
    intro isFree
    have argumentsStable : (arguments.map (normal decl)).map (normal decl) = arguments.map (normal decl) := by
      rw [List.map_map]
      exact List.map_congr_left fun argument member =>
        (ih argument member (restFree_apply isFree argument member)).1
    have selfStable : normal decl (normal decl (.apply label arguments)) = normal decl (.apply label arguments) := by
      rw [normal_apply, normal_apply, argumentsStable]
    refine ⟨selfStable, fun ps found chosen member atom inChosen => ?_⟩
    rw [normal_apply] at found selfStable
    cases arguments with
    | nil =>
      simp only [List.map_nil] at found
      by_cases absorbing : label = decl.absorbing
      · subst absorbing; simp [products] at found
      · by_cases unit : label = decl.unit
        · subst unit
          simp [products, valid.unitAbsorbing] at found
          subst found; simp at member; subst member; simp at inChosen
        · simp [products, absorbing, unit] at found
          subst found; simp at member; subst member; simp at inChosen; subst inChosen
          exact normal_constant _
    | cons first others =>
      simp [products] at found
      subst found; simp at member; subst member; simp at inChosen; subst inChosen; exact selfStable
  | hlambda binder body ih =>
    intro isFree
    have bodyStable := (ih (by simpa [restFree] using isFree)).1
    have selfStable : normal decl (normal decl (.lambda binder body)) = normal decl (.lambda binder body) := by
      rw [normal_lambda, normal_lambda, bodyStable]
    refine ⟨selfStable, fun ps found chosen member atom inChosen => ?_⟩
    rw [normal_lambda] at found selfStable
    simp [products] at found
    subst found; simp at member; subst member; simp at inChosen; subst inChosen; exact selfStable
  | hmultiLambda arity binders body ih =>
    intro isFree
    have bodyStable := (ih (by simpa [restFree] using isFree)).1
    have selfStable : normal decl (normal decl (.multiLambda arity binders body)) =
        normal decl (.multiLambda arity binders body) := by
      rw [normal_multiLambda, normal_multiLambda, bodyStable]
    refine ⟨selfStable, fun ps found chosen member atom inChosen => ?_⟩
    rw [normal_multiLambda] at found selfStable
    simp [products] at found
    subst found; simp at member; subst member; simp at inChosen; subst inChosen; exact selfStable
  | hsubst body replacement bodyIH replacementIH =>
    intro isFree
    have parts := restFree_subst isFree
    have selfStable : normal decl (normal decl (.subst body replacement)) = normal decl (.subst body replacement) := by
      rw [normal_subst, normal_subst, (bodyIH parts.1).1, (replacementIH parts.2).1]
    refine ⟨selfStable, fun ps found chosen member atom inChosen => ?_⟩
    rw [normal_subst] at found selfStable
    simp [products] at found
    subst found; simp at member; subst member; simp at inChosen; subst inChosen; exact selfStable
  | hcollection kind elements rest ih =>
    intro isFree
    obtain ⟨rfl, elementsFree⟩ := restFree_collection isFree
    have itemsStable : ∀ item ∈ elements.map (normal decl), normal decl item = item ∧
        ∀ ps, products decl item = some ps → ∀ chosen ∈ ps, ∀ atom ∈ chosen, normal decl atom = atom := by
      intro item member
      obtain ⟨element, elementMember, rfl⟩ := List.mem_map.mp member
      exact ih element elementMember (elementsFree element elementMember)
    have itemsCanonical : ∀ item ∈ elements.map (normal decl), Canonical decl item := by
      intro item member
      obtain ⟨element, elementMember, rfl⟩ := List.mem_map.mp member
      exact normal_canonical valid element (elementsFree element elementMember)
    have factorsAtomic : ∀ {items : List Pattern} {factors : List (List (List Pattern))},
        (∀ item ∈ items, Canonical decl item) → items.mapM (products decl) = some factors →
          ∀ factor ∈ factors, Atoms decl factor := by
      intro items factors canonical found factor member
      obtain ⟨item, itemMember, itemFound⟩ := mapM_mem found factor member
      rcases canonical item itemMember with rfl | ⟨ps, psFound, atomic, _⟩
      · simp [products_none.mpr rfl] at itemFound
      · rw [psFound] at itemFound; cases itemFound; exact atomic
    have factorsStable : ∀ {factors : List (List (List Pattern))},
        (elements.map (normal decl)).mapM (products decl) = some factors →
          ∀ factor ∈ factors, ∀ c ∈ factor, ∀ atom ∈ c, normal decl atom = atom := by
      intro factors found factor member c cMember atom inC
      obtain ⟨item, itemMember, itemFound⟩ := mapM_mem found factor member
      exact (itemsStable item itemMember).2 factor itemFound c cMember atom inC
    rw [normal_collection]
    by_cases isProduct : kind = decl.product
    · rw [if_pos isProduct]
      unfold multiply
      cases found : (elements.map (normal decl)).mapM (products decl) with
      | none => exact ⟨normal_constant _, fun ps absorbed => by simp [products_none.mpr rfl] at absorbed⟩
      | some factors =>
        simp only
        have atomic : Atoms decl (choices factors) := choices_atoms (factorsAtomic itemsCanonical found)
        have stable : ∀ c ∈ choices factors, ∀ atom ∈ c, normal decl atom = atom := by
          intro c cMember atom inC
          obtain ⟨factor, factorMember, c', c'Member, inC'⟩ := mem_choices_atom cMember inC
          exact factorsStable found factor factorMember c' c'Member atom inC'
        refine ⟨normal_sumOf valid atomic stable, fun ps sumFound chosen member atom inChosen => ?_⟩
        obtain ⟨c, cMember, inC⟩ := products_sumOf_atoms valid atomic sumFound chosen member atom inChosen
        exact stable c cMember atom inC
    · rw [if_neg isProduct]
      by_cases isSum : kind = decl.sum
      · rw [if_pos isSum]
        unfold add
        cases found : (elements.map (normal decl)).mapM (products decl) with
        | none => exact ⟨normal_constant _, fun ps absorbed => by simp [products_none.mpr rfl] at absorbed⟩
        | some parts =>
          simp only
          have atomic : Atoms decl parts.flatten := by
            intro chosen member atom inChosen
            obtain ⟨part, partMember, chosenMember⟩ := List.mem_flatten.mp member
            exact factorsAtomic itemsCanonical found part partMember chosen chosenMember atom inChosen
          have stable : ∀ c ∈ parts.flatten, ∀ atom ∈ c, normal decl atom = atom := by
            intro c cMember atom inC
            obtain ⟨part, partMember, cInPart⟩ := List.mem_flatten.mp cMember
            exact factorsStable found part partMember c cInPart atom inC
          refine ⟨normal_sumOf valid atomic stable, fun ps sumFound chosen member atom inChosen => ?_⟩
          obtain ⟨c, cMember, inC⟩ := products_sumOf_atoms valid atomic sumFound chosen member atom inChosen
          exact stable c cMember atom inC
      · rw [if_neg isSum]
        have arranged : (arrange kind (elements.map (normal decl))).map (normal decl) =
            arrange kind (elements.map (normal decl)) := by
          conv => rhs; rw [← List.map_id (arrange kind (elements.map (normal decl)))]
          exact List.map_congr_left fun item member => (itemsStable item ((arrange_mem item).mp member)).1
        have selfStable : normal decl (.collection kind (arrange kind (elements.map (normal decl))) none) =
            .collection kind (arrange kind (elements.map (normal decl))) none := by
          rw [normal_collection, if_neg isProduct, if_neg isSum, arranged, arrange_idem]
        refine ⟨selfStable, fun ps found chosen member atom inChosen => ?_⟩
        simp [products, isProduct, isSum] at found
        subst found; simp at member; subst member; simp at inChosen; subst inChosen; exact selfStable

/-! ## Every move keeps the canonical form -/

/-- Composition of denotations; the absorbing element absorbs. -/
def plus : Option (Finset (Multiset Pattern)) → Option (Finset (Multiset Pattern)) → Option (Finset (Multiset Pattern))
  | some left, some right => some (left + right)
  | _, _ => none

/-- Summation of denotations; the absorbing element absorbs. -/
def cup : Option (Finset (Multiset Pattern)) → Option (Finset (Multiset Pattern)) → Option (Finset (Multiset Pattern))
  | some left, some right => some (left ∪ right)
  | _, _ => none

theorem plus_comm (a b : Option (Finset (Multiset Pattern))) : plus a b = plus b a := by
  cases a <;> cases b <;> simp [plus, add_comm]

theorem plus_assoc (a b c : Option (Finset (Multiset Pattern))) : plus (plus a b) c = plus a (plus b c) := by
  cases a <;> cases b <;> cases c <;> simp [plus, add_assoc]

theorem plus_zero (a : Option (Finset (Multiset Pattern))) : plus a (some 0) = a := by
  cases a <;> simp [plus]

theorem plus_left_comm (a b c : Option (Finset (Multiset Pattern))) : plus a (plus b c) = plus b (plus a c) := by
  rw [← plus_assoc, plus_comm a b, plus_assoc]

theorem cup_comm (a b : Option (Finset (Multiset Pattern))) : cup a b = cup b a := by
  cases a <;> cases b <;> simp [cup, Finset.union_comm]

theorem cup_assoc (a b c : Option (Finset (Multiset Pattern))) : cup (cup a b) c = cup a (cup b c) := by
  cases a <;> cases b <;> cases c <;> simp [cup, Finset.union_assoc]

theorem cup_empty (a : Option (Finset (Multiset Pattern))) : cup a (some ∅) = a := by
  cases a <;> simp [cup]

theorem cup_self (a : Option (Finset (Multiset Pattern))) : cup a a = a := by
  cases a <;> simp [cup]

theorem cup_left_comm (a b c : Option (Finset (Multiset Pattern))) : cup a (cup b c) = cup b (cup a c) := by
  rw [← cup_assoc, cup_comm a b, cup_assoc]

theorem plus_cup (a b c : Option (Finset (Multiset Pattern))) : plus a (cup b c) = cup (plus a b) (plus a c) := by
  cases a <;> cases b <;> cases c <;> simp [plus, cup, Finset.add_union]

variable (decl) in
/-- What a composition of canonical forms denotes. -/
def total (items : List Pattern) : Option (Finset (Multiset Pattern)) :=
  items.foldr (fun item rest => plus (value decl item) rest) (some 0)

variable (decl) in
/-- What a sum of canonical forms denotes. -/
def union (items : List Pattern) : Option (Finset (Multiset Pattern)) :=
  items.foldr (fun item rest => cup (value decl item) rest) (some ∅)

theorem total_nil : total decl [] = some 0 := rfl
theorem total_cons (item : Pattern) (items : List Pattern) :
    total decl (item :: items) = plus (value decl item) (total decl items) := rfl
theorem union_nil : union decl [] = some ∅ := rfl
theorem union_cons (item : Pattern) (items : List Pattern) :
    union decl (item :: items) = cup (value decl item) (union decl items) := rfl

theorem total_append : ∀ (left right : List Pattern), total decl (left ++ right) = plus (total decl left) (total decl right)
  | [], right => by rw [List.nil_append, total_nil, plus_comm, plus_zero]
  | item :: left, right => by rw [List.cons_append, total_cons, total_cons, total_append left right, plus_assoc]

theorem union_append : ∀ (left right : List Pattern), union decl (left ++ right) = cup (union decl left) (union decl right)
  | [], right => by rw [List.nil_append, union_nil, cup_comm, cup_empty]
  | item :: left, right => by rw [List.cons_append, union_cons, union_cons, union_append left right, cup_assoc]

theorem total_perm {left right : List Pattern} (permutation : left.Perm right) : total decl left = total decl right := by
  induction permutation with
  | nil => rfl
  | cons item _ ih => rw [total_cons, total_cons, ih]
  | swap first second rest => rw [total_cons, total_cons, total_cons, total_cons, plus_left_comm]
  | trans _ _ first second => exact first.trans second

theorem union_perm {left right : List Pattern} (permutation : left.Perm right) : union decl left = union decl right := by
  induction permutation with
  | nil => rfl
  | cons item _ ih => rw [union_cons, union_cons, ih]
  | swap first second rest => rw [union_cons, union_cons, union_cons, union_cons, cup_left_comm]
  | trans _ _ first second => exact first.trans second

/-- A summand already present adds nothing to the union. -/
theorem cup_absorb_of_mem {item : Pattern} {items : List Pattern} (member : item ∈ items) :
    cup (value decl item) (union decl items) = union decl items := by
  obtain ⟨before, after, rfl⟩ := List.append_of_mem member
  rw [union_append, union_cons, cup_left_comm, ← cup_assoc (value decl item) (value decl item), cup_self]

theorem union_dedup : ∀ items : List Pattern, union decl items.dedup = union decl items
  | [] => rfl
  | item :: items => by
    by_cases member : item ∈ items
    · rw [List.dedup_cons_of_mem member, union_dedup items, union_cons, cup_absorb_of_mem member]
    · rw [List.dedup_cons_of_notMem member, union_cons, union_cons, union_dedup items]

/-- **The union depends only on which summands occur.** -/
theorem union_members {left right : List Pattern} (same : ∀ a, a ∈ left ↔ a ∈ right) :
    union decl left = union decl right := by
  rw [← union_dedup left, ← union_dedup right]
  apply union_perm
  rw [List.perm_ext_iff_of_nodup (List.nodup_dedup _) (List.nodup_dedup _)]
  intro a
  rw [List.mem_dedup, List.mem_dedup]
  exact same a

theorem mapM_sum_eq_total : ∀ (items : List Pattern), (items.mapM (value decl)).map List.sum = total decl items
  | [] => rfl
  | item :: items => by
    rw [total_cons, ← mapM_sum_eq_total items, List.mapM_cons]
    cases value decl item <;> cases items.mapM (value decl) <;> simp [plus]

theorem mapM_union_eq_union : ∀ (items : List Pattern),
    (items.mapM (value decl)).map (fun values => values.foldr (· ∪ ·) ∅) = union decl items
  | [] => rfl
  | item :: items => by
    rw [union_cons, ← mapM_union_eq_union items, List.mapM_cons]
    cases value decl item <;> cases items.mapM (value decl) <;> simp [cup]

theorem value_unit (valid : decl.Valid) : value decl (.apply decl.unit []) = some 0 := by
  simp [value, products_unit valid, presented, Finset.singleton_zero]

theorem multiply_total (valid : decl.Valid) {items : List Pattern} (canonical : ∀ item ∈ items, Canonical decl item) :
    Canonical decl (multiply decl items) ∧ value decl (multiply decl items) = total decl items := by
  obtain ⟨isCanonical, valued⟩ := multiply_value valid canonical
  exact ⟨isCanonical, valued.trans (mapM_sum_eq_total items)⟩

theorem add_union (valid : decl.Valid) {items : List Pattern} (canonical : ∀ item ∈ items, Canonical decl item) :
    Canonical decl (add decl items) ∧ value decl (add decl items) = union decl items := by
  obtain ⟨isCanonical, valued⟩ := add_value valid canonical
  exact ⟨isCanonical, valued.trans (mapM_union_eq_union items)⟩

theorem lawFor_cases {kind : CollType} {law : CollectionLaws.Laws}
    (found : CollectionLaws.lawFor (laws decl) kind = some law) :
    (kind = decl.product ∧ law = ⟨decl.product, some decl.unit⟩) ∨ (kind = decl.sum ∧ law = ⟨decl.sum, none⟩) := by
  have member := List.mem_of_find?_eq_some found
  have kindIs := CollectionLaws.lawFor_kind found
  simp only [laws, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact .inl ⟨kindIs.symm, rfl⟩
  · exact .inr ⟨kindIs.symm, rfl⟩

/-- The canonical forms of object terms are canonical. -/
theorem canonical_map (valid : decl.Valid) {items : List Pattern} (freeItems : ∀ item ∈ items, restFree item = true) :
    ∀ item ∈ items.map (normal decl), Canonical decl item := by
  intro item member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  exact normal_canonical valid original (freeItems original originalMember)

theorem normal_product (elements : List Pattern) :
    normal decl (.collection decl.product elements none) = multiply decl (elements.map (normal decl)) := by
  rw [normal_collection, if_pos rfl]

theorem normal_sum (valid : decl.Valid) (elements : List Pattern) :
    normal decl (.collection decl.sum elements none) = add decl (elements.map (normal decl)) := by
  rw [normal_collection, if_neg (Ne.symm valid.distinct), if_pos rfl]

theorem canonical_append {left right : List Pattern} (canonicalLeft : ∀ item ∈ left, Canonical decl item)
    (canonicalRight : ∀ item ∈ right, Canonical decl item) : ∀ item ∈ left ++ right, Canonical decl item := by
  intro item member
  rcases List.mem_append.mp member with inLeft | inRight
  · exact canonicalLeft item inLeft
  · exact canonicalRight item inRight

theorem canonical_cons {item : Pattern} {items : List Pattern} (here : Canonical decl item)
    (later : ∀ other ∈ items, Canonical decl other) : ∀ other ∈ item :: items, Canonical decl other := by
  intro other member
  rcases List.mem_cons.mp member with rfl | inItems
  · exact here
  · exact later other inItems

theorem mapM_none_of_mem {α : Type} {f : Pattern → Option α} {item : Pattern} (missing : f item = none) :
    ∀ {items : List Pattern}, item ∈ items → items.mapM f = none
  | [], member => by simp at member
  | other :: items, member => by
    rcases List.mem_cons.mp member with rfl | inItems
    · simp [List.mapM_cons, missing]
    · have later := mapM_none_of_mem missing inItems
      cases f other <;> simp [List.mapM_cons, later]

/-- **A law of the declared collection algebra keeps the canonical form** of object terms. -/
theorem LawStep.normal_eq (valid : decl.Valid) {left right : Pattern} (step : LawStep (laws decl) left right)
    (freeLeft : restFree left = true) (freeRight : restFree right = true) :
    normal decl left = normal decl right := by
  induction step with
  | @permute kind elements permuted rest unordered permutation =>
    obtain ⟨rfl, elementsPlain⟩ := restFree_collection freeLeft
    obtain ⟨_, permutedPlain⟩ := restFree_collection freeRight
    have mapped : (elements.map (normal decl)).Perm (permuted.map (normal decl)) := permutation.map _
    rw [normal_collection, normal_collection]
    split
    · obtain ⟨canonicalLeft, valueLeft⟩ := multiply_total valid (canonical_map valid elementsPlain)
      obtain ⟨canonicalRight, valueRight⟩ := multiply_total valid (canonical_map valid permutedPlain)
      exact canonicalLeft.eq canonicalRight (by rw [valueLeft, valueRight, total_perm mapped])
    · split
      · rename_i _ isSum
        obtain ⟨canonicalLeft, valueLeft⟩ := add_union valid (canonical_map valid elementsPlain)
        obtain ⟨canonicalRight, valueRight⟩ := add_union valid (canonical_map valid permutedPlain)
        exact canonicalLeft.eq canonicalRight (by rw [valueLeft, valueRight, union_perm mapped])
      · rw [arrange_perm unordered mapped]
  | @members elements others rest same =>
    obtain ⟨rfl, elementsPlain⟩ := restFree_collection freeLeft
    obtain ⟨_, othersPlain⟩ := restFree_collection freeRight
    have mapped : ∀ a, a ∈ elements.map (normal decl) ↔ a ∈ others.map (normal decl) := members_map same _
    rw [normal_collection, normal_collection]
    split
    · rename_i isProduct
      exact absurd (isProduct.trans valid.productBag) (by decide)
    · split
      · rename_i _ isSum
        obtain ⟨canonicalLeft, valueLeft⟩ := add_union valid (canonical_map valid elementsPlain)
        obtain ⟨canonicalRight, valueRight⟩ := add_union valid (canonical_map valid othersPlain)
        exact canonicalLeft.eq canonicalRight (by rw [valueLeft, valueRight, union_members mapped])
      · rw [arrange_eq_of_presents (kind := .hashSet) mapped]
  | @flatten kind law before inner after rest found =>
    obtain ⟨rfl, elementsPlain⟩ := restFree_collection freeLeft
    obtain ⟨_, flatPlain⟩ := restFree_collection freeRight
    have innerTerm : restFree (.collection kind inner none) = true := elementsPlain _ (by simp)
    obtain ⟨_, innerPlain⟩ := restFree_collection innerTerm
    have beforePlain : ∀ item ∈ before, restFree item = true := fun item member => elementsPlain item (by simp [member])
    have afterPlain : ∀ item ∈ after, restFree item = true := fun item member => elementsPlain item (by simp [member])
    rcases lawFor_cases found with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [normal_product, normal_product, List.map_append, List.map_cons, normal_product]
      obtain ⟨innerCanonical, innerValue⟩ := multiply_total valid (canonical_map valid innerPlain)
      obtain ⟨canonicalLeft, valueLeft⟩ := multiply_total valid
        (canonical_append (canonical_map valid beforePlain) (canonical_cons innerCanonical (canonical_map valid afterPlain)))
      obtain ⟨canonicalRight, valueRight⟩ := multiply_total valid (canonical_map valid flatPlain)
      refine canonicalLeft.eq canonicalRight ?_
      rw [valueLeft, valueRight, total_append, total_cons, innerValue, List.map_append, List.map_append, total_append,
        total_append, plus_assoc]
    · rw [normal_sum valid, normal_sum valid, List.map_append, List.map_cons, normal_sum valid]
      obtain ⟨innerCanonical, innerValue⟩ := add_union valid (canonical_map valid innerPlain)
      obtain ⟨canonicalLeft, valueLeft⟩ := add_union valid
        (canonical_append (canonical_map valid beforePlain) (canonical_cons innerCanonical (canonical_map valid afterPlain)))
      obtain ⟨canonicalRight, valueRight⟩ := add_union valid (canonical_map valid flatPlain)
      refine canonicalLeft.eq canonicalRight ?_
      rw [valueLeft, valueRight, union_append, union_cons, innerValue, List.map_append, List.map_append, union_append,
        union_append, cup_assoc]
  | @unit kind law label before after rest found unitIs =>
    obtain ⟨rfl, elementsPlain⟩ := restFree_collection freeLeft
    obtain ⟨_, restPlain⟩ := restFree_collection freeRight
    have beforePlain : ∀ item ∈ before, restFree item = true := fun item member => elementsPlain item (by simp [member])
    have afterPlain : ∀ item ∈ after, restFree item = true := fun item member => elementsPlain item (by simp [member])
    rcases lawFor_cases found with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases unitIs
      rw [normal_product, normal_product, List.map_append, List.map_cons, normal_apply, List.map_nil]
      obtain ⟨canonicalLeft, valueLeft⟩ := multiply_total valid
        (canonical_append (canonical_map valid beforePlain) (canonical_cons (unit_canonical valid) (canonical_map valid afterPlain)))
      obtain ⟨canonicalRight, valueRight⟩ := multiply_total valid (canonical_map valid restPlain)
      refine canonicalLeft.eq canonicalRight ?_
      rw [valueLeft, valueRight, total_append, total_cons, value_unit valid, List.map_append, total_append, plus_comm (some 0),
        plus_zero]
    · cases unitIs
  | @apply label before after argument changed _ ih =>
    rw [normal_apply, normal_apply]
    simp only [List.map_append, List.map_cons,
      ih (restFree_apply freeLeft argument (by simp)) (restFree_apply freeRight changed (by simp))]
  | lambda _ ih =>
    rw [normal_lambda, normal_lambda, ih (by simpa [restFree] using freeLeft) (by simpa [restFree] using freeRight)]
  | multiLambda _ ih =>
    rw [normal_multiLambda, normal_multiLambda, ih (by simpa [restFree] using freeLeft) (by simpa [restFree] using freeRight)]
  | substBody _ ih =>
    rw [normal_subst, normal_subst, ih (restFree_subst freeLeft).1 (restFree_subst freeRight).1]
  | substReplacement _ ih =>
    rw [normal_subst, normal_subst, ih (restFree_subst freeLeft).2 (restFree_subst freeRight).2]
  | @element kind before after element changed rest _ ih =>
    obtain ⟨rfl, leftPlain⟩ := restFree_collection freeLeft
    obtain ⟨_, rightPlain⟩ := restFree_collection freeRight
    have same : (before ++ element :: after).map (normal decl) = (before ++ changed :: after).map (normal decl) := by
      simp only [List.map_append, List.map_cons, ih (leftPlain element (by simp)) (rightPlain changed (by simp))]
    rw [normal_collection, normal_collection, same]

/-- **A wrapper law keeps the canonical form** of object terms. -/
theorem WrapperStep.normal_eq (valid : decl.Valid) {left right : Pattern} (step : Wrappers.WrapperStep (laws decl) left right)
    (freeLeft : restFree left = true) (freeRight : restFree right = true) :
    normal decl left = normal decl right := by
  induction step with
  | @singleton kind law element found =>
    obtain ⟨_, elementsPlain⟩ := restFree_collection freeLeft
    have canonicalElement := normal_canonical valid element (elementsPlain element (by simp))
    rcases lawFor_cases found with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [normal_product]
      obtain ⟨canonicalLeft, valueLeft⟩ := multiply_total valid (canonical_map valid elementsPlain)
      exact canonicalLeft.eq canonicalElement
        (by rw [valueLeft, List.map_cons, List.map_nil, total_cons, total_nil, plus_zero])
    · rw [normal_sum valid]
      obtain ⟨canonicalLeft, valueLeft⟩ := add_union valid (canonical_map valid elementsPlain)
      exact canonicalLeft.eq canonicalElement
        (by rw [valueLeft, List.map_cons, List.map_nil, union_cons, union_nil, cup_empty])
  | @empty kind law label found unitIs =>
    rcases lawFor_cases found with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases unitIs
      rw [normal_product, List.map_nil, normal_apply, List.map_nil]
      obtain ⟨canonicalLeft, valueLeft⟩ := multiply_total valid (decl := decl) (items := []) (by simp)
      exact canonicalLeft.eq (unit_canonical valid) (by rw [valueLeft, total_nil, value_unit valid])
    · cases unitIs
  | @apply label before after argument changed _ ih =>
    rw [normal_apply, normal_apply]
    simp only [List.map_append, List.map_cons,
      ih (restFree_apply freeLeft argument (by simp)) (restFree_apply freeRight changed (by simp))]
  | lambda _ ih =>
    rw [normal_lambda, normal_lambda, ih (by simpa [restFree] using freeLeft) (by simpa [restFree] using freeRight)]
  | multiLambda _ ih =>
    rw [normal_multiLambda, normal_multiLambda, ih (by simpa [restFree] using freeLeft) (by simpa [restFree] using freeRight)]
  | substBody _ ih =>
    rw [normal_subst, normal_subst, ih (restFree_subst freeLeft).1 (restFree_subst freeRight).1]
  | substReplacement _ ih =>
    rw [normal_subst, normal_subst, ih (restFree_subst freeLeft).2 (restFree_subst freeRight).2]
  | @element kind before after element changed rest _ ih =>
    obtain ⟨rfl, leftPlain⟩ := restFree_collection freeLeft
    obtain ⟨_, rightPlain⟩ := restFree_collection freeRight
    have same : (before ++ element :: after).map (normal decl) = (before ++ changed :: after).map (normal decl) := by
      simp only [List.map_append, List.map_cons, ih (leftPlain element (by simp)) (rightPlain changed (by simp))]
    rw [normal_collection, normal_collection, same]

/-- Composition distributes over summation, for denotations. -/
theorem plus_cup_right (a b c : Option (Finset (Multiset Pattern))) : plus (cup a b) c = cup (plus a c) (plus b c) := by
  rw [plus_comm, plus_cup, plus_comm c a, plus_comm c b]

/-- **A composition holding a sum denotes the union of the compositions holding its summands.** -/
theorem union_multiply (valid : decl.Valid) {before after : List Pattern}
    (canonicalBefore : ∀ item ∈ before, Canonical decl item) (canonicalAfter : ∀ item ∈ after, Canonical decl item) :
    ∀ (summands : List Pattern), (∀ item ∈ summands, Canonical decl item) → summands ≠ [] →
      union decl (summands.map fun summand => multiply decl (before ++ summand :: after)) =
        plus (total decl before) (plus (union decl summands) (total decl after))
  | [summand], canonical, _ => by
    have valued := (multiply_total valid (canonical_append canonicalBefore
      (canonical_cons (canonical summand (by simp)) canonicalAfter))).2
    rw [List.map_cons, List.map_nil, union_cons, union_nil, cup_empty, valued, union_cons, union_nil, cup_empty,
      total_append, total_cons]
  | summand :: next :: others, canonical, _ => by
    have valued := (multiply_total valid (canonical_append canonicalBefore
      (canonical_cons (canonical summand (by simp)) canonicalAfter))).2
    have later := union_multiply valid canonicalBefore canonicalAfter (next :: others)
      (fun item member => canonical item (List.mem_cons_of_mem _ member)) (by simp)
    rw [List.map_cons, union_cons, valued, later, union_cons (item := summand), plus_cup_right, plus_cup, total_append,
      total_cons]

/-- **A step keeps the canonical form** of object terms. -/
theorem Step.normal_eq (valid : decl.Valid) {left right : Pattern} (step : Step decl left right)
    (freeLeft : restFree left = true) (freeRight : restFree right = true) :
    normal decl left = normal decl right := by
  induction step with
  | @repeated before middle after element =>
    obtain ⟨_, leftPlain⟩ := restFree_collection freeLeft
    obtain ⟨_, rightPlain⟩ := restFree_collection freeRight
    rw [normal_sum valid, normal_sum valid]
    obtain ⟨canonicalLeft, valueLeft⟩ := add_union valid (canonical_map valid leftPlain)
    obtain ⟨canonicalRight, valueRight⟩ := add_union valid (canonical_map valid rightPlain)
    refine canonicalLeft.eq canonicalRight ?_
    rw [valueLeft, valueRight]
    have permLeft : ((before ++ element :: middle ++ element :: after).map (normal decl)).Perm
        (normal decl element :: normal decl element :: (before ++ middle ++ after).map (normal decl)) := by
      rw [List.perm_iff_count]
      intro item
      simp only [List.map_append, List.map_cons, List.count_append, List.count_cons]
      omega
    have permRight : ((before ++ element :: middle ++ after).map (normal decl)).Perm
        (normal decl element :: (before ++ middle ++ after).map (normal decl)) := by
      rw [List.perm_iff_count]
      intro item
      simp only [List.map_append, List.map_cons, List.count_append, List.count_cons]
      omega
    rw [union_perm permLeft, union_perm permRight]
    simp only [union_cons]
    rw [← cup_assoc, cup_self]
  | @absorbProduct before after =>
    rw [normal_product, normal_apply, List.map_nil]
    unfold multiply
    rw [mapM_none_of_mem (products_none.mpr rfl) (by simp [normal_apply])]
  | @absorbSum before after =>
    rw [normal_sum valid, normal_apply, List.map_nil]
    unfold add
    rw [mapM_none_of_mem (products_none.mpr rfl) (by simp [normal_apply])]
  | @distribute before after summands atLeastTwo =>
    obtain ⟨_, leftPlain⟩ := restFree_collection freeLeft
    have beforePlain : ∀ item ∈ before, restFree item = true := fun item member => leftPlain item (by simp [member])
    have afterPlain : ∀ item ∈ after, restFree item = true := fun item member => leftPlain item (by simp [member])
    obtain ⟨_, summandsPlain⟩ := restFree_collection (leftPlain (.collection decl.sum summands none) (by simp))
    have nonempty : summands ≠ [] := by rintro rfl; simp at atLeastTwo
    rw [normal_product, normal_sum valid, List.map_append, List.map_cons, normal_sum valid, List.map_map]
    have rightShape : (fun summand => normal decl (Pattern.collection decl.product (before ++ summand :: after) none)) =
        fun summand => multiply decl (before.map (normal decl) ++ normal decl summand :: after.map (normal decl)) := by
      funext summand
      rw [normal_product, List.map_append, List.map_cons]
    rw [Function.comp_def, rightShape]
    have canonicalSummands := canonical_map valid summandsPlain
    obtain ⟨sumCanonical, sumValue⟩ := add_union valid canonicalSummands
    obtain ⟨canonicalLeft, valueLeft⟩ := multiply_total valid (canonical_append (canonical_map valid beforePlain)
      (canonical_cons sumCanonical (canonical_map valid afterPlain)))
    have rightItems : ∀ item ∈ summands.map (fun summand =>
        multiply decl (before.map (normal decl) ++ normal decl summand :: after.map (normal decl))), Canonical decl item := by
      intro item member
      obtain ⟨summand, summandMember, rfl⟩ := List.mem_map.mp member
      exact (multiply_total valid (canonical_append (canonical_map valid beforePlain)
        (canonical_cons (normal_canonical valid summand (summandsPlain summand summandMember))
          (canonical_map valid afterPlain)))).1
    obtain ⟨canonicalRight, valueRight⟩ := add_union valid rightItems
    refine canonicalLeft.eq canonicalRight ?_
    rw [valueLeft, valueRight, total_append, total_cons, sumValue]
    have distributed := union_multiply valid (canonical_map valid beforePlain) (canonical_map valid afterPlain)
      (summands.map (normal decl)) canonicalSummands (by simpa using nonempty)
    rw [List.map_map, Function.comp_def] at distributed
    rw [distributed]
  | @apply label before after argument changed _ ih =>
    rw [normal_apply, normal_apply]
    simp only [List.map_append, List.map_cons,
      ih (restFree_apply freeLeft argument (by simp)) (restFree_apply freeRight changed (by simp))]
  | lambda _ ih =>
    rw [normal_lambda, normal_lambda, ih (by simpa [restFree] using freeLeft) (by simpa [restFree] using freeRight)]
  | multiLambda _ ih =>
    rw [normal_multiLambda, normal_multiLambda, ih (by simpa [restFree] using freeLeft) (by simpa [restFree] using freeRight)]
  | substBody _ ih =>
    rw [normal_subst, normal_subst, ih (restFree_subst freeLeft).1 (restFree_subst freeRight).1]
  | substReplacement _ ih =>
    rw [normal_subst, normal_subst, ih (restFree_subst freeLeft).2 (restFree_subst freeRight).2]
  | @element kind before after element changed rest _ ih =>
    obtain ⟨rfl, leftPlain⟩ := restFree_collection freeLeft
    obtain ⟨_, rightPlain⟩ := restFree_collection freeRight
    have same : (before ++ element :: after).map (normal decl) = (before ++ changed :: after).map (normal decl) := by
      simp only [List.map_append, List.map_cons, ih (leftPlain element (by simp)) (rightPlain changed (by simp))]
    rw [normal_collection, normal_collection, same]

/-- **Every move between object terms keeps the canonical form.** -/
theorem Move.normal_eq (valid : decl.Valid) {left right : Pattern} (move : Move decl left right)
    (freeLeft : restFree left = true) (freeRight : restFree right = true) :
    normal decl left = normal decl right := by
  rcases move with lawMove | wrapped | stepped
  · exact LawStep.normal_eq valid lawMove freeLeft freeRight
  · exact WrapperStep.normal_eq valid wrapped freeLeft freeRight
  · exact Step.normal_eq valid stepped freeLeft freeRight

/-! ## The canonical form is sound on terms without empty sums -/

theorem total_ne_zero : ∀ (items : List Pattern), (∀ item ∈ items, value decl item ≠ some ∅) →
    total decl items ≠ some ∅
  | [], _ => by simp [total_nil, ← Finset.singleton_zero]
  | item :: items, each => by
    rw [total_cons]
    have here := each item List.mem_cons_self
    have later := total_ne_zero items (fun other member => each other (List.mem_cons_of_mem _ member))
    cases valued : value decl item <;> cases totaled : total decl items <;> simp_all [plus, Finset.add_eq_empty]

theorem union_ne_zero : ∀ (items : List Pattern), items ≠ [] → (∀ item ∈ items, value decl item ≠ some ∅) →
    union decl items ≠ some ∅
  | [], nonempty, _ => absurd rfl nonempty
  | item :: items, _, each => by
    rw [union_cons]
    have here := each item List.mem_cons_self
    cases valued : value decl item <;> cases joined : union decl items <;> simp_all [cup]

/-- A plain term never denotes the zero. -/
theorem value_normal_ne_zero (valid : decl.Valid) (pattern : Pattern) (isPlain : plain decl pattern = true) :
    value decl (normal decl pattern) ≠ some ∅ := by
  have atomValue : ∀ {atom : Pattern}, IsAtom decl atom → value decl atom ≠ some ∅ := by
    intro atom isAtom
    simp [value, products_atom isAtom, presented]
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
    rw [normal_bvar]
    exact atomValue (isAtom_of_shape (fun _ same => by cases same) (fun _ same => by cases same)
      (fun _ same => by cases same))
  | hfvar name =>
    rw [normal_fvar]
    exact atomValue (isAtom_of_shape (fun _ same => by cases same) (fun _ same => by cases same)
      (fun _ same => by cases same))
  | happly label arguments _ =>
    rw [normal_apply]
    cases arguments with
    | nil =>
      by_cases absorbing : label = decl.absorbing
      · subst absorbing; rw [List.map_nil, value_absorbing]; simp
      · by_cases unit : label = decl.unit
        · subst unit; rw [List.map_nil, value_unit valid]; simp [Finset.singleton_zero.symm]
        · exact atomValue (isAtom_of_shape
            (fun other same => by cases same; exact ⟨absorbing, unit⟩) (fun _ same => by cases same)
            (fun _ same => by cases same))
    | cons first others =>
      exact atomValue (isAtom_of_shape (fun _ same => by cases same) (fun _ same => by cases same)
        (fun _ same => by cases same))
  | hlambda binder body _ =>
    rw [normal_lambda]
    exact atomValue (isAtom_of_shape (fun _ same => by cases same) (fun _ same => by cases same)
      (fun _ same => by cases same))
  | hmultiLambda arity binders body _ =>
    rw [normal_multiLambda]
    exact atomValue (isAtom_of_shape (fun _ same => by cases same) (fun _ same => by cases same)
      (fun _ same => by cases same))
  | hsubst body replacement _ _ =>
    rw [normal_subst]
    exact atomValue (isAtom_of_shape (fun _ same => by cases same) (fun _ same => by cases same)
      (fun _ same => by cases same))
  | hcollection kind elements rest ih =>
    obtain ⟨rfl, nonempty, elementsPlain⟩ := plain_collection isPlain
    have canonical := canonical_map (decl := decl) valid fun element member =>
      restFree_of_plain (elementsPlain element member)
    have each : ∀ item ∈ elements.map (normal decl), value decl item ≠ some ∅ := by
      intro item member
      obtain ⟨element, elementMember, rfl⟩ := List.mem_map.mp member
      exact ih element elementMember (elementsPlain element elementMember)
    rw [normal_collection]
    split
    · rw [(multiply_total valid canonical).2]
      exact total_ne_zero _ each
    · split
      · rename_i _ isSum
        rw [(add_union valid canonical).2]
        exact union_ne_zero _ (by simpa using nonempty isSum) each
      · rename_i notProduct notSum
        exact atomValue (isAtom_of_shape (fun _ same => by cases same)
          (fun _ same => by cases same; exact notProduct rfl) (fun _ same => by cases same; exact notSum rfl))

/-- A plain term's canonical form is not the empty sum. -/
theorem normal_ne_empty (valid : decl.Valid) {pattern : Pattern} (isPlain : plain decl pattern = true) :
    normal decl pattern ≠ .collection decl.sum [] none := by
  intro empty
  have zero := value_normal_ne_zero valid pattern isPlain
  rw [empty] at zero
  exact zero (by simp [value, products, presented])

/-! ## Canonical forms of processes -/

/-- **The canonical form of a term without empty sums has no empty sum.** -/
theorem plain_normal (valid : decl.Valid) (pattern : Pattern) (isPlain : plain decl pattern = true) :
    plain decl (normal decl pattern) = true := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => rw [normal_bvar]; rfl
  | hfvar name => rw [normal_fvar]; rfl
  | happly label arguments ih =>
    rw [normal_apply]
    simp only [plain]
    exact plainList_iff.mpr fun item member => by
      obtain ⟨argument, argumentMember, rfl⟩ := List.mem_map.mp member
      exact ih argument argumentMember (plain_apply isPlain argument argumentMember)
  | hlambda binder body ih => rw [normal_lambda]; simpa [plain] using ih (by simpa [plain] using isPlain)
  | hmultiLambda arity binders body ih =>
    rw [normal_multiLambda]; simpa [plain] using ih (by simpa [plain] using isPlain)
  | hsubst body replacement bodyIH replacementIH =>
    have parts : plain decl body = true ∧ plain decl replacement = true := by simpa [plain] using isPlain
    rw [normal_subst]
    simp [plain, bodyIH parts.1, replacementIH parts.2]
  | hcollection kind elements rest ih =>
    obtain ⟨rfl, nonempty, elementsPlain⟩ := plain_collection isPlain
    have itemsPlain : ∀ item ∈ elements.map (normal decl), plain decl item = true := by
      intro item member
      obtain ⟨element, elementMember, rfl⟩ := List.mem_map.mp member
      exact ih element elementMember (elementsPlain element elementMember)
    have itemsNotEmpty : ∀ item ∈ elements.map (normal decl), item ≠ .collection decl.sum [] none := by
      intro item member
      obtain ⟨element, elementMember, rfl⟩ := List.mem_map.mp member
      exact normal_ne_empty valid (elementsPlain element elementMember)
    rw [normal_collection]
    split
    · unfold multiply
      cases found : (elements.map (normal decl)).mapM (products decl) with
      | none => rfl
      | some factors =>
        apply plain_sumOf valid
        · apply choices_ne_nil
          intro factor member
          obtain ⟨item, itemMember, itemFound⟩ := mapM_mem found factor member
          exact products_ne_nil itemFound (itemsNotEmpty item itemMember)
        · apply choices_plain
          intro factor member
          obtain ⟨item, itemMember, itemFound⟩ := mapM_mem found factor member
          exact products_plain itemFound (itemsPlain item itemMember)
    · split
      · rename_i _ isSum
        unfold add
        cases found : (elements.map (normal decl)).mapM (products decl) with
        | none => rfl
        | some parts =>
          apply plain_sumOf valid
          · obtain ⟨first, others, shape⟩ := List.exists_cons_of_ne_nil (nonempty isSum)
            rw [shape, List.map_cons] at found
            obtain ⟨part, rest, partFound, _, rfl⟩ := mapM_cons_some found
            have partNonempty := products_ne_nil partFound
              (itemsNotEmpty _ (by rw [shape, List.map_cons]; exact List.mem_cons_self))
            obtain ⟨chosen, chosenMember⟩ := List.exists_mem_of_ne_nil part partNonempty
            intro empty
            have inFlat : chosen ∈ (part :: rest).flatten := List.mem_flatten.mpr ⟨part, List.mem_cons_self, chosenMember⟩
            rw [empty] at inFlat
            simp at inFlat
          · intro chosen member atom inChosen
            obtain ⟨part, partMember, chosenMember⟩ := List.mem_flatten.mp member
            obtain ⟨item, itemMember, itemFound⟩ := mapM_mem found part partMember
            exact products_plain itemFound (itemsPlain item itemMember) chosen chosenMember atom inChosen
      · rename_i notProduct notSum
        have arrangedPlain : ∀ item ∈ arrange kind (elements.map (normal decl)), plain decl item = true :=
          fun item member => itemsPlain item ((arrange_mem item).mp member)
        simp only [plain, Option.isNone_none, Bool.true_and, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
          Bool.and_eq_false_iff, decide_eq_false_iff_not]
        exact ⟨.inl notSum, plainList_iff.mpr arrangedPlain⟩

/-- **The canonical form is sound**: every process is congruent to its canonical form. -/
theorem congruent_normal (valid : decl.Valid) : ∀ pattern : Pattern, plain decl pattern = true →
    Congruent decl pattern (normal decl pattern)
  | .bvar index, _ => by rw [normal]; exact .refl _
  | .fvar name, _ => by rw [normal]; exact .refl _
  | .apply label arguments, isPlain => by
    rw [normal]
    have argumentsPlain := plain_apply isPlain
    have each : ∀ item ∈ arguments, Congruent decl item (normal decl item) := fun item member =>
      have : sizeOf item < sizeOf (Pattern.apply label arguments) := by
        have := List.sizeOf_lt_of_mem member; simp only [Pattern.apply.sizeOf_spec]; omega
      congruent_normal valid item (argumentsPlain item member)
    simpa using Congruent.arguments label (normal decl) [] arguments (by simp)
      (fun item member => ⟨argumentsPlain item member, plain_normal valid item (argumentsPlain item member)⟩) each
  | .lambda binder body, isPlain => by
    rw [normal]
    exact Congruent.lift (f := .lambda binder) (fun bodyPlain => by simpa [plain] using bodyPlain)
      (fun step => .lambda step) (fun step => .lambda step) (fun step => .lambda step)
      (congruent_normal valid body (by simpa [plain] using isPlain))
  | .multiLambda arity binders body, isPlain => by
    rw [normal]
    exact Congruent.lift (f := .multiLambda arity binders) (fun bodyPlain => by simpa [plain] using bodyPlain)
      (fun step => .multiLambda step) (fun step => .multiLambda step) (fun step => .multiLambda step)
      (congruent_normal valid body (by simpa [plain] using isPlain))
  | .subst body replacement, isPlain => by
    rw [normal]
    have parts : plain decl body = true ∧ plain decl replacement = true := by simpa [plain] using isPlain
    exact .trans _ _ _
      (Congruent.lift (f := fun x => .subst x replacement) (fun xPlain => by simp [plain, xPlain, parts.2])
        (fun step => .substBody step) (fun step => .substBody step) (fun step => .substBody step)
        (congruent_normal valid body parts.1))
      (Congruent.lift (f := fun x => .subst (normal decl body) x)
        (fun xPlain => by simp [plain, xPlain, plain_normal valid body parts.1])
        (fun step => .substReplacement step) (fun step => .substReplacement step) (fun step => .substReplacement step)
        (congruent_normal valid replacement parts.2))
  | .collection kind elements rest, isPlain => by
    obtain ⟨rfl, nonempty, elementsPlain⟩ := plain_collection isPlain
    have each : ∀ item ∈ elements, Congruent decl item (normal decl item) := fun item member =>
      have : sizeOf item < sizeOf (Pattern.collection kind elements none) := by
        have := List.sizeOf_lt_of_mem member; simp only [Pattern.collection.sizeOf_spec]; omega
      congruent_normal valid item (elementsPlain item member)
    have normalsPlain : ∀ item ∈ elements.map (normal decl), plain decl item = true := fun item member => by
      obtain ⟨element, elementMember, rfl⟩ := List.mem_map.mp member
      exact plain_normal valid element (elementsPlain element elementMember)
    have mapped : Congruent decl (.collection kind elements none) (.collection kind (elements.map (normal decl)) none) := by
      simpa using Congruent.mapPointwise (decl := decl) kind (fun item => item) (normal decl) [] elements (by simp)
        (fun item member => ⟨elementsPlain item member, plain_normal valid item (elementsPlain item member)⟩) each
    have mappedNonempty : kind = decl.sum → elements.map (normal decl) ≠ [] := fun same => by
      simpa using nonempty same
    have arranged : Congruent decl (.collection kind (elements.map (normal decl)) none)
        (.collection kind (arrange kind (elements.map (normal decl))) none) := by
      have mappedPlain : plain decl (.collection kind (elements.map (normal decl)) none) = true :=
        plain_collection_iff.mpr ⟨mappedNonempty, normalsPlain⟩
      cases kind with
      | vec => exact .refl _
      | hashBag => exact permute rfl (sortLex_perm _).symm mappedPlain
      | hashSet =>
        refine .rel _ _ ⟨mappedPlain, plain_collection_iff.mpr ⟨fun same => ?_, fun item member =>
          normalsPlain item ((arrange_mem item).mp member)⟩, .inl (.members fun a => (arrange_mem a).symm)⟩
        intro empty
        obtain ⟨item, member⟩ := List.exists_mem_of_ne_nil _ (mappedNonempty same)
        have inArranged : item ∈ arrange .hashSet (elements.map (normal decl)) := (arrange_mem item).mpr member
        rw [empty] at inArranged
        exact absurd inArranged (List.not_mem_nil)
    rw [normal_collection]
    split
    · rename_i same; subst same
      exact .trans _ _ _ mapped (multiply_sound valid normalsPlain)
    · split
      · rename_i _ same; subst same
        exact .trans _ _ _ mapped (add_sound valid (mappedNonempty rfl) normalsPlain)
      · exact .trans _ _ _ mapped arranged
termination_by pattern => sizeOf pattern

/-- **The canonical form is sound in the model**: every process is equal in the model to its canonical
form. -/
theorem to_normal (valid : decl.Valid) (pattern : Pattern) (isPlain : plain decl pattern = true) :
    Equal decl pattern (normal decl pattern) :=
  (congruent_normal valid pattern isPlain).equal

/-! ## The canonical form decides the laws -/

/-- Every collection rest dropped: an object term. -/
def dropRests : Pattern → Pattern
  | .bvar index => .bvar index
  | .fvar name => .fvar name
  | .apply label arguments => .apply label (arguments.map dropRests)
  | .lambda binder body => .lambda binder (dropRests body)
  | .multiLambda arity binders body => .multiLambda arity binders (dropRests body)
  | .subst body replacement => .subst (dropRests body) (dropRests replacement)
  | .collection kind elements _ => .collection kind (elements.map dropRests) none
decreasing_by all_goals sizeOf_pattern_dec

theorem restFree_dropRests (pattern : Pattern) : restFree (dropRests pattern) = true := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => rw [dropRests]; rfl
  | hfvar name => rw [dropRests]; rfl
  | happly label arguments ih =>
    rw [dropRests]
    simp only [restFree]
    exact restFreeList_iff.mpr fun item member => by
      obtain ⟨argument, argumentMember, rfl⟩ := List.mem_map.mp member
      exact ih argument argumentMember
  | hlambda binder body ih => rw [dropRests]; simpa [restFree] using ih
  | hmultiLambda arity binders body ih => rw [dropRests]; simpa [restFree] using ih
  | hsubst body replacement bodyIH replacementIH => rw [dropRests]; simp [restFree, bodyIH, replacementIH]
  | hcollection kind elements rest ih =>
    rw [dropRests]
    simp only [restFree, Option.isNone_none, Bool.true_and]
    exact restFreeList_iff.mpr fun item member => by
      obtain ⟨element, elementMember, rfl⟩ := List.mem_map.mp member
      exact ih element elementMember

theorem dropRests_of_restFree (pattern : Pattern) (isFree : restFree pattern = true) : dropRests pattern = pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => rw [dropRests]
  | hfvar name => rw [dropRests]
  | happly label arguments ih =>
    rw [dropRests]
    congr 1
    conv => rhs; rw [← List.map_id arguments]
    exact List.map_congr_left fun argument member => ih argument member (restFree_apply isFree argument member)
  | hlambda binder body ih => rw [dropRests, ih (by simpa [restFree] using isFree)]
  | hmultiLambda arity binders body ih => rw [dropRests, ih (by simpa [restFree] using isFree)]
  | hsubst body replacement bodyIH replacementIH =>
    rw [dropRests, bodyIH (restFree_subst isFree).1, replacementIH (restFree_subst isFree).2]
  | hcollection kind elements rest ih =>
    obtain ⟨rfl, elementsFree⟩ := restFree_collection isFree
    rw [dropRests]
    congr 1
    conv => rhs; rw [← List.map_id elements]
    exact List.map_congr_left fun element member => ih element member (elementsFree element member)

theorem dropRests_apply (label : String) (arguments : List Pattern) :
    dropRests (.apply label arguments) = .apply label (arguments.map dropRests) := by rw [dropRests]
theorem dropRests_collection (kind : CollType) (elements : List Pattern) (rest : Option String) :
    dropRests (.collection kind elements rest) = .collection kind (elements.map dropRests) none := by rw [dropRests]

/-- **Dropping rests keeps every move.** -/
theorem Move.dropRests {left right : Pattern} (move : Move decl left right) :
    Move decl (Distributive.dropRests left) (Distributive.dropRests right) := by
  rcases move with lawMove | wrapped | stepped
  · left
    induction lawMove with
    | permute unordered permutation =>
      rw [dropRests_collection, dropRests_collection]
      exact .permute unordered (permutation.map _)
    | members same =>
      rw [dropRests_collection, dropRests_collection]
      exact .members (members_map same _)
    | flatten found =>
      rw [dropRests_collection, dropRests_collection]
      simpa [List.map_append, dropRests_collection] using LawStep.flatten (rest := none) found
    | unit found unitIs =>
      rw [dropRests_collection, dropRests_collection]
      simpa [List.map_append, dropRests_apply] using LawStep.unit (rest := none) found unitIs
    | apply _ ih =>
      rw [dropRests_apply, dropRests_apply]
      simpa [List.map_append] using LawStep.apply ih
    | lambda _ ih => rw [Distributive.dropRests, Distributive.dropRests]; exact .lambda ih
    | multiLambda _ ih => rw [Distributive.dropRests, Distributive.dropRests]; exact .multiLambda ih
    | substBody _ ih => rw [Distributive.dropRests, Distributive.dropRests]; exact .substBody ih
    | substReplacement _ ih => rw [Distributive.dropRests, Distributive.dropRests]; exact .substReplacement ih
    | element _ ih =>
      rw [dropRests_collection, dropRests_collection]
      simpa [List.map_append] using LawStep.element (rest := none) ih
  · right; left
    induction wrapped with
    | singleton found =>
      rw [dropRests_collection]
      simpa using Wrappers.WrapperStep.singleton found
    | empty found unitIs =>
      rw [dropRests_collection, dropRests_apply]
      simpa using Wrappers.WrapperStep.empty found unitIs
    | apply _ ih =>
      rw [dropRests_apply, dropRests_apply]
      simpa [List.map_append] using Wrappers.WrapperStep.apply ih
    | lambda _ ih => rw [Distributive.dropRests, Distributive.dropRests]; exact .lambda ih
    | multiLambda _ ih => rw [Distributive.dropRests, Distributive.dropRests]; exact .multiLambda ih
    | substBody _ ih => rw [Distributive.dropRests, Distributive.dropRests]; exact .substBody ih
    | substReplacement _ ih => rw [Distributive.dropRests, Distributive.dropRests]; exact .substReplacement ih
    | element _ ih =>
      rw [dropRests_collection, dropRests_collection]
      simpa [List.map_append] using Wrappers.WrapperStep.element (rest := none) ih
  · right; right
    induction stepped with
    | repeated =>
      rw [dropRests_collection, dropRests_collection]
      simpa [List.map_append] using Step.repeated (decl := decl)
    | absorbProduct =>
      rw [dropRests_collection, dropRests_apply]
      simpa [List.map_append, dropRests_apply] using Step.absorbProduct (decl := decl)
    | absorbSum =>
      rw [dropRests_collection, dropRests_apply]
      simpa [List.map_append, dropRests_apply] using Step.absorbSum (decl := decl)
    | @distribute before after summands atLeastTwo =>
      rw [dropRests_collection, dropRests_collection]
      have moved := Step.distribute (decl := decl) (before := before.map Distributive.dropRests)
        (after := after.map Distributive.dropRests) (summands := summands.map Distributive.dropRests) (by simpa using atLeastTwo)
      simpa [List.map_append, List.map_map, Function.comp_def, dropRests_collection] using moved
    | apply _ ih =>
      rw [dropRests_apply, dropRests_apply]
      simpa [List.map_append] using Step.apply ih
    | lambda _ ih => rw [Distributive.dropRests, Distributive.dropRests]; exact .lambda ih
    | multiLambda _ ih => rw [Distributive.dropRests, Distributive.dropRests]; exact .multiLambda ih
    | substBody _ ih => rw [Distributive.dropRests, Distributive.dropRests]; exact .substBody ih
    | substReplacement _ ih => rw [Distributive.dropRests, Distributive.dropRests]; exact .substReplacement ih
    | element _ ih =>
      rw [dropRests_collection, dropRests_collection]
      simpa [List.map_append] using Step.element (rest := none) ih

/-- Equal terms have one canonical form once their rests are dropped. -/
theorem normal_dropRests_eq (valid : decl.Valid) {left right : Pattern} (related : Equal decl left right) :
    normal decl (dropRests left) = normal decl (dropRests right) := by
  induction related with
  | rel a b move => exact Move.normal_eq valid (Move.dropRests move) (restFree_dropRests a) (restFree_dropRests b)
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

/-- **Equal object terms have one canonical form.** -/
theorem normal_eq_of_equal (valid : decl.Valid) {left right : Pattern} (related : Equal decl left right)
    (freeLeft : restFree left = true) (freeRight : restFree right = true) : normal decl left = normal decl right := by
  have projected := normal_dropRests_eq valid related
  rwa [dropRests_of_restFree left freeLeft, dropRests_of_restFree right freeRight] at projected

/-- **The canonical form decides the laws** on terms without empty sums: two such terms are equal in the
model exactly when they have one canonical form. -/
theorem normal_eq_iff (valid : decl.Valid) {left right : Pattern} (plainLeft : plain decl left = true)
    (plainRight : plain decl right = true) : normal decl left = normal decl right ↔ Equal decl left right := by
  constructor
  · intro same
    have toRight := to_normal valid right plainRight
    rw [← same] at toRight
    exact .trans _ _ _ (to_normal valid left plainLeft) (.symm _ _ toRight)
  · intro related
    exact normal_eq_of_equal valid related (restFree_of_plain plainLeft) (restFree_of_plain plainRight)

/-- **The canonical form decides the congruence of processes.** -/
theorem congruent_iff (valid : decl.Valid) {left right : Pattern} (plainLeft : plain decl left = true)
    (plainRight : plain decl right = true) : Congruent decl left right ↔ normal decl left = normal decl right := by
  constructor
  · intro related
    exact normal_eq_of_equal valid related.equal (restFree_of_plain plainLeft) (restFree_of_plain plainRight)
  · intro same
    have toRight := congruent_normal valid right plainRight
    rw [← same] at toRight
    exact .trans _ _ _ (congruent_normal valid left plainLeft) (.symm _ _ toRight)

/-- On processes, equality in the model is the congruence of processes: passing through patterns that
are not processes relates no further processes. -/
theorem congruent_iff_equal (valid : decl.Valid) {left right : Pattern} (plainLeft : plain decl left = true)
    (plainRight : plain decl right = true) : Congruent decl left right ↔ Equal decl left right :=
  (congruent_iff valid plainLeft plainRight).trans (normal_eq_iff valid plainLeft plainRight)

/-! ## Examples: oriented processes -/

namespace Examples

/-- Parallel composition over a bag with unit `0`, summation over a set, and chaos. -/
def oriented : Decl := { product := .hashBag, unit := "PZero", sum := .hashSet, absorbing := "PChaos" }

def zero : Pattern := .apply "PZero" []
def chaos : Pattern := .apply "PChaos" []
def atom (label : String) : Pattern := .apply label [.fvar "x"]
def par (items : List Pattern) : Pattern := .collection .hashBag items none
def sum (items : List Pattern) : Pattern := .collection .hashSet items none

def p : Pattern := atom "P"
def q : Pattern := atom "Q"
def r : Pattern := atom "R"

/-! **Positive**: composition distributes over a sum. -/
#guard normal oriented (par [p, sum [q, r]]) == normal oriented (sum [par [p, q], par [p, r]])
#guard normal oriented (par [p, sum [q, r]]) == sum [par [p, q], par [p, r]]

/-! **Positive**: two sums multiply out into four products. -/
#guard normal oriented (par [sum [p, q], sum [r, atom "S"]]) ==
  normal oriented (sum [par [p, r], par [p, atom "S"], par [q, r], par [q, atom "S"]])

/-! **Positive**: chaos absorbs composition and summation, at any depth. -/
#guard normal oriented (par [p, chaos]) == chaos
#guard normal oriented (sum [p, chaos]) == chaos
#guard normal oriented (par [q, sum [p, par [chaos, r]]]) == chaos

/-! **Positive**: summation is idempotent and flattens; composition is not idempotent. -/
#guard normal oriented (sum [p, p]) == p
#guard normal oriented (sum [p, sum [q, p]]) == normal oriented (sum [p, q])
#guard normal oriented (par [p, p]) != p

/-! **Positive**: the wrapper laws of both collections. -/
#guard normal oriented (par [p]) == p
#guard normal oriented (par []) == zero
#guard normal oriented (sum [p]) == p
#guard normal oriented (par [p, zero]) == p

/-! The empty sum is the zero of the canonical form, as in the free algebra: a composition holding it is
the empty sum, and a sum holding it loses it. The laws only prove the second. -/
#guard normal oriented (par [p, sum []]) == sum []
#guard normal oriented (sum [p, sum []]) == p

/-! **Negative**: a sum of different products stays a sum, and `0` is no unit of summation. -/
#guard normal oriented (sum [p, q]) != p
#guard normal oriented (sum [p, zero]) != p

end Examples

end Mettapedia.OSLF.MeTTaIL.Distributive

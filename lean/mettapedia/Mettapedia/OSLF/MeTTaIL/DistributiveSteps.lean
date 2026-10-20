import Mettapedia.OSLF.MeTTaIL.DistributiveLaws

/-!
# One step modulo composition distributing over an idempotent sum

Summation is a context of reduction and is idempotent, so a process steps by refining one member of
its ensemble while it may keep the unrefined member too, and a redex shared by several members, as a
common factor of a presentation, fires in all of them at once. On what processes denote, the free
algebra of sets of products: with `S` the products of a process and `r` the atoms of a redex, one
step reaches exactly `(S \ R) ∪ (reduct ⊕ D)`, where `D` is a nonempty set of remainders whose
products `r + d` all lie in `S`, and `R` is any set of those products, the ones the step removes.

- `Reduces`: a root rule firing two atoms of a composition, chaos stepping to itself, and the
  composition and summation contexts;
- `Context.denote_fill`: what a filled context denotes is an affine image of what its hole denotes,
  `(v ⊕ A) ∪ B` (`Context.affine`);
- `step_family`: every step of every process denotes a member of the family;
- `family_step`: every member of the family is denoted by a step of a presentation congruent to the
  process: the unrefined members and the kept ones, summed with the redex composed with a sum of the
  remainders, which fires once for all of them.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Distributive

open Syntax CanonicalBags PatternLexOrder
open scoped Pointwise

variable {decl : Decl}

/-- What the free algebra holds: chaos, or a set of products. -/
abbrev Denotation := Option (Finset (Multiset Pattern))

variable (decl) in
/-- What a pattern denotes: the free-algebra element of its canonical form. -/
def denote (pattern : Pattern) : Denotation := value decl (normal decl pattern)

variable (decl) in
/-- What a composition of patterns denotes. -/
def totalOf (elements : List Pattern) : Denotation := elements.foldr (fun element rest => plus (denote decl element) rest) (some 0)

variable (decl) in
/-- What a sum of patterns denotes. -/
def unionOf (elements : List Pattern) : Denotation := elements.foldr (fun element rest => cup (denote decl element) rest) (some ∅)

theorem total_map_normal (elements : List Pattern) : total decl (elements.map (normal decl)) = totalOf decl elements := by
  induction elements with
  | nil => rfl
  | cons element elements ih => rw [List.map_cons, total_cons, ih]; rfl

theorem union_map_normal (elements : List Pattern) : union decl (elements.map (normal decl)) = unionOf decl elements := by
  induction elements with
  | nil => rfl
  | cons element elements ih => rw [List.map_cons, union_cons, ih]; rfl

theorem canonical_normals (valid : decl.Valid) {elements : List Pattern} (isFree : ∀ element ∈ elements, restFree element = true) :
    ∀ item ∈ elements.map (normal decl), Canonical decl item := fun item member => by
  obtain ⟨element, elementMember, rfl⟩ := List.mem_map.mp member
  exact normal_canonical valid element (isFree element elementMember)

/-- A composition denotes the sum of what its elements denote. -/
theorem denote_product (valid : decl.Valid) {elements : List Pattern} (isFree : ∀ element ∈ elements, restFree element = true) :
    denote decl (.collection decl.product elements none) = totalOf decl elements := by
  unfold denote
  rw [normal_collection, if_pos rfl, (multiply_total valid (canonical_normals valid isFree)).2, total_map_normal]

/-- A sum denotes the union of what its elements denote. -/
theorem denote_sum (valid : decl.Valid) {elements : List Pattern} (isFree : ∀ element ∈ elements, restFree element = true) :
    denote decl (.collection decl.sum elements none) = unionOf decl elements := by
  unfold denote
  rw [normal_collection, if_neg (fun same => valid.distinct same.symm), if_pos rfl,
    (add_union valid (canonical_normals valid isFree)).2, union_map_normal]

theorem totalOf_cons (element : Pattern) (elements : List Pattern) :
    totalOf decl (element :: elements) = plus (denote decl element) (totalOf decl elements) := rfl

theorem unionOf_cons (element : Pattern) (elements : List Pattern) :
    unionOf decl (element :: elements) = cup (denote decl element) (unionOf decl elements) := rfl

/-- One element of a composition, apart. -/
theorem totalOf_split : ∀ (before : List Pattern) (element : Pattern) (after : List Pattern),
    totalOf decl (before ++ element :: after) = plus (denote decl element) (totalOf decl (before ++ after))
  | [], _, _ => rfl
  | first :: before, element, after => by
    simp only [List.cons_append, totalOf_cons]
    rw [totalOf_split before element after, plus_left_comm]

/-- One summand of a sum, apart. -/
theorem unionOf_split : ∀ (before : List Pattern) (element : Pattern) (after : List Pattern),
    unionOf decl (before ++ element :: after) = cup (denote decl element) (unionOf decl (before ++ after))
  | [], _, _ => rfl
  | first :: before, element, after => by
    simp only [List.cons_append, unionOf_cons]
    rw [unionOf_split before element after, cup_left_comm]

/-! ## Steps -/

variable (decl) in
/-- **One step**: a root rule fires two atoms of a composition into a reduct, chaos steps to itself,
and steps happen inside compositions and inside sums. -/
inductive Reduces (fires : Pattern → Pattern → Pattern → Prop) : Pattern → Pattern → Prop where
  | fire {before middle after : List Pattern} {first second reduct : Pattern} :
      fires first second reduct →
      Reduces fires (.collection decl.product (before ++ first :: middle ++ second :: after) none)
        (.collection decl.product (before ++ reduct :: middle ++ after) none)
  | diverge : Reduces fires (.apply decl.absorbing []) (.apply decl.absorbing [])
  | product {before after : List Pattern} {element changed : Pattern} :
      Reduces fires element changed →
      Reduces fires (.collection decl.product (before ++ element :: after) none)
        (.collection decl.product (before ++ changed :: after) none)
  | sum {before after : List Pattern} {element changed : Pattern} :
      Reduces fires element changed →
      Reduces fires (.collection decl.sum (before ++ element :: after) none)
        (.collection decl.sum (before ++ changed :: after) none)

/-- A position reached through compositions and sums. -/
inductive Context where
  | hole
  | product (before after : List Pattern) (inner : Context)
  | sum (before after : List Pattern) (inner : Context)

variable (decl) in
/-- The pattern with a context's hole filled. -/
def Context.fill : Context → Pattern → Pattern
  | .hole, filler => filler
  | .product before after inner, filler => .collection decl.product (before ++ inner.fill filler :: after) none
  | .sum before after inner, filler => .collection decl.sum (before ++ inner.fill filler :: after) none

variable (decl) in
/-- What a filled context denotes, given what its hole denotes. -/
def Context.apply : Context → Denotation → Denotation
  | .hole, held => held
  | .product before after inner, held => plus (inner.apply held) (totalOf decl (before ++ after))
  | .sum before after inner, held => cup (inner.apply held) (unionOf decl (before ++ after))

variable (decl) in
/-- The siblings of a context's path are processes. -/
def Context.Plain : Context → Prop
  | .hole => True
  | .product before after inner => (∀ element ∈ before ++ after, plain decl element = true) ∧ inner.Plain
  | .sum before after inner => (∀ element ∈ before ++ after, plain decl element = true) ∧ inner.Plain

theorem forall_around_iff {p : Pattern → Prop} {before after : List Pattern} {x : Pattern} :
    (∀ item ∈ before ++ x :: after, p item) ↔ (∀ item ∈ before ++ after, p item) ∧ p x := by
  constructor
  · intro all
    refine ⟨fun item member => all item ?_, all x (by simp)⟩
    rcases List.mem_append.mp member with inBefore | inAfter
    · exact List.mem_append_left _ inBefore
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ inAfter)
  · rintro ⟨around, here⟩
    exact forall_around around here

/-- A filled context is a process exactly when its siblings and its filler are. -/
theorem Context.plain_fill (valid : decl.Valid) :
    ∀ (context : Context) (filler : Pattern),
      plain decl (context.fill decl filler) = true ↔ context.Plain decl ∧ plain decl filler = true
  | .hole, filler => by simp [Context.fill, Context.Plain]
  | .product before after inner, filler => by
    simp only [Context.fill, Context.Plain]
    rw [plain_collection_iff, forall_around_iff, Context.plain_fill valid inner filler]
    constructor
    · rintro ⟨_, around, innerPlain, fillerPlain⟩
      exact ⟨⟨around, innerPlain⟩, fillerPlain⟩
    · rintro ⟨⟨around, innerPlain⟩, fillerPlain⟩
      exact ⟨fun same => absurd same valid.distinct, around, innerPlain, fillerPlain⟩
  | .sum before after inner, filler => by
    simp only [Context.fill, Context.Plain]
    rw [plain_collection_iff, forall_around_iff, Context.plain_fill valid inner filler]
    constructor
    · rintro ⟨_, around, innerPlain, fillerPlain⟩
      exact ⟨⟨around, innerPlain⟩, fillerPlain⟩
    · rintro ⟨⟨around, innerPlain⟩, fillerPlain⟩
      exact ⟨fun _ => by simp, around, innerPlain, fillerPlain⟩

/-- **What a filled context denotes is the context applied to what its filler denotes.** -/
theorem Context.denote_fill (valid : decl.Valid) :
    ∀ (context : Context) {filler : Pattern}, plain decl (context.fill decl filler) = true →
      denote decl (context.fill decl filler) = context.apply decl (denote decl filler)
  | .hole, _, _ => rfl
  | .product before after inner, filler, isPlain => by
    have parts := (Context.plain_fill valid _ filler).mp isPlain
    have elements := (plain_collection isPlain).2.2
    simp only [Context.fill, Context.apply] at isPlain elements ⊢
    rw [denote_product valid fun element member => restFree_of_plain (elements element member), totalOf_split,
      Context.denote_fill valid inner ((Context.plain_fill valid inner filler).mpr ⟨parts.1.2, parts.2⟩)]
  | .sum before after inner, filler, isPlain => by
    have parts := (Context.plain_fill valid _ filler).mp isPlain
    have elements := (plain_collection isPlain).2.2
    simp only [Context.fill, Context.apply] at isPlain elements ⊢
    rw [denote_sum valid fun element member => restFree_of_plain (elements element member), unionOf_split,
      Context.denote_fill valid inner ((Context.plain_fill valid inner filler).mpr ⟨parts.1.2, parts.2⟩)]

theorem plus_ne_none {a b : Denotation} (product : plus a b ≠ none) : a ≠ none ∧ b ≠ none := by
  cases a <;> cases b <;> simp_all [plus]

theorem cup_ne_none {a b : Denotation} (joined : cup a b ≠ none) : a ≠ none ∧ b ≠ none := by
  cases a <;> cases b <;> simp_all [cup]

theorem denote_ne_empty (valid : decl.Valid) {pattern : Pattern} (isPlain : plain decl pattern = true) :
    denote decl pattern ≠ some ∅ :=
  value_normal_ne_zero valid pattern isPlain

theorem totalOf_ne_empty (valid : decl.Valid) {elements : List Pattern} (each : ∀ element ∈ elements, plain decl element = true) :
    totalOf decl elements ≠ some ∅ := by
  rw [← total_map_normal]
  exact total_ne_zero _ fun item member => by
    obtain ⟨element, elementMember, rfl⟩ := List.mem_map.mp member
    exact denote_ne_empty valid (each element elementMember)

variable (decl) in
/-- What a context composes its hole with: its compositions' siblings. -/
def Context.factor : Context → Denotation
  | .hole => some 0
  | .product before after inner => plus inner.factor (totalOf decl (before ++ after))
  | .sum _ _ inner => inner.factor

variable (decl) in
/-- What a context joins to its hole: its sums' siblings, composed with the compositions above them. -/
def Context.joined : Context → Denotation
  | .hole => some ∅
  | .product before after inner => plus inner.joined (totalOf decl (before ++ after))
  | .sum before after inner => cup inner.joined (unionOf decl (before ++ after))

/-- **A context acts affinely**: it composes what its hole holds with its factor and joins its joined
part. -/
theorem Context.apply_eq : ∀ (context : Context) (held : Denotation),
    context.apply decl held = cup (plus held (context.factor decl)) (context.joined decl)
  | .hole, held => by simp only [Context.apply, Context.factor, Context.joined, plus_zero, cup_empty]
  | .product before after inner, held => by
    simp only [Context.apply, Context.factor, Context.joined, Context.apply_eq inner held, plus_cup_right, plus_assoc]
  | .sum before after inner, held => by
    simp only [Context.apply, Context.factor, Context.joined, Context.apply_eq inner held, cup_assoc]

theorem plus_eq_empty {a b : Denotation} (empty : plus a b = some ∅) : a = some ∅ ∨ b = some ∅ := by
  cases a <;> cases b <;> simp_all [plus, Finset.add_eq_empty]

/-- The factor of a context whose siblings are processes holds a product. -/
theorem Context.factor_ne_empty (valid : decl.Valid) :
    ∀ (context : Context), context.Plain decl → context.factor decl ≠ some ∅
  | .hole, _ => by simp [Context.factor, ← Finset.singleton_zero]
  | .product before after inner, plainContext => by
    intro empty
    rcases plus_eq_empty empty with innerEmpty | siblingsEmpty
    · exact Context.factor_ne_empty valid inner plainContext.2 innerEmpty
    · exact totalOf_ne_empty valid plainContext.1 siblingsEmpty
  | .sum _ _ inner, plainContext => Context.factor_ne_empty valid inner plainContext.2

theorem Context.apply_none : ∀ (context : Context), context.apply decl none = none
  | .hole => rfl
  | .product _ _ inner => by simp [Context.apply, Context.apply_none inner, plus]
  | .sum _ _ inner => by simp [Context.apply, Context.apply_none inner, cup]

/-- Every step is a root step in a context. -/
theorem Reduces.context {fires : Pattern → Pattern → Pattern → Prop} {source target : Pattern}
    (step : Reduces decl fires source target) :
    ∃ (context : Context) (node node' : Pattern), source = context.fill decl node ∧ target = context.fill decl node' ∧
      ((∃ (before middle after : List Pattern) (first second reduct : Pattern), fires first second reduct ∧
          node = .collection decl.product (before ++ first :: middle ++ second :: after) none ∧
          node' = .collection decl.product (before ++ reduct :: middle ++ after) none) ∨
        (node = .apply decl.absorbing [] ∧ node' = .apply decl.absorbing [])) := by
  induction step with
  | fire fired => exact ⟨.hole, _, _, rfl, rfl, .inl ⟨_, _, _, _, _, _, fired, rfl, rfl⟩⟩
  | diverge => exact ⟨.hole, _, _, rfl, rfl, .inr ⟨rfl, rfl⟩⟩
  | @product before after _ _ _ ih =>
    obtain ⟨context, node, node', rfl, rfl, root⟩ := ih
    exact ⟨.product before after context, node, node', rfl, rfl, root⟩
  | @sum before after _ _ _ ih =>
    obtain ⟨context, node, node', rfl, rfl, root⟩ := ih
    exact ⟨.sum before after context, node, node', rfl, rfl, root⟩

/-! ## The family -/

/-- The products a redex with atoms `first` and `second` composes with a set of remainders. -/
def holding (first second : Pattern) (remainders : Finset (Multiset Pattern)) : Finset (Multiset Pattern) :=
  remainders.image fun remainder => first ::ₘ second ::ₘ remainder

/-- **The one-step family**: from `S`, fire a redex with atoms `first`, `second` and a reduct
denoting `reduct` in the products `first + second + d`, `d ∈ D`, which lie in `S`, and remove any set
`R` of them. From chaos, chaos. -/
def InFamily (source : Denotation) (first second : Pattern) (reduct target : Denotation) : Prop :=
  match source with
  | none => target = none
  | some products => ∃ remainders removed : Finset (Multiset Pattern), remainders.Nonempty ∧
      holding first second remainders ⊆ products ∧ removed ⊆ holding first second remainders ∧
      target = cup (some (products \ removed)) (plus reduct (some remainders))

theorem value_atom {atom : Pattern} (isAtom : IsAtom decl atom) : value decl atom = some {atom ::ₘ 0} := by
  simp [value, products_atom isAtom, presented]

theorem denote_atom {pattern : Pattern} (isAtom : IsAtom decl (normal decl pattern)) :
    denote decl pattern = some {normal decl pattern ::ₘ 0} :=
  value_atom isAtom

theorem denote_absorbing : denote decl (.apply decl.absorbing []) = none := by
  simp [denote, normal_apply, value_absorbing]

/-- A redex's atoms, composed. -/
theorem plus_atoms (first second : Pattern) (rest : Denotation) :
    plus (some {first ::ₘ 0}) (plus (some {second ::ₘ 0}) rest) = plus (some {first ::ₘ second ::ₘ 0}) rest := by
  cases rest with
  | none => rfl
  | some set =>
    simp [plus, ← add_assoc, Finset.singleton_add_singleton]

/-- The products holding a redex are the redex composed with the remainders. -/
theorem holding_eq (first second : Pattern) (remainders : Finset (Multiset Pattern)) :
    holding first second remainders = {first ::ₘ second ::ₘ 0} + remainders := by
  ext product
  simp [holding, Finset.mem_add, Multiset.cons_add]

/-- **Every step lands in the family**: a step of a process denotes a member of the one-step family of
what the process denotes, for the redex the step fires; chaos steps to chaos. -/
theorem step_family (valid : decl.Valid) {fires : Pattern → Pattern → Pattern → Prop}
    (atoms : ∀ {first second reduct : Pattern}, fires first second reduct →
      IsAtom decl (normal decl first) ∧ IsAtom decl (normal decl second))
    (reductPlain : ∀ {first second reduct : Pattern}, fires first second reduct → plain decl reduct = true)
    {source target : Pattern} (isPlain : plain decl source = true) (step : Reduces decl fires source target) :
    (denote decl source = none ∧ denote decl target = none) ∨
      ∃ first second reduct, fires first second reduct ∧
        InFamily (denote decl source) (normal decl first) (normal decl second) (denote decl reduct)
          (denote decl target) := by
  obtain ⟨context, node, node', rfl, rfl, root⟩ := step.context
  obtain ⟨plainContext, nodePlain⟩ := (Context.plain_fill valid context node).mp isPlain
  rw [Context.denote_fill valid context isPlain]
  rcases root with ⟨before, middle, after, first, second, reduct, fired, rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have elements := (plain_collection nodePlain).2.2
    have firstPlain := elements first (by simp)
    have secondPlain := elements second (by simp)
    have othersPlain : ∀ element ∈ before ++ (middle ++ after), plain decl element = true := fun element member => by
      apply elements element
      rcases List.mem_append.mp member with inBefore | inRest
      · exact List.mem_append_left _ (List.mem_append_left _ inBefore)
      · rcases List.mem_append.mp inRest with inMiddle | inAfter
        · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _ inMiddle))
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ inAfter)
    have targetNodePlain : plain decl (.collection decl.product (before ++ reduct :: middle ++ after) none) = true := by
      apply plain_product valid
      intro element member
      rw [List.append_assoc, List.cons_append] at member
      rcases List.mem_append.mp member with inBefore | inRest
      · exact othersPlain element (List.mem_append_left _ inBefore)
      · rcases List.mem_cons.mp inRest with rfl | inRest
        · exact reductPlain fired
        · exact othersPlain element (List.mem_append_right _ inRest)
    have targetPlain := (Context.plain_fill valid context _).mpr ⟨plainContext, targetNodePlain⟩
    rw [Context.denote_fill valid context targetPlain]
    have sourceNode : denote decl (.collection decl.product (before ++ first :: middle ++ second :: after) none) =
        plus (some {normal decl first ::ₘ normal decl second ::ₘ 0}) (totalOf decl (before ++ (middle ++ after))) := by
      rw [denote_product valid fun element member => restFree_of_plain (elements element member), totalOf_split,
        List.append_assoc, List.cons_append, totalOf_split, denote_atom (atoms fired).1, denote_atom (atoms fired).2,
        plus_left_comm, plus_atoms]
    have targetNode : denote decl (.collection decl.product (before ++ reduct :: middle ++ after) none) =
        plus (denote decl reduct) (totalOf decl (before ++ (middle ++ after))) := by
      rw [denote_product valid fun element member => restFree_of_plain ((plain_collection targetNodePlain).2.2 element member),
        List.append_assoc, List.cons_append, totalOf_split]
    rw [sourceNode, targetNode, Context.apply_eq, Context.apply_eq]
    right
    refine ⟨first, second, reduct, fired, ?_⟩
    have othersNonempty := totalOf_ne_empty valid othersPlain
    have factorNonempty := Context.factor_ne_empty valid context plainContext
    generalize totalOf decl (before ++ (middle ++ after)) = others at othersNonempty ⊢
    generalize context.factor decl = factor at factorNonempty ⊢
    generalize context.joined decl = joined
    cases others with
    | none => simp [InFamily, plus, cup]
    | some othersSet =>
      cases factor with
      | none => simp [InFamily, plus, cup]
      | some factorSet =>
        cases joined with
        | none => simp [InFamily, cup]
        | some joinedSet =>
          have remaindersNonempty : (othersSet + factorSet).Nonempty := by
            refine Finset.Nonempty.add ?_ ?_
            · exact Finset.nonempty_iff_ne_empty.mpr fun empty => othersNonempty (by rw [empty])
            · exact Finset.nonempty_iff_ne_empty.mpr fun empty => factorNonempty (by rw [empty])
          simp only [InFamily, plus, cup]
          refine ⟨othersSet + factorSet, holding (normal decl first) (normal decl second) (othersSet + factorSet) \ joinedSet,
            remaindersNonempty, ?_, Finset.sdiff_subset, ?_⟩
          · rw [holding_eq, add_assoc]
            exact Finset.subset_union_left
          · rw [holding_eq, ← add_assoc]
            cases reductDenoted : denote decl reduct with
            | none => simp
            | some reductSet =>
              simp only [Option.some.injEq]
              rw [add_assoc]
              ext product
              simp only [Finset.mem_union, Finset.mem_sdiff]
              tauto
  · left
    rw [Context.denote_fill valid context isPlain, denote_absorbing, Context.apply_none]
    exact ⟨rfl, rfl⟩

/-! ## Every member of the family is a step -/

/-- An atom of a canonical form of a process: an atom, its own canonical form, a process. -/
def GoodAtom (atom : Pattern) : Prop := IsAtom decl atom ∧ normal decl atom = atom ∧ plain decl atom = true

/-- **The atoms of what a process denotes are good.** -/
theorem good_of_denote (valid : decl.Valid) {pattern : Pattern} (isPlain : plain decl pattern = true)
    {products' : Finset (Multiset Pattern)} (found : denote decl pattern = some products') :
    ∀ product ∈ products', ∀ atom ∈ product, GoodAtom (decl := decl) atom := by
  intro product member atom inProduct
  unfold denote value at found
  cases productsFound : products decl (normal decl pattern) with
  | none => rw [productsFound] at found; cases found
  | some ps =>
    rw [productsFound] at found
    cases found
    obtain ⟨chosen, chosenMember, rfl⟩ := mem_presented.mp member
    have inChosen : atom ∈ chosen := Multiset.mem_coe.mp inProduct
    have canonical := normal_canonical valid pattern (restFree_of_plain isPlain)
    rcases canonical with absorbing | ⟨ps', found', atomic, _⟩
    · rw [absorbing, products_none.mpr rfl] at productsFound; cases productsFound
    · rw [productsFound] at found'
      cases found'
      exact ⟨atomic chosen chosenMember atom inChosen,
        (normal_stable valid pattern (restFree_of_plain isPlain)).2 ps productsFound chosen chosenMember atom inChosen,
        products_plain productsFound (plain_normal valid pattern isPlain) chosen chosenMember atom inChosen⟩

variable (decl) in
/-- A set of products, presented as a canonical sum. -/
noncomputable def present (products' : Finset (Multiset Pattern)) : Pattern :=
  sumOf decl (products'.toList.map Multiset.toList)

theorem presented_present (products' : Finset (Multiset Pattern)) :
    presented (products'.toList.map Multiset.toList) = products' := by
  ext product
  simp [presented]

theorem atoms_present {products' : Finset (Multiset Pattern)}
    (good : ∀ product ∈ products', ∀ atom ∈ product, GoodAtom (decl := decl) atom) :
    ∀ chosen ∈ products'.toList.map Multiset.toList, ∀ atom ∈ chosen, GoodAtom (decl := decl) atom := by
  intro chosen member atom inChosen
  obtain ⟨product, productMember, rfl⟩ := List.mem_map.mp member
  exact good product (Finset.mem_toList.mp productMember) atom (Multiset.mem_toList.mp inChosen)

/-- **A presented set denotes itself.** -/
theorem denote_present (valid : decl.Valid) {products' : Finset (Multiset Pattern)}
    (good : ∀ product ∈ products', ∀ atom ∈ product, GoodAtom (decl := decl) atom) :
    denote decl (present decl products') = some products' := by
  have goodAtoms := atoms_present good
  have atomic : Atoms decl (products'.toList.map Multiset.toList) := fun chosen member atom inChosen =>
    (goodAtoms chosen member atom inChosen).1
  unfold denote present
  rw [normal_sumOf valid atomic fun chosen member atom inChosen => (goodAtoms chosen member atom inChosen).2.1]
  obtain ⟨ps, found, presentedSame, _⟩ := products_sumOf valid atomic
  simp [value, found, presentedSame, presented_present]

theorem plain_present (valid : decl.Valid) {products' : Finset (Multiset Pattern)} (nonempty : products'.Nonempty)
    (good : ∀ product ∈ products', ∀ atom ∈ product, GoodAtom (decl := decl) atom) :
    plain decl (present decl products') = true := by
  apply plain_sumOf valid
  · intro empty
    obtain ⟨product, member⟩ := nonempty
    have : product ∈ products'.toList := Finset.mem_toList.mpr member
    have inMapped : product.toList ∈ products'.toList.map Multiset.toList := List.mem_map.mpr ⟨product, this, rfl⟩
    rw [empty] at inMapped
    simp at inMapped
  · exact fun chosen member atom inChosen => (atoms_present good chosen member atom inChosen).2.2

/-- Processes that denote the same are congruent. -/
theorem congruent_of_denote (valid : decl.Valid) {left right : Pattern} (leftPlain : plain decl left = true)
    (rightPlain : plain decl right = true) (same : denote decl left = denote decl right) : Congruent decl left right :=
  (congruent_iff valid leftPlain rightPlain).mpr
    (Canonical.eq (normal_canonical valid left (restFree_of_plain leftPlain))
      (normal_canonical valid right (restFree_of_plain rightPlain)) same)

/-- **Every member of the family is a step**: some presentation congruent to the process steps, by the
redex, to a process denoting the member. -/
theorem family_step (valid : decl.Valid) {fires : Pattern → Pattern → Pattern → Prop}
    (atoms : ∀ {first second reduct : Pattern}, fires first second reduct →
      IsAtom decl (normal decl first) ∧ IsAtom decl (normal decl second))
    (redexPlain : ∀ {first second reduct : Pattern}, fires first second reduct →
      plain decl first = true ∧ plain decl second = true ∧ plain decl reduct = true)
    {source : Pattern} (isPlain : plain decl source = true) {first second reduct : Pattern}
    (fired : fires first second reduct) {target : Denotation}
    (member : InFamily (denote decl source) (normal decl first) (normal decl second) (denote decl reduct) target) :
    ∃ presentation stepped, plain decl presentation = true ∧ Congruent decl source presentation ∧
      Reduces decl fires presentation stepped ∧ denote decl stepped = target := by
  obtain ⟨firstPlain, secondPlain, reductPlain⟩ := redexPlain fired
  have chaosPlain : plain decl (.apply decl.absorbing []) = true := plain_constant _
  cases denoted : denote decl source with
  | none =>
    rw [denoted] at member
    simp only [InFamily] at member
    subst member
    refine ⟨.apply decl.absorbing [], .apply decl.absorbing [], chaosPlain,
      congruent_of_denote valid isPlain chaosPlain (by rw [denoted, denote_absorbing]), .diverge, denote_absorbing⟩
  | some products' =>
    rw [denoted] at member
    obtain ⟨remainders, removed, nonempty, holds, removedHeld, rfl⟩ := member
    have good := good_of_denote valid isPlain denoted
    have remaindersGood : ∀ remainder ∈ remainders, ∀ atom ∈ remainder, GoodAtom (decl := decl) atom := by
      intro remainder inRemainders atom inRemainder
      have held : normal decl first ::ₘ normal decl second ::ₘ remainder ∈ products' :=
        holds (Finset.mem_image.mpr ⟨remainder, inRemainders, rfl⟩)
      exact good _ held atom (by simp [inRemainder])
    have remaindersPlain := plain_present valid nonempty remaindersGood
    have remaindersDenote := denote_present valid remaindersGood
    let core : Pattern := .collection decl.product [first, second, present decl remainders] none
    let fired' : Pattern := .collection decl.product [reduct, present decl remainders] none
    have coreStep : Reduces decl fires core fired' :=
      Reduces.fire (before := []) (middle := []) (after := [present decl remainders]) fired
    have corePlain : plain decl core = true := plain_product valid (by simp [firstPlain, secondPlain, remaindersPlain])
    have firedPlain : plain decl fired' = true := plain_product valid (by simp [reductPlain, remaindersPlain])
    have coreDenote : denote decl core = some (holding (normal decl first) (normal decl second) remainders) := by
      simp only [core]
      rw [denote_product valid (by simp [restFree_of_plain firstPlain, restFree_of_plain secondPlain,
          restFree_of_plain remaindersPlain]),
        totalOf_cons, totalOf_cons, totalOf_cons, denote_atom (atoms fired).1, denote_atom (atoms fired).2,
        remaindersDenote, plus_atoms, holding_eq]
      simp [totalOf, plus]
    have firedDenote : denote decl fired' = plus (denote decl reduct) (some remainders) := by
      simp only [fired']
      rw [denote_product valid (by simp [restFree_of_plain reductPlain, restFree_of_plain remaindersPlain]),
        totalOf_cons, totalOf_cons, remaindersDenote]
      simp [totalOf, plus_zero]
    set held := holding (normal decl first) (normal decl second) remainders
    by_cases restEmpty : (products' \ held) ∪ (held \ removed) = ∅
    · have allHeld : products' = held := by
        apply Finset.Subset.antisymm _ holds
        intro product inProducts
        by_contra notHeld
        have : product ∈ (products' \ held) ∪ (held \ removed) := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨inProducts, notHeld⟩)
        rw [restEmpty] at this
        simp at this
      have allRemoved : products' \ removed = ∅ := by
        ext product
        simp only [Finset.mem_sdiff, Finset.notMem_empty, iff_false, not_and, not_not]
        intro inProducts
        by_contra notRemoved
        have : product ∈ (products' \ held) ∪ (held \ removed) :=
          Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨allHeld ▸ inProducts, notRemoved⟩)
        rw [restEmpty] at this
        simp at this
      refine ⟨core, fired', corePlain, congruent_of_denote valid isPlain corePlain (by rw [denoted, coreDenote, allHeld]),
        coreStep, ?_⟩
      rw [firedDenote, allRemoved]
      cases plus (denote decl reduct) (some remainders) <;> simp [cup]
    · have restNonempty : ((products' \ held) ∪ (held \ removed)).Nonempty := Finset.nonempty_iff_ne_empty.mpr restEmpty
      have restGood : ∀ product ∈ (products' \ held) ∪ (held \ removed), ∀ atom ∈ product, GoodAtom (decl := decl) atom := by
        intro product inRest atom inProduct
        rcases Finset.mem_union.mp inRest with inFirst | inSecond
        · exact good product (Finset.mem_sdiff.mp inFirst).1 atom inProduct
        · exact good product (holds (Finset.mem_sdiff.mp inSecond).1) atom inProduct
      have restPlain := plain_present valid restNonempty restGood
      have restDenote := denote_present valid restGood
      have restEq : (products' \ held) ∪ (held \ removed) = products' \ removed := by
        ext product
        simp only [Finset.mem_union, Finset.mem_sdiff]
        constructor
        · rintro (⟨inProducts, notHeld⟩ | ⟨inHeld, notRemoved⟩)
          · exact ⟨inProducts, fun inRemoved => notHeld (removedHeld inRemoved)⟩
          · exact ⟨holds inHeld, notRemoved⟩
        · rintro ⟨inProducts, notRemoved⟩
          by_cases inHeld : product ∈ held
          · exact .inr ⟨inHeld, notRemoved⟩
          · exact .inl ⟨inProducts, inHeld⟩
      let presentation : Pattern := .collection decl.sum [present decl ((products' \ held) ∪ (held \ removed)), core] none
      let stepped : Pattern := .collection decl.sum [present decl ((products' \ held) ∪ (held \ removed)), fired'] none
      have presentationPlain : plain decl presentation = true := plain_sum (by simp) (by simp [restPlain, corePlain])
      have presentationDenote : denote decl presentation = some products' := by
        simp only [presentation]
        rw [denote_sum valid (by simp [restFree_of_plain restPlain, restFree_of_plain corePlain]), unionOf_cons,
          unionOf_cons, restDenote, coreDenote]
        simp only [unionOf, List.foldr_nil, cup, Option.some.injEq]
        ext product
        simp only [Finset.union_empty, Finset.mem_union, Finset.mem_sdiff]
        constructor
        · rintro ((⟨inProducts, _⟩ | ⟨inHeld, _⟩) | inHeld)
          · exact inProducts
          · exact holds inHeld
          · exact holds inHeld
        · intro inProducts
          by_cases inHeld : product ∈ held
          · exact .inr inHeld
          · exact .inl (.inl ⟨inProducts, inHeld⟩)
      refine ⟨presentation, stepped, presentationPlain,
        congruent_of_denote valid isPlain presentationPlain (by rw [denoted, presentationDenote]),
        Reduces.sum (before := [present decl ((products' \ held) ∪ (held \ removed))]) (after := []) coreStep, ?_⟩
      simp only [stepped]
      rw [denote_sum valid (by simp [restFree_of_plain restPlain, restFree_of_plain firedPlain]), unionOf_cons,
        unionOf_cons, restDenote, firedDenote, restEq]
      cases plus (denote decl reduct) (some remainders) <;> simp [unionOf, cup]

end Mettapedia.OSLF.MeTTaIL.Distributive

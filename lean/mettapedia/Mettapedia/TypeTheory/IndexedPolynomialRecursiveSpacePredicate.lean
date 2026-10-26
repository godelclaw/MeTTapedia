import Mettapedia.TypeTheory.IndexedPolynomialRecursiveSpaceRepresentation

/-!
# Constructor predicates for indexed families in recursive spaces

The guarded image of an indexed polynomial is a fixed point of its constructor
operator in the recursive-space representation. The operator retains the result
index and shape, tests every recursive position, and fills unused natural slots
with bottom. Its leastness follows from the original indexed family induction.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.IndexedPolynomial.RecursiveSpaceRepresentation

universe b i s p
variable {Base : Type b} {Index : Base → Type i}
variable (presentation : Presentation.{b, i, s, p} (Base := Base) (Index := Index))

theorem toRecursiveSpace_padded_node {environment : Base} {index : Index environment}
    (shape : presentation.polynomial.Shape environment index)
    (children : presentation.polynomial.Position shape →
      GuardedRaw.Tree presentation.polynomial (positions presentation) environment) :
    toRecursiveSpace presentation
      (Fix.roll (some ⟨index, shape⟩)
        ((presentation.coding shape).extend
          (GuardedRaw.absent _ _ environment) children)) =
      RecursiveSpace.construct (presentation.tag shape) (some ⟨index, shape⟩)
        ((presentation.coding shape).extend RecursiveSpace.bottom
          (fun position => toRecursiveSpace presentation (children position))) := by
  rw [toRecursiveSpace_node]
  apply congrArg (RecursiveSpace.construct (A := RecursivePayload presentation environment)
    (presentation.tag shape) (some ⟨index, shape⟩))
  funext slot
  cases decoded : (presentation.coding shape).decode slot with
  | none => simp only [SlotEncoding.extend, decoded, toRecursiveSpace_absent]
  | some position => simp only [SlotEncoding.extend, decoded]

def constructorStep
    (property : ∀ environment, Index environment →
      RecursiveSpace.Tree (RecursivePayload presentation environment) → Prop)
    (environment : Base) (index : Index environment)
    (tree : RecursiveSpace.Tree (RecursivePayload presentation environment)) : Prop :=
  ∃ (shape : presentation.polynomial.Shape environment index)
    (children : presentation.polynomial.Position shape →
      RecursiveSpace.Tree (RecursivePayload presentation environment)),
    tree = RecursiveSpace.construct (presentation.tag shape) (some ⟨index, shape⟩)
      ((presentation.coding shape).extend RecursiveSpace.bottom children) ∧
    ∀ position, property environment (presentation.polynomial.next shape position)
      (children position)

theorem constructorStep_mono
    (first second : ∀ environment, Index environment →
      RecursiveSpace.Tree (RecursivePayload presentation environment) → Prop)
    (included : ∀ environment index tree, first environment index tree →
      second environment index tree) (environment : Base) (index : Index environment)
    (tree : RecursiveSpace.Tree (RecursivePayload presentation environment)) :
    constructorStep presentation first environment index tree →
      constructorStep presentation second environment index tree := by
  rintro ⟨shape, children, same, valid⟩
  exact ⟨shape, children, same, fun position => included _ _ _ (valid position)⟩

theorem recursiveValid_iff_constructorStep (environment : Base) (index : Index environment)
    (tree : RecursiveSpace.Tree (RecursivePayload presentation environment)) :
    RecursiveValid presentation tree index ↔
      constructorStep presentation
        (fun _ index tree => RecursiveValid presentation tree index) environment index tree := by
  constructor
  · rintro ⟨encoded, valid⟩
    obtain ⟨shape, children, same, childrenValid⟩ :=
      (GuardedRaw.valid_iff_step presentation.polynomial (positions presentation)
        environment index (fromRecursiveSpace presentation tree encoded)).mp valid
    refine ⟨shape, (fun position => toRecursiveSpace presentation (children position)), ?_, ?_⟩
    · calc
        tree = toRecursiveSpace presentation (fromRecursiveSpace presentation tree encoded) :=
          (toRecursiveSpace_fromRecursiveSpace presentation tree encoded).symm
        _ = _ := congrArg (toRecursiveSpace presentation) same
        _ = _ := toRecursiveSpace_padded_node presentation shape children
    · intro position
      exact (recursiveValid_toRecursiveSpace_iff presentation _ _).mpr (childrenValid position)
  · rintro ⟨shape, children, rfl, childrenValid⟩
    let rawChildren := fun position =>
      fromRecursiveSpace presentation (children position) (childrenValid position).choose
    have restored : (fun position => toRecursiveSpace presentation (rawChildren position)) =
        children := by
      funext position
      exact toRecursiveSpace_fromRecursiveSpace presentation _ _
    have rawValid : GuardedRaw.Valid presentation.polynomial (positions presentation)
        (Fix.roll (some ⟨index, shape⟩)
          ((presentation.coding shape).extend
            (GuardedRaw.absent _ _ environment) rawChildren)) index :=
      (GuardedRaw.valid_iff_step presentation.polynomial (positions presentation)
        environment index _).mpr
          ⟨shape, rawChildren, rfl, fun position => (childrenValid position).choose_spec⟩
    have result := (recursiveValid_toRecursiveSpace_iff presentation _ _).mpr rawValid
    rw [toRecursiveSpace_padded_node, restored] at result
    exact result

def ConstructorClosed
    (property : ∀ environment, Index environment →
      RecursiveSpace.Tree (RecursivePayload presentation environment) → Prop) : Prop :=
  ∀ environment index tree, constructorStep presentation property environment index tree →
    property environment index tree

theorem recursiveValid_bottom_refused (environment : Base) (index : Index environment) :
    ¬ RecursiveValid presentation (environment := environment) RecursiveSpace.bottom index := by
  intro valid
  obtain ⟨shape, children, same, _⟩ :=
    (recursiveValid_iff_constructorStep presentation environment index _).mp valid
  exact RecursiveSpace.construct_ne_bottom _ _ _ same.symm

theorem recursiveValid_construct_iff {environment : Base} (index : Index environment)
    (tag : Nat) (point : Σ index, presentation.polynomial.Shape environment index)
    (children : Nat → RecursiveSpace.Tree (RecursivePayload presentation environment)) :
    RecursiveValid presentation (RecursiveSpace.construct tag (some point) children) index ↔
      index = point.1 ∧ tag = presentation.tag point.2 ∧
      (presentation.coding point.2).Canonical RecursiveSpace.bottom children ∧
      ∀ position, RecursiveValid presentation
        (children ((presentation.coding point.2).encode position))
        (presentation.polynomial.next point.2 position) := by
  rw [recursiveValid_iff_constructorStep]
  constructor
  · rintro ⟨shape, recursive, same, valid⟩
    obtain ⟨tags, payloads, branches⟩ :=
      (RecursiveSpace.construct_injective _ _ _ _ _ _).mp same
    have points := Option.some.inj payloads
    cases points
    refine ⟨rfl, tags, ?_, ?_⟩
    · rw [branches]
      exact (presentation.coding shape).extend_canonical _ _
    · intro position
      rw [branches, SlotEncoding.extend_at]
      exact valid position
  · rintro ⟨sameIndex, tags, canonical, valid⟩
    subst index
    refine ⟨point.2, (presentation.coding point.2).restrict children, ?_, valid⟩
    rw [SlotEncoding.extend_restrict _ _ _ canonical, tags]

theorem recursiveValid_index_unique {environment : Base}
    (tree : RecursiveSpace.Tree (RecursivePayload presentation environment))
    (first second : Index environment)
    (firstValid : RecursiveValid presentation tree first)
    (secondValid : RecursiveValid presentation tree second) : first = second := by
  obtain ⟨shape, children, same, _⟩ :=
    (recursiveValid_iff_constructorStep presentation environment first tree).mp firstValid
  rw [same] at secondValid
  exact ((recursiveValid_construct_iff presentation second _ _ _).mp secondValid).1.symm

def HasRootIndex {environment : Base}
    (tree : RecursiveSpace.Tree (RecursivePayload presentation environment))
    (index : Index environment) : Prop :=
  ∃ (tag : Nat) (shape : presentation.polynomial.Shape environment index)
    (children : Nat → RecursiveSpace.Tree (RecursivePayload presentation environment)),
    tree = RecursiveSpace.construct tag (some ⟨index, shape⟩) children

theorem hasRootIndex_construct_iff {environment : Base}
    (tag : Nat) (point : Σ index, presentation.polynomial.Shape environment index)
    (children : Nat → RecursiveSpace.Tree (RecursivePayload presentation environment))
    (index : Index environment) :
    HasRootIndex presentation (RecursiveSpace.construct tag (some point) children) index ↔
      index = point.1 := by
  constructor
  · rintro ⟨otherTag, shape, otherChildren, same⟩
    have samePoint := Option.some.inj
      ((RecursiveSpace.construct_injective _ _ _ _ _ _).mp same).2.1
    exact (congrArg Sigma.fst samePoint).symm
  · intro same
    subst index
    exact ⟨tag, point.2, children, rfl⟩

theorem recursiveValid_hasRootIndex {environment : Base}
    (tree : RecursiveSpace.Tree (RecursivePayload presentation environment))
    (index : Index environment) (valid : RecursiveValid presentation tree index) :
    HasRootIndex presentation tree index := by
  obtain ⟨shape, children, same, _⟩ :=
    (recursiveValid_iff_constructorStep presentation environment index tree).mp valid
  exact ⟨presentation.tag shape, shape, _, same⟩

def FamilyValid {environment : Base}
    (tree : RecursiveSpace.Tree (RecursivePayload presentation environment)) : Prop :=
  ∃ index, RecursiveValid presentation tree index

theorem recursiveValid_iff_family_and_root {environment : Base}
    (tree : RecursiveSpace.Tree (RecursivePayload presentation environment))
    (index : Index environment) :
    RecursiveValid presentation tree index ↔
      FamilyValid presentation tree ∧ HasRootIndex presentation tree index := by
  constructor
  · intro valid
    exact ⟨⟨index, valid⟩, recursiveValid_hasRootIndex presentation tree index valid⟩
  · rintro ⟨⟨other, valid⟩, root⟩
    obtain ⟨shape, children, same, _⟩ :=
      (recursiveValid_iff_constructorStep presentation environment other tree).mp valid
    rw [same, hasRootIndex_construct_iff] at root
    exact root.symm ▸ valid

def predicateStep
    (property : ∀ environment,
      RecursiveSpace.Tree (RecursivePayload presentation environment) → Prop)
    (environment : Base)
    (tree : RecursiveSpace.Tree (RecursivePayload presentation environment)) : Prop :=
  ∃ (point : Σ index, presentation.polynomial.Shape environment index)
    (children : Nat → RecursiveSpace.Tree (RecursivePayload presentation environment)),
    tree = RecursiveSpace.construct (presentation.tag point.2) (some point) children ∧
    (∀ slot position, (presentation.coding point.2).decode slot = some position →
      HasRootIndex presentation (children slot) (presentation.polynomial.next point.2 position) ∧
      property environment (children slot)) ∧
    (presentation.coding point.2).Canonical RecursiveSpace.bottom children

theorem familyValid_iff_predicateStep (environment : Base)
    (tree : RecursiveSpace.Tree (RecursivePayload presentation environment)) :
    FamilyValid presentation tree ↔
      predicateStep presentation (fun _ tree => FamilyValid presentation tree) environment tree := by
  constructor
  · rintro ⟨index, valid⟩
    obtain ⟨shape, recursive, same, childrenValid⟩ :=
      (recursiveValid_iff_constructorStep presentation environment index tree).mp valid
    refine ⟨⟨index, shape⟩, (presentation.coding shape).extend RecursiveSpace.bottom recursive,
      same, ?_, (presentation.coding shape).extend_canonical _ _⟩
    intro slot position decoded
    simp only [SlotEncoding.extend, decoded]
    exact ⟨recursiveValid_hasRootIndex presentation _ _ (childrenValid position),
      ⟨_, childrenValid position⟩⟩
  · rintro ⟨point, children, rfl, active, canonical⟩
    refine ⟨point.1, (recursiveValid_construct_iff presentation _ _ _ _).mpr
      ⟨rfl, rfl, canonical, ?_⟩⟩
    intro position
    have valid := active _ position ((presentation.coding point.2).decode_encode position)
    exact (recursiveValid_iff_family_and_root presentation _ _).mpr ⟨valid.2, valid.1⟩

def shapeGuard {environment : Base} (tag : Nat)
    (payload : RecursivePayload presentation environment) : Prop :=
  match payload with
  | none => False
  | some point => tag = presentation.tag point.2

def activeGuard {environment : Base} (payload : RecursivePayload presentation environment)
    (slot : Nat) : Prop :=
  match payload with
  | none => False
  | some point => ∃ position, (presentation.coding point.2).decode slot = some position

def edgeGuard {environment : Base} (payload : RecursivePayload presentation environment)
    (slot : Nat) (child : RecursiveSpace.Tree (RecursivePayload presentation environment)) : Prop :=
  match payload with
  | none => False
  | some point => ∃ position, (presentation.coding point.2).decode slot = some position ∧
      HasRootIndex presentation child (presentation.polynomial.next point.2 position)

def guardedStep
    (property : ∀ environment,
      RecursiveSpace.Tree (RecursivePayload presentation environment) → Prop)
    (environment : Base)
    (tree : RecursiveSpace.Tree (RecursivePayload presentation environment)) : Prop :=
  ∃ tag payload children,
    shapeGuard presentation tag payload ∧
    tree = RecursiveSpace.construct tag payload children ∧
    ∀ slot,
      (activeGuard presentation payload slot →
        edgeGuard presentation payload slot (children slot) ∧ property environment (children slot)) ∧
      (¬ activeGuard presentation payload slot → children slot = RecursiveSpace.bottom)

theorem guardedStep_iff_predicateStep
    (property : ∀ environment,
      RecursiveSpace.Tree (RecursivePayload presentation environment) → Prop)
    (environment : Base)
    (tree : RecursiveSpace.Tree (RecursivePayload presentation environment)) :
    guardedStep presentation property environment tree ↔
      predicateStep presentation property environment tree := by
  constructor
  · rintro ⟨tag, payload, children, validShape, same, conditions⟩
    cases payload with
    | none => exact validShape.elim
    | some point =>
      change tag = presentation.tag point.2 at validShape
      subst tag
      refine ⟨point, children, same, ?_, ?_⟩
      · intro slot position decoded
        obtain ⟨⟨other, otherDecoded, root⟩, holds⟩ :=
          (conditions slot).1 ⟨position, decoded⟩
        have equal := Option.some.inj (otherDecoded.symm.trans decoded)
        subst other
        exact ⟨root, holds⟩
      · intro slot absent
        apply (conditions slot).2
        rintro ⟨position, decoded⟩
        rw [absent] at decoded
        cases decoded
  · rintro ⟨point, children, same, active, canonical⟩
    refine ⟨presentation.tag point.2, some point, children, rfl, same, ?_⟩
    intro slot
    constructor
    · rintro ⟨position, decoded⟩
      obtain ⟨root, holds⟩ := active slot position decoded
      exact ⟨⟨position, decoded, root⟩, holds⟩
    · intro inactive
      apply canonical slot
      cases decoded : (presentation.coding point.2).decode slot with
      | none => rfl
      | some position => exact False.elim (inactive ⟨position, decoded⟩)

theorem familyValid_iff_guardedStep (environment : Base)
    (tree : RecursiveSpace.Tree (RecursivePayload presentation environment)) :
    FamilyValid presentation tree ↔
      guardedStep presentation (fun _ tree => FamilyValid presentation tree) environment tree :=
  (familyValid_iff_predicateStep presentation environment tree).trans
    (guardedStep_iff_predicateStep presentation _ environment tree).symm

theorem constructorClosed_contains
    (property : ∀ environment, Index environment →
      RecursiveSpace.Tree (RecursivePayload presentation environment) → Prop)
    (closed : ConstructorClosed presentation property) {environment : Base}
    {index : Index environment} (source : Fix presentation.polynomial environment index) :
    property environment index
      (toRecursiveSpace presentation
        (GuardedRaw.encode presentation.polynomial (positions presentation) source)) := by
  induction source with
  | roll shape children hypotheses =>
    apply closed
    refine ⟨shape, (fun position => toRecursiveSpace presentation
      (GuardedRaw.encode presentation.polynomial (positions presentation) (children position))), ?_,
      hypotheses⟩
    rw [GuardedRaw.encode_roll]
    exact toRecursiveSpace_padded_node presentation shape _

theorem recursiveValid_least
    (property : ∀ environment, Index environment →
      RecursiveSpace.Tree (RecursivePayload presentation environment) → Prop)
    (closed : ConstructorClosed presentation property) {environment : Base}
    {index : Index environment}
    (tree : RecursiveSpace.Tree (RecursivePayload presentation environment))
    (valid : RecursiveValid presentation tree index) : property environment index tree := by
  obtain ⟨encoded, rawValid⟩ := valid
  have result := constructorClosed_contains presentation property closed
    (GuardedRaw.decode presentation.polynomial (positions presentation)
      (fromRecursiveSpace presentation tree encoded) index rawValid)
  rw [GuardedRaw.encode_decode, toRecursiveSpace_fromRecursiveSpace] at result
  exact result

theorem recursiveValid_iff_least (environment : Base) (index : Index environment)
    (tree : RecursiveSpace.Tree (RecursivePayload presentation environment)) :
    RecursiveValid presentation tree index ↔
      ∀ property : ∀ environment, Index environment →
          RecursiveSpace.Tree (RecursivePayload presentation environment) → Prop,
        ConstructorClosed presentation property → property environment index tree := by
  constructor
  · intro valid property closed
    exact recursiveValid_least presentation property closed tree valid
  · intro least
    exact least (fun _ index tree => RecursiveValid presentation tree index)
      (fun environment index tree generated =>
        (recursiveValid_iff_constructorStep presentation environment index tree).mpr generated)

theorem familyValid_least
    (property : ∀ environment,
      RecursiveSpace.Tree (RecursivePayload presentation environment) → Prop)
    (closed : ∀ environment tree, guardedStep presentation property environment tree →
      property environment tree) (environment : Base)
    (tree : RecursiveSpace.Tree (RecursivePayload presentation environment))
    (valid : FamilyValid presentation tree) : property environment tree := by
  obtain ⟨index, valid⟩ := valid
  have strengthened := recursiveValid_least presentation
    (fun environment index tree => RecursiveValid presentation tree index ∧ property environment tree)
    (by
      intro environment index tree generated
      obtain ⟨shape, children, same, childFacts⟩ := generated
      have valid : RecursiveValid presentation tree index :=
        (recursiveValid_iff_constructorStep presentation environment index tree).mpr
          ⟨shape, children, same, fun position => (childFacts position).1⟩
      refine ⟨valid, closed environment tree ?_⟩
      apply (guardedStep_iff_predicateStep presentation property environment tree).mpr
      refine ⟨⟨index, shape⟩, (presentation.coding shape).extend RecursiveSpace.bottom children,
        same, ?_, (presentation.coding shape).extend_canonical _ _⟩
      intro slot position decoded
      simp only [SlotEncoding.extend, decoded]
      exact ⟨recursiveValid_hasRootIndex presentation _ _ (childFacts position).1,
        (childFacts position).2⟩) tree valid
  exact strengthened.2

theorem familyValid_iff_least (environment : Base)
    (tree : RecursiveSpace.Tree (RecursivePayload presentation environment)) :
    FamilyValid presentation tree ↔
      ∀ property : ∀ environment,
          RecursiveSpace.Tree (RecursivePayload presentation environment) → Prop,
        (∀ environment tree, guardedStep presentation property environment tree →
          property environment tree) → property environment tree := by
  constructor
  · intro valid property closed
    exact familyValid_least presentation property closed environment tree valid
  · intro least
    exact least (fun _ tree => FamilyValid presentation tree)
      (fun environment tree generated =>
        (familyValid_iff_guardedStep presentation environment tree).mpr generated)

theorem familyValid_induction (environment : Base)
    (property : RecursiveSpace.Tree (RecursivePayload presentation environment) → Prop)
    (at_constructor : ∀ (index : Index environment)
      (shape : presentation.polynomial.Shape environment index)
      (children : presentation.polynomial.Position shape →
        RecursiveSpace.Tree (RecursivePayload presentation environment)),
      (∀ position, RecursiveValid presentation (children position)
        (presentation.polynomial.next shape position) ∧ property (children position)) →
      property (RecursiveSpace.construct (presentation.tag shape) (some ⟨index, shape⟩)
        ((presentation.coding shape).extend RecursiveSpace.bottom children)))
    (tree : RecursiveSpace.Tree (RecursivePayload presentation environment))
    (valid : FamilyValid presentation tree) : property tree := by
  have encoded : ∀ (index : Index environment) (source : Fix presentation.polynomial environment index),
      property (toRecursiveSpace presentation
        (GuardedRaw.encode presentation.polynomial (positions presentation) source)) := by
    intro index source
    induction source with
    | roll shape children hypotheses =>
      have equality := (congrArg (toRecursiveSpace presentation)
        (GuardedRaw.encode_roll presentation.polynomial (positions presentation) shape children)).trans
          (toRecursiveSpace_padded_node presentation shape
            (fun position => GuardedRaw.encode presentation.polynomial (positions presentation)
              (children position)))
      apply (congrArg property equality).mpr
      apply at_constructor
      intro position
      exact ⟨(recursiveValid_toRecursiveSpace_iff presentation _ _).mpr
        (GuardedRaw.encode_valid presentation.polynomial (positions presentation) (children position)),
        hypotheses position⟩
  obtain ⟨index, encodedTree, rawValid⟩ := valid
  have result := encoded index (GuardedRaw.decode presentation.polynomial (positions presentation)
    (fromRecursiveSpace presentation tree encodedTree) index rawValid)
  rw [GuardedRaw.encode_decode, toRecursiveSpace_fromRecursiveSpace] at result
  exact result

#print axioms recursiveValid_iff_constructorStep
#print axioms constructorStep_mono
#print axioms recursiveValid_iff_least
#print axioms familyValid_iff_guardedStep
#print axioms familyValid_iff_least

end Mettapedia.TypeTheory.IndexedPolynomial.RecursiveSpaceRepresentation

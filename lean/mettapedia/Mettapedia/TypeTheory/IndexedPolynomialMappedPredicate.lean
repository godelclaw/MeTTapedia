import Mettapedia.TypeTheory.IndexedPolynomialRecursiveSpacePredicate
import Mettapedia.TypeTheory.RecursiveSpacePayloadMap

/-!
# Indexed family predicates after payload encoding

The target contains the images of the original indexed family under an actual
recursive payload map. Its constructor step retains every source position and
canonical padding. Root checks inspect only a constructor layer; recursive
membership is a separate predicate. Injectivity of the payload encoding gives
the exact index agreement needed to combine those two checks.
-/

set_option autoImplicit false
namespace Mettapedia.TypeTheory.IndexedPolynomial.RecursiveSpaceRepresentation.Mapped

universe b i s p t
variable {Base : Type b} {Index : Base → Type i}
variable (presentation : Presentation.{b,i,s,p} (Base := Base) (Index := Index))
  (environment : Base) {Payload : Type t}
  (mapping : RecursivePayload presentation environment → Payload)

def Valid (index : Index environment) (tree : RecursiveSpace.Tree Payload) : Prop :=
  ∃ original, RecursiveValid presentation original index ∧ RecursiveSpace.mapPayload mapping original = tree

def FamilyValid (tree : RecursiveSpace.Tree Payload) : Prop := ∃ index, Valid presentation environment mapping index tree

def ConstructorStep (property : Index environment → RecursiveSpace.Tree Payload → Prop)
    (index : Index environment) (tree : RecursiveSpace.Tree Payload) : Prop :=
  ∃ (shape : presentation.polynomial.Shape environment index)
    (children : presentation.polynomial.Position shape → RecursiveSpace.Tree Payload),
    tree = RecursiveSpace.construct (presentation.tag shape) (mapping (some ⟨index, shape⟩))
      ((presentation.coding shape).extend RecursiveSpace.bottom children) ∧
    ∀ position, property (presentation.polynomial.next shape position) (children position)

theorem map_extend {Position : Type p} (coding : SlotEncoding Position Nat)
    (children : Position → RecursiveSpace.Tree (RecursivePayload presentation environment)) :
    (fun slot => RecursiveSpace.mapPayload mapping (coding.extend RecursiveSpace.bottom children slot)) =
      coding.extend RecursiveSpace.bottom (fun position => RecursiveSpace.mapPayload mapping (children position)) := by
  funext slot
  cases decoded : coding.decode slot with
  | none => simp only [SlotEncoding.extend, decoded, RecursiveSpace.mapPayload_bottom]
  | some position => simp only [SlotEncoding.extend, decoded]

theorem valid_iff_constructorStep (index : Index environment) (tree : RecursiveSpace.Tree Payload) :
    Valid presentation environment mapping index tree ↔
      ConstructorStep presentation environment mapping (Valid presentation environment mapping) index tree := by
  constructor
  · rintro ⟨original, valid, rfl⟩
    obtain ⟨shape, children, same, childrenValid⟩ :=
      (recursiveValid_iff_constructorStep presentation environment index original).mp valid
    refine ⟨shape, (fun position => RecursiveSpace.mapPayload mapping (children position)), ?_, ?_⟩
    · rw [same, RecursiveSpace.mapPayload_construct, map_extend]
    · intro position
      exact ⟨children position, childrenValid position, rfl⟩
  · rintro ⟨shape, children, rfl, childrenValid⟩
    let originals := fun position => (childrenValid position).choose
    have restored : (fun position => RecursiveSpace.mapPayload mapping (originals position)) = children := by
      funext position
      exact (childrenValid position).choose_spec.2
    refine ⟨RecursiveSpace.construct (presentation.tag shape) (some ⟨index, shape⟩)
      ((presentation.coding shape).extend RecursiveSpace.bottom originals), ?_, ?_⟩
    · exact (recursiveValid_iff_constructorStep presentation environment index _).mpr
        ⟨shape, originals, rfl, fun position => (childrenValid position).choose_spec.1⟩
    · rw [RecursiveSpace.mapPayload_construct, map_extend, restored]

def HasRootIndex (tree : RecursiveSpace.Tree Payload) (index : Index environment) : Prop :=
  ∃ (shape : presentation.polynomial.Shape environment index)
    (children : Nat → RecursiveSpace.Tree Payload),
    tree = RecursiveSpace.construct (presentation.tag shape) (mapping (some ⟨index, shape⟩)) children

theorem valid_hasRootIndex (index : Index environment) (tree : RecursiveSpace.Tree Payload)
    (valid : Valid presentation environment mapping index tree) :
    HasRootIndex presentation environment mapping tree index := by
  obtain ⟨shape, children, same, _⟩ := (valid_iff_constructorStep presentation environment mapping index tree).mp valid
  exact ⟨shape, _, same⟩

theorem valid_bottom_refused (index : Index environment) :
    ¬ Valid presentation environment mapping index RecursiveSpace.bottom := by
  intro valid
  obtain ⟨shape, children, same⟩ := valid_hasRootIndex presentation environment mapping index _ valid
  exact RecursiveSpace.construct_ne_bottom _ _ _ same.symm

variable (injective : Function.Injective mapping)
include injective

theorem rootIndex_unique (tree : RecursiveSpace.Tree Payload) (first second : Index environment)
    (firstRoot : HasRootIndex presentation environment mapping tree first)
    (secondRoot : HasRootIndex presentation environment mapping tree second) : first = second := by
  obtain ⟨firstShape, firstChildren, firstEquation⟩ := firstRoot
  obtain ⟨secondShape, secondChildren, secondEquation⟩ := secondRoot
  have payloads := ((RecursiveSpace.construct_injective _ _ _ _ _ _).mp
    (firstEquation.symm.trans secondEquation)).2.1
  exact congrArg Sigma.fst (Option.some.inj (injective payloads))

theorem valid_iff_family_and_root (tree : RecursiveSpace.Tree Payload) (index : Index environment) :
    Valid presentation environment mapping index tree ↔
      FamilyValid presentation environment mapping tree ∧ HasRootIndex presentation environment mapping tree index := by
  constructor
  · intro valid
    exact ⟨⟨index, valid⟩, valid_hasRootIndex presentation environment mapping index tree valid⟩
  · rintro ⟨⟨other, valid⟩, root⟩
    have same := rootIndex_unique presentation environment mapping injective tree other index
      (valid_hasRootIndex presentation environment mapping other tree valid) root
    exact same ▸ valid

theorem valid_construct_iff (index : Index environment)
    (point : Σ index, presentation.polynomial.Shape environment index)
    (children : Nat → RecursiveSpace.Tree Payload) :
    Valid presentation environment mapping index
      (RecursiveSpace.construct (presentation.tag point.2) (mapping (some point)) children) ↔
      index = point.1 ∧ (presentation.coding point.2).Canonical RecursiveSpace.bottom children ∧
      ∀ position, Valid presentation environment mapping (presentation.polynomial.next point.2 position)
        (children ((presentation.coding point.2).encode position)) := by
  rw [valid_iff_constructorStep]
  constructor
  · rintro ⟨shape, recursive, same, valid⟩
    obtain ⟨_, payloads, branches⟩ := (RecursiveSpace.construct_injective _ _ _ _ _ _).mp same
    have points := Option.some.inj (injective payloads)
    cases points
    refine ⟨rfl, ?_, ?_⟩
    · rw [branches]
      exact (presentation.coding shape).extend_canonical _ _
    · intro position
      rw [branches, SlotEncoding.extend_at]
      exact valid position
  · rintro ⟨rfl, canonical, valid⟩
    refine ⟨point.2, (presentation.coding point.2).restrict children, ?_, valid⟩
    rw [SlotEncoding.extend_restrict _ _ _ canonical]

omit injective in
theorem family_induction (property : RecursiveSpace.Tree Payload → Prop)
    (at_constructor : ∀ (index : Index environment)
      (shape : presentation.polynomial.Shape environment index)
      (children : presentation.polynomial.Position shape → RecursiveSpace.Tree Payload),
      (∀ position, Valid presentation environment mapping (presentation.polynomial.next shape position)
        (children position) ∧ property (children position)) →
      property (RecursiveSpace.construct (presentation.tag shape) (mapping (some ⟨index, shape⟩))
        ((presentation.coding shape).extend RecursiveSpace.bottom children)))
    (tree : RecursiveSpace.Tree Payload) (valid : FamilyValid presentation environment mapping tree) : property tree := by
  obtain ⟨index, original, valid, rfl⟩ := valid
  apply familyValid_induction presentation environment
    (fun original => property (RecursiveSpace.mapPayload mapping original)) ?_ original ⟨index, valid⟩
  intro index shape children hypotheses
  rw [RecursiveSpace.mapPayload_construct, map_extend]
  apply at_constructor
  intro position
  exact ⟨⟨children position, (hypotheses position).1, rfl⟩, (hypotheses position).2⟩

def ShapeGuard (tag : Nat) (payload : Payload) : Prop :=
  ∃ point : Σ index, presentation.polynomial.Shape environment index,
    tag = presentation.tag point.2 ∧ payload = mapping (some point)

def ActiveGuard (payload : Payload) (slot : Nat) : Prop :=
  ∃ (point : Σ index, presentation.polynomial.Shape environment index)
    (position : presentation.polynomial.Position point.2),
    payload = mapping (some point) ∧ (presentation.coding point.2).decode slot = some position

def EdgeGuard (payload : Payload) (slot : Nat) (child : RecursiveSpace.Tree Payload) : Prop :=
  ∃ (point : Σ index, presentation.polynomial.Shape environment index)
    (position : presentation.polynomial.Position point.2),
    payload = mapping (some point) ∧ (presentation.coding point.2).decode slot = some position ∧
      HasRootIndex presentation environment mapping child (presentation.polynomial.next point.2 position)

def GuardedStep (property : RecursiveSpace.Tree Payload → Prop) (tree : RecursiveSpace.Tree Payload) : Prop :=
  ∃ tag payload children, ShapeGuard presentation environment mapping tag payload ∧
    tree = RecursiveSpace.construct tag payload children ∧
    ∀ slot,
      (ActiveGuard presentation environment mapping payload slot →
        EdgeGuard presentation environment mapping payload slot (children slot) ∧ property (children slot)) ∧
      (¬ ActiveGuard presentation environment mapping payload slot → children slot = RecursiveSpace.bottom)

def PredicateStep (property : RecursiveSpace.Tree Payload → Prop) (tree : RecursiveSpace.Tree Payload) : Prop :=
  ∃ (point : Σ index, presentation.polynomial.Shape environment index)
    (children : Nat → RecursiveSpace.Tree Payload),
    tree = RecursiveSpace.construct (presentation.tag point.2) (mapping (some point)) children ∧
    (∀ slot position, (presentation.coding point.2).decode slot = some position →
      HasRootIndex presentation environment mapping (children slot) (presentation.polynomial.next point.2 position) ∧
        property (children slot)) ∧
    (presentation.coding point.2).Canonical RecursiveSpace.bottom children

theorem guardedStep_iff_predicateStep (property : RecursiveSpace.Tree Payload → Prop) (tree : RecursiveSpace.Tree Payload) :
    GuardedStep presentation environment mapping property tree ↔
      PredicateStep presentation environment mapping property tree := by
  constructor
  · rintro ⟨tag, payload, children, ⟨point, tagSame, payloadSame⟩, same, conditions⟩
    subst tag
    subst payload
    refine ⟨point, children, same, ?_, ?_⟩
    · intro slot position decoded
      obtain ⟨⟨other, otherPosition, payloadSame, otherDecoded, root⟩, holds⟩ :=
        (conditions slot).1 ⟨point, position, rfl, decoded⟩
      have points := Option.some.inj (injective payloadSame)
      cases points
      have positions := Option.some.inj (otherDecoded.symm.trans decoded)
      subst otherPosition
      exact ⟨root, holds⟩
    · intro slot absent
      apply (conditions slot).2
      rintro ⟨other, position, payloadSame, decoded⟩
      have points := Option.some.inj (injective payloadSame)
      cases points
      rw [absent] at decoded
      cases decoded
  · rintro ⟨point, children, same, active, canonical⟩
    refine ⟨presentation.tag point.2, mapping (some point), children, ⟨point, rfl, rfl⟩, same, ?_⟩
    intro slot
    constructor
    · rintro ⟨other, position, payloadSame, decoded⟩
      have points := Option.some.inj (injective payloadSame)
      cases points
      obtain ⟨root, holds⟩ := active slot position decoded
      exact ⟨⟨point, position, rfl, decoded, root⟩, holds⟩
    · intro inactive
      apply canonical slot
      cases decoded : (presentation.coding point.2).decode slot with
      | none => rfl
      | some position => exact False.elim (inactive ⟨point, position, rfl, decoded⟩)

theorem familyValid_iff_predicateStep (tree : RecursiveSpace.Tree Payload) :
    FamilyValid presentation environment mapping tree ↔
      PredicateStep presentation environment mapping (FamilyValid presentation environment mapping) tree := by
  constructor
  · rintro ⟨index, valid⟩
    obtain ⟨shape, children, same, childrenValid⟩ :=
      (valid_iff_constructorStep presentation environment mapping index tree).mp valid
    refine ⟨⟨index, shape⟩, (presentation.coding shape).extend RecursiveSpace.bottom children,
      same, ?_, (presentation.coding shape).extend_canonical _ _⟩
    intro slot position decoded
    simp only [SlotEncoding.extend, decoded]
    exact ⟨valid_hasRootIndex presentation environment mapping _ _ (childrenValid position),
      ⟨_, childrenValid position⟩⟩
  · rintro ⟨point, children, rfl, active, canonical⟩
    apply Exists.intro point.1
    apply (valid_iff_constructorStep presentation environment mapping point.1 _).mpr
    refine ⟨point.2, (presentation.coding point.2).restrict children, ?_, ?_⟩
    · rw [SlotEncoding.extend_restrict _ _ _ canonical]
    · intro position
      obtain ⟨root, valid⟩ := active _ position ((presentation.coding point.2).decode_encode position)
      exact (valid_iff_family_and_root presentation environment mapping injective _ _).mpr ⟨valid, root⟩

theorem familyValid_fixed_point (tree : RecursiveSpace.Tree Payload) :
    FamilyValid presentation environment mapping tree ↔
      GuardedStep presentation environment mapping (FamilyValid presentation environment mapping) tree :=
  (familyValid_iff_predicateStep presentation environment mapping injective tree).trans
    (guardedStep_iff_predicateStep presentation environment mapping injective _ tree).symm

theorem familyValid_least (property : RecursiveSpace.Tree Payload → Prop)
    (closed : ∀ tree, GuardedStep presentation environment mapping property tree → property tree)
    (tree : RecursiveSpace.Tree Payload) (valid : FamilyValid presentation environment mapping tree) :
    property tree := by
  apply family_induction presentation environment mapping property ?_ tree valid
  intro index shape children hypotheses
  apply closed
  apply (guardedStep_iff_predicateStep presentation environment mapping injective _ _).mpr
  refine ⟨⟨index, shape⟩, (presentation.coding shape).extend RecursiveSpace.bottom children,
    rfl, ?_, (presentation.coding shape).extend_canonical _ _⟩
  intro slot position decoded
  simp only [SlotEncoding.extend, decoded]
  exact ⟨valid_hasRootIndex presentation environment mapping _ _ (hypotheses position).1,
    (hypotheses position).2⟩

theorem familyValid_iff_least (tree : RecursiveSpace.Tree Payload) :
    FamilyValid presentation environment mapping tree ↔
      ∀ property : RecursiveSpace.Tree Payload → Prop,
        (∀ value, GuardedStep presentation environment mapping property value → property value) → property tree := by
  constructor
  · intro valid property closed
    exact familyValid_least presentation environment mapping injective property closed tree valid
  · intro least
    exact least (FamilyValid presentation environment mapping)
      (fun value generated => (familyValid_fixed_point presentation environment mapping injective value).mpr generated)

#print axioms valid_iff_constructorStep
#print axioms rootIndex_unique
#print axioms family_induction
#print axioms guardedStep_iff_predicateStep
#print axioms familyValid_fixed_point
#print axioms familyValid_iff_least
end Mettapedia.TypeTheory.IndexedPolynomial.RecursiveSpaceRepresentation.Mapped

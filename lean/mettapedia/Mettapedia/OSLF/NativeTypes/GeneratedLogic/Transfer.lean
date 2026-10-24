import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Semantics

/-!
# Generated formulas along homomorphisms

A homomorphism of native structures carries steps to steps, with their labels, shapes to shapes, types
to types and names to names (`Hom`). Along it the generated logic splits into two fragments, exchanged by the dual
(`existential_dual`):
- **existential formulas hold at images** (`sat_of_hom`). These are built from the formers that assert
  a step, a predecessor, a shape, a type, a name or a witness, together with `∧`, `∨` and both fixed
  points;
- **universal formulas come back** (`sat_of_hom_universal`). These are built from the duals: every
  step, every predecessor, every presentation of a shape, `nonEmpty`, `notBound`, `untyped`, `isNot`
  and `everyOf`.

A finite structure that a language maps into therefore refutes existential formulas and proves
universal ones for it. This is the reach of a finite-model certificate. The hom formers belong to
neither fragment: they quantify over all arguments, which a homomorphism need not reach.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax
open Formula NativeStructure

universe u v

/-- **A homomorphism of native structures**: a map carrying steps to steps and shapes to shapes. -/
structure Hom {Source : Type u} {Target : Type v} (S : NativeStructure Source) (T : NativeStructure Target) where
  map : Source → Target
  step : ∀ {source label target}, S.step source label target → T.step (map source) label (map target)
  built : ∀ {element constructor parts}, S.built element constructor parts →
    T.built (map element) constructor (parts.map map)
  split : ∀ {element kind first second}, S.split element kind first second →
    T.split (map element) kind (map first) (map second)
  empty : ∀ {element kind}, S.empty element kind → T.empty (map element) kind
  single : ∀ {element kind member}, S.single element kind member → T.single (map element) kind (map member)
  body : ∀ {element inner}, S.body element inner → T.body (map element) (map inner)
  multiBody : ∀ {element arity inner}, S.multiBody element arity inner → T.multiBody (map element) arity (map inner)
  bound : ∀ {element index}, S.bound element index → T.bound (map element) index
  typed : ∀ {element type}, S.typed element type → T.typed (map element) type
  named : ∀ {element term}, S.named element term → T.named (map element) term

namespace Formula

mutual
/-- Whether a formula asserts only existence: steps, predecessors, shapes and witnesses. -/
def existential : {n : ℕ} → Formula n → Bool
  | _, .top | _, .bot | _, .var _ | _, .empty _ | _, .bound _ | _, .typed _ | _, .is _ => true
  | _, .and left right | _, .or left right | _, .split _ left right => existential left && existential right
  | _, .mu inner | _, .nu inner => existential inner
  | _, .possibly _ formula | _, .sometimeBefore _ formula | _, .single _ formula | _, .body formula
  | _, .multiBody _ formula | _, .someOf _ formula => existential formula
  | _, .built _ arguments => existentialList arguments
  | _, _ => false

def existentialList : {n : ℕ} → Formulas n → Bool
  | _, .nil => true
  | _, .cons formula formulas => existential formula && existentialList formulas
end

mutual
/-- Whether a formula asserts only universality: every step, every predecessor, every presentation. -/
def universal : {n : ℕ} → Formula n → Bool
  | _, .top | _, .bot | _, .var _ | _, .nonEmpty _ | _, .notBound _ | _, .untyped _ | _, .isNot _ => true
  | _, .and left right | _, .or left right | _, .everySplit _ left right => universal left && universal right
  | _, .mu inner | _, .nu inner => universal inner
  | _, .necessarily _ formula | _, .alwaysBefore _ formula | _, .everySingle _ formula | _, .everyBody formula
  | _, .everyMultiBody _ formula | _, .everyOf _ formula => universal formula
  | _, .everyBuilt _ arguments => universalList arguments
  | _, _ => false

def universalList : {n : ℕ} → Formulas n → Bool
  | _, .nil => true
  | _, .cons formula formulas => universal formula && universalList formulas
end

mutual
/-- **The dual exchanges the two fragments.** -/
theorem existential_dual : ∀ {n : ℕ} (formula : Formula n), existential formula.dual = universal formula
  | _, .top | _, .bot | _, .var _ | _, .empty _ | _, .nonEmpty _ | _, .bound _ | _, .notBound _
  | _, .typed _ | _, .untyped _ | _, .is _ | _, .isNot _ => rfl
  | _, .and left right | _, .or left right | _, .split _ left right | _, .everySplit _ left right => by
    simp only [dual, existential, universal, existential_dual left, existential_dual right]
  | _, .mapsAll _ _ | _, .mapsSome _ _ | _, .atLeast _ _ _ _ | _, .allButFewer _ _ _ _ => rfl
  | _, .mu inner | _, .nu inner => by simp only [dual, existential, universal, existential_dual inner]
  | _, .possibly _ formula | _, .necessarily _ formula | _, .sometimeBefore _ formula
  | _, .alwaysBefore _ formula | _, .single _ formula | _, .everySingle _ formula | _, .body formula
  | _, .everyBody formula | _, .multiBody _ formula | _, .everyMultiBody _ formula | _, .someOf _ formula
  | _, .everyOf _ formula => by simp only [dual, existential, universal, existential_dual formula]
  | _, .built _ arguments | _, .everyBuilt _ arguments => by
    simp only [dual, existential, universal, existentialList_dualList arguments]

theorem existentialList_dualList : ∀ {n : ℕ} (formulas : Formulas n),
    existentialList (dualList formulas) = universalList formulas
  | _, .nil => rfl
  | _, .cons formula formulas => by
    simp only [dualList, existentialList, universalList, existential_dual formula,
      existentialList_dualList formulas]
end

end Formula

namespace Hom

variable {Source : Type u} {Target : Type v} {S : NativeStructure Source} {T : NativeStructure Target}
  (hom : Hom S T)

/-- Environments related forward: what the source puts in a variable, the map puts in the target's. -/
def EnvForward {n : ℕ} (sourceEnv : Env Source n) (targetEnv : Env Target n) : Prop :=
  ∀ index element, element ∈ sourceEnv index → hom.map element ∈ targetEnv index

/-- Environments related backward: what the target puts in a variable at an image, the source has. -/
def EnvBackward {n : ℕ} (sourceEnv : Env Source n) (targetEnv : Env Target n) : Prop :=
  ∀ index element, hom.map element ∈ targetEnv index → element ∈ sourceEnv index

theorem EnvForward.extend {n : ℕ} {sourceEnv : Env Source n} {targetEnv : Env Target n}
    (related : hom.EnvForward sourceEnv targetEnv) {first : Set Source} {second : Set Target}
    (inside : ∀ element ∈ first, hom.map element ∈ second) :
    hom.EnvForward (sourceEnv.extend first) (targetEnv.extend second) := by
  intro index element
  refine Fin.cases (fun member => ?_) (fun index' member => ?_) index
  · exact inside element member
  · exact related index' element member

theorem EnvBackward.extend {n : ℕ} {sourceEnv : Env Source n} {targetEnv : Env Target n}
    (related : hom.EnvBackward sourceEnv targetEnv) {first : Set Source} {second : Set Target}
    (inside : ∀ element, hom.map element ∈ second → element ∈ first) :
    hom.EnvBackward (sourceEnv.extend first) (targetEnv.extend second) := by
  intro index element
  refine Fin.cases (fun member => ?_) (fun index' member => ?_) index
  · exact inside element member
  · exact related index' element member

mutual
/-- **Existential formulas hold at images.** -/
theorem sat_of_hom : ∀ {n : ℕ} (formula : Formula n), formula.existential = true →
    ∀ {sourceEnv : Env Source n} {targetEnv : Env Target n}, hom.EnvForward sourceEnv targetEnv →
      ∀ element, S.sat sourceEnv formula element → T.sat targetEnv formula (hom.map element)
  | _, .top, _, _, _, _, _, _ => trivial
  | _, .bot, _, _, _, _, _, holds => holds
  | _, .and left right, existential, _, _, related, element, holds => by
    simp only [Formula.existential, Bool.and_eq_true] at existential
    exact ⟨sat_of_hom left existential.1 related element holds.1,
      sat_of_hom right existential.2 related element holds.2⟩
  | _, .or left right, existential, _, _, related, element, holds => by
    simp only [Formula.existential, Bool.and_eq_true] at existential
    rcases holds with first | second
    · exact Or.inl (sat_of_hom left existential.1 related element first)
    · exact Or.inr (sat_of_hom right existential.2 related element second)
  | _, .var index, _, _, _, related, element, holds => related index element holds
  | _, .mu inner, existential, _, _, related, element, holds => by
    intro closed closedHolds
    exact holds (hom.map ⁻¹' closed) fun other otherHolds =>
      closedHolds _ (sat_of_hom inner existential (EnvForward.extend hom related fun _ member => member) other otherHolds)
  | _, .nu inner, existential, _, _, related, element, holds => by
    obtain ⟨invariant, member, preserved⟩ := holds
    refine ⟨hom.map '' invariant, ⟨element, member, rfl⟩, ?_⟩
    rintro _ ⟨other, otherMember, rfl⟩
    exact sat_of_hom inner existential
      (EnvForward.extend hom related fun _ innerMember => Set.mem_image_of_mem hom.map innerMember) other
      (preserved other otherMember)
  | _, .possibly _ formula, existential, _, _, related, _, holds => by
    obtain ⟨next, step, nextHolds⟩ := holds
    exact ⟨hom.map next, hom.step step, sat_of_hom formula existential related next nextHolds⟩
  | _, .sometimeBefore _ formula, existential, _, _, related, _, holds => by
    obtain ⟨previous, step, previousHolds⟩ := holds
    exact ⟨hom.map previous, hom.step step, sat_of_hom formula existential related previous previousHolds⟩
  | _, .built _ arguments, existential, _, _, related, _, holds => by
    obtain ⟨parts, isBuilt, all⟩ := holds
    exact ⟨parts.map hom.map, hom.built isBuilt, satAll_of_hom arguments existential related parts all⟩
  | _, .split _ left right, existential, _, _, related, _, holds => by
    simp only [Formula.existential, Bool.and_eq_true] at existential
    obtain ⟨first, second, isSplit, firstHolds, secondHolds⟩ := holds
    exact ⟨hom.map first, hom.map second, hom.split isSplit, sat_of_hom left existential.1 related first firstHolds,
      sat_of_hom right existential.2 related second secondHolds⟩
  | _, .empty _, _, _, _, _, _, holds => hom.empty holds
  | _, .single _ formula, existential, _, _, related, _, holds => by
    obtain ⟨member, isSingle, memberHolds⟩ := holds
    exact ⟨hom.map member, hom.single isSingle, sat_of_hom formula existential related member memberHolds⟩
  | _, .body formula, existential, _, _, related, _, holds => by
    obtain ⟨inner, isBody, innerHolds⟩ := holds
    exact ⟨hom.map inner, hom.body isBody, sat_of_hom formula existential related inner innerHolds⟩
  | _, .multiBody _ formula, existential, _, _, related, _, holds => by
    obtain ⟨inner, isBody, innerHolds⟩ := holds
    exact ⟨hom.map inner, hom.multiBody isBody, sat_of_hom formula existential related inner innerHolds⟩
  | _, .bound _, _, _, _, _, _, holds => hom.bound holds
  | _, .typed _, _, _, _, _, _, holds => hom.typed holds
  | _, .is _, _, _, _, _, _, holds => hom.named holds
  | _, .someOf _ formula, existential, _, _, related, _, holds => by
    obtain ⟨witness, isTyped, witnessHolds⟩ := holds
    exact ⟨hom.map witness, hom.typed isTyped, sat_of_hom formula existential related witness witnessHolds⟩
  | _, .necessarily _ _, existential, _, _, _, _, _ | _, .alwaysBefore _ _, existential, _, _, _, _, _
  | _, .everyBuilt _ _, existential, _, _, _, _, _ | _, .everySplit _ _ _, existential, _, _, _, _, _
  | _, .nonEmpty _, existential, _, _, _, _, _ | _, .everySingle _ _, existential, _, _, _, _, _
  | _, .everyBody _, existential, _, _, _, _, _ | _, .everyMultiBody _ _, existential, _, _, _, _, _
  | _, .notBound _, existential, _, _, _, _, _ | _, .untyped _, existential, _, _, _, _, _
  | _, .isNot _, existential, _, _, _, _, _ | _, .mapsAll _ _, existential, _, _, _, _, _
  | _, .mapsSome _ _, existential, _, _, _, _, _ | _, .everyOf _ _, existential, _, _, _, _, _ => by
    simp [Formula.existential] at existential

theorem satAll_of_hom : ∀ {n : ℕ} (formulas : Formulas n), Formula.existentialList formulas = true →
    ∀ {sourceEnv : Env Source n} {targetEnv : Env Target n}, hom.EnvForward sourceEnv targetEnv →
      ∀ parts, S.satAll sourceEnv formulas parts → T.satAll targetEnv formulas (parts.map hom.map)
  | _, .nil, _, _, _, _, [], _ => trivial
  | _, .cons formula formulas, existential, _, _, related, part :: parts, holds => by
    simp only [Formula.existentialList, Bool.and_eq_true] at existential
    exact ⟨sat_of_hom formula existential.1 related part holds.1,
      satAll_of_hom formulas existential.2 related parts holds.2⟩
  | _, .nil, _, _, _, _, _ :: _, holds => holds.elim
  | _, .cons _ _, _, _, _, _, [], holds => holds.elim
end

mutual
/-- **Universal formulas come back from images.** -/
theorem sat_of_hom_universal : ∀ {n : ℕ} (formula : Formula n), formula.universal = true →
    ∀ {sourceEnv : Env Source n} {targetEnv : Env Target n}, hom.EnvBackward sourceEnv targetEnv →
      ∀ element, T.sat targetEnv formula (hom.map element) → S.sat sourceEnv formula element
  | _, .top, _, _, _, _, _, _ => trivial
  | _, .bot, _, _, _, _, _, holds => holds
  | _, .and left right, universal, _, _, related, element, holds => by
    simp only [Formula.universal, Bool.and_eq_true] at universal
    exact ⟨sat_of_hom_universal left universal.1 related element holds.1,
      sat_of_hom_universal right universal.2 related element holds.2⟩
  | _, .or left right, universal, _, _, related, element, holds => by
    simp only [Formula.universal, Bool.and_eq_true] at universal
    rcases holds with first | second
    · exact Or.inl (sat_of_hom_universal left universal.1 related element first)
    · exact Or.inr (sat_of_hom_universal right universal.2 related element second)
  | _, .var index, _, _, _, related, element, holds => related index element holds
  | _, .mu inner, universal, _, _, related, element, holds => by
    intro closed closedHolds
    let pushed : Set Target := {image | ∀ origin, hom.map origin = image → origin ∈ closed}
    have inside : ∀ origin, hom.map origin ∈ pushed → origin ∈ closed := fun origin member => member origin rfl
    have pushedHolds := holds pushed fun image imageHolds origin originMaps => by
      subst originMaps
      exact closedHolds origin
        (sat_of_hom_universal inner universal (EnvBackward.extend hom related inside) origin imageHolds)
    exact inside element pushedHolds
  | _, .nu inner, universal, _, _, related, element, holds => by
    obtain ⟨invariant, member, preserved⟩ := holds
    refine ⟨hom.map ⁻¹' invariant, member, fun other otherMember => ?_⟩
    exact sat_of_hom_universal inner universal (EnvBackward.extend hom related fun _ inner => inner) other
      (preserved (hom.map other) otherMember)
  | _, .necessarily _ formula, universal, _, _, related, _, holds => by
    intro next step
    exact sat_of_hom_universal formula universal related next (holds _ (hom.step step))
  | _, .alwaysBefore _ formula, universal, _, _, related, _, holds => by
    intro previous step
    exact sat_of_hom_universal formula universal related previous (holds _ (hom.step step))
  | _, .everyBuilt _ arguments, universal, _, _, related, _, holds => by
    intro parts isBuilt
    exact satSome_of_hom_universal arguments universal related parts (holds _ (hom.built isBuilt))
  | _, .everySplit _ left right, universal, _, _, related, _, holds => by
    simp only [Formula.universal, Bool.and_eq_true] at universal
    intro first second isSplit
    rcases holds _ _ (hom.split isSplit) with firstHolds | secondHolds
    · exact Or.inl (sat_of_hom_universal left universal.1 related first firstHolds)
    · exact Or.inr (sat_of_hom_universal right universal.2 related second secondHolds)
  | _, .nonEmpty _, _, _, _, _, _, holds => fun isEmpty => holds (hom.empty isEmpty)
  | _, .everySingle _ formula, universal, _, _, related, _, holds => by
    intro member isSingle
    exact sat_of_hom_universal formula universal related member (holds _ (hom.single isSingle))
  | _, .everyBody formula, universal, _, _, related, _, holds => by
    intro inner isBody
    exact sat_of_hom_universal formula universal related inner (holds _ (hom.body isBody))
  | _, .everyMultiBody _ formula, universal, _, _, related, _, holds => by
    intro inner isBody
    exact sat_of_hom_universal formula universal related inner (holds _ (hom.multiBody isBody))
  | _, .notBound _, _, _, _, _, _, holds => fun isBound => holds (hom.bound isBound)
  | _, .untyped _, _, _, _, _, _, holds => fun isTyped => holds (hom.typed isTyped)
  | _, .isNot _, _, _, _, _, _, holds => fun isNamed => holds (hom.named isNamed)
  | _, .everyOf _ formula, universal, _, _, related, _, holds => by
    intro witness isTyped
    exact sat_of_hom_universal formula universal related witness (holds (hom.map witness) (hom.typed isTyped))
  | _, .possibly _ _, universal, _, _, _, _, _ | _, .sometimeBefore _ _, universal, _, _, _, _, _
  | _, .built _ _, universal, _, _, _, _, _ | _, .split _ _ _, universal, _, _, _, _, _
  | _, .empty _, universal, _, _, _, _, _ | _, .single _ _, universal, _, _, _, _, _
  | _, .body _, universal, _, _, _, _, _ | _, .multiBody _ _, universal, _, _, _, _, _
  | _, .bound _, universal, _, _, _, _, _ | _, .typed _, universal, _, _, _, _, _
  | _, .is _, universal, _, _, _, _, _ | _, .mapsAll _ _, universal, _, _, _, _, _
  | _, .mapsSome _ _, universal, _, _, _, _, _ | _, .someOf _ _, universal, _, _, _, _, _ => by
    simp [Formula.universal] at universal

theorem satSome_of_hom_universal : ∀ {n : ℕ} (formulas : Formulas n), Formula.universalList formulas = true →
    ∀ {sourceEnv : Env Source n} {targetEnv : Env Target n}, hom.EnvBackward sourceEnv targetEnv →
      ∀ parts, T.satSome targetEnv formulas (parts.map hom.map) → S.satSome sourceEnv formulas parts
  | _, .nil, _, _, _, _, [], holds => holds
  | _, .nil, _, _, _, _, _ :: _, _ => trivial
  | _, .cons _ _, _, _, _, _, [], _ => trivial
  | _, .cons formula formulas, universal, _, _, related, part :: parts, holds => by
    simp only [Formula.universalList, Bool.and_eq_true] at universal
    rcases holds with first | rest
    · exact Or.inl (sat_of_hom_universal formula universal.1 related part first)
    · exact Or.inr (satSome_of_hom_universal formulas universal.2 related parts rest)
end

/-- **A structure a language maps into refutes existential formulas**: when one fails at the image, it
fails at the element. -/
theorem not_sat_of_hom {n : ℕ} {formula : Formula n} (existential : formula.existential = true)
    {sourceEnv : Env Source n} {targetEnv : Env Target n} (related : hom.EnvForward sourceEnv targetEnv) {element : Source}
    (fails : ¬ T.sat targetEnv formula (hom.map element)) : ¬ S.sat sourceEnv formula element :=
  fun holds => fails (hom.sat_of_hom formula existential related element holds)

end Hom

end Mettapedia.OSLF.NativeTypes.GeneratedLogic

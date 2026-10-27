import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ManySorted
import Mettapedia.OSLF.Framework.SortedTypedStructuralObservations

/-!
# The sorted structural logic, embedded in many-sorted native types

The sorted structural logic (`SortedTypedInstruments.StructuralObservations`) has, for a sorted signature with
designated parallel sorts, a connective for each constructor, a binary cut and a unit at each parallel sort, read on
the classes of terms modulo associativity, commutativity and the unit of the cut.

- **The classes form a sorted structure** (`classStructure`): a class is built by a constructor from the classes of
  its arguments, splits into two classes it is the cut of, and is empty when it is the unit.
- **The embedding** (`embed`): a constructor connective becomes the constructor former with its arguments at their input
  sorts (`argumentsOf`), the cut becomes the bag split and the unit the empty bag.
- **It is exact** (`holds_iff`): a structural formula holds of a class exactly when its embedding holds there, when
  constructors have distinct names.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.ManySorted

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.SortedConstructors (Signature)
open Mettapedia.OSLF.SortedCommutative (Class classOf classCut Head Term)

universe v

/-! ## Argument formulas at positions -/

/-- Argument formulas, one at each position, each at its sort. -/
def argumentsOf {Srt : Type} {Γ : List Srt} : (n : ℕ) → (Fin n → Srt) → ((position : Fin n) → SFormula Srt Γ) →
    SFormulas Srt Γ
  | 0, _, _ => .nil
  | n + 1, sorts, formulas =>
    .cons (sorts 0) (formulas 0) (argumentsOf n (fun position => sorts position.succ) fun position => formulas position.succ)

/-- **Argument formulas at positions hold along a list exactly when it lists, at the positions' sorts, elements where
they hold.** -/
theorem ssatAll_argumentsOf {Srt : Type} (M : SortedStructure.{v} Srt) {Γ : List Srt} (env : Env M.Element Γ.length) :
    ∀ (n : ℕ) (sorts : Fin n → Srt) (formulas : (position : Fin n) → SFormula Srt Γ) (parts : List M.Element),
      M.ssatAll env (argumentsOf n sorts formulas) parts ↔
        ∃ elements : (position : Fin n) → M.Carrier (sorts position),
          parts = List.ofFn (fun position => ⟨sorts position, elements position⟩) ∧
            ∀ position, M.ssat env (formulas position) ⟨sorts position, elements position⟩
  | 0, sorts, formulas, [] => ⟨fun _ => ⟨fun position => position.elim0, rfl, fun position => position.elim0⟩,
      fun _ => trivial⟩
  | 0, sorts, formulas, _ :: _ => ⟨fun impossible => impossible.elim, by
      rintro ⟨elements, same, -⟩
      simp at same⟩
  | n + 1, sorts, formulas, [] => ⟨fun impossible => impossible.elim, by
      rintro ⟨elements, same, -⟩
      simp at same⟩
  | n + 1, sorts, formulas, ⟨partSort, part⟩ :: parts => by
    constructor
    · rintro ⟨(sortIs : partSort = sorts 0), holds, rest⟩
      subst sortIs
      obtain ⟨elements, partsIs, restHolds⟩ :=
        (ssatAll_argumentsOf M env n (fun position => sorts position.succ) (fun position => formulas position.succ)
          parts).mp rest
      refine ⟨Fin.cons (α := fun position => M.Carrier (sorts position)) part elements, ?_, fun position => ?_⟩
      · rw [List.ofFn_succ, partsIs]
        rfl
      · refine Fin.cases ?_ (fun position' => ?_) position
        · exact holds
        · exact restHolds position'
    · rintro ⟨elements, partsIs, holds⟩
      rw [List.ofFn_succ, List.cons.injEq] at partsIs
      obtain ⟨headIs, partsIs⟩ := partsIs
      simp only [Sigma.mk.injEq] at headIs
      obtain ⟨sortIs, partIs⟩ := headIs
      subst sortIs
      have partEq : part = elements 0 := eq_of_heq partIs
      subst partEq
      exact ⟨rfl, holds 0, (ssatAll_argumentsOf M env n (fun position => sorts position.succ)
        (fun position => formulas position.succ) parts).mpr ⟨fun position => elements position.succ, partsIs,
          fun position => holds position.succ⟩⟩

/-! ## The classes of a sorted signature -/

variable {source : Signature.{0, v}} {Parallel : source.Srt → Prop} (names : source.Constructor → String)

/-- **The sorted structure of the classes of terms** of a sorted signature with designated parallel sorts: a class is
built by a constructor from the classes of its arguments, splits into two classes it is the cut of, and is empty when
it is the unit. -/
def classStructure : SortedStructure.{v} source.Srt where
  Carrier sort := Class source Parallel sort
  step _ _ _ := False
  built {sort} element name parts := ∃ (constructor : source.Constructor)
    (children : (position : Fin (source.arity constructor)) → Class source Parallel (source.input constructor position)),
    names constructor = name ∧
    (⟨sort, element⟩ : Σ sort', Class source Parallel sort') =
      ⟨source.output constructor, (Head.node (signature := source) (Parallel := Parallel) constructor children).class⟩ ∧
    parts = List.ofFn fun position => ⟨source.input constructor position, children position⟩
  split {sort} element kind first second := kind = .hashBag ∧ ∃ parallel : Parallel sort,
    element = classCut parallel first second
  empty {sort} element kind := kind = .hashBag ∧ ∃ parallel : Parallel sort, element = classOf (.zero parallel)
  single _ _ _ := False
  named _ _ := False
  inRelation _ _ := False

open Mettapedia.OSLF.Framework.SortedTypedInstruments in
/-- **The embedding of a structural formula**: constructors to constructor formers, the cut to the bag split, the unit
to the empty bag. -/
def embed {Γ : List source.Srt} : {sort : source.Srt} → StructuralObservations.Formula source Parallel sort →
    SFormula source.Srt Γ
  | _, .unit _ => .empty .hashBag
  | _, .cut _ first second => .split .hashBag (embed first) (embed second)
  | _, .node constructor arguments =>
    .built (names constructor) (argumentsOf _ (source.input constructor) fun position => embed (arguments position))

open Mettapedia.OSLF.Framework.SortedTypedInstruments in
/-- **The embedding is exact**: a structural formula holds of a class exactly when its embedding holds there, when
constructors have distinct names. -/
theorem holds_iff (injective : Function.Injective names) {Γ : List source.Srt}
    (env : Env (classStructure (Parallel := Parallel) names).Element Γ.length) :
    ∀ {sort : source.Srt} (formula : StructuralObservations.Formula source Parallel sort)
      (element : Class source Parallel sort),
      StructuralObservations.Holds formula element ↔
        (classStructure names).ssat env (embed names formula) ⟨sort, element⟩
  | _, .unit parallel, element =>
    ⟨fun same => ⟨rfl, parallel, same⟩, fun ⟨_, _, same⟩ => same⟩
  | sort, .cut parallel first second, element => by
    constructor
    · rintro ⟨left, right, whole, leftHolds, rightHolds⟩
      exact ⟨left, right, ⟨rfl, parallel, whole⟩, (holds_iff injective env first left).mp leftHolds,
        (holds_iff injective env second right).mp rightHolds⟩
    · rintro ⟨left, right, ⟨-, _, whole⟩, leftHolds, rightHolds⟩
      exact ⟨left, right, whole, (holds_iff injective env first left).mpr leftHolds,
        (holds_iff injective env second right).mpr rightHolds⟩
  | _, .node constructor arguments, element => by
    constructor
    · rintro ⟨children, whole, holds⟩
      refine ⟨List.ofFn fun position => ⟨source.input constructor position, children position⟩,
        ⟨constructor, children, rfl, by rw [whole], rfl⟩, ?_⟩
      exact (ssatAll_argumentsOf _ env _ _ _ _).mpr ⟨children, rfl,
        fun position => (holds_iff injective env (arguments position) (children position)).mp (holds position)⟩
    · rintro ⟨parts, ⟨constructor', children, sameName, whole, partsIs⟩, all⟩
      have sameConstructor : constructor = constructor' := (injective sameName).symm
      subst sameConstructor
      simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at whole
      obtain ⟨elements, partsIs', holds⟩ := (ssatAll_argumentsOf _ env _ _ _ _).mp all
      rw [partsIs] at partsIs'
      have sameFunctions := List.ofFn_injective partsIs'
      have sameChildren : children = elements := by
        funext position
        exact eq_of_heq (Sigma.mk.inj (congrFun sameFunctions position)).2
      subst sameChildren
      exact ⟨children, whole,
        fun position => (holds_iff injective env (arguments position) (children position)).mpr (holds position)⟩

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.ManySorted

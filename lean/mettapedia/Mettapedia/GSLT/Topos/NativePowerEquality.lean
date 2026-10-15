import Mettapedia.GSLT.Topos.NativePowerPredicates
import Mettapedia.GSLT.Topos.PresheafPredicateUniversalQuantifier
import Mettapedia.GSLT.Topos.PresheafPredicateHeyting

/-!
# Internal Leibniz equality from the native predicate object

All locally generalized predicates are quantified. The separating predicate
is the characteristic name of the actual diagonal, curried through the
function object; no primitive equality predicate is part of the syntax.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos.NativePowerEquality

open _root_.CategoryTheory
open NativePowerPredicates ConstructivePresheaf PresheafPredicateGenericTruth

universe u
variable {C : Type u} [Category.{u} C] (A : Cᵒᵖ ⥤ Type u)

def pairs : Cᵒᵖ ⥤ Type u := FunctorToTypes.prod A A

def tested : Cᵒᵖ ⥤ Type u := FunctorToTypes.prod (pairs A) (power A)

def forgetPredicate : tested A ⟶ pairs A where
  app _ := TypeCat.ofHom Prod.fst
  naturality := by intros; rfl

def leftEvaluation : tested A ⟶ product A where
  app _ := TypeCat.ofHom fun value => (value.1.1, value.2)
  naturality := by intros; rfl

def rightEvaluation : tested A ⟶ product A where
  app _ := TypeCat.ofHom fun value => (value.1.2, value.2)
  naturality := by intros; rfl

/-- Equality is specified separately by the actual presheaf diagonal. -/
def diagonal : Subfunctor (pairs A) where
  obj _ := {value | value.1 = value.2}
  map := by
    intro world future arrow value equal
    change A.map arrow value.1 = A.map arrow value.2
    exact congrArg (A.map arrow) equal

/-- The common internal Leibniz reading quantifies over actual local predicates. -/
noncomputable def leibniz : Subfunctor (pairs A) :=
  forallAlong (forgetPredicate A)
    (himpPointwise ((membership A).preimage (leftEvaluation A))
      ((membership A).preimage (rightEvaluation A)))

noncomputable def singleton : A ⟶ power.{u} (C := C) A :=
  curryFunction (F := A) (G := omegaFunctor.{u, u} (C := C)) (H := A)
    (chiOfSubfunctor.{u, u} (C := C) (pairs A) (diagonal A))

theorem singleton_membership (world : Cᵒᵖ) (parameter argument : A.obj world) :
    (argument, (singleton A).app world parameter) ∈ (membership A).obj world ↔
      argument = parameter := by
  erw [membership_iff]
  change (chiOfSubfunctor.{u, u} (C := C) (pairs A) (diagonal A)).app world
      (argument, A.map (𝟙 world) parameter) = (⊤ : Sieve world.unop) ↔ _
  rw [A.map_id_apply]
  exact (truth_iff_top _ _).symm.trans (by
    change (argument, parameter) ∈
      ((truthPredicate C).preimage (chiOfSubfunctor.{u, u} (C := C) (pairs A) (diagonal A))).obj world ↔ _
    rw [characteristic_classifies]
    rfl)

theorem diagonal_le_leibniz : diagonal A ≤ leibniz A := by
  intro world value same future restriction probe consistent target step holdsLeft
  have coordinates : probe.1.1 = probe.1.2 := by
    have pairEquality : probe.1 = (pairs A).map restriction value := consistent
    rw [pairEquality]
    change A.map restriction value.1 = A.map restriction value.2
    exact congrArg (A.map restriction) same
  change (((tested A).map step probe).1.2, ((tested A).map step probe).2) ∈
    (membership A).obj target
  change (A.map step probe.1.2, (power A).map step probe.2) ∈ _
  rw [← coordinates]
  exact holdsLeft

theorem leibniz_le_diagonal : leibniz A ≤ diagonal A := by
  intro world value equal
  let predicate := (singleton A).app world value.1
  have testedAt := equal world (𝟙 world) (value, predicate) (by
    change value = (pairs A).map (𝟙 world) value
    exact ((pairs A).map_id_apply world value).symm)
  have left : (value.1, predicate) ∈ (membership A).obj world :=
    (singleton_membership A world value.1 value.1).mpr rfl
  have right := testedAt world (𝟙 world) (by
    have identity := (tested A).map_id_apply world (show (tested A).obj world from (value, predicate))
    rw [identity]
    exact left)
  have identity := (tested A).map_id_apply world (show (tested A).obj world from (value, predicate))
  change (((tested A).map (𝟙 world) (value, predicate)).1.2,
    ((tested A).map (𝟙 world) (value, predicate)).2) ∈ (membership A).obj world at right
  rw [identity] at right
  exact ((singleton_membership A world value.1 value.2).mp right).symm

/-- General internal equality agrees exactly with actual equality of sections. -/
theorem leibniz_eq_diagonal : leibniz A = diagonal A :=
  le_antisymm (leibniz_le_diagonal A) (diagonal_le_leibniz A)

theorem leibniz_iff (world : Cᵒᵖ) (first second : A.obj world) :
    (first, second) ∈ (leibniz A).obj world ↔ first = second := by
  rw [leibniz_eq_diagonal]
  rfl

/-- Restriction preserves the generated internal equality. -/
theorem leibniz_restrict {world future : Cᵒᵖ} (arrow : world ⟶ future)
    (first second : A.obj world) (equal : (first, second) ∈ (leibniz A).obj world) :
    (A.map arrow first, A.map arrow second) ∈ (leibniz A).obj future :=
  (leibniz A).map arrow equal

end Mettapedia.GSLT.Topos.NativePowerEquality

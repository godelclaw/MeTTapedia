import Mettapedia.OSLF.Syntax.RhoScopedParallelInventory
import Mettapedia.GSLT.Logic.BagRelativePushout
import Mettapedia.GSLT.Logic.RelativePushoutFullComparison

/-!
# Relative pushouts of actual scoped rho parallel contexts

A context contains an original rho process class and acts by parallel
composition. Its complete typed inventory gives a full and faithful category
comparison, including every competing apex, leg and mediator. Relative
pushouts and their exact minimality criterion therefore hold on the original
equation quotient, independently of a chosen syntax representative.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.RhoScopedParallelContexts

open _root_.CategoryTheory RhoSchema RhoQuotationClassFibres RhoScopedParallelInventory
open Mettapedia.GSLT.RelativePushout Mettapedia.GSLT.RedexRelativeCongruence

local instance (context : Ctx sig) : DecidableEq (Prime context) := Classical.decEq _

/-- Original process classes, used as the programs surrounding a parallel hole. -/
structure Surround (context : Ctx sig) where
  process : Process context

@[ext] theorem Surround.ext {context : Ctx sig} {first second : Surround context}
    (same : first.process = second.process) : first = second := by
  cases first
  cases second
  cases same
  rfl

instance (context : Ctx sig) : CommMonoid (Surround context) where
  one := ⟨zero context⟩
  mul first second := ⟨join first.process second.process⟩
  one_mul first := Surround.ext (join_zero_left _)
  mul_one first := Surround.ext (join_zero_right _)
  mul_assoc first second third := by
    apply Surround.ext
    apply read_injective context
    exact (read_join _ _).trans ((congrArg (· + read third.process) (read_join _ _)).trans
      ((add_assoc _ _ _).trans ((congrArg (read first.process + ·) (read_join _ _).symm).trans
        (read_join _ _).symm)))
  mul_comm first second := Surround.ext (join_commutes _ _)

abbrev ContextCategory (context : Ctx sig) := SingleObj (Surround context)

abbrev interface (context : Ctx sig) : ContextCategory context := SingleObj.star _

def arrow {context : Ctx sig} (process : Process context) : interface context ⟶ interface context :=
  ⟨process⟩

theorem arrow_injective {context : Ctx sig} : Function.Injective (arrow (context := context)) :=
  fun _ _ same => congrArg Surround.process same

theorem arrow_comp {context : Ctx sig} (first second : Process context) :
    arrow first ≫ arrow second = arrow (join first second) :=
  Surround.ext (join_commutes second first)

theorem arrow_zero (context : Ctx sig) : arrow (zero context) = 𝟙 (interface context) := rfl

def inventoryFunctor (context : Ctx sig) :
    ContextCategory context ⥤ SingleObj (Mettapedia.GSLT.BagRelativePushout.Bag (Prime context)) where
  obj _ := Mettapedia.GSLT.BagRelativePushout.Obj _
  map supplied := Mettapedia.GSLT.BagRelativePushout.bag (read supplied.process)
  map_id _ := by
    change Mettapedia.GSLT.BagRelativePushout.bag (read (zero context)) = _
    rw [read_zero]
    rfl
  map_comp first second := by
    rw [Mettapedia.GSLT.BagRelativePushout.bag_comp]
    apply congrArg Mettapedia.GSLT.BagRelativePushout.bag
    exact (read_join second.process first.process).trans (add_comm _ _)

instance inventoryFunctor_faithful (context : Ctx sig) : (inventoryFunctor context).Faithful where
  map_injective := by
    intro first second before after same
    exact Surround.ext (read_injective context
      (Mettapedia.GSLT.BagRelativePushout.bag_injective same))

instance inventoryFunctor_full (context : Ctx sig) : (inventoryFunctor context).Full where
  map_surjective := by
    intro first second supplied
    obtain ⟨inventory, same⟩ := Mettapedia.GSLT.BagRelativePushout.bag_surjective supplied
    exact ⟨⟨write inventory⟩,
      (congrArg Mettapedia.GSLT.BagRelativePushout.bag (read_write inventory)).trans same.symm⟩

theorem inventoryFunctor_objects (context : Ctx sig) :
    Function.Surjective (inventoryFunctor context).obj := by
  intro object
  cases object
  exact ⟨interface context, rfl⟩

theorem idemPushout_iff {context : Ctx sig} {W X Y Z : ContextCategory context}
    (first : W ⟶ X) (second : W ⟶ Y) (left : X ⟶ Z) (right : Y ⟶ Z)
    (square : first ≫ left = second ≫ right) :
    IsIdemPushout first second left right square ↔
      read left.process ∩ read right.process = 0 := by
  let F := inventoryFunctor context
  have mappedSquare : F.map first ≫ F.map left = F.map second ≫ F.map right := by
    rw [← F.map_comp, square, F.map_comp]
  have comparison : IsIdemPushout first second left right square ↔
      IsIdemPushout (F.map first) (F.map second) (F.map left) (F.map right) mappedSquare :=
    ⟨preserves_idemPushout F (inventoryFunctor_objects context) square,
      reflects_idemPushout F square⟩
  exact comparison.trans (Mettapedia.GSLT.BagRelativePushout.isIdemPushout_bag_iff
    (read first.process) (read second.process) (read left.process) (read right.process) mappedSquare)

/-- Every redex bound is covered, including all original equation-class contexts. -/
theorem hasRelativePushouts {context : Ctx sig}
    (first second : interface context ⟶ interface context) : HasRelativePushouts first second := by
  exact reflects_hasRelativePushouts (inventoryFunctor context) (inventoryFunctor_objects context)
    (Mettapedia.GSLT.BagRelativePushout.hasRelativePushouts
      (read first.process) (read second.process))

/-- The source-class operational equivalence is a congruence for every parallel context. -/
theorem bisimilar_join {context : Ctx sig}
    (rules : ReactionRule (interface context) → Prop) {first second : Process context}
    (related : IPOBisimilar rules (arrow first) (arrow second)) (surrounding : Process context) :
    IPOBisimilar rules (arrow (join first surrounding)) (arrow (join second surrounding)) := by
  rw [← arrow_comp, ← arrow_comp]
  exact ipoBisimilar_comp (fun _ agent rule _ => hasRelativePushouts agent rule.redex)
    related (arrow surrounding)

end Mettapedia.OSLF.Binding.RhoScopedParallelContexts

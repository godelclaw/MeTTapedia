import Mettapedia.OSLF.NativeTypes.Semantics.Modal
import Mettapedia.OSLF.NativeTypes.Modal.Possibility

open Mettapedia.OSLF.Framework

/-!
# Native empty-context possibility outputs

The canonical diamond is compared to actual occurrence receipts. Its
dependent output retains the primitive declaration, matcher trace, ordered
premises, equation administration and target certificate. A possibility
witness is one occurrence; it is not a complete universally quantified rely
implementation of a selected contextual former.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Modal

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL
open GeneralExecutionAdmission GeneralOccurrenceSemantics
open Mettapedia.OSLF.NativeTypes.Modal.Equations Mettapedia.OSLF.NativeTypes.Modal.Possibility
open GSLTTypeSynthesis

def possibilityPredicate (plan : Plan) (bound : List TypeExpr) (carrier : TypeExpr)
    (postcondition : EquationPredicate (gslt plan bound carrier)) :
    EquationPredicate (gslt plan bound carrier) :=
  semanticDiamond (gslt plan bound carrier) postcondition

abbrev PossibilityFamily (plan : Plan) (bound : List TypeExpr) (carrier : TypeExpr)
    (postcondition : EquationPredicate (gslt plan bound carrier)) (source : Pattern) :=
  GeneralOccurrenceNativeReceipts.NativeFamily plan bound carrier
    (fun target => PLift (postcondition target)) source

/-- The continuation's class invariance is earned from the supplied native
predicate, not from an additional operational completeness assumption. -/
theorem native_postcondition_invariant (plan : Plan) (bound : List TypeExpr) (carrier : TypeExpr)
    (postcondition : EquationPredicate (gslt plan bound carrier)) :
    SupportInvariant plan bound carrier (fun target => PLift (postcondition target)) := by
  intro source target equivalent
  constructor
  · rintro ⟨certificate⟩
    exact ⟨⟨(postcondition.property equivalent).mp certificate.down⟩⟩
  · rintro ⟨certificate⟩
    exact ⟨⟨(postcondition.property equivalent).mpr certificate.down⟩⟩

theorem possibility_family_iff_receipt_possibility {plan : Plan} {bound : List TypeExpr}
    {carrier : TypeExpr} {postcondition : EquationPredicate (gslt plan bound carrier)} {source : Pattern} :
    Nonempty (PossibilityFamily plan bound carrier postcondition source) ↔
      Mettapedia.OSLF.NativeTypes.Modal.Rules.Possibility plan bound carrier (fun target => PLift (postcondition target)) source := by
  constructor
  · rintro ⟨⟨receipt, certificate⟩⟩
    exact ⟨receipt.val, receipt.property, ⟨certificate⟩⟩
  · rintro ⟨receipt, valid, ⟨certificate⟩⟩
    exact ⟨⟨⟨receipt, valid⟩, certificate⟩⟩

/-- The exact native diamond law follows from the independent saturated
GSLT step relation and actual receipt conversion paths. -/
theorem possibility_family_support_iff {plan : Plan} {bound : List TypeExpr}
    {carrier : TypeExpr} {postcondition : EquationPredicate (gslt plan bound carrier)} {source : Pattern} :
    Nonempty (PossibilityFamily plan bound carrier postcondition source) ↔
      possibilityPredicate plan bound carrier postcondition source := by
  rw [possibility_family_iff_receipt_possibility,
    possibility_iff_existential_step (native_postcondition_invariant plan bound carrier postcondition)]
  have comparison := gsltDiamond_spec (gslt plan bound carrier) postcondition.val source
  constructor
  · rintro ⟨target, step, ⟨certificate⟩⟩
    exact comparison.mpr ⟨target, step, certificate.down⟩
  · intro member
    obtain ⟨target, step, certificate⟩ := comparison.mp member
    exact ⟨target, step, ⟨⟨certificate⟩⟩⟩

def possibilityNativeType (plan : Plan) (bound : List TypeExpr) (carrier : TypeExpr)
    (postcondition : EquationPredicate (gslt plan bound carrier)) : GSLTNativeType (gslt plan bound carrier) :=
  ⟨(), possibilityPredicate plan bound carrier postcondition⟩

theorem possibility_native_satisfaction_iff_family {plan : Plan} {bound : List TypeExpr}
    {carrier : TypeExpr} {postcondition : EquationPredicate (gslt plan bound carrier)} (source : Pattern) :
    (gsltOSLF (gslt plan bound carrier)).satisfies (S := ()) source
      (possibilityNativeType plan bound carrier postcondition).pred ↔
      Nonempty (PossibilityFamily plan bound carrier postcondition source) :=
  possibility_family_support_iff.symm

theorem possibility_family_equation_iff {plan : Plan} {bound : List TypeExpr}
    {carrier : TypeExpr} {postcondition : EquationPredicate (gslt plan bound carrier)} {source target : Pattern}
    (equivalent : (gslt plan bound carrier).Equiv source target) :
    Nonempty (PossibilityFamily plan bound carrier postcondition source) ↔
      Nonempty (PossibilityFamily plan bound carrier postcondition target) := by
  rw [possibility_family_support_iff, possibility_family_support_iff]
  exact (possibilityPredicate plan bound carrier postcondition).property equivalent

namespace PossibilityFamily

def introduce {plan : Plan} {bound : List TypeExpr} {carrier : TypeExpr}
    {postcondition : EquationPredicate (gslt plan bound carrier)} {source : Pattern}
    (receipt : GeneralOccurrenceNativeReceipts.ReceiptFamily plan bound carrier source)
    (certificate : postcondition receipt.val.target) :
    PossibilityFamily plan bound carrier postcondition source :=
  ⟨receipt, ⟨certificate⟩⟩

/-- Native elimination returns the actual primitive result and its native
postcondition, retaining the complete occurrence receipt in the family. -/
def eliminate {plan : Plan} {bound : List TypeExpr} {carrier : TypeExpr}
    {postcondition : EquationPredicate (gslt plan bound carrier)} {source : Pattern}
    (family : PossibilityFamily plan bound carrier postcondition source) :
    Σ target : Pattern, PLift (postcondition target) :=
  ⟨family.1.val.target, family.2⟩

theorem elimination_contract {plan : Plan} {bound : List TypeExpr} {carrier : TypeExpr}
    {postcondition : EquationPredicate (gslt plan bound carrier)} {source : Pattern}
    (family : PossibilityFamily plan bound carrier postcondition source) :
    (gslt plan bound carrier).Step source family.eliminate.1 ∧ postcondition family.eliminate.1 :=
  ⟨Receipt.semantic_step plan bound carrier family.1.property, family.2.down⟩

def rebase {plan : Plan} {bound : List TypeExpr} {carrier : TypeExpr}
    {postcondition : EquationPredicate (gslt plan bound carrier)} {source target : Pattern}
    (administration : List Conversion)
    (path : ConversionPath plan bound carrier target source administration)
    (family : PossibilityFamily plan bound carrier postcondition source) :
    PossibilityFamily plan bound carrier postcondition target :=
  ⟨⟨Mettapedia.OSLF.NativeTypes.Modal.Equations.rebase administration family.1.val,
    rebase_valid path family.1.property⟩, family.2⟩

theorem rebase_preserves_origin {plan : Plan} {bound : List TypeExpr} {carrier : TypeExpr}
    {postcondition : EquationPredicate (gslt plan bound carrier)} {source target : Pattern}
    (administration : List Conversion)
    (path : ConversionPath plan bound carrier target source administration)
    (family : PossibilityFamily plan bound carrier postcondition source) :
    (family.rebase administration path).1.val.firing = family.1.val.firing ∧
      (family.rebase administration path).eliminate.1 = family.eliminate.1 ∧
      (family.rebase administration path).1.val.conversions = administration ++ family.1.val.conversions :=
  ⟨rfl, rfl, rfl⟩

theorem rebase_identity {plan : Plan} {bound : List TypeExpr} {carrier : TypeExpr}
    {postcondition : EquationPredicate (gslt plan bound carrier)} {source : Pattern}
    (family : PossibilityFamily plan bound carrier postcondition source) :
    family.rebase [] (.nil source) = family := by
  cases family
  rfl

theorem rebase_composition {plan : Plan} {bound : List TypeExpr} {carrier : TypeExpr}
    {postcondition : EquationPredicate (gslt plan bound carrier)} {first second third : Pattern}
    (front middle : List Conversion)
    (firstPath : ConversionPath plan bound carrier second first front)
    (secondPath : ConversionPath plan bound carrier third second middle)
    (family : PossibilityFamily plan bound carrier postcondition first) :
    (family.rebase front firstPath).rebase middle secondPath =
      family.rebase (middle ++ front) (ConversionPath.append plan bound carrier secondPath firstPath) := by
  have receipts : ((family.rebase front firstPath).rebase middle secondPath).1.val =
      (family.rebase (middle ++ front) (ConversionPath.append plan bound carrier secondPath firstPath)).1.val := by
    change {family.1.val with conversions := middle ++ (front ++ family.1.val.conversions)} =
      {family.1.val with conversions := (middle ++ front) ++ family.1.val.conversions}
    exact congrArg (fun conversions => {family.1.val with conversions := conversions})
      (List.append_assoc middle front family.1.val.conversions).symm
  exact Sigma.ext (Subtype.ext receipts) HEq.rfl

end PossibilityFamily

end Mettapedia.OSLF.NativeTypes.Semantics.Modal

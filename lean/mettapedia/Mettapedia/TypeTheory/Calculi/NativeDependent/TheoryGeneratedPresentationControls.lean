import Mettapedia.TypeTheory.Calculi.NativeDependent.TheoryGeneratedPresentation
import Mettapedia.TypeTheory.Calculi.NativeDependent.RepresentableIndexedControls

/-!
# Conservation, dependent inhabitants and authored-origin controls

The controls use the complete equation-extended context quotient and its
actual extended-tree section readout. Original nonidentity arrows remain
distinct, one indexed family has varying inhabited and empty fibres, and
supplied bounded positions remain retained. A false independent equation is
rejected; duplicated valid equation occurrences retain distinct rule trees.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.TheoryGeneratedPresentation.Controls

open _root_.CategoryTheory Opposite
open RepresentableIndexedDeclarations
open TheoryRepresentables
open TheoryEquations

noncomputable section


/-- This source has objects in Type 1 and arrows in Type 0. -/
def independentTheory : Mettapedia.GSLT.Core.LambdaTheory.{1, 0} :=
  Mettapedia.GSLT.Core.LambdaTheory.ofCategory Type

def literalSuccessor : (Nat : independentTheory.Obj) ⟶ Nat := ↾Nat.succ

theorem independently_sized_original_arrows_are_conserved :
    (TheoryGeneratedPresentation.original independentTheory).map literalSuccessor ≠
      (TheoryGeneratedPresentation.original independentTheory).map (𝟙 Nat) := by
  intro same
  have arrows := (TheoryGeneratedPresentation.original_equation_iff
    independentTheory literalSuccessor (𝟙 Nat)).mp same
  have values := congrArg (fun arrow : (Nat : independentTheory.Obj) ⟶ Nat => arrow 0) arrows
  exact Nat.one_ne_zero values

abbrev Base := RepresentableIndexedDeclarations.Controls.Base
abbrev naturalObject := RepresentableIndexedDeclarations.Controls.naturalObject
abbrev unitObject := RepresentableIndexedDeclarations.Controls.unitObject
abbrev boundedIndex := RepresentableIndexedDeclarations.Controls.indexed

abbrev successor := RepresentableIndexedDeclarations.Controls.successor

def doubling : naturalObject ⟶ naturalObject := ⟨↾fun n => n * 2⟩

theorem actual_composite_readout (n : Nat) :
    ((objectName naturalObject).app (op unitObject)
      ((quotientReadout (originalFunctor.map (successor ≫ doubling))).app (op unitObject)
        ((objectNameInverse naturalObject).app (op unitObject)
          (RepresentableIndexedDeclarations.Controls.point n)))).down PUnit.unit = (n + 1) * 2 := by
  rw [generalized_original_readout]
  rfl

theorem successor_is_nonidentity : successor ≠ 𝟙 naturalObject := by
  intro same
  have pointRead := congrArg (fun arrow : naturalObject ⟶ naturalObject => arrow.down 0) same
  exact Nat.one_ne_zero pointRead

theorem actual_generated_arrows_remain_distinct :
    originalFunctor.map successor ≠ originalFunctor.map (𝟙 naturalObject) :=
  fun same => successor_is_nonidentity ((TheoryRepresentables.original_equation_iff _ _).mp same)

def wrongEquation : Declaration (symbols Base) :=
  .substitution (objectContext naturalObject) (objectContext naturalObject)
    (originalSubstitution successor) (originalSubstitution (𝟙 naturalObject))

theorem independently_declared_wrong_equation_is_rejected :
    ¬ wrongEquation.NativeAdmitted (model Base) := by
  intro admitted
  have compare := admitted (objectScope naturalObject) (objectScope naturalObject)
    (object_context_read naturalObject) (object_context_read naturalObject)
  change (model Base).evaluateSubstitution _ _ (originalSubstitution successor) =
    (model Base).evaluateSubstitution _ _ (originalSubstitution (𝟙 naturalObject)) at compare
  rw [original_substitution_read, original_substitution_read] at compare
  exact successor_is_nonidentity (RepresentableDeclarations.originalPresheafArrow_injective
    (Option.some.inj compare))

theorem no_false_equation_after_full_native_closure :
    ¬ TheoryEquations.Contextual.Holds (theory Base)
      (.substitutionEq (objectContext naturalObject) (objectContext naturalObject)
        (originalSubstitution successor) (originalSubstitution (𝟙 naturalObject))) := by
  intro equation
  exact actual_generated_arrows_remain_distinct
    ((TheoryEquations.Contextual.quotientProjection_map_eq_iff _ _).mpr equation)

theorem complete_retained_bounded_section (n : Nat) (position : Fin (n + 1)) :
    ((retainedForgetSection boundedIndex).val
      ⟨op unitObject, ⟨RepresentableIndexedDeclarations.Controls.argument n,
        RepresentableIndexedDeclarations.Controls.value n position⟩⟩).down PUnit.unit = ⟨n, position⟩ := by
  rw [retained_forget_readout]
  rfl

theorem equal_index_does_not_erase_positions :
    (retainedForgetSection boundedIndex).val
      ⟨op unitObject, ⟨RepresentableIndexedDeclarations.Controls.argument 3,
        RepresentableIndexedDeclarations.Controls.value 3 ⟨1, by decide⟩⟩⟩ ≠
    (retainedForgetSection boundedIndex).val
      ⟨op unitObject, ⟨RepresentableIndexedDeclarations.Controls.argument 3,
        RepresentableIndexedDeclarations.Controls.value 3 ⟨2, by decide⟩⟩⟩ := by
  intro same
  have pairs := congrArg (fun arrow => arrow.down PUnit.unit) same
  have values := (complete_retained_bounded_section 3 ⟨1, by decide⟩).symm.trans
    (pairs.trans (complete_retained_bounded_section 3 ⟨2, by decide⟩))
  have read := congrArg (fun value : Σ n : Nat, Fin (n + 1) => value.2.val) values
  contradiction

theorem generated_indexed_family_is_genuinely_dependent :
    (indexedFamilyReadout RepresentableIndexedDeclarations.Controls.successorIndexed).decoded.obj
        ⟨op unitObject, RepresentableIndexedDeclarations.Controls.argument 0⟩ ≠
      (indexedFamilyReadout RepresentableIndexedDeclarations.Controls.successorIndexed).decoded.obj
        ⟨op unitObject, RepresentableIndexedDeclarations.Controls.argument 12⟩ := by
  rw [indexed_family_readout]
  exact RepresentableIndexedDeclarations.Controls.the_same_native_indexed_type_has_distinct_fibres

def duplicatedEquations : Presentation (symbols Base) where
  Origin := ULift.{1} Bool
  declaration _ := declaration (.identity naturalObject)

def duplicatePremises (origin : Bool) :
    (position : Fin (duplicatedEquations.declaration ⟨origin⟩).premises.length) →
      TheoryEquations.Derivation (signature Base) duplicatedEquations
        ((duplicatedEquations.declaration ⟨origin⟩).premises.get position) := by
  intro position
  cases position using Fin.cases with
  | zero => exact TheoryEquations.original (firstPremise (.identity naturalObject))
  | succ position =>
      have bound : position.val < 1 := position.isLt
      have same : position = ⟨0, by decide⟩ := Fin.ext (by
        change position.val = 0
        omega)
      cases same
      exact TheoryEquations.original (secondPremise (.identity naturalObject))

def duplicateTree (origin : Bool) :=
  TheoryEquations.declare (D := signature Base) (equations := duplicatedEquations) ⟨origin⟩
    (duplicatePremises origin)

theorem independent_origins_retain_distinct_trees : duplicateTree false ≠ duplicateTree true := by
  intro same
  have origins := congrArg TheoryEquations.rootOrigin same
  have different := congrArg (fun origin => origin.map ULift.down) origins
  change some false = some true at different
  contradiction

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.TheoryGeneratedPresentation.Controls

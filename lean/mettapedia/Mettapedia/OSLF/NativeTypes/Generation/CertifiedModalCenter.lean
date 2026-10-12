import Mettapedia.OSLF.NativeTypes.Generation.CertifiedCenter
import Mettapedia.OSLF.NativeTypes.SortProfiles.Source.ModalCodes

open Mettapedia.OSLF.Framework

/-!
# Formation preservation for generated modal-code coordinates

The relied-on constructor expressions and every assignment-indexed
continuation may be transported through the selected equation or directed
code laws. Their valuations and the computed modal slots are retained.
Membership in the joint center then preserves the modal kind judgment.

These comparisons concern code formation. They do not assert equality of
arbitrary set-valued meanings or add equations between distinct modal heads.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.CertifiedCenter

open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.OSLF.NativeTypes.Generation
open Mettapedia.OSLF.NativeTypes.SortProfiles.Derived (CubeVertex)
open Mettapedia.OSLF.NativeTypes.SortProfiles.Source
open Mettapedia.OSLF.NativeTypes.Modal.Rules (Schema)
open ModalHypercube (HSort)

structure ModalEquationComparison (generated : Generated) (schema : Schema generated.plan)
    (first second : ModalExpression generated schema) : Prop where
  relies : ∀ name, first.relyValuations name = second.relyValuations name ∧
    Convertibility generated.vertex.2 (first.relyValuations name)
      (selectedEquations generated).system (first.relyExpressions name) (second.relyExpressions name)
  continuations : ∀ assignment,
    first.continuationValuations assignment = second.continuationValuations assignment ∧
    Convertibility generated.vertex.2 (first.continuationValuations assignment)
      (selectedEquations generated).system
      (first.continuationExpressions assignment) (second.continuationExpressions assignment)

structure ModalDirectedComparison (generated : Generated) (schema : Schema generated.plan)
    (first second : ModalExpression generated schema) : Prop where
  relies : ∀ name, first.relyValuations name = second.relyValuations name ∧
    Relation.ReflTransGen
      (NativeLawStep generated.vertex.2 (selectedDirectedLaws generated).system (first.relyValuations name))
      (first.relyExpressions name) (second.relyExpressions name)
  continuations : ∀ assignment,
    first.continuationValuations assignment = second.continuationValuations assignment ∧
    Relation.ReflTransGen (NativeLawStep generated.vertex.2 (selectedDirectedLaws generated).system
      (first.continuationValuations assignment))
      (first.continuationExpressions assignment) (second.continuationExpressions assignment)

theorem member_modal_equation_formation {snapshot : Snapshot} {fragment : LanguageFragment}
    {logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment}
    {vertex : CubeVertex (selectedSnapshot snapshot fragment).language}
    (member : vertex ∈ center snapshot fragment logic)
    (schema : Schema (generate snapshot fragment logic vertex).plan)
    (first second : ModalExpression (generate snapshot fragment logic vertex) schema)
    (comparison : ModalEquationComparison (generate snapshot fragment logic vertex) schema first second)
    (sort : HSort) :
    ModalKinded (generate snapshot fragment logic vertex) schema first sort ↔
      ModalKinded (generate snapshot fragment logic vertex) schema second sort := by
  constructor
  · intro formed
    cases formed with
    | constructor parameters computed expression relies continuations =>
        refine .constructor parameters computed second ?_ ?_
        · intro name
          obtain ⟨valuation, equivalent⟩ := comparison.relies name
          have result := (member_native_equation_universe member (first.relyValuations name)
            (first.relyExpressions name) (second.relyExpressions name) equivalent (parameters.inputs name)).mp
            (relies name)
          rwa [valuation] at result
        · intro assignment
          obtain ⟨valuation, equivalent⟩ := comparison.continuations assignment
          have result := (member_native_equation_universe member (first.continuationValuations assignment)
            (first.continuationExpressions assignment) (second.continuationExpressions assignment)
            equivalent parameters.output).mp (continuations assignment)
          rwa [valuation] at result
  · intro formed
    cases formed with
    | constructor parameters computed expression relies continuations =>
        refine .constructor parameters computed first ?_ ?_
        · intro name
          obtain ⟨valuation, equivalent⟩ := comparison.relies name
          apply (member_native_equation_universe member (first.relyValuations name)
            (first.relyExpressions name) (second.relyExpressions name) equivalent (parameters.inputs name)).mpr
          rw [valuation]
          exact relies name
        · intro assignment
          obtain ⟨valuation, equivalent⟩ := comparison.continuations assignment
          apply (member_native_equation_universe member (first.continuationValuations assignment)
            (first.continuationExpressions assignment) (second.continuationExpressions assignment)
            equivalent parameters.output).mpr
          rw [valuation]
          exact continuations assignment

theorem member_modal_directed_formation {snapshot : Snapshot} {fragment : LanguageFragment}
    {logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment}
    {vertex : CubeVertex (selectedSnapshot snapshot fragment).language}
    (member : vertex ∈ center snapshot fragment logic)
    (schema : Schema (generate snapshot fragment logic vertex).plan)
    (first second : ModalExpression (generate snapshot fragment logic vertex) schema)
    (comparison : ModalDirectedComparison (generate snapshot fragment logic vertex) schema first second)
    (sort : HSort) :
    ModalKinded (generate snapshot fragment logic vertex) schema first sort ↔
      ModalKinded (generate snapshot fragment logic vertex) schema second sort := by
  constructor
  · intro formed
    cases formed with
    | constructor parameters computed expression relies continuations =>
        refine .constructor parameters computed second ?_ ?_
        · intro name
          obtain ⟨valuation, path⟩ := comparison.relies name
          have result := (member_native_directed_path member (first.relyValuations name)
            (first.relyExpressions name) (second.relyExpressions name) path (parameters.inputs name)).mp
            (relies name)
          rwa [valuation] at result
        · intro assignment
          obtain ⟨valuation, path⟩ := comparison.continuations assignment
          have result := (member_native_directed_path member (first.continuationValuations assignment)
            (first.continuationExpressions assignment) (second.continuationExpressions assignment)
            path parameters.output).mp (continuations assignment)
          rwa [valuation] at result
  · intro formed
    cases formed with
    | constructor parameters computed expression relies continuations =>
        refine .constructor parameters computed first ?_ ?_
        · intro name
          obtain ⟨valuation, path⟩ := comparison.relies name
          apply (member_native_directed_path member (first.relyValuations name)
            (first.relyExpressions name) (second.relyExpressions name) path (parameters.inputs name)).mpr
          rw [valuation]
          exact relies name
        · intro assignment
          obtain ⟨valuation, path⟩ := comparison.continuations assignment
          apply (member_native_directed_path member (first.continuationValuations assignment)
            (first.continuationExpressions assignment) (second.continuationExpressions assignment)
            path parameters.output).mpr
          rw [valuation]
          exact continuations assignment

theorem member_modal_equation_universe {snapshot : Snapshot} {fragment : LanguageFragment}
    {logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment}
    {vertex : CubeVertex (selectedSnapshot snapshot fragment).language}
    (member : vertex ∈ center snapshot fragment logic)
    (schema : Schema (generate snapshot fragment logic vertex).plan)
    (first second : ModalExpression (generate snapshot fragment logic vertex) schema)
    (comparison : ModalEquationComparison (generate snapshot fragment logic vertex) schema first second)
    (sort : HSort) :
    first ∈ ModalUniverse (generate snapshot fragment logic vertex) schema sort ↔
      second ∈ ModalUniverse (generate snapshot fragment logic vertex) schema sort :=
  member_modal_equation_formation member schema first second comparison sort

theorem member_modal_directed_universe {snapshot : Snapshot} {fragment : LanguageFragment}
    {logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment}
    {vertex : CubeVertex (selectedSnapshot snapshot fragment).language}
    (member : vertex ∈ center snapshot fragment logic)
    (schema : Schema (generate snapshot fragment logic vertex).plan)
    (first second : ModalExpression (generate snapshot fragment logic vertex) schema)
    (comparison : ModalDirectedComparison (generate snapshot fragment logic vertex) schema first second)
    (sort : HSort) :
    first ∈ ModalUniverse (generate snapshot fragment logic vertex) schema sort ↔
      second ∈ ModalUniverse (generate snapshot fragment logic vertex) schema sort :=
  member_modal_directed_formation member schema first second comparison sort

end Mettapedia.OSLF.NativeTypes.Generation.CertifiedCenter

import Mettapedia.TypeTheory.NaturalVectorTransport
import Mettapedia.TypeTheory.NaturalRepresentations

/-!
# Dependent recursion for material and surreal natural representations

The representation comparisons here are the isomorphisms obtained from
initiality in `NaturalRepresentations`. Dependent motives and vector fibres
transport across them with propositional computation equations. This does
not identify material ordinals and surreals definitionally, select executable
decoders, or grant new computation rules to a dependent object language.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.NaturalDependentRepresentations

universe u v w

open NaturalAlgebra NaturalRepresentations NaturalDependentTransport
open IndexedPolynomial

/-- The universal comparison preserves dependent recursion for every family
on the natural-surreal substructure, including its branch data. -/
theorem material_surreal_dependent_eliminate
    (family : SurrealNatural → Sort v) (atZero : family surrealAlgebra.zero)
    (atSuccessor : ∀ value, family value → family (surrealAlgebra.succ value))
    (value : MaterialNatural.{u}) :
    algebraEliminate natMaterialIso
      (fun value => family (materialSurrealIso.toEquiv value))
      (materialSurrealIso.map_zero.symm ▸ atZero)
      (fun value result => (materialSurrealIso.map_succ value).symm ▸
        atSuccessor (materialSurrealIso.toEquiv value) result) value =
    algebraEliminate natSurrealIso family atZero atSuccessor
      (materialSurrealIso.toEquiv value) := by
  have naturality := algebraEliminate_iso natMaterialIso materialSurrealIso
    family atZero atSuccessor value
  simpa only [comparison_triangle] using naturality

/-- The comparison changes the length representation and retains the vector. -/
noncomputable def materialSurrealVectors (Element : Type v) :
    NaturalVectorTransport.Total natMaterialIso.toEquiv Element ≃
      NaturalVectorTransport.Total natSurrealIso.toEquiv Element :=
  NaturalVectorTransport.changeRepresentation natMaterialIso.toEquiv natSurrealIso.toEquiv

theorem materialSurrealVectors_length (Element : Type v)
    (vector : NaturalVectorTransport.Total natMaterialIso.{u}.toEquiv Element) :
    (materialSurrealVectors Element vector).1 = materialSurrealIso.toEquiv vector.1 := by
  rw [materialSurrealVectors, NaturalVectorTransport.changeRepresentation_length]
  have triangle := congrArg
    (fun comparison : Iso natAlgebra surrealAlgebra =>
      comparison.toEquiv (natMaterialIso.toEquiv.symm vector.1))
    comparison_triangle.{u}
  change materialSurrealIso.toEquiv
    (natMaterialIso.toEquiv (natMaterialIso.toEquiv.symm vector.1)) =
      natSurrealIso.toEquiv (natMaterialIso.toEquiv.symm vector.1) at triangle
  simpa only [Equiv.apply_symm_apply] using triangle.symm

theorem materialSurrealVectors_preserves_elements (Element : Type v)
    (vector : NaturalVectorTransport.Total natMaterialIso.{u}.toEquiv Element) :
    NaturalVectorTransport.erase natSurrealIso.toEquiv (materialSurrealVectors Element vector) =
      NaturalVectorTransport.erase natMaterialIso.toEquiv vector :=
  NaturalVectorTransport.erase_changeRepresentation _ _ _

namespace Controls

noncomputable def materialTwo :
    NaturalVectorTransport.Total natMaterialIso.{0}.toEquiv Nat :=
  NaturalVectorTransport.cons _ 7
    (NaturalVectorTransport.cons _ 7 (NaturalVectorTransport.nil _))

theorem materialTwo_length :
    materialTwo.1 = materialAlgebra.succ (materialAlgebra.succ materialAlgebra.zero) := by
  simp [materialTwo]

theorem materialTwo_keeps_both_elements :
    NaturalVectorTransport.erase natMaterialIso.toEquiv materialTwo =
      ListExample.cons 7 (ListExample.cons 7 ListExample.nil) := by
  simp [materialTwo]

theorem surrealTwo_length :
    (materialSurrealVectors Nat materialTwo).1 =
      surrealAlgebra.succ (surrealAlgebra.succ surrealAlgebra.zero) := by
  rw [materialSurrealVectors_length, materialTwo_length,
    materialSurrealIso.map_succ, materialSurrealIso.map_succ, materialSurrealIso.map_zero]

theorem surrealTwo_keeps_both_elements :
    NaturalVectorTransport.erase natSurrealIso.toEquiv (materialSurrealVectors Nat materialTwo) =
      ListExample.cons 7 (ListExample.cons 7 ListExample.nil) := by
  rw [materialSurrealVectors_preserves_elements]
  exact materialTwo_keeps_both_elements

/-- A length-two material vector cannot be confused with a nil vector. -/
theorem materialTwo_not_nil : materialTwo ≠ NaturalVectorTransport.nil natMaterialIso.toEquiv := by
  intro same
  have lengths := congrArg Sigma.fst same
  rw [materialTwo_length, NaturalVectorTransport.nil_length] at lengths
  have decoded := congrArg natMaterialIso.toEquiv.symm lengths
  change natMaterialIso.symm.toEquiv
    (materialAlgebra.succ (materialAlgebra.succ materialAlgebra.zero)) =
      natMaterialIso.symm.toEquiv materialAlgebra.zero at decoded
  rw [natMaterialIso.symm.map_succ, natMaterialIso.symm.map_succ,
    natMaterialIso.symm.map_zero] at decoded
  contradiction

end Controls

end Mettapedia.TypeTheory.NaturalDependentRepresentations

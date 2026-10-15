import Mettapedia.OSLF.NativeTypes.Generation.Core
import Mettapedia.OSLF.NativeTypes.Structural.Semantics

open Mettapedia.OSLF.Framework

/-!
# Structural codes at the generated constructor's sort slots

Each input code has its authored parameter carrier and its computed universe
coordinate. The result code reads the same operation profile used by the
equation-formation checker. Its inhabitants are typed equation classes of
constructor introductions whose ordered arguments inhabit the supplied codes.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Modal.Rules (TypeCode)
open Mettapedia.OSLF.NativeTypes.Structural (ConstructorValue)
open ModalHypercube (HSort)

def structuralDeclaration (generated : Generated) (index : Fin generated.snapshot.language.terms.length) :
    GrammarRule := generated.snapshot.language.terms[index]

def structuralOperation (generated : Generated) (index : Fin generated.snapshot.language.terms.length) :
    (Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.signature generated.snapshot.language).Operation :=
  Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.constructorOperation generated.snapshot.language
    (structuralDeclaration generated index) (List.getElem_mem _)

def structuralInputSort (generated : Generated) (index : Fin generated.snapshot.language.terms.length)
    (position : Fin (structuralDeclaration generated index).params.length) : HSort :=
  Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.input generated.vertex.2 (structuralOperation generated index) position

def structuralOutputSort (generated : Generated) (index : Fin generated.snapshot.language.terms.length) : HSort :=
  Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.output generated.vertex.2 (structuralOperation generated index)

abbrev StructuralInputs (generated : Generated) (bound : List TypeExpr)
    (index : Fin generated.snapshot.language.terms.length) :=
  (position : Fin (structuralDeclaration generated index).params.length) →
    TypeCode generated.plan bound (structuralDeclaration generated index).params[position].typeExpr
      (structuralInputSort generated index position)

def structuralMeaning (generated : Generated) (bound : List TypeExpr)
    (index : Fin generated.snapshot.language.terms.length)
    (inputs : StructuralInputs generated bound index) (term : Pattern) : Prop :=
  HasType generated.snapshot.language generated.snapshot.free bound term
    (.base (structuralDeclaration generated index).category) ∧
  ∃ value : ConstructorValue generated.snapshot.language generated.snapshot.free bound
      (structuralDeclaration generated index),
    Relation.EqvGen (Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceSemantics.Equation generated.plan bound
      (.base (structuralDeclaration generated index).category)) term value.pattern ∧
    ∀ position, (inputs position).meaning
      (value.arguments[(position.val)]'(by rw [value.arguments_length]; exact position.isLt))

def structuralCode (generated : Generated) (bound : List TypeExpr)
    (index : Fin generated.snapshot.language.terms.length)
    (inputs : StructuralInputs generated bound index) :
    TypeCode generated.plan bound (.base (structuralDeclaration generated index).category)
      (structuralOutputSort generated index) where
  meaning := structuralMeaning generated bound index inputs
  bounded _ inhabited := inhabited.1

def Generated.structuralFormer? (generated : Generated) (bound : List TypeExpr)
    (index : Fin generated.snapshot.language.terms.length)
    (inputs : StructuralInputs generated bound index) :
    Option (Σ sort : HSort,
      TypeCode generated.plan bound (.base (structuralDeclaration generated index).category) sort) :=
  if generated.equationAdmission = some true ∧
      (⟨index.val, structuralDeclaration generated index⟩ : Mettapedia.OSLF.NativeTypes.Structural.Former) ∈
        generated.structuralCatalogue then
    some ⟨structuralOutputSort generated index, structuralCode generated bound index inputs⟩
  else none

/-- Introduction uses the independent sorted constructor introduction and
the actual argument predicates, rather than a root-name Boolean oracle. -/
theorem structural_intro (generated : Generated) (bound : List TypeExpr)
    (index : Fin generated.snapshot.language.terms.length)
    (inputs : StructuralInputs generated bound index)
    (value : ConstructorValue generated.snapshot.language generated.snapshot.free bound
      (structuralDeclaration generated index))
    (arguments : ∀ position, (inputs position).meaning
      (value.arguments[(position.val)]'(by rw [value.arguments_length]; exact position.isLt))) :
    (structuralCode generated bound index inputs).meaning value.pattern :=
  ⟨value.typed (List.getElem_mem _), value, .refl _, arguments⟩

/-- Elimination recovers the constructor introduction, its equation witness
and every ordered dependent input certificate. -/
theorem structural_elim {generated : Generated} {bound : List TypeExpr}
    {index : Fin generated.snapshot.language.terms.length}
    {inputs : StructuralInputs generated bound index} {term : Pattern}
    (inhabited : (structuralCode generated bound index inputs).meaning term) :
    ∃ value : ConstructorValue generated.snapshot.language generated.snapshot.free bound
      (structuralDeclaration generated index),
      Relation.EqvGen (Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceSemantics.Equation generated.plan bound
        (.base (structuralDeclaration generated index).category)) term value.pattern ∧
      ∀ position, (inputs position).meaning
        (value.arguments[(position.val)]'(by rw [value.arguments_length]; exact position.isLt)) :=
  inhabited.2

theorem structural_result_reads_computed_slot {generated : Generated} {bound : List TypeExpr}
    {index : Fin generated.snapshot.language.terms.length} (inputs : StructuralInputs generated bound index)
    {code : Σ sort : HSort,
      TypeCode generated.plan bound (.base (structuralDeclaration generated index).category) sort}
    (formed : generated.structuralFormer? bound index inputs = some code) :
    code.1 = Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.output generated.vertex.2 (structuralOperation generated index) := by
  unfold Generated.structuralFormer? at formed
  split at formed
  · cases formed
    rfl
  · cases formed

theorem rejected_equation_profile_has_no_structural_code {generated : Generated}
    {bound : List TypeExpr} {index : Fin generated.snapshot.language.terms.length}
    (inputs : StructuralInputs generated bound index)
    (rejected : generated.equationAdmission = some false) :
    generated.structuralFormer? bound index inputs = none := by
  simp [Generated.structuralFormer?, rejected]

end Mettapedia.OSLF.NativeTypes.Generation

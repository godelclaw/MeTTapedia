import Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend
import Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated
import Mettapedia.OSLF.NativeTypes.Generation.EquationAdmission

open Mettapedia.OSLF.Framework

/-!
# Generated structural native judgments for the original machine

The language presentation is passed to the native type generator unchanged.
Constructor formers and their ordered parameter carriers are read from its
output. Local constructor decomposition interprets these native types, and
the actual equation-free occurrence engine interprets their modalities.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated

open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Generation (Generated LanguageFragment StructuralInputs structuralDeclaration
  structuralInputSort structuralOutputSort)
open Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes (Model)
open Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeIntroduction (EquationsInterpreted)
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core
open ModalHypercube (HSort)

def fragment : LanguageFragment := {operational := Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.permissions}
def chosen : Snapshot := Mettapedia.OSLF.NativeTypes.Generation.selectedSnapshot Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.snapshot fragment
def vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.CubeVertex chosen.language :=
  (fun _ => .star, fun _ => .star)
def generated : Generated := Mettapedia.OSLF.NativeTypes.Generation.generate Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.snapshot
  fragment Mettapedia.OSLF.NativeTypes.Structural.heytingFragment vertex

theorem generated_snapshot : generated.snapshot = Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.snapshot := by
  change Mettapedia.OSLF.NativeTypes.Generation.selectedSnapshot Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.snapshot fragment = _
  simp only [Mettapedia.OSLF.NativeTypes.Generation.selectedSnapshot, fragment,
    Mettapedia.OSLF.NativeTypes.Generation.unrestricted_signature]

theorem generated_plan : generated.plan = Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.plan := by
  unfold Mettapedia.OSLF.NativeTypes.Generation.Generated.plan
  rw [generated_snapshot]
  rfl

theorem generated_equations : generated.plan.equations = [] := by
  rw [generated_plan]
  exact Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.plan_equations

theorem generated_equation_admission : generated.equationAdmission = some true :=
  Mettapedia.OSLF.NativeTypes.Generation.no_authored_equations_generate_every_vertex
    Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.snapshot fragment Mettapedia.OSLF.NativeTypes.Structural.heytingFragment vertex rfl

theorem generated_structural_catalogue :
    generated.structuralCatalogue = Mettapedia.OSLF.NativeTypes.Structural.structuralFormers generated.snapshot.language := by
  change (if generated.equationAdmission != some false &&
      generated.logicFragment.core.structural then
    Mettapedia.OSLF.NativeTypes.Structural.structuralFormers generated.snapshot.language else []) = _
  rw [generated_equation_admission]
  rfl

def syntaxSort : Pattern → HSort
  | .bvar _ | .fvar _ => .box
  | _ => .star

def model : Model generated := fun bound =>
  {sortDomain := fun carrier sort source =>
    OpenPatternWellSorted generated.snapshot.language generated.snapshot.free bound carrier source ∧
      syntaxSort source = sort
   carrierBounded := fun _ _ _ inhabited => inhabited.1.1}

theorem equations_interpreted : EquationsInterpreted model := by
  intro bound carrier sort source receipt completed
  have impossible := completed.job.1
  rw [generated_equations] at impossible
  exact False.elim (List.not_mem_nil impossible)

def inputs (bound : List TypeExpr) (index : Fin generated.snapshot.language.terms.length) :
    StructuralInputs generated bound index := fun position =>
  {meaning := OpenPatternWellSorted generated.snapshot.language generated.snapshot.free bound
    (structuralDeclaration generated index).params[position].typeExpr
   bounded := fun _ inhabited => inhabited.1}

theorem inputs_interpreted (bound : List TypeExpr) (index : Fin generated.snapshot.language.terms.length) :
    Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated.InputsInterpreted (inputs bound index) := by
  intro position source receipt completed
  have impossible := completed.job.1
  rw [generated_equations] at impossible
  exact False.elim (List.not_mem_nil impossible)

theorem every_structural_former_emitted (bound : List TypeExpr)
    (index : Fin generated.snapshot.language.terms.length) :
    generated.structuralFormer? bound index (inputs bound index) =
      some ⟨structuralOutputSort generated index,
        Mettapedia.OSLF.NativeTypes.Generation.structuralCode generated bound index (inputs bound index)⟩ := by
  unfold Mettapedia.OSLF.NativeTypes.Generation.Generated.structuralFormer?
  apply if_pos
  refine ⟨generated_equation_admission, ?_⟩
  rw [generated_structural_catalogue]
  apply (Mettapedia.OSLF.NativeTypes.Structural.mem_structuralFormers_iff _ _).mpr
  exact List.getElem?_eq_getElem index.isLt

def effective (bound : List TypeExpr) (index : Fin generated.snapshot.language.terms.length) :
    Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated.Effective model bound index (inputs bound index) where
  output source := checkOpenPatternWellSorted generated.snapshot.language generated.snapshot.free bound
    (.base (structuralDeclaration generated index).category) source &&
      decide (syntaxSort source = structuralOutputSort generated index)
  output_exact source := by
    simp only [Bool.and_eq_true, checkOpenPatternWellSorted_eq_true_iff, decide_eq_true_eq, model]
  input position source := checkOpenPatternWellSorted generated.snapshot.language generated.snapshot.free bound
    (structuralDeclaration generated index).params[position].typeExpr source &&
      decide (syntaxSort source = structuralInputSort generated index position)
  input_exact position source := by
    simp only [Bool.and_eq_true, checkOpenPatternWellSorted_eq_true_iff, decide_eq_true_eq, model, inputs]
    tauto

def structuralBackend (bound : List TypeExpr) :
    Mettapedia.OSLF.NativeTypes.Decision.Structural.ConstructorBackend.OrderedBackend generated bound
      (Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.Source bound) :=
  let original := Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated.localBackend generated bound generated_equations
  {values := original.values
   closed := original.closed
   sound := original.sound
   coverage := original.coverage
   completionBudget := original.completionBudget
   complete_at := fun _ _ admitted => admitted.2.2.1
   values_stable := original.values_stable
   closed_stable := original.closed_stable
   ordered_coverage := original.ordered_coverage}

/-- Only the output carrier selects a constructor leaf. Its declaration and
parameter slots still come from the generated authored signature. -/
abbrev CfgFormer := {index : Fin generated.snapshot.language.terms.length //
  (structuralDeclaration generated index).category = "Cfg"}

theorem source_theory (bound : List TypeExpr) (former : CfgFormer) :
    Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated.sourceTheory generated bound former.val =
      Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.theory bound := by
  unfold Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated.sourceTheory Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.theory
  rw [generated_plan, former.property]

def tests (bound : List TypeExpr) (former : CfgFormer) :
    Test (Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.theory bound) (Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.Source bound) := by
  let actual := Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated.test equations_interpreted (structuralBackend bound)
    former.val (inputs bound former.val) (inputs_interpreted bound former.val) (effective bound former.val)
  exact {
    predicate := ⟨actual.predicate.val, by
      intro first second related
      apply actual.predicate.property
      change Relation.EqvGen (GeneralOccurrenceSemantics.Equation generated.plan bound
        (.base (structuralDeclaration generated former.val).category)) first second
      change Relation.EqvGen (GeneralOccurrenceSemantics.Equation Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.plan
        bound (.base "Cfg")) first second at related
      rw [generated_plan, former.property]
      exact related⟩
    evaluate := actual.evaluate
    positive := actual.positive
    negative := actual.negative
    completionBudget := actual.completionBudget
    complete_at := actual.complete_at
    complete_above := actual.complete_above}

theorem leaf_generated_meaning (bound : List TypeExpr) (former : CfgFormer) (source : Pattern) :
    (tests bound former).predicate source ↔
      (Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes.structuralCode (model bound) former.val
        (inputs bound former.val)).meaning source := by
  unfold tests
  exact Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated.test_generated_comparison equations_interpreted
    (structuralBackend bound) former.val (inputs bound former.val)
    (inputs_interpreted bound former.val) (effective bound former.val) source

def cfgFormers : List CfgFormer :=
  (List.finRange generated.snapshot.language.terms.length).filterMap fun index =>
    if category : (structuralDeclaration generated index).category = "Cfg" then some ⟨index, category⟩ else none

def former? (label : String) : Option CfgFormer :=
  cfgFormers.find? fun former => (structuralDeclaration generated former.val).label == label

def run (bound : List TypeExpr) (formula : Formula CfgFormer) (source : Pattern) (budget : Nat) :=
  check (Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.backend bound) (tests bound) formula source budget

def decisionBound (bound : List TypeExpr) (formula : Formula CfgFormer) (source : Pattern) : Nat :=
  workBound (Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.backend bound) (tests bound) formula source

theorem whole_language_formula_complete (bound : List TypeExpr) (formula : Formula CfgFormer)
    (source : Pattern) (admitted : Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.Source bound source) :
    (run bound formula source (decisionBound bound formula source)).Decided :=
  checked_complete (Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.backend bound) (tests bound) formula source admitted _
    (Nat.le_refl _)

theorem positive_generated_meaning (bound : List TypeExpr) (formula : Formula CfgFormer)
    (source : Pattern) (budget : Nat) (read : (run bound formula source budget).answer = some true) :
    denotation (tests bound) formula (.empty _) source :=
  Outcome.positive _ read

theorem negative_generated_meaning (bound : List TypeExpr) (formula : Formula CfgFormer)
    (source : Pattern) (budget : Nat) (read : (run bound formula source budget).answer = some false) :
    ¬ denotation (tests bound) formula (.empty _) source :=
  Outcome.negative _ read

end Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated

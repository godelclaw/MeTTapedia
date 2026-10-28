import Mettapedia.Logic.HOL.ConstructorProjections
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeVectorComputationRows

/-!
# Vec computation with constructed head and tail selectors

The selected head and tail are generated from the cons constructor. Their
equations follow from choice at the two field carriers and constructor field
injectivity. The existing computation-row producer consumes these derived
proofs. The remaining background contains no assumed projection equation.
Native source evidence for the constructor-level premises is still required.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorComputationRows
namespace SelectedProjections

open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Annotated NativeNaturalVectorFamilies
local infixr:60 " ⇒ " => HOL.Ty.arr
universe u v
variable {Base : Type u} {Const : HOL.Ty Base → Type v}

structure Choices (operations : Operations Base Const) where
  headSelection : HOL.ClosedTerm Const (HOL.SelectionProofs.Selection operations.element)
  tailSelection : HOL.ClosedTerm Const (HOL.SelectionProofs.Selection operations.vector)

variable (operations : Operations Base Const) (choices : Choices operations)

def constructed : Operations Base Const :=
  {operations with
    head := HOL.ConstructorProjections.secondProjection choices.headSelection operations.cons
    tail := HOL.ConstructorProjections.thirdProjection choices.tailSelection operations.cons}

def assumptions (Γ : HOL.Ctx Base) : List (HOL.Formula Const Γ) :=
  [HOL.SelectionProofs.principle (HOL.weakenCtx Γ operations.selection),
   HOL.NaturalRecursionProofs.statement (HOL.weakenCtx Γ operations.zero)
     (HOL.weakenCtx Γ operations.successor) (operations.vector ⇒ operations.result),
   HOL.SelectionProofs.principle (HOL.weakenCtx Γ choices.headSelection),
   HOL.SelectionProofs.principle (HOL.weakenCtx Γ choices.tailSelection),
   HOL.ConstructorProjections.fieldInjective (HOL.weakenCtx Γ operations.cons)]

def closedAssumptions : List (HOL.ClosedFormula Const) := assumptions operations choices []

theorem assumptions_substitute {Γ Ξ : HOL.Ctx Base} (σ : HOL.Subst Const Γ Ξ) :
    (assumptions operations choices Γ).map (HOL.subst σ) = assumptions operations choices Ξ := by
  simp only [assumptions, List.map_cons, List.map_nil]
  congr 1
  · simp [HOL.SelectionProofs.principle, HOL.SelectionProofs.instanceFormula,
      HOL.subst, HOL.subst_weaken, HOL.subst_weakenCtx, HOL.Subst.lift]
  · congr 1
    · simp [HOL.NaturalRecursionProofs.statement, HOL.NaturalRecursionProofs.subst_body,
        HOL.subst, HOL.subst_weaken, HOL.subst_weakenCtx, HOL.Subst.lift, HOL.Rename.weaken]
    · simp [HOL.SelectionProofs.principle, HOL.SelectionProofs.instanceFormula,
        HOL.subst, HOL.subst_weaken, HOL.subst_weakenCtx, HOL.Subst.lift]

theorem assumptions_eq_closed (Γ : HOL.Ctx Base) :
    assumptions operations choices Γ = AnnotatedPredicateReading.assumptions (closedAssumptions operations choices) Γ := by
  let ρ : HOL.Subst Const [] Γ := fun index => nomatch index
  calc
    _ = (assumptions operations choices []).map (HOL.subst ρ) := (assumptions_substitute operations choices ρ).symm
    _ = _ := by
      apply List.map_congr_left
      intro formula _
      exact HOL.subst_weakenCtx ρ formula

variable {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)}

def head_law (choice : HOL.ProofSyntax Const Δ (HOL.SelectionProofs.principle (HOL.weakenCtx Γ choices.headSelection)))
    (injectivity : HOL.ProofSyntax Const Δ (HOL.ConstructorProjections.fieldInjective (HOL.weakenCtx Γ operations.cons))) :
    HOL.ProofSyntax Const Δ (constructed operations choices).headLaw := by
  apply HOL.ProofSyntax.castIndices rfl ?_
    (HOL.ConstructorProjections.second_law (HOL.weakenCtx Γ choices.headSelection)
      (HOL.weakenCtx Γ operations.cons) choice injectivity)
  rw [← HOL.ConstructorProjections.weakenCtx_secondProjection]
  rfl

def tail_law (choice : HOL.ProofSyntax Const Δ (HOL.SelectionProofs.principle (HOL.weakenCtx Γ choices.tailSelection)))
    (injectivity : HOL.ProofSyntax Const Δ (HOL.ConstructorProjections.fieldInjective (HOL.weakenCtx Γ operations.cons))) :
    HOL.ProofSyntax Const Δ (constructed operations choices).tailLaw := by
  apply HOL.ProofSyntax.castIndices rfl ?_
    (HOL.ConstructorProjections.third_law (HOL.weakenCtx Γ choices.tailSelection)
      (HOL.weakenCtx Γ operations.cons) choice injectivity)
  rw [← HOL.ConstructorProjections.weakenCtx_thirdProjection]
  rfl

theorem head_law_free (choice : HOL.ProofSyntax Const Δ (HOL.SelectionProofs.principle (HOL.weakenCtx Γ choices.headSelection)))
    (injectivity : HOL.ProofSyntax Const Δ (HOL.ConstructorProjections.fieldInjective (HOL.weakenCtx Γ operations.cons)))
    (choiceFree : choice.FunctionExtensionalityFree) (injectivityFree : injectivity.FunctionExtensionalityFree) :
    (head_law operations choices choice injectivity).FunctionExtensionalityFree := by
  simpa only [head_law, HOL.ProofSyntax.functionExtensionalityFree_castIndices] using
    HOL.ConstructorProjections.second_law_free _ _ choice injectivity choiceFree injectivityFree

theorem tail_law_free (choice : HOL.ProofSyntax Const Δ (HOL.SelectionProofs.principle (HOL.weakenCtx Γ choices.tailSelection)))
    (injectivity : HOL.ProofSyntax Const Δ (HOL.ConstructorProjections.fieldInjective (HOL.weakenCtx Γ operations.cons)))
    (choiceFree : choice.FunctionExtensionalityFree) (injectivityFree : injectivity.FunctionExtensionalityFree) :
    (tail_law operations choices choice injectivity).FunctionExtensionalityFree := by
  simpa only [tail_law, HOL.ProofSyntax.functionExtensionalityFree_castIndices] using
    HOL.ConstructorProjections.third_law_free _ _ choice injectivity choiceFree injectivityFree

def rowProof (row : Row) :
    HOL.ProofSyntax Const (assumptions operations choices (row.parameters (constructed operations choices)))
      (.eq (row.leftCode (constructed operations choices)) (row.rightCode (constructed operations choices))) :=
  row.proofFrom (constructed operations choices)
    (.hyp ⟨0, by simp [assumptions]⟩)
    (.hyp ⟨1, by simp [assumptions]⟩)
    (head_law operations choices (.hyp ⟨2, by simp [assumptions]⟩) (.hyp ⟨4, by simp [assumptions]⟩))
    (tail_law operations choices (.hyp ⟨3, by simp [assumptions]⟩) (.hyp ⟨4, by simp [assumptions]⟩))

theorem rowProof_free (row : Row) : (rowProof operations choices row).FunctionExtensionalityFree := by
  apply Row.proofFrom_free
  · trivial
  · trivial
  · exact head_law_free operations choices _ _ True.intro True.intro
  · exact tail_law_free operations choices _ _ True.intro True.intro

def template (profile : Programs.ComputationProfiles.Selection) (row : Row) :
    AnnotatedPredicateReading.Roots.Template (constructed operations choices).lexicalReading
      (closedAssumptions operations choices) (Programs.Annotated.church profile).constantType where
  parameters := row.parameters (constructed operations choices)
  carrier := operations.result
  rawLeft := row.rawLeft (constructed operations choices)
  rawRight := row.rawRight (constructed operations choices)
  leftCode := row.leftCode (constructed operations choices)
  rightCode := row.rightCode (constructed operations choices)
  leftRead := (row.template (constructed operations choices) profile).leftRead
  rightRead := (row.template (constructed operations choices) profile).rightRead
  proof := HOL.ProofSyntax.castIndices (assumptions_eq_closed operations choices _) rfl (rowProof operations choices row)

def entries (profile : Programs.ComputationProfiles.Selection) :
    AnnotatedPredicateReading.Roots.Table (constructed operations choices).lexicalReading
      (closedAssumptions operations choices) (Programs.Annotated.church profile).constantType Checking.table
  | ⟨2, _⟩ => some ⟨template operations choices profile .nil, rfl⟩
  | ⟨3, _⟩ => some ⟨template operations choices profile .cons, rfl⟩
  | _ => none

theorem entries_free (profile : Programs.ComputationProfiles.Selection)
    (address : Fin Checking.table.length) (entry) (known : entries operations choices profile address = some entry) :
    entry.template.proof.FunctionExtensionalityFree := by
  fin_cases address <;> simp only [entries] at known
  · cases known
  · cases known
  · cases known
    simpa only [template, HOL.ProofSyntax.functionExtensionalityFree_castIndices] using rowProof_free operations choices .nil
  · cases known
    simpa only [template, HOL.ProofSyntax.functionExtensionalityFree_castIndices] using rowProof_free operations choices .cons

#print axioms head_law
#print axioms tail_law
#print axioms rowProof
#print axioms rowProof_free
#print axioms entries_free
end SelectedProjections
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorComputationRows

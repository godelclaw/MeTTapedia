import Mettapedia.Logic.HOL.RawVectorConstructors
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeVectorConstructorProjections
import Mettapedia.Logic.HOL.ProofSyntaxAppend

/-!
# Original Vec rows over an encoded recursive-space constructor

The constructor packs the original index/head payload and a padded child
function. Its field-injectivity proof feeds the constructed selectors, and
their equations feed the existing row producer. The remaining commitments
are choice instances, natural recursion instances and raw-constructor field
injectivity; no Vec-specific projection or injectivity law is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorComputationRows
namespace EncodedConstructor
open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Annotated NativeNaturalVectorFamilies
local infixr:60 " ⇒ " => HOL.Ty.arr
universe u v
variable {Base : Type u} {Const : HOL.Ty Base → Type v}

structure Interface (raw : HOL.RawVectorConstructors.Signature Base Const) where
  result : HOL.Ty Base
  recursionSelection : HOL.ClosedTerm Const (HOL.SelectionProofs.Selection (raw.number ⇒ raw.space ⇒ result))
  headSelection : HOL.ClosedTerm Const (HOL.SelectionProofs.Selection raw.element)
  tailSelection : HOL.ClosedTerm Const (HOL.SelectionProofs.Selection raw.space)

variable (raw : HOL.RawVectorConstructors.Signature Base Const) (interface : Interface raw)

def operations : Operations Base Const where
  number := raw.number
  element := raw.element
  vector := raw.space
  result := interface.result
  zero := raw.zero
  successor := raw.successor
  nil := raw.nil
  cons := raw.cons
  head := HOL.ConstructorProjections.secondProjection interface.headSelection raw.cons
  tail := HOL.ConstructorProjections.thirdProjection interface.tailSelection raw.cons
  selection := interface.recursionSelection

def choices : SelectedProjections.Choices (operations raw interface) :=
  ⟨interface.headSelection, interface.tailSelection⟩

def vectorAssumptions (Γ : HOL.Ctx Base) : List (HOL.Formula Const Γ) :=
  (SelectedProjections.assumptions (operations raw interface) (choices raw interface) Γ).take 4

def assumptions (Γ : HOL.Ctx Base) : List (HOL.Formula Const Γ) :=
  vectorAssumptions raw interface Γ ++ raw.assumptions Γ

def closedAssumptions : List (HOL.ClosedFormula Const) := assumptions raw interface []

theorem assumptions_substitute {Γ Ξ : HOL.Ctx Base} (σ : HOL.Subst Const Γ Ξ) :
    (assumptions raw interface Γ).map (HOL.subst σ) = assumptions raw interface Ξ := by
  simp only [assumptions, vectorAssumptions, List.map_append, List.map_take]
  rw [SelectedProjections.assumptions_substitute, raw.assumptions_substitute]

theorem assumptions_eq_closed (Γ : HOL.Ctx Base) :
    assumptions raw interface Γ = AnnotatedPredicateReading.assumptions (closedAssumptions raw interface) Γ := by
  let ρ : HOL.Subst Const [] Γ := fun index => nomatch index
  calc
    _ = (assumptions raw interface []).map (HOL.subst ρ) := (assumptions_substitute raw interface ρ).symm
    _ = _ := by
      apply List.map_congr_left
      intro formula _
      exact HOL.subst_weakenCtx ρ formula

def injectivity (Γ : HOL.Ctx Base) :
    HOL.ProofSyntax Const (assumptions raw interface Γ)
      (HOL.ConstructorProjections.fieldInjective (HOL.weakenCtx Γ (operations raw interface).cons)) := by
  apply HOL.ProofSyntax.castIndices rfl ?_
    ((raw.field_injective (Γ := Γ)).mono (HOL.ProofSyntax.OccurrenceMap.appendLeft (vectorAssumptions raw interface Γ) (raw.assumptions Γ)))
  rw [show (operations raw interface).cons = raw.cons from rfl, raw.weakenCtx_cons]

theorem injectivity_free (Γ : HOL.Ctx Base) : (injectivity raw interface Γ).FunctionExtensionalityFree := by
  simpa only [injectivity, HOL.ProofSyntax.functionExtensionalityFree_castIndices,
    HOL.ProofSyntax.functionExtensionalityFree_mono] using raw.field_injective_free (Γ := Γ)

def rowProof (row : Row) :
    HOL.ProofSyntax Const (assumptions raw interface (row.parameters (operations raw interface)))
      (.eq (row.leftCode (operations raw interface)) (row.rightCode (operations raw interface))) :=
  row.proofFrom (operations raw interface)
    (.hyp ⟨0, by simp [assumptions, vectorAssumptions, SelectedProjections.assumptions, HOL.RawVectorConstructors.Signature.assumptions]⟩)
    (.hyp ⟨1, by simp [assumptions, vectorAssumptions, SelectedProjections.assumptions, HOL.RawVectorConstructors.Signature.assumptions]⟩)
    (SelectedProjections.head_law (operations raw interface) (choices raw interface)
      (.hyp ⟨2, by simp [assumptions, vectorAssumptions, SelectedProjections.assumptions, HOL.RawVectorConstructors.Signature.assumptions]⟩)
      (injectivity raw interface _))
    (SelectedProjections.tail_law (operations raw interface) (choices raw interface)
      (.hyp ⟨3, by simp [assumptions, vectorAssumptions, SelectedProjections.assumptions, HOL.RawVectorConstructors.Signature.assumptions]⟩)
      (injectivity raw interface _))

theorem rowProof_free (row : Row) : (rowProof raw interface row).FunctionExtensionalityFree := by
  apply Row.proofFrom_free
  · trivial
  · trivial
  · exact SelectedProjections.head_law_free _ _ _ _ True.intro (injectivity_free raw interface _)
  · exact SelectedProjections.tail_law_free _ _ _ _ True.intro (injectivity_free raw interface _)

def template (profile : Programs.ComputationProfiles.Selection) (row : Row) :
    AnnotatedPredicateReading.Roots.Template (operations raw interface).lexicalReading
      (closedAssumptions raw interface) (Programs.Annotated.church profile).constantType where
  parameters := row.parameters (operations raw interface)
  carrier := interface.result
  rawLeft := row.rawLeft (operations raw interface)
  rawRight := row.rawRight (operations raw interface)
  leftCode := row.leftCode (operations raw interface)
  rightCode := row.rightCode (operations raw interface)
  leftRead := (row.template (operations raw interface) profile).leftRead
  rightRead := (row.template (operations raw interface) profile).rightRead
  proof := HOL.ProofSyntax.castIndices (assumptions_eq_closed raw interface _) rfl (rowProof raw interface row)

def entries (profile : Programs.ComputationProfiles.Selection) :
    AnnotatedPredicateReading.Roots.Table (operations raw interface).lexicalReading
      (closedAssumptions raw interface) (Programs.Annotated.church profile).constantType Checking.table
  | ⟨2, _⟩ => some ⟨template raw interface profile .nil, rfl⟩
  | ⟨3, _⟩ => some ⟨template raw interface profile .cons, rfl⟩
  | _ => none

theorem entries_free (profile : Programs.ComputationProfiles.Selection)
    (address : Fin Checking.table.length) (entry) (known : entries raw interface profile address = some entry) :
    entry.template.proof.FunctionExtensionalityFree := by
  fin_cases address <;> simp only [entries] at known
  · cases known
  · cases known
  · cases known
    simpa only [template, HOL.ProofSyntax.functionExtensionalityFree_castIndices] using rowProof_free raw interface .nil
  · cases known
    simpa only [template, HOL.ProofSyntax.functionExtensionalityFree_castIndices] using rowProof_free raw interface .cons

#print axioms injectivity
#print axioms injectivity_free
#print axioms rowProof
#print axioms rowProof_free
#print axioms entries_free
end EncodedConstructor
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorComputationRows

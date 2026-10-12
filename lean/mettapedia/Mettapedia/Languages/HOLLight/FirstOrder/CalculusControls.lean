import Mettapedia.Languages.HOLLight.FirstOrder.Builders

/-!
# Controls for HOL Light's first-order calculus

Small proofs that the generic inference checker accepts, and wrong goals it refuses: REFL and
ASSUME on a Boolean variable, ASSUME refused at a non-Boolean term, and DEDUCT_ANTISYM_RULE
combining two assumptions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.FirstOrder.CalculusControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.LabeledTreeOrder
open Mettapedia.Languages.OpenTheory

def validated : ValidatedCalculusLanguageDef := ⟨holCalculus [], holCalculus_valid⟩

/-- The Boolean variables `x` and `y`, and a variable `x` of type variable `x`. -/
def xTerm : DBTerm := .free ⟨Name.global "x", Ty.bool⟩
def yTerm : DBTerm := .free ⟨Name.global "y", Ty.bool⟩
def oddTerm : DBTerm := .free ⟨Name.global "x", .var (Name.global "x")⟩
def xP : Pattern := groundP (encodeTerm xTerm)
def yP : Pattern := groundP (encodeTerm yTerm)
def oddP : Pattern := groundP (encodeTerm oddTerm)

/-- `⊢ x = x` by REFL. -/
def reflProof : RawProof := .node ⟨⟨"hol.refl"⟩, [xP, boolP]⟩ [typeProof [] xTerm]

theorem refl_accepted : checkRaw validated (thmJ nilP (equalityTermP boolP xP xP)) reflProof = true := by
  decide +kernel

theorem refl_wrong_goal : checkRaw validated (thmJ nilP (equalityTermP boolP xP yP)) reflProof = false := by
  decide +kernel

/-- `x ⊢ x` by ASSUME. -/
def assumeProof (term : DBTerm) : RawProof :=
  .node ⟨⟨"hol.assume"⟩, [groundP (encodeTerm term)]⟩ [typeProof [] term]

theorem assume_accepted : checkRaw validated (thmJ (consP xP nilP) xP) (assumeProof xTerm) = true := by
  decide +kernel

/-- ASSUME needs a Boolean term: the variable `x` of type `x` is refused. -/
theorem assume_nonBoolean_refused :
    checkRaw validated (thmJ (consP oddP nilP) oddP) (assumeProof oddTerm) = false := by
  decide +kernel

/-- From `x ⊢ x` twice, DEDUCT_ANTISYM_RULE discharges both assumptions: `⊢ x = x`. -/
def deductProof : RawProof :=
  .node ⟨⟨"hol.deduct-antisym"⟩, [consP xP nilP, consP xP nilP, nilP, nilP, nilP, xP, xP, boolP]⟩
    [assumeProof xTerm, assumeProof xTerm, typeProof [] xTerm, typeProof [] xTerm,
      .node ⟨⟨"hol.erase-here"⟩, [xP, nilP]⟩ [], .node ⟨⟨"hol.erase-here"⟩, [xP, nilP]⟩ [],
      .node ⟨⟨"hol.union-left"⟩, [nilP]⟩ []]

theorem deduct_accepted : checkRaw validated (thmJ nilP (equalityTermP boolP xP xP)) deductProof = true := by
  decide +kernel

/-- The discharged assumption does not survive: `x ⊢ x = x` is refused. -/
theorem deduct_keeps_no_hypothesis :
    checkRaw validated (thmJ (consP xP nilP) (equalityTermP boolP xP xP)) deductProof = false := by
  decide +kernel

end Mettapedia.Languages.HOLLight.FirstOrder.CalculusControls

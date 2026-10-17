import Mettapedia.Languages.MeTTa.Experimental.StagedReflective.Presentation
import Mettapedia.Languages.MeTTa.PrimeCandidates.UniversalName
import Mettapedia.OSLF.Syntax.RhoSubstitutionEncoding

/-!
# candidate/rho structural non-collapse

candidate should internalize rho-style interaction without identifying its whole
native language with the rho calculus.  This module makes that boundary
precise at the raw-syntax level.

`DirectRhoFragment` is a deliberately generous rho-bearing fragment of
MeTTa Native syntax.  It contains arbitrary rho `Pattern` values and is closed
under native empty collections, superposition, and staged quotation.  Thus the
separation below does not depend on choosing only the one-node `pattern`
embedding.

The dependent Pure core is disjoint from this fragment.  In particular, a
native dependent function type is not a direct rho term, so the rho-bearing
fragment does not span candidate's native syntax.  This is a structural theorem
about the native constructors and the project's direct candidate-to-rho bridge.
It does not rule out an interpreter, a compiler, or another computational
encoding of candidate syntax as rho data.
-/

open Mettapedia.TypeTheory.Calculi.StagedScopedReflective
namespace Mettapedia.Languages.MeTTa.PrimeCandidates.RhoNonCollapse

open Mettapedia.Languages.MeTTa.Experimental.StagedReflective
open Mettapedia.Languages.MeTTa.PrimeCandidates.UniversalName
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Syntax
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- The direct rho-bearing fragment of MeTTa Native syntax.

The `pattern` case contains the complete rho syntax represented by `Pattern`.
The remaining cases close that image under the native collection and staging
constructors that are natural for interaction.  Dependent type formers are
intentionally absent: adding them would be an interpretation of dependent
type theory, rather than a direct rho embedding. -/
inductive DirectRhoFragment :
    {stage binders : Nat} → StagedReflectiveTm stage binders → Prop where
  | pattern {stage binders : Nat} (value : Pattern) :
      DirectRhoFragment (.pattern value : StagedReflectiveTm stage binders)
  | empty {stage binders : Nat} :
      DirectRhoFragment (.empty : StagedReflectiveTm stage binders)
  | superpose {stage binders : Nat}
      {left right : StagedReflectiveTm stage binders} :
      DirectRhoFragment left → DirectRhoFragment right →
      DirectRhoFragment (.superpose left right)
  | quote {high low binders : Nat} (route : StageHom high low)
      {term : StagedReflectiveTm high binders} :
      DirectRhoFragment term → DirectRhoFragment (.quote route term)

namespace DirectRhoFragment

/-- Every direct rho-bearing term is outside the partial projection to the
dependent Pure syntax. -/
@[simp] theorem pureProjection_eq_none
    {stage binders : Nat} {term : StagedReflectiveTm stage binders}
    (direct : DirectRhoFragment term) :
    term.twoSortProjection = none := by
  cases direct <;> rfl

/-- The direct rho-bearing fragment is closed under native superposition. -/
theorem superpose_closed {stage binders : Nat}
    {left right : StagedReflectiveTm stage binders}
    (leftDirect : DirectRhoFragment left)
    (rightDirect : DirectRhoFragment right) :
    DirectRhoFragment (.superpose left right) :=
  .superpose leftDirect rightDirect

/-- The direct rho-bearing fragment is closed under native quotation. -/
theorem quote_closed {high low binders : Nat} (route : StageHom high low)
    {term : StagedReflectiveTm high binders}
    (direct : DirectRhoFragment term) :
    DirectRhoFragment (.quote route term) :=
  .quote route direct

end DirectRhoFragment

/-- The current structural candidate-name translation lands in the direct
rho-bearing fragment when reified as a native runtime pattern. -/
def translatedCandidateName (name : CandidateName) : StagedReflectiveTm 0 0 :=
  .pattern (primeNameToRho name)

theorem translatedCandidateName_mem (name : CandidateName) :
    DirectRhoFragment (translatedCandidateName name) :=
  .pattern _

/-- No intrinsically Pure term is a direct rho-bearing native term.  The
separation holds for the entire conservative dependent core, not merely for
one selected constructor. -/
theorem pureImage_disjoint_directRho
    {stage binders : Nat} (term : ScopedTerm binders) :
    ¬ DirectRhoFragment (embedTwoSort stage term) := by
  intro direct
  have rejected := direct.pureProjection_eq_none
  rw [twoSortProjection_embedTwoSort] at rejected
  cases rejected

/-- A closed dependent function type in the native core. -/
def nativeDependentFunctionType : StagedReflectiveTm 0 0 :=
  embedTwoSort 0 (.pi .u0 .u0 : ScopedTerm 0)

/-- The dependent function type is a concrete negative witness for the direct
rho-bearing fragment. -/
theorem nativeDependentFunctionType_not_directRho :
    ¬ DirectRhoFragment nativeDependentFunctionType := by
  exact pureImage_disjoint_directRho (.pi .u0 .u0 : ScopedTerm 0)

/-- Structural rho spanning at an index means that every native term at that
index already belongs to the direct rho-bearing fragment. -/
def RhoSpansNativeAt (stage binders : Nat) : Prop :=
  ∀ term : StagedReflectiveTm stage binders, DirectRhoFragment term

/-- **candidate does not structurally collapse to rho.**  Even at the closed base
stage, the direct rho-bearing fragment fails to span native syntax. -/
theorem rho_does_not_span_closed_native_core :
    ¬ RhoSpansNativeAt 0 0 := by
  intro spans
  exact nativeDependentFunctionType_not_directRho
    (spans nativeDependentFunctionType)

/-! ## Positive and negative controls -/

example : DirectRhoFragment
    (.pattern (primeNameToRho UniversalName.mmPh) : StagedReflectiveTm 0 0) :=
  .pattern _

example : ¬ DirectRhoFragment nativeDependentFunctionType :=
  nativeDependentFunctionType_not_directRho


/-! ## Opaque data inclusion is not the open binding embedding

The `pattern` constructor includes arbitrary runtime syntax as inert data.
Its native substitution action deliberately leaves that data unchanged. The
existing intrinsic rho encoding has a different, proved action on open source
terms: `RhoSchema.IntrinsicEncoding.encodeTerm_bind` commutes with generic
pattern-context substitution. These actions cannot be identified merely because
both include the same closed runtime patterns.
-/

namespace PatternBoundary

open Mettapedia.OSLF.Binding
open RhoSchema RhoSchema.IntrinsicEncoding

/-- The existing open input refers to its ambient name beneath a distinct
input binder. It is included as data at native scope depth one. -/
def openInput : StagedReflectiveTm 0 1 :=
  .pattern (encodeTerm openInputDropsAmbient)

/-- The source calculus closes its ambient name using its own simultaneous
substitution, preserving the distinction from the input's new binder. -/
def sourceClosedInput : StagedReflectiveTm 0 0 :=
  .pattern (encodeTerm (bind closeInputAmbient openInputDropsAmbient))

/-- A well-scoped native environment supplying that same closed rho name. -/
def closeNativeAmbient : NativeSub 1 0 :=
  fun _ _ => .pattern (encodeTerm chan)

theorem openInput_in_direct_fragment : DirectRhoFragment openInput :=
  .pattern _

/-- Positive source control: the existing encoding closes the ambient name
under the input without capturing it as the new input variable. -/
theorem source_closing_preserves_input_binder :
    Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute
      (encodeSub closeInputAmbient) (encodeTerm openInputDropsAmbient) =
      .apply "PInput" [encodeTerm chan,
        .lambda none (.apply "PDrop" [encodeTerm chan])] :=
  openInput_bind_encodes_without_capture

/-- The complete native substitution leaves the runtime-data payload opaque,
including the source pattern's apparent de Bruijn indices. -/
theorem native_substitution_keeps_pattern_payload :
    nativeSubst closeNativeAmbient openInput =
      (.pattern (encodeTerm openInputDropsAmbient) : StagedReflectiveTm 0 0) :=
  rfl

/-- This concrete data inclusion fails the required source-substitution
square. The statement is relative to `pattern`, the actual native action,
and literal syntax equality; it is not an impossibility theorem for other
rho realizations in the native language. -/
theorem opaque_pattern_substitution_not_source_substitution :
    nativeSubst closeNativeAmbient openInput ≠ sourceClosedInput := by
  intro same
  change StagedReflectiveTm.pattern (encodeTerm openInputDropsAmbient) =
    StagedReflectiveTm.pattern
      (encodeTerm (bind closeInputAmbient openInputDropsAmbient)) at same
  have payloads := StagedReflectiveTm.pattern.inj same
  have distinct : encodeTerm openInputDropsAmbient ≠
      encodeTerm (bind closeInputAmbient openInputDropsAmbient) := by decide
  exact distinct payloads

/-- A source weakening changes both ambient name occurrences while lifting
past the input binder. -/
def weakenSource : Ren sig [Srt.nm] [Srt.nm, Srt.nm] :=
  fun _ value => .succ value

/-- Native weakening of opaque runtime data also fails the corresponding
source-renaming square, before any operational observations are quotiented. -/
theorem opaque_pattern_renaming_not_source_renaming :
    nativeRename nativeWk openInput ≠
      (.pattern (encodeTerm (rename weakenSource openInputDropsAmbient)) :
        StagedReflectiveTm 0 2) := by
  intro same
  change StagedReflectiveTm.pattern (encodeTerm openInputDropsAmbient) =
    StagedReflectiveTm.pattern
      (encodeTerm (rename weakenSource openInputDropsAmbient)) at same
  have payloads := StagedReflectiveTm.pattern.inj same
  have distinct : encodeTerm openInputDropsAmbient ≠
      encodeTerm (rename weakenSource openInputDropsAmbient) := by decide
  exact distinct payloads

end PatternBoundary

#print axioms translatedCandidateName_mem
#print axioms pureImage_disjoint_directRho
#print axioms nativeDependentFunctionType_not_directRho
#print axioms rho_does_not_span_closed_native_core

end Mettapedia.Languages.MeTTa.PrimeCandidates.RhoNonCollapse

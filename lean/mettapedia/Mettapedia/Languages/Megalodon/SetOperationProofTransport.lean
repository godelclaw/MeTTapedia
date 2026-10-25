import Mettapedia.Languages.Megalodon.CheckedProofReconstruction
import Mettapedia.Languages.Megalodon.PreambleDependencyRestriction
import Mettapedia.Languages.HOLLight.SetOperationReplay

/-!
# A checked Megalodon powerset proof in the common material signature

The supplied native powerset proof is reconstructed as a retained HOL proof
relative to its one used axiom. A typed constant interpretation then sends
membership and powerset to the independently stated common set-operation
signature. The resulting source proof can be compiled into HOL Light and
interpreted in the set, well-founded hyperset and full hyperset models.

Only the powerset-introduction profile is used here. The wider HOTG preamble,
and the stronger powerset-elimination statement, are not silently admitted.
The generic reconstruction covers the existing monomorphic proof fragment;
this module is its concrete material instance, not a full forward compiler
from all HOL proof constructors to Megalodon.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.Megalodon.SetOperationProofTransport

open MathdataKernel HenkinTermInterpretation
open PreambleDependencyRestriction PreambleFragmentVertical SetOperationSemanticAuthority
open Mettapedia.Logic HOL.Embedding

def sourceTheory : List (HOL.ClosedFormula NativeConstant) := [introduction]

theorem opaqueTerms : CheckedProofReconstruction.Opaque restrictedEnvironment := by
  intro name declaration lookup
  have member := lookupTermList?_mem restrictedEnvironment.terms name lookup
  simp only [restrictedEnvironment, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> rfl

def knownSources : CheckedProofReconstruction.KnownSources sourceTheory := by
  intro name raw lookup
  simp only [restrictedEnvironment, Environment.lookupKnown?, lookupKnownList?] at lookup
  split at lookup
  · cases lookup
    exact ⟨⟨0, by simp [sourceTheory]⟩, introduction_erased⟩
  · cases lookup

/-- This proof is computed from the actual native proof object and its check. -/
def retained : HOL.ProofSyntax NativeConstant sourceTheory conclusion :=
  CheckedProofReconstruction.checkedSource opaqueTerms sourceTheory knownSources 32 0
    (Γ := []) [] (rawHypotheses := []) rfl subsetPowerProof proof_fragment
    conclusion conclusion_erased restricted_native_accepted

def base (_ : HenkinTermInterpretation.Base) : HOL.Ty Unit := .base ()

def constant {type : HOL.Ty HenkinTermInterpretation.Base} (source : NativeConstant type) :
    ZFSetHenkinInterpretation.Symbol (HOL.Ty.substitute base type) := by
  cases source with
  | primitive index lookup => simp [restrictedEnvironment] at lookup
  | named name declaration lookup typed =>
      simp only [restrictedEnvironment, Environment.lookupTerm?, lookupTermList?,
        membershipDeclaration, powerDeclaration] at lookup
      split at lookup
      · cases lookup
        have typeEq : type = HOL.Ty.arr setType (.arr setType .prop) := reifyType_injective typed.symm
        subst type
        exact .member
      · split at lookup
        · cases lookup
          have typeEq : type = HOL.Ty.arr setType setType := reifyType_injective typed.symm
          subst type
          exact .power
        · cases lookup

open ZFSetHenkinInterpretation (Symbol set)

/-- The material statement is authored independently of the native encoding. -/
def powerIntroduction : HOL.ClosedFormula Symbol :=
  .all (.all (.imp
    (.all (.imp
      (ZFSetHenkinInterpretation.member (.var .vz) (.var (.vs .vz)))
      (ZFSetHenkinInterpretation.member (.var .vz) (.var (.vs (.vs .vz))))))
    (ZFSetHenkinInterpretation.member (.var .vz) (.app (.const .power) (.var (.vs .vz))))))

def powerSelf : HOL.ClosedFormula Symbol :=
  .all (ZFSetHenkinInterpretation.member (.var .vz) (.app (.const .power) (.var .vz)))

theorem mapped_introduction : HOL.mapTypes base constant introduction = powerIntroduction := rfl
theorem mapped_conclusion : HOL.mapTypes base constant conclusion = powerSelf := rfl

/-- All intermediate equality proofs, binders and hypothesis occurrences
survive the signature translation. -/
def commonProof : HOL.ProofSyntax Symbol [powerIntroduction] powerSelf :=
  HOL.ProofSyntax.castIndices (by simp [sourceTheory, mapped_introduction]) mapped_conclusion
    (HOL.ProofSyntax.mapTypes base constant retained)

universe u

theorem powerIntroduction_sets : ZFSetHenkinInterpretation.model.{u}.models powerIntroduction := by
  intro collection _ candidate _ included
  exact (ZFSet.mem_powerset).mpr (fun _ present => included _ trivial present)

theorem powerIntroduction_hypersets
    (presentation : Mettapedia.TypeTheory.MaterialSets.Hypersets.HSet.Presentation.{u}) :
    (HypersetHenkinInterpretation.model presentation).models powerIntroduction := by
  intro collection _ candidate _ included
  exact Mettapedia.TypeTheory.MaterialSets.Hypersets.HSet.mem_powerset.mpr
    (fun _ present => included _ trivial present)

/-- The transported native proof, rather than an independently supplied proof
of the conclusion, establishes the theorem in the hyperset interpretation. -/
theorem native_proof_hyperset_meaning
    (presentation : Mettapedia.TypeTheory.MaterialSets.Hypersets.HSet.Presentation.{u}) :
    (HypersetHenkinInterpretation.model presentation).models powerSelf :=
  HOL.Soundness.extDerivation_sound commonProof.erase
    (HypersetHenkinInterpretation.functionsRespectEqv presentation)
    (fun index => nomatch index)
    (by
      intro formula member
      have same : formula = powerIntroduction := List.mem_singleton.mp member
      subst formula
      exact powerIntroduction_hypersets presentation)

end Mettapedia.Languages.Megalodon.SetOperationProofTransport

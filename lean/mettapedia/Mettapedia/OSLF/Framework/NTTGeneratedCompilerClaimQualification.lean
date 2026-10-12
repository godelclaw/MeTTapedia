import Mettapedia.OSLF.Framework.NTTClaimTracker
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedParallelActionComparisonControls
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedNativeControls
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedOperationalControls

/-!
# Qualified generated compiler endpoint in the paper inventory

The original inventory is retained unchanged. This companion records the
complete, explicitly typed version of the abridged presentation in Examples
30/31 and Proposition 32. Its metadata counts are separate from the imported
literal-source inventory and are not mathematical completion certificates.

Two printed type ambiguities are normalized explicitly. The consuming-fetch
edge has its endpoint-determined inputs `V,T`; the source rewrite category is
over `T`, whose complete target interpretation is `[N,P]`, with edges in
`[N,E]`. No equality of the incompatible printed `Hom` sorts is claimed.

The construction imports independently authored source and target signatures,
their static and operational declarations, all five complete constructor
comparisons, the canonical return-indexed category isomorphism, and the
inherited parallel-edge action equations. Its controls retain full function
arguments, both matching projections and separately supplied receipt origins.

The full recursive calculus, an all-arity executor, unrestricted reflective
observers and unconditional dependent product/classifier preservation remain
separate extensions. The two other unresolved paper endpoints are unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.NTTGeneratedCompilerClaimQualification

open NTTClaimTracker

def compilerClaim : NTTClaim :=
  ⟨"Prop 32",
    "The explicitly typed abridged name-passing lambda to all-arity polyadic pi translation is a closed morphism of the independently presented theories",
    "NamePassingGeneratedOperationalInterpretation interprets the independently declared beta, consuming-fetch and three active closures with both complete endpoints. NamePassingGeneratedParallelActionComparison supplies the actual finite-limit and closed compiler into the target with inherited commutative parallel-edge action equations. NamePassingGeneratedParallelActionCategoryComparison earns an isomorphism with the independently formed return-indexed target category, including both chosen matching projections, unit, composition and arbitrary matching edges. NamePassingGeneratedParallelActionConstructorComparison compares all five independently assembled CPS constructors, calibrates complete padded product/function domains canonically and proves the full original compiler restriction. NamePassingGeneratedNativeLanguage retains complete origin-indexed native receipt and comprehension readouts under every future restriction. Nonidentity diagram controls change an endpoint while retaining ordered origins; omitted function arguments change the whole result despite equal origin readouts. The endpoint-determined two-input phi and T-indexed category interpreted in [N,P]/[N,E] are explicit corrections to the printed ambiguities. This is the paper's abridged typed presentation, not the full recursive Boudol calculus or an unrestricted rho runtime/observer claim",
    .proven⟩

def claimList : List NTTClaim :=
  nttClaimList.map fun claim =>
    if claim.loc = "Prop 32" then compilerClaim else claim

def remaining : List NTTClaim :=
  claimList.filter fun claim =>
    claim.status = .partiallyFormalized || claim.status = .notFormalized

def countByStatus (status : NTTClaimStatus) : Nat :=
  (claimList.filter fun claim => claim.status = status).length

/-- The normalized inventory retains every original paper endpoint. -/
theorem paper_endpoints_unchanged : claimList.map (·.loc) = nttClaimList.map (·.loc) := by
  decide

/-- The two remaining source obligations are not granted closure by this companion. -/
theorem remaining_locations : remaining.map (·.loc) = ["Def 3 / Thm 4", "Sec 4 (syntax)"] := by
  decide

/-- A count of qualified inventory entries, not an independent proof audit. -/
theorem proven_count : countByStatus .proven = 19 := by
  decide

theorem partial_count : countByStatus .partiallyFormalized = 2 := by
  decide

theorem missing_count : countByStatus .notFormalized = 0 := by
  decide

end Mettapedia.OSLF.Framework.NTTGeneratedCompilerClaimQualification

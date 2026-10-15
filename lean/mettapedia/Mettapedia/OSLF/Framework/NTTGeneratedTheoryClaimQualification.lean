import Mettapedia.OSLF.Framework.NTTGeneratedCompilerClaimQualification
import Mettapedia.TypeTheory.Calculi.NativeDependent.TheoryGeneratedPresentationControls

/-!
# Qualified corrected endpoints in the paper inventory

The original inventory and the typed compiler companion retain their source
snapshots. This is the current inventory of explicitly corrected endpoints,
including the conservative generated judgment presentation parameterized by
an arbitrary independently sized closed theory. Counts are metadata, not a
mathematical proof audit.

The behavioral endpoint is the proved deterministic correspondence with
complete availability guards. The displayed selected-edge product in
Definition 3 is not identified with general GSOS. Ordinary finite-premise
rules have the separately proved finite-observation qualification; finite
action carriers recover every deterministic law. The paper's proposed general
internal-relation extension and language-specific binding/name-passing
admission are separate construction targets, not unfinished parts of this
corrected deterministic correspondence.

The typed application rule uses an argument of the function's domain `A`;
the printed Pi-elimination premise instead says `u : B`. The independently
generated rules use the coherent typed premise and retain complete dependent
application. The paper's printed mu/nu encodings are separate from this
generated judgment, substitution and interpretation endpoint. Neither their
literal fixed-point claims nor corrected fixed-point encodings receive credit
from this inventory companion.

The original-category functor into the full generated mixed-context quotient
is faithful. Its complete presheaf interpretation is naturally isomorphic to
Yoneda, and earns full faithfulness, finite-limit preservation and canonical
closed comparison. These semantic isomorphisms do not identify independently
chosen syntactic type codes. Arbitrary pseudo initiality, internal universes,
equality/quotient type formation and unrestricted runtime observations remain
separate extensions.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.NTTGeneratedTheoryClaimQualification

open NTTClaimTracker

def behaviorClaim : NTTClaim :=
  ⟨"Def 3 / Thm 4",
    "Corrected deterministic behavior correspondence: complete availability-guarded schemas classify natural GSOS laws; finite-premise rules classify the finitely observed laws",
    "DeterministicGSOSCorrespondence.guardedLawEquiv constructs both directions between independently authored complete guarded schemas and actual natural laws F(Id x B) -> B T for finite-arity many-sorted signatures and arbitrary action carriers. fromLaw_toLaw and toLaw_fromLaw prove both roundtrips, including variable identifications. DeterministicGSOSFinitePresentation.admits_law_iff_consistent earns deterministic consistency of overlapping finite-premise clauses, law_unique proves denotation uniqueness, and DeterministicGSOSRuleQuotient.ConsistentPresentation.equivalence identifies their denotational classes with precisely the finitely-successfully-observed laws. The separate image-finite equivalence uses uniform finite observation; finite action carriers recover every law. GSOSNativeGuard.completeGuard_iff compares the actual native availability and Heyting-negative guard with the independently supplied Boolean profile under availability reflection and an inhabited origin carrier. Native firing occurrences retain every selected positive premise and authored origin. PositiveGSOSControls distinguishes active and passive premise domains; DeterministicGSOSControls proves that one selected edge cannot recover negative availability. Infinite-action controls separate complete guards, ordinary finite-premise rules and uniformly finite observation. The original displayed edge product needs this explicit guard correction. Theorem 4 is asserted without proof and its general internal-relation connection is proposed for future exploration; that broader claim is not granted by this corrected deterministic endpoint. Nondeterministic and language-specific binding/name-passing comparisons have their own construction and operational obligations",
    .proven⟩

def syntaxClaim : NTTClaim :=
  ⟨"Sec 4 (syntax)",
    "Generated higher-order dependent native syntax, with substitution coherence and its interpretation",
    "TheoryEquationDeclarations and TheoryEquationDerivations independently add typed equation occurrences, actual side-formation premises and authored origins to the complete 137-rule native judgment signature. TheoryEquationSoundness derives interpretation of every extended tree in independently sized arbitrary qualified local CwF/predicate models from local constructor/header laws and per-declaration evaluator equality. TheoryEquationContextualCategory, Quotient, Fibres and Cwf construct the whole generated mixed-context quotient and its type/term/predicate families, comprehension and substitution; Assumptions, Heyting and PredicateAction retain guarded contexts and their logical action. EvidenceExtraction, Interpretation and SemanticSubstitution derive complete dependent section, predicate and typed-substitution readouts through all generated equations. TheoryRepresentableEquations independently presents original identity/composition and indexed projection; Admission earns each equation in the actual presheaf model. Conservativity constructs the actual faithful original-category functor and reflects every original arrow equation after full native rule closure. StructuralComparison earns the whole Yoneda natural isomorphism of its complete interpretation, hence full faithfulness and canonical finite-limit/closed comparisons with complete product projections and function-domain calibration. Families supplies TS/TO/TE, the full indexed original-arrow family and its retained forget section, with type/term/predicate substitution. TheoryGeneratedPresentation covers independent original object/hom universes through the actual common-bound equivalence. Controls retain nonidentity original arrows, a genuine varying Fin(n+1) section, empty versus inhabited indexed fibres, rejected false equations and distinct authored origins. The typed Pi-elimination argument is A, correcting the printed B premise. Printed mu/nu expressions, arbitrary pseudo initiality, strict equality of chosen type codes and universe/equality/quotient type rules are outside this generated judgment endpoint",
    .proven⟩

def claimList : List NTTClaim :=
  NTTGeneratedCompilerClaimQualification.claimList.map fun claim =>
    if claim.loc = "Sec 4 (syntax)" then syntaxClaim
    else if claim.loc = "Def 3 / Thm 4" then behaviorClaim else claim

def remaining : List NTTClaim :=
  claimList.filter fun claim =>
    claim.status = .partiallyFormalized || claim.status = .notFormalized

def countByStatus (status : NTTClaimStatus) : Nat :=
  (claimList.filter fun claim => claim.status = status).length

/-- Every imported paper endpoint is retained. -/
theorem paper_endpoints_unchanged :
    claimList.map (·.loc) = NTTGeneratedCompilerClaimQualification.claimList.map (·.loc) := by
  decide

/-- The generated syntax and corrected deterministic rows are the only replacements. -/
theorem other_rows_unchanged :
    claimList.filter (fun claim =>
      claim.loc != "Sec 4 (syntax)" && claim.loc != "Def 3 / Thm 4") =
      NTTGeneratedCompilerClaimQualification.claimList.filter
        (fun claim => claim.loc != "Sec 4 (syntax)" && claim.loc != "Def 3 / Thm 4") := by
  have unchanged (claims : List NTTClaim) :
      (claims.map fun claim =>
        if claim.loc = "Sec 4 (syntax)" then syntaxClaim
        else if claim.loc = "Def 3 / Thm 4" then behaviorClaim else claim).filter
          (fun claim => claim.loc != "Sec 4 (syntax)" && claim.loc != "Def 3 / Thm 4") =
        claims.filter (fun claim =>
          claim.loc != "Sec 4 (syntax)" && claim.loc != "Def 3 / Thm 4") := by
    induction claims with
    | nil => rfl
    | cons claim rest ih =>
      by_cases selected : claim.loc = "Sec 4 (syntax)"
      · have replacement : syntaxClaim.loc = "Sec 4 (syntax)" := rfl
        simp [selected, replacement, ih]
      · by_cases behavioral : claim.loc = "Def 3 / Thm 4"
        · have replacement : behaviorClaim.loc = "Def 3 / Thm 4" := rfl
          simp [behavioral, replacement, ih]
        · simp [selected, behavioral, ih]
  exact unchanged NTTGeneratedCompilerClaimQualification.claimList

/-- Every endpoint is closed at its explicitly stated corrected scope. -/
theorem remaining_locations : remaining.map (·.loc) = [] := by
  decide

/-- Counts of qualified inventory rows, independent of declaration audits. -/
theorem proven_count : countByStatus .proven = 21 := by
  decide

theorem partial_count : countByStatus .partiallyFormalized = 0 := by
  decide

theorem missing_count : countByStatus .notFormalized = 0 := by
  decide

#check @Mettapedia.OSLF.DeterministicGSOS.guardedLawEquiv
#check @Mettapedia.OSLF.DeterministicGSOS.fromLaw_toLaw
#check @Mettapedia.OSLF.DeterministicGSOS.toLaw_fromLaw
#check @Mettapedia.OSLF.DeterministicGSOS.FinitePresentation.admits_law_iff_consistent
#check @Mettapedia.OSLF.DeterministicGSOS.ConsistentPresentation.equivalence

end Mettapedia.OSLF.Framework.NTTGeneratedTheoryClaimQualification

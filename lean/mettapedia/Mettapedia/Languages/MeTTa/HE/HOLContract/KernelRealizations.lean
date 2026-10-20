import Mettapedia.Languages.MeTTa.HE.HOLContract.Megalodon
import Mettapedia.Languages.MeTTa.HE.HOLContract.MM0
import Mettapedia.Languages.MeTTa.HE.HOLContract.Guest
import Mettapedia.Languages.MM0.Kernel.ProofComplexity

/-!
# Agreement and structural cost of the three flat-contract realizations

The HOL contract, Mathdata type checking and MM0 sort checking realize the
same existing first-order HE relation. This does not identify their proof
logics, conversion rules, or runtime declaration readers.

For the instantiated applicative term, Mathdata preserves the term-node
count. MM0 uses an explicit application constructor and has exactly twice
the source node count minus one. These are tree representation counts, not
running-time bounds: they exclude signature construction, type annotations,
index bit lengths, equality cost and sharing. No native speed ranking follows
from them alone.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.HOLContract.KernelRealizations

open Mettapedia.Languages.MeTTa.OSLFCore
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.NamedElaboration


theorem megalodon_iff_mm0 (space : Space) (expression type : Atom) :
    Megalodon.Realized space expression type ↔ MM0.Realized space expression type :=
  (Megalodon.firstOrder_iff_realized _ _ _).symm.trans (MM0.firstOrder_iff_realized _ _ _)

theorem three_way_agreement (space : Space) (expression type : Atom) :
    (Typed space expression type ↔ Megalodon.Realized space expression type) ∧
    (Typed space expression type ↔ MM0.Realized space expression type) :=
  ⟨Megalodon.hol_contract_iff_realized _ _ _, MM0.hol_contract_iff_realized _ _ _⟩

/-- The existing HOL Light source checker and the two finite native-syntax
realizations agree on each admitted elaborated term. The HOL signature and
naming conditions remain visible; no claim about a native reader is assumed. -/
theorem guest_checker_agreement {naming : Guest.Naming} {space : Space}
    {leaves : Atom → Prop}
    {signature : Mettapedia.Languages.OpenTheory.SignatureFormation.Signature}
    (checker : Guest.CheckerSignature naming space leaves signature)
    {term : ContractTerm} (applicative : Applicative term)
    (wellNamed : Guest.WellNamed space leaves term)
    {type : Ty Atom} (reading : Guest.ContractReading type) :
    (Guest.GuestTyped signature (Guest.guestTerm naming term) (Guest.guestTy naming type) ↔
      ∃ names types, FiniteApplicative.Support (nameType space) names types ∧
        Mettapedia.Languages.Megalodon.FiniteApplicative.check names types term type = true) ∧
    (Guest.GuestTyped signature (Guest.guestTerm naming term) (Guest.guestTy naming type) ↔
      ∃ names types certificate, FiniteApplicative.Support (nameType space) names types ∧
        Mettapedia.Languages.MM0.Translation.FiniteApplicative.check
          names types term type certificate = true) := by
  have hol := Guest.guestTyped_iff checker applicative wellNamed reading
  exact ⟨hol.symm.trans (Mettapedia.Languages.Megalodon.FiniteApplicative.typing_iff _ _ _),
    hol.symm.trans (Mettapedia.Languages.MM0.Translation.FiniteApplicative.typing_iff _ _ _)⟩

/-- Count term nodes without charging names or type annotations. -/
def sourceNodes {Base Variable Constant : Type} : NamedTerm Base Variable Constant → Nat
  | .variable _ | .constant _ | .top | .bottom => 1
  | .app left right | .and left right | .or left right | .imp left right | .equal left right =>
      1 + sourceNodes left + sourceNodes right
  | .lam _ _ body | .not body | .forallE _ _ body | .existsE _ _ body => 1 + sourceNodes body

def mathdataNodes : Mettapedia.Languages.Megalodon.MathdataKernel.Tm → Nat
  | .db _ | .named _ | .prim _ => 1
  | .app left right | .imp left right => 1 + mathdataNodes left + mathdataNodes right
  | .lam _ body | .all _ body | .typeApp body _ | .typeLam body | .typeAll body =>
      1 + mathdataNodes body

theorem mathdata_node_count {source : Mettapedia.Languages.Megalodon.ApplicativeTyping.Source}
    {target : Mettapedia.Languages.Megalodon.MathdataKernel.Tm} (translated : Mettapedia.Languages.Megalodon.ApplicativeTyping.translate source = some target) :
    mathdataNodes target = sourceNodes source := by
  induction source generalizing target with
  | constant index =>
      simp only [Mettapedia.Languages.Megalodon.ApplicativeTyping.translate, Option.some.injEq] at translated
      subst target
      rfl
  | app function argument functionIH argumentIH =>
      cases functionFound : Mettapedia.Languages.Megalodon.ApplicativeTyping.translate function with
      | none => simp [Mettapedia.Languages.Megalodon.ApplicativeTyping.translate, functionFound] at translated
      | some functionTarget =>
          cases argumentFound : Mettapedia.Languages.Megalodon.ApplicativeTyping.translate argument with
          | none => simp [Mettapedia.Languages.Megalodon.ApplicativeTyping.translate, functionFound, argumentFound] at translated
          | some argumentTarget =>
              have same : Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app functionTarget argumentTarget = target := by
                simpa [Mettapedia.Languages.Megalodon.ApplicativeTyping.translate, functionFound, argumentFound] using translated
              subst target
              simp only [mathdataNodes, sourceNodes, functionIH functionFound, argumentIH argumentFound]
  | _ => simp [Mettapedia.Languages.Megalodon.ApplicativeTyping.translate] at translated

theorem mm0_node_count {Base : Type} [DecidableEq Base]
    (constants sorts : List (Ty Base)) (certificate : Mettapedia.Languages.MM0.Translation.ApplicativeTyping.Certificate Base)
    {target : Mettapedia.Languages.MM0.Kernel.Preterm}
    (translated : Mettapedia.Languages.MM0.Translation.ApplicativeTyping.compile constants sorts certificate = some target) :
    target.size + 1 = 2 * sourceNodes certificate.erase := by
  induction certificate generalizing target with
  | constant index =>
      simp only [Mettapedia.Languages.MM0.Translation.ApplicativeTyping.compile] at translated
      split at translated
      · have same := Option.some.inj translated
        subst target
        rfl
      · contradiction
  | app domain result function argument functionIH argumentIH =>
      simp only [Mettapedia.Languages.MM0.Translation.ApplicativeTyping.compile] at translated
      split at translated
      · cases functionFound : Mettapedia.Languages.MM0.Translation.ApplicativeTyping.compile constants sorts function with
        | none => simp [functionFound] at translated
        | some functionTarget =>
            cases argumentFound : Mettapedia.Languages.MM0.Translation.ApplicativeTyping.compile constants sorts argument with
            | none => simp [functionFound, argumentFound] at translated
            | some argumentTarget =>
                have same : Mettapedia.Languages.MM0.Kernel.Preterm.app (.app
                    (.term (constants.length + sorts.idxOf (.arr domain result))) functionTarget)
                    argumentTarget = target := by
                  simpa [functionFound, argumentFound] using translated
                subst target
                have functionCount := functionIH functionFound
                have argumentCount := argumentIH argumentFound
                simp only [Mettapedia.Languages.MM0.Kernel.Preterm.size,
                  Mettapedia.Languages.MM0.Translation.ApplicativeTyping.Certificate.erase, sourceNodes]
                omega
      · contradiction

#print axioms three_way_agreement
#print axioms guest_checker_agreement
#print axioms mathdata_node_count
#print axioms mm0_node_count

end Mettapedia.Languages.MeTTa.HE.HOLContract.KernelRealizations

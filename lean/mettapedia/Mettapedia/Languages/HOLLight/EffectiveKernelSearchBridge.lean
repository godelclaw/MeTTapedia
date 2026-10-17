import Mettapedia.GSLT.LanguageDef.EffectiveKernelSearch
import Mettapedia.Languages.HOLLight.EffectiveEvidenceCompilation

/-!
# Fair partial-checker search produces independently checked HOL evidence

The supplied checking code, claim and source certificate remain quoted data
in one fixed finite HOL hosting theory. Successful bounded evidence invokes
the existing executable extractor and original shared HOL graph compiler.
Arbitrary accepted target proofs reflect to acceptance by that same supplied
code, rather than merely to the existence of our compiler's output.

To conclude derivability or model truth for a particular source language,
its code-to-source authority must be proved separately. This bridge cannot
authorize an unqualified checker, a changed declaration history, or an
unquoted conclusion. No polynomial artifact or extraction-clock bound is
asserted for this general route.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.EffectiveKernelSearchBridge

open Nat.Partrec (Code)
open Mettapedia.GSLT.LanguageDef.EffectiveKernelSearch
open Mettapedia.GSLT.LanguageDef.PartialRecursive
open Mettapedia.Languages.HOLLight.EffectiveEvidenceHosting
open Mettapedia.Languages.OpenTheory

def compileEvidence (code : Code) (claim : Nat) (evidence : ClockedEvidence) :
    Option ProofSystem.Certificate :=
  EffectiveEvidenceCompilation.compile evidence.2 code (Nat.pair claim evidence.1) 1

theorem clocked_is_original_evidence (code : Code) (claim : Nat)
    (evidence : ClockedEvidence) :
    clockedCheck code claim evidence =
      Mettapedia.Computability.UniversalEffectiveEvidence.check
        code (Nat.pair claim evidence.1) 1 evidence.2 := by
  simp only [clockedCheck, Mettapedia.Computability.UniversalEffectiveEvidence.check,
    Option.mem_def]

theorem compile_iff_clocked (code : Code) (claim : Nat) (evidence : ClockedEvidence) :
    (∃ graph, compileEvidence code claim evidence = some graph) ↔
      clockedCheck code claim evidence = true := by
  rw [clocked_is_original_evidence]
  exact EffectiveEvidenceCompilation.compile_iff_evidence evidence.2 code
    (Nat.pair claim evidence.1) 1

/-- The concrete output earns acceptance by the independent original HOL
kernel, with empty hypotheses and the exact quoted evaluation conclusion. -/
theorem emitted_kernel_checked (code : Code) (claim : Nat) (evidence : ClockedEvidence)
    {graph : ProofSystem.Certificate}
    (emitted : compileEvidence code claim evidence = some graph) :
    ∃ out, (ProofSystem.checker (InferenceHosting.policy universalRules)).check
        out graph = true ∧ out.sequent.hyp = ∅ ∧
      out.sequent.concl = InferenceCompiler.compileClaim
        (Judgment.eval code (Nat.pair claim evidence.1) 1).pattern :=
  EffectiveEvidenceCompilation.compile_kernel_checked evidence.2 code
    (Nat.pair claim evidence.1) 1 emitted

theorem original_acceptance_iff_compilation (code : Code) (claim certificate : Nat) :
    Accepted code claim certificate ↔
      ∃ bound graph, compileEvidence code claim (certificate, bound) = some graph := by
  rw [← clocked_iff]
  constructor
  · rintro ⟨bound, accepted⟩
    obtain ⟨graph, emitted⟩ := (compile_iff_clocked code claim (certificate, bound)).mpr accepted
    exact ⟨bound, graph, emitted⟩
  · rintro ⟨bound, graph, emitted⟩
    exact ⟨bound, (compile_iff_clocked code claim _).mp ⟨graph, emitted⟩⟩

theorem found_emits_graph (code : Code) (claim : Nat) (evidence : ClockedEvidence)
    (found : evidence ∈ search code claim) :
    ∃ graph, compileEvidence code claim evidence = some graph :=
  (compile_iff_clocked code claim evidence).mpr (search_sound code claim evidence found)

/-- This equivalence includes arbitrary original HOL certificates in the
fixed hosting theory; it is stronger than validating only emitted graphs. -/
theorem search_iff_target_proof (code : Code) (claim : Nat) :
    (search code claim).Dom ↔
      ∃ certificate, TargetChecked (.eval code (Nat.pair claim certificate) 1) := by
  rw [search_dom_iff]
  constructor
  · rintro ⟨certificate, accepted⟩
    exact ⟨certificate, (target_checked_iff _).mpr accepted⟩
  · rintro ⟨certificate, checked⟩
    exact ⟨certificate, (target_checked_iff _).mp checked⟩

/-- Code-to-source adequacy remains explicit. Under this qualification,
the same fixed HOL theory faithfully presents the source theorem set. -/
theorem source_iff_target_proof (code : Code) (Derivable : Nat → Prop)
    (authority : ∀ claim, (∃ certificate, Accepted code claim certificate) ↔ Derivable claim)
    (claim : Nat) : Derivable claim ↔
      ∃ certificate, TargetChecked (.eval code (Nat.pair claim certificate) 1) :=
  (authority claim).symm.trans
    ((search_dom_iff code claim).symm.trans (search_iff_target_proof code claim))

theorem wrong_bounded_evidence_emits_nothing (code : Code) (claim : Nat)
    (evidence : ClockedEvidence) (refused : clockedCheck code claim evidence = false) :
    compileEvidence code claim evidence = none :=
  EffectiveEvidenceCompilation.compile_refused evidence.2 code (Nat.pair claim evidence.1) 1
    ((clocked_is_original_evidence code claim evidence) ▸ refused)

namespace Controls

theorem right_has_emitted_graph :
    ∃ graph, compileEvidence .right 0 (1, 10) = some graph :=
  (compile_iff_clocked .right 0 (1, 10)).mpr
    Mettapedia.GSLT.LanguageDef.EffectiveKernelSearch.Controls.right_accepted

theorem wrong_source_result_refused : compileEvidence .right 0 (2, 10) = none :=
  wrong_bounded_evidence_emits_nothing .right 0 (2, 10)
    Mettapedia.GSLT.LanguageDef.EffectiveKernelSearch.Controls.wrong_result_refused

theorem insufficient_bound_refused : compileEvidence .right 0 (1, 0) = none :=
  wrong_bounded_evidence_emits_nothing .right 0 (1, 0)
    Mettapedia.GSLT.LanguageDef.EffectiveKernelSearch.Controls.insufficient_bound_unknown

end Controls

end Mettapedia.Languages.HOLLight.EffectiveKernelSearchBridge

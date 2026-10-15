import Mettapedia.GSLT.LanguageDef.InitialRuleClosureAuthority
import Mettapedia.GSLT.Logic.PropositionalResolutionAuthority

/-!
# Checker authority for propositional resolution

The native kernel lives in `PropositionalResolutionAuthority` (rules, replay,
`empty_iff_unsat`). This module only hosts that kernel as a qualified
SemanticService rule system: least closure is scope, Boolean consequence is meaning,
derivation trees are certificates. Foundation is not used.

Formerly `Mettapedia.Logic.Bridges.PropositionalResolutionNIK`, part of the native inference kernel (NIK) development of 2026-08-11 to 2026-10-08; renamed to its subject name on 2026-10-08.
The namespace was `Mettapedia.Logic.Bridges.PropositionalResolutionNIK`; it is now `Mettapedia.Logic.Bridges.PropositionalResolutionAuthority`.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Bridges.PropositionalResolutionAuthority

open Mettapedia.Logic
open Mettapedia.GSLT.LanguageDef.InitialRuleClosureAuthority
open Mettapedia.GSLT.Logic.PropositionalFormula
open Mettapedia.GSLT.Logic.PropositionalResolution

def resolutionKernel (Γ : CNF) : QualifiedRuleSystem Clause where
  rules := ResRule Γ
  witness := resWitness Γ
  Meaning := Consequence Γ
  rules_sound := fun _ _ rule hyp => resRule_sound rule hyp

theorem accepted_means_consequence (Γ : CNF) (c : Clause)
    (certificate : Derivation Clause (resWitness Γ).W)
    (accepted :
      ((resolutionKernel Γ).contract.checker ()).check c certificate = true) :
    Consequence Γ c :=
  QualifiedRuleSystem.accepted_meaning (resolutionKernel Γ) c certificate accepted

theorem empty_accepted_unsat (Γ : CNF)
    (certificate : Derivation Clause (resWitness Γ).W)
    (accepted :
      ((resolutionKernel Γ).contract.checker ()).check [] certificate = true) :
    Unsat Γ :=
  (empty_iff_unsat Γ).mp
    (((resolutionKernel Γ).contract.scopeAuthority ()).sound [] certificate accepted)

theorem unsat_has_accepted_empty (Γ : CNF) (h : Unsat Γ) :
    ∃ certificate : Derivation Clause (resWitness Γ).W,
      ((resolutionKernel Γ).contract.checker ()).check [] certificate = true := by
  obtain ⟨certificate, valid, concludes⟩ := replay_empty_of_unsat Γ h
  refine ⟨certificate, ?_⟩
  unfold QualifiedRuleSystem.contract QualifiedRuleSystem.checker
  simp [Mettapedia.OSLF.Framework.InitialModalSchema.replayChecker]
  exact ⟨valid, concludes⟩

#print axioms accepted_means_consequence
#print axioms empty_accepted_unsat
#print axioms unsat_has_accepted_empty

end Mettapedia.Logic.Bridges.PropositionalResolutionAuthority

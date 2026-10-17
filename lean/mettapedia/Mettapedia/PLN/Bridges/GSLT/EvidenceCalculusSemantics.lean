import Mettapedia.PLN.Bridges.GSLT.EvidenceCalculusModule
import Mettapedia.PLN.WorldModel.EvidenceContracts

/-!
# The revision rule of the evidence calculus is sound for identified observations

`EvidenceCalculusModule` presents the PLN evidence calculus as module data.
This module gives its revision fragment a semantics over identified
observations and proves that the `revise` schema read from the module is sound
for it, with its contract premise, and unsound without it.

An interpretation assigns
- to each query variable a predicate on worlds,
- to each evidence variable a ledger (a finite set of observation identities)
  and the count summary a reasoner stores for it.

`Evidence q e` means that the stored summary of `e` is the evidence its
observations give `q`; `Holds (disjoint e₁ e₂)` means that the two sets of
observations are disjoint.  Revision unions ledgers and adds summaries.

The soundness theorem is the ledger contract of
`Mettapedia.PLN.WorldModel.EvidenceContracts` read through the module: additive
revision is exact for disjoint ledgers.  The countermodel is the overlap that
additive revision counts twice.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.Bridges.GSLT.EvidenceCalculusSemantics

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.PLN.Bridges.GSLT.EvidenceCalculusModule
open Mettapedia.PLN.WorldModel.EvidenceContracts
open Mettapedia.PLN.WorldModel.EvidenceSpaces

/-- An interpretation of the metavariables of the evidence calculus. -/
structure Interpretation (Id W : Type) where
  query : String → W → Bool
  ledger : String → Finset Id
  summary : String → Evidence ℕ

namespace Interpretation

variable {Id W : Type} [DecidableEq Id]

/-- Denotation of a query pattern. -/
def queryOf (ρ : Interpretation Id W) : Pattern → Option (W → Bool)
  | .fvar q => some (ρ.query q)
  | _ => none

/-- The observations an evidence pattern stands for. -/
def ledgerOf (ρ : Interpretation Id W) : Pattern → Option (Finset Id)
  | .fvar e => some (ρ.ledger e)
  | .apply "revise" [.fvar a, .fvar b] => some (ρ.ledger a ∪ ρ.ledger b)
  | _ => none

/-- The count summary an evidence pattern stands for. -/
def summaryOf (ρ : Interpretation Id W) : Pattern → Option (Evidence ℕ)
  | .fvar e => some (ρ.summary e)
  | .apply "revise" [.fvar a, .fvar b] => some (ρ.summary a + ρ.summary b)
  | _ => none

/-- Meaning of the evidence and contract judgments of the revision fragment. -/
def Holds (world : Id → W) (ρ : Interpretation Id W) : Pattern → Prop
  | .apply "Evidence" [q, e] =>
      ∃ φ L s, ρ.queryOf q = some φ ∧ ρ.ledgerOf e = some L ∧ ρ.summaryOf e = some s ∧
        s = ledgerEvidence world φ L
  | .apply "Holds" [.apply "disjoint" [a, b]] =>
      ∃ L₁ L₂, ρ.ledgerOf a = some L₁ ∧ ρ.ledgerOf b = some L₂ ∧ Disjoint L₁ L₂
  | _ => False

end Interpretation

open Interpretation

/-- A rule schema is sound for an interpretation class when every instance whose
premises hold has a conclusion that holds. -/
def SoundFor (r : RuleSchema) : Prop :=
  ∀ (Id W : Type) [DecidableEq Id] (world : Id → W) (ρ : Interpretation Id W),
    (∀ p ∈ r.premises, ρ.Holds world p) → ρ.Holds world r.conclusion

/-- The `revise` schema of the module, with its disjointness contract, is sound
for identified observations. -/
theorem revise_sound : ∀ r ∈ evidenceCalculus.rules, r.id = ⟨"revise"⟩ → SoundFor r := by
  intro r hr hid
  simp only [evidenceCalculus, evidenceRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [rule, RuleId.mk.injEq, String.reduceEq] at hid
  intro Id W _ world ρ hprem
  simp only [rule, ev, holds, fv, app, List.map, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at hprem
  obtain ⟨⟨φ₁, L₁, s₁, hq₁, hL₁, hs₁, he₁⟩, ⟨φ₂, L₂, s₂, hq₂, hL₂, hs₂, he₂⟩,
    ⟨D₁, D₂, hD₁, hD₂, hdisj⟩⟩ := hprem
  simp only [queryOf, ledgerOf, summaryOf, Option.some.injEq] at hq₁ hL₁ hs₁ hq₂ hL₂ hs₂ hD₁ hD₂
  subst hq₁ hL₁ hs₁ hq₂ hL₂ hs₂ hD₁ hD₂
  refine ⟨ρ.query "q", ρ.ledger "e1" ∪ ρ.ledger "e2", ρ.summary "e1" + ρ.summary "e2",
    rfl, rfl, rfl, ?_⟩
  rw [ledgerEvidence_union_of_disjoint world _ hdisj, he₁, he₂]

/-- Without its contract premise the revision schema is unsound: one
observation recorded in both ledgers is counted twice. -/
theorem revise_without_contract_unsound :
    ¬ SoundFor (rule "revise" ["q", "e1", "e2"]
        [ev (fv "q") (fv "e1"), ev (fv "q") (fv "e2")]
        (ev (fv "q") (app "revise" [fv "e1", fv "e2"]))) := by
  intro sound
  let ρ : Interpretation Unit Unit :=
    { query := fun _ _ => true
      ledger := fun _ => {()}
      summary := fun _ => ledgerEvidence (fun _ : Unit => ()) (fun _ => true) {()} }
  have h := sound Unit Unit (fun _ => ()) ρ (by
    simp only [rule, ev, fv, app, List.map, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    exact ⟨⟨_, _, _, rfl, rfl, rfl, rfl⟩, ⟨_, _, _, rfl, rfl, rfl, rfl⟩⟩)
  obtain ⟨φ, L, s, hq, hL, hs, he⟩ := h
  simp only [fv, app, queryOf, ledgerOf, summaryOf, Option.some.injEq, ρ] at hq hL hs
  subst hq hL hs
  have := congrArg Evidence.pos he
  simp [ledgerEvidence, sampleEvidence, Evidence.positive] at this

end Mettapedia.PLN.Bridges.GSLT.EvidenceCalculusSemantics

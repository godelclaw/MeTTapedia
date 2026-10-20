import Mettapedia.PLN.Bridges.GSLT.EvidenceCalculusModule
import Mettapedia.PLN.WorldModel.EvidenceContracts

/-!
# Semantics of the PLN evidence calculus

`EvidenceCalculusModule` presents the PLN evidence calculus as module data.
This module gives each of its nine rules a semantics and proves the rule, as
read from the module, sound under its contract.  Where a rule has a contract,
a countermodel shows the contract is needed; where it has none, the docstring
says why.

A rule schema is sound for a reading of the judgments (`SchemaSound`) when every
model that makes its premises true makes its conclusion true.  The rules live
in four settings, one per kind of observation:

| Setting | Rules | Judgment meaning |
|---|---|---|
| `Ledger`: identified observations | `revise`, `revise-unknown-overlap`, `negate`, `conjoin-one-world`, `read-strength`, `read-interval` | the counts of a finite set of observations |
| `Paired`: separately drawn samples | `conjoin-independent` | the counts of a bag of worlds |
| `Reports`: testimony about a hypothesis | `fuse` | the likelihoods of a report under the hypothesis and its negation |
| `Population`: one bag of worlds | `deduce` | frequencies and conditional frequencies |

The module gives these settings distinct judgment heads and value sorts.
Counts cannot serve as report likelihoods, and an observation readout cannot
serve as a population frequency without an explicit semantic bridge.
`EvidenceTermComposition` strengthens this schema interpretation to recursive
terms and proves semantic soundness of the instantiated open proof checker.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.Bridges.GSLT.EvidenceCalculusSemantics

open Mettapedia.GSLT.LanguageDef.FirstOrderCalculus
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.SemanticSettings
open Mettapedia.PLN.Bridges.GSLT.EvidenceCalculusModule
open Mettapedia.PLN.WorldModel.EvidenceContracts
open Mettapedia.PLN.WorldModel.EvidenceSpaces
open Mettapedia.PLN.WorldModel.EvidenceSpaces.Evidence

/-! ## Identified observations -/

namespace Ledger

/-- An interpretation of the metavariables over identified observations: a
predicate on worlds for each query variable, and for each evidence variable
the observations it records and the counts a reasoner stores for it. -/
structure Interpretation (Id W : Type) where
  query : String → W → Bool
  ledger : String → Finset Id
  summary : String → Evidence ℕ
  /-- The prior strength of the imprecise Dirichlet model behind `interval`. -/
  priorStrength : ℝ
  priorStrength_pos : 0 < priorStrength

/-- A model: observations with their worlds, and an interpretation. -/
structure Model where
  Id : Type
  W : Type
  [decEq : DecidableEq Id]
  world : Id → W
  interp : Interpretation Id W

attribute [instance] Model.decEq

namespace Interpretation

variable {Id W : Type} [DecidableEq Id]

/-- Denotation of a query pattern. -/
def queryOf (ρ : Interpretation Id W) : Pattern → Option (W → Bool)
  | .fvar q => some (ρ.query q)
  | .apply "not" [.fvar q] => some (fun w => !ρ.query q w)
  | .apply "and" [.fvar a, .fvar b] => some (fun w => ρ.query a w && ρ.query b w)
  | _ => none

/-- The observations an evidence pattern stands for. -/
def ledgerOf (ρ : Interpretation Id W) : Pattern → Option (Finset Id)
  | .fvar e => some (ρ.ledger e)
  | .apply "revise" [.fvar a, .fvar b] => some (ρ.ledger a ∪ ρ.ledger b)
  | .apply "lowerMerge" [.fvar a, .fvar b] => some (ρ.ledger a ∪ ρ.ledger b)
  | .apply "swap" [.fvar e] => some (ρ.ledger e)
  | _ => none

/-- The count summary an evidence pattern stands for. -/
def summaryOf (ρ : Interpretation Id W) : Pattern → Option (Evidence ℕ)
  | .fvar e => some (ρ.summary e)
  | .apply "revise" [.fvar a, .fvar b] => some (ρ.summary a + ρ.summary b)
  | .apply "lowerMerge" [.fvar a, .fvar b] =>
      some ⟨max (ρ.summary a).pos (ρ.summary b).pos, max (ρ.summary a).neg (ρ.summary b).neg⟩
  | .apply "swap" [.fvar e] => some (against (ρ.summary e))
  | _ => none

/-- A readout value: the set of strengths it allows and the observations it is
about. -/
noncomputable def valueOf (ρ : Interpretation Id W) : Pattern → Option (Set ℝ × Finset Id)
  | .apply "strength" [.fvar e] => some ({realStrength (ρ.summary e)}, ρ.ledger e)
  | .apply "interval" [.fvar e] =>
      some (Set.Icc
          (Mettapedia.ProbabilityTheory.ImpreciseProbability.WalleyBinaryIDM.lowerEndpoint
            (ρ.summary e).pos (ρ.summary e).neg ρ.priorStrength)
          (Mettapedia.ProbabilityTheory.ImpreciseProbability.WalleyBinaryIDM.upperEndpoint
            (ρ.summary e).pos (ρ.summary e).neg ρ.priorStrength),
        ρ.ledger e)
  | .apply "frechet" [.fvar a, .fvar b] =>
      some (Set.Icc (max 0 (realStrength (ρ.summary a) + realStrength (ρ.summary b) - 1))
          (min (realStrength (ρ.summary a)) (realStrength (ρ.summary b))),
        ρ.ledger a ∪ ρ.ledger b)
  | _ => none

/-- Meaning of the judgments over identified observations:
- `ObservationCounts q e`: the stored counts are the evidence the observations give `q`;
- `ObservationLowerBound q e`: they are at most that evidence;
- `LedgerHolds (disjoint e₁ e₂)`: no observation is recorded twice;
- `LedgerHolds (oneWorld e₁ e₂)`: both are counts over the same observations;
- `CountReadout q v`: the strength of `q` over the observations of `v` is allowed by `v`. -/
def Holds (world : Id → W) (ρ : Interpretation Id W) : Pattern → Prop
  | .apply "ObservationCounts" [q, e] =>
      ∃ φ L s, ρ.queryOf q = some φ ∧ ρ.ledgerOf e = some L ∧ ρ.summaryOf e = some s ∧
        s = ledgerEvidence world φ L
  | .apply "ObservationLowerBound" [q, e] =>
      ∃ φ L s, ρ.queryOf q = some φ ∧ ρ.ledgerOf e = some L ∧ ρ.summaryOf e = some s ∧
        s ≤ ledgerEvidence world φ L
  | .apply "LedgerHolds" [.apply "disjoint" [a, b]] =>
      ∃ L₁ L₂, ρ.ledgerOf a = some L₁ ∧ ρ.ledgerOf b = some L₂ ∧ Disjoint L₁ L₂
  | .apply "LedgerHolds" [.apply "oneWorld" [a, b]] =>
      ∃ L, ρ.ledgerOf a = some L ∧ ρ.ledgerOf b = some L
  | .apply "CountReadout" [q, v] =>
      ∃ φ S L, ρ.queryOf q = some φ ∧ ρ.valueOf v = some (S, L) ∧
        realStrength (ledgerEvidence world φ L) ∈ S
  | _ => False

end Interpretation

/-- The reading of judgments in a model. -/
def Model.holds (m : Model) : Pattern → Prop := m.interp.Holds m.world

end Ledger

open Ledger Ledger.Interpretation

/-- Two lemmas used to pick one rule out of the module. -/
private theorem rules_eq : evidenceCalculus.rules = evidenceRules := rfl

/-- The `revise` schema of the module, with its disjointness contract, is sound:
the stored counts of disjoint ledgers add up to the counts of their union. -/
theorem revise_sound :
    ∀ r ∈ evidenceCalculus.rules, r.id = ⟨"revise"⟩ → SchemaSound Ledger.Model.holds r := by
  intro r hr hid
  simp only [rules_eq, evidenceRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [rule, RuleId.mk.injEq, String.reduceEq] at hid
  intro m hprem
  simp only [Ledger.Model.holds, rule, observationCounts, ledgerHolds, fv, app, List.map, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, Interpretation.Holds] at hprem ⊢
  obtain ⟨⟨φ₁, L₁, s₁, hq₁, hL₁, hs₁, he₁⟩, ⟨φ₂, L₂, s₂, hq₂, hL₂, hs₂, he₂⟩,
    ⟨D₁, D₂, hD₁, hD₂, hdisj⟩⟩ := hprem
  simp only [queryOf, ledgerOf, summaryOf, Option.some.injEq] at hq₁ hL₁ hs₁ hq₂ hL₂ hs₂ hD₁ hD₂
  subst hq₁ hL₁ hs₁ hq₂ hL₂ hs₂ hD₁ hD₂
  refine ⟨_, _, _, rfl, rfl, rfl, ?_⟩
  rw [ledgerEvidence_union_of_disjoint m.world _ hdisj, he₁, he₂]

/-- Without its contract premise the revision schema is unsound: one
observation recorded in both ledgers is counted twice. -/
theorem revise_without_contract_unsound :
    ¬ SchemaSound Ledger.Model.holds (rule "revise" ["q", "e1", "e2"]
        [observationCounts (fv "q") (fv "e1"), observationCounts (fv "q") (fv "e2")]
        (observationCounts (fv "q") (app "revise" [fv "e1", fv "e2"]))) := by
  intro sound
  let ρ : Interpretation Unit Unit :=
    { query := fun _ _ => true
      ledger := fun _ => {()}
      summary := fun _ => ledgerEvidence (fun _ : Unit => ()) (fun _ => true) {()}
      priorStrength := 1
      priorStrength_pos := one_pos }
  have h := sound ⟨Unit, Unit, fun _ => (), ρ⟩ (by
    simp only [Ledger.Model.holds, rule, observationCounts, fv, app, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Interpretation.Holds]
    exact ⟨⟨_, _, _, rfl, rfl, rfl, rfl⟩, ⟨_, _, _, rfl, rfl, rfl, rfl⟩⟩)
  simp only [Ledger.Model.holds, rule, observationCounts, fv, app, Interpretation.Holds] at h
  obtain ⟨φ, L, s, hq, hL, hs, he⟩ := h
  simp only [queryOf, ledgerOf, summaryOf, Option.some.injEq, ρ] at hq hL hs
  subst hq hL hs
  have := congrArg Evidence.pos he
  simp [ledgerEvidence, sampleEvidence, Evidence.positive] at this

/-- Revision under unknown overlap needs no contract: the coordinatewise
maximum of two exact counts never exceeds the counts of the union of their
observations, whatever the overlap.  Its conclusion is an under-count. -/
theorem reviseUnknownOverlap_sound :
    ∀ r ∈ evidenceCalculus.rules, r.id = ⟨"revise-unknown-overlap"⟩ →
      SchemaSound Ledger.Model.holds r := by
  intro r hr hid
  simp only [rules_eq, evidenceRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [rule, RuleId.mk.injEq, String.reduceEq] at hid
  intro m hprem
  simp only [Ledger.Model.holds, rule, observationCounts, observationLowerBound, fv, app, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, Interpretation.Holds] at hprem ⊢
  obtain ⟨⟨φ₁, L₁, s₁, hq₁, hL₁, hs₁, he₁⟩, ⟨φ₂, L₂, s₂, hq₂, hL₂, hs₂, he₂⟩⟩ := hprem
  simp only [queryOf, ledgerOf, summaryOf, Option.some.injEq] at hq₁ hL₁ hs₁ hq₂ hL₂ hs₂
  subst hq₁ hL₁ hs₁ hq₂ hL₂ hs₂
  refine ⟨_, _, _, rfl, rfl, rfl, ?_⟩
  rw [he₁, he₂]
  exact (unknown_overlap_bounds m.world _ _ _).1

/-- The unknown-overlap revision cannot conclude exact evidence: two disjoint
single observations merge to two samples, while the maximum records one. -/
theorem reviseUnknownOverlap_exact_unsound :
    ¬ SchemaSound Ledger.Model.holds (rule "revise-unknown-overlap" ["q", "e1", "e2"]
        [observationCounts (fv "q") (fv "e1"), observationCounts (fv "q") (fv "e2")]
        (observationCounts (fv "q") (app "lowerMerge" [fv "e1", fv "e2"]))) := by
  intro sound
  let ρ : Interpretation (Fin 2) Unit :=
    { query := fun _ _ => true
      ledger := fun e => if e = "e1" then {0} else {1}
      summary := fun _ => ⟨1, 0⟩
      priorStrength := 1
      priorStrength_pos := one_pos }
  have h := sound ⟨Fin 2, Unit, fun _ => (), ρ⟩ (by
    simp only [Ledger.Model.holds, rule, observationCounts, fv, app, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Interpretation.Holds]
    refine ⟨⟨_, _, _, rfl, rfl, rfl, ?_⟩, ⟨_, _, _, rfl, rfl, rfl, ?_⟩⟩ <;>
      simp only [ρ] <;> ext <;> decide)
  simp only [Ledger.Model.holds, rule, observationCounts, fv, app, Interpretation.Holds] at h
  obtain ⟨φ, L, s, hq, hL, hs, he⟩ := h
  simp only [queryOf, ledgerOf, summaryOf, Option.some.injEq, ρ] at hq hL hs
  subst hq hL hs
  have := congrArg Evidence.pos he
  revert this
  decide

/-- Negation needs no contract: every observation decides the query, so the
same observations give the negation the swapped counts. -/
theorem negate_sound :
    ∀ r ∈ evidenceCalculus.rules, r.id = ⟨"negate"⟩ → SchemaSound Ledger.Model.holds r := by
  intro r hr hid
  simp only [rules_eq, evidenceRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [rule, RuleId.mk.injEq, String.reduceEq] at hid
  intro m hprem
  simp only [Ledger.Model.holds, rule, observationCounts, fv, app, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq, Interpretation.Holds] at hprem ⊢
  obtain ⟨φ, L, s, hq, hL, hs, he⟩ := hprem
  simp only [queryOf, ledgerOf, summaryOf, Option.some.injEq] at hq hL hs
  subst hq hL hs
  refine ⟨_, _, _, rfl, rfl, rfl, ?_⟩
  rw [ledgerEvidence_not, he]

/-- Reading the strength needs no contract: it is a function of the counts,
and the premise says the counts are exact. -/
theorem readStrength_sound :
    ∀ r ∈ evidenceCalculus.rules, r.id = ⟨"read-strength"⟩ → SchemaSound Ledger.Model.holds r := by
  intro r hr hid
  simp only [rules_eq, evidenceRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [rule, RuleId.mk.injEq, String.reduceEq] at hid
  intro m hprem
  simp only [Ledger.Model.holds, rule, observationCounts, countReadout, fv, app, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq, Interpretation.Holds] at hprem ⊢
  obtain ⟨φ, L, s, hq, hL, hs, he⟩ := hprem
  simp only [queryOf, ledgerOf, summaryOf, Option.some.injEq] at hq hL hs
  subst hq hL hs
  exact ⟨_, _, _, rfl, rfl, by rw [he]; rfl⟩

/-- Strength cannot be read from an under-count: one of two observations
recorded gives strength `1`, while the frequency over both is `1/2`.  This is
why the module separates `ObservationLowerBound` from `ObservationCounts`. -/
theorem readStrength_from_atLeast_unsound :
    ¬ SchemaSound Ledger.Model.holds (rule "read-strength" ["q", "e"]
        [observationLowerBound (fv "q") (fv "e")] (countReadout (fv "q") (app "strength" [fv "e"]))) := by
  intro sound
  let ρ : Interpretation (Fin 2) (Fin 2) :=
    { query := fun _ w => decide (w = 0)
      ledger := fun _ => {0, 1}
      summary := fun _ => ⟨1, 0⟩
      priorStrength := 1
      priorStrength_pos := one_pos }
  have h := sound ⟨Fin 2, Fin 2, id, ρ⟩ (by
    simp only [Ledger.Model.holds, rule, observationLowerBound, fv, app, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq, Interpretation.Holds]
    refine ⟨_, _, _, rfl, rfl, rfl, ?_⟩
    simp only [ρ]
    rw [le_def]
    decide)
  simp only [Ledger.Model.holds, rule, countReadout, fv, app, Interpretation.Holds] at h
  obtain ⟨φ, S, L, hq, hv, hmem⟩ := h
  simp only [queryOf, valueOf, Option.some.injEq, Prod.mk.injEq, ρ] at hq hv
  obtain ⟨rfl, rfl⟩ := hv
  subst hq
  rw [Set.mem_singleton_iff, ledgerEvidence_eq_ofSamples, realStrength_ofSamples] at hmem
  have count : count ((({0, 1} : Finset (Fin 2)).val.map id)) (fun w => decide (w = 0)) = 1 := by
    decide
  have card : Multiset.card ((({0, 1} : Finset (Fin 2)).val.map id)) = 2 := by decide
  rw [count, card] at hmem
  simp [realStrength, strength, Evidence.total] at hmem

/-- Reading the credal interval needs no contract: the imprecise Dirichlet
interval of exact counts contains their frequency, for any prior strength. -/
theorem readInterval_sound :
    ∀ r ∈ evidenceCalculus.rules, r.id = ⟨"read-interval"⟩ → SchemaSound Ledger.Model.holds r := by
  intro r hr hid
  simp only [rules_eq, evidenceRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [rule, RuleId.mk.injEq, String.reduceEq] at hid
  intro m hprem
  simp only [Ledger.Model.holds, rule, observationCounts, countReadout, fv, app, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq, Interpretation.Holds] at hprem ⊢
  obtain ⟨φ, L, s, hq, hL, hs, he⟩ := hprem
  simp only [queryOf, ledgerOf, summaryOf, Option.some.injEq] at hq hL hs
  subst hq hL hs
  refine ⟨_, _, _, rfl, rfl, ?_⟩
  rw [← he]
  have hs := m.interp.priorStrength_pos
  set e := m.interp.summary "e"
  simp only [realStrength, strength, Evidence.total, map_apply_pos, map_apply_neg,
    Nat.coe_castRingHom, Set.mem_Icc]
  rcases Nat.eq_zero_or_pos (e.pos + e.neg) with empty | some
  · have p0 : e.pos = 0 := by omega
    have n0 : e.neg = 0 := by omega
    simp only [p0, n0, Nat.cast_zero, add_zero, div_zero,
      Mettapedia.ProbabilityTheory.ImpreciseProbability.WalleyBinaryIDM.lowerEndpoint,
      Mettapedia.ProbabilityTheory.ImpreciseProbability.WalleyBinaryIDM.upperEndpoint, zero_add,
      zero_div, le_refl, true_and]
    exact div_nonneg hs.le hs.le
  · exact idm_contains_frequency (Nat.cast_nonneg _) (Nat.cast_nonneg _) hs
      (by exact_mod_cast some)

/-- Conjunction on one world, with the contract that both bodies of evidence
are counts over the same observations: the strength of the conjunction lies in
the Fréchet interval of the two strengths. -/
theorem conjoinOneWorld_sound :
    ∀ r ∈ evidenceCalculus.rules, r.id = ⟨"conjoin-one-world"⟩ → SchemaSound Ledger.Model.holds r := by
  intro r hr hid
  simp only [rules_eq, evidenceRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [rule, RuleId.mk.injEq, String.reduceEq] at hid
  intro m hprem
  simp only [Ledger.Model.holds, rule, observationCounts, countReadout, ledgerHolds, fv, app, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, Interpretation.Holds] at hprem ⊢
  obtain ⟨⟨φ₁, L₁, s₁, hq₁, hL₁, hs₁, he₁⟩, ⟨φ₂, L₂, s₂, hq₂, hL₂, hs₂, he₂⟩,
    ⟨L, hD₁, hD₂⟩⟩ := hprem
  simp only [queryOf, ledgerOf, summaryOf, Option.some.injEq] at hq₁ hL₁ hs₁ hq₂ hL₂ hs₂ hD₁ hD₂
  subst hq₁ hL₁ hs₁ hq₂ hL₂ hs₂ hD₁
  refine ⟨_, _, _, rfl, rfl, ?_⟩
  rw [he₁, he₂, hD₂, Finset.union_self]
  simp only [ledgerEvidence_eq_ofSamples, Set.mem_Icc]
  exact frechet_strength _ _ _

/-- Without its contract the one-world conjunction is unsound: with `b = a`,
the first body records the one observation where `a` holds and the second the
one where it fails, so the Fréchet interval of the strengths `1` and `0` is
`{0}`, while over both observations `a ∧ a` has strength `1/2`. -/
theorem conjoinOneWorld_without_contract_unsound :
    ¬ SchemaSound Ledger.Model.holds (rule "conjoin-one-world" ["a", "b", "e1", "e2"]
        [observationCounts (fv "a") (fv "e1"), observationCounts (fv "b") (fv "e2")]
        (countReadout (app "and" [fv "a", fv "b"]) (app "frechet" [fv "e1", fv "e2"]))) := by
  intro sound
  let ρ : Interpretation (Fin 2) (Fin 2) :=
    { query := fun _ w => decide (w = 0)
      ledger := fun e => if e = "e1" then {0} else {1}
      summary := fun e => if e = "e1" then ⟨1, 0⟩ else ⟨0, 1⟩
      priorStrength := 1
      priorStrength_pos := one_pos }
  have h := sound ⟨Fin 2, Fin 2, id, ρ⟩ (by
    simp only [Ledger.Model.holds, rule, observationCounts, fv, app, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Interpretation.Holds]
    refine ⟨⟨_, _, _, rfl, rfl, rfl, ?_⟩, ⟨_, _, _, rfl, rfl, rfl, ?_⟩⟩ <;>
      simp only [ρ, String.reduceEq, ↓reduceIte] <;> ext <;> decide)
  simp only [Ledger.Model.holds, rule, countReadout, fv, app, Interpretation.Holds] at h
  obtain ⟨φ, S, L, hq, hv, hmem⟩ := h
  simp only [queryOf, valueOf, Option.some.injEq, Prod.mk.injEq, ρ, String.reduceEq,
    ↓reduceIte] at hq hv
  obtain ⟨rfl, rfl⟩ := hv
  subst hq
  have both : ledgerEvidence (id : Fin 2 → Fin 2) (fun w => decide (w = 0) && decide (w = 0))
      (({0} : Finset (Fin 2)) ∪ {1}) = ⟨1, 1⟩ := by
    ext <;> decide
  rw [both] at hmem
  norm_num [realStrength, strength, Evidence.total, Set.mem_Icc] at hmem

/-! ## Separately drawn samples -/

namespace Paired

/-- An interpretation over bags of worlds.  `combine w v` is the world that
agrees with `w` on what `a` asks and with `v` on what `b` asks, when the two
queries are about separable aspects of a world. -/
structure Model where
  W : Type
  query : String → W → Bool
  bag : String → Multiset W
  summary : String → Evidence ℕ
  combine : W → W → W

namespace Model

def queryOf (m : Model) : Pattern → Option (m.W → Bool)
  | .fvar q => some (m.query q)
  | .apply "and" [.fvar a, .fvar b] => some (fun w => m.query a w && m.query b w)
  | _ => none

def bagOf (m : Model) : Pattern → Option (Multiset m.W)
  | .fvar e => some (m.bag e)
  | .apply "pair" [.fvar a, .fvar b] =>
      some ((m.bag a ×ˢ m.bag b).map fun p => m.combine p.1 p.2)
  | _ => none

def summaryOf (m : Model) : Pattern → Option (Evidence ℕ)
  | .fvar e => some (m.summary e)
  | .apply "pair" [.fvar a, .fvar b] => some (m.summary a * m.summary b)
  | _ => none

/-- `SampleCounts q e`: the counts are the evidence of the bag for `q`;
`SampleHolds (independent a b)`: combined worlds keep what `a` saw in the first and
what `b` saw in the second. -/
def holds (m : Model) : Pattern → Prop
  | .apply "SampleCounts" [q, e] =>
      ∃ φ B s, m.queryOf q = some φ ∧ m.bagOf e = some B ∧ m.summaryOf e = some s ∧
        s = ofSamples φ B
  | .apply "SampleHolds" [.apply "independent" [.fvar a, .fvar b]] =>
      ∀ w v, m.query a (m.combine w v) = m.query a w ∧ m.query b (m.combine w v) = m.query b v
  | _ => False

end Model

end Paired

/-- Conjunction of independent bodies of evidence, with the contract that the
two queries are about separable aspects: the paired product of the counts is
the evidence of the combined samples for the conjunction. -/
theorem conjoinIndependent_sound :
    ∀ r ∈ evidenceCalculus.rules, r.id = ⟨"conjoin-independent"⟩ →
      SchemaSound Paired.Model.holds r := by
  intro r hr hid
  simp only [rules_eq, evidenceRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [rule, RuleId.mk.injEq, String.reduceEq] at hid
  intro m hprem
  simp only [Paired.Model.holds, rule, sampleCounts, sampleHolds, fv, app, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq] at hprem ⊢
  obtain ⟨⟨φ₁, B₁, s₁, hq₁, hB₁, hs₁, he₁⟩, ⟨φ₂, B₂, s₂, hq₂, hB₂, hs₂, he₂⟩, sep⟩ := hprem
  simp only [Paired.Model.queryOf, Paired.Model.bagOf, Paired.Model.summaryOf,
    Option.some.injEq] at hq₁ hB₁ hs₁ hq₂ hB₂ hs₂
  subst hq₁ hB₁ hs₁ hq₂ hB₂ hs₂
  refine ⟨_, _, _, rfl, rfl, rfl, ?_⟩
  rw [he₁, he₂, ← ofSamples_product]
  simp only [ofSamples, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro p _
  simp only [Function.comp_apply, sampleEvidence, (sep p.1 p.2).1, (sep p.1 p.2).2]

/-- Without its contract the independent conjunction is unsound: if combining
keeps only the first world, `a` and `b = a` on one positive and one negative
sample give paired counts `(0, 1)`, while the combined sample is positive. -/
theorem conjoinIndependent_without_contract_unsound :
    ¬ SchemaSound Paired.Model.holds (rule "conjoin-independent" ["a", "b", "e1", "e2"]
        [sampleCounts (fv "a") (fv "e1"), sampleCounts (fv "b") (fv "e2")]
        (sampleCounts (app "and" [fv "a", fv "b"]) (app "pair" [fv "e1", fv "e2"]))) := by
  intro sound
  let m : Paired.Model :=
    { W := Bool
      query := fun _ w => w
      bag := fun e => if e = "e1" then {true} else {false}
      summary := fun e => if e = "e1" then ⟨1, 0⟩ else ⟨0, 1⟩
      combine := fun w _ => w }
  have h := sound m (by
    simp only [Paired.Model.holds, rule, sampleCounts, fv, app, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    refine ⟨⟨_, _, _, rfl, rfl, rfl, ?_⟩, ⟨_, _, _, rfl, rfl, rfl, ?_⟩⟩ <;> simp [m] <;> rfl)
  simp only [Paired.Model.holds, rule, sampleCounts, fv, app] at h
  obtain ⟨φ, B, s, hq, hB, hs, he⟩ := h
  simp only [Paired.Model.queryOf, Paired.Model.bagOf, Paired.Model.summaryOf,
    Option.some.injEq, m] at hq hB hs
  subst hq hB hs
  have := congrArg Evidence.pos he
  revert this
  decide

/-! ## Reports about a hypothesis -/

namespace Reports

/-- A finite real-weight reading of hypotheses and reports. The algebraic
schema proof does not assume nonnegativity, normalization or supported
conditioning events. `EvidenceTermSettings.Reports` supplies those conditions
for its recursive probabilistic realization. -/
structure Model where
  Ω : Type
  [fin : Fintype Ω]
  weight : Ω → ℝ
  query : String → Ω → Bool
  report : String → Ω → Bool
  summary : String → Evidence ℝ

attribute [instance] Model.fin

namespace Model

/-- The probability of the event `E` given `H`. -/
noncomputable def likelihood (m : Model) (H E : m.Ω → Bool) : ℝ :=
  (∑ ω, if H ω && E ω then m.weight ω else 0) / ∑ ω, if H ω then m.weight ω else 0

/-- The likelihood pair of a report: under the hypothesis and under its negation. -/
noncomputable def likelihoods (m : Model) (H E : m.Ω → Bool) : Evidence ℝ :=
  ⟨m.likelihood H E, m.likelihood (fun ω => !H ω) E⟩

def queryOf (m : Model) : Pattern → Option (m.Ω → Bool)
  | .fvar q => some (m.query q)
  | _ => none

def reportOf (m : Model) : Pattern → Option (m.Ω → Bool)
  | .fvar e => some (m.report e)
  | .apply "fuse" [.fvar a, .fvar b] => some (fun ω => m.report a ω && m.report b ω)
  | _ => none

def summaryOf (m : Model) : Pattern → Option (Evidence ℝ)
  | .fvar e => some (m.summary e)
  | .apply "fuse" [.fvar a, .fvar b] => some (fuse (m.summary a) (m.summary b))
  | _ => none

/-- `ReportLikelihoods q e`: the stored pair is the likelihood pair of the report `e`
for the hypothesis `q`; `ReportHolds (reports q e₁ e₂)`: the two reports are
independent given `q` and given its negation. -/
def holds (m : Model) : Pattern → Prop
  | .apply "ReportLikelihoods" [q, e] =>
      ∃ H E s, m.queryOf q = some H ∧ m.reportOf e = some E ∧ m.summaryOf e = some s ∧
        s = m.likelihoods H E
  | .apply "ReportHolds" [.apply "reports" [.fvar q, .fvar a, .fvar b]] =>
      m.likelihood (m.query q) (fun ω => m.report a ω && m.report b ω) =
          m.likelihood (m.query q) (m.report a) * m.likelihood (m.query q) (m.report b) ∧
        m.likelihood (fun ω => !m.query q ω) (fun ω => m.report a ω && m.report b ω) =
          m.likelihood (fun ω => !m.query q ω) (m.report a) *
            m.likelihood (fun ω => !m.query q ω) (m.report b)
  | _ => False

end Model

end Reports

/-- Fusion of reports, with the contract that they are independent given the
hypothesis and given its negation: the product of the likelihood pairs is the
likelihood pair of the joint report.  Under a uniform prior its strength is the
posterior of the hypothesis (`EvidenceContracts.strength_fuse_uniform`). -/
theorem fuse_sound :
    ∀ r ∈ evidenceCalculus.rules, r.id = ⟨"fuse"⟩ → SchemaSound Reports.Model.holds r := by
  intro r hr hid
  simp only [rules_eq, evidenceRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [rule, RuleId.mk.injEq, String.reduceEq] at hid
  intro m hprem
  simp only [Reports.Model.holds, rule, reportLikelihoods, reportHolds, fv, app, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq] at hprem ⊢
  obtain ⟨⟨H₁, E₁, s₁, hq₁, hE₁, hs₁, he₁⟩, ⟨H₂, E₂, s₂, hq₂, hE₂, hs₂, he₂⟩, ci⟩ := hprem
  simp only [Reports.Model.queryOf, Reports.Model.reportOf, Reports.Model.summaryOf,
    Option.some.injEq] at hq₁ hE₁ hs₁ hq₂ hE₂ hs₂
  subst hq₁ hE₁ hs₁ hq₂ hE₂ hs₂
  refine ⟨_, _, _, rfl, rfl, rfl, ?_⟩
  rw [he₁, he₂]
  ext
  · exact ci.1.symm
  · exact ci.2.symm

/-- Without its contract fusion is unsound: the same noisy report counted
twice.  A report agreeing with the hypothesis three times in four has
likelihood `3/4`; fused with itself the product is `9/16`, while the joint
report is the report itself. -/
theorem fuse_without_contract_unsound :
    ¬ SchemaSound Reports.Model.holds (rule "fuse" ["q", "e1", "e2"]
        [reportLikelihoods (fv "q") (fv "e1"), reportLikelihoods (fv "q") (fv "e2")]
        (reportLikelihoods (fv "q") (app "fuse" [fv "e1", fv "e2"]))) := by
  intro sound
  let m : Reports.Model :=
    { Ω := Bool × Bool
      weight := fun ω => if ω.1 = ω.2 then 3 else 1
      query := fun _ ω => ω.1
      report := fun _ ω => ω.2
      summary := fun _ => ⟨3 / 4, 1 / 4⟩ }
  have lik : m.likelihoods (m.query "q") (m.report "e") = ⟨3 / 4, 1 / 4⟩ := by
    ext <;> simp [Reports.Model.likelihoods, Reports.Model.likelihood, m, Fintype.sum_prod_type] <;>
      norm_num
  have h := sound m (by
    simp only [Reports.Model.holds, rule, reportLikelihoods, fv, app, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    exact ⟨⟨_, _, _, rfl, rfl, rfl, lik.symm⟩, ⟨_, _, _, rfl, rfl, rfl, lik.symm⟩⟩)
  simp only [Reports.Model.holds, rule, reportLikelihoods, fv, app] at h
  obtain ⟨H, E, s, hq, hE, hs, he⟩ := h
  simp only [Reports.Model.queryOf, Reports.Model.reportOf, Reports.Model.summaryOf,
    Option.some.injEq] at hq hE hs
  subst hq hE hs
  have joint : (fun ω : Bool × Bool => m.report "e1" ω && m.report "e2" ω) = m.report "e" := by
    funext ω; simp [m]
  rw [joint, lik] at he
  have := congrArg Evidence.pos he
  simp [fuse] at this
  norm_num at this

/-! ## One population -/

namespace Population

/-- A bag of worlds read as a population, with values for the readout
variables. -/
structure Model where
  W : Type
  population : Multiset W
  query : String → W → Bool
  value : String → ℝ

namespace Model

/-- The number of worlds of the population satisfying a predicate. -/
abbrev freq (m : Model) (p : m.W → Bool) : ℕ := count m.population p

noncomputable def valueOf (m : Model) : Pattern → Option ℝ
  | .fvar s => some (m.value s)
  | .apply "deduction" [.fvar s₁, .fvar s₂, .fvar s₃, .fvar s₄] =>
      some (m.value s₁ * m.value s₂ + (1 - m.value s₁) *
        Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction.complementConditionalFromMarginal
          (m.value s₃) (m.value s₄) (m.value s₂))
  | _ => none

/-- `PopulationReadout (conditional a b) v`: `v` is the frequency of `b` among the `a`-worlds;
`PopulationReadout (probability a) v`: `v` is the frequency of `a`; `PopulationHolds (screens a b c)`: `c` is
independent of `a` given `b` and given `¬b`, and the conditioning events occur. -/
def holds (m : Model) : Pattern → Prop
  | .apply "PopulationReadout" [.apply "conditional" [.fvar a, .fvar b], v] =>
      ∃ r, m.valueOf v = some r ∧
        r = (m.freq (fun w => m.query a w && m.query b w) : ℝ) / m.freq (m.query a)
  | .apply "PopulationReadout" [.apply "probability" [.fvar a], v] =>
      ∃ r, m.valueOf v = some r ∧ r = (m.freq (m.query a) : ℝ) / Multiset.card m.population
  | .apply "PopulationHolds" [.apply "screens" [.fvar a, .fvar b, .fvar c]] =>
      m.freq (fun w => m.query a w && m.query b w && m.query c w) * m.freq (m.query b) =
          m.freq (fun w => m.query a w && m.query b w) *
            m.freq (fun w => m.query b w && m.query c w) ∧
        m.freq (fun w => m.query a w && !m.query b w && m.query c w) *
            m.freq (fun w => !m.query b w) =
          m.freq (fun w => m.query a w && !m.query b w) *
            m.freq (fun w => !m.query b w && m.query c w) ∧
        m.freq (m.query a) ≠ 0 ∧ m.freq (m.query b) ≠ 0 ∧ m.freq (fun w => !m.query b w) ≠ 0
  | _ => False

end Model

end Population

/-- PLN deduction, with the contract that `b` screens `c` off from `a`: the
deduction formula in the four frequencies is the frequency of `c` among the
`a`-worlds (`EvidenceContracts.deduction_exact_of_screening`). -/
theorem deduce_sound :
    ∀ r ∈ evidenceCalculus.rules, r.id = ⟨"deduce"⟩ → SchemaSound Population.Model.holds r := by
  intro r hr hid
  simp only [rules_eq, evidenceRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [rule, RuleId.mk.injEq, String.reduceEq] at hid
  intro m hprem
  simp only [Population.Model.holds, rule, populationReadout, populationHolds, fv, app, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hprem ⊢
  obtain ⟨⟨r₁, hv₁, h₁⟩, ⟨r₂, hv₂, h₂⟩, ⟨r₃, hv₃, h₃⟩, ⟨r₄, hv₄, h₄⟩,
    sB, sNB, hA, hB, hNB⟩ := hprem
  simp only [Population.Model.valueOf, Option.some.injEq] at hv₁ hv₂ hv₃ hv₄
  subst hv₁ hv₂ hv₃ hv₄
  refine ⟨_, rfl, ?_⟩
  rw [h₁, h₂, h₃, h₄]
  exact (deduction_exact_of_screening m.population (m.query "a") (m.query "b") (m.query "c")
    sB sNB hA hB hNB).symm

/-- Without screening off the deduction formula fails: in the four worlds of
`EvidenceContracts.Controls.unscreened` the formula gives `1/4`, while no
`a`-world has `c`. -/
theorem deduce_without_contract_unsound :
    ¬ SchemaSound Population.Model.holds (rule "deduce" ["a", "b", "c", "s1", "s2", "s3", "s4"]
        [populationReadout (app "conditional" [fv "a", fv "b"]) (fv "s1"),
          populationReadout (app "conditional" [fv "b", fv "c"]) (fv "s2"),
          populationReadout (app "probability" [fv "b"]) (fv "s3"), populationReadout (app "probability" [fv "c"]) (fv "s4")]
        (populationReadout (app "conditional" [fv "a", fv "c"])
          (app "deduction" [fv "s1", fv "s2", fv "s3", fv "s4"]))) := by
  intro sound
  let m : Population.Model :=
    { W := Controls.World3
      population := Controls.unscreened
      query := fun q w => if q = "a" then w.1 else if q = "b" then w.2.1 else w.2.2
      value := fun s =>
        if s = "s1" then 1 / 2 else if s = "s2" then 1 / 2 else if s = "s3" then 1 / 2
        else 1 / 4 }
  have h := sound m (by
    simp only [Population.Model.holds, rule, populationReadout, fv, app, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, Population.Model.valueOf, Option.some.injEq,
      exists_eq_left']
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [m, Population.Model.freq, String.reduceEq, ↓reduceIte] <;>
      norm_num [show count Controls.unscreened (fun w => w.1 && w.2.1) = 1 by decide,
        show count Controls.unscreened (fun w => w.1) = 2 by decide,
        show count Controls.unscreened (fun w => w.2.1 && w.2.2) = 1 by decide,
        show count Controls.unscreened (fun w => w.2.1) = 2 by decide,
        show count Controls.unscreened (fun w => w.2.2) = 1 by decide,
        show Multiset.card Controls.unscreened = 4 by decide])
  simp only [Population.Model.holds, rule, populationReadout, fv, app, Population.Model.valueOf,
    Option.some.injEq, exists_eq_left'] at h
  have zero : count Controls.unscreened (fun w => w.1 && w.2.2) = 0 := by decide
  simp only [m, Population.Model.freq, String.reduceEq, ↓reduceIte] at h
  rw [zero] at h
  unfold Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction.complementConditionalFromMarginal at h
  norm_num at h

end Mettapedia.PLN.Bridges.GSLT.EvidenceCalculusSemantics

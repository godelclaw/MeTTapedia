import Mathlib.Tactic

/-!
# No-threading lemma for the PNP steelman

This file records the finite logical obstruction behind the failed
success-domination route.  A statistic cannot be both neutral for a deterministic
witness bit and sufficient to determine that bit on each statistic fiber.

The statement is purely combinatorial: neutrality is equality of the true and
false counts in each finite fiber, and sufficiency says the witness bit is
constant on each statistic fiber.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

/-- True points in one statistic fiber. -/
abbrev FiberTrue {Phi U : Type*} [Fintype Phi] [DecidableEq U]
    (u : Phi -> U) (x : Phi -> Bool) (a : U) :=
  {phi : Phi // u phi = a ∧ x phi = true}

/-- False points in one statistic fiber. -/
abbrev FiberFalse {Phi U : Type*} [Fintype Phi] [DecidableEq U]
    (u : Phi -> U) (x : Phi -> Bool) (a : U) :=
  {phi : Phi // u phi = a ∧ x phi = false}

/-- Exact neutrality on every finite statistic fiber. -/
def Neutral {Phi U : Type*} [Fintype Phi] [DecidableEq U]
    (u : Phi -> U) (x : Phi -> Bool) : Prop :=
  ∀ a : U,
    Fintype.card (FiberTrue u x a) =
      Fintype.card (FiberFalse u x a)

/-- Sufficiency for a deterministic witness bit: the bit is constant on each
fiber of the statistic. -/
def Sufficient {Phi U : Type*}
    (u : Phi -> U) (x : Phi -> Bool) : Prop :=
  ∀ phi psi : Phi, u phi = u psi -> x phi = x psi

/-- Independence from the full instance, in this finite deterministic setting,
means the bit is constant across instances. -/
def IndependentOfInstance {Phi : Type*} (x : Phi -> Bool) : Prop :=
  ∀ phi psi : Phi, x phi = x psi

/-- A nontrivial deterministic witness bit takes both Boolean values. -/
def NontrivialWitnessBit {Phi : Type*} (x : Phi -> Bool) : Prop :=
  ∃ phi psi : Phi, x phi = true ∧ x psi = false

/-- Neutrality and sufficiency are inconsistent on any occupied fiber. -/
theorem noThreading_absurd_at
    {Phi U : Type*} [Fintype Phi] [DecidableEq U]
    {u : Phi -> U} {x : Phi -> Bool}
    (hN : Neutral u x) (hS : Sufficient u x) (phi : Phi) :
    False := by
  cases hbit : x phi
  · have hposFalse :
        0 < Fintype.card (FiberFalse u x (u phi)) := by
      apply Fintype.card_pos_iff.mpr
      exact ⟨⟨phi, ⟨rfl, hbit⟩⟩⟩
    have hposTrue :
        0 < Fintype.card (FiberTrue u x (u phi)) := by
      simpa [hN (u phi)] using hposFalse
    rcases Fintype.card_pos_iff.mp hposTrue with ⟨psi⟩
    have hsame : x psi.val = x phi :=
      hS psi.val phi psi.property.1
    rw [psi.property.2, hbit] at hsame
    cases hsame
  · have hposTrue :
        0 < Fintype.card (FiberTrue u x (u phi)) := by
      apply Fintype.card_pos_iff.mpr
      exact ⟨⟨phi, ⟨rfl, hbit⟩⟩⟩
    have hposFalse :
        0 < Fintype.card (FiberFalse u x (u phi)) := by
      simpa [hN (u phi)] using hposTrue
    rcases Fintype.card_pos_iff.mp hposFalse with ⟨psi⟩
    have hsame : x psi.val = x phi :=
      hS psi.val phi psi.property.1
    rw [psi.property.2, hbit] at hsame
    cases hsame

/-- The no-threading implication in independence form: from inconsistent
premises anything follows, including independence from the full instance. -/
theorem neutral_sufficient_forces_independent
    {Phi U : Type*} [Fintype Phi] [DecidableEq U]
    {u : Phi -> U} {x : Phi -> Bool}
    (hN : Neutral u x) (hS : Sufficient u x) :
    IndependentOfInstance x := by
  intro phi psi
  exact False.elim (noThreading_absurd_at hN hS phi)

/-- A concrete occupied fiber blocks simultaneous neutrality and sufficiency. -/
theorem noThreadingLemma
    {Phi U : Type*} [Fintype Phi] [DecidableEq U]
    {u : Phi -> U} {x : Phi -> Bool} (phi : Phi) :
    ¬ (Neutral u x ∧ Sufficient u x) := by
  intro h
  exact noThreading_absurd_at h.1 h.2 phi

theorem nontrivialWitnessBit_not_independent
    {Phi : Type*} {x : Phi -> Bool}
    (h : NontrivialWitnessBit x) :
    ¬ IndependentOfInstance x := by
  intro hind
  rcases h with ⟨phi, psi, hphi, hpsi⟩
  have hsame := hind phi psi
  rw [hphi, hpsi] at hsame
  cases hsame

/-- If the deterministic witness bit is nontrivial, no neutral statistic can
also be sufficient for it. -/
theorem noThreading_neutral_sufficient_blocks_nontrivial_bit
    {Phi U : Type*} [Fintype Phi] [DecidableEq U]
    {u : Phi -> U} {x : Phi -> Bool}
    (hNontrivial : NontrivialWitnessBit x) :
    ¬ (Neutral u x ∧ Sufficient u x) := by
  intro h
  exact
    nontrivialWitnessBit_not_independent hNontrivial
      (neutral_sufficient_forces_independent h.1 h.2)

/-! ## A two-point witness for the obstruction -/

def noThreadingToyStatistic (_phi : Bool) : Unit :=
  ()

def noThreadingToyWitness (phi : Bool) : Bool :=
  phi

theorem noThreadingToyWitness_nontrivial :
    NontrivialWitnessBit noThreadingToyWitness := by
  exact ⟨true, false, rfl, rfl⟩

theorem noThreadingToy_obstruction :
    ¬ (Neutral noThreadingToyStatistic noThreadingToyWitness ∧
        Sufficient noThreadingToyStatistic noThreadingToyWitness) :=
  noThreading_neutral_sufficient_blocks_nontrivial_bit
    noThreadingToyWitness_nontrivial

end Mettapedia.Computability.PNP

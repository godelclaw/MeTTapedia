import Mathlib.Data.Finset.Card
import Mettapedia.GraphTheory.FourColor.GoertzelV24ReductiveSpine

/-!
# Base implications and explicit census cardinality

This module records logical implications between base obligations and a
cardinality bound for an explicitly enumerated census. These statements do
not establish a lower bound on the work required by every base-verification
method, or the impossibility of a human-checkable proof.

Three layers:

* **necessity** — if any single bounded-size object failed the target, the
  universal theorem would be false; the base claim is a necessary component
  of the theorem, not an optional appendix.
* **transfer** — if any rival reductive system for the same target
  succeeds from its own base, the original system's base is thereby verified
  as well. This is a logical implication, not a requirement to enumerate
  either system's bounded objects.
* **census size** — a finite enumeration covering the bounded-size class
  contains every exhibited family of bounded-size objects, so its
  cardinality is at least the cardinality of that family.

The names `auditBurden` and `AuditableWithin` below measure only census
cardinality. They say nothing about compressed certificates, symbolic
arguments, derivation length, or the amount of inspection a referee needs.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ReductiveSpine

namespace ReductiveSystem

variable {Object : Type*} {target : Object → Prop}

/-- **Necessity.**  A single bounded-size counterexample refutes the
universal target outright.  Contrapositively, any correct proof of the
universal target certifies every bounded-size instance: the finite base
claim is a logical component of the theorem in this frame. -/
theorem not_target_all_of_base_counterexample
    (system : ReductiveSystem Object target) {object : Object}
    (_hsmall : system.size object ≤ system.threshold)
    (hbad : ¬ target object) :
    ¬ ∀ candidate, target candidate :=
  fun hall => hbad (hall object)

/-- **Transfer of base verification.** If a rival reductive system for the
same target — any choice of size measure, threshold, and reduction — succeeds
from its own base, then the original system's base claim is verified as well.
This does not require an explicit finite check of the original base. -/
theorem baseVerified_transfer
    (system rival : ReductiveSystem Object target)
    (hrival : rival.BaseVerified) :
    system.BaseVerified :=
  fun object _hsmall => rival.target_all_of_baseVerified hrival object

/-- A route-native census: a finite enumeration covering the entire
bounded-size class of one reductive system.  Completeness is the only
requirement — an overapproximating census only enlarges the audit, and the
lower bounds below hold against every complete census. -/
structure BaseCensus (system : ReductiveSystem Object target) where
  candidates : Finset Object
  complete :
    ∀ object, system.size object ≤ system.threshold → object ∈ candidates

namespace BaseCensus

variable {system : ReductiveSystem Object target}

/-- The number of entries in this explicit census, not a lower bound on the
number of instances every verification method must inspect. -/
def auditBurden (census : BaseCensus system) : Nat :=
  census.candidates.card

/-- This explicit census has at most `budget` entries. The predicate models
an enumeration-size budget, not human verifiability in general. -/
def AuditableWithin (census : BaseCensus system) (budget : Nat) : Prop :=
  census.auditBurden ≤ budget

/-- Any exhibited family of bounded-size objects is contained in every
complete census, so its cardinality bounds that census from below. -/
theorem card_le_auditBurden (census : BaseCensus system)
    (witnesses : Finset Object)
    (hwitnesses : ∀ witness ∈ witnesses,
      system.size witness ≤ system.threshold) :
    witnesses.card ≤ census.auditBurden := by
  refine Finset.card_le_card ?_
  intro witness hwitness
  exact census.complete witness (hwitnesses witness hwitness)

/-- More witnesses than the entry budget rule out a complete census within
that budget. This does not rule out a shorter non-enumerative proof. -/
theorem not_auditableWithin_of_budget_lt_card
    (census : BaseCensus system)
    (witnesses : Finset Object)
    (hwitnesses : ∀ witness ∈ witnesses,
      system.size witness ≤ system.threshold)
    {budget : Nat} (hbudget : budget < witnesses.card) :
    ¬ census.AuditableWithin budget := by
  intro hauditable
  have hlower := census.card_le_auditBurden witnesses hwitnesses
  exact Nat.lt_irrefl budget
    (Nat.lt_of_lt_of_le hbudget (Nat.le_trans hlower hauditable))

end BaseCensus

end ReductiveSystem

end GoertzelV24ReductiveSpine

end Mettapedia.GraphTheory.FourColor

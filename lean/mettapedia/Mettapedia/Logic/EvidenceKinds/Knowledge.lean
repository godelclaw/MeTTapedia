import Mettapedia.Logic.EvidenceKinds.Beliefs
import Mettapedia.Logic.EvidenceKinds.Verdicts

/-!
# What is known about one claim: a sum of results, a product of stores

A single result about a claim has one of three shapes (`Warrant`): a derivation of the claim or of
its negation under a dependency set (proved, admitted run, hypothesized, trusted: the sorts of the
atoms say which); identified observations of the claim's predicate (tested cases, PLN evidence);
or an unknown, carrying its receipt (an exhausted budget, an unfinished run).

What is known about the claim is one store per shape (`Knowledge`), and results enter by
injection (`ofWarrant`). In commutative monoids a finite coproduct is the product, so the sum of
shapes for one result and the product of stores for many are the same structure; the merge is
componentwise (`Knowledge.merge`).

## Laws

* **Merging is a semilattice** (`merge_comm`, `merge_assoc`, `merge_idem`): knowledge accumulates
  in any order and duplicate delivery is harmless, so accumulation needs no coordination.
* **No cross-kind contamination, by construction**: a derivation adds no observation
  (`derivation_adds_no_observation`, `counts_merge_derivation`); observations and unknown receipts
  decide nothing (`observations_do_not_decide`, `receipts_do_not_decide`).
* **The verdict is a reader's policy** (`verdict`): a reader names the atoms it grants, and a claim
  is established for it when some proof's set lies among them. The verdict reads soundly in every
  world where the granted atoms hold (`verdict_reads`). A trusted result is established for a
  reader that grants the promise and unknown for one that does not
  (`Controls.trust_is_reader_policy`). A conflict, a proof and a refutation both granted, shows the
  granted atoms cannot all hold (`conflict_inconsistent`).
* **More knowledge only refines the verdict, unless it conflicts** (`verdict_merge_established`).
* **Counts are a valuation of the ledger, not a homomorphism of the merge**
  (`counts_merge_valuation`): the counts of a merge plus the counts of the overlap are the sum of
  the counts, and the counts add exactly when the ledgers are disjoint (`counts_merge_additive_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.EvidenceKinds

open Mettapedia.PLN.WorldModel.EvidenceSpaces
open Mettapedia.PLN.WorldModel.EvidenceContracts

universe u v w x

/-- **A single result about a claim.** -/
inductive Warrant (Dep : Type u) (Obs : Type v) (Receipt : Type w) where
  /-- A derivation of the claim (`true`) or of its negation (`false`) under a dependency set. -/
  | derived (positive : Bool) (deps : Finset Dep)
  /-- Identified observations of the claim's predicate. -/
  | observed (ledger : Finset Obs)
  /-- Nothing was learned; the receipt says why. -/
  | unknown (receipt : Receipt)

/-- **What is known about one claim**: one store per shape. -/
@[ext] structure Knowledge (Dep : Type u) (Obs : Type v) (Receipt : Type w) where
  proofs : Finset (Finset Dep)
  refutations : Finset (Finset Dep)
  ledger : Finset Obs
  receipts : Finset Receipt

namespace Knowledge

variable {Dep : Type u} {Obs : Type v} {Receipt : Type w}
  [DecidableEq Dep] [DecidableEq Obs] [DecidableEq Receipt]

/-- Nothing known. -/
def empty : Knowledge Dep Obs Receipt := ⟨∅, ∅, ∅, ∅⟩

/-- **Merging knowledge**, componentwise. -/
def merge (first second : Knowledge Dep Obs Receipt) : Knowledge Dep Obs Receipt :=
  ⟨first.proofs ∪ second.proofs, first.refutations ∪ second.refutations,
    first.ledger ∪ second.ledger, first.receipts ∪ second.receipts⟩

/-- **A single result as knowledge.** -/
def ofWarrant : Warrant Dep Obs Receipt → Knowledge Dep Obs Receipt
  | .derived true deps => ⟨{deps}, ∅, ∅, ∅⟩
  | .derived false deps => ⟨∅, {deps}, ∅, ∅⟩
  | .observed ledger => ⟨∅, ∅, ledger, ∅⟩
  | .unknown receipt => ⟨∅, ∅, ∅, {receipt}⟩

theorem merge_comm (first second : Knowledge Dep Obs Receipt) :
    merge first second = merge second first := by
  ext <;> simp [merge, Finset.union_comm]

theorem merge_assoc (first second third : Knowledge Dep Obs Receipt) :
    merge (merge first second) third = merge first (merge second third) := by
  ext <;> simp [merge, Finset.union_assoc]

theorem merge_idem (knowledge : Knowledge Dep Obs Receipt) : merge knowledge knowledge = knowledge := by
  ext <;> simp [merge]

theorem merge_empty (knowledge : Knowledge Dep Obs Receipt) : merge knowledge empty = knowledge := by
  ext <;> simp [merge, empty]

omit [DecidableEq Dep] [DecidableEq Obs] [DecidableEq Receipt] in
/-- **A derivation adds no observation.** -/
theorem derivation_adds_no_observation (positive : Bool) (deps : Finset Dep) :
    (ofWarrant (.derived positive deps : Warrant Dep Obs Receipt)).ledger = ∅ := by
  cases positive <;> rfl

/-! ## Validity and the verdict -/

/-- **Valid knowledge**: every proof's set is sound for the claim, every refutation's for its
negation. -/
def Valid {World : Type x} (holdsAtom : World → Dep → Prop) (claim : World → Prop)
    (knowledge : Knowledge Dep Obs Receipt) : Prop :=
  (∀ deps ∈ knowledge.proofs, Sound holdsAtom claim deps) ∧
    (∀ deps ∈ knowledge.refutations, Sound holdsAtom (fun world => ¬ claim world) deps)

theorem Valid.merge {World : Type x} {holdsAtom : World → Dep → Prop} {claim : World → Prop}
    {first second : Knowledge Dep Obs Receipt} (h₁ : Valid holdsAtom claim first)
    (h₂ : Valid holdsAtom claim second) : Valid holdsAtom claim (merge first second) := by
  constructor
  · intro deps member
    rcases Finset.mem_union.mp member with inFirst | inSecond
    · exact h₁.1 deps inFirst
    · exact h₂.1 deps inSecond
  · intro deps member
    rcases Finset.mem_union.mp member with inFirst | inSecond
    · exact h₁.2 deps inFirst
    · exact h₂.2 deps inSecond

/-- Some proof rests only on granted atoms. -/
def Established (granted : Finset Dep) (knowledge : Knowledge Dep Obs Receipt) : Prop :=
  ∃ deps ∈ knowledge.proofs, deps ⊆ granted

/-- Some refutation rests only on granted atoms. -/
def Refuted (granted : Finset Dep) (knowledge : Knowledge Dep Obs Receipt) : Prop :=
  ∃ deps ∈ knowledge.refutations, deps ⊆ granted

instance (granted : Finset Dep) (knowledge : Knowledge Dep Obs Receipt) :
    Decidable (Established granted knowledge) := by
  unfold Established; infer_instance

instance (granted : Finset Dep) (knowledge : Knowledge Dep Obs Receipt) :
    Decidable (Refuted granted knowledge) := by
  unfold Refuted; infer_instance

/-- **The verdict of a reader that grants a set of atoms**; `none` is a conflict. -/
def verdict (granted : Finset Dep) (knowledge : Knowledge Dep Obs Receipt) : Option Verdict :=
  if Established granted knowledge then
    if Refuted granted knowledge then none else some .established
  else if Refuted granted knowledge then some .refuted else some .unknown

omit [DecidableEq Obs] [DecidableEq Receipt] in
/-- **The verdict reads soundly where the granted atoms hold.** -/
theorem verdict_reads {World : Type x} {holdsAtom : World → Dep → Prop} {claim : World → Prop}
    {knowledge : Knowledge Dep Obs Receipt} (valid : Valid holdsAtom claim knowledge)
    {granted : Finset Dep} {world : World} (holds : ∀ atom ∈ granted, holdsAtom world atom)
    {result : Verdict} (read : verdict granted knowledge = some result) :
    Verdict.Reads result (claim world) := by
  unfold verdict at read
  split_ifs at read with established refuted refuted'
  · cases read
    obtain ⟨deps, member, sub⟩ := established
    exact (valid.1 deps member).weaken sub world holds
  · cases read
    obtain ⟨deps, member, sub⟩ := refuted'
    exact (valid.2 deps member).weaken sub world holds
  · cases read
    trivial

omit [DecidableEq Obs] [DecidableEq Receipt] in
/-- **A conflict shows the granted atoms cannot all hold.** -/
theorem conflict_inconsistent {World : Type x} {holdsAtom : World → Dep → Prop}
    {claim : World → Prop} {knowledge : Knowledge Dep Obs Receipt}
    (valid : Valid holdsAtom claim knowledge) {granted : Finset Dep}
    (conflict : verdict granted knowledge = none) (world : World) :
    ¬ ∀ atom ∈ granted, holdsAtom world atom := by
  intro holds
  unfold verdict at conflict
  split_ifs at conflict with established refuted
  obtain ⟨proofDeps, inProofs, proofSub⟩ := established
  obtain ⟨refDeps, inRefs, refSub⟩ := refuted
  exact (valid.2 refDeps inRefs).weaken refSub world holds
    ((valid.1 proofDeps inProofs).weaken proofSub world holds)

/-- **Observations decide nothing.** -/
theorem observations_do_not_decide (granted : Finset Dep) (knowledge : Knowledge Dep Obs Receipt)
    (ledger : Finset Obs) :
    verdict granted (merge knowledge (ofWarrant (.observed ledger))) = verdict granted knowledge := by
  simp [verdict, Established, Refuted, merge, ofWarrant]

/-- **Unknown receipts decide nothing.** -/
theorem receipts_do_not_decide (granted : Finset Dep) (knowledge : Knowledge Dep Obs Receipt)
    (receipt : Receipt) :
    verdict granted (merge knowledge (ofWarrant (.unknown receipt))) = verdict granted knowledge := by
  simp [verdict, Established, Refuted, merge, ofWarrant]

/-- **More knowledge keeps an established verdict, unless it conflicts.** -/
theorem verdict_merge_established {granted : Finset Dep} {knowledge : Knowledge Dep Obs Receipt}
    (established : verdict granted knowledge = some .established) (more : Knowledge Dep Obs Receipt) :
    verdict granted (merge knowledge more) = some .established ∨
      verdict granted (merge knowledge more) = none := by
  have h₁ : Established granted knowledge := by
    by_contra notEstablished
    unfold verdict at established
    rw [if_neg notEstablished] at established
    split_ifs at established <;> simp at established
  have kept : Established granted (merge knowledge more) := by
    obtain ⟨deps, member, sub⟩ := h₁
    exact ⟨deps, Finset.mem_union_left _ member, sub⟩
  unfold verdict
  rw [if_pos kept]
  split_ifs <;> simp

/-! ## Counts -/

/-- The counts of the knowledge: the ledger evidence of its observations. -/
def counts {W : Type x} (world : Obs → W) (φ : W → Bool) (knowledge : Knowledge Dep Obs Receipt) :
    Evidence ℕ :=
  ledgerEvidence world φ knowledge.ledger

theorem counts_merge_derivation {W : Type x} (world : Obs → W) (φ : W → Bool)
    (knowledge : Knowledge Dep Obs Receipt) (positive : Bool) (deps : Finset Dep) :
    counts world φ (merge knowledge (ofWarrant (.derived positive deps))) = counts world φ knowledge := by
  cases positive <;> simp [counts, merge, ofWarrant]

/-- **Counts are a valuation of the ledger.** -/
theorem counts_merge_valuation {W : Type x} (world : Obs → W) (φ : W → Bool)
    (first second : Knowledge Dep Obs Receipt) :
    counts world φ (merge first second) + ledgerEvidence world φ (first.ledger ∩ second.ledger) =
      counts world φ first + counts world φ second :=
  ledgerEvidence_union_add_inter world φ first.ledger second.ledger

/-- **Counts add exactly when the ledgers are disjoint.** -/
theorem counts_merge_additive_iff {W : Type x} (world : Obs → W) (φ : W → Bool)
    (first second : Knowledge Dep Obs Receipt) :
    counts world φ first + counts world φ second = counts world φ (merge first second) ↔
      Disjoint first.ledger second.ledger :=
  additive_revision_exact_iff_disjoint world φ first.ledger second.ledger

end Knowledge

/-! ## Controls -/

namespace Controls

open Knowledge

/-- **Trust is a reader's policy**: a promise-based proof is established for a reader that grants
the promise and unknown for a strict reader; observations do not change that. -/
theorem trust_is_reader_policy :
    verdict ({.disjointPromise} : Finset Atom)
        (ofWarrant (.derived true {.disjointPromise} : Warrant Atom ℕ Unit)) = some .established ∧
      verdict (∅ : Finset Atom) (ofWarrant (.derived true {.disjointPromise} : Warrant Atom ℕ Unit)) =
        some .unknown ∧
      verdict (∅ : Finset Atom)
          (merge (ofWarrant (.derived true {.disjointPromise} : Warrant Atom ℕ Unit))
            (ofWarrant (.observed (Finset.range 100)))) = some .unknown := by
  refine ⟨by decide, by decide, ?_⟩
  rw [observations_do_not_decide]
  decide

/-- **A conflict between a proof and a refutation**: both granted, no world satisfies the granted
atoms; granting only one side gives that side's verdict. -/
theorem conflict_and_resolution :
    verdict ({.a, .b} : Finset Atom)
        (merge (ofWarrant (.derived true {.a} : Warrant Atom ℕ Unit)) (ofWarrant (.derived false {.b}))) =
        none ∧
      verdict ({.a} : Finset Atom)
        (merge (ofWarrant (.derived true {.a} : Warrant Atom ℕ Unit)) (ofWarrant (.derived false {.b}))) =
        some .established := by
  decide

/-- **Established, positive and negative**: a proof resting on atom `a` is established for a
reader that grants `a`, and not for one that grants nothing. -/
theorem granted_proof_established :
    Established ({.a} : Finset Atom) (ofWarrant (.derived true {.a} : Warrant Atom ℕ Unit)) ∧
      ¬ Established (∅ : Finset Atom) (ofWarrant (.derived true {.a} : Warrant Atom ℕ Unit)) := by
  decide

/-- **Refuted, positive and negative**: a refutation resting on `b` refutes for a reader granting
`b`; a proof resting on `b` does not. -/
theorem refutation_refuted :
    Refuted ({.b} : Finset Atom) (ofWarrant (.derived false {.b} : Warrant Atom ℕ Unit)) ∧
      ¬ Refuted ({.b} : Finset Atom) (ofWarrant (.derived true {.b} : Warrant Atom ℕ Unit)) := by
  unfold Refuted
  decide

end Controls

end Mettapedia.Logic.EvidenceKinds

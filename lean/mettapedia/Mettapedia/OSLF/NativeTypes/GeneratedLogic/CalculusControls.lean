import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CalculusPresentation
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Search
import Mettapedia.Languages.HOLLight.FirstOrder.CalculusControls
import Mettapedia.NARS.Bridges.GSLT.ScopedRevisionCalculus
import Mettapedia.PLN.Bridges.GSLT.EvidenceCalculusModule

/-!
# Controls: proof calculi decided as goal-stack rewriting

Three calculi, each read through its goal-stack presentation (`CalculusPresentation`): the front door answers
"some run reaches the empty stack", and the answer is derivability of the goal.

**HOL Light's kernel** (`hol`): 137 of its 147 rules are moded. The ten that are not are eight inference
rules for `hol.Thm` (transitivity, for example, has a middle term its conclusion does not fix), one typing
rule and one sorting rule. The inequality judgment of trees and the order judgments it uses are concluded
only by moded rules (`order_moded`), so for them the presentation is exact both ways.
- `hol.Neq` holds between two different leaves (`neq_derivable`) and not between a leaf and itself
  (`neq_irreflexive`): the front door proves the first by exploration and refutes the second with a closed
  region.
- `tree.Lt` orders the two leaves one way (`lt_derivable`) and not the other (`lt_asymmetric`).

**NARS revision** (`narsIn`): every rule is moded. Its contract judgments (same statement, disjoint or
overlapping sources, confidence order) have no rules: a context asserts them. Here a context is a list of
axioms, one rule without premises per assertion (`narsIn`).
- With disjoint sources, the revision of two valid beliefs has the summed counts (`revision_counted`).
- With overlapping sources, revision does not have the summed counts (`overlap_blocks_revision`), and the
  confidence choice keeps the counts of the more confident belief (`choice_counted`).

**PLN evidence** (`plnIn`): eight of its nine rules are moded; deduction through a middle term is not, and it
concludes population readouts only. Counts, lower bounds, count readouts and ledger contracts are concluded
only by moded rules (`pln_moded`).
- Two disjoint ledgers of a query revise to exact counts, whose strength can be read
  (`pln_revision_counted`).
- With nothing known about their overlap, there are no exact revised counts
  (`pln_revision_needs_disjointness`), only a lower bound (`pln_lower_bound`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.CalculusControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.LabeledTreeOrder (nodeP numeralP nilP)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.CalculusPresentation

/-! ## Reading answers as derivability -/

/-- A derivation of one goal is a derivation list of that goal. -/
theorem derivation_iff_list (definition : ValidatedCalculusLanguageDef) (goal : Pattern) :
    Nonempty (Derivation definition goal) ↔ Nonempty (DerivationList definition [goal]) :=
  (CalculusAsLanguage.derivation_nonempty_iff_proofSearch definition goal).trans
    (CalculusAsLanguage.derivationList_nonempty_iff_proofSearch definition [goal]).symm

/-- **A proof of "some run reaches the empty stack" is a derivation.** -/
theorem derivable_of_answer {definition : ValidatedCalculusLanguageDef} {goal : Pattern} {rounds : ℕ}
    {evidence : Evidence} (proper : ProperGoal goal)
    (answered : ask RelationEnv.empty [] (presentation definition.1) 1 reachesEmpty (stack [goal]) none rounds =
      .proved evidence) :
    Nonempty (Derivation definition goal) :=
  (derivation_iff_list definition goal).mpr
    (derivable_of_sat (by simpa using proper) (ask_proved answered))

/-- **A refutation is underivability**, where only moded rules conclude. -/
theorem underivable_of_answer {definition : ValidatedCalculusLanguageDef} {heads : List String}
    (headsModed : modedHeads definition.1 heads = true) {goal : Pattern} {rounds : ℕ} {evidence : Evidence}
    (proper : ProperGoal goal) (within : headIn heads goal = true)
    (answered : ask RelationEnv.empty [] (presentation definition.1) 1 reachesEmpty (stack [goal]) none rounds =
      .refuted evidence) :
    ¬ Nonempty (Derivation definition goal) := fun derivable =>
  ask_refuted answered ((derivable_iff_sat headsModed (by simpa using proper) (by simpa using within)).mp
    ((derivation_iff_list definition goal).mp derivable))

/-! ## HOL Light's kernel -/

def hol : ValidatedCalculusLanguageDef := Mettapedia.Languages.HOLLight.FirstOrder.CalculusControls.validated

/-- The order judgments of trees and the inequality they define. -/
def orderHeads : List String := ["tree.Below", "tree.Lt", "tree.LtList", "hol.Neq"]

/-- **Only moded rules conclude them.** -/
theorem order_moded : modedHeads hol.1 orderHeads = true := by decide +kernel

/-- **137 of the kernel's 147 rules are moded.** -/
theorem hol_moded_count : (hol.1.rules.filter moded).length = 137 ∧ hol.1.rules.length = 147 := by decide +kernel

/-- A leaf with a label. -/
def leaf (label : ℕ) : Pattern := nodeP (numeralP label) nilP

def neq (first second : Pattern) : Pattern := .apply "hol.Neq" [first, second]
def lt (first second : Pattern) : Pattern := .apply "tree.Lt" [first, second]

theorem neq_proper : ProperGoal (neq (leaf 0) (leaf 1)) ∧ ProperGoal (neq (leaf 0) (leaf 0)) := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;> decide +kernel

theorem lt_proper : ProperGoal (lt (leaf 0) (leaf 1)) ∧ ProperGoal (lt (leaf 1) (leaf 0)) := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;> decide +kernel

/-- **Two different leaves are unequal.** -/
theorem neq_derivable : Nonempty (Derivation hol (neq (leaf 0) (leaf 1))) :=
  derivable_of_answer neq_proper.1 (rounds := 8) (evidence := .exploration 8) (by decide +kernel)

/-- **A leaf is not unequal to itself.** -/
theorem neq_irreflexive : ¬ Nonempty (Derivation hol (neq (leaf 0) (leaf 0))) :=
  underivable_of_answer order_moded neq_proper.2 (by decide +kernel) (rounds := 8) (evidence := .closedRegion 8)
    (by decide +kernel)

/-- **The leaf labelled `0` is below the leaf labelled `1`.** -/
theorem lt_derivable : Nonempty (Derivation hol (lt (leaf 0) (leaf 1))) :=
  derivable_of_answer lt_proper.1 (rounds := 8) (evidence := .exploration 8) (by decide +kernel)

/-- **And not the other way round.** -/
theorem lt_asymmetric : ¬ Nonempty (Derivation hol (lt (leaf 1) (leaf 0))) :=
  underivable_of_answer order_moded lt_proper.2 (by decide +kernel) (rounds := 8) (evidence := .closedRegion 8)
    (by decide +kernel)

/-! ## NARS revision in a context -/

open Mettapedia.GSLT.LanguageDef.FirstOrderCalculus (term rule)
open Mettapedia.NARS.Bridges.GSLT.ScopedRevisionCalculus
  (sameStatement disjoint overlap validBelief counts revision choice countSum confidenceLe)

/-- Two atomic beliefs and their count readouts. -/
def belief₁ : Pattern := .apply "B1" []
def belief₂ : Pattern := .apply "B2" []
def counts₁ : Pattern := .apply "E1" []
def counts₂ : Pattern := .apply "E2" []

/-- **NARS revision in a context**: the calculus, the atomic beliefs and counts, and one axiom for each
contract judgment the context asserts. -/
def narsIn (context : List Pattern) : CalculusLanguageDef :=
  { Mettapedia.NARS.Bridges.GSLT.ScopedRevisionCalculus.calculus with
    name := "nars-scoped-revision-in-context"
    terms := Mettapedia.NARS.Bridges.GSLT.ScopedRevisionCalculus.calculus.terms ++
      [term "B1" "Belief" [], term "B2" "Belief" [], term "E1" "Counts" [], term "E2" "Counts" []]
    rules := Mettapedia.NARS.Bridges.GSLT.ScopedRevisionCalculus.calculus.rules ++
      context.zipIdx.map fun (judgment, index) => rule s!"context-{index}" [] [] judgment }

/-- Both beliefs valid, about one statement, with their counts, from disjoint sources. -/
def disjointContext : List Pattern :=
  [sameStatement belief₁ belief₂, disjoint belief₁ belief₂, validBelief belief₁, validBelief belief₂,
    counts belief₁ counts₁, counts belief₂ counts₂]

/-- The same, from overlapping sources, the first belief at least as confident as the second. -/
def overlapContext : List Pattern :=
  [sameStatement belief₁ belief₂, overlap belief₁ belief₂, validBelief belief₁, validBelief belief₂,
    counts belief₁ counts₁, counts belief₂ counts₂, confidenceLe belief₂ belief₁]

theorem disjoint_admitted : (narsIn disjointContext).isAdmitted = true := by decide +kernel
theorem overlap_admitted : (narsIn overlapContext).isAdmitted = true := by decide +kernel

def narsDisjoint : ValidatedCalculusLanguageDef := (narsIn disjointContext).validated disjoint_admitted
def narsOverlap : ValidatedCalculusLanguageDef := (narsIn overlapContext).validated overlap_admitted

/-- The judgments of NARS revision. -/
def narsHeads : List String :=
  ["SameStatement", "SourceDisjoint", "SourceOverlap", "ConfidenceLe", "ConfidenceLt", "ValidBelief", "EvidenceCounts"]

/-- **Every rule is moded**, so the presentation is exact for every judgment. -/
theorem nars_moded : modedHeads narsDisjoint.1 narsHeads = true ∧ modedHeads narsOverlap.1 narsHeads = true := by
  constructor <;> decide +kernel

def revisedCounts : Pattern := counts (revision belief₁ belief₂) (countSum counts₁ counts₂)
def chosenCounts : Pattern := counts (choice belief₁ belief₂) counts₁

theorem nars_proper : ProperGoal revisedCounts ∧ ProperGoal chosenCounts := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;> decide +kernel

/-- **With disjoint sources, the revision has the summed counts.** -/
theorem revision_counted : Nonempty (Derivation narsDisjoint revisedCounts) :=
  derivable_of_answer nars_proper.1 (rounds := 8) (evidence := .exploration 8) (by decide +kernel)

/-- **With overlapping sources, it does not.** -/
theorem overlap_blocks_revision : ¬ Nonempty (Derivation narsOverlap revisedCounts) :=
  underivable_of_answer nars_moded.2 nars_proper.1 (by decide +kernel) (rounds := 8)
    (evidence := .closedRegion 8) (by decide +kernel)

/-- **The confidence choice keeps the counts of the more confident belief.** -/
theorem choice_counted : Nonempty (Derivation narsOverlap chosenCounts) :=
  derivable_of_answer nars_proper.2 (rounds := 8) (evidence := .exploration 8) (by decide +kernel)

/-! ## PLN evidence in a context -/

open Mettapedia.PLN.Bridges.GSLT.EvidenceCalculusModule
  (evidenceCalculus observationCounts observationLowerBound ledgerHolds countReadout)

/-- A query and two observation ledgers for it. -/
def query : Pattern := .apply "Q" []
def ledger₁ : Pattern := .apply "L1" []
def ledger₂ : Pattern := .apply "L2" []

/-- **PLN evidence in a context**: the calculus, the query and ledgers, and one axiom for each assertion. -/
def plnIn (context : List Pattern) : CalculusLanguageDef :=
  { evidenceCalculus with
    name := "pln-evidence-calculus-in-context"
    terms := evidenceCalculus.terms ++
      [term "Q" "Query" [], term "L1" "ObservationCounts" [], term "L2" "ObservationCounts" []]
    rules := evidenceCalculus.rules ++ context.zipIdx.map fun (judgment, index) => rule s!"context-{index}" [] [] judgment }

/-- Two ledgers of the query, known to be disjoint. -/
def disjointLedgers : List Pattern :=
  [observationCounts query ledger₁, observationCounts query ledger₂, ledgerHolds (.apply "disjoint" [ledger₁, ledger₂])]

/-- Two ledgers of the query, with nothing known about their overlap. -/
def unknownOverlap : List Pattern := [observationCounts query ledger₁, observationCounts query ledger₂]

theorem pln_disjoint_admitted : (plnIn disjointLedgers).isAdmitted = true := by decide +kernel
theorem pln_unknown_admitted : (plnIn unknownOverlap).isAdmitted = true := by decide +kernel

def plnDisjoint : ValidatedCalculusLanguageDef := (plnIn disjointLedgers).validated pln_disjoint_admitted
def plnUnknown : ValidatedCalculusLanguageDef := (plnIn unknownOverlap).validated pln_unknown_admitted

/-- Counts, their lower bounds and readouts, and the ledger contracts. The one rule that is not moded,
deduction through a middle term, concludes population readouts, which are not among them. -/
def plnHeads : List String := ["ObservationCounts", "ObservationLowerBound", "LedgerHolds", "CountReadout"]

theorem pln_moded : modedHeads plnUnknown.1 plnHeads = true := by decide +kernel

def revisedLedger : Pattern := observationCounts query (.apply "revise" [ledger₁, ledger₂])
def mergedBound : Pattern := observationLowerBound query (.apply "lowerMerge" [ledger₁, ledger₂])
def revisedStrength : Pattern := countReadout query (.apply "strength" [.apply "revise" [ledger₁, ledger₂]])

theorem pln_proper : ProperGoal revisedLedger ∧ ProperGoal mergedBound ∧ ProperGoal revisedStrength := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;> decide +kernel

/-- **Disjoint ledgers revise to exact counts**, and their strength can be read. -/
theorem pln_revision_counted :
    Nonempty (Derivation plnDisjoint revisedLedger) ∧ Nonempty (Derivation plnDisjoint revisedStrength) :=
  ⟨derivable_of_answer pln_proper.1 (rounds := 8) (evidence := .exploration 8) (by decide +kernel),
    derivable_of_answer pln_proper.2.2 (rounds := 8) (evidence := .exploration 8) (by decide +kernel)⟩

/-- **Without disjointness, there are no exact revised counts.** -/
theorem pln_revision_needs_disjointness : ¬ Nonempty (Derivation plnUnknown revisedLedger) :=
  underivable_of_answer pln_moded pln_proper.1 (by decide +kernel) (rounds := 8) (evidence := .closedRegion 8)
    (by decide +kernel)

/-- **Only a lower bound.** -/
theorem pln_lower_bound : Nonempty (Derivation plnUnknown mergedBound) :=
  derivable_of_answer pln_proper.2.1 (rounds := 8) (evidence := .exploration 8) (by decide +kernel)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.CalculusControls

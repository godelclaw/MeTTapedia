import Mettapedia.PLN.Bridges
import Mettapedia.PLN.ConceptGeometry
import Mettapedia.PLN.Comparisons
import Mettapedia.PLN.Core
import Mettapedia.PLN.Evidence
import Mettapedia.PLN.InferenceControl
import Mettapedia.PLN.RuleFamilies
import Mettapedia.PLN.TruthValues
import Mettapedia.PLN.WorldModel

/-!
# Probabilistic Logic Networks

## The spine

PLN is a calculus of evidence.  Its essence is one chain; read these modules in
order.  Everything else in the room extends a link of the chain or relates it
to another formalism.

1. **Evidence carriers.**  `Evidence.EvidenceClass` (evidence is a commutative
   monoid under revision) and `Evidence.BinaryEvidence` (the count pair
   `(n⁺, n⁻)`, revision `+`, tensor `*`).  Ledgers with provenance:
   `Evidence.EvidentialLedger`, `Evidence.IdentityEvidence`.
2. **Observation contracts.**  `WorldModel.EvidenceContracts`: which
   combination is sound depends on what was observed.  Identified observations
   (revision exact iff disjoint, overlap interval), one world (Fréchet
   interval), pairs of samples (`WorldModel.PairedSampleDispersion`: pairs are
   not samples), reports about one hypothesis (the tensor is fusion).
3. **Readouts.**  Strength `n⁺ / (n⁺ + n⁻)`, undetermined at no evidence.
   Confidence is a chart of the evidence weight (`TruthValues.PLNConfidenceWeight`),
   forced to `w / (w + k)` once it is the width complement of the imprecise
   Dirichlet interval (`ProbabilityTheory.ImpreciseProbability.WalleyBinaryIDM`).
   Intervals: `TruthValues.PLNIndefiniteTruth`.
4. **Rules with contracts.**  Strength formulas derived from probability under
   a stated assumption (`RuleFamilies.FirstOrder.PLNDerivation`, Fréchet bounds
   in `RuleFamilies.FirstOrder.PLNFrechetBounds`), their exactness on Bayesian
   networks and the collider counterexample
   (`RuleFamilies.FirstOrder.PLNXiDerivedBNRules`), and conclusion confidence
   through intervals (`EvidenceContracts.deduction_confidence_route`).
5. **World models.**  `WorldModel.BinaryWorldModel` (states revised by `+`,
   queries answered by extracting evidence), `WorldModel.WorldModelCalculus`
   (a rule is a query rewrite guarded by its side condition),
   `WorldModel.PLNWorldModelCrispSpecialization` (the world model of a crisp
   semantics), `WorldModel.PLNWorldModelGeneric` (other conjugate carriers).
6. **Inference control.**  `InferenceControl`: certified chaining and premise
   selection over the world-model calculus.
7. **Bridges and comparisons.**  `Bridges` relates the spine to logics (FOL,
   HOL, modal), probability, category theory, GSLT and runtimes; `Comparisons`
   compares PLN with other systems.  Neither redefines a spine concept.
   Steps 1–4 as portable module data: `Bridges.GSLT.EvidenceCalculusModule`
   (the rules with their contract premises, read back through the verified
   module reader) and `Bridges.GSLT.EvidenceCalculusSemantics` (the revision
   rule is sound with its contract and unsound without it).

## Rooms

- `Evidence/`: carriers, revision mathematics, evidence-level bridges.
- `TruthValues/`: readouts (strength, confidence, intervals, distributions) and
  their counterexamples.
- `RuleFamilies/`: `FirstOrder` (deduction, induction, abduction, revision,
  quantifiers), `HigherOrder`, `MeasureTheoretic`, `QuantaleSemantics`,
  `Stratified`, `Temporal`.
- `WorldModel/`: the world-model interface, its calculus and its instances.
- `InferenceControl/`, `ConceptGeometry/`, `Bridges/`, `Comparisons/`.
- `Core/`: composite end-to-end theorems over several layers.

PLN and NARS are sibling formalizations.  They share source-neutral evidence
mathematics through `Mettapedia.Evidence`; every PLN–NARS claim lives in
`Mettapedia.NARS.Bridges.PLN`, with both agreement and obstruction theorems.
-/

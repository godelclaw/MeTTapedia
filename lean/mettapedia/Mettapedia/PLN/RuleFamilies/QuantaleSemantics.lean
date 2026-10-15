import Mettapedia.PLN.RuleFamilies.QuantaleSemantics.PBit
import Mettapedia.PLN.RuleFamilies.QuantaleSemantics.CDLogic
import Mettapedia.PLN.RuleFamilies.QuantaleSemantics.PLNModel
import Mettapedia.PLN.RuleFamilies.QuantaleSemantics.Soundness
import Mettapedia.PLN.RuleFamilies.QuantaleSemantics.PLNQuantaleConnection
import Mettapedia.PLN.RuleFamilies.QuantaleSemantics.PLNQuantaleDivergence
import Mettapedia.PLN.RuleFamilies.QuantaleSemantics.DoubleNegationCorners
import Mettapedia.PLN.RuleFamilies.QuantaleSemantics.TwistNegation

/-!
# PLN Quantale Semantics

Formal semantics for Probabilistic Logic Networks grounded in:
1. **Goertzel's p-bits** - 4-valued paraconsistent truth values
2. **Quantale algebra** - BinaryEvidence as commutative quantale
3. **K&S representation** - Embedding into ℝ via Hölder theorem

## Architecture

```
BinaryEvidence (pos, neg : ℝ≥0∞) = Goertzel's p-bits
  ↓ (averaging over situations)
PLN Truth Values (strength, confidence)
  ↓ (quantale operations)
Sound inference rules with provable bounds
```

## What This Module Provides

### PBit.lean - P-Bit Foundation
- `pTrue`, `pFalse`, `pNeither`, `pBoth`: The four corners of the p-bit square
- `isTrue`, `isFalse`, `isNeither`, `isBoth`: Classification predicates
- `quadrant`: Classify evidence into its quadrant
- `evidence_not_boolean`: Proof that BinaryEvidence is Heyting but not Boolean

### CDLogic.lean - Constructible Duality Operations
- `cdNeg` (∼): Involutive negation (swap pos/neg)
- `cdTensor` (⊙): Multiplicative conjunction (coordinatewise ×)
- `cdPar` (⅋): Additive disjunction (coordinatewise +)
- `cdTensor_sup_left/right`: Quantale distributivity

### DoubleNegationCorners.lean - Double Negation as the Corner Readout
- `isRegular_iff`: the elements fixed by double negation are the saturated corners
- `regularEquivQuadrant`, `toRegular_eq`: Glivenko's Boolean algebra of regular
  evidence is the four corners, and double negation reads off the quadrant
- `saturatedCorner_le_iff`: the corners carry Belnap's knowledge order
- `compl_compl_add`, `compl_compl_mul`: revision descends to the knowledge join,
  the tensor to the knowledge meet
- `wheel_quadrant`, `wheelOf_quadrant`: Dignāga's wheel of reasons is the quadrant
  of presence among similar and dissimilar instances

### TwistNegation.lean - Strong and Intuitionistic Negation
- `tmeet`, `tjoin`, `timp`: the truth-order operations (the twist structure of
  Nelson's logic over the chain `[0, ∞]`)
- `cdNeg_truthLE_inot_iff`: strong negation entails intuitionistic negation exactly
  on consistent evidence
- `inot_truthLE_cdNeg_iff`: intuitionistic negation entails strong negation exactly
  when absence of support counts as full refutation
- `inot_inot_apply`: double intuitionistic negation keeps two values (closed world),
  while the double complement of the information order keeps four

### PLNModel.lean - Formal Model Theory
- `PLNModel`: BinaryEvidence assignment to propositions
- `isValid`, `isInvalid`, `isUnknown`, `isContradictory`: Validity states
- `tensorCompose`, `parCompose`: Model composition operations
- `cdNegate`: Model-level CD negation
- Quantale distributivity at the model level

### Soundness.lean - Inference Rule Soundness
- `tensor_monotone`: Tensor preserves evidence ordering
- `par_monotone`: Par preserves evidence ordering
- `tensor_strength_ge`: Strength lower bound (foundation of deduction)
- Corner preservation theorems
- Model-level monotonicity

## Key Results

1. **BinaryEvidence = P-bits**: The existing `BinaryEvidence` type from `EvidenceQuantale.lean`
   is exactly Goertzel's p-bit structure from arXiv:2012.14474.

2. **CD Logic is algebraic**: All CD logic operations are proven to satisfy
   their algebraic laws (involution, commutativity, associativity, distributivity).

3. **BinaryEvidence is a Frame**: BinaryEvidence has complete Heyting algebra structure
   (proven in `EvidenceQuantale.lean` via `Order.Frame BinaryEvidence`).

4. **Quantale law**: Tensor distributes over join (cdTensor_sup_left/right).

5. **Soundness**: PLN inference operations preserve evidence ordering.

6. **Strength bounds**: Tensor product strength ≥ product of individual strengths.

## Connection to Goertzel's Research

| Goertzel Concept | Our Formalization |
|------------------|-------------------|
| P-bits (H × H^op) | `BinaryEvidence` with pos/neg |
| CD Negation | `cdNeg` = swap components |
| CD Tensor | `cdTensor` = coordinatewise × |
| CD Par | `cdPar` = coordinatewise + |
| Averaging over situations | `strength`, `confidence` views |
| Second-order probability | BinaryEvidence counts + κ prior |
| Paraconsistent "both" | `pBoth` corner with pos > 0 ∧ neg > 0 |
| Epistemic "neither" | `pNeither` corner with pos = 0 ∧ neg = 0 |

## Building on Existing Infrastructure

This module builds on:
- `EvidenceQuantale.lean`: BinaryEvidence structure, quantale instance, Frame instance
- `PLNDeduction.lean`: Deduction formula, consistency bounds
- `EvidenceBeta.lean`: Beta-BinaryEvidence connection, conjugate prior

## References

- Goertzel et al., "Paraconsistent Foundations for Probabilistic Reasoning,
  Programming and Concept Learning" (arXiv:2012.14474)
- Girard, "Linear Logic" (1987)
- Knuth & Skilling, "Foundations of Inference" (2012)
- Lawvere, "Metric spaces, generalized logic, and closed categories" (1973)
-/

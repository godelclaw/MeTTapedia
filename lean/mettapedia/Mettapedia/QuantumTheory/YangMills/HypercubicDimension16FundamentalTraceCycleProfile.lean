import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderFundamentalThreeCutRepair

/-!
# OUR complete three-cut trace-cycle profile

The preceding finite repair calibrated separate two- and six-cycle gates on
one fundamental three-cut placement.  This module performs the complete
bounded trace-topology calculation on the seven-cycle underlying that
carrier.  Every injective ordered choice of three cut labels is enumerated:
there are `210` such choices.  For each one, the six rewired trace
permutations are tested for the presence of one cycle of lengths `2` through
`6`.

The rational profile
\[
  (c_2,c_3,c_4,c_5,c_6)
    = (6/5,13/10,-1,-7/10,-3/5)
\]
annihilates the alternating six-term trace-cycle contribution for every one
of those choices.  The five coefficients are also forced by the four
topology types occurring in the enumeration together with the polarized
trace-anticommutator equation.

This is a kernel-checked finite trace-topology certificate.  It specifies
the cycle-profile part required of a later signed-`H(4)` coordinate lift; it
does not by itself construct that lift, establish full relation-submodule
descent, or supply Wilson-functional analytic coordinates.
-/

set_option autoImplicit false

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FundamentalTraceCycleProfile

open HypercubicDimension16IncomingCommutatorTraceMismatch

/-- OUR ordered three-cut label data on the concrete seven-cycle. -/
abbrev OurThreeCutLabels := Fin 7 × Fin 7 × Fin 7

/-- The six trace-cycle types in the fundamental three-cut relation for a
given ordered triple of labels. -/
def ourFundamentalThreeCutCycleSignature
    (labels : OurThreeCutLabels) : List (Multiset ℕ) :=
  let first := labels.1
  let second := labels.2.1
  let third := labels.2.2
  let traceOrder : Equiv.Perm (Fin 7) := finRotate 7
  [ Equiv.Perm.cycleType traceOrder
  , Equiv.Perm.cycleType (traceOrder.trans (Equiv.swap first second))
  , Equiv.Perm.cycleType (traceOrder.trans (Equiv.swap first third))
  , Equiv.Perm.cycleType (traceOrder.trans (Equiv.swap second third))
  , Equiv.Perm.cycleType (traceOrder.trans
      ((Equiv.swap second third).trans (Equiv.swap first second)))
  , Equiv.Perm.cycleType (traceOrder.trans
      ((Equiv.swap first second).trans (Equiv.swap second third))) ]

/-- The signed alternating sum of the indicator that a trace cycle type has
exactly one cycle of the selected length. -/
def ourFundamentalThreeCutCycleGateSum
    (cycleLength : ℕ) (signature : List (Multiset ℕ)) : Int :=
  (signature.zip [1, -1, -1, -1, 1, 1]).foldl
    (fun total entry =>
      if entry.1.count cycleLength = 1 then total + entry.2 else total) 0

/-- Every ordered triple of distinct labels in the seven-cycle. -/
def ourDistinctThreeCutLabels : List OurThreeCutLabels :=
  ((List.finRange 7).product ((List.finRange 7).product (List.finRange 7))).filter
    (fun labels => decide (labels.1 ≠ labels.2.1 ∧ labels.1 ≠ labels.2.2 ∧
      labels.2.1 ≠ labels.2.2)) |>.map
      (fun labels => (labels.1, labels.2.1, labels.2.2))

/-- Integer numerator (with denominator ten cleared) of OUR cycle profile. -/
def ourFundamentalThreeCutCycleProfileNumerator
    (labels : OurThreeCutLabels) : Int :=
  let signature := ourFundamentalThreeCutCycleSignature labels
  12 * ourFundamentalThreeCutCycleGateSum 2 signature +
    13 * ourFundamentalThreeCutCycleGateSum 3 signature -
      10 * ourFundamentalThreeCutCycleGateSum 4 signature -
        7 * ourFundamentalThreeCutCycleGateSum 5 signature -
          6 * ourFundamentalThreeCutCycleGateSum 6 signature

/-- Rational form of OUR cycle profile. -/
def ourFundamentalThreeCutCycleProfileValue
    (labels : OurThreeCutLabels) : ℚ :=
  (ourFundamentalThreeCutCycleProfileNumerator labels : ℚ) / 10

/-- The executable list of all profile numerators. -/
def ourDistinctThreeCutProfileNumerators : List Int :=
  ourDistinctThreeCutLabels.map ourFundamentalThreeCutCycleProfileNumerator

set_option maxRecDepth 100000 in
/-- There are exactly `210` ordered injective three-cut label choices. -/
theorem ourDistinctThreeCutLabels_card :
    ourDistinctThreeCutLabels.length = 210 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The bounded enumeration has zero numerator for every legal ordered
three-cut choice. -/
theorem ourDistinctThreeCutProfileNumerators_all_zero :
    ∀ numerator ∈ ourDistinctThreeCutProfileNumerators, numerator = 0 := by
  decide +kernel

/-- Consequently OUR rational trace-cycle profile vanishes on every
enumerated legal three-cut topology. -/
theorem ourFundamentalThreeCutCycleProfileValue_zero
    (labels : OurThreeCutLabels)
    (hlabels : labels ∈ ourDistinctThreeCutLabels) :
    ourFundamentalThreeCutCycleProfileValue labels = 0 := by
  have hnumerator : ourFundamentalThreeCutCycleProfileNumerator labels = 0 := by
    apply ourDistinctThreeCutProfileNumerators_all_zero
    exact List.mem_map.mpr ⟨labels, hlabels, rfl⟩
  unfold ourFundamentalThreeCutCycleProfileValue
  rw [hnumerator]
  norm_num

/-- The four topology equations together with the polarized
trace-anticommutator equation determine the profile coefficients uniquely. -/
theorem ourTraceCycleProfile_forced
    (c2 c3 c4 c5 c6 : ℚ)
    (hA : -c2 - 2 * c6 = 0)
    (hB : -c3 - c5 - c6 = 0)
    (hC : -2 * c3 - 2 * c4 - c6 = 0)
    (hD : -2 * c2 - c4 - 2 * c5 = 0)
    (hAnti : (1 / 2 : ℚ) - c2 - c5 = 0) :
    c2 = 6 / 5 ∧ c3 = 13 / 10 ∧ c4 = -1 ∧ c5 = -7 / 10 ∧ c6 = -3 / 5 := by
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith

#print axioms ourDistinctThreeCutLabels_card
#print axioms ourDistinctThreeCutProfileNumerators_all_zero
#print axioms ourFundamentalThreeCutCycleProfileValue_zero
#print axioms ourTraceCycleProfile_forced

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FundamentalTraceCycleProfile

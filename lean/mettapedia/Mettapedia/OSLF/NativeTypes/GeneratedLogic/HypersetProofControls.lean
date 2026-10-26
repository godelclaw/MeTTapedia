import Mettapedia.OSLF.NativeTypes.GeneratedLogic.HypersetProofs

/-!
# Controls: hyperset verdicts proved and refuted from the laws of the sets

Each verdict is a sentence of set theory about a coded graph, proved or refuted from the laws of the empty set, the
power set and separation, with the size of the derivation. Ω = {Ω} descends forever: the sentence exhibits the set of
codes of nodes on an infinite descent as an invariant. It has no well-founded descent: every predicate closed under
"all members have it" fails at its code. The empty set is the other way round.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.NativeTypes.GeneratedLogic.HypersetGraphs

/-- The coding of Ω's graph. -/
def omegaCoding : GraphCode omega := GraphCode.single rfl

/-- The coding of the empty set's graph. -/
def emptyCoding : GraphCode emptyGraph := GraphCode.single rfl

/-- The size of a derivation, and its side. -/
def graphReport {φ ψ : Mettapedia.Logic.HOL.ClosedFormula Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation.Symbol} :
    Proof lawList φ ⊕ Proof lawList ψ → String
  | .inl proof => s!"proved in {proofSize proof} rules"
  | .inr proof => s!"refuted in {proofSize proof} rules"

-- Ω descends forever.
/-- info: "proved in 510 rules" -/
#guard_msgs in
#eval graphReport (compileGraph omegaCoding (formula := descendsForever) rfl 0)

-- Ω has no well-founded descent.
/-- info: "refuted in 344 rules" -/
#guard_msgs in
#eval graphReport (compileGraph omegaCoding (formula := wellFounded) rfl 0)

-- The empty set's descents end.
/-- info: "proved in 215 rules" -/
#guard_msgs in
#eval graphReport (compileGraph emptyCoding (formula := wellFounded) rfl 0)

-- The empty set does not descend forever.
/-- info: "refuted in 99 rules" -/
#guard_msgs in
#eval graphReport (compileGraph emptyCoding (formula := descendsForever) rfl 0)

/-- The coding of the graph with two Ωs, their pair and the empty set, by the numerals `0` to `3`. -/
def twoOmegasCoding : GraphCode twoOmegas :=
  GraphCode.ofApart (fun node => [zero, one, two, three].getD node.val zero)
    (fun node => by
      have small := node.2
      change node.val < 4 at small
      have cases : node.val = 0 ∨ node.val = 1 ∨ node.val = 2 ∨ node.val = 3 := by omega
      rcases cases with h | h | h | h <;> simp only [h, List.getD_cons_zero, List.getD_cons_succ] <;>
        exact (hereditary_iff _).mp (by decide))
    (by decide +kernel)

-- In the four-node graph, node 0 has the two Ωs, nodes 1 and 2, as members, so it pictures {Ω, Ω} = Ω: it descends
-- forever. The edges from the other nodes are case-split away by their codes, the numerals 1, 2 and 3.
/-- info: "proved in 4546 rules" -/
#guard_msgs in
#eval graphReport (compileGraph twoOmegasCoding (formula := descendsForever) rfl 0)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

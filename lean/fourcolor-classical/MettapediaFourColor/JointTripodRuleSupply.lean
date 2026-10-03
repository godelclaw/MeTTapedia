import MettapediaFourColor.RuleFanTripodSupply

/-!
# Three shared charge readings force a tripod

Rule 002_1 and rule 003_1 on the same six-to-seven dart retain one
intermediate low vertex. Rule 002_2 on the adjacent dart, with that same
intermediate vertex as sender, supplies the other outer five. If the
intermediate degree is six, these readings are the four faces of D0052.
The complete boundary and colouring reconstruction come from the existing
tripod consumer. No separate occurrence hypothesis is required.
-/

namespace FourColor.JointTripodRuleSupply

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open NearLinearRuleData NearLinearCharge ExceptionalCoreOrientation ExceptionalOverlap

local instance (r : Fin 84) : NeZero (size r) :=
  ⟨by have := (headers r).1; omega⟩

theorem unit_amounts : amount 1 = 1 ∧ amount 3 = 1 ∧ amount 2 = 1 := by decide +kernel

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] (rotation : Data G)

/-- A source turn carries its actual facial corner, including the two edges. -/
theorem corner {r : Fin 84} (x : Occurrence rotation r) (i j k : Vertex r)
    (ij : (NearLinearRuleData.graph r).Adj i j)
    (ik : (NearLinearRuleData.graph r).Adj i k) (turn : Turn r i j k) :
    Corner rotation (x.vertex i) (x.vertex j) (x.vertex k) :=
  ⟨x.edge i j ij, x.edge i k ik, x.turn i j k ij ik turn⟩

variable (x : Occurrence rotation 3) (y : Occurrence rotation 1)
  (z : Occurrence rotation 2)
  (ys : y.vertex 0 = x.vertex 0) (yt : y.vertex 1 = x.vertex 1)
  (zs : z.vertex 0 = x.vertex 2) (zt : z.vertex 1 = x.vertex 1)

def vertices : Fin 6 → V :=
  ![x.vertex 3, x.vertex 2, x.vertex 0, x.vertex 1, y.vertex 2, z.vertex 2]

/-- The two darts share their receiver and the intermediate sender of rule 003_1. -/
def reading (tri : Triangular rotation) : FourTriangleCore.Reading 1 rotation := by
  apply FourTriangleFaces.reading 1 tri (vertices rotation x y z)
  intro k
  have a := corner rotation x 2 1 0 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  have b := corner rotation x 2 0 3 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  have c := corner rotation y 0 1 2 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  have e := corner rotation z 1 0 2 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  fin_cases k
  · exact a
  · exact b
  · change Corner rotation (x.vertex 0) (x.vertex 1) (y.vertex 2)
    simpa only [ys, yt] using c
  · change Corner rotation (x.vertex 1) (x.vertex 2) (z.vertex 2)
    simpa only [zs, zt] using e

/-- The source rule degrees supply all three outer fives. -/
theorem degrees (tri : Triangular rotation)
    (sender : G.degree (x.vertex 0) = 6)
    (receiver : G.degree (x.vertex 1) = 7)
    (middle : G.degree (x.vertex 2) = 6) :
    ∀ i, G.degree ((reading rotation x y z ys yt zs zt tri).map i) =
      FourTriangleCore.degree 1 i := by
  have xf : G.degree (x.vertex 3) = 5 := by
    have h := x.degree 3
    change 5 ≤ G.degree (x.vertex 3) ∧ (5 = 0 ∨ G.degree (x.vertex 3) ≤ 5) at h
    omega
  have yf : G.degree (y.vertex 2) = 5 := by
    have h := y.degree 2
    change 5 ≤ G.degree (y.vertex 2) ∧ (5 = 0 ∨ G.degree (y.vertex 2) ≤ 5) at h
    omega
  have zf : G.degree (z.vertex 2) = 5 := by
    have h := z.degree 2
    change 5 ≤ G.degree (z.vertex 2) ∧ (5 = 0 ∨ G.degree (z.vertex 2) ≤ 5) at h
    omega
  intro i
  change G.degree (vertices rotation x y z i) = FourTriangleCore.degree 1 i
  rw [RuleFanTripodSupply.degree_word]
  fin_cases i
  · exact xf
  · exact middle
  · exact sender
  · exact receiver
  · exact yf
  · exact zf

end FourColor.JointTripodRuleSupply

namespace FourColor.ActualJointTripodRuleSupply

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open GoertzelV24TwoEdgeCutMinimality NearLinearCharge NearLinearRuleData
open MinimalExceptionalEmbedding (graph rotation)

noncomputable section
attribute [local instance] Classical.propDecidable

local instance (r : Fin 84) : NeZero (size r) :=
  ⟨by have := (headers r).1; omega⟩

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  (original : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample original)

/-- Three retained source readings supply all geometry needed by actual tripod repair. -/
theorem not_readings
    (x : Occurrence (rotation original minimal) 3)
    (y : Occurrence (rotation original minimal) 1)
    (z : Occurrence (rotation original minimal) 2)
    (ys : y.vertex 0 = x.vertex 0) (yt : y.vertex 1 = x.vertex 1)
    (zs : z.vertex 0 = x.vertex 2) (zt : z.vertex 1 = x.vertex 1)
    (sender : (graph original minimal).degree (x.vertex 0) = 6)
    (receiver : (graph original minimal).degree (x.vertex 1) = 7)
    (middle : (graph original minimal).degree (x.vertex 2) = 6) : False := by
  let r := rotation original minimal
  let tri := MinimalExceptionalEmbedding.triangular original minimal
  exact ActualFourTrianglePatch.not_in_minimal original minimal 1
    (JointTripodRuleSupply.reading r x y z ys yt zs zt tri)
    (JointTripodRuleSupply.degrees r x y z ys yt zs zt tri sender receiver middle)

/-- The adjacent dart is determined by the original root, not chosen independently. -/
abbrev adjacentDart (d : (graph original minimal).Dart) :=
  ((rotation original minimal).vertexRotation d.symm).symm

/-- Executable joint matches force actual strict reconstruction. The middle
vertex is exactly the sender of the adjacent dart. -/
theorem not_checks (d : (graph original minimal).Dart)
    (sender : (graph original minimal).degree d.fst = 6)
    (receiver : (graph original minimal).degree d.snd = 7)
    (middle : (graph original minimal).degree (adjacentDart original minimal d).fst = 6)
    (left : RuleMatcher.check (rotation original minimal) 1 d = true)
    (cap : RuleMatcher.check (rotation original minimal) 3 d = true)
    (right : RuleMatcher.check (rotation original minimal) 2
      (adjacentDart original minimal d) = true) : False := by
  let r := rotation original minimal
  obtain ⟨x, xs, xt⟩ := (RuleMatcher.check_iff r d).mp cap
  obtain ⟨y, ys, yt⟩ := (RuleMatcher.check_iff r d).mp left
  obtain ⟨z, zs, zt⟩ := (RuleMatcher.check_iff r (adjacentDart original minimal d)).mp right
  change x.vertex 0 = d.fst at xs
  change x.vertex 1 = d.snd at xt
  change y.vertex 0 = d.fst at ys
  change y.vertex 1 = d.snd at yt
  change z.vertex 0 = (adjacentDart original minimal d).fst at zs
  change z.vertex 1 = (adjacentDart original minimal d).snd at zt
  have root : (⟨(x.vertex 1,x.vertex 0),x.edge 1 0 (by decide +kernel)⟩ :
      (graph original minimal).Dart) = d.symm := by
    apply SimpleGraph.Dart.ext
    exact Prod.ext xt xs
  have turn := x.turn 1 0 2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rw [root] at turn
  have same : (adjacentDart original minimal d).fst = x.vertex 2 :=
    congrArg (fun e : (graph original minimal).Dart => e.snd) turn
  have target : (adjacentDart original minimal d).snd = d.snd :=
    r.vertexRotation_fst d.symm
  exact not_readings original minimal x y z (ys.trans xs.symm) (yt.trans xt.symm)
    (zs.trans same) (zt.trans (target.trans xt.symm))
    (xs.symm ▸ sender) (xt.symm ▸ receiver) (same ▸ middle)

/-- Each of these source matches transfers one unit to the common receiver.
Their joint contribution is at most two, even though each individual rule
can apply. This bound retains the adjacent dart selected by the same rotation. -/
theorem joint_units_le_two (d : (graph original minimal).Dart)
    (sender : (graph original minimal).degree d.fst = 6)
    (receiver : (graph original minimal).degree d.snd = 7)
    (middle : (graph original minimal).degree (adjacentDart original minimal d).fst = 6) :
    (if RuleMatcher.check (rotation original minimal) 1 d then 1 else 0) +
      (if RuleMatcher.check (rotation original minimal) 3 d then 1 else 0) +
      (if RuleMatcher.check (rotation original minimal) 2
        (adjacentDart original minimal d) then 1 else 0) ≤ (2 : ℤ) := by
  by_cases a : RuleMatcher.check (rotation original minimal) 1 d = true
  <;> by_cases b : RuleMatcher.check (rotation original minimal) 3 d = true
  <;> by_cases c : RuleMatcher.check (rotation original minimal) 2
    (adjacentDart original minimal d) = true
  · exact False.elim (not_checks original minimal d sender receiver middle a b c)
  all_goals simp_all

/-- The upper bound concerns the actual amounts of the pinned source rules. -/
theorem joint_transfer_le_two (d : (graph original minimal).Dart)
    (sender : (graph original minimal).degree d.fst = 6)
    (receiver : (graph original minimal).degree d.snd = 7)
    (middle : (graph original minimal).degree (adjacentDart original minimal d).fst = 6) :
    (if RuleMatcher.check (rotation original minimal) 1 d then (amount 1 : ℤ) else 0) +
      (if RuleMatcher.check (rotation original minimal) 3 d then (amount 3 : ℤ) else 0) +
      (if RuleMatcher.check (rotation original minimal) 2
        (adjacentDart original minimal d) then (amount 2 : ℤ) else 0) ≤ 2 := by
  simpa only [JointTripodRuleSupply.unit_amounts.1, JointTripodRuleSupply.unit_amounts.2.1,
    JointTripodRuleSupply.unit_amounts.2.2, Nat.cast_one] using
      joint_units_le_two original minimal d sender receiver middle

end
end FourColor.ActualJointTripodRuleSupply

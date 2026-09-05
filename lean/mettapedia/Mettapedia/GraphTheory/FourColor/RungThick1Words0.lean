import Mettapedia.GraphTheory.FourColor.RungThick1
import Mathlib.Tactic.IntervalCases

/-! Boundary words 0–26 of `RungThick1`: one kernel theorem per word. -/

namespace Mettapedia.GraphTheory.FourColor.TubeSlab.RungThick1
namespace W0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w0 : P.enumMask 0 = labTable[0]! := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w1 : P.enumMask 1 = labTable[1]! := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w2 : P.enumMask 2 = labTable[2]! := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w3 : P.enumMask 3 = labTable[3]! := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w4 : P.enumMask 4 = labTable[4]! := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w5 : P.enumMask 5 = labTable[5]! := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w6 : P.enumMask 6 = labTable[6]! := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w7 : P.enumMask 7 = labTable[7]! := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w8 : P.enumMask 8 = labTable[8]! := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w9 : P.enumMask 9 = labTable[9]! := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w10 : P.enumMask 10 = labTable[10]! := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w11 : P.enumMask 11 = labTable[11]! := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w12 : P.enumMask 12 = labTable[12]! := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w13 : P.enumMask 13 = labTable[13]! := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w14 : P.enumMask 14 = labTable[14]! := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w15 : P.enumMask 15 = labTable[15]! := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w16 : P.enumMask 16 = labTable[16]! := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w17 : P.enumMask 17 = labTable[17]! := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w18 : P.enumMask 18 = labTable[18]! := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w19 : P.enumMask 19 = labTable[19]! := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w20 : P.enumMask 20 = labTable[20]! := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w21 : P.enumMask 21 = labTable[21]! := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w22 : P.enumMask 22 = labTable[22]! := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w23 : P.enumMask 23 = labTable[23]! := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w24 : P.enumMask 24 = labTable[24]! := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w25 : P.enumMask 25 = labTable[25]! := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w26 : P.enumMask 26 = labTable[26]! := by decide +kernel

theorem chunk (X : Nat) (h2 : X < 27) : P.enumMask X = labTable[X]! := by
  interval_cases X
  · exact w0
  · exact w1
  · exact w2
  · exact w3
  · exact w4
  · exact w5
  · exact w6
  · exact w7
  · exact w8
  · exact w9
  · exact w10
  · exact w11
  · exact w12
  · exact w13
  · exact w14
  · exact w15
  · exact w16
  · exact w17
  · exact w18
  · exact w19
  · exact w20
  · exact w21
  · exact w22
  · exact w23
  · exact w24
  · exact w25
  · exact w26

end W0
end Mettapedia.GraphTheory.FourColor.TubeSlab.RungThick1

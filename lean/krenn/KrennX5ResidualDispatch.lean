import KrennX5SupportConnector
import KrennX5Residuals

/-!
Generated semantic dispatch from representative-indexed X5 normalization
predicates to the exact case-specific residual refutations.

Each theorem fixes both the representative ordinal and the frozen case index.
This prevents a certificate for one normalized case from being used under
another representative label.
-/

namespace Krenn.X5ResidualDispatch

open MonochromaticQuantumGraph
open Krenn.X5GaugeNormalizationData
open Krenn.X5SupportConnector

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem refutesRepresentative5 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 5 W) : False := by
  apply Krenn.X5ResidualCase5.Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase5, selectedCase5] using h.selected 0
  · simpa [datum, datumCase5, selectedCase5] using h.selected 1
  · simpa [datum, datumCase5, selectedCase5] using h.selected 2
  · simpa [datum, datumCase5, selectedCase5] using h.selected 3
  · simpa [datum, datumCase5, selectedCase5] using h.selected 4

theorem refutesRepresentative84 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 66 W) : False := by
  apply Krenn.X5ResidualCase84.Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase84, selectedCase84] using h.selected 0
  · simpa [datum, datumCase84, selectedCase84] using h.selected 1
  · simpa [datum, datumCase84, selectedCase84] using h.selected 2
  · simpa [datum, datumCase84, selectedCase84] using h.selected 3
  · simpa [datum, datumCase84, selectedCase84] using h.selected 4

theorem refutesRepresentative86 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 68 W) : False := by
  apply Krenn.X5ResidualCase86.Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase86, selectedCase86] using h.selected 0
  · simpa [datum, datumCase86, selectedCase86] using h.selected 1
  · simpa [datum, datumCase86, selectedCase86] using h.selected 2
  · simpa [datum, datumCase86, selectedCase86] using h.selected 3
  · simpa [datum, datumCase86, selectedCase86] using h.selected 4

theorem refutesRepresentative98 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 80 W) : False := by
  apply Krenn.X5ResidualCase98.Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase98, selectedCase98] using h.selected 0
  · simpa [datum, datumCase98, selectedCase98] using h.selected 1
  · simpa [datum, datumCase98, selectedCase98] using h.selected 2
  · simpa [datum, datumCase98, selectedCase98] using h.selected 3
  · simpa [datum, datumCase98, selectedCase98] using h.selected 4

theorem refutesRepresentative102 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 84 W) : False := by
  apply Krenn.X5ResidualCase102.Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase102, selectedCase102] using h.selected 0
  · simpa [datum, datumCase102, selectedCase102] using h.selected 1
  · simpa [datum, datumCase102, selectedCase102] using h.selected 2
  · simpa [datum, datumCase102, selectedCase102] using h.selected 3
  · simpa [datum, datumCase102, selectedCase102] using h.selected 4

theorem refutesRepresentative131 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 95 W) : False := by
  apply Krenn.X5ResidualCase131.Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase131, selectedCase131] using h.selected 0
  · simpa [datum, datumCase131, selectedCase131] using h.selected 1
  · simpa [datum, datumCase131, selectedCase131] using h.selected 2
  · simpa [datum, datumCase131, selectedCase131] using h.selected 3
  · simpa [datum, datumCase131, selectedCase131] using h.selected 4

theorem refutesRepresentative170 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 110 W) : False := by
  apply Krenn.X5ResidualCase170.Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase170, selectedCase170] using h.selected 0
  · simpa [datum, datumCase170, selectedCase170] using h.selected 1
  · simpa [datum, datumCase170, selectedCase170] using h.selected 2
  · simpa [datum, datumCase170, selectedCase170] using h.selected 3
  · simpa [datum, datumCase170, selectedCase170] using h.selected 4

theorem refutesRepresentative304 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 160 W) : False := by
  apply Krenn.X5ResidualCase304.Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase304, selectedCase304] using h.selected 0
  · simpa [datum, datumCase304, selectedCase304] using h.selected 1
  · simpa [datum, datumCase304, selectedCase304] using h.selected 2
  · simpa [datum, datumCase304, selectedCase304] using h.selected 3
  · simpa [datum, datumCase304, selectedCase304] using h.selected 4

theorem refutesRepresentative316 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 172 W) : False := by
  apply Krenn.X5ResidualCase316.Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase316, selectedCase316] using h.selected 0
  · simpa [datum, datumCase316, selectedCase316] using h.selected 1
  · simpa [datum, datumCase316, selectedCase316] using h.selected 2
  · simpa [datum, datumCase316, selectedCase316] using h.selected 3
  · simpa [datum, datumCase316, selectedCase316] using h.selected 4

theorem refutesRepresentative385 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 199 W) : False := by
  apply Krenn.X5ResidualCase385.Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase385, selectedCase385] using h.selected 0
  · simpa [datum, datumCase385, selectedCase385] using h.selected 1
  · simpa [datum, datumCase385, selectedCase385] using h.selected 2
  · simpa [datum, datumCase385, selectedCase385] using h.selected 3
  · simpa [datum, datumCase385, selectedCase385] using h.selected 4

theorem refutesRepresentative388 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 202 W) : False := by
  apply Krenn.X5ResidualCase388.Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase388, selectedCase388] using h.selected 0
  · simpa [datum, datumCase388, selectedCase388] using h.selected 1
  · simpa [datum, datumCase388, selectedCase388] using h.selected 2
  · simpa [datum, datumCase388, selectedCase388] using h.selected 3
  · simpa [datum, datumCase388, selectedCase388] using h.selected 4

theorem refutesRepresentative429 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 213 W) : False := by
  apply Krenn.X5ResidualCase429.Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase429, selectedCase429] using h.selected 0
  · simpa [datum, datumCase429, selectedCase429] using h.selected 1
  · simpa [datum, datumCase429, selectedCase429] using h.selected 2
  · simpa [datum, datumCase429, selectedCase429] using h.selected 3
  · simpa [datum, datumCase429, selectedCase429] using h.selected 4

theorem refutesRepresentative516 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 216 W) : False := by
  apply Krenn.X5ResidualCase516.Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase516, selectedCase516] using h.selected 0
  · simpa [datum, datumCase516, selectedCase516] using h.selected 1
  · simpa [datum, datumCase516, selectedCase516] using h.selected 2
  · simpa [datum, datumCase516, selectedCase516] using h.selected 3
  · simpa [datum, datumCase516, selectedCase516] using h.selected 4

theorem refutesRepresentative642 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 270 W) : False := by
  apply Krenn.X5ResidualCase642.Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase642, selectedCase642] using h.selected 0
  · simpa [datum, datumCase642, selectedCase642] using h.selected 1
  · simpa [datum, datumCase642, selectedCase642] using h.selected 2
  · simpa [datum, datumCase642, selectedCase642] using h.selected 3
  · simpa [datum, datumCase642, selectedCase642] using h.selected 4

theorem refutesRepresentative817 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 295 W) : False := by
  apply Krenn.X5ResidualCase817.Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase817, selectedCase817] using h.selected 0
  · simpa [datum, datumCase817, selectedCase817] using h.selected 1
  · simpa [datum, datumCase817, selectedCase817] using h.selected 2
  · simpa [datum, datumCase817, selectedCase817] using h.selected 3
  · simpa [datum, datumCase817, selectedCase817] using h.selected 4

theorem refutesRepresentative861 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 309 W) : False := by
  apply Krenn.X5ResidualCase861.Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase861, selectedCase861] using h.selected 0
  · simpa [datum, datumCase861, selectedCase861] using h.selected 1
  · simpa [datum, datumCase861, selectedCase861] using h.selected 2
  · simpa [datum, datumCase861, selectedCase861] using h.selected 3
  · simpa [datum, datumCase861, selectedCase861] using h.selected 4

theorem refutesRepresentative863 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 311 W) : False := by
  apply Krenn.X5ResidualCase863.Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase863, selectedCase863] using h.selected 0
  · simpa [datum, datumCase863, selectedCase863] using h.selected 1
  · simpa [datum, datumCase863, selectedCase863] using h.selected 2
  · simpa [datum, datumCase863, selectedCase863] using h.selected 3
  · simpa [datum, datumCase863, selectedCase863] using h.selected 4

theorem refutesRepresentative1033 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 313 W) : False := by
  apply Krenn.X5ResidualCase1033.Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase1033, selectedCase1033] using h.selected 0
  · simpa [datum, datumCase1033, selectedCase1033] using h.selected 1
  · simpa [datum, datumCase1033, selectedCase1033] using h.selected 2
  · simpa [datum, datumCase1033, selectedCase1033] using h.selected 3
  · simpa [datum, datumCase1033, selectedCase1033] using h.selected 4

theorem refutesRepresentative1293 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 333 W) : False := by
  apply Krenn.X5ResidualCase1293.Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase1293, selectedCase1293] using h.selected 0
  · simpa [datum, datumCase1293, selectedCase1293] using h.selected 1
  · simpa [datum, datumCase1293, selectedCase1293] using h.selected 2
  · simpa [datum, datumCase1293, selectedCase1293] using h.selected 3
  · simpa [datum, datumCase1293, selectedCase1293] using h.selected 4

structure RefutedRepresentative where
  ordinal : Fin 336
  caseIndex : Fin 1296
  caseIndex_eq : representativeCase ordinal = caseIndex
  impossible : ∀ W, EqSystemN 6 3 W →
    NormalizedRepresentative ordinal W → False

def entry5 : RefutedRepresentative :=
  ⟨5, 5, by decide, refutesRepresentative5⟩

def entry84 : RefutedRepresentative :=
  ⟨66, 84, by decide, refutesRepresentative84⟩

def entry86 : RefutedRepresentative :=
  ⟨68, 86, by decide, refutesRepresentative86⟩

def entry98 : RefutedRepresentative :=
  ⟨80, 98, by decide, refutesRepresentative98⟩

def entry102 : RefutedRepresentative :=
  ⟨84, 102, by decide, refutesRepresentative102⟩

def entry131 : RefutedRepresentative :=
  ⟨95, 131, by decide, refutesRepresentative131⟩

def entry170 : RefutedRepresentative :=
  ⟨110, 170, by decide, refutesRepresentative170⟩

def entry304 : RefutedRepresentative :=
  ⟨160, 304, by decide, refutesRepresentative304⟩

def entry316 : RefutedRepresentative :=
  ⟨172, 316, by decide, refutesRepresentative316⟩

def entry385 : RefutedRepresentative :=
  ⟨199, 385, by decide, refutesRepresentative385⟩

def entry388 : RefutedRepresentative :=
  ⟨202, 388, by decide, refutesRepresentative388⟩

def entry429 : RefutedRepresentative :=
  ⟨213, 429, by decide, refutesRepresentative429⟩

def entry516 : RefutedRepresentative :=
  ⟨216, 516, by decide, refutesRepresentative516⟩

def entry642 : RefutedRepresentative :=
  ⟨270, 642, by decide, refutesRepresentative642⟩

def entry817 : RefutedRepresentative :=
  ⟨295, 817, by decide, refutesRepresentative817⟩

def entry861 : RefutedRepresentative :=
  ⟨309, 861, by decide, refutesRepresentative861⟩

def entry863 : RefutedRepresentative :=
  ⟨311, 863, by decide, refutesRepresentative863⟩

def entry1033 : RefutedRepresentative :=
  ⟨313, 1033, by decide, refutesRepresentative1033⟩

def entry1293 : RefutedRepresentative :=
  ⟨333, 1293, by decide, refutesRepresentative1293⟩

def residualRepresentatives : Fin 19 → RefutedRepresentative := ![
  entry5, entry84, entry86, entry98, entry102, entry131, entry170, entry304, entry316, entry385, entry388, entry429, entry516, entry642, entry817, entry861, entry863, entry1033, entry1293
]

def dispatchedCaseIndices : List Nat :=
  List.ofFn fun index => (residualRepresentatives index).caseIndex.val

theorem dispatchedCaseIndices_eq :
    dispatchedCaseIndices = Krenn.X5Residuals.residualCaseIndices := by
  decide

#print axioms Krenn.X5ResidualDispatch.dispatchedCaseIndices_eq
#print axioms Krenn.X5ResidualDispatch.refutesRepresentative5
#print axioms Krenn.X5ResidualDispatch.refutesRepresentative1293

end Krenn.X5ResidualDispatch

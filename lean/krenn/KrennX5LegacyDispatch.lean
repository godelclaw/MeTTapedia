import KrennX5SupportConnector
import KrennX5LegacyMigrated

/-!
Generated semantic dispatch from representative-indexed X5 normalization
predicates to every currently migrated historical refutation.

The generator derives each representative ordinal from the canonical
`representativeCase` table and rejects missing or duplicate indices.
-/

namespace Krenn.X5LegacyDispatch

open MonochromaticQuantumGraph
open Krenn.X5GaugeNormalizationData
open Krenn.X5SupportConnector

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem refutesRepresentative1 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 1 W) : False := by
  apply Krenn.X5Case1Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase1, selectedCase1] using h.selected 0
  · simpa [datum, datumCase1, selectedCase1] using h.selected 1
  · simpa [datum, datumCase1, selectedCase1] using h.selected 2
  · simpa [datum, datumCase1, selectedCase1] using h.selected 3
  · simpa [datum, datumCase1, selectedCase1] using h.selected 4

theorem refutesRepresentative3 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 3 W) : False := by
  apply Krenn.X5Case3Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase3, selectedCase3] using h.selected 0
  · simpa [datum, datumCase3, selectedCase3] using h.selected 1
  · simpa [datum, datumCase3, selectedCase3] using h.selected 2
  · simpa [datum, datumCase3, selectedCase3] using h.selected 3
  · simpa [datum, datumCase3, selectedCase3] using h.selected 4

theorem refutesRepresentative4 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 4 W) : False := by
  apply Krenn.X5Case4Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase4, selectedCase4] using h.selected 0
  · simpa [datum, datumCase4, selectedCase4] using h.selected 1
  · simpa [datum, datumCase4, selectedCase4] using h.selected 2
  · simpa [datum, datumCase4, selectedCase4] using h.selected 3
  · simpa [datum, datumCase4, selectedCase4] using h.selected 4

theorem refutesRepresentative6 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 6 W) : False := by
  apply Krenn.X5Case6Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase6, selectedCase6] using h.selected 0
  · simpa [datum, datumCase6, selectedCase6] using h.selected 1
  · simpa [datum, datumCase6, selectedCase6] using h.selected 2
  · simpa [datum, datumCase6, selectedCase6] using h.selected 3
  · simpa [datum, datumCase6, selectedCase6] using h.selected 4

theorem refutesRepresentative7 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 7 W) : False := by
  apply Krenn.X5Case7Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase7, selectedCase7] using h.selected 0
  · simpa [datum, datumCase7, selectedCase7] using h.selected 1
  · simpa [datum, datumCase7, selectedCase7] using h.selected 2
  · simpa [datum, datumCase7, selectedCase7] using h.selected 3
  · simpa [datum, datumCase7, selectedCase7] using h.selected 4

theorem refutesRepresentative8 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 8 W) : False := by
  apply Krenn.X5Case8Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase8, selectedCase8] using h.selected 0
  · simpa [datum, datumCase8, selectedCase8] using h.selected 1
  · simpa [datum, datumCase8, selectedCase8] using h.selected 2
  · simpa [datum, datumCase8, selectedCase8] using h.selected 3
  · simpa [datum, datumCase8, selectedCase8] using h.selected 4

theorem refutesRepresentative9 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 9 W) : False := by
  apply Krenn.X5Case9Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase9, selectedCase9] using h.selected 0
  · simpa [datum, datumCase9, selectedCase9] using h.selected 1
  · simpa [datum, datumCase9, selectedCase9] using h.selected 2
  · simpa [datum, datumCase9, selectedCase9] using h.selected 3
  · simpa [datum, datumCase9, selectedCase9] using h.selected 4

theorem refutesRepresentative10 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 10 W) : False := by
  apply Krenn.X5Case10Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase10, selectedCase10] using h.selected 0
  · simpa [datum, datumCase10, selectedCase10] using h.selected 1
  · simpa [datum, datumCase10, selectedCase10] using h.selected 2
  · simpa [datum, datumCase10, selectedCase10] using h.selected 3
  · simpa [datum, datumCase10, selectedCase10] using h.selected 4

theorem refutesRepresentative11 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 11 W) : False := by
  apply Krenn.X5Case11Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase11, selectedCase11] using h.selected 0
  · simpa [datum, datumCase11, selectedCase11] using h.selected 1
  · simpa [datum, datumCase11, selectedCase11] using h.selected 2
  · simpa [datum, datumCase11, selectedCase11] using h.selected 3
  · simpa [datum, datumCase11, selectedCase11] using h.selected 4

theorem refutesRepresentative13 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 13 W) : False := by
  apply Krenn.X5Case13Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase13, selectedCase13] using h.selected 0
  · simpa [datum, datumCase13, selectedCase13] using h.selected 1
  · simpa [datum, datumCase13, selectedCase13] using h.selected 2
  · simpa [datum, datumCase13, selectedCase13] using h.selected 3
  · simpa [datum, datumCase13, selectedCase13] using h.selected 4

theorem refutesRepresentative14 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 14 W) : False := by
  apply Krenn.X5Case14Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase14, selectedCase14] using h.selected 0
  · simpa [datum, datumCase14, selectedCase14] using h.selected 1
  · simpa [datum, datumCase14, selectedCase14] using h.selected 2
  · simpa [datum, datumCase14, selectedCase14] using h.selected 3
  · simpa [datum, datumCase14, selectedCase14] using h.selected 4

theorem refutesRepresentative15 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 15 W) : False := by
  apply Krenn.X5Case15Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase15, selectedCase15] using h.selected 0
  · simpa [datum, datumCase15, selectedCase15] using h.selected 1
  · simpa [datum, datumCase15, selectedCase15] using h.selected 2
  · simpa [datum, datumCase15, selectedCase15] using h.selected 3
  · simpa [datum, datumCase15, selectedCase15] using h.selected 4

theorem refutesRepresentative16 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 16 W) : False := by
  apply Krenn.X5Case16Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase16, selectedCase16] using h.selected 0
  · simpa [datum, datumCase16, selectedCase16] using h.selected 1
  · simpa [datum, datumCase16, selectedCase16] using h.selected 2
  · simpa [datum, datumCase16, selectedCase16] using h.selected 3
  · simpa [datum, datumCase16, selectedCase16] using h.selected 4

theorem refutesRepresentative17 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 17 W) : False := by
  apply Krenn.X5Case17Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase17, selectedCase17] using h.selected 0
  · simpa [datum, datumCase17, selectedCase17] using h.selected 1
  · simpa [datum, datumCase17, selectedCase17] using h.selected 2
  · simpa [datum, datumCase17, selectedCase17] using h.selected 3
  · simpa [datum, datumCase17, selectedCase17] using h.selected 4

theorem refutesRepresentative18 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 18 W) : False := by
  apply Krenn.X5Case18Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase18, selectedCase18] using h.selected 0
  · simpa [datum, datumCase18, selectedCase18] using h.selected 1
  · simpa [datum, datumCase18, selectedCase18] using h.selected 2
  · simpa [datum, datumCase18, selectedCase18] using h.selected 3
  · simpa [datum, datumCase18, selectedCase18] using h.selected 4

theorem refutesRepresentative19 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 19 W) : False := by
  apply Krenn.X5Case19Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase19, selectedCase19] using h.selected 0
  · simpa [datum, datumCase19, selectedCase19] using h.selected 1
  · simpa [datum, datumCase19, selectedCase19] using h.selected 2
  · simpa [datum, datumCase19, selectedCase19] using h.selected 3
  · simpa [datum, datumCase19, selectedCase19] using h.selected 4

theorem refutesRepresentative21 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 21 W) : False := by
  apply Krenn.X5Case21Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase21, selectedCase21] using h.selected 0
  · simpa [datum, datumCase21, selectedCase21] using h.selected 1
  · simpa [datum, datumCase21, selectedCase21] using h.selected 2
  · simpa [datum, datumCase21, selectedCase21] using h.selected 3
  · simpa [datum, datumCase21, selectedCase21] using h.selected 4

theorem refutesRepresentative22 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 22 W) : False := by
  apply Krenn.X5Case22Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase22, selectedCase22] using h.selected 0
  · simpa [datum, datumCase22, selectedCase22] using h.selected 1
  · simpa [datum, datumCase22, selectedCase22] using h.selected 2
  · simpa [datum, datumCase22, selectedCase22] using h.selected 3
  · simpa [datum, datumCase22, selectedCase22] using h.selected 4

theorem refutesRepresentative25 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 25 W) : False := by
  apply Krenn.X5Case25Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase25, selectedCase25] using h.selected 0
  · simpa [datum, datumCase25, selectedCase25] using h.selected 1
  · simpa [datum, datumCase25, selectedCase25] using h.selected 2
  · simpa [datum, datumCase25, selectedCase25] using h.selected 3
  · simpa [datum, datumCase25, selectedCase25] using h.selected 4

theorem refutesRepresentative27 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 27 W) : False := by
  apply Krenn.X5Case27Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase27, selectedCase27] using h.selected 0
  · simpa [datum, datumCase27, selectedCase27] using h.selected 1
  · simpa [datum, datumCase27, selectedCase27] using h.selected 2
  · simpa [datum, datumCase27, selectedCase27] using h.selected 3
  · simpa [datum, datumCase27, selectedCase27] using h.selected 4

theorem refutesRepresentative28 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 28 W) : False := by
  apply Krenn.X5Case28Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase28, selectedCase28] using h.selected 0
  · simpa [datum, datumCase28, selectedCase28] using h.selected 1
  · simpa [datum, datumCase28, selectedCase28] using h.selected 2
  · simpa [datum, datumCase28, selectedCase28] using h.selected 3
  · simpa [datum, datumCase28, selectedCase28] using h.selected 4

theorem refutesRepresentative29 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 29 W) : False := by
  apply Krenn.X5Case29Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase29, selectedCase29] using h.selected 0
  · simpa [datum, datumCase29, selectedCase29] using h.selected 1
  · simpa [datum, datumCase29, selectedCase29] using h.selected 2
  · simpa [datum, datumCase29, selectedCase29] using h.selected 3
  · simpa [datum, datumCase29, selectedCase29] using h.selected 4

theorem refutesRepresentative31 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 31 W) : False := by
  apply Krenn.X5Case31Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase31, selectedCase31] using h.selected 0
  · simpa [datum, datumCase31, selectedCase31] using h.selected 1
  · simpa [datum, datumCase31, selectedCase31] using h.selected 2
  · simpa [datum, datumCase31, selectedCase31] using h.selected 3
  · simpa [datum, datumCase31, selectedCase31] using h.selected 4

theorem refutesRepresentative33 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 33 W) : False := by
  apply Krenn.X5Case33Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase33, selectedCase33] using h.selected 0
  · simpa [datum, datumCase33, selectedCase33] using h.selected 1
  · simpa [datum, datumCase33, selectedCase33] using h.selected 2
  · simpa [datum, datumCase33, selectedCase33] using h.selected 3
  · simpa [datum, datumCase33, selectedCase33] using h.selected 4

theorem refutesRepresentative34 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 34 W) : False := by
  apply Krenn.X5Case34Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase34, selectedCase34] using h.selected 0
  · simpa [datum, datumCase34, selectedCase34] using h.selected 1
  · simpa [datum, datumCase34, selectedCase34] using h.selected 2
  · simpa [datum, datumCase34, selectedCase34] using h.selected 3
  · simpa [datum, datumCase34, selectedCase34] using h.selected 4

theorem refutesRepresentative42 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 36 W) : False := by
  apply Krenn.X5Case42Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase42, selectedCase42] using h.selected 0
  · simpa [datum, datumCase42, selectedCase42] using h.selected 1
  · simpa [datum, datumCase42, selectedCase42] using h.selected 2
  · simpa [datum, datumCase42, selectedCase42] using h.selected 3
  · simpa [datum, datumCase42, selectedCase42] using h.selected 4

theorem refutesRepresentative43 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 37 W) : False := by
  apply Krenn.X5Case43Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase43, selectedCase43] using h.selected 0
  · simpa [datum, datumCase43, selectedCase43] using h.selected 1
  · simpa [datum, datumCase43, selectedCase43] using h.selected 2
  · simpa [datum, datumCase43, selectedCase43] using h.selected 3
  · simpa [datum, datumCase43, selectedCase43] using h.selected 4

theorem refutesRepresentative44 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 38 W) : False := by
  apply Krenn.X5Case44Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase44, selectedCase44] using h.selected 0
  · simpa [datum, datumCase44, selectedCase44] using h.selected 1
  · simpa [datum, datumCase44, selectedCase44] using h.selected 2
  · simpa [datum, datumCase44, selectedCase44] using h.selected 3
  · simpa [datum, datumCase44, selectedCase44] using h.selected 4

theorem refutesRepresentative47 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 41 W) : False := by
  apply Krenn.X5Case47Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase47, selectedCase47] using h.selected 0
  · simpa [datum, datumCase47, selectedCase47] using h.selected 1
  · simpa [datum, datumCase47, selectedCase47] using h.selected 2
  · simpa [datum, datumCase47, selectedCase47] using h.selected 3
  · simpa [datum, datumCase47, selectedCase47] using h.selected 4

theorem refutesRepresentative49 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 43 W) : False := by
  apply Krenn.X5Case49Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase49, selectedCase49] using h.selected 0
  · simpa [datum, datumCase49, selectedCase49] using h.selected 1
  · simpa [datum, datumCase49, selectedCase49] using h.selected 2
  · simpa [datum, datumCase49, selectedCase49] using h.selected 3
  · simpa [datum, datumCase49, selectedCase49] using h.selected 4

theorem refutesRepresentative51 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 45 W) : False := by
  apply Krenn.X5Case51Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase51, selectedCase51] using h.selected 0
  · simpa [datum, datumCase51, selectedCase51] using h.selected 1
  · simpa [datum, datumCase51, selectedCase51] using h.selected 2
  · simpa [datum, datumCase51, selectedCase51] using h.selected 3
  · simpa [datum, datumCase51, selectedCase51] using h.selected 4

theorem refutesRepresentative52 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 46 W) : False := by
  apply Krenn.X5Case52Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase52, selectedCase52] using h.selected 0
  · simpa [datum, datumCase52, selectedCase52] using h.selected 1
  · simpa [datum, datumCase52, selectedCase52] using h.selected 2
  · simpa [datum, datumCase52, selectedCase52] using h.selected 3
  · simpa [datum, datumCase52, selectedCase52] using h.selected 4

theorem refutesRepresentative53 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 47 W) : False := by
  apply Krenn.X5Case53Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase53, selectedCase53] using h.selected 0
  · simpa [datum, datumCase53, selectedCase53] using h.selected 1
  · simpa [datum, datumCase53, selectedCase53] using h.selected 2
  · simpa [datum, datumCase53, selectedCase53] using h.selected 3
  · simpa [datum, datumCase53, selectedCase53] using h.selected 4

theorem refutesRepresentative54 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 48 W) : False := by
  apply Krenn.X5Case54Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase54, selectedCase54] using h.selected 0
  · simpa [datum, datumCase54, selectedCase54] using h.selected 1
  · simpa [datum, datumCase54, selectedCase54] using h.selected 2
  · simpa [datum, datumCase54, selectedCase54] using h.selected 3
  · simpa [datum, datumCase54, selectedCase54] using h.selected 4

theorem refutesRepresentative55 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 49 W) : False := by
  apply Krenn.X5Case55Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase55, selectedCase55] using h.selected 0
  · simpa [datum, datumCase55, selectedCase55] using h.selected 1
  · simpa [datum, datumCase55, selectedCase55] using h.selected 2
  · simpa [datum, datumCase55, selectedCase55] using h.selected 3
  · simpa [datum, datumCase55, selectedCase55] using h.selected 4

theorem refutesRepresentative56 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 50 W) : False := by
  apply Krenn.X5Case56Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase56, selectedCase56] using h.selected 0
  · simpa [datum, datumCase56, selectedCase56] using h.selected 1
  · simpa [datum, datumCase56, selectedCase56] using h.selected 2
  · simpa [datum, datumCase56, selectedCase56] using h.selected 3
  · simpa [datum, datumCase56, selectedCase56] using h.selected 4

theorem refutesRepresentative58 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 52 W) : False := by
  apply Krenn.X5Case58Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase58, selectedCase58] using h.selected 0
  · simpa [datum, datumCase58, selectedCase58] using h.selected 1
  · simpa [datum, datumCase58, selectedCase58] using h.selected 2
  · simpa [datum, datumCase58, selectedCase58] using h.selected 3
  · simpa [datum, datumCase58, selectedCase58] using h.selected 4

theorem refutesRepresentative60 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 54 W) : False := by
  apply Krenn.X5Case60Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase60, selectedCase60] using h.selected 0
  · simpa [datum, datumCase60, selectedCase60] using h.selected 1
  · simpa [datum, datumCase60, selectedCase60] using h.selected 2
  · simpa [datum, datumCase60, selectedCase60] using h.selected 3
  · simpa [datum, datumCase60, selectedCase60] using h.selected 4

theorem refutesRepresentative61 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 55 W) : False := by
  apply Krenn.X5Case61Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase61, selectedCase61] using h.selected 0
  · simpa [datum, datumCase61, selectedCase61] using h.selected 1
  · simpa [datum, datumCase61, selectedCase61] using h.selected 2
  · simpa [datum, datumCase61, selectedCase61] using h.selected 3
  · simpa [datum, datumCase61, selectedCase61] using h.selected 4

theorem refutesRepresentative63 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 57 W) : False := by
  apply Krenn.X5Case63Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase63, selectedCase63] using h.selected 0
  · simpa [datum, datumCase63, selectedCase63] using h.selected 1
  · simpa [datum, datumCase63, selectedCase63] using h.selected 2
  · simpa [datum, datumCase63, selectedCase63] using h.selected 3
  · simpa [datum, datumCase63, selectedCase63] using h.selected 4

theorem refutesRepresentative64 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 58 W) : False := by
  apply Krenn.X5Case64Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase64, selectedCase64] using h.selected 0
  · simpa [datum, datumCase64, selectedCase64] using h.selected 1
  · simpa [datum, datumCase64, selectedCase64] using h.selected 2
  · simpa [datum, datumCase64, selectedCase64] using h.selected 3
  · simpa [datum, datumCase64, selectedCase64] using h.selected 4

theorem refutesRepresentative65 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 59 W) : False := by
  apply Krenn.X5Case65Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase65, selectedCase65] using h.selected 0
  · simpa [datum, datumCase65, selectedCase65] using h.selected 1
  · simpa [datum, datumCase65, selectedCase65] using h.selected 2
  · simpa [datum, datumCase65, selectedCase65] using h.selected 3
  · simpa [datum, datumCase65, selectedCase65] using h.selected 4

theorem refutesRepresentative67 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 61 W) : False := by
  apply Krenn.X5Case67Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase67, selectedCase67] using h.selected 0
  · simpa [datum, datumCase67, selectedCase67] using h.selected 1
  · simpa [datum, datumCase67, selectedCase67] using h.selected 2
  · simpa [datum, datumCase67, selectedCase67] using h.selected 3
  · simpa [datum, datumCase67, selectedCase67] using h.selected 4

theorem refutesRepresentative68 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 62 W) : False := by
  apply Krenn.X5Case68Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase68, selectedCase68] using h.selected 0
  · simpa [datum, datumCase68, selectedCase68] using h.selected 1
  · simpa [datum, datumCase68, selectedCase68] using h.selected 2
  · simpa [datum, datumCase68, selectedCase68] using h.selected 3
  · simpa [datum, datumCase68, selectedCase68] using h.selected 4

theorem refutesRepresentative70 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 64 W) : False := by
  apply Krenn.X5Case70Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase70, selectedCase70] using h.selected 0
  · simpa [datum, datumCase70, selectedCase70] using h.selected 1
  · simpa [datum, datumCase70, selectedCase70] using h.selected 2
  · simpa [datum, datumCase70, selectedCase70] using h.selected 3
  · simpa [datum, datumCase70, selectedCase70] using h.selected 4

theorem refutesRepresentative85 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 67 W) : False := by
  apply Krenn.X5Case85Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase85, selectedCase85] using h.selected 0
  · simpa [datum, datumCase85, selectedCase85] using h.selected 1
  · simpa [datum, datumCase85, selectedCase85] using h.selected 2
  · simpa [datum, datumCase85, selectedCase85] using h.selected 3
  · simpa [datum, datumCase85, selectedCase85] using h.selected 4

theorem refutesRepresentative87 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 69 W) : False := by
  apply Krenn.X5Case87Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase87, selectedCase87] using h.selected 0
  · simpa [datum, datumCase87, selectedCase87] using h.selected 1
  · simpa [datum, datumCase87, selectedCase87] using h.selected 2
  · simpa [datum, datumCase87, selectedCase87] using h.selected 3
  · simpa [datum, datumCase87, selectedCase87] using h.selected 4

theorem refutesRepresentative88 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 70 W) : False := by
  apply Krenn.X5Case88Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase88, selectedCase88] using h.selected 0
  · simpa [datum, datumCase88, selectedCase88] using h.selected 1
  · simpa [datum, datumCase88, selectedCase88] using h.selected 2
  · simpa [datum, datumCase88, selectedCase88] using h.selected 3
  · simpa [datum, datumCase88, selectedCase88] using h.selected 4

theorem refutesRepresentative89 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 71 W) : False := by
  apply Krenn.X5Case89Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase89, selectedCase89] using h.selected 0
  · simpa [datum, datumCase89, selectedCase89] using h.selected 1
  · simpa [datum, datumCase89, selectedCase89] using h.selected 2
  · simpa [datum, datumCase89, selectedCase89] using h.selected 3
  · simpa [datum, datumCase89, selectedCase89] using h.selected 4

theorem refutesRepresentative91 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 73 W) : False := by
  apply Krenn.X5Case91Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase91, selectedCase91] using h.selected 0
  · simpa [datum, datumCase91, selectedCase91] using h.selected 1
  · simpa [datum, datumCase91, selectedCase91] using h.selected 2
  · simpa [datum, datumCase91, selectedCase91] using h.selected 3
  · simpa [datum, datumCase91, selectedCase91] using h.selected 4

theorem refutesRepresentative93 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 75 W) : False := by
  apply Krenn.X5Case93Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase93, selectedCase93] using h.selected 0
  · simpa [datum, datumCase93, selectedCase93] using h.selected 1
  · simpa [datum, datumCase93, selectedCase93] using h.selected 2
  · simpa [datum, datumCase93, selectedCase93] using h.selected 3
  · simpa [datum, datumCase93, selectedCase93] using h.selected 4

theorem refutesRepresentative94 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 76 W) : False := by
  apply Krenn.X5Case94Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase94, selectedCase94] using h.selected 0
  · simpa [datum, datumCase94, selectedCase94] using h.selected 1
  · simpa [datum, datumCase94, selectedCase94] using h.selected 2
  · simpa [datum, datumCase94, selectedCase94] using h.selected 3
  · simpa [datum, datumCase94, selectedCase94] using h.selected 4

theorem refutesRepresentative97 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 79 W) : False := by
  apply Krenn.X5Case97Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase97, selectedCase97] using h.selected 0
  · simpa [datum, datumCase97, selectedCase97] using h.selected 1
  · simpa [datum, datumCase97, selectedCase97] using h.selected 2
  · simpa [datum, datumCase97, selectedCase97] using h.selected 3
  · simpa [datum, datumCase97, selectedCase97] using h.selected 4

theorem refutesRepresentative99 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 81 W) : False := by
  apply Krenn.X5Case99Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase99, selectedCase99] using h.selected 0
  · simpa [datum, datumCase99, selectedCase99] using h.selected 1
  · simpa [datum, datumCase99, selectedCase99] using h.selected 2
  · simpa [datum, datumCase99, selectedCase99] using h.selected 3
  · simpa [datum, datumCase99, selectedCase99] using h.selected 4

theorem refutesRepresentative100 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 82 W) : False := by
  apply Krenn.X5Case100Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase100, selectedCase100] using h.selected 0
  · simpa [datum, datumCase100, selectedCase100] using h.selected 1
  · simpa [datum, datumCase100, selectedCase100] using h.selected 2
  · simpa [datum, datumCase100, selectedCase100] using h.selected 3
  · simpa [datum, datumCase100, selectedCase100] using h.selected 4

theorem refutesRepresentative101 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 83 W) : False := by
  apply Krenn.X5Case101Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase101, selectedCase101] using h.selected 0
  · simpa [datum, datumCase101, selectedCase101] using h.selected 1
  · simpa [datum, datumCase101, selectedCase101] using h.selected 2
  · simpa [datum, datumCase101, selectedCase101] using h.selected 3
  · simpa [datum, datumCase101, selectedCase101] using h.selected 4

theorem refutesRepresentative103 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 85 W) : False := by
  apply Krenn.X5Case103Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase103, selectedCase103] using h.selected 0
  · simpa [datum, datumCase103, selectedCase103] using h.selected 1
  · simpa [datum, datumCase103, selectedCase103] using h.selected 2
  · simpa [datum, datumCase103, selectedCase103] using h.selected 3
  · simpa [datum, datumCase103, selectedCase103] using h.selected 4

theorem refutesRepresentative105 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 87 W) : False := by
  apply Krenn.X5Case105Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase105, selectedCase105] using h.selected 0
  · simpa [datum, datumCase105, selectedCase105] using h.selected 1
  · simpa [datum, datumCase105, selectedCase105] using h.selected 2
  · simpa [datum, datumCase105, selectedCase105] using h.selected 3
  · simpa [datum, datumCase105, selectedCase105] using h.selected 4

theorem refutesRepresentative106 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 88 W) : False := by
  apply Krenn.X5Case106Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase106, selectedCase106] using h.selected 0
  · simpa [datum, datumCase106, selectedCase106] using h.selected 1
  · simpa [datum, datumCase106, selectedCase106] using h.selected 2
  · simpa [datum, datumCase106, selectedCase106] using h.selected 3
  · simpa [datum, datumCase106, selectedCase106] using h.selected 4

theorem refutesRepresentative126 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 90 W) : False := by
  apply Krenn.X5Case126Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase126, selectedCase126] using h.selected 0
  · simpa [datum, datumCase126, selectedCase126] using h.selected 1
  · simpa [datum, datumCase126, selectedCase126] using h.selected 2
  · simpa [datum, datumCase126, selectedCase126] using h.selected 3
  · simpa [datum, datumCase126, selectedCase126] using h.selected 4

theorem refutesRepresentative127 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 91 W) : False := by
  apply Krenn.X5Case127Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase127, selectedCase127] using h.selected 0
  · simpa [datum, datumCase127, selectedCase127] using h.selected 1
  · simpa [datum, datumCase127, selectedCase127] using h.selected 2
  · simpa [datum, datumCase127, selectedCase127] using h.selected 3
  · simpa [datum, datumCase127, selectedCase127] using h.selected 4

theorem refutesRepresentative128 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 92 W) : False := by
  apply Krenn.X5Case128Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase128, selectedCase128] using h.selected 0
  · simpa [datum, datumCase128, selectedCase128] using h.selected 1
  · simpa [datum, datumCase128, selectedCase128] using h.selected 2
  · simpa [datum, datumCase128, selectedCase128] using h.selected 3
  · simpa [datum, datumCase128, selectedCase128] using h.selected 4

theorem refutesRepresentative130 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 94 W) : False := by
  apply Krenn.X5Case130Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase130, selectedCase130] using h.selected 0
  · simpa [datum, datumCase130, selectedCase130] using h.selected 1
  · simpa [datum, datumCase130, selectedCase130] using h.selected 2
  · simpa [datum, datumCase130, selectedCase130] using h.selected 3
  · simpa [datum, datumCase130, selectedCase130] using h.selected 4

theorem refutesRepresentative132 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 96 W) : False := by
  apply Krenn.X5Case132Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase132, selectedCase132] using h.selected 0
  · simpa [datum, datumCase132, selectedCase132] using h.selected 1
  · simpa [datum, datumCase132, selectedCase132] using h.selected 2
  · simpa [datum, datumCase132, selectedCase132] using h.selected 3
  · simpa [datum, datumCase132, selectedCase132] using h.selected 4

theorem refutesRepresentative133 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 97 W) : False := by
  apply Krenn.X5Case133Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase133, selectedCase133] using h.selected 0
  · simpa [datum, datumCase133, selectedCase133] using h.selected 1
  · simpa [datum, datumCase133, selectedCase133] using h.selected 2
  · simpa [datum, datumCase133, selectedCase133] using h.selected 3
  · simpa [datum, datumCase133, selectedCase133] using h.selected 4

theorem refutesRepresentative134 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 98 W) : False := by
  apply Krenn.X5Case134Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase134, selectedCase134] using h.selected 0
  · simpa [datum, datumCase134, selectedCase134] using h.selected 1
  · simpa [datum, datumCase134, selectedCase134] using h.selected 2
  · simpa [datum, datumCase134, selectedCase134] using h.selected 3
  · simpa [datum, datumCase134, selectedCase134] using h.selected 4

theorem refutesRepresentative135 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 99 W) : False := by
  apply Krenn.X5Case135Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase135, selectedCase135] using h.selected 0
  · simpa [datum, datumCase135, selectedCase135] using h.selected 1
  · simpa [datum, datumCase135, selectedCase135] using h.selected 2
  · simpa [datum, datumCase135, selectedCase135] using h.selected 3
  · simpa [datum, datumCase135, selectedCase135] using h.selected 4

theorem refutesRepresentative136 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 100 W) : False := by
  apply Krenn.X5Case136Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase136, selectedCase136] using h.selected 0
  · simpa [datum, datumCase136, selectedCase136] using h.selected 1
  · simpa [datum, datumCase136, selectedCase136] using h.selected 2
  · simpa [datum, datumCase136, selectedCase136] using h.selected 3
  · simpa [datum, datumCase136, selectedCase136] using h.selected 4

theorem refutesRepresentative138 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 102 W) : False := by
  apply Krenn.X5Case138Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase138, selectedCase138] using h.selected 0
  · simpa [datum, datumCase138, selectedCase138] using h.selected 1
  · simpa [datum, datumCase138, selectedCase138] using h.selected 2
  · simpa [datum, datumCase138, selectedCase138] using h.selected 3
  · simpa [datum, datumCase138, selectedCase138] using h.selected 4

theorem refutesRepresentative139 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 103 W) : False := by
  apply Krenn.X5Case139Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase139, selectedCase139] using h.selected 0
  · simpa [datum, datumCase139, selectedCase139] using h.selected 1
  · simpa [datum, datumCase139, selectedCase139] using h.selected 2
  · simpa [datum, datumCase139, selectedCase139] using h.selected 3
  · simpa [datum, datumCase139, selectedCase139] using h.selected 4

theorem refutesRepresentative140 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 104 W) : False := by
  apply Krenn.X5Case140Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase140, selectedCase140] using h.selected 0
  · simpa [datum, datumCase140, selectedCase140] using h.selected 1
  · simpa [datum, datumCase140, selectedCase140] using h.selected 2
  · simpa [datum, datumCase140, selectedCase140] using h.selected 3
  · simpa [datum, datumCase140, selectedCase140] using h.selected 4

theorem refutesRepresentative142 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 106 W) : False := by
  apply Krenn.X5Case142Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase142, selectedCase142] using h.selected 0
  · simpa [datum, datumCase142, selectedCase142] using h.selected 1
  · simpa [datum, datumCase142, selectedCase142] using h.selected 2
  · simpa [datum, datumCase142, selectedCase142] using h.selected 3
  · simpa [datum, datumCase142, selectedCase142] using h.selected 4

theorem refutesRepresentative143 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 107 W) : False := by
  apply Krenn.X5Case143Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase143, selectedCase143] using h.selected 0
  · simpa [datum, datumCase143, selectedCase143] using h.selected 1
  · simpa [datum, datumCase143, selectedCase143] using h.selected 2
  · simpa [datum, datumCase143, selectedCase143] using h.selected 3
  · simpa [datum, datumCase143, selectedCase143] using h.selected 4

theorem refutesRepresentative171 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 111 W) : False := by
  apply Krenn.X5Case171Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase171, selectedCase171] using h.selected 0
  · simpa [datum, datumCase171, selectedCase171] using h.selected 1
  · simpa [datum, datumCase171, selectedCase171] using h.selected 2
  · simpa [datum, datumCase171, selectedCase171] using h.selected 3
  · simpa [datum, datumCase171, selectedCase171] using h.selected 4

theorem refutesRepresentative172 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 112 W) : False := by
  apply Krenn.X5Case172Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase172, selectedCase172] using h.selected 0
  · simpa [datum, datumCase172, selectedCase172] using h.selected 1
  · simpa [datum, datumCase172, selectedCase172] using h.selected 2
  · simpa [datum, datumCase172, selectedCase172] using h.selected 3
  · simpa [datum, datumCase172, selectedCase172] using h.selected 4

theorem refutesRepresentative173 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 113 W) : False := by
  apply Krenn.X5Case173Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase173, selectedCase173] using h.selected 0
  · simpa [datum, datumCase173, selectedCase173] using h.selected 1
  · simpa [datum, datumCase173, selectedCase173] using h.selected 2
  · simpa [datum, datumCase173, selectedCase173] using h.selected 3
  · simpa [datum, datumCase173, selectedCase173] using h.selected 4

theorem refutesRepresentative175 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 115 W) : False := by
  apply Krenn.X5Case175Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase175, selectedCase175] using h.selected 0
  · simpa [datum, datumCase175, selectedCase175] using h.selected 1
  · simpa [datum, datumCase175, selectedCase175] using h.selected 2
  · simpa [datum, datumCase175, selectedCase175] using h.selected 3
  · simpa [datum, datumCase175, selectedCase175] using h.selected 4

theorem refutesRepresentative177 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 117 W) : False := by
  apply Krenn.X5Case177Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase177, selectedCase177] using h.selected 0
  · simpa [datum, datumCase177, selectedCase177] using h.selected 1
  · simpa [datum, datumCase177, selectedCase177] using h.selected 2
  · simpa [datum, datumCase177, selectedCase177] using h.selected 3
  · simpa [datum, datumCase177, selectedCase177] using h.selected 4

theorem refutesRepresentative178 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 118 W) : False := by
  apply Krenn.X5Case178Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase178, selectedCase178] using h.selected 0
  · simpa [datum, datumCase178, selectedCase178] using h.selected 1
  · simpa [datum, datumCase178, selectedCase178] using h.selected 2
  · simpa [datum, datumCase178, selectedCase178] using h.selected 3
  · simpa [datum, datumCase178, selectedCase178] using h.selected 4

theorem refutesRepresentative211 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 121 W) : False := by
  apply Krenn.X5Case211Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase211, selectedCase211] using h.selected 0
  · simpa [datum, datumCase211, selectedCase211] using h.selected 1
  · simpa [datum, datumCase211, selectedCase211] using h.selected 2
  · simpa [datum, datumCase211, selectedCase211] using h.selected 3
  · simpa [datum, datumCase211, selectedCase211] using h.selected 4

theorem refutesRepresentative212 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 122 W) : False := by
  apply Krenn.X5Case212Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase212, selectedCase212] using h.selected 0
  · simpa [datum, datumCase212, selectedCase212] using h.selected 1
  · simpa [datum, datumCase212, selectedCase212] using h.selected 2
  · simpa [datum, datumCase212, selectedCase212] using h.selected 3
  · simpa [datum, datumCase212, selectedCase212] using h.selected 4

theorem refutesRepresentative214 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 124 W) : False := by
  apply Krenn.X5Case214Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase214, selectedCase214] using h.selected 0
  · simpa [datum, datumCase214, selectedCase214] using h.selected 1
  · simpa [datum, datumCase214, selectedCase214] using h.selected 2
  · simpa [datum, datumCase214, selectedCase214] using h.selected 3
  · simpa [datum, datumCase214, selectedCase214] using h.selected 4

theorem refutesRepresentative258 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 126 W) : False := by
  apply Krenn.X5Case258Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase258, selectedCase258] using h.selected 0
  · simpa [datum, datumCase258, selectedCase258] using h.selected 1
  · simpa [datum, datumCase258, selectedCase258] using h.selected 2
  · simpa [datum, datumCase258, selectedCase258] using h.selected 3
  · simpa [datum, datumCase258, selectedCase258] using h.selected 4

theorem refutesRepresentative260 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 128 W) : False := by
  apply Krenn.X5Case260Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase260, selectedCase260] using h.selected 0
  · simpa [datum, datumCase260, selectedCase260] using h.selected 1
  · simpa [datum, datumCase260, selectedCase260] using h.selected 2
  · simpa [datum, datumCase260, selectedCase260] using h.selected 3
  · simpa [datum, datumCase260, selectedCase260] using h.selected 4

theorem refutesRepresentative263 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 131 W) : False := by
  apply Krenn.X5Case263Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase263, selectedCase263] using h.selected 0
  · simpa [datum, datumCase263, selectedCase263] using h.selected 1
  · simpa [datum, datumCase263, selectedCase263] using h.selected 2
  · simpa [datum, datumCase263, selectedCase263] using h.selected 3
  · simpa [datum, datumCase263, selectedCase263] using h.selected 4

theorem refutesRepresentative264 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 132 W) : False := by
  apply Krenn.X5Case264Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase264, selectedCase264] using h.selected 0
  · simpa [datum, datumCase264, selectedCase264] using h.selected 1
  · simpa [datum, datumCase264, selectedCase264] using h.selected 2
  · simpa [datum, datumCase264, selectedCase264] using h.selected 3
  · simpa [datum, datumCase264, selectedCase264] using h.selected 4

theorem refutesRepresentative266 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 134 W) : False := by
  apply Krenn.X5Case266Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase266, selectedCase266] using h.selected 0
  · simpa [datum, datumCase266, selectedCase266] using h.selected 1
  · simpa [datum, datumCase266, selectedCase266] using h.selected 2
  · simpa [datum, datumCase266, selectedCase266] using h.selected 3
  · simpa [datum, datumCase266, selectedCase266] using h.selected 4

theorem refutesRepresentative267 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 135 W) : False := by
  apply Krenn.X5Case267Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase267, selectedCase267] using h.selected 0
  · simpa [datum, datumCase267, selectedCase267] using h.selected 1
  · simpa [datum, datumCase267, selectedCase267] using h.selected 2
  · simpa [datum, datumCase267, selectedCase267] using h.selected 3
  · simpa [datum, datumCase267, selectedCase267] using h.selected 4

theorem refutesRepresentative269 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 137 W) : False := by
  apply Krenn.X5Case269Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase269, selectedCase269] using h.selected 0
  · simpa [datum, datumCase269, selectedCase269] using h.selected 1
  · simpa [datum, datumCase269, selectedCase269] using h.selected 2
  · simpa [datum, datumCase269, selectedCase269] using h.selected 3
  · simpa [datum, datumCase269, selectedCase269] using h.selected 4

theorem refutesRepresentative270 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 138 W) : False := by
  apply Krenn.X5Case270Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase270, selectedCase270] using h.selected 0
  · simpa [datum, datumCase270, selectedCase270] using h.selected 1
  · simpa [datum, datumCase270, selectedCase270] using h.selected 2
  · simpa [datum, datumCase270, selectedCase270] using h.selected 3
  · simpa [datum, datumCase270, selectedCase270] using h.selected 4

theorem refutesRepresentative272 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 140 W) : False := by
  apply Krenn.X5Case272Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase272, selectedCase272] using h.selected 0
  · simpa [datum, datumCase272, selectedCase272] using h.selected 1
  · simpa [datum, datumCase272, selectedCase272] using h.selected 2
  · simpa [datum, datumCase272, selectedCase272] using h.selected 3
  · simpa [datum, datumCase272, selectedCase272] using h.selected 4

theorem refutesRepresentative274 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 142 W) : False := by
  apply Krenn.X5Case274Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase274, selectedCase274] using h.selected 0
  · simpa [datum, datumCase274, selectedCase274] using h.selected 1
  · simpa [datum, datumCase274, selectedCase274] using h.selected 2
  · simpa [datum, datumCase274, selectedCase274] using h.selected 3
  · simpa [datum, datumCase274, selectedCase274] using h.selected 4

theorem refutesRepresentative275 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 143 W) : False := by
  apply Krenn.X5Case275Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase275, selectedCase275] using h.selected 0
  · simpa [datum, datumCase275, selectedCase275] using h.selected 1
  · simpa [datum, datumCase275, selectedCase275] using h.selected 2
  · simpa [datum, datumCase275, selectedCase275] using h.selected 3
  · simpa [datum, datumCase275, selectedCase275] using h.selected 4

theorem refutesRepresentative276 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 144 W) : False := by
  apply Krenn.X5Case276Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase276, selectedCase276] using h.selected 0
  · simpa [datum, datumCase276, selectedCase276] using h.selected 1
  · simpa [datum, datumCase276, selectedCase276] using h.selected 2
  · simpa [datum, datumCase276, selectedCase276] using h.selected 3
  · simpa [datum, datumCase276, selectedCase276] using h.selected 4

theorem refutesRepresentative278 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 146 W) : False := by
  apply Krenn.X5Case278Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase278, selectedCase278] using h.selected 0
  · simpa [datum, datumCase278, selectedCase278] using h.selected 1
  · simpa [datum, datumCase278, selectedCase278] using h.selected 2
  · simpa [datum, datumCase278, selectedCase278] using h.selected 3
  · simpa [datum, datumCase278, selectedCase278] using h.selected 4

theorem refutesRepresentative279 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 147 W) : False := by
  apply Krenn.X5Case279Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase279, selectedCase279] using h.selected 0
  · simpa [datum, datumCase279, selectedCase279] using h.selected 1
  · simpa [datum, datumCase279, selectedCase279] using h.selected 2
  · simpa [datum, datumCase279, selectedCase279] using h.selected 3
  · simpa [datum, datumCase279, selectedCase279] using h.selected 4

theorem refutesRepresentative281 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 149 W) : False := by
  apply Krenn.X5Case281Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase281, selectedCase281] using h.selected 0
  · simpa [datum, datumCase281, selectedCase281] using h.selected 1
  · simpa [datum, datumCase281, selectedCase281] using h.selected 2
  · simpa [datum, datumCase281, selectedCase281] using h.selected 3
  · simpa [datum, datumCase281, selectedCase281] using h.selected 4

theorem refutesRepresentative282 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 150 W) : False := by
  apply Krenn.X5Case282Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase282, selectedCase282] using h.selected 0
  · simpa [datum, datumCase282, selectedCase282] using h.selected 1
  · simpa [datum, datumCase282, selectedCase282] using h.selected 2
  · simpa [datum, datumCase282, selectedCase282] using h.selected 3
  · simpa [datum, datumCase282, selectedCase282] using h.selected 4

theorem refutesRepresentative283 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 151 W) : False := by
  apply Krenn.X5Case283Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase283, selectedCase283] using h.selected 0
  · simpa [datum, datumCase283, selectedCase283] using h.selected 1
  · simpa [datum, datumCase283, selectedCase283] using h.selected 2
  · simpa [datum, datumCase283, selectedCase283] using h.selected 3
  · simpa [datum, datumCase283, selectedCase283] using h.selected 4

theorem refutesRepresentative284 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 152 W) : False := by
  apply Krenn.X5Case284Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase284, selectedCase284] using h.selected 0
  · simpa [datum, datumCase284, selectedCase284] using h.selected 1
  · simpa [datum, datumCase284, selectedCase284] using h.selected 2
  · simpa [datum, datumCase284, selectedCase284] using h.selected 3
  · simpa [datum, datumCase284, selectedCase284] using h.selected 4

theorem refutesRepresentative287 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 155 W) : False := by
  apply Krenn.X5Case287Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase287, selectedCase287] using h.selected 0
  · simpa [datum, datumCase287, selectedCase287] using h.selected 1
  · simpa [datum, datumCase287, selectedCase287] using h.selected 2
  · simpa [datum, datumCase287, selectedCase287] using h.selected 3
  · simpa [datum, datumCase287, selectedCase287] using h.selected 4

theorem refutesRepresentative300 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 156 W) : False := by
  apply Krenn.X5Case300Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase300, selectedCase300] using h.selected 0
  · simpa [datum, datumCase300, selectedCase300] using h.selected 1
  · simpa [datum, datumCase300, selectedCase300] using h.selected 2
  · simpa [datum, datumCase300, selectedCase300] using h.selected 3
  · simpa [datum, datumCase300, selectedCase300] using h.selected 4

theorem refutesRepresentative302 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 158 W) : False := by
  apply Krenn.X5Case302Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase302, selectedCase302] using h.selected 0
  · simpa [datum, datumCase302, selectedCase302] using h.selected 1
  · simpa [datum, datumCase302, selectedCase302] using h.selected 2
  · simpa [datum, datumCase302, selectedCase302] using h.selected 3
  · simpa [datum, datumCase302, selectedCase302] using h.selected 4

theorem refutesRepresentative303 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 159 W) : False := by
  apply Krenn.X5Case303Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase303, selectedCase303] using h.selected 0
  · simpa [datum, datumCase303, selectedCase303] using h.selected 1
  · simpa [datum, datumCase303, selectedCase303] using h.selected 2
  · simpa [datum, datumCase303, selectedCase303] using h.selected 3
  · simpa [datum, datumCase303, selectedCase303] using h.selected 4

theorem refutesRepresentative305 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 161 W) : False := by
  apply Krenn.X5Case305Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase305, selectedCase305] using h.selected 0
  · simpa [datum, datumCase305, selectedCase305] using h.selected 1
  · simpa [datum, datumCase305, selectedCase305] using h.selected 2
  · simpa [datum, datumCase305, selectedCase305] using h.selected 3
  · simpa [datum, datumCase305, selectedCase305] using h.selected 4

theorem refutesRepresentative306 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 162 W) : False := by
  apply Krenn.X5Case306Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase306, selectedCase306] using h.selected 0
  · simpa [datum, datumCase306, selectedCase306] using h.selected 1
  · simpa [datum, datumCase306, selectedCase306] using h.selected 2
  · simpa [datum, datumCase306, selectedCase306] using h.selected 3
  · simpa [datum, datumCase306, selectedCase306] using h.selected 4

theorem refutesRepresentative308 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 164 W) : False := by
  apply Krenn.X5Case308Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase308, selectedCase308] using h.selected 0
  · simpa [datum, datumCase308, selectedCase308] using h.selected 1
  · simpa [datum, datumCase308, selectedCase308] using h.selected 2
  · simpa [datum, datumCase308, selectedCase308] using h.selected 3
  · simpa [datum, datumCase308, selectedCase308] using h.selected 4

theorem refutesRepresentative311 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 167 W) : False := by
  apply Krenn.X5Case311Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase311, selectedCase311] using h.selected 0
  · simpa [datum, datumCase311, selectedCase311] using h.selected 1
  · simpa [datum, datumCase311, selectedCase311] using h.selected 2
  · simpa [datum, datumCase311, selectedCase311] using h.selected 3
  · simpa [datum, datumCase311, selectedCase311] using h.selected 4

theorem refutesRepresentative312 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 168 W) : False := by
  apply Krenn.X5Case312Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase312, selectedCase312] using h.selected 0
  · simpa [datum, datumCase312, selectedCase312] using h.selected 1
  · simpa [datum, datumCase312, selectedCase312] using h.selected 2
  · simpa [datum, datumCase312, selectedCase312] using h.selected 3
  · simpa [datum, datumCase312, selectedCase312] using h.selected 4

theorem refutesRepresentative314 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 170 W) : False := by
  apply Krenn.X5Case314Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase314, selectedCase314] using h.selected 0
  · simpa [datum, datumCase314, selectedCase314] using h.selected 1
  · simpa [datum, datumCase314, selectedCase314] using h.selected 2
  · simpa [datum, datumCase314, selectedCase314] using h.selected 3
  · simpa [datum, datumCase314, selectedCase314] using h.selected 4

theorem refutesRepresentative315 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 171 W) : False := by
  apply Krenn.X5Case315Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase315, selectedCase315] using h.selected 0
  · simpa [datum, datumCase315, selectedCase315] using h.selected 1
  · simpa [datum, datumCase315, selectedCase315] using h.selected 2
  · simpa [datum, datumCase315, selectedCase315] using h.selected 3
  · simpa [datum, datumCase315, selectedCase315] using h.selected 4

theorem refutesRepresentative317 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 173 W) : False := by
  apply Krenn.X5Case317Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase317, selectedCase317] using h.selected 0
  · simpa [datum, datumCase317, selectedCase317] using h.selected 1
  · simpa [datum, datumCase317, selectedCase317] using h.selected 2
  · simpa [datum, datumCase317, selectedCase317] using h.selected 3
  · simpa [datum, datumCase317, selectedCase317] using h.selected 4

theorem refutesRepresentative318 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 174 W) : False := by
  apply Krenn.X5Case318Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase318, selectedCase318] using h.selected 0
  · simpa [datum, datumCase318, selectedCase318] using h.selected 1
  · simpa [datum, datumCase318, selectedCase318] using h.selected 2
  · simpa [datum, datumCase318, selectedCase318] using h.selected 3
  · simpa [datum, datumCase318, selectedCase318] using h.selected 4

theorem refutesRepresentative319 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 175 W) : False := by
  apply Krenn.X5Case319Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase319, selectedCase319] using h.selected 0
  · simpa [datum, datumCase319, selectedCase319] using h.selected 1
  · simpa [datum, datumCase319, selectedCase319] using h.selected 2
  · simpa [datum, datumCase319, selectedCase319] using h.selected 3
  · simpa [datum, datumCase319, selectedCase319] using h.selected 4

theorem refutesRepresentative320 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 176 W) : False := by
  apply Krenn.X5Case320Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase320, selectedCase320] using h.selected 0
  · simpa [datum, datumCase320, selectedCase320] using h.selected 1
  · simpa [datum, datumCase320, selectedCase320] using h.selected 2
  · simpa [datum, datumCase320, selectedCase320] using h.selected 3
  · simpa [datum, datumCase320, selectedCase320] using h.selected 4

theorem refutesRepresentative323 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 179 W) : False := by
  apply Krenn.X5Case323Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase323, selectedCase323] using h.selected 0
  · simpa [datum, datumCase323, selectedCase323] using h.selected 1
  · simpa [datum, datumCase323, selectedCase323] using h.selected 2
  · simpa [datum, datumCase323, selectedCase323] using h.selected 3
  · simpa [datum, datumCase323, selectedCase323] using h.selected 4

theorem refutesRepresentative342 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 180 W) : False := by
  apply Krenn.X5Case342Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase342, selectedCase342] using h.selected 0
  · simpa [datum, datumCase342, selectedCase342] using h.selected 1
  · simpa [datum, datumCase342, selectedCase342] using h.selected 2
  · simpa [datum, datumCase342, selectedCase342] using h.selected 3
  · simpa [datum, datumCase342, selectedCase342] using h.selected 4

theorem refutesRepresentative344 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 182 W) : False := by
  apply Krenn.X5Case344Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase344, selectedCase344] using h.selected 0
  · simpa [datum, datumCase344, selectedCase344] using h.selected 1
  · simpa [datum, datumCase344, selectedCase344] using h.selected 2
  · simpa [datum, datumCase344, selectedCase344] using h.selected 3
  · simpa [datum, datumCase344, selectedCase344] using h.selected 4

theorem refutesRepresentative346 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 184 W) : False := by
  apply Krenn.X5Case346Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase346, selectedCase346] using h.selected 0
  · simpa [datum, datumCase346, selectedCase346] using h.selected 1
  · simpa [datum, datumCase346, selectedCase346] using h.selected 2
  · simpa [datum, datumCase346, selectedCase346] using h.selected 3
  · simpa [datum, datumCase346, selectedCase346] using h.selected 4

theorem refutesRepresentative348 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 186 W) : False := by
  apply Krenn.X5Case348Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase348, selectedCase348] using h.selected 0
  · simpa [datum, datumCase348, selectedCase348] using h.selected 1
  · simpa [datum, datumCase348, selectedCase348] using h.selected 2
  · simpa [datum, datumCase348, selectedCase348] using h.selected 3
  · simpa [datum, datumCase348, selectedCase348] using h.selected 4

theorem refutesRepresentative350 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 188 W) : False := by
  apply Krenn.X5Case350Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase350, selectedCase350] using h.selected 0
  · simpa [datum, datumCase350, selectedCase350] using h.selected 1
  · simpa [datum, datumCase350, selectedCase350] using h.selected 2
  · simpa [datum, datumCase350, selectedCase350] using h.selected 3
  · simpa [datum, datumCase350, selectedCase350] using h.selected 4

theorem refutesRepresentative353 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 191 W) : False := by
  apply Krenn.X5Case353Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase353, selectedCase353] using h.selected 0
  · simpa [datum, datumCase353, selectedCase353] using h.selected 1
  · simpa [datum, datumCase353, selectedCase353] using h.selected 2
  · simpa [datum, datumCase353, selectedCase353] using h.selected 3
  · simpa [datum, datumCase353, selectedCase353] using h.selected 4

theorem refutesRepresentative354 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 192 W) : False := by
  apply Krenn.X5Case354Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase354, selectedCase354] using h.selected 0
  · simpa [datum, datumCase354, selectedCase354] using h.selected 1
  · simpa [datum, datumCase354, selectedCase354] using h.selected 2
  · simpa [datum, datumCase354, selectedCase354] using h.selected 3
  · simpa [datum, datumCase354, selectedCase354] using h.selected 4

theorem refutesRepresentative355 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 193 W) : False := by
  apply Krenn.X5Case355Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase355, selectedCase355] using h.selected 0
  · simpa [datum, datumCase355, selectedCase355] using h.selected 1
  · simpa [datum, datumCase355, selectedCase355] using h.selected 2
  · simpa [datum, datumCase355, selectedCase355] using h.selected 3
  · simpa [datum, datumCase355, selectedCase355] using h.selected 4

theorem refutesRepresentative356 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 194 W) : False := by
  apply Krenn.X5Case356Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase356, selectedCase356] using h.selected 0
  · simpa [datum, datumCase356, selectedCase356] using h.selected 1
  · simpa [datum, datumCase356, selectedCase356] using h.selected 2
  · simpa [datum, datumCase356, selectedCase356] using h.selected 3
  · simpa [datum, datumCase356, selectedCase356] using h.selected 4

theorem refutesRepresentative358 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 196 W) : False := by
  apply Krenn.X5Case358Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase358, selectedCase358] using h.selected 0
  · simpa [datum, datumCase358, selectedCase358] using h.selected 1
  · simpa [datum, datumCase358, selectedCase358] using h.selected 2
  · simpa [datum, datumCase358, selectedCase358] using h.selected 3
  · simpa [datum, datumCase358, selectedCase358] using h.selected 4

theorem refutesRepresentative384 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 198 W) : False := by
  apply Krenn.X5Case384Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase384, selectedCase384] using h.selected 0
  · simpa [datum, datumCase384, selectedCase384] using h.selected 1
  · simpa [datum, datumCase384, selectedCase384] using h.selected 2
  · simpa [datum, datumCase384, selectedCase384] using h.selected 3
  · simpa [datum, datumCase384, selectedCase384] using h.selected 4

theorem refutesRepresentative386 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 200 W) : False := by
  apply Krenn.X5Case386Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase386, selectedCase386] using h.selected 0
  · simpa [datum, datumCase386, selectedCase386] using h.selected 1
  · simpa [datum, datumCase386, selectedCase386] using h.selected 2
  · simpa [datum, datumCase386, selectedCase386] using h.selected 3
  · simpa [datum, datumCase386, selectedCase386] using h.selected 4

theorem refutesRepresentative387 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 201 W) : False := by
  apply Krenn.X5Case387Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase387, selectedCase387] using h.selected 0
  · simpa [datum, datumCase387, selectedCase387] using h.selected 1
  · simpa [datum, datumCase387, selectedCase387] using h.selected 2
  · simpa [datum, datumCase387, selectedCase387] using h.selected 3
  · simpa [datum, datumCase387, selectedCase387] using h.selected 4

theorem refutesRepresentative389 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 203 W) : False := by
  apply Krenn.X5Case389Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase389, selectedCase389] using h.selected 0
  · simpa [datum, datumCase389, selectedCase389] using h.selected 1
  · simpa [datum, datumCase389, selectedCase389] using h.selected 2
  · simpa [datum, datumCase389, selectedCase389] using h.selected 3
  · simpa [datum, datumCase389, selectedCase389] using h.selected 4

theorem refutesRepresentative390 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 204 W) : False := by
  apply Krenn.X5Case390Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase390, selectedCase390] using h.selected 0
  · simpa [datum, datumCase390, selectedCase390] using h.selected 1
  · simpa [datum, datumCase390, selectedCase390] using h.selected 2
  · simpa [datum, datumCase390, selectedCase390] using h.selected 3
  · simpa [datum, datumCase390, selectedCase390] using h.selected 4

theorem refutesRepresentative392 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 206 W) : False := by
  apply Krenn.X5Case392Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase392, selectedCase392] using h.selected 0
  · simpa [datum, datumCase392, selectedCase392] using h.selected 1
  · simpa [datum, datumCase392, selectedCase392] using h.selected 2
  · simpa [datum, datumCase392, selectedCase392] using h.selected 3
  · simpa [datum, datumCase392, selectedCase392] using h.selected 4

theorem refutesRepresentative395 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 209 W) : False := by
  apply Krenn.X5Case395Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase395, selectedCase395] using h.selected 0
  · simpa [datum, datumCase395, selectedCase395] using h.selected 1
  · simpa [datum, datumCase395, selectedCase395] using h.selected 2
  · simpa [datum, datumCase395, selectedCase395] using h.selected 3
  · simpa [datum, datumCase395, selectedCase395] using h.selected 4

theorem refutesRepresentative426 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 210 W) : False := by
  apply Krenn.X5Case426Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase426, selectedCase426] using h.selected 0
  · simpa [datum, datumCase426, selectedCase426] using h.selected 1
  · simpa [datum, datumCase426, selectedCase426] using h.selected 2
  · simpa [datum, datumCase426, selectedCase426] using h.selected 3
  · simpa [datum, datumCase426, selectedCase426] using h.selected 4

theorem refutesRepresentative427 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 211 W) : False := by
  apply Krenn.X5Case427Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase427, selectedCase427] using h.selected 0
  · simpa [datum, datumCase427, selectedCase427] using h.selected 1
  · simpa [datum, datumCase427, selectedCase427] using h.selected 2
  · simpa [datum, datumCase427, selectedCase427] using h.selected 3
  · simpa [datum, datumCase427, selectedCase427] using h.selected 4

theorem refutesRepresentative428 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 212 W) : False := by
  apply Krenn.X5Case428Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase428, selectedCase428] using h.selected 0
  · simpa [datum, datumCase428, selectedCase428] using h.selected 1
  · simpa [datum, datumCase428, selectedCase428] using h.selected 2
  · simpa [datum, datumCase428, selectedCase428] using h.selected 3
  · simpa [datum, datumCase428, selectedCase428] using h.selected 4

theorem refutesRepresentative430 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 214 W) : False := by
  apply Krenn.X5Case430Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase430, selectedCase430] using h.selected 0
  · simpa [datum, datumCase430, selectedCase430] using h.selected 1
  · simpa [datum, datumCase430, selectedCase430] using h.selected 2
  · simpa [datum, datumCase430, selectedCase430] using h.selected 3
  · simpa [datum, datumCase430, selectedCase430] using h.selected 4

theorem refutesRepresentative517 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 217 W) : False := by
  apply Krenn.X5Case517Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase517, selectedCase517] using h.selected 0
  · simpa [datum, datumCase517, selectedCase517] using h.selected 1
  · simpa [datum, datumCase517, selectedCase517] using h.selected 2
  · simpa [datum, datumCase517, selectedCase517] using h.selected 3
  · simpa [datum, datumCase517, selectedCase517] using h.selected 4

theorem refutesRepresentative519 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 219 W) : False := by
  apply Krenn.X5Case519Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase519, selectedCase519] using h.selected 0
  · simpa [datum, datumCase519, selectedCase519] using h.selected 1
  · simpa [datum, datumCase519, selectedCase519] using h.selected 2
  · simpa [datum, datumCase519, selectedCase519] using h.selected 3
  · simpa [datum, datumCase519, selectedCase519] using h.selected 4

theorem refutesRepresentative521 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 221 W) : False := by
  apply Krenn.X5Case521Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase521, selectedCase521] using h.selected 0
  · simpa [datum, datumCase521, selectedCase521] using h.selected 1
  · simpa [datum, datumCase521, selectedCase521] using h.selected 2
  · simpa [datum, datumCase521, selectedCase521] using h.selected 3
  · simpa [datum, datumCase521, selectedCase521] using h.selected 4

theorem refutesRepresentative523 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 223 W) : False := by
  apply Krenn.X5Case523Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase523, selectedCase523] using h.selected 0
  · simpa [datum, datumCase523, selectedCase523] using h.selected 1
  · simpa [datum, datumCase523, selectedCase523] using h.selected 2
  · simpa [datum, datumCase523, selectedCase523] using h.selected 3
  · simpa [datum, datumCase523, selectedCase523] using h.selected 4

theorem refutesRepresentative524 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 224 W) : False := by
  apply Krenn.X5Case524Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase524, selectedCase524] using h.selected 0
  · simpa [datum, datumCase524, selectedCase524] using h.selected 1
  · simpa [datum, datumCase524, selectedCase524] using h.selected 2
  · simpa [datum, datumCase524, selectedCase524] using h.selected 3
  · simpa [datum, datumCase524, selectedCase524] using h.selected 4

theorem refutesRepresentative525 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 225 W) : False := by
  apply Krenn.X5Case525Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase525, selectedCase525] using h.selected 0
  · simpa [datum, datumCase525, selectedCase525] using h.selected 1
  · simpa [datum, datumCase525, selectedCase525] using h.selected 2
  · simpa [datum, datumCase525, selectedCase525] using h.selected 3
  · simpa [datum, datumCase525, selectedCase525] using h.selected 4

theorem refutesRepresentative526 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 226 W) : False := by
  apply Krenn.X5Case526Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase526, selectedCase526] using h.selected 0
  · simpa [datum, datumCase526, selectedCase526] using h.selected 1
  · simpa [datum, datumCase526, selectedCase526] using h.selected 2
  · simpa [datum, datumCase526, selectedCase526] using h.selected 3
  · simpa [datum, datumCase526, selectedCase526] using h.selected 4

theorem refutesRepresentative527 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 227 W) : False := by
  apply Krenn.X5Case527Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase527, selectedCase527] using h.selected 0
  · simpa [datum, datumCase527, selectedCase527] using h.selected 1
  · simpa [datum, datumCase527, selectedCase527] using h.selected 2
  · simpa [datum, datumCase527, selectedCase527] using h.selected 3
  · simpa [datum, datumCase527, selectedCase527] using h.selected 4

theorem refutesRepresentative529 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 229 W) : False := by
  apply Krenn.X5Case529Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase529, selectedCase529] using h.selected 0
  · simpa [datum, datumCase529, selectedCase529] using h.selected 1
  · simpa [datum, datumCase529, selectedCase529] using h.selected 2
  · simpa [datum, datumCase529, selectedCase529] using h.selected 3
  · simpa [datum, datumCase529, selectedCase529] using h.selected 4

theorem refutesRepresentative531 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 231 W) : False := by
  apply Krenn.X5Case531Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase531, selectedCase531] using h.selected 0
  · simpa [datum, datumCase531, selectedCase531] using h.selected 1
  · simpa [datum, datumCase531, selectedCase531] using h.selected 2
  · simpa [datum, datumCase531, selectedCase531] using h.selected 3
  · simpa [datum, datumCase531, selectedCase531] using h.selected 4

theorem refutesRepresentative533 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 233 W) : False := by
  apply Krenn.X5Case533Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase533, selectedCase533] using h.selected 0
  · simpa [datum, datumCase533, selectedCase533] using h.selected 1
  · simpa [datum, datumCase533, selectedCase533] using h.selected 2
  · simpa [datum, datumCase533, selectedCase533] using h.selected 3
  · simpa [datum, datumCase533, selectedCase533] using h.selected 4

theorem refutesRepresentative535 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 235 W) : False := by
  apply Krenn.X5Case535Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase535, selectedCase535] using h.selected 0
  · simpa [datum, datumCase535, selectedCase535] using h.selected 1
  · simpa [datum, datumCase535, selectedCase535] using h.selected 2
  · simpa [datum, datumCase535, selectedCase535] using h.selected 3
  · simpa [datum, datumCase535, selectedCase535] using h.selected 4

theorem refutesRepresentative537 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 237 W) : False := by
  apply Krenn.X5Case537Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase537, selectedCase537] using h.selected 0
  · simpa [datum, datumCase537, selectedCase537] using h.selected 1
  · simpa [datum, datumCase537, selectedCase537] using h.selected 2
  · simpa [datum, datumCase537, selectedCase537] using h.selected 3
  · simpa [datum, datumCase537, selectedCase537] using h.selected 4

theorem refutesRepresentative538 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 238 W) : False := by
  apply Krenn.X5Case538Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase538, selectedCase538] using h.selected 0
  · simpa [datum, datumCase538, selectedCase538] using h.selected 1
  · simpa [datum, datumCase538, selectedCase538] using h.selected 2
  · simpa [datum, datumCase538, selectedCase538] using h.selected 3
  · simpa [datum, datumCase538, selectedCase538] using h.selected 4

theorem refutesRepresentative539 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 239 W) : False := by
  apply Krenn.X5Case539Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase539, selectedCase539] using h.selected 0
  · simpa [datum, datumCase539, selectedCase539] using h.selected 1
  · simpa [datum, datumCase539, selectedCase539] using h.selected 2
  · simpa [datum, datumCase539, selectedCase539] using h.selected 3
  · simpa [datum, datumCase539, selectedCase539] using h.selected 4

theorem refutesRepresentative558 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 240 W) : False := by
  apply Krenn.X5Case558Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase558, selectedCase558] using h.selected 0
  · simpa [datum, datumCase558, selectedCase558] using h.selected 1
  · simpa [datum, datumCase558, selectedCase558] using h.selected 2
  · simpa [datum, datumCase558, selectedCase558] using h.selected 3
  · simpa [datum, datumCase558, selectedCase558] using h.selected 4

theorem refutesRepresentative560 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 242 W) : False := by
  apply Krenn.X5Case560Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase560, selectedCase560] using h.selected 0
  · simpa [datum, datumCase560, selectedCase560] using h.selected 1
  · simpa [datum, datumCase560, selectedCase560] using h.selected 2
  · simpa [datum, datumCase560, selectedCase560] using h.selected 3
  · simpa [datum, datumCase560, selectedCase560] using h.selected 4

theorem refutesRepresentative561 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 243 W) : False := by
  apply Krenn.X5Case561Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase561, selectedCase561] using h.selected 0
  · simpa [datum, datumCase561, selectedCase561] using h.selected 1
  · simpa [datum, datumCase561, selectedCase561] using h.selected 2
  · simpa [datum, datumCase561, selectedCase561] using h.selected 3
  · simpa [datum, datumCase561, selectedCase561] using h.selected 4

theorem refutesRepresentative564 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 246 W) : False := by
  apply Krenn.X5Case564Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase564, selectedCase564] using h.selected 0
  · simpa [datum, datumCase564, selectedCase564] using h.selected 1
  · simpa [datum, datumCase564, selectedCase564] using h.selected 2
  · simpa [datum, datumCase564, selectedCase564] using h.selected 3
  · simpa [datum, datumCase564, selectedCase564] using h.selected 4

theorem refutesRepresentative567 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 249 W) : False := by
  apply Krenn.X5Case567Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase567, selectedCase567] using h.selected 0
  · simpa [datum, datumCase567, selectedCase567] using h.selected 1
  · simpa [datum, datumCase567, selectedCase567] using h.selected 2
  · simpa [datum, datumCase567, selectedCase567] using h.selected 3
  · simpa [datum, datumCase567, selectedCase567] using h.selected 4

theorem refutesRepresentative569 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 251 W) : False := by
  apply Krenn.X5Case569Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase569, selectedCase569] using h.selected 0
  · simpa [datum, datumCase569, selectedCase569] using h.selected 1
  · simpa [datum, datumCase569, selectedCase569] using h.selected 2
  · simpa [datum, datumCase569, selectedCase569] using h.selected 3
  · simpa [datum, datumCase569, selectedCase569] using h.selected 4

theorem refutesRepresentative571 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 253 W) : False := by
  apply Krenn.X5Case571Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase571, selectedCase571] using h.selected 0
  · simpa [datum, datumCase571, selectedCase571] using h.selected 1
  · simpa [datum, datumCase571, selectedCase571] using h.selected 2
  · simpa [datum, datumCase571, selectedCase571] using h.selected 3
  · simpa [datum, datumCase571, selectedCase571] using h.selected 4

theorem refutesRepresentative572 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 254 W) : False := by
  apply Krenn.X5Case572Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase572, selectedCase572] using h.selected 0
  · simpa [datum, datumCase572, selectedCase572] using h.selected 1
  · simpa [datum, datumCase572, selectedCase572] using h.selected 2
  · simpa [datum, datumCase572, selectedCase572] using h.selected 3
  · simpa [datum, datumCase572, selectedCase572] using h.selected 4

theorem refutesRepresentative573 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 255 W) : False := by
  apply Krenn.X5Case573Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase573, selectedCase573] using h.selected 0
  · simpa [datum, datumCase573, selectedCase573] using h.selected 1
  · simpa [datum, datumCase573, selectedCase573] using h.selected 2
  · simpa [datum, datumCase573, selectedCase573] using h.selected 3
  · simpa [datum, datumCase573, selectedCase573] using h.selected 4

theorem refutesRepresentative574 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 256 W) : False := by
  apply Krenn.X5Case574Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase574, selectedCase574] using h.selected 0
  · simpa [datum, datumCase574, selectedCase574] using h.selected 1
  · simpa [datum, datumCase574, selectedCase574] using h.selected 2
  · simpa [datum, datumCase574, selectedCase574] using h.selected 3
  · simpa [datum, datumCase574, selectedCase574] using h.selected 4

theorem refutesRepresentative575 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 257 W) : False := by
  apply Krenn.X5Case575Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase575, selectedCase575] using h.selected 0
  · simpa [datum, datumCase575, selectedCase575] using h.selected 1
  · simpa [datum, datumCase575, selectedCase575] using h.selected 2
  · simpa [datum, datumCase575, selectedCase575] using h.selected 3
  · simpa [datum, datumCase575, selectedCase575] using h.selected 4

theorem refutesRepresentative600 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 258 W) : False := by
  apply Krenn.X5Case600Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase600, selectedCase600] using h.selected 0
  · simpa [datum, datumCase600, selectedCase600] using h.selected 1
  · simpa [datum, datumCase600, selectedCase600] using h.selected 2
  · simpa [datum, datumCase600, selectedCase600] using h.selected 3
  · simpa [datum, datumCase600, selectedCase600] using h.selected 4

theorem refutesRepresentative603 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 261 W) : False := by
  apply Krenn.X5Case603Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase603, selectedCase603] using h.selected 0
  · simpa [datum, datumCase603, selectedCase603] using h.selected 1
  · simpa [datum, datumCase603, selectedCase603] using h.selected 2
  · simpa [datum, datumCase603, selectedCase603] using h.selected 3
  · simpa [datum, datumCase603, selectedCase603] using h.selected 4

theorem refutesRepresentative605 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 263 W) : False := by
  apply Krenn.X5Case605Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase605, selectedCase605] using h.selected 0
  · simpa [datum, datumCase605, selectedCase605] using h.selected 1
  · simpa [datum, datumCase605, selectedCase605] using h.selected 2
  · simpa [datum, datumCase605, selectedCase605] using h.selected 3
  · simpa [datum, datumCase605, selectedCase605] using h.selected 4

theorem refutesRepresentative607 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 265 W) : False := by
  apply Krenn.X5Case607Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase607, selectedCase607] using h.selected 0
  · simpa [datum, datumCase607, selectedCase607] using h.selected 1
  · simpa [datum, datumCase607, selectedCase607] using h.selected 2
  · simpa [datum, datumCase607, selectedCase607] using h.selected 3
  · simpa [datum, datumCase607, selectedCase607] using h.selected 4

theorem refutesRepresentative608 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 266 W) : False := by
  apply Krenn.X5Case608Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase608, selectedCase608] using h.selected 0
  · simpa [datum, datumCase608, selectedCase608] using h.selected 1
  · simpa [datum, datumCase608, selectedCase608] using h.selected 2
  · simpa [datum, datumCase608, selectedCase608] using h.selected 3
  · simpa [datum, datumCase608, selectedCase608] using h.selected 4

theorem refutesRepresentative609 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 267 W) : False := by
  apply Krenn.X5Case609Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase609, selectedCase609] using h.selected 0
  · simpa [datum, datumCase609, selectedCase609] using h.selected 1
  · simpa [datum, datumCase609, selectedCase609] using h.selected 2
  · simpa [datum, datumCase609, selectedCase609] using h.selected 3
  · simpa [datum, datumCase609, selectedCase609] using h.selected 4

theorem refutesRepresentative611 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 269 W) : False := by
  apply Krenn.X5Case611Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase611, selectedCase611] using h.selected 0
  · simpa [datum, datumCase611, selectedCase611] using h.selected 1
  · simpa [datum, datumCase611, selectedCase611] using h.selected 2
  · simpa [datum, datumCase611, selectedCase611] using h.selected 3
  · simpa [datum, datumCase611, selectedCase611] using h.selected 4

theorem refutesRepresentative643 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 271 W) : False := by
  apply Krenn.X5Case643Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase643, selectedCase643] using h.selected 0
  · simpa [datum, datumCase643, selectedCase643] using h.selected 1
  · simpa [datum, datumCase643, selectedCase643] using h.selected 2
  · simpa [datum, datumCase643, selectedCase643] using h.selected 3
  · simpa [datum, datumCase643, selectedCase643] using h.selected 4

theorem refutesRepresentative646 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 274 W) : False := by
  apply Krenn.X5Case646Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase646, selectedCase646] using h.selected 0
  · simpa [datum, datumCase646, selectedCase646] using h.selected 1
  · simpa [datum, datumCase646, selectedCase646] using h.selected 2
  · simpa [datum, datumCase646, selectedCase646] using h.selected 3
  · simpa [datum, datumCase646, selectedCase646] using h.selected 4

theorem refutesRepresentative647 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 275 W) : False := by
  apply Krenn.X5Case647Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase647, selectedCase647] using h.selected 0
  · simpa [datum, datumCase647, selectedCase647] using h.selected 1
  · simpa [datum, datumCase647, selectedCase647] using h.selected 2
  · simpa [datum, datumCase647, selectedCase647] using h.selected 3
  · simpa [datum, datumCase647, selectedCase647] using h.selected 4

theorem refutesRepresentative774 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 276 W) : False := by
  apply Krenn.X5Case774Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase774, selectedCase774] using h.selected 0
  · simpa [datum, datumCase774, selectedCase774] using h.selected 1
  · simpa [datum, datumCase774, selectedCase774] using h.selected 2
  · simpa [datum, datumCase774, selectedCase774] using h.selected 3
  · simpa [datum, datumCase774, selectedCase774] using h.selected 4

theorem refutesRepresentative776 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 278 W) : False := by
  apply Krenn.X5Case776Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase776, selectedCase776] using h.selected 0
  · simpa [datum, datumCase776, selectedCase776] using h.selected 1
  · simpa [datum, datumCase776, selectedCase776] using h.selected 2
  · simpa [datum, datumCase776, selectedCase776] using h.selected 3
  · simpa [datum, datumCase776, selectedCase776] using h.selected 4

theorem refutesRepresentative778 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 280 W) : False := by
  apply Krenn.X5Case778Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase778, selectedCase778] using h.selected 0
  · simpa [datum, datumCase778, selectedCase778] using h.selected 1
  · simpa [datum, datumCase778, selectedCase778] using h.selected 2
  · simpa [datum, datumCase778, selectedCase778] using h.selected 3
  · simpa [datum, datumCase778, selectedCase778] using h.selected 4

theorem refutesRepresentative780 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 282 W) : False := by
  apply Krenn.X5Case780Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase780, selectedCase780] using h.selected 0
  · simpa [datum, datumCase780, selectedCase780] using h.selected 1
  · simpa [datum, datumCase780, selectedCase780] using h.selected 2
  · simpa [datum, datumCase780, selectedCase780] using h.selected 3
  · simpa [datum, datumCase780, selectedCase780] using h.selected 4

theorem refutesRepresentative782 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 284 W) : False := by
  apply Krenn.X5Case782Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase782, selectedCase782] using h.selected 0
  · simpa [datum, datumCase782, selectedCase782] using h.selected 1
  · simpa [datum, datumCase782, selectedCase782] using h.selected 2
  · simpa [datum, datumCase782, selectedCase782] using h.selected 3
  · simpa [datum, datumCase782, selectedCase782] using h.selected 4

theorem refutesRepresentative783 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 285 W) : False := by
  apply Krenn.X5Case783Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase783, selectedCase783] using h.selected 0
  · simpa [datum, datumCase783, selectedCase783] using h.selected 1
  · simpa [datum, datumCase783, selectedCase783] using h.selected 2
  · simpa [datum, datumCase783, selectedCase783] using h.selected 3
  · simpa [datum, datumCase783, selectedCase783] using h.selected 4

theorem refutesRepresentative784 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 286 W) : False := by
  apply Krenn.X5Case784Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase784, selectedCase784] using h.selected 0
  · simpa [datum, datumCase784, selectedCase784] using h.selected 1
  · simpa [datum, datumCase784, selectedCase784] using h.selected 2
  · simpa [datum, datumCase784, selectedCase784] using h.selected 3
  · simpa [datum, datumCase784, selectedCase784] using h.selected 4

theorem refutesRepresentative786 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 288 W) : False := by
  apply Krenn.X5Case786Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase786, selectedCase786] using h.selected 0
  · simpa [datum, datumCase786, selectedCase786] using h.selected 1
  · simpa [datum, datumCase786, selectedCase786] using h.selected 2
  · simpa [datum, datumCase786, selectedCase786] using h.selected 3
  · simpa [datum, datumCase786, selectedCase786] using h.selected 4

theorem refutesRepresentative787 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 289 W) : False := by
  apply Krenn.X5Case787Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase787, selectedCase787] using h.selected 0
  · simpa [datum, datumCase787, selectedCase787] using h.selected 1
  · simpa [datum, datumCase787, selectedCase787] using h.selected 2
  · simpa [datum, datumCase787, selectedCase787] using h.selected 3
  · simpa [datum, datumCase787, selectedCase787] using h.selected 4

theorem refutesRepresentative788 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 290 W) : False := by
  apply Krenn.X5Case788Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase788, selectedCase788] using h.selected 0
  · simpa [datum, datumCase788, selectedCase788] using h.selected 1
  · simpa [datum, datumCase788, selectedCase788] using h.selected 2
  · simpa [datum, datumCase788, selectedCase788] using h.selected 3
  · simpa [datum, datumCase788, selectedCase788] using h.selected 4

theorem refutesRepresentative790 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 292 W) : False := by
  apply Krenn.X5Case790Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase790, selectedCase790] using h.selected 0
  · simpa [datum, datumCase790, selectedCase790] using h.selected 1
  · simpa [datum, datumCase790, selectedCase790] using h.selected 2
  · simpa [datum, datumCase790, selectedCase790] using h.selected 3
  · simpa [datum, datumCase790, selectedCase790] using h.selected 4

theorem refutesRepresentative816 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 294 W) : False := by
  apply Krenn.X5Case816Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase816, selectedCase816] using h.selected 0
  · simpa [datum, datumCase816, selectedCase816] using h.selected 1
  · simpa [datum, datumCase816, selectedCase816] using h.selected 2
  · simpa [datum, datumCase816, selectedCase816] using h.selected 3
  · simpa [datum, datumCase816, selectedCase816] using h.selected 4

theorem refutesRepresentative818 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 296 W) : False := by
  apply Krenn.X5Case818Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase818, selectedCase818] using h.selected 0
  · simpa [datum, datumCase818, selectedCase818] using h.selected 1
  · simpa [datum, datumCase818, selectedCase818] using h.selected 2
  · simpa [datum, datumCase818, selectedCase818] using h.selected 3
  · simpa [datum, datumCase818, selectedCase818] using h.selected 4

theorem refutesRepresentative819 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 297 W) : False := by
  apply Krenn.X5Case819Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase819, selectedCase819] using h.selected 0
  · simpa [datum, datumCase819, selectedCase819] using h.selected 1
  · simpa [datum, datumCase819, selectedCase819] using h.selected 2
  · simpa [datum, datumCase819, selectedCase819] using h.selected 3
  · simpa [datum, datumCase819, selectedCase819] using h.selected 4

theorem refutesRepresentative821 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 299 W) : False := by
  apply Krenn.X5Case821Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase821, selectedCase821] using h.selected 0
  · simpa [datum, datumCase821, selectedCase821] using h.selected 1
  · simpa [datum, datumCase821, selectedCase821] using h.selected 2
  · simpa [datum, datumCase821, selectedCase821] using h.selected 3
  · simpa [datum, datumCase821, selectedCase821] using h.selected 4

theorem refutesRepresentative822 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 300 W) : False := by
  apply Krenn.X5Case822Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase822, selectedCase822] using h.selected 0
  · simpa [datum, datumCase822, selectedCase822] using h.selected 1
  · simpa [datum, datumCase822, selectedCase822] using h.selected 2
  · simpa [datum, datumCase822, selectedCase822] using h.selected 3
  · simpa [datum, datumCase822, selectedCase822] using h.selected 4

theorem refutesRepresentative824 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 302 W) : False := by
  apply Krenn.X5Case824Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase824, selectedCase824] using h.selected 0
  · simpa [datum, datumCase824, selectedCase824] using h.selected 1
  · simpa [datum, datumCase824, selectedCase824] using h.selected 2
  · simpa [datum, datumCase824, selectedCase824] using h.selected 3
  · simpa [datum, datumCase824, selectedCase824] using h.selected 4

theorem refutesRepresentative826 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 304 W) : False := by
  apply Krenn.X5Case826Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase826, selectedCase826] using h.selected 0
  · simpa [datum, datumCase826, selectedCase826] using h.selected 1
  · simpa [datum, datumCase826, selectedCase826] using h.selected 2
  · simpa [datum, datumCase826, selectedCase826] using h.selected 3
  · simpa [datum, datumCase826, selectedCase826] using h.selected 4

theorem refutesRepresentative858 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 306 W) : False := by
  apply Krenn.X5Case858Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase858, selectedCase858] using h.selected 0
  · simpa [datum, datumCase858, selectedCase858] using h.selected 1
  · simpa [datum, datumCase858, selectedCase858] using h.selected 2
  · simpa [datum, datumCase858, selectedCase858] using h.selected 3
  · simpa [datum, datumCase858, selectedCase858] using h.selected 4

theorem refutesRepresentative859 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 307 W) : False := by
  apply Krenn.X5Case859Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase859, selectedCase859] using h.selected 0
  · simpa [datum, datumCase859, selectedCase859] using h.selected 1
  · simpa [datum, datumCase859, selectedCase859] using h.selected 2
  · simpa [datum, datumCase859, selectedCase859] using h.selected 3
  · simpa [datum, datumCase859, selectedCase859] using h.selected 4

theorem refutesRepresentative860 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 308 W) : False := by
  apply Krenn.X5Case860Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase860, selectedCase860] using h.selected 0
  · simpa [datum, datumCase860, selectedCase860] using h.selected 1
  · simpa [datum, datumCase860, selectedCase860] using h.selected 2
  · simpa [datum, datumCase860, selectedCase860] using h.selected 3
  · simpa [datum, datumCase860, selectedCase860] using h.selected 4

theorem refutesRepresentative862 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 310 W) : False := by
  apply Krenn.X5Case862Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase862, selectedCase862] using h.selected 0
  · simpa [datum, datumCase862, selectedCase862] using h.selected 1
  · simpa [datum, datumCase862, selectedCase862] using h.selected 2
  · simpa [datum, datumCase862, selectedCase862] using h.selected 3
  · simpa [datum, datumCase862, selectedCase862] using h.selected 4

theorem refutesRepresentative1032 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 312 W) : False := by
  apply Krenn.X5Case1032Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase1032, selectedCase1032] using h.selected 0
  · simpa [datum, datumCase1032, selectedCase1032] using h.selected 1
  · simpa [datum, datumCase1032, selectedCase1032] using h.selected 2
  · simpa [datum, datumCase1032, selectedCase1032] using h.selected 3
  · simpa [datum, datumCase1032, selectedCase1032] using h.selected 4

theorem refutesRepresentative1035 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 315 W) : False := by
  apply Krenn.X5Case1035Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase1035, selectedCase1035] using h.selected 0
  · simpa [datum, datumCase1035, selectedCase1035] using h.selected 1
  · simpa [datum, datumCase1035, selectedCase1035] using h.selected 2
  · simpa [datum, datumCase1035, selectedCase1035] using h.selected 3
  · simpa [datum, datumCase1035, selectedCase1035] using h.selected 4

theorem refutesRepresentative1037 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 317 W) : False := by
  apply Krenn.X5Case1037Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase1037, selectedCase1037] using h.selected 0
  · simpa [datum, datumCase1037, selectedCase1037] using h.selected 1
  · simpa [datum, datumCase1037, selectedCase1037] using h.selected 2
  · simpa [datum, datumCase1037, selectedCase1037] using h.selected 3
  · simpa [datum, datumCase1037, selectedCase1037] using h.selected 4

theorem refutesRepresentative1038 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 318 W) : False := by
  apply Krenn.X5Case1038Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase1038, selectedCase1038] using h.selected 0
  · simpa [datum, datumCase1038, selectedCase1038] using h.selected 1
  · simpa [datum, datumCase1038, selectedCase1038] using h.selected 2
  · simpa [datum, datumCase1038, selectedCase1038] using h.selected 3
  · simpa [datum, datumCase1038, selectedCase1038] using h.selected 4

theorem refutesRepresentative1041 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 321 W) : False := by
  apply Krenn.X5Case1041Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase1041, selectedCase1041] using h.selected 0
  · simpa [datum, datumCase1041, selectedCase1041] using h.selected 1
  · simpa [datum, datumCase1041, selectedCase1041] using h.selected 2
  · simpa [datum, datumCase1041, selectedCase1041] using h.selected 3
  · simpa [datum, datumCase1041, selectedCase1041] using h.selected 4

theorem refutesRepresentative1043 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 323 W) : False := by
  apply Krenn.X5Case1043Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase1043, selectedCase1043] using h.selected 0
  · simpa [datum, datumCase1043, selectedCase1043] using h.selected 1
  · simpa [datum, datumCase1043, selectedCase1043] using h.selected 2
  · simpa [datum, datumCase1043, selectedCase1043] using h.selected 3
  · simpa [datum, datumCase1043, selectedCase1043] using h.selected 4

theorem refutesRepresentative1075 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 325 W) : False := by
  apply Krenn.X5Case1075Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase1075, selectedCase1075] using h.selected 0
  · simpa [datum, datumCase1075, selectedCase1075] using h.selected 1
  · simpa [datum, datumCase1075, selectedCase1075] using h.selected 2
  · simpa [datum, datumCase1075, selectedCase1075] using h.selected 3
  · simpa [datum, datumCase1075, selectedCase1075] using h.selected 4

theorem refutesRepresentative1078 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 328 W) : False := by
  apply Krenn.X5Case1078Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase1078, selectedCase1078] using h.selected 0
  · simpa [datum, datumCase1078, selectedCase1078] using h.selected 1
  · simpa [datum, datumCase1078, selectedCase1078] using h.selected 2
  · simpa [datum, datumCase1078, selectedCase1078] using h.selected 3
  · simpa [datum, datumCase1078, selectedCase1078] using h.selected 4

theorem refutesRepresentative1079 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 329 W) : False := by
  apply Krenn.X5Case1079Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase1079, selectedCase1079] using h.selected 0
  · simpa [datum, datumCase1079, selectedCase1079] using h.selected 1
  · simpa [datum, datumCase1079, selectedCase1079] using h.selected 2
  · simpa [datum, datumCase1079, selectedCase1079] using h.selected 3
  · simpa [datum, datumCase1079, selectedCase1079] using h.selected 4

theorem refutesRepresentative1291 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 331 W) : False := by
  apply Krenn.X5Case1291Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase1291, selectedCase1291] using h.selected 0
  · simpa [datum, datumCase1291, selectedCase1291] using h.selected 1
  · simpa [datum, datumCase1291, selectedCase1291] using h.selected 2
  · simpa [datum, datumCase1291, selectedCase1291] using h.selected 3
  · simpa [datum, datumCase1291, selectedCase1291] using h.selected 4

theorem refutesRepresentative1292 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 332 W) : False := by
  apply Krenn.X5Case1292Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase1292, selectedCase1292] using h.selected 0
  · simpa [datum, datumCase1292, selectedCase1292] using h.selected 1
  · simpa [datum, datumCase1292, selectedCase1292] using h.selected 2
  · simpa [datum, datumCase1292, selectedCase1292] using h.selected 3
  · simpa [datum, datumCase1292, selectedCase1292] using h.selected 4

theorem refutesRepresentative1294 (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W)
    (h : NormalizedRepresentative 334 W) : False := by
  apply Krenn.X5Case1294Bridge.noNormalizedCase W hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, h.outside05, h.outside12, h.outside13,
    h.outside14, h.outside23, h.outside24, h.outside25, h.outside34,
    h.outside35, h.outside45⟩
  · simpa [datum, datumCase1294, selectedCase1294] using h.selected 0
  · simpa [datum, datumCase1294, selectedCase1294] using h.selected 1
  · simpa [datum, datumCase1294, selectedCase1294] using h.selected 2
  · simpa [datum, datumCase1294, selectedCase1294] using h.selected 3
  · simpa [datum, datumCase1294, selectedCase1294] using h.selected 4

structure RefutedRepresentative where
  ordinal : Fin 336
  caseIndex : Fin 1296
  caseIndex_eq : representativeCase ordinal = caseIndex
  impossible : ∀ W, EqSystemN 6 3 W →
    NormalizedRepresentative ordinal W → False

def entry1 : RefutedRepresentative :=
  ⟨1, 1, by decide, refutesRepresentative1⟩

def entry3 : RefutedRepresentative :=
  ⟨3, 3, by decide, refutesRepresentative3⟩

def entry4 : RefutedRepresentative :=
  ⟨4, 4, by decide, refutesRepresentative4⟩

def entry6 : RefutedRepresentative :=
  ⟨6, 6, by decide, refutesRepresentative6⟩

def entry7 : RefutedRepresentative :=
  ⟨7, 7, by decide, refutesRepresentative7⟩

def entry8 : RefutedRepresentative :=
  ⟨8, 8, by decide, refutesRepresentative8⟩

def entry9 : RefutedRepresentative :=
  ⟨9, 9, by decide, refutesRepresentative9⟩

def entry10 : RefutedRepresentative :=
  ⟨10, 10, by decide, refutesRepresentative10⟩

def entry11 : RefutedRepresentative :=
  ⟨11, 11, by decide, refutesRepresentative11⟩

def entry13 : RefutedRepresentative :=
  ⟨13, 13, by decide, refutesRepresentative13⟩

def entry14 : RefutedRepresentative :=
  ⟨14, 14, by decide, refutesRepresentative14⟩

def entry15 : RefutedRepresentative :=
  ⟨15, 15, by decide, refutesRepresentative15⟩

def entry16 : RefutedRepresentative :=
  ⟨16, 16, by decide, refutesRepresentative16⟩

def entry17 : RefutedRepresentative :=
  ⟨17, 17, by decide, refutesRepresentative17⟩

def entry18 : RefutedRepresentative :=
  ⟨18, 18, by decide, refutesRepresentative18⟩

def entry19 : RefutedRepresentative :=
  ⟨19, 19, by decide, refutesRepresentative19⟩

def entry21 : RefutedRepresentative :=
  ⟨21, 21, by decide, refutesRepresentative21⟩

def entry22 : RefutedRepresentative :=
  ⟨22, 22, by decide, refutesRepresentative22⟩

def entry25 : RefutedRepresentative :=
  ⟨25, 25, by decide, refutesRepresentative25⟩

def entry27 : RefutedRepresentative :=
  ⟨27, 27, by decide, refutesRepresentative27⟩

def entry28 : RefutedRepresentative :=
  ⟨28, 28, by decide, refutesRepresentative28⟩

def entry29 : RefutedRepresentative :=
  ⟨29, 29, by decide, refutesRepresentative29⟩

def entry31 : RefutedRepresentative :=
  ⟨31, 31, by decide, refutesRepresentative31⟩

def entry33 : RefutedRepresentative :=
  ⟨33, 33, by decide, refutesRepresentative33⟩

def entry34 : RefutedRepresentative :=
  ⟨34, 34, by decide, refutesRepresentative34⟩

def entry42 : RefutedRepresentative :=
  ⟨36, 42, by decide, refutesRepresentative42⟩

def entry43 : RefutedRepresentative :=
  ⟨37, 43, by decide, refutesRepresentative43⟩

def entry44 : RefutedRepresentative :=
  ⟨38, 44, by decide, refutesRepresentative44⟩

def entry47 : RefutedRepresentative :=
  ⟨41, 47, by decide, refutesRepresentative47⟩

def entry49 : RefutedRepresentative :=
  ⟨43, 49, by decide, refutesRepresentative49⟩

def entry51 : RefutedRepresentative :=
  ⟨45, 51, by decide, refutesRepresentative51⟩

def entry52 : RefutedRepresentative :=
  ⟨46, 52, by decide, refutesRepresentative52⟩

def entry53 : RefutedRepresentative :=
  ⟨47, 53, by decide, refutesRepresentative53⟩

def entry54 : RefutedRepresentative :=
  ⟨48, 54, by decide, refutesRepresentative54⟩

def entry55 : RefutedRepresentative :=
  ⟨49, 55, by decide, refutesRepresentative55⟩

def entry56 : RefutedRepresentative :=
  ⟨50, 56, by decide, refutesRepresentative56⟩

def entry58 : RefutedRepresentative :=
  ⟨52, 58, by decide, refutesRepresentative58⟩

def entry60 : RefutedRepresentative :=
  ⟨54, 60, by decide, refutesRepresentative60⟩

def entry61 : RefutedRepresentative :=
  ⟨55, 61, by decide, refutesRepresentative61⟩

def entry63 : RefutedRepresentative :=
  ⟨57, 63, by decide, refutesRepresentative63⟩

def entry64 : RefutedRepresentative :=
  ⟨58, 64, by decide, refutesRepresentative64⟩

def entry65 : RefutedRepresentative :=
  ⟨59, 65, by decide, refutesRepresentative65⟩

def entry67 : RefutedRepresentative :=
  ⟨61, 67, by decide, refutesRepresentative67⟩

def entry68 : RefutedRepresentative :=
  ⟨62, 68, by decide, refutesRepresentative68⟩

def entry70 : RefutedRepresentative :=
  ⟨64, 70, by decide, refutesRepresentative70⟩

def entry85 : RefutedRepresentative :=
  ⟨67, 85, by decide, refutesRepresentative85⟩

def entry87 : RefutedRepresentative :=
  ⟨69, 87, by decide, refutesRepresentative87⟩

def entry88 : RefutedRepresentative :=
  ⟨70, 88, by decide, refutesRepresentative88⟩

def entry89 : RefutedRepresentative :=
  ⟨71, 89, by decide, refutesRepresentative89⟩

def entry91 : RefutedRepresentative :=
  ⟨73, 91, by decide, refutesRepresentative91⟩

def entry93 : RefutedRepresentative :=
  ⟨75, 93, by decide, refutesRepresentative93⟩

def entry94 : RefutedRepresentative :=
  ⟨76, 94, by decide, refutesRepresentative94⟩

def entry97 : RefutedRepresentative :=
  ⟨79, 97, by decide, refutesRepresentative97⟩

def entry99 : RefutedRepresentative :=
  ⟨81, 99, by decide, refutesRepresentative99⟩

def entry100 : RefutedRepresentative :=
  ⟨82, 100, by decide, refutesRepresentative100⟩

def entry101 : RefutedRepresentative :=
  ⟨83, 101, by decide, refutesRepresentative101⟩

def entry103 : RefutedRepresentative :=
  ⟨85, 103, by decide, refutesRepresentative103⟩

def entry105 : RefutedRepresentative :=
  ⟨87, 105, by decide, refutesRepresentative105⟩

def entry106 : RefutedRepresentative :=
  ⟨88, 106, by decide, refutesRepresentative106⟩

def entry126 : RefutedRepresentative :=
  ⟨90, 126, by decide, refutesRepresentative126⟩

def entry127 : RefutedRepresentative :=
  ⟨91, 127, by decide, refutesRepresentative127⟩

def entry128 : RefutedRepresentative :=
  ⟨92, 128, by decide, refutesRepresentative128⟩

def entry130 : RefutedRepresentative :=
  ⟨94, 130, by decide, refutesRepresentative130⟩

def entry132 : RefutedRepresentative :=
  ⟨96, 132, by decide, refutesRepresentative132⟩

def entry133 : RefutedRepresentative :=
  ⟨97, 133, by decide, refutesRepresentative133⟩

def entry134 : RefutedRepresentative :=
  ⟨98, 134, by decide, refutesRepresentative134⟩

def entry135 : RefutedRepresentative :=
  ⟨99, 135, by decide, refutesRepresentative135⟩

def entry136 : RefutedRepresentative :=
  ⟨100, 136, by decide, refutesRepresentative136⟩

def entry138 : RefutedRepresentative :=
  ⟨102, 138, by decide, refutesRepresentative138⟩

def entry139 : RefutedRepresentative :=
  ⟨103, 139, by decide, refutesRepresentative139⟩

def entry140 : RefutedRepresentative :=
  ⟨104, 140, by decide, refutesRepresentative140⟩

def entry142 : RefutedRepresentative :=
  ⟨106, 142, by decide, refutesRepresentative142⟩

def entry143 : RefutedRepresentative :=
  ⟨107, 143, by decide, refutesRepresentative143⟩

def entry171 : RefutedRepresentative :=
  ⟨111, 171, by decide, refutesRepresentative171⟩

def entry172 : RefutedRepresentative :=
  ⟨112, 172, by decide, refutesRepresentative172⟩

def entry173 : RefutedRepresentative :=
  ⟨113, 173, by decide, refutesRepresentative173⟩

def entry175 : RefutedRepresentative :=
  ⟨115, 175, by decide, refutesRepresentative175⟩

def entry177 : RefutedRepresentative :=
  ⟨117, 177, by decide, refutesRepresentative177⟩

def entry178 : RefutedRepresentative :=
  ⟨118, 178, by decide, refutesRepresentative178⟩

def entry211 : RefutedRepresentative :=
  ⟨121, 211, by decide, refutesRepresentative211⟩

def entry212 : RefutedRepresentative :=
  ⟨122, 212, by decide, refutesRepresentative212⟩

def entry214 : RefutedRepresentative :=
  ⟨124, 214, by decide, refutesRepresentative214⟩

def entry258 : RefutedRepresentative :=
  ⟨126, 258, by decide, refutesRepresentative258⟩

def entry260 : RefutedRepresentative :=
  ⟨128, 260, by decide, refutesRepresentative260⟩

def entry263 : RefutedRepresentative :=
  ⟨131, 263, by decide, refutesRepresentative263⟩

def entry264 : RefutedRepresentative :=
  ⟨132, 264, by decide, refutesRepresentative264⟩

def entry266 : RefutedRepresentative :=
  ⟨134, 266, by decide, refutesRepresentative266⟩

def entry267 : RefutedRepresentative :=
  ⟨135, 267, by decide, refutesRepresentative267⟩

def entry269 : RefutedRepresentative :=
  ⟨137, 269, by decide, refutesRepresentative269⟩

def entry270 : RefutedRepresentative :=
  ⟨138, 270, by decide, refutesRepresentative270⟩

def entry272 : RefutedRepresentative :=
  ⟨140, 272, by decide, refutesRepresentative272⟩

def entry274 : RefutedRepresentative :=
  ⟨142, 274, by decide, refutesRepresentative274⟩

def entry275 : RefutedRepresentative :=
  ⟨143, 275, by decide, refutesRepresentative275⟩

def entry276 : RefutedRepresentative :=
  ⟨144, 276, by decide, refutesRepresentative276⟩

def entry278 : RefutedRepresentative :=
  ⟨146, 278, by decide, refutesRepresentative278⟩

def entry279 : RefutedRepresentative :=
  ⟨147, 279, by decide, refutesRepresentative279⟩

def entry281 : RefutedRepresentative :=
  ⟨149, 281, by decide, refutesRepresentative281⟩

def entry282 : RefutedRepresentative :=
  ⟨150, 282, by decide, refutesRepresentative282⟩

def entry283 : RefutedRepresentative :=
  ⟨151, 283, by decide, refutesRepresentative283⟩

def entry284 : RefutedRepresentative :=
  ⟨152, 284, by decide, refutesRepresentative284⟩

def entry287 : RefutedRepresentative :=
  ⟨155, 287, by decide, refutesRepresentative287⟩

def entry300 : RefutedRepresentative :=
  ⟨156, 300, by decide, refutesRepresentative300⟩

def entry302 : RefutedRepresentative :=
  ⟨158, 302, by decide, refutesRepresentative302⟩

def entry303 : RefutedRepresentative :=
  ⟨159, 303, by decide, refutesRepresentative303⟩

def entry305 : RefutedRepresentative :=
  ⟨161, 305, by decide, refutesRepresentative305⟩

def entry306 : RefutedRepresentative :=
  ⟨162, 306, by decide, refutesRepresentative306⟩

def entry308 : RefutedRepresentative :=
  ⟨164, 308, by decide, refutesRepresentative308⟩

def entry311 : RefutedRepresentative :=
  ⟨167, 311, by decide, refutesRepresentative311⟩

def entry312 : RefutedRepresentative :=
  ⟨168, 312, by decide, refutesRepresentative312⟩

def entry314 : RefutedRepresentative :=
  ⟨170, 314, by decide, refutesRepresentative314⟩

def entry315 : RefutedRepresentative :=
  ⟨171, 315, by decide, refutesRepresentative315⟩

def entry317 : RefutedRepresentative :=
  ⟨173, 317, by decide, refutesRepresentative317⟩

def entry318 : RefutedRepresentative :=
  ⟨174, 318, by decide, refutesRepresentative318⟩

def entry319 : RefutedRepresentative :=
  ⟨175, 319, by decide, refutesRepresentative319⟩

def entry320 : RefutedRepresentative :=
  ⟨176, 320, by decide, refutesRepresentative320⟩

def entry323 : RefutedRepresentative :=
  ⟨179, 323, by decide, refutesRepresentative323⟩

def entry342 : RefutedRepresentative :=
  ⟨180, 342, by decide, refutesRepresentative342⟩

def entry344 : RefutedRepresentative :=
  ⟨182, 344, by decide, refutesRepresentative344⟩

def entry346 : RefutedRepresentative :=
  ⟨184, 346, by decide, refutesRepresentative346⟩

def entry348 : RefutedRepresentative :=
  ⟨186, 348, by decide, refutesRepresentative348⟩

def entry350 : RefutedRepresentative :=
  ⟨188, 350, by decide, refutesRepresentative350⟩

def entry353 : RefutedRepresentative :=
  ⟨191, 353, by decide, refutesRepresentative353⟩

def entry354 : RefutedRepresentative :=
  ⟨192, 354, by decide, refutesRepresentative354⟩

def entry355 : RefutedRepresentative :=
  ⟨193, 355, by decide, refutesRepresentative355⟩

def entry356 : RefutedRepresentative :=
  ⟨194, 356, by decide, refutesRepresentative356⟩

def entry358 : RefutedRepresentative :=
  ⟨196, 358, by decide, refutesRepresentative358⟩

def entry384 : RefutedRepresentative :=
  ⟨198, 384, by decide, refutesRepresentative384⟩

def entry386 : RefutedRepresentative :=
  ⟨200, 386, by decide, refutesRepresentative386⟩

def entry387 : RefutedRepresentative :=
  ⟨201, 387, by decide, refutesRepresentative387⟩

def entry389 : RefutedRepresentative :=
  ⟨203, 389, by decide, refutesRepresentative389⟩

def entry390 : RefutedRepresentative :=
  ⟨204, 390, by decide, refutesRepresentative390⟩

def entry392 : RefutedRepresentative :=
  ⟨206, 392, by decide, refutesRepresentative392⟩

def entry395 : RefutedRepresentative :=
  ⟨209, 395, by decide, refutesRepresentative395⟩

def entry426 : RefutedRepresentative :=
  ⟨210, 426, by decide, refutesRepresentative426⟩

def entry427 : RefutedRepresentative :=
  ⟨211, 427, by decide, refutesRepresentative427⟩

def entry428 : RefutedRepresentative :=
  ⟨212, 428, by decide, refutesRepresentative428⟩

def entry430 : RefutedRepresentative :=
  ⟨214, 430, by decide, refutesRepresentative430⟩

def entry517 : RefutedRepresentative :=
  ⟨217, 517, by decide, refutesRepresentative517⟩

def entry519 : RefutedRepresentative :=
  ⟨219, 519, by decide, refutesRepresentative519⟩

def entry521 : RefutedRepresentative :=
  ⟨221, 521, by decide, refutesRepresentative521⟩

def entry523 : RefutedRepresentative :=
  ⟨223, 523, by decide, refutesRepresentative523⟩

def entry524 : RefutedRepresentative :=
  ⟨224, 524, by decide, refutesRepresentative524⟩

def entry525 : RefutedRepresentative :=
  ⟨225, 525, by decide, refutesRepresentative525⟩

def entry526 : RefutedRepresentative :=
  ⟨226, 526, by decide, refutesRepresentative526⟩

def entry527 : RefutedRepresentative :=
  ⟨227, 527, by decide, refutesRepresentative527⟩

def entry529 : RefutedRepresentative :=
  ⟨229, 529, by decide, refutesRepresentative529⟩

def entry531 : RefutedRepresentative :=
  ⟨231, 531, by decide, refutesRepresentative531⟩

def entry533 : RefutedRepresentative :=
  ⟨233, 533, by decide, refutesRepresentative533⟩

def entry535 : RefutedRepresentative :=
  ⟨235, 535, by decide, refutesRepresentative535⟩

def entry537 : RefutedRepresentative :=
  ⟨237, 537, by decide, refutesRepresentative537⟩

def entry538 : RefutedRepresentative :=
  ⟨238, 538, by decide, refutesRepresentative538⟩

def entry539 : RefutedRepresentative :=
  ⟨239, 539, by decide, refutesRepresentative539⟩

def entry558 : RefutedRepresentative :=
  ⟨240, 558, by decide, refutesRepresentative558⟩

def entry560 : RefutedRepresentative :=
  ⟨242, 560, by decide, refutesRepresentative560⟩

def entry561 : RefutedRepresentative :=
  ⟨243, 561, by decide, refutesRepresentative561⟩

def entry564 : RefutedRepresentative :=
  ⟨246, 564, by decide, refutesRepresentative564⟩

def entry567 : RefutedRepresentative :=
  ⟨249, 567, by decide, refutesRepresentative567⟩

def entry569 : RefutedRepresentative :=
  ⟨251, 569, by decide, refutesRepresentative569⟩

def entry571 : RefutedRepresentative :=
  ⟨253, 571, by decide, refutesRepresentative571⟩

def entry572 : RefutedRepresentative :=
  ⟨254, 572, by decide, refutesRepresentative572⟩

def entry573 : RefutedRepresentative :=
  ⟨255, 573, by decide, refutesRepresentative573⟩

def entry574 : RefutedRepresentative :=
  ⟨256, 574, by decide, refutesRepresentative574⟩

def entry575 : RefutedRepresentative :=
  ⟨257, 575, by decide, refutesRepresentative575⟩

def entry600 : RefutedRepresentative :=
  ⟨258, 600, by decide, refutesRepresentative600⟩

def entry603 : RefutedRepresentative :=
  ⟨261, 603, by decide, refutesRepresentative603⟩

def entry605 : RefutedRepresentative :=
  ⟨263, 605, by decide, refutesRepresentative605⟩

def entry607 : RefutedRepresentative :=
  ⟨265, 607, by decide, refutesRepresentative607⟩

def entry608 : RefutedRepresentative :=
  ⟨266, 608, by decide, refutesRepresentative608⟩

def entry609 : RefutedRepresentative :=
  ⟨267, 609, by decide, refutesRepresentative609⟩

def entry611 : RefutedRepresentative :=
  ⟨269, 611, by decide, refutesRepresentative611⟩

def entry643 : RefutedRepresentative :=
  ⟨271, 643, by decide, refutesRepresentative643⟩

def entry646 : RefutedRepresentative :=
  ⟨274, 646, by decide, refutesRepresentative646⟩

def entry647 : RefutedRepresentative :=
  ⟨275, 647, by decide, refutesRepresentative647⟩

def entry774 : RefutedRepresentative :=
  ⟨276, 774, by decide, refutesRepresentative774⟩

def entry776 : RefutedRepresentative :=
  ⟨278, 776, by decide, refutesRepresentative776⟩

def entry778 : RefutedRepresentative :=
  ⟨280, 778, by decide, refutesRepresentative778⟩

def entry780 : RefutedRepresentative :=
  ⟨282, 780, by decide, refutesRepresentative780⟩

def entry782 : RefutedRepresentative :=
  ⟨284, 782, by decide, refutesRepresentative782⟩

def entry783 : RefutedRepresentative :=
  ⟨285, 783, by decide, refutesRepresentative783⟩

def entry784 : RefutedRepresentative :=
  ⟨286, 784, by decide, refutesRepresentative784⟩

def entry786 : RefutedRepresentative :=
  ⟨288, 786, by decide, refutesRepresentative786⟩

def entry787 : RefutedRepresentative :=
  ⟨289, 787, by decide, refutesRepresentative787⟩

def entry788 : RefutedRepresentative :=
  ⟨290, 788, by decide, refutesRepresentative788⟩

def entry790 : RefutedRepresentative :=
  ⟨292, 790, by decide, refutesRepresentative790⟩

def entry816 : RefutedRepresentative :=
  ⟨294, 816, by decide, refutesRepresentative816⟩

def entry818 : RefutedRepresentative :=
  ⟨296, 818, by decide, refutesRepresentative818⟩

def entry819 : RefutedRepresentative :=
  ⟨297, 819, by decide, refutesRepresentative819⟩

def entry821 : RefutedRepresentative :=
  ⟨299, 821, by decide, refutesRepresentative821⟩

def entry822 : RefutedRepresentative :=
  ⟨300, 822, by decide, refutesRepresentative822⟩

def entry824 : RefutedRepresentative :=
  ⟨302, 824, by decide, refutesRepresentative824⟩

def entry826 : RefutedRepresentative :=
  ⟨304, 826, by decide, refutesRepresentative826⟩

def entry858 : RefutedRepresentative :=
  ⟨306, 858, by decide, refutesRepresentative858⟩

def entry859 : RefutedRepresentative :=
  ⟨307, 859, by decide, refutesRepresentative859⟩

def entry860 : RefutedRepresentative :=
  ⟨308, 860, by decide, refutesRepresentative860⟩

def entry862 : RefutedRepresentative :=
  ⟨310, 862, by decide, refutesRepresentative862⟩

def entry1032 : RefutedRepresentative :=
  ⟨312, 1032, by decide, refutesRepresentative1032⟩

def entry1035 : RefutedRepresentative :=
  ⟨315, 1035, by decide, refutesRepresentative1035⟩

def entry1037 : RefutedRepresentative :=
  ⟨317, 1037, by decide, refutesRepresentative1037⟩

def entry1038 : RefutedRepresentative :=
  ⟨318, 1038, by decide, refutesRepresentative1038⟩

def entry1041 : RefutedRepresentative :=
  ⟨321, 1041, by decide, refutesRepresentative1041⟩

def entry1043 : RefutedRepresentative :=
  ⟨323, 1043, by decide, refutesRepresentative1043⟩

def entry1075 : RefutedRepresentative :=
  ⟨325, 1075, by decide, refutesRepresentative1075⟩

def entry1078 : RefutedRepresentative :=
  ⟨328, 1078, by decide, refutesRepresentative1078⟩

def entry1079 : RefutedRepresentative :=
  ⟨329, 1079, by decide, refutesRepresentative1079⟩

def entry1291 : RefutedRepresentative :=
  ⟨331, 1291, by decide, refutesRepresentative1291⟩

def entry1292 : RefutedRepresentative :=
  ⟨332, 1292, by decide, refutesRepresentative1292⟩

def entry1294 : RefutedRepresentative :=
  ⟨334, 1294, by decide, refutesRepresentative1294⟩

def migratedRepresentatives : Fin 207 → RefutedRepresentative := ![
  entry1, entry3, entry4, entry6, entry7, entry8, entry9, entry10, entry11, entry13, entry14, entry15, entry16, entry17, entry18, entry19, entry21, entry22, entry25, entry27, entry28, entry29, entry31, entry33, entry34, entry42, entry43, entry44, entry47, entry49, entry51, entry52, entry53, entry54, entry55, entry56, entry58, entry60, entry61, entry63, entry64, entry65, entry67, entry68, entry70, entry85, entry87, entry88, entry89, entry91, entry93, entry94, entry97, entry99, entry100, entry101, entry103, entry105, entry106, entry126, entry127, entry128, entry130, entry132, entry133, entry134, entry135, entry136, entry138, entry139, entry140, entry142, entry143, entry171, entry172, entry173, entry175, entry177, entry178, entry211, entry212, entry214, entry258, entry260, entry263, entry264, entry266, entry267, entry269, entry270, entry272, entry274, entry275, entry276, entry278, entry279, entry281, entry282, entry283, entry284, entry287, entry300, entry302, entry303, entry305, entry306, entry308, entry311, entry312, entry314, entry315, entry317, entry318, entry319, entry320, entry323, entry342, entry344, entry346, entry348, entry350, entry353, entry354, entry355, entry356, entry358, entry384, entry386, entry387, entry389, entry390, entry392, entry395, entry426, entry427, entry428, entry430, entry517, entry519, entry521, entry523, entry524, entry525, entry526, entry527, entry529, entry531, entry533, entry535, entry537, entry538, entry539, entry558, entry560, entry561, entry564, entry567, entry569, entry571, entry572, entry573, entry574, entry575, entry600, entry603, entry605, entry607, entry608, entry609, entry611, entry643, entry646, entry647, entry774, entry776, entry778, entry780, entry782, entry783, entry784, entry786, entry787, entry788, entry790, entry816, entry818, entry819, entry821, entry822, entry824, entry826, entry858, entry859, entry860, entry862, entry1032, entry1035, entry1037, entry1038, entry1041, entry1043, entry1075, entry1078, entry1079, entry1291, entry1292, entry1294
]

def dispatchedCaseIndices : List Nat :=
  List.ofFn fun index => (migratedRepresentatives index).caseIndex.val

theorem dispatchedCaseIndices_eq :
    dispatchedCaseIndices = Krenn.X5LegacyMigrated.migratedCaseIndices := by
  decide

#print axioms Krenn.X5LegacyDispatch.dispatchedCaseIndices_eq
#print axioms Krenn.X5LegacyDispatch.refutesRepresentative1
#print axioms Krenn.X5LegacyDispatch.refutesRepresentative1294

end Krenn.X5LegacyDispatch

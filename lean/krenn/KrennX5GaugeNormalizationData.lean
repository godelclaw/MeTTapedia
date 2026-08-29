import KrennGaugeNormalization

/-! Generated integral gauge-normalization data for audited X5 cases. -/

namespace Krenn.X5GaugeNormalizationData

open MonochromaticQuantumGraph
open Krenn.GaugeNormalization
open scoped Matrix

/- The generated registries contain 336 entries.  This raises only
elaboration recursion depth; every arithmetic proof remains `by decide`. -/
set_option maxRecDepth 100000

def selectedCase0 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 1, MonochromaticQuantumGraph.mkEdge 0 4 0 1, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase0 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 0, 1, 0], ![(-1), (-1), (-1), 3, (-1)], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![1, 0, 0, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase0 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase0 parameter.1 parameter.2

theorem rightInverseCase0_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase0 k) parameter *
      rightInverseCase0 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase0 : NormalizationDatum :=
  ⟨0, selectedCase0, rightInverseCase0,
    rightInverseCase0_ok⟩

def selectedCase1 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 1, MonochromaticQuantumGraph.mkEdge 0 4 0 1, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase1 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, (-1)]], ![![0, 0, 0, 0, 0], ![1, 0, 0, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase1 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase1 parameter.1 parameter.2

theorem rightInverseCase1_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase1 k) parameter *
      rightInverseCase1 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase1 : NormalizationDatum :=
  ⟨1, selectedCase1, rightInverseCase1,
    rightInverseCase1_ok⟩

def selectedCase2 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 1, MonochromaticQuantumGraph.mkEdge 0 4 0 1, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase2 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![1, 0, 0, (-2), (-1)], ![1, 0, 0, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase2 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase2 parameter.1 parameter.2

theorem rightInverseCase2_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase2 k) parameter *
      rightInverseCase2 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase2 : NormalizationDatum :=
  ⟨2, selectedCase2, rightInverseCase2,
    rightInverseCase2_ok⟩

def selectedCase3 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 1, MonochromaticQuantumGraph.mkEdge 0 4 0 1, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase3 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0], ![1, 0, 0, (-1), (-1)]], ![![0, 0, 0, 0, 0], ![1, 0, 0, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase3 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase3 parameter.1 parameter.2

theorem rightInverseCase3_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase3 k) parameter *
      rightInverseCase3 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase3 : NormalizationDatum :=
  ⟨3, selectedCase3, rightInverseCase3,
    rightInverseCase3_ok⟩

def selectedCase4 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 1, MonochromaticQuantumGraph.mkEdge 0 4 0 1, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase4 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, (-1), (-1)], ![1, 0, 0, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase4 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase4 parameter.1 parameter.2

theorem rightInverseCase4_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase4 k) parameter *
      rightInverseCase4 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase4 : NormalizationDatum :=
  ⟨4, selectedCase4, rightInverseCase4,
    rightInverseCase4_ok⟩

def selectedCase5 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 1, MonochromaticQuantumGraph.mkEdge 0 4 0 1, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase5 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 0, 1, 0], ![(-1), (-1), (-1), 3, (-1)], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![1, 0, 0, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase5 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase5 parameter.1 parameter.2

theorem rightInverseCase5_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase5 k) parameter *
      rightInverseCase5 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase5 : NormalizationDatum :=
  ⟨5, selectedCase5, rightInverseCase5,
    rightInverseCase5_ok⟩

def selectedCase6 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 1, MonochromaticQuantumGraph.mkEdge 0 4 0 2, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase6 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 0, 1, 0], ![(-1), (-1), (-1), 3, (-1)], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![1, 0, 0, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase6 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase6 parameter.1 parameter.2

theorem rightInverseCase6_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase6 k) parameter *
      rightInverseCase6 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase6 : NormalizationDatum :=
  ⟨6, selectedCase6, rightInverseCase6,
    rightInverseCase6_ok⟩

def selectedCase7 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 1, MonochromaticQuantumGraph.mkEdge 0 4 0 2, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase7 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, (-1)]], ![![0, 0, 0, 0, 0], ![1, 0, 0, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase7 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase7 parameter.1 parameter.2

theorem rightInverseCase7_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase7 k) parameter *
      rightInverseCase7 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase7 : NormalizationDatum :=
  ⟨7, selectedCase7, rightInverseCase7,
    rightInverseCase7_ok⟩

def selectedCase8 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 1, MonochromaticQuantumGraph.mkEdge 0 4 0 2, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase8 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![1, 0, 0, (-2), (-1)], ![1, 0, 0, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase8 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase8 parameter.1 parameter.2

theorem rightInverseCase8_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase8 k) parameter *
      rightInverseCase8 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase8 : NormalizationDatum :=
  ⟨8, selectedCase8, rightInverseCase8,
    rightInverseCase8_ok⟩

def selectedCase9 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 1, MonochromaticQuantumGraph.mkEdge 0 4 0 2, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase9 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0], ![1, 0, 0, (-1), (-1)]], ![![0, 0, 0, 0, 0], ![1, 0, 0, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase9 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase9 parameter.1 parameter.2

theorem rightInverseCase9_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase9 k) parameter *
      rightInverseCase9 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase9 : NormalizationDatum :=
  ⟨9, selectedCase9, rightInverseCase9,
    rightInverseCase9_ok⟩

def selectedCase10 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 1, MonochromaticQuantumGraph.mkEdge 0 4 0 2, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase10 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, (-1), (-1)], ![1, 0, 0, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase10 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase10 parameter.1 parameter.2

theorem rightInverseCase10_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase10 k) parameter *
      rightInverseCase10 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase10 : NormalizationDatum :=
  ⟨10, selectedCase10, rightInverseCase10,
    rightInverseCase10_ok⟩

def selectedCase11 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 1, MonochromaticQuantumGraph.mkEdge 0 4 0 2, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase11 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 0, 1, 0], ![(-1), (-1), (-1), 3, (-1)], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![1, 0, 0, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase11 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase11 parameter.1 parameter.2

theorem rightInverseCase11_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase11 k) parameter *
      rightInverseCase11 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase11 : NormalizationDatum :=
  ⟨11, selectedCase11, rightInverseCase11,
    rightInverseCase11_ok⟩

def selectedCase12 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 1, MonochromaticQuantumGraph.mkEdge 0 4 1 0, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase12 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![1, 1, (-2), 1, 1], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase12 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase12 parameter.1 parameter.2

theorem rightInverseCase12_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase12 k) parameter *
      rightInverseCase12 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase12 : NormalizationDatum :=
  ⟨12, selectedCase12, rightInverseCase12,
    rightInverseCase12_ok⟩

def selectedCase13 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 1, MonochromaticQuantumGraph.mkEdge 0 4 1 0, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase13 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, (-1)]], ![![0, 0, 0, 0, 0], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase13 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase13 parameter.1 parameter.2

theorem rightInverseCase13_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase13 k) parameter *
      rightInverseCase13 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase13 : NormalizationDatum :=
  ⟨13, selectedCase13, rightInverseCase13,
    rightInverseCase13_ok⟩

def selectedCase14 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 1, MonochromaticQuantumGraph.mkEdge 0 4 1 0, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase14 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![1, 0, (-2), 0, (-1)], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase14 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase14 parameter.1 parameter.2

theorem rightInverseCase14_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase14 k) parameter *
      rightInverseCase14 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase14 : NormalizationDatum :=
  ⟨14, selectedCase14, rightInverseCase14,
    rightInverseCase14_ok⟩

def selectedCase15 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 1, MonochromaticQuantumGraph.mkEdge 0 4 1 0, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase15 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, (-1), 0, (-1)]], ![![0, 0, 0, 0, 0], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase15 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase15 parameter.1 parameter.2

theorem rightInverseCase15_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase15 k) parameter *
      rightInverseCase15 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase15 : NormalizationDatum :=
  ⟨15, selectedCase15, rightInverseCase15,
    rightInverseCase15_ok⟩

def selectedCase16 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 1, MonochromaticQuantumGraph.mkEdge 0 4 1 0, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase16 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![0, 0, (-1), 0, (-1)], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase16 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase16 parameter.1 parameter.2

theorem rightInverseCase16_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase16 k) parameter *
      rightInverseCase16 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase16 : NormalizationDatum :=
  ⟨16, selectedCase16, rightInverseCase16,
    rightInverseCase16_ok⟩

def selectedCase17 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 1, MonochromaticQuantumGraph.mkEdge 0 4 1 0, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase17 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![1, 0, (-1), 0, 0], ![1, 1, (-2), 1, 1]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase17 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase17 parameter.1 parameter.2

theorem rightInverseCase17_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase17 k) parameter *
      rightInverseCase17 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase17 : NormalizationDatum :=
  ⟨17, selectedCase17, rightInverseCase17,
    rightInverseCase17_ok⟩

def selectedCase18 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 1, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase18 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![1, 1, (-2), 1, 1], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase18 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase18 parameter.1 parameter.2

theorem rightInverseCase18_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase18 k) parameter *
      rightInverseCase18 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase18 : NormalizationDatum :=
  ⟨18, selectedCase18, rightInverseCase18,
    rightInverseCase18_ok⟩

def selectedCase19 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 1, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase19 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, (-1)]], ![![0, 0, 0, 0, 0], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase19 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase19 parameter.1 parameter.2

theorem rightInverseCase19_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase19 k) parameter *
      rightInverseCase19 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase19 : NormalizationDatum :=
  ⟨19, selectedCase19, rightInverseCase19,
    rightInverseCase19_ok⟩

def selectedCase20 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 1, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase20 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![1, 0, (-2), 0, (-1)], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase20 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase20 parameter.1 parameter.2

theorem rightInverseCase20_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase20 k) parameter *
      rightInverseCase20 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase20 : NormalizationDatum :=
  ⟨20, selectedCase20, rightInverseCase20,
    rightInverseCase20_ok⟩

def selectedCase21 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 1, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase21 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, (-1), 0, (-1)]], ![![0, 0, 0, 0, 0], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase21 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase21 parameter.1 parameter.2

theorem rightInverseCase21_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase21 k) parameter *
      rightInverseCase21 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase21 : NormalizationDatum :=
  ⟨21, selectedCase21, rightInverseCase21,
    rightInverseCase21_ok⟩

def selectedCase22 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 1, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase22 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![0, 0, (-1), 0, (-1)], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase22 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase22 parameter.1 parameter.2

theorem rightInverseCase22_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase22 k) parameter *
      rightInverseCase22 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase22 : NormalizationDatum :=
  ⟨22, selectedCase22, rightInverseCase22,
    rightInverseCase22_ok⟩

def selectedCase23 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 1, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase23 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![1, 0, (-1), 0, 0], ![1, 1, (-2), 1, 1]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase23 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase23 parameter.1 parameter.2

theorem rightInverseCase23_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase23 k) parameter *
      rightInverseCase23 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase23 : NormalizationDatum :=
  ⟨23, selectedCase23, rightInverseCase23,
    rightInverseCase23_ok⟩

def selectedCase24 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 1, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase24 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![(-1), (-1), 2, 0, (-1)], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase24 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase24 parameter.1 parameter.2

theorem rightInverseCase24_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase24 k) parameter *
      rightInverseCase24 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase24 : NormalizationDatum :=
  ⟨24, selectedCase24, rightInverseCase24,
    rightInverseCase24_ok⟩

def selectedCase25 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 1, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase25 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 1, 1], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase25 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase25 parameter.1 parameter.2

theorem rightInverseCase25_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase25 k) parameter *
      rightInverseCase25 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase25 : NormalizationDatum :=
  ⟨25, selectedCase25, rightInverseCase25,
    rightInverseCase25_ok⟩

def selectedCase26 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 1, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase26 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![1, 0, (-2), 0, (-1)], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase26 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase26 parameter.1 parameter.2

theorem rightInverseCase26_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase26 k) parameter *
      rightInverseCase26 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase26 : NormalizationDatum :=
  ⟨26, selectedCase26, rightInverseCase26,
    rightInverseCase26_ok⟩

def selectedCase27 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 1, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase27 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, 0, (-1), 0, 0], ![1, 0, (-1), (-1), (-1)]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase27 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase27 parameter.1 parameter.2

theorem rightInverseCase27_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase27 k) parameter *
      rightInverseCase27 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase27 : NormalizationDatum :=
  ⟨27, selectedCase27, rightInverseCase27,
    rightInverseCase27_ok⟩

def selectedCase28 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 1, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase28 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, (-1), 0, (-1)], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase28 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase28 parameter.1 parameter.2

theorem rightInverseCase28_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase28 k) parameter *
      rightInverseCase28 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase28 : NormalizationDatum :=
  ⟨28, selectedCase28, rightInverseCase28,
    rightInverseCase28_ok⟩

def selectedCase29 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 1, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase29 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![(-1), (-1), 2, 0, (-1)], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase29 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase29 parameter.1 parameter.2

theorem rightInverseCase29_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase29 k) parameter *
      rightInverseCase29 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase29 : NormalizationDatum :=
  ⟨29, selectedCase29, rightInverseCase29,
    rightInverseCase29_ok⟩

def selectedCase30 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 1, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase30 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![(-1), (-1), 2, 0, (-1)], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase30 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase30 parameter.1 parameter.2

theorem rightInverseCase30_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase30 k) parameter *
      rightInverseCase30 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase30 : NormalizationDatum :=
  ⟨30, selectedCase30, rightInverseCase30,
    rightInverseCase30_ok⟩

def selectedCase31 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 1, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase31 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 1, 1], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase31 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase31 parameter.1 parameter.2

theorem rightInverseCase31_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase31 k) parameter *
      rightInverseCase31 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase31 : NormalizationDatum :=
  ⟨31, selectedCase31, rightInverseCase31,
    rightInverseCase31_ok⟩

def selectedCase32 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 1, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase32 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![1, 0, (-2), 0, (-1)], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase32 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase32 parameter.1 parameter.2

theorem rightInverseCase32_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase32 k) parameter *
      rightInverseCase32 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase32 : NormalizationDatum :=
  ⟨32, selectedCase32, rightInverseCase32,
    rightInverseCase32_ok⟩

def selectedCase33 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 1, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase33 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, 0, (-1), 0, 0], ![1, 0, (-1), (-1), (-1)]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase33 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase33 parameter.1 parameter.2

theorem rightInverseCase33_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase33 k) parameter *
      rightInverseCase33 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase33 : NormalizationDatum :=
  ⟨33, selectedCase33, rightInverseCase33,
    rightInverseCase33_ok⟩

def selectedCase34 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 1, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase34 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, (-1), 0, (-1)], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase34 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase34 parameter.1 parameter.2

theorem rightInverseCase34_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase34 k) parameter *
      rightInverseCase34 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase34 : NormalizationDatum :=
  ⟨34, selectedCase34, rightInverseCase34,
    rightInverseCase34_ok⟩

def selectedCase35 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 1, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase35 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![(-1), (-1), 2, 0, (-1)], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase35 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase35 parameter.1 parameter.2

theorem rightInverseCase35_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase35 k) parameter *
      rightInverseCase35 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase35 : NormalizationDatum :=
  ⟨35, selectedCase35, rightInverseCase35,
    rightInverseCase35_ok⟩

def selectedCase42 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 0 2, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase42 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 0, 1, 0], ![(-1), (-1), 0, 2, (-1)], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![1, 0, 0, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase42 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase42 parameter.1 parameter.2

theorem rightInverseCase42_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase42 k) parameter *
      rightInverseCase42 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase42 : NormalizationDatum :=
  ⟨42, selectedCase42, rightInverseCase42,
    rightInverseCase42_ok⟩

def selectedCase43 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 0 2, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase43 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0], ![0, 0, (-1), 1, (-1)]], ![![0, 0, 0, 0, 0], ![1, 0, 0, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase43 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase43 parameter.1 parameter.2

theorem rightInverseCase43_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase43 k) parameter *
      rightInverseCase43 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase43 : NormalizationDatum :=
  ⟨43, selectedCase43, rightInverseCase43,
    rightInverseCase43_ok⟩

def selectedCase44 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 0 2, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase44 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![1, 0, 0, (-2), (-1)], ![1, 0, 0, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase44 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase44 parameter.1 parameter.2

theorem rightInverseCase44_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase44 k) parameter *
      rightInverseCase44 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase44 : NormalizationDatum :=
  ⟨44, selectedCase44, rightInverseCase44,
    rightInverseCase44_ok⟩

def selectedCase45 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 0 2, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase45 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0], ![1, 0, (-1), 0, (-1)]], ![![0, 0, 0, 0, 0], ![1, 0, 0, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase45 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase45 parameter.1 parameter.2

theorem rightInverseCase45_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase45 k) parameter *
      rightInverseCase45 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase45 : NormalizationDatum :=
  ⟨45, selectedCase45, rightInverseCase45,
    rightInverseCase45_ok⟩

def selectedCase46 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 0 2, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase46 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, (-1), (-1)], ![1, 0, 0, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase46 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase46 parameter.1 parameter.2

theorem rightInverseCase46_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase46 k) parameter *
      rightInverseCase46 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase46 : NormalizationDatum :=
  ⟨46, selectedCase46, rightInverseCase46,
    rightInverseCase46_ok⟩

def selectedCase47 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 0 2, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase47 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 0, 1, 0], ![(-1), (-1), 0, 2, (-1)], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![1, 0, 0, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase47 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase47 parameter.1 parameter.2

theorem rightInverseCase47_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase47 k) parameter *
      rightInverseCase47 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase47 : NormalizationDatum :=
  ⟨47, selectedCase47, rightInverseCase47,
    rightInverseCase47_ok⟩

def selectedCase48 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 1 0, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase48 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![1, 1, (-2), 1, 1], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase48 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase48 parameter.1 parameter.2

theorem rightInverseCase48_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase48 k) parameter *
      rightInverseCase48 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase48 : NormalizationDatum :=
  ⟨48, selectedCase48, rightInverseCase48,
    rightInverseCase48_ok⟩

def selectedCase49 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 1 0, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase49 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, (-1)]], ![![0, 0, 0, 0, 0], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase49 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase49 parameter.1 parameter.2

theorem rightInverseCase49_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase49 k) parameter *
      rightInverseCase49 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase49 : NormalizationDatum :=
  ⟨49, selectedCase49, rightInverseCase49,
    rightInverseCase49_ok⟩

def selectedCase50 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 1 0, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase50 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![1, 0, (-2), 0, (-1)], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase50 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase50 parameter.1 parameter.2

theorem rightInverseCase50_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase50 k) parameter *
      rightInverseCase50 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase50 : NormalizationDatum :=
  ⟨50, selectedCase50, rightInverseCase50,
    rightInverseCase50_ok⟩

def selectedCase51 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 1 0, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase51 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, (-1), 0, (-1)]], ![![0, 0, 0, 0, 0], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase51 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase51 parameter.1 parameter.2

theorem rightInverseCase51_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase51 k) parameter *
      rightInverseCase51 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase51 : NormalizationDatum :=
  ⟨51, selectedCase51, rightInverseCase51,
    rightInverseCase51_ok⟩

def selectedCase52 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 1 0, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase52 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![0, 0, (-1), 0, (-1)], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase52 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase52 parameter.1 parameter.2

theorem rightInverseCase52_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase52 k) parameter *
      rightInverseCase52 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase52 : NormalizationDatum :=
  ⟨52, selectedCase52, rightInverseCase52,
    rightInverseCase52_ok⟩

def selectedCase53 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 1 0, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase53 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![1, 0, (-1), 0, 0], ![1, 1, (-2), 1, 1]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase53 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase53 parameter.1 parameter.2

theorem rightInverseCase53_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase53 k) parameter *
      rightInverseCase53 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase53 : NormalizationDatum :=
  ⟨53, selectedCase53, rightInverseCase53,
    rightInverseCase53_ok⟩

def selectedCase54 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase54 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![1, 1, (-2), 1, 1], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase54 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase54 parameter.1 parameter.2

theorem rightInverseCase54_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase54 k) parameter *
      rightInverseCase54 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase54 : NormalizationDatum :=
  ⟨54, selectedCase54, rightInverseCase54,
    rightInverseCase54_ok⟩

def selectedCase55 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase55 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, (-1)]], ![![0, 0, 0, 0, 0], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase55 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase55 parameter.1 parameter.2

theorem rightInverseCase55_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase55 k) parameter *
      rightInverseCase55 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase55 : NormalizationDatum :=
  ⟨55, selectedCase55, rightInverseCase55,
    rightInverseCase55_ok⟩

def selectedCase56 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase56 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![1, 0, (-2), 0, (-1)], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase56 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase56 parameter.1 parameter.2

theorem rightInverseCase56_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase56 k) parameter *
      rightInverseCase56 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase56 : NormalizationDatum :=
  ⟨56, selectedCase56, rightInverseCase56,
    rightInverseCase56_ok⟩

def selectedCase57 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase57 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, (-1), 0, (-1)]], ![![0, 0, 0, 0, 0], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase57 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase57 parameter.1 parameter.2

theorem rightInverseCase57_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase57 k) parameter *
      rightInverseCase57 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase57 : NormalizationDatum :=
  ⟨57, selectedCase57, rightInverseCase57,
    rightInverseCase57_ok⟩

def selectedCase58 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase58 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![0, 0, (-1), 0, (-1)], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase58 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase58 parameter.1 parameter.2

theorem rightInverseCase58_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase58 k) parameter *
      rightInverseCase58 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase58 : NormalizationDatum :=
  ⟨58, selectedCase58, rightInverseCase58,
    rightInverseCase58_ok⟩

def selectedCase59 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase59 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![1, 0, (-1), 0, 0], ![1, 1, (-2), 1, 1]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase59 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase59 parameter.1 parameter.2

theorem rightInverseCase59_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase59 k) parameter *
      rightInverseCase59 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase59 : NormalizationDatum :=
  ⟨59, selectedCase59, rightInverseCase59,
    rightInverseCase59_ok⟩

def selectedCase60 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase60 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![(-1), (-1), 2, 0, (-1)], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase60 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase60 parameter.1 parameter.2

theorem rightInverseCase60_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase60 k) parameter *
      rightInverseCase60 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase60 : NormalizationDatum :=
  ⟨60, selectedCase60, rightInverseCase60,
    rightInverseCase60_ok⟩

def selectedCase61 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase61 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 1, 1], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase61 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase61 parameter.1 parameter.2

theorem rightInverseCase61_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase61 k) parameter *
      rightInverseCase61 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase61 : NormalizationDatum :=
  ⟨61, selectedCase61, rightInverseCase61,
    rightInverseCase61_ok⟩

def selectedCase62 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase62 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![1, 0, (-2), 0, (-1)], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase62 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase62 parameter.1 parameter.2

theorem rightInverseCase62_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase62 k) parameter *
      rightInverseCase62 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase62 : NormalizationDatum :=
  ⟨62, selectedCase62, rightInverseCase62,
    rightInverseCase62_ok⟩

def selectedCase63 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase63 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, 0, (-1), 0, 0], ![1, 0, (-1), (-1), (-1)]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase63 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase63 parameter.1 parameter.2

theorem rightInverseCase63_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase63 k) parameter *
      rightInverseCase63 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase63 : NormalizationDatum :=
  ⟨63, selectedCase63, rightInverseCase63,
    rightInverseCase63_ok⟩

def selectedCase64 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase64 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, (-1), 0, (-1)], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase64 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase64 parameter.1 parameter.2

theorem rightInverseCase64_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase64 k) parameter *
      rightInverseCase64 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase64 : NormalizationDatum :=
  ⟨64, selectedCase64, rightInverseCase64,
    rightInverseCase64_ok⟩

def selectedCase65 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase65 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![(-1), (-1), 2, 0, (-1)], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase65 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase65 parameter.1 parameter.2

theorem rightInverseCase65_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase65 k) parameter *
      rightInverseCase65 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase65 : NormalizationDatum :=
  ⟨65, selectedCase65, rightInverseCase65,
    rightInverseCase65_ok⟩

def selectedCase66 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase66 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![(-1), (-1), 2, 0, (-1)], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase66 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase66 parameter.1 parameter.2

theorem rightInverseCase66_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase66 k) parameter *
      rightInverseCase66 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase66 : NormalizationDatum :=
  ⟨66, selectedCase66, rightInverseCase66,
    rightInverseCase66_ok⟩

def selectedCase67 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase67 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 1, 1], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase67 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase67 parameter.1 parameter.2

theorem rightInverseCase67_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase67 k) parameter *
      rightInverseCase67 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase67 : NormalizationDatum :=
  ⟨67, selectedCase67, rightInverseCase67,
    rightInverseCase67_ok⟩

def selectedCase68 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase68 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![1, 0, (-2), 0, (-1)], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase68 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase68 parameter.1 parameter.2

theorem rightInverseCase68_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase68 k) parameter *
      rightInverseCase68 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase68 : NormalizationDatum :=
  ⟨68, selectedCase68, rightInverseCase68,
    rightInverseCase68_ok⟩

def selectedCase69 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase69 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, 0, (-1), 0, 0], ![1, 0, (-1), (-1), (-1)]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase69 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase69 parameter.1 parameter.2

theorem rightInverseCase69_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase69 k) parameter *
      rightInverseCase69 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase69 : NormalizationDatum :=
  ⟨69, selectedCase69, rightInverseCase69,
    rightInverseCase69_ok⟩

def selectedCase70 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase70 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, (-1), 0, (-1)], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase70 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase70 parameter.1 parameter.2

theorem rightInverseCase70_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase70 k) parameter *
      rightInverseCase70 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase70 : NormalizationDatum :=
  ⟨70, selectedCase70, rightInverseCase70,
    rightInverseCase70_ok⟩

def selectedCase71 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase71 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![(-1), (-1), 2, 0, (-1)], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase71 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase71 parameter.1 parameter.2

theorem rightInverseCase71_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase71 k) parameter *
      rightInverseCase71 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase71 : NormalizationDatum :=
  ⟨71, selectedCase71, rightInverseCase71,
    rightInverseCase71_ok⟩

def selectedCase84 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 1 0, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase84 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![1, (-1), 0, 1, 1], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase84 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase84 parameter.1 parameter.2

theorem rightInverseCase84_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase84 k) parameter *
      rightInverseCase84 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase84 : NormalizationDatum :=
  ⟨84, selectedCase84, rightInverseCase84,
    rightInverseCase84_ok⟩

def selectedCase85 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 1 0, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase85 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, (-1)]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase85 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase85 parameter.1 parameter.2

theorem rightInverseCase85_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase85 k) parameter *
      rightInverseCase85 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase85 : NormalizationDatum :=
  ⟨85, selectedCase85, rightInverseCase85,
    rightInverseCase85_ok⟩

def selectedCase86 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 1 0, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase86 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![1, (-2), (-1), 1, (-1)], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase86 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase86 parameter.1 parameter.2

theorem rightInverseCase86_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase86 k) parameter *
      rightInverseCase86 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase86 : NormalizationDatum :=
  ⟨86, selectedCase86, rightInverseCase86,
    rightInverseCase86_ok⟩

def selectedCase87 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 1 0, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase87 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0], ![1, (-1), 0, 0, (-1)]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase87 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase87 parameter.1 parameter.2

theorem rightInverseCase87_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase87 k) parameter *
      rightInverseCase87 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase87 : NormalizationDatum :=
  ⟨87, selectedCase87, rightInverseCase87,
    rightInverseCase87_ok⟩

def selectedCase88 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 1 0, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase88 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![0, (-1), (-1), 1, (-1)], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase88 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase88 parameter.1 parameter.2

theorem rightInverseCase88_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase88 k) parameter *
      rightInverseCase88 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase88 : NormalizationDatum :=
  ⟨88, selectedCase88, rightInverseCase88,
    rightInverseCase88_ok⟩

def selectedCase89 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 1 0, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase89 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![1, (-1), 0, 1, 1]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase89 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase89 parameter.1 parameter.2

theorem rightInverseCase89_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase89 k) parameter *
      rightInverseCase89 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase89 : NormalizationDatum :=
  ⟨89, selectedCase89, rightInverseCase89,
    rightInverseCase89_ok⟩

def selectedCase90 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase90 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![1, (-1), 0, 1, 1], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase90 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase90 parameter.1 parameter.2

theorem rightInverseCase90_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase90 k) parameter *
      rightInverseCase90 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase90 : NormalizationDatum :=
  ⟨90, selectedCase90, rightInverseCase90,
    rightInverseCase90_ok⟩

def selectedCase91 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase91 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, (-1)]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase91 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase91 parameter.1 parameter.2

theorem rightInverseCase91_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase91 k) parameter *
      rightInverseCase91 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase91 : NormalizationDatum :=
  ⟨91, selectedCase91, rightInverseCase91,
    rightInverseCase91_ok⟩

def selectedCase92 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase92 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![1, (-2), (-1), 1, (-1)], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase92 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase92 parameter.1 parameter.2

theorem rightInverseCase92_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase92 k) parameter *
      rightInverseCase92 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase92 : NormalizationDatum :=
  ⟨92, selectedCase92, rightInverseCase92,
    rightInverseCase92_ok⟩

def selectedCase93 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase93 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0], ![1, (-1), 0, 0, (-1)]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase93 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase93 parameter.1 parameter.2

theorem rightInverseCase93_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase93 k) parameter *
      rightInverseCase93 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase93 : NormalizationDatum :=
  ⟨93, selectedCase93, rightInverseCase93,
    rightInverseCase93_ok⟩

def selectedCase94 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase94 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![0, (-1), (-1), 1, (-1)], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase94 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase94 parameter.1 parameter.2

theorem rightInverseCase94_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase94 k) parameter *
      rightInverseCase94 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase94 : NormalizationDatum :=
  ⟨94, selectedCase94, rightInverseCase94,
    rightInverseCase94_ok⟩

def selectedCase95 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase95 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![1, (-1), 0, 1, 1]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase95 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase95 parameter.1 parameter.2

theorem rightInverseCase95_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase95 k) parameter *
      rightInverseCase95 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase95 : NormalizationDatum :=
  ⟨95, selectedCase95, rightInverseCase95,
    rightInverseCase95_ok⟩

def selectedCase96 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase96 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![1, (-1), 1, 0, 1], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase96 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase96 parameter.1 parameter.2

theorem rightInverseCase96_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase96 k) parameter *
      rightInverseCase96 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase96 : NormalizationDatum :=
  ⟨96, selectedCase96, rightInverseCase96,
    rightInverseCase96_ok⟩

def selectedCase97 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase97 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 1, 1], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase97 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase97 parameter.1 parameter.2

theorem rightInverseCase97_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase97 k) parameter *
      rightInverseCase97 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase97 : NormalizationDatum :=
  ⟨97, selectedCase97, rightInverseCase97,
    rightInverseCase97_ok⟩

def selectedCase98 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase98 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![1, (-2), 0, 0, (-1)], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase98 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase98 parameter.1 parameter.2

theorem rightInverseCase98_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase98 k) parameter *
      rightInverseCase98 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase98 : NormalizationDatum :=
  ⟨98, selectedCase98, rightInverseCase98,
    rightInverseCase98_ok⟩

def selectedCase99 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase99 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![1, (-1), 0, (-1), (-1)]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase99 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase99 parameter.1 parameter.2

theorem rightInverseCase99_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase99 k) parameter *
      rightInverseCase99 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase99 : NormalizationDatum :=
  ⟨99, selectedCase99, rightInverseCase99,
    rightInverseCase99_ok⟩

def selectedCase100 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase100 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, (-1), 0, 0, (-1)], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase100 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase100 parameter.1 parameter.2

theorem rightInverseCase100_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase100 k) parameter *
      rightInverseCase100 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase100 : NormalizationDatum :=
  ⟨100, selectedCase100, rightInverseCase100,
    rightInverseCase100_ok⟩

def selectedCase101 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase101 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![1, (-1), 1, 0, 1]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase101 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase101 parameter.1 parameter.2

theorem rightInverseCase101_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase101 k) parameter *
      rightInverseCase101 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase101 : NormalizationDatum :=
  ⟨101, selectedCase101, rightInverseCase101,
    rightInverseCase101_ok⟩

def selectedCase102 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase102 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![1, (-1), 1, 0, 1], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase102 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase102 parameter.1 parameter.2

theorem rightInverseCase102_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase102 k) parameter *
      rightInverseCase102 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase102 : NormalizationDatum :=
  ⟨102, selectedCase102, rightInverseCase102,
    rightInverseCase102_ok⟩

def selectedCase103 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase103 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 1, 1], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase103 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase103 parameter.1 parameter.2

theorem rightInverseCase103_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase103 k) parameter *
      rightInverseCase103 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase103 : NormalizationDatum :=
  ⟨103, selectedCase103, rightInverseCase103,
    rightInverseCase103_ok⟩

def selectedCase104 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase104 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![1, (-2), 0, 0, (-1)], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase104 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase104 parameter.1 parameter.2

theorem rightInverseCase104_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase104 k) parameter *
      rightInverseCase104 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase104 : NormalizationDatum :=
  ⟨104, selectedCase104, rightInverseCase104,
    rightInverseCase104_ok⟩

def selectedCase105 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase105 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![1, (-1), 0, (-1), (-1)]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase105 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase105 parameter.1 parameter.2

theorem rightInverseCase105_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase105 k) parameter *
      rightInverseCase105 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase105 : NormalizationDatum :=
  ⟨105, selectedCase105, rightInverseCase105,
    rightInverseCase105_ok⟩

def selectedCase106 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase106 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, (-1), 0, 0, (-1)], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase106 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase106 parameter.1 parameter.2

theorem rightInverseCase106_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase106 k) parameter *
      rightInverseCase106 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase106 : NormalizationDatum :=
  ⟨106, selectedCase106, rightInverseCase106,
    rightInverseCase106_ok⟩

def selectedCase107 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase107 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![1, (-1), 1, 0, 1]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase107 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase107 parameter.1 parameter.2

theorem rightInverseCase107_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase107 k) parameter *
      rightInverseCase107 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase107 : NormalizationDatum :=
  ⟨107, selectedCase107, rightInverseCase107,
    rightInverseCase107_ok⟩

def selectedCase126 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase126 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![1, (-1), 0, 1, 1], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase126 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase126 parameter.1 parameter.2

theorem rightInverseCase126_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase126 k) parameter *
      rightInverseCase126 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase126 : NormalizationDatum :=
  ⟨126, selectedCase126, rightInverseCase126,
    rightInverseCase126_ok⟩

def selectedCase127 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase127 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, (-1), 1, (-1)]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase127 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase127 parameter.1 parameter.2

theorem rightInverseCase127_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase127 k) parameter *
      rightInverseCase127 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase127 : NormalizationDatum :=
  ⟨127, selectedCase127, rightInverseCase127,
    rightInverseCase127_ok⟩

def selectedCase128 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase128 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![1, (-2), 0, 0, (-1)], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase128 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase128 parameter.1 parameter.2

theorem rightInverseCase128_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase128 k) parameter *
      rightInverseCase128 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase128 : NormalizationDatum :=
  ⟨128, selectedCase128, rightInverseCase128,
    rightInverseCase128_ok⟩

def selectedCase129 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase129 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0], ![1, (-1), (-1), 1, (-1)]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase129 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase129 parameter.1 parameter.2

theorem rightInverseCase129_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase129 k) parameter *
      rightInverseCase129 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase129 : NormalizationDatum :=
  ⟨129, selectedCase129, rightInverseCase129,
    rightInverseCase129_ok⟩

def selectedCase130 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase130 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![0, (-1), 0, 0, (-1)], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase130 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase130 parameter.1 parameter.2

theorem rightInverseCase130_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase130 k) parameter *
      rightInverseCase130 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase130 : NormalizationDatum :=
  ⟨130, selectedCase130, rightInverseCase130,
    rightInverseCase130_ok⟩

def selectedCase131 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase131 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![1, (-1), 0, 1, 1]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase131 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase131 parameter.1 parameter.2

theorem rightInverseCase131_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase131 k) parameter *
      rightInverseCase131 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase131 : NormalizationDatum :=
  ⟨131, selectedCase131, rightInverseCase131,
    rightInverseCase131_ok⟩

def selectedCase132 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase132 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![1, (-1), 1, 0, 1], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase132 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase132 parameter.1 parameter.2

theorem rightInverseCase132_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase132 k) parameter *
      rightInverseCase132 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase132 : NormalizationDatum :=
  ⟨132, selectedCase132, rightInverseCase132,
    rightInverseCase132_ok⟩

def selectedCase133 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase133 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 1, 1], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase133 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase133 parameter.1 parameter.2

theorem rightInverseCase133_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase133 k) parameter *
      rightInverseCase133 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase133 : NormalizationDatum :=
  ⟨133, selectedCase133, rightInverseCase133,
    rightInverseCase133_ok⟩

def selectedCase134 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase134 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![1, (-2), 0, 0, (-1)], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase134 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase134 parameter.1 parameter.2

theorem rightInverseCase134_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase134 k) parameter *
      rightInverseCase134 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase134 : NormalizationDatum :=
  ⟨134, selectedCase134, rightInverseCase134,
    rightInverseCase134_ok⟩

def selectedCase135 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase135 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![1, (-1), 0, (-1), (-1)]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase135 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase135 parameter.1 parameter.2

theorem rightInverseCase135_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase135 k) parameter *
      rightInverseCase135 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase135 : NormalizationDatum :=
  ⟨135, selectedCase135, rightInverseCase135,
    rightInverseCase135_ok⟩

def selectedCase136 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase136 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, (-1), 0, 0, (-1)], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase136 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase136 parameter.1 parameter.2

theorem rightInverseCase136_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase136 k) parameter *
      rightInverseCase136 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase136 : NormalizationDatum :=
  ⟨136, selectedCase136, rightInverseCase136,
    rightInverseCase136_ok⟩

def selectedCase137 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase137 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![1, (-1), 1, 0, 1]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase137 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase137 parameter.1 parameter.2

theorem rightInverseCase137_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase137 k) parameter *
      rightInverseCase137 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase137 : NormalizationDatum :=
  ⟨137, selectedCase137, rightInverseCase137,
    rightInverseCase137_ok⟩

def selectedCase138 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase138 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![1, (-1), 1, 0, 1], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase138 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase138 parameter.1 parameter.2

theorem rightInverseCase138_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase138 k) parameter *
      rightInverseCase138 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase138 : NormalizationDatum :=
  ⟨138, selectedCase138, rightInverseCase138,
    rightInverseCase138_ok⟩

def selectedCase139 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase139 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 1, 1], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase139 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase139 parameter.1 parameter.2

theorem rightInverseCase139_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase139 k) parameter *
      rightInverseCase139 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase139 : NormalizationDatum :=
  ⟨139, selectedCase139, rightInverseCase139,
    rightInverseCase139_ok⟩

def selectedCase140 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase140 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![1, (-2), 0, 0, (-1)], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase140 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase140 parameter.1 parameter.2

theorem rightInverseCase140_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase140 k) parameter *
      rightInverseCase140 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase140 : NormalizationDatum :=
  ⟨140, selectedCase140, rightInverseCase140,
    rightInverseCase140_ok⟩

def selectedCase141 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase141 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![1, (-1), 0, (-1), (-1)]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase141 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase141 parameter.1 parameter.2

theorem rightInverseCase141_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase141 k) parameter *
      rightInverseCase141 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase141 : NormalizationDatum :=
  ⟨141, selectedCase141, rightInverseCase141,
    rightInverseCase141_ok⟩

def selectedCase142 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase142 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, (-1), 0, 0, (-1)], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase142 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase142 parameter.1 parameter.2

theorem rightInverseCase142_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase142 k) parameter *
      rightInverseCase142 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase142 : NormalizationDatum :=
  ⟨142, selectedCase142, rightInverseCase142,
    rightInverseCase142_ok⟩

def selectedCase143 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase143 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![1, (-1), 1, 0, 1]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase143 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase143 parameter.1 parameter.2

theorem rightInverseCase143_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase143 k) parameter *
      rightInverseCase143 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase143 : NormalizationDatum :=
  ⟨143, selectedCase143, rightInverseCase143,
    rightInverseCase143_ok⟩

def selectedCase168 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase168 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![(-1), 1, 0, 0, (-1)], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase168 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase168 parameter.1 parameter.2

theorem rightInverseCase168_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase168 k) parameter *
      rightInverseCase168 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase168 : NormalizationDatum :=
  ⟨168, selectedCase168, rightInverseCase168,
    rightInverseCase168_ok⟩

def selectedCase169 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase169 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 1, 1], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase169 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase169 parameter.1 parameter.2

theorem rightInverseCase169_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase169 k) parameter *
      rightInverseCase169 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase169 : NormalizationDatum :=
  ⟨169, selectedCase169, rightInverseCase169,
    rightInverseCase169_ok⟩

def selectedCase170 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase170 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![1, (-2), (-1), 1, (-1)], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase170 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase170 parameter.1 parameter.2

theorem rightInverseCase170_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase170 k) parameter *
      rightInverseCase170 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase170 : NormalizationDatum :=
  ⟨170, selectedCase170, rightInverseCase170,
    rightInverseCase170_ok⟩

def selectedCase171 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase171 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![1, (-1), 0, (-1), (-1)]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase171 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase171 parameter.1 parameter.2

theorem rightInverseCase171_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase171 k) parameter *
      rightInverseCase171 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase171 : NormalizationDatum :=
  ⟨171, selectedCase171, rightInverseCase171,
    rightInverseCase171_ok⟩

def selectedCase172 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase172 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, (-1), (-1), 1, (-1)], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase172 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase172 parameter.1 parameter.2

theorem rightInverseCase172_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase172 k) parameter *
      rightInverseCase172 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase172 : NormalizationDatum :=
  ⟨172, selectedCase172, rightInverseCase172,
    rightInverseCase172_ok⟩

def selectedCase173 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase173 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![(-1), 1, 0, 0, (-1)], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase173 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase173 parameter.1 parameter.2

theorem rightInverseCase173_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase173 k) parameter *
      rightInverseCase173 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase173 : NormalizationDatum :=
  ⟨173, selectedCase173, rightInverseCase173,
    rightInverseCase173_ok⟩

def selectedCase174 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase174 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![(-1), 1, 0, 0, (-1)], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase174 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase174 parameter.1 parameter.2

theorem rightInverseCase174_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase174 k) parameter *
      rightInverseCase174 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase174 : NormalizationDatum :=
  ⟨174, selectedCase174, rightInverseCase174,
    rightInverseCase174_ok⟩

def selectedCase175 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase175 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 1, 1], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase175 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase175 parameter.1 parameter.2

theorem rightInverseCase175_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase175 k) parameter *
      rightInverseCase175 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase175 : NormalizationDatum :=
  ⟨175, selectedCase175, rightInverseCase175,
    rightInverseCase175_ok⟩

def selectedCase176 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase176 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![1, (-2), (-1), 1, (-1)], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase176 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase176 parameter.1 parameter.2

theorem rightInverseCase176_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase176 k) parameter *
      rightInverseCase176 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase176 : NormalizationDatum :=
  ⟨176, selectedCase176, rightInverseCase176,
    rightInverseCase176_ok⟩

def selectedCase177 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase177 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![1, (-1), 0, (-1), (-1)]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase177 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase177 parameter.1 parameter.2

theorem rightInverseCase177_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase177 k) parameter *
      rightInverseCase177 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase177 : NormalizationDatum :=
  ⟨177, selectedCase177, rightInverseCase177,
    rightInverseCase177_ok⟩

def selectedCase178 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase178 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, (-1), (-1), 1, (-1)], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase178 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase178 parameter.1 parameter.2

theorem rightInverseCase178_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase178 k) parameter *
      rightInverseCase178 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase178 : NormalizationDatum :=
  ⟨178, selectedCase178, rightInverseCase178,
    rightInverseCase178_ok⟩

def selectedCase179 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase179 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![(-1), 1, 0, 0, (-1)], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase179 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase179 parameter.1 parameter.2

theorem rightInverseCase179_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase179 k) parameter *
      rightInverseCase179 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase179 : NormalizationDatum :=
  ⟨179, selectedCase179, rightInverseCase179,
    rightInverseCase179_ok⟩

def selectedCase210 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 2 1, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase210 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![(-1), 1, (-1), 1, (-1)], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase210 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase210 parameter.1 parameter.2

theorem rightInverseCase210_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase210 k) parameter *
      rightInverseCase210 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase210 : NormalizationDatum :=
  ⟨210, selectedCase210, rightInverseCase210,
    rightInverseCase210_ok⟩

def selectedCase211 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 2 1, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase211 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 1, 1], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase211 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase211 parameter.1 parameter.2

theorem rightInverseCase211_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase211 k) parameter *
      rightInverseCase211 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase211 : NormalizationDatum :=
  ⟨211, selectedCase211, rightInverseCase211,
    rightInverseCase211_ok⟩

def selectedCase212 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 2 1, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase212 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![1, (-2), 0, 0, (-1)], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase212 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase212 parameter.1 parameter.2

theorem rightInverseCase212_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase212 k) parameter *
      rightInverseCase212 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase212 : NormalizationDatum :=
  ⟨212, selectedCase212, rightInverseCase212,
    rightInverseCase212_ok⟩

def selectedCase213 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 2 1, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase213 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![1, (-1), 0, (-1), (-1)]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase213 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase213 parameter.1 parameter.2

theorem rightInverseCase213_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase213 k) parameter *
      rightInverseCase213 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase213 : NormalizationDatum :=
  ⟨213, selectedCase213, rightInverseCase213,
    rightInverseCase213_ok⟩

def selectedCase214 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 2 1, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase214 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, (-1), 0, 0, (-1)], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase214 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase214 parameter.1 parameter.2

theorem rightInverseCase214_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase214 k) parameter *
      rightInverseCase214 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase214 : NormalizationDatum :=
  ⟨214, selectedCase214, rightInverseCase214,
    rightInverseCase214_ok⟩

def selectedCase215 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 1, MonochromaticQuantumGraph.mkEdge 0 3 2 1, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase215 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![(-1), 1, (-1), 1, (-1)], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase215 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase215 parameter.1 parameter.2

theorem rightInverseCase215_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase215 k) parameter *
      rightInverseCase215 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase215 : NormalizationDatum :=
  ⟨215, selectedCase215, rightInverseCase215,
    rightInverseCase215_ok⟩

def selectedCase258 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 0 2, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase258 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 0, 1, 0], ![(-1), 0, 0, 1, (-1)], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![1, 0, 0, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, 0, (-1), 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase258 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase258 parameter.1 parameter.2

theorem rightInverseCase258_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase258 k) parameter *
      rightInverseCase258 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase258 : NormalizationDatum :=
  ⟨258, selectedCase258, rightInverseCase258,
    rightInverseCase258_ok⟩

def selectedCase259 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 0 2, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase259 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0], ![0, (-1), (-1), 2, (-1)]], ![![0, 0, 0, 0, 0], ![1, 0, 0, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, 0, (-1), 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase259 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase259 parameter.1 parameter.2

theorem rightInverseCase259_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase259 k) parameter *
      rightInverseCase259 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase259 : NormalizationDatum :=
  ⟨259, selectedCase259, rightInverseCase259,
    rightInverseCase259_ok⟩

def selectedCase260 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 0 2, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase260 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![1, 0, 0, (-2), (-1)], ![1, 0, 0, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, 0, (-1), 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase260 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase260 parameter.1 parameter.2

theorem rightInverseCase260_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase260 k) parameter *
      rightInverseCase260 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase260 : NormalizationDatum :=
  ⟨260, selectedCase260, rightInverseCase260,
    rightInverseCase260_ok⟩

def selectedCase261 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 0 2, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase261 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0], ![1, (-1), (-1), 1, (-1)]], ![![0, 0, 0, 0, 0], ![1, 0, 0, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, 0, (-1), 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase261 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase261 parameter.1 parameter.2

theorem rightInverseCase261_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase261 k) parameter *
      rightInverseCase261 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase261 : NormalizationDatum :=
  ⟨261, selectedCase261, rightInverseCase261,
    rightInverseCase261_ok⟩

def selectedCase262 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 0 2, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase262 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, (-1), (-1)], ![1, 0, 0, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, 0, (-1), 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase262 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase262 parameter.1 parameter.2

theorem rightInverseCase262_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase262 k) parameter *
      rightInverseCase262 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase262 : NormalizationDatum :=
  ⟨262, selectedCase262, rightInverseCase262,
    rightInverseCase262_ok⟩

def selectedCase263 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 0 2, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase263 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 0, 1, 0], ![(-1), 0, 0, 1, (-1)], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![1, 0, 0, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, 0, (-1), 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase263 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase263 parameter.1 parameter.2

theorem rightInverseCase263_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase263 k) parameter *
      rightInverseCase263 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase263 : NormalizationDatum :=
  ⟨263, selectedCase263, rightInverseCase263,
    rightInverseCase263_ok⟩

def selectedCase264 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 1 0, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase264 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![1, 0, (-1), 1, 1], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase264 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase264 parameter.1 parameter.2

theorem rightInverseCase264_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase264 k) parameter *
      rightInverseCase264 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase264 : NormalizationDatum :=
  ⟨264, selectedCase264, rightInverseCase264,
    rightInverseCase264_ok⟩

def selectedCase265 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 1 0, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase265 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, (-1), 1, 0, (-1)]], ![![0, 0, 0, 0, 0], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase265 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase265 parameter.1 parameter.2

theorem rightInverseCase265_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase265 k) parameter *
      rightInverseCase265 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase265 : NormalizationDatum :=
  ⟨265, selectedCase265, rightInverseCase265,
    rightInverseCase265_ok⟩

def selectedCase266 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 1 0, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase266 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![1, 0, (-2), 0, (-1)], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase266 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase266 parameter.1 parameter.2

theorem rightInverseCase266_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase266 k) parameter *
      rightInverseCase266 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase266 : NormalizationDatum :=
  ⟨266, selectedCase266, rightInverseCase266,
    rightInverseCase266_ok⟩

def selectedCase267 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 1 0, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase267 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, (-1), 0, 0, (-1)]], ![![0, 0, 0, 0, 0], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase267 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase267 parameter.1 parameter.2

theorem rightInverseCase267_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase267 k) parameter *
      rightInverseCase267 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase267 : NormalizationDatum :=
  ⟨267, selectedCase267, rightInverseCase267,
    rightInverseCase267_ok⟩

def selectedCase268 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 1 0, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase268 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![0, 0, (-1), 0, (-1)], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase268 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase268 parameter.1 parameter.2

theorem rightInverseCase268_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase268 k) parameter *
      rightInverseCase268 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase268 : NormalizationDatum :=
  ⟨268, selectedCase268, rightInverseCase268,
    rightInverseCase268_ok⟩

def selectedCase269 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 1 0, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase269 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![1, 0, (-1), 0, 0], ![1, 0, (-1), 1, 1]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase269 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase269 parameter.1 parameter.2

theorem rightInverseCase269_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase269 k) parameter *
      rightInverseCase269 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase269 : NormalizationDatum :=
  ⟨269, selectedCase269, rightInverseCase269,
    rightInverseCase269_ok⟩

def selectedCase270 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase270 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![1, 0, (-1), 1, 1], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase270 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase270 parameter.1 parameter.2

theorem rightInverseCase270_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase270 k) parameter *
      rightInverseCase270 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase270 : NormalizationDatum :=
  ⟨270, selectedCase270, rightInverseCase270,
    rightInverseCase270_ok⟩

def selectedCase271 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase271 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, (-1), 1, 0, (-1)]], ![![0, 0, 0, 0, 0], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase271 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase271 parameter.1 parameter.2

theorem rightInverseCase271_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase271 k) parameter *
      rightInverseCase271 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase271 : NormalizationDatum :=
  ⟨271, selectedCase271, rightInverseCase271,
    rightInverseCase271_ok⟩

def selectedCase272 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase272 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![1, 0, (-2), 0, (-1)], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase272 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase272 parameter.1 parameter.2

theorem rightInverseCase272_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase272 k) parameter *
      rightInverseCase272 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase272 : NormalizationDatum :=
  ⟨272, selectedCase272, rightInverseCase272,
    rightInverseCase272_ok⟩

def selectedCase273 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase273 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, (-1), 0, 0, (-1)]], ![![0, 0, 0, 0, 0], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase273 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase273 parameter.1 parameter.2

theorem rightInverseCase273_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase273 k) parameter *
      rightInverseCase273 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase273 : NormalizationDatum :=
  ⟨273, selectedCase273, rightInverseCase273,
    rightInverseCase273_ok⟩

def selectedCase274 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase274 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![0, 0, (-1), 0, (-1)], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase274 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase274 parameter.1 parameter.2

theorem rightInverseCase274_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase274 k) parameter *
      rightInverseCase274 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase274 : NormalizationDatum :=
  ⟨274, selectedCase274, rightInverseCase274,
    rightInverseCase274_ok⟩

def selectedCase275 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase275 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![1, 0, (-1), 0, 0], ![1, 0, (-1), 1, 1]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase275 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase275 parameter.1 parameter.2

theorem rightInverseCase275_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase275 k) parameter *
      rightInverseCase275 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase275 : NormalizationDatum :=
  ⟨275, selectedCase275, rightInverseCase275,
    rightInverseCase275_ok⟩

def selectedCase276 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase276 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![(-1), 0, 1, 0, (-1)], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase276 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase276 parameter.1 parameter.2

theorem rightInverseCase276_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase276 k) parameter *
      rightInverseCase276 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase276 : NormalizationDatum :=
  ⟨276, selectedCase276, rightInverseCase276,
    rightInverseCase276_ok⟩

def selectedCase277 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase277 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 1, (-1), 1, 1], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase277 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase277 parameter.1 parameter.2

theorem rightInverseCase277_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase277 k) parameter *
      rightInverseCase277 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase277 : NormalizationDatum :=
  ⟨277, selectedCase277, rightInverseCase277,
    rightInverseCase277_ok⟩

def selectedCase278 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase278 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![1, 0, (-2), 0, (-1)], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase278 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase278 parameter.1 parameter.2

theorem rightInverseCase278_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase278 k) parameter *
      rightInverseCase278 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase278 : NormalizationDatum :=
  ⟨278, selectedCase278, rightInverseCase278,
    rightInverseCase278_ok⟩

def selectedCase279 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase279 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, 0, (-1), 0, 0], ![1, (-1), 0, (-1), (-1)]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase279 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase279 parameter.1 parameter.2

theorem rightInverseCase279_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase279 k) parameter *
      rightInverseCase279 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase279 : NormalizationDatum :=
  ⟨279, selectedCase279, rightInverseCase279,
    rightInverseCase279_ok⟩

def selectedCase280 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase280 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, (-1), 0, (-1)], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase280 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase280 parameter.1 parameter.2

theorem rightInverseCase280_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase280 k) parameter *
      rightInverseCase280 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase280 : NormalizationDatum :=
  ⟨280, selectedCase280, rightInverseCase280,
    rightInverseCase280_ok⟩

def selectedCase281 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase281 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![(-1), 0, 1, 0, (-1)], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase281 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase281 parameter.1 parameter.2

theorem rightInverseCase281_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase281 k) parameter *
      rightInverseCase281 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase281 : NormalizationDatum :=
  ⟨281, selectedCase281, rightInverseCase281,
    rightInverseCase281_ok⟩

def selectedCase282 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase282 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![(-1), 0, 1, 0, (-1)], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase282 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase282 parameter.1 parameter.2

theorem rightInverseCase282_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase282 k) parameter *
      rightInverseCase282 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase282 : NormalizationDatum :=
  ⟨282, selectedCase282, rightInverseCase282,
    rightInverseCase282_ok⟩

def selectedCase283 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase283 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 1, (-1), 1, 1], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase283 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase283 parameter.1 parameter.2

theorem rightInverseCase283_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase283 k) parameter *
      rightInverseCase283 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase283 : NormalizationDatum :=
  ⟨283, selectedCase283, rightInverseCase283,
    rightInverseCase283_ok⟩

def selectedCase284 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase284 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![1, 0, (-2), 0, (-1)], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase284 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase284 parameter.1 parameter.2

theorem rightInverseCase284_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase284 k) parameter *
      rightInverseCase284 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase284 : NormalizationDatum :=
  ⟨284, selectedCase284, rightInverseCase284,
    rightInverseCase284_ok⟩

def selectedCase285 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase285 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, 0, (-1), 0, 0], ![1, (-1), 0, (-1), (-1)]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase285 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase285 parameter.1 parameter.2

theorem rightInverseCase285_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase285 k) parameter *
      rightInverseCase285 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase285 : NormalizationDatum :=
  ⟨285, selectedCase285, rightInverseCase285,
    rightInverseCase285_ok⟩

def selectedCase286 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase286 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, (-1), 0, (-1)], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase286 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase286 parameter.1 parameter.2

theorem rightInverseCase286_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase286 k) parameter *
      rightInverseCase286 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase286 : NormalizationDatum :=
  ⟨286, selectedCase286, rightInverseCase286,
    rightInverseCase286_ok⟩

def selectedCase287 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 0 2, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase287 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 0, 1, 0, 0], ![(-1), 0, 1, 0, (-1)], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, 0, (-1), 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase287 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase287 parameter.1 parameter.2

theorem rightInverseCase287_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase287 k) parameter *
      rightInverseCase287 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase287 : NormalizationDatum :=
  ⟨287, selectedCase287, rightInverseCase287,
    rightInverseCase287_ok⟩

def selectedCase300 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 1 0, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase300 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![1, (-1), 0, 1, 1], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase300 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase300 parameter.1 parameter.2

theorem rightInverseCase300_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase300 k) parameter *
      rightInverseCase300 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase300 : NormalizationDatum :=
  ⟨300, selectedCase300, rightInverseCase300,
    rightInverseCase300_ok⟩

def selectedCase301 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 1 0, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase301 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, (-1)]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase301 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase301 parameter.1 parameter.2

theorem rightInverseCase301_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase301 k) parameter *
      rightInverseCase301 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase301 : NormalizationDatum :=
  ⟨301, selectedCase301, rightInverseCase301,
    rightInverseCase301_ok⟩

def selectedCase302 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 1 0, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase302 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![1, (-2), (-1), 1, (-1)], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase302 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase302 parameter.1 parameter.2

theorem rightInverseCase302_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase302 k) parameter *
      rightInverseCase302 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase302 : NormalizationDatum :=
  ⟨302, selectedCase302, rightInverseCase302,
    rightInverseCase302_ok⟩

def selectedCase303 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 1 0, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase303 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0], ![1, (-1), 0, 0, (-1)]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase303 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase303 parameter.1 parameter.2

theorem rightInverseCase303_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase303 k) parameter *
      rightInverseCase303 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase303 : NormalizationDatum :=
  ⟨303, selectedCase303, rightInverseCase303,
    rightInverseCase303_ok⟩

def selectedCase304 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 1 0, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase304 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![0, (-1), (-1), 1, (-1)], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase304 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase304 parameter.1 parameter.2

theorem rightInverseCase304_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase304 k) parameter *
      rightInverseCase304 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase304 : NormalizationDatum :=
  ⟨304, selectedCase304, rightInverseCase304,
    rightInverseCase304_ok⟩

def selectedCase305 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 1 0, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase305 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![1, (-1), 0, 1, 1]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase305 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase305 parameter.1 parameter.2

theorem rightInverseCase305_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase305 k) parameter *
      rightInverseCase305 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase305 : NormalizationDatum :=
  ⟨305, selectedCase305, rightInverseCase305,
    rightInverseCase305_ok⟩

def selectedCase306 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase306 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![1, (-1), 0, 1, 1], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase306 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase306 parameter.1 parameter.2

theorem rightInverseCase306_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase306 k) parameter *
      rightInverseCase306 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase306 : NormalizationDatum :=
  ⟨306, selectedCase306, rightInverseCase306,
    rightInverseCase306_ok⟩

def selectedCase307 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase307 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, (-1)]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase307 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase307 parameter.1 parameter.2

theorem rightInverseCase307_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase307 k) parameter *
      rightInverseCase307 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase307 : NormalizationDatum :=
  ⟨307, selectedCase307, rightInverseCase307,
    rightInverseCase307_ok⟩

def selectedCase308 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase308 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![1, (-2), (-1), 1, (-1)], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase308 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase308 parameter.1 parameter.2

theorem rightInverseCase308_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase308 k) parameter *
      rightInverseCase308 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase308 : NormalizationDatum :=
  ⟨308, selectedCase308, rightInverseCase308,
    rightInverseCase308_ok⟩

def selectedCase309 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase309 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0], ![1, (-1), 0, 0, (-1)]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase309 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase309 parameter.1 parameter.2

theorem rightInverseCase309_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase309 k) parameter *
      rightInverseCase309 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase309 : NormalizationDatum :=
  ⟨309, selectedCase309, rightInverseCase309,
    rightInverseCase309_ok⟩

def selectedCase310 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase310 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![0, (-1), (-1), 1, (-1)], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase310 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase310 parameter.1 parameter.2

theorem rightInverseCase310_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase310 k) parameter *
      rightInverseCase310 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase310 : NormalizationDatum :=
  ⟨310, selectedCase310, rightInverseCase310,
    rightInverseCase310_ok⟩

def selectedCase311 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase311 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![1, (-1), 0, 1, 1]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase311 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase311 parameter.1 parameter.2

theorem rightInverseCase311_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase311 k) parameter *
      rightInverseCase311 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase311 : NormalizationDatum :=
  ⟨311, selectedCase311, rightInverseCase311,
    rightInverseCase311_ok⟩

def selectedCase312 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase312 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![1, (-1), 1, 0, 1], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase312 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase312 parameter.1 parameter.2

theorem rightInverseCase312_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase312 k) parameter *
      rightInverseCase312 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase312 : NormalizationDatum :=
  ⟨312, selectedCase312, rightInverseCase312,
    rightInverseCase312_ok⟩

def selectedCase313 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase313 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 1, 1], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase313 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase313 parameter.1 parameter.2

theorem rightInverseCase313_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase313 k) parameter *
      rightInverseCase313 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase313 : NormalizationDatum :=
  ⟨313, selectedCase313, rightInverseCase313,
    rightInverseCase313_ok⟩

def selectedCase314 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase314 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![1, (-2), 0, 0, (-1)], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase314 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase314 parameter.1 parameter.2

theorem rightInverseCase314_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase314 k) parameter *
      rightInverseCase314 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase314 : NormalizationDatum :=
  ⟨314, selectedCase314, rightInverseCase314,
    rightInverseCase314_ok⟩

def selectedCase315 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase315 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![1, (-1), 0, (-1), (-1)]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase315 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase315 parameter.1 parameter.2

theorem rightInverseCase315_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase315 k) parameter *
      rightInverseCase315 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase315 : NormalizationDatum :=
  ⟨315, selectedCase315, rightInverseCase315,
    rightInverseCase315_ok⟩

def selectedCase316 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase316 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, (-1), 0, 0, (-1)], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase316 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase316 parameter.1 parameter.2

theorem rightInverseCase316_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase316 k) parameter *
      rightInverseCase316 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase316 : NormalizationDatum :=
  ⟨316, selectedCase316, rightInverseCase316,
    rightInverseCase316_ok⟩

def selectedCase317 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase317 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![1, (-1), 1, 0, 1]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase317 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase317 parameter.1 parameter.2

theorem rightInverseCase317_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase317 k) parameter *
      rightInverseCase317 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase317 : NormalizationDatum :=
  ⟨317, selectedCase317, rightInverseCase317,
    rightInverseCase317_ok⟩

def selectedCase318 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase318 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![1, (-1), 1, 0, 1], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase318 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase318 parameter.1 parameter.2

theorem rightInverseCase318_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase318 k) parameter *
      rightInverseCase318 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase318 : NormalizationDatum :=
  ⟨318, selectedCase318, rightInverseCase318,
    rightInverseCase318_ok⟩

def selectedCase319 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase319 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 1, 1], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase319 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase319 parameter.1 parameter.2

theorem rightInverseCase319_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase319 k) parameter *
      rightInverseCase319 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase319 : NormalizationDatum :=
  ⟨319, selectedCase319, rightInverseCase319,
    rightInverseCase319_ok⟩

def selectedCase320 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase320 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![1, (-2), 0, 0, (-1)], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase320 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase320 parameter.1 parameter.2

theorem rightInverseCase320_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase320 k) parameter *
      rightInverseCase320 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase320 : NormalizationDatum :=
  ⟨320, selectedCase320, rightInverseCase320,
    rightInverseCase320_ok⟩

def selectedCase321 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase321 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![1, (-1), 0, (-1), (-1)]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase321 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase321 parameter.1 parameter.2

theorem rightInverseCase321_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase321 k) parameter *
      rightInverseCase321 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase321 : NormalizationDatum :=
  ⟨321, selectedCase321, rightInverseCase321,
    rightInverseCase321_ok⟩

def selectedCase322 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase322 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, (-1), 0, 0, (-1)], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase322 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase322 parameter.1 parameter.2

theorem rightInverseCase322_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase322 k) parameter *
      rightInverseCase322 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase322 : NormalizationDatum :=
  ⟨322, selectedCase322, rightInverseCase322,
    rightInverseCase322_ok⟩

def selectedCase323 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase323 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![1, (-1), 1, 0, 1]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase323 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase323 parameter.1 parameter.2

theorem rightInverseCase323_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase323 k) parameter *
      rightInverseCase323 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase323 : NormalizationDatum :=
  ⟨323, selectedCase323, rightInverseCase323,
    rightInverseCase323_ok⟩

def selectedCase342 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase342 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![1, (-1), 0, 1, 1], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase342 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase342 parameter.1 parameter.2

theorem rightInverseCase342_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase342 k) parameter *
      rightInverseCase342 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase342 : NormalizationDatum :=
  ⟨342, selectedCase342, rightInverseCase342,
    rightInverseCase342_ok⟩

def selectedCase343 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase343 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, (-1), 1, (-1)]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase343 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase343 parameter.1 parameter.2

theorem rightInverseCase343_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase343 k) parameter *
      rightInverseCase343 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase343 : NormalizationDatum :=
  ⟨343, selectedCase343, rightInverseCase343,
    rightInverseCase343_ok⟩

def selectedCase344 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase344 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![1, (-2), 0, 0, (-1)], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase344 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase344 parameter.1 parameter.2

theorem rightInverseCase344_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase344 k) parameter *
      rightInverseCase344 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase344 : NormalizationDatum :=
  ⟨344, selectedCase344, rightInverseCase344,
    rightInverseCase344_ok⟩

def selectedCase345 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase345 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0], ![1, (-1), (-1), 1, (-1)]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase345 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase345 parameter.1 parameter.2

theorem rightInverseCase345_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase345 k) parameter *
      rightInverseCase345 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase345 : NormalizationDatum :=
  ⟨345, selectedCase345, rightInverseCase345,
    rightInverseCase345_ok⟩

def selectedCase346 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase346 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![0, (-1), 0, 0, (-1)], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase346 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase346 parameter.1 parameter.2

theorem rightInverseCase346_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase346 k) parameter *
      rightInverseCase346 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase346 : NormalizationDatum :=
  ⟨346, selectedCase346, rightInverseCase346,
    rightInverseCase346_ok⟩

def selectedCase347 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase347 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![1, (-1), 0, 1, 1]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase347 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase347 parameter.1 parameter.2

theorem rightInverseCase347_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase347 k) parameter *
      rightInverseCase347 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase347 : NormalizationDatum :=
  ⟨347, selectedCase347, rightInverseCase347,
    rightInverseCase347_ok⟩

def selectedCase348 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase348 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![1, (-1), 1, 0, 1], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase348 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase348 parameter.1 parameter.2

theorem rightInverseCase348_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase348 k) parameter *
      rightInverseCase348 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase348 : NormalizationDatum :=
  ⟨348, selectedCase348, rightInverseCase348,
    rightInverseCase348_ok⟩

def selectedCase349 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase349 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 1, 1], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase349 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase349 parameter.1 parameter.2

theorem rightInverseCase349_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase349 k) parameter *
      rightInverseCase349 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase349 : NormalizationDatum :=
  ⟨349, selectedCase349, rightInverseCase349,
    rightInverseCase349_ok⟩

def selectedCase350 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase350 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![1, (-2), 0, 0, (-1)], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase350 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase350 parameter.1 parameter.2

theorem rightInverseCase350_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase350 k) parameter *
      rightInverseCase350 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase350 : NormalizationDatum :=
  ⟨350, selectedCase350, rightInverseCase350,
    rightInverseCase350_ok⟩

def selectedCase351 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase351 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![1, (-1), 0, (-1), (-1)]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase351 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase351 parameter.1 parameter.2

theorem rightInverseCase351_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase351 k) parameter *
      rightInverseCase351 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase351 : NormalizationDatum :=
  ⟨351, selectedCase351, rightInverseCase351,
    rightInverseCase351_ok⟩

def selectedCase352 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase352 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, (-1), 0, 0, (-1)], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase352 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase352 parameter.1 parameter.2

theorem rightInverseCase352_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase352 k) parameter *
      rightInverseCase352 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase352 : NormalizationDatum :=
  ⟨352, selectedCase352, rightInverseCase352,
    rightInverseCase352_ok⟩

def selectedCase353 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase353 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![1, (-1), 1, 0, 1]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase353 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase353 parameter.1 parameter.2

theorem rightInverseCase353_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase353 k) parameter *
      rightInverseCase353 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase353 : NormalizationDatum :=
  ⟨353, selectedCase353, rightInverseCase353,
    rightInverseCase353_ok⟩

def selectedCase354 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase354 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![1, (-1), 1, 0, 1], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase354 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase354 parameter.1 parameter.2

theorem rightInverseCase354_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase354 k) parameter *
      rightInverseCase354 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase354 : NormalizationDatum :=
  ⟨354, selectedCase354, rightInverseCase354,
    rightInverseCase354_ok⟩

def selectedCase355 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase355 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 1, 1], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase355 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase355 parameter.1 parameter.2

theorem rightInverseCase355_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase355 k) parameter *
      rightInverseCase355 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase355 : NormalizationDatum :=
  ⟨355, selectedCase355, rightInverseCase355,
    rightInverseCase355_ok⟩

def selectedCase356 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase356 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![1, (-2), 0, 0, (-1)], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase356 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase356 parameter.1 parameter.2

theorem rightInverseCase356_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase356 k) parameter *
      rightInverseCase356 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase356 : NormalizationDatum :=
  ⟨356, selectedCase356, rightInverseCase356,
    rightInverseCase356_ok⟩

def selectedCase357 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase357 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![1, (-1), 0, (-1), (-1)]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase357 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase357 parameter.1 parameter.2

theorem rightInverseCase357_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase357 k) parameter *
      rightInverseCase357 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase357 : NormalizationDatum :=
  ⟨357, selectedCase357, rightInverseCase357,
    rightInverseCase357_ok⟩

def selectedCase358 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase358 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, (-1), 0, 0, (-1)], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase358 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase358 parameter.1 parameter.2

theorem rightInverseCase358_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase358 k) parameter *
      rightInverseCase358 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase358 : NormalizationDatum :=
  ⟨358, selectedCase358, rightInverseCase358,
    rightInverseCase358_ok⟩

def selectedCase359 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase359 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![1, (-1), 1, 0, 1]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase359 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase359 parameter.1 parameter.2

theorem rightInverseCase359_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase359 k) parameter *
      rightInverseCase359 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase359 : NormalizationDatum :=
  ⟨359, selectedCase359, rightInverseCase359,
    rightInverseCase359_ok⟩

def selectedCase384 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase384 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![(-1), 1, 0, 0, (-1)], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase384 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase384 parameter.1 parameter.2

theorem rightInverseCase384_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase384 k) parameter *
      rightInverseCase384 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase384 : NormalizationDatum :=
  ⟨384, selectedCase384, rightInverseCase384,
    rightInverseCase384_ok⟩

def selectedCase385 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase385 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 1, 1], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase385 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase385 parameter.1 parameter.2

theorem rightInverseCase385_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase385 k) parameter *
      rightInverseCase385 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase385 : NormalizationDatum :=
  ⟨385, selectedCase385, rightInverseCase385,
    rightInverseCase385_ok⟩

def selectedCase386 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase386 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![1, (-2), (-1), 1, (-1)], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase386 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase386 parameter.1 parameter.2

theorem rightInverseCase386_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase386 k) parameter *
      rightInverseCase386 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase386 : NormalizationDatum :=
  ⟨386, selectedCase386, rightInverseCase386,
    rightInverseCase386_ok⟩

def selectedCase387 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase387 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![1, (-1), 0, (-1), (-1)]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase387 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase387 parameter.1 parameter.2

theorem rightInverseCase387_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase387 k) parameter *
      rightInverseCase387 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase387 : NormalizationDatum :=
  ⟨387, selectedCase387, rightInverseCase387,
    rightInverseCase387_ok⟩

def selectedCase388 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase388 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, (-1), (-1), 1, (-1)], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase388 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase388 parameter.1 parameter.2

theorem rightInverseCase388_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase388 k) parameter *
      rightInverseCase388 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase388 : NormalizationDatum :=
  ⟨388, selectedCase388, rightInverseCase388,
    rightInverseCase388_ok⟩

def selectedCase389 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase389 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![(-1), 1, 0, 0, (-1)], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase389 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase389 parameter.1 parameter.2

theorem rightInverseCase389_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase389 k) parameter *
      rightInverseCase389 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase389 : NormalizationDatum :=
  ⟨389, selectedCase389, rightInverseCase389,
    rightInverseCase389_ok⟩

def selectedCase390 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase390 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![(-1), 1, 0, 0, (-1)], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase390 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase390 parameter.1 parameter.2

theorem rightInverseCase390_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase390 k) parameter *
      rightInverseCase390 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase390 : NormalizationDatum :=
  ⟨390, selectedCase390, rightInverseCase390,
    rightInverseCase390_ok⟩

def selectedCase391 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase391 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 1, 1], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase391 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase391 parameter.1 parameter.2

theorem rightInverseCase391_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase391 k) parameter *
      rightInverseCase391 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase391 : NormalizationDatum :=
  ⟨391, selectedCase391, rightInverseCase391,
    rightInverseCase391_ok⟩

def selectedCase392 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase392 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![1, (-2), (-1), 1, (-1)], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase392 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase392 parameter.1 parameter.2

theorem rightInverseCase392_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase392 k) parameter *
      rightInverseCase392 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase392 : NormalizationDatum :=
  ⟨392, selectedCase392, rightInverseCase392,
    rightInverseCase392_ok⟩

def selectedCase393 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase393 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![1, (-1), 0, (-1), (-1)]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase393 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase393 parameter.1 parameter.2

theorem rightInverseCase393_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase393 k) parameter *
      rightInverseCase393 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase393 : NormalizationDatum :=
  ⟨393, selectedCase393, rightInverseCase393,
    rightInverseCase393_ok⟩

def selectedCase394 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase394 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, (-1), (-1), 1, (-1)], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase394 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase394 parameter.1 parameter.2

theorem rightInverseCase394_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase394 k) parameter *
      rightInverseCase394 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase394 : NormalizationDatum :=
  ⟨394, selectedCase394, rightInverseCase394,
    rightInverseCase394_ok⟩

def selectedCase395 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase395 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![(-1), 1, 0, 0, (-1)], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase395 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase395 parameter.1 parameter.2

theorem rightInverseCase395_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase395 k) parameter *
      rightInverseCase395 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase395 : NormalizationDatum :=
  ⟨395, selectedCase395, rightInverseCase395,
    rightInverseCase395_ok⟩

def selectedCase426 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 2 1, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase426 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![(-1), 1, (-1), 1, (-1)], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase426 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase426 parameter.1 parameter.2

theorem rightInverseCase426_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase426 k) parameter *
      rightInverseCase426 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase426 : NormalizationDatum :=
  ⟨426, selectedCase426, rightInverseCase426,
    rightInverseCase426_ok⟩

def selectedCase427 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 2 1, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase427 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 1, 1], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase427 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase427 parameter.1 parameter.2

theorem rightInverseCase427_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase427 k) parameter *
      rightInverseCase427 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase427 : NormalizationDatum :=
  ⟨427, selectedCase427, rightInverseCase427,
    rightInverseCase427_ok⟩

def selectedCase428 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 2 1, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase428 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![1, (-2), 0, 0, (-1)], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase428 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase428 parameter.1 parameter.2

theorem rightInverseCase428_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase428 k) parameter *
      rightInverseCase428 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase428 : NormalizationDatum :=
  ⟨428, selectedCase428, rightInverseCase428,
    rightInverseCase428_ok⟩

def selectedCase429 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 2 1, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase429 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![1, (-1), 0, (-1), (-1)]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase429 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase429 parameter.1 parameter.2

theorem rightInverseCase429_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase429 k) parameter *
      rightInverseCase429 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase429 : NormalizationDatum :=
  ⟨429, selectedCase429, rightInverseCase429,
    rightInverseCase429_ok⟩

def selectedCase430 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 2 1, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase430 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, (-1), 0, 0, (-1)], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase430 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase430 parameter.1 parameter.2

theorem rightInverseCase430_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase430 k) parameter *
      rightInverseCase430 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase430 : NormalizationDatum :=
  ⟨430, selectedCase430, rightInverseCase430,
    rightInverseCase430_ok⟩

def selectedCase431 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 0 2, MonochromaticQuantumGraph.mkEdge 0 3 2 1, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase431 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![0, 1, 0, 0, 0], ![(-1), 1, (-1), 1, (-1)], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![1, (-1), 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase431 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase431 parameter.1 parameter.2

theorem rightInverseCase431_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase431 k) parameter *
      rightInverseCase431 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase431 : NormalizationDatum :=
  ⟨431, selectedCase431, rightInverseCase431,
    rightInverseCase431_ok⟩

def selectedCase516 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 1 0, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase516 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 1, 1], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase516 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase516 parameter.1 parameter.2

theorem rightInverseCase516_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase516 k) parameter *
      rightInverseCase516 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase516 : NormalizationDatum :=
  ⟨516, selectedCase516, rightInverseCase516,
    rightInverseCase516_ok⟩

def selectedCase517 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 1 0, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase517 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, (-1)]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase517 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase517 parameter.1 parameter.2

theorem rightInverseCase517_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase517 k) parameter *
      rightInverseCase517 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase517 : NormalizationDatum :=
  ⟨517, selectedCase517, rightInverseCase517,
    rightInverseCase517_ok⟩

def selectedCase518 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 1 0, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase518 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![(-1), (-1), (-1), 2, (-1)], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase518 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase518 parameter.1 parameter.2

theorem rightInverseCase518_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase518 k) parameter *
      rightInverseCase518 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase518 : NormalizationDatum :=
  ⟨518, selectedCase518, rightInverseCase518,
    rightInverseCase518_ok⟩

def selectedCase519 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 1 0, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase519 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, (-1)]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase519 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase519 parameter.1 parameter.2

theorem rightInverseCase519_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase519 k) parameter *
      rightInverseCase519 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase519 : NormalizationDatum :=
  ⟨519, selectedCase519, rightInverseCase519,
    rightInverseCase519_ok⟩

def selectedCase520 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 1 0, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase520 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![(-1), (-1), (-1), 2, (-1)], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase520 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase520 parameter.1 parameter.2

theorem rightInverseCase520_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase520 k) parameter *
      rightInverseCase520 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase520 : NormalizationDatum :=
  ⟨520, selectedCase520, rightInverseCase520,
    rightInverseCase520_ok⟩

def selectedCase521 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 1 0, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase521 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 1, 1], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, (-1), (-1)], ![0, 0, 0, 0, 0]], ![![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase521 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase521 parameter.1 parameter.2

theorem rightInverseCase521_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase521 k) parameter *
      rightInverseCase521 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase521 : NormalizationDatum :=
  ⟨521, selectedCase521, rightInverseCase521,
    rightInverseCase521_ok⟩

def selectedCase522 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase522 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 1, 1], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase522 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase522 parameter.1 parameter.2

theorem rightInverseCase522_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase522 k) parameter *
      rightInverseCase522 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase522 : NormalizationDatum :=
  ⟨522, selectedCase522, rightInverseCase522,
    rightInverseCase522_ok⟩

def selectedCase523 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase523 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, (-1)]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase523 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase523 parameter.1 parameter.2

theorem rightInverseCase523_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase523 k) parameter *
      rightInverseCase523 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase523 : NormalizationDatum :=
  ⟨523, selectedCase523, rightInverseCase523,
    rightInverseCase523_ok⟩

def selectedCase524 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase524 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![(-1), (-1), (-1), 2, (-1)], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase524 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase524 parameter.1 parameter.2

theorem rightInverseCase524_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase524 k) parameter *
      rightInverseCase524 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase524 : NormalizationDatum :=
  ⟨524, selectedCase524, rightInverseCase524,
    rightInverseCase524_ok⟩

def selectedCase525 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase525 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, (-1)]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase525 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase525 parameter.1 parameter.2

theorem rightInverseCase525_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase525 k) parameter *
      rightInverseCase525 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase525 : NormalizationDatum :=
  ⟨525, selectedCase525, rightInverseCase525,
    rightInverseCase525_ok⟩

def selectedCase526 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase526 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![(-1), (-1), (-1), 2, (-1)], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase526 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase526 parameter.1 parameter.2

theorem rightInverseCase526_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase526 k) parameter *
      rightInverseCase526 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase526 : NormalizationDatum :=
  ⟨526, selectedCase526, rightInverseCase526,
    rightInverseCase526_ok⟩

def selectedCase527 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase527 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 1, 1], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, (-1), (-1)], ![0, 0, 0, 0, 0]], ![![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase527 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase527 parameter.1 parameter.2

theorem rightInverseCase527_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase527 k) parameter *
      rightInverseCase527 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase527 : NormalizationDatum :=
  ⟨527, selectedCase527, rightInverseCase527,
    rightInverseCase527_ok⟩

def selectedCase528 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase528 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 1, 0, 1], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase528 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase528 parameter.1 parameter.2

theorem rightInverseCase528_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase528 k) parameter *
      rightInverseCase528 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase528 : NormalizationDatum :=
  ⟨528, selectedCase528, rightInverseCase528,
    rightInverseCase528_ok⟩

def selectedCase529 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase529 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 1, 1], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase529 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase529 parameter.1 parameter.2

theorem rightInverseCase529_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase529 k) parameter *
      rightInverseCase529 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase529 : NormalizationDatum :=
  ⟨529, selectedCase529, rightInverseCase529,
    rightInverseCase529_ok⟩

def selectedCase530 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase530 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![(-1), (-1), 1, 0, (-1)], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase530 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase530 parameter.1 parameter.2

theorem rightInverseCase530_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase530 k) parameter *
      rightInverseCase530 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase530 : NormalizationDatum :=
  ⟨530, selectedCase530, rightInverseCase530,
    rightInverseCase530_ok⟩

def selectedCase531 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase531 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, (-1), (-1)], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 1, 1], ![0, 0, 0, 0, 0]], ![![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase531 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase531 parameter.1 parameter.2

theorem rightInverseCase531_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase531 k) parameter *
      rightInverseCase531 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase531 : NormalizationDatum :=
  ⟨531, selectedCase531, rightInverseCase531,
    rightInverseCase531_ok⟩

def selectedCase532 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase532 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![(-1), (-1), 1, 0, (-1)], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase532 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase532 parameter.1 parameter.2

theorem rightInverseCase532_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase532 k) parameter *
      rightInverseCase532 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase532 : NormalizationDatum :=
  ⟨532, selectedCase532, rightInverseCase532,
    rightInverseCase532_ok⟩

def selectedCase533 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase533 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 1, 0, 1], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![0, 0, (-1), 0, (-1)], ![0, 0, 0, 0, 0]], ![![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase533 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase533 parameter.1 parameter.2

theorem rightInverseCase533_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase533 k) parameter *
      rightInverseCase533 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase533 : NormalizationDatum :=
  ⟨533, selectedCase533, rightInverseCase533,
    rightInverseCase533_ok⟩

def selectedCase534 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase534 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 1, 0, 1], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase534 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase534 parameter.1 parameter.2

theorem rightInverseCase534_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase534 k) parameter *
      rightInverseCase534 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase534 : NormalizationDatum :=
  ⟨534, selectedCase534, rightInverseCase534,
    rightInverseCase534_ok⟩

def selectedCase535 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase535 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 1, 1], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase535 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase535 parameter.1 parameter.2

theorem rightInverseCase535_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase535 k) parameter *
      rightInverseCase535 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase535 : NormalizationDatum :=
  ⟨535, selectedCase535, rightInverseCase535,
    rightInverseCase535_ok⟩

def selectedCase536 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase536 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![(-1), (-1), 1, 0, (-1)], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase536 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase536 parameter.1 parameter.2

theorem rightInverseCase536_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase536 k) parameter *
      rightInverseCase536 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase536 : NormalizationDatum :=
  ⟨536, selectedCase536, rightInverseCase536,
    rightInverseCase536_ok⟩

def selectedCase537 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase537 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, (-1), (-1)], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 1, 1], ![0, 0, 0, 0, 0]], ![![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase537 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase537 parameter.1 parameter.2

theorem rightInverseCase537_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase537 k) parameter *
      rightInverseCase537 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase537 : NormalizationDatum :=
  ⟨537, selectedCase537, rightInverseCase537,
    rightInverseCase537_ok⟩

def selectedCase538 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase538 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![(-1), (-1), 1, 0, (-1)], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase538 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase538 parameter.1 parameter.2

theorem rightInverseCase538_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase538 k) parameter *
      rightInverseCase538 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase538 : NormalizationDatum :=
  ⟨538, selectedCase538, rightInverseCase538,
    rightInverseCase538_ok⟩

def selectedCase539 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 1 0, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase539 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 1, 0, 1], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![0, 0, (-1), 0, (-1)], ![0, 0, 0, 0, 0]], ![![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase539 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase539 parameter.1 parameter.2

theorem rightInverseCase539_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase539 k) parameter *
      rightInverseCase539 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase539 : NormalizationDatum :=
  ⟨539, selectedCase539, rightInverseCase539,
    rightInverseCase539_ok⟩

def selectedCase558 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase558 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 1, 1], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase558 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase558 parameter.1 parameter.2

theorem rightInverseCase558_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase558 k) parameter *
      rightInverseCase558 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase558 : NormalizationDatum :=
  ⟨558, selectedCase558, rightInverseCase558,
    rightInverseCase558_ok⟩

def selectedCase559 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase559 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, (-1), 1, (-1)]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase559 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase559 parameter.1 parameter.2

theorem rightInverseCase559_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase559 k) parameter *
      rightInverseCase559 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase559 : NormalizationDatum :=
  ⟨559, selectedCase559, rightInverseCase559,
    rightInverseCase559_ok⟩

def selectedCase560 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase560 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![(-1), (-1), 0, 1, (-1)], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase560 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase560 parameter.1 parameter.2

theorem rightInverseCase560_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase560 k) parameter *
      rightInverseCase560 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase560 : NormalizationDatum :=
  ⟨560, selectedCase560, rightInverseCase560,
    rightInverseCase560_ok⟩

def selectedCase561 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase561 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, (-1), 1, (-1)]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase561 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase561 parameter.1 parameter.2

theorem rightInverseCase561_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase561 k) parameter *
      rightInverseCase561 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase561 : NormalizationDatum :=
  ⟨561, selectedCase561, rightInverseCase561,
    rightInverseCase561_ok⟩

def selectedCase562 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase562 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![(-1), (-1), 0, 1, (-1)], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase562 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase562 parameter.1 parameter.2

theorem rightInverseCase562_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase562 k) parameter *
      rightInverseCase562 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase562 : NormalizationDatum :=
  ⟨562, selectedCase562, rightInverseCase562,
    rightInverseCase562_ok⟩

def selectedCase563 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase563 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 1, 1], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, (-1), (-1)], ![0, 0, 0, 0, 0]], ![![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase563 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase563 parameter.1 parameter.2

theorem rightInverseCase563_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase563 k) parameter *
      rightInverseCase563 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase563 : NormalizationDatum :=
  ⟨563, selectedCase563, rightInverseCase563,
    rightInverseCase563_ok⟩

def selectedCase564 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase564 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 1, 0, 1], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase564 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase564 parameter.1 parameter.2

theorem rightInverseCase564_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase564 k) parameter *
      rightInverseCase564 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase564 : NormalizationDatum :=
  ⟨564, selectedCase564, rightInverseCase564,
    rightInverseCase564_ok⟩

def selectedCase565 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase565 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 1, 1], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase565 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase565 parameter.1 parameter.2

theorem rightInverseCase565_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase565 k) parameter *
      rightInverseCase565 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase565 : NormalizationDatum :=
  ⟨565, selectedCase565, rightInverseCase565,
    rightInverseCase565_ok⟩

def selectedCase566 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase566 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![(-1), (-1), 1, 0, (-1)], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase566 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase566 parameter.1 parameter.2

theorem rightInverseCase566_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase566 k) parameter *
      rightInverseCase566 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase566 : NormalizationDatum :=
  ⟨566, selectedCase566, rightInverseCase566,
    rightInverseCase566_ok⟩

def selectedCase567 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase567 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, (-1), (-1)], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 1, 1], ![0, 0, 0, 0, 0]], ![![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase567 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase567 parameter.1 parameter.2

theorem rightInverseCase567_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase567 k) parameter *
      rightInverseCase567 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase567 : NormalizationDatum :=
  ⟨567, selectedCase567, rightInverseCase567,
    rightInverseCase567_ok⟩

def selectedCase568 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase568 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![(-1), (-1), 1, 0, (-1)], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase568 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase568 parameter.1 parameter.2

theorem rightInverseCase568_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase568 k) parameter *
      rightInverseCase568 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase568 : NormalizationDatum :=
  ⟨568, selectedCase568, rightInverseCase568,
    rightInverseCase568_ok⟩

def selectedCase569 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase569 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 1, 0, 1], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![0, 0, (-1), 0, (-1)], ![0, 0, 0, 0, 0]], ![![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase569 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase569 parameter.1 parameter.2

theorem rightInverseCase569_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase569 k) parameter *
      rightInverseCase569 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase569 : NormalizationDatum :=
  ⟨569, selectedCase569, rightInverseCase569,
    rightInverseCase569_ok⟩

def selectedCase570 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase570 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 1, 0, 1], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase570 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase570 parameter.1 parameter.2

theorem rightInverseCase570_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase570 k) parameter *
      rightInverseCase570 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase570 : NormalizationDatum :=
  ⟨570, selectedCase570, rightInverseCase570,
    rightInverseCase570_ok⟩

def selectedCase571 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase571 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 1, 1], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase571 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase571 parameter.1 parameter.2

theorem rightInverseCase571_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase571 k) parameter *
      rightInverseCase571 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase571 : NormalizationDatum :=
  ⟨571, selectedCase571, rightInverseCase571,
    rightInverseCase571_ok⟩

def selectedCase572 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase572 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![(-1), (-1), 1, 0, (-1)], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase572 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase572 parameter.1 parameter.2

theorem rightInverseCase572_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase572 k) parameter *
      rightInverseCase572 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase572 : NormalizationDatum :=
  ⟨572, selectedCase572, rightInverseCase572,
    rightInverseCase572_ok⟩

def selectedCase573 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase573 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, (-1), (-1)], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 1, 1], ![0, 0, 0, 0, 0]], ![![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase573 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase573 parameter.1 parameter.2

theorem rightInverseCase573_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase573 k) parameter *
      rightInverseCase573 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase573 : NormalizationDatum :=
  ⟨573, selectedCase573, rightInverseCase573,
    rightInverseCase573_ok⟩

def selectedCase574 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase574 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![(-1), (-1), 1, 0, (-1)], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase574 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase574 parameter.1 parameter.2

theorem rightInverseCase574_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase574 k) parameter *
      rightInverseCase574 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase574 : NormalizationDatum :=
  ⟨574, selectedCase574, rightInverseCase574,
    rightInverseCase574_ok⟩

def selectedCase575 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase575 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 1, 0, 1], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![0, 0, (-1), 0, (-1)], ![0, 0, 0, 0, 0]], ![![0, 1, (-1), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase575 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase575 parameter.1 parameter.2

theorem rightInverseCase575_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase575 k) parameter *
      rightInverseCase575 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase575 : NormalizationDatum :=
  ⟨575, selectedCase575, rightInverseCase575,
    rightInverseCase575_ok⟩

def selectedCase600 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase600 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 1, 0, 0, 1], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase600 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase600 parameter.1 parameter.2

theorem rightInverseCase600_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase600 k) parameter *
      rightInverseCase600 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase600 : NormalizationDatum :=
  ⟨600, selectedCase600, rightInverseCase600,
    rightInverseCase600_ok⟩

def selectedCase601 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase601 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 1, 1], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase601 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase601 parameter.1 parameter.2

theorem rightInverseCase601_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase601 k) parameter *
      rightInverseCase601 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase601 : NormalizationDatum :=
  ⟨601, selectedCase601, rightInverseCase601,
    rightInverseCase601_ok⟩

def selectedCase602 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase602 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![(-1), 0, (-1), 1, (-1)], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase602 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase602 parameter.1 parameter.2

theorem rightInverseCase602_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase602 k) parameter *
      rightInverseCase602 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase602 : NormalizationDatum :=
  ⟨602, selectedCase602, rightInverseCase602,
    rightInverseCase602_ok⟩

def selectedCase603 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase603 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, (-1), (-1)], ![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 1, 1], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase603 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase603 parameter.1 parameter.2

theorem rightInverseCase603_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase603 k) parameter *
      rightInverseCase603 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase603 : NormalizationDatum :=
  ⟨603, selectedCase603, rightInverseCase603,
    rightInverseCase603_ok⟩

def selectedCase604 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase604 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![(-1), 0, (-1), 1, (-1)], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase604 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase604 parameter.1 parameter.2

theorem rightInverseCase604_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase604 k) parameter *
      rightInverseCase604 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase604 : NormalizationDatum :=
  ⟨604, selectedCase604, rightInverseCase604,
    rightInverseCase604_ok⟩

def selectedCase605 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase605 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 1, 0, 0, 1], ![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![0, (-1), 0, 0, (-1)], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase605 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase605 parameter.1 parameter.2

theorem rightInverseCase605_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase605 k) parameter *
      rightInverseCase605 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase605 : NormalizationDatum :=
  ⟨605, selectedCase605, rightInverseCase605,
    rightInverseCase605_ok⟩

def selectedCase606 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase606 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 1, 0, 0, 1], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase606 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase606 parameter.1 parameter.2

theorem rightInverseCase606_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase606 k) parameter *
      rightInverseCase606 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase606 : NormalizationDatum :=
  ⟨606, selectedCase606, rightInverseCase606,
    rightInverseCase606_ok⟩

def selectedCase607 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase607 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 1, 1], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase607 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase607 parameter.1 parameter.2

theorem rightInverseCase607_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase607 k) parameter *
      rightInverseCase607 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase607 : NormalizationDatum :=
  ⟨607, selectedCase607, rightInverseCase607,
    rightInverseCase607_ok⟩

def selectedCase608 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase608 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![(-1), 0, (-1), 1, (-1)], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase608 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase608 parameter.1 parameter.2

theorem rightInverseCase608_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase608 k) parameter *
      rightInverseCase608 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase608 : NormalizationDatum :=
  ⟨608, selectedCase608, rightInverseCase608,
    rightInverseCase608_ok⟩

def selectedCase609 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase609 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, (-1), (-1)], ![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 1, 1], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase609 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase609 parameter.1 parameter.2

theorem rightInverseCase609_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase609 k) parameter *
      rightInverseCase609 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase609 : NormalizationDatum :=
  ⟨609, selectedCase609, rightInverseCase609,
    rightInverseCase609_ok⟩

def selectedCase610 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase610 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![(-1), 0, (-1), 1, (-1)], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase610 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase610 parameter.1 parameter.2

theorem rightInverseCase610_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase610 k) parameter *
      rightInverseCase610 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase610 : NormalizationDatum :=
  ⟨610, selectedCase610, rightInverseCase610,
    rightInverseCase610_ok⟩

def selectedCase611 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase611 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 1, 0, 0, 1], ![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![0, (-1), 0, 0, (-1)], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase611 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase611 parameter.1 parameter.2

theorem rightInverseCase611_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase611 k) parameter *
      rightInverseCase611 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase611 : NormalizationDatum :=
  ⟨611, selectedCase611, rightInverseCase611,
    rightInverseCase611_ok⟩

def selectedCase642 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 2 1, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase642 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 1, 1, (-1), 1], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase642 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase642 parameter.1 parameter.2

theorem rightInverseCase642_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase642 k) parameter *
      rightInverseCase642 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase642 : NormalizationDatum :=
  ⟨642, selectedCase642, rightInverseCase642,
    rightInverseCase642_ok⟩

def selectedCase643 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 2 1, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase643 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 1, 1], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase643 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase643 parameter.1 parameter.2

theorem rightInverseCase643_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase643 k) parameter *
      rightInverseCase643 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase643 : NormalizationDatum :=
  ⟨643, selectedCase643, rightInverseCase643,
    rightInverseCase643_ok⟩

def selectedCase644 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 2 1, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase644 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![(-1), 0, 0, 0, (-1)], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase644 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase644 parameter.1 parameter.2

theorem rightInverseCase644_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase644 k) parameter *
      rightInverseCase644 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase644 : NormalizationDatum :=
  ⟨644, selectedCase644, rightInverseCase644,
    rightInverseCase644_ok⟩

def selectedCase645 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 2 1, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase645 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, (-1), (-1)], ![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 1, 1], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase645 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase645 parameter.1 parameter.2

theorem rightInverseCase645_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase645 k) parameter *
      rightInverseCase645 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase645 : NormalizationDatum :=
  ⟨645, selectedCase645, rightInverseCase645,
    rightInverseCase645_ok⟩

def selectedCase646 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 2 1, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase646 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![(-1), 0, 0, 0, (-1)], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase646 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase646 parameter.1 parameter.2

theorem rightInverseCase646_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase646 k) parameter *
      rightInverseCase646 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase646 : NormalizationDatum :=
  ⟨646, selectedCase646, rightInverseCase646,
    rightInverseCase646_ok⟩

def selectedCase647 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 0, MonochromaticQuantumGraph.mkEdge 0 3 2 1, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase647 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 1, 1, (-1), 1], ![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![0, (-1), (-1), 1, (-1)], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase647 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase647 parameter.1 parameter.2

theorem rightInverseCase647_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase647 k) parameter *
      rightInverseCase647 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase647 : NormalizationDatum :=
  ⟨647, selectedCase647, rightInverseCase647,
    rightInverseCase647_ok⟩

def selectedCase774 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 2, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase774 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 1, 1], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, 0, (-1), 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase774 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase774 parameter.1 parameter.2

theorem rightInverseCase774_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase774 k) parameter *
      rightInverseCase774 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase774 : NormalizationDatum :=
  ⟨774, selectedCase774, rightInverseCase774,
    rightInverseCase774_ok⟩

def selectedCase775 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 2, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase775 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, (-1), (-1), 2, (-1)]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, 0, (-1), 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase775 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase775 parameter.1 parameter.2

theorem rightInverseCase775_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase775 k) parameter *
      rightInverseCase775 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase775 : NormalizationDatum :=
  ⟨775, selectedCase775, rightInverseCase775,
    rightInverseCase775_ok⟩

def selectedCase776 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 2, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase776 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![(-1), 0, 0, 0, (-1)], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, 0, (-1), 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase776 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase776 parameter.1 parameter.2

theorem rightInverseCase776_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase776 k) parameter *
      rightInverseCase776 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase776 : NormalizationDatum :=
  ⟨776, selectedCase776, rightInverseCase776,
    rightInverseCase776_ok⟩

def selectedCase777 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 2, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase777 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, (-1), (-1), 2, (-1)]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, 0, (-1), 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase777 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase777 parameter.1 parameter.2

theorem rightInverseCase777_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase777 k) parameter *
      rightInverseCase777 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase777 : NormalizationDatum :=
  ⟨777, selectedCase777, rightInverseCase777,
    rightInverseCase777_ok⟩

def selectedCase778 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 2, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase778 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![(-1), 0, 0, 0, (-1)], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, 0, (-1), 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase778 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase778 parameter.1 parameter.2

theorem rightInverseCase778_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase778 k) parameter *
      rightInverseCase778 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase778 : NormalizationDatum :=
  ⟨778, selectedCase778, rightInverseCase778,
    rightInverseCase778_ok⟩

def selectedCase779 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 2, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 1 2, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase779 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 1, 1], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, (-1), (-1)], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, 0, (-1), 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase779 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase779 parameter.1 parameter.2

theorem rightInverseCase779_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase779 k) parameter *
      rightInverseCase779 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase779 : NormalizationDatum :=
  ⟨779, selectedCase779, rightInverseCase779,
    rightInverseCase779_ok⟩

def selectedCase780 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 2, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase780 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 1, 0, 1], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase780 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase780 parameter.1 parameter.2

theorem rightInverseCase780_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase780 k) parameter *
      rightInverseCase780 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase780 : NormalizationDatum :=
  ⟨780, selectedCase780, rightInverseCase780,
    rightInverseCase780_ok⟩

def selectedCase781 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 2, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase781 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 1, (-1), 1, 1], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase781 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase781 parameter.1 parameter.2

theorem rightInverseCase781_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase781 k) parameter *
      rightInverseCase781 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase781 : NormalizationDatum :=
  ⟨781, selectedCase781, rightInverseCase781,
    rightInverseCase781_ok⟩

def selectedCase782 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 2, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase782 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![(-1), 0, 0, 0, (-1)], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase782 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase782 parameter.1 parameter.2

theorem rightInverseCase782_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase782 k) parameter *
      rightInverseCase782 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase782 : NormalizationDatum :=
  ⟨782, selectedCase782, rightInverseCase782,
    rightInverseCase782_ok⟩

def selectedCase783 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 2, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase783 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, (-1), 1, (-1), (-1)], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 1, 1], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase783 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase783 parameter.1 parameter.2

theorem rightInverseCase783_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase783 k) parameter *
      rightInverseCase783 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase783 : NormalizationDatum :=
  ⟨783, selectedCase783, rightInverseCase783,
    rightInverseCase783_ok⟩

def selectedCase784 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 2, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase784 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![(-1), 0, 0, 0, (-1)], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase784 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase784 parameter.1 parameter.2

theorem rightInverseCase784_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase784 k) parameter *
      rightInverseCase784 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase784 : NormalizationDatum :=
  ⟨784, selectedCase784, rightInverseCase784,
    rightInverseCase784_ok⟩

def selectedCase785 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 2, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase785 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 1, 0, 1], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![0, 0, (-1), 0, (-1)], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase785 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase785 parameter.1 parameter.2

theorem rightInverseCase785_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase785 k) parameter *
      rightInverseCase785 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase785 : NormalizationDatum :=
  ⟨785, selectedCase785, rightInverseCase785,
    rightInverseCase785_ok⟩

def selectedCase786 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 2, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase786 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 1, 0, 1], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase786 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase786 parameter.1 parameter.2

theorem rightInverseCase786_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase786 k) parameter *
      rightInverseCase786 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase786 : NormalizationDatum :=
  ⟨786, selectedCase786, rightInverseCase786,
    rightInverseCase786_ok⟩

def selectedCase787 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 2, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase787 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 1, (-1), 1, 1], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase787 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase787 parameter.1 parameter.2

theorem rightInverseCase787_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase787 k) parameter *
      rightInverseCase787 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase787 : NormalizationDatum :=
  ⟨787, selectedCase787, rightInverseCase787,
    rightInverseCase787_ok⟩

def selectedCase788 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 2, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase788 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![(-1), 0, 0, 0, (-1)], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase788 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase788 parameter.1 parameter.2

theorem rightInverseCase788_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase788 k) parameter *
      rightInverseCase788 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase788 : NormalizationDatum :=
  ⟨788, selectedCase788, rightInverseCase788,
    rightInverseCase788_ok⟩

def selectedCase789 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 2, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase789 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, (-1), 1, (-1), (-1)], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![0, 1, (-1), 1, 1], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase789 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase789 parameter.1 parameter.2

theorem rightInverseCase789_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase789 k) parameter *
      rightInverseCase789 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase789 : NormalizationDatum :=
  ⟨789, selectedCase789, rightInverseCase789,
    rightInverseCase789_ok⟩

def selectedCase790 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 2, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase790 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![(-1), 0, 0, 0, (-1)], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase790 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase790 parameter.1 parameter.2

theorem rightInverseCase790_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase790 k) parameter *
      rightInverseCase790 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase790 : NormalizationDatum :=
  ⟨790, selectedCase790, rightInverseCase790,
    rightInverseCase790_ok⟩

def selectedCase791 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 2, MonochromaticQuantumGraph.mkEdge 0 3 1 2, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase791 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 1, 0, 1], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![0, 0, (-1), 0, (-1)], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, (-1), 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase791 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase791 parameter.1 parameter.2

theorem rightInverseCase791_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase791 k) parameter *
      rightInverseCase791 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase791 : NormalizationDatum :=
  ⟨791, selectedCase791, rightInverseCase791,
    rightInverseCase791_ok⟩

def selectedCase816 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 2, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase816 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 1, 0, 0, 1], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase816 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase816 parameter.1 parameter.2

theorem rightInverseCase816_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase816 k) parameter *
      rightInverseCase816 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase816 : NormalizationDatum :=
  ⟨816, selectedCase816, rightInverseCase816,
    rightInverseCase816_ok⟩

def selectedCase817 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 2, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase817 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 1, 1], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase817 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase817 parameter.1 parameter.2

theorem rightInverseCase817_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase817 k) parameter *
      rightInverseCase817 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase817 : NormalizationDatum :=
  ⟨817, selectedCase817, rightInverseCase817,
    rightInverseCase817_ok⟩

def selectedCase818 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 2, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase818 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![(-1), 0, (-1), 1, (-1)], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase818 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase818 parameter.1 parameter.2

theorem rightInverseCase818_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase818 k) parameter *
      rightInverseCase818 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase818 : NormalizationDatum :=
  ⟨818, selectedCase818, rightInverseCase818,
    rightInverseCase818_ok⟩

def selectedCase819 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 2, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase819 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, (-1), (-1)], ![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 1, 1], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase819 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase819 parameter.1 parameter.2

theorem rightInverseCase819_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase819 k) parameter *
      rightInverseCase819 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase819 : NormalizationDatum :=
  ⟨819, selectedCase819, rightInverseCase819,
    rightInverseCase819_ok⟩

def selectedCase820 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 2, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase820 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![(-1), 0, (-1), 1, (-1)], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase820 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase820 parameter.1 parameter.2

theorem rightInverseCase820_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase820 k) parameter *
      rightInverseCase820 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase820 : NormalizationDatum :=
  ⟨820, selectedCase820, rightInverseCase820,
    rightInverseCase820_ok⟩

def selectedCase821 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 2, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase821 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 1, 0, 0, 1], ![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![0, (-1), 0, 0, (-1)], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase821 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase821 parameter.1 parameter.2

theorem rightInverseCase821_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase821 k) parameter *
      rightInverseCase821 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase821 : NormalizationDatum :=
  ⟨821, selectedCase821, rightInverseCase821,
    rightInverseCase821_ok⟩

def selectedCase822 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 2, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase822 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 1, 0, 0, 1], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase822 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase822 parameter.1 parameter.2

theorem rightInverseCase822_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase822 k) parameter *
      rightInverseCase822 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase822 : NormalizationDatum :=
  ⟨822, selectedCase822, rightInverseCase822,
    rightInverseCase822_ok⟩

def selectedCase823 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 2, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase823 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 1, 1], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase823 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase823 parameter.1 parameter.2

theorem rightInverseCase823_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase823 k) parameter *
      rightInverseCase823 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase823 : NormalizationDatum :=
  ⟨823, selectedCase823, rightInverseCase823,
    rightInverseCase823_ok⟩

def selectedCase824 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 2, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase824 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![(-1), 0, (-1), 1, (-1)], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase824 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase824 parameter.1 parameter.2

theorem rightInverseCase824_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase824 k) parameter *
      rightInverseCase824 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase824 : NormalizationDatum :=
  ⟨824, selectedCase824, rightInverseCase824,
    rightInverseCase824_ok⟩

def selectedCase825 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 2, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase825 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, (-1), (-1)], ![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 1, 1], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase825 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase825 parameter.1 parameter.2

theorem rightInverseCase825_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase825 k) parameter *
      rightInverseCase825 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase825 : NormalizationDatum :=
  ⟨825, selectedCase825, rightInverseCase825,
    rightInverseCase825_ok⟩

def selectedCase826 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 2, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase826 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![(-1), 0, (-1), 1, (-1)], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase826 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase826 parameter.1 parameter.2

theorem rightInverseCase826_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase826 k) parameter *
      rightInverseCase826 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase826 : NormalizationDatum :=
  ⟨826, selectedCase826, rightInverseCase826,
    rightInverseCase826_ok⟩

def selectedCase827 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 2, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase827 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 1, 0, 0, 1], ![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![0, (-1), 0, 0, (-1)], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase827 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase827 parameter.1 parameter.2

theorem rightInverseCase827_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase827 k) parameter *
      rightInverseCase827 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase827 : NormalizationDatum :=
  ⟨827, selectedCase827, rightInverseCase827,
    rightInverseCase827_ok⟩

def selectedCase858 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 2, MonochromaticQuantumGraph.mkEdge 0 3 2 1, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase858 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 1, 1, (-1), 1], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase858 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase858 parameter.1 parameter.2

theorem rightInverseCase858_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase858 k) parameter *
      rightInverseCase858 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase858 : NormalizationDatum :=
  ⟨858, selectedCase858, rightInverseCase858,
    rightInverseCase858_ok⟩

def selectedCase859 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 2, MonochromaticQuantumGraph.mkEdge 0 3 2 1, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase859 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 1, 1], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase859 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase859 parameter.1 parameter.2

theorem rightInverseCase859_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase859 k) parameter *
      rightInverseCase859 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase859 : NormalizationDatum :=
  ⟨859, selectedCase859, rightInverseCase859,
    rightInverseCase859_ok⟩

def selectedCase860 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 2, MonochromaticQuantumGraph.mkEdge 0 3 2 1, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase860 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![(-1), 0, 0, 0, (-1)], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase860 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase860 parameter.1 parameter.2

theorem rightInverseCase860_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase860 k) parameter *
      rightInverseCase860 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase860 : NormalizationDatum :=
  ⟨860, selectedCase860, rightInverseCase860,
    rightInverseCase860_ok⟩

def selectedCase861 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 2, MonochromaticQuantumGraph.mkEdge 0 3 2 1, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase861 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, (-1), (-1)], ![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 1, 1], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase861 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase861 parameter.1 parameter.2

theorem rightInverseCase861_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase861 k) parameter *
      rightInverseCase861 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase861 : NormalizationDatum :=
  ⟨861, selectedCase861, rightInverseCase861,
    rightInverseCase861_ok⟩

def selectedCase862 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 2, MonochromaticQuantumGraph.mkEdge 0 3 2 1, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase862 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![(-1), 0, 0, 0, (-1)], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase862 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase862 parameter.1 parameter.2

theorem rightInverseCase862_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase862 k) parameter *
      rightInverseCase862 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase862 : NormalizationDatum :=
  ⟨862, selectedCase862, rightInverseCase862,
    rightInverseCase862_ok⟩

def selectedCase863 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 1 2, MonochromaticQuantumGraph.mkEdge 0 3 2 1, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase863 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 1, 1, (-1), 1], ![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![0, (-1), (-1), 1, (-1)], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase863 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase863 parameter.1 parameter.2

theorem rightInverseCase863_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase863 k) parameter *
      rightInverseCase863 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase863 : NormalizationDatum :=
  ⟨863, selectedCase863, rightInverseCase863,
    rightInverseCase863_ok⟩

def selectedCase1032 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 2 0, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase1032 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, (-1)], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase1032 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase1032 parameter.1 parameter.2

theorem rightInverseCase1032_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase1032 k) parameter *
      rightInverseCase1032 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase1032 : NormalizationDatum :=
  ⟨1032, selectedCase1032, rightInverseCase1032,
    rightInverseCase1032_ok⟩

def selectedCase1033 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 2 0, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase1033 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 1, 1], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase1033 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase1033 parameter.1 parameter.2

theorem rightInverseCase1033_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase1033 k) parameter *
      rightInverseCase1033 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase1033 : NormalizationDatum :=
  ⟨1033, selectedCase1033, rightInverseCase1033,
    rightInverseCase1033_ok⟩

def selectedCase1034 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 2 0, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase1034 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![(-1), (-1), (-1), 2, (-1)], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase1034 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase1034 parameter.1 parameter.2

theorem rightInverseCase1034_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase1034 k) parameter *
      rightInverseCase1034 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase1034 : NormalizationDatum :=
  ⟨1034, selectedCase1034, rightInverseCase1034,
    rightInverseCase1034_ok⟩

def selectedCase1035 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 2 0, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase1035 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, (-1), (-1)], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 1, 1], ![0, 0, 0, 0, 0]], ![![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase1035 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase1035 parameter.1 parameter.2

theorem rightInverseCase1035_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase1035 k) parameter *
      rightInverseCase1035 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase1035 : NormalizationDatum :=
  ⟨1035, selectedCase1035, rightInverseCase1035,
    rightInverseCase1035_ok⟩

def selectedCase1036 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 2 0, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase1036 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![(-1), (-1), (-1), 2, (-1)], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase1036 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase1036 parameter.1 parameter.2

theorem rightInverseCase1036_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase1036 k) parameter *
      rightInverseCase1036 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase1036 : NormalizationDatum :=
  ⟨1036, selectedCase1036, rightInverseCase1036,
    rightInverseCase1036_ok⟩

def selectedCase1037 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 2 0, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 0, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase1037 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, (-1)], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase1037 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase1037 parameter.1 parameter.2

theorem rightInverseCase1037_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase1037 k) parameter *
      rightInverseCase1037 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase1037 : NormalizationDatum :=
  ⟨1037, selectedCase1037, rightInverseCase1037,
    rightInverseCase1037_ok⟩

def selectedCase1038 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 2 0, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase1038 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, (-1)], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase1038 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase1038 parameter.1 parameter.2

theorem rightInverseCase1038_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase1038 k) parameter *
      rightInverseCase1038 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase1038 : NormalizationDatum :=
  ⟨1038, selectedCase1038, rightInverseCase1038,
    rightInverseCase1038_ok⟩

def selectedCase1039 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 2 0, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase1039 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 1, 1], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase1039 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase1039 parameter.1 parameter.2

theorem rightInverseCase1039_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase1039 k) parameter *
      rightInverseCase1039 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase1039 : NormalizationDatum :=
  ⟨1039, selectedCase1039, rightInverseCase1039,
    rightInverseCase1039_ok⟩

def selectedCase1040 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 2 0, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase1040 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![(-1), (-1), (-1), 2, (-1)], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase1040 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase1040 parameter.1 parameter.2

theorem rightInverseCase1040_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase1040 k) parameter *
      rightInverseCase1040 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase1040 : NormalizationDatum :=
  ⟨1040, selectedCase1040, rightInverseCase1040,
    rightInverseCase1040_ok⟩

def selectedCase1041 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 2 0, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase1041 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, (-1), (-1)], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 1, 1], ![0, 0, 0, 0, 0]], ![![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase1041 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase1041 parameter.1 parameter.2

theorem rightInverseCase1041_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase1041 k) parameter *
      rightInverseCase1041 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase1041 : NormalizationDatum :=
  ⟨1041, selectedCase1041, rightInverseCase1041,
    rightInverseCase1041_ok⟩

def selectedCase1042 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 2 0, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase1042 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![(-1), (-1), (-1), 2, (-1)], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase1042 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase1042 parameter.1 parameter.2

theorem rightInverseCase1042_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase1042 k) parameter *
      rightInverseCase1042 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase1042 : NormalizationDatum :=
  ⟨1042, selectedCase1042, rightInverseCase1042,
    rightInverseCase1042_ok⟩

def selectedCase1043 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 2 0, MonochromaticQuantumGraph.mkEdge 0 3 2 0, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase1043 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, (-1)], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase1043 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase1043 parameter.1 parameter.2

theorem rightInverseCase1043_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase1043 k) parameter *
      rightInverseCase1043 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase1043 : NormalizationDatum :=
  ⟨1043, selectedCase1043, rightInverseCase1043,
    rightInverseCase1043_ok⟩

def selectedCase1074 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 2 0, MonochromaticQuantumGraph.mkEdge 0 3 2 1, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase1074 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, (-1), 1, (-1)], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase1074 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase1074 parameter.1 parameter.2

theorem rightInverseCase1074_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase1074 k) parameter *
      rightInverseCase1074 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase1074 : NormalizationDatum :=
  ⟨1074, selectedCase1074, rightInverseCase1074,
    rightInverseCase1074_ok⟩

def selectedCase1075 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 2 0, MonochromaticQuantumGraph.mkEdge 0 3 2 1, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase1075 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 1, 1], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase1075 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase1075 parameter.1 parameter.2

theorem rightInverseCase1075_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase1075 k) parameter *
      rightInverseCase1075 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase1075 : NormalizationDatum :=
  ⟨1075, selectedCase1075, rightInverseCase1075,
    rightInverseCase1075_ok⟩

def selectedCase1076 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 2 0, MonochromaticQuantumGraph.mkEdge 0 3 2 1, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase1076 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![(-1), (-1), 0, 1, (-1)], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase1076 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase1076 parameter.1 parameter.2

theorem rightInverseCase1076_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase1076 k) parameter *
      rightInverseCase1076 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase1076 : NormalizationDatum :=
  ⟨1076, selectedCase1076, rightInverseCase1076,
    rightInverseCase1076_ok⟩

def selectedCase1077 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 2 0, MonochromaticQuantumGraph.mkEdge 0 3 2 1, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase1077 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, (-1), (-1)], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 1, 1], ![0, 0, 0, 0, 0]], ![![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase1077 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase1077 parameter.1 parameter.2

theorem rightInverseCase1077_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase1077 k) parameter *
      rightInverseCase1077 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase1077 : NormalizationDatum :=
  ⟨1077, selectedCase1077, rightInverseCase1077,
    rightInverseCase1077_ok⟩

def selectedCase1078 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 2 0, MonochromaticQuantumGraph.mkEdge 0 3 2 1, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase1078 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![(-1), (-1), 0, 1, (-1)], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase1078 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase1078 parameter.1 parameter.2

theorem rightInverseCase1078_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase1078 k) parameter *
      rightInverseCase1078 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase1078 : NormalizationDatum :=
  ⟨1078, selectedCase1078, rightInverseCase1078,
    rightInverseCase1078_ok⟩

def selectedCase1079 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 2 0, MonochromaticQuantumGraph.mkEdge 0 3 2 1, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase1079 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, (-1), 1, (-1)], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase1079 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase1079 parameter.1 parameter.2

theorem rightInverseCase1079_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase1079 k) parameter *
      rightInverseCase1079 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase1079 : NormalizationDatum :=
  ⟨1079, selectedCase1079, rightInverseCase1079,
    rightInverseCase1079_ok⟩

def selectedCase1290 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 2 1, MonochromaticQuantumGraph.mkEdge 0 3 2 1, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 0 1]

def rightInverseTableCase1290 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, (-1), (-1), 2, (-1)], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase1290 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase1290 parameter.1 parameter.2

theorem rightInverseCase1290_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase1290 k) parameter *
      rightInverseCase1290 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase1290 : NormalizationDatum :=
  ⟨1290, selectedCase1290, rightInverseCase1290,
    rightInverseCase1290_ok⟩

def selectedCase1291 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 2 1, MonochromaticQuantumGraph.mkEdge 0 3 2 1, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 0 2]

def rightInverseTableCase1291 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 1, 1], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase1291 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase1291 parameter.1 parameter.2

theorem rightInverseCase1291_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase1291 k) parameter *
      rightInverseCase1291 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase1291 : NormalizationDatum :=
  ⟨1291, selectedCase1291, rightInverseCase1291,
    rightInverseCase1291_ok⟩

def selectedCase1292 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 2 1, MonochromaticQuantumGraph.mkEdge 0 3 2 1, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 1 0]

def rightInverseTableCase1292 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![(-1), 0, 0, 0, (-1)], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase1292 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase1292 parameter.1 parameter.2

theorem rightInverseCase1292_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase1292 k) parameter *
      rightInverseCase1292 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase1292 : NormalizationDatum :=
  ⟨1292, selectedCase1292, rightInverseCase1292,
    rightInverseCase1292_ok⟩

def selectedCase1293 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 2 1, MonochromaticQuantumGraph.mkEdge 0 3 2 1, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 1 2]

def rightInverseTableCase1293 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, (-1), (-1)], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 1, 1], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase1293 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase1293 parameter.1 parameter.2

theorem rightInverseCase1293_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase1293 k) parameter *
      rightInverseCase1293 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase1293 : NormalizationDatum :=
  ⟨1293, selectedCase1293, rightInverseCase1293,
    rightInverseCase1293_ok⟩

def selectedCase1294 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 2 1, MonochromaticQuantumGraph.mkEdge 0 3 2 1, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 2 0]

def rightInverseTableCase1294 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0]], ![![(-1), 0, 0, 0, (-1)], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase1294 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase1294 parameter.1 parameter.2

theorem rightInverseCase1294_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase1294 k) parameter *
      rightInverseCase1294 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase1294 : NormalizationDatum :=
  ⟨1294, selectedCase1294, rightInverseCase1294,
    rightInverseCase1294_ok⟩

def selectedCase1295 : Fin 5 → EdgeN 6 3 := ![MonochromaticQuantumGraph.mkEdge 0 1 0 1, MonochromaticQuantumGraph.mkEdge 0 2 2 1, MonochromaticQuantumGraph.mkEdge 0 3 2 1, MonochromaticQuantumGraph.mkEdge 0 4 2 1, MonochromaticQuantumGraph.mkEdge 1 5 2 1]

def rightInverseTableCase1295 : Fin 5 → Fin 3 → Fin 5 → ℤ :=
  ![![![1, 0, 0, 0, 0], ![0, (-1), (-1), 2, (-1)], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1), 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

def rightInverseCase1295 : GaugeParameter → Fin 5 → ℤ :=
  fun parameter => rightInverseTableCase1295 parameter.1 parameter.2

theorem rightInverseCase1295_ok : ∀ k l,
    ∑ parameter, channelExponent (selectedCase1295 k) parameter *
      rightInverseCase1295 parameter l = if k = l then 1 else 0 := by
  decide

def datumCase1295 : NormalizationDatum :=
  ⟨1295, selectedCase1295, rightInverseCase1295,
    rightInverseCase1295_ok⟩

def representativeCase : Fin 336 → Fin 1296 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 210, 211, 212, 213, 214, 215, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 321, 322, 323, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355, 356, 357, 358, 359, 384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 426, 427, 428, 429, 430, 431, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527, 528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 558, 559, 560, 561, 562, 563, 564, 565, 566, 567, 568, 569, 570, 571, 572, 573, 574, 575, 600, 601, 602, 603, 604, 605, 606, 607, 608, 609, 610, 611, 642, 643, 644, 645, 646, 647, 774, 775, 776, 777, 778, 779, 780, 781, 782, 783, 784, 785, 786, 787, 788, 789, 790, 791, 816, 817, 818, 819, 820, 821, 822, 823, 824, 825, 826, 827, 858, 859, 860, 861, 862, 863, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039, 1040, 1041, 1042, 1043, 1074, 1075, 1076, 1077, 1078, 1079, 1290, 1291, 1292, 1293, 1294, 1295]

def orbitSize : Fin 336 → Nat :=
  ![6, 6, 6, 6, 6, 6, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 18, 18, 18, 18, 18, 18, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 18, 18, 18, 18, 18, 18, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 18, 18, 18, 18, 18, 18, 36, 36, 36, 36, 36, 36, 18, 18, 18, 18, 18, 18, 6, 6, 6, 6, 6, 6, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 18, 18, 18, 18, 18, 18, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 18, 18, 18, 18, 18, 18, 36, 36, 36, 36, 36, 36, 18, 18, 18, 18, 18, 18, 6, 6, 6, 6, 6, 6, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 18, 18, 18, 18, 18, 18, 36, 36, 36, 36, 36, 36, 18, 18, 18, 18, 18, 18, 6, 6, 6, 6, 6, 6, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 36, 36, 36, 36, 36, 36, 18, 18, 18, 18, 18, 18, 6, 6, 6, 6, 6, 6, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 6, 6, 6, 6, 6, 6]

def datum : Fin 336 → NormalizationDatum :=
  ![datumCase0, datumCase1, datumCase2, datumCase3, datumCase4, datumCase5, datumCase6, datumCase7, datumCase8, datumCase9, datumCase10, datumCase11, datumCase12, datumCase13, datumCase14, datumCase15, datumCase16, datumCase17, datumCase18, datumCase19, datumCase20, datumCase21, datumCase22, datumCase23, datumCase24, datumCase25, datumCase26, datumCase27, datumCase28, datumCase29, datumCase30, datumCase31, datumCase32, datumCase33, datumCase34, datumCase35, datumCase42, datumCase43, datumCase44, datumCase45, datumCase46, datumCase47, datumCase48, datumCase49, datumCase50, datumCase51, datumCase52, datumCase53, datumCase54, datumCase55, datumCase56, datumCase57, datumCase58, datumCase59, datumCase60, datumCase61, datumCase62, datumCase63, datumCase64, datumCase65, datumCase66, datumCase67, datumCase68, datumCase69, datumCase70, datumCase71, datumCase84, datumCase85, datumCase86, datumCase87, datumCase88, datumCase89, datumCase90, datumCase91, datumCase92, datumCase93, datumCase94, datumCase95, datumCase96, datumCase97, datumCase98, datumCase99, datumCase100, datumCase101, datumCase102, datumCase103, datumCase104, datumCase105, datumCase106, datumCase107, datumCase126, datumCase127, datumCase128, datumCase129, datumCase130, datumCase131, datumCase132, datumCase133, datumCase134, datumCase135, datumCase136, datumCase137, datumCase138, datumCase139, datumCase140, datumCase141, datumCase142, datumCase143, datumCase168, datumCase169, datumCase170, datumCase171, datumCase172, datumCase173, datumCase174, datumCase175, datumCase176, datumCase177, datumCase178, datumCase179, datumCase210, datumCase211, datumCase212, datumCase213, datumCase214, datumCase215, datumCase258, datumCase259, datumCase260, datumCase261, datumCase262, datumCase263, datumCase264, datumCase265, datumCase266, datumCase267, datumCase268, datumCase269, datumCase270, datumCase271, datumCase272, datumCase273, datumCase274, datumCase275, datumCase276, datumCase277, datumCase278, datumCase279, datumCase280, datumCase281, datumCase282, datumCase283, datumCase284, datumCase285, datumCase286, datumCase287, datumCase300, datumCase301, datumCase302, datumCase303, datumCase304, datumCase305, datumCase306, datumCase307, datumCase308, datumCase309, datumCase310, datumCase311, datumCase312, datumCase313, datumCase314, datumCase315, datumCase316, datumCase317, datumCase318, datumCase319, datumCase320, datumCase321, datumCase322, datumCase323, datumCase342, datumCase343, datumCase344, datumCase345, datumCase346, datumCase347, datumCase348, datumCase349, datumCase350, datumCase351, datumCase352, datumCase353, datumCase354, datumCase355, datumCase356, datumCase357, datumCase358, datumCase359, datumCase384, datumCase385, datumCase386, datumCase387, datumCase388, datumCase389, datumCase390, datumCase391, datumCase392, datumCase393, datumCase394, datumCase395, datumCase426, datumCase427, datumCase428, datumCase429, datumCase430, datumCase431, datumCase516, datumCase517, datumCase518, datumCase519, datumCase520, datumCase521, datumCase522, datumCase523, datumCase524, datumCase525, datumCase526, datumCase527, datumCase528, datumCase529, datumCase530, datumCase531, datumCase532, datumCase533, datumCase534, datumCase535, datumCase536, datumCase537, datumCase538, datumCase539, datumCase558, datumCase559, datumCase560, datumCase561, datumCase562, datumCase563, datumCase564, datumCase565, datumCase566, datumCase567, datumCase568, datumCase569, datumCase570, datumCase571, datumCase572, datumCase573, datumCase574, datumCase575, datumCase600, datumCase601, datumCase602, datumCase603, datumCase604, datumCase605, datumCase606, datumCase607, datumCase608, datumCase609, datumCase610, datumCase611, datumCase642, datumCase643, datumCase644, datumCase645, datumCase646, datumCase647, datumCase774, datumCase775, datumCase776, datumCase777, datumCase778, datumCase779, datumCase780, datumCase781, datumCase782, datumCase783, datumCase784, datumCase785, datumCase786, datumCase787, datumCase788, datumCase789, datumCase790, datumCase791, datumCase816, datumCase817, datumCase818, datumCase819, datumCase820, datumCase821, datumCase822, datumCase823, datumCase824, datumCase825, datumCase826, datumCase827, datumCase858, datumCase859, datumCase860, datumCase861, datumCase862, datumCase863, datumCase1032, datumCase1033, datumCase1034, datumCase1035, datumCase1036, datumCase1037, datumCase1038, datumCase1039, datumCase1040, datumCase1041, datumCase1042, datumCase1043, datumCase1074, datumCase1075, datumCase1076, datumCase1077, datumCase1078, datumCase1079, datumCase1290, datumCase1291, datumCase1292, datumCase1293, datumCase1294, datumCase1295]

theorem datum_caseIndex : ∀ i,
    (datum i).caseIndex = representativeCase i := by
  decide

theorem orbitSize_total : ∑ i, orbitSize i = 7776 := by
  decide

#print axioms Krenn.X5GaugeNormalizationData.rightInverseCase0_ok
#print axioms Krenn.X5GaugeNormalizationData.datum_caseIndex
#print axioms Krenn.X5GaugeNormalizationData.orbitSize_total

end Krenn.X5GaugeNormalizationData

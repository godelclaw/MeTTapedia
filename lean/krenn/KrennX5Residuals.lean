import KrennX5ResidualCase5.Bridge
import KrennX5ResidualCase84.Bridge
import KrennX5ResidualCase86.Bridge
import KrennX5ResidualCase98.Bridge
import KrennX5ResidualCase102.Bridge
import KrennX5ResidualCase131.Bridge
import KrennX5ResidualCase170.Bridge
import KrennX5ResidualCase304.Bridge
import KrennX5ResidualCase316.Bridge
import KrennX5ResidualCase385.Bridge
import KrennX5ResidualCase388.Bridge
import KrennX5ResidualCase429.Bridge
import KrennX5ResidualCase516.Bridge
import KrennX5ResidualCase642.Bridge
import KrennX5ResidualCase817.Bridge
import KrennX5ResidualCase861.Bridge
import KrennX5ResidualCase863.Bridge
import KrennX5ResidualCase1033.Bridge
import KrennX5ResidualCase1293.Bridge

/-!
Typed registry for the nineteen residual representatives of the
`X = {01,02,03,04,15}` support orbit.

Cases 5 and 1293 have direct strict parent identities.  The other seventeen
entries are refuted by an exhaustive three-coordinate carrier split whose
eight leaves each carry a strict exact identity.  Every `impossible` field is
attached to the official `EqSystemN 6 3` equations and the exact frozen
normalization predicate for its case.

This registry does not by itself prove that these are exactly the complement
of the 317 historical multilinear closures; that outer partition remains a
separate coverage theorem.
-/

namespace Krenn.X5Residuals

open MonochromaticQuantumGraph

structure RefutedResidualCase where
  caseIndex : Nat
  Normalized : WeightsN 6 3 ℂ → Prop
  impossible : ∀ W, EqSystemN 6 3 W → Normalized W → False
  closureKind : String

def entry5 : RefutedResidualCase := ⟨5,
  Krenn.X5ResidualCase5.Bridge.NormalizedCase,
  Krenn.X5ResidualCase5.Bridge.noNormalizedCase,
  "strict-parent-identity"⟩

def entry84 : RefutedResidualCase := ⟨84,
  Krenn.X5ResidualCase84.Bridge.NormalizedCase,
  Krenn.X5ResidualCase84.Bridge.noNormalizedCase,
  "strict-eight-leaf-carrier-tree"⟩

def entry86 : RefutedResidualCase := ⟨86,
  Krenn.X5ResidualCase86.Bridge.NormalizedCase,
  Krenn.X5ResidualCase86.Bridge.noNormalizedCase,
  "strict-eight-leaf-carrier-tree"⟩

def entry98 : RefutedResidualCase := ⟨98,
  Krenn.X5ResidualCase98.Bridge.NormalizedCase,
  Krenn.X5ResidualCase98.Bridge.noNormalizedCase,
  "strict-eight-leaf-carrier-tree"⟩

def entry102 : RefutedResidualCase := ⟨102,
  Krenn.X5ResidualCase102.Bridge.NormalizedCase,
  Krenn.X5ResidualCase102.Bridge.noNormalizedCase,
  "strict-eight-leaf-carrier-tree"⟩

def entry131 : RefutedResidualCase := ⟨131,
  Krenn.X5ResidualCase131.Bridge.NormalizedCase,
  Krenn.X5ResidualCase131.Bridge.noNormalizedCase,
  "strict-eight-leaf-carrier-tree"⟩

def entry170 : RefutedResidualCase := ⟨170,
  Krenn.X5ResidualCase170.Bridge.NormalizedCase,
  Krenn.X5ResidualCase170.Bridge.noNormalizedCase,
  "strict-eight-leaf-carrier-tree"⟩

def entry304 : RefutedResidualCase := ⟨304,
  Krenn.X5ResidualCase304.Bridge.NormalizedCase,
  Krenn.X5ResidualCase304.Bridge.noNormalizedCase,
  "strict-eight-leaf-carrier-tree"⟩

def entry316 : RefutedResidualCase := ⟨316,
  Krenn.X5ResidualCase316.Bridge.NormalizedCase,
  Krenn.X5ResidualCase316.Bridge.noNormalizedCase,
  "strict-eight-leaf-carrier-tree"⟩

def entry385 : RefutedResidualCase := ⟨385,
  Krenn.X5ResidualCase385.Bridge.NormalizedCase,
  Krenn.X5ResidualCase385.Bridge.noNormalizedCase,
  "strict-eight-leaf-carrier-tree"⟩

def entry388 : RefutedResidualCase := ⟨388,
  Krenn.X5ResidualCase388.Bridge.NormalizedCase,
  Krenn.X5ResidualCase388.Bridge.noNormalizedCase,
  "strict-eight-leaf-carrier-tree"⟩

def entry429 : RefutedResidualCase := ⟨429,
  Krenn.X5ResidualCase429.Bridge.NormalizedCase,
  Krenn.X5ResidualCase429.Bridge.noNormalizedCase,
  "strict-eight-leaf-carrier-tree"⟩

def entry516 : RefutedResidualCase := ⟨516,
  Krenn.X5ResidualCase516.Bridge.NormalizedCase,
  Krenn.X5ResidualCase516.Bridge.noNormalizedCase,
  "strict-eight-leaf-carrier-tree"⟩

def entry642 : RefutedResidualCase := ⟨642,
  Krenn.X5ResidualCase642.Bridge.NormalizedCase,
  Krenn.X5ResidualCase642.Bridge.noNormalizedCase,
  "strict-eight-leaf-carrier-tree"⟩

def entry817 : RefutedResidualCase := ⟨817,
  Krenn.X5ResidualCase817.Bridge.NormalizedCase,
  Krenn.X5ResidualCase817.Bridge.noNormalizedCase,
  "strict-eight-leaf-carrier-tree"⟩

def entry861 : RefutedResidualCase := ⟨861,
  Krenn.X5ResidualCase861.Bridge.NormalizedCase,
  Krenn.X5ResidualCase861.Bridge.noNormalizedCase,
  "strict-eight-leaf-carrier-tree"⟩

def entry863 : RefutedResidualCase := ⟨863,
  Krenn.X5ResidualCase863.Bridge.NormalizedCase,
  Krenn.X5ResidualCase863.Bridge.noNormalizedCase,
  "strict-eight-leaf-carrier-tree"⟩

def entry1033 : RefutedResidualCase := ⟨1033,
  Krenn.X5ResidualCase1033.Bridge.NormalizedCase,
  Krenn.X5ResidualCase1033.Bridge.noNormalizedCase,
  "strict-eight-leaf-carrier-tree"⟩

def entry1293 : RefutedResidualCase := ⟨1293,
  Krenn.X5ResidualCase1293.Bridge.NormalizedCase,
  Krenn.X5ResidualCase1293.Bridge.noNormalizedCase,
  "strict-parent-identity"⟩

def residualCases : Fin 19 → RefutedResidualCase := ![
  entry5, entry84, entry86, entry98, entry102, entry131, entry170, entry304,
  entry316, entry385, entry388, entry429, entry516, entry642, entry817,
  entry861, entry863, entry1033, entry1293
]

def residualCaseIndices : List Nat :=
  [5, 84, 86, 98, 102, 131, 170, 304, 316, 385, 388, 429, 516, 642,
   817, 861, 863, 1033, 1293]

theorem residualCaseIndices_length : residualCaseIndices.length = 19 := by decide

theorem residualCaseIndices_nodup : residualCaseIndices.Nodup := by decide

#print axioms Krenn.X5Residuals.residualCaseIndices_nodup

end Krenn.X5Residuals

import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAllResults

/-!
# Independent universe bounds for native Vector result views

The existing result program is instantiated in the native Vec profile at
`gamma = max(alpha, beta)`, with elimination into `succ gamma`. Its function
type retains independent caller bounds `A : U_alpha` and `R : U_beta`.
Both input and output vectors belong to this enlarged Vec instance.

The signature is formed by the existing level-instantiation construction.
Finite evidence and independent typing replay have separate companions.
Transport from an original lower-universe Vec instance, computation coherence
and arbitrary open-container interpretation remain separate comparisons.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.ResultView.Universes

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation Declaration RussellTarski
open NativeNaturalVectorFamilies

def dataLevel : LevelExpr Nat := .param 0
def resultLevel : LevelExpr Nat := .param 2
def vectorLevel : LevelExpr Nat := .max dataLevel resultLevel

def programLevels (parameter : Nat) : LevelExpr Nat :=
  if parameter = 0 then vectorLevel else .param parameter

def levels (parameter : Nat) : LevelExpr Nat :=
  if parameter = 0 then vectorLevel
  else if parameter = 1 then .succ vectorLevel
  else .param parameter

def levelInstance : LevelInstance NativeNaturalVectorFamilies.rawSignature levels where
  computation := NativeNaturalVectorFamilies.iotaComputation
  computationMap step := by
    obtain ⟨evidence⟩ := step
    exact ⟨NativeNaturalVectorFamilies.Programs.mapIota (substLevelsHead levels) evidence⟩

abbrev signature := levelInstance.signature
abbrev rules := levelInstance.rules

theorem signature_formed : signature.Formed Tower.rules :=
  levelInstance.formed NativeNaturalVectorFamilies.rawSignature_formed

def decoder : StructuralConversionCode.RootDecoder rules.computation :=
  DeclarationConversionCode.rootDecoder (base := Tower.rules) (signature := signature)
    (.ofEmpty _ rfl) NativeNaturalVectorFamilies.Checking.iotaDecoder

def program : Tower.Tm 0 := substLevelsTm programLevels ResultView.program

def programType : Tower.Tm 0 :=
  .pi (sortTm dataLevel)
    (.pi (sortTm resultLevel)
      (.pi natTm
        (.pi (vecApp (.var 2) (.var 0))
          (.pi (substLevelsTm programLevels
            (NativeVectorAll.allType (.var 3) (ResultView.predicate (.var 2)) (.var 1) (.var 0)))
            (vecApp (.var 3) (.var 2))))))

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.ResultView.Universes

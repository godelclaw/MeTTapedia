import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.IntrinsicNativeListMaps
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.IntrinsicNativeListRelator
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeRelatorRootConversionCode

/-!
# Level instances of the proof-relevant native List relator

The native List relation is universe-polymorphic.  This module instantiates
all of its universe parameters at one selected cumulative-tower level while
retaining the exact List and relational iota evidence.  It is the relational
counterpart of `IntrinsicMaps.listLevelInstance`.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeIndexedFamilies
namespace IntrinsicRelatorLevels

open Presentation Presentation.Declaration RussellTarski

/-- Map a relational iota witness through a universe-head substitution. -/
def mapRelatorIotaEvidence
    (map : Tower.Head → Tower.Head)
    {n : Nat}
    {left right : Tower.Tm n}
    (evidence : IntrinsicRelator.IotaEvidence n left right) :
    IntrinsicRelator.IotaEvidence n (left.mapHead map) (right.mapHead map) := by
  cases evidence with
  | nil => exact .nil _ _ _ _ _ _
  | cons => exact .cons _ _ _ _ _ _ _ _ _ _ _ _

/-- Map either retained List or retained relational evidence. -/
def mapCombinedIotaEvidence
    (map : Tower.Head → Tower.Head)
    {n : Nat}
    {left right : Tower.Tm n}
    (evidence : IntrinsicRelator.CombinedIotaEvidence n left right) :
    IntrinsicRelator.CombinedIotaEvidence n
      (left.mapHead map) (right.mapHead map) := by
  cases evidence with
  | list evidence =>
      exact .list (IntrinsicMaps.mapIotaEvidence map evidence)
  | rel evidence =>
      exact .rel (mapRelatorIotaEvidence map evidence)

/-- Instantiate the complete List/relator signature at one universe level. -/
def levelInstance (level : LevelExpr Nat) :
    LevelInstance IntrinsicRelator.rawSignature
      (IntrinsicMaps.sameLevelSubstitution level) where
  computation := IntrinsicRelator.combinedProofRelevantIotaComputation.support
  computationMap := by
    intro n left right step
    rcases step with ⟨evidence⟩
    exact ⟨mapCombinedIotaEvidence
      (substLevelsHead (IntrinsicMaps.sameLevelSubstitution level)) evidence⟩

def signatureAt (level : LevelExpr Nat) : Signature Tower.Head :=
  (levelInstance level).signature

def rulesAt (level : LevelExpr Nat) : Rules Tower.Head :=
  (levelInstance level).rules

/-- Level instantiation retains formation of the complete signature. -/
theorem signatureAt_formed (level : LevelExpr Nat) :
    (signatureAt level).Formed Tower.rules :=
  (levelInstance level).formed IntrinsicRelator.rawSignature_formed

@[simp] theorem signatureAt_value_none (level : LevelExpr Nat)
    (name : DeclName) : (signatureAt level).valueOf? name = none := by
  simp [signatureAt, LevelInstance.signature,
    IntrinsicRelator.rawSignature_valueOf_none]

/-- The finite relational root code is level-insensitive: its retained terms
already live in the requested ambient syntax. -/
def rootDecoder (level : LevelExpr Nat) :
    StructuralConversionCode.RootDecoder (rulesAt level).computation where
  Code := NativeRelatorRootConversionCode.Code
  decode := NativeRelatorRootConversionCode.decode
  sound := by
    intro n code left right decoded
    cases code with
    | indexed code =>
        cases code <;> cases Option.some.inj decoded <;>
          exact RootStep.declared ⟨.list (by constructor)⟩
    | relNil source target relation motive nilCase consCase =>
        cases Option.some.inj decoded
        exact RootStep.declared ⟨.rel (.nil _ _ _ _ _ _)⟩
    | relCons source target relation motive nilCase consCase sourceHead targetHead
        sourceTail targetTail headEvidence tailEvidence =>
        cases Option.some.inj decoded
        exact RootStep.declared
          ⟨.rel (.cons _ _ _ _ _ _ _ _ _ _ _ _)⟩
  complete := by
    intro n left right step
    cases step with
    | inherited impossible => exact impossible.elim
    | @delta name value unfolding =>
        change (signatureAt level).valueOf? name = some value at unfolding
        rw [signatureAt_value_none] at unfolding
        cases unfolding
    | declared retained =>
        obtain ⟨evidence⟩ := retained
        exact ⟨NativeRelatorRootConversionCode.encodeEvidence evidence,
          NativeRelatorRootConversionCode.decode_evidence evidence⟩

#print axioms mapRelatorIotaEvidence
#print axioms mapCombinedIotaEvidence
#print axioms levelInstance
#print axioms signatureAt_formed
#print axioms rootDecoder

end IntrinsicRelatorLevels
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeIndexedFamilies

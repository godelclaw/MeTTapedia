import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorAnnotated
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.InductivePackage

/-! Generated annotated proof source; each theorem is checked by Lean. -/

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies.Programs.Annotated.Evidence

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Annotated

variable (enabled : ComputationProfiles.Selection)

local instance : DecidableRel (ComputationProfiles.rules enabled).headTyping := fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred (ComputationProfiles.rules enabled).isUniverse := fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable ((ComputationProfiles.rules enabled).join u v w) := fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel (ComputationProfiles.rules enabled).cumulative := fun u v => inferInstanceAs (Decidable (Tower.rules.cumulative u v))

private def e0 : Tower.Ctx 0 :=
.nil

private def e1 : Tower.Tm 0 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0))

private def e2 : Tower.Tm 0 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)))

private theorem e3 : CTyped (church enabled) (liftCtx e0) (liftTm e1) (liftTm e2) :=
.headType (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e4 : Tower.Tm 0 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat

private theorem e5 : CTyped (church enabled) (liftCtx e0) (liftTm e4) (liftTm e1) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e3 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e6 : Tower.Ctx 1 :=
.snoc e0 e4

private def e7 : Tower.Tm 1 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat

private def e8 : Tower.Tm 1 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0))

private theorem e9 : CTyped (church enabled) (liftCtx e6) (liftTm e7) (liftTm e8) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e3 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e10 : Tower.Tm 0 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)

private def e11 : Tower.Tm 0 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)))

private theorem e12 : CTyped (church enabled) (liftCtx e0) (liftTm e10) (liftTm e11) :=
.piForm (e5 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e9 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e13 : Tower.Tm 1 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1)))

private def e14 : Tower.Tm 1 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))))

private theorem e15 : CTyped (church enabled) (liftCtx e6) (liftTm e13) (liftTm e14) :=
.headType (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e16 : Tower.Tm 0 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))))

private def e17 : Tower.Tm 0 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1)))))

private theorem e18 : CTyped (church enabled) (liftCtx e0) (liftTm e16) (liftTm e17) :=
.piForm (e5 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e15 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e19 : Tower.Ctx 1 :=
.snoc e0 e16

private def e20 : Tower.Tm 1 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0

private def e21 : Tower.Tm 1 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))))

private theorem e22 : CTyped (church enabled) (liftCtx e19) (liftTm e20) (liftTm e21) :=
by
  change CTyped (church enabled) (liftCtx e19) (.var 0) (liftTm (Ctx.lookup e19 0))
  rw [← liftCtx_lookup]
  exact .var 0

private def e23 : Tower.Tm 1 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero

private theorem e24 : CTyped (church enabled) (liftCtx e19) (liftTm e23) (liftTm e7) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e5 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e25 : Tower.Tm 2 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1)))

private def e26 : Tower.Tm 1 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero)

private theorem e27 : CTyped (church enabled) (liftCtx e19) (liftTm e26) (liftTm e13) :=
by
  change CTyped (church enabled) (liftCtx e19) (.app (liftTm e20) (liftTm e23)) (liftTm (inst0 e23 e25))
  rw [liftTm_inst0]
  exact .appElim (e22 enabled) (e24 enabled)

private def e28 : Tower.Ctx 2 :=
.snoc e19 e26

private def e29 : Tower.Tm 2 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat

private def e30 : Tower.Tm 2 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0))

private theorem e31 : CTyped (church enabled) (liftCtx e28) (liftTm e29) (liftTm e30) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e3 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e32 : Tower.Ctx 3 :=
.snoc e28 e29

private def e33 : Tower.Tm 3 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2

private def e34 : Tower.Tm 3 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))))

private theorem e35 : CTyped (church enabled) (liftCtx e32) (liftTm e33) (liftTm e34) :=
by
  change CTyped (church enabled) (liftCtx e32) (.var 2) (liftTm (Ctx.lookup e32 2))
  rw [← liftCtx_lookup]
  exact .var 2

private def e36 : Tower.Tm 3 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0

private def e37 : Tower.Tm 3 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat

private theorem e38 : CTyped (church enabled) (liftCtx e32) (liftTm e36) (liftTm e37) :=
by
  change CTyped (church enabled) (liftCtx e32) (.var 0) (liftTm (Ctx.lookup e32 0))
  rw [← liftCtx_lookup]
  exact .var 0

private def e39 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1)))

private def e40 : Tower.Tm 3 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)

private def e41 : Tower.Tm 3 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1)))

private theorem e42 : CTyped (church enabled) (liftCtx e32) (liftTm e40) (liftTm e41) :=
by
  change CTyped (church enabled) (liftCtx e32) (.app (liftTm e33) (liftTm e36)) (liftTm (inst0 e36 e39))
  rw [liftTm_inst0]
  exact .appElim (e35 enabled) (e38 enabled)

private def e43 : Tower.Ctx 4 :=
.snoc e32 e40

private def e44 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3

private def e45 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))))

private theorem e46 : CTyped (church enabled) (liftCtx e43) (liftTm e44) (liftTm e45) :=
by
  change CTyped (church enabled) (liftCtx e43) (.var 3) (liftTm (Ctx.lookup e43 3))
  rw [← liftCtx_lookup]
  exact .var 3

private def e47 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ

private def e48 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)

private theorem e49 : CTyped (church enabled) (liftCtx e43) (liftTm e47) (liftTm e48) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e12 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e50 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1

private def e51 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat

private theorem e52 : CTyped (church enabled) (liftCtx e43) (liftTm e50) (liftTm e51) :=
by
  change CTyped (church enabled) (liftCtx e43) (.var 1) (liftTm (Ctx.lookup e43 1))
  rw [← liftCtx_lookup]
  exact .var 1

private def e53 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat

private def e54 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)

private theorem e55 : CTyped (church enabled) (liftCtx e43) (liftTm e54) (liftTm e51) :=
by
  change CTyped (church enabled) (liftCtx e43) (.app (liftTm e47) (liftTm e50)) (liftTm (inst0 e50 e53))
  rw [liftTm_inst0]
  exact .appElim (e49 enabled) (e52 enabled)

private def e56 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1)))

private def e57 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))

private theorem e58 : CTyped (church enabled) (liftCtx e43) (liftTm e57) (liftTm e39) :=
by
  change CTyped (church enabled) (liftCtx e43) (.app (liftTm e44) (liftTm e54)) (liftTm (inst0 e54 e56))
  rw [liftTm_inst0]
  exact .appElim (e46 enabled) (e55 enabled)

private def e59 : Tower.Tm 3 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))

private def e60 : Tower.Tm 3 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))))

private theorem e61 : CTyped (church enabled) (liftCtx e32) (liftTm e59) (liftTm e60) :=
.piForm (e42 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e58 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e62 : Tower.Tm 2 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))))

private def e63 : Tower.Tm 2 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1)))))

private theorem e64 : CTyped (church enabled) (liftCtx e28) (liftTm e62) (liftTm e63) :=
.piForm (e31 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e61 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e65 : Tower.Ctx 3 :=
.snoc e28 e62

private def e66 : Tower.Tm 3 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0))

private theorem e67 : CTyped (church enabled) (liftCtx e65) (liftTm e37) (liftTm e66) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e3 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e68 : Tower.Ctx 4 :=
.snoc e65 e37

private theorem e69 : CTyped (church enabled) (liftCtx e68) (liftTm e44) (liftTm e45) :=
by
  change CTyped (church enabled) (liftCtx e68) (.var 3) (liftTm (Ctx.lookup e68 3))
  rw [← liftCtx_lookup]
  exact .var 3

private def e70 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0

private theorem e71 : CTyped (church enabled) (liftCtx e68) (liftTm e70) (liftTm e51) :=
by
  change CTyped (church enabled) (liftCtx e68) (.var 0) (liftTm (Ctx.lookup e68 0))
  rw [← liftCtx_lookup]
  exact .var 0

private def e72 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)

private theorem e73 : CTyped (church enabled) (liftCtx e68) (liftTm e72) (liftTm e39) :=
by
  change CTyped (church enabled) (liftCtx e68) (.app (liftTm e44) (liftTm e70)) (liftTm (inst0 e70 e56))
  rw [liftTm_inst0]
  exact .appElim (e69 enabled) (e71 enabled)

private def e74 : Tower.Tm 3 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))

private def e75 : Tower.Tm 3 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))))

private theorem e76 : CTyped (church enabled) (liftCtx e65) (liftTm e74) (liftTm e75) :=
.piForm (e67 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e73 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e77 : Tower.Tm 2 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))

private def e78 : Tower.Tm 2 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))))
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1)))))

private theorem e79 : CTyped (church enabled) (liftCtx e28) (liftTm e77) (liftTm e78) :=
.piForm (e64 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e76 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e80 : Tower.Tm 1 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))

private def e81 : Tower.Tm 1 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))))
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))))))

private theorem e82 : CTyped (church enabled) (liftCtx e19) (liftTm e80) (liftTm e81) :=
.piForm (e27 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e79 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e83 : Tower.Tm 0 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1)))))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))))

private def e84 : Tower.Tm 0 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))))
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
                (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
                (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
                (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
                (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))))
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1)))))))

private theorem e85 : CTyped (church enabled) (liftCtx e0) (liftTm e83) (liftTm e84) :=
.piForm (e18 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e82 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e86 : Tower.Tm 0 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))

private def e87 : Tower.Tm 0 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))

private theorem e88 : CTyped (church enabled) (liftCtx e0) (liftTm e86) (liftTm e87) :=
.headType (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e89 : Tower.Ctx 1 :=
.snoc e0 e86

private theorem e90 : CTyped (church enabled) (liftCtx e89) (liftTm e7) (liftTm e8) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e3 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e91 : Tower.Ctx 2 :=
.snoc e89 e7

private def e92 : Tower.Tm 2 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))

private def e93 : Tower.Tm 2 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))

private theorem e94 : CTyped (church enabled) (liftCtx e91) (liftTm e92) (liftTm e93) :=
.headType (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e95 : Tower.Tm 1 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))

private def e96 : Tower.Tm 1 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))

private theorem e97 : CTyped (church enabled) (liftCtx e89) (liftTm e95) (liftTm e96) :=
.piForm (e90 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e94 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e98 : Tower.Tm 0 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))

private def e99 : Tower.Tm 0 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))

private theorem e100 : CTyped (church enabled) (liftCtx e0) (liftTm e98) (liftTm e99) :=
.piForm (e88 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e97 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e101 : Tower.Tm 1 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec

private def e102 : Tower.Tm 1 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))

private theorem e103 : CTyped (church enabled) (liftCtx e89) (liftTm e101) (liftTm e102) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e100 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e104 : Tower.Tm 1 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))

private theorem e105 : CTyped (church enabled) (liftCtx e89) (liftTm e20) (liftTm e104) :=
by
  change CTyped (church enabled) (liftCtx e89) (.var 0) (liftTm (Ctx.lookup e89 0))
  rw [← liftCtx_lookup]
  exact .var 0

private def e106 : Tower.Tm 2 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))

private def e107 : Tower.Tm 1 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)

private theorem e108 : CTyped (church enabled) (liftCtx e89) (liftTm e107) (liftTm e95) :=
by
  change CTyped (church enabled) (liftCtx e89) (.app (liftTm e101) (liftTm e20)) (liftTm (inst0 e20 e106))
  rw [liftTm_inst0]
  exact .appElim (e103 enabled) (e105 enabled)

private theorem e109 : CTyped (church enabled) (liftCtx e89) (liftTm e23) (liftTm e7) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e5 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e110 : Tower.Tm 1 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero)

private theorem e111 : CTyped (church enabled) (liftCtx e89) (liftTm e110) (liftTm e104) :=
by
  change CTyped (church enabled) (liftCtx e89) (.app (liftTm e107) (liftTm e23)) (liftTm (inst0 e23 e92))
  rw [liftTm_inst0]
  exact .appElim (e108 enabled) (e109 enabled)

private def e112 : Tower.Tm 0 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero))

private def e113 : Tower.Tm 0 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))

private theorem e114 : CTyped (church enabled) (liftCtx e0) (liftTm e112) (liftTm e113) :=
.piForm (e88 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e111 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e115 : Tower.Tm 2 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1

private theorem e116 : CTyped (church enabled) (liftCtx e91) (liftTm e115) (liftTm e92) :=
by
  change CTyped (church enabled) (liftCtx e91) (.var 1) (liftTm (Ctx.lookup e91 1))
  rw [← liftCtx_lookup]
  exact .var 1

private def e117 : Tower.Ctx 3 :=
.snoc e91 e115

private def e118 : Tower.Tm 3 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec

private def e119 : Tower.Tm 3 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))

private theorem e120 : CTyped (church enabled) (liftCtx e117) (liftTm e118) (liftTm e119) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e100 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e121 : Tower.Tm 3 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))

private theorem e122 : CTyped (church enabled) (liftCtx e117) (liftTm e33) (liftTm e121) :=
by
  change CTyped (church enabled) (liftCtx e117) (.var 2) (liftTm (Ctx.lookup e117 2))
  rw [← liftCtx_lookup]
  exact .var 2

private def e123 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))

private def e124 : Tower.Tm 3 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2)

private def e125 : Tower.Tm 3 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))

private theorem e126 : CTyped (church enabled) (liftCtx e117) (liftTm e124) (liftTm e125) :=
by
  change CTyped (church enabled) (liftCtx e117) (.app (liftTm e118) (liftTm e33)) (liftTm (inst0 e33 e123))
  rw [liftTm_inst0]
  exact .appElim (e120 enabled) (e122 enabled)

private def e127 : Tower.Tm 3 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1

private theorem e128 : CTyped (church enabled) (liftCtx e117) (liftTm e127) (liftTm e37) :=
by
  change CTyped (church enabled) (liftCtx e117) (.var 1) (liftTm (Ctx.lookup e117 1))
  rw [← liftCtx_lookup]
  exact .var 1

private def e129 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))

private def e130 : Tower.Tm 3 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)

private theorem e131 : CTyped (church enabled) (liftCtx e117) (liftTm e130) (liftTm e121) :=
by
  change CTyped (church enabled) (liftCtx e117) (.app (liftTm e124) (liftTm e127)) (liftTm (inst0 e127 e129))
  rw [liftTm_inst0]
  exact .appElim (e126 enabled) (e128 enabled)

private def e132 : Tower.Ctx 4 :=
.snoc e117 e130

private def e133 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec

private def e134 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))

private theorem e135 : CTyped (church enabled) (liftCtx e132) (liftTm e133) (liftTm e134) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e100 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e136 : CTyped (church enabled) (liftCtx e132) (liftTm e44) (liftTm e129) :=
by
  change CTyped (church enabled) (liftCtx e132) (.var 3) (liftTm (Ctx.lookup e132 3))
  rw [← liftCtx_lookup]
  exact .var 3

private def e137 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))

private def e138 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)

private theorem e139 : CTyped (church enabled) (liftCtx e132) (liftTm e138) (liftTm e123) :=
by
  change CTyped (church enabled) (liftCtx e132) (.app (liftTm e133) (liftTm e44)) (liftTm (inst0 e44 e137))
  rw [liftTm_inst0]
  exact .appElim (e135 enabled) (e136 enabled)

private theorem e140 : CTyped (church enabled) (liftCtx e132) (liftTm e47) (liftTm e48) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e12 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e141 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2

private theorem e142 : CTyped (church enabled) (liftCtx e132) (liftTm e141) (liftTm e51) :=
by
  change CTyped (church enabled) (liftCtx e132) (.var 2) (liftTm (Ctx.lookup e132 2))
  rw [← liftCtx_lookup]
  exact .var 2

private def e143 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2)

private theorem e144 : CTyped (church enabled) (liftCtx e132) (liftTm e143) (liftTm e51) :=
by
  change CTyped (church enabled) (liftCtx e132) (.app (liftTm e47) (liftTm e141)) (liftTm (inst0 e141 e53))
  rw [liftTm_inst0]
  exact .appElim (e140 enabled) (e142 enabled)

private def e145 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))

private def e146 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))

private theorem e147 : CTyped (church enabled) (liftCtx e132) (liftTm e146) (liftTm e129) :=
by
  change CTyped (church enabled) (liftCtx e132) (.app (liftTm e138) (liftTm e143)) (liftTm (inst0 e143 e145))
  rw [liftTm_inst0]
  exact .appElim (e139 enabled) (e144 enabled)

private def e148 : Tower.Tm 3 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2)))

private def e149 : Tower.Tm 3 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))

private theorem e150 : CTyped (church enabled) (liftCtx e117) (liftTm e148) (liftTm e149) :=
.piForm (e131 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e147 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e151 : Tower.Tm 2 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))))

private def e152 : Tower.Tm 2 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))

private theorem e153 : CTyped (church enabled) (liftCtx e91) (liftTm e151) (liftTm e152) :=
.piForm (e116 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e150 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e154 : Tower.Tm 1 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2)))))

private def e155 : Tower.Tm 1 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))

private theorem e156 : CTyped (church enabled) (liftCtx e89) (liftTm e154) (liftTm e155) :=
.piForm (e90 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e153 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e157 : Tower.Tm 0 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))))))

private def e158 : Tower.Tm 0 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))))

private theorem e159 : CTyped (church enabled) (liftCtx e0) (liftTm e157) (liftTm e158) :=
.piForm (e88 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e156 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e160 : Tower.Tm 2 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec

private def e161 : Tower.Tm 2 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))

private theorem e162 : CTyped (church enabled) (liftCtx e91) (liftTm e160) (liftTm e161) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e100 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e163 : Tower.Tm 2 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)

private theorem e164 : CTyped (church enabled) (liftCtx e91) (liftTm e163) (liftTm e106) :=
by
  change CTyped (church enabled) (liftCtx e91) (.app (liftTm e160) (liftTm e115)) (liftTm (inst0 e115 e125))
  rw [liftTm_inst0]
  exact .appElim (e162 enabled) (e116 enabled)

private def e165 : Tower.Tm 2 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0

private theorem e166 : CTyped (church enabled) (liftCtx e91) (liftTm e165) (liftTm e29) :=
by
  change CTyped (church enabled) (liftCtx e91) (.var 0) (liftTm (Ctx.lookup e91 0))
  rw [← liftCtx_lookup]
  exact .var 0

private def e167 : Tower.Tm 2 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)

private theorem e168 : CTyped (church enabled) (liftCtx e91) (liftTm e167) (liftTm e92) :=
by
  change CTyped (church enabled) (liftCtx e91) (.app (liftTm e163) (liftTm e165)) (liftTm (inst0 e165 e121))
  rw [liftTm_inst0]
  exact .appElim (e164 enabled) (e166 enabled)

private def e169 : Tower.Ctx 3 :=
.snoc e91 e167

private def e170 : Tower.Tm 3 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))))

private theorem e171 : CTyped (church enabled) (liftCtx e169) (liftTm e41) (liftTm e170) :=
.headType (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e172 : Tower.Tm 2 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))))

private def e173 : Tower.Tm 2 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1)))))

private theorem e174 : CTyped (church enabled) (liftCtx e91) (liftTm e172) (liftTm e173) :=
.piForm (e168 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e171 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e175 : Tower.Tm 1 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1)))))

private def e176 : Tower.Tm 1 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))))))

private theorem e177 : CTyped (church enabled) (liftCtx e89) (liftTm e175) (liftTm e176) :=
.piForm (e90 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e174 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e178 : Tower.Ctx 2 :=
.snoc e89 e175

private def e179 : Tower.Tm 2 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1)))))

private theorem e180 : CTyped (church enabled) (liftCtx e178) (liftTm e165) (liftTm e179) :=
by
  change CTyped (church enabled) (liftCtx e178) (.var 0) (liftTm (Ctx.lookup e178 0))
  rw [← liftCtx_lookup]
  exact .var 0

private def e181 : Tower.Tm 2 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero

private theorem e182 : CTyped (church enabled) (liftCtx e178) (liftTm e181) (liftTm e29) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e5 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e183 : Tower.Tm 3 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))))

private def e184 : Tower.Tm 2 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero)

private def e185 : Tower.Tm 2 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))))

private theorem e186 : CTyped (church enabled) (liftCtx e178) (liftTm e184) (liftTm e185) :=
by
  change CTyped (church enabled) (liftCtx e178) (.app (liftTm e165) (liftTm e181)) (liftTm (inst0 e181 e183))
  rw [liftTm_inst0]
  exact .appElim (e180 enabled) (e182 enabled)

private def e187 : Tower.Tm 2 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.nil

private def e188 : Tower.Tm 2 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero))

private theorem e189 : CTyped (church enabled) (liftCtx e178) (liftTm e187) (liftTm e188) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e114 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e190 : CTyped (church enabled) (liftCtx e178) (liftTm e115) (liftTm e92) :=
by
  change CTyped (church enabled) (liftCtx e178) (.var 1) (liftTm (Ctx.lookup e178 1))
  rw [← liftCtx_lookup]
  exact .var 1

private def e191 : Tower.Tm 3 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero)

private def e192 : Tower.Tm 2 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.nil)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)

private def e193 : Tower.Tm 2 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero)

private theorem e194 : CTyped (church enabled) (liftCtx e178) (liftTm e192) (liftTm e193) :=
by
  change CTyped (church enabled) (liftCtx e178) (.app (liftTm e187) (liftTm e115)) (liftTm (inst0 e115 e191))
  rw [liftTm_inst0]
  exact .appElim (e189 enabled) (e190 enabled)

private def e195 : Tower.Tm 2 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.nil)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))

private theorem e196 : CTyped (church enabled) (liftCtx e178) (liftTm e195) (liftTm e25) :=
by
  change CTyped (church enabled) (liftCtx e178) (.app (liftTm e184) (liftTm e192)) (liftTm (inst0 e192 e41))
  rw [liftTm_inst0]
  exact .appElim (e186 enabled) (e194 enabled)

private def e197 : Tower.Ctx 3 :=
.snoc e178 e195

private theorem e198 : CTyped (church enabled) (liftCtx e197) (liftTm e37) (liftTm e66) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e3 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e199 : Tower.Ctx 4 :=
.snoc e197 e37

private theorem e200 : CTyped (church enabled) (liftCtx e199) (liftTm e44) (liftTm e129) :=
by
  change CTyped (church enabled) (liftCtx e199) (.var 3) (liftTm (Ctx.lookup e199 3))
  rw [← liftCtx_lookup]
  exact .var 3

private def e201 : Tower.Ctx 5 :=
.snoc e199 e44

private def e202 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec

private def e203 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))

private theorem e204 : CTyped (church enabled) (liftCtx e201) (liftTm e202) (liftTm e203) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e100 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e205 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4

private theorem e206 : CTyped (church enabled) (liftCtx e201) (liftTm e205) (liftTm e145) :=
by
  change CTyped (church enabled) (liftCtx e201) (.var 4) (liftTm (Ctx.lookup e201 4))
  rw [← liftCtx_lookup]
  exact .var 4

private def e207 : Tower.Tm 6 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))

private def e208 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)

private theorem e209 : CTyped (church enabled) (liftCtx e201) (liftTm e208) (liftTm e137) :=
by
  change CTyped (church enabled) (liftCtx e201) (.app (liftTm e202) (liftTm e205)) (liftTm (inst0 e205 e207))
  rw [liftTm_inst0]
  exact .appElim (e204 enabled) (e206 enabled)

private def e210 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1

private theorem e211 : CTyped (church enabled) (liftCtx e201) (liftTm e210) (liftTm e53) :=
by
  change CTyped (church enabled) (liftCtx e201) (.var 1) (liftTm (Ctx.lookup e201 1))
  rw [← liftCtx_lookup]
  exact .var 1

private def e212 : Tower.Tm 6 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))

private def e213 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)

private theorem e214 : CTyped (church enabled) (liftCtx e201) (liftTm e213) (liftTm e145) :=
by
  change CTyped (church enabled) (liftCtx e201) (.app (liftTm e208) (liftTm e210)) (liftTm (inst0 e210 e212))
  rw [liftTm_inst0]
  exact .appElim (e209 enabled) (e211 enabled)

private def e215 : Tower.Ctx 6 :=
.snoc e201 e213

private def e216 : Tower.Tm 6 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4

private def e217 : Tower.Tm 6 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1)))))

private theorem e218 : CTyped (church enabled) (liftCtx e215) (liftTm e216) (liftTm e217) :=
by
  change CTyped (church enabled) (liftCtx e215) (.var 4) (liftTm (Ctx.lookup e215 4))
  rw [← liftCtx_lookup]
  exact .var 4

private def e219 : Tower.Tm 6 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2

private def e220 : Tower.Tm 6 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat

private theorem e221 : CTyped (church enabled) (liftCtx e215) (liftTm e219) (liftTm e220) :=
by
  change CTyped (church enabled) (liftCtx e215) (.var 2) (liftTm (Ctx.lookup e215 2))
  rw [← liftCtx_lookup]
  exact .var 2

private def e222 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))))

private def e223 : Tower.Tm 6 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2)

private def e224 : Tower.Tm 6 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))))

private theorem e225 : CTyped (church enabled) (liftCtx e215) (liftTm e223) (liftTm e224) :=
by
  change CTyped (church enabled) (liftCtx e215) (.app (liftTm e216) (liftTm e219)) (liftTm (inst0 e219 e222))
  rw [liftTm_inst0]
  exact .appElim (e218 enabled) (e221 enabled)

private def e226 : Tower.Tm 6 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0

private def e227 : Tower.Tm 6 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2)

private theorem e228 : CTyped (church enabled) (liftCtx e215) (liftTm e226) (liftTm e227) :=
by
  change CTyped (church enabled) (liftCtx e215) (.var 0) (liftTm (Ctx.lookup e215 0))
  rw [← liftCtx_lookup]
  exact .var 0

private def e229 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1)))

private def e230 : Tower.Tm 6 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)

private def e231 : Tower.Tm 6 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1)))

private theorem e232 : CTyped (church enabled) (liftCtx e215) (liftTm e230) (liftTm e231) :=
by
  change CTyped (church enabled) (liftCtx e215) (.app (liftTm e223) (liftTm e226)) (liftTm (inst0 e226 e229))
  rw [liftTm_inst0]
  exact .appElim (e225 enabled) (e228 enabled)

private def e233 : Tower.Ctx 7 :=
.snoc e215 e230

private def e234 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5

private def e235 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1)))))

private theorem e236 : CTyped (church enabled) (liftCtx e233) (liftTm e234) (liftTm e235) :=
by
  change CTyped (church enabled) (liftCtx e233) (.var 5) (liftTm (Ctx.lookup e233 5))
  rw [← liftCtx_lookup]
  exact .var 5

private def e237 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ

private def e238 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)

private theorem e239 : CTyped (church enabled) (liftCtx e233) (liftTm e237) (liftTm e238) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e12 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e240 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3

private def e241 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat

private theorem e242 : CTyped (church enabled) (liftCtx e233) (liftTm e240) (liftTm e241) :=
by
  change CTyped (church enabled) (liftCtx e233) (.var 3) (liftTm (Ctx.lookup e233 3))
  rw [← liftCtx_lookup]
  exact .var 3

private def e243 : Tower.Tm 8 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat

private def e244 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)

private theorem e245 : CTyped (church enabled) (liftCtx e233) (liftTm e244) (liftTm e241) :=
by
  change CTyped (church enabled) (liftCtx e233) (.app (liftTm e237) (liftTm e240)) (liftTm (inst0 e240 e243))
  rw [liftTm_inst0]
  exact .appElim (e239 enabled) (e242 enabled)

private def e246 : Tower.Tm 8 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))))

private def e247 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))

private def e248 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))))

private theorem e249 : CTyped (church enabled) (liftCtx e233) (liftTm e247) (liftTm e248) :=
by
  change CTyped (church enabled) (liftCtx e233) (.app (liftTm e234) (liftTm e244)) (liftTm (inst0 e244 e246))
  rw [liftTm_inst0]
  exact .appElim (e236 enabled) (e245 enabled)

private def e250 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.cons

private def e251 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))))))

private theorem e252 : CTyped (church enabled) (liftCtx e233) (liftTm e250) (liftTm e251) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e159 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e253 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6

private def e254 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))

private theorem e255 : CTyped (church enabled) (liftCtx e233) (liftTm e253) (liftTm e254) :=
by
  change CTyped (church enabled) (liftCtx e233) (.var 6) (liftTm (Ctx.lookup e233 6))
  rw [← liftCtx_lookup]
  exact .var 6

private def e256 : Tower.Tm 8 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2)))))

private def e257 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.cons)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)

private def e258 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 9))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2)))))

private theorem e259 : CTyped (church enabled) (liftCtx e233) (liftTm e257) (liftTm e258) :=
by
  change CTyped (church enabled) (liftCtx e233) (.app (liftTm e250) (liftTm e253)) (liftTm (inst0 e253 e256))
  rw [liftTm_inst0]
  exact .appElim (e252 enabled) (e255 enabled)

private def e260 : Tower.Tm 8 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 9))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))))

private def e261 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.cons)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)

private def e262 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5))))

private theorem e263 : CTyped (church enabled) (liftCtx e233) (liftTm e261) (liftTm e262) :=
by
  change CTyped (church enabled) (liftCtx e233) (.app (liftTm e257) (liftTm e240)) (liftTm (inst0 e240 e260))
  rw [liftTm_inst0]
  exact .appElim (e259 enabled) (e242 enabled)

private def e264 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2

private theorem e265 : CTyped (church enabled) (liftCtx e233) (liftTm e264) (liftTm e253) :=
by
  change CTyped (church enabled) (liftCtx e233) (.var 2) (liftTm (Ctx.lookup e233 2))
  rw [← liftCtx_lookup]
  exact .var 2

private def e266 : Tower.Tm 8 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)))

private def e267 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.cons)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2)

private def e268 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)))

private theorem e269 : CTyped (church enabled) (liftCtx e233) (liftTm e267) (liftTm e268) :=
by
  change CTyped (church enabled) (liftCtx e233) (.app (liftTm e261) (liftTm e264)) (liftTm (inst0 e264 e266))
  rw [liftTm_inst0]
  exact .appElim (e263 enabled) (e265 enabled)

private def e270 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1

private def e271 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)

private theorem e272 : CTyped (church enabled) (liftCtx e233) (liftTm e270) (liftTm e271) :=
by
  change CTyped (church enabled) (liftCtx e233) (.var 1) (liftTm (Ctx.lookup e233 1))
  rw [← liftCtx_lookup]
  exact .var 1

private def e273 : Tower.Tm 8 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))

private def e274 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.cons)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)

private def e275 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))

private theorem e276 : CTyped (church enabled) (liftCtx e233) (liftTm e274) (liftTm e275) :=
by
  change CTyped (church enabled) (liftCtx e233) (.app (liftTm e267) (liftTm e270)) (liftTm (inst0 e270 e273))
  rw [liftTm_inst0]
  exact .appElim (e269 enabled) (e272 enabled)

private def e277 : Tower.Tm 8 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1)))

private def e278 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.cons)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))

private theorem e279 : CTyped (church enabled) (liftCtx e233) (liftTm e278) (liftTm e229) :=
by
  change CTyped (church enabled) (liftCtx e233) (.app (liftTm e247) (liftTm e274)) (liftTm (inst0 e274 e277))
  rw [liftTm_inst0]
  exact .appElim (e249 enabled) (e276 enabled)

private def e280 : Tower.Tm 6 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.cons)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))

private def e281 : Tower.Tm 6 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))))

private theorem e282 : CTyped (church enabled) (liftCtx e215) (liftTm e280) (liftTm e281) :=
.piForm (e232 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e279 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e283 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.cons)
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))))

private def e284 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1)))))

private theorem e285 : CTyped (church enabled) (liftCtx e201) (liftTm e283) (liftTm e284) :=
.piForm (e214 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e282 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e286 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.cons)
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))))

private def e287 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))))))

private theorem e288 : CTyped (church enabled) (liftCtx e199) (liftTm e286) (liftTm e287) :=
.piForm (e200 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e285 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e289 : Tower.Tm 3 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.cons)
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))))))

private def e290 : Tower.Tm 3 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1)))))))

private theorem e291 : CTyped (church enabled) (liftCtx e197) (liftTm e289) (liftTm e290) :=
.piForm (e198 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e288 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e292 : Tower.Ctx 4 :=
.snoc e197 e289

private def e293 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0))

private theorem e294 : CTyped (church enabled) (liftCtx e292) (liftTm e51) (liftTm e293) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e3 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e295 : Tower.Ctx 5 :=
.snoc e292 e51

private theorem e296 : CTyped (church enabled) (liftCtx e295) (liftTm e202) (liftTm e203) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e100 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e297 : CTyped (church enabled) (liftCtx e295) (liftTm e205) (liftTm e145) :=
by
  change CTyped (church enabled) (liftCtx e295) (.var 4) (liftTm (Ctx.lookup e295 4))
  rw [← liftCtx_lookup]
  exact .var 4

private theorem e298 : CTyped (church enabled) (liftCtx e295) (liftTm e208) (liftTm e137) :=
by
  change CTyped (church enabled) (liftCtx e295) (.app (liftTm e202) (liftTm e205)) (liftTm (inst0 e205 e207))
  rw [liftTm_inst0]
  exact .appElim (e296 enabled) (e297 enabled)

private def e299 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0

private theorem e300 : CTyped (church enabled) (liftCtx e295) (liftTm e299) (liftTm e53) :=
by
  change CTyped (church enabled) (liftCtx e295) (.var 0) (liftTm (Ctx.lookup e295 0))
  rw [← liftCtx_lookup]
  exact .var 0

private def e301 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)

private theorem e302 : CTyped (church enabled) (liftCtx e295) (liftTm e301) (liftTm e145) :=
by
  change CTyped (church enabled) (liftCtx e295) (.app (liftTm e208) (liftTm e299)) (liftTm (inst0 e299 e212))
  rw [liftTm_inst0]
  exact .appElim (e298 enabled) (e300 enabled)

private def e303 : Tower.Ctx 6 :=
.snoc e295 e301

private theorem e304 : CTyped (church enabled) (liftCtx e303) (liftTm e216) (liftTm e217) :=
by
  change CTyped (church enabled) (liftCtx e303) (.var 4) (liftTm (Ctx.lookup e303 4))
  rw [← liftCtx_lookup]
  exact .var 4

private def e305 : Tower.Tm 6 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1

private theorem e306 : CTyped (church enabled) (liftCtx e303) (liftTm e305) (liftTm e220) :=
by
  change CTyped (church enabled) (liftCtx e303) (.var 1) (liftTm (Ctx.lookup e303 1))
  rw [← liftCtx_lookup]
  exact .var 1

private def e307 : Tower.Tm 6 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)

private def e308 : Tower.Tm 6 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))))

private theorem e309 : CTyped (church enabled) (liftCtx e303) (liftTm e307) (liftTm e308) :=
by
  change CTyped (church enabled) (liftCtx e303) (.app (liftTm e216) (liftTm e305)) (liftTm (inst0 e305 e222))
  rw [liftTm_inst0]
  exact .appElim (e304 enabled) (e306 enabled)

private def e310 : Tower.Tm 6 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)

private theorem e311 : CTyped (church enabled) (liftCtx e303) (liftTm e226) (liftTm e310) :=
by
  change CTyped (church enabled) (liftCtx e303) (.var 0) (liftTm (Ctx.lookup e303 0))
  rw [← liftCtx_lookup]
  exact .var 0

private def e312 : Tower.Tm 6 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)

private theorem e313 : CTyped (church enabled) (liftCtx e303) (liftTm e312) (liftTm e231) :=
by
  change CTyped (church enabled) (liftCtx e303) (.app (liftTm e307) (liftTm e226)) (liftTm (inst0 e226 e229))
  rw [liftTm_inst0]
  exact .appElim (e309 enabled) (e311 enabled)

private def e314 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))

private def e315 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))))

private theorem e316 : CTyped (church enabled) (liftCtx e295) (liftTm e314) (liftTm e315) :=
.piForm (e302 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e313 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e317 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))

private def e318 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1)))))

private theorem e319 : CTyped (church enabled) (liftCtx e292) (liftTm e317) (liftTm e318) :=
.piForm (e294 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e316 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e320 : Tower.Tm 3 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                      `CumulativeTower.Vec.cons)
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))))))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))

private def e321 : Tower.Tm 3 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
                (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
                (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
                (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
                (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))))))
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))))))

private theorem e322 : CTyped (church enabled) (liftCtx e197) (liftTm e320) (liftTm e321) :=
.piForm (e291 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e319 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e323 : Tower.Tm 2 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.nil)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                        `CumulativeTower.Vec.cons)
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))))))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))))

private def e324 : Tower.Tm 2 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
                (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
                  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
                  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))
                (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
                  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
                  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))))))
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1)))))))

private theorem e325 : CTyped (church enabled) (liftCtx e178) (liftTm e323) (liftTm e324) :=
.piForm (e196 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e322 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e326 : Tower.Tm 1 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))))))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.nil)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                      `CumulativeTower.Nat.succ)
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)))
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                          `CumulativeTower.Vec.cons)
                        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))))))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))))

private def e327 : Tower.Tm 1 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1)))))
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
                (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
                (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
                  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
                    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
                    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))
                  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
                    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
                    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))))))
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
                (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
                (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))))))))

private theorem e328 : CTyped (church enabled) (liftCtx e89) (liftTm e326) (liftTm e327) :=
.piForm (e177 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e325 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e329 : Tower.Tm 0 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))))))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.nil)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                        `CumulativeTower.Nat.succ)
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)))
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                            `CumulativeTower.Vec.cons)
                          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
                        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))))))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))))))

private def e330 : Tower.Tm 0 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
                (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
                (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1)))))
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
                (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
                (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
                  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
                  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
                    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
                      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
                      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))
                    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
                      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
                      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))))))
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
                (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
                (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
                  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
                  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1)))))))))

private theorem e331 : CTyped (church enabled) (liftCtx e0) (liftTm e329) (liftTm e330) :=
.piForm (e88 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e328 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e332 : Tower.Tm 3 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.eliminate

private def e333 : Tower.Tm 3 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1)))))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))))

private theorem e334 : CTyped (church enabled) (liftCtx e65) (liftTm e332) (liftTm e333) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e85 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e335 : CTyped (church enabled) (liftCtx e65) (liftTm e33) (liftTm e34) :=
by
  change CTyped (church enabled) (liftCtx e65) (.var 2) (liftTm (Ctx.lookup e65 2))
  rw [← liftCtx_lookup]
  exact .var 2

private def e336 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))

private def e337 : Tower.Tm 3 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.eliminate)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2)

private def e338 : Tower.Tm 3 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))

private theorem e339 : CTyped (church enabled) (liftCtx e65) (liftTm e337) (liftTm e338) :=
by
  change CTyped (church enabled) (liftCtx e65) (.app (liftTm e332) (liftTm e33)) (liftTm (inst0 e33 e336))
  rw [liftTm_inst0]
  exact .appElim (e334 enabled) (e335 enabled)

private def e340 : Tower.Tm 3 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero)

private theorem e341 : CTyped (church enabled) (liftCtx e65) (liftTm e127) (liftTm e340) :=
by
  change CTyped (church enabled) (liftCtx e65) (.var 1) (liftTm (Ctx.lookup e65 1))
  rw [← liftCtx_lookup]
  exact .var 1

private def e342 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))

private def e343 : Tower.Tm 3 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.eliminate)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)

private def e344 : Tower.Tm 3 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))

private theorem e345 : CTyped (church enabled) (liftCtx e65) (liftTm e343) (liftTm e344) :=
by
  change CTyped (church enabled) (liftCtx e65) (.app (liftTm e337) (liftTm e127)) (liftTm (inst0 e127 e342))
  rw [liftTm_inst0]
  exact .appElim (e339 enabled) (e341 enabled)

private def e346 : Tower.Tm 3 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))))

private theorem e347 : CTyped (church enabled) (liftCtx e65) (liftTm e36) (liftTm e346) :=
by
  change CTyped (church enabled) (liftCtx e65) (.var 0) (liftTm (Ctx.lookup e65 0))
  rw [← liftCtx_lookup]
  exact .var 0

private def e348 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))

private def e349 : Tower.Tm 3 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.eliminate)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)

private theorem e350 : CTyped (church enabled) (liftCtx e65) (liftTm e349) (liftTm e74) :=
by
  change CTyped (church enabled) (liftCtx e65) (.app (liftTm e343) (liftTm e36)) (liftTm (inst0 e36 e348))
  rw [liftTm_inst0]
  exact .appElim (e345 enabled) (e347 enabled)

private def e351 : Tower.Tm 3 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero

private theorem e352 : CTyped (church enabled) (liftCtx e65) (liftTm e351) (liftTm e37) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e5 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e353 : Tower.Tm 3 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.eliminate)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero)

private theorem e354 : CTyped (church enabled) (liftCtx e65) (liftTm e353) (liftTm e340) :=
by
  change CTyped (church enabled) (liftCtx e65) (.app (liftTm e349) (liftTm e351)) (liftTm (inst0 e351 e72))
  rw [liftTm_inst0]
  exact .appElim (e350 enabled) (e352 enabled)

private theorem e355 : CCtxFormed (church enabled) (liftCtx e0) :=
.nil

private theorem e356 : CCtxFormed (church enabled) (liftCtx e19) :=
.snoc (e355 enabled) ⟨Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1)))), (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel), (e18 enabled)⟩

private theorem e357 : CCtxFormed (church enabled) (liftCtx e28) :=
.snoc (e356 enabled) ⟨Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1)), (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel), (e27 enabled)⟩

private theorem e358 : CCtxFormed (church enabled) (liftCtx e65) :=
.snoc (e357 enabled) ⟨Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1)))), (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel), (e64 enabled)⟩

private def e359 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.eliminate

private def e360 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1)))))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))))

private theorem e361 : CTyped (church enabled) (liftCtx e68) (liftTm e359) (liftTm e360) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e85 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e362 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))

private def e363 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.eliminate)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)

private def e364 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))

private theorem e365 : CTyped (church enabled) (liftCtx e68) (liftTm e363) (liftTm e364) :=
by
  change CTyped (church enabled) (liftCtx e68) (.app (liftTm e359) (liftTm e44)) (liftTm (inst0 e44 e362))
  rw [liftTm_inst0]
  exact .appElim (e361 enabled) (e69 enabled)

private def e366 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero)

private theorem e367 : CTyped (church enabled) (liftCtx e68) (liftTm e141) (liftTm e366) :=
by
  change CTyped (church enabled) (liftCtx e68) (.var 2) (liftTm (Ctx.lookup e68 2))
  rw [← liftCtx_lookup]
  exact .var 2

private def e368 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))

private def e369 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.eliminate)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2)

private theorem e370 : CTyped (church enabled) (liftCtx e68) (liftTm e369) (liftTm e342) :=
by
  change CTyped (church enabled) (liftCtx e68) (.app (liftTm e363) (liftTm e141)) (liftTm (inst0 e141 e368))
  rw [liftTm_inst0]
  exact .appElim (e365 enabled) (e367 enabled)

private def e371 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))))

private theorem e372 : CTyped (church enabled) (liftCtx e68) (liftTm e50) (liftTm e371) :=
by
  change CTyped (church enabled) (liftCtx e68) (.var 1) (liftTm (Ctx.lookup e68 1))
  rw [← liftCtx_lookup]
  exact .var 1

private def e373 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))

private def e374 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.eliminate)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)

private theorem e375 : CTyped (church enabled) (liftCtx e68) (liftTm e374) (liftTm e348) :=
by
  change CTyped (church enabled) (liftCtx e68) (.app (liftTm e369) (liftTm e50)) (liftTm (inst0 e50 e373))
  rw [liftTm_inst0]
  exact .appElim (e370 enabled) (e372 enabled)

private theorem e376 : CTyped (church enabled) (liftCtx e68) (liftTm e47) (liftTm e48) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e12 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e377 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)

private theorem e378 : CTyped (church enabled) (liftCtx e68) (liftTm e377) (liftTm e51) :=
by
  change CTyped (church enabled) (liftCtx e68) (.app (liftTm e47) (liftTm e70)) (liftTm (inst0 e70 e53))
  rw [liftTm_inst0]
  exact .appElim (e376 enabled) (e71 enabled)

private def e379 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)

private def e380 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.eliminate)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))

private def e381 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))

private theorem e382 : CTyped (church enabled) (liftCtx e68) (liftTm e380) (liftTm e381) :=
by
  change CTyped (church enabled) (liftCtx e68) (.app (liftTm e374) (liftTm e377)) (liftTm (inst0 e377 e379))
  rw [liftTm_inst0]
  exact .appElim (e375 enabled) (e378 enabled)

private theorem e383 : CCtxFormed (church enabled) (liftCtx e68) :=
.snoc (e358 enabled) ⟨Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0), (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel), (e67 enabled)⟩

private def e384 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))

private def e385 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)

private def e386 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))

private theorem e387 : CTyped (church enabled) (liftCtx e68) (liftTm e385) (liftTm e386) :=
by
  change CTyped (church enabled) (liftCtx e68) (.app (liftTm e50) (liftTm e70)) (liftTm (inst0 e70 e384))
  rw [liftTm_inst0]
  exact .appElim (e372 enabled) (e71 enabled)

private def e388 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.eliminate)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)

private theorem e389 : CTyped (church enabled) (liftCtx e68) (liftTm e388) (liftTm e72) :=
by
  change CTyped (church enabled) (liftCtx e68) (.app (liftTm e374) (liftTm e70)) (liftTm (inst0 e70 e379))
  rw [liftTm_inst0]
  exact .appElim (e375 enabled) (e71 enabled)

private def e390 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))

private def e391 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.eliminate)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))

private theorem e392 : CTyped (church enabled) (liftCtx e68) (liftTm e391) (liftTm e381) :=
by
  change CTyped (church enabled) (liftCtx e68) (.app (liftTm e385) (liftTm e388)) (liftTm (inst0 e388 e390))
  rw [liftTm_inst0]
  exact .appElim (e387 enabled) (e389 enabled)

private def e393 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.eliminate

private def e394 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))))))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.nil)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                        `CumulativeTower.Nat.succ)
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)))
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                            `CumulativeTower.Vec.cons)
                          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
                        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))))))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))))))

private theorem e395 : CTyped (church enabled) (liftCtx e292) (liftTm e393) (liftTm e394) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e331 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e396 : CTyped (church enabled) (liftCtx e292) (liftTm e44) (liftTm e129) :=
by
  change CTyped (church enabled) (liftCtx e292) (.var 3) (liftTm (Ctx.lookup e292 3))
  rw [← liftCtx_lookup]
  exact .var 3

private def e397 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))))))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.nil)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                      `CumulativeTower.Nat.succ)
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)))
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                          `CumulativeTower.Vec.cons)
                        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))))))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))))

private def e398 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.eliminate)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)

private def e399 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))))))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.nil)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                      `CumulativeTower.Nat.succ)
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)))
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                          `CumulativeTower.Vec.cons)
                        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 9))
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))))))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))))

private theorem e400 : CTyped (church enabled) (liftCtx e292) (liftTm e398) (liftTm e399) :=
by
  change CTyped (church enabled) (liftCtx e292) (.app (liftTm e393) (liftTm e44)) (liftTm (inst0 e44 e397))
  rw [liftTm_inst0]
  exact .appElim (e395 enabled) (e396 enabled)

private def e401 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1)))))

private theorem e402 : CTyped (church enabled) (liftCtx e292) (liftTm e141) (liftTm e401) :=
by
  change CTyped (church enabled) (liftCtx e292) (.var 2) (liftTm (Ctx.lookup e292 2))
  rw [← liftCtx_lookup]
  exact .var 2

private def e403 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.nil)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                        `CumulativeTower.Vec.cons)
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 9))
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))))))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))))

private def e404 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.eliminate)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2)

private def e405 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.nil)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7)
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                        `CumulativeTower.Vec.cons)
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8))
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))))))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))))

private theorem e406 : CTyped (church enabled) (liftCtx e292) (liftTm e404) (liftTm e405) :=
by
  change CTyped (church enabled) (liftCtx e292) (.app (liftTm e398) (liftTm e141)) (liftTm (inst0 e141 e403))
  rw [liftTm_inst0]
  exact .appElim (e400 enabled) (e402 enabled)

private def e407 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.nil)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))

private theorem e408 : CTyped (church enabled) (liftCtx e292) (liftTm e50) (liftTm e407) :=
by
  change CTyped (church enabled) (liftCtx e292) (.var 1) (liftTm (Ctx.lookup e292 1))
  rw [← liftCtx_lookup]
  exact .var 1

private def e409 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7)
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                      `CumulativeTower.Vec.cons)
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8))
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))))))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))

private def e410 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.eliminate)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)

private def e411 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                      `CumulativeTower.Vec.cons)
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7))
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))))))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))

private theorem e412 : CTyped (church enabled) (liftCtx e292) (liftTm e410) (liftTm e411) :=
by
  change CTyped (church enabled) (liftCtx e292) (.app (liftTm e404) (liftTm e50)) (liftTm (inst0 e50 e409))
  rw [liftTm_inst0]
  exact .appElim (e406 enabled) (e408 enabled)

private def e413 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.cons)
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7))
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))))))

private theorem e414 : CTyped (church enabled) (liftCtx e292) (liftTm e70) (liftTm e413) :=
by
  change CTyped (church enabled) (liftCtx e292) (.var 0) (liftTm (Ctx.lookup e292 0))
  rw [← liftCtx_lookup]
  exact .var 0

private def e415 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))

private def e416 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.eliminate)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)

private theorem e417 : CTyped (church enabled) (liftCtx e292) (liftTm e416) (liftTm e317) :=
by
  change CTyped (church enabled) (liftCtx e292) (.app (liftTm e410) (liftTm e70)) (liftTm (inst0 e70 e415))
  rw [liftTm_inst0]
  exact .appElim (e412 enabled) (e414 enabled)

private def e418 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero

private theorem e419 : CTyped (church enabled) (liftCtx e292) (liftTm e418) (liftTm e51) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e5 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e420 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.eliminate)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero)

private def e421 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))

private theorem e422 : CTyped (church enabled) (liftCtx e292) (liftTm e420) (liftTm e421) :=
by
  change CTyped (church enabled) (liftCtx e292) (.app (liftTm e416) (liftTm e418)) (liftTm (inst0 e418 e314))
  rw [liftTm_inst0]
  exact .appElim (e417 enabled) (e419 enabled)

private def e423 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.nil

private def e424 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero))

private theorem e425 : CTyped (church enabled) (liftCtx e292) (liftTm e423) (liftTm e424) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e114 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e426 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero)

private def e427 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.nil)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)

private def e428 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero)

private theorem e429 : CTyped (church enabled) (liftCtx e292) (liftTm e427) (liftTm e428) :=
by
  change CTyped (church enabled) (liftCtx e292) (.app (liftTm e423) (liftTm e44)) (liftTm (inst0 e44 e426))
  rw [liftTm_inst0]
  exact .appElim (e425 enabled) (e396 enabled)

private def e430 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)

private def e431 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.eliminate)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.nil)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))

private theorem e432 : CTyped (church enabled) (liftCtx e292) (liftTm e431) (liftTm e407) :=
by
  change CTyped (church enabled) (liftCtx e292) (.app (liftTm e420) (liftTm e427)) (liftTm (inst0 e427 e430))
  rw [liftTm_inst0]
  exact .appElim (e422 enabled) (e429 enabled)

private theorem e433 : CCtxFormed (church enabled) (liftCtx e89) :=
.snoc (e355 enabled) ⟨Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)), (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel), (e88 enabled)⟩

private theorem e434 : CCtxFormed (church enabled) (liftCtx e178) :=
.snoc (e433 enabled) ⟨Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))))), (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel), (e177 enabled)⟩

private theorem e435 : CCtxFormed (church enabled) (liftCtx e197) :=
.snoc (e434 enabled) ⟨Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1)), (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel), (e196 enabled)⟩

private theorem e436 : CCtxFormed (church enabled) (liftCtx e292) :=
.snoc (e435 enabled) ⟨Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1)))))), (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel), (e291 enabled)⟩

private def e437 : Tower.Ctx 6 :=
.snoc e295 e205

private def e438 : Tower.Ctx 7 :=
.snoc e437 e310

private def e439 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.eliminate

private def e440 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))))))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.nil)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                        `CumulativeTower.Nat.succ)
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)))
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                            `CumulativeTower.Vec.cons)
                          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
                        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))))))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))))))

private theorem e441 : CTyped (church enabled) (liftCtx e438) (liftTm e439) (liftTm e440) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e331 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e442 : CTyped (church enabled) (liftCtx e438) (liftTm e253) (liftTm e254) :=
by
  change CTyped (church enabled) (liftCtx e438) (.var 6) (liftTm (Ctx.lookup e438 6))
  rw [← liftCtx_lookup]
  exact .var 6

private def e443 : Tower.Tm 8 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))))))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.nil)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                      `CumulativeTower.Nat.succ)
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)))
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                          `CumulativeTower.Vec.cons)
                        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))))))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))))

private def e444 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.eliminate)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)

private def e445 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))))))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.nil)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7)))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 9)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 10))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                      `CumulativeTower.Nat.succ)
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)))
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                          `CumulativeTower.Vec.cons)
                        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 12))
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))))))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 10))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))))

private theorem e446 : CTyped (church enabled) (liftCtx e438) (liftTm e444) (liftTm e445) :=
by
  change CTyped (church enabled) (liftCtx e438) (.app (liftTm e439) (liftTm e253)) (liftTm (inst0 e253 e443))
  rw [liftTm_inst0]
  exact .appElim (e441 enabled) (e442 enabled)

private theorem e447 : CTyped (church enabled) (liftCtx e438) (liftTm e234) (liftTm e235) :=
by
  change CTyped (church enabled) (liftCtx e438) (.var 5) (liftTm (Ctx.lookup e438 5))
  rw [← liftCtx_lookup]
  exact .var 5

private def e448 : Tower.Tm 8 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.nil)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7)))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 9)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 10))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                        `CumulativeTower.Vec.cons)
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 12))
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))))))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 10))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))))

private def e449 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.eliminate)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)

private def e450 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.nil)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 9))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 9)
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 10)
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                        `CumulativeTower.Vec.cons)
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 11))
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))))))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 9))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 9)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))))

private theorem e451 : CTyped (church enabled) (liftCtx e438) (liftTm e449) (liftTm e450) :=
by
  change CTyped (church enabled) (liftCtx e438) (.app (liftTm e444) (liftTm e234)) (liftTm (inst0 e234 e448))
  rw [liftTm_inst0]
  exact .appElim (e446 enabled) (e447 enabled)

private def e452 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4

private def e453 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.nil)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))

private theorem e454 : CTyped (church enabled) (liftCtx e438) (liftTm e452) (liftTm e453) :=
by
  change CTyped (church enabled) (liftCtx e438) (.var 4) (liftTm (Ctx.lookup e438 4))
  rw [← liftCtx_lookup]
  exact .var 4

private def e455 : Tower.Tm 8 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 9))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 9)
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 10)
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                      `CumulativeTower.Vec.cons)
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 11))
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))))))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 9))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 9)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))

private def e456 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.eliminate)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)

private def e457 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8)
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 9)
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                      `CumulativeTower.Vec.cons)
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 10))
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))))))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))

private theorem e458 : CTyped (church enabled) (liftCtx e438) (liftTm e456) (liftTm e457) :=
by
  change CTyped (church enabled) (liftCtx e438) (.app (liftTm e449) (liftTm e452)) (liftTm (inst0 e452 e455))
  rw [liftTm_inst0]
  exact .appElim (e451 enabled) (e454 enabled)

private def e459 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 9)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.cons)
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 10))
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))))))

private theorem e460 : CTyped (church enabled) (liftCtx e438) (liftTm e240) (liftTm e459) :=
by
  change CTyped (church enabled) (liftCtx e438) (.var 3) (liftTm (Ctx.lookup e438 3))
  rw [← liftCtx_lookup]
  exact .var 3

private def e461 : Tower.Tm 8 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))

private def e462 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.eliminate)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)

private def e463 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))

private theorem e464 : CTyped (church enabled) (liftCtx e438) (liftTm e462) (liftTm e463) :=
by
  change CTyped (church enabled) (liftCtx e438) (.app (liftTm e456) (liftTm e240)) (liftTm (inst0 e240 e461))
  rw [liftTm_inst0]
  exact .appElim (e458 enabled) (e460 enabled)

private theorem e465 : CTyped (church enabled) (liftCtx e438) (liftTm e237) (liftTm e238) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e12 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e466 : CTyped (church enabled) (liftCtx e438) (liftTm e264) (liftTm e241) :=
by
  change CTyped (church enabled) (liftCtx e438) (.var 2) (liftTm (Ctx.lookup e438 2))
  rw [← liftCtx_lookup]
  exact .var 2

private def e467 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2)

private theorem e468 : CTyped (church enabled) (liftCtx e438) (liftTm e467) (liftTm e241) :=
by
  change CTyped (church enabled) (liftCtx e438) (.app (liftTm e237) (liftTm e264)) (liftTm (inst0 e264 e243))
  rw [liftTm_inst0]
  exact .appElim (e465 enabled) (e466 enabled)

private def e469 : Tower.Tm 8 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))

private def e470 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.eliminate)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))

private def e471 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2)))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))

private theorem e472 : CTyped (church enabled) (liftCtx e438) (liftTm e470) (liftTm e471) :=
by
  change CTyped (church enabled) (liftCtx e438) (.app (liftTm e462) (liftTm e467)) (liftTm (inst0 e467 e469))
  rw [liftTm_inst0]
  exact .appElim (e464 enabled) (e468 enabled)

private theorem e473 : CTyped (church enabled) (liftCtx e438) (liftTm e250) (liftTm e251) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e159 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e474 : CTyped (church enabled) (liftCtx e438) (liftTm e257) (liftTm e258) :=
by
  change CTyped (church enabled) (liftCtx e438) (.app (liftTm e250) (liftTm e253)) (liftTm (inst0 e253 e256))
  rw [liftTm_inst0]
  exact .appElim (e473 enabled) (e442 enabled)

private def e475 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.cons)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2)

private def e476 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))))

private theorem e477 : CTyped (church enabled) (liftCtx e438) (liftTm e475) (liftTm e476) :=
by
  change CTyped (church enabled) (liftCtx e438) (.app (liftTm e257) (liftTm e264)) (liftTm (inst0 e264 e260))
  rw [liftTm_inst0]
  exact .appElim (e474 enabled) (e466 enabled)

private theorem e478 : CTyped (church enabled) (liftCtx e438) (liftTm e270) (liftTm e253) :=
by
  change CTyped (church enabled) (liftCtx e438) (.var 1) (liftTm (Ctx.lookup e438 1))
  rw [← liftCtx_lookup]
  exact .var 1

private def e479 : Tower.Tm 8 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)))

private def e480 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.cons)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)

private def e481 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)))

private theorem e482 : CTyped (church enabled) (liftCtx e438) (liftTm e480) (liftTm e481) :=
by
  change CTyped (church enabled) (liftCtx e438) (.app (liftTm e475) (liftTm e270)) (liftTm (inst0 e270 e479))
  rw [liftTm_inst0]
  exact .appElim (e477 enabled) (e478 enabled)

private def e483 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0

private def e484 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2)

private theorem e485 : CTyped (church enabled) (liftCtx e438) (liftTm e483) (liftTm e484) :=
by
  change CTyped (church enabled) (liftCtx e438) (.var 0) (liftTm (Ctx.lookup e438 0))
  rw [← liftCtx_lookup]
  exact .var 0

private def e486 : Tower.Tm 8 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))

private def e487 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.cons)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)

private def e488 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))

private theorem e489 : CTyped (church enabled) (liftCtx e438) (liftTm e487) (liftTm e488) :=
by
  change CTyped (church enabled) (liftCtx e438) (.app (liftTm e480) (liftTm e483)) (liftTm (inst0 e483 e486))
  rw [liftTm_inst0]
  exact .appElim (e482 enabled) (e485 enabled)

private def e490 : Tower.Tm 8 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)

private def e491 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.eliminate)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2)))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.cons)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))

private def e492 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2)))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.cons)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))

private theorem e493 : CTyped (church enabled) (liftCtx e438) (liftTm e491) (liftTm e492) :=
by
  change CTyped (church enabled) (liftCtx e438) (.app (liftTm e470) (liftTm e487)) (liftTm (inst0 e487 e490))
  rw [liftTm_inst0]
  exact .appElim (e472 enabled) (e489 enabled)

private theorem e494 : CCtxFormed (church enabled) (liftCtx e295) :=
.snoc (e436 enabled) ⟨Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0), (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel), (e294 enabled)⟩

private theorem e495 : CCtxFormed (church enabled) (liftCtx e437) :=
.snoc (e494 enabled) ⟨Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0), (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel), (e297 enabled)⟩

private def e496 : Tower.Tm 6 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec

private def e497 : Tower.Tm 6 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))

private theorem e498 : CTyped (church enabled) (liftCtx e437) (liftTm e496) (liftTm e497) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e100 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e499 : Tower.Tm 6 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5

private theorem e500 : CTyped (church enabled) (liftCtx e437) (liftTm e499) (liftTm e212) :=
by
  change CTyped (church enabled) (liftCtx e437) (.var 5) (liftTm (Ctx.lookup e437 5))
  rw [← liftCtx_lookup]
  exact .var 5

private def e501 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))

private def e502 : Tower.Tm 6 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)

private theorem e503 : CTyped (church enabled) (liftCtx e437) (liftTm e502) (liftTm e207) :=
by
  change CTyped (church enabled) (liftCtx e437) (.app (liftTm e496) (liftTm e499)) (liftTm (inst0 e499 e501))
  rw [liftTm_inst0]
  exact .appElim (e498 enabled) (e500 enabled)

private theorem e504 : CTyped (church enabled) (liftCtx e437) (liftTm e305) (liftTm e220) :=
by
  change CTyped (church enabled) (liftCtx e437) (.var 1) (liftTm (Ctx.lookup e437 1))
  rw [← liftCtx_lookup]
  exact .var 1

private theorem e505 : CTyped (church enabled) (liftCtx e437) (liftTm e310) (liftTm e212) :=
by
  change CTyped (church enabled) (liftCtx e437) (.app (liftTm e502) (liftTm e305)) (liftTm (inst0 e305 e254))
  rw [liftTm_inst0]
  exact .appElim (e503 enabled) (e504 enabled)

private theorem e506 : CCtxFormed (church enabled) (liftCtx e438) :=
.snoc (e495 enabled) ⟨Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0), (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel), (e505 enabled)⟩

private def e507 : Tower.Tm 8 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 9)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.cons)
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 10))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))))

private def e508 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2)

private def e509 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.cons)
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 9))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))))

private theorem e510 : CTyped (church enabled) (liftCtx e438) (liftTm e508) (liftTm e509) :=
by
  change CTyped (church enabled) (liftCtx e438) (.app (liftTm e240) (liftTm e264)) (liftTm (inst0 e264 e507))
  rw [liftTm_inst0]
  exact .appElim (e460 enabled) (e466 enabled)

private def e511 : Tower.Tm 8 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.cons)
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 9))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))))

private def e512 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)

private def e513 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.cons)
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))))

private theorem e514 : CTyped (church enabled) (liftCtx e438) (liftTm e512) (liftTm e513) :=
by
  change CTyped (church enabled) (liftCtx e438) (.app (liftTm e508) (liftTm e270)) (liftTm (inst0 e270 e511))
  rw [liftTm_inst0]
  exact .appElim (e510 enabled) (e478 enabled)

private def e515 : Tower.Tm 8 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.cons)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))

private def e516 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)

private def e517 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.cons)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))

private theorem e518 : CTyped (church enabled) (liftCtx e438) (liftTm e516) (liftTm e517) :=
by
  change CTyped (church enabled) (liftCtx e438) (.app (liftTm e512) (liftTm e483)) (liftTm (inst0 e483 e515))
  rw [liftTm_inst0]
  exact .appElim (e514 enabled) (e485 enabled)

private def e519 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.eliminate)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2)

private def e520 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))

private theorem e521 : CTyped (church enabled) (liftCtx e438) (liftTm e519) (liftTm e520) :=
by
  change CTyped (church enabled) (liftCtx e438) (.app (liftTm e462) (liftTm e264)) (liftTm (inst0 e264 e469))
  rw [liftTm_inst0]
  exact .appElim (e464 enabled) (e466 enabled)

private def e522 : Tower.Tm 8 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)

private def e523 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.eliminate)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)

private def e524 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)

private theorem e525 : CTyped (church enabled) (liftCtx e438) (liftTm e523) (liftTm e524) :=
by
  change CTyped (church enabled) (liftCtx e438) (.app (liftTm e519) (liftTm e483)) (liftTm (inst0 e483 e522))
  rw [liftTm_inst0]
  exact .appElim (e521 enabled) (e485 enabled)

private def e526 : Tower.Tm 8 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.cons)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))

private def e527 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                `CumulativeTower.Vec.eliminate)
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))

private theorem e528 : CTyped (church enabled) (liftCtx e438) (liftTm e527) (liftTm e492) :=
by
  change CTyped (church enabled) (liftCtx e438) (.app (liftTm e516) (liftTm e523)) (liftTm (inst0 e523 e526))
  rw [liftTm_inst0]
  exact .appElim (e518 enabled) (e525 enabled)

theorem declaration_0 : CTyped (church enabled) (liftCtx e0) (liftTm e1) (liftTm e2) := (e3 enabled)

theorem declaration_1 : CTyped (church enabled) (liftCtx e0) (liftTm e4) (liftTm e1) := (e5 enabled)

theorem declaration_2 : CTyped (church enabled) (liftCtx e0) (liftTm e10) (liftTm e11) := (e12 enabled)

theorem declaration_3 : CTyped (church enabled) (liftCtx e0) (liftTm e83) (liftTm e84) := (e85 enabled)

theorem declaration_4 : CTyped (church enabled) (liftCtx e0) (liftTm e98) (liftTm e99) := (e100 enabled)

theorem declaration_5 : CTyped (church enabled) (liftCtx e0) (liftTm e112) (liftTm e113) := (e114 enabled)

theorem declaration_6 : CTyped (church enabled) (liftCtx e0) (liftTm e157) (liftTm e158) := (e159 enabled)

theorem declaration_7 : CTyped (church enabled) (liftCtx e0) (liftTm e329) (liftTm e330) := (e331 enabled)

theorem left_0 : CTyped (church enabled) (liftCtx e65) (liftTm e353) (liftTm e340) := (e354 enabled)

theorem context_0 : CCtxFormed (church enabled) (liftCtx e65) := (e358 enabled)

theorem right_0 : CTyped (church enabled) (liftCtx e65) (liftTm e127) (liftTm e340) := (e341 enabled)

theorem left_1 : CTyped (church enabled) (liftCtx e68) (liftTm e380) (liftTm e381) := (e382 enabled)

theorem context_1 : CCtxFormed (church enabled) (liftCtx e68) := (e383 enabled)

theorem right_1 : CTyped (church enabled) (liftCtx e68) (liftTm e391) (liftTm e381) := (e392 enabled)

theorem left_2 : CTyped (church enabled) (liftCtx e292) (liftTm e431) (liftTm e407) := (e432 enabled)

theorem context_2 : CCtxFormed (church enabled) (liftCtx e292) := (e436 enabled)

theorem right_2 : CTyped (church enabled) (liftCtx e292) (liftTm e50) (liftTm e407) := (e408 enabled)

theorem left_3 : CTyped (church enabled) (liftCtx e438) (liftTm e491) (liftTm e492) := (e493 enabled)

theorem context_3 : CCtxFormed (church enabled) (liftCtx e438) := (e506 enabled)

theorem right_3 : CTyped (church enabled) (liftCtx e438) (liftTm e527) (liftTm e492) := (e528 enabled)

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies.Programs.Annotated.Evidence

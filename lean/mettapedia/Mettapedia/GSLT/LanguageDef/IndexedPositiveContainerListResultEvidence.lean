import Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerListResultAdapter

/-! Generated finite evidence; independently replayed by the checking companion. -/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
namespace Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerListResultAdapter.Registered.Evidence
open Presentation Declaration
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

private abbrev S (n : Nat) := StructuralConversionCode.StepCode Tower.Head NativeListResultView.decoder.Code n
private abbrev C (n : Nat) := StructuralConversionCode.Code Tower.Head NativeListResultView.decoder.Code n
private abbrev T (n : Nat) := StructuralTypingReplay.Code Tower.Head C n
private abbrev X (n : Nat) := StructuralTypingReplay.ContextCode Tower.Head C n

private def e0 : X 0 :=
.nil

private def e1 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))

private def e2 : T 0 :=
.headType

private def e3 : X 1 :=
.snoc (e0) (e1) (e2)

private def e4 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))

private def e5 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)

private def e6 : T 1 :=
.var

private def e7 : T 2 :=
.headType

private def e8 : T 1 :=
.piForm (e5) (e1) (e6) (e7)

private def e9 : X 2 :=
.snoc (e3) (e4) (e8)

private def e10 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))

private def e11 : Tower.Tm 2 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))

private def e12 : Tower.Tm 3 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))

private def e13 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))

private def e14 : T 1 :=
.headType

private def e15 : T 0 :=
.piForm (e1) (e1) (e2) (e14)

private def e16 : T 2 :=
.const (e13) (e15)

private def e17 : T 2 :=
.var

private def e18 : T 2 :=
.appElim (e11) (e12) (e16) (e17)

private def e19 : T 3 :=
.var

private def e20 : T 2 :=
.piForm (e5) (e5) (e18) (e19)

private def e21 : X 3 :=
.snoc (e9) (e10) (e20)

private def e22 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))

private def e23 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))

private def e24 : T 3 :=
.const (e13) (e15)

private def e25 : T 3 :=
.appElim (e12) (e23) (e24) (e19)

private def e26 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))

private def e27 : T 4 :=
.const (e13) (e15)

private def e28 : T 4 :=
.var

private def e29 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4

private def e30 : Tower.Tm 6 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))

private def e31 : T 5 :=
.var

private def e32 : T 5 :=
.appElim (e29) (e30) (e31) (e31)

private def e33 : T 4 :=
.sigmaForm (e5) (e5) (e28) (e32)

private def e34 : T 4 :=
.cumul (e10) (e33)

private def e35 : T 4 :=
.appElim (e23) (e26) (e27) (e34)

private def e36 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)

private def e37 : Tower.Tm 6 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5

private def e38 : T 5 :=
.appElim (e36) (e37) (e31) (e31)

private def e39 : T 5 :=
.appElim (e29) (e30) (e31) (e38)

private def e40 : T 4 :=
.piForm (e5) (e5) (e35) (e39)

private def e41 : T 3 :=
.piForm (e5) (e10) (e25) (e40)

private def e42 : X 4 :=
.snoc (e21) (e22) (e41)

private def e43 : T 4 :=
.appElim (e23) (e26) (e27) (e28)

private def e44 : X 5 :=
.snoc (e42) (e5) (e43)

private def e45 : T 5 :=
.const (e13) (e15)

private def e46 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))

private def e47 : T 6 :=
.var

private def e48 : T 6 :=
.appElim (e37) (e46) (e47) (e47)

private def e49 : T 5 :=
.sigmaForm (e5) (e5) (e31) (e48)

private def e50 : T 5 :=
.cumul (e10) (e49)

private def e51 : T 5 :=
.appElim (e26) (e30) (e45) (e50)

private def e52 : Tower.Tm 6 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))

private def e53 : Tower.Tm 6 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)

private def e54 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))

private def e55 : Tower.Tm 6 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))

private def e56 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))

private def e57 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))

private def e58 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))))

private def e59 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))))

private def e60 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))))

private def e61 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))

private def e62 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))

private def e63 : T 4 :=
.headType

private def e64 : T 3 :=
.piForm (e5) (e1) (e19) (e63)

private def e65 : T 2 :=
.piForm (e5) (e4) (e17) (e64)

private def e66 : T 5 :=
.headType

private def e67 : T 4 :=
.piForm (e5) (e1) (e43) (e66)

private def e68 : T 3 :=
.piForm (e5) (e4) (e25) (e67)

private def e69 : T 2 :=
.piForm (e62) (e62) (e65) (e68)

private def e70 : T 1 :=
.piForm (e1) (e61) (e14) (e69)

private def e71 : T 0 :=
.piForm (e1) (e60) (e2) (e70)

private def e72 : T 6 :=
.const (e59) (e71)

private def e73 : T 6 :=
.appElim (e30) (e58) (e72) (e47)

private def e74 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6

private def e75 : Tower.Tm 8 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))

private def e76 : T 7 :=
.var

private def e77 : T 7 :=
.appElim (e74) (e75) (e76) (e76)

private def e78 : T 6 :=
.sigmaForm (e5) (e5) (e47) (e77)

private def e79 : T 6 :=
.cumul (e10) (e78)

private def e80 : T 6 :=
.appElim (e30) (e57) (e73) (e79)

private def e81 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))

private def e82 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))

private def e83 : Tower.Tm 8 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7

private def e84 : Tower.Tm 9 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))

private def e85 : T 8 :=
.var

private def e86 : T 8 :=
.appElim (e83) (e84) (e85) (e85)

private def e87 : T 7 :=
.sigmaForm (e5) (e5) (e76) (e86)

private def e88 : T 8 :=
.headType

private def e89 : T 7 :=
.piForm (e10) (e1) (e87) (e88)

private def e90 : T 6 :=
.piForm (e5) (e82) (e47) (e89)

private def e91 : Tower.Tm 9 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)

private def e92 : T 8 :=
.fstElim (e91) (e85)

private def e93 : T 8 :=
.idForm (e5) (e85) (e85) (e92)

private def e94 : T 7 :=
.lamIntro (e82) (e89) (e93)

private def e95 : T 6 :=
.lamIntro (e81) (e90) (e94)

private def e96 : T 6 :=
.appElim (e55) (e56) (e80) (e95)

private def e97 : T 6 :=
.appElim (e53) (e54) (e96) (e47)

private def e98 : T 6 :=
.appElim (e52) (e46) (e97) (e47)

private def e99 : T 5 :=
.sigmaForm (e5) (e5) (e51) (e98)

private def e100 : T 5 :=
.cumul (e10) (e99)

private def e101 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))

private def e102 : T 6 :=
.const (e13) (e15)

private def e103 : T 6 :=
.appElim (e30) (e46) (e102) (e79)

private def e104 : T 5 :=
.piForm (e10) (e5) (e99) (e103)

private def e105 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List.mapRel)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.id
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.fst
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)

private def e106 : T 6 :=
.fstElim (e105) (e47)

private def e107 : T 5 :=
.lamIntro (e101) (e104) (e106)

def inputSubmission : FormationSensitiveElaboration.Submission Tower.Head NativeListResultView.decoder.Code 5 :=
{ context := e44, term := e100 }

def outputSubmission : FormationSensitiveElaboration.Submission Tower.Head NativeListResultView.decoder.Code 5 :=
{ context := e44, term := e51 }

def projectionSubmission : FormationSensitiveElaboration.Submission Tower.Head NativeListResultView.decoder.Code 5 :=
{ context := e44, term := e107 }

def resultSubmission : FormationSensitiveElaboration.Submission Tower.Head NativeListResultView.decoder.Code 5 :=
{ context := e44, term := e39 }


end Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerListResultAdapter.Registered.Evidence

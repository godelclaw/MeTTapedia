import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeListResultView

/-! Generated finite evidence; independently replayed by the checking companion. -/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeListResultView.Evidence
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
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))

private def e2 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))

private def e3 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))

private def e4 : T 0 :=
.headType

private def e5 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))

private def e6 : T 1 :=
.headType

private def e7 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)

private def e8 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))

private def e9 : Tower.Tm 2 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))

private def e10 : Tower.Tm 3 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))

private def e11 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))

private def e12 : T 0 :=
.piForm (e2) (e2) (e4) (e6)

private def e13 : T 2 :=
.const (e11) (e12)

private def e14 : T 2 :=
.var

private def e15 : T 2 :=
.appElim (e9) (e10) (e13) (e14)

private def e16 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))

private def e17 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))

private def e18 : T 3 :=
.const (e11) (e12)

private def e19 : T 3 :=
.var

private def e20 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3

private def e21 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))

private def e22 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))

private def e23 : T 4 :=
.var

private def e24 : T 5 :=
.headType

private def e25 : T 4 :=
.piForm (e7) (e2) (e23) (e24)

private def e26 : T 5 :=
.var

private def e27 : T 4 :=
.lamIntro (e22) (e25) (e26)

private def e28 : T 4 :=
.appElim (e20) (e21) (e27) (e23)

private def e29 : T 3 :=
.sigmaForm (e7) (e7) (e19) (e28)

private def e30 : T 3 :=
.cumul (e16) (e29)

private def e31 : T 3 :=
.appElim (e10) (e17) (e18) (e30)

private def e32 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))

private def e33 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)

private def e34 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))

private def e35 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))

private def e36 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))

private def e37 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))

private def e38 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))

private def e39 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))

private def e40 : Tower.Tm 5 :=
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

private def e41 : Tower.Head :=
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

private def e42 : Tower.Head :=
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

private def e43 : Tower.Head :=
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

private def e44 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))

private def e45 : T 4 :=
.headType

private def e46 : T 3 :=
.piForm (e7) (e2) (e19) (e45)

private def e47 : T 2 :=
.piForm (e7) (e22) (e14) (e46)

private def e48 : T 3 :=
.appElim (e10) (e17) (e18) (e19)

private def e49 : T 4 :=
.const (e11) (e12)

private def e50 : T 4 :=
.appElim (e17) (e21) (e49) (e23)

private def e51 : T 4 :=
.piForm (e7) (e2) (e50) (e24)

private def e52 : T 3 :=
.piForm (e7) (e22) (e48) (e51)

private def e53 : T 2 :=
.piForm (e44) (e44) (e47) (e52)

private def e54 : T 1 :=
.piForm (e2) (e43) (e6) (e53)

private def e55 : T 0 :=
.piForm (e2) (e42) (e4) (e54)

private def e56 : T 4 :=
.const (e41) (e55)

private def e57 : T 4 :=
.appElim (e17) (e40) (e56) (e23)

private def e58 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4

private def e59 : Tower.Tm 6 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))

private def e60 : T 6 :=
.headType

private def e61 : T 5 :=
.piForm (e7) (e2) (e26) (e60)

private def e62 : T 6 :=
.var

private def e63 : T 5 :=
.lamIntro (e22) (e61) (e62)

private def e64 : T 5 :=
.appElim (e58) (e59) (e63) (e26)

private def e65 : T 4 :=
.sigmaForm (e7) (e7) (e23) (e64)

private def e66 : T 4 :=
.cumul (e16) (e65)

private def e67 : T 4 :=
.appElim (e17) (e39) (e57) (e66)

private def e68 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))

private def e69 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))

private def e70 : T 5 :=
.sigmaForm (e7) (e7) (e26) (e62)

private def e71 : T 5 :=
.piForm (e16) (e2) (e70) (e60)

private def e72 : T 4 :=
.piForm (e7) (e69) (e23) (e71)

private def e73 : T 5 :=
.const (e11) (e12)

private def e74 : T 5 :=
.appElim (e21) (e59) (e73) (e26)

private def e75 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))

private def e76 : T 6 :=
.const (e11) (e12)

private def e77 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6

private def e78 : Tower.Tm 8 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))

private def e79 : T 7 :=
.var

private def e80 : T 8 :=
.headType

private def e81 : T 7 :=
.piForm (e7) (e2) (e79) (e80)

private def e82 : T 8 :=
.var

private def e83 : T 7 :=
.lamIntro (e22) (e81) (e82)

private def e84 : T 7 :=
.appElim (e77) (e78) (e83) (e79)

private def e85 : T 6 :=
.sigmaForm (e7) (e7) (e62) (e84)

private def e86 : T 6 :=
.cumul (e16) (e85)

private def e87 : T 6 :=
.appElim (e59) (e75) (e76) (e86)

private def e88 : T 7 :=
.headType

private def e89 : T 6 :=
.piForm (e7) (e2) (e87) (e88)

private def e90 : T 5 :=
.piForm (e7) (e22) (e74) (e89)

private def e91 : T 4 :=
.piForm (e68) (e44) (e72) (e90)

private def e92 : C 4 :=
.refl (e37)

private def e93 : C 4 :=
.trans (e92) (e92)

private def e94 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5

private def e95 : Tower.Tm 6 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0

private def e96 : S 6 :=
.betaPi (e94) (e95)

private def e97 : S 5 :=
.congSigmaCod (e58) (e96)

private def e98 : S 5 :=
.congPiDom (e97) (e59)

private def e99 : S 4 :=
.congPiCod (e20) (e98)

private def e100 : S 4 :=
.congPiDom (e99) (e36)

private def e101 : C 4 :=
.single (e100)

private def e102 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))

private def e103 : C 4 :=
.refl (e102)

private def e104 : C 4 :=
.trans (e101) (e103)

private def e105 : C 4 :=
.trans (e93) (e104)

private def e106 : C 4 :=
.symm (e103)

private def e107 : C 4 :=
.trans (e103) (e106)

private def e108 : C 4 :=
.trans (e105) (e107)

private def e109 : C 4 :=
.trans (e92) (e108)

private def e110 : C 4 :=
.trans (e109) (e106)

private def e111 : C 4 :=
.trans (e92) (e110)

private def e112 : C 4 :=
.trans (e111) (e103)

private def e113 : C 4 :=
.trans (e112) (e106)

private def e114 : C 4 :=
.trans (e92) (e113)

private def e115 : C 4 :=
.trans (e92) (e114)

private def e116 : C 4 :=
.trans (e115) (e106)

private def e117 : C 4 :=
.trans (e92) (e116)

private def e118 : C 4 :=
.trans (e117) (e103)

private def e119 : C 4 :=
.trans (e118) (e106)

private def e120 : C 4 :=
.trans (e92) (e119)

private def e121 : T 4 :=
.convert (e37) (e38) (e67) (e91) (e120)

private def e122 : T 6 :=
.fstElim (e94) (e62)

private def e123 : T 6 :=
.idForm (e7) (e62) (e62) (e122)

private def e124 : T 5 :=
.lamIntro (e69) (e71) (e123)

private def e125 : T 4 :=
.lamIntro (e68) (e72) (e124)

private def e126 : T 4 :=
.appElim (e35) (e36) (e121) (e125)

private def e127 : T 4 :=
.appElim (e33) (e34) (e126) (e23)

private def e128 : T 4 :=
.appElim (e32) (e21) (e127) (e23)

private def e129 : T 3 :=
.sigmaForm (e7) (e7) (e31) (e128)

private def e130 : T 3 :=
.piForm (e16) (e7) (e129) (e50)

private def e131 : T 2 :=
.piForm (e7) (e8) (e15) (e130)

private def e132 : T 1 :=
.piForm (e2) (e5) (e6) (e131)

private def e133 : T 0 :=
.piForm (e2) (e3) (e4) (e132)

private def e134 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)

private def e135 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5))))

private def e136 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))

private def e137 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2)

private def e138 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)))))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)))

private def e139 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List.nil)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7)))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                    `CumulativeTower.List.cons)
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7)
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8))
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))))))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))

private def e140 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))

private def e141 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))

private def e142 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List.nil)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                    `CumulativeTower.List.cons)
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8)
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 9))
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))))))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))

private def e143 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List.nil)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7))
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                      `CumulativeTower.List.cons)
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8)
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 9))
                        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))))))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))))

private def e144 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))

private def e145 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List.nil)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                      `CumulativeTower.List.cons)
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5))
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))))))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))))

private def e146 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
                (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
                (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))))

private def e147 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))

private def e148 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))

private def e149 : Tower.Tm 1 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))

private def e150 : T 1 :=
.const (e11) (e12)

private def e151 : T 1 :=
.var

private def e152 : T 1 :=
.appElim (e149) (e9) (e150) (e151)

private def e153 : T 2 :=
.headType

private def e154 : T 1 :=
.piForm (e7) (e2) (e152) (e153)

private def e155 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))

private def e156 : Tower.Tm 2 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)

private def e157 : Tower.Tm 3 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)

private def e158 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))

private def e159 : T 0 :=
.piForm (e2) (e7) (e4) (e152)

private def e160 : T 2 :=
.const (e158) (e159)

private def e161 : T 2 :=
.appElim (e9) (e157) (e160) (e14)

private def e162 : T 2 :=
.appElim (e156) (e10) (e14) (e161)

private def e163 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))

private def e164 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))

private def e165 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)

private def e166 : T 5 :=
.appElim (e165) (e59) (e26) (e26)

private def e167 : Tower.Tm 6 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)

private def e168 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)

private def e169 : Tower.Tm 6 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5

private def e170 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7))

private def e171 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2)))

private def e172 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))

private def e173 : T 2 :=
.piForm (e7) (e7) (e15) (e48)

private def e174 : T 1 :=
.piForm (e7) (e16) (e151) (e173)

private def e175 : T 0 :=
.piForm (e2) (e164) (e4) (e174)

private def e176 : T 6 :=
.const (e172) (e175)

private def e177 : T 6 :=
.appElim (e59) (e171) (e176) (e62)

private def e178 : T 6 :=
.appElim (e169) (e170) (e177) (e62)

private def e179 : T 6 :=
.appElim (e167) (e168) (e178) (e62)

private def e180 : T 6 :=
.appElim (e167) (e75) (e62) (e179)

private def e181 : T 5 :=
.piForm (e7) (e7) (e166) (e180)

private def e182 : T 4 :=
.piForm (e7) (e16) (e50) (e181)

private def e183 : T 3 :=
.piForm (e7) (e164) (e19) (e182)

private def e184 : T 4 :=
.piForm (e7) (e7) (e50) (e166)

private def e185 : T 3 :=
.piForm (e163) (e16) (e183) (e184)

private def e186 : T 2 :=
.piForm (e7) (e155) (e162) (e185)

private def e187 : T 1 :=
.piForm (e22) (e148) (e154) (e186)

private def e188 : T 0 :=
.piForm (e2) (e147) (e4) (e187)

private def e189 : T 4 :=
.const (e146) (e188)

private def e190 : T 4 :=
.appElim (e17) (e145) (e189) (e66)

private def e191 : T 4 :=
.appElim (e17) (e21) (e49) (e66)

private def e192 : T 4 :=
.piForm (e7) (e2) (e191) (e24)

private def e193 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))

private def e194 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))

private def e195 : Tower.Tm 6 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)

private def e196 : T 5 :=
.const (e158) (e159)

private def e197 : T 6 :=
.piForm (e7) (e2) (e62) (e88)

private def e198 : T 6 :=
.lamIntro (e22) (e197) (e79)

private def e199 : T 6 :=
.appElim (e169) (e75) (e198) (e62)

private def e200 : T 5 :=
.sigmaForm (e7) (e7) (e26) (e199)

private def e201 : T 5 :=
.cumul (e16) (e200)

private def e202 : T 5 :=
.appElim (e21) (e195) (e196) (e201)

private def e203 : T 5 :=
.appElim (e194) (e59) (e26) (e202)

private def e204 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))

private def e205 : T 6 :=
.sigmaForm (e7) (e7) (e62) (e79)

private def e206 : T 7 :=
.const (e11) (e12)

private def e207 : Tower.Tm 8 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7

private def e208 : Tower.Tm 9 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))

private def e209 : T 9 :=
.headType

private def e210 : T 8 :=
.piForm (e7) (e2) (e82) (e209)

private def e211 : T 9 :=
.var

private def e212 : T 8 :=
.lamIntro (e22) (e210) (e211)

private def e213 : T 8 :=
.appElim (e207) (e208) (e212) (e82)

private def e214 : T 7 :=
.sigmaForm (e7) (e7) (e79) (e213)

private def e215 : T 7 :=
.cumul (e16) (e214)

private def e216 : T 7 :=
.appElim (e75) (e78) (e206) (e215)

private def e217 : Tower.Tm 8 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))

private def e218 : T 8 :=
.appElim (e217) (e208) (e82) (e82)

private def e219 : Tower.Tm 9 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 9))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))

private def e220 : Tower.Tm 10 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))

private def e221 : Tower.Tm 10 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 9)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 10))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))

private def e222 : Tower.Tm 9 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8)

private def e223 : Tower.Tm 10 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 9)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 10))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 10)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 11))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))

private def e224 : Tower.Tm 9 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 9))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 9)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 10))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 10)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 11))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))))

private def e225 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))

private def e226 : Tower.Tm 10 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2)))

private def e227 : T 9 :=
.const (e172) (e175)

private def e228 : Tower.Tm 10 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 9

private def e229 : Tower.Tm 11 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))

private def e230 : T 10 :=
.var

private def e231 : T 11 :=
.headType

private def e232 : T 10 :=
.piForm (e7) (e2) (e230) (e231)

private def e233 : T 11 :=
.var

private def e234 : T 10 :=
.lamIntro (e22) (e232) (e233)

private def e235 : T 10 :=
.appElim (e228) (e229) (e234) (e230)

private def e236 : T 9 :=
.sigmaForm (e7) (e7) (e211) (e235)

private def e237 : T 9 :=
.cumul (e16) (e236)

private def e238 : T 9 :=
.appElim (e208) (e226) (e227) (e237)

private def e239 : T 9 :=
.sigmaForm (e7) (e7) (e211) (e230)

private def e240 : T 10 :=
.const (e11) (e12)

private def e241 : Tower.Tm 11 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 10

private def e242 : Tower.Tm 12 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))

private def e243 : T 12 :=
.headType

private def e244 : T 11 :=
.piForm (e7) (e2) (e233) (e243)

private def e245 : T 12 :=
.var

private def e246 : T 11 :=
.lamIntro (e22) (e244) (e245)

private def e247 : T 11 :=
.appElim (e241) (e242) (e246) (e233)

private def e248 : T 10 :=
.sigmaForm (e7) (e7) (e230) (e247)

private def e249 : T 10 :=
.cumul (e16) (e248)

private def e250 : T 10 :=
.appElim (e220) (e229) (e240) (e249)

private def e251 : T 11 :=
.const (e11) (e12)

private def e252 : Tower.Tm 12 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 11

private def e253 : Tower.Tm 13 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))

private def e254 : T 13 :=
.headType

private def e255 : T 12 :=
.piForm (e7) (e2) (e245) (e254)

private def e256 : T 13 :=
.var

private def e257 : T 12 :=
.lamIntro (e22) (e255) (e256)

private def e258 : T 12 :=
.appElim (e252) (e253) (e257) (e245)

private def e259 : T 11 :=
.sigmaForm (e7) (e7) (e233) (e258)

private def e260 : T 11 :=
.cumul (e16) (e259)

private def e261 : T 11 :=
.appElim (e229) (e242) (e251) (e260)

private def e262 : T 10 :=
.piForm (e7) (e7) (e250) (e261)

private def e263 : T 9 :=
.piForm (e16) (e16) (e239) (e262)

private def e264 : C 9 :=
.refl (e224)

private def e265 : C 9 :=
.trans (e264) (e264)

private def e266 : Tower.Tm 9 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8

private def e267 : Tower.Tm 11 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 9

private def e268 : Tower.Tm 10 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0

private def e269 : S 10 :=
.betaPi (e267) (e268)

private def e270 : S 9 :=
.congSigmaCod (e266) (e269)

private def e271 : S 9 :=
.congPiDom (e270) (e223)

private def e272 : C 9 :=
.single (e271)

private def e273 : Tower.Tm 9 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 9)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 10))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 10)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 11))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))))

private def e274 : C 9 :=
.refl (e273)

private def e275 : C 9 :=
.trans (e272) (e274)

private def e276 : C 9 :=
.trans (e265) (e275)

private def e277 : C 9 :=
.symm (e274)

private def e278 : C 9 :=
.trans (e274) (e277)

private def e279 : C 9 :=
.trans (e276) (e278)

private def e280 : C 9 :=
.trans (e264) (e279)

private def e281 : C 9 :=
.trans (e280) (e277)

private def e282 : C 9 :=
.trans (e264) (e281)

private def e283 : C 9 :=
.trans (e282) (e274)

private def e284 : C 9 :=
.trans (e283) (e277)

private def e285 : C 9 :=
.trans (e264) (e284)

private def e286 : T 9 :=
.convert (e224) (e225) (e238) (e263) (e285)

private def e287 : T 9 :=
.appElim (e222) (e223) (e286) (e211)

private def e288 : T 9 :=
.appElim (e219) (e221) (e287) (e211)

private def e289 : T 9 :=
.appElim (e219) (e220) (e211) (e288)

private def e290 : T 8 :=
.piForm (e7) (e7) (e218) (e289)

private def e291 : T 7 :=
.piForm (e7) (e16) (e216) (e290)

private def e292 : T 6 :=
.piForm (e16) (e164) (e205) (e291)

private def e293 : T 7 :=
.piForm (e7) (e7) (e216) (e218)

private def e294 : T 6 :=
.piForm (e204) (e16) (e292) (e293)

private def e295 : T 5 :=
.piForm (e7) (e193) (e203) (e294)

private def e296 : T 4 :=
.piForm (e22) (e140) (e192) (e295)

private def e297 : C 4 :=
.refl (e143)

private def e298 : C 4 :=
.trans (e297) (e297)

private def e299 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List.nil)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))

private def e300 : Tower.Tm 8 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6

private def e301 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0

private def e302 : S 7 :=
.betaPi (e300) (e301)

private def e303 : S 6 :=
.congSigmaCod (e169) (e302)

private def e304 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List.cons)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8)
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 9))
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))))

private def e305 : S 6 :=
.congPiDom (e303) (e304)

private def e306 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))

private def e307 : S 6 :=
.congPiDom (e305) (e306)

private def e308 : S 5 :=
.congPiCod (e299) (e307)

private def e309 : S 4 :=
.congPiCod (e141) (e308)

private def e310 : C 4 :=
.single (e309)

private def e311 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List.nil)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7))
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                      `CumulativeTower.List.cons)
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8)
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 9))
                        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))))))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))))

private def e312 : C 4 :=
.refl (e311)

private def e313 : C 4 :=
.trans (e310) (e312)

private def e314 : C 4 :=
.trans (e298) (e313)

private def e315 : C 4 :=
.symm (e312)

private def e316 : C 4 :=
.trans (e312) (e315)

private def e317 : C 4 :=
.trans (e314) (e316)

private def e318 : C 4 :=
.trans (e297) (e317)

private def e319 : C 4 :=
.trans (e318) (e315)

private def e320 : C 4 :=
.trans (e297) (e319)

private def e321 : C 4 :=
.trans (e320) (e312)

private def e322 : C 4 :=
.trans (e321) (e315)

private def e323 : C 4 :=
.trans (e297) (e322)

private def e324 : C 4 :=
.trans (e323) (e312)

private def e325 : C 4 :=
.trans (e324) (e315)

private def e326 : C 4 :=
.trans (e297) (e325)

private def e327 : C 4 :=
.trans (e297) (e326)

private def e328 : C 4 :=
.trans (e327) (e315)

private def e329 : C 4 :=
.trans (e297) (e328)

private def e330 : C 4 :=
.trans (e297) (e329)

private def e331 : C 4 :=
.trans (e330) (e315)

private def e332 : C 4 :=
.trans (e297) (e331)

private def e333 : T 4 :=
.convert (e143) (e144) (e190) (e296) (e332)

private def e334 : T 4 :=
.lamIntro (e22) (e192) (e74)

private def e335 : T 4 :=
.appElim (e141) (e142) (e333) (e334)

private def e336 : T 7 :=
.appElim (e75) (e78) (e206) (e79)

private def e337 : T 8 :=
.const (e11) (e12)

private def e338 : T 8 :=
.appElim (e78) (e208) (e337) (e82)

private def e339 : T 7 :=
.piForm (e7) (e7) (e336) (e338)

private def e340 : T 6 :=
.piForm (e7) (e16) (e87) (e339)

private def e341 : T 5 :=
.piForm (e16) (e164) (e70) (e340)

private def e342 : T 6 :=
.piForm (e7) (e7) (e87) (e336)

private def e343 : T 5 :=
.piForm (e204) (e16) (e341) (e342)

private def e344 : T 4 :=
.piForm (e7) (e193) (e50) (e343)

private def e345 : C 4 :=
.refl (e139)

private def e346 : C 4 :=
.trans (e345) (e345)

private def e347 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List.nil)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))

private def e348 : S 4 :=
.betaPi (e134) (e347)

private def e349 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7)))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List.cons)
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7)
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8))
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))))))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))

private def e350 : S 4 :=
.congPiDom (e348) (e349)

private def e351 : C 4 :=
.single (e350)

private def e352 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7)))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                    `CumulativeTower.List.cons)
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7)
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8))
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))))))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))

private def e353 : C 4 :=
.refl (e352)

private def e354 : C 4 :=
.trans (e353) (e353)

private def e355 : C 4 :=
.trans (e351) (e354)

private def e356 : C 4 :=
.trans (e346) (e355)

private def e357 : C 4 :=
.symm (e354)

private def e358 : C 4 :=
.trans (e353) (e357)

private def e359 : C 4 :=
.trans (e356) (e358)

private def e360 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)

private def e361 : Tower.Tm 6 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))

private def e362 : Tower.Tm 8 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)

private def e363 : S 7 :=
.betaPi (e362) (e301)

private def e364 : Tower.Tm 8 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7)))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List.cons)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))

private def e365 : S 7 :=
.congPiDom (e363) (e364)

private def e366 : S 6 :=
.congPiCod (e361) (e365)

private def e367 : S 5 :=
.congPiCod (e360) (e366)

private def e368 : Tower.Tm 6 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))

private def e369 : S 5 :=
.congPiDom (e367) (e368)

private def e370 : S 4 :=
.congPiCod (e137) (e369)

private def e371 : C 4 :=
.single (e370)

private def e372 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7)))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                    `CumulativeTower.List.cons)
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7)
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8))
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))))))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))

private def e373 : C 4 :=
.refl (e372)

private def e374 : C 4 :=
.trans (e373) (e373)

private def e375 : C 4 :=
.trans (e371) (e374)

private def e376 : C 4 :=
.trans (e354) (e375)

private def e377 : C 4 :=
.symm (e374)

private def e378 : C 4 :=
.trans (e373) (e377)

private def e379 : C 4 :=
.trans (e376) (e378)

private def e380 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)

private def e381 : Tower.Tm 9 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7)

private def e382 : Tower.Tm 8 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List.cons)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)

private def e383 : S 8 :=
.betaPi (e381) (e382)

private def e384 : S 7 :=
.congPiCod (e380) (e383)

private def e385 : S 6 :=
.congPiCod (e361) (e384)

private def e386 : S 5 :=
.congPiCod (e360) (e385)

private def e387 : S 5 :=
.congPiDom (e386) (e368)

private def e388 : S 4 :=
.congPiCod (e137) (e387)

private def e389 : C 4 :=
.single (e388)

private def e390 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)))))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))

private def e391 : C 4 :=
.refl (e390)

private def e392 : C 4 :=
.trans (e391) (e391)

private def e393 : C 4 :=
.trans (e389) (e392)

private def e394 : C 4 :=
.trans (e374) (e393)

private def e395 : C 4 :=
.symm (e392)

private def e396 : C 4 :=
.trans (e391) (e395)

private def e397 : C 4 :=
.trans (e394) (e396)

private def e398 : C 4 :=
.trans (e379) (e397)

private def e399 : C 4 :=
.symm (e391)

private def e400 : C 4 :=
.trans (e398) (e399)

private def e401 : C 4 :=
.trans (e353) (e400)

private def e402 : C 4 :=
.trans (e353) (e401)

private def e403 : C 4 :=
.trans (e402) (e399)

private def e404 : C 4 :=
.trans (e353) (e403)

private def e405 : C 4 :=
.trans (e353) (e404)

private def e406 : C 4 :=
.trans (e405) (e399)

private def e407 : C 4 :=
.trans (e353) (e406)

private def e408 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))))

private def e409 : S 6 :=
.congPiCod (e361) (e363)

private def e410 : S 5 :=
.congPiCod (e408) (e409)

private def e411 : S 4 :=
.congPiCod (e137) (e410)

private def e412 : C 4 :=
.single (e411)

private def e413 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)))))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5))))

private def e414 : C 4 :=
.refl (e413)

private def e415 : C 4 :=
.trans (e414) (e414)

private def e416 : C 4 :=
.trans (e412) (e415)

private def e417 : C 4 :=
.trans (e392) (e416)

private def e418 : C 4 :=
.symm (e415)

private def e419 : C 4 :=
.trans (e414) (e418)

private def e420 : C 4 :=
.trans (e417) (e419)

private def e421 : C 4 :=
.trans (e391) (e420)

private def e422 : C 4 :=
.symm (e414)

private def e423 : C 4 :=
.trans (e421) (e422)

private def e424 : C 4 :=
.trans (e391) (e423)

private def e425 : C 4 :=
.trans (e407) (e424)

private def e426 : C 4 :=
.trans (e425) (e422)

private def e427 : C 4 :=
.trans (e353) (e426)

private def e428 : C 4 :=
.trans (e359) (e427)

private def e429 : C 4 :=
.trans (e428) (e422)

private def e430 : C 4 :=
.trans (e345) (e429)

private def e431 : T 4 :=
.convert (e139) (e140) (e335) (e344) (e430)

private def e432 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)

private def e433 : T 4 :=
.const (e158) (e159)

private def e434 : T 4 :=
.appElim (e17) (e432) (e433) (e23)

private def e435 : T 4 :=
.appElim (e137) (e138) (e431) (e434)

private def e436 : T 4 :=
.sigmaForm (e7) (e7) (e23) (e26)

private def e437 : T 5 :=
.appElim (e21) (e59) (e73) (e201)

private def e438 : T 6 :=
.appElim (e59) (e75) (e76) (e62)

private def e439 : T 6 :=
.piForm (e7) (e7) (e438) (e336)

private def e440 : T 5 :=
.piForm (e7) (e16) (e437) (e439)

private def e441 : T 4 :=
.piForm (e16) (e164) (e436) (e440)

private def e442 : Tower.Tm 8 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7))

private def e443 : Tower.Tm 8 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2)))

private def e444 : T 7 :=
.const (e172) (e175)

private def e445 : T 7 :=
.appElim (e75) (e443) (e444) (e79)

private def e446 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)

private def e447 : T 7 :=
.sigmaForm (e7) (e7) (e79) (e82)

private def e448 : T 7 :=
.piForm (e16) (e7) (e447) (e82)

private def e449 : Tower.Tm 9 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7

private def e450 : T 8 :=
.sndElim (e207) (e449) (e82)

private def e451 : T 7 :=
.lamIntro (e8) (e448) (e450)

private def e452 : T 7 :=
.appElim (e446) (e300) (e451) (e79)

private def e453 : T 7 :=
.appElim (e94) (e442) (e445) (e452)

private def e454 : T 7 :=
.appElim (e380) (e362) (e453) (e79)

private def e455 : T 6 :=
.lamIntro (e16) (e439) (e454)

private def e456 : T 5 :=
.lamIntro (e164) (e440) (e455)

private def e457 : T 4 :=
.lamIntro (e204) (e441) (e456)

private def e458 : T 4 :=
.appElim (e135) (e136) (e435) (e457)

private def e459 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.List.mapRel)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.id
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.fst
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)

private def e460 : T 4 :=
.fstElim (e459) (e23)

private def e461 : T 4 :=
.appElim (e32) (e134) (e458) (e460)

private def e462 : T 3 :=
.lamIntro (e8) (e130) (e461)

private def e463 : T 2 :=
.lamIntro (e5) (e131) (e462)

private def e464 : T 1 :=
.lamIntro (e3) (e132) (e463)

private def e465 : T 0 :=
.lamIntro (e1) (e133) (e464)

def submission : FormationSensitiveElaboration.Submission Tower.Head NativeListResultView.decoder.Code 0 :=
{ context := e0, term := e465 }


end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeListResultView.Evidence

import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAll

/-! Generated finite evidence; independently replayed by the checking companion. -/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.TypeFormation
open Presentation Declaration
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

private abbrev S (n : Nat) := StructuralConversionCode.StepCode Tower.Head NativeVectorAll.decoder.Code n
private abbrev C (n : Nat) := StructuralConversionCode.Code Tower.Head NativeVectorAll.decoder.Code n
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
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)

private def e11 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0))

private def e12 : T 2 :=
.const (e11) (e2)

private def e13 : X 3 :=
.snoc (e9) (e10) (e12)

private def e14 : Tower.Tm 3 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat

private def e15 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))

private def e16 : Tower.Tm 3 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))

private def e17 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))

private def e18 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))

private def e19 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))

private def e20 : T 1 :=
.const (e11) (e2)

private def e21 : T 1 :=
.piForm (e10) (e1) (e20) (e7)

private def e22 : T 0 :=
.piForm (e1) (e19) (e2) (e21)

private def e23 : T 3 :=
.const (e18) (e22)

private def e24 : T 3 :=
.var

private def e25 : T 3 :=
.appElim (e16) (e17) (e23) (e24)

private def e26 : T 3 :=
.appElim (e14) (e15) (e25) (e24)

private def e27 : X 4 :=
.snoc (e13) (e5) (e26)

private def e28 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)

private def e29 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))

private def e30 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat

private def e31 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))

private def e32 : Tower.Tm 4 :=
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
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))))

private def e33 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))

private def e34 : Tower.Tm 5 :=
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
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))

private def e35 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))
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
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
                        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
                        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))
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
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
                    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))))

private def e36 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ
                (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ
                (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))))
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))))

private def e37 : Tower.Tm 4 :=
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
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))

private def e38 : Tower.Tm 5 :=
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

private def e39 : Tower.Tm 5 :=
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
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))))
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

private def e40 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
                (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
                (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
                  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ
                    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))
                  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ
                    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))))
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ
                (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))))))

private def e41 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
                (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ
                  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))
                (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ
                  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))))
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))))

private def e42 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))

private def e43 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))

private def e44 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))

private def e45 : Tower.Tm 2 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat

private def e46 : Tower.Tm 2 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))

private def e47 : Tower.Tm 3 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))

private def e48 : T 2 :=
.const (e18) (e22)

private def e49 : T 2 :=
.var

private def e50 : T 2 :=
.appElim (e46) (e47) (e48) (e49)

private def e51 : T 2 :=
.appElim (e45) (e16) (e50) (e49)

private def e52 : T 3 :=
.headType

private def e53 : T 2 :=
.piForm (e5) (e44) (e51) (e52)

private def e54 : T 1 :=
.piForm (e10) (e43) (e20) (e53)

private def e55 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ
              (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))))
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))

private def e56 : Tower.Tm 2 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero)

private def e57 : Tower.Tm 3 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))

private def e58 : Tower.Tm 3 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))

private def e59 : T 0 :=
.const (e11) (e2)

private def e60 : T 2 :=
.const (e10) (e59)

private def e61 : T 2 :=
.appElim (e45) (e58) (e49) (e60)

private def e62 : Tower.Tm 3 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero)

private def e63 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))

private def e64 : Tower.Tm 1 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat

private def e65 : Tower.Tm 1 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))

private def e66 : Tower.Tm 2 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))

private def e67 : T 1 :=
.const (e18) (e22)

private def e68 : T 1 :=
.appElim (e65) (e66) (e67) (e6)

private def e69 : T 1 :=
.const (e10) (e59)

private def e70 : T 1 :=
.appElim (e64) (e46) (e68) (e69)

private def e71 : T 0 :=
.piForm (e1) (e5) (e2) (e70)

private def e72 : T 2 :=
.const (e63) (e71)

private def e73 : T 2 :=
.appElim (e46) (e62) (e72) (e49)

private def e74 : T 2 :=
.appElim (e56) (e57) (e61) (e73)

private def e75 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))))

private def e76 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))

private def e77 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))

private def e78 : T 3 :=
.const (e11) (e2)

private def e79 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))

private def e80 : T 4 :=
.var

private def e81 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))

private def e82 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat

private def e83 : Tower.Tm 6 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))

private def e84 : Tower.Tm 6 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))

private def e85 : T 5 :=
.const (e18) (e22)

private def e86 : T 5 :=
.var

private def e87 : T 5 :=
.appElim (e29) (e84) (e85) (e86)

private def e88 : T 5 :=
.appElim (e82) (e83) (e87) (e86)

private def e89 : Tower.Tm 6 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2)

private def e90 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))

private def e91 : Tower.Tm 6 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat

private def e92 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))

private def e93 : T 6 :=
.var

private def e94 : T 6 :=
.appElim (e91) (e92) (e93) (e93)

private def e95 : T 6 :=
.appElim (e89) (e90) (e94) (e93)

private def e96 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))

private def e97 : Tower.Tm 8 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))

private def e98 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat

private def e99 : Tower.Tm 8 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))

private def e100 : T 7 :=
.var

private def e101 : Tower.Tm 8 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat

private def e102 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0))

private def e103 : T 0 :=
.piForm (e10) (e10) (e59) (e20)

private def e104 : T 7 :=
.const (e102) (e103)

private def e105 : T 7 :=
.appElim (e98) (e101) (e104) (e100)

private def e106 : T 7 :=
.appElim (e98) (e99) (e100) (e105)

private def e107 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)

private def e108 : Tower.Tm 8 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))

private def e109 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6

private def e110 : Tower.Tm 8 :=
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

private def e111 : Tower.Tm 8 :=
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

private def e112 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))

private def e113 : Tower.Tm 8 :=
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

private def e114 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))

private def e115 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))

private def e116 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))

private def e117 : Tower.Head :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))

private def e118 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))

private def e119 : T 4 :=
.const (e18) (e22)

private def e120 : T 4 :=
.appElim (e15) (e118) (e119) (e80)

private def e121 : T 4 :=
.const (e102) (e103)

private def e122 : T 4 :=
.appElim (e30) (e82) (e121) (e80)

private def e123 : T 4 :=
.appElim (e30) (e29) (e120) (e122)

private def e124 : T 3 :=
.piForm (e5) (e5) (e26) (e123)

private def e125 : T 2 :=
.piForm (e5) (e117) (e49) (e124)

private def e126 : T 1 :=
.piForm (e10) (e116) (e20) (e125)

private def e127 : T 0 :=
.piForm (e1) (e115) (e2) (e126)

private def e128 : T 7 :=
.const (e114) (e127)

private def e129 : T 7 :=
.appElim (e112) (e113) (e128) (e100)

private def e130 : T 7 :=
.appElim (e98) (e111) (e129) (e100)

private def e131 : T 7 :=
.appElim (e109) (e110) (e130) (e100)

private def e132 : T 7 :=
.appElim (e107) (e108) (e131) (e100)

private def e133 : T 7 :=
.appElim (e96) (e97) (e106) (e132)

private def e134 : T 6 :=
.piForm (e1) (e1) (e95) (e133)

private def e135 : T 5 :=
.piForm (e5) (e81) (e88) (e134)

private def e136 : T 4 :=
.piForm (e5) (e79) (e80) (e135)

private def e137 : T 3 :=
.piForm (e10) (e77) (e78) (e136)

private def e138 : T 4 :=
.const (e11) (e2)

private def e139 : Tower.Tm 6 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)

private def e140 : T 6 :=
.appElim (e139) (e90) (e94) (e93)

private def e141 : T 5 :=
.piForm (e5) (e1) (e88) (e140)

private def e142 : T 4 :=
.piForm (e10) (e4) (e138) (e141)

private def e143 : T 3 :=
.piForm (e75) (e76) (e137) (e142)

private def e144 : T 2 :=
.piForm (e1) (e55) (e74) (e143)

private def e145 : T 1 :=
.piForm (e42) (e36) (e54) (e144)

private def e146 : T 0 :=
.piForm (e1) (e41) (e2) (e145)

private def e147 : T 4 :=
.const (e40) (e146)

private def e148 : T 4 :=
.appElim (e15) (e39) (e147) (e80)

private def e149 : T 6 :=
.headType

private def e150 : T 5 :=
.piForm (e5) (e44) (e88) (e149)

private def e151 : T 4 :=
.piForm (e10) (e43) (e138) (e150)

private def e152 : T 5 :=
.lamIntro (e43) (e150) (e149)

private def e153 : T 4 :=
.lamIntro (e42) (e151) (e152)

private def e154 : T 4 :=
.appElim (e37) (e38) (e148) (e153)

private def e155 : T 4 :=
.headType

private def e156 : T 5 :=
.const (e11) (e2)

private def e157 : Tower.Tm 8 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))

private def e158 : Tower.Tm 8 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))

private def e159 : T 7 :=
.const (e18) (e22)

private def e160 : T 7 :=
.appElim (e112) (e158) (e159) (e100)

private def e161 : T 7 :=
.appElim (e98) (e157) (e160) (e100)

private def e162 : T 8 :=
.headType

private def e163 : T 9 :=
.headType

private def e164 : T 8 :=
.piForm (e1) (e1) (e162) (e163)

private def e165 : T 7 :=
.piForm (e5) (e81) (e161) (e164)

private def e166 : T 6 :=
.piForm (e5) (e79) (e93) (e165)

private def e167 : T 5 :=
.piForm (e10) (e77) (e156) (e166)

private def e168 : T 6 :=
.const (e11) (e2)

private def e169 : T 7 :=
.piForm (e5) (e1) (e161) (e162)

private def e170 : T 6 :=
.piForm (e10) (e4) (e168) (e169)

private def e171 : T 5 :=
.piForm (e75) (e76) (e167) (e170)

private def e172 : T 4 :=
.piForm (e1) (e55) (e155) (e171)

private def e173 : C 4 :=
.refl (e35)

private def e174 : C 4 :=
.trans (e173) (e173)

private def e175 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))

private def e176 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero

private def e177 : S 4 :=
.betaPi (e175) (e176)

private def e178 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.nil)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)

private def e179 : S 4 :=
.congAppFun (e177) (e178)

private def e180 : Tower.Tm 5 :=
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
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
                      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
                      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))
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
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
                  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))))

private def e181 : S 4 :=
.congPiDom (e179) (e180)

private def e182 : C 4 :=
.single (e181)

private def e183 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))
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
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
                        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
                        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))
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
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
                    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))))

private def e184 : C 4 :=
.refl (e183)

private def e185 : C 4 :=
.trans (e182) (e184)

private def e186 : C 4 :=
.trans (e174) (e185)

private def e187 : C 4 :=
.trans (e184) (e184)

private def e188 : C 4 :=
.trans (e186) (e187)

private def e189 : S 4 :=
.betaPi (e29) (e178)

private def e190 : S 4 :=
.congPiDom (e189) (e180)

private def e191 : C 4 :=
.single (e190)

private def e192 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))
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
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
                        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
                        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))
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
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
                    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))))

private def e193 : C 4 :=
.refl (e192)

private def e194 : C 4 :=
.trans (e191) (e193)

private def e195 : C 4 :=
.trans (e188) (e194)

private def e196 : C 4 :=
.trans (e193) (e193)

private def e197 : C 4 :=
.trans (e196) (e193)

private def e198 : Tower.Tm 6 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5

private def e199 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)

private def e200 : Tower.Tm 9 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))

private def e201 : Tower.Tm 8 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2

private def e202 : S 8 :=
.betaPi (e200) (e201)

private def e203 : Tower.Tm 8 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0

private def e204 : S 8 :=
.congAppFun (e202) (e203)

private def e205 : Tower.Tm 9 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.cons)
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))

private def e206 : S 8 :=
.congPiDom (e204) (e205)

private def e207 : S 7 :=
.congPiCod (e199) (e206)

private def e208 : S 6 :=
.congPiCod (e198) (e207)

private def e209 : S 5 :=
.congPiCod (e82) (e208)

private def e210 : Tower.Tm 6 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
                (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))

private def e211 : S 5 :=
.congPiDom (e209) (e210)

private def e212 : S 4 :=
.congPiCod (e15) (e211)

private def e213 : C 4 :=
.single (e212)

private def e214 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))
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
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
                    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
                        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))
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
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
                    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))))

private def e215 : C 4 :=
.refl (e214)

private def e216 : C 4 :=
.trans (e213) (e215)

private def e217 : C 4 :=
.trans (e196) (e216)

private def e218 : C 4 :=
.trans (e217) (e215)

private def e219 : Tower.Tm 9 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))

private def e220 : S 8 :=
.betaPi (e219) (e203)

private def e221 : S 8 :=
.congPiDom (e220) (e205)

private def e222 : S 7 :=
.congPiCod (e199) (e221)

private def e223 : S 6 :=
.congPiCod (e198) (e222)

private def e224 : S 5 :=
.congPiCod (e82) (e223)

private def e225 : S 5 :=
.congPiDom (e224) (e210)

private def e226 : S 4 :=
.congPiCod (e15) (e225)

private def e227 : C 4 :=
.single (e226)

private def e228 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))
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
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
                (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
                      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
                        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))
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
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
                    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))))

private def e229 : C 4 :=
.refl (e228)

private def e230 : C 4 :=
.trans (e227) (e229)

private def e231 : C 4 :=
.trans (e218) (e230)

private def e232 : C 4 :=
.trans (e229) (e229)

private def e233 : C 4 :=
.trans (e229) (e232)

private def e234 : Tower.Tm 10 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))

private def e235 : Tower.Tm 9 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.succ)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3)

private def e236 : S 9 :=
.betaPi (e234) (e235)

private def e237 : Tower.Tm 9 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec.cons)
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8))
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)

private def e238 : S 9 :=
.congAppFun (e236) (e237)

private def e239 : S 8 :=
.congPiCod (e157) (e238)

private def e240 : S 7 :=
.congPiCod (e199) (e239)

private def e241 : S 6 :=
.congPiCod (e198) (e240)

private def e242 : S 5 :=
.congPiCod (e82) (e241)

private def e243 : S 5 :=
.congPiDom (e242) (e210)

private def e244 : S 4 :=
.congPiCod (e15) (e243)

private def e245 : C 4 :=
.single (e244)

private def e246 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))
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
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
                (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
                    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))
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
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
                    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))))

private def e247 : C 4 :=
.refl (e246)

private def e248 : C 4 :=
.trans (e245) (e247)

private def e249 : C 4 :=
.trans (e233) (e248)

private def e250 : C 4 :=
.trans (e247) (e247)

private def e251 : C 4 :=
.trans (e250) (e247)

private def e252 : C 4 :=
.trans (e251) (e247)

private def e253 : C 4 :=
.trans (e252) (e247)

private def e254 : C 4 :=
.trans (e249) (e253)

private def e255 : Tower.Tm 10 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))

private def e256 : S 9 :=
.betaPi (e255) (e237)

private def e257 : S 8 :=
.congPiCod (e157) (e256)

private def e258 : S 7 :=
.congPiCod (e199) (e257)

private def e259 : S 6 :=
.congPiCod (e198) (e258)

private def e260 : S 5 :=
.congPiCod (e82) (e259)

private def e261 : S 5 :=
.congPiDom (e260) (e210)

private def e262 : S 4 :=
.congPiCod (e15) (e261)

private def e263 : C 4 :=
.single (e262)

private def e264 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))
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
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
                (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
                (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))))
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
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
                  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
                    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))))

private def e265 : C 4 :=
.refl (e264)

private def e266 : C 4 :=
.trans (e263) (e265)

private def e267 : C 4 :=
.trans (e254) (e266)

private def e268 : C 4 :=
.trans (e231) (e267)

private def e269 : C 4 :=
.trans (e197) (e268)

private def e270 : C 4 :=
.trans (e193) (e269)

private def e271 : C 4 :=
.trans (e193) (e270)

private def e272 : C 4 :=
.trans (e265) (e265)

private def e273 : C 4 :=
.trans (e272) (e265)

private def e274 : Tower.Tm 5 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
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
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))))

private def e275 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)

private def e276 : Tower.Tm 8 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1

private def e277 : S 8 :=
.betaPi (e200) (e276)

private def e278 : S 8 :=
.congAppFun (e277) (e203)

private def e279 : S 7 :=
.congPiCod (e275) (e278)

private def e280 : S 6 :=
.congPiCod (e91) (e279)

private def e281 : S 5 :=
.congPiCod (e274) (e280)

private def e282 : S 4 :=
.congPiCod (e15) (e281)

private def e283 : C 4 :=
.single (e282)

private def e284 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))
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
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
                (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
                (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
                (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))))

private def e285 : C 4 :=
.refl (e284)

private def e286 : C 4 :=
.trans (e283) (e285)

private def e287 : C 4 :=
.trans (e272) (e286)

private def e288 : C 4 :=
.trans (e287) (e285)

private def e289 : S 7 :=
.congPiCod (e275) (e220)

private def e290 : S 6 :=
.congPiCod (e91) (e289)

private def e291 : S 5 :=
.congPiCod (e274) (e290)

private def e292 : S 4 :=
.congPiCod (e15) (e291)

private def e293 : C 4 :=
.single (e292)

private def e294 : Tower.Tm 4 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))
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
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
                (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
              (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
                (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))))))
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Vec)
            (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
          (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))))

private def e295 : C 4 :=
.refl (e294)

private def e296 : C 4 :=
.trans (e293) (e295)

private def e297 : C 4 :=
.trans (e288) (e296)

private def e298 : C 4 :=
.trans (e273) (e297)

private def e299 : C 4 :=
.trans (e265) (e298)

private def e300 : C 4 :=
.trans (e271) (e299)

private def e301 : C 4 :=
.trans (e195) (e300)

private def e302 : S 4 :=
.head (e5) (e5)

private def e303 : S 4 :=
.congPiDom (e302) (e34)

private def e304 : C 4 :=
.single (e303)

private def e305 : C 4 :=
.trans (e295) (e295)

private def e306 : C 4 :=
.trans (e305) (e295)

private def e307 : S 8 :=
.head (e5) (e5)

private def e308 : S 8 :=
.congPiDom (e307) (e219)

private def e309 : S 7 :=
.congPiCod (e199) (e308)

private def e310 : S 6 :=
.congPiCod (e198) (e309)

private def e311 : S 5 :=
.congPiCod (e82) (e310)

private def e312 : Tower.Tm 6 :=
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
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0))))

private def e313 : S 5 :=
.congPiDom (e311) (e312)

private def e314 : S 4 :=
.congPiCod (e15) (e313)

private def e315 : C 4 :=
.single (e314)

private def e316 : S 9 :=
.head (e5) (e5)

private def e317 : S 8 :=
.congPiCod (e157) (e316)

private def e318 : S 7 :=
.congPiCod (e199) (e317)

private def e319 : S 6 :=
.congPiCod (e198) (e318)

private def e320 : S 5 :=
.congPiCod (e82) (e319)

private def e321 : S 5 :=
.congPiDom (e320) (e312)

private def e322 : S 4 :=
.congPiCod (e15) (e321)

private def e323 : C 4 :=
.single (e322)

private def e324 : C 4 :=
.trans (e315) (e323)

private def e325 : C 4 :=
.trans (e306) (e324)

private def e326 : C 4 :=
.trans (e295) (e325)

private def e327 : C 4 :=
.trans (e295) (e326)

private def e328 : S 7 :=
.congPiCod (e275) (e307)

private def e329 : S 6 :=
.congPiCod (e91) (e328)

private def e330 : S 5 :=
.congPiCod (e274) (e329)

private def e331 : S 4 :=
.congPiCod (e15) (e330)

private def e332 : C 4 :=
.single (e331)

private def e333 : C 4 :=
.trans (e306) (e332)

private def e334 : C 4 :=
.trans (e295) (e333)

private def e335 : C 4 :=
.trans (e327) (e334)

private def e336 : C 4 :=
.trans (e304) (e335)

private def e337 : C 4 :=
.trans (e306) (e305)

private def e338 : C 4 :=
.trans (e295) (e337)

private def e339 : C 4 :=
.trans (e295) (e338)

private def e340 : C 4 :=
.trans (e306) (e295)

private def e341 : C 4 :=
.trans (e295) (e340)

private def e342 : C 4 :=
.trans (e339) (e341)

private def e343 : C 4 :=
.trans (e295) (e342)

private def e344 : C 4 :=
.symm (e343)

private def e345 : C 4 :=
.trans (e336) (e344)

private def e346 : C 4 :=
.trans (e301) (e345)

private def e347 : T 4 :=
.convert (e35) (e36) (e154) (e172) (e346)

private def e348 : T 4 :=
.const (e10) (e59)

private def e349 : T 4 :=
.idForm (e10) (e138) (e348) (e348)

private def e350 : T 4 :=
.cumul (e10) (e349)

private def e351 : T 4 :=
.appElim (e15) (e34) (e347) (e350)

private def e352 : Tower.Tm 7 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
  (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)))

private def e353 : T 6 :=
.const (e18) (e22)

private def e354 : T 6 :=
.appElim (e83) (e352) (e353) (e93)

private def e355 : T 6 :=
.appElim (e91) (e112) (e354) (e93)

private def e356 : T 7 :=
.headType

private def e357 : T 7 :=
.piForm (e1) (e1) (e356) (e162)

private def e358 : T 6 :=
.piForm (e5) (e81) (e355) (e357)

private def e359 : T 5 :=
.piForm (e5) (e79) (e86) (e358)

private def e360 : T 4 :=
.piForm (e10) (e77) (e138) (e359)

private def e361 : Tower.Tm 8 :=
Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 7

private def e362 : T 8 :=
.var

private def e363 : T 8 :=
.appElim (e361) (e219) (e362) (e362)

private def e364 : T 9 :=
.var

private def e365 : T 8 :=
.sigmaForm (e5) (e5) (e363) (e364)

private def e366 : T 8 :=
.cumul (e117) (e365)

private def e367 : T 7 :=
.lamIntro (e81) (e357) (e366)

private def e368 : T 6 :=
.lamIntro (e79) (e358) (e367)

private def e369 : T 5 :=
.lamIntro (e77) (e359) (e368)

private def e370 : T 4 :=
.lamIntro (e75) (e360) (e369)

private def e371 : T 4 :=
.appElim (e32) (e33) (e351) (e370)

private def e372 : T 4 :=
.appElim (e30) (e31) (e371) (e80)

private def e373 : T 4 :=
.appElim (e28) (e29) (e372) (e80)

def submission : FormationSensitiveElaboration.Submission Tower.Head NativeVectorAll.decoder.Code 4 :=
{ context := e27, term := e373 }


end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.TypeFormation

import Mathlib

/-! Shared definitions for the reduced C6 Boolean support cover. -/

namespace Krenn.CollapseSupportCover

structure Stratum where
  zero : BitVec 26
  component : Nat
deriving DecidableEq, Repr

structure ActiveCover where
  active : BitVec 14
  strata : List Stratum
deriving DecidableEq, Repr

def relationLeftActive (pattern : Fin 26 → Prop) : Fin 14 → Prop
  | 0 => pattern 0 ∧ pattern 7
  | 1 => pattern 0 ∧ pattern 13
  | 2 => pattern 1 ∧ pattern 8
  | 3 => pattern 1 ∧ pattern 23
  | 4 => pattern 3 ∧ pattern 25
  | 5 => pattern 4 ∧ pattern 20
  | 6 => pattern 5 ∧ pattern 13
  | 7 => pattern 6 ∧ pattern 19
  | 8 => pattern 9 ∧ pattern 16
  | 9 => pattern 9 ∧ pattern 18
  | 10 => pattern 10 ∧ pattern 17
  | 11 => pattern 10 ∧ pattern 21
  | 12 => pattern 14 ∧ pattern 22
  | 13 => pattern 15 ∧ pattern 25

def relationRightActive (pattern : Fin 26 → Prop) : Fin 14 → Prop
  | 0 => pattern 2 ∧ pattern 5
  | 1 => pattern 17 ∧ pattern 23
  | 2 => pattern 3 ∧ pattern 6
  | 3 => pattern 2 ∧ pattern 22
  | 4 => pattern 4 ∧ pattern 24
  | 5 => pattern 8 ∧ pattern 21
  | 6 => pattern 12 ∧ pattern 19
  | 7 => pattern 7 ∧ pattern 18
  | 8 => pattern 11 ∧ pattern 14
  | 9 => pattern 20
  | 10 => pattern 12 ∧ pattern 15
  | 11 => pattern 11
  | 12 => pattern 24
  | 13 => pattern 16

def Feasible (pattern : Fin 26 → Prop) : Prop :=
  (relationLeftActive pattern 0 ↔ relationRightActive pattern 0) ∧
    (relationLeftActive pattern 1 ↔ relationRightActive pattern 1) ∧
    (relationLeftActive pattern 2 ↔ relationRightActive pattern 2) ∧
    (relationLeftActive pattern 3 ↔ relationRightActive pattern 3) ∧
    (relationLeftActive pattern 4 ↔ relationRightActive pattern 4) ∧
    (relationLeftActive pattern 5 ↔ relationRightActive pattern 5) ∧
    (relationLeftActive pattern 6 ↔ relationRightActive pattern 6) ∧
    (relationLeftActive pattern 7 ↔ relationRightActive pattern 7) ∧
    (relationLeftActive pattern 8 ↔ relationRightActive pattern 8) ∧
    (relationLeftActive pattern 9 ↔ relationRightActive pattern 9) ∧
    (relationLeftActive pattern 10 ↔ relationRightActive pattern 10) ∧
    (relationLeftActive pattern 11 ↔ relationRightActive pattern 11) ∧
    (relationLeftActive pattern 12 ↔ relationRightActive pattern 12) ∧
    (relationLeftActive pattern 13 ↔ relationRightActive pattern 13)

def ActiveMatches (active : BitVec 14) (pattern : Fin 26 → Prop) : Prop :=
  (active.getLsbD 0 = true ↔ relationLeftActive pattern 0) ∧
    (active.getLsbD 1 = true ↔ relationLeftActive pattern 1) ∧
    (active.getLsbD 2 = true ↔ relationLeftActive pattern 2) ∧
    (active.getLsbD 3 = true ↔ relationLeftActive pattern 3) ∧
    (active.getLsbD 4 = true ↔ relationLeftActive pattern 4) ∧
    (active.getLsbD 5 = true ↔ relationLeftActive pattern 5) ∧
    (active.getLsbD 6 = true ↔ relationLeftActive pattern 6) ∧
    (active.getLsbD 7 = true ↔ relationLeftActive pattern 7) ∧
    (active.getLsbD 8 = true ↔ relationLeftActive pattern 8) ∧
    (active.getLsbD 9 = true ↔ relationLeftActive pattern 9) ∧
    (active.getLsbD 10 = true ↔ relationLeftActive pattern 10) ∧
    (active.getLsbD 11 = true ↔ relationLeftActive pattern 11) ∧
    (active.getLsbD 12 = true ↔ relationLeftActive pattern 12) ∧
    (active.getLsbD 13 = true ↔ relationLeftActive pattern 13)

def ZeroMatches (zero : BitVec 26) (pattern : Fin 26 → Prop) : Prop :=
  (zero.getLsbD 0 = true → ¬ pattern 0) ∧
    (zero.getLsbD 1 = true → ¬ pattern 1) ∧
    (zero.getLsbD 2 = true → ¬ pattern 2) ∧
    (zero.getLsbD 3 = true → ¬ pattern 3) ∧
    (zero.getLsbD 4 = true → ¬ pattern 4) ∧
    (zero.getLsbD 5 = true → ¬ pattern 5) ∧
    (zero.getLsbD 6 = true → ¬ pattern 6) ∧
    (zero.getLsbD 7 = true → ¬ pattern 7) ∧
    (zero.getLsbD 8 = true → ¬ pattern 8) ∧
    (zero.getLsbD 9 = true → ¬ pattern 9) ∧
    (zero.getLsbD 10 = true → ¬ pattern 10) ∧
    (zero.getLsbD 11 = true → ¬ pattern 11) ∧
    (zero.getLsbD 12 = true → ¬ pattern 12) ∧
    (zero.getLsbD 13 = true → ¬ pattern 13) ∧
    (zero.getLsbD 14 = true → ¬ pattern 14) ∧
    (zero.getLsbD 15 = true → ¬ pattern 15) ∧
    (zero.getLsbD 16 = true → ¬ pattern 16) ∧
    (zero.getLsbD 17 = true → ¬ pattern 17) ∧
    (zero.getLsbD 18 = true → ¬ pattern 18) ∧
    (zero.getLsbD 19 = true → ¬ pattern 19) ∧
    (zero.getLsbD 20 = true → ¬ pattern 20) ∧
    (zero.getLsbD 21 = true → ¬ pattern 21) ∧
    (zero.getLsbD 22 = true → ¬ pattern 22) ∧
    (zero.getLsbD 23 = true → ¬ pattern 23) ∧
    (zero.getLsbD 24 = true → ¬ pattern 24) ∧
    (zero.getLsbD 25 = true → ¬ pattern 25)

end Krenn.CollapseSupportCover

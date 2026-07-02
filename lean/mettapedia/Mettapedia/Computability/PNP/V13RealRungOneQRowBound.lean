import Mettapedia.Computability.PNP.V13RealRungOneAdaptiveRows

/-!
# PNP v13 real rung one: q-row bound assembly

This file packages the finite sampled experiment for the real row-observer
theorem.  It names exactly one remaining pinned counting obligation:
`V13RealLinearAdaptiveRowSpanCountingBound`.  The kernel-flip side has already
been reduced to adaptive branch exact-half; once that contributes the surcharge
bound below, the explicit q-row success estimate is immediate.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

/-- A finite experiment samples an invertible linear map from `Seed` and then
the hidden witness vector uniformly. -/
structure V13RealLinearAdaptiveQRowExperiment
    (m q : Nat) (Seed : Type*) where
  sampleA : Seed → V13F2LinearEquiv m
  observer : V13RealLinearAdaptiveRowObserver m q

abbrev V13RealLinearAdaptiveQRowWorld (m : Nat) (Seed : Type*) :=
  Seed × F2Vec m

def V13RealLinearAdaptiveQRowExperiment.world {m q : Nat} {Seed : Type*}
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed)
    (omega : V13RealLinearAdaptiveQRowWorld m Seed) :
    V13RealLinearWorld m :=
  { x := omega.2, A := E.sampleA omega.1 }

def V13RealLinearAdaptiveQRowExperiment.target {m q : Nat} {Seed : Type*}
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m)
    (omega : V13RealLinearAdaptiveQRowWorld m Seed) : ZMod 2 :=
  v13RealLinearTarget i₀ (E.world omega)

def V13RealLinearAdaptiveQRowExperiment.decision {m q : Nat} {Seed : Type*}
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed)
    (omega : V13RealLinearAdaptiveQRowWorld m Seed) : ZMod 2 :=
  E.observer.decide (E.world omega)

def V13RealLinearAdaptiveQRowExperiment.branch {m q : Nat} {Seed : Type*}
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed)
    (omega : V13RealLinearAdaptiveQRowWorld m Seed) : E.observer.Branch :=
  E.observer.branch (E.world omega)

def V13RealLinearAdaptiveQRowExperiment.branchRows {m q : Nat}
    {Seed : Type*} (E : V13RealLinearAdaptiveQRowExperiment m q Seed)
    (omega : V13RealLinearAdaptiveQRowWorld m Seed) : Finset (Fin m) :=
  (E.observer.staticBranch (E.branch omega)).rows

def V13RealLinearAdaptiveQRowExperiment.blocked {m q : Nat} {Seed : Type*}
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m)
    (omega : V13RealLinearAdaptiveQRowWorld m Seed) : Prop :=
  V13RealLinearRowsBlockTarget
    (E.sampleA omega.1) (E.branchRows omega) i₀

def V13RealLinearAdaptiveQRowExperiment.correct {m q : Nat} {Seed : Type*}
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m)
    (omega : V13RealLinearAdaptiveQRowWorld m Seed) : Prop :=
  E.decision omega = E.target i₀ omega

def V13RealLinearAdaptiveQRowCorrect {m q : Nat} {Seed : Type*}
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m) :=
  {omega : V13RealLinearAdaptiveQRowWorld m Seed // E.correct i₀ omega}

def V13RealLinearAdaptiveQRowBlocked {m q : Nat} {Seed : Type*}
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m) :=
  {omega : V13RealLinearAdaptiveQRowWorld m Seed // E.blocked i₀ omega}

noncomputable instance {m q : Nat} {Seed : Type*} [Fintype Seed]
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m) :
    Fintype (V13RealLinearAdaptiveQRowCorrect E i₀) := by
  classical
  unfold V13RealLinearAdaptiveQRowCorrect
  infer_instance

noncomputable instance {m q : Nat} {Seed : Type*} [Fintype Seed]
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m) :
    Fintype (V13RealLinearAdaptiveQRowBlocked E i₀) := by
  classical
  unfold V13RealLinearAdaptiveQRowBlocked
  infer_instance

noncomputable def v13RealLinearAdaptiveQRowSuccess {m q : Nat}
    {Seed : Type*} [Fintype Seed]
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m) :
    Rat :=
  (Fintype.card (V13RealLinearAdaptiveQRowCorrect E i₀) : Rat) /
    (Fintype.card (V13RealLinearAdaptiveQRowWorld m Seed) : Rat)

noncomputable def v13RealLinearAdaptiveQRowBlockedMass {m q : Nat}
    {Seed : Type*} [Fintype Seed]
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m) :
    Rat :=
  (Fintype.card (V13RealLinearAdaptiveQRowBlocked E i₀) : Rat) /
    (Fintype.card (V13RealLinearAdaptiveQRowWorld m Seed) : Rat)

/-- Explicit target error term for q row reads. -/
noncomputable def v13RealLinearQRowEpsilon (q m : Nat) : Rat :=
  (2 ^ q : Rat) / (2 ^ m : Rat)

/-- The single named pinned obligation: the realized branch is span-blocked
with mass at most `2^q / 2^m`. -/
def V13RealLinearAdaptiveRowSpanCountingBound {m q : Nat}
    {Seed : Type*} [Fintype Seed]
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m) :
    Prop :=
  v13RealLinearAdaptiveQRowBlockedMass E i₀ ≤
    v13RealLinearQRowEpsilon q m

/-- Kernel-flip branch pairing reduces success to half plus the blocked-branch
mass.  This is not a pinned counting assumption; it is the arithmetic interface
fed by the adaptive branch exact-half theorem. -/
def V13RealLinearAdaptiveKernelFlipSurchargeBound {m q : Nat}
    {Seed : Type*} [Fintype Seed]
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m) :
    Prop :=
  v13RealLinearAdaptiveQRowSuccess E i₀ ≤
    (1 / 2 : Rat) + v13RealLinearAdaptiveQRowBlockedMass E i₀

theorem v13RealLinear_adaptive_qrow_success_bound_of_spanCounting
    {m q : Nat} {Seed : Type*} [Fintype Seed]
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m)
    (hflip : V13RealLinearAdaptiveKernelFlipSurchargeBound E i₀)
    (hcount : V13RealLinearAdaptiveRowSpanCountingBound E i₀) :
    v13RealLinearAdaptiveQRowSuccess E i₀ ≤
      (1 / 2 : Rat) + v13RealLinearQRowEpsilon q m := by
  unfold V13RealLinearAdaptiveKernelFlipSurchargeBound at hflip
  unfold V13RealLinearAdaptiveRowSpanCountingBound at hcount
  linarith

theorem v13RealLinear_qrow_epsilon_nonnegative (q m : Nat) :
    0 ≤ v13RealLinearQRowEpsilon q m := by
  unfold v13RealLinearQRowEpsilon
  positivity

end Mettapedia.Computability.PNP

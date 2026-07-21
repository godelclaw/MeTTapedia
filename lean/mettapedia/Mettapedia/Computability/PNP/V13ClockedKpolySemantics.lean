import Mettapedia.Computability.PNP.V13FaithfulQuantitativeFrontiers

/-!
# PNP v13: operational clocked `Kpoly` semantics

Definition 2.1 and Theorem 10.9 concern the minimum prefix-program length
needed to output the
global message from the encoded public instance within clock
`(|Y| + 2)^D`, for `D >= 1`, with value `⊤` if no program succeeds.  A bare
natural-valued observable cannot express that meaning.  This module supplies
the operational law required of the final M4 object.

Programs remain abstract, but their binary descriptions are injective and
prefix-free.  Every length sublevel is explicitly enumerated with the
exponential bound used by the prefix-program union count.  The evaluator is
fuel-indexed and monotone after termination.  The sublevel-set equivalence
states the minimum-length semantics directly:
`Kpoly_D(M(Y)|Y) <= a` exactly when an `a`-bit program returns `M(Y)` within
the displayed clock.  This is a finite operational representation of the
manuscript definition, not an analytic hardness premise.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

namespace V13ClockedKpolySemantics

variable {E : V13QuantitativeEnsemble}

/-- Zero assigned complexity at two worlds with the same public input forces
their messages to agree under any operational clocked-Kpoly semantics. -/
theorem message_eq_of_samePublic_of_clockedKpoly_zero
    (S : V13ClockedKpolySemantics E)
    {m t : Nat} {parameter : E.Parameter}
    (D : Nat) (omega0 omega1 : E.World parameter m t)
    (hpublic : E.publicInput omega0 = E.publicInput omega1)
    (hzero0 : E.clockedKpoly D omega0 = 0)
    (hzero1 : E.clockedKpoly D omega1 = 0) :
    E.message (E.witnessOfWorld omega0) =
      E.message (E.witnessOfWorld omega1) := by
  have hle0 : E.clockedKpoly D omega0 <= (0 : WithTop Nat) := by
    simp [hzero0]
  have hle1 : E.clockedKpoly D omega1 <= (0 : WithTop Nat) := by
    simp [hzero1]
  rcases (S.clockedKpoly_le_iff D omega0 0).mp hle0 with
    ⟨p0, hp0, hrun0⟩
  rcases (S.clockedKpoly_le_iff D omega1 0).mp hle1 with
    ⟨p1, hp1, hrun1⟩
  have hlength0 : E.programLength p0 = 0 := Nat.eq_zero_of_le_zero hp0
  have hlength1 : E.programLength p1 = 0 := Nat.eq_zero_of_le_zero hp1
  have hcode0 : S.programCode p0 = [] := by
    apply List.length_eq_zero_iff.mp
    rw [← S.programLength_eq_codeLength, hlength0]
  have hcode1 : S.programCode p1 = [] := by
    apply List.length_eq_zero_iff.mp
    rw [← S.programLength_eq_codeLength, hlength1]
  have hp : p0 = p1 :=
    S.programCode_injective (hcode0.trans hcode1.symm)
  have hencoded :
      S.encodePublic (E.publicInput omega0) =
        S.encodePublic (E.publicInput omega1) :=
    congrArg S.encodePublic hpublic
  rw [hp, hencoded] at hrun0
  rw [hrun0] at hrun1
  exact Option.some.inj hrun1

/-- A same-public, different-message pair carrying zero raw complexity proves
that no operational clocked-Kpoly semantics can inhabit the ensemble. -/
theorem not_nonempty_of_samePublic_distinctMessage_clockedKpoly_zero
    {m t : Nat} {parameter : E.Parameter}
    (D : Nat) (omega0 omega1 : E.World parameter m t)
    (hpublic : E.publicInput omega0 = E.publicInput omega1)
    (hmessage :
      E.message (E.witnessOfWorld omega0) ≠
        E.message (E.witnessOfWorld omega1))
    (hzero0 : E.clockedKpoly D omega0 = 0)
    (hzero1 : E.clockedKpoly D omega1 = 0) :
    ¬ Nonempty (V13ClockedKpolySemantics E) := by
  rintro ⟨S⟩
  exact hmessage
    (S.message_eq_of_samePublic_of_clockedKpoly_zero
      D omega0 omega1 hpublic hzero0 hzero1)

end V13ClockedKpolySemantics

end Mettapedia.Computability.PNP

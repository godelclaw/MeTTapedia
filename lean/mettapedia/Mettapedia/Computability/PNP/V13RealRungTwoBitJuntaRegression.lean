import Mettapedia.Computability.PNP.V13RealRungTwoBitJunta

/-!
# Regression canaries for PNP v13 real rung-two bit-junta observers
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

example (j m : Nat) :
    v13RealLinearBitJuntaEpsilon2 j m =
      (4 * (2 : Rat) ^ j) / ((2 : Rat) ^ m) :=
  rfl

example {m j : Nat} (i₀ : Fin m)
    (observer : V13RealLinearBitJuntaObserver m j)
    (A : V13F2LinearEquiv m) :
    V13RealLinearBitJuntaBlocked observer A i₀ ↔
      ∀ w : F2Vec m,
        (∀ row : Fin m,
          row ∈ v13RealLinearBitJuntaRhsRows observer →
            A.toEquiv w row = 0) →
          w i₀ = 0 :=
  v13RealLinearBitJunta_blocked_iff_kernel observer A i₀

example {m j : Nat} (i₀ : Fin m)
    (observer : V13RealLinearParityObserver m j)
    (A : V13F2LinearEquiv m) :
    V13RealLinearParityObserverDeterminesTarget observer A i₀ ↔
      v13RealLinearParityObserverConstant observer A = 0 ∧
        V13RealLinearParityObserverRhsParityMatchesTarget
          observer A i₀ :=
  v13RealLinearParityObserver_determinesTarget_iff observer A i₀

end Mettapedia.Computability.PNP

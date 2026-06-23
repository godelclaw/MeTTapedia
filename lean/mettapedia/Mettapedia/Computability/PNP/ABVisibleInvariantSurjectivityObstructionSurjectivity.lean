import Mettapedia.Computability.PNP.ABVisibleInvariantSurjectivityObstructionCore

/-!
# P vs NP crux: AB-invariance blocks surjectivity

This module isolates the nontrivial-latent-space theorem: an AB-invariant exact
visible family cannot be surjective onto all Boolean rules on the exact surface.
-/

namespace Mettapedia.Computability.PNP
section Core

variable {Z : Type*} {k : ℕ}

theorem exists_ne_exactVisiblePostSwitchSurface_of_same_abVisibleData
    [Nontrivial Z] :
    ∃ u v : ExactVisiblePostSwitchSurface Z k, u ≠ v ∧ abVisibleData u = abVisibleData v := by
  classical
  obtain ⟨z₀, z₁, hz⟩ := exists_pair_ne Z
  let a : BitVec k := default
  let b : BitVec k := default
  refine ⟨⟨z₀, a, b⟩, ⟨z₁, a, b⟩, ?_, rfl⟩
  intro h
  apply hz
  simpa [a, b] using congrArg (fun u : ExactVisiblePostSwitchSurface Z k => u.z) h

theorem not_surjective_predict_of_abVisibleInvariant_of_nontrivial
    [Nontrivial Z]
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G) :
    ¬ Function.Surjective G.predict := by
  classical
  obtain ⟨u, v, huv, hab⟩ :=
    exists_ne_exactVisiblePostSwitchSurface_of_same_abVisibleData (Z := Z) (k := k)
  let rule : ExactVisiblePostSwitchSurface Z k → Bool :=
    fun w => if h : w = u then true else false
  intro hsurj
  rcases hsurj rule with ⟨i, hi⟩
  have hu : G.predict i u = true := by
    simpa [rule] using congrFun hi u
  have hvu : v ≠ u := by
    intro h
    exact huv h.symm
  have hv : G.predict i v = false := by
    simpa [rule, hvu] using congrFun hi v
  have hs : G.predict i u = G.predict i v := hinv i u v hab
  have htf : true = false := hu.symm.trans <| hs.trans hv
  cases htf

theorem not_surjective_predict_of_factorsThrough_abVisibleData_of_nontrivial
    [Nontrivial Z]
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (hfactor : G.FactorsThrough abVisibleData H) :
    ¬ Function.Surjective G.predict := by
  exact
    not_surjective_predict_of_abVisibleInvariant_of_nontrivial
      (Z := Z) (k := k)
      (abVisibleInvariant_of_factorsThrough_abVisibleData
        (Z := Z) (k := k) hfactor)

end Core

end Mettapedia.Computability.PNP

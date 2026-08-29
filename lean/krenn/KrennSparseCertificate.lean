import KrennCertificateReflection

/-!
A small reflection layer for concrete sparse polynomial certificates.

Discovery and serialization may happen outside Lean.  The trusted statement is
an equality of `MvPolynomial`s reconstructed from integer coefficients and
finite power lists.  Mapping that equality into any nontrivial commutative
ring turns a unit certificate into a no-common-zero theorem.
-/

namespace Krenn.SparseCertificate

open MvPolynomial

/-- One sparse monomial with an integer coefficient.  Repeated variables are
allowed in `powers`; their exponents then add during multiplication. -/
structure SparseTerm (σ : Type*) where
  coefficient : ℤ
  powers : List (σ × ℕ)
deriving DecidableEq, Repr

/-- A sparse polynomial is a list of terms.  Duplicate monomials are harmless:
`MvPolynomial` combines them canonically. -/
abbrev SparsePoly (σ : Type*) := List (SparseTerm σ)

noncomputable def SparseTerm.toPoly {σ : Type*} [DecidableEq σ]
    (term : SparseTerm σ) : MvPolynomial σ ℤ :=
  term.powers.foldl
    (fun polynomial power => polynomial * X power.1 ^ power.2)
    (C term.coefficient)

noncomputable def SparsePoly.toPoly {σ : Type*} [DecidableEq σ]
    (polynomial : SparsePoly σ) : MvPolynomial σ ℤ :=
  polynomial.foldl (fun result term => result + term.toPoly) 0

/-- A checked sparse unit certificate rules out a simultaneous zero after
evaluation in any nontrivial commutative ring. -/
theorem noCommonZero_of_sparseUnitCertificate
    {σ ι R : Type*} [DecidableEq σ] [Fintype ι]
    [CommRing R] [Nontrivial R]
    (equations multipliers : ι → SparsePoly σ)
    (certificate : ∑ i, (multipliers i).toPoly * (equations i).toPoly = 1)
    (values : σ → R) :
    ¬ ∀ i, eval₂Hom (Int.castRingHom R) values (equations i).toPoly = 0 := by
  let evaluate : MvPolynomial σ ℤ →+* R :=
    eval₂Hom (Int.castRingHom R) values
  let coefficients : ι → R := fun i => evaluate (multipliers i).toPoly
  let generators : ι → R := fun i => evaluate (equations i).toPoly
  have unitCombination : ∑ i, coefficients i * generators i = 1 := by
    simpa [coefficients, generators, evaluate] using congrArg evaluate certificate
  exact Krenn.CertificateReflection.noCommonZero_of_unitCombination
    coefficients generators unitCombination

/-- A checked sparse certificate with any integer constant on the right rules
out a common zero whenever that integer remains nonzero in the target ring.
This is the appropriate interface for exact characteristic-zero certificates
whose reduced constant basis is not normalized to one. -/
theorem noCommonZero_of_sparseConstantCertificate
    {σ ι R : Type*} [DecidableEq σ] [Fintype ι]
    [CommRing R] [Nontrivial R]
    (equations multipliers : ι → SparsePoly σ) (constant : ℤ)
    (certificate : ∑ i, (multipliers i).toPoly * (equations i).toPoly = C constant)
    (constantNonzero : (constant : R) ≠ 0)
    (values : σ → R) :
    ¬ ∀ i, eval₂Hom (Int.castRingHom R) values (equations i).toPoly = 0 := by
  let evaluate : MvPolynomial σ ℤ →+* R :=
    eval₂Hom (Int.castRingHom R) values
  let coefficients : ι → R := fun i => evaluate (multipliers i).toPoly
  let generators : ι → R := fun i => evaluate (equations i).toPoly
  have constantCombination :
      ∑ i, coefficients i * generators i = (constant : R) := by
    simpa [coefficients, generators, evaluate] using congrArg evaluate certificate
  intro generatorsZero
  have zeroCombination : ∑ i, coefficients i * generators i = 0 := by
    simp [generators, evaluate, generatorsZero]
  exact constantNonzero (constantCombination ▸ zeroCombination)

/- Sanity check: the sparse representation computes and reflects a tiny
integer certificate without any special-purpose theorem. -/
section Sanity

def sanityEquations : Fin 2 → SparsePoly (Fin 1)
  | 0 => [{ coefficient := 1, powers := [(0, 1)] }]
  | 1 => [
      { coefficient := 1, powers := [] },
      { coefficient := -1, powers := [(0, 1)] }
    ]

def sanityMultipliers : Fin 2 → SparsePoly (Fin 1)
  | _ => [{ coefficient := 1, powers := [] }]

example : ∑ i, (sanityMultipliers i).toPoly *
    (sanityEquations i).toPoly = 1 := by
  simp [sanityMultipliers, sanityEquations, SparsePoly.toPoly,
    SparseTerm.toPoly]

end Sanity

end Krenn.SparseCertificate

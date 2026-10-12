import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Encoding
import Mathlib.Data.Nat.Size
import Mathlib.Data.Num.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mettapedia.GSLT.LanguageDef.KernelAuthority

/-!
# Proof systems, simulations and elaboration

A proof system in the sense of Cook and Reckhow (1979) is a checker that accepts a
certificate for a claim exactly when the claim is true, in time polynomial in the
sizes of the claim and the certificate. In their function form, each certificate
determines the claim it proves. One proof system p-simulates another when a
polynomial-time translation turns every certificate of the second into a certificate
of the first for the same claim.

Checkers, soundness and exactness are those of `KernelAuthority`. Sizes are lengths
of code words, as for Mathlib's `Computability.Encoding`, and polynomial bounds use
`Polynomial ℕ`, as `TM2ComputableInPolyTime` does. A running time is a time
function stated next to its checker, in the style of Nipkow et al.: one unit per
call plus the times of the calls it makes. The definitions here use only its bounds.

Elaboration relates the two ends of the explicitness spectrum. A computing checker
accepts a certificate exactly when an elaborator turns it into a certificate that an
explicit checker accepts. The elaborator is not trusted: the explicit checker's
soundness alone gives the computing checker's. When the computing checker's run
writes the elaborated certificate out, its running time is at least that
certificate's size, so checking by computation does at least the work of reading an
explicit certificate.

The controls certify evenness. Binary certificates p-simulate unary ones, and the
converse fails because a translation would have to write certificates exponentially
longer than its input. A checker with empty certificates computes the witness, and
elaborates into the binary checker.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ProofSystems

open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Polynomial

universe uClaim uCertificate uExplicit uOther

/-! ## Polynomial bounds -/

/-- Evaluation of a polynomial with natural coefficients is monotone. -/
theorem eval_mono (p : ℕ[X]) {a b : ℕ} (le : a ≤ b) : p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q left right => simpa only [eval_add] using Nat.add_le_add left right
  | monomial n c =>
      simpa only [eval_monomial] using Nat.mul_le_mul_left c (Nat.pow_le_pow_left le n)

/-- `cost` is bounded by a polynomial in `size`. -/
def PolyBoundedBy {α : Type uOther} (cost size : α → ℕ) : Prop :=
  ∃ p : ℕ[X], ∀ x, cost x ≤ p.eval (size x)

namespace PolyBoundedBy

variable {α : Type uOther}

theorem refl (size : α → ℕ) : PolyBoundedBy size size := ⟨X, fun x => by simp⟩

theorem const (c : ℕ) (size : α → ℕ) : PolyBoundedBy (fun _ => c) size := ⟨C c, fun x => by simp⟩

theorem of_le {cost cost' size : α → ℕ} (le : ∀ x, cost x ≤ cost' x)
    (bounded : PolyBoundedBy cost' size) : PolyBoundedBy cost size := by
  obtain ⟨p, bound⟩ := bounded
  exact ⟨p, fun x => (le x).trans (bound x)⟩

theorem mono_size {cost size size' : α → ℕ} (le : ∀ x, size x ≤ size' x)
    (bounded : PolyBoundedBy cost size) : PolyBoundedBy cost size' := by
  obtain ⟨p, bound⟩ := bounded
  exact ⟨p, fun x => (bound x).trans (eval_mono p (le x))⟩

/-- A cost bounded polynomially in an intermediate measure that is itself bounded
polynomially in the size is bounded polynomially in the size. -/
theorem trans {cost middle size : α → ℕ} (first : PolyBoundedBy cost middle)
    (second : PolyBoundedBy middle size) : PolyBoundedBy cost size := by
  obtain ⟨p, boundP⟩ := first
  obtain ⟨q, boundQ⟩ := second
  exact ⟨p.comp q, fun x => by rw [eval_comp]; exact (boundP x).trans (eval_mono p (boundQ x))⟩

theorem add {cost cost' size : α → ℕ} (left : PolyBoundedBy cost size)
    (right : PolyBoundedBy cost' size) : PolyBoundedBy (fun x => cost x + cost' x) size := by
  obtain ⟨p, boundP⟩ := left
  obtain ⟨q, boundQ⟩ := right
  exact ⟨p + q, fun x => by rw [eval_add]; exact Nat.add_le_add (boundP x) (boundQ x)⟩

theorem mul {cost cost' size : α → ℕ} (left : PolyBoundedBy cost size)
    (right : PolyBoundedBy cost' size) : PolyBoundedBy (fun x => cost x * cost' x) size := by
  obtain ⟨p, boundP⟩ := left
  obtain ⟨q, boundQ⟩ := right
  exact ⟨p * q, fun x => by rw [eval_mul]; exact Nat.mul_le_mul (boundP x) (boundQ x)⟩

/-- Bounds pull back along any map. -/
theorem comp {β : Type*} {cost size : α → ℕ} (bounded : PolyBoundedBy cost size) (f : β → α) :
    PolyBoundedBy (cost ∘ f) (size ∘ f) := by
  obtain ⟨p, bound⟩ := bounded
  exact ⟨p, fun x => bound (f x)⟩

end PolyBoundedBy

/-- A polynomial with natural coefficients is dominated by `C * (x + 1) ^ d`. -/
theorem exists_envelope (p : ℕ[X]) : ∃ C d : ℕ, ∀ x, p.eval x ≤ C * (x + 1) ^ d := by
  induction p using Polynomial.induction_on' with
  | add p q left right =>
      obtain ⟨C₁, d₁, bound₁⟩ := left
      obtain ⟨C₂, d₂, bound₂⟩ := right
      refine ⟨C₁ + C₂, max d₁ d₂, fun x => ?_⟩
      rw [eval_add, Nat.add_mul]
      have positive : 0 < x + 1 := Nat.succ_pos x
      exact Nat.add_le_add
        ((bound₁ x).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right positive (le_max_left _ _))))
        ((bound₂ x).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right positive (le_max_right _ _))))
  | monomial n c =>
      exact ⟨c, n, fun x => by
        rw [eval_monomial]
        exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left (Nat.le_succ x) n)⟩

theorem sq_le_two_pow {t : ℕ} (large : 4 ≤ t) : t ^ 2 ≤ 2 ^ t := by
  induction t, large using Nat.le_induction with
  | base => norm_num
  | succ t large ih =>
      have square : 2 * t + 1 ≤ t ^ 2 := by nlinarith
      calc (t + 1) ^ 2 = t ^ 2 + (2 * t + 1) := by ring
        _ ≤ 2 ^ t + 2 ^ t := by omega
        _ = 2 ^ (t + 1) := by ring

/-- An exponential eventually exceeds every polynomial envelope. -/
theorem exists_lt_two_pow (C d a b : ℕ) : ∃ m, C * (a * m + b) ^ d < 2 ^ m := by
  obtain ⟨t, tLarge, tDegree, tFactor⟩ :
      ∃ t, 4 ≤ t ∧ d + 1 ≤ t ∧ C * (a + b) ^ d + 1 ≤ t :=
    ⟨max 4 (max (d + 1) (C * (a + b) ^ d + 1)), le_max_left _ _,
      (le_max_left _ _).trans (le_max_right _ _), (le_max_right _ _).trans (le_max_right _ _)⟩
  refine ⟨(d + 1) * t, ?_⟩
  have tLe : t ≤ (d + 1) * t := Nat.le_mul_of_pos_left t (Nat.succ_pos d)
  have positive : 0 < (d + 1) * t := by omega
  have linear : a * ((d + 1) * t) + b ≤ (a + b) * ((d + 1) * t) := by nlinarith
  calc C * (a * ((d + 1) * t) + b) ^ d
      ≤ C * ((a + b) * ((d + 1) * t)) ^ d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left linear d)
    _ = C * (a + b) ^ d * ((d + 1) * t) ^ d := by rw [mul_pow]; ring
    _ < (d + 1) * t * ((d + 1) * t) ^ d :=
        Nat.mul_lt_mul_of_pos_right (by omega) (Nat.pow_pos positive)
    _ = ((d + 1) * t) ^ (d + 1) := by ring
    _ ≤ (t * t) ^ (d + 1) := Nat.pow_le_pow_left (Nat.mul_le_mul_right t tDegree) _
    _ = (t ^ 2) ^ (d + 1) := by ring
    _ ≤ (2 ^ t) ^ (d + 1) := Nat.pow_le_pow_left (sq_le_two_pow tLarge) _
    _ = 2 ^ ((d + 1) * t) := by rw [← pow_mul, Nat.mul_comm]

/-- No polynomial bounds `2 ^ m` at a linear function of `m`. -/
theorem exists_eval_lt_two_pow (p : ℕ[X]) (a b : ℕ) : ∃ m, p.eval (a * m + b) < 2 ^ m := by
  obtain ⟨C, d, bound⟩ := exists_envelope p
  obtain ⟨m, lt⟩ := exists_lt_two_pow C d a (b + 1)
  exact ⟨m, (bound _).trans_lt (by simpa [Nat.add_assoc] using lt)⟩

/-! ## Sizes of encoded values -/

/-- The size of a value under an encoding is the length of its code word. -/
def encodedSize {α : Type uOther} {Γ : Type*} (encoding : Computability.Encoding α Γ) (x : α) : ℕ :=
  (encoding.encode x).length

theorem length_unaryEncodeNat (n : ℕ) : (Computability.unaryEncodeNat n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Computability.unaryEncodeNat, ih]

theorem encodedSize_unary (n : ℕ) : encodedSize Computability.unaryEncodingNat n = n :=
  length_unaryEncodeNat n

theorem length_encodePosNum (p : PosNum) : (Computability.encodePosNum p).length = p.natSize := by
  induction p with
  | one => rfl
  | bit0 p ih => simp [Computability.encodePosNum, PosNum.natSize, ih]
  | bit1 p ih => simp [Computability.encodePosNum, PosNum.natSize, ih]

theorem length_encodeNum (n : Num) : (Computability.encodeNum n).length = n.natSize := by
  cases n with
  | zero => rfl
  | pos p => exact length_encodePosNum p

/-- Binary code words of numbers have the length `Nat.size`. -/
theorem encodedSize_binary (n : ℕ) : encodedSize Computability.encodingNatBool n = n.size := by
  change (Computability.encodeNum (n : Num)).length = n.size
  rw [length_encodeNum, Num.natSize_to_nat, Num.to_of_nat]

/-! ## Checkers with sizes and running times -/

/-- A checker together with the sizes of its claims and certificates. -/
structure SizedChecker (Claim : Type uClaim) (Certificate : Type uCertificate)
    extends Checker Claim Certificate where
  claimSize : Claim → ℕ
  certificateSize : Certificate → ℕ

namespace SizedChecker

variable {Claim : Type uClaim} {Certificate : Type uCertificate}

/-- The size of an input of the checker. -/
def inputSize (checker : SizedChecker Claim Certificate) (input : Claim × Certificate) : ℕ :=
  checker.claimSize input.1 + checker.certificateSize input.2

/-- Every true claim has an accepted certificate of size polynomial in the claim's size. -/
def PolynomiallyBounded (checker : SizedChecker Claim Certificate) (Meaning : Claim → Prop) : Prop :=
  ∃ p : ℕ[X], ∀ claim, Meaning claim →
    ∃ certificate, checker.check claim certificate = true ∧
      checker.certificateSize certificate ≤ p.eval (checker.claimSize claim)

end SizedChecker

/-- A sized checker together with its running time, a time function stated next to the
checker. -/
structure TimedChecker (Claim : Type uClaim) (Certificate : Type uCertificate)
    extends SizedChecker Claim Certificate where
  time : Claim → Certificate → ℕ

namespace TimedChecker

variable {Claim : Type uClaim} {Certificate : Type uCertificate}

/-- The checker runs in time polynomial in the size of its input. -/
def PolynomialTime (checker : TimedChecker Claim Certificate) : Prop :=
  PolyBoundedBy (fun input : Claim × Certificate => checker.time input.1 input.2)
    checker.toSizedChecker.inputSize

/-- The checker runs in time linear in the size of its input. -/
def LinearTime (checker : TimedChecker Claim Certificate) : Prop :=
  ∃ factor offset : ℕ, ∀ claim certificate,
    checker.time claim certificate ≤ factor * checker.toSizedChecker.inputSize (claim, certificate) + offset

theorem LinearTime.polynomialTime {checker : TimedChecker Claim Certificate}
    (linear : checker.LinearTime) : checker.PolynomialTime := by
  obtain ⟨factor, offset, bound⟩ := linear
  exact ⟨C factor * X + C offset, fun input => by simpa using bound input.1 input.2⟩

end TimedChecker

/-! ## Proof systems in the sense of Cook and Reckhow -/

/-- A proof system for a meaning: an exact checker running in polynomial time. -/
structure ProofSystem (Claim : Type uClaim) (Certificate : Type uCertificate)
    (Meaning : Claim → Prop) extends TimedChecker Claim Certificate where
  authority : toChecker.Authority Meaning
  polynomialTime : toTimedChecker.PolynomialTime

/-- An accepted certificate of a proof system never proves a false claim. -/
theorem ProofSystem.meaning_of_accepted {Claim : Type uClaim} {Certificate : Type uCertificate}
    {Meaning : Claim → Prop} (system : ProofSystem Claim Certificate Meaning) {claim : Claim}
    {certificate : Certificate} (accepted : system.check claim certificate = true) :
    Meaning claim :=
  system.authority.sound claim certificate accepted

/-- Cook and Reckhow's function form: a certificate determines the claim it proves, if any. -/
structure FunctionForm (Claim : Type uClaim) (Certificate : Type uCertificate) where
  conclusion? : Certificate → Option Claim

namespace FunctionForm

variable {Claim : Type uClaim} {Certificate : Type uCertificate}

/-- A function form checks a claim by comparing it with the computed conclusion. -/
def toChecker [DecidableEq Claim] (form : FunctionForm Claim Certificate) :
    Checker Claim Certificate where
  check claim certificate := decide (form.conclusion? certificate = some claim)

theorem toChecker_check_iff [DecidableEq Claim] (form : FunctionForm Claim Certificate)
    (claim : Claim) (certificate : Certificate) :
    form.toChecker.check claim certificate = true ↔ form.conclusion? certificate = some claim := by
  simp [toChecker]

/-- With a true claim as default, the function form becomes Cook and Reckhow's total map. -/
def total (form : FunctionForm Claim Certificate) (default : Claim) : Certificate → Claim :=
  fun certificate => (form.conclusion? certificate).getD default

/-- If the conclusions are exactly the true claims, the total map is onto the true claims. -/
theorem range_total {Meaning : Claim → Prop} (form : FunctionForm Claim Certificate)
    (exact : ∀ claim, (∃ certificate, form.conclusion? certificate = some claim) ↔ Meaning claim)
    {default : Claim} (trueDefault : Meaning default) :
    Set.range (form.total default) = {claim | Meaning claim} := by
  ext claim
  constructor
  · rintro ⟨certificate, rfl⟩
    cases conclusion : form.conclusion? certificate with
    | none => simpa [total, conclusion] using trueDefault
    | some proved =>
        simpa [total, conclusion] using (exact proved).mp ⟨certificate, conclusion⟩
  · intro isTrue
    obtain ⟨certificate, conclusion⟩ := (exact claim).mpr isTrue
    exact ⟨certificate, by simp [total, conclusion]⟩

/-- The function form of a checker: a certificate for the pair's claim proves that claim. -/
def ofChecker (checker : Checker Claim Certificate) :
    FunctionForm Claim (Claim × Certificate) where
  conclusion? input := if checker.check input.1 input.2 then some input.1 else none

theorem ofChecker_conclusion_iff (checker : Checker Claim Certificate)
    (input : Claim × Certificate) (claim : Claim) :
    (ofChecker checker).conclusion? input = some claim ↔
      input.1 = claim ∧ checker.check input.1 input.2 = true := by
  cases accepted : checker.check input.1 input.2 <;> simp [ofChecker, accepted]

/-- The conclusions of an exact checker's function form are exactly the true claims. -/
theorem ofChecker_exact {checker : Checker Claim Certificate} {Meaning : Claim → Prop}
    (authority : checker.Authority Meaning) (claim : Claim) :
    (∃ input, (ofChecker checker).conclusion? input = some claim) ↔ Meaning claim := by
  constructor
  · rintro ⟨input, conclusion⟩
    obtain ⟨same, accepted⟩ := (ofChecker_conclusion_iff checker input claim).mp conclusion
    exact same ▸ authority.sound _ _ accepted
  · intro isTrue
    obtain ⟨certificate, accepted⟩ := authority.complete claim isTrue
    exact ⟨(claim, certificate), (ofChecker_conclusion_iff checker _ claim).mpr ⟨rfl, accepted⟩⟩

/-- A function form whose conclusions are exactly the true claims gives an exact checker. -/
theorem authority_toChecker [DecidableEq Claim] {Meaning : Claim → Prop}
    (form : FunctionForm Claim Certificate)
    (exact : ∀ claim, (∃ certificate, form.conclusion? certificate = some claim) ↔ Meaning claim) :
    form.toChecker.Authority Meaning where
  sound claim certificate accepted :=
    (exact claim).mp ⟨certificate, (form.toChecker_check_iff claim certificate).mp accepted⟩
  complete claim isTrue := by
    obtain ⟨certificate, conclusion⟩ := (exact claim).mpr isTrue
    exact ⟨certificate, (form.toChecker_check_iff claim certificate).mpr conclusion⟩

end FunctionForm

/-! ## Simulations -/

section Simulations

variable {Claim : Type uClaim}

/-- `target` simulates `source` when a translation turns every certificate that
`source` accepts into one that `target` accepts for the same claim. -/
structure Simulation {Certificate₁ : Type uCertificate} {Certificate₂ : Type uExplicit}
    (target : Checker Claim Certificate₁) (source : Checker Claim Certificate₂) where
  translate : Claim → Certificate₂ → Certificate₁
  preserves : ∀ claim certificate, source.check claim certificate = true →
    target.check claim (translate claim certificate) = true

namespace Simulation

variable {Certificate₁ : Type uCertificate} {Certificate₂ : Type uExplicit}
  {Certificate₃ : Type uOther}

/-- Every checker simulates itself. -/
def refl (checker : Checker Claim Certificate₁) : Simulation checker checker :=
  ⟨fun _ certificate => certificate, fun _ _ accepted => accepted⟩

/-- Simulations compose. -/
def trans {first : Checker Claim Certificate₁} {second : Checker Claim Certificate₂}
    {third : Checker Claim Certificate₃} (outer : Simulation first second)
    (inner : Simulation second third) : Simulation first third :=
  ⟨fun claim certificate => outer.translate claim (inner.translate claim certificate),
    fun _ _ accepted => outer.preserves _ _ (inner.preserves _ _ accepted)⟩

/-- A checker simulated by a sound checker is sound. -/
theorem sound {target : Checker Claim Certificate₁} {source : Checker Claim Certificate₂}
    (simulation : Simulation target source) {Meaning : Claim → Prop}
    (targetSound : target.Sound Meaning) : source.Sound Meaning :=
  fun claim certificate accepted =>
    targetSound claim _ (simulation.preserves claim certificate accepted)

/-- A checker that simulates a complete checker is complete. -/
theorem complete {target : Checker Claim Certificate₁} {source : Checker Claim Certificate₂}
    (simulation : Simulation target source) {Meaning : Claim → Prop}
    (sourceComplete : source.CertificateComplete Meaning) : target.CertificateComplete Meaning := by
  intro claim isTrue
  obtain ⟨certificate, accepted⟩ := sourceComplete claim isTrue
  exact ⟨_, simulation.preserves claim certificate accepted⟩

end Simulation

/-- A simulation whose translated certificates are polynomially bounded in the size of
the source input. -/
structure SizeSimulation {Certificate₁ : Type uCertificate} {Certificate₂ : Type uExplicit}
    (target : SizedChecker Claim Certificate₁) (source : SizedChecker Claim Certificate₂)
    extends Simulation target.toChecker source.toChecker where
  sizeBound : PolyBoundedBy
    (fun input : Claim × Certificate₂ => target.certificateSize (translate input.1 input.2))
    source.inputSize

/-- A p-simulation in the sense of Cook and Reckhow: the translation's own running time,
given by its time function, is polynomial in the size of the source input. -/
structure PSimulation {Certificate₁ : Type uCertificate} {Certificate₂ : Type uExplicit}
    (target : SizedChecker Claim Certificate₁) (source : SizedChecker Claim Certificate₂)
    extends SizeSimulation target source where
  translationTime : Claim → Certificate₂ → ℕ
  timeBound : PolyBoundedBy (fun input : Claim × Certificate₂ => translationTime input.1 input.2)
    source.inputSize

namespace SizeSimulation

variable {Certificate₁ : Type uCertificate} {Certificate₂ : Type uExplicit}
  {Certificate₃ : Type uOther}

/-- Every timed checker size-simulates itself. -/
def refl (checker : SizedChecker Claim Certificate₁) : SizeSimulation checker checker where
  toSimulation := Simulation.refl checker.toChecker
  sizeBound := ⟨X, fun input => by simp [SizedChecker.inputSize, Simulation.refl]⟩

/-- Size simulations compose when the middle checker measures claims as the source does. -/
def trans {first : SizedChecker Claim Certificate₁} {second : SizedChecker Claim Certificate₂}
    {third : SizedChecker Claim Certificate₃} (outer : SizeSimulation first second)
    (inner : SizeSimulation second third) (sameClaims : second.claimSize = third.claimSize) :
    SizeSimulation first third where
  toSimulation := outer.toSimulation.trans inner.toSimulation
  sizeBound := by
    have middle : PolyBoundedBy
        (fun input : Claim × Certificate₃ =>
          second.inputSize (input.1, inner.translate input.1 input.2))
        third.inputSize := by
      have claims : PolyBoundedBy (fun input : Claim × Certificate₃ => second.claimSize input.1)
          third.inputSize :=
        PolyBoundedBy.of_le (fun input => by simp [SizedChecker.inputSize, sameClaims])
          (PolyBoundedBy.refl _)
      exact PolyBoundedBy.add claims inner.sizeBound
    have outerBound : PolyBoundedBy
        (fun input : Claim × Certificate₃ =>
          first.certificateSize (outer.translate input.1 (inner.translate input.1 input.2)))
        (fun input => second.inputSize (input.1, inner.translate input.1 input.2)) :=
      outer.sizeBound.comp (fun input : Claim × Certificate₃ => (input.1, inner.translate input.1 input.2))
    exact PolyBoundedBy.trans outerBound middle

/-- Polynomially bounded certificates survive a size simulation. -/
theorem polynomiallyBounded {target : SizedChecker Claim Certificate₁}
    {source : SizedChecker Claim Certificate₂} (simulation : SizeSimulation target source)
    (sameClaims : target.claimSize = source.claimSize) {Meaning : Claim → Prop}
    (bounded : source.PolynomiallyBounded Meaning) : target.PolynomiallyBounded Meaning := by
  obtain ⟨p, boundP⟩ := bounded
  obtain ⟨q, boundQ⟩ := simulation.sizeBound
  refine ⟨q.comp (X + p), fun claim isTrue => ?_⟩
  obtain ⟨certificate, accepted, small⟩ := boundP claim isTrue
  refine ⟨simulation.translate claim certificate, simulation.preserves _ _ accepted, ?_⟩
  calc target.certificateSize (simulation.translate claim certificate)
      ≤ q.eval (source.inputSize (claim, certificate)) := boundQ (claim, certificate)
    _ ≤ q.eval (source.claimSize claim + p.eval (source.claimSize claim)) :=
        eval_mono q (Nat.add_le_add_left small _)
    _ = (q.comp (X + p)).eval (target.claimSize claim) := by simp [eval_comp, sameClaims]

end SizeSimulation

namespace PSimulation

variable {Certificate₁ : Type uCertificate} {Certificate₂ : Type uExplicit}
  {Certificate₃ : Type uOther}

/-- Every timed checker p-simulates itself, with the identity translation read once. -/
def refl (checker : SizedChecker Claim Certificate₁) : PSimulation checker checker where
  toSizeSimulation := SizeSimulation.refl checker
  translationTime claim certificate := checker.inputSize (claim, certificate)
  timeBound := ⟨X, fun input => by simp [SizedChecker.inputSize]⟩

/-- p-simulations compose when the middle checker measures claims as the source does. -/
def trans {first : SizedChecker Claim Certificate₁} {second : SizedChecker Claim Certificate₂}
    {third : SizedChecker Claim Certificate₃} (outer : PSimulation first second)
    (inner : PSimulation second third) (sameClaims : second.claimSize = third.claimSize) :
    PSimulation first third where
  toSizeSimulation := outer.toSizeSimulation.trans inner.toSizeSimulation sameClaims
  translationTime claim certificate :=
    inner.translationTime claim certificate +
      outer.translationTime claim (inner.translate claim certificate)
  timeBound := by
    have middle : PolyBoundedBy
        (fun input : Claim × Certificate₃ =>
          second.inputSize (input.1, inner.translate input.1 input.2))
        third.inputSize := by
      have claims : PolyBoundedBy (fun input : Claim × Certificate₃ => second.claimSize input.1)
          third.inputSize :=
        PolyBoundedBy.of_le (fun input => by simp [SizedChecker.inputSize, sameClaims])
          (PolyBoundedBy.refl _)
      exact PolyBoundedBy.add claims inner.sizeBound
    have outerBound : PolyBoundedBy
        (fun input : Claim × Certificate₃ =>
          outer.translationTime input.1 (inner.translate input.1 input.2))
        (fun input => second.inputSize (input.1, inner.translate input.1 input.2)) :=
      outer.timeBound.comp (fun input : Claim × Certificate₃ => (input.1, inner.translate input.1 input.2))
    exact PolyBoundedBy.add inner.timeBound (PolyBoundedBy.trans outerBound middle)

end PSimulation

end Simulations

/-! ## Elaboration -/

section Elaboration

variable {Claim : Type uClaim} {Certificate : Type uCertificate} {Explicit : Type uExplicit}

/-- An elaboration of a computing checker into an explicit one: the computing checker
accepts exactly when the elaborator succeeds and the explicit checker accepts its
output. Nothing is assumed about the elaborator beyond this equation. -/
structure Elaboration (computing : Checker Claim Certificate) (explicit : Checker Claim Explicit) where
  elaborate : Claim → Certificate → Option Explicit
  exact : ∀ claim certificate, computing.check claim certificate = true ↔
    ∃ elaborated, elaborate claim certificate = some elaborated ∧
      explicit.check claim elaborated = true

namespace Elaboration

variable {computing : Checker Claim Certificate} {explicit : Checker Claim Explicit}

/-- Trust reduction: the explicit checker's soundness gives the computing checker's,
with no trust in the elaborator. -/
theorem sound (elaboration : Elaboration computing explicit) {Meaning : Claim → Prop}
    (explicitSound : explicit.Sound Meaning) : computing.Sound Meaning := by
  intro claim certificate accepted
  obtain ⟨elaborated, _, explicitAccepted⟩ := (elaboration.exact claim certificate).mp accepted
  exact explicitSound claim elaborated explicitAccepted

/-- Everything the computing checker can certify, the explicit checker can certify. -/
theorem complete (elaboration : Elaboration computing explicit) {Meaning : Claim → Prop}
    (computingComplete : computing.CertificateComplete Meaning) :
    explicit.CertificateComplete Meaning := by
  intro claim isTrue
  obtain ⟨certificate, accepted⟩ := computingComplete claim isTrue
  obtain ⟨elaborated, _, explicitAccepted⟩ := (elaboration.exact claim certificate).mp accepted
  exact ⟨elaborated, explicitAccepted⟩

/-- The explicit checker simulates the computing checker through the elaborator. -/
def simulation [Inhabited Explicit] (elaboration : Elaboration computing explicit) :
    Simulation explicit computing where
  translate claim certificate := (elaboration.elaborate claim certificate).getD default
  preserves claim certificate accepted := by
    obtain ⟨elaborated, produced, explicitAccepted⟩ :=
      (elaboration.exact claim certificate).mp accepted
    simpa [produced] using explicitAccepted

end Elaboration

/-- The computing checker's run writes the elaborated certificate out: its size is at
most the computing checker's running time. -/
def Elaboration.TraceBounded {computing : TimedChecker Claim Certificate}
    {explicit : SizedChecker Claim Explicit}
    (elaboration : Elaboration computing.toChecker explicit.toChecker) : Prop :=
  ∀ claim certificate elaborated, elaboration.elaborate claim certificate = some elaborated →
    explicit.certificateSize elaborated ≤ computing.time claim certificate

namespace Elaboration

variable {computing : TimedChecker Claim Certificate} {explicit : SizedChecker Claim Explicit}

/-- Work conservation: a computing checker whose run writes out its elaboration spends at
least the size of an explicit certificate that the explicit checker accepts. -/
theorem work_conservation (elaboration : Elaboration computing.toChecker explicit.toChecker)
    (traced : elaboration.TraceBounded) {claim : Claim} {certificate : Certificate}
    (accepted : computing.check claim certificate = true) :
    ∃ elaborated, explicit.check claim elaborated = true ∧
      explicit.certificateSize elaborated ≤ computing.time claim certificate := by
  obtain ⟨elaborated, produced, explicitAccepted⟩ :=
    (elaboration.exact claim certificate).mp accepted
  exact ⟨elaborated, explicitAccepted, traced claim certificate elaborated produced⟩

/-- Checking the elaborated certificate with a linear-time explicit checker costs at most
a constant multiple of the claim's size and the computing checker's time. -/
theorem explicit_time_le {timed : TimedChecker Claim Explicit}
    (elaboration : Elaboration computing.toChecker timed.toChecker)
    (traced : elaboration.TraceBounded (explicit := timed.toSizedChecker)) {factor offset : ℕ}
    (linear : ∀ claim elaborated, timed.time claim elaborated ≤
      factor * timed.toSizedChecker.inputSize (claim, elaborated) + offset)
    {claim : Claim} {certificate : Certificate} {elaborated : Explicit}
    (produced : elaboration.elaborate claim certificate = some elaborated) :
    timed.time claim elaborated ≤
      factor * (timed.claimSize claim + computing.time claim certificate) + offset := by
  have small := traced claim certificate elaborated produced
  calc timed.time claim elaborated
      ≤ factor * timed.toSizedChecker.inputSize (claim, elaborated) + offset := linear claim elaborated
    _ ≤ factor * (timed.claimSize claim + computing.time claim certificate) + offset := by
        unfold SizedChecker.inputSize
        exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_left small _)) _

/-- A polynomial-time computing checker whose run writes out its elaboration is
size-simulated by the explicit checker. -/
def sizeSimulation [Inhabited Explicit]
    (elaboration : Elaboration computing.toChecker explicit.toChecker)
    (traced : elaboration.TraceBounded) (polynomial : computing.PolynomialTime)
    (defaultSmall : ∀ claim certificate, elaboration.elaborate claim certificate = none →
      explicit.certificateSize default ≤ computing.time claim certificate) :
    SizeSimulation explicit computing.toSizedChecker where
  toSimulation := elaboration.simulation
  sizeBound := by
    have timeBound : PolyBoundedBy (fun input : Claim × Certificate => computing.time input.1 input.2)
        computing.toSizedChecker.inputSize := polynomial
    refine PolyBoundedBy.of_le (fun input => ?_) timeBound
    change explicit.certificateSize ((elaboration.elaborate input.1 input.2).getD default) ≤ _
    cases produced : elaboration.elaborate input.1 input.2 with
    | none => simpa using defaultSmall input.1 input.2 produced
    | some elaborated => simpa using traced input.1 input.2 elaborated produced

end Elaboration

end Elaboration

/-! ## Controls: certificates of evenness -/

namespace Evenness

open Computability

/-- Claims are numbers, measured in binary; a certificate for `n` is a `k` with
`2 * k = n`, written in unary. The time reads the certificate symbol by symbol into a
binary counter of at most the claim's length, then compares. -/
def unaryChecker : TimedChecker ℕ ℕ where
  check n k := decide (2 * k = n)
  claimSize := encodedSize encodingNatBool
  certificateSize := encodedSize unaryEncodingNat
  time n k := (encodedSize unaryEncodingNat k + 1) * (encodedSize encodingNatBool n + 1)

/-- The same certificates written in binary. Doubling is a shift, so the time reads both
numbers once. -/
def binaryChecker : TimedChecker ℕ ℕ where
  check n k := decide (2 * k = n)
  claimSize := encodedSize encodingNatBool
  certificateSize := encodedSize encodingNatBool
  time n k := encodedSize encodingNatBool k + encodedSize encodingNatBool n + 1

/-- A computing checker with empty certificates: it halves the claim and checks the
remainder. Halving writes the half out, so the time is the claim's length plus one. -/
def computingChecker : TimedChecker ℕ Unit where
  check n _ := decide (n % 2 = 0)
  claimSize := encodedSize encodingNatBool
  certificateSize _ := 0
  time n _ := encodedSize encodingNatBool n + 1

theorem check_iff (n k : ℕ) : unaryChecker.check n k = true ↔ 2 * k = n := by
  simp [unaryChecker]

theorem binary_check_iff (n k : ℕ) : binaryChecker.check n k = true ↔ 2 * k = n := by
  simp [binaryChecker]

theorem even_iff_exists_double (n : ℕ) : Even n ↔ ∃ k, 2 * k = n := by
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, by omega⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, by omega⟩

theorem size_le_self (n : ℕ) : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self

/-- Unary certificates make a proof system for evenness. -/
def unarySystem : ProofSystem ℕ ℕ Even where
  toTimedChecker := unaryChecker
  authority :=
    { sound := fun n k accepted => (even_iff_exists_double n).mpr ⟨k, (check_iff n k).mp accepted⟩
      complete := fun n isEven => by
        obtain ⟨k, double⟩ := (even_iff_exists_double n).mp isEven
        exact ⟨k, (check_iff n k).mpr double⟩ }
  polynomialTime := ⟨(X + 1) * (X + 1), fun input => by
    simp only [unaryChecker, SizedChecker.inputSize, eval_mul, eval_add, eval_X, eval_one]
    exact Nat.mul_le_mul (by omega) (by omega)⟩

/-- Binary certificates make a proof system for evenness. -/
def binarySystem : ProofSystem ℕ ℕ Even where
  toTimedChecker := binaryChecker
  authority :=
    { sound := fun n k accepted =>
        (even_iff_exists_double n).mpr ⟨k, (binary_check_iff n k).mp accepted⟩
      complete := fun n isEven => by
        obtain ⟨k, double⟩ := (even_iff_exists_double n).mp isEven
        exact ⟨k, (binary_check_iff n k).mpr double⟩ }
  polynomialTime := ⟨X + 1, fun input => by
    simp only [binaryChecker, SizedChecker.inputSize, eval_add, eval_X, eval_one]
    omega⟩

/-- Binary certificates p-simulate unary ones: the translation rewrites the number. -/
def binarySimulatesUnary : PSimulation binaryChecker.toSizedChecker unaryChecker.toSizedChecker where
  translate _ k := k
  preserves n k accepted := (binary_check_iff n k).mpr ((check_iff n k).mp accepted)
  sizeBound := ⟨X, fun input => by
    simp only [binaryChecker, unaryChecker, SizedChecker.inputSize, encodedSize_binary,
      encodedSize_unary, eval_X]
    exact (size_le_self _).trans (Nat.le_add_left _ _)⟩
  translationTime _ k := k + 1
  timeBound := ⟨X + 1, fun input => by
    simp only [unaryChecker, SizedChecker.inputSize, encodedSize_unary, eval_add, eval_X, eval_one]
    omega⟩

/-- Unary certificates do not size-simulate binary ones: the claim `2 ^ (m + 1)` has the
binary certificate `2 ^ m` of length `m + 1`, while its only unary certificate has
length `2 ^ m`. -/
theorem unary_not_sizeSimulates_binary :
    IsEmpty (SizeSimulation unaryChecker.toSizedChecker binaryChecker.toSizedChecker) := by
  refine ⟨fun simulation => ?_⟩
  obtain ⟨p, bound⟩ := simulation.sizeBound
  obtain ⟨m, small⟩ := exists_eval_lt_two_pow p 2 3
  have power : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
  have accepted : binaryChecker.check (2 ^ (m + 1)) (2 ^ m) = true :=
    (binary_check_iff _ _).mpr power.symm
  have translated := (check_iff _ _).mp (simulation.preserves _ _ accepted)
  have forced : simulation.translate (2 ^ (m + 1)) (2 ^ m) = 2 ^ m := by
    generalize simulation.translate (2 ^ (m + 1)) (2 ^ m) = k at translated ⊢
    omega
  have sized := bound (2 ^ (m + 1), 2 ^ m)
  simp only [unaryChecker, binaryChecker, SizedChecker.inputSize, encodedSize_unary,
    encodedSize_binary, Nat.size_pow] at sized
  rw [forced] at sized
  have same : m + 1 + 1 + (m + 1) = 2 * m + 3 := by ring
  rw [same] at sized
  omega

/-- Binary certificates are polynomially bounded: half of an even number is no longer
than the number. -/
theorem binary_polynomiallyBounded : binaryChecker.toSizedChecker.PolynomiallyBounded Even := by
  refine ⟨X, fun n isEven => ?_⟩
  obtain ⟨k, double⟩ := (even_iff_exists_double n).mp isEven
  refine ⟨k, (binary_check_iff n k).mpr double, ?_⟩
  simp only [binaryChecker, encodedSize_binary, eval_X]
  exact Nat.size_le_size (by omega)

/-- Unary certificates are not polynomially bounded. -/
theorem unary_not_polynomiallyBounded : ¬ unaryChecker.toSizedChecker.PolynomiallyBounded Even := by
  rintro ⟨p, bound⟩
  obtain ⟨m, small⟩ := exists_eval_lt_two_pow p 1 2
  have power : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
  have isEven : Even (2 ^ (m + 1)) := (even_iff_exists_double _).mpr ⟨2 ^ m, power.symm⟩
  obtain ⟨k, accepted, sized⟩ := bound _ isEven
  have double := (check_iff _ _).mp accepted
  have forced : k = 2 ^ m := by omega
  simp only [unaryChecker, encodedSize_unary, encodedSize_binary, Nat.size_pow] at sized
  rw [forced] at sized
  have same : m + 1 + 1 = 1 * m + 2 := by ring
  rw [same] at sized
  omega

/-- The computing checker elaborates into the binary checker by writing out the half. -/
def halving : Elaboration computingChecker.toChecker binaryChecker.toChecker where
  elaborate n _ := if n % 2 = 0 then some (n / 2) else none
  exact n _ := by
    constructor
    · intro accepted
      have even : n % 2 = 0 := by simpa [computingChecker] using accepted
      exact ⟨n / 2, by simp [even], (binary_check_iff _ _).mpr (by omega)⟩
    · rintro ⟨k, produced, accepted⟩
      have double := (binary_check_iff _ _).mp accepted
      by_cases even : n % 2 = 0
      · simp [computingChecker, even]
      · simp [even] at produced

/-- The half is written out during the run, so the elaboration is trace-bounded. -/
theorem halving_traceBounded : halving.TraceBounded := by
  intro n _ k produced
  by_cases even : n % 2 = 0
  · simp only [halving, even, if_true, Option.some.injEq] at produced
    subst produced
    simp only [binaryChecker, computingChecker, encodedSize_binary]
    exact (Nat.size_le_size (Nat.div_le_self n 2)).trans (Nat.le_succ _)
  · simp [halving, even] at produced

/-- Trust reduction in the control: the computing checker is sound because the binary
checker is. -/
theorem computing_sound : computingChecker.Sound Even :=
  halving.sound binarySystem.authority.sound

/-- A computing checker that does no work cannot be trace-bounded: with unit time, the
half of `4` would have to fit in one unit, but it has length two. -/
theorem unitTime_not_traceBounded :
    ¬ (∀ n (_ : Unit) k, halving.elaborate n () = some k →
      binaryChecker.certificateSize k ≤ 1) := by
  intro bounded
  have produced : halving.elaborate 4 () = some 2 := by decide
  have sized := bounded 4 () 2 produced
  have two : Nat.size 2 = 2 := by simpa using (Nat.size_pow (n := 1))
  simp only [binaryChecker, encodedSize_binary, two] at sized
  omega

/-- The identity translation on unary certificates is a p-simulation, and binary
certificates p-simulate unary ones but not conversely. -/
example : Nonempty (PSimulation unaryChecker.toSizedChecker unaryChecker.toSizedChecker) :=
  ⟨PSimulation.refl _⟩

example : Nonempty (PSimulation binaryChecker.toSizedChecker unaryChecker.toSizedChecker) :=
  ⟨binarySimulatesUnary⟩

end Evenness

end Mettapedia.GSLT.LanguageDef.ProofSystems

import Mettapedia.GSLT.LanguageDef.ResourceComputation

/-!
# Executed checking classes and the orientation of kernel comparison

Linear and polynomial checking concern the actual machine on a fixed physical
encoding. They do not describe an axiom system, a model class, or the primitive
operations permitted by a chosen replay discipline.

An exact translation transfers checking, including refusals. A linear
translation into a linear checker gives linear source checking after charging
the actual output-writing and handoff work. A polynomial translation only
transfers polynomial checking.

Universal hosting, least objects and efficient equivalence are separate
properties. The concrete unary/binary certificate example refutes collapse
of exact checker authority into a single certificate-size equivalence class.
Its existing time accounts are declared accounts, not machine executions.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ResourceTranslation

open SemanticEvidence HeterogeneousTheory ProofSystems Polynomial
open Mettapedia.Computability

/-- The original clock is bounded linearly in the complete encoded packet. -/
def LinearClock {Kind Γ : Type} [Fintype Γ] {theory : TheoryFamily Kind}
    {authority : AuthorityContract theory}
    {encoding : Computability.Encoding (Packet authority) Γ}
    (implementation : CheckerExecution authority encoding) : Prop :=
  ∃ factor offset : Nat, ∀ packet,
    implementation.time packet ≤ factor * (encoding.encode packet).length + offset

/-- A linear checker exists under this fixed authority and encoding. -/
def LinearChecking (source : EncodedAuthority) : Prop :=
  ∃ implementation : CheckerExecution source.authority source.encoding,
    LinearClock implementation

theorem linearChecking_polynomial {source : EncodedAuthority}
    (linear : LinearChecking source) : PolynomialChecking source := by
  obtain ⟨implementation, factor, offset, bound⟩ := linear
  refine ⟨implementation, C factor * X + C offset, fun packet => ?_⟩
  simpa only [eval_add, eval_mul, eval_C, eval_X] using bound packet

section Translation

variable {SK TK Γ Δ : Type} [Fintype Γ] [Fintype Δ] [Inhabited Δ]
  {S : TheoryFamily SK} {T : TheoryFamily TK}
  {SA : AuthorityContract S} {TA : AuthorityContract T}
  {se : Computability.Encoding (Packet SA) Γ}
  {te : Computability.Encoding (Packet TA) Δ}

/-- A linear bound on the polynomial machine's original clock. -/
def LinearTranslationClock (translation : OperationalTranslation SA TA se te) : Prop :=
  ∃ factor offset : Nat, ∀ packet,
    translation.realization.time.eval (se.encode packet).length ≤
      factor * (se.encode packet).length + offset

/-- Linearity survives translation only after accounting for the actual
written target packet. The machine's syntactic push bound supplies its factor. -/
theorem linearClock_via
    (translation : OperationalTranslation SA TA se te)
    (exactReplay : translation.toTranslation.Exact)
    (target : CheckerExecution TA te)
    (compilerLinear : LinearTranslationClock translation)
    (checkerLinear : LinearClock target) :
    LinearClock (CheckerExecution.via translation exactReplay target) := by
  obtain ⟨a, b, compilerBound⟩ := compilerLinear
  obtain ⟨c, d, checkerBound⟩ := checkerLinear
  let pushes := StackMachineSpaceGrowth.machinePushBound translation.realization.tm
  refine ⟨a + (2 + c) * (1 + pushes * a),
    b + (2 + c) * (pushes * b) + 2 + d, fun packet => ?_⟩
  have outputBound := MachineBounds.output_length translation.realization packet
  have timeBound := compilerBound packet
  have targetBound := checkerBound (translation.packet packet)
  rw [CheckerExecution.via_time]
  have written : (te.encode (translation.packet packet)).length ≤
      (se.encode packet).length + pushes *
        (a * (se.encode packet).length + b) :=
    outputBound.trans (Nat.add_le_add_left (Nat.mul_le_mul_left pushes timeBound) _)
  calc
    translation.realization.time.eval (se.encode packet).length +
          2 * (te.encode (translation.packet packet)).length + 2 +
          target.time (translation.packet packet)
        ≤ a * (se.encode packet).length + b +
          (2 + c) * (te.encode (translation.packet packet)).length + 2 + d := by
            nlinarith
    _ ≤ a * (se.encode packet).length + b +
          (2 + c) * ((se.encode packet).length + pushes *
            (a * (se.encode packet).length + b)) + 2 + d := by
              exact Nat.add_le_add_right
                (Nat.add_le_add_right
                  (Nat.add_le_add_left (Nat.mul_le_mul_left (2 + c) written) _) _) _
    _ = _ := by dsimp only [pushes]; ring

end Translation

/-- The same two arrows which transfer checking do not identify exact costs,
logical axioms, model classes, or proof-search strategies. -/
theorem polynomialChecking_invariant
    {policy : ComparisonPolicy} (requiresExact : policy.exactReplay = true)
    {source target : EncodedAuthority}
    (equivalent : (mutualSimulation policy).r source target) :
    PolynomialChecking source ↔ PolynomialChecking target :=
  ⟨fun checked => polynomialChecking_of_comparison requiresExact equivalent.2 checked,
    fun checked => polynomialChecking_of_comparison requiresExact equivalent.1 checked⟩

end Mettapedia.GSLT.LanguageDef.ResourceTranslation

namespace Mettapedia.GSLT.LanguageDef.KernelComparisonBoundary

open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.ProofSystems

/-- Existence of a size-bounded compiler, oriented source to destination. -/
def HasSizeTranslation {Claim Source Target : Type*}
    (source : SizedChecker Claim Source) (target : SizedChecker Claim Target) : Prop :=
  Nonempty (SizeSimulation target source)

/-- These checkers have exactly the same accepted numbers and exact authority
for the same mathematical predicate, despite different certificate encodings. -/
theorem same_authority_different_size_class :
    Evenness.unaryChecker.toChecker.Authority Even ∧
    Evenness.binaryChecker.toChecker.Authority Even ∧
    (∀ claim certificate,
      Evenness.unaryChecker.check claim certificate =
        Evenness.binaryChecker.check claim certificate) ∧
    HasSizeTranslation Evenness.unaryChecker.toSizedChecker
      Evenness.binaryChecker.toSizedChecker ∧
    ¬ HasSizeTranslation Evenness.binaryChecker.toSizedChecker
      Evenness.unaryChecker.toSizedChecker := by
  refine ⟨Evenness.unarySystem.authority, Evenness.binarySystem.authority,
    fun _ _ => rfl, ⟨Evenness.binarySimulatesUnary.toSizeSimulation⟩, ?_⟩
  rintro ⟨translation⟩
  exact Evenness.unary_not_sizeSimulates_binary.false translation

/-- Exact authority and polynomial declared checking accounts cannot imply
that all certificate presentations are mutually size-simulating. -/
theorem not_all_polynomial_accounts_size_equivalent :
    ¬ (∀ (first second : ProofSystem Nat Nat Even),
      HasSizeTranslation first.toSizedChecker second.toSizedChecker) := by
  intro collapse
  obtain ⟨translation⟩ := collapse Evenness.binarySystem Evenness.unarySystem
  exact Evenness.unary_not_sizeSimulates_binary.false translation

end Mettapedia.GSLT.LanguageDef.KernelComparisonBoundary

namespace Mettapedia.GSLT.LanguageDef.KernelAuthority.Checker

universe u v w x

variable {Claim : Type u} {Certificate : Type v} {Output : Type w}

/-- Reconstruct untrusted output, publishing only the certificate that the
independent destination checker accepts. Failure to propose and refusal of a
proposal both publish no certificate. -/
def reconstruct (checker : Checker Claim Certificate)
    (propose : Claim → Output → Option Certificate) (claim : Claim) (output : Output) :
    Option Certificate :=
  (propose claim output).bind fun certificate =>
    if checker.check claim certificate then some certificate else none

theorem reconstruct_eq_some (checker : Checker Claim Certificate)
    (propose : Claim → Output → Option Certificate) (claim : Claim) (output : Output)
    (certificate : Certificate) :
    checker.reconstruct propose claim output = some certificate ↔
      propose claim output = some certificate ∧ checker.check claim certificate = true := by
  cases proposed : propose claim output with
  | none => simp [reconstruct, proposed]
  | some candidate =>
      cases checked : checker.check claim candidate with
      | false =>
          constructor
          · intro published
            simp [reconstruct, proposed, checked] at published
          · rintro ⟨same, accepted⟩
            cases same
            simp [checked] at accepted
      | true =>
          constructor
          · intro published
            have same : candidate = certificate := by
              simpa [reconstruct, proposed, checked] using published
            cases same
            exact ⟨rfl, checked⟩
          · rintro ⟨same, _⟩
            cases same
            simp [reconstruct, proposed, checked]

theorem reconstruct_eq_none (checker : Checker Claim Certificate)
    (propose : Claim → Output → Option Certificate) (claim : Claim) (output : Output) :
    checker.reconstruct propose claim output = none ↔
      propose claim output = none ∨
        ∃ certificate, propose claim output = some certificate ∧
          checker.check claim certificate = false := by
  cases proposed : propose claim output with
  | none => simp [reconstruct, proposed]
  | some candidate =>
      cases checked : checker.check claim candidate <;>
        simp [reconstruct, proposed, checked]

/-- A producer has no soundness obligation. The checked result inherits the
destination's independently established meaning. -/
theorem reconstruct_sound (checker : Checker Claim Certificate)
    (propose : Claim → Output → Option Certificate) {Meaning : Claim → Prop}
    (sound : checker.Sound Meaning) {claim : Claim} {output : Output}
    {certificate : Certificate}
    (published : checker.reconstruct propose claim output = some certificate) : Meaning claim :=
  sound claim certificate ((reconstruct_eq_some checker propose claim output certificate).mp published).2

/-- Coverage is relative to what the producer can actually return. It is
not a completeness theorem for an arbitrary heuristic or external prover. -/
theorem exists_reconstruction_iff (checker : Checker Claim Certificate)
    (propose : Claim → Output → Option Certificate) (claim : Claim) :
    (∃ output certificate, checker.reconstruct propose claim output = some certificate) ↔
      ∃ output certificate, propose claim output = some certificate ∧
        checker.check claim certificate = true := by
  simp only [reconstruct_eq_some]

/-- Both trust boundaries remain checked when reconstruction has two stages. -/
theorem reconstruct_compose {Middle : Type x}
    (middle : Checker Claim Middle) (destination : Checker Claim Certificate)
    (first : Claim → Output → Option Middle) (second : Claim → Middle → Option Certificate)
    (claim : Claim) (output : Output) :
    destination.reconstruct
        (fun goal raw => (middle.reconstruct first goal raw).bind (second goal)) claim output =
      (middle.reconstruct first claim output).bind
        (destination.reconstruct second claim) := by
  cases produced : middle.reconstruct first claim output with
  | none =>
      change ((middle.reconstruct first claim output).bind (second claim)).bind _ = _
      rw [produced]
      rfl
  | some certificate =>
      change ((middle.reconstruct first claim output).bind (second claim)).bind _ = _
      rw [produced]
      rfl

end Mettapedia.GSLT.LanguageDef.KernelAuthority.Checker

namespace Mettapedia.GSLT.LanguageDef.ProofSystems

open KernelAuthority

universe u v w

variable {Claim : Type u} {Certificate : Type v} {Output : Type w}

/-- The actual proposal-and-recheck pipeline, with external output as its
untrusted certificate. -/
def reconstructionChecker (destination : Checker Claim Certificate)
    (propose : Claim → Output → Option Certificate) : Checker Claim Output where
  check claim output := (destination.reconstruct propose claim output).isSome

/-- Checked reconstruction is an elaboration into the destination's native
evidence. It need not reconstruct every valid external proof. -/
def reconstructionElaboration (destination : Checker Claim Certificate)
    (propose : Claim → Output → Option Certificate) :
    Elaboration (reconstructionChecker destination propose) destination where
  elaborate := destination.reconstruct propose
  exact claim output := by
    change (destination.reconstruct propose claim output).isSome = true ↔ _
    constructor
    · intro accepted
      obtain ⟨certificate, published⟩ := Option.isSome_iff_exists.mp accepted
      exact ⟨certificate, published,
        ((Checker.reconstruct_eq_some destination propose claim output certificate).mp published).2⟩
    · rintro ⟨certificate, published, _⟩
      simp [published]

namespace Elaboration

variable {computing : SizedChecker Claim Output} {explicit : SizedChecker Claim Certificate}

/-- Size of the certificate actually returned by a partial elaborator.
Failed elaborations return no bytes. This is a size account, not a machine
execution or a polynomial-time computability assertion. -/
def outputSize (elaboration : Elaboration computing.toChecker explicit.toChecker)
    (input : Claim × Output) : Nat :=
  ((elaboration.elaborate input.1 input.2).map explicit.certificateSize).getD 0

/-- A partial elaboration with a polynomial output bound induces the existing
size simulation. The default on failed inputs is charged explicitly. -/
def sizeSimulationOfOutputBound [Inhabited Certificate]
    (elaboration : Elaboration computing.toChecker explicit.toChecker)
    (bounded : PolyBoundedBy elaboration.outputSize computing.inputSize) :
    SizeSimulation explicit computing where
  toSimulation := elaboration.simulation
  sizeBound := by
    obtain ⟨p, bound⟩ := bounded
    refine ⟨p + Polynomial.C (explicit.certificateSize default), fun input => ?_⟩
    rcases input with ⟨claim, output⟩
    have estimate := bound (claim, output)
    cases produced : elaboration.elaborate claim output with
    | none => simp [Elaboration.simulation, produced, Polynomial.eval_add]
    | some certificate =>
        simp only [outputSize, produced, Option.map_some, Option.getD_some] at estimate
        simpa [Elaboration.simulation, produced, Polynomial.eval_add] using
          estimate.trans (Nat.le_add_right _ _)

end Elaboration

/-- An explicit exponential lower-bound family obstructs every polynomial
size translation from a linearly encoded accepted family. No lower bound is
inferred merely from a particular compiler expanding its own output. -/
theorem not_sizeSimulation_of_exponential_family
    {Source : Type v} {Target : Type w}
    (source : SizedChecker Claim Source) (target : SizedChecker Claim Target)
    (claims : Nat → Claim) (certificates : Nat → Source) (factor offset : Nat)
    (accepted : ∀ n, source.check (claims n) (certificates n) = true)
    (small : ∀ n, source.inputSize (claims n, certificates n) ≤ factor * n + offset)
    (large : ∀ n certificate, target.check (claims n) certificate = true →
      2 ^ n ≤ target.certificateSize certificate) :
    ¬ Nonempty (SizeSimulation target source) := by
  rintro ⟨simulation⟩
  obtain ⟨p, bounded⟩ := simulation.sizeBound
  obtain ⟨n, gap⟩ := exists_eval_lt_two_pow p factor offset
  have lower := large n _ (simulation.preserves _ _ (accepted n))
  have upper := (bounded (claims n, certificates n)).trans (eval_mono p (small n))
  exact Nat.not_le_of_gt gap (lower.trans upper)

end Mettapedia.GSLT.LanguageDef.ProofSystems

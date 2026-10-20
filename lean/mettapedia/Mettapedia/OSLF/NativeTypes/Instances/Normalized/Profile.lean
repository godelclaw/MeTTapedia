import Mettapedia.OSLF.NativeTypes.Decision.NormalizedBackend
import Mettapedia.OSLF.NativeTypes.Runtime.Interface
import Mettapedia.OSLF.MeTTaIL.Complete.Presented

/-!
# Authored native execution with certified equality normalization

The operational relation is fixed by the generated plan's actual primitive
receipts. A profile chooses authored equations, presented equality, or an
explicit model extension by specified law moves. Equality normalization and local
firing coherence are checked separately from finite primitive coverage.

Registered observations are predicates of normal forms. Their declarations
use the generated vocabulary's formation permissions; this association does
not identify an arbitrary observation with a constructor's image predicate.
Admission checks the original source. Normalization preserves source sorting;
it need not reflect sorting on arbitrary malformed expressions.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Normalized

open Mettapedia.GSLT
open Mettapedia.OSLF.Framework GSLTTypeSynthesis
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Generation (Generated)
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core
open Mettapedia.OSLF.NativeTypes.Decision.Machine (CursorBackend)
open Mettapedia.OSLF.NativeTypes.Runtime Description

inductive EqualityPolicy where
  | authored
  | presented
  /-- Explicit model laws extend the selected authored equality. Their
  normalization certificate is required by `Profile`; no conservativity
  of this semantic extension is asserted. -/
  | model (moves : Generated → List TypeExpr → TypeExpr → Pattern → Pattern → Prop)

def EqualityPolicy.equation (policy : EqualityPolicy) (generated : Generated)
    (bound : List TypeExpr) (expected : TypeExpr) : Pattern → Pattern → Prop :=
  match policy with
  | .authored => GeneralOccurrenceSemantics.Equation generated.plan bound expected
  | .presented => Complete.Presented.ModelEquation generated.plan bound expected
  | .model moves => fun source target =>
      GeneralOccurrenceSemantics.Equation generated.plan bound expected source target ∨
        moves generated bound expected source target

def EqualityPolicy.sourceSystem (policy : EqualityPolicy) (generated : Generated)
    (bound : List TypeExpr) (expected : TypeExpr) : GSLT :=
  FiniteEquationCoverage.moduloGSLT (policy.equation generated bound expected)
    (GeneralOccurrenceSemantics.Primitive generated.plan bound expected) GeneralRuleJobs.Receipt.target

theorem authored_sourceSystem (generated : Generated) (bound : List TypeExpr) (expected : TypeExpr) :
    EqualityPolicy.authored.sourceSystem generated bound expected =
      GeneralOccurrenceSemantics.gslt generated.plan bound expected := rfl

theorem presented_sourceSystem (generated : Generated) (bound : List TypeExpr) (expected : TypeExpr) :
    EqualityPolicy.presented.sourceSystem generated bound expected =
      Complete.Presented.gslt generated.plan bound expected := rfl

/-- This graph is fixed by the selected source plan, rather than supplied
by a caller alongside unrelated generated metadata. -/
def raw (generated : Generated) (bound : List TypeExpr) (expected : TypeExpr) : GSLT :=
  equalityGSLT Pattern fun source target =>
    ∃ receipt, GeneralOccurrenceSemantics.Primitive generated.plan bound expected source receipt ∧
      receipt.target = target

def Source (generated : Generated) (bound : List TypeExpr) (expected : TypeExpr)
    (source : Pattern) : Prop :=
  OpenPatternWellSorted generated.snapshot.language generated.snapshot.free bound expected source

structure Observation (generated : Generated) where
  name : String
  declaration : Fin generated.snapshot.language.terms.length
  observe : Pattern → Bool

/-- Primitive provenance is separate from endpoint coverage. These maps retain
the full authored packet (declaration, assignment, premise history and site).
They do not assert that every possible authored receipt has been enumerated. -/
structure PrimitiveReceipts (generated : Generated) (bound : List TypeExpr) (expected : TypeExpr)
    (base : Backend (raw generated bound expected) (Source generated bound expected))
    (cursor : CursorBackend (raw generated bound expected) (Source generated bound expected)) where
  finiteOrigin : (source : Pattern) → base.Receipt source → GeneralRuleJobs.Receipt
  finite_valid : ∀ budget source receipt, receipt ∈ base.frontier budget source →
    GeneralOccurrenceSemantics.Primitive generated.plan bound expected source (finiteOrigin source receipt)
  finite_target : ∀ source receipt, base.target source receipt = (finiteOrigin source receipt).target
  cursorOrigin : (source : Pattern) → cursor.Receipt source → GeneralRuleJobs.Receipt
  cursor_valid : ∀ source receipt, receipt ∈ (cursor.tasks source).flatten →
    GeneralOccurrenceSemantics.Primitive generated.plan bound expected source (cursorOrigin source receipt)
  cursor_target : ∀ source receipt, cursor.target source receipt = (cursorOrigin source receipt).target

structure Profile (generated : Generated) (bound : List TypeExpr) (expected : TypeExpr) where
  policy : EqualityPolicy := .authored
  nf : Pattern → Pattern
  certificate : Mettapedia.OSLF.NativeTypes.Decision.NormalizedBackend.Certificate
    (raw generated bound expected) (policy.equation generated bound expected) nf
  foundation : generated.plan.complete = true
  normal_admitted : ∀ source, Source generated bound expected source →
    Source generated bound expected (nf source)
  base : Backend (raw generated bound expected) (Source generated bound expected)
  cursor : CursorBackend (raw generated bound expected) (Source generated bound expected)
  provenance : PrimitiveReceipts generated bound expected base cursor
  profileChoice : Mettapedia.OSLF.NativeTypes.Decision.ProfileAdmission.Choice generated := .uniform
  observations : List (Observation generated)

variable {generated : Generated} {bound : List TypeExpr} {expected : TypeExpr}

abbrev Profile.system (profile : Profile generated bound expected) : GSLT :=
  Mettapedia.OSLF.NativeTypes.Decision.NormalizedBackend.theory
    (raw generated bound expected) (profile.policy.equation generated bound expected)

/-- Erasing a receipt to its endpoint graph changes neither direction of
the independently defined authored/presented step relation. -/
theorem Profile.step_iff_source (profile : Profile generated bound expected)
    (source target : Pattern) :
    profile.system.Step source target ↔
      (profile.policy.sourceSystem generated bound expected).Step source target := by
  change (∃ representative result,
      Relation.EqvGen _ source representative ∧
        (∃ receipt, GeneralOccurrenceSemantics.Primitive generated.plan bound expected
          representative receipt ∧ receipt.target = result) ∧
        Relation.EqvGen _ result target) ↔ _
  constructor
  · rintro ⟨representative, result, before, ⟨receipt, firing, rfl⟩, after⟩
    exact ⟨representative, receipt, before, firing, after⟩
  · rintro ⟨representative, receipt, before, firing, after⟩
    exact ⟨representative, receipt.target, before, ⟨receipt, firing, rfl⟩, after⟩

theorem Profile.equality_iff_source (profile : Profile generated bound expected)
    (source target : Pattern) :
    profile.system.Equiv source target ↔
      (profile.policy.sourceSystem generated bound expected).Equiv source target := Iff.rfl

theorem Profile.equality_exact (profile : Profile generated bound expected)
    (source target : Pattern) :
    (profile.policy.sourceSystem generated bound expected).Equiv source target ↔
      profile.nf source = profile.nf target := by
  rw [← profile.equality_iff_source]
  exact profile.certificate.equality_exact source target

def Profile.admitted (_profile : Profile generated bound expected) (source : Pattern) : Prop :=
  Source generated bound expected source

def Profile.decode (profile : Profile generated bound expected) (source : Pattern) :
    Except SourceIssue {term : Pattern // profile.admitted term ∧ term = source} :=
  if checked : checkOpenPatternWellSorted generated.snapshot.language generated.snapshot.free
      bound expected source = true then
    .ok ⟨source, checkOpenPatternWellSorted_sound checked, rfl⟩
  else .error .illScopedOrSorted

theorem Profile.decode_complete (profile : Profile generated bound expected) (source : Pattern)
    (admitted : ∃ term, profile.admitted term ∧ term = source) :
    (profile.decode source).isOk = true := by
  obtain ⟨term, typed, rfl⟩ := admitted
  have checked := checkOpenPatternWellSorted_complete typed
  simp only [Profile.decode, checked, dite_true]
  rfl

abbrev Profile.Leaf (profile : Profile generated bound expected) := Fin profile.observations.length

def Profile.tests (profile : Profile generated bound expected) (leaf : profile.Leaf) :
    Test profile.system profile.admitted :=
  (Mettapedia.OSLF.NativeTypes.Decision.NormalizedBackend.test
    (raw := raw generated bound expected) (equation := profile.policy.equation generated bound expected)
    (accepted := Source generated bound expected) (nf := profile.nf) profile.certificate
    profile.observations[leaf].observe).onProfile profile.admitted profile.normal_admitted

def Profile.driver (profile : Profile generated bound expected) : Driver where
  generated := generated
  profile := profile.profileChoice
  expected := expected
  system := profile.system
  admitted := profile.admitted
  render := id
  render_injective := Function.injective_id
  decode := profile.decode
  decode_complete := profile.decode_complete
  backend := Mettapedia.OSLF.NativeTypes.Decision.NormalizedBackend.typedBackend
    (raw := raw generated bound expected) (equation := profile.policy.equation generated bound expected)
    (accepted := Source generated bound expected) (nf := profile.nf) profile.certificate
    profile.normal_admitted profile.base
  Leaf := profile.Leaf
  tests := profile.tests
  leafAdmission := rootAdmission generated expected (fun leaf : profile.Leaf =>
    profile.observations[leaf].declaration.val)
  lookup name := (List.finRange profile.observations.length).find? fun leaf =>
    profile.observations[leaf].name == name

def Profile.engine (profile : Profile generated bound expected) : Engine profile.driver where
  cursor := Mettapedia.OSLF.NativeTypes.Decision.NormalizedBackend.typedCursorBackend
    (raw := raw generated bound expected) (equation := profile.policy.equation generated bound expected)
    (accepted := Source generated bound expected) (nf := profile.nf)
    profile.certificate profile.normal_admitted profile.cursor
  leaves (leaf : profile.Leaf) := Mettapedia.OSLF.NativeTypes.Decision.Machine.LeafBackend.ofBoolean
    (profile.tests leaf).predicate
    (fun source => profile.observations[leaf].observe (profile.nf source)) (fun _ => Iff.rfl)
  leaf_meaning _ := rfl

def Profile.installed (profile : Profile generated bound expected) : Installed :=
  ⟨profile.driver, profile.engine⟩

/-- Equality preprocessing retains the supplied cursor's receipt stream.
Full coverage of authored origins is stronger than endpoint coverage. -/
theorem Profile.receipts_exact (profile : Profile generated bound expected) (source : Pattern) :
    (profile.engine.cursor.tasks source).flatten =
      (profile.cursor.tasks (profile.nf source)).flatten := rfl

/-- Every retained packet reads back to a genuine complete primitive firing
at the canonical representative, including its original scoped evidence. -/
theorem Profile.origin_valid (profile : Profile generated bound expected) (source : Pattern)
    (receipt : profile.engine.cursor.Receipt source)
    (listed : receipt ∈ (profile.engine.cursor.tasks source).flatten) :
    GeneralOccurrenceSemantics.Primitive generated.plan bound expected (profile.nf source)
      (profile.provenance.cursorOrigin (profile.nf source) receipt) :=
  profile.provenance.cursor_valid _ _ listed

theorem Profile.origin_target (profile : Profile generated bound expected) (source : Pattern)
    (receipt : profile.engine.cursor.Receipt source) :
    profile.engine.cursor.target source receipt =
      profile.nf (profile.provenance.cursorOrigin (profile.nf source) receipt).target :=
  congrArg profile.nf (profile.provenance.cursor_target _ _)

end Mettapedia.OSLF.NativeTypes.Instances.Normalized

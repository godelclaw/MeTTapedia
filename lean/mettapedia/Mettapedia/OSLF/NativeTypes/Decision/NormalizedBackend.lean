import Mettapedia.OSLF.NativeTypes.Decision.Machine.Interface
import Mettapedia.OSLF.Framework.FiniteEquationCoverage
import Mettapedia.OSLF.MeTTaIL.Complete.Coherence

/-!
# Finite native execution modulo a certified normal form

Equality normalization, local firing coherence, and finite operational
coverage are independent inputs. Quotient coverage is derived from them.
The adapter searches only the canonical source, retains every raw receipt,
and commits canonical targets. It does not enumerate an equation class or
infer termination from decidable equality.

The selected equation relation is explicit. Connecting this extension to an
authored presentation requires equality and transition correspondence at the
language adapter; an arbitrary larger equality is not silently conservative.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Decision.NormalizedBackend

open Mettapedia.GSLT
open Mettapedia.OSLF.Framework
open GSLTTypeSynthesis
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core
open Mettapedia.OSLF.NativeTypes.Decision.Machine
open Mettapedia.OSLF.NativeTypes.Decision.Scheduling (Stream)
open Relation (EqvGen)

variable (raw : GSLT.{0}) (equation : raw.Term → raw.Term → Prop) (nf : raw.Term → raw.Term)

/-- These are local laws, not the quotient successor-completeness theorem. -/
structure Certificate : Prop where
  normalizer : Mettapedia.OSLF.MeTTaIL.Complete.Coherence.Normalizer equation nf
  raw_equations : ∀ {first second}, raw.Equiv first second → EqvGen equation first second
  normalize_step : ∀ {source target}, raw.Step source target →
    ∃ next, raw.Step (nf source) next ∧ EqvGen equation target next

abbrev theory : GSLT := FiniteEquationCoverage.moduloGSLT equation raw.Step id

variable {raw equation nf}

theorem Certificate.equality_exact (certificate : Certificate raw equation nf)
    (first second : raw.Term) :
    (theory raw equation).Equiv first second ↔ nf first = nf second := by
  constructor
  · exact certificate.normalizer.eqvGen_eq
  · intro same
    exact .trans _ _ _ (certificate.normalizer.sound first)
      (.trans _ _ _ (same ▸ EqvGen.refl (nf first))
        (EqvGen.symm _ _ (certificate.normalizer.sound second)))

def admitted (accepted : raw.Term → Prop) (nf : raw.Term → raw.Term) (source : raw.Term) : Prop :=
  accepted (nf source)

theorem Certificate.step_of_raw (certificate : Certificate raw equation nf)
    {source target : raw.Term} (step : raw.Step (nf source) target) :
    (theory raw equation).Step source (nf target) :=
  ⟨nf source, target, certificate.normalizer.sound source, step,
    certificate.normalizer.sound target⟩

/-- Any source representative can fire at the canonical source, with an
equivalent result. This local-to-global implication earns quotient coverage. -/
theorem Certificate.step_at_normal (certificate : Certificate raw equation nf)
    {source target : raw.Term} (step : (theory raw equation).Step source target) :
    ∃ next, raw.Step (nf source) next ∧ EqvGen equation target next := by
  obtain ⟨representative, result, before, fired, after⟩ := step
  obtain ⟨next, normalized, related⟩ := certificate.normalize_step fired
  have same := certificate.normalizer.eqvGen_eq before
  refine ⟨next, ?_, .trans _ _ _ (.symm _ _ after) related⟩
  rw [same]
  exact normalized

/-- The raw receipt is unchanged, including its declaration/premise origin.
Its source is explicitly the canonical source. -/
def backend {accepted : raw.Term → Prop}
    (certificate : Certificate raw equation nf)
    (normal_admitted : ∀ source, accepted source → accepted (nf source))
    (base : Backend raw accepted) :
    Backend (theory raw equation) (admitted accepted nf) where
  Receipt source := base.Receipt (nf source)
  target source receipt := nf (base.target (nf source) receipt)
  frontier budget source := base.frontier budget (nf source)
  closed budget source := base.closed budget (nf source)
  sound budget source receipt member := certificate.step_of_raw (base.sound budget _ receipt member)
  coverage budget source closed actual stepped := by
    obtain ⟨next, fired, equivalent⟩ := certificate.step_at_normal stepped
    obtain ⟨receipt, member, rawEqual⟩ := base.coverage budget (nf source) closed next fired
    exact ⟨receipt, member, .trans _ _ _ equivalent
      (.trans _ _ _ (certificate.raw_equations rawEqual)
        (certificate.normalizer.sound (base.target (nf source) receipt)))⟩
  target_admitted budget source typed receipt member := by
    exact normal_admitted _ (normal_admitted _
      (base.target_admitted budget (nf source) typed receipt member))
  completionBudget source := base.completionBudget (nf source)
  complete_at source typed := base.complete_at (nf source) typed
  frontier_stable source budget enough := base.frontier_stable (nf source) budget enough
  closed_stable source budget enough := base.closed_stable (nf source) budget enough

/-- The runtime retains the original delayed stream, including every
receipt occurrence. Normalization is a declared preprocessing operation,
not a claim about its physical instruction cost. -/
def cursorBackend {accepted : raw.Term → Prop}
    (certificate : Certificate raw equation nf)
    (normal_admitted : ∀ source, accepted source → accepted (nf source))
    (base : CursorBackend raw accepted) :
    CursorBackend (theory raw equation) (admitted accepted nf) where
  Receipt source := base.Receipt (nf source)
  target source receipt := nf (base.target (nf source) receipt)
  tasks source := .pause fun _ => base.tasks (nf source)
  sound source receipt member := by
    exact certificate.step_of_raw (base.sound (nf source) receipt member)
  coverage source typed actual stepped := by
    obtain ⟨next, fired, equivalent⟩ := certificate.step_at_normal stepped
    obtain ⟨receipt, member, rawEqual⟩ := base.coverage (nf source) typed next fired
    exact ⟨receipt, member, .trans _ _ _ equivalent
      (.trans _ _ _ (certificate.raw_equations rawEqual)
        (certificate.normalizer.sound (base.target (nf source) receipt)))⟩
  target_admitted source typed receipt member := by
    exact normal_admitted _ (normal_admitted _ (base.target_admitted (nf source) typed receipt member))

theorem cursor_receipts_exact {accepted : raw.Term → Prop}
    (certificate : Certificate raw equation nf)
    (normal_admitted : ∀ source, accepted source → accepted (nf source))
    (base : CursorBackend raw accepted) (source : raw.Term) :
    ((cursorBackend certificate normal_admitted base).tasks source).flatten =
      (base.tasks (nf source)).flatten := rfl

/-- Source admission can remain on the original terms. Normalization need
only preserve their admission; it need not reflect it on malformed syntax. -/
def typedBackend {accepted : raw.Term → Prop}
    (certificate : Certificate raw equation nf)
    (normal_admitted : ∀ source, accepted source → accepted (nf source))
    (base : Backend raw accepted) : Backend (theory raw equation) accepted where
  Receipt source := base.Receipt (nf source)
  target source receipt := nf (base.target (nf source) receipt)
  frontier budget source := base.frontier budget (nf source)
  closed budget source := base.closed budget (nf source)
  sound := (backend certificate normal_admitted base).sound
  coverage := (backend certificate normal_admitted base).coverage
  target_admitted budget source typed receipt member :=
    normal_admitted _ (base.target_admitted budget (nf source)
      (normal_admitted source typed) receipt member)
  completionBudget source := base.completionBudget (nf source)
  complete_at source typed := base.complete_at (nf source) (normal_admitted source typed)
  frontier_stable source budget enough := base.frontier_stable (nf source) budget enough
  closed_stable source budget enough := base.closed_stable (nf source) budget enough

def typedCursorBackend {accepted : raw.Term → Prop}
    (certificate : Certificate raw equation nf)
    (normal_admitted : ∀ source, accepted source → accepted (nf source))
    (base : CursorBackend raw accepted) : CursorBackend (theory raw equation) accepted where
  Receipt source := base.Receipt (nf source)
  target source receipt := nf (base.target (nf source) receipt)
  tasks source := .pause fun _ => base.tasks (nf source)
  sound := (cursorBackend certificate normal_admitted base).sound
  coverage source typed actual stepped :=
    (cursorBackend certificate normal_admitted base).coverage source
      (normal_admitted source typed) actual stepped
  target_admitted source typed receipt member :=
    normal_admitted _ (base.target_admitted (nf source) (normal_admitted source typed) receipt member)

/-- Normal-form observations are invariant by construction. Arbitrary raw
constructor tests need not have this property. -/
def test {accepted : raw.Term → Prop} (certificate : Certificate raw equation nf)
    (observe : raw.Term → Bool) : Test (theory raw equation) (admitted accepted nf) :=
  Test.ofBoolean
    ⟨fun source => observe (nf source) = true, by
      intro first second equivalent
      exact Iff.of_eq (congrArg (fun value => observe value = true)
        (certificate.normalizer.eqvGen_eq equivalent))⟩
    (fun source => observe (nf source)) (fun _ => Iff.rfl)

def leafBackend {accepted : raw.Term → Prop} (certificate : Certificate raw equation nf)
    (observe : raw.Term → Bool) : LeafBackend (theory raw equation) (admitted accepted nf) :=
  LeafBackend.ofBoolean (test (accepted := accepted) certificate observe).predicate
    (fun source => observe (nf source)) (fun _ => Iff.rfl)

end Mettapedia.OSLF.NativeTypes.Decision.NormalizedBackend

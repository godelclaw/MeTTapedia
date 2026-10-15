import Mettapedia.OSLF.Syntax.RhoScopedScopeDecomposition
import Mettapedia.OSLF.Syntax.RhoFiniteQuotedParallel

/-!
# Validated scope readback and complete scope search

The fast procedure decodes a canonical body, partitions its complete
inventory once, and tests the two independently supplied scope predicates.
Every returned pair satisfies the original quotient-level scope semantics.
Completeness requires the earned exposure and component-colour discipline.

The second procedure searches the complete finite quotation-and-parallel
catalogue. It is complete for arbitrary decidable process predicates and
retains every admitted pair, including distinct origins of the same name.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoScopedScopeDecision

open RhoSchema RhoQuotationClassFibres RhoScopedParallelInventory
open RhoScopedScopeDecomposition RhoFiniteQuotedParallel RhoIntrinsicReadback

variable {context : Ctx sig}

def validated (classify : Prime context → Bool) (left right : Process context → Prop)
    [DecidablePred left] [DecidablePred right] (name : Name context) :
    Option (Process context × Process context) :=
  (readPair classify name).filter (fun pair => decide (left pair.1 ∧ right pair.2))

theorem validated_eq_some_iff {classify : Prime context → Bool}
    {left right : Process context → Prop} [DecidablePred left] [DecidablePred right]
    (name : Name context) (pair : Process context × Process context) :
    validated classify left right name = some pair ↔
      readPair classify name = some pair ∧ left pair.1 ∧ right pair.2 := by
  simp [validated, Option.filter_eq_some_iff]

theorem validated_sound {classify : Prime context → Bool}
    {left right : Process context → Prop} [DecidablePred left] [DecidablePred right]
    {name : Name context} {pair : Process context × Process context}
    (returned : validated classify left right name = some pair) :
    left pair.1 ∧ right pair.2 ∧ quote (join pair.1 pair.2) = name := by
  obtain ⟨decoded, firstAdmitted, secondAdmitted⟩ := (validated_eq_some_iff name pair).mp returned
  exact ⟨firstAdmitted, secondAdmitted, readPair_sound decoded⟩

theorem validated_recovers {classify : Prime context → Bool}
    {left right : Process context → Prop} [DecidablePred left] [DecidablePred right]
    (first : LeftSupported classify left) (second : RightSupported classify right)
    (exposed : ExposedComposites left right)
    {name : Name context} {a b : Process context} (admittedA : left a)
    (admittedB : right b) (readout : quote (join a b) = name) :
    validated classify left right name = some (a, b) := by
  apply (validated_eq_some_iff name (a, b)).mpr
  rw [← readout]
  exact ⟨readPair_of_member first second exposed admittedA admittedB, admittedA, admittedB⟩

def verdict (classify : Prime context → Bool) (left right : Process context → Prop)
    [DecidablePred left] [DecidablePred right] (name : Name context) : Bool :=
  (validated classify left right name).isSome

/-- Soundness holds even for scopes that do not satisfy the fast procedure's admission. -/
theorem verdict_sound {classify : Prime context → Bool}
    {left right : Process context → Prop} [DecidablePred left] [DecidablePred right]
    {name : Name context} (accepted : verdict classify left right name = true) :
    Composite left right name := by
  obtain ⟨pair, returned⟩ := Option.isSome_iff_exists.mp accepted
  obtain ⟨firstAdmitted, secondAdmitted, readout⟩ := validated_sound returned
  exact ⟨pair.1, pair.2, firstAdmitted, secondAdmitted, readout⟩

theorem verdict_iff_composite {classify : Prime context → Bool}
    {left right : Process context → Prop} [DecidablePred left] [DecidablePred right]
    (first : LeftSupported classify left) (second : RightSupported classify right)
    (exposed : ExposedComposites left right) (name : Name context) :
    verdict classify left right name = true ↔ Composite left right name := by
  constructor
  · exact verdict_sound
  · rintro ⟨a, b, admittedA, admittedB, readout⟩
    unfold verdict
    rw [validated_recovers first second exposed admittedA admittedB readout]
    rfl

def fastDecision {classify : Prime context → Bool} {left right : Process context → Prop}
    [DecidablePred left] [DecidablePred right]
    (first : LeftSupported classify left) (second : RightSupported classify right)
    (exposed : ExposedComposites left right) (name : Name context) :
    Decidable (Composite left right name) :=
  decidable_of_iff (verdict classify left right name = true)
    (verdict_iff_composite first second exposed name)

local instance processDecision (context : Ctx sig) : DecidableEq (Process context) :=
  equationClassDecision context Srt.pr

/-- Complete search retains all admitted process-class pairs, rather than choosing one origin. -/
def admittedCatalogue (left right : Process context → Prop)
    [DecidablePred left] [DecidablePred right] (name : Name context) :
    Finset (Process context × Process context) :=
  (decompositions name).filter (fun pair => left pair.1 ∧ right pair.2)

theorem mem_admittedCatalogue {left right : Process context → Prop}
    [DecidablePred left] [DecidablePred right] (name : Name context)
    (pair : Process context × Process context) :
    pair ∈ admittedCatalogue left right name ↔
      left pair.1 ∧ right pair.2 ∧ quote (join pair.1 pair.2) = name := by
  rw [admittedCatalogue, Finset.mem_filter, ← quoted_parallel_iff]
  tauto

theorem composite_iff_catalogue_nonempty {left right : Process context → Prop}
    [DecidablePred left] [DecidablePred right] (name : Name context) :
    Composite left right name ↔ (admittedCatalogue left right name).Nonempty := by
  constructor
  · rintro ⟨a, b, admittedA, admittedB, readout⟩
    exact ⟨(a, b), (mem_admittedCatalogue name (a, b)).mpr
      ⟨admittedA, admittedB, readout⟩⟩
  · rintro ⟨pair, returned⟩
    obtain ⟨admittedA, admittedB, readout⟩ := (mem_admittedCatalogue name pair).mp returned
    exact ⟨pair.1, pair.2, admittedA, admittedB, readout⟩

def catalogueDecision (left right : Process context → Prop)
    [DecidablePred left] [DecidablePred right] (name : Name context) :
    Decidable (Composite left right name) :=
  decidable_of_iff (admittedCatalogue left right name).Nonempty
    (composite_iff_catalogue_nonempty name).symm

/-- Under fast admission, the complete independent search returns exactly the decoded pair. -/
theorem admittedCatalogue_singleton {classify : Prime context → Bool}
    {left right : Process context → Prop} [DecidablePred left] [DecidablePred right]
    (first : LeftSupported classify left) (second : RightSupported classify right)
    (exposed : ExposedComposites left right)
    {name : Name context} {pair : Process context × Process context}
    (returned : validated classify left right name = some pair) :
    admittedCatalogue left right name = {pair} := by
  apply Finset.ext
  intro competitor
  rw [Finset.mem_singleton, mem_admittedCatalogue]
  constructor
  · rintro ⟨firstAdmitted, secondAdmitted, readout⟩
    have recovered := validated_recovers first second exposed firstAdmitted secondAdmitted readout
    rw [returned] at recovered
    exact (Option.some.inj recovered).symm
  · intro same
    subst competitor
    exact validated_sound returned

end Mettapedia.OSLF.Binding.RhoScopedScopeDecision

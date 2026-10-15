import Mettapedia.OSLF.Framework.RhoGeneratedScopeDecision
import Mathlib.Data.List.Range

/-!
# Executable minimum derivation depths of arbitrary atomic scopes

The finite search checks actual bounded membership in increasing depth order,
up to the earned canonical-size cutoff. A returned depth is attained and
excludes every smaller certificate depth. It agrees with the independently
defined semantic stratum. Rejection is complete for the generated scope;
this numeric readout does not identify or erase distinct derivation receipts.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.RhoGeneratedScopeMinimum

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres
open RhoEquationGeneratedScope RhoGeneratedScopeStrata
open RhoScopeBoundedDecision RhoScopeCanonicalSizeBound RhoGeneratedScopeDecision

def minimumDepth? {context : Ctx sig} (left right : Process context → Prop)
    [DecidablePred left] [DecidablePred right] (name : Name context) : Option Nat :=
  (List.range (canonicalSize name + 1)).find? (fun limit => boundedTest left right limit name)

theorem minimum_none_iff {context : Ctx sig} (left right : Process context → Prop)
    [DecidablePred left] [DecidablePred right] (name : Name context) :
    minimumDepth? left right name = none ↔ ¬ generated left right name := by
  rw [minimumDepth?, List.find?_eq_none]
  constructor
  · intro rejected member
    have accepted := (boundedTest_true_iff left right (canonicalSize name) name).mpr
      ((generated_iff_size_bounded left right name).mp member)
    exact rejected (canonicalSize name) (List.mem_range.mpr (Nat.lt_succ_self _)) accepted
  · intro excluded limit _ accepted
    obtain ⟨certificate, _⟩ := (boundedTest_true_iff left right limit name).mp accepted
    exact excluded (certificate_sound certificate)

theorem minimum_some_spec {context : Ctx sig} (left right : Process context → Prop)
    [DecidablePred left] [DecidablePred right] (name : Name context) {depth : Nat}
    (readout : minimumDepth? left right name = some depth) :
    depth ≤ canonicalSize name ∧ Bounded left right depth name ∧
      ∀ earlier, earlier < depth → ¬ Bounded left right earlier name := by
  have found := readout
  change (List.range (canonicalSize name + 1)).find? (fun limit =>
    boundedTest left right limit name) = some depth at found
  have inRange := List.mem_range.mp (List.mem_of_find?_eq_some found)
  have success : boundedTest left right depth name = true :=
    List.find?_some (p := fun limit => boundedTest left right limit name) found
  have attained := (boundedTest_true_iff left right depth name).mp success
  refine ⟨Nat.le_of_lt_succ inRange, attained, ?_⟩
  obtain ⟨_, beforeDepths, afterDepths, presentation, rejected⟩ := List.find?_eq_some_iff_append.mp found
  have ordered : (beforeDepths ++ depth :: afterDepths).Pairwise (· < ·) := by
    rw [← presentation]
    exact List.pairwise_lt_range
  have suffixLater := (List.pairwise_cons.mp (List.pairwise_append.mp ordered).2.1).1
  intro earlier small admitted
  have member : earlier ∈ beforeDepths ++ depth :: afterDepths := by
    rw [← presentation]
    exact List.mem_range.mpr (small.trans inRange)
  rcases List.mem_append.mp member with before | after
  · have refused := rejected earlier before
    have accepted := (boundedTest_true_iff left right earlier name).mpr admitted
    simp only [accepted, Bool.not_true, Bool.false_eq_true] at refused
  · rcases List.mem_cons.mp after with same | later
    · exact Nat.lt_irrefl depth (same ▸ small)
    · exact Nat.lt_asymm small (suffixLater earlier later)

theorem minimum_equals_semantic_stratum {context : Ctx sig}
    (left right : Process context → Prop) [DecidablePred left] [DecidablePred right]
    (name : Name context) {depth : Nat} (readout : minimumDepth? left right name = some depth)
    (member : generated left right name) : depth = stratum member := by
  obtain ⟨_, attained, earlierExcluded⟩ := minimum_some_spec left right name readout
  apply Nat.le_antisymm
  · by_contra notSmall
    exact earlierExcluded (stratum member) (Nat.lt_of_not_ge notSmall) (stratum_attained member)
  · exact stratum_le member attained

theorem minimum_attained_exactly {context : Ctx sig} (left right : Process context → Prop)
    [DecidablePred left] [DecidablePred right] (name : Name context) {depth : Nat}
    (readout : minimumDepth? left right name = some depth) :
    ∃ certificate : Certificate left right name, certificate.depth = depth := by
  obtain ⟨_, ⟨certificate, small⟩, earlierExcluded⟩ := minimum_some_spec left right name readout
  refine ⟨certificate, Nat.le_antisymm small ?_⟩
  by_contra notSmall
  exact earlierExcluded certificate.depth (Nat.lt_of_not_ge notSmall) ⟨certificate, Nat.le_refl _⟩

theorem admitted_minimum_readout {context : Ctx sig} (left right : Process context → Prop)
    [DecidablePred left] [DecidablePred right] (name : Name context)
    (member : generated left right name) : minimumDepth? left right name = some (stratum member) := by
  cases readout : minimumDepth? left right name with
  | none => exact ((minimum_none_iff left right name).mp readout member).elim
  | some depth =>
    have same := minimum_equals_semantic_stratum left right name readout member
    exact congrArg some same

theorem minimum_zero_iff_bounded {context : Ctx sig} (left right : Process context → Prop)
    [DecidablePred left] [DecidablePred right] (name : Name context) :
    minimumDepth? left right name = some 0 ↔ Bounded left right 0 name := by
  constructor
  · intro readout
    exact (minimum_some_spec left right name readout).2.1
  · intro bounded
    obtain ⟨certificate, small⟩ := bounded
    have member := certificate_sound certificate
    have zero : stratum member = 0 := Nat.eq_zero_of_le_zero (stratum_le member ⟨certificate, small⟩)
    rw [admitted_minimum_readout left right name member, zero]

theorem minimum_zero_iff_atomic_pair {context : Ctx sig} (left right : Process context → Prop)
    [DecidablePred left] [DecidablePred right] (name : Name context) :
    minimumDepth? left right name = some 0 ↔
      ∃ first second, left first ∧ right second ∧ quote (join first second) = name := by
  rw [minimum_zero_iff_bounded, bounded_zero_iff_atoms]

theorem returned_minimum_le_every_receipt {context : Ctx sig}
    (left right : Process context → Prop) [DecidablePred left] [DecidablePred right]
    (name : Name context) {depth : Nat} (readout : minimumDepth? left right name = some depth)
    (certificate : Certificate left right name) : depth ≤ certificate.depth := by
  rw [minimum_equals_semantic_stratum left right name readout (certificate_sound certificate)]
  exact stratum_le_certificate _ certificate

theorem minimum_isSome_iff {context : Ctx sig} (left right : Process context → Prop)
    [DecidablePred left] [DecidablePred right] (name : Name context) :
    (minimumDepth? left right name).isSome = true ↔ generated left right name := by
  constructor
  · intro accepted
    cases readout : minimumDepth? left right name with
    | none => rw [readout] at accepted; cases accepted
    | some depth =>
      obtain ⟨_, ⟨certificate, _⟩, _⟩ := minimum_some_spec left right name readout
      exact certificate_sound certificate
  · intro member
    rw [admitted_minimum_readout left right name member]
    rfl

theorem minimum_presence_agrees_with_guard {context : Ctx sig}
    (left right : Process context → Prop) [DecidablePred left] [DecidablePred right]
    (name : Name context) : (minimumDepth? left right name).isSome = guard left right name := by
  apply Bool.eq_iff_iff.mpr
  rw [minimum_isSome_iff, guard_true_iff]

end Mettapedia.OSLF.Framework.RhoGeneratedScopeMinimum

import Mettapedia.GSLT.LanguageDef.RegexDependentProjection
import Mettapedia.GSLT.LanguageDef.RegexExtendedLoweringExecution

/-!
# Selected regex source through the actual authored compiler

Source encoding retains counted constructors and raw lookbehind direction.
Only reference identities are resolved against the completed declaration
layout. The independently attributed source judgment then licenses actual
module-equation lowering and compilation to the structural ordered rows.

Encoding does not first ask the compiler for its result. In particular a
reverse body is not reversed here and then reversed a second time by the
authored lowering equations. This boundary remains separate from native C
refinement and from selection of a CST out of a complete packed forest.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexDependentAuthored

open RegexDependentProjection
open DeterministicEquations (Term Applies apply)
open RegexSourceProjection (State Repeat Flags)


def repeatSource (kind : Repeat) (body : Term) (greedy : Bool) : Term :=
  match kind with
  | .optional => .expr [.sym "re:optional", body, RegexExtendedEquationExecution.preference greedy]
  | .star => .expr [.sym "re:star", body, RegexExtendedEquationExecution.preference greedy]
  | .plus => .expr [.sym "re:plus", body, RegexExtendedEquationExecution.preference greedy]
  | .exact count => .expr [.sym "re:repeat-exact", body, RegexExtendedLoweringExecution.count count]
  | .atLeast count => .expr [.sym "re:repeat-at-least", body, RegexExtendedLoweringExecution.count count, RegexExtendedEquationExecution.preference greedy]
  | .bounded lower extra =>
      .expr [.sym "re:repeat-bounded", body, RegexExtendedLoweringExecution.count lower, RegexExtendedLoweringExecution.count extra, RegexExtendedEquationExecution.preference greedy]

/-- Encode the source structure before lowering. Counts and directions stay
authored inputs; declaration lookup cannot shorten a numeric reference. -/
def encode (layout : State) : SourcePattern → Option Term
  | .regular pattern => some (RegexExtendedEquationExecution.source (embedRegular pattern))
  | .binary alternate first second => do
      let first ← encode layout first
      let second ← encode layout second
      some (.expr [.sym (if alternate then "re:alt" else "re:seq"), first, second])
  | .capture group body => do
      return .expr [.sym "re:capture", RegexExtendedEquationExecution.natural group, ← encode layout body]
  | .repeat kind body greedy => (repeatSource kind · greedy) <$> encode layout body
  | .reference identity mode => do
      return .expr [.sym "re:backref", RegexExtendedEquationExecution.natural (← reference? layout identity), RegexExtendedEquationExecution.comparison mode]
  | .look kind body => RegexExtendedEquationExecution.lookSource kind <$> encode layout body

theorem regular_lowers (pattern : RegexSelection.Pattern) :
    RegexExtendedLoweringExecution.Lowers (RegexExtendedEquationExecution.source (embedRegular pattern)) (embedRegular pattern) := by
  induction pattern with
  | zero => exact .zero
  | epsilon => exact .epsilon
  | literal scalar => exact .literal scalar
  | any => exact .any
  | class_ ranges => exact .class_ ranges
  | assertion name => exact .assertion name
  | seq first second ihFirst ihSecond => exact .seq ihFirst ihSecond
  | alt first second ihFirst ihSecond => exact .alt ihFirst ihSecond
  | optional body greedy ih => exact .optional greedy ih
  | star body greedy ih => exact .star greedy ih
  | plus body greedy ih => exact .plus greedy ih
  | capture group body ih => exact .capture group ih

theorem copies_eq (body tail : Executable) (count : Nat) :
    copies body count tail = RegexExtendedLoweringExecution.prependCopies body count tail := by
  induction count with
  | zero => rfl
  | succ count ih => simp [copies, RegexExtendedLoweringExecution.prependCopies, ih]

theorem options_eq (body : Executable) (count : Nat) (greedy : Bool) :
    options body count greedy = RegexExtendedLoweringExecution.options body count greedy := by
  induction count with
  | zero => rfl
  | succ count ih => simp [options, RegexExtendedLoweringExecution.options, ih]

theorem repeat_lowers {input : Term} {body : Executable} (kind : Repeat) (greedy : Bool)
    (lowered : RegexExtendedLoweringExecution.Lowers input body) :
    RegexExtendedLoweringExecution.Lowers (repeatSource kind input greedy) (applyRepeat kind body greedy) := by
  cases kind with
  | optional => exact .optional greedy lowered
  | star => exact .star greedy lowered
  | plus => exact .plus greedy lowered
  | exact count =>
      simpa [repeatSource, applyRepeat, RegexExtendedLoweringExecution.exactCopies, copies_eq] using RegexExtendedLoweringExecution.Lowers.exact count lowered
  | atLeast count =>
      cases count <;>
        simpa [repeatSource, applyRepeat, RegexExtendedLoweringExecution.atLeast, copies_eq] using
          RegexExtendedLoweringExecution.Lowers.atLeast _ greedy lowered
  | bounded lower extra =>
      simpa [repeatSource, applyRepeat, RegexExtendedLoweringExecution.bounded, copies_eq, options_eq] using
        RegexExtendedLoweringExecution.Lowers.bounded lower extra greedy lowered

theorem look_lowers {input : Term} {body : Executable} (kind : RegexDependentObservation.LookKind)
    (lowered : RegexExtendedLoweringExecution.Lowers input body) :
    RegexExtendedLoweringExecution.Lowers (RegexExtendedEquationExecution.lookSource kind input) (prepareLook kind body) := by
  cases kind
  · exact .lookahead lowered
  · exact .notLookahead lowered
  · exact .lookbehind lowered
  · exact .notLookbehind lowered
  · exact .reverseLookbehind lowered
  · exact .reverseNotLookbehind lowered

/-- Independent source resolution supplies an actual encoded input whose
authored lowering is proved, including counts and the reversal phase. -/
theorem resolves_encoded {layout : State} {pattern : SourcePattern} {target : Executable}
    (resolved : Resolves layout pattern target) :
    ∃ input, encode layout pattern = some input ∧ RegexExtendedLoweringExecution.Lowers input target := by
  induction resolved with
  | regular pattern => exact ⟨_, rfl, regular_lowers pattern⟩
  | @binary alternate first second left right _ _ ihFirst ihSecond =>
      obtain ⟨firstInput, firstEqual, firstLower⟩ := ihFirst
      obtain ⟨secondInput, secondEqual, secondLower⟩ := ihSecond
      cases alternate
      · exact ⟨_, by simp [encode, firstEqual, secondEqual], .seq firstLower secondLower⟩
      · exact ⟨_, by simp [encode, firstEqual, secondEqual], .alt firstLower secondLower⟩
  | @capture group body result _ ih =>
      obtain ⟨input, equal, lowered⟩ := ih
      exact ⟨_, by simp [encode, equal], .capture group lowered⟩
  | @«repeat» kind body greedy result _ ih =>
      obtain ⟨input, equal, lowered⟩ := ih
      exact ⟨_, by simp [encode, equal], repeat_lowers kind greedy lowered⟩
  | reference chosen => exact ⟨_, by simp [encode, chosen], .backref _ _⟩
  | @look kind body result _ ih =>
      obtain ⟨input, equal, lowered⟩ := ih
      exact ⟨_, by simp [encode, equal], look_lowers kind lowered⟩

theorem resolved_authored_exact {layout : State} {pattern : SourcePattern} {target : Executable}
    (resolved : Resolves layout pattern target) :
    ∃ input, encode layout pattern = some input ∧
      ∀ result, Applies RegexExtendedEquationExecution.program RegexExtendedEquationExecution.host "re:compile-authored" [input] result ↔
        result = RegexExtendedAccumulatorExecution.code (RegexExtendedCompilerSemantics.compile target) := by
  obtain ⟨input, encoded, lowered⟩ := resolves_encoded resolved
  exact ⟨input, encoded, RegexExtendedLoweringExecution.compile_authored_result_exact lowered⟩

theorem encoded_authored_exact {layout : State} {pattern : SourcePattern} {target : Executable} {input result : Term}
    (resolved : Resolves layout pattern target) (encoded : encode layout pattern = some input) :
    Applies RegexExtendedEquationExecution.program RegexExtendedEquationExecution.host "re:compile-authored" [input] result ↔
      result = RegexExtendedAccumulatorExecution.code (RegexExtendedCompilerSemantics.compile target) := by
  obtain ⟨actual, actualEncoded, lowered⟩ := resolves_encoded resolved
  have same : actual = input := Option.some.inj (actualEncoded.symm.trans encoded)
  subst actual
  exact RegexExtendedLoweringExecution.compile_authored_result_exact lowered result

/-- The public selected-CST handoff joins a real traversal, its independently
authorized source meaning, and actual extracted module-equation execution. -/
theorem projected_authored_exact (catalog : RegexClassMaterialization.Catalog) (payloadDepth : Nat)
    (policy : LookbehindPolicy) (state : State) (tree : CettaWire.Term) (answer : Output)
    (target : Executable) (fuel : Nat)
    (selected : project (view? catalog payloadDepth policy) fuel state tree = some answer)
    (prepared : prepare answer = some target) :
    ∃ input, Projects (view? catalog payloadDepth policy) state tree answer ∧
      encode answer.state answer.pattern = some input ∧
      ∀ result, Applies RegexExtendedEquationExecution.program RegexExtendedEquationExecution.host "re:compile-authored" [input] result ↔
        result = RegexExtendedAccumulatorExecution.code (RegexExtendedCompilerSemantics.compile target) := by
  have source := project_sound _ _ _ _ _ selected
  have resolved := (prepare_iff answer target).mp prepared |>.2
  obtain ⟨input, encoded, exactness⟩ := resolved_authored_exact resolved
  exact ⟨input, source, encoded, exactness⟩

theorem encoded_authored_completed {layout : State} {pattern : SourcePattern} {target : Executable}
    {input : Term} (resolved : Resolves layout pattern target) (encoded : encode layout pattern = some input)
    (fuel : Nat) (completed : apply RegexExtendedEquationExecution.program RegexExtendedEquationExecution.host fuel "re:compile-authored" [input] ≠ .exhausted) :
    apply RegexExtendedEquationExecution.program RegexExtendedEquationExecution.host fuel "re:compile-authored" [input] =
      .value (RegexExtendedAccumulatorExecution.code (RegexExtendedCompilerSemantics.compile target)) := by
  obtain ⟨actual, actualEncoded, lowered⟩ := resolves_encoded resolved
  have same : actual = input := Option.some.inj (actualEncoded.symm.trans encoded)
  subst actual
  exact RegexExtendedLoweringExecution.compile_authored_completed lowered fuel completed

/-- Every admitted source handoff has a finite sufficient compiler budget;
larger budgets preserve the exact returned rows. No fixed ceiling occurs. -/
theorem projected_authored_terminates (catalog : RegexClassMaterialization.Catalog) (payloadDepth : Nat)
    (policy : LookbehindPolicy) (state : State) (tree : CettaWire.Term) (answer : Output)
    (target : Executable) (fuel : Nat)
    (selected : project (view? catalog payloadDepth policy) fuel state tree = some answer)
    (prepared : prepare answer = some target) :
    ∃ input bound, encode answer.state answer.pattern = some input ∧
      ∀ budget, bound ≤ budget →
        apply RegexExtendedEquationExecution.program RegexExtendedEquationExecution.host budget
          "re:compile-authored" [input] =
          .value (RegexExtendedAccumulatorExecution.code (RegexExtendedCompilerSemantics.compile target)) := by
  obtain ⟨input, _, encoded, exactness⟩ :=
    projected_authored_exact catalog payloadDepth policy state tree answer target fuel selected prepared
  have runs := (exactness _).mpr rfl
  obtain ⟨bound, stable⟩ := runs.at_least
  exact ⟨input, bound, encoded, stable⟩

namespace Controls

private def reverseSource : SourcePattern :=
  .look .reverseBehind (.binary false (.regular (.literal 97)) (.regular (.literal 98)))

private def reverseInput : Term :=
  .expr [.sym "re:lookbehind", .sym "Reverse", .expr [.sym "re:seq",
    .expr [.sym "re:literal", RegexExtendedEquationExecution.natural 97],
    .expr [.sym "re:literal", RegexExtendedEquationExecution.natural 98]]]

private def reverseTarget : Executable := .look .reverseBehind (.seq (.literal 98) (.literal 97))

/-- Written order survives encoding; actual lowering reverses it once. -/
theorem reversed_compilation_has_the_independently_resolved_rows (result : Term) :
    Applies RegexExtendedEquationExecution.program RegexExtendedEquationExecution.host
      "re:compile-authored" [reverseInput] result ↔
      result = RegexExtendedAccumulatorExecution.code (RegexExtendedCompilerSemantics.compile reverseTarget) := by
  have resolved : Resolves {} reverseSource reverseTarget :=
    .look (.binary (.regular (.literal 97)) (.regular (.literal 98)))
  exact encoded_authored_exact resolved rfl

theorem encoding_does_not_prematurely_reverse_consuming_order :
    encode {} reverseSource = some reverseInput := rfl

theorem counted_and_reverse_inputs_retain_their_authored_phase :
    encode ⟨{}, 2, [(1, "x")]⟩
      (.look .reverseBehind (.repeat (.atLeast 1) (.capture 1 (.regular (.literal 97))) true)) =
      some (.expr [.sym "re:lookbehind", .sym "Reverse",
        .expr [.sym "re:repeat-at-least",
          .expr [.sym "re:capture", RegexExtendedEquationExecution.natural 1, .expr [.sym "re:literal", RegexExtendedEquationExecution.natural 97]],
          RegexExtendedLoweringExecution.count 1, .sym "Greedy"]]) := by rfl

theorem named_forward_reference_is_encoded_only_after_layout_resolution :
    encode ⟨{}, 2, [(1, "x")]⟩ (.reference (.name "x") .exact) =
      some (.expr [.sym "re:backref", RegexExtendedEquationExecution.natural 1, .sym "Exact"]) ∧
    encode {} (.reference (.name "x") .exact) = none := by constructor <;> rfl

theorem count_one_uses_plus_not_copy_then_star :
    applyRepeat (.atLeast 1) (.capture 1 (.literal 97)) true = .plus (.capture 1 (.literal 97)) true := by decide

end Controls

end Mettapedia.GSLT.LanguageDef.RegexDependentAuthored

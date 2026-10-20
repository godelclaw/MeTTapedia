import Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory
import Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation
open Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.ModelTransport

/-!
# Executable-independent equation-query steps

`Spec.Eval.EquationQueryStep` is the spec-specification boundary for one selected,
hygienically freshened equation rule.  It describes the match, ambient-binding
merge, and emitted right-hand-side observation.  It deliberately stops at the
work-item boundary: it neither claims nor assumes recursive evaluation of the
emitted atom.

The relation mentions neither executable matcher nor executable merger.  An
engine-specific conformance theorem is responsible for proving that its rule
selection and alpha-renaming produce the `freshPattern` and `freshRhs` supplied
here.
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory (HEBindingSatisfied applyClassSolution)
open Spec.Bindings.ScopeObservation

/-- One successful equation-query step from a selected, freshened rule.

`emitted` is observationally the freshened rule RHS under every model of the
merged spec binding set.  This is the complete semantic content of the work
item produced by a successful query step; recursive evaluation belongs to a
separate evaluator-conformance judgment. -/
def Spec.Eval.EquationQueryStep
    (query freshPattern : Atom)
    (incoming output : Bindings)
    (freshRhs emitted : Metta.Atom) : Prop :=
  ∃ matched : Bindings,
    Spec.Match.SolutionTheory.VarsDisjoint query freshPattern ∧
      Spec.Match.Merge.MatchRel
        Spec.Match.Merge.equalityGroundedSemantic
        query freshPattern matched ∧
      LogicalMergeRel incoming matched output ∧
      ∀ valuation : String → Metta.Atom,
        HEBindingSatisfied valuation output →
          applyClassSolution valuation emitted =
            applyClassSolution valuation freshRhs

/-! ## Boundary examples -/

/-- Positive: an equal-symbol rule can emit its unchanged RHS from empty
bindings. -/
example :
    Spec.Eval.EquationQueryStep
      (.symbol "a") (.symbol "a")
      Bindings.empty Bindings.empty (.sym "result") (.sym "result") := by
  refine ⟨Bindings.empty,
    (by simp [Spec.Match.SolutionTheory.VarsDisjoint, Spec.Match.SolutionTheory.encodeModelAtom,
      Metta.Atom.vars]),
    Spec.Match.Merge.MatchRel.symSym "a"
      Spec.Match.Merge.semanticLoopFree_empty, ?_, ?_⟩
  · refine ⟨BindingSourceAgreement.refl _, fun name => .var name, ?_⟩
    simp [Spec.Type.RuntimeRefinement.TypeBindingSatisfied, Bindings.empty]
  · intro valuation _
    rfl

/-- Negative: a successful equation-query step cannot disguise a mismatch
between distinct symbol heads. -/
theorem symbol_mismatch_not_specEquationQueryStep
    {left right : String} (hne : left ≠ right)
    (incoming output : Bindings) (freshRhs emitted : Metta.Atom) :
    ¬Spec.Eval.EquationQueryStep
      (.symbol left) (.symbol right)
      incoming output freshRhs emitted := by
  rintro ⟨matched, _hygienic, hmatch, _hmerge, _hemitted⟩
  exact Spec.Match.Merge.symbol_mismatch_not_match
    hne matched hmatch

end Mettapedia.Languages.MeTTa.HE

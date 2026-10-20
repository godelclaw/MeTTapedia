import Mettapedia.Languages.MeTTa.HE.LeaTTaBindingTransport
import Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory
open Mettapedia.Languages.MeTTa.HE.BindingComposition

/-!
# Matching solution theories across runtime representations

`DeclMatchSpec`/`DeclMergeSpec` characterize the executable matcher
syntactically (which derivations exist). The HE binding algebra supplies the extensional
account: every binding set returned by the executable `matchAtoms` presents,
through its value and equality constraints, **exactly the solution set of the
input atom equation**, and the merge/add helpers present exactly constraint
conjunction.  Representation details — relation order, equality orientation,
class chronology, the particular reconciliation route taken — are invisible at
this layer.

The native solution laws below are provided by `BindingComposition`; they
depend only on the HE matcher and the structural atom model. This downstream
module compares them with the other runtime's solution theory.

Available results:
* `matchAtoms_solution_iff` — executable matcher outputs present the equation.
* `matchAtomsList_solution_iff` — a list result presents the selected seed and
  the component equations, without requiring expression admission.
* `mergeBindings_solution_iff` — merge presents solution intersection.
* `addVarBinding_solution_iff` / `addVarEquality_solution_iff` — the
  incremental helpers present exactly one added constraint.
* `heMatch_leaMatch_solutionTheoryEquiv` — an executable HE witness and a
  repaired-LeaTTa witness for one translated equation always have equal
  binding solution theories: the semantic half of the cross-engine congruence,
  with no comparison of binding representations.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaBridge

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-! ## The cross-engine corollary -/

/-- Any executable HE match witness and any repaired-LeaTTa match witness for
one translated equation have **equal binding solution theories**.  This is the
semantic half of the cross-engine congruence, obtained with no comparison of
binding representations — either engine may present the solution set through
any spanning tree, orientation, or reconciliation route. -/
theorem heMatch_leaMatch_solutionTheoryEquiv
    {l r : Atom} {b : Bindings} {fuel : Nat} {lb : Metta.Bindings}
    (hHE : b ∈ matchAtoms l r fuel)
    (hLea : lb ∈ Metta.matchAtoms (encodeModelAtom l) (encodeModelAtom r))
    (hlNoFloat : MettaAtomNoFloat (encodeModelAtom l))
    (hrNoFloat : MettaAtomNoFloat (encodeModelAtom r)) :
    LeaBindingSolutionTheoryEquiv b lb := by
  intro μ
  rw [matchAtoms_solution_iff hHE μ]
  exact (leaMatchAtoms_solution_iff μ hlNoFloat hrNoFloat hLea).symm

/-! ## Oracles -/

/-- POSITIVE: on the connected-class regression shape, the solution reading of
**any** matcher output identifies the two query variables — the observable the
oriented-`val` unifier-discard bug lost. -/
example {b : Bindings} {μ : String → Metta.Atom}
    (h : b ∈ matchAtoms
      (.expression [.symbol "g", .var "q1", .var "q1", .var "q2"])
      (.expression [.symbol "g", .var "p1", .var "p2", .var "p2"]) 10)
    (hsat : HEBindingSatisfied μ b) : μ "q1" = μ "q2" := by
  have heq := (matchAtoms_solution_iff h μ).mp hsat
  simp only [MettaEquationSatisfied, applyModel_expression,
    encodeModelAtoms_cons, encodeModelAtoms_nil, List.map_cons, List.map_nil,
    applyModel_symbol, applyModel_var, Metta.Atom.expr.injEq,
    List.cons.injEq, and_true, true_and] at heq
  obtain ⟨h1, h2, h3⟩ := heq
  exact h2.trans h3.symm

/-- NEGATIVE: the solution reading accepts nothing beyond the equation — a
valuation disagreeing with the matched symbol is rejected. -/
example {b : Bindings}
    (h : b ∈ matchAtoms (.var "x") (.symbol "a") 10) :
    ¬ HEBindingSatisfied (fun _ => .sym "b") b := by
  intro hsat
  have heq := (matchAtoms_solution_iff h _).mp hsat
  simp [MettaEquationSatisfied] at heq

end Mettapedia.Languages.MeTTa.HE.LeaTTaBridge

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaSpecConformance
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- A specification match result and any repaired-LeaTTa result for the translated
equation present the same complete binding solution theory.  This theorem is
direct: it compares the spec relation with LeaTTa and has no HE executable
matcher or merger premise. -/
theorem specMatch_leaMatch_solutionTheoryEquiv
    {query pattern : Atom} {specOut : Bindings}
    {leaOut : Metta.Bindings}
    (hspec : Spec.Match.Merge.MatchRel
      Spec.Match.Merge.equalityGroundedSemantic
      query pattern specOut)
    (hlea : leaOut ∈ Metta.matchAtoms
      (encodeModelAtom pattern) (encodeModelAtom query)) :
    LeaBindingSolutionTheoryEquiv specOut leaOut := by
  intro valuation
  rw [matchRel_solution_iff hspec valuation,
    leaMatchAtoms_solution_iff valuation
      (encodeModelAtom_noFloat pattern)
      (encodeModelAtom_noFloat query) hlea]
  simp only [MettaEquationSatisfied]
  exact eq_comm

end Mettapedia.Languages.MeTTa.HE.LeaTTaSpecConformance

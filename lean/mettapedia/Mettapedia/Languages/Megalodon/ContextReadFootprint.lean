import Mettapedia.Languages.Megalodon.CursorEnvironment

/-!
# Context formation and conversion enlarge a checker's read footprint

The exact local hypothesis rule does not consult its environment. A checker
that additionally forms hypotheses does consult it; a converter also reads
definition bodies. Consequently the exact rule's witness-only footprint is
insufficient for these additional observations. The negative controls below
exhibit both failures on ordinary well-formed propositional declarations.

The repaired support frames the existing type inference and normalization
operations, including absent names and transitive definition dependencies.
This is not a verification of the native lazy converter or its C caches.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.ContextReadFootprint

open MathdataKernel ProofJudgment BorrowedProofCursor NativeSupport
open EnvironmentDependency EnvironmentDependencyCheck

def hypothesesSupport : List Tm → Support
  | [] => ∅
  | term :: rest => termSupport term ∪ hypothesesSupport rest

/-- This matches the environment-dependent part of native `mg_ctx_formed`:
every hypothesis must have ordinary type Prop in the supplied term context. -/
def hypothesesFormed (environment : Environment) (depth : Nat) (terms : List Tp)
    (hypotheses : List Tm) : Bool :=
  hypotheses.all fun term => inferTerm environment depth terms term == some .prop

def contextFormed (environment : Environment) (context : Context) : Bool :=
  hypothesesFormed environment context.typeDepth context.terms context.hypotheses

def judgmentSupport (judgment : Judgment) : Support :=
  hypothesesSupport judgment.context.hypotheses ∪ termSupport judgment.proposition

/-- Source operands which the exact structural rules do not inspect can be
inputs of a lazy conversion check, so they must also be retained. -/
def operandSupport : Witness → Support
  | .termApp argument _ body => termSupport argument ∪ termSupport body
  | .proofApp domain | .proofLam domain => termSupport domain
  | .typeApp _ body => termSupport body
  | .known name => {.knownName name}
  | _ => ∅

def requested (witness : Witness) (judgment : Judgment) : Support :=
  CursorEnvironment.requested witness ∪ operandSupport witness ∪ judgmentSupport judgment

def footprint (environment : Environment) (witness : Witness) (judgment : Judgment) : Support :=
  dependencyClosure environment (requested witness judgment)

def revalidate (source target : Environment) (witness : Witness) (judgment : Judgment) : Bool :=
  agreementCheck source target (footprint source witness judgment)

theorem hypothesesFormed_frame {source target : Environment} {support : Support}
    (agreement : Agreement source target support) (depth : Nat) (terms : List Tp)
    (hypotheses : List Tm) (included : hypothesesSupport hypotheses ⊆ support) :
    hypothesesFormed target depth terms hypotheses =
      hypothesesFormed source depth terms hypotheses := by
  induction hypotheses with
  | nil => rfl
  | cons term rest ih =>
      obtain ⟨head, tail⟩ := Finset.union_subset_iff.mp included
      have restSame := ih tail
      unfold hypothesesFormed at restSame
      simp only [hypothesesFormed, List.all_cons,
        inferTerm_frame agreement head, restSame]

/-- Normalization-based comparison retains exhaustion as `none`. It is a
reference observation for conversion, not the native lazy algorithm. -/
def compareNormal (environment : Environment) (fuel : Nat) (left right : Tm) : Option Bool := do
  let l ← normalize environment fuel left
  let r ← normalize environment fuel right
  pure (l == r)

theorem compareNormal_frame {source target : Environment} {support : Support}
    (agreement : Agreement source target support) (closed : Closed source support)
    (fuel : Nat) (left right : Tm)
    (leftIncluded : termSupport left ⊆ support)
    (rightIncluded : termSupport right ⊆ support) :
    compareNormal target fuel left right = compareNormal source fuel left right := by
  simp only [compareNormal, normalize_frame agreement closed leftIncluded,
    normalize_frame agreement closed rightIncluded]

theorem revalidate_preserves_context_and_claim {source target : Environment}
    {witness : Witness} {judgment : Judgment}
    (accepted : revalidate source target witness judgment = true) (fuel : Nat) :
    contextFormed target judgment.context = contextFormed source judgment.context ∧
      checkProposition target judgment.context.typeDepth judgment.context.terms judgment.proposition =
        checkProposition source judgment.context.typeDepth judgment.context.terms judgment.proposition ∧
      normalize target fuel judgment.proposition = normalize source fuel judgment.proposition := by
  have agreement := (agreementCheck_iff source target _).mp accepted
  have included : judgmentSupport judgment ⊆ footprint source witness judgment :=
    Finset.Subset.trans Finset.subset_union_right
      (subset_dependencyClosure source (requested witness judgment))
  obtain ⟨hyps, prop⟩ := Finset.union_subset_iff.mp included
  exact ⟨hypothesesFormed_frame agreement _ _ _ hyps,
    checkProposition_frame agreement prop,
    normalize_frame agreement (dependencyClosure_closed source _) prop⟩

theorem revalidate_preserves_exact_observation {source target : Environment}
    {witness : Witness} {judgment : Judgment}
    (accepted : revalidate source target witness judgment = true) (fuel : Nat) :
    RuleObservation.observe target fuel witness judgment =
      RuleObservation.observe source fuel witness judgment := by
  apply CursorEnvironment.observation_frame
    ((agreementCheck_iff source target _).mp accepted)
    (dependencyClosure_closed source _) fuel witness judgment
  exact (Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left).trans
    (subset_dependencyClosure source (requested witness judgment))

namespace Controls

def declared : Environment := { terms := [⟨"P", .prop, none⟩] }
def withdrawn : Environment := {}
def extended : Environment := { terms := [⟨"unrelated", .prop, none⟩, ⟨"P", .prop, none⟩] }
def hypothesis : Judgment := ⟨⟨0, [], [.named "P"]⟩, .named "P"⟩

/-- The exact hypothesis rule's old footprint is correct for that rule, but
cannot justify the additional context-formation check. -/
theorem witness_only_misses_context_withdrawal :
    CursorEnvironment.revalidate declared withdrawn (.hyp 0) = true ∧
      contextFormed declared hypothesis.context = true ∧
      contextFormed withdrawn hypothesis.context = false := by decide

theorem corrected_footprint_rejects_withdrawal :
    revalidate declared withdrawn (.hyp 0) hypothesis = false := by decide

theorem unrelated_extension_still_accepted :
    revalidate declared extended (.hyp 0) hypothesis = true := by decide

def withAlias : Environment :=
  { terms := [⟨"alias", .prop, some (.named "P")⟩, ⟨"P", .prop, none⟩] }

/-- Modus ponens in the exact checker compares syntax. Extending it to
conversion introduces a read of `alias`, although the old witness support
for proof application is empty. Withdrawal changes the conversion answer. -/
theorem witness_only_misses_conversion_withdrawal :
    CursorEnvironment.revalidate withAlias declared (.proofApp (.named "P")) = true ∧
      compareNormal withAlias 2 (.named "alias") (.named "P") = some true ∧
      compareNormal declared 2 (.named "alias") (.named "P") = some false := by
  refine ⟨by decide, ?_, ?_⟩ <;>
    simp [compareNormal, withAlias, declared, MathdataKernel.normalize, deltaNormalize,
      Environment.lookupTerm?, lookupTermList?, Tm.normalize, Tm.normalizeOne]

theorem conversion_support_rejects_withdrawal :
    revalidate withAlias declared (.proofApp (.named "alias")) hypothesis = false := by decide

end Controls

#print axioms hypothesesFormed_frame
#print axioms compareNormal_frame
#print axioms revalidate_preserves_context_and_claim
#print axioms revalidate_preserves_exact_observation
#print axioms Controls.witness_only_misses_context_withdrawal
#print axioms Controls.witness_only_misses_conversion_withdrawal

end Mettapedia.Languages.Megalodon.ContextReadFootprint

import Mettapedia.Languages.MM0.HOLKernelJudgment
import Mettapedia.Languages.MM0.Kernel.ProofChecking

/-!
# Structured MM0 proofs for the maintained HOL context rules

The declarations are the actual `id`, `syl`, `ian`, `anl` and `anr` schemas.
Their native applications retain explicit substitutions and ordered child
proofs. Availability is a lookup in the selected theorem signature; sequential
admission of that signature remains a separate premise of the kernel theory.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.HOLKernelStructuralRules

open Kernel HOLKernelSyntax HOLKernelJudgment

inductive Rule where
  | id | syl | ian | anl | anr
  deriving DecidableEq, Repr

def Rule.all : List Rule := [.id, .syl, .ian, .anl, .anr]

theorem Rule.mem_all (rule : Rule) : rule ∈ Rule.all := by
  cases rule <;> simp [Rule.all]

def Rule.name : Rule → String
  | .id => "id"
  | .syl => "syl"
  | .ian => "ian"
  | .anl => "anl"
  | .anr => "anr"

def Rule.declaration (references : Symbol → Nat) (wff : Nat) : Rule → TheoremDecl
  | .id => ⟨[.regular wff ∅], [], entails references (.var 0) (.var 0)⟩
  | .syl => ⟨[.regular wff ∅, .regular wff ∅, .regular wff ∅],
      [entails references (.var 0) (.var 1), entails references (.var 1) (.var 2)],
      entails references (.var 0) (.var 2)⟩
  | .ian => ⟨[.regular wff ∅, .regular wff ∅, .regular wff ∅],
      [entails references (.var 0) (.var 1), entails references (.var 0) (.var 2)],
      entails references (.var 0) (conjunction references (.var 1) (.var 2))⟩
  | .anl => ⟨[.regular wff ∅, .regular wff ∅], [],
      entails references (conjunction references (.var 0) (.var 1)) (.var 0)⟩
  | .anr => ⟨[.regular wff ∅, .regular wff ∅], [],
      entails references (conjunction references (.var 0) (.var 1)) (.var 1)⟩

structure Rules (theorems : TheoremSignature) (references : Symbol → Nat) (wff : Nat) where
  index : Rule → Nat
  declared : ∀ rule, theorems (index rule) = some (rule.declaration references wff)

def Rules.read? (theorems : TheoremSignature) (references : Symbol → Nat) (wff : Nat)
    (indices : Rule → Nat) : Option (Rules theorems references wff) :=
  if known : Rule.all.all (fun rule =>
      decide (theorems (indices rule) = some (rule.declaration references wff))) = true then
    some {
      index := indices
      declared := by
        intro rule
        exact of_decide_eq_true ((List.all_eq_true.mp known) rule (Rule.mem_all rule)) }
  else none

variable {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
variable {theorems : TheoremSignature} {context : Context} {hypotheses : List Preterm}

abbrev CheckedProof (expression : Preterm) :=
  { witness : ProofWitness //
    ProofWitness.Checks terms definitions theorems context hypotheses witness expression }

private theorem regular_admissible (values : List Preterm) (sort : Nat)
    (typed : ∀ value ∈ values, Preterm.HasType terms context value [] sort) :
    Substitution.Admissible terms (values.map (fun _ => .regular sort ∅)) context values := by
  apply (Substitution.admissible_iff_typed_of_regular_formals _ _ _ _ ?_).mpr
  · induction values with
    | nil => exact .nil
    | cons head tail ih =>
        exact .cons (.regular (typed head (List.mem_cons_self)))
          (ih (fun value member => typed value (List.mem_cons_of_mem _ member)))
  · intro binder member
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp member
    exact ⟨sort, ∅, rfl⟩

def identity (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids.wff)
    (proposition : Preterm)
    (sorted : Preterm.HasType terms context proposition [] signature.ids.wff) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol proposition proposition) := by
  refine ⟨.theoremApp (rules.index .id) [proposition] [],
    .theoremApp (instantiation := ⟨[], entails signature.symbol proposition proposition⟩)
      (rules.declared .id) ?_ .nil⟩
  refine ⟨?_, .nil, ?_⟩
  · apply regular_admissible [proposition]
    intro value member
    have same : value = proposition := by simpa only [List.mem_singleton] using member
    simpa only [same] using sorted
  · apply Preterm.substitute_sound
    simp [Rule.declaration, entails, applySymbol, Preterm.applyArgs,
      Preterm.substitute, Substitution.ofList]

def compose (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids.wff)
    (first middle last : Preterm)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.wff)
    (middleSorted : Preterm.HasType terms context middle [] signature.ids.wff)
    (lastSorted : Preterm.HasType terms context last [] signature.ids.wff)
    (one : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses) (entails signature.symbol first middle))
    (two : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses) (entails signature.symbol middle last)) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses) (entails signature.symbol first last) := by
  refine ⟨.theoremApp (rules.index .syl) [first, middle, last] [one.val, two.val],
    .theoremApp (instantiation := ⟨[entails signature.symbol first middle,
      entails signature.symbol middle last], entails signature.symbol first last⟩)
      (rules.declared .syl) ?_ (.cons one.property (.cons two.property .nil))⟩
  refine ⟨?_, .cons ?_ (.cons ?_ .nil), ?_⟩
  · apply regular_admissible [first, middle, last]
    intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> assumption
  all_goals
    apply Preterm.substitute_sound
    simp [Rule.declaration, entails, applySymbol, Preterm.applyArgs,
      Preterm.substitute, Substitution.ofList]

def pair (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids.wff)
    (antecedent first second : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.wff)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.wff)
    (one : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses) (entails signature.symbol antecedent first))
    (two : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses) (entails signature.symbol antecedent second)) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (conjunction signature.symbol first second)) := by
  refine ⟨.theoremApp (rules.index .ian) [antecedent, first, second] [one.val, two.val],
    .theoremApp (instantiation := ⟨[entails signature.symbol antecedent first,
      entails signature.symbol antecedent second],
      entails signature.symbol antecedent (conjunction signature.symbol first second)⟩)
      (rules.declared .ian) ?_ (.cons one.property (.cons two.property .nil))⟩
  refine ⟨?_, .cons ?_ (.cons ?_ .nil), ?_⟩
  · apply regular_admissible [antecedent, first, second]
    intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> assumption
  all_goals
    apply Preterm.substitute_sound
    simp [Rule.declaration, entails, conjunction, applySymbol, Preterm.applyArgs,
      Preterm.substitute, Substitution.ofList]

def left (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids.wff)
    (first second : Preterm)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.wff)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.wff) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (conjunction signature.symbol first second) first) := by
  refine ⟨.theoremApp (rules.index .anl) [first, second] [],
    .theoremApp (instantiation := ⟨[],
      entails signature.symbol (conjunction signature.symbol first second) first⟩)
      (rules.declared .anl) ?_ .nil⟩
  refine ⟨?_, .nil, ?_⟩
  · apply regular_admissible [first, second]
    intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> assumption
  · apply Preterm.substitute_sound
    simp [Rule.declaration, entails, conjunction, applySymbol, Preterm.applyArgs,
      Preterm.substitute, Substitution.ofList]

def right (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids.wff)
    (first second : Preterm)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.wff)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.wff) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (conjunction signature.symbol first second) second) := by
  refine ⟨.theoremApp (rules.index .anr) [first, second] [],
    .theoremApp (instantiation := ⟨[],
      entails signature.symbol (conjunction signature.symbol first second) second⟩)
      (rules.declared .anr) ?_ .nil⟩
  refine ⟨?_, .nil, ?_⟩
  · apply regular_admissible [first, second]
    intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> assumption
  · apply Preterm.substitute_sound
    simp [Rule.declaration, entails, conjunction, applySymbol, Preterm.applyArgs,
      Preterm.substitute, Substitution.ofList]

def weaken (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids.wff)
    (antecedent extra conclusion : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (extraSorted : Preterm.HasType terms context extra [] signature.ids.wff)
    (conclusionSorted : Preterm.HasType terms context conclusion [] signature.ids.wff)
    (source : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses) (entails signature.symbol antecedent conclusion)) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (conjunction signature.symbol antecedent extra) conclusion) :=
  compose signature rules _ _ _
    (conjunction_sorted signature _ antecedentSorted extraSorted) antecedentSorted conclusionSorted
    (left signature rules antecedent extra antecedentSorted extraSorted) source

structure ProofContext (terms : TermSignature) (definitions : Definition.Signature)
    (theorems : TheoremSignature) (context : Context) (hypotheses : List Preterm)
    (references : Symbol → Nat) (wff : Nat) where
  formation : Preterm
  logical : Preterm
  formationSorted : Preterm.HasType terms context formation [] wff
  logicalSorted : Preterm.HasType terms context logical [] wff
  projection : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
    (context := context) (hypotheses := hypotheses) (entails references logical formation)

def ProofContext.identity (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids.wff) (antecedent : Preterm)
    (sorted : Preterm.HasType terms context antecedent [] signature.ids.wff) :
    ProofContext terms definitions theorems context hypotheses signature.symbol signature.ids.wff :=
  ⟨antecedent, antecedent, sorted, sorted, HOLKernelStructuralRules.identity signature rules antecedent sorted⟩

def ProofContext.under (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids.wff)
    (source : ProofContext terms definitions theorems context hypotheses signature.symbol signature.ids.wff)
    (assumption : Preterm)
    (sorted : Preterm.HasType terms context assumption [] signature.ids.wff) :
    ProofContext terms definitions theorems context hypotheses signature.symbol signature.ids.wff :=
  ⟨source.formation, conjunction signature.symbol source.logical assumption,
    source.formationSorted, conjunction_sorted signature context source.logicalSorted sorted,
    HOLKernelStructuralRules.weaken signature rules source.logical assumption source.formation
      source.logicalSorted sorted source.formationSorted source.projection⟩

def ProofContext.promote (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids.wff)
    (source : ProofContext terms definitions theorems context hypotheses signature.symbol signature.ids.wff)
    (conclusion : Preterm)
    (sorted : Preterm.HasType terms context conclusion [] signature.ids.wff)
    (proof : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses) (entails signature.symbol source.formation conclusion)) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses) (entails signature.symbol source.logical conclusion) :=
  compose signature rules source.logical source.formation conclusion source.logicalSorted source.formationSorted
    sorted source.projection proof

def ProofContext.extend (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids.wff)
    (source : ProofContext terms definitions theorems context hypotheses signature.symbol signature.ids.wff)
    (assumption : Preterm)
    (sorted : Preterm.HasType terms context assumption [] signature.ids.wff) :
    ProofContext terms definitions theorems context hypotheses signature.symbol signature.ids.wff := by
  let extendedLogical := conjunction signature.symbol source.logical assumption
  have extendedLogicalSorted := conjunction_sorted signature context source.logicalSorted sorted
  let formationProjection := HOLKernelStructuralRules.weaken signature rules source.logical assumption source.formation
    source.logicalSorted sorted source.formationSorted source.projection
  let assumptionProjection := HOLKernelStructuralRules.right (definitions := definitions) (hypotheses := hypotheses)
    signature rules source.logical assumption source.logicalSorted sorted
  exact ⟨conjunction signature.symbol source.formation assumption, extendedLogical,
    conjunction_sorted signature context source.formationSorted sorted, extendedLogicalSorted,
    pair signature rules extendedLogical source.formation assumption extendedLogicalSorted source.formationSorted
      sorted formationProjection assumptionProjection⟩

def ProofContext.promoteUnder (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids.wff)
    (source : ProofContext terms definitions theorems context hypotheses signature.symbol signature.ids.wff)
    (assumption conclusion : Preterm)
    (assumptionSorted : Preterm.HasType terms context assumption [] signature.ids.wff)
    (conclusionSorted : Preterm.HasType terms context conclusion [] signature.ids.wff)
    (proof : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (conjunction signature.symbol source.formation assumption) conclusion)) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (conjunction signature.symbol source.logical assumption) conclusion) :=
  (source.extend signature rules assumption assumptionSorted).promote signature rules conclusion conclusionSorted proof


#print axioms ProofContext.identity
#print axioms ProofContext.under
#print axioms ProofContext.promote
#print axioms ProofContext.extend
#print axioms ProofContext.promoteUnder
#print axioms identity
#print axioms compose
#print axioms pair
#print axioms left
#print axioms right
#print axioms weaken

end Mettapedia.Languages.MM0.HOLKernelStructuralRules

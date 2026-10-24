import Mettapedia.TypeTheory.HypercubeBubbles
import Mettapedia.GSLT.Dedukti.PureTypeSystemChecker
import Mettapedia.TypeTheory.ContextualCodeObserverFactorization
import Mettapedia.TypeTheory.TarskiCodeFamilyObserverFactorization

/-!
# Direct and reified index formation in the lambda cube

The direct interface in `HypercubeBubbles` binds a value `x : A` and forms
`P x` in the same context.  This module gives the corresponding type-reified
interface in the same annotated PTS:

```
Q : Type → Type ⊢ Π X : Type. Π x : X. Q X
```

The reified route does not use the value-to-type product rule.  It uses
ordinary functions, polymorphism and type operators instead.  A caller must
supply the type code `X`, an inhabitant `x : X`, and a separate semantic
coherence argument relating `Q X` to the direct family at the represented
value.  The previously proved quote/splice and Tarski-decoding factorization
theorems state those semantic obligations; formation alone does not discharge
them.

The executable controls compare the actual terms with the existing sound PTS
checker.  Their fuel thresholds and syntax-node counts are measurements of
this reference checker and representation, not universal complexity bounds.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ReifiedIndexElaboration

open Mettapedia.GSLT.Dedukti
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF (Srt)
open Mettapedia.GSLT.LanguageDef.LFProfile
open Mettapedia.TypeTheory.HypercubeBubbles

/-! ## Every annotated product in a typed subject is licensed -/

def productRules : PTerm → List ProductRule
  | .var _ => []
  | .sort _ => []
  | .pi rule domain body => rule :: productRules domain ++ productRules body
  | .lam _ domain body => productRules domain ++ productRules body
  | .app function argument => productRules function ++ productRules argument

theorem productRule_mem_of_typed_subject
    {profile : Profile} {conversion : PTerm → PTerm → Prop}
    {context : SortedCtx} {judgment : Judgment}
    (derivation : TypedUnder profile conversion context judgment) :
    ∀ rule, rule ∈ productRules judgment.subject → rule ∈ profile.products := by
  induction derivation with
  | sort axiomHolds => simp [Judgment.subject, productRules]
  | @pi context domain body domainSort codomainSort resultSort
      domainTyped bodyTyped member ihDomain ihBody =>
      intro rule occurs
      simp only [Judgment.subject, productRules, List.mem_cons,
        List.mem_append] at occurs
      rcases occurs with (rfl | inDomain) | inBody
      · exact member
      · exact ihDomain rule inDomain
      · exact ihBody rule inBody
  | ofTerm subject axiomHolds ih => exact ih
  | toTerm subject axiomHolds ih => exact ih
  | var found => simp [Judgment.subject, productRules]
  | @lam context domain body bodyType domainSort codomainSort resultSort
      domainTyped bodyTypeTyped member bodyTyped ihDomain ihBodyType ihBody =>
      intro rule occurs
      simp only [Judgment.subject, productRules, List.mem_append] at occurs
      exact occurs.elim (ihDomain rule) (ihBody rule)
  | @app context function argument domain bodyType domainSort codomainSort resultSort
      domainTyped bodyTypeTyped member functionTyped argumentTyped
      ihDomain ihBodyType ihFunction ihArgument =>
      intro rule occurs
      simp only [Judgment.subject, productRules, List.mem_append] at occurs
      exact occurs.elim (ihFunction rule) (ihArgument rule)
  | conv _ _ _ ihTerm _ => exact ihTerm

/-! ## The reified formation vertex -/

/-- The three rules used by type-reified indexing: ordinary functions,
polymorphism, and type operators.  Direct value-to-type dependency is absent. -/
def reifiedIndexProducts : List ProductRule :=
  [typeTypeType, kindTypeType, kindKindKind]

/-- `Q : Type → Type`, with the single context entry written innermost first. -/
def reifiedPredicateContext : SortedCtx :=
  [(typeOperatorKind, .kind)]

/-- Inside `X : Type`, the type `Π x : X. Q X`. -/
def reifiedBody : PTerm :=
  .pi typeTypeType (.var 0) (.app (.var 2) (.var 1))

/-- The type-reified universal `Π X : Type. Π x : X. Q X`. -/
def reifiedForall : PTerm :=
  .pi kindTypeType (.sort .type) reifiedBody

/-- The type-operator context is well formed exactly when its displayed rule
is available. -/
theorem reifiedPredicateContext_formed
    (products : List ProductRule) (steps : PTerm → PTerm → Prop)
    (operators : kindKindKind ∈ products) :
    ContextFormedUnder (vertex products) (bubbleConv steps)
      reifiedPredicateContext :=
  .cons .nil (typeOperatorKind_formed products steps operators)

/-- The inner reified body is formed from ordinary functions and type
operators.  Its result depends on the type code `X`, not on the inhabitant
`x : X`. -/
theorem reifiedBody_formed
    (products : List ProductRule) (steps : PTerm → PTerm → Prop)
    (simple : typeTypeType ∈ products)
    (operators : kindKindKind ∈ products) :
    Kernel products steps
      ((.sort .type, .kind) :: reifiedPredicateContext)
      (.type reifiedBody .type) := by
  let outerContext : SortedCtx :=
    [(.sort .type, .kind), (typeOperatorKind, .kind)]
  let innerContext : SortedCtx :=
    [(.var 0, .type), (.sort .type, .kind), (typeOperatorKind, .kind)]
  have codeType : Kernel products steps outerContext (.type (.var 0) .type) :=
    .ofTerm (.var rfl) rfl
  have operatorDomain : Kernel products steps innerContext
      (.type (.sort .type) .kind) :=
    .sort rfl
  have operatorBody : Kernel products steps
      ((.sort .type, .kind) :: innerContext)
      (.type (.sort .type) .kind) :=
    .sort rfl
  have operator : Kernel products steps innerContext
      (.term (.var 2) typeOperatorKind .kind) :=
    .var rfl
  have codeArgument : Kernel products steps innerContext
      (.term (.var 1) (.sort .type) .kind) :=
    .var rfl
  have applied : Kernel products steps innerContext
      (.term (.app (.var 2) (.var 1)) (.sort .type) .kind) :=
    .app operatorDomain operatorBody operators operator codeArgument
  exact .pi codeType (.ofTerm applied rfl) simple

/-- Polymorphism closes the inner body over its type code. -/
theorem reifiedForall_formed
    (products : List ProductRule) (steps : PTerm → PTerm → Prop)
    (simple : typeTypeType ∈ products)
    (polymorphic : kindTypeType ∈ products)
    (operators : kindKindKind ∈ products) :
    Kernel products steps reifiedPredicateContext (.type reifiedForall .type) :=
  .pi (.sort rfl) (reifiedBody_formed products steps simple operators) polymorphic

/-- The complete reified interface includes formation of its `Q` context and
of the displayed universal. -/
def ReifiedTypeIndexedForall
    (products : List ProductRule) (steps : PTerm → PTerm → Prop) : Prop :=
  ContextFormedUnder (vertex products) (bubbleConv steps)
      reifiedPredicateContext ∧
    Kernel products steps reifiedPredicateContext (.type reifiedForall .type)

/-- Exact rule boundary for the reified interface.  Conversion cannot supply
any missing formation rule. -/
theorem reifiedTypeIndexedForall_iff
    (products : List ProductRule) (steps : PTerm → PTerm → Prop) :
    ReifiedTypeIndexedForall products steps ↔
      reifiedIndexProducts ⊆ products := by
  constructor
  · rintro ⟨contextFormed, forallFormed⟩ rule required
    simp only [reifiedIndexProducts, List.mem_cons, List.not_mem_nil,
      or_false] at required
    rcases required with rfl | rfl | rfl
    · exact productRule_mem_of_typed_subject forallFormed typeTypeType (by decide)
    · exact forallFormed.pi_rule_mem rfl
    · cases contextFormed with
      | cons prior operatorKind => exact operatorKind.pi_rule_mem rfl
  · intro contains
    have simple := contains (by decide : typeTypeType ∈ reifiedIndexProducts)
    have polymorphic := contains (by decide : kindTypeType ∈ reifiedIndexProducts)
    have operators := contains (by decide : kindKindKind ∈ reifiedIndexProducts)
    exact ⟨reifiedPredicateContext_formed products steps operators,
      reifiedForall_formed products steps simple polymorphic operators⟩

theorem reifiedTypeIndexedForall_bubble_iff
    (products : List ProductRule) (first second : PTerm → PTerm → Prop) :
    ReifiedTypeIndexedForall products first ↔
      ReifiedTypeIndexedForall products second := by
  rw [reifiedTypeIndexedForall_iff, reifiedTypeIndexedForall_iff]

/-- The direct and reified routes occupy incomparable three-rule/two-rule
vertices.  Each supplies its own interface and refuses the other one. -/
theorem direct_reified_formation_fork :
    DirectValueIndexedForall dependentProducts noSteps ∧
      ¬ ReifiedTypeIndexedForall dependentProducts noSteps ∧
      ReifiedTypeIndexedForall reifiedIndexProducts noSteps ∧
      ¬ DirectValueIndexedForall reifiedIndexProducts noSteps := by
  constructor
  · exact directValueIndexedForall_at_dependent
  constructor
  · rw [reifiedTypeIndexedForall_iff]
    decide
  constructor
  · rw [reifiedTypeIndexedForall_iff]
  · rw [directValueIndexedForall_iff_contains_dependentProducts]
    decide

/-! ## Concrete syntax and checker-cost controls -/

def termNodeCount : PTerm → Nat
  | .var _ => 1
  | .sort _ => 1
  | .pi _ domain body => 1 + termNodeCount domain + termNodeCount body
  | .lam _ domain body => 1 + termNodeCount domain + termNodeCount body
  | .app function argument => 1 + termNodeCount function + termNodeCount argument

def contextNodeCount (context : SortedCtx) : Nat :=
  (context.map fun entry => termNodeCount entry.1).sum

def interfaceNodeCount (context : SortedCtx) (type : PTerm) : Nat :=
  contextNodeCount context + termNodeCount type

theorem direct_interface_nodes :
    interfaceNodeCount directPredicateContext directForall = 9 := by decide

theorem reified_interface_nodes :
    interfaceNodeCount reifiedPredicateContext reifiedForall = 10 := by decide

theorem reified_interface_has_one_more_node :
    interfaceNodeCount reifiedPredicateContext reifiedForall =
      interfaceNodeCount directPredicateContext directForall + 1 := by decide

/-- Count free occurrences of one variable in the surrounding context. -/
def freeVarCount (target : Nat) : PTerm → Nat
  | .var index => if index = target then 1 else 0
  | .sort _ => 0
  | .pi _ domain body => freeVarCount target domain + freeVarCount (target + 1) body
  | .lam _ domain body => freeVarCount target domain + freeVarCount (target + 1) body
  | .app function argument => freeVarCount target function + freeVarCount target argument

/-- Direct elaboration applies the proof function to the runtime index. -/
def elaborateDirectApplication (function value : PTerm) : PTerm :=
  .app function value

/-- Reified elaboration applies the proof function first to a type code and
then to an inhabitant witnessing that code. -/
def elaborateReifiedApplication
    (function codeType codedValue : PTerm) : PTerm :=
  .app (.app function codeType) codedValue

theorem direct_application_node_formula (function value : PTerm) :
    termNodeCount (elaborateDirectApplication function value) =
      1 + termNodeCount function + termNodeCount value :=
  rfl

theorem reified_application_node_formula (function codeType codedValue : PTerm) :
    termNodeCount (elaborateReifiedApplication function codeType codedValue) =
      2 + termNodeCount function + termNodeCount codeType +
        termNodeCount codedValue := by
  simp only [elaborateReifiedApplication, termNodeCount]
  omega

/-- One direct function and its actual value argument, added to the direct
predicate context. -/
def directApplicationContext : SortedCtx :=
  [(PTerm.lift 1 0 directForall, .type),
    (.var 1, .type)] ++ directPredicateContext

def directApplication : PTerm := elaborateDirectApplication (.var 0) (.var 1)
def directApplicationType : PTerm := .app (.var 2) (.var 1)

/-- One reified function, a witness of a supplied type code, that type code,
and the type operator `Q`. -/
def reifiedApplicationContext : SortedCtx :=
  [(PTerm.lift 2 0 reifiedForall, .type),
    (.var 0, .type),
    (.sort .type, .kind),
    (typeOperatorKind, .kind)]

def reifiedApplication : PTerm :=
  elaborateReifiedApplication (.var 0) (.var 2) (.var 1)

def reifiedApplicationType : PTerm :=
  .app (.var 3) (.var 2)

theorem directApplicationContext_formed :
    ContextFormedUnder (vertex dependentProducts) PTerm.Conv
      directApplicationContext := by
  have base : ContextFormedUnder (vertex dependentProducts) PTerm.Conv
      directPredicateContext := by
    rw [← bubbleConv_betaRoot]
    exact directPredicateContext_formed dependentProducts betaRoot (by decide)
  have withValue : ContextFormedUnder (vertex dependentProducts) PTerm.Conv
      ((.var 1, .type) :: directPredicateContext) :=
    .cons base (.ofTerm (.var rfl) rfl)
  have functionTypeFound :
      Checker.inferSort (vertex dependentProducts) 0 5
        ((.var 1, .type) :: directPredicateContext)
        (PTerm.lift 1 0 directForall) = some .type := by
    decide +kernel
  exact .cons withValue
    (derives_iff_typedUnder.mp (Checker.inferSort_sound functionTypeFound))

theorem reifiedApplicationContext_formed :
    ContextFormedUnder (vertex reifiedIndexProducts) PTerm.Conv
      reifiedApplicationContext := by
  have base : ContextFormedUnder (vertex reifiedIndexProducts) PTerm.Conv
      reifiedPredicateContext := by
    rw [← bubbleConv_betaRoot]
    exact reifiedPredicateContext_formed reifiedIndexProducts betaRoot (by decide)
  have withCode : ContextFormedUnder (vertex reifiedIndexProducts) PTerm.Conv
      ((.sort .type, .kind) :: reifiedPredicateContext) :=
    .cons base (.sort rfl)
  have withWitness : ContextFormedUnder (vertex reifiedIndexProducts) PTerm.Conv
      ((.var 0, .type) :: (.sort .type, .kind) :: reifiedPredicateContext) :=
    .cons withCode (.ofTerm (.var rfl) rfl)
  have functionTypeFound :
      Checker.inferSort (vertex reifiedIndexProducts) 0 5
        ((.var 0, .type) :: (.sort .type, .kind) :: reifiedPredicateContext)
        (PTerm.lift 2 0 reifiedForall) = some .type := by
    decide +kernel
  exact .cons withWitness
    (derives_iff_typedUnder.mp (Checker.inferSort_sound functionTypeFound))

namespace Controls

/-- Formation of the reified syntax does not discharge the independently
required Tarski decoding coherence.  The maintained varying-decoding control
has a reified code carrier but no full code-and-decoding factorization. -/
theorem formation_with_missing_decoding_coherence :
    ReifiedTypeIndexedForall reifiedIndexProducts noSteps ∧
      Nonempty
        (_root_.Mettapedia.TypeTheory.DependentFamilyObserverFactorization.FamilyFactorization
          _root_.Mettapedia.TypeTheory.TarskiCodeFamilyObserverFactorization.Canary.coarseLevel
          _root_.Mettapedia.TypeTheory.TarskiCodeFamilyObserverFactorization.Canary.varyingDecoding.Code) ∧
      ¬ Nonempty
        (_root_.Mettapedia.TypeTheory.TarskiCodeFamilyObserverFactorization.CodeDecodingFactorization
          _root_.Mettapedia.TypeTheory.TarskiCodeFamilyObserverFactorization.Canary.varyingDecoding
          _root_.Mettapedia.TypeTheory.TarskiCodeFamilyObserverFactorization.Canary.coarseLevel) := by
  refine ⟨(reifiedTypeIndexedForall_iff _ _).2 (fun _ member => member), ?_⟩
  exact _root_.Mettapedia.TypeTheory.TarskiCodeFamilyObserverFactorization.Canary.code_syntax_does_not_determine_decoding_factorization

theorem directFormation_refuses_fuel_four :
    Checker.inferSort (vertex dependentProducts) 0 4
      directPredicateContext directForall = none := by decide +kernel

theorem directFormation_accepts_fuel_five :
    Checker.inferSort (vertex dependentProducts) 0 5
      directPredicateContext directForall = some .type := by decide +kernel

theorem reifiedFormation_refuses_fuel_four :
    Checker.inferSort (vertex reifiedIndexProducts) 0 4
      reifiedPredicateContext reifiedForall = none := by decide +kernel

theorem reifiedFormation_accepts_fuel_five :
    Checker.inferSort (vertex reifiedIndexProducts) 0 5
      reifiedPredicateContext reifiedForall = some .type := by decide +kernel

theorem directApplication_refuses_fuel_four :
    Checker.inferTerm (vertex dependentProducts) 0 4
      directApplicationContext directApplication = none := by decide +kernel

theorem directApplication_accepts_fuel_five :
    Checker.inferTerm (vertex dependentProducts) 0 5
      directApplicationContext directApplication =
        some (directApplicationType, .type) := by decide +kernel

theorem reifiedApplication_refuses_fuel_five :
    Checker.inferTerm (vertex reifiedIndexProducts) 0 5
      reifiedApplicationContext reifiedApplication = none := by decide +kernel

theorem reifiedApplication_accepts_fuel_six :
    Checker.inferTerm (vertex reifiedIndexProducts) 0 6
      reifiedApplicationContext reifiedApplication =
        some (reifiedApplicationType, .type) := by decide +kernel

theorem directApplication_typed :
    Derives (vertex dependentProducts) directApplicationContext
      (.term directApplication directApplicationType .type) :=
  Checker.inferTerm_sound directApplication_accepts_fuel_five

theorem reifiedApplication_typed :
    Derives (vertex reifiedIndexProducts) reifiedApplicationContext
      (.term reifiedApplication reifiedApplicationType .type) :=
  Checker.inferTerm_sound reifiedApplication_accepts_fuel_six

theorem applications_have_formed_contexts :
    ContextFormedUnder (vertex dependentProducts) PTerm.Conv
        directApplicationContext ∧
      ContextFormedUnder (vertex reifiedIndexProducts) PTerm.Conv
        reifiedApplicationContext :=
  ⟨directApplicationContext_formed, reifiedApplicationContext_formed⟩

theorem application_node_counts :
    termNodeCount directApplication = 3 ∧
      termNodeCount reifiedApplication = 5 := by decide

/-- Direct result types retain the runtime argument occurrence. Reified result
types retain the type-code occurrence and omit the witness occurrence; relating
that code back to the represented value is the separate coherence boundary. -/
theorem result_transport_surface :
    freeVarCount 1 directApplicationType = 1 ∧
      freeVarCount 1 reifiedApplicationType = 0 ∧
      freeVarCount 2 reifiedApplicationType = 1 := by decide

def verdicts : List (String × Bool) :=
  [("direct formation accepts at fuel five",
      (Checker.inferSort (vertex dependentProducts) 0 5
        directPredicateContext directForall).isSome),
   ("reified formation accepts at fuel five",
      (Checker.inferSort (vertex reifiedIndexProducts) 0 5
        reifiedPredicateContext reifiedForall).isSome),
   ("direct application accepts at fuel five",
      (Checker.inferTerm (vertex dependentProducts) 0 5
        directApplicationContext directApplication).isSome),
   ("reified application refuses at fuel five",
      (Checker.inferTerm (vertex reifiedIndexProducts) 0 5
        reifiedApplicationContext reifiedApplication).isNone),
   ("reified application accepts at fuel six",
      (Checker.inferTerm (vertex reifiedIndexProducts) 0 6
        reifiedApplicationContext reifiedApplication).isSome)]

theorem all_verdicts : verdicts.all Prod.snd = true := by decide +kernel

end Controls

#print axioms productRule_mem_of_typed_subject
#print axioms reifiedBody_formed
#print axioms reifiedForall_formed
#print axioms reifiedTypeIndexedForall_iff
#print axioms direct_reified_formation_fork
#print axioms direct_interface_nodes
#print axioms reified_interface_nodes
#print axioms Controls.directApplication_typed
#print axioms Controls.reifiedApplication_typed
#print axioms Controls.result_transport_surface
#print axioms Controls.formation_with_missing_decoding_coherence
#print axioms directApplicationContext_formed
#print axioms reifiedApplicationContext_formed

end Mettapedia.TypeTheory.ReifiedIndexElaboration

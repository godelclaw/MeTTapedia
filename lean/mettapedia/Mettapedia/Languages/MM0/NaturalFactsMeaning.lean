import Mettapedia.Languages.MM0.NaturalRecursion
import Mettapedia.Languages.HOLLight.NaturalFacts
import Mettapedia.Languages.Megalodon.NaturalRecursion
import Mettapedia.Logic.HOL.ConstantSubstitutionSemantics

/-!
# The standard interpretation of the native natural-law interface

These are the universally closed readings of the native rules, retaining the
induction premises, the direction of constructor separation, Boolean equality
in injectivity, and the non-surjectivity presentation of infinity. They are
compared with the shared natural formulas in the stated standard model.
The graph's intrinsic syntax independently prints the exact native definition
and denotes the existing inductive graph with its method arguments transposed.
None of these comparisons establishes a soundness theorem for linked native C.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.NaturalFactsMeaning

open Mettapedia.Logic.HOL
open NaturalRecursion (Source number target method)
open Mettapedia.Languages.HOLLight.NaturalFacts (Fact)

open Mettapedia.Languages.Megalodon.NaturalRecursion (Graph)
abbrev graphContext : Ctx Mettapedia.Logic.HOL.NaturalFacts.Base :=
  [target, number, method, target]

/-- The four free arguments are value, number, method and start, in de Bruijn
order. The relation and its two step arguments are genuine typed binders. -/
def graphDefinition : Formula Source graphContext := by
  refine .all (σ := number ⇒ target ⇒ .prop) ?_
  refine .imp
    (.app (.app (.var .vz) (.const .zero))
      (.var (.vs (.vs (.vs (.vs .vz)))))) ?_
  refine .imp ?_
    (.app (.app (.var .vz) (.var (.vs (.vs .vz)))) (.var (.vs .vz)))
  refine .all (σ := number) (.all (σ := target) ?_)
  exact .imp
    (.app (.app (.var (.vs (.vs .vz))) (.var (.vs .vz))) (.var .vz))
    (.app (.app (.var (.vs (.vs .vz)))
        (.app (.const .successor) (.var (.vs .vz))))
      (.app (.app (.var (.vs (.vs (.vs (.vs (.vs .vz)))))) (.var .vz))
        (.var (.vs .vz))))

def graphNames : Names graphContext
  | _, .vz => "v"
  | _, .vs .vz => "n"
  | _, .vs (.vs .vz) => "f"
  | _, .vs (.vs (.vs .vz)) => "a"

def graphBinders : Nat → String
  | 0 => "r"
  | 1 => "k"
  | 2 => "w"
  | index + 3 => "bound" ++ toString (index + 3)

/-- Two independently constructed representations agree, including the free
argument indices and the result-before-predecessor method application. -/
theorem graph_definition_prints :
    HOLSyntaxWire.encodeTerm NaturalRecursion.encodeBase NaturalRecursion.encodeConst
      graphBinders graphNames 0 graphDefinition = NaturalRecursion.graphBody := by
  rfl


/-- The impredicative graph syntax denotes the existing finite inductive graph
in this standard interpretation. The relation is instantiated by that graph
in the forward direction, and graph induction proves the reverse direction. -/
theorem graph_meaning {numbers : Type 1} (origin : numbers) (next : numbers → numbers)
    (result : Type 1)
    (valuation : (Mettapedia.Logic.HOL.NaturalFacts.model origin next result).Valuation graphContext) :
    ((Mettapedia.Logic.HOL.NaturalFacts.model origin next result).denote
      graphDefinition valuation).down ↔
      Graph origin next (valuation (.vs (.vs (.vs .vz))))
        (fun n previous => valuation (.vs (.vs .vz)) previous n)
        (valuation (.vs .vz)) (valuation .vz) := by
  constructor
  · intro valid
    exact valid (fun n value => ULift.up
      (Graph origin next (valuation (.vs (.vs (.vs .vz))))
        (fun n previous => valuation (.vs (.vs .vz)) previous n) n value))
      trivial .zero (fun _ _ _ _ prior => .successor prior)
  · intro graph relation _ atZero atSuccessor
    exact graph.fold atZero (fun n value prior => atSuccessor n trivial value trivial prior)

/-- Expand the source presentation's `one_one` at its natural carrier. -/
def injectionBody {context : Ctx Mettapedia.Logic.HOL.NaturalFacts.Base} :
    Term Source context ((number ⇒ number) ⇒ .prop) :=
  .lam (.all (σ := number) (.all (σ := number)
    (.imp (.eq (.app (.var (.vs (.vs .vz))) (.var (.vs .vz)))
        (.app (.var (.vs (.vs .vz))) (.var .vz)))
      (.eq (.var (.vs .vz)) (.var .vz)))))

/-- The source `onto` uses target-before-image equality. -/
def ontoBody {context : Ctx Mettapedia.Logic.HOL.NaturalFacts.Base} :
    Term Source context ((number ⇒ number) ⇒ .prop) :=
  .lam (.all (σ := number) (.ex (σ := number)
    (.eq (.var (.vs .vz)) (.app (.var (.vs (.vs .vz))) (.var .vz)))))

def formula : Fact → ClosedFormula Source
  | .recursion => NaturalRecursion.formula
  | .induction => .all (σ := number ⇒ .prop)
      (.imp (.app (.var .vz) (.const .zero))
        (.imp (.all (σ := number)
          (.imp (.app (.var (.vs .vz)) (.var .vz))
            (.app (.var (.vs .vz)) (.app (.const .successor) (.var .vz)))))
          (.all (σ := number) (.app (.var (.vs .vz)) (.var .vz)))))
  | .zeroNotSuccessor => .all (σ := number)
      (.not (.eq (.const .zero) (.app (.const .successor) (.var .vz))))
  | .successorInjective => .all (σ := number) (.all (σ := number)
      (.eq (.eq (.app (.const .successor) (.var (.vs .vz)))
          (.app (.const .successor) (.var .vz)))
        (.eq (.var (.vs .vz)) (.var .vz))))
  | .infinity => .ex (σ := number ⇒ number)
      (.and (.app injectionBody (.var .vz)) (.not (.app ontoBody (.var .vz))))

/-- The native induction rule's free terms are intrinsically typed. Its two
logical premises remain separate, rather than being erased by closure. -/
abbrev inductionContext : Ctx Mettapedia.Logic.HOL.NaturalFacts.Base :=
  [number, number ⇒ .prop]

def inductionNames : Names inductionContext
  | _, .vz => "n"
  | _, .vs .vz => "p"

def inductionInitial : Formula Source inductionContext :=
  .app (.var (.vs .vz)) (.const .zero)

def inductionStep : Formula Source inductionContext :=
  .all (σ := number)
    (.imp (.app (.var (.vs (.vs .vz))) (.var .vz))
      (.app (.var (.vs (.vs .vz))) (.app (.const .successor) (.var .vz))))

def inductionConclusion : Formula Source inductionContext :=
  .app (.var (.vs .vz)) (.var .vz)

/-- Print the sequent with its object-typing guards and logical premises. -/
def printedInductionStatement : String :=
    NaturalClosure.statement "holNaturalInduction"
      "((var G wff ()) (var n term ()) (var p term ()) (bound k term))"
      [NaturalClosure.typed (NaturalClosure.symbol "n") NaturalType.numbers,
       NaturalClosure.typed (NaturalClosure.symbol "p")
         (NaturalClosure.arrow NaturalType.numbers (NaturalClosure.node "bool" [])),
       NaturalClosure.asserts (HOLSyntaxWire.encodeTerm NaturalRecursion.encodeBase
         NaturalRecursion.encodeConst (fun _ => "k") inductionNames 0 inductionInitial),
       NaturalClosure.asserts (HOLSyntaxWire.encodeTerm NaturalRecursion.encodeBase
         NaturalRecursion.encodeConst (fun _ => "k") inductionNames 0 inductionStep)]
      (NaturalClosure.asserts (HOLSyntaxWire.encodeTerm NaturalRecursion.encodeBase
        NaturalRecursion.encodeConst (fun _ => "k") inductionNames 0 inductionConclusion))

theorem induction_statement_prints : printedInductionStatement =
      NaturalType.inductionStatement := by rfl

def separationBody : Formula Source [number] :=
  .not (.eq (.const .zero) (.app (.const .successor) (.var .vz)))

theorem separation_prints :
    HOLSyntaxWire.encodeTerm NaturalRecursion.encodeBase NaturalRecursion.encodeConst
      (fun _ => "unused") (fun _ => "n") 0 separationBody = NaturalType.noConfusion := by rfl

def injectivityBody : Formula Source [number, number] :=
  .eq (.eq (.app (.const .successor) (.var (.vs .vz)))
      (.app (.const .successor) (.var .vz)))
    (.eq (.var (.vs .vz)) (.var .vz))

def pairNames : Names ([number, number] : Ctx Mettapedia.Logic.HOL.NaturalFacts.Base)
  | _, .vz => "n"
  | _, .vs .vz => "m"

/-- `bi` is the native Boolean-equality abbreviation, not an extra logical
axiom. Both native arguments agree with the independently typed formula. -/
theorem injectivity_prints :
    ∃ left right : HOLSyntaxWire.Wire,
      NaturalType.injectivity = NaturalClosure.node "bi" [left, right] ∧
      HOLSyntaxWire.encodeTerm NaturalRecursion.encodeBase NaturalRecursion.encodeConst
        (fun _ => "unused") pairNames 0 injectivityBody =
        NaturalClosure.node "eqc" [NaturalClosure.node "bool" [], left, right] := by
  exact ⟨_, _, rfl, rfl⟩

/-- Only the two closed definitions used by native infinity are added to
the source signature. Their interpretations are compound terms, not assumed
truth values or additional infinity axioms. -/
inductive Alias : Ty Mettapedia.Logic.HOL.NaturalFacts.Base → Type
  | oneOne : Alias ((number ⇒ number) ⇒ .prop)
  | onto : Alias ((number ⇒ number) ⇒ .prop)

abbrev NativeConst (type : Ty Mettapedia.Logic.HOL.NaturalFacts.Base) :=
  Source type ⊕ Alias type

def definitions {type} : NativeConst type → ClosedTerm Source type
  | .inl constant => .const constant
  | .inr .oneOne => injectionBody
  | .inr .onto => ontoBody

def encodeNativeConst {type} : NativeConst type → HOLSyntaxWire.Wire
  | .inl constant => NaturalRecursion.encodeConst constant
  | .inr .oneOne => NaturalClosure.node "one_one" [NaturalType.numbers, NaturalType.numbers]
  | .inr .onto => NaturalClosure.node "onto" [NaturalType.numbers, NaturalType.numbers]

def nativeInfinity : ClosedFormula NativeConst :=
  .ex (σ := number ⇒ number)
    (.and (.app (.const (.inr .oneOne)) (.var .vz))
      (.not (.app (.const (.inr .onto)) (.var .vz))))

theorem infinity_prints :
    HOLSyntaxWire.encodeTerm NaturalRecursion.encodeBase encodeNativeConst
      (fun _ => "f") NaturalRecursion.closedNames 0 nativeInfinity = NaturalType.infinity := by rfl

/-- Closed definition substitution really produces the expanded intrinsic
formula, including weakening the definitions beneath the existential binder. -/
theorem infinity_expands : substConst definitions nativeInfinity = formula .infinity := by rfl

/-- The named native infinity and its expansion have the same meaning in
the genuine definition reduct of any Henkin model. Carriers, admissibility,
contexts and substitution use the existing reduct construction. -/
theorem infinity_definitions_meaning (model : HenkinModel Mettapedia.Logic.HOL.NaturalFacts.Base Source) :
    (model.constantSubstitutionReduct definitions).models nativeInfinity ↔
      model.models (formula .infinity) := by
  rw [← HenkinModel.models_substConst, infinity_expands]

theorem induction_meaning {numbers : Type 1} (origin : numbers) (next : numbers → numbers)
    (result : Type 1) :
    (Mettapedia.Logic.HOL.NaturalFacts.model origin next result).models (formula .induction) ↔
      ∀ predicate : numbers → Prop, predicate origin →
        (∀ n, predicate n → predicate (next n)) → ∀ n, predicate n := by
  constructor
  · intro valid predicate atZero atNext n
    exact valid (fun n => ULift.up (predicate n)) trivial atZero
      (fun n _ => atNext n) n trivial
  · intro inductionPrinciple predicate _ atZero atNext n _
    exact inductionPrinciple (fun n => (predicate n).down) atZero
      (fun n => atNext n trivial) n

/-- Closing the induction statement has not lost its open-rule meaning.
Admissibility of the free native arguments is represented by their intrinsic
types; both logical hypotheses are still needed at the selected valuation. -/
theorem induction_rule {numbers : Type 1} (origin : numbers) (next : numbers → numbers)
    (result : Type 1)
    (valid : (Mettapedia.Logic.HOL.NaturalFacts.model origin next result).models (formula .induction))
    (valuation : (Mettapedia.Logic.HOL.NaturalFacts.model origin next result).Valuation inductionContext)
    (initial : ((Mettapedia.Logic.HOL.NaturalFacts.model origin next result).denote
      inductionInitial valuation).down)
    (step : ((Mettapedia.Logic.HOL.NaturalFacts.model origin next result).denote
      inductionStep valuation).down) :
    ((Mettapedia.Logic.HOL.NaturalFacts.model origin next result).denote
      inductionConclusion valuation).down :=
  valid (valuation (.vs .vz)) trivial initial step (valuation .vz) trivial

theorem no_confusion_meaning {numbers : Type 1} (origin : numbers) (next : numbers → numbers)
    (result : Type 1) :
    (Mettapedia.Logic.HOL.NaturalFacts.model origin next result).models (formula .zeroNotSuccessor) ↔
      ∀ n, next n ≠ origin := by
  constructor
  · intro valid n same
    exact valid n trivial same.symm
  · intro different n _ same
    exact different n same.symm

theorem infinity_meaning {numbers : Type 1} (origin : numbers) (next : numbers → numbers)
    (result : Type 1) :
    (Mettapedia.Logic.HOL.NaturalFacts.model origin next result).models (formula .infinity) ↔
      ∃ function : numbers → numbers, Function.Injective function ∧
        ∃ missing, ∀ n, function n ≠ missing := by
  classical
  constructor
  · rintro ⟨function, _, injective, notOnto⟩
    refine ⟨function, (fun m n same => injective m trivial n trivial same), ?_⟩
    obtain ⟨missing, omitted⟩ := not_forall.mp notOnto
    refine ⟨missing, ?_⟩
    intro n same
    exact omitted (fun _ => ⟨n, trivial, same.symm⟩)
  · rintro ⟨function, injective, missing, omitted⟩
    refine ⟨function, trivial, (fun m _ n _ same => injective same), ?_⟩
    intro onto
    obtain ⟨n, _, same⟩ := onto missing trivial
    exact omitted n same.symm

/-- The native presentations agree on the five statements in the declared
standard interpretation. This does not identify their proof objects or costs. -/
theorem shared_fact_meaning {numbers : Type 1} (origin : numbers) (next : numbers → numbers)
    (result : Type 1) (fact : Fact) :
    (Mettapedia.Logic.HOL.NaturalFacts.model origin next result).models (formula fact) ↔
      (Mettapedia.Logic.HOL.NaturalFacts.model origin next result).models
        (Mettapedia.Languages.HOLLight.NaturalFacts.formula fact) := by
  cases fact with
  | recursion => exact NaturalRecursion.shared_fact_meaning origin next result
  | induction =>
    exact (induction_meaning origin next result).trans
      (Mettapedia.Logic.HOL.NaturalFacts.induction_meaning origin next result).symm
  | zeroNotSuccessor =>
    exact (no_confusion_meaning origin next result).trans
      (Mettapedia.Logic.HOL.NaturalFacts.noConfusion_meaning origin next result).symm
  | successorInjective => rfl
  | infinity =>
    exact (infinity_meaning origin next result).trans
      (Mettapedia.Logic.HOL.NaturalFacts.infinity_meaning origin next result).symm

def verdicts : List (String × Bool) := [
  ("MM0 typed graph prints the native body",
    (HOLSyntaxWire.encodeTerm NaturalRecursion.encodeBase NaturalRecursion.encodeConst
      graphBinders graphNames 0 graphDefinition).render == NaturalRecursion.graphBody.render),
  ("MM0 exchanged graph arguments refuse",
    (HOLSyntaxWire.encodeTerm NaturalRecursion.encodeBase NaturalRecursion.encodeConst
      graphBinders (fun index => if graphNames index == "v" then "n" else graphNames index)
        0 graphDefinition).render != NaturalRecursion.graphBody.render),
  ("MM0 typed induction preserves its guarded sequent", printedInductionStatement == NaturalType.inductionStatement),
  ("MM0 induction differs from the unguarded rule",
    printedInductionStatement != NaturalClosure.statement "holNaturalInduction"
      "((var G wff ()) (var n term ()) (var p term ()) (bound k term))" []
      (NaturalClosure.asserts (NaturalClosure.application (NaturalClosure.symbol "p")
        (NaturalClosure.symbol "n")))),
  ("MM0 typed infinity prints the named aliases",
    (HOLSyntaxWire.encodeTerm NaturalRecursion.encodeBase encodeNativeConst
      (fun _ => "f") NaturalRecursion.closedNames 0 nativeInfinity).render == NaturalType.infinity.render),
  ("MM0 named infinity differs from its expanded wire body",
    (HOLSyntaxWire.encodeTerm NaturalRecursion.encodeBase NaturalRecursion.encodeConst
      (fun _ => "f") NaturalRecursion.closedNames 0 (formula .infinity)).render != NaturalType.infinity.render)]

theorem all_verdicts : verdicts.all Prod.snd = true := by decide +kernel

end Mettapedia.Languages.MM0.NaturalFactsMeaning

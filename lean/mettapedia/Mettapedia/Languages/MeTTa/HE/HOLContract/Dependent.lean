import Mettapedia.Languages.MeTTa.HE.HOLContract.Signature
import Mettapedia.Languages.MeTTa.HE.TypeGrounding.SpecBoundary

/-!
# Dependent HE judgments are not contract judgments

A telescope `(-> (: $x A) B)` names its argument, so a dependent judgment mentions terms in
its type.  With `(: remember (-> (: $p Fact) (WitnessOf $p)))`, the term `(remember fact)` has
type `(WitnessOf fact)` and `(remember other)` has type `(WitnessOf other)`.  `DependentTyped`
is that reading: λΠ's application rule for declared constants applied to closed arguments,
without conversion.  The type of an application substitutes the arguments for the telescope's
variables, and each argument must have its binder's type under the same substitution.

**Contracts are declaration-invariant.**  Exchanging two symbols with the same declaration in a
term preserves contract typing (`typed_swap_iff`): the contract reads a term only through the
declared types of its constants, and its types never mention terms.  The same holds for every
compositional contract whose leaves are typed by their declarations, whatever its types are
(`CompositionalContract.swap_iff`).  Such relations are `DeclarationInvariant`.

**Dependent typing is not.**  In the signature of HE's dependent-binder conformance programme
(`bindersSpace`), `fact` and `other` are both declared `Fact`, yet `(remember fact)` and
`(remember other)` have different types, and `(useWitness other otherWitness)` is typed while
`(useWitness fact otherWitness)` is not.  So no declaration-invariant relation agrees with
dependent typing there (`no_declarationInvariant_agrees`): neither the contract
(`typed_disagrees_dependent`) nor any compositional contract with declared leaves, under any
reading of HE's types (`CompositionalContract.disagrees_dependent`).  Every relation that
types `(useWitness other otherWitness)` and is declaration-invariant also types
`(useWitness fact otherWitness)`, which the dependent reading refutes
(`declarationInvariant_types_refuted_golden`).

A contract that agrees has to type some symbol by its name rather than by its declaration, as
symbol punning does: that is the cost of leaving invariance.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.HOLContract

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.TypeGrounding
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.NamedElaboration
open Spec.Type
open Spec.Type.RuntimeRefinement

/-! ## Exchanging two symbols -/

/-- Exchange the names `left` and `right`. -/
def swapString (left right name : String) : String :=
  if name = left then right else if name = right then left else name

theorem swapString_swapString (left right name : String) :
    swapString left right (swapString left right name) = name := by
  unfold swapString
  split_ifs <;> simp_all

/-- Exchange the symbols `left` and `right` throughout an atom. -/
def swapAtom (left right : String) : Atom → Atom
  | .symbol name => .symbol (swapString left right name)
  | .var name => .var name
  | .grounded value => .grounded value
  | .expression atoms => .expression (atoms.map (swapAtom left right))

theorem swapAtom_swapAtom (left right : String) (atom : Atom) :
    swapAtom left right (swapAtom left right atom) = atom := by
  induction atom using Atom.rec (motive_2 := fun atoms =>
      atoms.map (fun atom => swapAtom left right (swapAtom left right atom)) = atoms) with
  | symbol name => simp [swapAtom, swapString_swapString]
  | var name => simp [swapAtom]
  | grounded value => simp [swapAtom]
  | expression atoms ih =>
      simp only [swapAtom, List.map_map, Function.comp_def]
      rw [ih]
  | nil => rfl
  | cons head tail headIH tailIH =>
      simp only [List.map_cons, headIH, tailIH]

/-- Exchange `left` and `right` in the constant of a declared name; the application and
product constants are unchanged. -/
def swapName (left right : String) : Name → Name
  | .declared constant occurrence instanceType =>
      .declared (swapAtom left right constant) occurrence instanceType
  | .apply parameters result => .apply parameters result
  | .pair components => .pair components
  | .fst components => .fst components
  | .snd components => .snd components
  | .one => .one

theorem tupleTerm_mapConst_swap (left right : String) :
    ∀ (types : List Atom) (terms : List ContractTerm),
      (tupleTerm types terms).mapConst (swapName left right) =
        tupleTerm types (terms.map (NamedTerm.mapConst (swapName left right)))
  | [], _ => rfl
  | _ :: _, [] => rfl
  | component :: components, term :: terms => by
      simp only [tupleTerm, NamedTerm.mapConst, swapName, List.map_cons]
      rw [tupleTerm_mapConst_swap left right components terms]

mutual

/-- Annotation commutes with exchanging two symbols. -/
theorem Annotates.swap (left right : String) :
    {expression : Atom} → {term : ContractTerm} → Annotates expression term →
      Annotates (swapAtom left right expression) (term.mapConst (swapName left right))
  | _, _, .declared atom occurrence instanceType => by
      simp only [NamedTerm.mapConst, swapName]
      exact .declared _ _ _
  | _, _, .application head arguments => by
      rw [NamedTerm.mapConst_foldl]
      simp only [swapAtom, NamedTerm.mapConst, swapName, List.map_cons]
      exact .application (Annotates.swap left right head) (AnnotatesList.swap left right arguments)
  | _, _, .tuple notArrow lengths head arguments => by
      rw [tupleTerm_mapConst_swap, List.map_cons]
      simp only [swapAtom, List.map_cons]
      exact .tuple notArrow (by simpa using lengths) (Annotates.swap left right head)
        (AnnotatesList.swap left right arguments)

theorem AnnotatesList.swap (left right : String) :
    {arguments : List Atom} → {terms : List ContractTerm} → AnnotatesList arguments terms →
      AnnotatesList (arguments.map (swapAtom left right))
        (terms.map (NamedTerm.mapConst (swapName left right)))
  | _, _, .nil => .nil
  | _, _, .cons head tail =>
      .cons (Annotates.swap left right head) (AnnotatesList.swap left right tail)

end

/-- Exchanging `left` and `right` keeps every declaration of the space: every atom has the
declarations of its exchange. -/
def EquallyDeclared (space : Space) (left right : String) : Prop :=
  ∀ atom, declarations space (swapAtom left right atom) = declarations space atom

theorem nameType_swapName {space : Space} {left right : String}
    (same : EquallyDeclared space left right) :
    ∀ name, nameType space (swapName left right name) = nameType space name
  | .declared constant occurrence instanceType => by
      have instanceIff :
          Instance space (swapAtom left right constant) occurrence instanceType ↔
            Instance space constant occurrence instanceType := by
        simp only [Instance, same constant]
      simp only [swapName, nameType]
      by_cases isInstance : Instance space constant occurrence instanceType
      · rw [if_pos (instanceIff.mpr isInstance), if_pos isInstance]
      · rw [if_neg (fun swapped => isInstance (instanceIff.mp swapped)), if_neg isInstance]
  | .apply _ _ => rfl
  | .pair _ => rfl
  | .fst _ => rfl
  | .snd _ => rfl
  | .one => rfl

/-- **The contract cannot tell equally declared symbols apart.** -/
theorem typed_swap_iff {space : Space} {left right : String}
    (same : EquallyDeclared space left right) (expression type : Atom) :
    Typed space (swapAtom left right expression) type ↔ Typed space expression type := by
  have typeOf : nameType space ∘ swapName left right = nameType space :=
    funext (nameType_swapName same)
  have forward : ∀ source, Typed space source type →
      Typed space (swapAtom left right source) type := by
    intro source typed
    obtain ⟨term, annotates, applicativeTyped⟩ := (typed_iff space source type).mp typed
    refine (typed_iff space _ type).mpr
      ⟨term.mapConst (swapName left right), annotates.swap left right, ?_⟩
    rw [applicativeTyped_mapConst_iff _ annotates.applicative, typeOf]
    exact applicativeTyped
  constructor
  · intro typed
    have back := forward _ typed
    rwa [swapAtom_swapAtom] at back
  · exact forward expression

/-! ## Declaration-invariant relations -/

/-- A relation between terms and types is declaration-invariant on a space when exchanging two
equally declared symbols in a term preserves it. -/
def DeclarationInvariant (space : Space) (relation : Atom → Atom → Prop) : Prop :=
  ∀ left right, EquallyDeclared space left right →
    ∀ expression type, relation (swapAtom left right expression) type ↔ relation expression type

theorem typed_declarationInvariant (space : Space) :
    DeclarationInvariant space (Typed space) :=
  fun _ _ same expression type => typed_swap_iff same expression type

/-! ## Compositional contracts -/

/-- A compositional contract with types in `τ`: a leaf is typed by its declaration, and an
expression's types are determined by the types of its parts. -/
structure CompositionalContract (space : Space) (τ : Type) where
  /-- The types of a leaf. -/
  leaf : Atom → τ → Prop
  /-- The types of an expression whose parts have the given types. -/
  combine : List τ → τ → Prop
  /-- The typing of terms. -/
  typed : Atom → τ → Prop
  leaf_declared : ∀ left right, EquallyDeclared space left right →
      ∀ type, leaf (.symbol left) type ↔ leaf (.symbol right) type
  typed_symbol : ∀ name type, typed (.symbol name) type ↔ leaf (.symbol name) type
  typed_var : ∀ name type, typed (.var name) type ↔ leaf (.var name) type
  typed_grounded : ∀ value type, typed (.grounded value) type ↔ leaf (.grounded value) type
  typed_expression : ∀ atoms type,
    typed (.expression atoms) type ↔ ∃ parts, List.Forall₂ typed atoms parts ∧ combine parts type

namespace CompositionalContract

variable {space : Space} {τ : Type} (contract : CompositionalContract space τ)

private theorem forall₂_map_iff {α β : Type} (f : α → α) (relation : α → β → Prop)
    (pointwise : ∀ a b, relation (f a) b ↔ relation a b) :
    ∀ (sources : List α) (targets : List β),
      List.Forall₂ relation (sources.map f) targets ↔ List.Forall₂ relation sources targets
  | [], targets => by simp
  | source :: sources, [] => by simp
  | source :: sources, target :: targets => by
      simp only [List.map_cons, List.forall₂_cons, pointwise,
        forall₂_map_iff f relation pointwise sources targets]

/-- **Compositional contracts cannot tell equally declared symbols apart.** -/
theorem swap_iff {left right : String} (same : EquallyDeclared space left right) :
    ∀ (expression : Atom) (type : τ),
      contract.typed (swapAtom left right expression) type ↔ contract.typed expression type := by
  intro expression
  induction expression using Atom.rec (motive_2 := fun atoms =>
      ∀ (parts : List τ),
        List.Forall₂ contract.typed (atoms.map (swapAtom left right)) parts ↔
          List.Forall₂ contract.typed atoms parts) with
  | symbol name =>
      intro type
      simp only [swapAtom, contract.typed_symbol, swapString]
      split_ifs with isLeft isRight
      · subst isLeft
        exact (contract.leaf_declared _ _ same type).symm
      · subst isRight
        exact contract.leaf_declared _ _ same type
      · exact Iff.rfl
  | var name => intro type; simp only [swapAtom]
  | grounded value => intro type; simp only [swapAtom]
  | expression atoms ih =>
      intro type
      simp only [swapAtom, contract.typed_expression]
      constructor
      · rintro ⟨parts, typedParts, combined⟩
        exact ⟨parts, (ih parts).mp typedParts, combined⟩
      · rintro ⟨parts, typedParts, combined⟩
        exact ⟨parts, (ih parts).mpr typedParts, combined⟩
  | nil => simp
  | cons head tail headIH tailIH =>
      rename_i parts
      cases parts with
      | nil => simp
      | cons part parts =>
          simp only [List.map_cons, List.forall₂_cons, headIH part, tailIH parts]

/-- Read HE's types into a compositional contract's types, the relation the contract gives
between HE terms and HE types is declaration-invariant. -/
theorem declarationInvariant (read : Atom → τ) :
    DeclarationInvariant space (fun expression type => contract.typed expression (read type)) :=
  fun _ _ same expression type => contract.swap_iff same expression (read type)

end CompositionalContract

/-! ## Dependent typing of HE telescopes -/

/-- The telescope `(-> (: $x₁ A₁) … (: $xₙ Aₙ) B)`. -/
def telescope (binders : List (String × Atom)) (result : Atom) : Atom :=
  .expression (.symbol "->" ::
    (binders.map (fun binder => .expression [.symbol ":", .var binder.1, binder.2]) ++ [result]))

/-- A declaration read by dependent typing: a plain type, or a telescope. -/
inductive DependentDeclaration where
  | plain (type : Atom)
  | telescope (binders : List (String × Atom)) (result : Atom)

/-- The HE type that a dependent declaration reads. -/
def DependentDeclaration.atom : DependentDeclaration → Atom
  | .plain type => type
  | .telescope binders result => HOLContract.telescope binders result

/-- The valuation sending each telescope variable to its argument; any other variable stays. -/
def argumentValuation : List (String × Atom) → List Atom → String → Atom
  | (bound, _) :: binders, argument :: arguments, other =>
      if other = bound then argument else argumentValuation binders arguments other
  | _, _, other => .var other

/-- **Dependent typing of HE telescopes**, the reading he-prime gives a binder that names its
argument: a constant has its declared type, and an application of a constant declared with a
telescope to arguments has the telescope's result with the arguments substituted for its
variables, when each argument has its binder's type under the same substitution.  This is
λΠ's application rule for declared constants, without conversion. -/
inductive DependentTyped (declarations : String → Option DependentDeclaration) :
    Atom → Atom → Prop where
  | constant {name : String} {type : Atom} :
      declarations name = some (.plain type) → DependentTyped declarations (.symbol name) type
  | application {name : String} {binders : List (String × Atom)} {result : Atom}
      {arguments : List Atom} :
      declarations name = some (.telescope binders result) →
      binders.length = arguments.length →
      (∀ (index : Nat) (inBinders : index < binders.length) (inArguments : index < arguments.length),
        DependentTyped declarations arguments[index]
          (applyTypeValuation (argumentValuation binders arguments) binders[index].2)) →
      DependentTyped declarations (.expression (.symbol name :: arguments))
        (applyTypeValuation (argumentValuation binders arguments) result)

/-! ## The dependent-binder signature -/

private def sym (name : String) : Atom := .symbol name

private def app (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)

/-- The binder declarations of the dependent-binder conformance programme. -/
def bindersDeclarations : String → Option DependentDeclaration
  | "fact" => some (.plain (sym "Fact"))
  | "other" => some (.plain (sym "Fact"))
  | "goodWitness" => some (.plain (app "WitnessOf" [sym "fact"]))
  | "otherWitness" => some (.plain (app "WitnessOf" [sym "other"]))
  | "remember" => some (.telescope [("p", sym "Fact")] (app "WitnessOf" [.var "p"]))
  | "useWitness" => some (.telescope [("p", sym "Fact"), ("w", app "WitnessOf" [.var "p"])]
      (app "Checked" [.var "p", .var "w"]))
  | _ => none

/-- The HE space of those declarations. -/
def bindersSpace : Space :=
  Space.ofList
    [SpecBoundary.annotation "Fact" (sym "Type"),
     SpecBoundary.annotation "fact" (sym "Fact"),
     SpecBoundary.annotation "other" (sym "Fact"),
     SpecBoundary.annotation "WitnessOf" (.expression [sym "->", .var "p", sym "Type"]),
     SpecBoundary.annotation "remember" ((DependentDeclaration.telescope [("p", sym "Fact")]
        (app "WitnessOf" [.var "p"])).atom),
     SpecBoundary.annotation "goodWitness" (app "WitnessOf" [sym "fact"]),
     SpecBoundary.annotation "otherWitness" (app "WitnessOf" [sym "other"]),
     SpecBoundary.annotation "Checked" (.expression [sym "->", .var "p", .var "w", sym "Type"]),
     SpecBoundary.annotation "useWitness" ((DependentDeclaration.telescope
        [("p", sym "Fact"), ("w", app "WitnessOf" [.var "p"])]
        (app "Checked" [.var "p", .var "w"])).atom)]

/-- The dependent declarations are the space's declarations. -/
theorem bindersDeclarations_read (name : String) (declaration : DependentDeclaration)
    (lookup : bindersDeclarations name = some declaration) :
    declaredType? bindersSpace (.symbol name) = some declaration.atom := by
  unfold bindersDeclarations at lookup
  split at lookup <;> (try cases lookup) <;> decide

/-- The programme annotates no expression. -/
theorem getAnnotatedTypes_bindersSpace_expression (atoms : List Atom) :
    getAnnotatedTypes bindersSpace (.expression atoms) = [] := by
  simp [getAnnotatedTypes, bindersSpace, Space.ofList, SpecBoundary.annotation, BEq.beq,
    Atom.beq]

/-- `fact` and `other` are equally declared: both are declared `Fact`, and nothing else
distinguishes them. -/
theorem fact_other_equally_declared : EquallyDeclared bindersSpace "fact" "other" := by
  intro atom
  cases atom with
  | symbol name =>
      simp only [swapAtom, swapString]
      split_ifs with isFact isOther
      · subst isFact
        decide
      · subst isOther
        decide
      · rfl
  | var name => simp only [swapAtom]
  | grounded value => simp only [swapAtom]
  | expression atoms =>
      cases atoms with
      | nil => simp only [swapAtom, List.map_nil]
      | cons head tail =>
          simp only [swapAtom, List.map_cons, declarations,
            getAnnotatedTypes_bindersSpace_expression]

/-! ## Dependent typing of the programme -/

private theorem typed_constant {name : String} {type : Atom}
    (lookup : bindersDeclarations name = some (.plain type)) :
    DependentTyped bindersDeclarations (.symbol name) type :=
  .constant lookup

/-- `(remember fact)` has type `(WitnessOf fact)`. -/
theorem dependentTyped_remember_fact :
    DependentTyped bindersDeclarations (app "remember" [sym "fact"])
      (app "WitnessOf" [sym "fact"]) := by
  have typed := DependentTyped.application (declarations := bindersDeclarations)
    (name := "remember") (binders := [("p", sym "Fact")]) (result := app "WitnessOf" [.var "p"])
    (arguments := [sym "fact"]) rfl rfl (by
      intro index inBinders _
      simp only [List.length_cons, List.length_nil] at inBinders
      obtain rfl : index = 0 := by omega
      simp only [List.getElem_cons_zero, sym, applyTypeValuation]
      exact typed_constant rfl)
  simpa [app, sym, applyTypeValuation, argumentValuation] using typed

/-- `(useWitness other otherWitness)` has type `(Checked other otherWitness)`. -/
theorem dependentTyped_useWitness_other :
    DependentTyped bindersDeclarations (app "useWitness" [sym "other", sym "otherWitness"])
      (app "Checked" [sym "other", sym "otherWitness"]) := by
  have typed := DependentTyped.application (declarations := bindersDeclarations)
    (name := "useWitness") (binders := [("p", sym "Fact"), ("w", app "WitnessOf" [.var "p"])])
    (result := app "Checked" [.var "p", .var "w"])
    (arguments := [sym "other", sym "otherWitness"]) rfl rfl (by
      intro index inBinders _
      simp only [List.length_cons, List.length_nil] at inBinders
      rcases (show index = 0 ∨ index = 1 by omega) with rfl | rfl
      · simp only [List.getElem_cons_zero, sym, applyTypeValuation]
        exact typed_constant rfl
      · simp only [List.getElem_cons_succ, List.getElem_cons_zero, app, sym, applyTypeValuation,
          argumentValuation, List.map_cons, List.map_nil]
        exact typed_constant rfl)
  simpa [app, sym, applyTypeValuation, argumentValuation] using typed

/-- The only type of a constant with a plain declaration is that declaration. -/
private theorem dependentTyped_symbol_eq {name : String} {type declared : Atom}
    (lookup : bindersDeclarations name = some (.plain declared))
    (typed : DependentTyped bindersDeclarations (.symbol name) type) : type = declared := by
  cases typed with
  | constant found =>
      rw [lookup] at found
      cases found
      rfl

/-- The only type of `(remember other)` is `(WitnessOf other)`. -/
theorem dependentTyped_remember_other_eq {type : Atom}
    (typed : DependentTyped bindersDeclarations (app "remember" [sym "other"]) type) :
    type = app "WitnessOf" [sym "other"] := by
  cases typed with
  | application lookup lengths arguments =>
      rename_i binders result
      simp only [bindersDeclarations, Option.some.injEq,
        DependentDeclaration.telescope.injEq] at lookup
      obtain ⟨rfl, rfl⟩ := lookup
      simp [app, sym, applyTypeValuation, argumentValuation]

/-- `(remember other)` does not have type `(WitnessOf fact)`. -/
theorem not_dependentTyped_remember_other_fact :
    ¬DependentTyped bindersDeclarations (app "remember" [sym "other"])
      (app "WitnessOf" [sym "fact"]) := by
  intro typed
  have equal := dependentTyped_remember_other_eq typed
  simp [app, sym] at equal

/-- **The golden refutation.**  `(useWitness fact otherWitness)` has no type: the witness
belongs to the family of `other`. -/
theorem not_dependentTyped_useWitness_fact (type : Atom) :
    ¬DependentTyped bindersDeclarations (app "useWitness" [sym "fact", sym "otherWitness"]) type := by
  intro typed
  cases typed with
  | application lookup lengths arguments =>
      rename_i binders result
      simp only [bindersDeclarations, Option.some.injEq,
        DependentDeclaration.telescope.injEq] at lookup
      obtain ⟨rfl, rfl⟩ := lookup
      have witness := arguments 1 (by simp) (by simp)
      simp only [List.getElem_cons_succ, List.getElem_cons_zero] at witness
      have equal := dependentTyped_symbol_eq (name := "otherWitness") rfl witness
      simp [app, sym, applyTypeValuation, argumentValuation] at equal

/-! ## No declaration-invariant relation agrees -/

theorem swap_remember :
    swapAtom "fact" "other" (app "remember" [sym "fact"]) = app "remember" [sym "other"] := by
  simp [swapAtom, swapString, app, sym]

theorem swap_useWitness :
    swapAtom "fact" "other" (app "useWitness" [sym "other", sym "otherWitness"]) =
      app "useWitness" [sym "fact", sym "otherWitness"] := by
  simp [swapAtom, swapString, app, sym]

/-- **A declaration-invariant relation types the refuted golden.**  Whatever types
`(useWitness other otherWitness)` and cannot tell `fact` from `other` also types
`(useWitness fact otherWitness)`, at the same type. -/
theorem declarationInvariant_types_refuted_golden {relation : Atom → Atom → Prop}
    (invariant : DeclarationInvariant bindersSpace relation) {type : Atom}
    (typed : relation (app "useWitness" [sym "other", sym "otherWitness"]) type) :
    relation (app "useWitness" [sym "fact", sym "otherWitness"]) type := by
  rw [← swap_useWitness]
  exact (invariant "fact" "other" fact_other_equally_declared _ type).mpr typed

/-- **No declaration-invariant relation agrees with dependent typing** on the dependent-binder
programme. -/
theorem no_declarationInvariant_agrees {relation : Atom → Atom → Prop}
    (invariant : DeclarationInvariant bindersSpace relation)
    (agrees : ∀ expression type,
      relation expression type ↔ DependentTyped bindersDeclarations expression type) : False := by
  have rememberFact := (agrees _ _).mpr dependentTyped_remember_fact
  rw [← (invariant "fact" "other" fact_other_equally_declared _ _), swap_remember] at rememberFact
  exact not_dependentTyped_remember_other_fact ((agrees _ _).mp rememberFact)

/-- **The contract disagrees with dependent typing.** -/
theorem typed_disagrees_dependent :
    ¬∀ expression type,
      Typed bindersSpace expression type ↔ DependentTyped bindersDeclarations expression type :=
  fun agrees => no_declarationInvariant_agrees (typed_declarationInvariant bindersSpace) agrees

/-- **No compositional contract with declared leaves agrees with dependent typing**, under any
reading of HE's types into its own. -/
theorem CompositionalContract.disagrees_dependent {τ : Type}
    (contract : CompositionalContract bindersSpace τ) (read : Atom → τ) :
    ¬∀ expression type,
      contract.typed expression (read type) ↔ DependentTyped bindersDeclarations expression type :=
  fun agrees => no_declarationInvariant_agrees (contract.declarationInvariant read) agrees

/-- Dependent typing is not declaration-invariant. -/
theorem dependentTyped_not_declarationInvariant :
    ¬DeclarationInvariant bindersSpace (DependentTyped bindersDeclarations) :=
  fun invariant => no_declarationInvariant_agrees invariant (fun _ _ => Iff.rfl)

#print axioms typed_swap_iff
#print axioms CompositionalContract.swap_iff
#print axioms dependentTyped_remember_fact
#print axioms dependentTyped_useWitness_other
#print axioms not_dependentTyped_useWitness_fact
#print axioms declarationInvariant_types_refuted_golden
#print axioms no_declarationInvariant_agrees
#print axioms typed_disagrees_dependent
#print axioms CompositionalContract.disagrees_dependent
#print axioms dependentTyped_not_declarationInvariant

end Mettapedia.Languages.MeTTa.HE.HOLContract

import Mettapedia.Languages.MeTTa.HE.HOLContract.Agreement

/-!
# What the contract licenses at run time

A runtime may decide HE's typing once and reuse the decision, instead of checking at every call,
when the contract licenses it.  The hosted HOL Light checker stays the contract's check and its
audit; nothing here asks a runtime to call it.

* **Signature dependence.**  A contract judgment depends only on the declarations and the term
  (`typed_iff_of_sameDeclarations`): adding an atom that is not a type declaration changes no
  judgment (`typed_add_iff`), and adding a declaration can (`declaration_changes_judgment`).  A
  runtime may therefore keep contract judgments per declaration revision.  The contract has no
  subtyping, meta-types or `%Undefined%`: a subtype declaration changes no contract judgment
  (`typed_add_subtypeDeclaration_iff`) but changes HE's answers, so a cache of HE's answers is
  keyed on the subtype declarations as well (`subtype_edge_outside_declarations`).
* **Principal types.**  On first-order expressions over schematic declarations, HE's exact
  candidate, which HE computes by first-order unification, is the principal type scheme of the
  contract's typings (`principal_of_exact`).  `NativeChecker` is what a native checker must
  answer and `NativeChecker.decides` its correctness; HE's candidate is admitted
  (`exactChecker`), and the most general answer is not (`generalChecker_not_admitted`).  The
  checker of `Principal`, which computes principal types by first-order unification, is admitted
  in `PrincipalNative`.
* **Erasure.**  A typed call stays typed when its arguments are replaced by atoms with the same
  types (`typed_replace_arguments`), and a call through a declaration whose result variables
  occur in its parameters has a single type for given argument types (`call_type_determined`).
  So when every argument's value keeps its static type, the runtime applicability check of the
  arguments of a statically typed call succeeds and can be omitted.  With a result-only type
  variable it cannot: under `(: if (-> Bool $a $a $t))`, `(if True Z Z)` has the
  constructor-free type `Empty` though its value `Z`, by HE's equation
  `(= (if True $then $else) $then)`, has not, and the call `(absurd (if True Z Z))` is typed while
  `(absurd Z)` is not (`IfEmpty`).  A declaration returning `%Undefined%` gives a call no typing
  to license anything (`undefined_result_untyped`).  Erasure licenses argument checks only: a
  static type says nothing about the bodies that compute a call's value, so checking a result
  needs evidence about the bodies (`WrongBody.static_type_not_body_type`).
* **Multiplicity.**  The contract terms of a judgment correspond one to one to the derivations of
  HE's first-order rule (`judgmentTermEquiv`, from `derivationTerm_injective` and
  `derivationTerm_surjective`), and the derivations of a judgment are the same in every space
  with the same declarations, with the same terms (`derivationTransport`).  On variable-free
  declarations a derivation is determined by its skeleton, the declaration occurrences and rules
  it uses (`skeleton_determines`), which is how HE's specified relation enumerates its
  candidates, one per operator type and choice of argument candidates
  (`ApplicationPackageMatrixRel`).  So a cache that keeps one entry per derivation keeps HE's
  multiplicity: `(h b)` under two declarations of `h` and of `b` has exactly two derivations
  (`Multiplicity.hb_derivations`), and a declaration repeated verbatim is two constants
  (`Multiplicity.g_occurrences_differ`).  With a type variable that no result fixes, one skeleton
  has a derivation for every value of the variable (`Multiplicity.lenNil_one_skeleton_two_derivations`):
  there HE answers one principal scheme per skeleton, and a cache keeps the schemes.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.HOLContract

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.TypeGrounding
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.NamedElaboration
open Spec.Type
open Spec.Type.Presentation
open Spec.Type.RuntimeRefinement
open Spec.Bindings.ScopeObservation

/-! ## Signature dependence -/

/-- Two spaces with the same declarations. -/
def SameDeclarations (space other : Space) : Prop :=
  ∀ atom, declarations space atom = declarations other atom

theorem nameType_of_sameDeclarations {space other : Space} (same : SameDeclarations space other) :
    nameType space = nameType other := by
  funext name
  cases name with
  | declared constant occurrence instanceType =>
      have instanceIff : Instance space constant occurrence instanceType ↔
          Instance other constant occurrence instanceType := by
        simp only [Instance, same constant]
      simp only [nameType]
      by_cases isInstance : Instance space constant occurrence instanceType
      · rw [if_pos isInstance, if_pos (instanceIff.mp isInstance)]
      · rw [if_neg isInstance, if_neg (fun other => isInstance (instanceIff.mpr other))]
  | apply _ _ => rfl
  | pair components => cases components <;> rfl
  | fst components => cases components <;> rfl
  | snd components => cases components <;> rfl
  | one => rfl

/-- **A judgment depends only on the declarations.** -/
theorem typed_iff_of_sameDeclarations {space other : Space} (same : SameDeclarations space other)
    (expression type : Atom) : Typed space expression type ↔ Typed other expression type := by
  rw [typed_iff, typed_iff, nameType_of_sameDeclarations same]

/-- An atom that is not a type declaration adds no declared type. -/
theorem getAnnotatedTypes_add {space : Space} {atom : Atom}
    (notDeclaration : Space.isTypeAnnotation atom = false) (subject : Atom) :
    getAnnotatedTypes (space.add atom) subject = getAnnotatedTypes space subject := by
  unfold getAnnotatedTypes Space.add
  rw [List.filterMap_cons]
  split
  · rfl
  · next found value equal =>
      exfalso
      split at equal
      · simp [Space.isTypeAnnotation] at notDeclaration
      · cases equal

/-- Adding an atom that is not a type declaration keeps every declaration. -/
theorem sameDeclarations_add {space : Space} {atom : Atom}
    (notDeclaration : Space.isTypeAnnotation atom = false) :
    SameDeclarations (space.add atom) space := by
  intro subject
  cases subject with
  | grounded value => rfl
  | var name => rfl
  | symbol name => exact getAnnotatedTypes_add notDeclaration _
  | expression atoms =>
      cases atoms with
      | nil => rfl
      | cons head rest => exact getAnnotatedTypes_add notDeclaration _

/-- **Adding an atom that is not a declaration changes no judgment.** -/
theorem typed_add_iff {space : Space} {atom : Atom}
    (notDeclaration : Space.isTypeAnnotation atom = false) (expression type : Atom) :
    Typed (space.add atom) expression type ↔ Typed space expression type :=
  typed_iff_of_sameDeclarations (sameDeclarations_add notDeclaration) expression type

/-- **Negative control: adding a declaration can change a judgment.**  An undeclared symbol has
no type; declared, it has its declared type. -/
theorem declaration_changes_judgment :
    ¬Typed Space.empty (.symbol "x") (.symbol "A") ∧
      Typed (Space.empty.add (SpecBoundary.annotation "x" (.symbol "A"))) (.symbol "x")
        (.symbol "A") := by
  constructor
  · rw [typed_iff_firstOrder]
    intro typed
    cases typed with
    | declared isInstance =>
        obtain ⟨_, found, _⟩ := isInstance
        simp [declarations, getAnnotatedTypes, Space.empty] at found
  · rw [typed_iff_firstOrder]
    exact .declared (occurrence := 0) ⟨.symbol "A", by decide,
      typeInstance_self (contractType_symbol (by decide))⟩

/-! ### The boundary of signature dependence: subtype declarations -/

/-- A subtype declaration `(:< sub super)`. -/
def subtypeDeclaration (sub super : Atom) : Atom := .expression [.symbol ":<", sub, super]

/-- The subtype declarations of a space, as pairs. -/
def subtypeEdges (space : Space) : List (Atom × Atom) :=
  space.atoms.filterMap fun atom =>
    match atom with
    | .expression [.symbol ":<", sub, super] => some (sub, super)
    | _ => none

/-- A space without subtype declarations. -/
def SubtypeFree (space : Space) : Prop := subtypeEdges space = []

/-- **The contract ignores subtype declarations.**  `(:< sub super)` is not a type declaration, so
adding it changes no contract judgment. -/
theorem typed_add_subtypeDeclaration_iff {space : Space} (sub super expression type : Atom) :
    Typed (space.add (subtypeDeclaration sub super)) expression type ↔
      Typed space expression type :=
  typed_add_iff rfl expression type

/-- **Negative control: the declarations do not determine HE's answers once subtypes occur.**
`(: x A)` and `(: x A) (:< A B)` have the same declarations, so the same contract judgments, but
different subtype declarations; HE answers `[A]` to `(get-type x)` in the first and `[A, B]` in the
second.  A cache keyed by declarations stands for HE's answers only on subtype-free spaces, where
the contract agrees with HE; a cache of HE's answers is keyed on the subtype declarations too, and
on the imports that feed either. -/
theorem subtype_edge_outside_declarations :
    SameDeclarations
        ((Space.ofList [SpecBoundary.annotation "x" (.symbol "A")]).add
          (subtypeDeclaration (.symbol "A") (.symbol "B")))
        (Space.ofList [SpecBoundary.annotation "x" (.symbol "A")]) ∧
      SubtypeFree (Space.ofList [SpecBoundary.annotation "x" (.symbol "A")]) ∧
      ¬SubtypeFree ((Space.ofList [SpecBoundary.annotation "x" (.symbol "A")]).add
        (subtypeDeclaration (.symbol "A") (.symbol "B"))) := by
  refine ⟨sameDeclarations_add rfl, by unfold SubtypeFree; decide, by unfold SubtypeFree; decide⟩

/-! ## Principal types -/

/-- **HE's exact candidate is the principal type.**  On a first-order expression over
schematic declarations without `%Undefined%` fallback, the contract types the expression at a
ground first-order type exactly when the type is a first-order instance of HE's exact
candidate. -/
theorem principal_of_exact {space : Space} {expression principal type : Atom}
    (fragment : Schematic.SchematicTerm space expression)
    (noFallback : NoUndefinedFallback space expression)
    (exact : ExactTypes space expression [principal])
    (ground : Schematic.GroundFirstOrder type) :
    Typed space expression type ↔
      ∃ valuation, Schematic.FirstOrderValuation valuation ∧
        applyTypeValuation valuation principal = type := by
  rw [schematic_iff_exact fragment ground]
  constructor
  · rintro ⟨_, other, otherExact, instanceOf⟩
    exact (Schematic.exact_candidates_same_instances fragment noFallback otherExact exact
      type).mp instanceOf
  · intro instanceOf
    exact ⟨noFallback, principal, exact, instanceOf⟩

/-- A ground first-order instance of a scheme. -/
def GroundInstance (scheme type : Atom) : Prop :=
  Schematic.GroundFirstOrder type ∧
    ∃ valuation, Schematic.FirstOrderValuation valuation ∧ applyTypeValuation valuation scheme = type

/-- A native checker of a fragment answers a type scheme for each expression.  It is admitted
with two laws at ground first-order types: every instance of its answer is a contract typing
(soundness), and every contract typing is an instance of its answer (completeness). -/
structure NativeChecker (space : Space) (fragment : Atom → Prop) where
  answer : Atom → Atom
  sound : ∀ expression, fragment expression → ∀ type,
    GroundInstance (answer expression) type → Typed space expression type
  complete : ∀ expression, fragment expression → ∀ type, Schematic.GroundFirstOrder type →
    Typed space expression type → GroundInstance (answer expression) type

/-- **An admitted native checker decides the contract on its fragment.** -/
theorem NativeChecker.decides {space : Space} {fragment : Atom → Prop}
    (checker : NativeChecker space fragment) {expression type : Atom}
    (inFragment : fragment expression) (ground : Schematic.GroundFirstOrder type) :
    Typed space expression type ↔ GroundInstance (checker.answer expression) type :=
  ⟨checker.complete expression inFragment type ground, checker.sound expression inFragment type⟩

/-- Two admitted native checkers answer schemes with the same ground first-order instances: the
answer is the principal type, whichever checker computes it. -/
theorem NativeChecker.same_instances {space : Space} {fragment : Atom → Prop}
    (left right : NativeChecker space fragment) {expression : Atom} (inFragment : fragment expression)
    (type : Atom) :
    GroundInstance (left.answer expression) type ↔ GroundInstance (right.answer expression) type := by
  constructor
  · intro instance'
    exact (right.decides inFragment instance'.1).mp ((left.decides inFragment instance'.1).mpr instance')
  · intro instance'
    exact (left.decides inFragment instance'.1).mp ((right.decides inFragment instance'.1).mpr instance')

/-- First-order expressions over schematic declarations without `%Undefined%` fallback that have
an exact candidate. -/
def SchematicFragment (space : Space) (expression : Atom) : Prop :=
  Schematic.SchematicTerm space expression ∧ NoUndefinedFallback space expression ∧
    ∃ principal, ExactTypes space expression [principal]

open Classical in
/-- **HE's candidate is an admitted native answer.**  The checker answering HE's exact candidate
decides the contract on first-order expressions over schematic declarations. -/
noncomputable def exactChecker (space : Space) : NativeChecker space (SchematicFragment space) where
  answer := fun expression =>
    if candidate : ∃ principal, ExactTypes space expression [principal] then candidate.choose
    else Atom.undefinedType
  sound := by
    intro expression ⟨fragment, noFallback, candidate⟩ type ⟨ground, instanceOf⟩
    simp only [dif_pos candidate] at instanceOf
    exact (principal_of_exact fragment noFallback candidate.choose_spec ground).mpr instanceOf
  complete := by
    intro expression ⟨fragment, noFallback, candidate⟩ type ground typed
    refine ⟨ground, ?_⟩
    simp only [dif_pos candidate]
    exact (principal_of_exact fragment noFallback candidate.choose_spec ground).mp typed

/-- **Negative control: the most general answer is not admitted.**  `(cons zero zero)` has no
type, though `Nat` is a ground first-order instance of the scheme `$t`. -/
theorem generalChecker_not_admitted :
    ¬∃ checker : NativeChecker Schematic.listSpace (fun expression =>
        expression = Schematic.consZeroZero),
      checker.answer Schematic.consZeroZero = .var "t" := by
  rintro ⟨checker, answerEq⟩
  have ground : Schematic.GroundFirstOrder (.symbol "Nat") :=
    ⟨Schematic.reservedFree_symbol_iff.mpr (by decide), rfl⟩
  have typed := checker.sound Schematic.consZeroZero rfl (.symbol "Nat")
    ⟨ground, fun _ => .symbol "Nat", fun _ => ground, by rw [answerEq]; simp [applyTypeValuation]⟩
  rw [typed_iff_firstOrder] at typed
  have hol := schematicHOL_of_firstOrder Schematic.consZeroZero_fragment typed
  exact Schematic.consZeroZero_not_hol _ hol

/-! ## Erasure -/

/-- **A typed call stays typed with arguments of the same types.**  If every argument may be
replaced by an atom that has every type the argument has, the call keeps its type: the
applicability check of a statically typed call, on arguments that keep their static types,
succeeds. -/
theorem typed_replace_arguments {space : Space} {head : Atom} {arguments values : List Atom}
    {type : Atom} (unannotated : declarations space (.expression (head :: arguments)) = [])
    (typed : FirstOrderType space (.expression (head :: arguments)) type)
    (keep : List.Forall₂ (fun argument value =>
      ∀ argumentType, FirstOrderType space argument argumentType →
        FirstOrderType space value argumentType) arguments values) :
    FirstOrderType space (.expression (head :: values)) type := by
  have replace : ∀ {arguments values types : List Atom},
      List.Forall₂ (fun argument value =>
        ∀ argumentType, FirstOrderType space argument argumentType →
          FirstOrderType space value argumentType) arguments values →
      FirstOrderTypes space arguments types → FirstOrderTypes space values types := by
    intro arguments values types keep typed
    induction keep generalizing types with
    | nil =>
        cases typed
        exact .nil
    | cons headKeep _ restIH =>
        cases typed with
        | cons headTyped restTyped => exact .cons (headKeep _ headTyped) (restIH restTyped)
  cases typed with
  | declared isInstance =>
      obtain ⟨_, found, _⟩ := isInstance
      simp [unannotated] at found
  | application headTyped argumentsTyped => exact .application headTyped (replace keep argumentsTyped)
  | tuple headTyped headNotArrow argumentsTyped =>
      exact .tuple headTyped headNotArrow (replace keep argumentsTyped)

/-- A declaration determines its result when every type variable of its result occurs in its
parameters. -/
def ResultDetermined (parameters : List Atom) (result : Atom) : Prop :=
  ∀ name ∈ TypeSubst.typeVars result, name ∈ TypeSubst.typeVarsList parameters

/-- Two valuations that agree on an atom's instance agree on its variables. -/
theorem valuations_agree {left right : String → Atom} :
    ∀ (atom : Atom), applyTypeValuation left atom = applyTypeValuation right atom →
      ∀ name ∈ TypeSubst.typeVars atom, left name = right name := by
  intro atom
  induction atom using Atom.rec (motive_2 := fun atoms =>
      atoms.map (applyTypeValuation left) = atoms.map (applyTypeValuation right) →
        ∀ name ∈ TypeSubst.typeVarsList atoms, left name = right name) with
  | symbol name => intro _ other member; simp [TypeSubst.typeVars] at member
  | grounded value => intro _ other member; simp [TypeSubst.typeVars] at member
  | var name =>
      intro equal other member
      simp only [TypeSubst.typeVars, List.mem_singleton] at member
      subst member
      simpa [applyTypeValuation] using equal
  | expression atoms ih =>
      intro equal other member
      simp only [applyTypeValuation, Atom.expression.injEq] at equal
      exact ih equal other (by simpa [TypeSubst.typeVars] using member)
  | nil =>
      rename_i _ other member
      simp [TypeSubst.typeVarsList] at member
  | cons head tail headIH tailIH =>
      rename_i equal other member
      simp only [List.map_cons, List.cons.injEq] at equal
      simp only [TypeSubst.typeVarsList, List.mem_append] at member
      rcases member with member | member
      · exact headIH equal.1 other member
      · exact tailIH equal.2 other member

theorem valuations_agree_list {left right : String → Atom} :
    ∀ (atoms : List Atom), atoms.map (applyTypeValuation left) = atoms.map (applyTypeValuation right) →
      ∀ name ∈ TypeSubst.typeVarsList atoms, left name = right name
  | [], _, name, member => by simp [TypeSubst.typeVarsList] at member
  | head :: tail, equal, name, member => by
      simp only [List.map_cons, List.cons.injEq] at equal
      simp only [TypeSubst.typeVarsList, List.mem_append] at member
      rcases member with member | member
      · exact valuations_agree head equal.1 name member
      · exact valuations_agree_list tail equal.2 name member

/-- **A determined call has one type for given argument types.**  A call through a single
declaration whose result variables occur in its parameters, with arguments of unique types,
has a single type. -/
theorem call_type_determined {space : Space} {name : String} {arguments parameters : List Atom}
    {result : Atom}
    (declared : declarations space (.symbol name) = [arrowAtom parameters result])
    (determined : ResultDetermined parameters result)
    (unannotated : declarations space (.expression (.symbol name :: arguments)) = [])
    (argumentsUnique : ∀ argument ∈ arguments, ∀ {left right : Atom},
      FirstOrderType space argument left → FirstOrderType space argument right → left = right)
    {left right : Atom}
    (leftTyped : FirstOrderType space (.expression (.symbol name :: arguments)) left)
    (rightTyped : FirstOrderType space (.expression (.symbol name :: arguments)) right) :
    left = right := by
  have headCases : ∀ {type : Atom}, FirstOrderType space (.symbol name) type →
      ∃ valuation : String → Atom,
        type = arrowAtom (parameters.map (applyTypeValuation valuation))
          (applyTypeValuation valuation result) := by
    intro type typed
    obtain ⟨occurrence, scheme, found, _, valuation, _, instanceEq⟩ := firstOrder_symbol typed
    rw [declared] at found
    cases occurrence with
    | succ _ => simp at found
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at found
        subst found
        exact ⟨valuation, by rw [← instanceEq, applyTypeValuation_arrowAtom]⟩
  have callCases : ∀ {type : Atom},
      FirstOrderType space (.expression (.symbol name :: arguments)) type →
      ∃ valuation : String → Atom, type = applyTypeValuation valuation result ∧
        FirstOrderTypes space arguments (parameters.map (applyTypeValuation valuation)) := by
    intro type typed
    cases typed with
    | declared isInstance =>
        obtain ⟨_, found, _⟩ := isInstance
        simp [unannotated] at found
    | application headTyped argumentsTyped =>
        obtain ⟨valuation, headEq⟩ := headCases headTyped
        obtain ⟨parametersEq, resultEq⟩ := arrowAtom_injective headEq
        subst parametersEq resultEq
        exact ⟨valuation, rfl, argumentsTyped⟩
    | tuple headTyped headNotArrow _ =>
        obtain ⟨valuation, headEq⟩ := headCases headTyped
        rw [headEq] at headNotArrow
        exact absurd (arrowAtom_arrowShaped _ _) headNotArrow
  obtain ⟨leftValuation, rfl, leftArguments⟩ := callCases leftTyped
  obtain ⟨rightValuation, rfl, rightArguments⟩ := callCases rightTyped
  have unique : ∀ {arguments types others : List Atom},
      (∀ argument ∈ arguments, ∀ {left right : Atom},
        FirstOrderType space argument left → FirstOrderType space argument right → left = right) →
      FirstOrderTypes space arguments types → FirstOrderTypes space arguments others →
      types = others := by
    intro arguments types others argumentsUnique typed others'
    induction arguments generalizing types others with
    | nil =>
        cases typed
        cases others'
        rfl
    | cons head tail ih =>
        cases typed with
        | cons headTyped tailTyped =>
            cases others' with
            | cons headOther tailOther =>
                rw [argumentsUnique head (by simp) headTyped headOther,
                  ih (fun argument member => argumentsUnique argument (List.mem_cons_of_mem _ member))
                    tailTyped tailOther]
  have parametersEq := unique argumentsUnique leftArguments rightArguments
  exact applyTypeValuation_congr_of_typeVars result (fun other member =>
    valuations_agree_list parameters parametersEq other (determined other member))

/-! ### A result-only type variable blocks erasure -/

namespace IfEmpty

abbrev boolType : Atom := .symbol "Bool"
abbrev natType : Atom := .symbol "Nat"
abbrev emptyType : Atom := .symbol "Empty"
abbrev unitType : Atom := .symbol "Unit"

/-- `(: if (-> Bool $a $a $t))`, `(: True Bool)`, `(: Z Nat)`, `(: Empty Type)` and
`(: absurd (-> Empty Unit))`: `Empty` has no constructor, and the result variable `$t` of `if`
occurs in no parameter. -/
def ifSpace : Space :=
  Space.ofList
    [SpecBoundary.annotation "if" (arrowAtom [boolType, .var "a", .var "a"] (.var "t")),
     SpecBoundary.annotation "True" boolType,
     SpecBoundary.annotation "Z" natType,
     SpecBoundary.annotation "Empty" (.symbol "Type"),
     SpecBoundary.annotation "absurd" (arrowAtom [emptyType] unitType)]

/-- `(if True Z Z)`. -/
abbrev ifCall : Atom := .expression [.symbol "if", .symbol "True", .symbol "Z", .symbol "Z"]

theorem if_not_determined :
    ¬ResultDetermined [boolType, .var "a", .var "a"] (.var "t") := by
  intro determined
  have := determined "t" (by simp [TypeSubst.typeVars])
  simp [TypeSubst.typeVarsList, TypeSubst.typeVars] at this

private theorem contract (name : String) (notReserved : name ∉ reservedTypeNames := by decide) :
    ContractType (.symbol name) :=
  contractType_symbol notReserved

private theorem declaredSymbol {name : String} {type : Atom}
    (found : (declarations ifSpace (.symbol name))[0]? = some type) (contractType : ContractType type) :
    FirstOrderType ifSpace (.symbol name) type :=
  .declared (occurrence := 0) ⟨type, found, typeInstance_self contractType⟩

/-- `(if True Z Z)` at any type `T`: `$a` is `Nat` and `$t` is `T`. -/
private theorem ifCall_typed {type : Atom} (typeAtom : ContractType type) :
    FirstOrderType ifSpace ifCall type := by
  refine .application (parameters := [boolType, natType, natType]) (result := type) ?_
    (.cons (declaredSymbol (by decide) (contract "Bool"))
      (.cons (declaredSymbol (by decide) (contract "Nat"))
        (.cons (declaredSymbol (by decide) (contract "Nat")) .nil)))
  have boolContract := contract "Bool"
  have natContract := contract "Nat"
  refine .declared (occurrence := 0) ⟨arrowAtom [boolType, .var "a", .var "a"] (.var "t"), by decide,
    contractType_arrowAtom (by simp [boolContract, natContract, typeAtom]),
    fun name => if name = "a" then natType else if name = "t" then type else .var name, ?_, ?_⟩
  · intro name
    by_cases isA : name = "a"
    · simp only [if_pos isA]
      exact (contract "Nat").1
    · by_cases isT : name = "t"
      · simp only [if_neg isA, if_pos isT]
        exact typeAtom.1
      · simp only [if_neg isA, if_neg isT]
        exact .var name
  · simp [applyTypeValuation, arrowAtom]

/-- **`(if True Z Z)` has the constructor-free type `Empty`**, statically. -/
theorem ifCall_empty : Typed ifSpace ifCall emptyType :=
  typed_iff_firstOrder.mpr (ifCall_typed (contract "Empty"))

/-- It also has the type `Nat`: its argument types do not determine its type. -/
theorem ifCall_nat : Typed ifSpace ifCall natType :=
  typed_iff_firstOrder.mpr (ifCall_typed (contract "Nat"))

/-- **The call `(absurd (if True Z Z))` is typed statically.** -/
theorem absurd_ifCall : Typed ifSpace (.expression [.symbol "absurd", ifCall]) unitType := by
  have emptyContract := contract "Empty"
  have unitContract := contract "Unit"
  exact typed_iff_firstOrder.mpr (.application (parameters := [emptyType])
    (declaredSymbol (by decide) (contractType_arrowAtom (by simp [emptyContract, unitContract])))
    (.cons (ifCall_typed emptyContract) .nil))

/-- **The value `Z` is not of type `Empty`.** -/
theorem z_not_empty : ¬Typed ifSpace (.symbol "Z") emptyType := by
  rw [typed_iff_firstOrder]
  intro typed
  obtain ⟨occurrence, scheme, found, _, valuation, _, instanceEq⟩ := firstOrder_symbol typed
  cases occurrence with
  | zero =>
      have declared : (declarations ifSpace (.symbol "Z"))[0]? = some natType := by decide
      rw [declared, Option.some.injEq] at found
      subst found
      simp [applyTypeValuation] at instanceEq
  | succ index =>
      have length : (declarations ifSpace (.symbol "Z")).length = 1 := by decide
      rw [List.getElem?_eq_none (by rw [length]; omega)] at found
      cases found

/-- **Negative control: the check on the value fails.**  `(absurd Z)` has no type: had the
runtime omitted the check of `absurd`'s argument because `(absurd (if True Z Z))` is typed, it
would apply `absurd` to `Z`. -/
theorem absurd_z_untyped (type : Atom) :
    ¬Typed ifSpace (.expression [.symbol "absurd", .symbol "Z"]) type := by
  rw [typed_iff_firstOrder]
  intro typed
  cases typed with
  | declared isInstance =>
      obtain ⟨_, found, _⟩ := isInstance
      have none : declarations ifSpace (.expression [.symbol "absurd", .symbol "Z"]) = [] := by
        decide
      simp [none] at found
  | application headTyped argumentsTyped =>
      obtain ⟨occurrence, scheme, found, _, valuation, _, instanceEq⟩ := firstOrder_symbol headTyped
      cases occurrence with
      | succ index =>
          have length : (declarations ifSpace (.symbol "absurd")).length = 1 := by decide
          rw [List.getElem?_eq_none (by rw [length]; omega)] at found
          cases found
      | zero =>
          have declared : (declarations ifSpace (.symbol "absurd"))[0]? =
              some (arrowAtom [emptyType] unitType) := by decide
          rw [declared, Option.some.injEq] at found
          subst found
          rw [applyTypeValuation_of_ground valuation (by decide)] at instanceEq
          obtain ⟨parametersEq, _⟩ := arrowAtom_injective instanceEq
          subst parametersEq
          cases argumentsTyped with
          | cons zTyped _ =>
              exact z_not_empty (typed_iff_firstOrder.mpr zTyped)
  | tuple headTyped headNotArrow _ =>
      obtain ⟨occurrence, scheme, found, _, valuation, _, instanceEq⟩ := firstOrder_symbol headTyped
      cases occurrence with
      | succ index =>
          have length : (declarations ifSpace (.symbol "absurd")).length = 1 := by decide
          rw [List.getElem?_eq_none (by rw [length]; omega)] at found
          cases found
      | zero =>
          have declared : (declarations ifSpace (.symbol "absurd"))[0]? =
              some (arrowAtom [emptyType] unitType) := by decide
          rw [declared, Option.some.injEq] at found
          subst found
          rw [← instanceEq, applyTypeValuation_of_ground valuation (by decide)] at headNotArrow
          exact headNotArrow (arrowAtom_arrowShaped _ _)

end IfEmpty

/-! ### Erasure covers argument checks, not results -/

namespace WrongBody

/-- `(: f (-> Number Number))` and `(= (f $x) "wrong")`. -/
def wrongSpace : Space :=
  Space.ofList
    [SpecBoundary.annotation "f" (arrowAtom [.symbol "Number"] (.symbol "Number")),
     .expression [.symbol "=", .expression [.symbol "f", .var "x"], .grounded (.string "wrong")]]

/-- `(f 1)`. -/
abbrev call : Atom := .expression [.symbol "f", .grounded (.int 1)]

/-- **Negative control: a static type says nothing about a body.**  `(f 1)` has the static type
`Number`, while the body of `f`, the right side of its equation, has no type `Number`: HE
evaluates `(f 1)` to `"wrong"` and reports `(Error "wrong" (BadType Number String))`, and with the
body `(empty)` the call has no value at all.  So the erasure theorems license omitting the
applicability check of the arguments at a statically typed call; omitting a check or a
normalization of the result needs evidence about the bodies, which the contract does not
contain. -/
theorem static_type_not_body_type :
    Typed wrongSpace call (.symbol "Number") ∧
      ¬Typed wrongSpace (.grounded (.string "wrong")) (.symbol "Number") := by
  have numberContract : ContractType (.symbol "Number") := contractType_symbol (by decide)
  constructor
  · refine typed_iff_firstOrder.mpr (.application (parameters := [.symbol "Number"]) ?_ ?_)
    · exact .declared (occurrence := 0) ⟨arrowAtom [.symbol "Number"] (.symbol "Number"),
        by decide, typeInstance_self (contractType_arrowAtom (by simp [numberContract]))⟩
    · exact .cons (.declared (occurrence := 0) ⟨.symbol "Number", rfl,
        typeInstance_self numberContract⟩) .nil
  · rw [typed_iff_firstOrder]
    intro typed
    cases typed with
    | declared isInstance =>
        rename_i occurrence
        obtain ⟨scheme, found, instance'⟩ := isInstance
        cases occurrence with
        | zero =>
            simp only [declarations, getGroundedType, List.getElem?_cons_zero,
              Option.some.injEq] at found
            subst found
            have equal := typeInstance_of_ground rfl instance'
            simp at equal
        | succ index => simp [declarations] at found

end WrongBody

/-! ### `%Undefined%` gives no typing -/

/-- A declaration whose instance would contain `%Undefined%` has no instance. -/
theorem not_instance_of_undefined {space : Space} {constant scheme : Atom} {occurrence : Nat}
    (found : (declarations space constant)[occurrence]? = some scheme)
    (undefinedResult : ∃ parameters, scheme = arrowAtom parameters Atom.undefinedType)
    (type : Atom) : ¬Instance space constant occurrence type := by
  rintro ⟨scheme', found', ⟨atomic, _⟩, valuation, _, instanceEq⟩
  rw [found] at found'
  cases found'
  obtain ⟨parameters, rfl⟩ := undefinedResult
  rw [applyTypeValuation_arrowAtom] at instanceEq
  subst instanceEq
  have components := atomic.arrowAtom_components
  have undefined := components (applyTypeValuation valuation Atom.undefinedType) (by simp)
  simp only [applyTypeValuation, Atom.undefinedType] at undefined
  exact undefined.1 |> fun typeAtom => by
    cases typeAtom with
    | symbol _ notUndefined => exact notUndefined rfl

/-- **A call through a declaration returning `%Undefined%` has no typing.**  With
`(: g (-> A %Undefined%))` and `(: a A)`, `(g a)` has no contract type: nothing licenses omitting
the runtime's check there. -/
theorem undefined_result_untyped (type : Atom) :
    ¬Typed (Space.ofList [SpecBoundary.annotation "g" (arrowAtom [.symbol "A"] Atom.undefinedType),
      SpecBoundary.annotation "a" (.symbol "A")])
      (.expression [.symbol "g", .symbol "a"]) type := by
  rw [typed_iff_firstOrder]
  intro typed
  have gUntyped : ∀ {headType : Atom}, ¬FirstOrderType
      (Space.ofList [SpecBoundary.annotation "g" (arrowAtom [.symbol "A"] Atom.undefinedType),
        SpecBoundary.annotation "a" (.symbol "A")]) (.symbol "g") headType := by
    intro headType headTyped
    obtain ⟨occurrence, scheme, found, isInstance⟩ := firstOrder_symbol headTyped
    cases occurrence with
    | succ index =>
        have length : (declarations
            (Space.ofList [SpecBoundary.annotation "g" (arrowAtom [.symbol "A"] Atom.undefinedType),
              SpecBoundary.annotation "a" (.symbol "A")]) (.symbol "g")).length = 1 := by decide
        rw [List.getElem?_eq_none (by rw [length]; omega)] at found
        cases found
    | zero =>
        exact not_instance_of_undefined found ⟨[.symbol "A"], by
          have declared : (declarations
              (Space.ofList [SpecBoundary.annotation "g" (arrowAtom [.symbol "A"] Atom.undefinedType),
                SpecBoundary.annotation "a" (.symbol "A")]) (.symbol "g"))[0]? =
              some (arrowAtom [.symbol "A"] Atom.undefinedType) := by decide
          rw [declared, Option.some.injEq] at found
          exact found.symm⟩ headType ⟨scheme, found, isInstance⟩
  cases typed with
  | declared isInstance =>
      obtain ⟨_, found, _⟩ := isInstance
      have none : declarations
          (Space.ofList [SpecBoundary.annotation "g" (arrowAtom [.symbol "A"] Atom.undefinedType),
            SpecBoundary.annotation "a" (.symbol "A")]) (.expression [.symbol "g", .symbol "a"]) = [] := by
        decide
      simp [none] at found
  | application headTyped _ => exact gUntyped headTyped
  | tuple headTyped _ _ => exact gUntyped headTyped

/-! ## Multiplicity -/

mutual

/-- A derivation of HE's first-order rule: the declaration occurrence and instance of each
declared leaf, the rule of each expression, and the parameters of each application. -/
inductive FirstOrderDerivation (space : Space) : Atom → Atom → Type where
  | declared {atom type : Atom} (occurrence : Nat) :
      Instance space atom occurrence type → FirstOrderDerivation space atom type
  | application {head result : Atom} {arguments : List Atom} (parameters : List Atom) :
      FirstOrderDerivation space head (arrowAtom parameters result) →
      FirstOrderDerivations space arguments parameters →
      FirstOrderDerivation space (.expression (head :: arguments)) result
  | tuple {head headType : Atom} {arguments argumentTypes : List Atom} :
      FirstOrderDerivation space head headType → ¬ArrowShaped headType →
      FirstOrderDerivations space arguments argumentTypes →
      FirstOrderDerivation space (.expression (head :: arguments))
        (.expression (headType :: argumentTypes))

/-- Derivations of a list of expressions at a list of types. -/
inductive FirstOrderDerivations (space : Space) : List Atom → List Atom → Type where
  | nil : FirstOrderDerivations space [] []
  | cons {argument type : Atom} {arguments types : List Atom} :
      FirstOrderDerivation space argument type → FirstOrderDerivations space arguments types →
      FirstOrderDerivations space (argument :: arguments) (type :: types)

end

mutual

theorem FirstOrderDerivation.firstOrder {space : Space} :
    {expression type : Atom} → FirstOrderDerivation space expression type →
      FirstOrderType space expression type
  | _, _, .declared _ isInstance => .declared isInstance
  | _, _, .application _ head arguments =>
      .application (FirstOrderDerivation.firstOrder head)
        (FirstOrderDerivations.firstOrder arguments)
  | _, _, .tuple head headNotArrow arguments =>
      .tuple (FirstOrderDerivation.firstOrder head) headNotArrow
        (FirstOrderDerivations.firstOrder arguments)

theorem FirstOrderDerivations.firstOrder {space : Space} :
    {arguments types : List Atom} → FirstOrderDerivations space arguments types →
      FirstOrderTypes space arguments types
  | _, _, .nil => .nil
  | _, _, .cons head tail =>
      .cons (FirstOrderDerivation.firstOrder head) (FirstOrderDerivations.firstOrder tail)

end

mutual

/-- Every first-order typing has a derivation. -/
theorem FirstOrderType.derivation {space : Space} :
    {expression type : Atom} → FirstOrderType space expression type →
      Nonempty (FirstOrderDerivation space expression type)
  | _, _, @FirstOrderType.declared _ _ _ occurrence isInstance =>
      ⟨.declared occurrence isInstance⟩
  | _, _, @FirstOrderType.application _ _ _ _ parameters head arguments =>
      match FirstOrderType.derivation head, FirstOrderTypes.derivations arguments with
      | ⟨headDerivation⟩, ⟨argumentDerivations⟩ =>
          ⟨.application parameters headDerivation argumentDerivations⟩
  | _, _, .tuple head headNotArrow arguments =>
      match FirstOrderType.derivation head, FirstOrderTypes.derivations arguments with
      | ⟨headDerivation⟩, ⟨argumentDerivations⟩ =>
          ⟨.tuple headDerivation headNotArrow argumentDerivations⟩

theorem FirstOrderTypes.derivations {space : Space} :
    {arguments types : List Atom} → FirstOrderTypes space arguments types →
      Nonempty (FirstOrderDerivations space arguments types)
  | _, _, .nil => ⟨.nil⟩
  | _, _, .cons head tail =>
      match FirstOrderType.derivation head, FirstOrderTypes.derivations tail with
      | ⟨headDerivation⟩, ⟨tailDerivations⟩ => ⟨.cons headDerivation tailDerivations⟩

end

/-- A judgment holds exactly when it has a derivation. -/
theorem typed_iff_derivation {space : Space} {expression type : Atom} :
    Typed space expression type ↔ Nonempty (FirstOrderDerivation space expression type) := by
  rw [typed_iff_firstOrder]
  exact ⟨FirstOrderType.derivation, fun ⟨derivation⟩ => derivation.firstOrder⟩

mutual

/-- The contract term of a derivation. -/
def derivationTerm {space : Space} :
    {expression type : Atom} → FirstOrderDerivation space expression type → ContractTerm
  | atom, type, .declared occurrence _ => .constant (.declared atom occurrence type)
  | _, result, .application parameters head arguments =>
      (derivationTerms arguments).foldl .app
        (.app (.constant (.apply parameters result)) (derivationTerm head))
  | _, _, @FirstOrderDerivation.tuple _ _ headType _ argumentTypes head _ arguments =>
      tupleTerm (headType :: argumentTypes) (derivationTerm head :: derivationTerms arguments)

/-- The contract terms of a list of derivations. -/
def derivationTerms {space : Space} :
    {arguments types : List Atom} → FirstOrderDerivations space arguments types →
      List ContractTerm
  | _, _, .nil => []
  | _, _, .cons head tail => derivationTerm head :: derivationTerms tail

end

theorem FirstOrderDerivations.length_eq {space : Space} :
    {arguments types : List Atom} → FirstOrderDerivations space arguments types →
      types.length = arguments.length
  | _, _, .nil => rfl
  | _, _, .cons _ tail => by simp [FirstOrderDerivations.length_eq tail]

theorem derivationTerms_length {space : Space} :
    {arguments types : List Atom} → (derivations : FirstOrderDerivations space arguments types) →
      (derivationTerms derivations).length = types.length
  | _, _, .nil => rfl
  | _, _, .cons _ tail => by simp [derivationTerms, derivationTerms_length tail]

mutual

theorem derivationTerm_annotates {space : Space} :
    {expression type : Atom} → (derivation : FirstOrderDerivation space expression type) →
      Annotates expression (derivationTerm derivation)
  | _, _, .declared occurrence _ => .declared _ occurrence _
  | _, _, .application _ head arguments =>
      .application (derivationTerm_annotates head) (derivationTerms_annotate arguments)
  | _, _, .tuple head headNotArrow arguments =>
      .tuple headNotArrow arguments.length_eq (derivationTerm_annotates head)
        (derivationTerms_annotate arguments)

theorem derivationTerms_annotate {space : Space} :
    {arguments types : List Atom} → (derivations : FirstOrderDerivations space arguments types) →
      AnnotatesList arguments (derivationTerms derivations)
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons (derivationTerm_annotates head) (derivationTerms_annotate tail)

end

mutual

theorem derivationTerm_typed {space : Space} :
    {expression type : Atom} → (derivation : FirstOrderDerivation space expression type) →
      ApplicativeTyped (nameType space) (derivationTerm derivation) (.base type)
  | _, _, .declared _ isInstance =>
      .constant (nameType_declared_eq_some_iff.mpr ⟨isInstance, rfl⟩)
  | _, _, .application _ head arguments =>
      applicativeTyped_apply_iff.mpr ⟨(FirstOrderType.contractType head.firstOrder).1, rfl,
        derivationTerm_typed head, derivationTerms_typed arguments⟩
  | _, _, @FirstOrderDerivation.tuple _ _ headType _ argumentTypes head _ arguments => by
      have lengths : (headType :: argumentTypes).length =
          (derivationTerm head :: derivationTerms arguments).length := by
        simp [derivationTerms_length]
      exact (applicativeTyped_tupleTerm_iff lengths).mpr
        ⟨rfl, .cons (derivationTerm_typed head) (derivationTerms_typed arguments)⟩

theorem derivationTerms_typed {space : Space} :
    {arguments types : List Atom} → (derivations : FirstOrderDerivations space arguments types) →
      List.Forall₂ (fun term type => ApplicativeTyped (nameType space) term (.base type))
        (derivationTerms derivations) types
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons (derivationTerm_typed head) (derivationTerms_typed tail)

end

/-- The head and the arguments of a left-nested spine of applications. -/
def spine : ContractTerm → ContractTerm × List ContractTerm
  | .app function argument => ((spine function).1, (spine function).2 ++ [argument])
  | term => (term, [])

theorem spine_constant (name : Name) : spine (.constant name) = (.constant name, []) :=
  rfl

theorem spine_foldl (arguments : List ContractTerm) (function : ContractTerm) :
    spine (arguments.foldl .app function) =
      ((spine function).1, (spine function).2 ++ arguments) := by
  induction arguments generalizing function with
  | nil => simp
  | cons argument arguments ih => simp [ih, spine]

/-- A spine of applications to a constant determines the constant and the arguments. -/
theorem foldl_app_constant_injective {left right : List ContractTerm} {leftName rightName : Name}
    (equal : (left.foldl .app (.constant leftName) : ContractTerm) =
      right.foldl .app (.constant rightName)) :
    leftName = rightName ∧ left = right := by
  have spines := congrArg spine equal
  simp only [spine_foldl, spine_constant, List.nil_append, Prod.mk.injEq,
    NamedTerm.constant.injEq] at spines
  exact spines

theorem tupleTerm_cons_spine (component : Atom) (components : List Atom) (term : ContractTerm)
    (terms : List ContractTerm) :
    tupleTerm (component :: components) (term :: terms) =
      [term, tupleTerm components terms].foldl .app
        (.constant (.pair (component :: components))) :=
  rfl

theorem tupleTerm_injective :
    ∀ {components : List Atom} {left right : List ContractTerm},
      left.length = components.length → right.length = components.length →
        tupleTerm components left = tupleTerm components right → left = right
  | [], [], [], _, _, _ => rfl
  | [], _ :: _, _, lengths, _, _ => by simp at lengths
  | [], [], _ :: _, _, lengths, _ => by simp at lengths
  | _ :: _, [], _, lengths, _, _ => by simp at lengths
  | _ :: _, _ :: _, [], _, lengths, _ => by simp at lengths
  | component :: components, leftTerm :: left, rightTerm :: right, leftLengths, rightLengths,
      equal => by
      rw [tupleTerm_cons_spine, tupleTerm_cons_spine] at equal
      obtain ⟨_, terms⟩ := foldl_app_constant_injective equal
      simp only [List.cons.injEq] at terms
      rw [terms.1, tupleTerm_injective (by simpa using leftLengths) (by simpa using rightLengths)
        terms.2.1]

mutual

/-- **Different derivations have different contract terms.** -/
theorem derivationTerm_injective {space : Space} :
    {expression type : Atom} → (left right : FirstOrderDerivation space expression type) →
      derivationTerm left = derivationTerm right → left = right
  | _, _, .declared occurrence isInstance, right, equal => by
      cases right with
      | declared occurrence' isInstance' =>
          simp only [derivationTerm] at equal
          obtain ⟨-, occurrenceEq, -⟩ := Name.declared.inj (NamedTerm.constant.inj equal)
          subst occurrenceEq
          rfl
      | application parameters' head' arguments' =>
          simp only [derivationTerm] at equal
          have spines := foldl_app_constant_injective (left := [])
            (right := derivationTerm head' :: derivationTerms arguments') equal
          simp at spines
      | @tuple _ headType' _ argumentTypes' head' _ arguments' =>
          simp only [derivationTerm] at equal
          rw [tupleTerm_cons_spine] at equal
          have spines := foldl_app_constant_injective (left := []) equal
          simp at spines
  | _, _, .application parameters head arguments, right, equal => by
      cases right with
      | declared occurrence' isInstance' =>
          simp only [derivationTerm] at equal
          have spines := foldl_app_constant_injective
            (left := derivationTerm head :: derivationTerms arguments) (right := []) equal
          simp at spines
      | application parameters' head' arguments' =>
          simp only [derivationTerm] at equal
          obtain ⟨names, terms⟩ := foldl_app_constant_injective
            (left := derivationTerm head :: derivationTerms arguments)
            (right := derivationTerm head' :: derivationTerms arguments') equal
          obtain ⟨parametersEq, -⟩ := Name.apply.inj names
          subst parametersEq
          simp only [List.cons.injEq] at terms
          rw [derivationTerm_injective head head' terms.1,
            derivationTerms_injective arguments arguments' terms.2]
      | @tuple _ headType' _ argumentTypes' head' _ arguments' =>
          simp only [derivationTerm] at equal
          rw [tupleTerm_cons_spine] at equal
          have spines := foldl_app_constant_injective
            (left := derivationTerm head :: derivationTerms arguments) equal
          simp at spines
  | _, _, @FirstOrderDerivation.tuple _ _ headType _ argumentTypes head _ arguments, right,
      equal => by
      cases right with
      | declared occurrence' isInstance' =>
          simp only [derivationTerm] at equal
          rw [tupleTerm_cons_spine] at equal
          have spines := foldl_app_constant_injective (right := []) equal
          simp at spines
      | application parameters' head' arguments' =>
          simp only [derivationTerm] at equal
          rw [tupleTerm_cons_spine] at equal
          have spines := foldl_app_constant_injective
            (right := derivationTerm head' :: derivationTerms arguments') equal
          simp at spines
      | tuple head' _ arguments' =>
          simp only [derivationTerm] at equal
          have terms := tupleTerm_injective
            (by simp [derivationTerms_length]) (by simp [derivationTerms_length]) equal
          simp only [List.cons.injEq] at terms
          rw [derivationTerm_injective head head' terms.1,
            derivationTerms_injective arguments arguments' terms.2]

theorem derivationTerms_injective {space : Space} :
    {arguments types : List Atom} → (left right : FirstOrderDerivations space arguments types) →
      derivationTerms left = derivationTerms right → left = right
  | _, _, .nil, .nil, _ => rfl
  | _, _, .cons head tail, .cons head' tail', equal => by
      simp only [derivationTerms, List.cons.injEq] at equal
      rw [derivationTerm_injective head head' equal.1, derivationTerms_injective tail tail' equal.2]

end

mutual

/-- **Every contract term of a judgment is the term of a derivation.** -/
theorem derivationTerm_surjective {space : Space} :
    {expression : Atom} → {term : ContractTerm} → Annotates expression term →
      ∀ {type : Atom}, ApplicativeTyped (nameType space) term (.base type) →
        ∃ derivation : FirstOrderDerivation space expression type, derivationTerm derivation = term
  | _, _, .declared atom occurrence instanceType, _, typed => by
      cases typed with
      | constant lookup =>
          obtain ⟨isInstance, typeEq⟩ := nameType_declared_eq_some_iff.mp lookup
          cases typeEq
          exact ⟨.declared occurrence isInstance, rfl⟩
  | _, _, @Annotates.application _ _ _ parameters _ _ head arguments, _, typed => by
      obtain ⟨_, rfl, headTyped, all⟩ := applicativeTyped_apply_iff.mp typed
      obtain ⟨headDerivation, headEq⟩ := derivationTerm_surjective head headTyped
      obtain ⟨argumentDerivations, argumentsEq⟩ := derivationTerms_surjective arguments all
      exact ⟨.application parameters headDerivation argumentDerivations, by
        simp only [derivationTerm, headEq, argumentsEq]⟩
  | _, _, @Annotates.tuple _ headType _ argumentTypes headTerm terms headNotArrow lengths
      head arguments, _, typed => by
      have termLengths : (headType :: argumentTypes).length = (headTerm :: terms).length := by
        simp [annotatesList_length arguments, lengths]
      obtain ⟨typeEq, all⟩ := (applicativeTyped_tupleTerm_iff termLengths).mp typed
      cases typeEq
      cases all with
      | cons headTyped rest =>
          obtain ⟨headDerivation, headEq⟩ := derivationTerm_surjective head headTyped
          obtain ⟨argumentDerivations, argumentsEq⟩ := derivationTerms_surjective arguments rest
          exact ⟨.tuple headDerivation headNotArrow argumentDerivations, by
            simp only [derivationTerm, headEq, argumentsEq]⟩

theorem derivationTerms_surjective {space : Space} :
    {arguments : List Atom} → {terms : List ContractTerm} → AnnotatesList arguments terms →
      ∀ {types : List Atom},
        List.Forall₂ (fun term type => ApplicativeTyped (nameType space) term (.base type))
          terms types →
        ∃ derivations : FirstOrderDerivations space arguments types,
          derivationTerms derivations = terms
  | _, _, .nil, _, all => by
      cases all
      exact ⟨.nil, rfl⟩
  | _, _, .cons head tail, _, all => by
      cases all with
      | cons headTyped rest =>
          obtain ⟨headDerivation, headEq⟩ := derivationTerm_surjective head headTyped
          obtain ⟨tailDerivations, tailEq⟩ := derivationTerms_surjective tail rest
          exact ⟨.cons headDerivation tailDerivations, by
            simp only [derivationTerms, headEq, tailEq]⟩

end

theorem derivationTerm_elaborates {space : Space} {expression type : Atom}
    (derivation : FirstOrderDerivation space expression type) :
    Elaborates (signature space) (derivationTerm derivation) (.base type) := by
  have typeOf : signatureType (signature space) = nameType space :=
    funext (signatureType_signature space)
  have typed := derivationTerm_typed derivation
  rw [← typeOf] at typed
  exact (elaborates_iff_applicativeTyped (derivationTerm_annotates derivation).applicative).mpr
    typed

/-- The contract terms of a judgment: the HOL terms of the expression that elaborate at the
base type of the type. -/
def JudgmentTerm (space : Space) (expression type : Atom) : Type :=
  { term : ContractTerm //
      Annotates expression term ∧ Elaborates (signature space) term (.base type) }

/-- **One contract term per derivation.**  The contract terms of a judgment correspond one to one
to the derivations of HE's first-order rule. -/
noncomputable def judgmentTermEquiv (space : Space) (expression type : Atom) :
    FirstOrderDerivation space expression type ≃ JudgmentTerm space expression type :=
  Equiv.ofBijective
    (fun derivation => ⟨derivationTerm derivation, derivationTerm_annotates derivation,
      derivationTerm_elaborates derivation⟩)
    ⟨fun left right equal => derivationTerm_injective left right (congrArg Subtype.val equal),
      fun ⟨term, annotates, elaborates⟩ => by
        have typeOf : signatureType (signature space) = nameType space :=
          funext (signatureType_signature space)
        have typed := (elaborates_iff_applicativeTyped annotates.applicative).mp elaborates
        rw [typeOf] at typed
        obtain ⟨derivation, termEq⟩ := derivationTerm_surjective annotates typed
        exact ⟨derivation, Subtype.ext termEq⟩⟩

/-! ### Derivations per declaration revision -/

theorem SameDeclarations.symm {space other : Space} (same : SameDeclarations space other) :
    SameDeclarations other space :=
  fun atom => (same atom).symm

theorem instance_of_sameDeclarations {space other : Space} (same : SameDeclarations space other)
    {atom type : Atom} {occurrence : Nat} (isInstance : Instance space atom occurrence type) :
    Instance other atom occurrence type := by
  unfold Instance at isInstance ⊢
  rw [← same atom]
  exact isInstance

mutual

/-- A derivation in one space is a derivation in any space with the same declarations. -/
def FirstOrderDerivation.transport {space other : Space} (same : SameDeclarations space other) :
    {expression type : Atom} → FirstOrderDerivation space expression type →
      FirstOrderDerivation other expression type
  | _, _, .declared occurrence isInstance =>
      .declared occurrence (instance_of_sameDeclarations same isInstance)
  | _, _, .application parameters head arguments =>
      .application parameters (FirstOrderDerivation.transport same head)
        (FirstOrderDerivations.transport same arguments)
  | _, _, .tuple head headNotArrow arguments =>
      .tuple (FirstOrderDerivation.transport same head) headNotArrow
        (FirstOrderDerivations.transport same arguments)

def FirstOrderDerivations.transport {space other : Space} (same : SameDeclarations space other) :
    {arguments types : List Atom} → FirstOrderDerivations space arguments types →
      FirstOrderDerivations other arguments types
  | _, _, .nil => .nil
  | _, _, .cons head tail =>
      .cons (FirstOrderDerivation.transport same head) (FirstOrderDerivations.transport same tail)

end

mutual

theorem derivationTerm_transport {space other : Space} (same : SameDeclarations space other) :
    {expression type : Atom} → (derivation : FirstOrderDerivation space expression type) →
      derivationTerm (FirstOrderDerivation.transport same derivation) = derivationTerm derivation
  | _, _, .declared _ _ => rfl
  | _, _, .application _ head arguments => by
      simp only [FirstOrderDerivation.transport, derivationTerm, derivationTerm_transport same head,
        derivationTerms_transport same arguments]
  | _, _, .tuple head _ arguments => by
      simp only [FirstOrderDerivation.transport, derivationTerm, derivationTerm_transport same head,
        derivationTerms_transport same arguments]

theorem derivationTerms_transport {space other : Space} (same : SameDeclarations space other) :
    {arguments types : List Atom} → (derivations : FirstOrderDerivations space arguments types) →
      derivationTerms (FirstOrderDerivations.transport same derivations) =
        derivationTerms derivations
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
      simp only [FirstOrderDerivations.transport, derivationTerms,
        derivationTerm_transport same head, derivationTerms_transport same tail]

end

/-- **A cache keeps its multiplicity across revisions that keep the declarations.**  The
derivations of a judgment in two spaces with the same declarations correspond one to one, and
corresponding derivations have the same contract term. -/
def derivationTransport {space other : Space} (same : SameDeclarations space other)
    (expression type : Atom) :
    FirstOrderDerivation space expression type ≃ FirstOrderDerivation other expression type where
  toFun := FirstOrderDerivation.transport same
  invFun := FirstOrderDerivation.transport same.symm
  left_inv derivation := derivationTerm_injective _ _ (by
    rw [derivationTerm_transport, derivationTerm_transport])
  right_inv derivation := derivationTerm_injective _ _ (by
    rw [derivationTerm_transport, derivationTerm_transport])

/-! ### Skeletons -/

/-- The shape of a derivation: the declaration occurrence of each declared leaf and the rule of
each expression, without instances. -/
inductive Skeleton where
  | declared (occurrence : Nat)
  | application (head : Skeleton) (arguments : List Skeleton)
  | tuple (head : Skeleton) (arguments : List Skeleton)

mutual

def FirstOrderDerivation.skeleton {space : Space} :
    {expression type : Atom} → FirstOrderDerivation space expression type → Skeleton
  | _, _, .declared occurrence _ => .declared occurrence
  | _, _, .application _ head arguments =>
      .application (FirstOrderDerivation.skeleton head) (FirstOrderDerivations.skeletons arguments)
  | _, _, .tuple head _ arguments =>
      .tuple (FirstOrderDerivation.skeleton head) (FirstOrderDerivations.skeletons arguments)

def FirstOrderDerivations.skeletons {space : Space} :
    {arguments types : List Atom} → FirstOrderDerivations space arguments types → List Skeleton
  | _, _, .nil => []
  | _, _, .cons head tail =>
      FirstOrderDerivation.skeleton head :: FirstOrderDerivations.skeletons tail

end

/-- Every declaration of the space is variable-free. -/
def GroundDeclarations (space : Space) : Prop :=
  ∀ atom, ∀ scheme ∈ declarations space atom, TypeSubst.typeVars scheme = []

mutual

/-- **On variable-free declarations a skeleton determines its derivation and its type.** -/
theorem skeleton_determines {space : Space} (ground : GroundDeclarations space) :
    {expression left right : Atom} → (leftDerivation : FirstOrderDerivation space expression left) →
      (rightDerivation : FirstOrderDerivation space expression right) →
      FirstOrderDerivation.skeleton leftDerivation = FirstOrderDerivation.skeleton rightDerivation →
        left = right ∧ derivationTerm leftDerivation = derivationTerm rightDerivation
  | _, _, _, .declared occurrence isInstance, rightDerivation, equal => by
      cases rightDerivation with
      | declared occurrence' isInstance' =>
          simp only [FirstOrderDerivation.skeleton, Skeleton.declared.injEq] at equal
          subst equal
          obtain ⟨scheme, found, leftInstance⟩ := isInstance
          obtain ⟨scheme', found', rightInstance⟩ := isInstance'
          rw [found] at found'
          cases found'
          have groundScheme := ground _ scheme (List.mem_of_getElem? found)
          have leftEq := typeInstance_of_ground groundScheme leftInstance
          have rightEq := typeInstance_of_ground groundScheme rightInstance
          subst leftEq
          subst rightEq
          exact ⟨rfl, rfl⟩
      | application => simp [FirstOrderDerivation.skeleton] at equal
      | tuple => simp [FirstOrderDerivation.skeleton] at equal
  | _, _, _, .application parameters head arguments, rightDerivation, equal => by
      cases rightDerivation with
      | declared => simp [FirstOrderDerivation.skeleton] at equal
      | application parameters' head' arguments' =>
          simp only [FirstOrderDerivation.skeleton, Skeleton.application.injEq] at equal
          obtain ⟨headTypes, headTerms⟩ := skeleton_determines ground head head' equal.1
          obtain ⟨parametersEq, resultEq⟩ := arrowAtom_injective headTypes
          subst parametersEq
          subst resultEq
          obtain ⟨_, argumentTerms⟩ := skeletons_determine ground arguments arguments' equal.2
          exact ⟨rfl, by simp only [derivationTerm, headTerms, argumentTerms]⟩
      | tuple => simp [FirstOrderDerivation.skeleton] at equal
  | _, _, _, .tuple head _ arguments, rightDerivation, equal => by
      cases rightDerivation with
      | declared => simp [FirstOrderDerivation.skeleton] at equal
      | application => simp [FirstOrderDerivation.skeleton] at equal
      | tuple head' _ arguments' =>
          simp only [FirstOrderDerivation.skeleton, Skeleton.tuple.injEq] at equal
          obtain ⟨headTypes, headTerms⟩ := skeleton_determines ground head head' equal.1
          obtain ⟨argumentTypes, argumentTerms⟩ :=
            skeletons_determine ground arguments arguments' equal.2
          subst headTypes
          subst argumentTypes
          exact ⟨rfl, by simp only [derivationTerm, headTerms, argumentTerms]⟩

theorem skeletons_determine {space : Space} (ground : GroundDeclarations space) :
    {arguments left right : List Atom} →
      (leftDerivations : FirstOrderDerivations space arguments left) →
      (rightDerivations : FirstOrderDerivations space arguments right) →
      FirstOrderDerivations.skeletons leftDerivations =
          FirstOrderDerivations.skeletons rightDerivations →
        left = right ∧ derivationTerms leftDerivations = derivationTerms rightDerivations
  | _, _, _, .nil, .nil, _ => ⟨rfl, rfl⟩
  | _, _, _, .cons head tail, .cons head' tail', equal => by
      simp only [FirstOrderDerivations.skeletons, List.cons.injEq] at equal
      obtain ⟨typeEq, termEq⟩ := skeleton_determines ground head head' equal.1
      obtain ⟨typesEq, termsEq⟩ := skeletons_determine ground tail tail' equal.2
      exact ⟨by rw [typeEq, typesEq], by simp only [derivationTerms, termEq, termsEq]⟩

end

/-- On variable-free declarations, derivations of one judgment with the same skeleton are
equal. -/
theorem derivation_eq_of_skeleton {space : Space} (ground : GroundDeclarations space)
    {expression type : Atom} (left right : FirstOrderDerivation space expression type)
    (equal : FirstOrderDerivation.skeleton left = FirstOrderDerivation.skeleton right) :
    left = right :=
  derivationTerm_injective left right (skeleton_determines ground left right equal).2

/-- A space whose annotations are variable-free has variable-free declarations. -/
theorem groundDeclarations_ofList {atoms : List Atom}
    (ground : ∀ subject type, Atom.expression [.symbol ":", subject, type] ∈ atoms →
      TypeSubst.typeVars type = []) :
    GroundDeclarations (Space.ofList atoms) := by
  have annotated : ∀ subject scheme, scheme ∈ getAnnotatedTypes (Space.ofList atoms) subject →
      TypeSubst.typeVars scheme = [] := by
    intro subject scheme found
    unfold getAnnotatedTypes at found
    rw [List.mem_filterMap] at found
    obtain ⟨annotation, inAtoms, picked⟩ := found
    split at picked
    · next annotatedAtom annotatedType =>
        split at picked
        · simp only [Option.some.injEq] at picked
          subst picked
          exact ground annotatedAtom annotatedType inAtoms
        · cases picked
    · cases picked
  intro atom scheme member
  cases atom with
  | grounded value =>
      simp only [declarations, List.mem_singleton] at member
      subst member
      cases value <;> rfl
  | var _ => simp [declarations] at member
  | symbol name => exact annotated _ _ member
  | expression atoms' =>
      cases atoms' with
      | nil => simp [declarations] at member
      | cons head rest => exact annotated _ _ member

/-! ### Controls -/

namespace Multiplicity

private theorem contract (name : String) (notReserved : name ∉ reservedTypeNames := by decide) :
    ContractType (.symbol name) :=
  contractType_symbol notReserved

abbrev rType : Atom := .symbol "R"
abbrev b1 : Atom := .symbol "B1"
abbrev b2 : Atom := .symbol "B2"

/-- `(: h (-> B1 R))`, `(: h (-> B2 R))`, `(: b B1)` and `(: b B2)`. -/
def hSpace : Space :=
  Space.ofList
    [SpecBoundary.annotation "h" (arrowAtom [b1] rType),
     SpecBoundary.annotation "h" (arrowAtom [b2] rType),
     SpecBoundary.annotation "b" b1,
     SpecBoundary.annotation "b" b2]

/-- `(h b)`. -/
abbrev hb : Atom := .expression [.symbol "h", .symbol "b"]

theorem hSpace_ground : GroundDeclarations hSpace := by
  apply groundDeclarations_ofList
  intro subject type member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with equal | equal | equal | equal <;> cases equal <;> rfl

private theorem arrowContract (parameter : String)
    (notReserved : parameter ∉ reservedTypeNames := by decide) :
    ContractType (arrowAtom [.symbol parameter] rType) := by
  have parameterContract := contract parameter notReserved
  have resultContract := contract "R"
  exact contractType_arrowAtom (by simp [parameterContract, resultContract])

/-- `h` through its first declaration, `b` through its first. -/
def first : FirstOrderDerivation hSpace hb rType :=
  .application [b1]
    (.declared 0 ⟨arrowAtom [b1] rType, by decide, typeInstance_self (arrowContract "B1")⟩)
    (.cons (.declared 0 ⟨b1, by decide, typeInstance_self (contract "B1")⟩) .nil)

/-- `h` through its second declaration, `b` through its second. -/
def second : FirstOrderDerivation hSpace hb rType :=
  .application [b2]
    (.declared 1 ⟨arrowAtom [b2] rType, by decide, typeInstance_self (arrowContract "B2")⟩)
    (.cons (.declared 1 ⟨b2, by decide, typeInstance_self (contract "B2")⟩) .nil)

theorem first_ne_second : first ≠ second := by
  intro equal
  have skeletons := congrArg FirstOrderDerivation.skeleton equal
  simp [first, second, FirstOrderDerivation.skeleton, FirstOrderDerivations.skeletons] at skeletons

/-- **`(h b)` has exactly two derivations at `R`**, so two contract terms: HE answers
`[R, R]`.  A cache of the types of `(h b)` without multiplicity would answer `[R]`. -/
theorem hb_derivations (derivation : FirstOrderDerivation hSpace hb rType) :
    derivation = first ∨ derivation = second := by
  suffices skeletons : FirstOrderDerivation.skeleton derivation =
        FirstOrderDerivation.skeleton first ∨
      FirstOrderDerivation.skeleton derivation = FirstOrderDerivation.skeleton second by
    rcases skeletons with equal | equal
    · exact .inl (derivation_eq_of_skeleton hSpace_ground _ _ equal)
    · exact .inr (derivation_eq_of_skeleton hSpace_ground _ _ equal)
  have headDeclarations : declarations hSpace (.symbol "h") =
      [arrowAtom [b1] rType, arrowAtom [b2] rType] := by decide
  have argumentDeclarations : declarations hSpace (.symbol "b") = [b1, b2] := by decide
  cases derivation with
  | declared occurrence isInstance =>
      exfalso
      obtain ⟨_, found, _⟩ := isInstance
      have none : declarations hSpace hb = [] := by decide
      simp [none] at found
  | application parameters head arguments =>
      cases arguments with
      | cons argument rest =>
          cases rest
          cases head with
          | declared headOccurrence headInstance =>
              cases argument with
              | declared argumentOccurrence argumentInstance =>
                  simp only [FirstOrderDerivation.skeleton, FirstOrderDerivations.skeletons, first,
                    second]
                  obtain ⟨headScheme, headFound, headTypeInstance⟩ := headInstance
                  obtain ⟨argumentScheme, argumentFound, argumentTypeInstance⟩ := argumentInstance
                  rw [headDeclarations] at headFound
                  rw [argumentDeclarations] at argumentFound
                  match headOccurrence, argumentOccurrence, headFound, argumentFound with
                  | 0, 0, _, _ => exact .inl rfl
                  | 1, 1, _, _ => exact .inr rfl
                  | 0, 1, headFound, argumentFound =>
                      exfalso
                      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
                        Option.some.injEq] at headFound argumentFound
                      subst headFound argumentFound
                      have headEq := typeInstance_of_ground rfl headTypeInstance
                      have argumentEq := typeInstance_of_ground rfl argumentTypeInstance
                      have typeEq := (List.cons.inj (arrowAtom_injective headEq).1).1
                      rw [typeEq] at argumentEq
                      exact absurd argumentEq (by decide)
                  | 1, 0, headFound, argumentFound =>
                      exfalso
                      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
                        Option.some.injEq] at headFound argumentFound
                      subst headFound argumentFound
                      have headEq := typeInstance_of_ground rfl headTypeInstance
                      have argumentEq := typeInstance_of_ground rfl argumentTypeInstance
                      have typeEq := (List.cons.inj (arrowAtom_injective headEq).1).1
                      rw [typeEq] at argumentEq
                      exact absurd argumentEq (by decide)
                  | _ + 2, _, headFound, _ => simp at headFound
                  | _, _ + 2, _, argumentFound => simp at argumentFound

/-- `(: g (-> B1 R))` twice and `(: b B1)`: the same declaration twice is two constants. -/
def gSpace : Space :=
  Space.ofList
    [SpecBoundary.annotation "g" (arrowAtom [b1] rType),
     SpecBoundary.annotation "g" (arrowAtom [b1] rType),
     SpecBoundary.annotation "b" b1]

/-- `(g b)` through each occurrence of the declaration of `g`. -/
def throughOccurrence (occurrence : Nat)
    (found : (declarations gSpace (.symbol "g"))[occurrence]? = some (arrowAtom [b1] rType)) :
    FirstOrderDerivation gSpace (.expression [.symbol "g", .symbol "b"]) rType :=
  .application [b1]
    (.declared occurrence ⟨arrowAtom [b1] rType, found, typeInstance_self (arrowContract "B1")⟩)
    (.cons (.declared 0 ⟨b1, by decide, typeInstance_self (contract "B1")⟩) .nil)

/-- **A repeated declaration keeps its occurrence identity**: `(g b)` has two derivations,
and HE answers `[R, R]`. -/
theorem g_occurrences_differ :
    throughOccurrence 0 (by decide) ≠ throughOccurrence 1 (by decide) := by
  intro equal
  have skeletons := congrArg FirstOrderDerivation.skeleton equal
  simp [throughOccurrence, FirstOrderDerivation.skeleton,
    FirstOrderDerivations.skeletons] at skeletons

/-- `(: nil (List $a))` and `(: len (-> (List $b) Nat))`. -/
def lenSpace : Space :=
  Space.ofList
    [SpecBoundary.annotation "nil" (.expression [.symbol "List", .var "a"]),
     SpecBoundary.annotation "len"
       (arrowAtom [.expression [.symbol "List", .var "b"]] (.symbol "Nat"))]

/-- `(len nil)`. -/
abbrev lenNil : Atom := .expression [.symbol "len", .symbol "nil"]

private theorem listContract (element : String)
    (notReserved : element ∉ reservedTypeNames := by decide) :
    ContractType (.expression [.symbol "List", .symbol element]) := by
  refine contractType_of_groundFirstOrder ⟨?_, rfl⟩
  refine Schematic.reservedFree_expression_iff.mpr ?_
  intro atom member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact Schematic.reservedFree_symbol_iff.mpr (by decide)
  · exact Schematic.reservedFree_symbol_iff.mpr notReserved

/-- The valuation of one type variable. -/
def only (name : String) (value : Atom) : String → Atom :=
  fun other => if other = name then value else .var other

theorem only_typeAtom {name : String} {value : Atom} (atomic : TypeAtom value) (other : String) :
    TypeAtom (only name value other) := by
  unfold only
  split
  · exact atomic
  · exact .var other

/-- `(len nil)` at `Nat` through `nil : (List element)`. -/
def lenAt (element : String) (notReserved : element ∉ reservedTypeNames := by decide) :
    FirstOrderDerivation lenSpace lenNil (.symbol "Nat") :=
  .application [.expression [.symbol "List", .symbol element]]
    (.declared 0 ⟨arrowAtom [.expression [.symbol "List", .var "b"]] (.symbol "Nat"), by decide,
      by
        have listElement := listContract element notReserved
        have natContract := contract "Nat"
        exact contractType_arrowAtom (by simp [listElement, natContract]),
      only "b" (.symbol element), only_typeAtom (contract element notReserved).1,
      by simp [only, applyTypeValuation, arrowAtom]⟩)
    (.cons (.declared 0 ⟨.expression [.symbol "List", .var "a"], by decide,
      listContract element notReserved, only "a" (.symbol element),
      only_typeAtom (contract element notReserved).1, by simp [only, applyTypeValuation]⟩) .nil)

/-- **Negative control: with a type variable that no result fixes, one skeleton has many
derivations.**  `(len nil)` has one skeleton, and HE answers `[Nat]` once, but a derivation at
`Nat` for each element type of the list.  There a cache keeps one principal scheme per skeleton,
not one ground type per derivation. -/
theorem lenNil_one_skeleton_two_derivations :
    FirstOrderDerivation.skeleton (lenAt "Nat") = FirstOrderDerivation.skeleton (lenAt "Bool") ∧
      lenAt "Nat" ≠ lenAt "Bool" := by
  refine ⟨rfl, ?_⟩
  intro equal
  have terms := congrArg derivationTerm equal
  simp [lenAt, derivationTerm, derivationTerms] at terms

theorem lenSpace_not_ground : ¬GroundDeclarations lenSpace := by
  intro ground
  have := ground (.symbol "nil") (.expression [.symbol "List", .var "a"]) (by decide)
  simp [TypeSubst.typeVars, TypeSubst.typeVarsList] at this


/-! #### Two answers through a type variable, and tuples beside an application -/

/-- `(: f (-> $t R))`, `(: b B1)` and `(: b B2)`. -/
def fSpace : Space :=
  Space.ofList
    [SpecBoundary.annotation "f" (arrowAtom [.var "t"] rType),
     SpecBoundary.annotation "b" b1,
     SpecBoundary.annotation "b" b2]

/-- `(f b)`. -/
abbrev fb : Atom := .expression [.symbol "f", .symbol "b"]

/-- `(f b)` at `R` through the declaration of `b` at `occurrence`, of type `parameter`. -/
def fThrough (occurrence : Nat) (parameter : String)
    (found : (declarations fSpace (.symbol "b"))[occurrence]? = some (.symbol parameter))
    (notReserved : parameter ∉ reservedTypeNames := by decide) :
    FirstOrderDerivation fSpace fb rType :=
  .application [.symbol parameter]
    (.declared 0 ⟨arrowAtom [.var "t"] rType, by decide, arrowContract parameter notReserved,
      only "t" (.symbol parameter), only_typeAtom (contract parameter notReserved).1,
      by simp [only, applyTypeValuation, arrowAtom]⟩)
    (.cons (.declared occurrence ⟨.symbol parameter, found,
      typeInstance_self (contract parameter notReserved)⟩) .nil)

/-- **`(f b)` has exactly two derivations at `R`**, one through each declaration of `b`: HE
answers `[R, R]`. -/
theorem fb_derivations (derivation : FirstOrderDerivation fSpace fb rType) :
    derivation = fThrough 0 "B1" (by decide) ∨ derivation = fThrough 1 "B2" (by decide) := by
  suffices terms : derivationTerm derivation = derivationTerm (fThrough 0 "B1" (by decide)) ∨
      derivationTerm derivation = derivationTerm (fThrough 1 "B2" (by decide)) by
    rcases terms with equal | equal
    · exact .inl (derivationTerm_injective _ _ equal)
    · exact .inr (derivationTerm_injective _ _ equal)
  have headDeclarations : declarations fSpace (.symbol "f") = [arrowAtom [.var "t"] rType] := by
    decide
  have argumentDeclarations : declarations fSpace (.symbol "b") = [b1, b2] := by decide
  cases derivation with
  | declared occurrence isInstance =>
      exfalso
      obtain ⟨_, found, _⟩ := isInstance
      have none : declarations fSpace fb = [] := by decide
      simp [none] at found
  | application parameters head arguments =>
      cases arguments with
      | cons argument rest =>
          cases rest
          cases head with
          | declared headOccurrence headInstance =>
              cases argument with
              | declared argumentOccurrence argumentInstance =>
                  obtain ⟨headScheme, headFound, _⟩ := headInstance
                  obtain ⟨argumentScheme, argumentFound, argumentTypeInstance⟩ := argumentInstance
                  rw [headDeclarations] at headFound
                  rw [argumentDeclarations] at argumentFound
                  match headOccurrence, argumentOccurrence, headFound, argumentFound with
                  | 0, 0, _, argumentFound =>
                      simp only [List.getElem?_cons_zero, Option.some.injEq] at argumentFound
                      subst argumentFound
                      have typeEq := typeInstance_of_ground rfl argumentTypeInstance
                      subst typeEq
                      exact .inl rfl
                  | 0, 1, _, argumentFound =>
                      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
                        Option.some.injEq] at argumentFound
                      subst argumentFound
                      have typeEq := typeInstance_of_ground rfl argumentTypeInstance
                      subst typeEq
                      exact .inr rfl
                  | _ + 1, _, headFound, _ => simp at headFound
                  | _, _ + 2, _, argumentFound => simp at argumentFound

/-- `(: v V)`, `(: v (-> B1 R))`, `(: b B1)` and `(: b B2)`. -/
def vSpace : Space :=
  Space.ofList
    [SpecBoundary.annotation "v" (.symbol "V"),
     SpecBoundary.annotation "v" (arrowAtom [b1] rType),
     SpecBoundary.annotation "b" b1,
     SpecBoundary.annotation "b" b2]

/-- `(v b)`. -/
abbrev vb : Atom := .expression [.symbol "v", .symbol "b"]

/-- **A head with a value type and an arrow type has both readings.**  `(v b)` is the tuple
`(V B1)` and the tuple `(V B2)` through `v : V`, and has type `R` through `v : (-> B1 R)`: HE
answers `[(V B1), (V B2), R]`. -/
theorem vb_typings :
    Typed vSpace vb (.expression [.symbol "V", b1]) ∧
      Typed vSpace vb (.expression [.symbol "V", b2]) ∧ Typed vSpace vb rType := by
  have vValue : FirstOrderType vSpace (.symbol "v") (.symbol "V") :=
    .declared (occurrence := 0) ⟨.symbol "V", by decide, typeInstance_self (contract "V")⟩
  have bFirst : FirstOrderType vSpace (.symbol "b") b1 :=
    .declared (occurrence := 0) ⟨b1, by decide, typeInstance_self (contract "B1")⟩
  have bSecond : FirstOrderType vSpace (.symbol "b") b2 :=
    .declared (occurrence := 1) ⟨b2, by decide, typeInstance_self (contract "B2")⟩
  have notArrow : ¬ArrowShaped (.symbol "V") := by
    rintro ⟨_, equal⟩
    cases equal
  refine ⟨typed_iff_firstOrder.mpr (.tuple vValue notArrow (.cons bFirst .nil)),
    typed_iff_firstOrder.mpr (.tuple vValue notArrow (.cons bSecond .nil)),
    typed_iff_firstOrder.mpr (.application (parameters := [b1]) ?_ (.cons bFirst .nil))⟩
  exact .declared (occurrence := 1) ⟨arrowAtom [b1] rType, by decide,
    typeInstance_self (arrowContract "B1")⟩

end Multiplicity

#print axioms typed_iff_of_sameDeclarations
#print axioms typed_add_iff
#print axioms declaration_changes_judgment
#print axioms typed_add_subtypeDeclaration_iff
#print axioms subtype_edge_outside_declarations
#print axioms principal_of_exact
#print axioms NativeChecker.decides
#print axioms NativeChecker.same_instances
#print axioms exactChecker
#print axioms generalChecker_not_admitted
#print axioms typed_replace_arguments
#print axioms call_type_determined
#print axioms IfEmpty.if_not_determined
#print axioms IfEmpty.ifCall_empty
#print axioms IfEmpty.ifCall_nat
#print axioms IfEmpty.absurd_ifCall
#print axioms IfEmpty.absurd_z_untyped
#print axioms WrongBody.static_type_not_body_type
#print axioms undefined_result_untyped
#print axioms typed_iff_derivation
#print axioms derivationTerm_injective
#print axioms derivationTerm_surjective
#print axioms judgmentTermEquiv
#print axioms derivationTerm_transport
#print axioms derivationTransport
#print axioms skeleton_determines
#print axioms derivation_eq_of_skeleton
#print axioms Multiplicity.hb_derivations
#print axioms Multiplicity.first_ne_second
#print axioms Multiplicity.g_occurrences_differ
#print axioms Multiplicity.lenNil_one_skeleton_two_derivations
#print axioms Multiplicity.lenSpace_not_ground
#print axioms Multiplicity.fb_derivations
#print axioms Multiplicity.vb_typings

end Mettapedia.Languages.MeTTa.HE.HOLContract

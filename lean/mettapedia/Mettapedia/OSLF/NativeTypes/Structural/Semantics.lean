import Mettapedia.OSLF.NativeTypes.Structural.Logic
import Mettapedia.OSLF.Framework.SortedInstrumentCongruenceLogic

open Mettapedia.OSLF.Framework

/-!
# Equation-invariant structural and propositional meanings

Structural splitting uses the same equation-class decomposition as the
sorted instrument logic, while retaining the authored binding representations
of a `LanguageDef`. Free binary constructors give positional splitting.
Commutativity and associativity yield the corresponding separating laws when
they are actual laws of the equation relation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Structural

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- The semantic binary split before fixing formulas for its two parts. -/
def SplitHolds (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (equation : Pattern → Pattern → Prop)
    (former : Former) (first second : Pattern → Prop) (term : Pattern) : Prop :=
  former ∈ structuralFormers language ∧
    ∃ value : ConstructorValue language free bound former.declaration,
      equation term value.pattern ∧
      ∃ left right, value.arguments = [left, right] ∧ first left ∧ second right

theorem split_equation_invariant {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {equation : Pattern → Pattern → Prop}
    (laws : Equivalence equation) (former : Former) (first second : Pattern → Prop)
    {left right : Pattern} (related : equation left right) :
    SplitHolds language free bound equation former first second left ↔
      SplitHolds language free bound equation former first second right := by
  constructor
  · rintro ⟨member, value, witness, parts⟩
    exact ⟨member, value, laws.trans (laws.symm related) witness, parts⟩
  · rintro ⟨member, value, witness, parts⟩
    exact ⟨member, value, laws.trans related witness, parts⟩

/-- Positional splitting for an ordinary binary constructor with syntactic
equality. The argument order is the authored order. -/
theorem free_positional_split {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {former : Former}
    (member : former ∈ structuralFormers language)
    (ordinary : ¬ UsesBareCollection former.declaration)
    (first second : Pattern → Prop) (term : Pattern) :
    SplitHolds language free bound Eq former first second term ↔
      ∃ left right, term = .apply former.declaration.label [left, right] ∧
        ArgumentsHaveTypes language free bound [left, right] former.declaration.params ∧
        first left ∧ second right := by
  constructor
  · rintro ⟨_, value, equation, left, right, arguments, firstHolds, secondHolds⟩
    cases value with
    | ordinary actual _ typed =>
        change actual = [left, right] at arguments
        subst actual
        exact ⟨left, right, equation, typed, firstHolds, secondHolds⟩
    | collection parameterName kind elementType elements rest shape typed =>
        exact False.elim (ordinary ⟨parameterName, kind, elementType, shape⟩)
  · rintro ⟨left, right, equation, typed, firstHolds, secondHolds⟩
    exact ⟨member, .ordinary [left, right] ordinary typed, equation,
      left, right, rfl, firstHolds, secondHolds⟩

/-- Meaning is independent of elaboration: it reads the declaration at a
structural index and uses its actual argument carriers. -/
def Holds (language : LanguageDef) (free : FreeTypeContext) (bound : List TypeExpr)
    (equation : TypeExpr → Pattern → Pattern → Prop)
    (atom : TypeExpr → Nat → Pattern → Prop) (expected : TypeExpr) : Formula → Pattern → Prop
  | .top, _ => True
  | .bottom, _ => False
  | .atom index, term => atom expected index term
  | .conj left right, term =>
      Holds language free bound equation atom expected left term ∧
      Holds language free bound equation atom expected right term
  | .disj left right, term =>
      Holds language free bound equation atom expected left term ∨
      Holds language free bound equation atom expected right term
  | .imp left right, term =>
      Holds language free bound equation atom expected left term →
      Holds language free bound equation atom expected right term
  | .neg inner, term => ¬ Holds language free bound equation atom expected inner term
  | .root index, term =>
      ∃ declaration, language.terms[index]? = some declaration ∧
        expected = .base declaration.category ∧
        StructuralHolds language free bound (equation expected) ⟨index, declaration⟩ term
  | .split index left right, term =>
      ∃ declaration firstParam secondParam firstSort secondSort,
        language.terms[index]? = some declaration ∧
        expected = .base declaration.category ∧
        declaration.params = [firstParam, secondParam] ∧
        parameterType? firstParam = some firstSort ∧
        parameterType? secondParam = some secondSort ∧
        SplitHolds language free bound (equation expected) ⟨index, declaration⟩
          (Holds language free bound equation atom firstSort left)
          (Holds language free bound equation atom secondSort right) term
  | .spatial index left right, term =>
      ∃ declaration, language.terms[index]? = some declaration ∧
        expected = .base declaration.category ∧
        SpatialHolds language free bound (equation expected) ⟨index, declaration⟩
          (Holds language free bound equation atom expected left)
          (Holds language free bound equation atom expected right) term

theorem holds_equation_invariant {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {equation : TypeExpr → Pattern → Pattern → Prop}
    {atom : TypeExpr → Nat → Pattern → Prop}
    (laws : ∀ type, Equivalence (equation type))
    (atomInvariant : ∀ type index left right, equation type left right →
      (atom type index left ↔ atom type index right)) (formula : Formula) :
    ∀ type left right, equation type left right →
      (Holds language free bound equation atom type formula left ↔
        Holds language free bound equation atom type formula right) := by
  induction formula with
  | top => intro type left right related; exact Iff.rfl
  | bottom => intro type left right related; exact Iff.rfl
  | atom index => exact fun type left right related => atomInvariant type index left right related
  | conj left right ihLeft ihRight =>
      intro type first second related
      exact and_congr (ihLeft type first second related) (ihRight type first second related)
  | disj left right ihLeft ihRight =>
      intro type first second related
      exact or_congr (ihLeft type first second related) (ihRight type first second related)
  | imp left right ihLeft ihRight =>
      intro type first second related
      exact imp_congr (ihLeft type first second related) (ihRight type first second related)
  | neg inner ih =>
      intro type first second related
      exact not_congr (ih type first second related)
  | root index =>
      intro type left right related
      unfold Holds
      apply exists_congr
      intro declaration
      exact and_congr_right fun _ => and_congr_right fun _ =>
        structural_equation_invariant (laws type) ⟨index, declaration⟩ related
  | split index first second _ _ =>
      intro type left right related
      unfold Holds
      apply exists_congr
      intro declaration
      apply exists_congr
      intro firstParam
      apply exists_congr
      intro secondParam
      apply exists_congr
      intro firstSort
      apply exists_congr
      intro secondSort
      exact and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
        and_congr_right fun _ => and_congr_right fun _ =>
          split_equation_invariant (laws type) ⟨index, declaration⟩ _ _ related
  | spatial index first second _ _ =>
      intro type left right related
      unfold Holds
      apply exists_congr
      intro declaration
      exact and_congr_right fun _ => and_congr_right fun _ =>
        spatial_equation_invariant (laws type) ⟨index, declaration⟩ _ _ related

/-- Successful formation does not assert semantic truth. -/
theorem formed_bottom_is_false {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {equation : TypeExpr → Pattern → Pattern → Prop}
    {atom : TypeExpr → Nat → Pattern → Prop} (type : TypeExpr) (term : Pattern) :
    ¬ Holds language free bound equation atom type .bottom term := fun falsehood => falsehood

/-- The root query is exactly the generated former, once the declaration's
carrier has been checked. -/
theorem holds_root_exact {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {equation : TypeExpr → Pattern → Pattern → Prop}
    {atom : TypeExpr → Nat → Pattern → Prop} {index : Nat} {declaration : GrammarRule}
    (lookup : language.terms[index]? = some declaration) (term : Pattern) :
    Holds language free bound equation atom (.base declaration.category) (.root index) term ↔
      StructuralHolds language free bound (equation (.base declaration.category))
        ⟨index, declaration⟩ term := by
  simp [Holds, lookup]

theorem holds_split_exact {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {equation : TypeExpr → Pattern → Pattern → Prop}
    {atom : TypeExpr → Nat → Pattern → Prop} {index : Nat} {declaration : GrammarRule}
    {firstParam secondParam : TermParam} {firstSort secondSort : TypeExpr}
    (lookup : language.terms[index]? = some declaration)
    (arity : declaration.params = [firstParam, secondParam])
    (firstType : parameterType? firstParam = some firstSort)
    (secondType : parameterType? secondParam = some secondSort)
    (first second : Formula) (term : Pattern) :
    Holds language free bound equation atom (.base declaration.category)
        (.split index first second) term ↔
      SplitHolds language free bound (equation (.base declaration.category)) ⟨index, declaration⟩
        (Holds language free bound equation atom firstSort first)
        (Holds language free bound equation atom secondSort second) term := by
  simp [Holds, lookup, arity, firstType, secondType]

theorem holds_spatial_exact {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {equation : TypeExpr → Pattern → Pattern → Prop}
    {atom : TypeExpr → Nat → Pattern → Prop} {index : Nat} {declaration : GrammarRule}
    (lookup : language.terms[index]? = some declaration) (first second : Formula) (term : Pattern) :
    Holds language free bound equation atom (.base declaration.category)
      (.spatial index first second) term ↔
      SpatialHolds language free bound (equation (.base declaration.category)) ⟨index, declaration⟩
        (Holds language free bound equation atom (.base declaration.category) first)
        (Holds language free bound equation atom (.base declaration.category) second) term := by
  simp [Holds, lookup]

/-- A homogeneous ordinary binary declaration has no bare collection arm. -/
theorem binary_not_bare {declaration : GrammarRule} {first second : TermParam}
    (arity : declaration.params = [first, second]) : ¬ UsesBareCollection declaration := by
  rintro ⟨name, kind, elementType, bare⟩
  rw [arity] at bare
  cases bare

private theorem binary_typed_inv {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {declaration : GrammarRule} {sort : TypeExpr}
    {firstName secondName : String} {left right : Pattern}
    (arity : declaration.params = [.simple firstName sort, .simple secondName sort])
    (typed : ArgumentsHaveTypes language free bound [left, right] declaration.params) :
    HasType language free bound left sort ∧ HasType language free bound right sort := by
  rw [arity] at typed
  obtain ⟨first, rest⟩ := typed.simple_cons_inv
  obtain ⟨second, _⟩ := rest.simple_cons_inv
  exact ⟨first, second⟩

private theorem binary_typed {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {declaration : GrammarRule} {sort : TypeExpr}
    {firstName secondName : String} {left right : Pattern}
    (arity : declaration.params = [.simple firstName sort, .simple secondName sort])
    (first : HasType language free bound left sort) (second : HasType language free bound right sort) :
    ArgumentsHaveTypes language free bound [left, right] declaration.params := by
  rw [arity]
  exact .cons trivial rfl first (.cons trivial rfl second .nil)

/-- A binary split retains the typed pair independently of its equation
justification. This applies in every ambient binding context. -/
theorem binary_split_iff {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {equation : Pattern → Pattern → Prop} {former : Former}
    {firstName secondName : String}
    (member : former ∈ structuralFormers language)
    (arity : former.declaration.params =
      [.simple firstName (.base former.declaration.category),
        .simple secondName (.base former.declaration.category)])
    (first second : Pattern → Prop) (term : Pattern) :
    SplitHolds language free bound equation former first second term ↔
      ∃ left right, equation term (.apply former.declaration.label [left, right]) ∧
        HasType language free bound left (.base former.declaration.category) ∧
        HasType language free bound right (.base former.declaration.category) ∧
        first left ∧ second right := by
  have ordinary := binary_not_bare arity
  constructor
  · rintro ⟨_, value, related, left, right, parts, firstHolds, secondHolds⟩
    cases value with
    | collection name kind elementType elements rest shape typed =>
        exact False.elim (ordinary ⟨name, kind, elementType, shape⟩)
    | ordinary actual _ typed =>
        change actual = [left, right] at parts
        subst actual
        obtain ⟨leftTyped, rightTyped⟩ := binary_typed_inv arity typed
        exact ⟨left, right, related, leftTyped, rightTyped, firstHolds, secondHolds⟩
  · rintro ⟨left, right, related, leftTyped, rightTyped, firstHolds, secondHolds⟩
    exact ⟨member, .ordinary [left, right] ordinary (binary_typed arity leftTyped rightTyped),
      related, left, right, rfl, firstHolds, secondHolds⟩

/-- The equation-class split of a homogeneous binary constructor is symmetric
when commutativity is an actual equation law on every well-typed pair. -/
theorem ac_split_commutative {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {equation : Pattern → Pattern → Prop} {former : Former}
    {firstName secondName : String}
    (arity : former.declaration.params =
      [.simple firstName (.base former.declaration.category),
        .simple secondName (.base former.declaration.category)])
    (laws : Equivalence equation)
    (commutative : ∀ left right,
      HasType language free bound left (.base former.declaration.category) →
      HasType language free bound right (.base former.declaration.category) →
      equation (.apply former.declaration.label [left, right])
        (.apply former.declaration.label [right, left]))
    (first second : Pattern → Prop) (term : Pattern) :
    SplitHolds language free bound equation former first second term ↔
      SplitHolds language free bound equation former second first term := by
  have forward : ∀ first second : Pattern → Prop,
      SplitHolds language free bound equation former first second term →
        SplitHolds language free bound equation former second first term := by
    intro first second
    rintro ⟨member, value, related, left, right, parts, firstHolds, secondHolds⟩
    have ordinary := binary_not_bare arity
    cases value with
    | collection name kind elementType elements rest shape typed =>
        exact False.elim (ordinary ⟨name, kind, elementType, shape⟩)
    | ordinary actual _ typed =>
        change actual = [left, right] at parts
        subst actual
        obtain ⟨leftTyped, rightTyped⟩ := binary_typed_inv arity typed
        refine ⟨member, .ordinary [right, left] ordinary
          (binary_typed arity rightTyped leftTyped), ?_, right, left, rfl,
          secondHolds, firstHolds⟩
        exact laws.trans related (commutative left right leftTyped rightTyped)
  exact ⟨forward first second, forward second first⟩

/-- Associativity of the genuine separating interpretation follows from
congruence and the authored association law, rather than parse-tree reassociation.
-/
theorem ac_split_associative {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {equation : Pattern → Pattern → Prop} {former : Former}
    {firstName secondName : String}
    (member : former ∈ structuralFormers language)
    (arity : former.declaration.params =
      [.simple firstName (.base former.declaration.category),
        .simple secondName (.base former.declaration.category)])
    (laws : Equivalence equation)
    (congruent : ∀ first first' second second', equation first first' → equation second second' →
      equation (.apply former.declaration.label [first, second])
        (.apply former.declaration.label [first', second']))
    (associative : ∀ first second third,
      HasType language free bound first (.base former.declaration.category) →
      HasType language free bound second (.base former.declaration.category) →
      HasType language free bound third (.base former.declaration.category) →
      equation (.apply former.declaration.label
          [first, .apply former.declaration.label [second, third]])
        (.apply former.declaration.label
          [.apply former.declaration.label [first, second], third]))
    (first second third : Pattern → Prop) (term : Pattern) :
    SplitHolds language free bound equation former first
        (SplitHolds language free bound equation former second third) term ↔
      SplitHolds language free bound equation former
        (SplitHolds language free bound equation former first second) third term := by
  have declarationMember : former.declaration ∈ language.terms :=
    List.mem_of_getElem? ((mem_structuralFormers_iff language former).mp member)
  have pairTyped : ∀ left right,
      HasType language free bound left (.base former.declaration.category) →
      HasType language free bound right (.base former.declaration.category) →
      HasType language free bound (.apply former.declaration.label [left, right])
        (.base former.declaration.category) := by
    intro left right leftTyped rightTyped
    exact .constructor declarationMember (binary_not_bare arity)
      (binary_typed arity leftTyped rightTyped)
  constructor
  · intro split
    obtain ⟨left, remainder, outerEquation, leftTyped, _, firstHolds, inner⟩ :=
      (binary_split_iff member arity first _ term).mp split
    obtain ⟨middle, right, innerEquation, middleTyped, rightTyped, secondHolds, thirdHolds⟩ :=
      (binary_split_iff member arity second third remainder).mp inner
    apply (binary_split_iff member arity _ third term).mpr
    refine ⟨.apply former.declaration.label [left, middle], right, ?_,
      pairTyped left middle leftTyped middleTyped, rightTyped, ?_, thirdHolds⟩
    · exact laws.trans outerEquation
        (laws.trans (congruent _ _ _ _ (laws.refl left) innerEquation)
          (associative left middle right leftTyped middleTyped rightTyped))
    · exact (binary_split_iff member arity first second _).mpr
        ⟨left, middle, laws.refl _, leftTyped, middleTyped, firstHolds, secondHolds⟩
  · intro split
    obtain ⟨remainder, right, outerEquation, _, rightTyped, inner, thirdHolds⟩ :=
      (binary_split_iff member arity _ third term).mp split
    obtain ⟨left, middle, innerEquation, leftTyped, middleTyped, firstHolds, secondHolds⟩ :=
      (binary_split_iff member arity first second remainder).mp inner
    apply (binary_split_iff member arity first _ term).mpr
    refine ⟨left, .apply former.declaration.label [middle, right], ?_,
      leftTyped, pairTyped middle right middleTyped rightTyped, firstHolds, ?_⟩
    · exact laws.trans outerEquation
        (laws.trans (congruent _ _ _ _ innerEquation (laws.refl right))
          (laws.symm (associative left middle right leftTyped middleTyped rightTyped)))
    · exact (binary_split_iff member arity second third _).mpr
        ⟨middle, right, laws.refl _, middleTyped, rightTyped, secondHolds, thirdHolds⟩

/-! The existing sorted structural interpretation is the same mathematical
decomposition discipline. Its established equation response theorem remains
available for every admitted sorted constructor, including changing roots. -/

theorem sorted_structural_decomposition_invariant
    {signature : Mettapedia.OSLF.SortedConstructors.Signature}
    {theory : Mettapedia.OSLF.SortedConstructors.Congruence signature}
    (base : Mettapedia.OSLF.Framework.SortedInstrumentCongruence.BaseSystem theory)
    (constructor : signature.Constructor)
    (arguments : (position : Fin (signature.arity constructor)) →
      Mettapedia.OSLF.Framework.SortedInstrumentCongruence.Formula signature
        base.Atom base.Label (signature.input constructor position))
    {left right : Mettapedia.OSLF.SortedConstructors.Term signature (signature.output constructor)}
    (related : theory.Rel left right) :
    Mettapedia.OSLF.Framework.SortedInstrumentCongruence.Holds base (.node constructor arguments) left ↔
      Mettapedia.OSLF.Framework.SortedInstrumentCongruence.Holds base (.node constructor arguments) right :=
  Mettapedia.OSLF.Framework.SortedInstrumentCongruence.holds_resp base
    (.node constructor arguments) related

end Mettapedia.OSLF.NativeTypes.Structural

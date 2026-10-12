import Mettapedia.Languages.HOLLight.FirstOrder.Calculus
import Mettapedia.Languages.OpenTheory.CoreTerm

/-!
# Reading encoded syntax back from rule patterns

A rule of the calculus builds patterns from labels and metavariables. When such a pattern is
the encoding of a datum, the datum has the matching constructor and the metavariables are
the encodings of its fields. These lemmas recover the datum: one per constructor of the
de Bruijn terms and types that the inference rules inspect, and the exact shape of encoded
equalities (`groundP_encodeTerm_eq_equalityTermP`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.FirstOrder

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.LabeledTreeOrder
open Mettapedia.Languages.OpenTheory

/-! ## Trees against label patterns -/

theorem toPatternList_eq_listP (trees : List LabeledTree) :
    LabeledTree.toPatternList trees = listP (trees.map LabeledTree.toPattern) := by
  induction trees with
  | nil => rfl
  | cons head tail ih => simp [LabeledTree.toPatternList, listP, ih]

theorem groundP_node (label : Nat) (children : List LabeledTree) :
    groundP (.node label children) = treeP label (children.map groundP) := by
  simp only [groundP, LabeledTree.toPattern, treeP, toPatternList_eq_listP]
  rfl

theorem listP_injective : Function.Injective listP := by
  intro first
  induction first with
  | nil => intro second same; cases second <;> simp_all [listP, nilP, consP]
  | cons head tail ih =>
      intro second same
      cases second with
      | nil => simp [listP, nilP, consP] at same
      | cons other others =>
          simp only [listP, consP, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at same
          rw [same.1, ih same.2]

/-- A tree's pattern has a given label and children exactly when the tree does. -/
theorem groundP_eq_treeP_iff (tree : LabeledTree) (label : Nat) (children : List Pattern) :
    groundP tree = treeP label children ↔
      ∃ subtrees, tree = .node label subtrees ∧ children = subtrees.map groundP := by
  cases tree with
  | node treeLabel subtrees =>
      rw [groundP_node]
      simp only [treeP, nodeP, Pattern.apply.injEq, List.cons.injEq, and_true, true_and,
        LabeledTree.node.injEq]
      constructor
      · rintro ⟨labels, lists⟩
        exact ⟨subtrees, ⟨numeralP_injective labels, rfl⟩, (listP_injective lists).symm⟩
      · rintro ⟨others, ⟨rfl, rfl⟩, rfl⟩
        exact ⟨rfl, rfl⟩

/-- Equal tree patterns have equal labels and equal children. -/
theorem treeP_injective {label label' : Nat} {children children' : List Pattern}
    (same : treeP label children = treeP label' children') : label = label' ∧ children = children' := by
  simp only [treeP, nodeP, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at same
  exact ⟨numeralP_injective same.1, listP_injective same.2⟩

/-! ## De Bruijn terms -/

theorem encodeTerm_eq_app {term : DBTerm} {function argument : Pattern}
    (same : groundP (encodeTerm term) = appTermP function argument) :
    ∃ functionTerm argumentTerm, term = .app functionTerm argumentTerm ∧
      function = groundP (encodeTerm functionTerm) ∧ argument = groundP (encodeTerm argumentTerm) := by
  obtain ⟨subtrees, shape, children⟩ := (groundP_eq_treeP_iff _ _ _).mp same
  cases term with
  | app functionTerm argumentTerm =>
      simp only [encodeTerm, LabeledTree.node.injEq, true_and] at shape
      subst shape
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at children
      exact ⟨functionTerm, argumentTerm, rfl, children.1, children.2⟩
  | _ => simp [encodeTerm, termConstLabel, termFreeLabel, termBoundLabel, termAppLabel, termAbsLabel] at shape

theorem encodeTerm_eq_abs {term : DBTerm} {type body : Pattern}
    (same : groundP (encodeTerm term) = absTermP type body) :
    ∃ domain bodyTerm, term = .abs domain bodyTerm ∧
      type = groundP (encodeTy domain) ∧ body = groundP (encodeTerm bodyTerm) := by
  obtain ⟨subtrees, shape, children⟩ := (groundP_eq_treeP_iff _ _ _).mp same
  cases term with
  | abs domain bodyTerm =>
      simp only [encodeTerm, LabeledTree.node.injEq, true_and] at shape
      subst shape
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at children
      exact ⟨domain, bodyTerm, rfl, children.1, children.2⟩
  | _ => simp [encodeTerm, termConstLabel, termFreeLabel, termBoundLabel, termAppLabel, termAbsLabel] at shape

theorem encodeTerm_eq_const {term : DBTerm} {constant type : Pattern}
    (same : groundP (encodeTerm term) = constTermP constant type) :
    ∃ constantValue typeValue, term = .const constantValue typeValue ∧
      constant = groundP (encodeConst constantValue) ∧ type = groundP (encodeTy typeValue) := by
  obtain ⟨subtrees, shape, children⟩ := (groundP_eq_treeP_iff _ _ _).mp same
  cases term with
  | const constantValue typeValue =>
      simp only [encodeTerm, LabeledTree.node.injEq, true_and] at shape
      subst shape
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at children
      exact ⟨constantValue, typeValue, rfl, children.1, children.2⟩
  | _ => simp [encodeTerm, termConstLabel, termFreeLabel, termBoundLabel, termAppLabel, termAbsLabel] at shape

theorem encodeTerm_eq_free {term : DBTerm} {name type : Pattern}
    (same : groundP (encodeTerm term) = freeTermP name type) :
    ∃ sourceVar : SourceVar, term = .free sourceVar ∧
      name = groundP (encodeName sourceVar.name) ∧ type = groundP (encodeTy sourceVar.ty) := by
  obtain ⟨subtrees, shape, children⟩ := (groundP_eq_treeP_iff _ _ _).mp same
  cases term with
  | free sourceVar =>
      simp only [encodeTerm, LabeledTree.node.injEq, true_and] at shape
      subst shape
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at children
      exact ⟨sourceVar, rfl, children.1, children.2⟩
  | _ => simp [encodeTerm, termConstLabel, termFreeLabel, termBoundLabel, termAppLabel, termAbsLabel] at shape

theorem encodeTerm_eq_bound {term : DBTerm} {index : Pattern}
    (same : groundP (encodeTerm term) = boundTermP index) :
    ∃ indexValue, term = .bound indexValue ∧ index = groundP (encodeUnary indexValue) := by
  obtain ⟨subtrees, shape, children⟩ := (groundP_eq_treeP_iff _ _ _).mp same
  cases term with
  | bound indexValue =>
      simp only [encodeTerm, LabeledTree.node.injEq, true_and] at shape
      subst shape
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at children
      exact ⟨indexValue, rfl, children⟩
  | _ => simp [encodeTerm, termConstLabel, termFreeLabel, termBoundLabel, termAppLabel, termAbsLabel] at shape

/-! ## Source terms -/

theorem encodeSourceTerm_eq_app {source : SourceTerm} {function argument : Pattern}
    (same : groundP (encodeSourceTerm source) = sourceAppP function argument) :
    ∃ functionSource argumentSource, source = .app functionSource argumentSource ∧
      function = groundP (encodeSourceTerm functionSource) ∧
        argument = groundP (encodeSourceTerm argumentSource) := by
  obtain ⟨subtrees, shape, children⟩ := (groundP_eq_treeP_iff _ _ _).mp same
  cases source with
  | app functionSource argumentSource =>
      simp only [encodeSourceTerm, LabeledTree.node.injEq, true_and] at shape
      subst shape
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at children
      exact ⟨functionSource, argumentSource, rfl, children.1, children.2⟩
  | _ => simp [encodeSourceTerm, sourceConstLabel, sourceVarLabel, sourceAppLabel, sourceAbsLabel] at shape

theorem encodeSourceTerm_eq_abs {source : SourceTerm} {name type body : Pattern}
    (same : groundP (encodeSourceTerm source) = sourceAbsP name type body) :
    ∃ nameValue typeValue bodySource, source = .abs nameValue typeValue bodySource ∧
      name = groundP (encodeName nameValue) ∧ type = groundP (encodeTy typeValue) ∧
        body = groundP (encodeSourceTerm bodySource) := by
  obtain ⟨subtrees, shape, children⟩ := (groundP_eq_treeP_iff _ _ _).mp same
  cases source with
  | abs nameValue typeValue bodySource =>
      simp only [encodeSourceTerm, LabeledTree.node.injEq, true_and] at shape
      subst shape
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at children
      exact ⟨nameValue, typeValue, bodySource, rfl, children.1, children.2.1, children.2.2⟩
  | _ => simp [encodeSourceTerm, sourceConstLabel, sourceVarLabel, sourceAppLabel, sourceAbsLabel] at shape

theorem encodeSourceTerm_eq_var {source : SourceTerm} {name type : Pattern}
    (same : groundP (encodeSourceTerm source) = sourceVarP name type) :
    ∃ nameValue typeValue, source = .var nameValue typeValue ∧
      name = groundP (encodeName nameValue) ∧ type = groundP (encodeTy typeValue) := by
  obtain ⟨subtrees, shape, children⟩ := (groundP_eq_treeP_iff _ _ _).mp same
  cases source with
  | var nameValue typeValue =>
      simp only [encodeSourceTerm, LabeledTree.node.injEq, true_and] at shape
      subst shape
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at children
      exact ⟨nameValue, typeValue, rfl, children.1, children.2⟩
  | _ => simp [encodeSourceTerm, sourceConstLabel, sourceVarLabel, sourceAppLabel, sourceAbsLabel] at shape

/-! ## Types -/

theorem encodeTy_eq_function {type : Ty} {domain codomain : Pattern}
    (same : groundP (encodeTy type) = functionTyP domain codomain) :
    ∃ domainType codomainType, type = Ty.function domainType codomainType ∧
      domain = groundP (encodeTy domainType) ∧ codomain = groundP (encodeTy codomainType) := by
  obtain ⟨subtrees, shape, children⟩ := (groundP_eq_treeP_iff _ _ _).mp same
  cases type with
  | var name => simp [encodeTy, tyVarLabel, tyOpLabel] at shape
  | op operator arguments =>
      simp only [encodeTy, LabeledTree.node.injEq, true_and] at shape
      subst shape
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at children
      obtain ⟨operatorSame, argumentsSame⟩ := children
      have operatorEq : operator = TypeOp.function :=
        encodeTypeOp_injective _ _ (LabeledTree.toPattern_injective _ _ operatorSame.symm)
      subst operatorEq
      obtain ⟨items, listShape, itemsSame⟩ := (groundP_eq_treeP_iff _ _ _).mp argumentsSame.symm
      simp only [LabeledTree.node.injEq, true_and] at listShape
      match arguments, listShape, itemsSame with
      | [domainType, codomainType], listShape, itemsSame =>
          simp only [encodeTys] at listShape
          subst listShape
          simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at itemsSame
          exact ⟨domainType, codomainType, rfl, itemsSame.1, itemsSame.2⟩
      | [], listShape, itemsSame => simp [encodeTys] at listShape; subst listShape; simp at itemsSame
      | [_], listShape, itemsSame => simp [encodeTys] at listShape; subst listShape; simp at itemsSame
      | _ :: _ :: _ :: _, listShape, itemsSame =>
          simp [encodeTys] at listShape; subst listShape; simp at itemsSame

theorem encodeTy_eq_var {type : Ty} {name : Pattern} (same : groundP (encodeTy type) = tyVarP name) :
    ∃ nameValue, type = .var nameValue ∧ name = groundP (encodeName nameValue) := by
  obtain ⟨subtrees, shape, children⟩ := (groundP_eq_treeP_iff _ _ _).mp same
  cases type with
  | var nameValue =>
      simp only [encodeTy, LabeledTree.node.injEq, true_and] at shape
      subst shape
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at children
      exact ⟨nameValue, rfl, children⟩
  | op operator arguments => simp [encodeTy, tyVarLabel, tyOpLabel] at shape

/-- An encoded type with the shape of an operator application; the arguments as a list. -/
theorem encodeTy_eq_op {type : Ty} {operator arguments : Pattern}
    (same : groundP (encodeTy type) = tyOpP operator arguments) :
    ∃ operatorValue argumentValues, type = .op operatorValue argumentValues ∧
      operator = groundP (encodeTypeOp operatorValue) ∧
        arguments = listP ((encodeTys argumentValues).map groundP) := by
  obtain ⟨subtrees, shape, children⟩ := (groundP_eq_treeP_iff _ _ _).mp same
  cases type with
  | var nameValue => simp [encodeTy, tyVarLabel, tyOpLabel] at shape
  | op operatorValue argumentValues =>
      simp only [encodeTy, LabeledTree.node.injEq, true_and] at shape
      subst shape
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at children
      obtain ⟨operatorSame, argumentsSame⟩ := children
      rw [groundP_node] at argumentsSame
      simp only [treeP, nodeP, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at argumentsSame
      exact ⟨operatorValue, argumentValues, rfl, operatorSame, argumentsSame⟩

theorem groundP_encodeTy_op (operator : TypeOp) (arguments : List Ty) :
    groundP (encodeTy (.op operator arguments)) =
      tyOpP (groundP (encodeTypeOp operator)) (listP ((encodeTys arguments).map groundP)) := by
  simp only [encodeTy, groundP_node, List.map_cons, List.map_nil, tyOpP, treeP]

theorem groundP_encodeTy_bool : groundP (encodeTy Ty.bool) = boolP := rfl

/-- The encoded equality at an operand type. -/
theorem groundP_encodeTerm_CanonicalTerm.equalityDB (operand : Ty) (left right : DBTerm) :
    groundP (encodeTerm (CanonicalTerm.equalityDB operand left right)) =
      equalityTermP (groundP (encodeTy operand)) (groundP (encodeTerm left)) (groundP (encodeTerm right)) := by
  rfl

/-- **An encoded term with the shape of an equality is an equality.** -/
theorem groundP_encodeTerm_eq_equalityTermP {term : DBTerm} {type left right : Pattern}
    (same : groundP (encodeTerm term) = equalityTermP type left right) :
    ∃ operand leftTerm rightTerm, term = CanonicalTerm.equalityDB operand leftTerm rightTerm ∧
      type = groundP (encodeTy operand) ∧ left = groundP (encodeTerm leftTerm) ∧
        right = groundP (encodeTerm rightTerm) := by
  obtain ⟨headTerm, rightTerm, rfl, headSame, rightSame⟩ := encodeTerm_eq_app same
  obtain ⟨constantTerm, leftTerm, rfl, constantSame, leftSame⟩ := encodeTerm_eq_app headSame.symm
  obtain ⟨constant, annotation, rfl, constantNameSame, annotationSame⟩ := encodeTerm_eq_const constantSame.symm
  have constantEq : constant = Const.equality :=
    encodeConst_injective _ _ (LabeledTree.toPattern_injective _ _ constantNameSame.symm)
  subst constantEq
  obtain ⟨operand, rest, rfl, typeSame, restSame⟩ := encodeTy_eq_function annotationSame.symm
  obtain ⟨operand', boolType, rfl, operandSame, boolSame⟩ := encodeTy_eq_function restSame.symm
  have operands : operand' = operand :=
    encodeTy_injective _ _ (LabeledTree.toPattern_injective _ _ (operandSame.symm.trans typeSame))
  subst operands
  have boolEq : boolType = Ty.bool :=
    encodeTy_injective _ _ (LabeledTree.toPattern_injective _ _ boolSame.symm)
  subst boolEq
  exact ⟨operand', leftTerm, rightTerm, rfl, typeSame, leftSame, rightSame⟩

end Mettapedia.Languages.HOLLight.FirstOrder

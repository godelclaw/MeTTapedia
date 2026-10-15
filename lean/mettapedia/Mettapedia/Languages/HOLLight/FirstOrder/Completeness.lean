import Mettapedia.Languages.HOLLight.FirstOrder.Closure
import Mettapedia.Languages.OpenTheory.FunctionRecognition

/-!
# Every derivation of HOL Light's kernel is a derivation of its first-order calculus

The converse of `holCalculus_sound`. Each judgment of the calculus gets a builder that turns
the data HOL Light computes with into a derivation: firing a rule (`fire`, `fireAt`) at
arguments that are encodings, with the derivations of its premises as children. The
derivations are values, so their erasures are the certificates the checker accepts.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.FirstOrder

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.LabeledTreeOrder
open Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules (checkSchema checkSchemas checkSchema_iff checkSchemas_iff)
open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.MM0.Translation.CalculusSimulation
  (substSchema substSchemas bindingValue instantiateSchemaAt?_eq instantiateSchemasAt?_eq)
open Mettapedia.GSLT.LanguageDef (ValidatedCalculusLanguageDef)
open Mettapedia.Logic (Derives)

/-! ## Valid arguments -/

/-- An argument the checker accepts at depth zero: ground, without binder metadata. -/
def Valid (pattern : Pattern) : Prop := argumentValidAt 0 pattern = true

theorem valid_apply {head : String} {arguments : List Pattern}
    (valid : ∀ argument ∈ arguments, Valid argument) : Valid (.apply head arguments) := by
  have both : Pattern.isGroundListAt 0 arguments = true ∧
      Pattern.hasCanonicalBinderMetadataList arguments = true := by
    induction arguments with
    | nil => exact ⟨rfl, rfl⟩
    | cons first _ ih =>
        have firstValid := valid first (List.mem_cons.mpr (Or.inl rfl))
        obtain ⟨restGround, restMetadata⟩ := ih fun argument member => valid argument (List.mem_cons_of_mem _ member)
        simp only [Valid, argumentValidAt, Bool.and_eq_true] at firstValid
        simp only [Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadataList, Bool.and_eq_true]
        exact ⟨⟨firstValid.1, restGround⟩, firstValid.2, restMetadata⟩
  simp only [Valid, argumentValidAt, Pattern.isGroundAt, Pattern.hasCanonicalBinderMetadata, both.1, both.2,
    Bool.and_self]

@[simp] theorem valid_numeralP : ∀ count, Valid (numeralP count)
  | 0 => valid_apply (by simp)
  | count + 1 => valid_apply (by simp [valid_numeralP count])

@[simp] theorem valid_nilP : Valid nilP := valid_apply (by simp)

theorem valid_consP {head tail : Pattern} (headValid : Valid head) (tailValid : Valid tail) :
    Valid (consP head tail) :=
  valid_apply (by simp [headValid, tailValid])

theorem valid_nodeP {label children : Pattern} (labelValid : Valid label) (childrenValid : Valid children) :
    Valid (nodeP label children) :=
  valid_apply (by simp [labelValid, childrenValid])

theorem valid_listP : ∀ {items : List Pattern}, (∀ item ∈ items, Valid item) → Valid (listP items)
  | [], _ => valid_nilP
  | item :: _, valid =>
      valid_consP (valid item (List.mem_cons.mpr (Or.inl rfl)))
        (valid_listP fun other member => valid other (List.mem_cons_of_mem _ member))

theorem valid_treeP {label : Nat} {children : List Pattern} (valid : ∀ child ∈ children, Valid child) :
    Valid (treeP label children) :=
  valid_nodeP (valid_numeralP label) (valid_listP valid)

mutual
  @[simp] theorem valid_toPattern : ∀ tree : LabeledTree, Valid tree.toPattern
    | .node label children => valid_nodeP (valid_numeralP label) (valid_toPatternList children)

  @[simp] theorem valid_toPatternList : ∀ trees : List LabeledTree, Valid (LabeledTree.toPatternList trees)
    | [] => valid_nilP
    | tree :: rest => valid_consP (valid_toPattern tree) (valid_toPatternList rest)
end

@[simp] theorem valid_groundP (tree : LabeledTree) : Valid (groundP tree) := valid_toPattern tree

theorem argumentsValidAt_of_valid : ∀ {names : List String} {arguments : List Pattern},
    arguments.length = names.length → (∀ argument ∈ arguments, Valid argument) →
      argumentsValidAt (names.map fun name => (name, 0)) arguments = true
  | [], [], _, _ => rfl
  | _ :: names, argument :: arguments, arity, valid => by
      have first := valid argument (List.mem_cons.mpr (Or.inl rfl))
      have rest := argumentsValidAt_of_valid (names := names) (arguments := arguments)
        (by simpa using arity) fun other member => valid other (List.mem_cons_of_mem _ member)
      simp only [List.map_cons, argumentsValidAt, Bool.and_eq_true]
      exact ⟨first, rest⟩
  | [], _ :: _, arity, _ => by simp at arity
  | _ :: _, [], arity, _ => by simp at arity

/-! ## Firing a rule -/

/-- A rule as `rule` builds it: formals at depth zero, no side conditions, first-order schemas. -/
structure RuleShape (r : RuleSchema) : Prop where
  formals : r.metavariables = (r.metavariables.map Prod.fst).map fun name => (name, 0)
  sides : r.sideConditions = []
  premisesSchema : checkSchemas (r.metavariables.map Prod.fst) r.premises = true
  conclusionSchema : checkSchema (r.metavariables.map Prod.fst) r.conclusion = true

/-- The values a rule's formals take from positional arguments. -/
def ruleValues (r : RuleSchema) (arguments : List Pattern) : String → Pattern :=
  bindingValue ((r.metavariables.map Prod.fst).zip arguments)

/-- **Fire a rule** on arguments: from derivations of its instantiated premises, a derivation
of its instantiated conclusion. -/
def fire {definition : ValidatedCalculusLanguageDef} {r : RuleSchema} (member : r ∈ definition.1.rules)
    (shape : RuleShape r) (arguments : List Pattern) (arity : arguments.length = r.metavariables.length)
    (valid : ∀ argument ∈ arguments, Valid argument)
    (children : DerivationList definition (substSchemas (ruleValues r arguments) r.premises)) :
    Derivation definition (substSchema (ruleValues r arguments) r.conclusion) :=
  have arity' : arguments.length = (r.metavariables.map Prod.fst).length := by simpa using arity
  .byRule ⟨r.id, arguments⟩
    (.intro r (lookupRule?_eq_some_of_mem definition member)
      (by rw [shape.formals]; exact argumentsValidAt_of_valid arity' valid)
      (RuleSchema.sideConditionsHold_of_empty _ _ shape.sides)
      (by
        rw [shape.formals]
        exact instantiateSchemasAt?_sound
          (instantiateSchemasAt?_eq arity' ((checkSchemas_iff _ _).mp shape.premisesSchema)))
      (by
        rw [shape.formals]
        exact instantiateSchemaAt?_sound
          (instantiateSchemaAt?_eq arity' ((checkSchema_iff _ _).mp shape.conclusionSchema))))
    children

/-- A derivation read at an equal judgment. -/
def recast {definition : ValidatedCalculusLanguageDef} {first second : Pattern} (same : first = second)
    (derivation : Derivation definition first) : Derivation definition second :=
  same ▸ derivation

theorem erase_recast {definition : ValidatedCalculusLanguageDef} {first second : Pattern}
    (same : first = second) (derivation : Derivation definition first) :
    (recast same derivation).erase = derivation.erase := by
  subst same
  rfl

/-! ## The calculus at hand -/

section Calculus

variable {axioms : List Sequent} {definition : ValidatedCalculusLanguageDef}
  (calculus : definition.1 = holCalculus axioms)

include calculus in
theorem member_of_holRules {r : RuleSchema} (member : r ∈ holRules axioms) : r ∈ definition.1.rules := by
  rw [calculus]
  exact member

theorem orderRules_shape : ∀ r ∈ orderRules, RuleShape r := by
  intro r member
  simp only [orderRules, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨rfl, rfl, by decide +kernel, by decide +kernel⟩

include calculus in
theorem member_of_orderRules {r : RuleSchema} (member : r ∈ orderRules) : r ∈ definition.1.rules :=
  member_of_holRules calculus (by simp only [holRules, List.mem_append]; tauto)

include calculus in
/-- `m < n` as a derivation of `Below`. -/
def deriveBelow : ∀ (first second : Nat), first < second →
    Derivation definition (belowJudgment (numeralP first) (numeralP second))
  | 0, second + 1, _ =>
      recast rfl (fire (r := belowZeroRule) (member_of_orderRules calculus (by simp [orderRules]))
        (orderRules_shape _ (by simp [orderRules])) [numeralP second] rfl (by simp [valid_numeralP]) .nil)
  | first + 1, second + 1, lower =>
      recast rfl (fire (r := belowSuccRule) (member_of_orderRules calculus (by simp [orderRules]))
        (orderRules_shape _ (by simp [orderRules])) [numeralP first, numeralP second] rfl
        (by simp [valid_numeralP])
        (.cons (deriveBelow first second (by omega)) .nil))
  | _, 0, lower => absurd lower (Nat.not_lt_zero _)

end Calculus

/-! ## Inversion of the order of trees -/

theorem treeLt_node_inv {label label' : Nat} {children children' : List LabeledTree}
    (lower : LabeledTree.node label children < LabeledTree.node label' children') :
    label < label' ∨ label = label' ∧ LabeledTree.ListLt children children' := by
  cases lower with
  | label labels => exact Or.inl labels
  | children lists => exact Or.inr ⟨rfl, lists⟩

theorem listLt_cons_inv {first second : LabeledTree} {firsts seconds : List LabeledTree}
    (lower : LabeledTree.ListLt (first :: firsts) (second :: seconds)) :
    first < second ∨ first = second ∧ LabeledTree.ListLt firsts seconds := by
  cases lower with
  | head heads => exact Or.inl heads
  | tail tails => exact Or.inr ⟨rfl, tails⟩

theorem listLt_nil_right {firsts : List LabeledTree} : ¬ LabeledTree.ListLt firsts [] := by
  intro lower
  cases lower

/-- A rule built by `rule` has the shape `fire` needs once its schemas are first-order. -/
theorem rule_shape {id : String} {names : List String} {premises : List Pattern} {conclusion : Pattern}
    (checked : checkSchemas names premises = true ∧ checkSchema names conclusion = true) :
    RuleShape (rule id names premises conclusion) := by
  have names_eq : ((names.map fun name => (name, 0)).map Prod.fst) = names := by
    simp [List.map_map, Function.comp_def]
  refine ⟨?_, rfl, ?_, ?_⟩
  · simp only [rule, names_eq]
  · simp only [rule, names_eq]
    exact checked.1
  · simp only [rule, names_eq]
    exact checked.2

/-- Fire a rule at the judgments its instantiation computes. -/
def fireAt {definition : ValidatedCalculusLanguageDef} {r : RuleSchema} (member : r ∈ definition.1.rules)
    (shape : RuleShape r) (arguments : List Pattern) (arity : arguments.length = r.metavariables.length)
    (valid : ∀ argument ∈ arguments, Valid argument) {premises : List Pattern} {conclusion : Pattern}
    (premisesEq : substSchemas (ruleValues r arguments) r.premises = premises)
    (conclusionEq : substSchema (ruleValues r arguments) r.conclusion = conclusion)
    (children : DerivationList definition premises) : Derivation definition conclusion :=
  recast conclusionEq (fire member shape arguments arity valid (premisesEq ▸ children))

theorem erase_fireAt {definition : ValidatedCalculusLanguageDef} {r : RuleSchema} (member : r ∈ definition.1.rules)
    (shape : RuleShape r) (arguments : List Pattern) (arity : arguments.length = r.metavariables.length)
    (valid : ∀ argument ∈ arguments, Valid argument) {premises : List Pattern} {conclusion : Pattern}
    (premisesEq : substSchemas (ruleValues r arguments) r.premises = premises)
    (conclusionEq : substSchema (ruleValues r arguments) r.conclusion = conclusion)
    (children : DerivationList definition premises) :
    (fireAt member shape arguments arity valid premisesEq conclusionEq children).erase =
      .node ⟨r.id, arguments⟩ (DerivationList.erase children) := by
  subst premisesEq conclusionEq
  rfl

section Calculus

variable {axioms : List Sequent} {definition : ValidatedCalculusLanguageDef}
  (calculus : definition.1 = holCalculus axioms)

include calculus in
theorem member_of_neqRules {r : RuleSchema} (member : r ∈ neqRules) : r ∈ definition.1.rules :=
  member_of_holRules calculus (by simp only [holRules, List.mem_append]; tauto)

mutual
  /-- `first < second` as a derivation of `Lt`. -/
  def deriveLt : (first second : LabeledTree) → first < second →
      Derivation definition (ltJudgment first.toPattern second.toPattern)
    | .node label children, .node label' children', lower =>
        if labels : label < label' then
          recast rfl (fire (r := ltLabelRule) (member_of_orderRules calculus (by simp [orderRules]))
            (orderRules_shape _ (by simp [orderRules]))
            [numeralP label, numeralP label', LabeledTree.toPatternList children,
              LabeledTree.toPatternList children'] rfl
            (by simp [valid_numeralP, valid_toPatternList])
            (.cons (deriveBelow calculus label label' labels) .nil))
        else
          have inverted := (treeLt_node_inv lower).resolve_left labels
          recast (by rw [← inverted.1]; rfl)
            (fire (r := ltChildrenRule) (member_of_orderRules calculus (by simp [orderRules]))
              (orderRules_shape _ (by simp [orderRules]))
              [numeralP label, LabeledTree.toPatternList children, LabeledTree.toPatternList children'] rfl
              (by simp [valid_numeralP, valid_toPatternList])
              (.cons (deriveLtList children children' inverted.2) .nil))

  /-- `ListLt` as a derivation of `LtList`. -/
  def deriveLtList : (firsts seconds : List LabeledTree) → LabeledTree.ListLt firsts seconds →
      Derivation definition (ltListJudgment (LabeledTree.toPatternList firsts) (LabeledTree.toPatternList seconds))
    | [], second :: seconds, _ =>
        recast rfl (fire (r := ltListNilRule) (member_of_orderRules calculus (by simp [orderRules]))
          (orderRules_shape _ (by simp [orderRules]))
          [second.toPattern, LabeledTree.toPatternList seconds] rfl
          (by simp [valid_toPattern, valid_toPatternList]) .nil)
    | first :: firsts, second :: seconds, lower =>
        if heads : first < second then
          recast rfl (fire (r := ltListHeadRule) (member_of_orderRules calculus (by simp [orderRules]))
            (orderRules_shape _ (by simp [orderRules]))
            [first.toPattern, second.toPattern, LabeledTree.toPatternList firsts, LabeledTree.toPatternList seconds]
            rfl (by simp [valid_toPattern, valid_toPatternList])
            (.cons (deriveLt first second heads) .nil))
        else
          have inverted := (listLt_cons_inv lower).resolve_left heads
          recast (by rw [← inverted.1]; rfl)
            (fire (r := ltListTailRule) (member_of_orderRules calculus (by simp [orderRules]))
              (orderRules_shape _ (by simp [orderRules]))
              [first.toPattern, LabeledTree.toPatternList firsts, LabeledTree.toPatternList seconds] rfl
              (by simp [valid_toPattern, valid_toPatternList])
              (.cons (deriveLtList firsts seconds inverted.2) .nil))
    | _, [], lower => absurd lower listLt_nil_right
end

include calculus in
/-- Distinct trees as a derivation of `Neq`. -/
def deriveNeq (first second : LabeledTree) (different : first ≠ second) :
    Derivation definition (neqJ first.toPattern second.toPattern) :=
  if lower : first < second then
    fireAt (r := neqRules[0]) (member_of_neqRules calculus (List.getElem_mem _)) (rule_shape (by decide +kernel))
      [first.toPattern, second.toPattern] rfl (by simp [valid_toPattern]) rfl rfl
      (.cons (deriveLt calculus first second lower) .nil)
  else
    fireAt (r := neqRules[1]) (member_of_neqRules calculus (List.getElem_mem _)) (rule_shape (by decide +kernel))
      [first.toPattern, second.toPattern] rfl (by simp [valid_toPattern]) rfl rfl
      (.cons (deriveLt calculus second first ((lt_or_gt_of_ne different).resolve_left lower)) .nil)

end Calculus

/-! ## Well-formed data -/

theorem substSchema_bitP (values : String → Pattern) (bit : Nat) : substSchema values (bitP bit) = bitP bit := by
  simp [bitP, substSchema_treeP]

/-- Instantiate a rule's schemas symbolically: substitution through the builders and lookups
of the names, as in `rule_simp`, with the given rule groups unfolded. -/
syntax "fire_simp" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| fire_simp) => `(tactic| fire_simp [])
  | `(tactic| fire_simp [$extra,*]) => `(tactic| simp only [ruleValues, rule, substSchemas, substSchema,
      substSchema_treeP, substSchema_nodeP, substSchema_consP, substSchema_nilP, substSchema_numeralP,
      substSchema_fvar, substSchema_groundP, substSchema_listP, substSchema_functionOpP, substSchema_boolP,
      substSchema_equalityConstP, substSchema_bitP, bindingValue, List.zip, List.zipWith, List.find?, List.map, mv,
      String.reduceAppend, String.reduceBEq, beq_self_eq_true, Bool.false_eq_true, ite_true, ite_false,
      List.getElem_cons_zero, List.getElem_cons_succ, wfJ, charP, thmJ, neqJ, nthJ, typeOfJ, boundIndexJ,
      notBoundJ, toDBJ, notFreeJ, notFreeAllJ, closeJ, instantiateJ, unionJ, eraseJ, insertJ, sortJ, varTypeJ,
      tyActJ, tyActListJ, termTyActJ, termTyActListJ, admitTmJ, tmLookupJ, tmNoKeyJ, tmApplyJ, tmApplyListJ,
      equalityTermP, appTermP, absTermP, constTermP, freeTermP, boundTermP, functionTyP, sourceAppP, sourceAbsP,
      sourceVarP, sourceConstP, unaryZeroP, unarySuccP, $extra,*])

theorem groundP_encodeChar (character : Char) :
    groundP (encodeChar character) =
      charP (groundP (encodeUnary (character.toNat / 65536))) ((bitsDown character.toNat 16).map bitP) := by
  simp only [encodeChar, groundP_node, charP, List.map_cons, List.map_map]
  rfl

theorem bitsDown_binary (number : Nat) : ∀ count, ∀ bit ∈ bitsDown number count, bit < 2
  | 0 => by simp [bitsDown]
  | count + 1 => by
      intro bit member
      simp only [bitsDown, List.mem_cons] at member
      rcases member with rfl | member
      · exact Nat.mod_lt _ (by decide)
      · exact bitsDown_binary number count bit member

/-- In plane zero, a character outside the surrogate block, top bits `11011`, has one of the
five fixed bits of the plane-zero rules. -/
theorem planeZero_cases (character : Char) (zero : character.toNat / 65536 = 0) :
    charBit character 15 = 0 ∨ charBit character 14 = 0 ∨ charBit character 13 = 1 ∨
      charBit character 12 = 0 ∨ charBit character 11 = 0 := by
  have valid : character.toNat < 0xd800 ∨ (0xdfff < character.toNat ∧ character.toNat < 0x110000) :=
    character.valid
  simp only [charBit, Nat.reducePow]
  omega

theorem groundP_encodeString (text : String) :
    groundP (encodeString text) = nodeP (numeralP stringLabel) (charsP text.toList) := by
  simp only [encodeString, groundP_node, treeP, charsP, List.map_map]
  rfl

theorem groundP_encodeName (name : Name) :
    groundP (encodeName name) =
      treeP nameLabel [listNodeP (stringsP name.namespaceComponents), groundP (encodeString name.component)] := by
  simp only [encodeName, groundP_node, treeP, listNodeP, stringsP, List.map_cons, List.map_nil, List.map_map]
  rfl

theorem groundP_encodeTypeOpProvenance_defined (predicate : SourceTerm) (parameters : List Name) :
    groundP (encodeTypeOpProvenance (.defined predicate parameters)) =
      treeP typeOpDefinedLabel [groundP (encodeSourceTerm predicate), listNodeP (namesP parameters)] := by
  simp only [encodeTypeOpProvenance, groundP_node, treeP, listNodeP, namesP, List.map_cons, List.map_nil,
    List.map_map]
  rfl

theorem tysP_eq_listP (types : List Ty) : tysP types = listP ((encodeTys types).map groundP) := rfl

/-! ## Finite sets as increasing lists of trees -/

/-- Merge two lists of trees, keeping one copy of a tree in both. -/
def treeUnion : List LabeledTree → List LabeledTree → List LabeledTree
  | [], seconds => seconds
  | first :: firsts, [] => first :: firsts
  | first :: firsts, second :: seconds =>
      if first < second then first :: treeUnion firsts (second :: seconds)
      else if second < first then second :: treeUnion (first :: firsts) seconds
      else first :: treeUnion firsts seconds
termination_by firsts seconds => firsts.length + seconds.length

/-- Remove the first copy of a tree. -/
def treeErase (tree : LabeledTree) : List LabeledTree → List LabeledTree
  | [] => []
  | first :: rest => if first = tree then rest else first :: treeErase tree rest

/-- Insert a tree before the first larger one, unless it is there. -/
def treeInsert (tree : LabeledTree) : List LabeledTree → List LabeledTree
  | [] => [tree]
  | first :: rest =>
      if tree = first then first :: rest
      else if tree < first then tree :: first :: rest
      else first :: treeInsert tree rest

/-- Sort by insertion, keeping one copy of each tree. -/
def treeSort : List LabeledTree → List LabeledTree
  | [] => []
  | first :: rest => treeInsert first (treeSort rest)

theorem mem_treeUnion : ∀ (firsts seconds : List LabeledTree) (tree : LabeledTree),
    tree ∈ treeUnion firsts seconds ↔ tree ∈ firsts ∨ tree ∈ seconds
  | [], seconds, tree => by simp [treeUnion]
  | first :: firsts, [], tree => by simp [treeUnion]
  | first :: firsts, second :: seconds, tree => by
      unfold treeUnion
      split_ifs with lower upper
      · simp only [List.mem_cons, mem_treeUnion firsts (second :: seconds) tree]
        tauto
      · simp only [List.mem_cons, mem_treeUnion (first :: firsts) seconds tree]
        tauto
      · obtain rfl : first = second := (lt_trichotomy first second).resolve_left lower |>.resolve_right upper
        simp only [List.mem_cons, mem_treeUnion firsts seconds tree]
        tauto
termination_by firsts seconds => firsts.length + seconds.length

theorem treeUnion_increasing : ∀ (firsts seconds : List LabeledTree),
    Increasing firsts → Increasing seconds → Increasing (treeUnion firsts seconds)
  | [], seconds, _, increasing => by simpa [treeUnion] using increasing
  | first :: firsts, [], increasing, _ => by simpa [treeUnion] using increasing
  | first :: firsts, second :: seconds, firstsIncreasing, secondsIncreasing => by
      obtain ⟨firstBelow, firstsRest⟩ := List.pairwise_cons.mp firstsIncreasing
      obtain ⟨secondBelow, secondsRest⟩ := List.pairwise_cons.mp secondsIncreasing
      unfold treeUnion
      split_ifs with lower upper
      · refine List.pairwise_cons.mpr ⟨fun other member => ?_,
          treeUnion_increasing firsts (second :: seconds) firstsRest secondsIncreasing⟩
        rcases (mem_treeUnion _ _ other).mp member with inFirsts | inSeconds
        · exact firstBelow other inFirsts
        · rcases List.mem_cons.mp inSeconds with rfl | inRest
          · exact lower
          · exact lt_trans lower (secondBelow other inRest)
      · refine List.pairwise_cons.mpr ⟨fun other member => ?_,
          treeUnion_increasing (first :: firsts) seconds firstsIncreasing secondsRest⟩
        rcases (mem_treeUnion _ _ other).mp member with inFirsts | inSeconds
        · rcases List.mem_cons.mp inFirsts with rfl | inRest
          · exact upper
          · exact lt_trans upper (firstBelow other inRest)
        · exact secondBelow other inSeconds
      · obtain rfl : first = second := (lt_trichotomy first second).resolve_left lower |>.resolve_right upper
        refine List.pairwise_cons.mpr ⟨fun other member => ?_,
          treeUnion_increasing firsts seconds firstsRest secondsRest⟩
        rcases (mem_treeUnion _ _ other).mp member with inFirsts | inSeconds
        · exact firstBelow other inFirsts
        · exact secondBelow other inSeconds
termination_by firsts seconds => firsts.length + seconds.length

theorem mem_treeErase (tree : LabeledTree) : ∀ (trees : List LabeledTree), Increasing trees →
    ∀ other, other ∈ treeErase tree trees ↔ other ∈ trees ∧ other ≠ tree
  | [], _, other => by simp [treeErase]
  | first :: rest, increasing, other => by
      obtain ⟨firstBelow, restIncreasing⟩ := List.pairwise_cons.mp increasing
      unfold treeErase
      split_ifs with same
      · subst same
        constructor
        · intro member
          exact ⟨List.mem_cons_of_mem _ member, fun equal => lt_irrefl _ (equal ▸ firstBelow other member)⟩
        · rintro ⟨member, different⟩
          rcases List.mem_cons.mp member with rfl | inRest
          · exact absurd rfl different
          · exact inRest
      · simp only [List.mem_cons, mem_treeErase tree rest restIncreasing other]
        constructor
        · rintro (rfl | ⟨member, different⟩)
          · exact ⟨Or.inl rfl, same⟩
          · exact ⟨Or.inr member, different⟩
        · rintro ⟨rfl | member, different⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨member, different⟩

theorem treeErase_sublist (tree : LabeledTree) : ∀ trees : List LabeledTree, (treeErase tree trees).Sublist trees
  | [] => by simp [treeErase]
  | first :: rest => by
      unfold treeErase
      split_ifs
      · exact List.sublist_cons_self _ _
      · exact (treeErase_sublist tree rest).cons_cons first

theorem mem_treeInsert (tree : LabeledTree) : ∀ (trees : List LabeledTree) (other : LabeledTree),
    other ∈ treeInsert tree trees ↔ other = tree ∨ other ∈ trees
  | [], other => by simp [treeInsert]
  | first :: rest, other => by
      unfold treeInsert
      split_ifs with same lower
      · subst same
        simp only [List.mem_cons]
        tauto
      · simp only [List.mem_cons]
      · simp only [List.mem_cons, mem_treeInsert tree rest other]
        tauto

theorem treeInsert_increasing (tree : LabeledTree) : ∀ trees : List LabeledTree,
    Increasing trees → Increasing (treeInsert tree trees)
  | [], _ => by simp [treeInsert, Increasing]
  | first :: rest, increasing => by
      obtain ⟨firstBelow, restIncreasing⟩ := List.pairwise_cons.mp increasing
      unfold treeInsert
      split_ifs with same lower
      · exact increasing
      · refine List.pairwise_cons.mpr ⟨fun other member => ?_, increasing⟩
        rcases List.mem_cons.mp member with rfl | inRest
        · exact lower
        · exact lt_trans lower (firstBelow other inRest)
      · have upper : first < tree := (lt_trichotomy tree first).resolve_left lower |>.resolve_left same
        refine List.pairwise_cons.mpr ⟨fun other member => ?_, treeInsert_increasing tree rest restIncreasing⟩
        rcases (mem_treeInsert tree rest other).mp member with rfl | inRest
        · exact upper
        · exact firstBelow other inRest

theorem mem_treeSort : ∀ (trees : List LabeledTree) (other : LabeledTree), other ∈ treeSort trees ↔ other ∈ trees
  | [], other => by simp [treeSort]
  | first :: rest, other => by
      simp only [treeSort, mem_treeInsert, mem_treeSort rest other, List.mem_cons]

theorem treeSort_increasing : ∀ trees : List LabeledTree, Increasing (treeSort trees)
  | [] => by simp [treeSort, Increasing]
  | first :: rest => treeInsert_increasing first _ (treeSort_increasing rest)

/-- The union of two rendered hypothesis sets is the rendering of their union. -/
theorem treeUnion_hypothesisTrees (left right : Finset CanonicalTerm) :
    treeUnion (hypothesisTrees left) (hypothesisTrees right) = hypothesisTrees (left ∪ right) := by
  refine hypothesisTrees_unique (treeUnion_increasing _ _ (hypothesisTrees_increasing left)
    (hypothesisTrees_increasing right)) fun tree => ?_
  rw [mem_treeUnion, mem_hypothesisTrees, mem_hypothesisTrees]
  simp only [Finset.mem_union]
  constructor
  · rintro (⟨term, member, rfl⟩ | ⟨term, member, rfl⟩)
    · exact ⟨term, Or.inl member, rfl⟩
    · exact ⟨term, Or.inr member, rfl⟩
  · rintro ⟨term, member | member, rfl⟩
    · exact Or.inl ⟨term, member, rfl⟩
    · exact Or.inr ⟨term, member, rfl⟩

/-- Erasing from a rendered hypothesis set renders the erased set. -/
theorem treeErase_hypothesisTrees (hypotheses : Finset CanonicalTerm) (removed : CanonicalTerm) :
    treeErase (encodeCanonical removed) (hypothesisTrees hypotheses) = hypothesisTrees (hypotheses.erase removed) := by
  have increasing := hypothesisTrees_increasing hypotheses
  refine hypothesisTrees_unique (List.Pairwise.sublist (treeErase_sublist _ _) increasing) fun tree => ?_
  rw [mem_treeErase _ _ increasing, mem_hypothesisTrees]
  constructor
  · rintro ⟨⟨source, member, rfl⟩, different⟩
    exact ⟨source, Finset.mem_erase.mpr ⟨fun same => different (congrArg encodeCanonical same), member⟩, rfl⟩
  · rintro ⟨source, member, rfl⟩
    obtain ⟨different, member⟩ := Finset.mem_erase.mp member
    exact ⟨⟨source, member, rfl⟩, fun same => different (encodeCanonical_injective same)⟩

/-- Sorting the action of a term map on a rendered hypothesis set renders the image set. -/
theorem treeSort_image_hypothesisTrees (hypotheses : Finset CanonicalTerm) {action : DBTerm → DBTerm}
    {apply : CanonicalTerm → CanonicalTerm} (applied : ∀ term, (apply term).term = action term.term) :
    treeSort ((((sortedHypotheses hypotheses).map CanonicalTerm.term).map action).map encodeTerm) =
      hypothesisTrees (hypotheses.image apply) := by
  refine hypothesisTrees_unique (treeSort_increasing _) fun tree => ?_
  rw [mem_treeSort]
  simp only [List.map_map, List.mem_map, Function.comp_apply, sortedHypotheses, Finset.mem_sort,
    Finset.mem_image, encodeCanonical]
  constructor
  · rintro ⟨term, member, rfl⟩
    exact ⟨apply term, ⟨term, member, rfl⟩, by rw [applied]⟩
  · rintro ⟨_, ⟨term, member, rfl⟩, rfl⟩
    exact ⟨term, member, by rw [applied]⟩

section Calculus

variable {axioms : List Sequent} {definition : ValidatedCalculusLanguageDef}
  (calculus : definition.1 = holCalculus axioms)

include calculus in
theorem member_of_wellFormedRules {r : RuleSchema} (member : r ∈ wellFormedRules) : r ∈ definition.1.rules :=
  member_of_holRules calculus (by simp only [holRules, List.mem_append]; tauto)

include calculus in
theorem member_of_bitPlaneRules {r : RuleSchema} (member : r ∈ bitPlaneRules) : r ∈ definition.1.rules :=
  member_of_wellFormedRules calculus (by simp only [wellFormedRules, List.mem_append]; tauto)

include calculus in
theorem member_of_charRules {r : RuleSchema} (member : r ∈ charRules) : r ∈ definition.1.rules :=
  member_of_wellFormedRules calculus (by simp only [wellFormedRules, List.mem_append]; tauto)

include calculus in
theorem member_of_textRules {r : RuleSchema} (member : r ∈ textRules) : r ∈ definition.1.rules :=
  member_of_wellFormedRules calculus (by simp only [wellFormedRules, List.mem_append]; tauto)

include calculus in
theorem member_of_syntaxRules {r : RuleSchema} (member : r ∈ syntaxRules) : r ∈ definition.1.rules :=
  member_of_wellFormedRules calculus (by simp only [wellFormedRules, List.mem_append]; tauto)

include calculus in
def deriveBit : (bit : Nat) → bit < 2 → Derivation definition (wfJ "Bit" (bitP bit))
  | 0, _ =>
      fireAt (r := bitPlaneRules[0]) (member_of_bitPlaneRules calculus (List.getElem_mem _))
        (rule_shape (by decide +kernel)) [] rfl (by simp) rfl rfl .nil
  | 1, _ =>
      fireAt (r := bitPlaneRules[1]) (member_of_bitPlaneRules calculus (List.getElem_mem _))
        (rule_shape (by decide +kernel)) [] rfl (by simp) rfl rfl .nil
  | _ + 2, small => absurd small (by omega)

include calculus in
def deriveBits : (bits : List Nat) → (∀ bit ∈ bits, bit < 2) →
    DerivationList definition (bits.map fun bit => wfJ "Bit" (bitP bit))
  | [], _ => .nil
  | bit :: rest, binary =>
      .cons (deriveBit calculus bit (binary bit (List.mem_cons.mpr (Or.inl rfl))))
        (deriveBits rest fun other member => binary other (List.mem_cons_of_mem _ member))

include calculus in
theorem planeRule_mem {plane : Nat} (low : 1 ≤ plane) (high : plane ≤ 16) :
    rule ("hol.wf-plane-" ++ toString plane) [] [] (wfJ "Plane" (groundP (encodeUnary plane))) ∈
      definition.1.rules := by
  refine member_of_bitPlaneRules calculus ?_
  simp only [bitPlaneRules, List.mem_append, List.mem_map, List.mem_range]
  exact Or.inr ⟨plane - 1, by omega, by simp only [Nat.sub_add_cancel low]⟩

include calculus in
def derivePlane (plane : Nat) (low : 1 ≤ plane) (high : plane ≤ 16) :
    Derivation definition (wfJ "Plane" (groundP (encodeUnary plane))) :=
  fireAt (planeRule_mem calculus low high)
    (rule_shape ⟨by simp [checkSchemas], by simp [wfJ, checkSchema, checkSchemas, groundP, checkSchema_toPattern]⟩)
    [] rfl (by simp) rfl (by simp [rule, wfJ, substSchema, substSchemas, substSchema_groundP]) .nil

include calculus in
/-- A character outside plane zero, by the plane rule. -/
def deriveCharPlane (character : Char) (nonzero : character.toNat / 65536 ≠ 0) :
    Derivation definition (wfJ "Char" (groundP (encodeChar character))) :=
  have high : character.toNat / 65536 ≤ 16 := by
    have bounded : character.toNat < 0x110000 := by
      have valid : character.toNat < 0xd800 ∨ (0xdfff < character.toNat ∧ character.toNat < 0x110000) :=
        character.valid
      omega
    omega
  fireAt (r := charRules[0]) (member_of_charRules calculus (List.getElem_mem _)) (rule_shape (by decide +kernel))
    (groundP (encodeUnary (character.toNat / 65536)) :: (bitsDown character.toNat 16).map bitP)
    (by simp [charRules, rule, bitNames, bitsDown_length])
    (by
      intro argument member
      simp only [List.mem_cons, List.mem_map] at member
      rcases member with rfl | ⟨bit, -, rfl⟩
      · exact valid_groundP _
      · exact valid_treeP (by simp))
    (by fire_simp [charRules, bitNames_eq, bitsDown])
    (by rw [groundP_encodeChar]; fire_simp [charRules, bitNames_eq, bitsDown])
    (.cons (derivePlane calculus _ (by omega) high)
      (deriveBits calculus (bitsDown character.toNat 16) (bitsDown_binary _ _)))

theorem charRules_shape : ∀ r ∈ charRules, RuleShape r := by
  intro r member
  simp only [charRules, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> exact rule_shape (by decide +kernel)

theorem charBit_lt (character : Char) (position : Nat) : charBit character position < 2 :=
  Nat.mod_lt _ (by decide)

include calculus in
/-- A plane-zero character by the plane-zero rule at `index`, whose fixed bit it has. -/
def deriveCharFixed (character : Char) (index : Nat) (bound : index < charRules.length) (others : List Nat)
    (arity : (others.map fun position => bitP (charBit character position)).length =
      charRules[index].metavariables.length)
    (premisesEq : substSchemas (ruleValues charRules[index] (others.map fun position => bitP (charBit character position)))
      charRules[index].premises = (others.map (charBit character)).map fun bit => wfJ "Bit" (bitP bit))
    (conclusionEq : substSchema (ruleValues charRules[index] (others.map fun position => bitP (charBit character position)))
      charRules[index].conclusion = wfJ "Char" (groundP (encodeChar character))) :
    Derivation definition (wfJ "Char" (groundP (encodeChar character))) :=
  fireAt (member_of_charRules calculus (List.getElem_mem bound)) (charRules_shape _ (List.getElem_mem bound))
    (others.map fun position => bitP (charBit character position)) arity
    (by
      intro argument member
      obtain ⟨position, -, rfl⟩ := List.mem_map.mp member
      exact valid_treeP (by simp))
    premisesEq conclusionEq
    (deriveBits calculus _ fun bit member => by
      obtain ⟨position, -, rfl⟩ := List.mem_map.mp member
      exact charBit_lt _ _)

include calculus in
/-- A character in plane zero, by the first plane-zero rule whose fixed bit it has. -/
def deriveCharZero (character : Char) (zero : character.toNat / 65536 = 0) :
    Derivation definition (wfJ "Char" (groundP (encodeChar character))) :=
  if fifteen : charBit character 15 = 0 then
    deriveCharFixed calculus character 1 (by decide) [14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]
      (by simp [charRules, planeZeroRule_15_eq, rule])
      (by fire_simp [charRules, planeZeroRule_15_eq])
      (by
        simp only [charBit] at fifteen
        rw [groundP_encodeChar, zero]
        fire_simp [charRules, planeZeroRule_15_eq, bitsDown, charBit, fifteen])
  else if fourteen : charBit character 14 = 0 then
    deriveCharFixed calculus character 2 (by decide) [15, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]
      (by simp [charRules, planeZeroRule_14_eq, rule])
      (by fire_simp [charRules, planeZeroRule_14_eq])
      (by
        simp only [charBit] at fourteen
        rw [groundP_encodeChar, zero]
        fire_simp [charRules, planeZeroRule_14_eq, bitsDown, charBit, fourteen])
  else if thirteen : charBit character 13 = 1 then
    deriveCharFixed calculus character 3 (by decide) [15, 14, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]
      (by simp [charRules, planeZeroRule_13_eq, rule])
      (by fire_simp [charRules, planeZeroRule_13_eq])
      (by
        simp only [charBit] at thirteen
        rw [groundP_encodeChar, zero]
        fire_simp [charRules, planeZeroRule_13_eq, bitsDown, charBit, thirteen])
  else if twelve : charBit character 12 = 0 then
    deriveCharFixed calculus character 4 (by decide) [15, 14, 13, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]
      (by simp [charRules, planeZeroRule_12_eq, rule])
      (by fire_simp [charRules, planeZeroRule_12_eq])
      (by
        simp only [charBit] at twelve
        rw [groundP_encodeChar, zero]
        fire_simp [charRules, planeZeroRule_12_eq, bitsDown, charBit, twelve])
  else
    have eleven : charBit character 11 = 0 := by
      rcases planeZero_cases character zero with h | h | h | h | h
      · exact absurd h fifteen
      · exact absurd h fourteen
      · exact absurd h thirteen
      · exact absurd h twelve
      · exact h
    deriveCharFixed calculus character 5 (by decide) [15, 14, 13, 12, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]
      (by simp [charRules, planeZeroRule_11_eq, rule])
      (by fire_simp [charRules, planeZeroRule_11_eq])
      (by
        simp only [charBit] at eleven
        rw [groundP_encodeChar, zero]
        fire_simp [charRules, planeZeroRule_11_eq, bitsDown, charBit, eleven])

include calculus in
def deriveChar (character : Char) : Derivation definition (wfJ "Char" (groundP (encodeChar character))) :=
  if zero : character.toNat / 65536 = 0 then deriveCharZero calculus character zero
  else deriveCharPlane calculus character zero

include calculus in
def deriveChars : (characters : List Char) → Derivation definition (wfJ "Chars" (charsP characters))
  | [] =>
      fireAt (r := textRules[0]) (member_of_textRules calculus (List.getElem_mem _))
        (rule_shape (by decide +kernel)) [] rfl (by simp) rfl rfl .nil
  | character :: rest =>
      fireAt (r := textRules[1]) (member_of_textRules calculus (List.getElem_mem _))
        (rule_shape (by decide +kernel)) [groundP (encodeChar character), charsP rest] rfl
        (by simp [valid_groundP, charsP, valid_listP, List.mem_map]) rfl rfl
        (.cons (deriveChar calculus character) (.cons (deriveChars rest) .nil))

include calculus in
def deriveString (text : String) : Derivation definition (wfJ "String" (groundP (encodeString text))) :=
  fireAt (r := textRules[2]) (member_of_textRules calculus (List.getElem_mem _))
    (rule_shape (by decide +kernel)) [charsP text.toList] rfl
    (by simp [valid_groundP, charsP, valid_listP, List.mem_map]) rfl
    (by rw [groundP_encodeString]; rfl)
    (.cons (deriveChars calculus text.toList) .nil)

include calculus in
def deriveStrings : (texts : List String) → Derivation definition (wfJ "Strings" (stringsP texts))
  | [] =>
      fireAt (r := textRules[3]) (member_of_textRules calculus (List.getElem_mem _))
        (rule_shape (by decide +kernel)) [] rfl (by simp) rfl rfl .nil
  | text :: rest =>
      fireAt (r := textRules[4]) (member_of_textRules calculus (List.getElem_mem _))
        (rule_shape (by decide +kernel)) [groundP (encodeString text), stringsP rest] rfl
        (by simp [valid_groundP, stringsP, valid_listP, List.mem_map]) rfl rfl
        (.cons (deriveString calculus text) (.cons (deriveStrings rest) .nil))

include calculus in
def deriveName (name : Name) : Derivation definition (wfJ "Name" (groundP (encodeName name))) :=
  fireAt (r := textRules[5]) (member_of_textRules calculus (List.getElem_mem _))
    (rule_shape (by decide +kernel)) [stringsP name.namespaceComponents, groundP (encodeString name.component)] rfl
    (by simp [valid_groundP, stringsP, valid_listP, List.mem_map]) rfl
    (by rw [groundP_encodeName]; rfl)
    (.cons (deriveStrings calculus name.namespaceComponents) (.cons (deriveString calculus name.component) .nil))

include calculus in
def deriveNames : (names : List Name) → Derivation definition (wfJ "Names" (namesP names))
  | [] =>
      fireAt (r := textRules[6]) (member_of_textRules calculus (List.getElem_mem _))
        (rule_shape (by decide +kernel)) [] rfl (by simp) rfl rfl .nil
  | name :: rest =>
      fireAt (r := textRules[7]) (member_of_textRules calculus (List.getElem_mem _))
        (rule_shape (by decide +kernel)) [groundP (encodeName name), namesP rest] rfl
        (by simp [valid_groundP, namesP, valid_listP, List.mem_map]) rfl rfl
        (.cons (deriveName calculus name) (.cons (deriveNames rest) .nil))

theorem syntaxRules_shape : ∀ r ∈ syntaxRules, RuleShape r := by
  intro r member
  simp only [syntaxRules, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> exact rule_shape (by decide +kernel)

include calculus in
/-- Fire the syntax rule at an index. -/
def fireSyntax (index : Nat) (bound : index < syntaxRules.length) (arguments : List Pattern)
    (arity : arguments.length = syntaxRules[index].metavariables.length)
    (valid : ∀ argument ∈ arguments, Valid argument) {premises : List Pattern} {conclusion : Pattern}
    (premisesEq : substSchemas (ruleValues syntaxRules[index] arguments) syntaxRules[index].premises = premises)
    (conclusionEq : substSchema (ruleValues syntaxRules[index] arguments) syntaxRules[index].conclusion = conclusion)
    (children : DerivationList definition premises) : Derivation definition conclusion :=
  fireAt (member_of_syntaxRules calculus (List.getElem_mem bound)) (syntaxRules_shape _ (List.getElem_mem bound))
    arguments arity valid premisesEq conclusionEq children

mutual
  def deriveTy : (type : Ty) → Derivation definition (wfJ "Ty" (groundP (encodeTy type)))
    | .var name =>
        fireSyntax calculus 0 (by decide) [groundP (encodeName name)] rfl (by simp [valid_groundP]) rfl rfl
          (.cons (deriveName calculus name) .nil)
    | .op operator arguments =>
        fireSyntax calculus 1 (by decide) [groundP (encodeTypeOp operator), tysP arguments] rfl
          (by simp [valid_groundP, tysP_eq_listP, valid_listP, List.mem_map]) rfl
          (by rw [groundP_encodeTy_op]; rfl)
          (.cons (deriveTypeOp operator) (.cons (deriveTys arguments) .nil))

  def deriveTys : (types : List Ty) → Derivation definition (wfJ "Tys" (tysP types))
    | [] => fireSyntax calculus 2 (by decide) [] rfl (by simp) rfl rfl .nil
    | type :: rest =>
        fireSyntax calculus 3 (by decide) [groundP (encodeTy type), tysP rest] rfl
          (by simp [valid_groundP, tysP_eq_listP, valid_listP, List.mem_map]) rfl rfl
          (.cons (deriveTy type) (.cons (deriveTys rest) .nil))

  def deriveTypeOp : (operator : TypeOp) → Derivation definition (wfJ "TypeOp" (groundP (encodeTypeOp operator)))
    | .mk name provenance =>
        fireSyntax calculus 4 (by decide) [groundP (encodeName name), groundP (encodeTypeOpProvenance provenance)] rfl
          (by simp [valid_groundP]) rfl rfl
          (.cons (deriveName calculus name) (.cons (deriveTypeOpProvenance provenance) .nil))

  def deriveTypeOpProvenance : (provenance : TypeOpProvenance) →
      Derivation definition (wfJ "TypeOpProv" (groundP (encodeTypeOpProvenance provenance)))
    | .undefined => fireSyntax calculus 5 (by decide) [] rfl (by simp) rfl rfl .nil
    | .defined predicate parameters =>
        fireSyntax calculus 6 (by decide) [groundP (encodeSourceTerm predicate), namesP parameters] rfl
          (by simp [valid_groundP, namesP, valid_listP, List.mem_map]) rfl
          (by rw [groundP_encodeTypeOpProvenance_defined]; rfl)
          (.cons (deriveSource predicate) (.cons (deriveNames calculus parameters) .nil))

  def deriveConst : (constant : Const) → Derivation definition (wfJ "Const" (groundP (encodeConst constant)))
    | .mk name provenance =>
        fireSyntax calculus 7 (by decide) [groundP (encodeName name), groundP (encodeConstProvenance provenance)] rfl
          (by simp [valid_groundP]) rfl rfl
          (.cons (deriveName calculus name) (.cons (deriveConstProvenance provenance) .nil))

  def deriveConstProvenance : (provenance : ConstProvenance) →
      Derivation definition (wfJ "ConstProv" (groundP (encodeConstProvenance provenance)))
    | .undefined => fireSyntax calculus 8 (by decide) [] rfl (by simp) rfl rfl .nil
    | .defined definition' =>
        fireSyntax calculus 9 (by decide) [groundP (encodeSourceTerm definition')] rfl (by simp [valid_groundP]) rfl rfl
          (.cons (deriveSource definition') .nil)
    | .abstraction operator =>
        fireSyntax calculus 10 (by decide) [groundP (encodeTypeOp operator)] rfl (by simp [valid_groundP]) rfl rfl
          (.cons (deriveTypeOp operator) .nil)
    | .representation operator =>
        fireSyntax calculus 11 (by decide) [groundP (encodeTypeOp operator)] rfl (by simp [valid_groundP]) rfl rfl
          (.cons (deriveTypeOp operator) .nil)

  def deriveSource : (source : SourceTerm) → Derivation definition (wfJ "Source" (groundP (encodeSourceTerm source)))
    | .const constant type =>
        fireSyntax calculus 12 (by decide) [groundP (encodeConst constant), groundP (encodeTy type)] rfl
          (by simp [valid_groundP]) rfl rfl
          (.cons (deriveConst constant) (.cons (deriveTy type) .nil))
    | .var name type =>
        fireSyntax calculus 13 (by decide) [groundP (encodeName name), groundP (encodeTy type)] rfl
          (by simp [valid_groundP]) rfl rfl
          (.cons (deriveName calculus name) (.cons (deriveTy type) .nil))
    | .app function argument =>
        fireSyntax calculus 14 (by decide) [groundP (encodeSourceTerm function), groundP (encodeSourceTerm argument)]
          rfl (by simp [valid_groundP]) rfl rfl
          (.cons (deriveSource function) (.cons (deriveSource argument) .nil))
    | .abs name type body =>
        fireSyntax calculus 15 (by decide)
          [groundP (encodeName name), groundP (encodeTy type), groundP (encodeSourceTerm body)] rfl
          (by simp [valid_groundP]) rfl rfl
          (.cons (deriveName calculus name) (.cons (deriveTy type) (.cons (deriveSource body) .nil)))
end

include calculus in
def deriveTypeMaplets : (entries : List (Ty × Ty)) → Derivation definition (wfJ "TypeMaplets" (typeMapletsP entries))
  | [] => fireSyntax calculus 16 (by decide) [] rfl (by simp) rfl rfl .nil
  | (replacement, key) :: rest =>
      fireSyntax calculus 17 (by decide) [groundP (encodeTy replacement), groundP (encodeTy key), typeMapletsP rest] rfl
        (by
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          rintro argument (rfl | rfl | rfl)
          · exact valid_groundP _
          · exact valid_groundP _
          · exact valid_listP (by
              simp only [List.mem_map]
              rintro _ ⟨⟨first, second⟩, -, rfl⟩
              exact valid_treeP (by simp [valid_groundP])))
        rfl rfl
        (.cons (deriveTy calculus replacement) (.cons (deriveTy calculus key) (.cons (deriveTypeMaplets rest) .nil)))

/-! ## Context lookup and type inference -/

include calculus in
theorem member_of_nthRules {r : RuleSchema} (member : r ∈ nthRules) : r ∈ definition.1.rules :=
  member_of_holRules calculus (by simp only [holRules, List.mem_append]; tauto)

include calculus in
theorem member_of_typeRules {r : RuleSchema} (member : r ∈ typeRules) : r ∈ definition.1.rules :=
  member_of_holRules calculus (by simp only [holRules, List.mem_append]; tauto)

include calculus in
def deriveNth : (context : List Ty) → (index : Nat) → (type : Ty) → context[index]? = some type →
    Derivation definition (nthJ (contextP context) (groundP (encodeUnary index)) (groundP (encodeTy type)))
  | first :: rest, 0, type, found =>
      fireAt (r := nthRules[0]) (member_of_nthRules calculus (List.getElem_mem _)) (rule_shape (by decide +kernel))
        [groundP (encodeTy first), contextP rest] rfl
        (by simp [valid_groundP, contextP, valid_listP, List.mem_map]) rfl
        (by
          obtain rfl : first = type := Option.some.inj found
          rfl)
        .nil
  | first :: rest, index + 1, type, found =>
      fireAt (r := nthRules[1]) (member_of_nthRules calculus (List.getElem_mem _)) (rule_shape (by decide +kernel))
        [groundP (encodeTy first), contextP rest, groundP (encodeUnary index), groundP (encodeTy type)] rfl
        (by simp [valid_groundP, contextP, valid_listP, List.mem_map]) rfl rfl
        (.cons (deriveNth rest index type (by simpa using found)) .nil)
  | [], _, _, found => absurd found (by simp)

include calculus in
def deriveTypeOf (context : List Ty) : (term : DBTerm) → (type : Ty) → term.inferType context = some type →
    Derivation definition (typeOfJ (contextP context) (groundP (encodeTerm term)) (groundP (encodeTy type)))
  | .const constant annotation, type, typed =>
      fireAt (r := typeRules[0]) (member_of_typeRules calculus (List.getElem_mem _)) (rule_shape (by decide +kernel))
        [groundP (encodeConst constant), groundP (encodeTy annotation), contextP context] rfl
        (by simp [valid_groundP, contextP, valid_listP, List.mem_map]) rfl
        (by
          obtain rfl : annotation = type := Option.some.inj (by simpa [DBTerm.inferType] using typed)
          rfl)
        (.cons (deriveConst calculus constant) (.cons (deriveTy calculus annotation) .nil))
  | .free sourceVar, type, typed =>
      fireAt (r := typeRules[1]) (member_of_typeRules calculus (List.getElem_mem _)) (rule_shape (by decide +kernel))
        [groundP (encodeName sourceVar.name), groundP (encodeTy sourceVar.ty), contextP context] rfl
        (by simp [valid_groundP, contextP, valid_listP, List.mem_map]) rfl
        (by
          obtain rfl : sourceVar.ty = type := Option.some.inj (by simpa [DBTerm.inferType] using typed)
          rfl)
        (.cons (deriveName calculus sourceVar.name) (.cons (deriveTy calculus sourceVar.ty) .nil))
  | .bound index, type, typed =>
      fireAt (r := typeRules[2]) (member_of_typeRules calculus (List.getElem_mem _)) (rule_shape (by decide +kernel))
        [groundP (encodeUnary index), groundP (encodeTy type), contextP context] rfl
        (by simp [valid_groundP, contextP, valid_listP, List.mem_map]) rfl rfl
        (.cons (deriveNth calculus context index type (by simpa [DBTerm.inferType] using typed)) .nil)
  | .app function argument, type, typed =>
      match argumentTyped : argument.inferType context with
      | some domain =>
          have functionTyped : function.inferType context = some (Ty.function domain type) := by
            obtain ⟨domain', functionTyped', argumentTyped'⟩ := DBTerm.inferType_app_eq_some_iff.mp typed
            obtain rfl : domain' = domain := Option.some.inj (argumentTyped'.symm.trans argumentTyped)
            exact functionTyped'
          fireAt (r := typeRules[3]) (member_of_typeRules calculus (List.getElem_mem _))
            (rule_shape (by decide +kernel))
            [groundP (encodeTerm function), groundP (encodeTerm argument), groundP (encodeTy domain),
              groundP (encodeTy type), contextP context] rfl
            (by simp [valid_groundP, contextP, valid_listP, List.mem_map])
            (by fire_simp [typeRules, functionOpP]; rfl) rfl
            (.cons (deriveTypeOf context function (Ty.function domain type) functionTyped)
              (.cons (deriveTypeOf context argument domain argumentTyped) .nil))
      | none => absurd typed (by
          intro typed'
          obtain ⟨_, _, argumentTyped'⟩ := DBTerm.inferType_app_eq_some_iff.mp typed'
          rw [argumentTyped] at argumentTyped'
          cases argumentTyped')
  | .abs domain body, type, typed =>
      match bodyTyped : body.inferType (domain :: context) with
      | some codomain =>
          have typeEq : type = Ty.function domain codomain := by
            obtain ⟨codomain', bodyTyped', typeEq⟩ := DBTerm.inferType_abs_eq_some_iff.mp typed
            obtain rfl : codomain' = codomain := Option.some.inj (bodyTyped'.symm.trans bodyTyped)
            exact typeEq
          fireAt (r := typeRules[4]) (member_of_typeRules calculus (List.getElem_mem _))
            (rule_shape (by decide +kernel))
            [groundP (encodeTy domain), groundP (encodeTerm body), groundP (encodeTy codomain), contextP context] rfl
            (by simp [valid_groundP, contextP, valid_listP, List.mem_map]) rfl
            (by
              subst typeEq
              fire_simp [typeRules, functionOpP]
              rfl)
            (.cons (deriveTy calculus domain) (.cons (deriveTypeOf (domain :: context) body codomain bodyTyped) .nil))
      | none => absurd typed (by
          intro typed'
          obtain ⟨_, bodyTyped', _⟩ := DBTerm.inferType_abs_eq_some_iff.mp typed'
          rw [bodyTyped] at bodyTyped'
          cases bodyTyped')

/-! ## Binders and the conversion to de Bruijn form -/

theorem bindersP_cons (binder : SourceVar) (binders : List SourceVar) :
    bindersP (binder :: binders) = consP (freeVarP binder) (bindersP binders) := rfl

@[simp] theorem valid_bindersP (binders : List SourceVar) : Valid (bindersP binders) :=
  valid_listP (by simp only [List.mem_map]; rintro _ ⟨_, -, rfl⟩; exact valid_groundP _)

@[simp] theorem valid_termsP (terms : List DBTerm) : Valid (termsP terms) :=
  valid_listP (by simp only [List.mem_map]; rintro _ ⟨_, -, rfl⟩; exact valid_groundP _)

@[simp] theorem valid_contextP (context : List Ty) : Valid (contextP context) :=
  valid_listP (by simp only [List.mem_map]; rintro _ ⟨_, -, rfl⟩; exact valid_groundP _)

theorem encodeTerm_free_ne {first second : SourceVar} (different : first ≠ second) :
    encodeTerm (.free first) ≠ encodeTerm (.free second) := fun same =>
  different (by simpa using encodeTerm_injective same)

include calculus in
theorem member_of_binderRules {r : RuleSchema} (member : r ∈ binderRules) : r ∈ definition.1.rules :=
  member_of_holRules calculus (by simp only [holRules, List.mem_append]; tauto)

include calculus in
theorem member_of_toDBRules {r : RuleSchema} (member : r ∈ toDBRules) : r ∈ definition.1.rules :=
  member_of_holRules calculus (by simp only [holRules, List.mem_append]; tauto)

include calculus in
def deriveBoundIndex (needle : SourceVar) : (binders : List SourceVar) → (index : Nat) →
    boundIndex needle binders = some index →
      Derivation definition (boundIndexJ (bindersP binders) (freeVarP needle) (groundP (encodeUnary index)))
  | binder :: rest, index, found =>
      if same : sourceVarSame needle binder = true then
        have needleEq : needle = binder := (sourceVarSame_eq_true_iff _ _).mp same
        have indexEq : index = 0 := by simp [boundIndex, same] at found; omega
        fireAt (r := binderRules[0]) (member_of_binderRules calculus (List.getElem_mem _))
          (rule_shape (by decide +kernel)) [freeVarP binder, bindersP rest] rfl
          (by simp [freeVarP, valid_groundP, valid_bindersP]) rfl
          (by subst needleEq indexEq; rfl) .nil
      else
        match restFound : boundIndex needle rest with
        | some position =>
            have indexEq : index = position + 1 := by simp [boundIndex, same, restFound] at found; omega
            fireAt (r := binderRules[1]) (member_of_binderRules calculus (List.getElem_mem _))
              (rule_shape (by decide +kernel))
              [freeVarP binder, bindersP rest, freeVarP needle, groundP (encodeUnary position)] rfl
              (by simp [freeVarP, valid_groundP, valid_bindersP]) rfl (by subst indexEq; rfl)
              (.cons (deriveNeq calculus _ _ (encodeTerm_free_ne fun equal => same (by simp [equal])))
                (.cons (deriveBoundIndex needle rest position restFound) .nil))
        | none => absurd found (by simp [boundIndex, same, restFound])
  | [], _, found => absurd found (by simp [boundIndex])

include calculus in
def deriveNotBound (needle : SourceVar) : (binders : List SourceVar) → boundIndex needle binders = none →
    Derivation definition (notBoundJ (bindersP binders) (freeVarP needle))
  | [], _ =>
      fireAt (r := binderRules[2]) (member_of_binderRules calculus (List.getElem_mem _))
        (rule_shape (by decide +kernel)) [freeVarP needle] rfl (by simp [freeVarP, valid_groundP]) rfl rfl .nil
  | binder :: rest, missing =>
      have different : sourceVarSame needle binder ≠ true := fun same => by simp [boundIndex, same] at missing
      have restMissing : boundIndex needle rest = none := by
        simpa [boundIndex, different] using missing
      fireAt (r := binderRules[3]) (member_of_binderRules calculus (List.getElem_mem _))
        (rule_shape (by decide +kernel)) [freeVarP binder, bindersP rest, freeVarP needle] rfl
        (by simp [freeVarP, valid_groundP, valid_bindersP]) rfl rfl
        (.cons (deriveNeq calculus _ _ (encodeTerm_free_ne fun equal => different (by simp [equal])))
          (.cons (deriveNotBound needle rest restMissing) .nil))

include calculus in
def deriveToDB (binders : List SourceVar) : (source : SourceTerm) →
    Derivation definition (toDBJ (bindersP binders) (groundP (encodeSourceTerm source))
      (groundP (encodeTerm (source.toDB binders))))
  | .const constant type =>
      fireAt (r := toDBRules[0]) (member_of_toDBRules calculus (List.getElem_mem _))
        (rule_shape (by decide +kernel)) [bindersP binders, groundP (encodeConst constant), groundP (encodeTy type)] rfl
        (by simp [valid_groundP, valid_bindersP]) rfl (by simp only [SourceTerm.toDB]; rfl)
        (.cons (deriveConst calculus constant) (.cons (deriveTy calculus type) .nil))
  | .var name type =>
      match found : boundIndex ⟨name, type⟩ binders with
      | some index =>
          fireAt (r := toDBRules[1]) (member_of_toDBRules calculus (List.getElem_mem _))
            (rule_shape (by decide +kernel))
            [bindersP binders, groundP (encodeName name), groundP (encodeTy type), groundP (encodeUnary index)] rfl
            (by simp [valid_groundP, valid_bindersP]) rfl (by simp only [SourceTerm.toDB, found]; rfl)
            (.cons (deriveName calculus name) (.cons (deriveTy calculus type)
              (.cons (deriveBoundIndex calculus ⟨name, type⟩ binders index found) .nil)))
      | none =>
          fireAt (r := toDBRules[2]) (member_of_toDBRules calculus (List.getElem_mem _))
            (rule_shape (by decide +kernel)) [bindersP binders, groundP (encodeName name), groundP (encodeTy type)] rfl
            (by simp [valid_groundP, valid_bindersP]) rfl (by simp only [SourceTerm.toDB, found]; rfl)
            (.cons (deriveName calculus name) (.cons (deriveTy calculus type)
              (.cons (deriveNotBound calculus ⟨name, type⟩ binders found) .nil)))
  | .app function argument =>
      fireAt (r := toDBRules[3]) (member_of_toDBRules calculus (List.getElem_mem _))
        (rule_shape (by decide +kernel))
        [bindersP binders, groundP (encodeSourceTerm function), groundP (encodeSourceTerm argument),
          groundP (encodeTerm (function.toDB binders)), groundP (encodeTerm (argument.toDB binders))] rfl
        (by simp [valid_groundP, valid_bindersP]) rfl (by simp only [SourceTerm.toDB]; rfl)
        (.cons (deriveToDB binders function) (.cons (deriveToDB binders argument) .nil))
  | .abs name type body =>
      fireAt (r := toDBRules[4]) (member_of_toDBRules calculus (List.getElem_mem _))
        (rule_shape (by decide +kernel))
        [bindersP binders, groundP (encodeName name), groundP (encodeTy type), groundP (encodeSourceTerm body),
          groundP (encodeTerm (body.toDB (⟨name, type⟩ :: binders)))] rfl
        (by simp [valid_groundP, valid_bindersP]) rfl (by simp only [SourceTerm.toDB]; rfl)
        (.cons (deriveName calculus name) (.cons (deriveTy calculus type)
          (.cons (deriveToDB (⟨name, type⟩ :: binders) body) .nil)))

/-! ## Free variables, closing a variable, instantiation -/

include calculus in
theorem member_of_notFreeRules {r : RuleSchema} (member : r ∈ notFreeRules) : r ∈ definition.1.rules :=
  member_of_holRules calculus (by simp only [holRules, List.mem_append]; tauto)

include calculus in
theorem member_of_closeRules {r : RuleSchema} (member : r ∈ closeRules) : r ∈ definition.1.rules :=
  member_of_holRules calculus (by simp only [holRules, List.mem_append]; tauto)

include calculus in
theorem member_of_instantiateRules {r : RuleSchema} (member : r ∈ instantiateRules) : r ∈ definition.1.rules :=
  member_of_holRules calculus (by simp only [holRules, List.mem_append]; tauto)

include calculus in
def deriveNotFree (needle : SourceVar) : (term : DBTerm) → DBTerm.hasFree needle term = false →
    Derivation definition (notFreeJ (freeVarP needle) (groundP (encodeTerm term)))
  | .const constant type, _ =>
      fireAt (r := notFreeRules[0]) (member_of_notFreeRules calculus (List.getElem_mem _))
        (rule_shape (by decide +kernel)) [freeVarP needle, groundP (encodeConst constant), groundP (encodeTy type)]
        rfl (by simp [freeVarP, valid_groundP]) rfl rfl .nil
  | .free sourceVar, absent =>
      have different : needle ≠ sourceVar := fun same => by
        subst same
        have present : DBTerm.hasFree needle (.free needle) = true := by simp [DBTerm.hasFree]
        rw [absent] at present
        cases present
      fireAt (r := notFreeRules[1]) (member_of_notFreeRules calculus (List.getElem_mem _))
        (rule_shape (by decide +kernel))
        [freeVarP needle, groundP (encodeName sourceVar.name), groundP (encodeTy sourceVar.ty)]
        rfl (by simp [freeVarP, valid_groundP]) rfl rfl
        (.cons (deriveNeq calculus _ _ (encodeTerm_free_ne different)) .nil)
  | .bound index, _ =>
      fireAt (r := notFreeRules[2]) (member_of_notFreeRules calculus (List.getElem_mem _))
        (rule_shape (by decide +kernel)) [freeVarP needle, groundP (encodeUnary index)]
        rfl (by simp [freeVarP, valid_groundP]) rfl rfl .nil
  | .app function argument, absent =>
      have both : DBTerm.hasFree needle function = false ∧ DBTerm.hasFree needle argument = false := by
        simpa [DBTerm.hasFree] using absent
      fireAt (r := notFreeRules[3]) (member_of_notFreeRules calculus (List.getElem_mem _))
        (rule_shape (by decide +kernel))
        [freeVarP needle, groundP (encodeTerm function), groundP (encodeTerm argument)]
        rfl (by simp [freeVarP, valid_groundP]) rfl rfl
        (.cons (deriveNotFree needle function both.1) (.cons (deriveNotFree needle argument both.2) .nil))
  | .abs domain body, absent =>
      fireAt (r := notFreeRules[4]) (member_of_notFreeRules calculus (List.getElem_mem _))
        (rule_shape (by decide +kernel))
        [freeVarP needle, groundP (encodeTy domain), groundP (encodeTerm body)]
        rfl (by simp [freeVarP, valid_groundP]) rfl rfl
        (.cons (deriveNotFree needle body (by simpa [DBTerm.hasFree] using absent)) .nil)

include calculus in
def deriveNotFreeAll (needle : SourceVar) : (terms : List DBTerm) → (∀ term ∈ terms, DBTerm.hasFree needle term = false) →
    Derivation definition (notFreeAllJ (freeVarP needle) (termsP terms))
  | [], _ =>
      fireAt (r := notFreeRules[5]) (member_of_notFreeRules calculus (List.getElem_mem _))
        (rule_shape (by decide +kernel)) [freeVarP needle] rfl (by simp [freeVarP, valid_groundP]) rfl rfl .nil
  | term :: rest, absent =>
      fireAt (r := notFreeRules[6]) (member_of_notFreeRules calculus (List.getElem_mem _))
        (rule_shape (by decide +kernel)) [freeVarP needle, groundP (encodeTerm term), termsP rest]
        rfl (by simp [freeVarP, valid_groundP, valid_termsP]) rfl rfl
        (.cons (deriveNotFree calculus needle term (absent term (List.mem_cons.mpr (Or.inl rfl))))
          (.cons (deriveNotFreeAll needle rest fun other member => absent other (List.mem_cons_of_mem _ member)) .nil))

include calculus in
def deriveClose (needle : SourceVar) : (level : Nat) → (term : DBTerm) →
    Derivation definition (closeJ (freeVarP needle) (groundP (encodeUnary level)) (groundP (encodeTerm term))
      (groundP (encodeTerm (DBTerm.closeFreeAt needle level term))))
  | level, .const constant type =>
      fireAt (r := closeRules[0]) (member_of_closeRules calculus (List.getElem_mem _))
        (rule_shape (by decide +kernel))
        [freeVarP needle, groundP (encodeUnary level), groundP (encodeConst constant), groundP (encodeTy type)]
        rfl (by simp [freeVarP, valid_groundP]) rfl (by simp only [DBTerm.closeFreeAt]; rfl) .nil
  | level, .free sourceVar =>
      if same : sourceVarSame needle sourceVar = true then
        have needleEq : needle = sourceVar := (sourceVarSame_eq_true_iff _ _).mp same
        fireAt (r := closeRules[1]) (member_of_closeRules calculus (List.getElem_mem _))
          (rule_shape (by decide +kernel))
          [groundP (encodeName sourceVar.name), groundP (encodeTy sourceVar.ty), groundP (encodeUnary level)]
          rfl (by simp [valid_groundP]) rfl
          (by subst needleEq; simp only [DBTerm.closeFreeAt_exact]; rfl) .nil
      else
        have different : needle ≠ sourceVar := fun equal => same (by simp [equal])
        fireAt (r := closeRules[2]) (member_of_closeRules calculus (List.getElem_mem _))
          (rule_shape (by decide +kernel))
          [freeVarP needle, groundP (encodeUnary level), groundP (encodeName sourceVar.name),
            groundP (encodeTy sourceVar.ty)]
          rfl (by simp [freeVarP, valid_groundP]) rfl
          (by rw [DBTerm.closeFreeAt_other _ _ _ different]; rfl)
          (.cons (deriveNeq calculus _ _ (encodeTerm_free_ne different)) .nil)
  | level, .bound index =>
      fireAt (r := closeRules[3]) (member_of_closeRules calculus (List.getElem_mem _))
        (rule_shape (by decide +kernel)) [freeVarP needle, groundP (encodeUnary level), groundP (encodeUnary index)]
        rfl (by simp [freeVarP, valid_groundP]) rfl (by simp only [DBTerm.closeFreeAt]; rfl) .nil
  | level, .app function argument =>
      fireAt (r := closeRules[4]) (member_of_closeRules calculus (List.getElem_mem _))
        (rule_shape (by decide +kernel))
        [freeVarP needle, groundP (encodeUnary level), groundP (encodeTerm function), groundP (encodeTerm argument),
          groundP (encodeTerm (DBTerm.closeFreeAt needle level function)),
          groundP (encodeTerm (DBTerm.closeFreeAt needle level argument))]
        rfl (by simp [freeVarP, valid_groundP]) rfl (by simp only [DBTerm.closeFreeAt]; rfl)
        (.cons (deriveClose needle level function) (.cons (deriveClose needle level argument) .nil))
  | level, .abs domain body =>
      fireAt (r := closeRules[5]) (member_of_closeRules calculus (List.getElem_mem _))
        (rule_shape (by decide +kernel))
        [freeVarP needle, groundP (encodeUnary level), groundP (encodeTy domain), groundP (encodeTerm body),
          groundP (encodeTerm (DBTerm.closeFreeAt needle (level + 1) body))]
        rfl (by simp [freeVarP, valid_groundP]) rfl (by simp only [DBTerm.closeFreeAt]; rfl)
        (.cons (deriveClose needle (level + 1) body) .nil)

include calculus in
def deriveInstantiate (replacement : DBTerm) : (level : Nat) → (term : DBTerm) →
    Derivation definition (instantiateJ (groundP (encodeTerm replacement)) (groundP (encodeUnary level))
      (groundP (encodeTerm term)) (groundP (encodeTerm (DBTerm.instantiateAt replacement level term))))
  | level, .const constant type =>
      fireAt (r := instantiateRules[0]) (member_of_instantiateRules calculus (List.getElem_mem _))
        (rule_shape (by decide +kernel))
        [groundP (encodeTerm replacement), groundP (encodeUnary level), groundP (encodeConst constant),
          groundP (encodeTy type)]
        rfl (by simp [valid_groundP]) rfl (by simp only [DBTerm.instantiateAt]; rfl) .nil
  | level, .free sourceVar =>
      fireAt (r := instantiateRules[1]) (member_of_instantiateRules calculus (List.getElem_mem _))
        (rule_shape (by decide +kernel))
        [groundP (encodeTerm replacement), groundP (encodeUnary level), groundP (encodeName sourceVar.name),
          groundP (encodeTy sourceVar.ty)]
        rfl (by simp [valid_groundP]) rfl (by simp only [DBTerm.instantiateAt]; rfl) .nil
  | level, .bound index =>
      if target : index = level then
        fireAt (r := instantiateRules[2]) (member_of_instantiateRules calculus (List.getElem_mem _))
          (rule_shape (by decide +kernel)) [groundP (encodeTerm replacement), groundP (encodeUnary level)]
          rfl (by simp [valid_groundP]) rfl
          (by subst target; rw [DBTerm.instantiateAt_target]; rfl) .nil
      else
        fireAt (r := instantiateRules[3]) (member_of_instantiateRules calculus (List.getElem_mem _))
          (rule_shape (by decide +kernel))
          [groundP (encodeTerm replacement), groundP (encodeUnary level), groundP (encodeUnary index)]
          rfl (by simp [valid_groundP]) rfl (by rw [DBTerm.instantiateAt_other _ _ _ target]; rfl)
          (.cons (deriveNeq calculus _ _ fun same => target (encodeUnary_injective same)) .nil)
  | level, .app function argument =>
      fireAt (r := instantiateRules[4]) (member_of_instantiateRules calculus (List.getElem_mem _))
        (rule_shape (by decide +kernel))
        [groundP (encodeTerm replacement), groundP (encodeUnary level), groundP (encodeTerm function),
          groundP (encodeTerm argument), groundP (encodeTerm (DBTerm.instantiateAt replacement level function)),
          groundP (encodeTerm (DBTerm.instantiateAt replacement level argument))]
        rfl (by simp [valid_groundP]) rfl (by simp only [DBTerm.instantiateAt]; rfl)
        (.cons (deriveInstantiate replacement level function)
          (.cons (deriveInstantiate replacement level argument) .nil))
  | level, .abs domain body =>
      fireAt (r := instantiateRules[5]) (member_of_instantiateRules calculus (List.getElem_mem _))
        (rule_shape (by decide +kernel))
        [groundP (encodeTerm replacement), groundP (encodeUnary level), groundP (encodeTy domain),
          groundP (encodeTerm body), groundP (encodeTerm (DBTerm.instantiateAt replacement (level + 1) body))]
        rfl (by simp [valid_groundP]) rfl (by simp only [DBTerm.instantiateAt]; rfl)
        (.cons (deriveInstantiate replacement (level + 1) body) .nil)

/-! ## Union, erase, insertion and sorting -/

@[simp] theorem valid_treesP (trees : List LabeledTree) : Valid (treesP trees) :=
  valid_listP (by simp only [List.mem_map]; rintro _ ⟨_, -, rfl⟩; exact valid_groundP _)

theorem treesP_cons (tree : LabeledTree) (trees : List LabeledTree) :
    treesP (tree :: trees) = consP (groundP tree) (treesP trees) := rfl

include calculus in
theorem member_of_setRules {r : RuleSchema} (member : r ∈ setRules) : r ∈ definition.1.rules :=
  member_of_holRules calculus (by simp only [holRules, List.mem_append]; tauto)

include calculus in
theorem member_of_sortRules {r : RuleSchema} (member : r ∈ sortRules) : r ∈ definition.1.rules :=
  member_of_holRules calculus (by simp only [holRules, List.mem_append]; tauto)

include calculus in
def deriveUnion : (firsts seconds : List LabeledTree) →
    Derivation definition (unionJ (treesP firsts) (treesP seconds) (treesP (treeUnion firsts seconds)))
  | [], seconds =>
      fireAt (r := setRules[0]) (member_of_setRules calculus (List.getElem_mem _)) (rule_shape (by decide +kernel))
        [treesP seconds] rfl (by simp [valid_treesP]) rfl (by rw [treeUnion]; rfl) .nil
  | first :: firsts, [] =>
      fireAt (r := setRules[1]) (member_of_setRules calculus (List.getElem_mem _)) (rule_shape (by decide +kernel))
        [groundP first, treesP firsts] rfl (by simp [valid_treesP, valid_groundP]) rfl (by rw [treeUnion]; rfl) .nil
  | first :: firsts, second :: seconds =>
      if lower : first < second then
        fireAt (r := setRules[2]) (member_of_setRules calculus (List.getElem_mem _)) (rule_shape (by decide +kernel))
          [groundP first, treesP firsts, groundP second, treesP seconds, treesP (treeUnion firsts (second :: seconds))]
          rfl (by simp [valid_treesP, valid_groundP]) rfl (by rw [treeUnion, if_pos lower]; rfl)
          (.cons (deriveLt calculus first second lower) (.cons (deriveUnion firsts (second :: seconds)) .nil))
      else if upper : second < first then
        fireAt (r := setRules[3]) (member_of_setRules calculus (List.getElem_mem _)) (rule_shape (by decide +kernel))
          [groundP first, treesP firsts, groundP second, treesP seconds, treesP (treeUnion (first :: firsts) seconds)]
          rfl (by simp [valid_treesP, valid_groundP]) rfl (by rw [treeUnion, if_neg lower, if_pos upper]; rfl)
          (.cons (deriveLt calculus second first upper) (.cons (deriveUnion (first :: firsts) seconds) .nil))
      else
        have same : first = second := (lt_trichotomy first second).resolve_left lower |>.resolve_right upper
        fireAt (r := setRules[4]) (member_of_setRules calculus (List.getElem_mem _)) (rule_shape (by decide +kernel))
          [groundP first, treesP firsts, treesP seconds, treesP (treeUnion firsts seconds)]
          rfl (by simp [valid_treesP, valid_groundP]) rfl
          (by rw [treeUnion, if_neg lower, if_neg upper, ← same]; rfl)
          (.cons (deriveUnion firsts seconds) .nil)
termination_by firsts seconds => firsts.length + seconds.length

include calculus in
def deriveErase (tree : LabeledTree) : (trees : List LabeledTree) →
    Derivation definition (eraseJ (groundP tree) (treesP trees) (treesP (treeErase tree trees)))
  | [] =>
      fireAt (r := setRules[5]) (member_of_setRules calculus (List.getElem_mem _)) (rule_shape (by decide +kernel))
        [groundP tree] rfl (by simp [valid_groundP]) rfl (by rw [treeErase]; rfl) .nil
  | first :: rest =>
      if same : first = tree then
        fireAt (r := setRules[6]) (member_of_setRules calculus (List.getElem_mem _)) (rule_shape (by decide +kernel))
          [groundP tree, treesP rest] rfl (by simp [valid_treesP, valid_groundP]) rfl
          (by rw [treeErase, if_pos same, same]; rfl) .nil
      else
        fireAt (r := setRules[7]) (member_of_setRules calculus (List.getElem_mem _)) (rule_shape (by decide +kernel))
          [groundP tree, groundP first, treesP rest, treesP (treeErase tree rest)] rfl
          (by simp [valid_treesP, valid_groundP]) rfl (by rw [treeErase, if_neg same]; rfl)
          (.cons (deriveNeq calculus tree first fun equal => same equal.symm) (.cons (deriveErase tree rest) .nil))

include calculus in
def deriveInsert (tree : LabeledTree) : (trees : List LabeledTree) →
    Derivation definition (insertJ (groundP tree) (treesP trees) (treesP (treeInsert tree trees)))
  | [] =>
      fireAt (r := sortRules[0]) (member_of_sortRules calculus (List.getElem_mem _)) (rule_shape (by decide +kernel))
        [groundP tree] rfl (by simp [valid_groundP]) rfl (by rw [treeInsert]; rfl) .nil
  | first :: rest =>
      if same : tree = first then
        fireAt (r := sortRules[1]) (member_of_sortRules calculus (List.getElem_mem _)) (rule_shape (by decide +kernel))
          [groundP tree, treesP rest] rfl (by simp [valid_treesP, valid_groundP]) rfl
          (by rw [treeInsert, if_pos same, ← same]; rfl) .nil
      else if lower : tree < first then
        fireAt (r := sortRules[2]) (member_of_sortRules calculus (List.getElem_mem _)) (rule_shape (by decide +kernel))
          [groundP tree, groundP first, treesP rest] rfl (by simp [valid_treesP, valid_groundP]) rfl
          (by rw [treeInsert, if_neg same, if_pos lower]; rfl)
          (.cons (deriveLt calculus tree first lower) .nil)
      else
        have upper : first < tree := (lt_trichotomy tree first).resolve_left lower |>.resolve_left same
        fireAt (r := sortRules[3]) (member_of_sortRules calculus (List.getElem_mem _)) (rule_shape (by decide +kernel))
          [groundP tree, groundP first, treesP rest, treesP (treeInsert tree rest)] rfl
          (by simp [valid_treesP, valid_groundP]) rfl (by rw [treeInsert, if_neg same, if_neg lower]; rfl)
          (.cons (deriveLt calculus first tree upper) (.cons (deriveInsert tree rest) .nil))

include calculus in
def deriveSort : (trees : List LabeledTree) → Derivation definition (sortJ (treesP trees) (treesP (treeSort trees)))
  | [] =>
      fireAt (r := sortRules[4]) (member_of_sortRules calculus (List.getElem_mem _)) (rule_shape (by decide +kernel))
        [] rfl (by simp) rfl (by rw [treeSort]; rfl) .nil
  | first :: rest =>
      fireAt (r := sortRules[5]) (member_of_sortRules calculus (List.getElem_mem _)) (rule_shape (by decide +kernel))
        [groundP first, treesP rest, treesP (treeSort rest), treesP (treeInsert first (treeSort rest))] rfl
        (by simp [valid_treesP, valid_groundP]) rfl (by rw [treeSort]; rfl)
        (.cons (deriveSort rest) (.cons (deriveInsert calculus first (treeSort rest)) .nil))

/-! ## Type instantiation -/

@[simp] theorem valid_typeMapletsP (entries : List (Ty × Ty)) : Valid (typeMapletsP entries) :=
  valid_listP (by
    simp only [List.mem_map]
    rintro _ ⟨⟨first, second⟩, -, rfl⟩
    exact valid_treeP (by simp [valid_groundP]))

@[simp] theorem valid_tysP (types : List Ty) : Valid (tysP types) :=
  valid_listP (by simp only [List.mem_map]; rintro _ ⟨_, -, rfl⟩; exact valid_groundP _)

theorem typeMapletsP_cons_op (replacement : Ty) (operator : TypeOp) (arguments : List Ty) (rest : List (Ty × Ty)) :
    typeMapletsP ((replacement, .op operator arguments) :: rest) =
      consP (typeMapletP (groundP (encodeTy replacement)) (tyOpP (groundP (encodeTypeOp operator)) (tysP arguments)))
        (typeMapletsP rest) := by
  simp only [typeMapletsP, listP, List.map_cons, groundP_encodeTy_op]
  rfl

include calculus in
theorem member_of_typeActionRules {r : RuleSchema} (member : r ∈ typeActionRules) : r ∈ definition.1.rules :=
  member_of_holRules calculus (by simp only [holRules, List.mem_append]; tauto)

include calculus in
def deriveVarType : (entries : List (Ty × Ty)) → (name : Name) →
    Derivation definition (varTypeJ (typeMapletsP entries) (groundP (encodeName name))
      (groundP (encodeTy (SourceSubstitution.variableType entries name))))
  | [], name =>
      fireAt (r := typeActionRules[0]) (member_of_typeActionRules calculus (List.getElem_mem _))
        (rule_shape (by decide +kernel)) [groundP (encodeName name)] rfl (by simp [valid_groundP]) rfl rfl .nil
  | (replacement, .var key) :: rest, name =>
      if same : name = key then
        fireAt (r := typeActionRules[1]) (member_of_typeActionRules calculus (List.getElem_mem _))
          (rule_shape (by decide +kernel))
          [groundP (encodeTy replacement), groundP (encodeName key), typeMapletsP rest] rfl
          (by simp [valid_groundP, valid_typeMapletsP]) rfl
          (by subst same; simp only [SourceSubstitution.variableType, if_true]; rfl) .nil
      else
        fireAt (r := typeActionRules[2]) (member_of_typeActionRules calculus (List.getElem_mem _))
          (rule_shape (by decide +kernel))
          [groundP (encodeTy replacement), groundP (encodeName key), typeMapletsP rest, groundP (encodeName name),
            groundP (encodeTy (SourceSubstitution.variableType rest name))] rfl
          (by simp [valid_groundP, valid_typeMapletsP]) rfl
          (by simp only [SourceSubstitution.variableType, if_neg same]; rfl)
          (.cons (deriveNeq calculus _ _ fun equal => same (encodeName_injective equal))
            (.cons (deriveVarType rest name) .nil))
  | (replacement, .op operator arguments) :: rest, name =>
      fireAt (r := typeActionRules[3]) (member_of_typeActionRules calculus (List.getElem_mem _))
        (rule_shape (by decide +kernel))
        [groundP (encodeTy replacement), groundP (encodeTypeOp operator), tysP arguments, typeMapletsP rest,
          groundP (encodeName name), groundP (encodeTy (SourceSubstitution.variableType rest name))] rfl
        (by simp [valid_groundP, valid_typeMapletsP, valid_tysP]) rfl
        (by rw [typeMapletsP_cons_op]; simp only [SourceSubstitution.variableType]; rfl)
        (.cons (deriveVarType rest name) .nil)

mutual
  def deriveTyAct (entries : List (Ty × Ty)) : (type : Ty) →
      Derivation definition (tyActJ (typeMapletsP entries) (groundP (encodeTy type))
        (groundP (encodeTy (SourceSubstitution.typeAction entries type))))
    | .var name =>
        fireAt (r := typeActionRules[4]) (member_of_typeActionRules calculus (List.getElem_mem _))
          (rule_shape (by decide +kernel))
          [typeMapletsP entries, groundP (encodeName name),
            groundP (encodeTy (SourceSubstitution.variableType entries name))] rfl
          (by simp [valid_groundP, valid_typeMapletsP]) rfl
          (by simp only [SourceSubstitution.typeAction]; rfl)
          (.cons (deriveVarType calculus entries name) .nil)
    | .op operator arguments =>
        fireAt (r := typeActionRules[5]) (member_of_typeActionRules calculus (List.getElem_mem _))
          (rule_shape (by decide +kernel))
          [typeMapletsP entries, groundP (encodeTypeOp operator), tysP arguments,
            tysP (arguments.map (SourceSubstitution.typeAction entries))] rfl
          (by simp [valid_groundP, valid_typeMapletsP, valid_tysP]) rfl
          (by simp only [SourceSubstitution.typeAction, groundP_encodeTy_op]; rfl)
          (.cons (deriveTyActList entries arguments) .nil)

  def deriveTyActList (entries : List (Ty × Ty)) : (types : List Ty) →
      Derivation definition (tyActListJ (typeMapletsP entries) (tysP types)
        (tysP (types.map (SourceSubstitution.typeAction entries))))
    | [] =>
        fireAt (r := typeActionRules[6]) (member_of_typeActionRules calculus (List.getElem_mem _))
          (rule_shape (by decide +kernel)) [typeMapletsP entries] rfl (by simp [valid_typeMapletsP]) rfl rfl .nil
    | type :: rest =>
        fireAt (r := typeActionRules[7]) (member_of_typeActionRules calculus (List.getElem_mem _))
          (rule_shape (by decide +kernel))
          [typeMapletsP entries, groundP (encodeTy type), tysP rest,
            groundP (encodeTy (SourceSubstitution.typeAction entries type)),
            tysP (rest.map (SourceSubstitution.typeAction entries))] rfl
          (by simp [valid_groundP, valid_typeMapletsP, valid_tysP]) rfl rfl
          (.cons (deriveTyAct entries type) (.cons (deriveTyActList entries rest) .nil))
end

include calculus in
def deriveTermTyAct (entries : List (Ty × Ty)) : (term : DBTerm) →
    Derivation definition (termTyActJ (typeMapletsP entries) (groundP (encodeTerm term))
      (groundP (encodeTerm (termTypeAction entries term))))
  | .const constant type =>
      fireAt (r := typeActionRules[8]) (member_of_typeActionRules calculus (List.getElem_mem _))
        (rule_shape (by decide +kernel))
        [typeMapletsP entries, groundP (encodeConst constant), groundP (encodeTy type),
          groundP (encodeTy (SourceSubstitution.typeAction entries type))] rfl
        (by simp [valid_groundP, valid_typeMapletsP]) rfl rfl
        (.cons (deriveTyAct calculus entries type) .nil)
  | .free sourceVar =>
      fireAt (r := typeActionRules[9]) (member_of_typeActionRules calculus (List.getElem_mem _))
        (rule_shape (by decide +kernel))
        [typeMapletsP entries, groundP (encodeName sourceVar.name), groundP (encodeTy sourceVar.ty),
          groundP (encodeTy (SourceSubstitution.typeAction entries sourceVar.ty))] rfl
        (by simp [valid_groundP, valid_typeMapletsP]) rfl rfl
        (.cons (deriveTyAct calculus entries sourceVar.ty) .nil)
  | .bound index =>
      fireAt (r := typeActionRules[10]) (member_of_typeActionRules calculus (List.getElem_mem _))
        (rule_shape (by decide +kernel)) [typeMapletsP entries, groundP (encodeUnary index)] rfl
        (by simp [valid_groundP, valid_typeMapletsP]) rfl rfl .nil
  | .app function argument =>
      fireAt (r := typeActionRules[11]) (member_of_typeActionRules calculus (List.getElem_mem _))
        (rule_shape (by decide +kernel))
        [typeMapletsP entries, groundP (encodeTerm function), groundP (encodeTerm argument),
          groundP (encodeTerm (termTypeAction entries function)), groundP (encodeTerm (termTypeAction entries argument))]
        rfl (by simp [valid_groundP, valid_typeMapletsP]) rfl rfl
        (.cons (deriveTermTyAct entries function) (.cons (deriveTermTyAct entries argument) .nil))
  | .abs domain body =>
      fireAt (r := typeActionRules[12]) (member_of_typeActionRules calculus (List.getElem_mem _))
        (rule_shape (by decide +kernel))
        [typeMapletsP entries, groundP (encodeTy domain), groundP (encodeTerm body),
          groundP (encodeTy (SourceSubstitution.typeAction entries domain)),
          groundP (encodeTerm (termTypeAction entries body))]
        rfl (by simp [valid_groundP, valid_typeMapletsP]) rfl rfl
        (.cons (deriveTyAct calculus entries domain) (.cons (deriveTermTyAct entries body) .nil))

include calculus in
def deriveTermTyActList (entries : List (Ty × Ty)) : (terms : List DBTerm) →
    Derivation definition (termTyActListJ (typeMapletsP entries) (termsP terms)
      (termsP (terms.map (termTypeAction entries))))
  | [] =>
      fireAt (r := typeActionRules[13]) (member_of_typeActionRules calculus (List.getElem_mem _))
        (rule_shape (by decide +kernel)) [typeMapletsP entries] rfl (by simp [valid_typeMapletsP]) rfl rfl .nil
  | term :: rest =>
      fireAt (r := typeActionRules[14]) (member_of_typeActionRules calculus (List.getElem_mem _))
        (rule_shape (by decide +kernel))
        [typeMapletsP entries, groundP (encodeTerm term), termsP rest,
          groundP (encodeTerm (termTypeAction entries term)), termsP (rest.map (termTypeAction entries))] rfl
        (by simp [valid_groundP, valid_typeMapletsP, valid_termsP]) rfl rfl
        (.cons (deriveTermTyAct calculus entries term) (.cons (deriveTermTyActList entries rest) .nil))

/-! ## Term instantiation -/

@[simp] theorem valid_tableP (entries : List (SourceVar × CheckedSourceTerm)) : Valid (tableP entries) :=
  valid_listP (by
    simp only [List.mem_map]
    rintro _ ⟨⟨key, replacement⟩, -, rfl⟩
    exact valid_treeP (by simp [freeVarP, valid_groundP]))

@[simp] theorem valid_termMapletsP (maplets : List SourceSubstitution.TermMaplet) : Valid (termMapletsP maplets) :=
  valid_listP (by
    simp only [List.mem_map]
    rintro _ ⟨⟨replacement, key⟩, -, rfl⟩
    exact valid_treeP (by simp [valid_groundP]))

include calculus in
theorem member_of_termActionRules {r : RuleSchema} (member : r ∈ termActionRules) : r ∈ definition.1.rules :=
  member_of_holRules calculus (by simp only [holRules, List.mem_append]; tauto)

include calculus in
def deriveAdmit : (maplets : List SourceSubstitution.TermMaplet) → SourceSubstitution.TermMapletsAdmissible maplets →
    Derivation definition (admitTmJ (termMapletsP maplets) (tableP (SourceSubstitution.termEntries maplets)))
  | [], _ =>
      fireAt (r := termActionRules[0]) (member_of_termActionRules calculus (List.getElem_mem _))
        (rule_shape (by decide +kernel)) [] rfl (by simp) rfl rfl .nil
  | (replacement, .var name type) :: rest, admissible =>
      have typeEq : replacement.ty = type := admissible _ (List.mem_cons.mpr (Or.inl rfl))
      have typed : (replacement.source.toDB []).inferType [] = some type := by
        rw [← typeEq, ← replacement.checked]
        exact DBTerm.inferType_toDB [] replacement.source
      fireAt (r := termActionRules[1]) (member_of_termActionRules calculus (List.getElem_mem _))
        (rule_shape (by decide +kernel))
        [groundP (encodeSourceTerm replacement.source), groundP (encodeName name), groundP (encodeTy type),
          groundP (encodeTerm (replacement.source.toDB [])), termMapletsP rest,
          tableP (SourceSubstitution.termEntries rest)] rfl
        (by simp [valid_groundP, valid_termMapletsP, valid_tableP]) rfl rfl
        (.cons (deriveName calculus name) (.cons (deriveToDB calculus [] replacement.source)
          (.cons (deriveTypeOf calculus [] _ type typed)
            (.cons (deriveAdmit rest fun entry member => admissible entry (List.mem_cons_of_mem _ member)) .nil))))
  | (_, .const _ _) :: _, admissible => absurd (admissible _ (List.mem_cons.mpr (Or.inl rfl))) id
  | (_, .app _ _) :: _, admissible => absurd (admissible _ (List.mem_cons.mpr (Or.inl rfl))) id
  | (_, .abs _ _ _) :: _, admissible => absurd (admissible _ (List.mem_cons.mpr (Or.inl rfl))) id

include calculus in
def deriveLookup (needle : SourceVar) (replacement : CheckedSourceTerm) :
    (entries : List (SourceVar × CheckedSourceTerm)) →
      TermSubst.lookup ⟨TypeSubst.empty, entries⟩ needle = some replacement →
        Derivation definition (tmLookupJ (tableP entries) (freeVarP needle)
          (groundP (encodeTerm replacement.canonical.term)))
  | (key, value) :: rest, found =>
      if keySame : sourceVarSame key needle = true then
        have same : key = needle := (sourceVarSame_eq_true_iff _ _).mp keySame
        have valueEq : value = replacement := by
          subst same
          rw [lookup_cons_same] at found
          exact Option.some.inj found
        fireAt (r := termActionRules[2]) (member_of_termActionRules calculus (List.getElem_mem _))
          (rule_shape (by decide +kernel))
          [freeVarP key, groundP (encodeTerm value.canonical.term), tableP rest] rfl
          (by simp [freeVarP, valid_groundP, valid_tableP]) rfl (by subst same valueEq; rfl) .nil
      else
        fireAt (r := termActionRules[3]) (member_of_termActionRules calculus (List.getElem_mem _))
          (rule_shape (by decide +kernel))
          [freeVarP key, groundP (encodeTerm value.canonical.term), tableP rest, freeVarP needle,
            groundP (encodeTerm replacement.canonical.term)] rfl
          (by simp [freeVarP, valid_groundP, valid_tableP]) rfl rfl
          (.cons (deriveNeq calculus _ _ (encodeTerm_free_ne fun equal => keySame (by simp [equal])))
            (.cons (deriveLookup needle replacement rest
              (by rw [lookup_cons_other fun equal => keySame (by simp [equal])] at found; exact found)) .nil))
  | [], found => absurd found (by simp [TermSubst.lookup])

include calculus in
def deriveNoKey (needle : SourceVar) : (entries : List (SourceVar × CheckedSourceTerm)) →
    TermSubst.lookup ⟨TypeSubst.empty, entries⟩ needle = none →
      Derivation definition (tmNoKeyJ (tableP entries) (freeVarP needle))
  | [], _ =>
      fireAt (r := termActionRules[4]) (member_of_termActionRules calculus (List.getElem_mem _))
        (rule_shape (by decide +kernel)) [freeVarP needle] rfl (by simp [freeVarP, valid_groundP]) rfl rfl .nil
  | (key, value) :: rest, missing =>
      have different : key ≠ needle := fun same => by
        subst same
        rw [lookup_cons_same] at missing
        cases missing
      fireAt (r := termActionRules[5]) (member_of_termActionRules calculus (List.getElem_mem _))
        (rule_shape (by decide +kernel))
        [freeVarP key, groundP (encodeTerm value.canonical.term), tableP rest, freeVarP needle] rfl
        (by simp [freeVarP, valid_groundP, valid_tableP]) rfl rfl
        (.cons (deriveNeq calculus _ _ (encodeTerm_free_ne fun equal => different equal.symm))
          (.cons (deriveNoKey needle rest (by rw [lookup_cons_other different] at missing; exact missing)) .nil))

include calculus in
def deriveTmApply (entries : List (SourceVar × CheckedSourceTerm)) : (term : DBTerm) →
    Derivation definition (tmApplyJ (tableP entries) (groundP (encodeTerm term))
      (groundP (encodeTerm (tableAction entries term))))
  | .const constant type =>
      fireAt (r := termActionRules[6]) (member_of_termActionRules calculus (List.getElem_mem _))
        (rule_shape (by decide +kernel)) [tableP entries, groundP (encodeConst constant), groundP (encodeTy type)] rfl
        (by simp [valid_groundP, valid_tableP]) rfl
        (by simp only [tableAction, TermSubst.applyDB_const, TypeSubst.apply_empty]; rfl) .nil
  | .free sourceVar =>
      match found : TermSubst.lookup ⟨TypeSubst.empty, entries⟩ sourceVar with
      | some replacement =>
          fireAt (r := termActionRules[7]) (member_of_termActionRules calculus (List.getElem_mem _))
            (rule_shape (by decide +kernel))
            [tableP entries, groundP (encodeName sourceVar.name), groundP (encodeTy sourceVar.ty),
              groundP (encodeTerm replacement.canonical.term)] rfl
            (by simp [valid_groundP, valid_tableP]) rfl
            (by rw [tableAction_free_of_lookup_some found]; rfl)
            (.cons (deriveLookup calculus sourceVar replacement entries found) .nil)
      | none =>
          fireAt (r := termActionRules[8]) (member_of_termActionRules calculus (List.getElem_mem _))
            (rule_shape (by decide +kernel))
            [tableP entries, groundP (encodeName sourceVar.name), groundP (encodeTy sourceVar.ty)] rfl
            (by simp [valid_groundP, valid_tableP]) rfl
            (by rw [tableAction_free_of_lookup_none found]; rfl)
            (.cons (deriveNoKey calculus sourceVar entries found) .nil)
  | .bound index =>
      fireAt (r := termActionRules[9]) (member_of_termActionRules calculus (List.getElem_mem _))
        (rule_shape (by decide +kernel)) [tableP entries, groundP (encodeUnary index)] rfl
        (by simp [valid_groundP, valid_tableP]) rfl
        (by simp only [tableAction, TermSubst.applyDB_bound]; rfl) .nil
  | .app function argument =>
      fireAt (r := termActionRules[10]) (member_of_termActionRules calculus (List.getElem_mem _))
        (rule_shape (by decide +kernel))
        [tableP entries, groundP (encodeTerm function), groundP (encodeTerm argument),
          groundP (encodeTerm (tableAction entries function)), groundP (encodeTerm (tableAction entries argument))]
        rfl (by simp [valid_groundP, valid_tableP]) rfl
        (by simp only [tableAction, TermSubst.applyDB_app]; rfl)
        (.cons (deriveTmApply entries function) (.cons (deriveTmApply entries argument) .nil))
  | .abs domain body =>
      fireAt (r := termActionRules[11]) (member_of_termActionRules calculus (List.getElem_mem _))
        (rule_shape (by decide +kernel))
        [tableP entries, groundP (encodeTy domain), groundP (encodeTerm body),
          groundP (encodeTerm (tableAction entries body))]
        rfl (by simp [valid_groundP, valid_tableP]) rfl
        (by simp only [tableAction, TermSubst.applyDB_abs, TypeSubst.apply_empty]; rfl)
        (.cons (deriveTmApply entries body) .nil)

include calculus in
def deriveTmApplyList (entries : List (SourceVar × CheckedSourceTerm)) : (terms : List DBTerm) →
    Derivation definition (tmApplyListJ (tableP entries) (termsP terms) (termsP (terms.map (tableAction entries))))
  | [] =>
      fireAt (r := termActionRules[12]) (member_of_termActionRules calculus (List.getElem_mem _))
        (rule_shape (by decide +kernel)) [tableP entries] rfl (by simp [valid_tableP]) rfl rfl .nil
  | term :: rest =>
      fireAt (r := termActionRules[13]) (member_of_termActionRules calculus (List.getElem_mem _))
        (rule_shape (by decide +kernel))
        [tableP entries, groundP (encodeTerm term), termsP rest, groundP (encodeTerm (tableAction entries term)),
          termsP (rest.map (tableAction entries))] rfl
        (by simp [valid_groundP, valid_tableP, valid_termsP]) rfl rfl
        (.cons (deriveTmApply calculus entries term) (.cons (deriveTmApplyList entries rest) .nil))

/-! ## The inference rules, at given premises -/

include calculus in
theorem member_of_inferenceRules {r : RuleSchema} (member : r ∈ inferenceRules) : r ∈ definition.1.rules :=
  member_of_holRules calculus (by simp only [holRules, List.mem_append]; tauto)

include calculus in
theorem member_of_instantiationRules {r : RuleSchema} (member : r ∈ instantiationRules) :
    r ∈ definition.1.rules :=
  member_of_holRules calculus (by simp only [holRules, List.mem_append]; tauto)

include calculus in
def deriveReflRule {t a : Pattern} (valid : ∀ argument ∈ [t, a], Valid argument)
    (typed : Derivation definition (typeOfJ nilP t a)) :
    Derivation definition (thmJ nilP (equalityTermP a t t)) :=
  fireAt (r := inferenceRules[0]) (member_of_inferenceRules calculus (List.getElem_mem _))
    (rule_shape (by decide +kernel)) [t, a] rfl valid
    (by fire_simp [inferenceRules]) (by fire_simp [inferenceRules])
    (.cons typed .nil)

include calculus in
def deriveAssumeRule {t : Pattern} (valid : ∀ argument ∈ [t], Valid argument)
    (typed : Derivation definition (typeOfJ nilP t boolP)) : Derivation definition (thmJ (consP t nilP) t) :=
  fireAt (r := inferenceRules[1]) (member_of_inferenceRules calculus (List.getElem_mem _))
    (rule_shape (by decide +kernel)) [t] rfl valid (by fire_simp [inferenceRules]) (by fire_simp [inferenceRules])
    (.cons typed .nil)

include calculus in
def deriveTransRule {h1 h2 h a l m r : Pattern} (valid : ∀ argument ∈ [h1, h2, h, a, l, m, r], Valid argument)
    (left : Derivation definition (thmJ h1 (equalityTermP a l m)))
    (right : Derivation definition (thmJ h2 (equalityTermP a m r)))
    (union : Derivation definition (unionJ h1 h2 h)) : Derivation definition (thmJ h (equalityTermP a l r)) :=
  fireAt (r := inferenceRules[2]) (member_of_inferenceRules calculus (List.getElem_mem _))
    (rule_shape (by decide +kernel)) [h1, h2, h, a, l, m, r] rfl valid
    (by fire_simp [inferenceRules])
    (by fire_simp [inferenceRules])
    (.cons left (.cons right (.cons union .nil)))

include calculus in
def deriveMkCombRule {h1 h2 h a b f g x y : Pattern}
    (valid : ∀ argument ∈ [h1, h2, h, a, b, f, g, x, y], Valid argument)
    (functions : Derivation definition (thmJ h1 (equalityTermP (functionTyP a b) f g)))
    (arguments : Derivation definition (thmJ h2 (equalityTermP a x y)))
    (union : Derivation definition (unionJ h1 h2 h)) :
    Derivation definition (thmJ h (equalityTermP b (appTermP f x) (appTermP g y))) :=
  fireAt (r := inferenceRules[3]) (member_of_inferenceRules calculus (List.getElem_mem _))
    (rule_shape (by decide +kernel)) [h1, h2, h, a, b, f, g, x, y] rfl valid
    (by fire_simp [inferenceRules])
    (by fire_simp [inferenceRules])
    (.cons functions (.cons arguments (.cons union .nil)))

include calculus in
def deriveAbsRule {h a s t x b s2 t2 : Pattern} (valid : ∀ argument ∈ [h, a, s, t, x, b, s2, t2], Valid argument)
    (input : Derivation definition (thmJ h (equalityTermP a s t)))
    (named : Derivation definition (wfJ "Name" x)) (typedBinder : Derivation definition (wfJ "Ty" b))
    (fresh : Derivation definition (notFreeAllJ (freeTermP x b) h))
    (leftClosed : Derivation definition (closeJ (freeTermP x b) unaryZeroP s s2))
    (rightClosed : Derivation definition (closeJ (freeTermP x b) unaryZeroP t t2)) :
    Derivation definition (thmJ h (equalityTermP (functionTyP b a) (absTermP b s2) (absTermP b t2))) :=
  fireAt (r := inferenceRules[4]) (member_of_inferenceRules calculus (List.getElem_mem _))
    (rule_shape (by decide +kernel)) [h, a, s, t, x, b, s2, t2] rfl valid
    (by fire_simp [inferenceRules])
    (by fire_simp [inferenceRules])
    (.cons input (.cons named (.cons typedBinder (.cons fresh (.cons leftClosed (.cons rightClosed .nil))))))

include calculus in
def deriveBetaRule {x a t body u reduced : Pattern} (valid : ∀ argument ∈ [x, a, t, body, u, reduced], Valid argument)
    (converted : Derivation definition (toDBJ nilP (sourceAppP (sourceAbsP x a t) (sourceVarP x a))
      (appTermP (absTermP a body) (freeTermP x a))))
    (typed : Derivation definition (typeOfJ nilP (appTermP (absTermP a body) (freeTermP x a)) u))
    (instantiated : Derivation definition (instantiateJ (freeTermP x a) unaryZeroP body reduced)) :
    Derivation definition (thmJ nilP (equalityTermP u (appTermP (absTermP a body) (freeTermP x a)) reduced)) :=
  fireAt (r := inferenceRules[5]) (member_of_inferenceRules calculus (List.getElem_mem _))
    (rule_shape (by decide +kernel)) [x, a, t, body, u, reduced] rfl valid
    (by fire_simp [inferenceRules])
    (by fire_simp [inferenceRules])
    (.cons converted (.cons typed (.cons instantiated .nil)))

include calculus in
def deriveEqMpRule {h1 h2 h a p q : Pattern} (valid : ∀ argument ∈ [h1, h2, h, a, p, q], Valid argument)
    (equality : Derivation definition (thmJ h1 (equalityTermP a p q)))
    (premise : Derivation definition (thmJ h2 p)) (union : Derivation definition (unionJ h1 h2 h)) :
    Derivation definition (thmJ h q) :=
  fireAt (r := inferenceRules[6]) (member_of_inferenceRules calculus (List.getElem_mem _))
    (rule_shape (by decide +kernel)) [h1, h2, h, a, p, q] rfl valid
    (by fire_simp [inferenceRules])
    (by fire_simp [inferenceRules]) (.cons equality (.cons premise (.cons union .nil)))

include calculus in
def deriveDeductAntisymRule {h1 h2 k1 k2 h p q a : Pattern}
    (valid : ∀ argument ∈ [h1, h2, k1, k2, h, p, q, a], Valid argument)
    (left : Derivation definition (thmJ h1 p)) (right : Derivation definition (thmJ h2 q))
    (leftTyped : Derivation definition (typeOfJ nilP p a)) (rightTyped : Derivation definition (typeOfJ nilP q a))
    (leftErase : Derivation definition (eraseJ q h1 k1)) (rightErase : Derivation definition (eraseJ p h2 k2))
    (union : Derivation definition (unionJ k1 k2 h)) : Derivation definition (thmJ h (equalityTermP a p q)) :=
  fireAt (r := inferenceRules[7]) (member_of_inferenceRules calculus (List.getElem_mem _))
    (rule_shape (by decide +kernel)) [h1, h2, k1, k2, h, p, q, a] rfl valid
    (by fire_simp [inferenceRules])
    (by fire_simp [inferenceRules])
    (.cons left (.cons right (.cons leftTyped (.cons rightTyped (.cons leftErase (.cons rightErase
      (.cons union .nil)))))))

include calculus in
def deriveInstRule {h c ms table h1 h2 c2 : Pattern} (valid : ∀ argument ∈ [h, c, ms, table, h1, h2, c2], Valid argument)
    (input : Derivation definition (thmJ h c)) (admitted : Derivation definition (admitTmJ ms table))
    (hypotheses : Derivation definition (tmApplyListJ table h h1)) (sorted : Derivation definition (sortJ h1 h2))
    (concluded : Derivation definition (tmApplyJ table c c2)) : Derivation definition (thmJ h2 c2) :=
  fireAt (r := instantiationRules[0]) (member_of_instantiationRules calculus (List.getElem_mem _))
    (rule_shape (by decide +kernel)) [h, c, ms, table, h1, h2, c2] rfl valid
    (by fire_simp [instantiationRules]) (by fire_simp [instantiationRules])
    (.cons input (.cons admitted (.cons hypotheses (.cons sorted (.cons concluded .nil)))))

include calculus in
def deriveInstTypeRule {h c es h1 h2 c2 : Pattern} (valid : ∀ argument ∈ [h, c, es, h1, h2, c2], Valid argument)
    (input : Derivation definition (thmJ h c)) (entries : Derivation definition (wfJ "TypeMaplets" es))
    (hypotheses : Derivation definition (termTyActListJ es h h1)) (sorted : Derivation definition (sortJ h1 h2))
    (concluded : Derivation definition (termTyActJ es c c2)) : Derivation definition (thmJ h2 c2) :=
  fireAt (r := instantiationRules[1]) (member_of_instantiationRules calculus (List.getElem_mem _))
    (rule_shape (by decide +kernel)) [h, c, es, h1, h2, c2] rfl valid
    (by fire_simp [instantiationRules]) (by fire_simp [instantiationRules])
    (.cons input (.cons entries (.cons hypotheses (.cons sorted (.cons concluded .nil)))))

/-! ## Each inference of HOL Light as a derivation -/

@[simp] theorem valid_sequentHypothesesP (sequent : Sequent) : Valid (sequentHypothesesP sequent) := by
  rw [sequentHypothesesP_eq_treesP]
  exact valid_treesP _

@[simp] theorem valid_sequentConclusionP (sequent : Sequent) : Valid (sequentConclusionP sequent) := valid_groundP _

/-- A derivation of a rendered sequent as a derivation of its `Thm` judgment, with computed sides. -/
def asThm {sequent : Sequent} {hypotheses conclusion : Pattern}
    (hypothesesEq : sequentHypothesesP sequent = hypotheses) (conclusionEq : sequentConclusionP sequent = conclusion)
    (derivation : Derivation definition (sequentJ sequent)) : Derivation definition (thmJ hypotheses conclusion) :=
  recast (by rw [← hypothesesEq, ← conclusionEq]; rfl) derivation

/-- A derivation of a `Thm` judgment as a derivation of the rendered sequent it is. -/
def ofThm {sequent : Sequent} {hypotheses conclusion : Pattern}
    (hypothesesEq : hypotheses = sequentHypothesesP sequent) (conclusionEq : conclusion = sequentConclusionP sequent)
    (derivation : Derivation definition (thmJ hypotheses conclusion)) : Derivation definition (sequentJ sequent) :=
  recast (by rw [hypothesesEq, conclusionEq]; rfl) derivation

theorem sequentHypothesesP_of_hyp {sequent : Sequent} {hypotheses : Finset CanonicalTerm}
    (same : sequent.hyp = hypotheses) : sequentHypothesesP sequent = treesP (hypothesisTrees hypotheses) := by
  rw [sequentHypothesesP_eq_treesP, same]

theorem sequentConclusionP_of_term {sequent : Sequent} {term : DBTerm} (same : sequent.concl.term = term) :
    sequentConclusionP sequent = groundP (encodeTerm term) := by
  simp only [sequentConclusionP, encodeCanonical, same]

include calculus in
theorem refl_complete {term : CanonicalTerm} {out : Theorem} (semantics : ReflSemantics term out) :
    Nonempty (Derivation definition (sequentJ out.sequent)) := by
  obtain ⟨equality, ⟨-, shape⟩, -, hypEq, conclEq⟩ := semantics
  have conclusionTerm : out.sequent.concl.term = CanonicalTerm.equalityDB term.ty term.term term.term := by
    rw [conclEq, shape]
  exact ⟨ofThm (by rw [sequentHypothesesP_of_hyp hypEq, hypothesisTrees_empty]; rfl)
    (by rw [sequentConclusionP_of_term conclusionTerm]; rfl)
    (deriveReflRule calculus (by simp [valid_groundP]) (deriveTypeOf calculus [] term.term term.ty term.checked))⟩

include calculus in
theorem assume_complete {term : CanonicalTerm} {out : Theorem} (semantics : AssumeSemantics term out) :
    Nonempty (Derivation definition (sequentJ out.sequent)) := by
  obtain ⟨isBool, -, hypEq, conclEq⟩ := semantics
  have typed : term.term.inferType [] = some Ty.bool := by
    rw [term.checked]
    exact congrArg some isBool
  exact ⟨ofThm (by rw [sequentHypothesesP_of_hyp hypEq, hypothesisTrees_singleton]; rfl)
    (by rw [sequentConclusionP_of_term (congrArg CanonicalTerm.term conclEq)])
    (deriveAssumeRule calculus (by simp [valid_groundP]) (deriveTypeOf calculus [] term.term Ty.bool typed))⟩

include calculus in
theorem trans_complete {left right out : Theorem} (semantics : TransSemantics left right out)
    (leftDerived : Derivation definition (sequentJ left.sequent))
    (rightDerived : Derivation definition (sequentJ right.sequent)) :
    Nonempty (Derivation definition (sequentJ out.sequent)) := by
  obtain ⟨first, middle, middle', last, equality, ⟨firstTypes, leftShape⟩, ⟨lastTypes, rightShape⟩, rfl,
    ⟨-, shape⟩, -, hypEq, conclEq⟩ := semantics
  have conclusionTerm : out.sequent.concl.term = CanonicalTerm.equalityDB first.ty first.term last.term := by
    rw [conclEq, shape]
  have leftThm := asThm (sequentHypothesesP_eq_treesP _) (sequentConclusionP_of_term leftShape) leftDerived
  have rightThm := asThm (sequentHypothesesP_eq_treesP _)
    (by rw [sequentConclusionP_of_term rightShape, ← firstTypes]) rightDerived
  have union := deriveUnion calculus (hypothesisTrees left.sequent.hyp) (hypothesisTrees right.sequent.hyp)
  exact ⟨ofThm (by rw [sequentHypothesesP_of_hyp hypEq, treeUnion_hypothesisTrees])
    (by rw [sequentConclusionP_of_term conclusionTerm]; rfl)
    (deriveTransRule calculus (by simp) leftThm rightThm union)⟩

include calculus in
theorem mkComb_complete {functions arguments out : Theorem} (semantics : AppSemantics functions arguments out)
    (functionsDerived : Derivation definition (sequentJ functions.sequent))
    (argumentsDerived : Derivation definition (sequentJ arguments.sequent)) :
    Nonempty (Derivation definition (sequentJ out.sequent)) := by
  obtain ⟨leftFunction, rightFunction, leftArgument, rightArgument, leftApplication, rightApplication, equality,
    ⟨functionTypes, functionShape⟩, ⟨argumentTypes, argumentShape⟩, ⟨domain, codomain, recognized, domainEq,
      leftApplied⟩, ⟨domain', codomain', recognized', domainEq', rightApplied⟩, ⟨-, shape⟩, -, hypEq,
    conclEq⟩ := semantics
  have functionTyEq : leftFunction.ty = Ty.function domain codomain :=
    (Ty.destFunction?_eq_some_iff _ _ _).mp recognized
  have codomainEq : leftApplication.ty = codomain := by
    have typed := leftApplication.checked
    rw [leftApplied] at typed
    obtain ⟨domain'', functionTyped, argumentTyped⟩ := DBTerm.inferType_app_eq_some_iff.mp typed
    rw [leftFunction.checked, functionTyEq] at functionTyped
    exact ((Ty.function_inj (Option.some.inj functionTyped)).2).symm
  have conclusionTerm : out.sequent.concl.term = CanonicalTerm.equalityDB codomain
      (.app leftFunction.term leftArgument.term) (.app rightFunction.term rightArgument.term) := by
    rw [conclEq, shape, codomainEq, leftApplied, rightApplied]
  have functionThm := asThm (sequentHypothesesP_eq_treesP _)
    (by rw [sequentConclusionP_of_term functionShape, functionTyEq]) functionsDerived
  have argumentThm := asThm (sequentHypothesesP_eq_treesP _)
    (by rw [sequentConclusionP_of_term argumentShape, ← domainEq]) argumentsDerived
  have union := deriveUnion calculus (hypothesisTrees functions.sequent.hyp) (hypothesisTrees arguments.sequent.hyp)
  exact ⟨ofThm (by rw [sequentHypothesesP_of_hyp hypEq, treeUnion_hypothesisTrees])
    (by rw [sequentConclusionP_of_term conclusionTerm]; rfl)
    (deriveMkCombRule calculus (by simp) functionThm argumentThm union)⟩

include calculus in
theorem abs_complete {binder : SourceVar} {input out : Theorem} (semantics : AbsSemantics binder input out)
    (inputDerived : Derivation definition (sequentJ input.sequent)) :
    Nonempty (Derivation definition (sequentJ out.sequent)) := by
  obtain ⟨notFree, left, right, leftAbs, rightAbs, equality, ⟨types, inputShape⟩, leftAbstracted,
    rightAbstracted, ⟨-, shape⟩, -, hypEq, conclEq⟩ := semantics
  have leftAbsEq : leftAbs = left.abstractFree binder := CanonicalTerm.ext_term leftAbstracted
  have rightAbsEq : rightAbs = right.abstractFree binder := CanonicalTerm.ext_term rightAbstracted
  subst leftAbsEq rightAbsEq
  have conclusionTerm : out.sequent.concl.term = CanonicalTerm.equalityDB (Ty.function binder.ty left.ty)
      (.abs binder.ty (DBTerm.closeFreeAt binder 0 left.term))
      (.abs binder.ty (DBTerm.closeFreeAt binder 0 right.term)) := by
    rw [conclEq, shape]
    rfl
  have absent : ∀ term ∈ (sortedHypotheses input.sequent.hyp).map CanonicalTerm.term,
      DBTerm.hasFree binder term = false := by
    intro term member
    obtain ⟨hypothesis, hypothesisMember, rfl⟩ := List.mem_map.mp member
    cases occurs : DBTerm.hasFree binder hypothesis.term
    · rfl
    · exact absurd ⟨hypothesis, by simpa [sortedHypotheses] using hypothesisMember,
        (DBTerm.hasFree_eq_true_iff _ _).mp occurs⟩ notFree
  have inputThm := asThm rfl (sequentConclusionP_of_term inputShape) inputDerived
  have fresh : Derivation definition (notFreeAllJ (freeVarP binder) (sequentHypothesesP input.sequent)) :=
    recast (by rw [sequentHypothesesP_eq_termsP]) (deriveNotFreeAll calculus binder _ absent)
  exact ⟨ofThm (by unfold sequentHypothesesP; rw [hypEq]) (by rw [sequentConclusionP_of_term conclusionTerm]; rfl)
    (deriveAbsRule calculus (by simp) inputThm (deriveName calculus binder.name) (deriveTy calculus binder.ty)
      fresh (deriveClose calculus binder 0 left.term) (deriveClose calculus binder 0 right.term))⟩

theorem trivialBetaRedex_shape : ∀ {source : SourceTerm}, TrivialBetaRedex source →
    ∃ name type body, source = .app (.abs name type body) (.var name type)
  | .app (.abs name type body) (.var _ _), trivial => by
      obtain ⟨rfl, rfl⟩ := trivial
      exact ⟨name, type, body, rfl⟩
  | .const _ _, trivial => (trivial : False).elim
  | .var _ _, trivial => (trivial : False).elim
  | .abs _ _ _, trivial => (trivial : False).elim
  | .app (.const _ _) _, trivial => (trivial : False).elim
  | .app (.var _ _) _, trivial => (trivial : False).elim
  | .app (.app _ _) _, trivial => (trivial : False).elim
  | .app (.abs _ _ _) (.const _ _), trivial => (trivial : False).elim
  | .app (.abs _ _ _) (.app _ _), trivial => (trivial : False).elim
  | .app (.abs _ _ _) (.abs _ _ _), trivial => (trivial : False).elim

include calculus in
theorem beta_complete {source : CheckedSourceTerm} {out : Theorem} (semantics : SourceBetaSemantics source out) :
    Nonempty (Derivation definition (sequentJ out.sequent)) := by
  obtain ⟨trivial, reduced, equality, ⟨domain, body, argument, wholeShape, reducedShape⟩, ⟨-, shape⟩, -, hypEq,
    conclEq⟩ := semantics
  obtain ⟨name, type, bodySource, sourceShape⟩ := trivialBetaRedex_shape trivial
  have toDBEq : source.source.toDB [] =
      .app (.abs type (bodySource.toDB [⟨name, type⟩])) (.free ⟨name, type⟩) := by
    rw [sourceShape]
    simp [SourceTerm.toDB, boundIndex]
  have redexTerm : source.canonical.term = .app (.abs type (bodySource.toDB [⟨name, type⟩])) (.free ⟨name, type⟩) :=
    toDBEq
  rw [redexTerm] at wholeShape
  injection wholeShape with functionEq argumentEq
  injection functionEq with domainEq bodyEq
  have reducedTerm : reduced.term = DBTerm.instantiateAt (.free ⟨name, type⟩) 0 (bodySource.toDB [⟨name, type⟩]) := by
    rw [reducedShape, ← argumentEq, ← bodyEq]
  have conclusionTerm : out.sequent.concl.term = CanonicalTerm.equalityDB source.ty
      (.app (.abs type (bodySource.toDB [⟨name, type⟩])) (.free ⟨name, type⟩))
      (DBTerm.instantiateAt (.free ⟨name, type⟩) 0 (bodySource.toDB [⟨name, type⟩])) := by
    rw [conclEq, shape, ← redexTerm, ← reducedTerm]
    rfl
  have checked : (source.source.toDB []).inferType [] = some source.ty := by
    rw [← source.checked]
    exact DBTerm.inferType_toDB [] source.source
  have converted := recast (by rw [toDBEq, sourceShape]) (deriveToDB calculus [] source.source)
  have typed := recast (by rw [toDBEq]) (deriveTypeOf calculus [] _ source.ty checked)
  have instantiated := deriveInstantiate calculus (.free ⟨name, type⟩) 0 (bodySource.toDB [⟨name, type⟩])
  exact ⟨ofThm (by rw [sequentHypothesesP_of_hyp hypEq, hypothesisTrees_empty]; rfl)
    (by rw [sequentConclusionP_of_term conclusionTerm]; rfl)
    (deriveBetaRule calculus (x := groundP (encodeName name)) (a := groundP (encodeTy type))
      (t := groundP (encodeSourceTerm bodySource)) (by simp) converted typed instantiated)⟩

include calculus in
theorem eqMp_complete {equality premise out : Theorem} (semantics : EqMpSemantics equality premise out)
    (equalityDerived : Derivation definition (sequentJ equality.sequent))
    (premiseDerived : Derivation definition (sequentJ premise.sequent)) :
    Nonempty (Derivation definition (sequentJ out.sequent)) := by
  obtain ⟨left, right, ⟨-, shape⟩, same, -, hypEq, conclEq⟩ := semantics
  have equalityThm := asThm (sequentHypothesesP_eq_treesP _) (sequentConclusionP_of_term shape) equalityDerived
  have premiseThm := asThm (sequentHypothesesP_eq_treesP _)
    (sequentConclusionP_of_term (congrArg CanonicalTerm.term same.symm)) premiseDerived
  have union := deriveUnion calculus (hypothesisTrees equality.sequent.hyp) (hypothesisTrees premise.sequent.hyp)
  exact ⟨ofThm (by rw [sequentHypothesesP_of_hyp hypEq, treeUnion_hypothesisTrees])
    (by rw [sequentConclusionP_of_term (congrArg CanonicalTerm.term conclEq)]; rfl)
    (deriveEqMpRule calculus (by simp) equalityThm premiseThm union)⟩

include calculus in
theorem deductAntisym_complete {left right out : Theorem} (semantics : DeductAntisymSemantics left right out)
    (leftDerived : Derivation definition (sequentJ left.sequent))
    (rightDerived : Derivation definition (sequentJ right.sequent)) :
    Nonempty (Derivation definition (sequentJ out.sequent)) := by
  obtain ⟨equality, ⟨types, shape⟩, -, hypEq, conclEq⟩ := semantics
  have leftThm := asThm (sequentHypothesesP_eq_treesP _) rfl leftDerived
  have rightThm := asThm (sequentHypothesesP_eq_treesP _) rfl rightDerived
  have leftTyped := deriveTypeOf calculus [] left.sequent.concl.term left.sequent.concl.ty left.sequent.concl.checked
  have rightTyped := recast (by rw [← types])
    (deriveTypeOf calculus [] right.sequent.concl.term right.sequent.concl.ty right.sequent.concl.checked)
  have leftErase := recast (by rw [treeErase_hypothesisTrees])
    (deriveErase calculus (encodeCanonical right.sequent.concl) (hypothesisTrees left.sequent.hyp))
  have rightErase := recast (by rw [treeErase_hypothesisTrees])
    (deriveErase calculus (encodeCanonical left.sequent.concl) (hypothesisTrees right.sequent.hyp))
  have union := deriveUnion calculus (hypothesisTrees (left.sequent.hyp.erase right.sequent.concl))
    (hypothesisTrees (right.sequent.hyp.erase left.sequent.concl))
  have conclusionTerm : out.sequent.concl.term = CanonicalTerm.equalityDB left.sequent.concl.ty
      left.sequent.concl.term right.sequent.concl.term := by
    rw [conclEq, shape]
  exact ⟨ofThm (by rw [sequentHypothesesP_of_hyp hypEq, treeUnion_hypothesisTrees])
    (by rw [sequentConclusionP_of_term conclusionTerm]; rfl)
    (deriveDeductAntisymRule calculus (by simp) leftThm rightThm leftTyped rightTyped leftErase rightErase union)⟩

include calculus in
theorem inst_complete {maplets : List SourceSubstitution.TermMaplet} {input out : Theorem}
    (semantics : ∃ substitution, SourceSubstitution.admitTermSubstitution maplets = some substitution ∧
      TheoremSubstitutionSemantics substitution input out)
    (inputDerived : Derivation definition (sequentJ input.sequent)) :
    Nonempty (Derivation definition (sequentJ out.sequent)) := by
  obtain ⟨substitution, admitted, -, hypothesesImage, conclusionImage⟩ := semantics
  have admissible := (SourceSubstitution.admitTermSubstitution_isSome_iff maplets).mp (by rw [admitted]; rfl)
  have action : ∀ term : DBTerm,
      substitution.raw.applyDB term = tableAction (SourceSubstitution.termEntries maplets) term := by
    intro term
    rw [SourceSubstitution.admittedTermSubstitution_raw admitted]
    rfl
  have hypEq : out.sequent.hyp = input.sequent.hyp.image substitution.apply := by
    ext term
    rw [hypothesesImage term, Finset.mem_image]
    constructor
    · rintro ⟨source, member, termEq⟩
      exact ⟨source, member, CanonicalTerm.ext_term termEq.symm⟩
    · rintro ⟨source, member, rfl⟩
      exact ⟨source, member, rfl⟩
  have inputThm := asThm (sequentHypothesesP_eq_termsP _) rfl inputDerived
  have hypotheses := deriveTmApplyList calculus (SourceSubstitution.termEntries maplets)
    ((sortedHypotheses input.sequent.hyp).map CanonicalTerm.term)
  have sorted := recast (by rw [← termsP_eq_treesP])
    (deriveSort calculus ((((sortedHypotheses input.sequent.hyp).map CanonicalTerm.term).map
      (tableAction (SourceSubstitution.termEntries maplets))).map encodeTerm))
  have concluded := deriveTmApply calculus (SourceSubstitution.termEntries maplets) input.sequent.concl.term
  exact ⟨ofThm
    (by
      rw [treeSort_image_hypothesisTrees _ (apply := substitution.apply) (fun term => action term.term), ← hypEq,
        sequentHypothesesP_eq_treesP])
    (by rw [sequentConclusionP_of_term conclusionImage, action])
    (deriveInstRule calculus (by simp) inputThm (deriveAdmit calculus maplets admissible) hypotheses sorted
      concluded)⟩

include calculus in
theorem instType_complete {entries : List (Ty × Ty)} {input out : Theorem}
    (semantics : TheoremSubstitutionSemantics (SourceSubstitution.typeOnlySubstitution entries) input out)
    (inputDerived : Derivation definition (sequentJ input.sequent)) :
    Nonempty (Derivation definition (sequentJ out.sequent)) := by
  obtain ⟨-, hypothesesImage, conclusionImage⟩ := semantics
  have hypEq : out.sequent.hyp = input.sequent.hyp.image (SourceSubstitution.typeOnlySubstitution entries).apply := by
    ext term
    rw [hypothesesImage term, Finset.mem_image]
    constructor
    · rintro ⟨source, member, termEq⟩
      exact ⟨source, member, CanonicalTerm.ext_term termEq.symm⟩
    · rintro ⟨source, member, rfl⟩
      exact ⟨source, member, rfl⟩
  have inputThm := asThm (sequentHypothesesP_eq_termsP _) rfl inputDerived
  have hypotheses := deriveTermTyActList calculus entries ((sortedHypotheses input.sequent.hyp).map CanonicalTerm.term)
  have sorted := recast (by rw [← termsP_eq_treesP])
    (deriveSort calculus ((((sortedHypotheses input.sequent.hyp).map CanonicalTerm.term).map
      (termTypeAction entries)).map encodeTerm))
  have concluded := deriveTermTyAct calculus entries input.sequent.concl.term
  exact ⟨ofThm
    (by
      rw [treeSort_image_hypothesisTrees _ (apply := (SourceSubstitution.typeOnlySubstitution entries).apply)
        (fun term => applyDB_typeOnly entries term.term), ← hypEq, sequentHypothesesP_eq_treesP])
    (by
      rw [sequentConclusionP_of_term conclusionImage]
      exact congrArg (fun term => groundP (encodeTerm term)) (applyDB_typeOnly entries _).symm)
    (deriveInstTypeRule calculus (by simp) inputThm (deriveTypeMaplets calculus entries) hypotheses sorted
      concluded)⟩

include calculus in
theorem axiom_complete {sequent : Sequent} (member : sequent ∈ axioms) {out : Theorem}
    (semantics : AxiomSemantics sequent out) : Nonempty (Derivation definition (sequentJ out.sequent)) := by
  obtain ⟨-, -, hypEq, conclEq⟩ := semantics
  rw [show out.sequent = sequent from Sequent.ext hypEq conclEq]
  have indexed : (sequent, axioms.idxOf sequent) ∈ axioms.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]
    rw [List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem member), List.getElem_idxOf]
  have ruleMember : rule ("hol.axiom-" ++ toString (axioms.idxOf sequent)) [] [] (sequentJ sequent) ∈
      definition.1.rules :=
    member_of_holRules calculus (by
      simp only [holRules, List.mem_append]
      exact Or.inr (List.mem_map.mpr ⟨_, indexed, rfl⟩))
  exact ⟨fireAt ruleMember (rule_shape ⟨by simp [checkSchemas], checkSchema_sequentJ [] sequent⟩) [] rfl (by simp)
    (by simp [rule, substSchemas]) (by simp only [rule]; exact substSchema_sequentJ _ _) .nil⟩

include calculus in
/-- **Completeness.** Every theorem that HOL Light's rules derive from axioms of the calculus has a
derivation of its rendered sequent. -/
theorem holCalculus_complete (policy : AxiomPolicy) (inList : ∀ sequent, policy sequent → sequent ∈ axioms)
    {out : Theorem} (derived : Derives (Rule policy) out) :
    Nonempty (Derivation definition (sequentJ out.sequent)) := by
  induction derived with
  | node premises out rule children ih =>
      rcases rule with ⟨request, rfl, semantics⟩ | ⟨sequent, rfl, -, allowed, semantics⟩
      · cases request with
        | refl term => exact refl_complete calculus semantics
        | assume term => exact assume_complete calculus semantics
        | trans left right =>
            obtain ⟨leftDerived⟩ := ih left (by simp [InferenceRequest.premises])
            obtain ⟨rightDerived⟩ := ih right (by simp [InferenceRequest.premises])
            exact trans_complete calculus semantics leftDerived rightDerived
        | mkComb functions arguments =>
            obtain ⟨functionsDerived⟩ := ih functions (by simp [InferenceRequest.premises])
            obtain ⟨argumentsDerived⟩ := ih arguments (by simp [InferenceRequest.premises])
            exact mkComb_complete calculus semantics functionsDerived argumentsDerived
        | abs binder input =>
            obtain ⟨inputDerived⟩ := ih input (by simp [InferenceRequest.premises])
            exact abs_complete calculus semantics inputDerived
        | beta source => exact beta_complete calculus semantics
        | eqMp equality premise =>
            obtain ⟨equalityDerived⟩ := ih equality (by simp [InferenceRequest.premises])
            obtain ⟨premiseDerived⟩ := ih premise (by simp [InferenceRequest.premises])
            exact eqMp_complete calculus semantics equalityDerived premiseDerived
        | deductAntisym left right =>
            obtain ⟨leftDerived⟩ := ih left (by simp [InferenceRequest.premises])
            obtain ⟨rightDerived⟩ := ih right (by simp [InferenceRequest.premises])
            exact deductAntisym_complete calculus semantics leftDerived rightDerived
        | instType entries input =>
            obtain ⟨inputDerived⟩ := ih input (by simp [InferenceRequest.premises])
            exact instType_complete calculus semantics inputDerived
        | inst maplets input =>
            obtain ⟨inputDerived⟩ := ih input (by simp [InferenceRequest.premises])
            exact inst_complete calculus semantics inputDerived
      · exact axiom_complete calculus (inList sequent allowed) semantics

include calculus in
/-- **Exactness.** For axioms admitted by a policy that admits nothing else, the rendering of a
sequent is derivable in the calculus exactly when HOL Light's rules derive a theorem with that
sequent. -/
theorem holCalculus_exact (policy : AxiomPolicy)
    (admitted : ∀ sequent ∈ axioms, sequent.hyp = ∅ ∧ policy sequent ∧ sequent.IsBool)
    (inList : ∀ sequent, policy sequent → sequent ∈ axioms) (sequent : Sequent) :
    Nonempty (Derivation definition (sequentJ sequent)) ↔
      ∃ out : Theorem, Derives (Rule policy) out ∧ out.sequent = sequent := by
  constructor
  · rintro ⟨derivation⟩
    exact holCalculus_sound_sequent policy admitted calculus derivation
  · rintro ⟨out, derived, rfl⟩
    exact holCalculus_complete calculus policy inList derived

include calculus in
/-- **The checker accepts exactly HOL Light's theorems**: some certificate checks the rendering
of a sequent exactly when HOL Light derives it. -/
theorem holCalculus_accepts_iff (policy : AxiomPolicy)
    (admitted : ∀ sequent ∈ axioms, sequent.hyp = ∅ ∧ policy sequent ∧ sequent.IsBool)
    (inList : ∀ sequent, policy sequent → sequent ∈ axioms) (sequent : Sequent) :
    (∃ proof, checkRaw definition (sequentJ sequent) proof = true) ↔
      ∃ out : Theorem, Derives (Rule policy) out ∧ out.sequent = sequent := by
  rw [← holCalculus_exact calculus policy admitted inList]
  constructor
  · rintro ⟨proof, accepted⟩
    obtain ⟨derivation, -⟩ := G2_checkRaw_iff_exists_derivation_erases_to.mp accepted
    exact ⟨derivation⟩
  · rintro ⟨derivation⟩
    exact ⟨derivation.erase, G2_checkRaw_iff_exists_derivation_erases_to.mpr ⟨derivation, rfl⟩⟩

end Calculus

end Mettapedia.Languages.HOLLight.FirstOrder

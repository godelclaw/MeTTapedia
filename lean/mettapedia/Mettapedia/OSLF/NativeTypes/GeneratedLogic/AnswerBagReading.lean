import Mettapedia.OSLF.NativeTypes.GeneratedLogic.DriverBridge
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.BagCanonicalParts
import Mettapedia.OSLF.NativeTypes.Instances.SpatialBag

/-!
# The answer-bag driver, read at the front door

The answer-bag driver (`Instances.SpatialBag`) observes a completed collection of answers: a bag of payloads of an
abstract sort `Atom`, identified up to the order of its elements, split into sub-bags, with an empty test and a
singleton test for each payload. Its payloads are patterns of some object language that the driver does not
interpret. The reference structure identifies two bags up to order only when they are bags of a sort, so the reading
takes the consumer's payload language:

- **The answer language** (`answers`): a payload language (`Payload`: no equations, rules or collection algebra) with
  the answer-bag former.
- **The region** (`Payloads`): bags of closed payloads of sort `Atom` with no bag or set inside them. There the
  reference equivalence of two answer bags is a permutation of their elements (`objectEquivalent_iff`), so their
  splits are the driver's partitions (`split_iff`), and the empty and singleton tests are the empty former and the
  named bag of one payload (`test_iff`).
- **The rendering is a split morphism** along the encoding (`rendering`): no rule fires, and a split of an encoded bag
  has encoded parts. A singleton's member is a payload, not a bag, so there is no bounded morphism.
- **The reading** (`faithful`, `reading`): the driver's tests are infinitely many; a formula's tests are listed in a
  table, and the meaning of every driver formula at a bag of payloads is the truth of its closed formula
  (`meaning_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.AnswerBag

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (canon canon_collection canon_apply arrange arrange_bag arrange_vec
  perm_of_sortLex_eq)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics (DerivedInstance)
open Mettapedia.OSLF.NativeTypes.Decision.Spatial
open Mettapedia.GSLT.LanguageDef.BagNormalForm (elementsHaveType_iff isObjectPatternList_iff)
open Mettapedia.OSLF.NativeTypes.Instances.SpatialBag (bagFormer driver)
open Mettapedia.OSLF.NativeTypes.Runtime.Description (Meaning)
open Embeddings

/-! ## The answer language -/

/-- **The answer language of a payload language**: the payload language with the answer-bag former, which collects
payloads of sort `Atom` into answers. -/
def answers (payload : LanguageDef) : LanguageDef :=
  { payload with types := payload.types ++ [("Answers" : TypeDecl)], terms := payload.terms ++ [bagFormer] }

/-- **A payload language**: no equations, no rules and no collection algebra; its terms are completed answers. -/
structure Payload (payload : LanguageDef) : Prop where
  equations : payload.equations = []
  rewrites : payload.rewrites = []
  algebra : payload.hasAlgebraDeclarations = false

variable {payload : LanguageDef}

theorem answers_equations (pay : Payload payload) : (answers payload).equations = [] := pay.equations

theorem answers_algebra (pay : Payload payload) : (answers payload).hasAlgebraDeclarations = false := by
  have none := pay.algebra
  unfold LanguageDef.hasAlgebraDeclarations at none ⊢
  simp only [answers, List.any_append, none, Bool.false_or]
  rfl

/-! ## Payloads with no bag inside -/

mutual
/-- **No bag or set** occurs in a pattern. -/
def bagFree : Pattern → Bool
  | .bvar _ => true
  | .fvar _ => true
  | .apply _ arguments => bagFreeList arguments
  | .lambda _ body => bagFree body
  | .multiLambda _ _ body => bagFree body
  | .subst body replacement => bagFree body && bagFree replacement
  | .collection .vec elements _ => bagFreeList elements
  | .collection .hashBag _ _ => false
  | .collection .hashSet _ _ => false

/-- No bag or set occurs in any pattern of a list. -/
def bagFreeList : List Pattern → Bool
  | [] => true
  | pattern :: patterns => bagFree pattern && bagFreeList patterns
end

theorem bagFreeList_iff : ∀ patterns : List Pattern, bagFreeList patterns = true ↔ ∀ pattern ∈ patterns, bagFree pattern = true
  | [] => by simp [bagFreeList]
  | pattern :: patterns => by simp [bagFreeList, bagFreeList_iff patterns]

theorem bagFreeList_map {patterns : List Pattern} (same : ∀ pattern ∈ patterns, bagFree (canon pattern) = bagFree pattern) :
    bagFreeList (patterns.map canon) = bagFreeList patterns := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns recurse =>
    simp only [List.map_cons, bagFreeList, same pattern List.mem_cons_self,
      recurse fun other member => same other (List.mem_cons_of_mem _ member)]

/-- **Sorting keeps a pattern free of bags or not.** -/
theorem bagFree_canon (pattern : Pattern) : bagFree (canon pattern) = bagFree pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar => rw [canon]
  | hfvar => rw [canon]
  | happly label arguments recurse =>
    rw [canon_apply]
    simp only [bagFree]
    exact bagFreeList_map recurse
  | hlambda binder body recurse => rw [canon]; simp only [bagFree, recurse]
  | hmultiLambda arity binders body recurse => rw [canon]; simp only [bagFree, recurse]
  | hsubst body replacement bodyRecurse replacementRecurse =>
    rw [canon]; simp only [bagFree, bodyRecurse, replacementRecurse]
  | hcollection kind elements rest recurse =>
    rw [canon_collection]
    cases kind with
    | vec => simp only [arrange_vec, bagFree]; exact bagFreeList_map recurse
    | hashBag => rfl
    | hashSet => rfl

/-- **Sorting leaves a pattern with no bag or set unchanged.** -/
theorem canon_eq_of_bagFree (pattern : Pattern) : bagFree pattern = true → canon pattern = pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar => intro; rw [canon]
  | hfvar => intro; rw [canon]
  | happly label arguments recurse =>
    intro free
    rw [canon_apply]
    simp only [bagFree, bagFreeList_iff] at free
    congr 1
    conv => rhs; rw [← List.map_id arguments]
    exact List.map_congr_left fun argument member => recurse argument member (free argument member)
  | hlambda binder body recurse =>
    intro free; rw [canon]; simp only [bagFree] at free; rw [recurse free]
  | hmultiLambda arity binders body recurse =>
    intro free; rw [canon]; simp only [bagFree] at free; rw [recurse free]
  | hsubst body replacement bodyRecurse replacementRecurse =>
    intro free; rw [canon]; simp only [bagFree, Bool.and_eq_true] at free
    rw [bodyRecurse free.1, replacementRecurse free.2]
  | hcollection kind elements rest recurse =>
    intro free
    rw [canon_collection]
    cases kind with
    | vec =>
      simp only [bagFree, bagFreeList_iff] at free
      rw [arrange_vec]
      congr 1
      conv => rhs; rw [← List.map_id elements]
      exact List.map_congr_left fun element member => recurse element member (free element member)
    | hashBag => simp [bagFree] at free
    | hashSet => simp [bagFree] at free

/-- A pattern whose sorted form has no bag or set is its sorted form. -/
theorem canon_eq_of_bagFree_canon {pattern : Pattern} (free : bagFree (canon pattern) = true) : canon pattern = pattern :=
  canon_eq_of_bagFree pattern ((bagFree_canon pattern).symm.trans free)

/-! ## The region -/

variable (payload) in
/-- **A payload**: a closed object of sort `Atom` with no bag or set in it. -/
def IsPayload (item : Pattern) : Prop :=
  isObjectPattern item = true ∧ bagFree item = true ∧
    HasType (answers payload) FreeTypeContext.empty [] item (.base "Atom")

variable (payload) in
/-- **Bags of payloads.** -/
def Payloads (items : List Pattern) : Prop := ∀ item ∈ items, IsPayload payload item

theorem payloads_perm {items others : List Pattern} (region : Payloads payload items) (perm : items.Perm others) :
    Payloads payload others :=
  fun item member => region item (perm.symm.subset member)

theorem object_encode {items : List Pattern} (region : Payloads payload items) :
    isObjectPattern (BagModel.encode items) = true := by
  simp only [BagModel.encode, isObjectPattern, Option.isNone_none, Bool.true_and, isObjectPatternList_iff]
  exact fun item member => (region item member).1

variable {relEnv : RelationEnv}

/-- **A permutation of a bag of payloads is an equation** of the answer language. -/
theorem objectEquivalent_of_perm {items others : List Pattern} (region : Payloads payload items)
    (perm : items.Perm others) :
    ObjectEquivalent relEnv (answers payload) .syntax (BagModel.encode items) (BagModel.encode others) := by
  have typed : CollectionTypedAt (answers payload) bagFormer .hashBag items :=
    ⟨.simple "items" (.collection .hashBag (.base "Atom")), List.mem_singleton_self _, .base "Atom", .here,
      FreeTypeContext.empty, [], HasType.collection (elementsHaveType_iff.mpr fun item member => (region item member).2.2)⟩
  have generator : Generator relEnv (answers payload) (BagModel.encode items) (BagModel.encode others) :=
    Or.inr (DerivedInstance.bagPerm (List.mem_append_right _ (List.mem_singleton_self _)) typed perm)
  exact Relation.EqvGen.rel _ _ ⟨object_encode region, object_encode (payloads_perm region perm),
    EquationStep.inContext .hole generator⟩

/-- **Two answer bags equivalent in the answer language are a permutation of each other**, the first a bag of
payloads. -/
theorem perm_of_objectEquivalent (pay : Payload payload) {items others : List Pattern} (region : Payloads payload items)
    (equivalent : ObjectEquivalent relEnv (answers payload) .syntax (BagModel.encode items) (BagModel.encode others)) :
    items.Perm others := by
  have same := BagForms.canon_eq_of_equivalent (answers_equations pay) (answers_algebra pay) equivalent
  simp only [BagModel.encode, canon_collection, arrange_bag, Pattern.collection.injEq, true_and, and_true] at same
  have itemsCanon : items.map canon = items := by
    conv => rhs; rw [← List.map_id items]
    exact List.map_congr_left fun item member => canon_eq_of_bagFree item (region item member).2.1
  have perm := perm_of_sortLex_eq same
  rw [itemsCanon] at perm
  have othersCanon : others.map canon = others := by
    conv => rhs; rw [← List.map_id others]
    refine List.map_congr_left fun other member => canon_eq_of_bagFree_canon ?_
    exact (region _ (perm.symm.subset (List.mem_map_of_mem member))).2.1
  rwa [othersCanon] at perm

/-- **On bags of payloads, the reference equivalence is permutation.** -/
theorem objectEquivalent_iff (pay : Payload payload) {items : List Pattern} (region : Payloads payload items)
    (others : List Pattern) :
    ObjectEquivalent relEnv (answers payload) .syntax (BagModel.encode items) (BagModel.encode others) ↔
      items.Perm others :=
  ⟨perm_of_objectEquivalent pay region, objectEquivalent_of_perm region⟩

/-- An answer bag is equivalent to no collection of another kind. -/
theorem not_objectEquivalent_kind (pay : Payload payload) {items : List Pattern} {kind : CollType}
    (differs : kind ≠ .hashBag) {elements : List Pattern} {rest : Option String} :
    ¬ ObjectEquivalent relEnv (answers payload) .syntax (BagModel.encode items) (.collection kind elements rest) := by
  intro equivalent
  have same := BagForms.canon_eq_of_equivalent (answers_equations pay) (answers_algebra pay) equivalent
  simp only [BagModel.encode, canon_collection, Pattern.collection.injEq] at same
  exact differs same.1.symm

/-! ## The rendering -/

/-- The reference structure of the answer language. -/
abbrev Reference (relEnv : RelationEnv) (payload : LanguageDef) : NativeStructure Pattern :=
  referenceStructure relEnv (answers payload)

/-- **No rule of the answer language fires.** -/
theorem no_step (pay : Payload payload) {source target : Pattern} {label : StepLabel} :
    ¬ (Reference relEnv payload).step source label target := by
  rintro ⟨-, -, redex, contractum, witness, -, -, valid, -⟩
  cases valid with
  | rule found _ _ =>
    have none : (answers payload).rewrites = [] := pay.rewrites
    rw [none] at found
    cases found

/-- **A split of an answer bag has answer bags as parts.** -/
theorem split_image (pay : Payload payload) (items : List Pattern) (kind : CollType) (first second : Pattern)
    (split : (Reference relEnv payload).split (BagModel.encode items) kind first second) :
    (∃ left, BagModel.encode left = first) ∧ ∃ right, BagModel.encode right = second := by
  obtain ⟨-, left, right, equivalent, rfl, rfl⟩ := split
  by_cases bag : kind = .hashBag
  · subst bag
    exact ⟨⟨left, rfl⟩, ⟨right, rfl⟩⟩
  · exact absurd equivalent (not_objectEquivalent_kind pay bag)

/-- The structure on bags pulled back along the encoding. -/
abbrev bags (relEnv : RelationEnv) (payload : LanguageDef) : NativeStructure (List Pattern) :=
  pullback (Reference relEnv payload) BagModel.encode

/-- **The encoding is a split morphism.** -/
def rendering (pay : Payload payload) : SplitMorphism (bags relEnv payload) (Reference relEnv payload) :=
  pullbackSplit _ _ (fun _ _ _ _ step => (no_step pay step).elim) (split_image pay)

/-- **The splits of a bag of payloads are its partitions.** -/
theorem split_iff (pay : Payload payload) {items : List Pattern} (region : Payloads payload items)
    (first second : List Pattern) :
    (bags relEnv payload).split items .hashBag first second ↔ (first ++ second).Perm items := by
  constructor
  · rintro ⟨-, left, right, equivalent, sameFirst, sameSecond⟩
    simp only [BagModel.encode, Pattern.collection.injEq, true_and, and_true] at sameFirst sameSecond
    subst sameFirst sameSecond
    exact ((objectEquivalent_iff pay region _).mp equivalent).symm
  · intro perm
    exact ⟨object_encode region, first, second, objectEquivalent_of_perm region perm.symm, rfl, rfl⟩

instance : DecidableEq driver.Leaf := inferInstanceAs (DecidableEq BagModel.Leaf)

/-- The collection kind of a spatial index: the bag at the driver's one index, and a kind no bag splits into at the
others. -/
def kindOf (index : ℕ) : CollType := if index = 0 then .hashBag else .vec

/-- **The structure realizes the driver's splits** for every formula. -/
theorem realized (pay : Payload payload) :
    ∀ formula : driver.Formula,
      SplitsRealizedOn (system := BagModel.system) kindOf (Payloads payload) (bags relEnv payload) BagModel.spatial formula
  | .atom _ | .top | .bottom => trivial
  | .conj left right | .disj left right | .imp left right => ⟨realized pay left, realized pay right⟩
  | .neg inner | .possibility inner | .outgoingUniversal inner => realized pay inner
  | .separating index left right => by
    refine ⟨fun whole region first second => ?_, fun whole first second region split => ?_, realized pay left,
      realized pay right⟩
    · by_cases zero : index = 0
      · subst zero
        rw [show kindOf 0 = .hashBag from rfl, split_iff pay region]
        exact ⟨fun perm => ⟨rfl, perm⟩, fun split => split.2⟩
      · rw [show kindOf index = .vec from if_neg zero]
        refine iff_of_false ?_ fun split => zero split.1
        rintro ⟨-, left, right, equivalent, -, -⟩
        exact not_objectEquivalent_kind pay (by decide) equivalent
    · obtain ⟨-, perm⟩ := split
      exact ⟨fun item member => region item (perm.subset (List.mem_append_left _ member)),
        fun item member => region item (perm.subset (List.mem_append_right _ member))⟩

/-! ## The tests -/

/-- **The tests as formulas**: the empty former, and the named bag of one payload. -/
def testFormula : BagModel.Leaf → Formula 0
  | .emp => .empty .hashBag
  | .singleton value => .is (BagModel.encode [value])

theorem testFormula_forward (leaf : BagModel.Leaf) : (testFormula leaf).forward = true := by
  cases leaf <;> rfl

/-- **Each test is its formula** on bags of payloads. -/
theorem test_iff (pay : Payload payload) {items : List Pattern} (region : Payloads payload items)
    (leaf : BagModel.Leaf) :
    (driver.tests leaf).predicate.1 items ↔
      (Reference relEnv payload).sat Env.closed (testFormula leaf) (BagModel.encode items) := by
  cases leaf with
  | emp =>
    show (items : Multiset Pattern) = 0 ↔
      isObjectPattern (BagModel.encode items) = true ∧
        ObjectEquivalent relEnv (answers payload) .syntax (BagModel.encode items) (BagModel.encode [])
    rw [objectEquivalent_iff pay region, Multiset.coe_eq_zero, List.perm_nil]
    exact ⟨fun empty => ⟨object_encode region, empty⟩, fun both => both.2⟩
  | singleton value =>
    show (items : Multiset Pattern) = {value} ↔
      isObjectPattern (BagModel.encode items) = true ∧
        ObjectEquivalent relEnv (answers payload) .syntax (BagModel.encode items) (BagModel.encode [value])
    rw [objectEquivalent_iff pay region, ← Multiset.coe_singleton, Multiset.coe_eq_coe]
    exact ⟨fun perm => ⟨object_encode region, perm⟩, fun both => both.2⟩

/-! ## The reading -/

variable (relEnv) in
/-- **The faithful reading of the answer-bag driver**, for the tests a table lists. -/
def faithful (pay : Payload payload) (used : List driver.Leaf) :
    Faithful driver relEnv (answers payload) (LeafTable.positiveIndex used) (LeafTable.negativeIndex used) where
  structure_ := bags relEnv payload
  region := Payloads payload
  steps source _ target := iff_of_false (fun step => no_step pay step) (BagModel.no_step source target)
  closed _ _ _ step := (BagModel.no_step _ _ step).elim
  rendering := rendering pay
  renders := rfl
  covers leaf := leaf ∈ used
  test := LeafTable.test used testFormula
  testAgrees leaf covered source region := by
    rw [LeafTable.test_of_mem (Leaf := driver.Leaf) used testFormula covered]
    exact test_iff pay region leaf
  closing := LeafTable.closing used testFormula
  closesPositive := LeafTable.closesPositive used testFormula
  closesNegative := LeafTable.closesNegative used testFormula
  closingForward := LeafTable.closingForward used testFormula fun leaf _ => testFormula_forward leaf

variable (relEnv) in
/-- **The reading of every driver formula** whose tests the table lists. -/
def reading (pay : Payload payload) (used : List driver.Leaf) :
    Reading driver relEnv (answers payload) (LeafTable.positiveIndex used) (LeafTable.negativeIndex used) kindOf :=
  (faithful relEnv pay used).readingAll (realized pay)

/-- **The meaning of a driver formula at a bag of payloads is the truth of its closed formula.** -/
theorem meaning_iff (pay : Payload payload) (formula : driver.Formula) {items : List Pattern}
    (region : Payloads payload items) :
    Meaning driver formula (BagModel.encode items) ↔
      (Reference relEnv payload).sat Env.closed
        ((ofCore (LeafTable.positiveIndex (leaves formula)) (LeafTable.negativeIndex (leaves formula)) kindOf true
          formula).subst (LeafTable.closing (leaves formula) testFormula)) (BagModel.encode items) :=
  meaning_iff_sat (faithful relEnv pay (leaves formula)) formula (atomsCovered_of_leaves formula fun _ member => member)
    (realized pay formula) ⟨items, trivial, rfl⟩ region

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.AnswerBag

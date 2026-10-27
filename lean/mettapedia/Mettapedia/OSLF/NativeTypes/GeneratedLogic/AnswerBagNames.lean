import Mettapedia.OSLF.NativeTypes.GeneratedLogic.AnswerBagReading
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.FrontDoorAgreement
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.FrontDoorParts

/-!
# Every completed answer bag at the front door, by naming its answers

The answer-bag reading (`AnswerBagReading`) reads bags of payloads of a payload language. A consumer's answers are
arbitrary patterns, possibly with bags inside or out of any declared sort, and the bag observations look at an answer
only through equality with the values a formula names. So the answers can be named:

- **Renaming payloads keeps the observations** (`holds_rename`): renaming the answers and the values a formula names by
  a map that is injective on all of them keeps the truth of every bag formula. Splits of the renamed bag are renamings
  of splits of the bag, and the bag has no steps.
- **Names are numerals** (`numerals`, `numeral`): the payload language of `zero` and `succ`, whose closed terms are
  payloads.
- **Each answer is named by its position** among the answers and the formula's values (`nameIn`), which is injective
  on them.
- **Every bag formula at every bag of answers is the front door's native type** at the bag of names
  (`holds_iff_frontDoor`), and the generated front door's decided answers about it are sound (`answer_sound`), with the
  bag parts decider over the canonical forms of the bags of numerals.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.AnswerBag.Names

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Decision.Reference
open Mettapedia.OSLF.NativeTypes.Decision.Spatial
open Mettapedia.OSLF.NativeTypes.Instances.SpatialBag (driver)
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (gsltDiamond_spec)
open FrontDoorAgreement Embeddings

/-! ## Renaming payloads -/

/-- A test with its payload renamed. -/
def renameLeaf (name : Pattern → Pattern) : BagModel.Leaf → BagModel.Leaf
  | .emp => .emp
  | .singleton value => .singleton (name value)

/-- **A bag formula with the values it names renamed.** -/
def rename (name : Pattern → Pattern) : Core.Formula BagModel.Leaf → Core.Formula BagModel.Leaf
  | .atom leaf => .atom (renameLeaf name leaf)
  | .top => .top
  | .bottom => .bottom
  | .conj first second => .conj (rename name first) (rename name second)
  | .disj first second => .disj (rename name first) (rename name second)
  | .neg inner => .neg (rename name inner)
  | .imp first second => .imp (rename name first) (rename name second)
  | .possibility inner => .possibility (rename name inner)
  | .outgoingUniversal inner => .outgoingUniversal (rename name inner)
  | .separating index first second => .separating index (rename name first) (rename name second)

/-- The values a bag formula names. -/
def values : Core.Formula BagModel.Leaf → List Pattern
  | .atom .emp => []
  | .atom (.singleton value) => [value]
  | .top | .bottom => []
  | .conj first second | .disj first second | .imp first second | .separating _ first second =>
    values first ++ values second
  | .neg inner | .possibility inner | .outgoingUniversal inner => values inner

/-- A split of a renamed bag is a renaming of a split of the bag. -/
theorem split_of_map (name : Pattern → Pattern) {items first second : List Pattern}
    (split : (first ++ second).Perm (items.map name)) :
    ∃ first' second' : List Pattern, (first' ++ second').Perm items ∧ first'.map name = first ∧
      second'.map name = second := by
  have related : List.Forall₂ (fun named item => named = name item) (items.map name) items := by
    rw [List.forall₂_map_left_iff]
    exact List.forall₂_same.mpr fun _ _ => rfl
  obtain ⟨renamed, forall₂, perm⟩ := List.perm_comp_forall₂ split related
  have mapped : first ++ second = renamed.map name := by
    have equal := (List.forall₂_map_right_iff (R := Eq) (f := name)).mpr forall₂
    rwa [List.forall₂_eq_eq_eq] at equal
  obtain ⟨first', second', rfl, firstMapped, secondMapped⟩ := List.map_eq_append_iff.mp mapped.symm
  exact ⟨first', second', perm, firstMapped, secondMapped⟩

/-- **Renaming payloads keeps the observations**: renaming the answers and the values a formula names by a map
injective on all of them keeps the truth of the formula. -/
theorem holds_rename (name : Pattern → Pattern) {domain : List Pattern}
    (injective : ∀ x ∈ domain, ∀ y ∈ domain, name x = name y → x = y) :
    ∀ (formula : Core.Formula BagModel.Leaf) (items : List Pattern), (∀ value ∈ values formula, value ∈ domain) →
      (∀ item ∈ items, item ∈ domain) →
        (BagModel.holds (rename name formula) (items.map name) ↔ BagModel.holds formula items)
  | .atom .emp, items, _, _ => by
    change ((items.map name : List Pattern) : Multiset Pattern) = 0 ↔ (items : Multiset Pattern) = 0
    simp
  | .atom (.singleton value), items, named, inside => by
    change ((items.map name : List Pattern) : Multiset Pattern) = {name value} ↔
      (items : Multiset Pattern) = {value}
    rw [Multiset.coe_eq_singleton, Multiset.coe_eq_singleton, List.map_eq_singleton_iff]
    constructor
    · rintro ⟨item, rfl, same⟩
      rw [injective item (inside item (by simp)) value (named value (by simp [values])) same]
    · rintro rfl
      exact ⟨value, rfl, rfl⟩
  | .top, _, _, _ => Iff.rfl
  | .bottom, _, _, _ => Iff.rfl
  | .conj first second, items, named, inside => by
    have firstSame := holds_rename name injective first items
      (fun value member => named value (List.mem_append_left _ member)) inside
    have secondSame := holds_rename name injective second items
      (fun value member => named value (List.mem_append_right _ member)) inside
    exact and_congr firstSame secondSame
  | .disj first second, items, named, inside => by
    have firstSame := holds_rename name injective first items
      (fun value member => named value (List.mem_append_left _ member)) inside
    have secondSame := holds_rename name injective second items
      (fun value member => named value (List.mem_append_right _ member)) inside
    exact or_congr firstSame secondSame
  | .neg inner, items, named, inside => not_congr (holds_rename name injective inner items named inside)
  | .imp first second, items, named, inside => by
    have firstSame := holds_rename name injective first items
      (fun value member => named value (List.mem_append_left _ member)) inside
    have secondSame := holds_rename name injective second items
      (fun value member => named value (List.mem_append_right _ member)) inside
    exact imp_congr firstSame secondSame
  | .possibility inner, items, _, _ => by
    change Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltDiamond BagModel.system _ (items.map name) ↔
      Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltDiamond BagModel.system _ items
    rw [gsltDiamond_spec, gsltDiamond_spec]
    exact iff_of_false (fun ⟨target, step, _⟩ => BagModel.no_step _ target step)
      (fun ⟨target, step, _⟩ => BagModel.no_step _ target step)
  | .outgoingUniversal inner, items, _, _ =>
    iff_of_true (fun target step => (BagModel.no_step _ target step).elim)
      (fun target step => (BagModel.no_step _ target step).elim)
  | .separating index first second, items, named, inside => by
    change (∃ left right : List Pattern, (index = 0 ∧ (left ++ right).Perm (items.map name)) ∧
        BagModel.holds (rename name first) left ∧ BagModel.holds (rename name second) right) ↔
      (∃ left right : List Pattern, (index = 0 ∧ (left ++ right).Perm items) ∧
        BagModel.holds first left ∧ BagModel.holds second right)
    have firstNamed : ∀ value ∈ values first, value ∈ domain :=
      fun value member => named value (List.mem_append_left _ member)
    have secondNamed : ∀ value ∈ values second, value ∈ domain :=
      fun value member => named value (List.mem_append_right _ member)
    constructor
    · rintro ⟨left, right, ⟨declared, split⟩, leftHolds, rightHolds⟩
      obtain ⟨left', right', perm, rfl, rfl⟩ := split_of_map name split
      have leftInside : ∀ item ∈ left', item ∈ domain :=
        fun item member => inside item (perm.subset (List.mem_append_left _ member))
      have rightInside : ∀ item ∈ right', item ∈ domain :=
        fun item member => inside item (perm.subset (List.mem_append_right _ member))
      exact ⟨left', right', ⟨declared, perm⟩,
        (holds_rename name injective first left' firstNamed leftInside).mp leftHolds,
        (holds_rename name injective second right' secondNamed rightInside).mp rightHolds⟩
    · rintro ⟨left, right, ⟨declared, perm⟩, leftHolds, rightHolds⟩
      have leftInside : ∀ item ∈ left, item ∈ domain :=
        fun item member => inside item (perm.subset (List.mem_append_left _ member))
      have rightInside : ∀ item ∈ right, item ∈ domain :=
        fun item member => inside item (perm.subset (List.mem_append_right _ member))
      refine ⟨left.map name, right.map name, ⟨declared, ?_⟩,
        (holds_rename name injective first left firstNamed leftInside).mpr leftHolds,
        (holds_rename name injective second right secondNamed rightInside).mpr rightHolds⟩
      rw [← List.map_append]
      exact perm.map name

/-! ## Names are numerals -/

def zeroRule : GrammarRule := { label := "zero", category := "Atom", params := [], syntaxPattern := [] }

def succRule : GrammarRule :=
  { label := "succ", category := "Atom", params := [.simple "n" (.base "Atom")], syntaxPattern := [] }

/-- **The payload language of names**: `zero` and `succ`. -/
def numerals : LanguageDef where
  name := "Names"
  types := ["Atom"]
  terms := [zeroRule, succRule]
  equations := []
  rewrites := []

theorem payload : Payload numerals := ⟨rfl, rfl, by decide⟩

/-- The numeral of a number. -/
def numeral : Nat → Pattern
  | 0 => .apply "zero" []
  | n + 1 => .apply "succ" [numeral n]

theorem numeral_injective : Function.Injective numeral := by
  intro first second same
  induction first generalizing second with
  | zero => cases second <;> simp_all [numeral]
  | succ first recurse =>
    cases second with
    | zero => simp [numeral] at same
    | succ second =>
      simp only [numeral, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at same
      rw [recurse same]

theorem zeroRule_notBare : ¬ UsesBareCollection zeroRule := by
  rintro ⟨_, _, _, bare⟩
  simp [zeroRule, GrammarRule.bareParams] at bare

theorem succRule_notBare : ¬ UsesBareCollection succRule := by
  rintro ⟨_, _, _, bare⟩
  simp [succRule, GrammarRule.bareParams] at bare

theorem hasType_numeral : ∀ n, HasType (answers numerals) FreeTypeContext.empty [] (numeral n) (.base "Atom")
  | 0 => .constructor (rule := zeroRule) (by simp [answers, numerals]) zeroRule_notBare .nil
  | n + 1 => .constructor (rule := succRule) (by simp [answers, numerals]) succRule_notBare
      (.cons trivial rfl (hasType_numeral n) .nil)

theorem isPayload_numeral : ∀ n, IsPayload numerals (numeral n)
  | 0 => ⟨rfl, rfl, hasType_numeral 0⟩
  | n + 1 => by
    obtain ⟨object, free, -⟩ := isPayload_numeral n
    refine ⟨?_, ?_, hasType_numeral (n + 1)⟩
    · simp [numeral, isObjectPattern, isObjectPatternList, object]
    · simp [numeral, bagFree, bagFreeList, free]

/-- **Each answer is named by its position** in a list. -/
def nameIn (domain : List Pattern) (item : Pattern) : Pattern := numeral (domain.idxOf item)

theorem nameIn_injective (domain : List Pattern) :
    ∀ x ∈ domain, ∀ y ∈ domain, nameIn domain x = nameIn domain y → x = y := by
  intro x xInside y _ same
  exact (List.idxOf_inj xInside).mp (numeral_injective same)

theorem payloads_named (domain items : List Pattern) : Payloads numerals (items.map (nameIn domain)) := by
  intro item member
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp member
  exact isPayload_numeral _

/-! ## Every bag formula at the front door -/

/-- The answers and the values a formula names. -/
def domainOf (formula : Core.Formula BagModel.Leaf) (items : List Pattern) : List Pattern := items ++ values formula

/-- The formula with its values named. -/
def named (formula : Core.Formula BagModel.Leaf) (items : List Pattern) : Core.Formula BagModel.Leaf :=
  rename (nameIn (domainOf formula items)) formula

/-- The bag of the answers' names. -/
def namedBag (formula : Core.Formula BagModel.Leaf) (items : List Pattern) : List Pattern :=
  items.map (nameIn (domainOf formula items))

/-- The front door's closed formula of a bag formula at a bag of answers. -/
def closedFormula (formula : Core.Formula BagModel.Leaf) (items : List Pattern) : Formula 0 :=
  closedOf (reading RelationEnv.empty payload (leaves (named formula items))) (named formula items)

theorem holds_named (formula : Core.Formula BagModel.Leaf) (items : List Pattern) :
    BagModel.holds (named formula items) (namedBag formula items) ↔ BagModel.holds formula items :=
  holds_rename _ (nameIn_injective (domainOf formula items)) formula items
    (fun _ member => List.mem_append_right _ member) (fun _ member => List.mem_append_left _ member)

/-- **Every bag formula at every bag of answers is the front door's native type** at the bag of names. -/
theorem holds_iff_frontDoor (formula : Core.Formula BagModel.Leaf) (items : List Pattern) :
    BagModel.holds formula items ↔
      (Reference RelationEnv.empty numerals).sat Env.closed (closedFormula formula items)
        (BagModel.encode (namedBag formula items)) :=
  (holds_named formula items).symm.trans
    ((Mettapedia.OSLF.NativeTypes.Instances.SpatialBag.meaning_at_bag _ _).symm.trans
      (meaning_iff (relEnv := RelationEnv.empty) payload (named formula items)
        (payloads_named (domainOf formula items) items)))

theorem no_equations : (answers numerals).equations = [] := rfl

theorem no_algebra : (answers numerals).hasAlgebraDeclarations = false := answers_algebra payload

theorem guarded : (answers numerals).rewrites.all (fun rule => rule.premises.all BagForms.guard) = true := rfl

/-- The canonical forms of the bags of names. -/
def forms : CanonicalForms RelationEnv.empty (answers numerals) 2 :=
  BagForms.forms no_equations no_algebra guarded 2

/-- The bag parts decider over the bags of names, with a number of rounds. -/
def decider (rounds : ℕ) : Decider RelationEnv.empty (answers numerals) :=
  partsDecider (fuel := 2) (presentations := List.singleton) (BagForms.canonical no_equations no_algebra)
    (BagForms.coherent no_equations no_algebra guarded 2) (BagForms.parts no_equations no_algebra) rounds

/-- **The generated front door's answer** about a bag formula at a bag of answers, at the bag of their names. -/
def answer (formula : Core.Formula BagModel.Leaf) (items : List Pattern) (rounds : ℕ) : Option Bool :=
  frontDoorOn (reading RelationEnv.empty payload (leaves (named formula items))) (decider rounds) [] 2
    (named formula items) (BagModel.encode (namedBag formula items)) rounds (some forms)

/-- **The generated front door's decided answers are sound** about every bag formula at every bag of answers. -/
theorem answer_sound {formula : Core.Formula BagModel.Leaf} {items : List Pattern} {rounds : ℕ} {result : Bool}
    (answered : answer formula items rounds = some result) : BagModel.holds formula items ↔ result = true := by
  rw [holds_iff_frontDoor]
  unfold answer frontDoorOn at answered
  split at answered
  · rename_i evidence proved
    cases answered
    exact iff_of_true (askWith_proved (forms := some forms) (by rfl) proved) rfl
  · rename_i evidence refuted
    cases answered
    exact iff_of_false (askWith_refuted (forms := some forms) (by rfl) refuted) Bool.false_ne_true
  · cases answered

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.AnswerBag.Names

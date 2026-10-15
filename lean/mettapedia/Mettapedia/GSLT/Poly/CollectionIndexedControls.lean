import Mettapedia.GSLT.Poly.CollectionIndexedAlgebra
import Mettapedia.GSLT.Poly.CollectionIndexedEquiv
import Mettapedia.GSLT.Poly.CollectionIndexedRho

/-!
# Controls for indexed collection quotients

A second language has two sorts, one binder, and one bag. A vector keeps
order. A set forgets a duplicate and a bag keeps it. Outermost bag
permutation identifies a swapped parallel pair and does not flatten or delete
`PZero`. The parallel algebra does both, including under an input binder,
and does not contract `QuoteDrop`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Poly.CollectionIndexedControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.Poly.CollectionIndexed
open Mettapedia.GSLT.Poly.CollectionIndexedEquiv
open Mettapedia.GSLT.Poly.CollectionIndexedRho
open Mettapedia.GSLT.Poly.CollectionIndexedAlgebra
open Mettapedia.GSLT.Poly.RhoCalcControl
open Mettapedia.GSLT.Poly.BindingSignature
open IPFunctor
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag

def unitRule : GrammarRule :=
  { label := "Unit", category := "A", params := [], syntaxPattern := [] }

def wrapRule : GrammarRule :=
  { label := "Wrap", category := "B",
    params := [.abstraction "f" (.arrow (.base "A") (.base "B"))],
    syntaxPattern := [] }

def bagRule : GrammarRule :=
  { label := "Bag", category := "B",
    params := [.simple "xs" (.collection .hashBag (.base "B"))],
    syntaxPattern := [] }

/-- Two sorts, one binder, and one bag. Not the ρ calculus. -/
def binderBagLanguage : LanguageDef :=
  { name := "BinderBag", types := [{ name := "A" }, { name := "B" }],
    terms := [unitRule, wrapRule, bagRule], equations := [], rewrites := [] }

theorem binderBag_fragment : ∀ rule ∈ binderBagLanguage.terms, FragmentRule rule := by
  intro rule member
  simp only [binderBagLanguage, unitRule, wrapRule, bagRule, List.mem_cons,
    List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl
  · intro parameter member
    simp at member
  · intro parameter member
    simp only [List.mem_singleton] at member
    subst member
    simp [bindingDecl?, baseCollection?]
  · intro parameter member
    simp only [List.mem_singleton] at member
    subst member
    simp [bindingDecl?, baseCollection?]

theorem binderBag_labels : (binderBagLanguage.terms.map (·.label)).Nodup := by
  decide

theorem binderBag_uniqueBare : UniqueBare binderBagLanguage := by
  intro rule₁ rule₂ kind element₁ element₂ mem₁ mem₂ _category bare₁ bare₂
  simp only [binderBagLanguage, unitRule, wrapRule, bagRule, List.mem_cons,
    List.mem_nil_iff, or_false] at mem₁ mem₂
  rcases mem₁ with rfl | rfl | rfl
  · simp [bareCollection?] at bare₁
  · simp [bareCollection?] at bare₁
  · rcases mem₂ with rfl | rfl | rfl
    · simp [bareCollection?] at bare₂
    · simp [bareCollection?] at bare₂
    · rfl

/-- Closed patterns of the second language at `B` are its indexed trees. -/
noncomputable def binderBagEquiv :
    Tree binderBagLanguage ([], "B") ≃ ClosedObject binderBagLanguage "B" :=
  closedIndexedEquiv binderBag_fragment binderBag_labels binderBag_uniqueBare "B"

theorem vec_pair_shaped :
    VecShaped (.collection .vec [.apply "U" [], .apply "W" []] none) := by
  refine ⟨rfl, ?_⟩
  intro element member
  simp only [List.mem_cons, List.mem_singleton] at member
  rcases member with rfl | rfl <;> simp [VecShaped]

/-- A vector does not identify a permutation of its elements. -/
theorem vec_keeps_order :
    ¬ PatternCong
      (.collection .vec [.apply "U" [], .apply "W" []] none)
      (.collection .vec [.apply "W" [], .apply "U" []] none) := by
  intro related
  have equal := vec_cong_eq related (Or.inl vec_pair_shaped)
  simp [Pattern.collection.injEq, Pattern.apply.injEq] at equal

/-- A set forgets one copy of a duplicated element. -/
theorem set_forgets_duplicate :
    PatternCong
      (.collection .hashSet [.apply "U" [], .apply "U" []] none)
      (.collection .hashSet [.apply "U" []] none) :=
  PatternCong.setDup

/-- Length of a top-level hash bag. -/
def hashBagLength : Pattern → Option Nat
  | .collection .hashBag elements none => some elements.length
  | _ => none

theorem patternCong_hashBagLength {left right : Pattern}
    (related : PatternCong left right) :
    hashBagLength left = hashBagLength right := by
  induction related with
  | refl _ => rfl
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ inductionHypothesis inductionHypothesis' =>
      exact inductionHypothesis.trans inductionHypothesis'
  | bagPerm permutation =>
      simp [hashBagLength, List.Perm.length_eq permutation]
  | setPerm _ => simp [hashBagLength]
  | setDup => simp [hashBagLength]
  | applyAt _ _ => simp [hashBagLength]
  | lambdaAt _ _ => simp [hashBagLength]
  | multiLambdaAt _ _ => simp [hashBagLength]
  | collectionAt _ _ =>
      simp [hashBagLength, List.length_append]

/-- A bag keeps both copies of a duplicated element. -/
theorem bag_keeps_duplicate :
    ¬ PatternCong
      (.collection .hashBag [.apply "U" [], .apply "U" []] none)
      (.collection .hashBag [.apply "U" []] none) := by
  intro related
  have lengths := patternCong_hashBagLength related
  simp [hashBagLength] at lengths

/-- Swapped parallel processes are one element of the outermost bag quotient. -/
theorem ordered_swapped_one :
    Quotient.mk rhoBagSetoid orderedClosed = Quotient.mk rhoBagSetoid swappedClosed :=
  Quotient.sound parallel_swap_related

/-- A nested bag is not an outermost permutation of the flat bag. -/
theorem nested_not_one : ¬ Relation.EqvGen RhoBagStep nestedPar orderedPar :=
  nested_not_flat

/-- `{P | 0}` is not an outermost permutation of `{P}`. -/
theorem zero_not_one : ¬ Relation.EqvGen RhoBagStep withZero onlyDrop := by
  intro related
  have lengths := eqv_outerLength related
  simp [withZero, onlyDrop, outerLength] at lengths

def withZeroProcess : RhoProcess := ⟨withZero, withZero_closed⟩

def onlyDropProcess : RhoProcess := ⟨onlyDrop, onlyDrop_closed⟩

/-- The algebra deletes `PZero`, and the multiset reading agrees. -/
theorem zero_same_bag : fromProcess withZeroProcess = fromProcess onlyDropProcess :=
  algebra_fromProcess zero_deletes

def nestedProcess : RhoProcess := ofList [orderedPar] nestedClosed

def flatProcess : RhoProcess := ofList [procDrop, procOutput] flatClosed

/-- The algebra flattens a nested bag, and the multiset reading agrees. -/
theorem nested_same_bag : fromProcess nestedProcess = fromProcess flatProcess :=
  algebra_fromProcess (by simpa [nestedProcess, flatProcess, ofList] using nested_flattens)

/-- `QuoteDrop` identifies a bag the parallel algebra keeps apart. -/
theorem quote_drop_outside : ¬ AlgebraCong quotedOutput procOutput :=
  quoted_not_algebra

theorem quote_drop_same_bag : fromProcess quotedProcess = fromProcess plainProcess :=
  quoted_fromProcess

/-! ## Distinct labels do not separate two bare collections -/

def leftVecRule : GrammarRule :=
  { label := "Left", category := "A",
    params := [.simple "xs" (.collection .vec (.base "A"))], syntaxPattern := [] }

def rightVecRule : GrammarRule :=
  { label := "Right", category := "A",
    params := [.simple "xs" (.collection .vec (.base "A"))], syntaxPattern := [] }

/-- Two bare vector rules, with distinct labels, of one element sort. -/
def twoBareLanguage : LanguageDef :=
  { name := "TwoBare", types := [{ name := "A" }],
    terms := [leftVecRule, rightVecRule], equations := [], rewrites := [] }

theorem twoBare_labels : (twoBareLanguage.terms.map (·.label)).Nodup := by
  decide

def leftVecHead : HeadData leftVecRule.params where
  counts := [0]
  lengths := [0]
  counts_length := rfl
  lengths_length := rfl
  counts_fixed := by
    intro index _
    cases index <;> rfl
  lengths_fixed := by
    intro index _
    cases index <;> rfl

def rightVecHead : HeadData rightVecRule.params where
  counts := [0]
  lengths := [0]
  counts_length := rfl
  lengths_length := rfl
  counts_fixed := by
    intro index _
    cases index <;> rfl
  lengths_fixed := by
    intro index _
    cases index <;> rfl

def leftVecPacked :
    {rule : GrammarRule //
      rule ∈ twoBareLanguage.terms ∧ FragmentRule rule ∧ rule.category = "A"} :=
  ⟨leftVecRule, by
    refine ⟨?_, ?_, rfl⟩
    · exact List.mem_cons_self
    · intro parameter member
      simp only [leftVecRule, List.mem_singleton] at member
      subst member
      simp [bindingDecl?, baseCollection?]⟩

def rightVecPacked :
    {rule : GrammarRule //
      rule ∈ twoBareLanguage.terms ∧ FragmentRule rule ∧ rule.category = "A"} :=
  ⟨rightVecRule, by
    refine ⟨?_, ?_, rfl⟩
    · exact List.mem_cons_of_mem _ (List.mem_cons_self)
    · intro parameter member
      simp only [rightVecRule, List.mem_singleton] at member
      subst member
      simp [bindingDecl?, baseCollection?]⟩

def leftEmptyTree : Tree twoBareLanguage ([], "A") :=
  IFreeM.liftBind (P := polynomial (indexedSignature twoBareLanguage))
    ⟨leftVecPacked, leftVecHead⟩ Fin.elim0

def rightEmptyTree : Tree twoBareLanguage ([], "A") :=
  IFreeM.liftBind (P := polynomial (indexedSignature twoBareLanguage))
    ⟨rightVecPacked, rightVecHead⟩ Fin.elim0

theorem leftEmpty_pattern : toPattern leftEmptyTree = .collection .vec [] none := by
  rw [toPattern_liftBind]
  simp [nodeOf, leftEmptyTree, leftVecPacked, leftVecRule, bareCollection?, List.ofFn_zero]

theorem rightEmpty_pattern : toPattern rightEmptyTree = .collection .vec [] none := by
  rw [toPattern_liftBind]
  simp [nodeOf, rightEmptyTree, rightVecPacked, rightVecRule, bareCollection?, List.ofFn_zero]

/-- The two labels are distinct, and both rules are bare vectors. -/
theorem twoBare_not_unique : ¬ UniqueBare twoBareLanguage := by
  intro unique
  have same :=
    unique (rule₁ := leftVecRule) (rule₂ := rightVecRule) (kind := .vec) (element₁ := "A")
      (element₂ := "A") List.mem_cons_self
      (List.mem_cons_of_mem _ List.mem_cons_self) rfl
      (by simp [bareCollection?, leftVecRule]) (by simp [bareCollection?, rightVecRule])
  simp [leftVecRule, rightVecRule] at same

/-- The empty vectors print as one pattern and are not one tree. -/
theorem bare_labels_not_injective :
    toPattern leftEmptyTree = toPattern rightEmptyTree ∧ leftEmptyTree ≠ rightEmptyTree := by
  refine ⟨?_, ?_⟩
  · rw [leftEmpty_pattern, rightEmpty_pattern]
  · intro same
    have operators :=
      (IFreeM.liftBind_inj (P := polynomial (indexedSignature twoBareLanguage))
        (s := ([], "A")) ⟨leftVecPacked, leftVecHead⟩ ⟨rightVecPacked, rightVecHead⟩
        Fin.elim0 Fin.elim0).mp same
    obtain ⟨equal, _⟩ := operators
    have rules := congrArg (fun operator => operator.1.1.label) equal
    simp [leftVecPacked, rightVecPacked, leftVecRule, rightVecRule] at rules
    exact absurd rules (by decide)

end Mettapedia.GSLT.Poly.CollectionIndexedControls

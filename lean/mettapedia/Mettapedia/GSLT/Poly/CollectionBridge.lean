import Mettapedia.GSLT.LanguageDef.WellSorted
import Mettapedia.GSLT.Poly.CollectionIndexedEquiv
import Mathlib.Data.List.OfFn
import Mathlib.Data.PFunctor.Univariate.Basic
import Mathlib.Data.W.Basic

/-!
# Ordered collections as the list polynomial

A language whose constructors are nullary or one `vec` of their own sort has,
at that sort, the polynomial whose head is either a nullary label or a length
and whose directions are the positions of that length. Closed object patterns
typed at the sort are the W-trees of this polynomial.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Poly.CollectionBridge

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.Poly.BindingLanguage hiding toPattern
open Mettapedia.GSLT.Poly.CollectionIndexed
open Mettapedia.GSLT.Poly.CollectionIndexedEquiv

def atomURule : GrammarRule :=
  { label := "U", category := "A", params := [], syntaxPattern := [] }

def atomWRule : GrammarRule :=
  { label := "W", category := "A", params := [], syntaxPattern := [] }

def vecRule : GrammarRule :=
  { label := "Vec", category := "A",
    params := [.simple "xs" (.collection .vec (.base "A"))], syntaxPattern := [] }

theorem not_bare_atom (rule : GrammarRule) (empty : rule.params = []) :
    ¬ UsesBareCollection rule := by
  intro used
  rcases used with ⟨_, _, _, shape⟩
  cases mode : rule.collectionRepresentation <;> simp [GrammarRule.bareParams, mode, empty] at shape

/-- Heads of the ordered-collection polynomial: two atoms, or a length. -/
inductive VecLabel where
  | u
  | w
  | length (n : Nat)

/-- Directions of one head. An atom has none. A length has one per position. -/
abbrev vecBranch : VecLabel → Type
  | .u => Empty
  | .w => Empty
  | .length n => Fin n

/-- The list polynomial of the ordered-collection language. -/
abbrev vecLanguagePolynomial : PFunctor.{0, 0} :=
  ⟨VecLabel, vecBranch⟩

/-- Nullary atoms and one ordered collection of the same sort. -/
def vecLanguage : LanguageDef :=
  { name := "Vec", types := [{ name := "A" }],
    terms := [atomURule, atomWRule, vecRule],
    equations := [], rewrites := [] }

/-- One node of the list polynomial, once its directions are already patterns. -/
def shapePattern : (Σ label : VecLabel, vecBranch label → Pattern) → Pattern
  | ⟨.u, _⟩ => .apply "U" []
  | ⟨.w, _⟩ => .apply "W" []
  | ⟨.length _, children⟩ => .collection .vec (List.ofFn children) none

/-- A W-tree of the list polynomial, printed as a pattern. -/
def vecToPattern : WType vecBranch → Pattern :=
  WType.elim Pattern shapePattern

theorem vecToPattern_mk (label : VecLabel) (children : vecBranch label → WType vecBranch) :
    vecToPattern (WType.mk label children) =
      shapePattern ⟨label, fun index => vecToPattern (children index)⟩ := by
  simp [vecToPattern, WType.elim]

theorem ofFn_elements_typed {n : Nat} (children : Fin n → Pattern)
    (typed : ∀ index, HasType vecLanguage FreeTypeContext.empty [] (children index) (.base "A")) :
    ElementsHaveType vecLanguage FreeTypeContext.empty [] (List.ofFn children) (.base "A") := by
  induction n with
  | zero =>
      simp [List.ofFn_zero]
      exact ElementsHaveType.nil [] (.base "A")
  | succ n inductionHypothesis =>
      rw [List.ofFn_succ]
      exact ElementsHaveType.cons (typed 0)
        (inductionHypothesis (fun index => children index.succ) (fun index => typed index.succ))

theorem vecToPattern_hasType (tree : WType vecBranch) :
    HasType vecLanguage FreeTypeContext.empty [] (vecToPattern tree) (.base "A") := by
  induction tree with
  | mk label children typed =>
      rw [vecToPattern_mk]
      cases label with
      | u =>
          exact HasType.constructor (rule := atomURule) (by simp [vecLanguage])
            (not_bare_atom atomURule rfl) ArgumentsHaveTypes.nil
      | w =>
          exact HasType.constructor (rule := atomWRule) (by simp [vecLanguage])
            (not_bare_atom atomWRule rfl) ArgumentsHaveTypes.nil
      | length n =>
          simp only [shapePattern]
          exact HasType.collectionConstructor (rule := vecRule) (by simp [vecLanguage]) rfl
            (ofFn_elements_typed _ typed)

theorem ofFn_elements_object {n : Nat} (children : Fin n → Pattern)
    (objects : ∀ index, isObjectPattern (children index) = true) :
    isObjectPatternList (List.ofFn children) = true := by
  induction n with
  | zero => simp [List.ofFn_zero, isObjectPatternList]
  | succ n inductionHypothesis =>
      rw [List.ofFn_succ]
      simp [isObjectPatternList, objects 0,
        inductionHypothesis (fun index => children index.succ) (fun index => objects index.succ)]

theorem vecToPattern_isObject (tree : WType vecBranch) :
    isObjectPattern (vecToPattern tree) = true := by
  induction tree with
  | mk label children objects =>
      rw [vecToPattern_mk]
      cases label with
      | u => simp [shapePattern, isObjectPattern, isObjectPatternList]
      | w => simp [shapePattern, isObjectPattern, isObjectPatternList]
      | length _ =>
          simp [shapePattern, isObjectPattern, ofFn_elements_object _ objects]

theorem elements_get :
    {elements : List Pattern} →
      ElementsHaveType vecLanguage FreeTypeContext.empty [] elements (.base "A") →
      (index : Nat) → (bound : index < elements.length) →
      HasType vecLanguage FreeTypeContext.empty []
        (elements.get ⟨index, bound⟩) (.base "A")
  | [], _, _, bound => by simp at bound
  | _ :: _, .cons headTyped _, 0, _ => by simpa using headTyped
  | _ :: tail, .cons _ tailTyped, index + 1, bound => by
      simpa using elements_get tailTyped index (by simpa using bound)

theorem vec_member_object {elements : List Pattern}
    (objects : isObjectPatternList elements = true) (element : Pattern)
    (member : element ∈ elements) : isObjectPattern element = true := by
  induction elements with
  | nil => cases member
  | cons head tail inductionHypothesis =>
      simp [isObjectPatternList] at objects
      cases member with
      | head => exact objects.1
      | tail _ tailMember => exact inductionHypothesis objects.2 tailMember

/-- Every closed object pattern of the ordered-collection language is a W-tree. -/
theorem vec_exists_of_size :
    (bound : Nat) → (pattern : Pattern) → sizeOf pattern < bound →
      (type : TypeExpr) →
      HasType vecLanguage FreeTypeContext.empty [] pattern type →
      type = .base "A" →
      isObjectPattern pattern = true →
      ∃ tree : WType vecBranch, vecToPattern tree = pattern
  | 0, _, small, _, _, _, _ => absurd small (Nat.not_lt_zero _)
  | bound + 1, pattern, small, _, typed, typeEqual, objects => by
      cases pattern with
      | bvar _ =>
          cases typed with
          | bvar found => simp at found
      | fvar _ =>
          cases typed with
          | fvar found => simp [FreeTypeContext.empty] at found
      | lambda _ _ =>
          cases typed with
          | lambda _ => cases typeEqual
      | multiLambda _ _ _ =>
          cases typed with
          | multiLambda _ => cases typeEqual
      | subst _ _ => simp [isObjectPattern] at objects
      | apply _ arguments =>
          cases typed with
          | constructor member notBare argumentsTyped =>
              rename_i rule
              simp only [vecLanguage, List.mem_cons, List.mem_nil_iff, or_false] at member
              rcases member with rfl | rfl | rfl
              · have argumentsEmpty : arguments = [] := by
                  simpa [atomURule, List.eq_nil_of_length_eq_zero] using
                    argumentsTyped.length_eq
                subst argumentsEmpty
                exact ⟨WType.mk .u Empty.elim, by simp [vecToPattern_mk, shapePattern, atomURule]⟩
              · have argumentsEmpty : arguments = [] := by
                  simpa [atomWRule, List.eq_nil_of_length_eq_zero] using
                    argumentsTyped.length_eq
                subst argumentsEmpty
                exact ⟨WType.mk .w Empty.elim, by simp [vecToPattern_mk, shapePattern, atomWRule]⟩
              · exact False.elim (notBare ⟨"xs", .vec, .base "A", rfl⟩)
      | collection collectionType elements rest =>
          cases typed with
          | collection _ => cases typeEqual
          | collectionConstructor member shape elementsTyped =>
              simp only [vecLanguage, List.mem_cons, List.mem_nil_iff, or_false] at member
              rcases member with rfl | rfl | rfl
              · simp only [atomURule] at shape
                cases shape
              · simp only [atomWRule] at shape
                cases shape
              · simp only [vecRule] at shape
                have objectParts :
                    rest.isNone = true ∧ isObjectPatternList elements = true := by
                  simpa [isObjectPattern, Bool.and_eq_true] using objects
                cases rest with
                | some _ => simp at objectParts
                | none =>
                    injection shape with parameterEqual _
                    injection parameterEqual with _ elementTypeEqual
                    injection elementTypeEqual with collectionEqual elementEqual
                    cases collectionEqual
                    cases elementEqual
                    have children : ∀ index : Fin elements.length,
                        ∃ child : WType vecBranch,
                          vecToPattern child =
                            elements.get ⟨index.1, index.2⟩ := by
                      intro index
                      have size : sizeOf (elements.get ⟨index.1, index.2⟩) < bound := by
                        have smaller := List.sizeOf_lt_of_mem
                          (List.get_mem elements ⟨index.1, index.2⟩)
                        simp only [Pattern.collection.sizeOf_spec] at small
                        omega
                      exact vec_exists_of_size bound _
                        size (.base "A")
                        (elements_get elementsTyped index.1 index.2) rfl
                        (vec_member_object objectParts.2 _
                          (List.get_mem elements ⟨index.1, index.2⟩))
                    choose child printed using children
                    refine ⟨WType.mk (.length elements.length) child, ?_⟩
                    rw [vecToPattern_mk]
                    simp only [shapePattern]
                    congr 1
                    apply List.ext_getElem
                    · simp [List.length_ofFn]
                    · intro index _ indexGiven
                      simp only [List.getElem_ofFn]
                      simpa using printed ⟨index, indexGiven⟩

theorem vecToPattern_injective {left right : WType vecBranch}
    (same : vecToPattern left = vecToPattern right) : left = right := by
  induction left generalizing right with
  | mk label children inductionHypothesis =>
      cases right with
      | mk label' children' =>
          rw [vecToPattern_mk, vecToPattern_mk] at same
          cases label with
          | u =>
              cases label' with
              | u =>
                  have childrenEqual : children = children' := by
                    funext empty
                    nomatch empty
                  subst childrenEqual
                  rfl
              | w => simp [shapePattern, Pattern.apply.injEq] at same
              | length _ => simp [shapePattern] at same
          | w =>
              cases label' with
              | u => simp [shapePattern, Pattern.apply.injEq] at same
              | w =>
                  have childrenEqual : children = children' := by
                    funext empty
                    nomatch empty
                  subst childrenEqual
                  rfl
              | length _ => simp [shapePattern] at same
          | length n =>
              cases label' with
              | u => simp [shapePattern] at same
              | w => simp [shapePattern] at same
              | length m =>
                  simp only [shapePattern, Pattern.collection.injEq] at same
                  rcases same with ⟨_, listsEqual, _⟩
                  have lengthEqual : n = m := by
                    simpa [List.length_ofFn] using congrArg List.length listsEqual
                  subst lengthEqual
                  have childrenEqual : children = children' := by
                    funext index
                    apply inductionHypothesis index
                    have atIndex :=
                      congrArg (fun list : List Pattern => list[index.1]?) listsEqual
                    simp only [List.getElem?_ofFn, dif_pos index.isLt] at atIndex
                    injection atIndex
                  subst childrenEqual
                  rfl

theorem vecLanguage_fragment : ∀ rule ∈ vecLanguage.terms, FragmentRule rule := by
  intro rule member
  simp only [vecLanguage, atomURule, atomWRule, vecRule, List.mem_cons, List.mem_nil_iff,
    or_false] at member
  rcases member with rfl | rfl | rfl
  · intro parameter member
    simp at member
  · intro parameter member
    simp at member
  · intro parameter member
    simp only [List.mem_singleton] at member
    subst member
    simp [bindingDecl?, baseCollection?]

theorem vecLanguage_labels : (vecLanguage.terms.map (·.label)).Nodup := by
  decide

theorem vecLanguage_uniqueBare : UniqueBare vecLanguage := by
  intro rule₁ rule₂ kind element₁ element₂ mem₁ mem₂ _category bare₁ bare₂
  simp only [vecLanguage, atomURule, atomWRule, vecRule, List.mem_cons, List.mem_nil_iff,
    or_false] at mem₁ mem₂
  rcases mem₁ with rfl | rfl | rfl
  · simp [bareCollection?] at bare₁
  · simp [bareCollection?] at bare₁
  · rcases mem₂ with rfl | rfl | rfl
    · simp [bareCollection?] at bare₂
    · simp [bareCollection?] at bare₂
    · rfl

theorem vecLanguage_vecOnly : VecOnly vecLanguage := by
  intro rule member parameter parameterMember kind element shape
  simp only [vecLanguage, atomURule, atomWRule, vecRule, List.mem_cons, List.mem_nil_iff,
    or_false] at member
  rcases member with rfl | rfl | rfl
  · simp at parameterMember
  · simp at parameterMember
  · simp only [List.mem_singleton] at parameterMember
    subst parameterMember
    simp [baseCollection?] at shape
    exact shape.1.symm

/-- Indexed trees of the ordered-collection language. -/
noncomputable def indexedVecEquiv :
    Tree vecLanguage ([], "A") ≃ ClosedObject vecLanguage "A" :=
  closedIndexedEquiv vecLanguage_fragment vecLanguage_labels vecLanguage_uniqueBare "A"

theorem toPattern_indexedVec (object : ClosedObject vecLanguage "A") :
    toPattern (indexedVecEquiv.symm object) = object.1 :=
  congrArg Subtype.val (indexedVecEquiv.right_inv object)

/-- The list-polynomial tree whose print is the indexed tree. -/
noncomputable def wRecover (tree : Tree vecLanguage ([], "A")) : WType vecBranch :=
  Classical.choose
    (vec_exists_of_size (sizeOf (toPattern tree) + 1) (toPattern tree) (Nat.lt_succ_self _)
      (.base "A") (toPattern_hasType tree) rfl (toPattern_isObject tree))

theorem wRecover_spec (tree : Tree vecLanguage ([], "A")) :
    vecToPattern (wRecover tree) = toPattern tree :=
  Classical.choose_spec
    (vec_exists_of_size (sizeOf (toPattern tree) + 1) (toPattern tree) (Nat.lt_succ_self _)
      (.base "A") (toPattern_hasType tree) rfl (toPattern_isObject tree))

/-- List-polynomial trees are the indexed trees of this language. -/
noncomputable def wTypeTreeEquiv : WType vecBranch ≃ Tree vecLanguage ([], "A") where
  toFun tree :=
    indexedVecEquiv.symm ⟨vecToPattern tree, vecToPattern_hasType tree, vecToPattern_isObject tree⟩
  invFun := wRecover
  left_inv tree := by
    have printed :=
      wRecover_spec
        (indexedVecEquiv.symm ⟨vecToPattern tree, vecToPattern_hasType tree, vecToPattern_isObject tree⟩)
    have back :=
      toPattern_indexedVec ⟨vecToPattern tree, vecToPattern_hasType tree, vecToPattern_isObject tree⟩
    exact vecToPattern_injective (printed.trans back)
  right_inv tree := by
    have sameObject :
        (⟨vecToPattern (wRecover tree), vecToPattern_hasType (wRecover tree),
            vecToPattern_isObject (wRecover tree)⟩ : ClosedObject vecLanguage "A") =
          ⟨toPattern tree, toPattern_hasType tree, toPattern_isObject tree⟩ :=
      Subtype.ext (wRecover_spec tree)
    exact (congrArg indexedVecEquiv.symm sameObject).trans (indexedVecEquiv.left_inv tree)

/-- With only vectors, the pattern quotient is already the indexed tree. -/
noncomputable def vecLanguageIndexed :
    Quotient (patternSetoid (language := vecLanguage) "A") ≃ Tree vecLanguage ([], "A") :=
  vecQuotientEquiv vecLanguage_fragment vecLanguage_labels vecLanguage_uniqueBare
    vecLanguage_vecOnly "A"

/-- Closed object patterns at the base sort are the W-trees of the list polynomial.
The W-trees are the indexed trees, and those are the closed patterns. -/
noncomputable def vecClosedEquiv :
    WType vecBranch ≃
      {pattern : Pattern //
        HasType vecLanguage FreeTypeContext.empty [] pattern (.base "A") ∧
          isObjectPattern pattern = true} :=
  wTypeTreeEquiv.trans indexedVecEquiv

end Mettapedia.GSLT.Poly.CollectionBridge

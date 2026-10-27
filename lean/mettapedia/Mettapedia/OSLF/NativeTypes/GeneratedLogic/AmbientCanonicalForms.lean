import Mettapedia.OSLF.NativeTypes.GeneratedLogic.AlgebraTypedForms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiCanonicalForms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ComputedNormalForm
import Mettapedia.Languages.ProcessCalculi.Ambient.MobileAmbientsReflection

/-!
# Canonical forms for mobile ambients

Mobile ambients (`ambientCalc`) compose processes in parallel in a bag with the flattening algebra and inaction as its
unit, and name ambients by terms of a second sort. Read as the typed judgment at the sorts, the bag normal form gives
canonical forms on closed processes and names (`canonical`, an instance of `AlgebraTyped`).

The rules look inside bags: entering and leaving find a capability among the components of an ambient's content, and
opening finds a capability and an ambient among the components of a composition. The normal form drops a singleton
bag, so `n[in m.P]` has no bag for the entry rule to look into. **Steps are listed at the padded form** (`pad`): every
ambient's content a bag, a singleton where the normal form has one component. Padding keeps the normal form
(`normalForm_pad`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.AmbientForms

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.PatternCode (sortPatterns patternCode patternCode_injective)
open Mettapedia.GSLT.LanguageDef.BagNormalForm
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Languages.ProcessCalculi.Ambient.Mobile
  (ambientCalc AmbientRawStep amb par step_iff_raw)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.AlgebraForms (normalForm_idempotent normalizeBag_single
  contents_normalizeBag contents_map_structural Structural)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiForms (perm_getElem_eraseIdx exists_index_of_perm
  exists_two_indices_of_perm perm_two_selected tail_none element_object)

/-- The normal form of the laws of ambients. -/
local notation "nf" => normalForm (some "AZero")

/-! ## The bag theory and the sorts -/

/-- The parallel composition. -/
abbrev parallel : GrammarRule := ambientCalc.terms[1]

theorem bareBagTheory : BareBagTheory ambientCalc parallel (some "AZero") :=
  (bagTheory_of_check (by decide +kernel)).asBare rfl

/-- The sorts of ambients. -/
def sorts : List String := ["Proc", "Name"]

theorem sortsCover : AlgebraTyped.SortsCover ambientCalc sorts := by
  intro term sort typed object
  cases typed with
  | bvar lookup => simp at lookup
  | fvar lookup => simp [FreeTypeContext.empty] at lookup
  | constructor member _ _ =>
    simp only [ambientCalc, Mettapedia.Languages.ProcessCalculi.Ambient.Mobile.terms, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [sorts]
  | collectionConstructor member _ _ =>
    simp only [ambientCalc, Mettapedia.Languages.ProcessCalculi.Ambient.Mobile.terms, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [sorts]
  | subst => simp [isObjectPattern] at object

/-- A type with no binder in it. -/
def binderFreeType : TypeExpr → Bool
  | .base _ => true
  | .arrow _ _ => false
  | .multiBinder _ => false
  | .collection _ element => binderFreeType element

/-- **Every parameter of ambients has a binder-free type.** -/
theorem params_binderFree {rule : GrammarRule} (member : rule ∈ ambientCalc.terms) :
    ∀ param ∈ rule.params, ∀ type, parameterType? param = some type → binderFreeType type = true := by
  simp only [ambientCalc, Mettapedia.Languages.ProcessCalculi.Ambient.Mobile.terms, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> intro param inside type found <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inside <;>
    (try rcases inside with rfl | rfl) <;>
    simp [parameterType?] at found <;> subst found <;> rfl

/-- Each argument of a typed application has the type of its parameter. -/
theorem argument_typed {bound : List TypeExpr} : ∀ {arguments : List Pattern} {params : List TermParam},
    ArgumentsHaveTypes ambientCalc FreeTypeContext.empty bound arguments params →
    ∀ argument ∈ arguments, ∃ param ∈ params, ∃ type, parameterType? param = some type ∧
      HasType ambientCalc FreeTypeContext.empty bound argument type
  | [], _, _, _, inside => by simp at inside
  | first :: rest, _, typed, argument, inside => by
    cases typed with
    | @cons _ _ _ parameter parameters expected _ found firstTyped restTyped =>
      rcases List.mem_cons.mp inside with rfl | later
      · exact ⟨parameter, List.mem_cons_self, expected, found, firstTyped⟩
      · obtain ⟨param, member, type, found', typed'⟩ := argument_typed restTyped argument later
        exact ⟨param, List.mem_cons_of_mem _ member, type, found', typed'⟩

/-- **A closed object of a binder-free type has canonical binder metadata**: it has no binder. -/
theorem metadata_of_typed (term : Pattern) : ∀ {bound : List TypeExpr} {type : TypeExpr},
    HasType ambientCalc FreeTypeContext.empty bound term type → binderFreeType type = true →
    isObjectPattern term = true → term.hasCanonicalBinderMetadata = true := by
  induction term using Pattern.inductionOn with
  | hbvar => intros; rfl
  | hfvar => intros; rfl
  | happly label arguments recurse =>
    intro bound type typed _ object
    obtain ⟨rule, member, -, -, -, argumentsTyped⟩ := hasType_apply_inversion typed
    simp only [isObjectPattern, isObjectPatternList_iff] at object
    simp only [Pattern.hasCanonicalBinderMetadata, hasCanonicalBinderMetadataList_iff]
    intro argument inside
    obtain ⟨param, paramMember, argumentType, found, argumentTyped⟩ := argument_typed argumentsTyped argument inside
    exact recurse argument inside argumentTyped (params_binderFree member param paramMember argumentType found)
      (object argument inside)
  | hlambda binder body _ =>
    intro bound type typed free _
    generalize patternEquality : Pattern.lambda binder body = pattern at typed
    cases typed <;> first | (cases patternEquality; done) | simp [binderFreeType] at free
  | hmultiLambda arity binders body _ =>
    intro bound type typed free _
    generalize patternEquality : Pattern.multiLambda arity binders body = pattern at typed
    cases typed <;> first | (cases patternEquality; done) | simp [binderFreeType] at free
  | hsubst => intro _ _ _ _ object; simp [isObjectPattern] at object
  | hcollection kind elements rest recurse =>
    intro bound type typed free object
    simp only [isObjectPattern, Bool.and_eq_true, isObjectPatternList_iff] at object
    simp only [Pattern.hasCanonicalBinderMetadata, hasCanonicalBinderMetadataList_iff]
    have elementwise : ∃ elementType, binderFreeType elementType = true ∧
        ElementsHaveType ambientCalc FreeTypeContext.empty bound elements elementType := by
      generalize patternEquality : Pattern.collection kind elements rest = pattern at typed
      cases typed with
      | collection elementsTyped =>
        cases patternEquality
        exact ⟨_, by simpa [binderFreeType] using free, elementsTyped⟩
      | @collectionConstructor _ rule parameterName collectionType elements' rest' elementType member shape
          elementsTyped =>
        cases patternEquality
        have bare : rule.collectionRepresentation = .bare := by
          cases representation : rule.collectionRepresentation with
          | bare => rfl
          | wrapped => simp [GrammarRule.bareParams, representation] at shape
        rw [GrammarRule.bareParams_of_bare rule bare] at shape
        have typeFree := params_binderFree member _ (by rw [shape]; exact List.mem_singleton_self _) _ rfl
        exact ⟨elementType, by simpa [binderFreeType] using typeFree, elementsTyped⟩
      | _ => cases patternEquality
    obtain ⟨elementType, elementFree, elementsTyped⟩ := elementwise
    intro element inside
    exact recurse element inside (elementsHaveType_iff.mp elementsTyped element inside) elementFree
      (object.2 element inside)

theorem metadataOfTyped : AlgebraTyped.MetadataOfTyped ambientCalc :=
  fun typed object => metadata_of_typed _ typed rfl object

/-- Closed processes and names of ambients. -/
abbrev domain : Pattern → Bool := AlgebraTyped.domain ambientCalc sorts

/-- **Canonical forms of ambients**: the bag normal form on closed processes and names. -/
theorem canonical (relEnv : RelationEnv) :
    Canonical relEnv ambientCalc (AlgebraTyped.canon ambientCalc (some "AZero") sorts) domain AlgebraTyped.reading :=
  AlgebraTyped.canonical bareBagTheory sortsCover metadataOfTyped

/-! ## Bag contents -/

theorem bagContents_perm {first second : List Pattern} (perm : first.Perm second) :
    (bagContents "AZero" first).Perm (bagContents "AZero" second) :=
  (perm.flatMap_right splice).filter _

/-- A component that is neither a bag nor inaction contributes itself. -/
theorem contents_plain {pattern : Pattern} (notUnit : pattern ≠ .apply "AZero" []) (notBag : ¬ IsBagNode pattern) :
    bagContents "AZero" [pattern] = [pattern] := by
  simp [bagContents, splice_of_not_bag notBag, notUnit]

theorem contents_apply {label : String} {arguments : List Pattern} (notUnit : label ≠ "AZero") :
    bagContents "AZero" [.apply label arguments] = [.apply label arguments] :=
  contents_plain (by simp [notUnit]) (by rintro ⟨_, same⟩; cases same)

/-- Normalizing the components of normal forms again changes no contents. -/
theorem contents_renormal (patterns : List Pattern) :
    (bagContents "AZero" ((bagContents "AZero" (patterns.map nf)).map nf)).Perm
      (bagContents "AZero" (patterns.map nf)) := by
  have each := contents_map_structural "AZero" Structural.identity 0 (elements := patterns)
    fun element _ => (normalForm_idempotent "AZero" element).symm
  simp only [Structural.identity] at each
  exact each.symm

/-- A normal form whose contents are at least two is the bag of its sorted contents. -/
theorem normalForm_bag_of_long {elements : List Pattern}
    (long : 2 ≤ (bagContents "AZero" (elements.map nf)).length) :
    nf (.collection .hashBag elements none) =
      .collection .hashBag (sortPatterns (bagContents "AZero" (elements.map nf))) none := by
  rw [normalForm_bag]
  simp only [normalizeBag]
  have sortedLong : 2 ≤ (sortPatterns (bagContents "AZero" (elements.map nf))).length := by simpa using long
  generalize sortPatterns (bagContents "AZero" (elements.map nf)) = sorted at sortedLong ⊢
  match sorted, sortedLong with
  | _ :: _ :: _, _ => rfl

/-- Two lists with the same contents normalize alike as bags. -/
theorem normalForm_bag_congr {first second : List Pattern}
    (same : (bagContents "AZero" (first.map nf)).Perm (bagContents "AZero" (second.map nf))) :
    nf (.collection .hashBag first none) = nf (.collection .hashBag second none) := by
  rw [normalForm_bag, normalForm_bag]
  exact normalizeBag_contents_perm "AZero" same

theorem contents_cons_congr {first second : Pattern} {rest rest' : List Pattern} (same : first = second)
    (restPerm : (bagContents "AZero" rest).Perm (bagContents "AZero" rest')) :
    (bagContents "AZero" (first :: rest)).Perm (bagContents "AZero" (second :: rest')) := by
  rw [bagContents_cons "AZero" first rest, bagContents_cons "AZero" second rest', same]
  exact restPerm.append_left _

/-! ## The padded form -/

/-- A bag stays a bag; anything else becomes the bag of itself. -/
def wrap : Pattern → Pattern
  | .collection .hashBag elements none => .collection .hashBag elements none
  | pattern => .collection .hashBag [pattern] none

mutual
/-- **The padded form**: every ambient's content a bag. -/
def pad : Pattern → Pattern
  | .apply "AAmb" [name, content] => .apply "AAmb" [name, wrap (pad content)]
  | .collection .hashBag elements none => .collection .hashBag (padList elements) none
  | pattern => pattern

/-- The padded forms of a list. -/
def padList : List Pattern → List Pattern
  | [] => []
  | pattern :: patterns => pad pattern :: padList patterns
end

theorem padList_eq_map (patterns : List Pattern) : padList patterns = patterns.map pad := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns recurse => simp [padList, recurse]

theorem pad_bag (elements : List Pattern) :
    pad (.collection .hashBag elements none) = .collection .hashBag (elements.map pad) none := by
  simp [pad, padList_eq_map]

theorem pad_ambient (name content : Pattern) : pad (amb name content) = amb name (wrap (pad content)) := by
  simp [pad, amb]

theorem wrap_of_not_bag {pattern : Pattern} (notBag : ¬ IsBagNode pattern) :
    wrap pattern = .collection .hashBag [pattern] none := by
  unfold wrap
  split
  · rename_i elements
    exact absurd ⟨elements, rfl⟩ notBag
  · rfl

theorem pad_of_not_bag_not_ambient {pattern : Pattern} (notBag : ¬ IsBagNode pattern)
    (notAmbient : ∀ name content, pattern ≠ amb name content) : pad pattern = pattern := by
  unfold pad
  split
  · rename_i name content
    exact absurd rfl (notAmbient name content)
  · rename_i elements
    exact absurd ⟨elements, rfl⟩ notBag
  · rfl

/-- Padding keeps a term a bag or not a bag. -/
theorem isBagNode_pad {pattern : Pattern} : IsBagNode (pad pattern) ↔ IsBagNode pattern := by
  constructor
  · rintro ⟨elements, same⟩
    unfold pad at same
    split at same
    · cases same
    · rename_i elements'
      exact ⟨elements', rfl⟩
    · exact ⟨elements, same⟩
  · rintro ⟨elements, rfl⟩
    exact ⟨_, pad_bag elements⟩

/-- **Wrapping keeps the normal form.** -/
theorem normalForm_wrap (pattern : Pattern) : nf (wrap pattern) = nf pattern := by
  by_cases bag : IsBagNode pattern
  · obtain ⟨elements, rfl⟩ := bag
    rfl
  · rw [wrap_of_not_bag bag, normalForm_bag]
    simp only [List.map_cons, List.map_nil]
    exact normalizeBag_single "AZero" (rootNormal_normalForm "AZero" pattern)

/-- **Padding keeps the normal form.** -/
theorem normalForm_pad (pattern : Pattern) : nf (pad pattern) = nf pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar => rfl
  | hfvar => rfl
  | happly label arguments recurse =>
    by_cases ambient : ∃ name content, Pattern.apply label arguments = amb name content
    · obtain ⟨name, content, same⟩ := ambient
      simp only [amb, Pattern.apply.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      rw [show Pattern.apply "AAmb" [name, content] = amb name content from rfl, pad_ambient]
      simp only [amb, normalForm_apply, List.map_cons, List.map_nil, normalForm_wrap,
        recurse content (by simp)]
    · rw [pad_of_not_bag_not_ambient (by rintro ⟨_, same⟩; cases same)
        (fun name content same => ambient ⟨name, content, same⟩)]
  | hlambda => rfl
  | hmultiLambda => rfl
  | hsubst => rfl
  | hcollection kind elements rest recurse =>
    by_cases bagNode : kind = .hashBag ∧ rest = none
    · obtain ⟨rfl, rfl⟩ := bagNode
      rw [pad_bag, normalForm_bag, normalForm_bag, List.map_map]
      congr 1
      exact List.map_congr_left fun element member => recurse element member
    · rw [pad_of_not_bag_not_ambient (by rintro ⟨_, same⟩; cases same; exact bagNode ⟨rfl, rfl⟩)
        (fun _ _ same => by cases same)]

/-- Wrapping the padded collapse of components gives the bag of their padded forms. -/
theorem wrap_pad_collapse {components : List Pattern} (nonempty : components ≠ [])
    (plain : ∀ component ∈ components, ¬ IsBagNode component) :
    wrap (pad (collapse "AZero" components)) = .collection .hashBag (components.map pad) none := by
  match components, nonempty with
  | [component], _ =>
    simp only [collapse, List.map_cons, List.map_nil]
    exact wrap_of_not_bag (fun bag => plain component (by simp) (isBagNode_pad.mp bag))
  | first :: second :: rest, _ =>
    simp only [collapse]
    rw [pad_bag]
    rfl

/-! ## Steps of a bag -/

/-- **Inaction has no step.** -/
theorem unit_stuck {target : Pattern} : ¬ AmbientRawStep (.apply "AZero" []) target := by
  intro step
  generalize sourceIs : Pattern.apply "AZero" [] = source at step
  cases step <;> first | cases sourceIs | simp [amb] at sourceIs

/-- **A step of a bag keeps a frame**: its result is a bag, and other components added to the source are
added to the result. -/
theorem frame {elements : List Pattern} {tail : Option String} {target : Pattern}
    (step : AmbientRawStep (.collection .hashBag elements tail) target) :
    ∃ components, target = .collection .hashBag components none ∧
      ∀ others, AmbientRawStep (.collection .hashBag (elements ++ others) none)
        (.collection .hashBag (components ++ others) none) := by
  generalize sourceIs : Pattern.collection .hashBag elements tail = source at step
  cases step with
  | @«open» elements' tail' i hi j hj name process content capability boundary =>
    cases sourceIs
    refine ⟨_, rfl, fun others => ?_⟩
    have hi' : i < (elements ++ others).length := by simp; omega
    have eraseFirst : (elements ++ others).eraseIdx i = elements.eraseIdx i ++ others :=
      List.eraseIdx_append_of_lt_length hi others
    have hj' : j < ((elements ++ others).eraseIdx i).length := by rw [eraseFirst]; simp; omega
    have eraseSecond : ((elements ++ others).eraseIdx i).eraseIdx j = (elements.eraseIdx i).eraseIdx j ++ others := by
      rw [eraseFirst, List.eraseIdx_append_of_lt_length hj others]
    have fired := AmbientRawStep.open (elements := elements ++ others) (tail := none) i hi' j hj' name process content
      ((List.getElem_append_left hi).trans capability)
      (((List.getElem_of_eq eraseFirst hj').trans (List.getElem_append_left hj)).trans boundary)
    rw [eraseSecond] at fired
    simpa using fired
  | @enter elements' tail' i hi j hj name target process host inner innerTail k hk mover capability destination =>
    cases sourceIs
    refine ⟨_, rfl, fun others => ?_⟩
    have hi' : i < (elements ++ others).length := by simp; omega
    have eraseFirst : (elements ++ others).eraseIdx i = elements.eraseIdx i ++ others :=
      List.eraseIdx_append_of_lt_length hi others
    have hj' : j < ((elements ++ others).eraseIdx i).length := by rw [eraseFirst]; simp; omega
    have eraseSecond : ((elements ++ others).eraseIdx i).eraseIdx j = (elements.eraseIdx i).eraseIdx j ++ others := by
      rw [eraseFirst, List.eraseIdx_append_of_lt_length hj others]
    have fired := AmbientRawStep.enter (elements := elements ++ others) (tail := none) i hi' j hj' name target
      process host k hk ((List.getElem_append_left hi).trans mover) capability
      (((List.getElem_of_eq eraseFirst hj').trans (List.getElem_append_left hj)).trans destination)
    rw [eraseSecond] at fired
    simpa using fired
  | exit => simp [amb] at sourceIs
  | @par elements' tail' i hi target inner =>
    cases sourceIs
    refine ⟨_, rfl, fun others => ?_⟩
    have hi' : i < (elements ++ others).length := by simp; omega
    have fired := AmbientRawStep.par (elements := elements ++ others) (tail := none) i hi'
      (by rw [List.getElem_append_left hi]; exact inner)
    rw [List.eraseIdx_append_of_lt_length hi others] at fired
    simpa using fired
  | ambient => simp [amb] at sourceIs

/-- **A step of a bag is a step of every reordering of it**, to a reordered result. -/
theorem reorder {elements other components : List Pattern} {tail : Option String}
    (step : AmbientRawStep (.collection .hashBag elements tail) (.collection .hashBag components none))
    (perm : elements.Perm other) :
    ∃ components', AmbientRawStep (.collection .hashBag other none) (.collection .hashBag components' none) ∧
      components'.Perm components := by
  generalize sourceIs : Pattern.collection .hashBag elements tail = source at step
  generalize targetIs : Pattern.collection .hashBag components none = target at step
  cases step with
  | @«open» elements' tail' i hi j hj name process content capability boundary =>
    cases sourceIs
    cases targetIs
    have selected := perm_two_selected elements i hi j hj
    rw [capability, boundary] at selected
    obtain ⟨i', hi', j', hj', atCapability, atBoundary, restPerm⟩ :=
      exists_two_indices_of_perm (selected.symm.trans perm).symm
    exact ⟨_, AmbientRawStep.open (tail := none) i' hi' j' hj' name process content atCapability atBoundary,
      (restPerm.cons _).cons _⟩
  | @enter elements' tail' i hi j hj name target process host inner innerTail k hk mover capability destination =>
    cases sourceIs
    cases targetIs
    have selected := perm_two_selected elements i hi j hj
    rw [mover, destination] at selected
    obtain ⟨i', hi', j', hj', atMover, atDestination, restPerm⟩ :=
      exists_two_indices_of_perm (selected.symm.trans perm).symm
    exact ⟨_, AmbientRawStep.enter (tail := none) i' hi' j' hj' name target process host k hk atMover capability
      atDestination, restPerm.cons _⟩
  | exit => simp [amb] at sourceIs
  | @par elements' tail' i hi target inner =>
    cases sourceIs
    cases targetIs
    obtain ⟨i', hi', atSelected, restPerm⟩ :=
      exists_index_of_perm ((perm_getElem_eraseIdx elements i hi).symm.trans perm).symm
    exact ⟨_, AmbientRawStep.par (tail := none) i' hi' (by rw [atSelected]; exact inner), restPerm.cons _⟩
  | ambient => simp [amb] at sourceIs

/-! ## Contents of normal forms -/

/-- The contents of normal forms are not bags. -/
theorem contents_plain_of_normal {elements : List Pattern} {component : Pattern}
    (member : component ∈ bagContents "AZero" (elements.map nf)) : ¬ IsBagNode component :=
  (bagContents_spec (fun element inside => by
    obtain ⟨original, -, rfl⟩ := List.mem_map.mp inside
    exact rootNormal_normalForm "AZero" original) member).2

/-- The normal form of a bag: the collapse of its sorted contents. -/
theorem normalForm_bag_collapse (elements : List Pattern) :
    nf (.collection .hashBag elements none) =
      collapse "AZero" (sortPatterns (bagContents "AZero" (elements.map nf))) := by
  rw [normalForm_bag]
  rfl

/-- **The padded content of an ambient whose content is a bag holding some component** is the bag of the padded
sorted contents. -/
theorem wrap_pad_normalForm_bag {elements : List Pattern} (nonempty : bagContents "AZero" (elements.map nf) ≠ []) :
    wrap (pad (nf (.collection .hashBag elements none))) =
      .collection .hashBag ((sortPatterns (bagContents "AZero" (elements.map nf))).map pad) none := by
  rw [normalForm_bag_collapse]
  refine wrap_pad_collapse ?_ fun component member => contents_plain_of_normal (mem_sortPatterns.mp member)
  intro empty
  exact nonempty (List.eq_nil_of_length_eq_zero (by simpa using congrArg List.length empty))

/-- The contents of a bag with one selected component. -/
theorem contents_of_one {elements : List Pattern} (i : ℕ) (hi : i < elements.length) {label : String}
    {arguments : List Pattern} (selected : elements[i] = .apply label arguments) (notUnit : label ≠ "AZero") :
    (bagContents "AZero" (elements.map nf)).Perm
      (.apply label (arguments.map nf) :: bagContents "AZero" ((elements.eraseIdx i).map nf)) := by
  have split := perm_getElem_eraseIdx elements i hi
  rw [selected] at split
  have mapped := bagContents_perm (split.map nf)
  simp only [List.map_cons] at mapped
  refine mapped.trans ?_
  rw [bagContents_cons, normalForm_apply, contents_apply notUnit]
  rfl

/-- The contents of a bag with two selected components. -/
theorem contents_of_two {elements : List Pattern} (i : ℕ) (hi : i < elements.length) (j : ℕ)
    (hj : j < (elements.eraseIdx i).length) {firstLabel secondLabel : String}
    {firstArguments secondArguments : List Pattern} (first : elements[i] = .apply firstLabel firstArguments)
    (second : (elements.eraseIdx i)[j] = .apply secondLabel secondArguments) (firstNotUnit : firstLabel ≠ "AZero")
    (secondNotUnit : secondLabel ≠ "AZero") :
    (bagContents "AZero" (elements.map nf)).Perm
      (.apply firstLabel (firstArguments.map nf) :: .apply secondLabel (secondArguments.map nf) ::
        bagContents "AZero" (((elements.eraseIdx i).eraseIdx j).map nf)) :=
  (contents_of_one i hi first firstNotUnit).trans ((contents_of_one j hj second secondNotUnit).cons _)

/-- Padded leftovers of sorted contents normalize to the contents of what they came from. -/
theorem contents_padded_rest {rest' rest : List Pattern}
    (perm : rest'.Perm ((bagContents "AZero" (rest.map nf)).map pad)) :
    (bagContents "AZero" (rest'.map nf)).Perm (bagContents "AZero" (rest.map nf)) := by
  refine (bagContents_perm (perm.map nf)).trans ?_
  rw [List.map_map, show (nf ∘ pad) = nf from funext normalForm_pad]
  exact contents_renormal rest

theorem pad_apply_plain {label : String} {arguments : List Pattern} (notAmbient : label ≠ "AAmb") :
    pad (.apply label arguments) = .apply label arguments :=
  pad_of_not_bag_not_ambient (by rintro ⟨_, same⟩; cases same)
    (fun _ _ same => by simp [amb] at same; exact notAmbient same.1)

theorem normalForm_amb (name content : Pattern) : nf (amb name content) = amb (nf name) (nf content) := by
  simp only [amb, normalForm_apply, List.map_cons, List.map_nil]

theorem pad_apply_ambient (name content : Pattern) :
    pad (.apply "AAmb" [name, content]) = amb name (wrap (pad content)) :=
  pad_ambient name content

theorem wrap_of_bag {pattern : Pattern} (bag : IsBagNode pattern) : wrap pattern = pattern := by
  obtain ⟨elements, rfl⟩ := bag
  rfl

theorem object_of_amb {name content : Pattern} (object : isObjectPattern (amb name content) = true) :
    isObjectPattern content = true := by
  simp only [amb, isObjectPattern, isObjectPatternList_iff] at object
  exact object content (by simp)

/-- The padded normal form of a bag with at least two contents: the bag of its padded sorted contents. -/
theorem pad_normalForm_bag_of_long {elements : List Pattern}
    (long : 2 ≤ (bagContents "AZero" (elements.map nf)).length) :
    pad (nf (.collection .hashBag elements none)) =
      .collection .hashBag ((sortPatterns (bagContents "AZero" (elements.map nf))).map pad) none := by
  rw [normalForm_bag_of_long long, pad_bag]

/-- **A capability in the content of an ambient is a component of its padded content**, and what remains pads the
contents of the rest. -/
theorem padded_capability {inner : List Pattern} (k : ℕ) (hk : k < inner.length) {label : String}
    {first second : Pattern} (capability : inner[k] = .apply label [first, second]) (notUnit : label ≠ "AZero")
    (notAmbient : label ≠ "AAmb") :
    ∃ (inner' : List Pattern) (k' : ℕ) (hk' : k' < inner'.length),
      wrap (pad (nf (.collection .hashBag inner none))) = .collection .hashBag inner' none ∧
      inner'[k'] = .apply label [nf first, nf second] ∧
      (inner'.eraseIdx k').Perm ((bagContents "AZero" ((inner.eraseIdx k).map nf)).map pad) := by
  have contents := contents_of_one k hk capability notUnit
  simp only [List.map_cons, List.map_nil] at contents
  have nonempty : bagContents "AZero" (inner.map nf) ≠ [] := by
    intro empty
    have lengths := contents.length_eq
    rw [empty] at lengths
    simp at lengths
  have mapped := ((sortPatterns_perm _).trans contents).map pad
  rw [List.map_cons, pad_apply_plain notAmbient] at mapped
  obtain ⟨k', hk', atCapability, restPerm⟩ := exists_index_of_perm mapped
  exact ⟨_, k', hk', wrap_pad_normalForm_bag nonempty, atCapability, restPerm⟩

/-! ## Simulation at the padded normal form -/

/-- **Every step of a closed term is matched by a step of its padded normal form**, to a term with the same normal
form. -/
theorem simulation {source target : Pattern} (step : AmbientRawStep source target) :
    isObjectPattern source = true → ∃ target', AmbientRawStep (pad (nf source)) target' ∧ nf target' = nf target := by
  induction step with
  | @«open» elements tail i hi j hj name process content capability boundary =>
    intro object
    obtain rfl := tail_none object
    have contents := contents_of_two i hi j hj capability boundary (by decide) (by decide)
    simp only [List.map_cons, List.map_nil] at contents
    have long : 2 ≤ (bagContents "AZero" (elements.map nf)).length := by
      rw [contents.length_eq]; simp
    rw [pad_normalForm_bag_of_long long]
    have mapped := ((sortPatterns_perm _).trans contents).map pad
    rw [List.map_cons, List.map_cons, pad_apply_plain (by decide), pad_apply_ambient] at mapped
    obtain ⟨i', hi', j', hj', atCapability, atBoundary, restPerm⟩ := exists_two_indices_of_perm mapped
    refine ⟨_, AmbientRawStep.open (tail := none) i' hi' j' hj' (nf name) (nf process) _ atCapability atBoundary, ?_⟩
    apply normalForm_bag_congr
    simp only [List.map_cons]
    exact contents_cons_congr (normalForm_idempotent "AZero" process)
      (contents_cons_congr (by rw [normalForm_wrap, normalForm_pad, normalForm_idempotent])
        (contents_padded_rest restPerm))
  | @enter elements tail i hi j hj name target process host inner innerTail k hk mover capability destination =>
    intro object
    obtain rfl := tail_none object
    have moverObject := element_object object (List.getElem_mem hi)
    rw [mover] at moverObject
    obtain rfl := tail_none (object_of_amb moverObject)
    have contents := contents_of_two i hi j hj mover destination (by decide) (by decide)
    simp only [List.map_cons, List.map_nil] at contents
    have long : 2 ≤ (bagContents "AZero" (elements.map nf)).length := by
      rw [contents.length_eq]; simp
    rw [pad_normalForm_bag_of_long long]
    obtain ⟨inner', k', hk', padded, atCapability, innerPerm⟩ :=
      padded_capability k hk capability (by decide) (by decide)
    have mapped := ((sortPatterns_perm _).trans contents).map pad
    rw [List.map_cons, List.map_cons, pad_apply_ambient, pad_apply_ambient, padded] at mapped
    obtain ⟨i', hi', j', hj', atMover, atDestination, restPerm⟩ := exists_two_indices_of_perm mapped
    refine ⟨_, AmbientRawStep.enter (tail := none) i' hi' j' hj' (nf name) (nf target) (nf process) _ k' hk'
      atMover atCapability atDestination, ?_⟩
    apply normalForm_bag_congr
    simp only [List.map_cons]
    refine contents_cons_congr ?_ (contents_padded_rest restPerm)
    simp only [normalForm_amb, normalForm_idempotent]
    congr 1
    apply normalForm_bag_congr
    simp only [List.map_cons, List.map_nil, normalForm_amb, normalForm_idempotent, normalForm_wrap, normalForm_pad]
    refine contents_cons_congr ?_ (List.Perm.refl _)
    congr 1
    apply normalForm_bag_congr
    simp only [List.map_cons]
    exact contents_cons_congr (normalForm_idempotent "AZero" process) (contents_padded_rest innerPerm)
  | @exit contents tail i hi name parent process inner innerTail k hk mover capability =>
    intro object
    have contentObject := object_of_amb object
    obtain rfl := tail_none contentObject
    have moverObject := element_object contentObject (List.getElem_mem hi)
    rw [mover] at moverObject
    obtain rfl := tail_none (object_of_amb moverObject)
    have outer := contents_of_one i hi mover (by decide)
    simp only [List.map_cons, List.map_nil] at outer
    have nonempty : bagContents "AZero" (contents.map nf) ≠ [] := by
      intro empty
      have lengths := outer.length_eq
      rw [empty] at lengths
      simp at lengths
    obtain ⟨inner', k', hk', padded, atCapability, innerPerm⟩ :=
      padded_capability k hk capability (by decide) (by decide)
    rw [normalForm_amb, pad_ambient, wrap_pad_normalForm_bag nonempty]
    have mapped := ((sortPatterns_perm _).trans outer).map pad
    rw [List.map_cons, pad_apply_ambient, padded] at mapped
    obtain ⟨i', hi', atMover, restPerm⟩ := exists_index_of_perm mapped
    refine ⟨_, AmbientRawStep.exit (tail := none) i' hi' (nf name) (nf parent) (nf process) k' hk' atMover
      atCapability, ?_⟩
    apply normalForm_bag_congr
    simp only [List.map_cons, List.map_nil, normalForm_amb, normalForm_idempotent]
    refine contents_cons_congr ?_ (contents_cons_congr ?_ (List.Perm.refl _))
    · congr 1
      apply normalForm_bag_congr
      simp only [List.map_cons]
      exact contents_cons_congr (normalForm_idempotent "AZero" process) (contents_padded_rest innerPerm)
    · congr 1
      exact normalForm_bag_congr (contents_padded_rest restPerm)
  | @par elements tail i hi target inner recurse =>
    intro object
    obtain rfl := tail_none object
    obtain ⟨target', fired, same⟩ := recurse (element_object object (List.getElem_mem hi))
    have split := perm_getElem_eraseIdx elements i hi
    have contents : (bagContents "AZero" (elements.map nf)).Perm
        (bagContents "AZero" [nf elements[i]] ++ bagContents "AZero" ((elements.eraseIdx i).map nf)) := by
      have mapped := bagContents_perm (split.map nf)
      simp only [List.map_cons] at mapped
      rwa [bagContents_cons] at mapped
    have wholeTarget : ∀ result : Pattern, nf result = nf target →
        nf (.collection .hashBag (target :: elements.eraseIdx i) none) =
          normalizeBag (some "AZero") (nf result :: (elements.eraseIdx i).map nf) := by
      intro result sameResult
      rw [normalForm_bag, List.map_cons, sameResult]
    have normal := rootNormal_normalForm "AZero" elements[i]
    by_cases bag : IsBagNode (nf elements[i])
    · obtain ⟨components, isBag⟩ := bag
      obtain ⟨-, componentsLong, plain⟩ := normal components isBag
      have spliced : bagContents "AZero" [nf elements[i]] = components := by
        rw [isBag]
        simp only [bagContents, List.flatMap_cons, List.flatMap_nil, List.append_nil, splice_bag]
        exact List.filter_eq_self.mpr fun component member => by simpa using (plain component member).1
      rw [spliced] at contents
      rw [isBag, pad_bag] at fired
      obtain ⟨results, rfl, framed⟩ := frame fired
      have long : 2 ≤ (bagContents "AZero" (elements.map nf)).length := by
        rw [contents.length_eq]; simp; omega
      rw [pad_normalForm_bag_of_long long]
      have padPerm : (components.map pad ++ (bagContents "AZero" ((elements.eraseIdx i).map nf)).map pad).Perm
          ((sortPatterns (bagContents "AZero" (elements.map nf))).map pad) := by
        rw [← List.map_append]
        exact (((sortPatterns_perm _).trans contents).map pad).symm
      obtain ⟨results', reordered, resultsPerm⟩ := reorder (framed _) padPerm
      refine ⟨_, reordered, ?_⟩
      rw [wholeTarget _ same, normalForm_bag]
      apply normalizeBag_contents_perm
      rw [bagContents_cons]
      refine (bagContents_perm (resultsPerm.map nf)).trans ?_
      rw [List.map_append, bagContents_append]
      refine List.Perm.append ?_ (contents_padded_rest (List.Perm.refl _))
      rw [normalForm_bag]
      exact (contents_normalizeBag "AZero" fun component member => by
        obtain ⟨original, -, rfl⟩ := List.mem_map.mp member
        exact rootNormal_normalForm "AZero" original).symm
    · by_cases unit : nf elements[i] = .apply "AZero" []
      · rw [unit, pad_apply_plain (by decide)] at fired
        exact absurd fired unit_stuck
      · rw [contents_plain unit bag] at contents
        by_cases lone : bagContents "AZero" ((elements.eraseIdx i).map nf) = []
        · rw [lone] at contents
          have alone : bagContents "AZero" (elements.map nf) = [nf elements[i]] := List.perm_singleton.mp contents
          have nfSource : nf (.collection .hashBag elements none) = nf elements[i] := by
            rw [normalForm_bag]
            simp only [normalizeBag, alone, sortPatterns_singleton, collapse]
          rw [nfSource]
          refine ⟨target', fired, ?_⟩
          rw [wholeTarget _ same]
          refine (normalizeBag_single "AZero" (rootNormal_normalForm "AZero" target')).symm.trans ?_
          apply normalizeBag_contents_perm
          rw [bagContents_cons "AZero" (nf target') ((elements.eraseIdx i).map nf), lone, List.append_nil]
        · have long : 2 ≤ (bagContents "AZero" (elements.map nf)).length := by
            rw [contents.length_eq]
            have := List.length_pos_of_ne_nil lone
            simp; omega
          rw [pad_normalForm_bag_of_long long]
          have mapped := ((sortPatterns_perm _).trans contents).map pad
          simp only [List.singleton_append, List.map_cons] at mapped
          obtain ⟨i', hi', atSelected, restPerm⟩ := exists_index_of_perm mapped
          refine ⟨_, AmbientRawStep.par (tail := none) i' hi' (by rw [atSelected]; exact fired), ?_⟩
          rw [wholeTarget _ same, normalForm_bag, List.map_cons]
          apply normalizeBag_contents_perm
          exact contents_cons_congr rfl (contents_padded_rest restPerm)
  | @ambient name content target inner recurse =>
    intro object
    obtain ⟨target', fired, same⟩ := recurse (object_of_amb object)
    rw [normalForm_amb, pad_ambient]
    by_cases bag : IsBagNode (nf content)
    · rw [wrap_of_bag (isBagNode_pad.mpr bag)]
      refine ⟨amb (nf name) target', AmbientRawStep.ambient (nf name) fired, ?_⟩
      rw [normalForm_amb, normalForm_amb, normalForm_idempotent, same]
    · rw [wrap_of_not_bag (fun padded => bag (isBagNode_pad.mp padded))]
      refine ⟨amb (nf name) (.collection .hashBag [target'] none),
        AmbientRawStep.ambient (nf name)
          (AmbientRawStep.par (elements := [pad (nf content)]) (tail := none) 0 (by simp) fired), ?_⟩
      rw [normalForm_amb, normalForm_amb, normalForm_idempotent, normalForm_bag, List.map_cons, List.map_nil,
        normalizeBag_single "AZero" (rootNormal_normalForm "AZero" target'), same]

/-! ## Steps keep closed processes closed processes -/

/-- The capabilities and the ambient take a name and a process. -/
theorem binary_params {rule : GrammarRule} (member : rule ∈ ambientCalc.terms)
    (binary : rule.label = "AIn" ∨ rule.label = "AOut" ∨ rule.label = "AOpen" ∨ rule.label = "AAmb") :
    rule.params = [.simple "n" (.base "Name"), .simple "p" (.base "Proc")] ∧ rule.category = "Proc" := by
  simp only [ambientCalc, Mettapedia.Languages.ProcessCalculi.Ambient.Mobile.terms, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at binary <;> exact ⟨rfl, rfl⟩

theorem binary_typed {free : FreeTypeContext} {bound : List TypeExpr} {label : String}
    (binary : label = "AIn" ∨ label = "AOut" ∨ label = "AOpen" ∨ label = "AAmb") {first second : Pattern}
    {type : TypeExpr} (typed : HasType ambientCalc free bound (.apply label [first, second]) type) :
    type = .base "Proc" ∧ HasType ambientCalc free bound first (.base "Name") ∧
      HasType ambientCalc free bound second (.base "Proc") := by
  obtain ⟨rule, member, rfl, -, rfl, arguments⟩ := hasType_apply_inversion typed
  obtain ⟨params, category⟩ := binary_params member binary
  rw [params] at arguments
  cases arguments with
  | cons _ firstType firstTyped rest =>
    cases rest with
    | cons _ secondType secondTyped _ =>
      simp only [parameterType?, Option.some.injEq] at firstType secondType
      subst firstType secondType
      exact ⟨by rw [category], firstTyped, secondTyped⟩

/-- A typed capability or ambient, rebuilt with a name and a process. -/
theorem binary_hasType {free : FreeTypeContext} {bound : List TypeExpr} {label : String}
    (binary : label = "AIn" ∨ label = "AOut" ∨ label = "AOpen" ∨ label = "AAmb") {first second first' second' : Pattern}
    {type : TypeExpr} (typed : HasType ambientCalc free bound (.apply label [first, second]) type)
    (firstTyped : HasType ambientCalc free bound first' (.base "Name"))
    (secondTyped : HasType ambientCalc free bound second' (.base "Proc")) :
    HasType ambientCalc free bound (.apply label [first', second']) type := by
  obtain ⟨rule, member, rfl, notBare, rfl, -⟩ := hasType_apply_inversion typed
  obtain ⟨params, -⟩ := binary_params member binary
  refine HasType.constructor member notBare ?_
  rw [params]
  exact .cons trivial rfl firstTyped (.cons trivial rfl secondTyped .nil)

/-- A bag typed at a sort is a process, of processes. -/
theorem bag_typed {free : FreeTypeContext} {bound : List TypeExpr} {elements : List Pattern} {tail : Option String}
    {sort : String} (typed : HasType ambientCalc free bound (.collection .hashBag elements tail) (.base sort)) :
    sort = "Proc" ∧ ∀ element ∈ elements, HasType ambientCalc free bound element (.base "Proc") := by
  obtain ⟨-, same, elementsTyped⟩ := bag_typing bareBagTheory typed rfl
  have category : parallel.category = "Proc" := rfl
  rw [category] at same elementsTyped
  cases same
  exact ⟨rfl, elementsHaveType_iff.mp elementsTyped⟩

theorem bag_proc {free : FreeTypeContext} {bound : List TypeExpr} {elements : List Pattern}
    (each : ∀ element ∈ elements, HasType ambientCalc free bound element (.base "Proc")) :
    HasType ambientCalc free bound (.collection .hashBag elements none) (.base "Proc") :=
  bag_hasType bareBagTheory (elementsHaveType_iff.mpr each)

/-- **A step keeps a process a process**, in every context. -/
theorem typed_of_raw {source target : Pattern} (step : AmbientRawStep source target) :
    ∀ {free : FreeTypeContext} {bound : List TypeExpr} {sort : String},
      HasType ambientCalc free bound source (.base sort) → HasType ambientCalc free bound target (.base sort) := by
  induction step with
  | @«open» elements tail i hi j hj name process content capability boundary =>
    intro free bound sort typed
    obtain ⟨rfl, each⟩ := bag_typed typed
    have capabilityTyped := capability ▸ each _ (List.getElem_mem hi)
    have boundaryTyped := boundary ▸ each _ (List.mem_of_mem_eraseIdx (List.getElem_mem hj))
    obtain ⟨-, -, processTyped⟩ := binary_typed (label := "AOpen") (by simp) capabilityTyped
    obtain ⟨-, -, contentTyped⟩ := binary_typed (label := "AAmb") (by simp) boundaryTyped
    refine bag_proc fun element member => ?_
    simp only [List.mem_cons] at member
    rcases member with rfl | rfl | inRest
    · exact processTyped
    · exact contentTyped
    · exact each element (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx inRest))
  | @enter elements tail i hi j hj name target process host inner innerTail k hk mover capability destination =>
    intro free bound sort typed
    obtain ⟨rfl, each⟩ := bag_typed typed
    have moverTyped := mover ▸ each _ (List.getElem_mem hi)
    have destinationTyped := destination ▸ each _ (List.mem_of_mem_eraseIdx (List.getElem_mem hj))
    obtain ⟨-, nameTyped, innerBagTyped⟩ := binary_typed (label := "AAmb") (by simp) moverTyped
    obtain ⟨-, eachInner⟩ := bag_typed innerBagTyped
    obtain ⟨-, targetTyped, hostTyped⟩ := binary_typed (label := "AAmb") (by simp) destinationTyped
    obtain ⟨-, -, processTyped⟩ :=
      binary_typed (label := "AIn") (by simp) (capability ▸ eachInner _ (List.getElem_mem hk))
    refine bag_proc fun element member => ?_
    rcases List.mem_cons.mp member with rfl | inRest
    · refine binary_hasType (label := "AAmb") (by simp) destinationTyped targetTyped (bag_proc fun element member => ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · refine binary_hasType (label := "AAmb") (by simp) moverTyped nameTyped (bag_proc fun element member => ?_)
        rcases List.mem_cons.mp member with rfl | inRest
        · exact processTyped
        · exact eachInner element (List.mem_of_mem_eraseIdx inRest)
      · exact hostTyped
    · exact each element (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx inRest))
  | @exit contents tail i hi name parent process inner innerTail k hk mover capability =>
    intro free bound sort typed
    obtain ⟨same, parentTyped, contentTyped⟩ := binary_typed (label := "AAmb") (by simp) typed
    cases same
    obtain ⟨-, each⟩ := bag_typed contentTyped
    have moverTyped := mover ▸ each _ (List.getElem_mem hi)
    obtain ⟨-, nameTyped, innerBagTyped⟩ := binary_typed (label := "AAmb") (by simp) moverTyped
    obtain ⟨-, eachInner⟩ := bag_typed innerBagTyped
    obtain ⟨-, -, processTyped⟩ :=
      binary_typed (label := "AOut") (by simp) (capability ▸ eachInner _ (List.getElem_mem hk))
    refine bag_proc fun element member => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · refine binary_hasType (label := "AAmb") (by simp) moverTyped nameTyped (bag_proc fun element member => ?_)
      rcases List.mem_cons.mp member with rfl | inRest
      · exact processTyped
      · exact eachInner element (List.mem_of_mem_eraseIdx inRest)
    · exact binary_hasType (label := "AAmb") (by simp) typed parentTyped
        (bag_proc fun element member => each element (List.mem_of_mem_eraseIdx member))
  | @par elements tail i hi target inner recurse =>
    intro free bound sort typed
    obtain ⟨rfl, each⟩ := bag_typed typed
    refine bag_proc fun element member => ?_
    rcases List.mem_cons.mp member with rfl | inRest
    · exact recurse (each _ (List.getElem_mem hi))
    · exact each element (List.mem_of_mem_eraseIdx inRest)
  | @ambient name content target inner recurse =>
    intro free bound sort typed
    obtain ⟨same, nameTyped, contentTyped⟩ := binary_typed (label := "AAmb") (by simp) typed
    cases same
    exact binary_hasType (label := "AAmb") (by simp) typed nameTyped (recurse contentTyped)

theorem object_binary {label : String} {first second : Pattern} :
    isObjectPattern (.apply label [first, second]) = true ↔
      isObjectPattern first = true ∧ isObjectPattern second = true := by
  simp [isObjectPattern, isObjectPatternList_iff]

theorem object_bag {elements : List Pattern} :
    isObjectPattern (.collection .hashBag elements none) = true ↔ ∀ element ∈ elements, isObjectPattern element = true := by
  simp [isObjectPattern, isObjectPatternList_iff]

/-- **A step keeps a term closed.** -/
theorem object_of_raw {source target : Pattern} (step : AmbientRawStep source target) :
    isObjectPattern source = true → isObjectPattern target = true := by
  induction step with
  | @«open» elements tail i hi j hj name process content capability boundary =>
    intro object
    have each : ∀ element ∈ elements, isObjectPattern element = true := fun _ member => element_object object member
    have capabilityObject := capability ▸ each _ (List.getElem_mem hi)
    have boundaryObject := boundary ▸ each _ (List.mem_of_mem_eraseIdx (List.getElem_mem hj))
    refine object_bag.mpr fun element member => ?_
    simp only [List.mem_cons] at member
    rcases member with rfl | rfl | inRest
    · exact (object_binary.mp capabilityObject).2
    · exact (object_binary (label := "AAmb")).mp boundaryObject |>.2
    · exact each element (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx inRest))
  | @enter elements tail i hi j hj name target process host inner innerTail k hk mover capability destination =>
    intro object
    have each : ∀ element ∈ elements, isObjectPattern element = true := fun _ member => element_object object member
    have moverObject := (object_binary (label := "AAmb")).mp (mover ▸ each _ (List.getElem_mem hi))
    have destinationObject := (object_binary (label := "AAmb")).mp
      (destination ▸ each _ (List.mem_of_mem_eraseIdx (List.getElem_mem hj)))
    have eachInner : ∀ element ∈ inner, isObjectPattern element = true :=
      fun _ member => element_object moverObject.2 member
    have processObject := (object_binary.mp (capability ▸ eachInner _ (List.getElem_mem hk))).2
    refine object_bag.mpr fun element member => ?_
    rcases List.mem_cons.mp member with rfl | inRest
    · refine (object_binary (label := "AAmb")).mpr ⟨destinationObject.1, object_bag.mpr fun element member => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · refine (object_binary (label := "AAmb")).mpr ⟨moverObject.1, object_bag.mpr fun element member => ?_⟩
        rcases List.mem_cons.mp member with rfl | inRest
        · exact processObject
        · exact eachInner element (List.mem_of_mem_eraseIdx inRest)
      · exact destinationObject.2
    · exact each element (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx inRest))
  | @exit contents tail i hi name parent process inner innerTail k hk mover capability =>
    intro object
    have outer := (object_binary (label := "AAmb")).mp object
    have each : ∀ element ∈ contents, isObjectPattern element = true :=
      fun _ member => element_object outer.2 member
    have moverObject := (object_binary (label := "AAmb")).mp (mover ▸ each _ (List.getElem_mem hi))
    have eachInner : ∀ element ∈ inner, isObjectPattern element = true :=
      fun _ member => element_object moverObject.2 member
    have processObject := (object_binary.mp (capability ▸ eachInner _ (List.getElem_mem hk))).2
    refine object_bag.mpr fun element member => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · refine (object_binary (label := "AAmb")).mpr ⟨moverObject.1, object_bag.mpr fun element member => ?_⟩
      rcases List.mem_cons.mp member with rfl | inRest
      · exact processObject
      · exact eachInner element (List.mem_of_mem_eraseIdx inRest)
    · exact (object_binary (label := "AAmb")).mpr
        ⟨outer.1, object_bag.mpr fun element member => each element (List.mem_of_mem_eraseIdx member)⟩
  | @par elements tail i hi target inner recurse =>
    intro object
    have each : ∀ element ∈ elements, isObjectPattern element = true := fun _ member => element_object object member
    refine object_bag.mpr fun element member => ?_
    rcases List.mem_cons.mp member with rfl | inRest
    · exact recurse (each _ (List.getElem_mem hi))
    · exact each element (List.mem_of_mem_eraseIdx inRest)
  | @ambient name content target inner recurse =>
    intro object
    have parts := (object_binary (label := "AAmb")).mp object
    exact (object_binary (label := "AAmb")).mpr ⟨parts.1, recurse parts.2⟩

/-- **A step keeps a closed process or name in the domain.** -/
theorem domain_of_raw {source target : Pattern} (step : AmbientRawStep source target) (admitted : domain source = true) :
    domain target = true := by
  obtain ⟨sort, -, admissible⟩ := AlgebraTyped.domain_iff.mp admitted
  exact AlgebraTyped.domain_of_typed sortsCover metadataOfTyped (typed_of_raw step admissible.typed)
    (object_of_raw step admissible.object)

/-- **Padding keeps the type.** -/
theorem pad_typed (pattern : Pattern) : ∀ {free : FreeTypeContext} {bound : List TypeExpr} {sort : String},
    HasType ambientCalc free bound pattern (.base sort) → HasType ambientCalc free bound (pad pattern) (.base sort) := by
  induction pattern using Pattern.inductionOn with
  | hbvar => intro _ _ _ typed; exact typed
  | hfvar => intro _ _ _ typed; exact typed
  | happly label arguments recurse =>
    intro free bound sort typed
    by_cases ambient : ∃ name content, Pattern.apply label arguments = amb name content
    · obtain ⟨name, content, same⟩ := ambient
      simp only [amb, Pattern.apply.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      rw [pad_apply_ambient]
      obtain ⟨sorted, nameTyped, contentTyped⟩ := binary_typed (label := "AAmb") (by simp) typed
      cases sorted
      refine binary_hasType (label := "AAmb") (by simp) typed nameTyped ?_
      have padded := recurse content (by simp) contentTyped
      by_cases bag : IsBagNode (pad content)
      · rw [wrap_of_bag bag]
        exact padded
      · rw [wrap_of_not_bag bag]
        exact bag_proc fun element member => by
          rw [List.mem_singleton.mp member]
          exact padded
    · rw [pad_of_not_bag_not_ambient (by rintro ⟨_, same⟩; cases same)
        (fun name content same => ambient ⟨name, content, same⟩)]
      exact typed
  | hlambda => intro _ _ _ typed; exact typed
  | hmultiLambda => intro _ _ _ typed; exact typed
  | hsubst => intro _ _ _ typed; exact typed
  | hcollection kind elements rest recurse =>
    intro free bound sort typed
    by_cases bagNode : kind = .hashBag ∧ rest = none
    · obtain ⟨rfl, rfl⟩ := bagNode
      rw [pad_bag]
      obtain ⟨rfl, each⟩ := bag_typed typed
      exact bag_proc fun element member => by
        obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
        exact recurse original inside (each original inside)
    · rw [pad_of_not_bag_not_ambient (by rintro ⟨_, same⟩; cases same; exact bagNode ⟨rfl, rfl⟩)
        (fun _ _ same => by cases same)]
      exact typed

/-- **Padding keeps a term closed.** -/
theorem pad_object (pattern : Pattern) : isObjectPattern pattern = true → isObjectPattern (pad pattern) = true := by
  induction pattern using Pattern.inductionOn with
  | hbvar => exact id
  | hfvar => exact id
  | happly label arguments recurse =>
    intro object
    by_cases ambient : ∃ name content, Pattern.apply label arguments = amb name content
    · obtain ⟨name, content, same⟩ := ambient
      simp only [amb, Pattern.apply.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      rw [pad_apply_ambient]
      have parts := object_binary.mp object
      refine (object_binary (label := "AAmb")).mpr ⟨parts.1, ?_⟩
      have padded := recurse content (by simp) parts.2
      by_cases bag : IsBagNode (pad content)
      · rw [wrap_of_bag bag]
        exact padded
      · rw [wrap_of_not_bag bag]
        exact object_bag.mpr fun element member => by
          rw [List.mem_singleton.mp member]
          exact padded
    · rw [pad_of_not_bag_not_ambient (by rintro ⟨_, same⟩; cases same)
        (fun name content same => ambient ⟨name, content, same⟩)]
      exact object
  | hlambda => exact id
  | hmultiLambda => exact id
  | hsubst => exact id
  | hcollection kind elements rest recurse =>
    intro object
    by_cases bagNode : kind = .hashBag ∧ rest = none
    · obtain ⟨rfl, rfl⟩ := bagNode
      rw [pad_bag]
      refine object_bag.mpr fun element member => ?_
      obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
      exact recurse original inside (object_bag.mp object original inside)
    · rw [pad_of_not_bag_not_ambient (by rintro ⟨_, same⟩; cases same; exact bagNode ⟨rfl, rfl⟩)
        (fun _ _ same => by cases same)]
      exact object

theorem pad_domain {term : Pattern} (admitted : domain term = true) : domain (pad term) = true := by
  obtain ⟨sort, -, admissible⟩ := AlgebraTyped.domain_iff.mp admitted
  exact AlgebraTyped.domain_of_typed sortsCover metadataOfTyped (pad_typed _ admissible.typed)
    (pad_object _ admissible.object)

/-! ## Coherence -/

open Mettapedia.OSLF.MeTTaIL.ReferenceStep (StepValid ReferenceProfile contextualStep_iff_step)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep (enough mem_stepsAt_of_enough)

/-- **The presentation at which a state's steps are listed**: its padded form. -/
def presentations (term : Pattern) : List Pattern := [pad term]

/-- The canonical form: the normal form on closed processes and names. -/
abbrev canon : Pattern → Pattern := AlgebraTyped.canon ambientCalc (some "AZero") sorts

theorem profile : ReferenceProfile ambientCalc := profile_of_aligned (by decide)

/-- The reference steps of ambients are the steps of their occurrence specification. -/
theorem reference_iff_raw {source target : Pattern} :
    (∃ witness, StepValid RelationEnv.empty ambientCalc source witness target) ↔ AmbientRawStep source target :=
  (contextualStep_iff_step RelationEnv.empty ambientCalc profile).symm.trans (step_iff_raw source target)

/-- **Coherence for plain steps**: a step from any term equivalent to a canonical one is matched, up to canonical
form, by a step listed at its padded form, wherever the fuel lists its steps. -/
theorem coherentPlain (fuel : ℕ) :
    CoherentPlain RelationEnv.empty ambientCalc fuel canon domain presentations AlgebraTyped.reading := by
  intro state redex witness contractum _ stateAdmitted canonState complete before _ valid
  have redexAdmitted := (canonical RelationEnv.empty).invariant stateAdmitted before
  have same : canon redex = state :=
    ((canonical RelationEnv.empty).same stateAdmitted before).symm.trans canonState
  have stateIs : state = nf redex := by
    rw [← same]
    show AlgebraTyped.canon ambientCalc (some "AZero") sorts redex = nf redex
    unfold AlgebraTyped.canon
    rw [if_pos redexAdmitted]
  obtain ⟨sort, -, admissible⟩ := AlgebraTyped.domain_iff.mp redexAdmitted
  have raw := reference_iff_raw.mp ⟨witness, valid⟩
  obtain ⟨contractum', raw', sameNormal⟩ := simulation raw admissible.object
  obtain ⟨witness', valid'⟩ := reference_iff_raw.mpr raw'
  have contractumAdmitted := domain_of_raw raw redexAdmitted
  have padAdmitted := pad_domain stateAdmitted
  have enoughPadded : enough RelationEnv.empty ambientCalc fuel (pad state) = true :=
    enoughAt_iff.mp complete (pad state) (List.mem_singleton_self _)
  subst stateIs
  have contractum'Admitted := domain_of_raw raw' padAdmitted
  refine ⟨(witness', contractum'), mem_listedAt.mpr ⟨pad (nf redex), List.mem_singleton_self _,
    mem_stepsAt_of_enough enoughPadded valid'⟩, ?_⟩
  show AlgebraTyped.canon ambientCalc (some "AZero") sorts contractum' =
    AlgebraTyped.canon ambientCalc (some "AZero") sorts contractum
  unfold AlgebraTyped.canon
  rw [if_pos contractum'Admitted, if_pos contractumAdmitted]
  exact sameNormal

/-! ## Computing -/

open Mettapedia.OSLF.NativeTypes.GeneratedLogic.ComputedNormalForm (fastNormalForm fastNormalForm_eq)

/-- The canonical form, computed. -/
def fastCanon (term : Pattern) : Pattern := if domain term then fastNormalForm "AZero" term else term

theorem fastCanon_eq : fastCanon = canon := by
  funext term
  unfold fastCanon canon AlgebraTyped.canon
  rw [fastNormalForm_eq]

/-- **The canonical forms of ambients, as the front door takes them**: in the typed reading, steps listed at the
padded form, coherent for plain steps. -/
def forms (fuel : ℕ) : CanonicalForms RelationEnv.empty ambientCalc fuel where
  reading := AlgebraTyped.reading
  canon := fastCanon
  domain := domain
  canonical := by rw [fastCanon_eq]; exact canonical RelationEnv.empty
  presentations := presentations
  labels := plainLabel
  coherent := by rw [fastCanon_eq]; exact CoherentPlain.on (coherentPlain fuel)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.AmbientForms

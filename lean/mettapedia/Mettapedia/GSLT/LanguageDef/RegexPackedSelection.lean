import Mettapedia.GSLT.Parsing.PackedForestSelection
import Mettapedia.GSLT.LanguageDef.RegexDependentProjection

/-!
# Early maximal-decimal selection and physical regex CSTs

The prepared syntax store remains immutable. A family policy rejects a numeric
reference whose scalar stop is followed by another Unicode decimal digit.
The policy does not consult capture declarations. For child-retaining CST and
transparent actions, recursive family selection is exactly the existing late
physical-CST policy. Arbitrary actions that discard semantic children require
their own coverage argument and are not silently included.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexPackedSelection

open Mettapedia.GSLT.Parsing.PackedForestSelection
open CettaWire (Term)
open RegexSourceProjection (cst cp decimalDigit?)
open RegexDependentProjection (Occurs EndsDecimalRun NumericReferencesMaximal)

def decimalEnd (input : List Nat) (stop : Nat) : Bool :=
  match input[stop]? with
  | none => true
  | some scalar => (decimalDigit? scalar).isNone

theorem decimalEnd_iff (input : List Nat) (stop : Nat) :
    decimalEnd input stop = true ↔ EndsDecimalRun input stop := by
  cases following : input[stop]? with
  | none => simp [decimalEnd, EndsDecimalRun, following]
  | some scalar =>
      cases digit : decimalDigit? scalar <;> simp [decimalEnd, EndsDecimalRun, following, digit]

theorem occurs_application_iff (wanted : Term) (head : String) (children : List Term) :
    Occurs wanted (.application head children) ↔
      wanted = .application head children ∨ ∃ child ∈ children, Occurs wanted child := by
  constructor
  · intro occurs
    cases occurs with
    | root => exact Or.inl rfl
    | child member nested => exact Or.inr ⟨_, member, nested⟩
  · rintro (rfl | ⟨child, member, nested⟩)
    · exact .root _
    · exact .child member nested

theorem maximal_cst_iff (input : List Nat) (label : String) (children : List Term) (start stop : Nat) :
    NumericReferencesMaximal input (cst label children start stop) ↔
      (label = "re-src:backref" → EndsDecimalRun input stop) ∧
        ∀ child ∈ children, NumericReferencesMaximal input child := by
  constructor
  · intro maximal
    constructor
    · intro reference
      subst label
      exact maximal start stop children (.root _)
    · intro child present first last nested contains
      exact maximal first last nested (.child (by simp [present]) contains)
  · rintro ⟨own, descendants⟩ first last nested contains
    rcases (occurs_application_iff _ _ _).mp contains with equal | ⟨child, present, occurs⟩
    · simp only [cst, Term.application.injEq, List.cons.injEq, Term.string.injEq,
        Term.natural.injEq] at equal
      obtain ⟨_, labelEqual, firstEqual, lastEqual, _⟩ := equal
      subst last
      exact own labelEqual.symm
    · simp only [List.mem_cons] at present
      rcases present with rfl | rfl | rfl | present
      · cases occurs
      · cases occurs
      · cases occurs
      · exact descendants child present first last nested occurs

theorem maximal_cp (input : List Nat) (scalar : Nat) : NumericReferencesMaximal input (cp scalar) := by
  intro first last children contains
  rcases (occurs_application_iff _ _ _).mp contains with equal | ⟨child, present, occurs⟩
  · simp [cst] at equal
  · simp only [List.mem_singleton] at present
    subst child
    cases occurs

def MaximalTerms (input : List Nat) (terms : List Term) : Prop :=
  ∀ term ∈ terms, NumericReferencesMaximal input term

@[simp] theorem maximalTerms_nil (input : List Nat) : MaximalTerms input [] := by
  simp [MaximalTerms]

@[simp] theorem maximalTerms_cons (input : List Nat) (first : Term) (rest : List Term) :
    MaximalTerms input (first :: rest) ↔ NumericReferencesMaximal input first ∧ MaximalTerms input rest := by
  simp [MaximalTerms]

@[simp] theorem maximalTerms_append (input : List Nat) (first second : List Term) :
    MaximalTerms input (first ++ second) ↔ MaximalTerms input first ∧ MaximalTerms input second := by
  constructor
  · intro maximal
    exact ⟨fun term member => maximal term (List.mem_append_left _ member),
      fun term member => maximal term (List.mem_append_right _ member)⟩
  · rintro ⟨left, right⟩ term member
    rcases List.mem_append.mp member with member | member
    · exact left term member
    · exact right term member

/-- These frames expose all semantic children. Terminal constants cannot
contain a reference, and transparent helper families retain their children
without inventing another source occurrence. -/
inductive Frame where
  | cst (label : String) (start stop : Nat)
  | scalar (value : Nat)
  | transparent
  deriving Repr, DecidableEq

def allow (input : List Nat) : Frame → Bool
  | .cst label _ stop => if label = "re-src:backref" then decimalEnd input stop else true
  | .scalar _ | .transparent => true

def renderFrame : Frame → List Term → List Term
  | .cst label start stop, children => [cst label children start stop]
  | .scalar scalar, children => cp scalar :: children
  | .transparent, children => children

theorem renderFrame_maximal_iff (input : List Nat) (frame : Frame) (children : List Term) :
    MaximalTerms input (renderFrame frame children) ↔ allow input frame = true ∧ MaximalTerms input children := by
  cases frame with
  | cst label start stop =>
      simp only [renderFrame, maximalTerms_cons, maximalTerms_nil, and_true, maximal_cst_iff,
        allow]
      change ((label = "re-src:backref" → EndsDecimalRun input stop) ∧ MaximalTerms input children) ↔ _
      by_cases reference : label = "re-src:backref" <;> simp [reference, decimalEnd_iff]
  | scalar scalar => simp [renderFrame, allow, maximal_cp]
  | transparent => simp [renderFrame, allow]

mutual
  def render {Family : Type} (frame : Family → Frame) : Derivation Family → List Term
    | .node family children => renderFrame (frame family) (renderChildren frame children)
  def renderChildren {Family : Type} (frame : Family → Frame) : List (Derivation Family) → List Term
    | [] => []
    | child :: rest => render frame child ++ renderChildren frame rest
end

mutual
  theorem render_maximal_iff {Family : Type} (input : List Nat) (frame : Family → Frame)
      (tree : Derivation Family) :
      MaximalTerms input (render frame tree) ↔ selected (allow input ∘ frame) tree = true := by
    cases tree with
    | node family children =>
        rw [render, renderFrame_maximal_iff, renderChildren_maximal_iff]
        simp [selected]
  theorem renderChildren_maximal_iff {Family : Type} (input : List Nat) (frame : Family → Frame)
      (children : List (Derivation Family)) :
      MaximalTerms input (renderChildren frame children) ↔ selectedChildren (allow input ∘ frame) children = true := by
    cases children with
    | nil => simp [renderChildren, selectedChildren]
    | cons first rest =>
        rw [renderChildren, maximalTerms_append, render_maximal_iff, renderChildren_maximal_iff]
        simp [selectedChildren]
end

theorem early_extract_iff_late_maximal {Key Family : Type}
    (families : Key → List Family) (children : Family → List Key) (frame : Family → Frame)
    (input : List Nat) (depth : Nat) (key : Key) (tree : Derivation Family) :
    tree ∈ extract families children (allow input ∘ frame) depth key ↔
      tree ∈ extract families children (fun _ => true) depth key ∧ MaximalTerms input (render frame tree) := by
  rw [extract_all_selected, List.mem_filter, render_maximal_iff]

/-- The selected ordered list, not only its result set, agrees with any
independent classifier of the declared late physical-CST observation. -/
theorem projected_list_exact {Key Family Output : Type}
    (families : Key → List Family) (children : Family → List Key) (frame : Family → Frame)
    (input : List Nat) (late : Derivation Family → Bool)
    (lateExact : ∀ tree, late tree = true ↔ MaximalTerms input (render frame tree))
    (project : Derivation Family → Option Output) (depth : Nat) (key : Key) :
    (extract families children (allow input ∘ frame) depth key).filterMap project =
      ((extract families children (fun _ => true) depth key).filter late).filterMap project := by
  rw [extract_all_selected]
  congr 1
  apply List.filter_congr
  intro tree present
  exact Bool.eq_iff_iff.mpr ((render_maximal_iff input frame tree).symm.trans (lateExact tree).symm)

open Mettapedia.GSLT.Parsing
open ClassAwarePackedForest (Family ProductionRef)
open ClassAwareNativeForestContract (ForestView IdentityTable FamilyDerivation)

def familyFrame (labels : ProductionRef → String) (family : Family) : Frame :=
  .cst (labels family.production) family.parent.start family.parent.stop

/-- Family labels are resolved through the retained production-identity
table, while spans come from the actual owning symbol node. -/
def nativeFrame? (view : ForestView) (table : IdentityTable)
    (labels : ProductionRef → String) (parent : Nat)
    (choice : ClassAwareNativeForestContract.Choice) : Option Frame := do
  let node ← view.nodes[parent]?
  let production ← table.productionRef? choice.productionIndex
  return .cst (labels production) node.scalarStart node.scalarStop

theorem native_family_policy_exact {view : ForestView} {table : IdentityTable}
    {profile : ParserProfileSemantics.ParserProfileLayer} {input : List Nat}
    {parent : Nat} {choice : ClassAwareNativeForestContract.Choice} {family : Family}
    (derived : FamilyDerivation view table profile input parent choice family)
    (labels : ProductionRef → String) :
    nativeFrame? view table labels parent choice = some (familyFrame labels family) := by
  cases derived with
  | symbol parentAt owned sortAt productionAt body =>
      simp [nativeFrame?, parentAt.1, productionAt, familyFrame]

namespace Controls

private def families : Nat → List Nat
  | 0 => [0]
  | 1 => [1, 2]
  | _ => []

private def children : Nat → List Nat
  | 0 => [1, 1, 1, 1]
  | _ => []

private def frames : Nat → Frame
  | 1 => .cst "re-src:backref" 0 2
  | 2 => .cst "re-src:backref" 0 3
  | _ => .cst "re-src:sequence" 0 3

theorem mixed_decimal_run_is_selected_before_its_products :
    (extract families children (allow [92,49,1634] ∘ frames) 2 0).length = 1 ∧
      (extract families children (fun _ => true) 2 0).length = 16 := by decide

theorem transparent_projection_retains_reference_policy :
    selected (allow [92,49,1634])
      (.node .transparent [.node (.cst "re-src:backref" 0 3) []]) = true ∧
      MaximalTerms [92,49,1634]
        (render id (.node .transparent [.node (.cst "re-src:backref" 0 3) []])) := by
  constructor
  · decide
  · exact (render_maximal_iff _ _ _).mpr (by decide)

theorem declared_prefix_cannot_license_shorter_numeric_family :
    allow [92,49,1634] (.cst "re-src:backref" 0 2) = false ∧
      RegexDependentProjection.reference? ⟨{},2,[(1,"x")]⟩ (.number 1) = some 1 := by decide

end Controls

end Mettapedia.GSLT.LanguageDef.RegexPackedSelection

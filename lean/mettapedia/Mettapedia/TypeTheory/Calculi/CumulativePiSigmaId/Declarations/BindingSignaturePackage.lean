import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.BindingSignatureInterpretation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveConstantInterpretation
import Mettapedia.OSLF.Syntax.SignatureMorphismReadback
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Nodup
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.BindingSignatureEmbedding
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.DeclarationSignature
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.UniverseProfiles

/-!
# Finite native declarations for an arbitrary binding signature

The source signature may have infinitely many sorts and constructors. Each
source term computes a finite declaration inventory containing its ambient
sorts and every result and binder sort used by its constructors. Literal
lookups in that inventory earn the existing formation-sensitive judgment.
The entries are opaque and introduce no declared root computation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.BindingSignaturePackage

open Mettapedia.OSLF
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Presentation.Declaration Presentation.FormationSensitive
open BindingSignatureEmbedding

variable {S : Binding.Signature}

abbrev Symbol (S : Binding.Signature) := S.Srt ⊕ (Sigma S.Op)

def declarationName (names : Names S) : Symbol S → DeclName
  | .inl sort => names.sort sort
  | .inr operator => names.operator operator.2

def declarationEntry (names : Names S) : Symbol S → Entry Tower.Head
  | .inl _ => ⟨.head (.sort Tower.zero), none⟩
  | .inr operator => ⟨operatorType names operator.2, none⟩

def declarationList (names : Names S) (inventory : List (Symbol S)) :
    List (DeclName × Entry Tower.Head) :=
  inventory.map (fun symbol => (declarationName names symbol, declarationEntry names symbol))

def signature (names : Names S) (inventory : List (Symbol S)) : Signature Tower.Head :=
  .ofList (declarationList names inventory)

def rules (names : Names S) (inventory : List (Symbol S)) : Rules Tower.Head :=
  extendRules Tower.rules (signature names inventory)

/-- Repeated identical symbols are permitted; a name cannot silently replace
a different source symbol. -/
theorem lookup (names : Names S) (unique : Function.Injective (declarationName names))
    (inventory : List (Symbol S)) {symbol : Symbol S} (present : symbol ∈ inventory) :
    (signature names inventory).entries (declarationName names symbol) =
      some (declarationEntry names symbol) := by
  induction inventory with
  | nil => cases present
  | cons first rest inductionHypothesis =>
      by_cases same : symbol = first
      · subst first
        simp [signature, declarationList, Signature.ofList, Signature.insert]
      · have different : declarationName names symbol ≠ declarationName names first :=
          fun equal => same (unique equal)
        have inRest : symbol ∈ rest := (List.mem_cons.mp present).resolve_left same
        simpa [signature, declarationList, Signature.ofList, Signature.insert, different]
          using inductionHypothesis inRest

theorem type_lookup (names : Names S) (unique : Function.Injective (declarationName names))
    (inventory : List (Symbol S)) {symbol : Symbol S} (present : symbol ∈ inventory) :
    (rules names inventory).constantType (declarationName names symbol) =
      some (declarationEntry names symbol).type := by
  change (signature names inventory).typeOf? _ = _
  rw [Signature.typeOf?, lookup names unique inventory present]
  rfl

/-- A name is unavailable when its original symbol is absent from the finite
inventory. This inspects the actual declaration lookup. -/
theorem missing_lookup (names : Names S)
    (unique : Function.Injective (declarationName names)) (inventory : List (Symbol S))
    {symbol : Symbol S} (absent : symbol ∉ inventory) :
    (rules names inventory).constantType (declarationName names symbol) = none := by
  change (signature names inventory).typeOf? _ = none
  cases selected : (signature names inventory).entries (declarationName names symbol) with
  | none => simp [Signature.typeOf?, selected]
  | some entry =>
      have membership := Signature.entries_ofList_mem (declarationList names inventory) selected
      obtain ⟨other, present, same⟩ := List.mem_map.mp membership
      have equal := unique (congrArg Prod.fst same)
      subst other
      exact False.elim (absent present)

theorem extends_append (names : Names S) (first second : List (Symbol S)) :
    (signature names first).Extends (signature names (first ++ second)) := by
  simpa only [signature, declarationList, List.map_append] using
    Signature.ofList_extends_append (declarationList names first) (declarationList names second)

def sortRealization (names : Names S) (unique : Function.Injective (declarationName names))
    (inventory : List (Symbol S)) :
    SupportedSortRealization names (rules names inventory)
      (fun sort => Sum.inl sort ∈ inventory) where
  typeUniverse := .sort Tower.zero
  above := .sort (.succ Tower.zero)
  joined := .sort (.max Tower.zero Tower.zero)
  universeTyped := .sort Tower.zero
  universeIs := .sort Tower.zero
  aboveIs := .sort (.succ Tower.zero)
  joinSelf := .sorts Tower.zero Tower.zero
  collapseSelf := by
    intro valuation
    simp [Mettapedia.TypeTheory.UniverseLevel.LevelExpr.eval, Tower.zero,
      LevelTower.zero]
  sortLookup := fun sort present => type_lookup names unique inventory present

/-- Closure checks the full result and argument telescope of every installed
constructor, rather than just the outer type of a displayed term. -/
def Closed (inventory : List (Symbol S)) : Prop :=
  ∀ (operator : Sigma S.Op), Sum.inr operator ∈ inventory →
    Sum.inl operator.1 ∈ inventory ∧
      ∀ sort ∈ aritySorts (S.arity operator.2), Sum.inl sort ∈ inventory

theorem Closed.append {first second : List (Symbol S)}
    (left : Closed first) (right : Closed second) : Closed (first ++ second) := by
  intro operator present
  rcases List.mem_append.mp present with member | member
  · have covered := left operator member
    exact ⟨List.mem_append_left _ covered.1,
      fun sort belongs => List.mem_append_left _ (covered.2 sort belongs)⟩
  · have covered := right operator member
    exact ⟨List.mem_append_right _ covered.1,
      fun sort belongs => List.mem_append_right _ (covered.2 sort belongs)⟩

@[simp] theorem value_lookup (names : Names S) (inventory : List (Symbol S))
    (name : DeclName) : (signature names inventory).valueOf? name = none := by
  cases selected : (signature names inventory).entries name with
  | none => simp [Signature.valueOf?, selected]
  | some entry =>
      have membership := Signature.entries_ofList_mem (declarationList names inventory) selected
      obtain ⟨symbol, _, same⟩ := List.mem_map.mp membership
      have entrySame : entry = declarationEntry names symbol := (congrArg Prod.snd same).symm
      cases symbol <;> simp [Signature.valueOf?, selected, entrySame, declarationEntry]

/-- Opaque declarations contribute neither delta unfolding nor a declared
source equation. Ordinary native beta computation remains available. -/
theorem rootFree (names : Names S) (inventory : List (Symbol S)) :
    ConstantSubstitution.RootFree (rules names inventory).computation := by
  intro n left right step
  cases step with
  | inherited impossible => exact impossible.elim
  | delta impossible =>
      rw [value_lookup] at impossible
      cases impossible
  | declared impossible =>
      rw [signature, Signature.computation_ofList] at impossible
      exact impossible.elim

@[simp] theorem computation_empty (names : Names S) (inventory : List (Symbol S)) :
    (rules names inventory).computation = RootComputation.empty :=
  ConstantSubstitution.RootFree.eq_empty (rootFree names inventory)

theorem wellFormed (names : Names S) (unique : Function.Injective (declarationName names))
    (inventory : List (Symbol S)) (closed : Closed inventory) :
    (signature names inventory).WellFormed Tower.rules where
  fresh := by intro name entry _selected; rfl
  types := by
    intro name type selected
    unfold Signature.typeOf? at selected
    cases entrySelected : (signature names inventory).entries name with
    | none => simp [entrySelected] at selected
    | some entry =>
        have typeSame : entry.type = type := by simpa [entrySelected] using selected
        have membership := Signature.entries_ofList_mem (declarationList names inventory) entrySelected
        obtain ⟨symbol, present, same⟩ := List.mem_map.mp membership
        have entrySame : entry = declarationEntry names symbol := (congrArg Prod.snd same).symm
        subst entry
        subst type
        cases symbol with
        | inl sort =>
            exact ⟨.sort (.succ Tower.zero), .sort _, .headType (.sort Tower.zero)⟩
        | inr operator =>
            have covered := closed operator present
            exact ⟨.sort Tower.zero, .sort _,
              ((sortRealization names unique inventory).operatorType_formed operator.2
                covered.1 covered.2).toRaw⟩
  values := by
    intro name type value _selected impossible
    rw [value_lookup] at impossible
    cases impossible
  noSelfDelta := by
    intro name value impossible
    rw [value_lookup] at impossible
    cases impossible
  declaredPreserves := by
    intro n gamma left right type impossible _typed
    rw [signature, Signature.computation_ofList] at impossible
    exact impossible.elim

mutual

def usedOperators : {gamma : Binding.Ctx S} → {sort : S.Srt} →
    Binding.Term S gamma sort → List (Sigma S.Op)
  | _, _, .var _ => []
  | _, sort, .op operator arguments => ⟨sort, operator⟩ :: usedArgumentOperators arguments

def usedArgumentOperators : {gamma : Binding.Ctx S} →
    {arguments : List (List S.Srt × S.Srt)} →
    Binding.Args S arguments gamma → List (Sigma S.Op)
  | _, _, .nil => []
  | _, _, .cons body rest => usedOperators body ++ usedArgumentOperators rest

end

mutual

theorem usedOperators_rename : ∀ {gamma delta : Binding.Ctx S} {sort : S.Srt}
    (action : Binding.Ren S gamma delta) (term : Binding.Term S gamma sort),
    usedOperators (Binding.rename action term) = usedOperators term
  | _, _, _, _, .var _ => rfl
  | _, _, _, action, .op operator arguments => by
      simp only [Binding.rename, usedOperators, usedArgumentOperators_rename action]

theorem usedArgumentOperators_rename :
    ∀ {gamma delta : Binding.Ctx S} {arguments : List (List S.Srt × S.Srt)}
      (action : Binding.Ren S gamma delta) (values : Binding.Args S arguments gamma),
      usedArgumentOperators (Binding.renameArgs action values) = usedArgumentOperators values
  | _, _, _, _, .nil => rfl
  | _, _, _, action, .cons body rest => by
      simp only [Binding.renameArgs, usedArgumentOperators, usedOperators_rename,
        usedArgumentOperators_rename action]

end

mutual

theorem used_operator_sorts :
    ∀ {gamma : Binding.Ctx S} {sort : S.Srt} (term : Binding.Term S gamma sort)
      (operator : Sigma S.Op), operator ∈ usedOperators term →
      operator.1 ∈ usedSorts term ∧
        ∀ s ∈ aritySorts (S.arity operator.2), s ∈ usedSorts term
  | _, _, .var _, _, impossible => False.elim (List.not_mem_nil impossible)
  | _, _, .op head arguments, operator, present => by
      rcases List.mem_cons.mp present with same | member
      · subst operator
        exact ⟨List.mem_cons_self, fun s belongs => List.mem_cons_of_mem _
          (aritySorts_subset_usedArgumentSorts arguments belongs)⟩
      · have covered := used_argument_operator_sorts arguments operator member
        exact ⟨List.mem_cons_of_mem _ covered.1,
          fun s belongs => List.mem_cons_of_mem _ (covered.2 s belongs)⟩

theorem used_argument_operator_sorts :
    ∀ {gamma : Binding.Ctx S} {arguments : List (List S.Srt × S.Srt)}
      (values : Binding.Args S arguments gamma) (operator : Sigma S.Op),
      operator ∈ usedArgumentOperators values →
      operator.1 ∈ usedArgumentSorts values ∧
        ∀ s ∈ aritySorts (S.arity operator.2), s ∈ usedArgumentSorts values
  | _, _, .nil, _, impossible => False.elim (List.not_mem_nil impossible)
  | _, _, .cons (bs := bound) (s := result) body rest, operator, present => by
      rcases List.mem_append.mp present with inBody | inRest
      · have covered := used_operator_sorts body operator inBody
        exact ⟨List.mem_append_right _ (List.mem_cons_of_mem _
            (List.mem_append_left _ covered.1)), fun s belongs =>
          List.mem_append_right _ (List.mem_cons_of_mem _
            (List.mem_append_left _ (covered.2 s belongs)))⟩
      · have covered := used_argument_operator_sorts rest operator inRest
        exact ⟨List.mem_append_right _ (List.mem_cons_of_mem _
            (List.mem_append_right _ covered.1)), fun s belongs =>
          List.mem_append_right _ (List.mem_cons_of_mem _
            (List.mem_append_right _ (covered.2 s belongs)))⟩

end

/-- Every ambient entry is retained, even when the submitted term does not
use its variable. There is no finiteness assumption on the whole signature. -/
def inventory {gamma : Binding.Ctx S} {sort : S.Srt} (term : Binding.Term S gamma sort) :
    List (Symbol S) :=
  (gamma ++ usedSorts term).map Sum.inl ++ (usedOperators term).map Sum.inr

theorem inventory_closed {gamma : Binding.Ctx S} {sort : S.Srt}
    (term : Binding.Term S gamma sort) : Closed (inventory term) := by
  intro operator present
  have member : operator ∈ usedOperators term := by
    simpa [inventory] using present
  have covered := used_operator_sorts term operator member
  constructor
  · exact List.mem_append_left _ (List.mem_map.mpr
      ⟨operator.1, List.mem_append_right _ covered.1, rfl⟩)
  · intro s belongs
    exact List.mem_append_left _ (List.mem_map.mpr
      ⟨s, List.mem_append_right _ (covered.2 s belongs), rfl⟩)

mutual

theorem installed (names : Names S) (unique : Function.Injective (declarationName names))
    (inventory : List (Symbol S)) :
    ∀ {gamma : Binding.Ctx S} {sort : S.Srt} (term : Binding.Term S gamma sort),
      (∀ operator ∈ usedOperators term, Sum.inr operator ∈ inventory) →
      Installed names (rules names inventory) term
  | _, _, .var position, _present => .var position
  | _, sort, .op operator arguments, present =>
      .op operator arguments
        (type_lookup names unique inventory (present ⟨sort, operator⟩ List.mem_cons_self))
        (installedArgs names unique inventory arguments (fun op member =>
          present op (List.mem_cons_of_mem _ member)))

theorem installedArgs (names : Names S) (unique : Function.Injective (declarationName names))
    (inventory : List (Symbol S)) :
    ∀ {gamma : Binding.Ctx S} {arguments : List (List S.Srt × S.Srt)}
      (values : Binding.Args S arguments gamma),
      (∀ operator ∈ usedArgumentOperators values, Sum.inr operator ∈ inventory) →
      InstalledArgs names (rules names inventory) values
  | _, _, .nil, _present => .nil
  | _, _, .cons body rest, present =>
      .cons (installed names unique inventory body (fun op member =>
        present op (List.mem_append_left _ member)))
        (installedArgs names unique inventory rest (fun op member =>
          present op (List.mem_append_right _ member)))

end

/-- Any declaration inventory containing the primitive sort and constructor
requirements supports the same source term and ambient context. -/
theorem supported_judgment (names : Names S)
    (unique : Function.Injective (declarationName names)) (selected : List (Symbol S))
    {gamma : Binding.Ctx S} {sort : S.Srt} (term : Binding.Term S gamma sort)
    (operators : ∀ operator ∈ usedOperators term, Sum.inr operator ∈ selected)
    (sorts : ∀ s ∈ gamma ++ usedSorts term, Sum.inl s ∈ selected) :
    Judgment (rules names selected) (context names gamma)
      (encode names term) (sortType names sort) :=
  (sortRealization names unique selected).encode_judgment term
    (installed names unique selected term operators)
    (fun s member => sorts s (List.mem_append_left _ member))
    (fun s member => sorts s (List.mem_append_right _ member))

theorem source_judgment (names : Names S)
    (unique : Function.Injective (declarationName names))
    {gamma : Binding.Ctx S} {sort : S.Srt} (term : Binding.Term S gamma sort) :
    Judgment (rules names (inventory term)) (context names gamma)
      (encode names term) (sortType names sort) :=
  supported_judgment names unique (inventory term) term
    (fun operator member => List.mem_append_right _ (List.mem_map.mpr ⟨operator, member, rfl⟩))
    (fun s member => List.mem_append_left _ (List.mem_map.mpr ⟨s, member, rfl⟩))

@[simp] theorem inventory_length {gamma : Binding.Ctx S} {sort : S.Srt}
    (term : Binding.Term S gamma sort) :
    (inventory term).length = gamma.length + (usedSorts term).length + (usedOperators term).length := by
  simp only [inventory, List.length_append, List.length_map]

theorem source_wellFormed (names : Names S)
    (unique : Function.Injective (declarationName names))
    {gamma : Binding.Ctx S} {sort : S.Srt} (term : Binding.Term S gamma sort) :
    (signature names (inventory term)).WellFormed Tower.rules :=
  wellFormed names unique (inventory term) (inventory_closed term)

#print axioms missing_lookup
#print axioms Closed.append
#print axioms supported_judgment
#print axioms extends_append
#print axioms rootFree
#print axioms computation_empty
#print axioms wellFormed
#print axioms used_operator_sorts
#print axioms inventory_closed
#print axioms source_judgment
#print axioms source_wellFormed

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.BindingSignaturePackage


set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.BindingSignaturePackage
open Mettapedia.OSLF
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation BindingSignatureEmbedding
variable {S : Binding.Signature} {M : List (Binding.MetaArity S)}

/-- The source primitive package retains every sort and ordinary constructor.
Metavariable function declarations belong to their separate native telescope. -/
def primitiveSymbol? : Symbol (Binding.withMetas S M) → Option (Symbol S)
  | .inl sort => some (.inl sort)
  | .inr ⟨_, .inl operator⟩ => some (.inr ⟨_, operator⟩)
  | .inr ⟨_, .inr _⟩ => none

def primitiveInventory {source : Binding.Ctx S} {sort : S.Srt}
    (term : Binding.Term (Binding.withMetas S M) source sort) : List (Symbol S) :=
  (inventory term).filterMap primitiveSymbol?

theorem primitiveInventory_sort {source : Binding.Ctx S} {sort : S.Srt}
    (term : Binding.Term (Binding.withMetas S M) source sort) (selected : S.Srt) :
    Sum.inl selected ∈ primitiveInventory term ↔ Sum.inl selected ∈ inventory term := by
  constructor
  · intro present
    obtain ⟨symbol, member, read⟩ := List.mem_filterMap.mp present
    cases symbol with
    | inl original =>
        have same : original = selected := Sum.inl.inj (Option.some.inj read)
        subst original
        exact member
    | inr operation =>
        rcases operation with ⟨result, operator⟩
        cases operator <;> simp only [primitiveSymbol?, Option.some.injEq, reduceCtorEq] at read
  · intro present
    exact List.mem_filterMap.mpr ⟨.inl selected, present, rfl⟩

theorem primitiveInventory_operator {source : Binding.Ctx S} {sort result : S.Srt}
    (term : Binding.Term (Binding.withMetas S M) source sort) (operator : S.Op result)
    (present : Sum.inr ⟨result, Sum.inl operator⟩ ∈ inventory term) :
    Sum.inr ⟨result, operator⟩ ∈ primitiveInventory term :=
  List.mem_filterMap.mpr ⟨.inr ⟨result, .inl operator⟩, present, rfl⟩

/-- Filtering removes function declarations without removing any of their
argument/result sorts. Every ordinary operator retains its full arity. -/
theorem primitiveInventory_closed {source : Binding.Ctx S} {sort : S.Srt}
    (term : Binding.Term (Binding.withMetas S M) source sort) : Closed (primitiveInventory term) := by
  intro operation present
  obtain ⟨symbol, member, read⟩ := List.mem_filterMap.mp present
  cases symbol with
  | inl original => simp only [primitiveSymbol?, Option.some.injEq, reduceCtorEq] at read
  | inr original =>
      rcases original with ⟨result, operator⟩
      cases operator with
      | inr metavariable => simp only [primitiveSymbol?, reduceCtorEq] at read
      | inl sourceOp =>
          have same : (⟨result, sourceOp⟩ : Sigma S.Op) = operation := Sum.inr.inj (Option.some.inj read)
          subst operation
          have closed := inventory_closed term ⟨result, .inl sourceOp⟩ member
          refine ⟨(primitiveInventory_sort term result).mpr closed.1, ?_⟩
          intro selected occurs
          apply (primitiveInventory_sort term selected).mpr
          apply closed.2 selected
          simpa only [Binding.withMetas, BindingSignatureEmbedding.Schema.aritySorts_withMetas] using occurs

mutual
  theorem allOperators_used : ∀ {source : Binding.Ctx S} {sort : S.Srt}
      (term : Binding.Term S source sort),
      term.AllOperators (fun {result} operator => (⟨result, operator⟩ : Sigma S.Op) ∈ usedOperators term)
    | _, _, .var position => .var position
    | _, _, .op operator arguments => .op operator arguments List.mem_cons_self
        ((allArgumentOperators_used arguments).mono (fun _ member => List.mem_cons_of_mem _ member))
  termination_by _ _ term => 2 * Binding.termSize term
  decreasing_by all_goals simp only [Binding.termSize]; omega

  theorem allArgumentOperators_used : ∀ {source : Binding.Ctx S} {arity : List (List S.Srt × S.Srt)}
      (arguments : Binding.Args S arity source),
      arguments.AllOperators (fun {result} operator => (⟨result, operator⟩ : Sigma S.Op) ∈ usedArgumentOperators arguments)
    | _, _, .nil => .nil
    | _, _, .cons body rest => .cons body rest
        ((allOperators_used body).mono (fun _ member => List.mem_append_left _ member))
        ((allArgumentOperators_used rest).mono (fun _ member => List.mem_append_right _ member))
  termination_by _ _ arguments => 2 * Binding.argsSize arguments + 1
  decreasing_by
    all_goals simp only [Binding.argsSize]
    all_goals first | omega | have positive := Binding.termSize_pos body; omega
end

/-- Every use keeps the original ordinal; this list preserves repeated
occurrences and does not replace the source occurrence journal by a set. -/
def metaPosition? : (Sigma (Binding.withMetas S M).Op) → Option (Fin M.length)
  | ⟨_, .inl _⟩ => none
  | ⟨_, .inr (.mk index)⟩ => some index

def usedMetavariables {source : Binding.Ctx S} {sort : S.Srt}
    (term : Binding.Term (Binding.withMetas S M) source sort) : List (Fin M.length) :=
  (usedOperators term).filterMap metaPosition?

theorem usedMetavariables_occurrence {source : Binding.Ctx S} {sort : S.Srt}
    (term : Binding.Term (Binding.withMetas S M) source sort) (index : Fin M.length)
    (present : (⟨(M.get index).2, Sum.inr (.mk index)⟩ : Sigma (Binding.withMetas S M).Op) ∈ usedOperators term) :
    index ∈ usedMetavariables term :=
  List.mem_filterMap.mpr ⟨_, present, rfl⟩

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.BindingSignaturePackage


set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.BindingSignaturePackage
open Mettapedia.OSLF
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Declaration BindingSignatureEmbedding TelescopeAbstraction FormationSensitive
variable {S : Binding.Signature} {M : List (Binding.MetaArity S)}

namespace SchemaTemplates

/-- Metadata sorts remain admitted even when their functions are not used. -/
def metadataSorts (metas : List (Binding.MetaArity S)) : List S.Srt :=
  metas.flatMap fun entry => entry.2 :: entry.1

def inventory {source : Binding.Ctx S} {sort : S.Srt}
    (term : Binding.Term (Binding.withMetas S M) source sort) : List (Symbol S) :=
  (metadataSorts M).map Sum.inl ++ primitiveInventory term

def selected {source : Binding.Ctx S} {sort : S.Srt}
    (term : Binding.Term (Binding.withMetas S M) source sort) : List (Fin M.length) :=
  (usedMetavariables term).dedup

theorem selected_nodup {source : Binding.Ctx S} {sort : S.Srt}
    (term : Binding.Term (Binding.withMetas S M) source sort) : (selected term).Nodup :=
  List.nodup_dedup _

theorem selected_mem {source : Binding.Ctx S} {sort : S.Srt}
    (term : Binding.Term (Binding.withMetas S M) source sort) (index : Fin M.length) :
    index ∈ selected term ↔ index ∈ usedMetavariables term := List.mem_dedup

def sourceIndex {source : Binding.Ctx S} {sort : S.Srt}
    (term : Binding.Term (Binding.withMetas S M) source sort)
    (index : Fin (selected term).length) : Fin M.length := (selected term).get index

theorem sourceIndex_injective {source : Binding.Ctx S} {sort : S.Srt}
    (term : Binding.Term (Binding.withMetas S M) source sort) :
    Function.Injective (sourceIndex term) := (selected_nodup term).injective_get

def functionType (names : Names S) (index : Fin M.length) : Tm Tower.Head 0 :=
  closeType (context names ((M.get index).1 ++ [])) (sortType names (M.get index).2)

def functionNames {source : Binding.Ctx S} {sort : S.Srt}
    (namespaceTag : DeclName) (term : Binding.Term (Binding.withMetas S M) source sort)
    (index : Fin (selected term).length) : DeclName :=
  FiniteParameters.indexedName namespaceTag (sourceIndex term index)

def functionTypes {source : Binding.Ctx S} {sort : S.Srt}
    (names : Names S) (term : Binding.Term (Binding.withMetas S M) source sort)
    (index : Fin (selected term).length) : Tm Tower.Head 0 := functionType names (sourceIndex term index)

def signature {source : Binding.Ctx S} {sort : S.Srt}
    (names : Names S) (namespaceTag : DeclName)
    (term : Binding.Term (Binding.withMetas S M) source sort) : Signature Tower.Head :=
  FiniteParameters.signature (declarationList names (inventory term))
    (functionNames namespaceTag term) (functionTypes names term)

def rules {source : Binding.Ctx S} {sort : S.Srt}
    (names : Names S) (namespaceTag : DeclName)
    (term : Binding.Term (Binding.withMetas S M) source sort) : Rules Tower.Head :=
  extendRules Tower.rules (signature names namespaceTag term)

def programs (namespaceTag : DeclName) (index : Fin M.length) : Tm Tower.Head 0 :=
  .const (FiniteParameters.indexedName namespaceTag index)

variable {source : Binding.Ctx S} {sort : S.Srt}

/-- The finite selector uses original source ordinals. -/
theorem functionNames_injective (namespaceTag : DeclName)
    (term : Binding.Term (Binding.withMetas S M) source sort) :
    Function.Injective (functionNames namespaceTag term) :=
  (FiniteParameters.indexedName_injective namespaceTag).comp (sourceIndex_injective term)

theorem primitive_kept (names : Names S) (namespaceTag : DeclName)
    (term : Binding.Term (Binding.withMetas S M) source sort)
    (fresh : ∀ symbol : Symbol S,
      FiniteParameters.indexedPositions namespaceTag M.length (declarationName names symbol) = none)
    (symbol : Symbol S) :
    (signature names namespaceTag term).entries (declarationName names symbol) =
      (BindingSignaturePackage.signature names (inventory term)).entries (declarationName names symbol) :=
  FiniteParameters.kept _ _ _ _ (sourceIndex term)
    (fun index => FiniteParameters.indexedPositions_name namespaceTag (sourceIndex term index))
    (declarationName names symbol) (fresh symbol)


theorem metadataSorts_result (index : Fin M.length) :
    (M.get index).2 ∈ metadataSorts M :=
  List.mem_flatMap.mpr ⟨M.get index, List.get_mem M index, List.mem_cons_self⟩

theorem metadataSorts_dependency (index : Fin M.length) (selectedSort : S.Srt)
    (present : selectedSort ∈ (M.get index).1) : selectedSort ∈ metadataSorts M :=
  List.mem_flatMap.mpr ⟨M.get index, List.get_mem M index, List.mem_cons_of_mem _ present⟩

theorem metadata_sort_present (term : Binding.Term (Binding.withMetas S M) source sort)
    (selectedSort : S.Srt) (present : selectedSort ∈ metadataSorts M) :
    Sum.inl selectedSort ∈ inventory term :=
  List.mem_append_left _ (List.mem_map.mpr ⟨selectedSort, present, rfl⟩)

theorem context_sort_present (term : Binding.Term (Binding.withMetas S M) source sort)
    (selectedSort : S.Srt) (present : selectedSort ∈ source) :
    Sum.inl selectedSort ∈ inventory term := by
  apply List.mem_append_right _
  apply (primitiveInventory_sort term selectedSort).mpr
  exact List.mem_append_left _ (List.mem_map.mpr
    ⟨selectedSort, List.mem_append_left _ present, rfl⟩)

theorem used_sort_present (term : Binding.Term (Binding.withMetas S M) source sort)
    (selectedSort : S.Srt) (present : selectedSort ∈ usedSorts term) :
    Sum.inl selectedSort ∈ inventory term := by
  apply List.mem_append_right _
  apply (primitiveInventory_sort term selectedSort).mpr
  exact List.mem_append_left _ (List.mem_map.mpr
    ⟨selectedSort, List.mem_append_right _ present, rfl⟩)

theorem inventory_closed (term : Binding.Term (Binding.withMetas S M) source sort) :
    Closed (inventory term) := by
  intro operator member
  rcases List.mem_append.mp member with impossible | present
  · obtain ⟨selectedSort, _, same⟩ := List.mem_map.mp impossible
    cases same
  · have covered := primitiveInventory_closed term operator present
    exact ⟨List.mem_append_right _ covered.1,
      fun selectedSort belongs => List.mem_append_right _ (covered.2 selectedSort belongs)⟩

def sortRealization (names : Names S) (unique : Function.Injective (declarationName names))
    (namespaceTag : DeclName) (term : Binding.Term (Binding.withMetas S M) source sort)
    (fresh : ∀ symbol : Symbol S,
      FiniteParameters.indexedPositions namespaceTag M.length (declarationName names symbol) = none) :
    SupportedSortRealization names (rules names namespaceTag term)
      (fun selectedSort => Sum.inl selectedSort ∈ inventory term) where
  typeUniverse := .sort Tower.zero
  above := .sort (.succ Tower.zero)
  joined := .sort (.max Tower.zero Tower.zero)
  universeTyped := .sort Tower.zero
  universeIs := .sort Tower.zero
  aboveIs := .sort (.succ Tower.zero)
  joinSelf := .sorts Tower.zero Tower.zero
  collapseSelf := by
    intro valuation
    simp [Mettapedia.TypeTheory.UniverseLevel.LevelExpr.eval, Tower.zero, LevelTower.zero]
  sortLookup := by
    intro selectedSort present
    change (signature names namespaceTag term).typeOf? _ = _
    change Option.map Entry.type ((signature names namespaceTag term).entries (declarationName names (.inl selectedSort))) = _
    rw [primitive_kept names namespaceTag term fresh,
      lookup names unique (inventory term) present]
    rfl

theorem functionType_eq (names : Names S) (index : Fin M.length) :
    functionType names index = bindingType names (M.get index).1 (M.get index).2 := by
  have closed := ClosedOperators.closeType_spine (ClosedOperators.namedTypes (Head := Tower.Head) names)
    ((M.get index).1 ++ []) (sortType names (M.get index).2)
  rw [ClosedOperators.typeContext_named, ClosedOperators.spineType_named] at closed
  simpa only [List.append_nil, functionType, bindingType, sortType, liftClosed, rename] using closed

theorem functionType_formed (names : Names S) (unique : Function.Injective (declarationName names))
    (namespaceTag : DeclName) (term : Binding.Term (Binding.withMetas S M) source sort)
    (fresh : ∀ symbol : Symbol S,
      FiniteParameters.indexedPositions namespaceTag M.length (declarationName names symbol) = none)
    (index : Fin M.length) :
    Typing (rules names namespaceTag term) .nil (functionType names index) (.head (.sort Tower.zero)) := by
  rw [functionType_eq]
  exact (sortRealization names unique namespaceTag term fresh).bindingType_formed _
    (fun selectedSort present => metadata_sort_present term selectedSort
      (metadataSorts_dependency index selectedSort present)) _
    (metadata_sort_present term _ (metadataSorts_result index))

theorem function_lookup (names : Names S) (namespaceTag : DeclName)
    (term : Binding.Term (Binding.withMetas S M) source sort) (index : Fin M.length)
    (present : index ∈ selected term) :
    (rules names namespaceTag term).constantType (FiniteParameters.indexedName namespaceTag index) =
      some (functionType names index) := by
  obtain ⟨position, same⟩ := List.mem_iff_get.mp present
  have found := FiniteParameters.lookup (declarationList names (inventory term))
    (functionNames namespaceTag term) (functionTypes names term)
    (functionNames_injective namespaceTag term) position
  change (signature names namespaceTag term).typeOf? _ = _
  unfold Signature.typeOf?
  change (signature names namespaceTag term).entries (functionNames namespaceTag term position) =
    some (FiniteParameters.entry (functionTypes names term) position) at found
  change (selected term).get position = index at same
  change sourceIndex term position = index at same
  rw [← same]
  rw [show FiniteParameters.indexedName namespaceTag (sourceIndex term position) =
    functionNames namespaceTag term position from rfl, found]
  rfl

theorem ordinary_lookup (names : Names S) (unique : Function.Injective (declarationName names))
    (namespaceTag : DeclName) (term : Binding.Term (Binding.withMetas S M) source sort)
    (fresh : ∀ symbol : Symbol S,
      FiniteParameters.indexedPositions namespaceTag M.length (declarationName names symbol) = none)
    {result : S.Srt} (operator : S.Op result)
    (present : (⟨result, Sum.inl operator⟩ : Sigma (Binding.withMetas S M).Op) ∈ usedOperators term) :
    (rules names namespaceTag term).constantType (names.operator operator) = some (operatorType names operator) := by
  have covered : Sum.inr ⟨result, operator⟩ ∈ inventory term :=
    List.mem_append_right _ (primitiveInventory_operator term operator
      (List.mem_append_right _ (List.mem_map.mpr ⟨_, present, rfl⟩)))
  change (signature names namespaceTag term).typeOf? _ = _
  change Option.map Entry.type ((signature names namespaceTag term).entries
    (declarationName names (.inr ⟨result, operator⟩))) = _
  rw [primitive_kept names namespaceTag term fresh,
    lookup names unique (inventory term) covered]
  rfl

/-- Only functions actually read by the shared compiler need a supplied
primitive. Unused metadata rows are still retained by the finite source. -/
theorem fixedTemplate_formed (names : Names S) (unique : Function.Injective (declarationName names))
    (namespaceTag : DeclName) (term : Binding.Term (Binding.withMetas S M) source sort)
    (fresh : ∀ symbol : Symbol S,
      FiniteParameters.indexedPositions namespaceTag M.length (declarationName names symbol) = none) :
    Typing (rules names namespaceTag term) (context names source)
      (Schema.fixedTemplate names (programs namespaceTag) term) (sortType names sort) := by
  apply Schema.fixedTemplate_typing_supported (sortRealization names unique namespaceTag term fresh)
    (programs namespaceTag) term
  · have primitive : ∀ {result : S.Srt} (operator : (Binding.withMetas S M).Op result),
        (⟨result, operator⟩ : Sigma (Binding.withMetas S M).Op) ∈ usedOperators term →
        Schema.ProgramPrimitive (M := M) names (rules names namespaceTag term) (programs namespaceTag) operator
      | _, .inl sourceOp, present => ordinary_lookup names unique namespaceTag term fresh sourceOp present
      | _, .inr (.mk index), present => by
          have member := (selected_mem term index).mpr (usedMetavariables_occurrence term index present)
          have valueTyped := Typing.const (Γ := Ctx.nil) (function_lookup names namespaceTag term index member)
            (functionType_formed names unique namespaceTag term fresh index) (.sort Tower.zero)
          change Typing _ .nil (.const _) (closeType (context names ((M.get index).1 ++ []))
            (liftClosed (sortType names (M.get index).2)))
          rw [liftClosed_zero] at valueTyped
          simpa only [List.append_nil, functionType, sortType, liftClosed, rename] using valueTyped
    exact (allOperators_used term).mono primitive
  · exact used_sort_present term


theorem original_entries_opaque (names : Names S)
    (term : Binding.Term (Binding.withMetas S M) source sort) (name : DeclName) (entry : Entry Tower.Head)
    (present : (name, entry) ∈ declarationList names (inventory term)) : entry.value? = none := by
  obtain ⟨symbol, _, same⟩ := List.mem_map.mp present
  have sameEntry : declarationEntry names symbol = entry := congrArg Prod.snd same
  rw [← sameEntry]
  cases symbol <;> rfl

theorem rootFree (names : Names S) (namespaceTag : DeclName)
    (term : Binding.Term (Binding.withMetas S M) source sort) :
    ConstantSubstitution.RootFree (rules names namespaceTag term).computation :=
  FiniteParameters.rootFree Tower.rules (fun impossible => impossible.elim)
    (declarationList names (inventory term)) (functionNames namespaceTag term)
    (functionTypes names term) (original_entries_opaque names term)

/-- Every actual finite declaration has a formed type, including the complete
unused metadata; no value inhabiting an unused source type is requested. -/
theorem wellFormed (names : Names S) (unique : Function.Injective (declarationName names))
    (namespaceTag : DeclName) (term : Binding.Term (Binding.withMetas S M) source sort)
    (fresh : ∀ symbol : Symbol S,
      FiniteParameters.indexedPositions namespaceTag M.length (declarationName names symbol) = none) :
    (signature names namespaceTag term).WellFormed Tower.rules := by
  apply FiniteParameters.wellFormed Tower.rules (fun _ => rfl)
    (declarationList names (inventory term)) (functionNames namespaceTag term)
    (functionTypes names term) (original_entries_opaque names term)
  intro name type known
  change (signature names namespaceTag term).typeOf? name = some type at known
  unfold Signature.typeOf? at known
  cases entrySelected : (signature names namespaceTag term).entries name with
  | none => simp only [entrySelected, Option.map_none, reduceCtorEq] at known
  | some value =>
      have sameType : value.type = type := by simpa only [entrySelected, Option.map_some, Option.some.injEq] using known
      have member := Signature.entries_ofList_mem
        (FiniteParameters.declarations (functionNames namespaceTag term) (functionTypes names term) ++
          declarationList names (inventory term)) entrySelected
      subst type
      rcases List.mem_append.mp member with functionMember | primitiveMember
      · obtain ⟨position, same⟩ := List.mem_ofFn.mp functionMember
        have sameEntry : FiniteParameters.entry (functionTypes names term) position = value := congrArg Prod.snd same
        rw [← sameEntry]
        exact ⟨.sort Tower.zero,
          functionType_formed names unique namespaceTag term fresh (sourceIndex term position), .sort Tower.zero⟩
      · obtain ⟨symbol, present, same⟩ := List.mem_map.mp primitiveMember
        have sameEntry : declarationEntry names symbol = value := congrArg Prod.snd same
        rw [← sameEntry]
        cases symbol with
        | inl selectedSort =>
            exact ⟨.sort (.succ Tower.zero), .headType (.sort Tower.zero), .sort (.succ Tower.zero)⟩
        | inr operator =>
            have covered := inventory_closed term operator present
            exact ⟨.sort Tower.zero,
              (sortRealization names unique namespaceTag term fresh).operatorType_formed operator.2 covered.1 covered.2,
              .sort Tower.zero⟩

end SchemaTemplates
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.BindingSignaturePackage


set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.BindingSignaturePackage
open Mettapedia.OSLF
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Declaration BindingSignatureEmbedding TelescopeAbstraction FormationSensitive
variable {S : Binding.Signature} {M : List (Binding.MetaArity S)} {Head : Type} {n : Nat}

namespace SchemaTemplates

theorem result_used : ∀ {source : Binding.Ctx S} {sort : S.Srt}
    (term : Binding.Term S source sort), sort ∈ usedSorts term
  | _, _, .var _ => List.mem_cons_self
  | _, _, .op _ _ => List.mem_cons_self

/-- Native type interpretation follows the binding telescope rather than an
assumed whole-program correspondence. -/
theorem interpret_closedArrow (values : ConstantSubstitution.Values Head n)
    (domain codomain : Tm Head 0) :
    ConstantSubstitution.interpret values Fin.elim0 (closedArrow domain codomain) =
      .pi (ConstantSubstitution.interpret values Fin.elim0 domain)
        (rename wk (ConstantSubstitution.interpret values Fin.elim0 codomain)) := by
  simp only [closedArrow, ConstantSubstitution.interpret,
    ConstantSubstitution.interpret_liftClosed, ConstantSubstitution.rename_interpret_closed]
  rfl

theorem interpret_telescopeType (names : Names S) (types : ClosedOperators.Types S Head)
    (values : ConstantSubstitution.Values Head n) (bound : List S.Srt)
    (covered : ∀ sort ∈ bound, values (names.sort sort) = liftClosed (types sort))
    (sourceResult targetResult : Tm Head 0)
    (resultEq : ConstantSubstitution.interpret values Fin.elim0 sourceResult = liftClosed targetResult) :
    ConstantSubstitution.interpret values Fin.elim0 (telescopeType names bound sourceResult) =
      liftClosed (ClosedOperators.spineType types bound targetResult) := by
  induction bound generalizing sourceResult targetResult with
  | nil => exact resultEq
  | cons sort rest ih =>
      apply ih (fun other member => covered other (List.mem_cons_of_mem _ member))
      rw [interpret_closedArrow, resultEq]
      change Tm.pi (values (names.sort sort)) (rename wk (liftClosed targetResult)) = _
      rw [covered sort List.mem_cons_self, rename_liftClosed, liftClosed_closedArrow]

theorem interpret_bindingType (names : Names S) (types : ClosedOperators.Types S Head)
    (values : ConstantSubstitution.Values Head n) (bound : List S.Srt) (sort : S.Srt)
    (covered : ∀ selected ∈ bound, values (names.sort selected) = liftClosed (types selected))
    (resultEq : values (names.sort sort) = liftClosed (types sort)) :
    ConstantSubstitution.interpret values Fin.elim0 (bindingType names bound sort) =
      liftClosed (ClosedOperators.bindingType types bound sort) :=
  interpret_telescopeType names types values bound covered _ _ resultEq

theorem interpret_argumentsType (names : Names S) (types : ClosedOperators.Types S Head)
    (values : ConstantSubstitution.Values Head n) (arity : List (List S.Srt × S.Srt))
    (covered : ∀ sort ∈ aritySorts arity, values (names.sort sort) = liftClosed (types sort))
    (sourceResult targetResult : Tm Head 0)
    (resultEq : ConstantSubstitution.interpret values Fin.elim0 sourceResult = liftClosed targetResult) :
    ConstantSubstitution.interpret values Fin.elim0 (argumentsType names arity sourceResult) =
      liftClosed (ClosedOperators.argumentsType types arity targetResult) := by
  induction arity with
  | nil => exact resultEq
  | cons argument rest ih =>
      rw [argumentsType, ClosedOperators.argumentsType, interpret_closedArrow,
        interpret_bindingType names types values argument.1 argument.2
          (fun selected member => covered selected (List.mem_append_left _ member))
          (covered argument.2 (List.mem_append_right _ List.mem_cons_self)),
        ih (fun selected member => covered selected (List.mem_append_right _ (List.mem_cons_of_mem _ member))),
        rename_liftClosed, liftClosed_closedArrow]

theorem interpret_operatorType (names : Names S) (types : ClosedOperators.Types S Head)
    (values : ConstantSubstitution.Values Head n) {sort : S.Srt} (operator : S.Op sort)
    (covered : ∀ selected ∈ aritySorts (S.arity operator),
      values (names.sort selected) = liftClosed (types selected))
    (resultEq : values (names.sort sort) = liftClosed (types sort)) :
    ConstantSubstitution.interpret values Fin.elim0 (operatorType names operator) =
      liftClosed (ClosedOperators.operatorType types operator) :=
  interpret_argumentsType names types values (S.arity operator) covered _ _ resultEq

/-- The dispatcher reads the actual finite declaration inventory. It never
enumerates the ambient binding signature. -/
def readSymbol? (names : Names S) (symbols : List (Symbol S)) (name : DeclName) : Option (Symbol S) :=
  symbols.find? fun symbol => declarationName names symbol == name

theorem readSymbol?_present (names : Names S) (unique : Function.Injective (declarationName names))
    (symbols : List (Symbol S)) (symbol : Symbol S) (present : symbol ∈ symbols) :
    readSymbol? names symbols (declarationName names symbol) = some symbol := by
  induction symbols with
  | nil => cases present
  | cons first rest ih =>
      by_cases same : symbol = first
      · subst first
        simp [readSymbol?, List.find?]
      · have different : declarationName names first ≠ declarationName names symbol :=
          fun equal => same (unique equal.symm)
        simpa only [readSymbol?, List.find?, beq_eq_false_iff_ne.mpr different, Bool.false_eq_true, ↓reduceIte] using
          (ih ((List.mem_cons.mp present).resolve_left same))


def selectedPosition? {source : Binding.Ctx S} {sort : S.Srt}
    (term : Binding.Term (Binding.withMetas S M) source sort) (index : Fin M.length) :
    Option (Fin (selected term).length) :=
  if present : index ∈ selected term then
    some ⟨(selected term).idxOf index, List.idxOf_lt_length_iff.mpr present⟩
  else none

theorem selectedPosition?_sourceIndex {source : Binding.Ctx S} {sort : S.Srt}
    (term : Binding.Term (Binding.withMetas S M) source sort) (position : Fin (selected term).length) :
    selectedPosition? term (sourceIndex term position) = some position := by
  unfold selectedPosition? sourceIndex
  split
  · apply congrArg some
    apply Fin.ext
    exact List.get_idxOf (selected_nodup term) position
  · rename_i absent
    exact False.elim (absent (List.get_mem (selected term) position))

theorem readSymbol?_function (names : Names S) (namespaceTag : DeclName)
    (symbols : List (Symbol S))
    (fresh : ∀ symbol : Symbol S,
      FiniteParameters.indexedPositions namespaceTag M.length (declarationName names symbol) = none)
    (index : Fin M.length) :
    readSymbol? names symbols (FiniteParameters.indexedName namespaceTag index) = none := by
  induction symbols with
  | nil => rfl
  | cons first rest ih =>
      have different : declarationName names first ≠ FiniteParameters.indexedName namespaceTag index := by
        intro same
        have impossible := fresh first
        rw [same, FiniteParameters.indexedPositions_name] at impossible
        cases impossible
      simpa only [readSymbol?, List.find?, beq_eq_false_iff_ne.mpr different, Bool.false_eq_true, ↓reduceIte] using ih

/-- Primitive types and ordinary constructors receive their actual native
images. A used function receives its own finite caller position. -/
def nativeValues {source : Binding.Ctx S} {sort : S.Srt}
    (names : Names S) (namespaceTag : DeclName)
    (term : Binding.Term (Binding.withMetas S M) source sort)
    (types : ClosedOperators.Types S Tower.Head) (images : ClosedOperators.Images S Tower.Head)
    (functions : Fin (selected term).length → Tm Tower.Head n) : ConstantSubstitution.Values Tower.Head n :=
  fun name => match readSymbol? names (inventory term) name with
    | some (.inl selectedSort) => liftClosed (types selectedSort)
    | some (.inr operator) => liftClosed (images operator.2)
    | none => match FiniteParameters.indexedPositions namespaceTag M.length name with
      | none => .const name
      | some original => match selectedPosition? term original with
        | none => .const name
        | some position => functions position

theorem nativeValues_sort {source : Binding.Ctx S} {sort : S.Srt}
    (names : Names S) (unique : Function.Injective (declarationName names)) (namespaceTag : DeclName)
    (term : Binding.Term (Binding.withMetas S M) source sort)
    (types : ClosedOperators.Types S Tower.Head) (images : ClosedOperators.Images S Tower.Head)
    (functions : Fin (selected term).length → Tm Tower.Head n)
    (selectedSort : S.Srt) (present : Sum.inl selectedSort ∈ inventory term) :
    nativeValues names namespaceTag term types images functions (names.sort selectedSort) = liftClosed (types selectedSort) := by
  unfold nativeValues
  change (match readSymbol? names (inventory term) (declarationName names (.inl selectedSort)) with
    | some (.inl s) => liftClosed (types s)
    | some (.inr operator) => liftClosed (images operator.2)
    | none => _) = _
  rw [readSymbol?_present names unique (inventory term) (.inl selectedSort) present]

theorem nativeValues_operator {source : Binding.Ctx S} {sort : S.Srt}
    (names : Names S) (unique : Function.Injective (declarationName names)) (namespaceTag : DeclName)
    (term : Binding.Term (Binding.withMetas S M) source sort)
    (types : ClosedOperators.Types S Tower.Head) (images : ClosedOperators.Images S Tower.Head)
    (functions : Fin (selected term).length → Tm Tower.Head n)
    (operator : Sigma S.Op) (present : Sum.inr operator ∈ inventory term) :
    nativeValues names namespaceTag term types images functions (names.operator operator.2) = liftClosed (images operator.2) := by
  unfold nativeValues
  change (match readSymbol? names (inventory term) (declarationName names (.inr operator)) with
    | some (.inl s) => liftClosed (types s)
    | some (.inr operation) => liftClosed (images operation.2)
    | none => _) = _
  rw [readSymbol?_present names unique (inventory term) (.inr operator) present]

theorem nativeValues_function {source : Binding.Ctx S} {sort : S.Srt}
    (names : Names S) (namespaceTag : DeclName)
    (term : Binding.Term (Binding.withMetas S M) source sort)
    (types : ClosedOperators.Types S Tower.Head) (images : ClosedOperators.Images S Tower.Head)
    (functions : Fin (selected term).length → Tm Tower.Head n)
    (fresh : ∀ symbol : Symbol S,
      FiniteParameters.indexedPositions namespaceTag M.length (declarationName names symbol) = none)
    (position : Fin (selected term).length) :
    nativeValues names namespaceTag term types images functions
      (functionNames namespaceTag term position) = functions position := by
  unfold nativeValues functionNames
  simp only [readSymbol?_function names namespaceTag (inventory term) fresh,
    FiniteParameters.indexedPositions_name, selectedPosition?_sourceIndex]


theorem native_functionType {source : Binding.Ctx S} {sort : S.Srt}
    (names : Names S) (unique : Function.Injective (declarationName names)) (namespaceTag : DeclName)
    (term : Binding.Term (Binding.withMetas S M) source sort)
    (types : ClosedOperators.Types S Tower.Head) (images : ClosedOperators.Images S Tower.Head)
    (functions : Fin (selected term).length → Tm Tower.Head n) (index : Fin M.length) :
    ConstantSubstitution.interpret (nativeValues names namespaceTag term types images functions) Fin.elim0
      (functionType names index) =
      liftClosed (ClosedOperators.bindingType types (M.get index).1 (M.get index).2) := by
  rw [functionType_eq]
  apply interpret_bindingType names types
  · exact fun selectedSort present => nativeValues_sort names unique namespaceTag term types images functions
      selectedSort (metadata_sort_present term selectedSort (metadataSorts_dependency index selectedSort present))
  · exact nativeValues_sort names unique namespaceTag term types images functions _
      (metadata_sort_present term _ (metadataSorts_result index))

/-- Native primitive authority is reconstructed by inspecting every entry of
the actual finite source package: sorts, ordinary constructors, or used
function parameters. The target may retain its declared computations. -/
theorem nativeValues_typed {source : Binding.Ctx S} {sort : S.Srt}
    (names : Names S) (unique : Function.Injective (declarationName names)) (namespaceTag : DeclName)
    (term : Binding.Term (Binding.withMetas S M) source sort)
    (fresh : ∀ symbol : Symbol S,
      FiniteParameters.indexedPositions namespaceTag M.length (declarationName names symbol) = none)
    (destination : Signature Tower.Head)
    (types : ClosedOperators.Types S Tower.Head) (images : ClosedOperators.Images S Tower.Head)
    (realization : ClosedOperators.Realization types images (extendRules Tower.rules destination))
    (sameUniverse : realization.typeUniverse = .sort Tower.zero)
    (caller : Ctx Tower.Head n) (functions : Fin (selected term).length → Tm Tower.Head n)
    (functionTyped : ∀ position, Typing (extendRules Tower.rules destination) caller (functions position)
      (liftClosed (ClosedOperators.bindingType types (M.get (sourceIndex term position)).1
        (M.get (sourceIndex term position)).2))) :
    ConstantSubstitution.TypedValues (rules names namespaceTag term) (extendRules Tower.rules destination) caller
      (nativeValues names namespaceTag term types images functions) := by
  intro name type known
  obtain ⟨entry, selectedEntry, sameType⟩ := FiniteParameters.constant_entry Tower.rules (fun _ => rfl)
    (declarationList names (inventory term)) (functionNames namespaceTag term) (functionTypes names term) known
  subst type
  have member := Signature.entries_ofList_mem
    (FiniteParameters.declarations (functionNames namespaceTag term) (functionTypes names term) ++
      declarationList names (inventory term)) selectedEntry
  rcases List.mem_append.mp member with functionMember | primitiveMember
  · obtain ⟨position, same⟩ := List.mem_ofFn.mp functionMember
    have sameName : functionNames namespaceTag term position = name := congrArg Prod.fst same
    have sameEntry : FiniteParameters.entry (functionTypes names term) position = entry := congrArg Prod.snd same
    rw [← sameName, ← sameEntry]
    change Typing _ caller (nativeValues names namespaceTag term types images functions (functionNames namespaceTag term position))
      (ConstantSubstitution.interpret _ Fin.elim0 (functionType names (sourceIndex term position)))
    rw [nativeValues_function names namespaceTag term types images functions fresh,
      native_functionType names unique namespaceTag term types images functions]
    exact functionTyped position
  · obtain ⟨symbol, present, same⟩ := List.mem_map.mp primitiveMember
    have sameName : declarationName names symbol = name := congrArg Prod.fst same
    have sameEntry : declarationEntry names symbol = entry := congrArg Prod.snd same
    rw [← sameName, ← sameEntry]
    cases symbol with
    | inl selectedSort =>
        change Typing _ caller
          (nativeValues names namespaceTag term types images functions (names.sort selectedSort)) (.head (.sort Tower.zero))
        rw [nativeValues_sort names unique namespaceTag term types images functions selectedSort present]
        have formed := realization.typeFormed selectedSort
        rw [sameUniverse] at formed
        exact FormationCheckedTelescopePrograms.liftClosed_typing formed caller
    | inr operator =>
        change Typing _ caller
          (nativeValues names namespaceTag term types images functions (names.operator operator.2))
          (ConstantSubstitution.interpret _ Fin.elim0 (operatorType names operator.2))
        have covered := inventory_closed term operator present
        rw [nativeValues_operator names unique namespaceTag term types images functions operator present,
          interpret_operatorType names types _ operator.2
            (fun selectedSort member => nativeValues_sort names unique namespaceTag term types images functions
              selectedSort (covered.2 selectedSort member))
            (nativeValues_sort names unique namespaceTag term types images functions operator.1 covered.1)]
        exact FormationCheckedTelescopePrograms.liftClosed_typing (realization.imageTyped operator.2) caller

/-- Formation of the compiled source template is transported to the actual
native primitive programs and supplied function values, with source assignment
handled by the ordinary typed simultaneous substitution. -/
theorem interpretedTemplate_typing {source : Binding.Ctx S} {sort : S.Srt}
    (names : Names S) (unique : Function.Injective (declarationName names)) (namespaceTag : DeclName)
    (term : Binding.Term (Binding.withMetas S M) source sort)
    (fresh : ∀ symbol : Symbol S,
      FiniteParameters.indexedPositions namespaceTag M.length (declarationName names symbol) = none)
    (destination : Signature Tower.Head)
    (types : ClosedOperators.Types S Tower.Head) (images : ClosedOperators.Images S Tower.Head)
    (realization : ClosedOperators.Realization types images (extendRules Tower.rules destination))
    (sameUniverse : realization.typeUniverse = .sort Tower.zero)
    (caller : Ctx Tower.Head n) (functions : Fin (selected term).length → Tm Tower.Head n)
    (functionTyped : ∀ position, Typing (extendRules Tower.rules destination) caller (functions position)
      (liftClosed (ClosedOperators.bindingType types (M.get (sourceIndex term position)).1
        (M.get (sourceIndex term position)).2)))
    (assignment : Sub Tower.Head source.length n)
    (variableTyped : ConstantSubstitution.TypedVariables (extendRules Tower.rules destination)
      (context names source) caller (nativeValues names namespaceTag term types images functions) assignment) :
    Typing (extendRules Tower.rules destination) caller
      (ConstantSubstitution.interpret (nativeValues names namespaceTag term types images functions) assignment
        (Schema.fixedTemplate names (programs namespaceTag) term))
      (liftClosed (types sort)) := by
  have map := FiniteParameters.rulesMap Tower.rules (fun impossible => impossible.elim)
    (declarationList names (inventory term)) (functionNames namespaceTag term) (functionTypes names term)
    (original_entries_opaque names term) destination
  have interpreted := ConstantSubstitution.typing map (fixedTemplate_formed names unique namespaceTag term fresh)
    (nativeValues_typed names unique namespaceTag term fresh destination types images realization sameUniverse caller functions functionTyped)
    variableTyped
  have occurs := result_used (S := Binding.withMetas S M) term
  have resultLookup := nativeValues_sort names unique namespaceTag term types images functions sort
    (used_sort_present term sort occurs)
  change Typing _ caller _
    (nativeValues names namespaceTag term types images functions (names.sort sort)) at interpreted
  rw [resultLookup] at interpreted
  exact interpreted

end SchemaTemplates
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.BindingSignaturePackage


set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.BindingSignaturePackage.SchemaTemplates
open Mettapedia.OSLF
variable {S : Binding.Signature} {M : List (Binding.MetaArity S)} {Value : Type}
variable {source : Binding.Ctx S} {sort : S.Srt}

/-- The caller supplies a finite table keyed by original source ordinals.
Only functions actually referenced by the compiled schema are requested. -/
def readFunctions? (term : Binding.Term (Binding.withMetas S M) source sort)
    (supplied : List (Fin M.length × Value)) : Option (List Value) :=
  (selected term).mapM fun original => supplied.lookup original

/-- Availability is exact on the original used ordinals. Neither an unused
metadata row nor a duplicate occurrence creates another caller obligation. -/
theorem readFunctions?_exact (term : Binding.Term (Binding.withMetas S M) source sort)
    (supplied : List (Fin M.length × Value)) :
    (∃ values, readFunctions? term supplied = some values) ↔
      ∀ original ∈ usedMetavariables term, ∃ value, supplied.lookup original = some value := by
  rw [readFunctions?, Binding.SortArityDecoder.mapM_exists_iff]
  constructor
  · intro available original member
    exact available original ((selected_mem term original).mpr member)
  · intro available original member
    exact available original ((selected_mem term original).mp member)

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.BindingSignaturePackage.SchemaTemplates

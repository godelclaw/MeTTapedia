import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.CanonicalSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Laws
import Mettapedia.OSLF.MeTTaIL.CanonicalTable

/-!
# Canonical forms, in MeTTa

On patterns whose names are in the table, `gslt:canon:cmp` is `CanonicalCompare.cmp`,
`gslt:canon:sort` is insertion sort by it, and `gslt:canon:canon` is `CanonicalBags.canon`
(`canon_returns`): the canonical form computed with comparisons of numbers and string equality, a set's
sorted elements kept once each (`gslt:canon:dedup-sorted`).
`gslt:canon:canonical` is the standard form of the declared laws followed by the canonical form
(`canonical_returns`). A table is `(LCons name … LNil)`, an ordering `LT`, `EQ` or `GT`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open Mettapedia.GSLT.LanguageDef CettaWire InferenceCettaWire
open Mettapedia.OSLF.MeTTaIL Syntax PatternLexOrder CanonicalBags CanonicalCompare CollectionLaws
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Effects (State)
open Eval
open BridgeKit WireKit

/-! ## The data -/

def orderingTerm : Ordering → Term
  | .lt => .symbol "LT"
  | .eq => .symbol "EQ"
  | .gt => .symbol "GT"

abbrev orderingValue (ordering : Ordering) : Atom := encoded (orderingTerm ordering)

abbrev tableValue (table : List String) : Atom := encoded (CettaWire.encodeList Term.string table)

/-- Walk a body of the canonical library. -/
syntax "canonical_eval" (" [" term,* "]")? (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| canonical_eval $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (metta_call_in canonicalProof_checked using canonicalProof_agreement; metta_eval [$facts,*] with canonicalProof_checked in canonicalProof_agreement
      unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?, pattern_symbol_unmatched,
        orderingValue, orderingTerm, tableValue, $extra,*]))

/-! ## Numbers and names -/

@[metta_head "gslt:canon:nat-cmp"]
theorem nat_cmp_returns (state : State) (left right : Nat) :
    PureReturns canonicalLibrary.runtime [] state (apply "gslt:canon:nat-cmp" [number left, number right]) state
      (orderingValue (compare left right)) := by
  rcases Nat.lt_trichotomy left right with less | same | more
  · canonical_eval unfolding [less, Nat.compare_eq_lt.mpr less]
  · subst same
    canonical_eval unfolding [compare_refl, Nat.lt_irrefl]
  · canonical_eval unfolding [Nat.not_lt.mpr (Nat.le_of_lt more), Nat.ne_of_gt more, Nat.compare_eq_gt.mpr more]

@[metta_head "gslt:canon:name-scan"]
theorem name_scan_returns (state : State) (left right : String) : ∀ table : List String,
    left ∈ table ∨ right ∈ table →
    PureReturns canonicalLibrary.runtime [] state
      (apply "gslt:canon:name-scan" [tableValue table, encoded (.string left), encoded (.string right)]) state
      (orderingValue (nameScan table left right))
  | [], found => by simp at found
  | name :: rest, found => by
    by_cases first : name = left
    · subst first
      canonical_eval unfolding [CettaWire.encodeList, nameScan]
    · by_cases second : name = right
      · subst second
        canonical_eval unfolding [CettaWire.encodeList, nameScan, first]
      · have later := name_scan_returns state left right rest (by
          rcases found with inside | inside
          · exact Or.inl ((List.mem_cons.mp inside).resolve_left (Ne.symm first))
          · exact Or.inr ((List.mem_cons.mp inside).resolve_left (Ne.symm second)))
        canonical_eval [later] unfolding [CettaWire.encodeList, nameScan, first, second]

@[metta_head "gslt:canon:name-cmp"]
theorem name_cmp_returns (state : State) (table : List String) (left right : String)
    (found : left ∈ table ∧ right ∈ table) :
    PureReturns canonicalLibrary.runtime [] state
      (apply "gslt:canon:name-cmp" [tableValue table, encoded (.string left), encoded (.string right)]) state
      (orderingValue (nameCmp table left right)) := by
  by_cases same : left = right
  · subst same
    canonical_eval unfolding [nameCmp]
  · have scan := name_scan_returns state left right table (Or.inl found.1)
    canonical_eval [scan] unfolding [nameCmp, same]

@[metta_head "gslt:canon:length-cmp"]
theorem length_cmp_returns {α : Type} (element : α → Term) (state : State) : ∀ left right : List α,
    PureReturns canonicalLibrary.runtime [] state
      (apply "gslt:canon:length-cmp" [encoded (CettaWire.encodeList element left),
        encoded (CettaWire.encodeList element right)]) state
      (orderingValue (compare left.length right.length))
  | [], [] => by canonical_eval unfolding [CettaWire.encodeList, compare_refl]
  | [], _ :: _ => by canonical_eval unfolding [CettaWire.encodeList, List.length_cons, Nat.compare_eq_lt.mpr (Nat.succ_pos _)]
  | _ :: _, [] => by canonical_eval unfolding [CettaWire.encodeList, List.length_cons, Nat.compare_eq_gt.mpr (Nat.succ_pos _)]
  | _ :: lefts, _ :: rights => by
    have later := length_cmp_returns element state lefts rights
    have succ : compare (lefts.length + 1) (rights.length + 1) = compare lefts.length rights.length := by
      rcases Nat.lt_trichotomy lefts.length rights.length with less | same | more
      · rw [Nat.compare_eq_lt.mpr less, Nat.compare_eq_lt.mpr (Nat.succ_lt_succ less)]
      · rw [same, compare_refl, compare_refl]
      · rw [Nat.compare_eq_gt.mpr more, Nat.compare_eq_gt.mpr (Nat.succ_lt_succ more)]
    simp only [List.length_cons, succ]
    canonical_eval [later] unfolding [CettaWire.encodeList, List.length_cons, succ]

theorem patterns_length_cmp_returns (state : State) (left right : List Pattern) :
    PureReturns canonicalLibrary.runtime [] state
      (apply "gslt:canon:length-cmp" [patternsValue left, patternsValue right]) state
      (orderingValue (compare left.length right.length)) := by
  simpa only [patternsValue, encodePatterns_eq_encodeList] using length_cmp_returns encodePattern state left right

@[metta_head "gslt:canon:names-pairwise"]
theorem names_pairwise_returns (state : State) (table : List String) : ∀ left right : List String,
    left.length = right.length → (∀ name ∈ left, name ∈ table) → (∀ name ∈ right, name ∈ table) →
    PureReturns canonicalLibrary.runtime [] state
      (apply "gslt:canon:names-pairwise" [tableValue table, encoded (CettaWire.encodeList Term.string left),
        encoded (CettaWire.encodeList Term.string right)]) state
      (orderingValue (namesPairwise table left right))
  | [], [], _, _, _ => by canonical_eval unfolding [CettaWire.encodeList, namesPairwise]
  | [], _ :: _, lengths, _, _ => by simp at lengths
  | _ :: _, [], lengths, _, _ => by simp at lengths
  | left :: lefts, right :: rights, lengths, leftIn, rightIn => by
    have here := name_cmp_returns state table left right ⟨leftIn left (by simp), rightIn right (by simp)⟩
    have later := names_pairwise_returns state table lefts rights (by simpa using lengths)
      (fun name member => leftIn name (by simp [member])) (fun name member => rightIn name (by simp [member]))
    cases ordering : nameCmp table left right with
    | lt => rw [ordering] at here; canonical_eval [here] unfolding [CettaWire.encodeList, namesPairwise, ordering]
    | eq =>
      rw [ordering] at here
      simp only [namesPairwise, ordering, eq_then]
      canonical_eval [here, later] unfolding [CettaWire.encodeList, namesPairwise, ordering]
    | gt => rw [ordering] at here; canonical_eval [here] unfolding [CettaWire.encodeList, namesPairwise, ordering]

@[metta_head "gslt:canon:names-cmp"]
theorem names_cmp_returns (state : State) (table : List String) (left right : List String)
    (leftIn : ∀ name ∈ left, name ∈ table) (rightIn : ∀ name ∈ right, name ∈ table) :
    PureReturns canonicalLibrary.runtime [] state
      (apply "gslt:canon:names-cmp" [tableValue table, encoded (CettaWire.encodeList Term.string left),
        encoded (CettaWire.encodeList Term.string right)]) state
      (orderingValue (namesCmp table left right)) := by
  have lengths := length_cmp_returns Term.string state left right
  by_cases same : left.length = right.length
  · have pairwise := names_pairwise_returns state table left right same leftIn rightIn
    rw [same, compare_refl] at lengths
    simp only [namesCmp, same, compare_refl, eq_then]
    canonical_eval [lengths, pairwise] unfolding [namesCmp, same, compare_refl, eq_then]
  · cases ordering : compare left.length right.length with
    | lt => rw [ordering] at lengths; canonical_eval [lengths] unfolding [namesCmp, ordering]
    | eq => exact absurd (Nat.compare_eq_eq.mp ordering) same
    | gt => rw [ordering] at lengths; canonical_eval [lengths] unfolding [namesCmp, ordering]

@[metta_head "gslt:canon:binder-cmp"]
theorem binder_cmp_returns (state : State) (table : List String) (left right : Option String)
    (leftIn : ∀ name ∈ left.toList, name ∈ table) (rightIn : ∀ name ∈ right.toList, name ∈ table) :
    PureReturns canonicalLibrary.runtime [] state
      (apply "gslt:canon:binder-cmp" [tableValue table, encoded (encodeBinder left), encoded (encodeBinder right)])
      state (orderingValue (optCmp table left right)) := by
  cases left with
  | none => cases right <;> canonical_eval unfolding [encodeBinder, optCmp]
  | some name =>
    cases right with
    | none => canonical_eval unfolding [encodeBinder, optCmp]
    | some other =>
      have names := name_cmp_returns state table name other ⟨leftIn name (by simp), rightIn other (by simp)⟩
      canonical_eval [names] unfolding [encodeBinder, optCmp]

@[metta_head "gslt:canon:rest-cmp"]
theorem rest_cmp_returns (state : State) (table : List String) (left right : Option String)
    (leftIn : ∀ name ∈ left.toList, name ∈ table) (rightIn : ∀ name ∈ right.toList, name ∈ table) :
    PureReturns canonicalLibrary.runtime [] state
      (apply "gslt:canon:rest-cmp" [tableValue table, encoded (encodeRest left), encoded (encodeRest right)])
      state (orderingValue (optCmp table left right)) := by
  cases left with
  | none => cases right <;> canonical_eval unfolding [encodeRest, optCmp]
  | some name =>
    cases right with
    | none => canonical_eval unfolding [encodeRest, optCmp]
    | some other =>
      have names := name_cmp_returns state table name other ⟨leftIn name (by simp), rightIn other (by simp)⟩
      canonical_eval [names] unfolding [encodeRest, optCmp]

/-! ## Tags -/

@[metta_head "gslt:canon:tag"]
theorem tag_returns (state : State) (pattern : Pattern) :
    PureReturns canonicalLibrary.runtime [] state (apply "gslt:canon:tag" [patternValue pattern]) state
      (number (tag pattern)) := by
  cases pattern <;> canonical_eval unfolding [tag, patternValue, encodePattern]

@[metta_head "gslt:canon:kind-tag"]
theorem kind_tag_returns (state : State) (kind : CollType) :
    PureReturns canonicalLibrary.runtime [] state (apply "gslt:canon:kind-tag" [encoded (encodeCollectionType kind)])
      state (number (collectionTag kind)) := by
  cases kind <;> canonical_eval unfolding [collectionTag, encodeCollectionType]

@[metta_head "gslt:canon:unordered"]
theorem unordered_returns (state : State) (kind : CollType) :
    PureReturns canonicalLibrary.runtime [] state (apply "gslt:canon:unordered" [encoded (encodeCollectionType kind)])
      state (Effects.boolean (Unordered kind)) := by
  cases kind <;> canonical_eval unfolding [Unordered, encodeCollectionType]

/-! ## Comparing patterns -/

/-- What `gslt:canon:cmp` returns. -/
abbrev CmpAt (state : State) (table : List String) (left right : Pattern) : Prop :=
  PureReturns canonicalLibrary.runtime [] state
    (apply "gslt:canon:cmp" [tableValue table, patternValue left, patternValue right]) state
    (orderingValue (cmp table left right))

/-- What `gslt:canon:cmp-pairwise` returns. -/
abbrev PairwiseAt (state : State) (table : List String) (left right : List Pattern) : Prop :=
  PureReturns canonicalLibrary.runtime [] state
    (apply "gslt:canon:cmp-pairwise" [tableValue table, patternsValue left, patternsValue right]) state
    (orderingValue (cmpList table left right))

/-- What `gslt:canon:cmp-counted` returns. -/
abbrev CountedAt (state : State) (table : List String) (left right : List Pattern) : Prop :=
  PureReturns canonicalLibrary.runtime [] state
    (apply "gslt:canon:cmp-counted" [tableValue table, patternsValue left, patternsValue right]) state
    (orderingValue ((compare left.length right.length).then (cmpList table left right)))

@[metta_head "gslt:canon:cmp-pairwise"]
theorem cmp_pairwise_of (state : State) (table : List String) : ∀ left : List Pattern,
    (∀ pattern ∈ left, ∀ other, Covered table pattern → Covered table other → CmpAt state table pattern other) →
    ∀ right : List Pattern, left.length = right.length → (∀ pattern ∈ left, Covered table pattern) →
      (∀ pattern ∈ right, Covered table pattern) → PairwiseAt state table left right
  | [], _, [], _, _, _ => by canonical_eval unfolding [PairwiseAt, cmpList, patternsValue, encodePatterns]
  | [], _, _ :: _, lengths, _, _ => by simp at lengths
  | _ :: _, _, [], lengths, _, _ => by simp at lengths
  | first :: lefts, each, other :: rights, lengths, leftIn, rightIn => by
    have here := each first (by simp) other (leftIn first (by simp)) (rightIn other (by simp))
    have later := cmp_pairwise_of state table lefts (fun pattern member => each pattern (by simp [member])) rights
      (by simpa using lengths) (fun pattern member => leftIn pattern (by simp [member]))
      (fun pattern member => rightIn pattern (by simp [member]))
    cases ordering : cmp table first other with
    | lt =>
      rw [CmpAt, ordering] at here
      canonical_eval [here] unfolding [PairwiseAt, cmpList, ordering, patternsValue, patternValue, encodePatterns]
    | eq =>
      rw [CmpAt, ordering] at here
      simp only [PairwiseAt, cmpList, ordering, eq_then]
      canonical_eval [here, later]
        unfolding [PairwiseAt, cmpList, ordering, eq_then, patternsValue, patternValue, encodePatterns]
    | gt =>
      rw [CmpAt, ordering] at here
      canonical_eval [here] unfolding [PairwiseAt, cmpList, ordering, patternsValue, patternValue, encodePatterns]

@[metta_head "gslt:canon:cmp-counted"]
theorem cmp_counted_of (state : State) (table : List String) (left right : List Pattern)
    (each : ∀ pattern ∈ left, ∀ other, Covered table pattern → Covered table other → CmpAt state table pattern other)
    (leftIn : ∀ pattern ∈ left, Covered table pattern) (rightIn : ∀ pattern ∈ right, Covered table pattern) :
    CountedAt state table left right := by
  have lengths := patterns_length_cmp_returns state left right
  by_cases same : left.length = right.length
  · have pairwise := cmp_pairwise_of state table left each right same leftIn rightIn
    rw [same, compare_refl] at lengths
    simp only [CountedAt, same, compare_refl, eq_then]
    canonical_eval [lengths, pairwise] unfolding [CountedAt, PairwiseAt, same, compare_refl, eq_then]
  · cases ordering : compare left.length right.length with
    | lt => rw [ordering] at lengths; canonical_eval [lengths] unfolding [CountedAt, ordering]
    | eq => exact absurd (Nat.compare_eq_eq.mp ordering) same
    | gt => rw [ordering] at lengths; canonical_eval [lengths] unfolding [CountedAt, ordering]

/-- Combine a first comparison with a later one, as `(if (== first EQ) later first)` does. -/
theorem then_cases {first : Ordering} {P : Ordering → Prop} (second : Ordering)
    (eq : first = .eq → P second) (other : first ≠ .eq → P first) : P (first.then second) := by
  cases first with
  | eq => exact eq rfl
  | lt => exact other (by decide)
  | gt => exact other (by decide)

/-! ### Coverage of the parts of a pattern -/

theorem covered_apply {table : List String} {label : String} {arguments : List Pattern}
    (covered : Covered table (.apply label arguments)) :
    label ∈ table ∧ ∀ argument ∈ arguments, Covered table argument :=
  ⟨covered label (by simp [names]),
    covered_elements.mp fun name member => covered name (by simp [names, member])⟩

theorem covered_lambda {table : List String} {binder : Option String} {body : Pattern}
    (covered : Covered table (.lambda binder body)) :
    (∀ name ∈ binder.toList, name ∈ table) ∧ Covered table body :=
  ⟨fun name member => covered name (by simp [names, member]),
    fun name member => covered name (by simp [names, member])⟩

theorem covered_multiLambda {table : List String} {arity : Nat} {binders : List String} {body : Pattern}
    (covered : Covered table (.multiLambda arity binders body)) :
    (∀ name ∈ binders, name ∈ table) ∧ Covered table body :=
  ⟨fun name member => covered name (by simp [names, member]),
    fun name member => covered name (by simp [names, member])⟩

theorem covered_subst {table : List String} {body replacement : Pattern}
    (covered : Covered table (.subst body replacement)) : Covered table body ∧ Covered table replacement :=
  ⟨fun name member => covered name (by simp [names, member]),
    fun name member => covered name (by simp [names, member])⟩

theorem covered_collection {table : List String} {kind : CollType} {elements : List Pattern} {rest : Option String}
    (covered : Covered table (.collection kind elements rest)) :
    (∀ element ∈ elements, Covered table element) ∧ ∀ name ∈ rest.toList, name ∈ table :=
  ⟨covered_elements.mp fun name member => covered name (by simp [names, member]),
    fun name member => covered name (by simp [names, member])⟩

/-! ### Two patterns -/

theorem ordering_then_lt (second : Ordering) : Ordering.lt.then second = .lt := rfl
theorem ordering_then_gt (second : Ordering) : Ordering.gt.then second = .gt := rfl

/-- Different tags: the tags decide. -/
theorem cmp_of_tags (state : State) (table : List String) {left right : Pattern} (different : tag left ≠ tag right) :
    CmpAt state table left right := by
  have leftTag := tag_returns state left
  have rightTag := tag_returns state right
  have ordered := nat_cmp_returns state (tag left) (tag right)
  rw [CmpAt, CanonicalCompare.cmp_of_tag different]
  canonical_eval [leftTag, rightTag, ordered] unfolding [different]

/-- The same tag: `gslt:canon:cmp-same` decides. -/
theorem cmp_of_same (state : State) (table : List String) {left right : Pattern} (same : tag left = tag right)
    (decided : PureReturns canonicalLibrary.runtime [] state
      (apply "gslt:canon:cmp-same" [tableValue table, patternValue left, patternValue right]) state
      (orderingValue (cmp table left right))) :
    CmpAt state table left right := by
  have leftTag := tag_returns state left
  have rightTag := tag_returns state right
  canonical_eval [leftTag, rightTag, decided] unfolding [CmpAt, same]

/-- The comparison core is a literal slice of the pinned canonical source. -/
private def cmpProofHeads (head : String) : Bool :=
  !head.startsWith "gslt:" || ["gslt:canon:nat-cmp", "gslt:canon:name-scan", "gslt:canon:name-cmp", "gslt:canon:length-cmp", "gslt:canon:names-pairwise", "gslt:canon:names-cmp", "gslt:canon:binder-cmp", "gslt:canon:rest-cmp", "gslt:canon:tag", "gslt:canon:kind-tag", "gslt:canon:unordered", "gslt:canon:cmp", "gslt:canon:cmp-same", "gslt:canon:cmp-counted", "gslt:canon:cmp-pairwise"].contains head

private def cmpProofSource : SpaceSemantics.Program where
  equations := canonicalSource.program.equations.take 15
  declarations := canonicalSource.program.declarations.take 15
  layout := List.replicate 15 .equation ++ List.replicate 15 .declaration

private def cmpProofLibrary : BridgeKit.Library :=
  ⟨{ equations := [], declarations := [] }, cmpProofSource, ["gslt:"]⟩

private local instance cmpProofEquationEq : DecidableEq SpaceSemantics.Equation := by
  intro left right
  apply decidable_of_iff (left.head = right.head ∧
    left.arguments = right.arguments ∧ left.body = right.body)
  constructor
  · rintro ⟨head, arguments, body⟩
    cases left
    cases right
    cases head
    cases arguments
    cases body
    rfl
  · intro same
    cases same
    exact ⟨rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
private theorem cmpProof_equations : cmpProofLibrary.runtime.equations =
    RuleExecutionProgram.interpretedPremiseProgram.equations.filter (fun row => cmpProofHeads row.head) := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem cmpProof_declarations : cmpProofLibrary.runtime.declarations =
    RuleExecutionProgram.interpretedPremiseProgram.declarations.filter (retainedCallDeclaration cmpProofHeads) := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem cmpProof_checked : cmpProofLibrary.check = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem cmpProof_closed : ProgramClosed cmpProofHeads cmpProofLibrary.runtime := by
  apply closed_of_all _ _ (by decide +kernel)
  decide +kernel

private theorem cmpProof_agreement : ProgramAgreementOn cmpProofHeads
    cmpProofLibrary.runtime RuleExecutionProgram.interpretedPremiseProgram :=
  fragment_agreement _ _ cmpProof_equations cmpProof_declarations (fun _ kept => kept)

private theorem cmpProof_raw_closed : ProgramClosed cmpProofHeads RuleExecutionProgram.interpretedPremiseProgram where
  binding := cmpProof_closed.binding
  bodies := by
    intro equation member kept
    have selected : equation ∈ cmpProofLibrary.runtime.equations := by
      rw [cmpProof_equations]
      exact List.mem_filter.mpr ⟨member, kept⟩
    exact cmpProof_closed.bodies equation selected kept

private theorem cmpProof_reverse : ProgramAgreementOn cmpProofHeads
    RuleExecutionProgram.interpretedPremiseProgram cmpProofLibrary.runtime where
  dispatch head kept := (cmpProof_agreement.dispatch head kept).symm
  demand head index kept := (cmpProof_agreement.demand head index kept).symm
  bodies head values kept := (cmpProof_agreement.bodies head values kept).symm

syntax "cmp_fragment_eval" (" [" term,* "]")? (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| cmp_fragment_eval $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (metta_call cmpProof_checked; metta_eval [$facts,*] with cmpProof_checked
      unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?, pattern_symbol_unmatched,
        orderingValue, orderingTerm, tableValue, $extra,*]))

private theorem cmp_native_nat_cmp_returns (state : State) (left right : Nat) :
    PureReturns cmpProofLibrary.runtime [] state (apply "gslt:canon:nat-cmp" [number left, number right]) state
      (orderingValue (compare left right))  := by
  exact transport_call cmpProof_raw_closed cmpProof_reverse
    (by decide +kernel) (by decide) (by decide +kernel) (by decide)
    ["left", "right"] (by decide) rfl (by decide +kernel)
    (nat_cmp_returns state left right)

private theorem cmp_native_name_cmp_returns (state : State) (table : List String) (left right : String)
    (found : left ∈ table ∧ right ∈ table) :
    PureReturns cmpProofLibrary.runtime [] state
      (apply "gslt:canon:name-cmp" [tableValue table, encoded (.string left), encoded (.string right)]) state
      (orderingValue (nameCmp table left right))  := by
  exact transport_call cmpProof_raw_closed cmpProof_reverse
    (by decide +kernel) (by decide) (by decide +kernel) (by decide)
    ["names", "left", "right"] (by decide) rfl (by decide +kernel)
    (name_cmp_returns state table left right found)

private theorem cmp_native_patterns_length_cmp_returns (state : State) (left right : List Pattern) :
    PureReturns cmpProofLibrary.runtime [] state
      (apply "gslt:canon:length-cmp" [patternsValue left, patternsValue right]) state
      (orderingValue (compare left.length right.length))  := by
  exact transport_call cmpProof_raw_closed cmpProof_reverse
    (by decide +kernel) (by decide) (by decide +kernel) (by decide)
    ["left", "right"] (by decide) rfl (by decide +kernel)
    (patterns_length_cmp_returns state left right)

private theorem cmp_native_names_cmp_returns (state : State) (table : List String) (left right : List String)
    (leftIn : ∀ name ∈ left, name ∈ table) (rightIn : ∀ name ∈ right, name ∈ table) :
    PureReturns cmpProofLibrary.runtime [] state
      (apply "gslt:canon:names-cmp" [tableValue table, encoded (CettaWire.encodeList Term.string left),
        encoded (CettaWire.encodeList Term.string right)]) state
      (orderingValue (namesCmp table left right))  := by
  exact transport_call cmpProof_raw_closed cmpProof_reverse
    (by decide +kernel) (by decide) (by decide +kernel) (by decide)
    ["names", "left", "right"] (by decide) rfl (by decide +kernel)
    (names_cmp_returns state table left right leftIn rightIn)

private theorem cmp_native_binder_cmp_returns (state : State) (table : List String) (left right : Option String)
    (leftIn : ∀ name ∈ left.toList, name ∈ table) (rightIn : ∀ name ∈ right.toList, name ∈ table) :
    PureReturns cmpProofLibrary.runtime [] state
      (apply "gslt:canon:binder-cmp" [tableValue table, encoded (encodeBinder left), encoded (encodeBinder right)])
      state (orderingValue (optCmp table left right))  := by
  exact transport_call cmpProof_raw_closed cmpProof_reverse
    (by decide +kernel) (by decide) (by decide +kernel) (by decide)
    ["names", "left", "right"] (by decide) rfl (by decide +kernel)
    (binder_cmp_returns state table left right leftIn rightIn)

private theorem cmp_native_rest_cmp_returns (state : State) (table : List String) (left right : Option String)
    (leftIn : ∀ name ∈ left.toList, name ∈ table) (rightIn : ∀ name ∈ right.toList, name ∈ table) :
    PureReturns cmpProofLibrary.runtime [] state
      (apply "gslt:canon:rest-cmp" [tableValue table, encoded (encodeRest left), encoded (encodeRest right)])
      state (orderingValue (optCmp table left right))  := by
  exact transport_call cmpProof_raw_closed cmpProof_reverse
    (by decide +kernel) (by decide) (by decide +kernel) (by decide)
    ["names", "left", "right"] (by decide) rfl (by decide +kernel)
    (rest_cmp_returns state table left right leftIn rightIn)

private theorem cmp_native_tag_returns (state : State) (pattern : Pattern) :
    PureReturns cmpProofLibrary.runtime [] state (apply "gslt:canon:tag" [patternValue pattern]) state
      (number (tag pattern))  := by
  exact transport_call cmpProof_raw_closed cmpProof_reverse
    (by decide +kernel) (by decide) (by decide +kernel) (by decide)
    ["pattern"] (by decide) rfl (by decide +kernel)
    (tag_returns state pattern)

private theorem cmp_native_kind_tag_returns (state : State) (kind : CollType) :
    PureReturns cmpProofLibrary.runtime [] state (apply "gslt:canon:kind-tag" [encoded (encodeCollectionType kind)])
      state (number (collectionTag kind))  := by
  exact transport_call cmpProof_raw_closed cmpProof_reverse
    (by decide +kernel) (by decide) (by decide +kernel) (by decide)
    ["kind"] (by decide) rfl (by decide +kernel)
    (kind_tag_returns state kind)

/-- What `gslt:canon:cmp` returns. -/
private abbrev CmpProofAt (state : State) (table : List String) (left right : Pattern) : Prop :=
  PureReturns cmpProofLibrary.runtime [] state
    (apply "gslt:canon:cmp" [tableValue table, patternValue left, patternValue right]) state
    (orderingValue (cmp table left right))

/-- What `gslt:canon:cmp-pairwise` returns. -/
private abbrev CmpProofPairwiseAt (state : State) (table : List String) (left right : List Pattern) : Prop :=
  PureReturns cmpProofLibrary.runtime [] state
    (apply "gslt:canon:cmp-pairwise" [tableValue table, patternsValue left, patternsValue right]) state
    (orderingValue (cmpList table left right))

/-- What `gslt:canon:cmp-counted` returns. -/
private abbrev CmpProofCountedAt (state : State) (table : List String) (left right : List Pattern) : Prop :=
  PureReturns cmpProofLibrary.runtime [] state
    (apply "gslt:canon:cmp-counted" [tableValue table, patternsValue left, patternsValue right]) state
    (orderingValue ((compare left.length right.length).then (cmpList table left right)))

private theorem cmp_proof_pairwise_of (state : State) (table : List String) : ∀ left : List Pattern,
    (∀ pattern ∈ left, ∀ other, Covered table pattern → Covered table other → CmpProofAt state table pattern other) →
    ∀ right : List Pattern, left.length = right.length → (∀ pattern ∈ left, Covered table pattern) →
      (∀ pattern ∈ right, Covered table pattern) → CmpProofPairwiseAt state table left right
  | [], _, [], _, _, _ => by cmp_fragment_eval unfolding [CmpProofPairwiseAt, cmpList, patternsValue, encodePatterns]
  | [], _, _ :: _, lengths, _, _ => by simp at lengths
  | _ :: _, _, [], lengths, _, _ => by simp at lengths
  | first :: lefts, each, other :: rights, lengths, leftIn, rightIn => by
    have here := each first (by simp) other (leftIn first (by simp)) (rightIn other (by simp))
    have later := cmp_proof_pairwise_of state table lefts (fun pattern member => each pattern (by simp [member])) rights
      (by simpa using lengths) (fun pattern member => leftIn pattern (by simp [member]))
      (fun pattern member => rightIn pattern (by simp [member]))
    cases ordering : cmp table first other with
    | lt =>
      rw [CmpProofAt, ordering] at here
      cmp_fragment_eval [here] unfolding [CmpProofPairwiseAt, cmpList, ordering, patternsValue, patternValue, encodePatterns]
    | eq =>
      rw [CmpProofAt, ordering] at here
      cmp_fragment_eval [here, later]
        unfolding [CmpProofPairwiseAt, cmpList, ordering, eq_then, patternsValue, patternValue, encodePatterns]
    | gt =>
      rw [CmpProofAt, ordering] at here
      cmp_fragment_eval [here] unfolding [CmpProofPairwiseAt, cmpList, ordering, patternsValue, patternValue, encodePatterns]

private theorem cmp_proof_counted_of (state : State) (table : List String) (left right : List Pattern)
    (each : ∀ pattern ∈ left, ∀ other, Covered table pattern → Covered table other → CmpProofAt state table pattern other)
    (leftIn : ∀ pattern ∈ left, Covered table pattern) (rightIn : ∀ pattern ∈ right, Covered table pattern) :
    CmpProofCountedAt state table left right := by
  have lengths := cmp_native_patterns_length_cmp_returns state left right
  by_cases same : left.length = right.length
  · have pairwise := cmp_proof_pairwise_of state table left each right same leftIn rightIn
    rw [same, compare_refl] at lengths
    cmp_fragment_eval [lengths, pairwise] unfolding [CmpProofCountedAt, CmpProofPairwiseAt, same, compare_refl, eq_then]
  · cases ordering : compare left.length right.length with
    | lt => rw [ordering] at lengths; cmp_fragment_eval [lengths] unfolding [CmpProofCountedAt, ordering]
    | eq => exact absurd (Nat.compare_eq_eq.mp ordering) same
    | gt => rw [ordering] at lengths; cmp_fragment_eval [lengths] unfolding [CmpProofCountedAt, ordering]

/-- Different tags: the tags decide. -/
private theorem cmp_proof_of_tags (state : State) (table : List String) {left right : Pattern} (different : tag left ≠ tag right) :
    CmpProofAt state table left right := by
  have leftTag := cmp_native_tag_returns state left
  have rightTag := cmp_native_tag_returns state right
  have ordered := cmp_native_nat_cmp_returns state (tag left) (tag right)
  rw [CmpProofAt, CanonicalCompare.cmp_of_tag different]
  cmp_fragment_eval [leftTag, rightTag, ordered] unfolding [different]

/-- The same tag: `gslt:canon:cmp-same` decides. -/
private theorem cmp_proof_of_same (state : State) (table : List String) {left right : Pattern} (same : tag left = tag right)
    (decided : PureReturns cmpProofLibrary.runtime [] state
      (apply "gslt:canon:cmp-same" [tableValue table, patternValue left, patternValue right]) state
      (orderingValue (cmp table left right))) :
    CmpProofAt state table left right := by
  have leftTag := cmp_native_tag_returns state left
  have rightTag := cmp_native_tag_returns state right
  cmp_fragment_eval [leftTag, rightTag, decided] unfolding [CmpProofAt, same]

/-- **`gslt:canon:cmp` is `CanonicalCompare.cmp`** on covered patterns. -/
private theorem cmp_proof_returns (state : State) (table : List String) (left : Pattern) :
    ∀ right, Covered table left → Covered table right → CmpProofAt state table left right := by
  induction left using Pattern.inductionOn with
  | hbvar index =>
    intro right _ _
    by_cases same : tag (.bvar index) = tag right
    · apply cmp_proof_of_same state table same
      cases right with
      | bvar other =>
        have ordered := cmp_native_nat_cmp_returns state index other
        cmp_fragment_eval [ordered] unfolding [CanonicalCompare.cmp, patternValue, encodePattern]
      | _ => simp [tag] at same
    · exact cmp_proof_of_tags state table same
  | hfvar name =>
    intro right leftIn rightIn
    by_cases same : tag (.fvar name) = tag right
    · apply cmp_proof_of_same state table same
      cases right with
      | fvar other =>
        have names := cmp_native_name_cmp_returns state table name other
          ⟨leftIn name (by simp [CanonicalCompare.names]), rightIn other (by simp [CanonicalCompare.names])⟩
        cmp_fragment_eval [names] unfolding [CanonicalCompare.cmp, patternValue, encodePattern]
      | _ => simp [tag] at same
    · exact cmp_proof_of_tags state table same
  | happly label arguments ih =>
    intro right leftIn rightIn
    by_cases same : tag (.apply label arguments) = tag right
    · apply cmp_proof_of_same state table same
      cases right with
      | apply other others =>
        obtain ⟨labelIn, argumentsIn⟩ := covered_apply leftIn
        obtain ⟨otherIn, othersIn⟩ := covered_apply rightIn
        have names := cmp_native_name_cmp_returns state table label other ⟨labelIn, otherIn⟩
        have counted := cmp_proof_counted_of state table arguments others ih argumentsIn othersIn
        cases ordering : nameCmp table label other with
        | eq =>
          rw [ordering] at names
          cmp_fragment_eval [names, counted]
            unfolding [CanonicalCompare.cmp, ordering, eq_then, CmpProofCountedAt, patternValue, patternsValue, encodePattern]
        | lt =>
          rw [ordering] at names
          cmp_fragment_eval [names] unfolding [CanonicalCompare.cmp, ordering, ordering_then_lt, patternValue, encodePattern]
        | gt =>
          rw [ordering] at names
          cmp_fragment_eval [names] unfolding [CanonicalCompare.cmp, ordering, ordering_then_gt, patternValue, encodePattern]
      | _ => simp [tag] at same
    · exact cmp_proof_of_tags state table same
  | hlambda binder body ih =>
    intro right leftIn rightIn
    by_cases same : tag (.lambda binder body) = tag right
    · apply cmp_proof_of_same state table same
      cases right with
      | lambda other otherBody =>
        obtain ⟨binderIn, bodyIn⟩ := covered_lambda leftIn
        obtain ⟨otherIn, otherBodyIn⟩ := covered_lambda rightIn
        have binders := cmp_native_binder_cmp_returns state table binder other binderIn otherIn
        have bodies := ih otherBody bodyIn otherBodyIn
        cases ordering : optCmp table binder other with
        | eq =>
          rw [ordering] at binders
          cmp_fragment_eval [binders, bodies] unfolding [CanonicalCompare.cmp, ordering, eq_then, CmpProofAt, patternValue, encodePattern]
        | lt =>
          rw [ordering] at binders
          cmp_fragment_eval [binders] unfolding [CanonicalCompare.cmp, ordering, ordering_then_lt, patternValue, encodePattern]
        | gt =>
          rw [ordering] at binders
          cmp_fragment_eval [binders] unfolding [CanonicalCompare.cmp, ordering, ordering_then_gt, patternValue, encodePattern]
      | _ => simp [tag] at same
    · exact cmp_proof_of_tags state table same
  | hmultiLambda arity binders body ih =>
    intro right leftIn rightIn
    by_cases same : tag (.multiLambda arity binders body) = tag right
    · apply cmp_proof_of_same state table same
      cases right with
      | multiLambda otherArity otherBinders otherBody =>
        obtain ⟨bindersIn, bodyIn⟩ := covered_multiLambda leftIn
        obtain ⟨otherBindersIn, otherBodyIn⟩ := covered_multiLambda rightIn
        have arities := cmp_native_nat_cmp_returns state arity otherArity
        have namesCompared := cmp_native_names_cmp_returns state table binders otherBinders bindersIn otherBindersIn
        have bodies := ih otherBody bodyIn otherBodyIn
        cases byArity : compare arity otherArity with
        | eq =>
          rw [byArity] at arities
          cases byBinders : namesCmp table binders otherBinders with
          | eq =>
            rw [byBinders] at namesCompared
            cmp_fragment_eval [arities, namesCompared, bodies]
              unfolding [CanonicalCompare.cmp, byArity, byBinders, eq_then, CmpProofAt, patternValue, encodePattern,
                InferenceCettaWire.encodeList]
          | lt =>
            rw [byBinders] at namesCompared
            cmp_fragment_eval [arities, namesCompared]
              unfolding [CanonicalCompare.cmp, byArity, byBinders, eq_then, ordering_then_lt, patternValue, encodePattern,
                InferenceCettaWire.encodeList]
          | gt =>
            rw [byBinders] at namesCompared
            cmp_fragment_eval [arities, namesCompared]
              unfolding [CanonicalCompare.cmp, byArity, byBinders, eq_then, ordering_then_gt, patternValue, encodePattern,
                InferenceCettaWire.encodeList]
        | lt =>
          rw [byArity] at arities
          cmp_fragment_eval [arities] unfolding [CanonicalCompare.cmp, byArity, ordering_then_lt, patternValue, encodePattern]
        | gt =>
          rw [byArity] at arities
          cmp_fragment_eval [arities] unfolding [CanonicalCompare.cmp, byArity, ordering_then_gt, patternValue, encodePattern]
      | _ => simp [tag] at same
    · exact cmp_proof_of_tags state table same
  | hsubst body replacement bodyIH replacementIH =>
    intro right leftIn rightIn
    by_cases same : tag (.subst body replacement) = tag right
    · apply cmp_proof_of_same state table same
      cases right with
      | subst otherBody otherReplacement =>
        obtain ⟨bodyIn, replacementIn⟩ := covered_subst leftIn
        obtain ⟨otherBodyIn, otherReplacementIn⟩ := covered_subst rightIn
        have bodies := bodyIH otherBody bodyIn otherBodyIn
        have replacements := replacementIH otherReplacement replacementIn otherReplacementIn
        cases ordering : cmp table body otherBody with
        | eq =>
          rw [CmpProofAt, ordering] at bodies
          cmp_fragment_eval [bodies, replacements] unfolding [CanonicalCompare.cmp, ordering, eq_then, CmpProofAt, patternValue, encodePattern]
        | lt =>
          rw [CmpProofAt, ordering] at bodies
          cmp_fragment_eval [bodies] unfolding [CanonicalCompare.cmp, ordering, ordering_then_lt, patternValue, encodePattern]
        | gt =>
          rw [CmpProofAt, ordering] at bodies
          cmp_fragment_eval [bodies] unfolding [CanonicalCompare.cmp, ordering, ordering_then_gt, patternValue, encodePattern]
      | _ => simp [tag] at same
    · exact cmp_proof_of_tags state table same
  | hcollection kind elements rest ih =>
    intro right leftIn rightIn
    by_cases same : tag (.collection kind elements rest) = tag right
    · apply cmp_proof_of_same state table same
      cases right with
      | collection otherKind others otherRest =>
        obtain ⟨elementsIn, restIn⟩ := covered_collection leftIn
        obtain ⟨othersIn, otherRestIn⟩ := covered_collection rightIn
        have kindTag := cmp_native_kind_tag_returns state kind
        have otherKindTag := cmp_native_kind_tag_returns state otherKind
        have kinds := cmp_native_nat_cmp_returns state (collectionTag kind) (collectionTag otherKind)
        have counted := cmp_proof_counted_of state table elements others ih elementsIn othersIn
        have rests := cmp_native_rest_cmp_returns state table rest otherRest restIn otherRestIn
        cases byKind : compare (collectionTag kind) (collectionTag otherKind) with
        | eq =>
          rw [byKind] at kinds
          cases byElements : (compare elements.length others.length).then (cmpList table elements others) with
          | eq =>
            rw [CmpProofCountedAt, byElements] at counted
            have shape : CanonicalCompare.cmp table (.collection kind elements rest) (.collection otherKind others otherRest) =
                optCmp table rest otherRest := by
              simp only [CanonicalCompare.cmp, byKind, eq_then, ← then_assoc, byElements]
            rw [shape]
            cmp_fragment_eval [kindTag, otherKindTag, kinds, counted, rests] unfolding [patternValue, patternsValue, encodePattern]
          | lt =>
            rw [CmpProofCountedAt, byElements] at counted
            have shape : CanonicalCompare.cmp table (.collection kind elements rest) (.collection otherKind others otherRest) =
                .lt := by
              simp only [CanonicalCompare.cmp, byKind, eq_then, ← then_assoc, byElements, ordering_then_lt]
            rw [shape]
            cmp_fragment_eval [kindTag, otherKindTag, kinds, counted] unfolding [patternValue, patternsValue, encodePattern]
          | gt =>
            rw [CmpProofCountedAt, byElements] at counted
            have shape : CanonicalCompare.cmp table (.collection kind elements rest) (.collection otherKind others otherRest) =
                .gt := by
              simp only [CanonicalCompare.cmp, byKind, eq_then, ← then_assoc, byElements, ordering_then_gt]
            rw [shape]
            cmp_fragment_eval [kindTag, otherKindTag, kinds, counted] unfolding [patternValue, patternsValue, encodePattern]
        | lt =>
          rw [byKind] at kinds
          cmp_fragment_eval [kindTag, otherKindTag, kinds]
            unfolding [CanonicalCompare.cmp, byKind, ordering_then_lt, patternValue, encodePattern]
        | gt =>
          rw [byKind] at kinds
          cmp_fragment_eval [kindTag, otherKindTag, kinds]
            unfolding [CanonicalCompare.cmp, byKind, ordering_then_gt, patternValue, encodePattern]
      | _ => simp [tag] at same
    · exact cmp_proof_of_tags state table same

theorem cmp_returns (state : State) (table : List String) (left : Pattern) :
    ∀ right, Covered table left → Covered table right → CmpAt state table left right  := by
  intro right leftIn rightIn
  exact transport_call cmpProof_closed cmpProof_agreement
    (by decide +kernel) (by decide) (by decide +kernel) (by decide)
    ["names", "left", "right"] (by decide) rfl (by decide +kernel)
    (cmp_proof_returns state table left right leftIn rightIn)

/-! ## Sorting -/

@[metta_head "gslt:canon:insert"]
theorem insert_returns (state : State) (table : List String) (pattern : Pattern) (patternIn : Covered table pattern) :
    ∀ sorted : List Pattern, (∀ other ∈ sorted, Covered table other) →
      PureReturns canonicalLibrary.runtime [] state
        (apply "gslt:canon:insert" [tableValue table, patternValue pattern, patternsValue sorted]) state
        (patternsValue (sorted.orderedInsert (CmpLe table) pattern))
  | [], _ => by canonical_eval unfolding [List.orderedInsert, patternsValue, encodePatterns]
  | first :: rest, covered => by
    have ordered := cmp_returns state table pattern first patternIn (covered first (by simp))
    have later := insert_returns state table pattern patternIn rest (fun other member => covered other (by simp [member]))
    cases ordering : cmp table pattern first with
    | gt =>
      rw [CmpAt, ordering] at ordered
      canonical_eval [ordered, later]
        unfolding [List.orderedInsert, CmpLe, ordering, patternsValue, patternValue, encodePatterns]
    | lt =>
      rw [CmpAt, ordering] at ordered
      canonical_eval [ordered] unfolding [List.orderedInsert, CmpLe, ordering, patternsValue, patternValue, encodePatterns]
    | eq =>
      rw [CmpAt, ordering] at ordered
      canonical_eval [ordered] unfolding [List.orderedInsert, CmpLe, ordering, patternsValue, patternValue, encodePatterns]

@[metta_head "gslt:canon:sort"]
theorem sort_returns (state : State) (table : List String) : ∀ patterns : List Pattern,
    (∀ pattern ∈ patterns, Covered table pattern) →
    PureReturns canonicalLibrary.runtime [] state
      (apply "gslt:canon:sort" [tableValue table, patternsValue patterns]) state
      (patternsValue (sortBy table patterns))
  | [], _ => by canonical_eval unfolding [sortBy, List.insertionSort_nil, patternsValue, encodePatterns]
  | first :: rest, covered => by
    have later := sort_returns state table rest (fun pattern member => covered pattern (by simp [member]))
    have inserted := insert_returns state table first (covered first (by simp)) (sortBy table rest)
      (fun pattern member => covered pattern (by simp [(List.perm_insertionSort _ rest).mem_iff.mp member]))
    canonical_eval [later, inserted] unfolding [sortBy, List.insertionSort_cons, patternsValue, patternValue, encodePatterns]

/-! ## Sets -/

@[metta_head "gslt:canon:is-set"]
theorem is_set_returns (state : State) (kind : CollType) :
    PureReturns canonicalLibrary.runtime [] state (apply "gslt:canon:is-set" [encoded (encodeCollectionType kind)])
      state (Effects.boolean (decide (kind = .hashSet))) := by
  have sameKind : decide (kind = .hashSet) =
      decide (encodeCollectionType kind = .string "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashSet") := by
    cases kind <;> simp [encodeCollectionType]
  rw [sameKind]
  cases kind <;> canonical_eval unfolding [encodeCollectionType]

/-- A sorted list's elements once each: equal elements are adjacent, so each run keeps its last member. -/
def dedupSorted : List Pattern → List Pattern
  | [] => []
  | [item] => [item]
  | first :: second :: rest =>
    if first = second then dedupSorted (second :: rest) else first :: dedupSorted (second :: rest)

/-- On a list sorted by the lexicographic order, `dedupSorted` is `List.dedup`. -/
theorem dedupSorted_eq_dedup : ∀ {items : List Pattern}, items.Pairwise PatternLe → dedupSorted items = items.dedup
  | [], _ => rfl
  | [item], _ => by rw [dedupSorted, (List.nodup_singleton item).dedup]
  | first :: second :: rest, sorted => by
    have tail := dedupSorted_eq_dedup (List.pairwise_cons.mp sorted).2
    by_cases same : first = second
    · subst same
      rw [dedupSorted, if_pos rfl, tail, List.dedup_cons_of_mem (List.mem_cons_self ..)]
    · have absent : first ∉ second :: rest := by
        intro member
        rcases List.mem_cons.mp member with equal | later
        · exact same equal
        · exact same (antisymm ((List.pairwise_cons.mp sorted).1 second (List.mem_cons_self ..))
            ((List.pairwise_cons.mp (List.pairwise_cons.mp sorted).2).1 first later))
      rw [dedupSorted, if_neg same, tail, List.dedup_cons_of_notMem absent]

@[metta_head "gslt:canon:dedup-sorted"]
theorem dedup_sorted_returns (state : State) : ∀ items : List Pattern,
    PureReturns canonicalLibrary.runtime [] state (apply "gslt:canon:dedup-sorted" [patternsValue items]) state
      (patternsValue (dedupSorted items))
  | [] => by canonical_eval unfolding [dedupSorted, patternsValue, encodePatterns]
  | [item] => by canonical_eval unfolding [dedupSorted, patternsValue, encodePatterns]
  | first :: second :: rest => by
    have tail := dedup_sorted_returns state (second :: rest)
    by_cases same : first = second
    · subst same
      canonical_eval [tail] unfolding [dedupSorted, patternsValue, encodePatterns]
    · have different : encodePattern first ≠ encodePattern second :=
        fun equal => same (InferenceCettaWire.encodePattern_injective equal)
      canonical_eval [tail] unfolding [dedupSorted, same, different, patternsValue, encodePatterns]

/-! ## The canonical form -/

/-- What `gslt:canon:canon` returns. -/
abbrev CanonAt (state : State) (table : List String) (pattern : Pattern) : Prop :=
  PureReturns canonicalLibrary.runtime [] state (apply "gslt:canon:canon" [tableValue table, patternValue pattern])
    state (patternValue (canonBy table pattern))

@[metta_head "gslt:canon:canon-list"]
theorem canon_list_of (state : State) (table : List String) : ∀ patterns : List Pattern,
    (∀ pattern ∈ patterns, CanonAt state table pattern) →
    PureReturns canonicalLibrary.runtime [] state
      (apply "gslt:canon:canon-list" [tableValue table, patternsValue patterns]) state
      (patternsValue (patterns.map (canonBy table)))
  | [], _ => by canonical_eval unfolding [patternsValue, encodePatterns]
  | pattern :: rest, each => by
    have here := each pattern (by simp)
    have later := canon_list_of state table rest (fun other member => each other (by simp [member]))
    canonical_eval [here, later] unfolding [CanonAt, patternsValue, patternValue, encodePatterns, List.map_cons]

theorem canonBy_collection (table : List String) (kind : CollType) (elements : List Pattern) (rest : Option String) :
    canonBy table (.collection kind elements rest) =
      .collection kind (arrangeBy table kind (elements.map (canonBy table))) rest := by
  rw [canonBy]

/-- **`gslt:canon:canon` is the canonical form sorted by the table** on covered patterns. -/
theorem canon_by_returns (state : State) {table : List String} (ordered : NameOrdered table) (pattern : Pattern)
    (covered : Covered table pattern) : CanonAt state table pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => canonical_eval unfolding [CanonAt, canonBy, patternValue, encodePattern]
  | hfvar name => canonical_eval unfolding [CanonAt, canonBy, patternValue, encodePattern]
  | happly label arguments ih =>
    have inner := canon_list_of state table arguments
      (fun argument member => ih argument member ((covered_apply covered).2 argument member))
    canonical_eval [inner] unfolding [CanonAt, canonBy, patternValue, patternsValue, encodePattern]
  | hlambda binder body ih =>
    have inner := ih (covered_lambda covered).2
    canonical_eval [inner] unfolding [CanonAt, canonBy, patternValue, encodePattern]
  | hmultiLambda arity binders body ih =>
    have inner := ih (covered_multiLambda covered).2
    canonical_eval [inner] unfolding [CanonAt, canonBy, patternValue, encodePattern]
  | hsubst body replacement bodyIH replacementIH =>
    have first := bodyIH (covered_subst covered).1
    have second := replacementIH (covered_subst covered).2
    canonical_eval [first, second] unfolding [CanonAt, canonBy, patternValue, encodePattern]
  | hcollection kind elements rest ih =>
    obtain ⟨elementsIn, _⟩ := covered_collection covered
    have inner := canon_list_of state table elements (fun element member => ih element member (elementsIn element member))
    have innerCovered : ∀ element ∈ elements.map (canonBy table), Covered table element := by
      intro changed member
      obtain ⟨element, elementIn, rfl⟩ := List.mem_map.mp member
      rw [(canonBy_eq_canon ordered element (elementsIn element elementIn)).1]
      exact (canonBy_eq_canon ordered element (elementsIn element elementIn)).2
    have sorted := sort_returns state table (elements.map (canonBy table)) innerCovered
    have pairwise : (sortBy table (elements.map (canonBy table))).Pairwise PatternLe := by
      rw [sortBy_eq_sortLex ordered innerCovered]
      exact sortLex_pairwise _
    have deduped := dedup_sorted_returns state (sortBy table (elements.map (canonBy table)))
    rw [dedupSorted_eq_dedup pairwise] at deduped
    cases kind with
    | vec =>
      have unordered : PureReturns canonicalLibrary.runtime [] state
          (apply "gslt:canon:unordered" [encoded (encodeCollectionType .vec)]) state (Effects.boolean false) :=
        unordered_returns state .vec
      canonical_eval [inner, unordered]
        unfolding [CanonAt, canonBy_collection, arrangeBy, patternValue, patternsValue, encodePattern]
    | hashBag =>
      have unordered : PureReturns canonicalLibrary.runtime [] state
          (apply "gslt:canon:unordered" [encoded (encodeCollectionType .hashBag)]) state (Effects.boolean true) :=
        unordered_returns state .hashBag
      have isSet : PureReturns canonicalLibrary.runtime [] state
          (apply "gslt:canon:is-set" [encoded (encodeCollectionType .hashBag)]) state (Effects.boolean false) :=
        is_set_returns state .hashBag
      canonical_eval [inner, unordered, sorted, isSet]
        unfolding [CanonAt, canonBy_collection, arrangeBy, patternValue, patternsValue, encodePattern]
    | hashSet =>
      have unordered : PureReturns canonicalLibrary.runtime [] state
          (apply "gslt:canon:unordered" [encoded (encodeCollectionType .hashSet)]) state (Effects.boolean true) :=
        unordered_returns state .hashSet
      have isSet : PureReturns canonicalLibrary.runtime [] state
          (apply "gslt:canon:is-set" [encoded (encodeCollectionType .hashSet)]) state (Effects.boolean true) :=
        is_set_returns state .hashSet
      canonical_eval [inner, unordered, sorted, isSet, deduped]
        unfolding [CanonAt, canonBy_collection, arrangeBy, patternValue, patternsValue, encodePattern]

/-- **`gslt:canon:canon` is `CanonicalBags.canon`** on covered patterns. -/
@[metta_head "gslt:canon:canon"]
theorem canon_returns (state : State) {table : List String} (ordered : NameOrdered table) (pattern : Pattern)
    (covered : Covered table pattern) :
    PureReturns canonicalLibrary.runtime [] state (apply "gslt:canon:canon" [tableValue table, patternValue pattern])
      state (patternValue (canon pattern)) := by
  rw [← (canonBy_eq_canon ordered pattern covered).1]
  exact canon_by_returns state ordered pattern covered

/-- **`gslt:canon:canonical` is the standard form followed by the canonical form.** -/
@[metta_head "gslt:canon:canonical"]
theorem canonical_returns (state : State) {table : List String} (ordered : NameOrdered table) (laws : List Laws)
    (extrusions : List Extrusion) (pattern : Pattern) (covered : Covered table pattern) :
    PureReturns canonicalLibrary.runtime [] state
      (apply "gslt:canon:canonical" [tableValue table, lawsValue laws, extrusionsValue extrusions, patternValue pattern])
      state (patternValue (canon (standardForm laws extrusions pattern))) := by
  have standard := standard_returns state laws extrusions pattern
  have canonical := canon_returns state ordered (standardForm laws extrusions pattern)
    (covered_standardForm laws extrusions covered)
  canonical_eval [standard, canonical] unfolding [lawsValue, extrusionsValue]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.nat_cmp_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.name_scan_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.name_cmp_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.length_cmp_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.patterns_length_cmp_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.names_pairwise_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.names_cmp_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.binder_cmp_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.rest_cmp_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.tag_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.kind_tag_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.unordered_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.cmp_pairwise_of
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.cmp_counted_of
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.then_cases
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.covered_apply
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.covered_lambda
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.covered_multiLambda
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.covered_subst
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.covered_collection
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.ordering_then_lt
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.ordering_then_gt
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.cmp_of_tags
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.cmp_of_same
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.cmp_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.insert_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.sort_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.is_set_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.dedupSorted_eq_dedup
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.dedup_sorted_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.canon_list_of
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.canonBy_collection
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.canon_by_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.canon_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.canonical_returns

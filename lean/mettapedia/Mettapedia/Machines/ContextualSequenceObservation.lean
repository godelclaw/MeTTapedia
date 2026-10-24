import Mettapedia.Machines.SubstitutionFold
import Mettapedia.Machines.ReadOnlyQuery
import Mathlib.Tactic

/-!
# Structural projection through a lexical value

Root alias resolution may enter a different lexical frame. Projection keeps
that frame for the selected child or suffix. The independent full-image
relation substitutes every child, including unbound cell coordinates.

The refinement laws apply to finite successful full images in one stable
store. Native acyclicity/metadata evidence, frame generations, allocation,
ownership and compiler correspondence remain implementation obligations.
Private counted collections, cells and rational values retain their own
interpreters; this sequence observation does not reinterpret their fields.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ContextualSequenceObservation

abbrev Term := SubstitutionFold.Term

structure Value (Frame Variable Literal : Type) where
  term : Term Variable Literal
  frame : Frame

abbrev Store (Frame Variable Literal : Type) :=
  Frame → Variable → Option (Value Frame Variable Literal)

variable {Frame Variable Literal : Type}

mutual
  inductive Image (store : Store Frame Variable Literal) :
      Value Frame Variable Literal → Term (Frame × Variable) Literal → Prop where
    | free {frame cell} : store frame cell = none →
      Image store ⟨.var cell, frame⟩ (.var (frame, cell))
    | binding {frame cell entered result} :
      store frame cell = some entered → Image store entered result →
      Image store ⟨.var cell, frame⟩ result
    | leaf {frame literal} : Image store ⟨.leaf literal, frame⟩ (.leaf literal)
    | expression {frame fields results} : Images store frame fields results →
      Image store ⟨.expr fields, frame⟩ (.expr results)

  inductive Images (store : Store Frame Variable Literal) : Frame →
      List (Term Variable Literal) → List (Term (Frame × Variable) Literal) → Prop where
    | nil {frame} : Images store frame [] []
    | cons {frame field fields result results} :
      Image store ⟨field, frame⟩ result → Images store frame fields results →
      Images store frame (field :: fields) (result :: results)
end

inductive RootRead (store : Store Frame Variable Literal) :
    Value Frame Variable Literal → Value Frame Variable Literal → Prop where
  | free {frame cell} : store frame cell = none →
    RootRead store ⟨.var cell, frame⟩ ⟨.var cell, frame⟩
  | binding {frame cell entered result} :
    store frame cell = some entered → RootRead store entered result →
    RootRead store ⟨.var cell, frame⟩ result
  | leaf {frame literal} : RootRead store ⟨.leaf literal, frame⟩ ⟨.leaf literal, frame⟩
  | expression {frame fields} :
    RootRead store ⟨.expr fields, frame⟩ ⟨.expr fields, frame⟩

theorem root_image_iff {store : Store Frame Variable Literal}
    {source target : Value Frame Variable Literal}
    (read : RootRead store source target)
    (result : Term (Frame × Variable) Literal) :
    Image store source result ↔ Image store target result := by
  induction read with
  | free _ => rfl
  | leaf => rfl
  | expression => rfl
  | @binding frame cell entered target found _ ih =>
    constructor
    · intro image
      cases image with
      | free missing => simp [found] at missing
      | @binding _ _ other _ stored child =>
        have same : entered = other := by simpa [found] using stored
        subst other
        exact ih.mp child
    · intro image
      exact .binding found (ih.mpr image)

theorem fields_length {store : Store Frame Variable Literal} {frame : Frame}
    {fields : List (Term Variable Literal)} {results : List (Term (Frame × Variable) Literal)}
    (images : Images store frame fields results) : fields.length = results.length := by
  induction fields generalizing results with
  | nil => cases images; rfl
  | cons field fields ih =>
    cases images with
    | cons _ rest => simpa using congrArg Nat.succ (ih rest)

theorem head_projection {store : Store Frame Variable Literal}
    {source : Value Frame Variable Literal} {frame : Frame}
    {field : Term Variable Literal} {fields : List (Term Variable Literal)}
    {result : Term (Frame × Variable) Literal} {results : List (Term (Frame × Variable) Literal)}
    (root : RootRead store source ⟨.expr (field :: fields), frame⟩)
    (whole : Image store source (.expr (result :: results))) :
    Image store ⟨field, frame⟩ result := by
  have image := (root_image_iff root _).mp whole
  cases image with
  | expression images => cases images with
    | cons first _ => exact first

theorem tail_projection {store : Store Frame Variable Literal}
    {source : Value Frame Variable Literal} {frame : Frame}
    {field : Term Variable Literal} {fields : List (Term Variable Literal)}
    {result : Term (Frame × Variable) Literal} {results : List (Term (Frame × Variable) Literal)}
    (root : RootRead store source ⟨.expr (field :: fields), frame⟩)
    (whole : Image store source (.expr (result :: results))) :
    Image store ⟨.expr fields, frame⟩ (.expr results) := by
  have image := (root_image_iff root _).mp whole
  cases image with
  | expression images => cases images with
    | cons _ rest => exact .expression rest

theorem length_projection {store : Store Frame Variable Literal}
    {source : Value Frame Variable Literal} {frame : Frame}
    {fields : List (Term Variable Literal)} {results : List (Term (Frame × Variable) Literal)}
    (root : RootRead store source ⟨.expr fields, frame⟩)
    (whole : Image store source (.expr results)) : fields.length = results.length := by
  have image := (root_image_iff root _).mp whole
  cases image with
  | expression images => exact fields_length images

theorem logical_list_tail_projection {store : Store Frame Variable Literal}
    {source : Value Frame Variable Literal} {frame : Frame}
    {header field : Term Variable Literal} {fields : List (Term Variable Literal)}
    {listTag : Literal} {result : Term (Frame × Variable) Literal}
    {results : List (Term (Frame × Variable) Literal)}
    (root : RootRead store source ⟨.expr (header :: field :: fields), frame⟩)
    (whole : Image store source (.expr (.leaf listTag :: result :: results))) :
    Image store ⟨.expr (.leaf listTag :: fields), frame⟩ (.expr (.leaf listTag :: results)) := by
  have image := (root_image_iff root _).mp whole
  cases image with
  | expression images => cases images with
    | cons _ rest => cases rest with
      | cons _ remaining => exact .expression (.cons .leaf remaining)

def rootShape {Cell : Type} : Term Cell Literal → Option Literal × Nat
  | .var _ => (none, 0)
  | .leaf literal => (some literal, 0)
  | .expr fields => (none, fields.length)

theorem root_shape_refines_full_image {store : Store Frame Variable Literal}
    {source target : Value Frame Variable Literal}
    (read : RootRead store source target)
    {result : Term (Frame × Variable) Literal} (whole : Image store source result) :
    rootShape target.term = rootShape result := by
  induction read generalizing result with
  | free absent =>
    cases whole with
    | free => rfl
    | binding present _ => simp [absent] at present
  | leaf => cases whole; rfl
  | expression =>
    cases whole with
    | expression images => simp [rootShape, fields_length images]
  | @binding frame cell entered target present _ ih =>
    cases whole with
    | free absent => simp [present] at absent
    | @binding _ _ other _ stored child =>
      have same : entered = other := by simpa [present] using stored
      subst other
      exact ih child

theorem field_projection {store : Store Frame Variable Literal} {frame : Frame}
    {fields : List (Term Variable Literal)} {results : List (Term (Frame × Variable) Literal)}
    (images : Images store frame fields results) (index : Nat)
    {field : Term Variable Literal} {result : Term (Frame × Variable) Literal}
    (atField : fields[index]? = some field) (atResult : results[index]? = some result) :
    Image store ⟨field, frame⟩ result := by
  induction fields generalizing results index with
  | nil => simp at atField
  | cons first rest ih =>
    cases images with
    | cons firstImage restImages =>
      cases index with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at atField atResult
        subst field
        subst result
        exact firstImage
      | succ index => exact ih restImages index atField atResult

def separatingStore : Store Nat Nat Nat := fun frame cell =>
  if frame = 2 ∧ cell = 0 then some ⟨.expr [.var 1], 1⟩
  else if cell = 1 then some ⟨.leaf (if frame = 1 then 23 else 11), frame⟩
  else none

theorem alias_enters_new_frame :
    RootRead separatingStore ⟨.var 0, 2⟩ ⟨.expr [.var 1], 1⟩ := by
  exact .binding (by simp [separatingStore]) .expression

theorem preserved_child_scope :
    Image separatingStore ⟨.var 1, 1⟩ (.leaf 23) := by
  exact .binding (entered := ⟨.leaf 23, 1⟩) (by simp [separatingStore]) .leaf

theorem caller_scope_changes_answer :
    Image separatingStore ⟨.var 1, 2⟩ (.leaf 11) := by
  exact .binding (entered := ⟨.leaf 11, 2⟩) (by simp [separatingStore]) .leaf

theorem wrong_scope_cannot_return_selected_child :
    ¬ Image separatingStore ⟨.var 1, 2⟩ (.leaf 23) := by
  intro image
  cases image with
  | @binding _ _ entered _ present child =>
    have same : entered = ⟨.leaf 11, 2⟩ := by simpa [separatingStore] using present.symm
    subst entered
    cases child

/-! Constructor role is determined by at most four root coordinates: tuple
arity, head tag, domain arity and domain head tag. The query model exposes
those coordinates individually and excludes previously derived role facts.
It counts root observations, not alias-chain steps or machine instructions. -/

inductive Role where
  | ordinary
  | compound
  | registered
  deriving DecidableEq, Repr

abbrev Header := Fin 4 → Nat

def referenceRole (header : Header) : Role :=
  if header 0 = 2 then
    if header 1 = 1 then .compound else .ordinary
  else if header 0 = 3 then
    if header 1 = 2 then .compound
    else if header 1 = 3 ∨ (header 2 = 2 ∧ header 3 = 4) then .registered
    else .ordinary
  else .ordinary

def roleQuery : ReadOnlyQuery.Program (Fin 4) Nat Role :=
  .read 0 fun arity =>
    if arity = 2 then .read 1 fun head =>
      .pure (if head = 1 then .compound else .ordinary)
    else if arity = 3 then .read 1 fun head =>
      if head = 2 then .pure .compound
      else if head = 3 then .pure .registered
      else .read 2 fun domainArity =>
        if domainArity = 2 then .read 3 fun domainHead =>
          .pure (if domainHead = 4 then .registered else .ordinary)
        else .pure .ordinary
    else .pure .ordinary

theorem role_query_correct (header : Header) :
    (ReadOnlyQuery.run header roleQuery).answer = referenceRole header := by
  by_cases arityTwo : header 0 = 2 <;>
    by_cases arityThree : header 0 = 3 <;>
    by_cases headCompound : header 1 = 1 <;>
    by_cases headPartial : header 1 = 2 <;>
    by_cases headNullary : header 1 = 3 <;>
    by_cases domainPair : header 2 = 2 <;>
    by_cases domainIdentity : header 3 = 4 <;>
    simp_all [roleQuery, ReadOnlyQuery.run, referenceRole]

theorem role_query_read_bound (header : Header) :
    (ReadOnlyQuery.run header roleQuery).reads.length ≤ 4 := by
  by_cases arityTwo : header 0 = 2 <;>
    by_cases arityThree : header 0 = 3 <;>
    by_cases headCompound : header 1 = 1 <;>
    by_cases headPartial : header 1 = 2 <;>
    by_cases headNullary : header 1 = 3 <;>
    by_cases domainPair : header 2 = 2 <;>
    by_cases domainIdentity : header 3 = 4 <;>
    simp_all [roleQuery, ReadOnlyQuery.run]

theorem must_read_changed_coordinate
    {Answer : Type} (reference : Header → Answer)
    (program : ReadOnlyQuery.Program (Fin 4) Nat Answer)
    (correct : ∀ header, (ReadOnlyQuery.run header program).answer = reference header)
    (header : Header) (key : Fin 4) (replacement : Nat)
    (changed : reference (Function.update header key replacement) ≠ reference header) :
    key ∈ (ReadOnlyQuery.run header program).reads.map Prod.fst := by
  by_contra absent
  have agree : ReadOnlyQuery.Agrees (Function.update header key replacement)
      (ReadOnlyQuery.run header program).reads := by
    intro observed member
    have different : observed.1 ≠ key := by
      intro same
      apply absent
      exact List.mem_map.mpr ⟨observed, member, same⟩
    have old := ReadOnlyQuery.run_agrees header program observed member
    simpa [Function.update, different] using old
  have same := congrArg ReadOnlyQuery.Observation.answer
    (ReadOnlyQuery.run_eq_of_agrees header (Function.update header key replacement) program agree)
  rw [correct, correct] at same
  exact changed same

def registeredHeader : Header := ![3, 0, 2, 4]
def separatingValue : Fin 4 → Nat := ![4, 2, 0, 0]

theorem each_registered_coordinate_matters (key : Fin 4) :
    referenceRole (Function.update registeredHeader key (separatingValue key)) ≠
      referenceRole registeredHeader := by
  fin_cases key <;> decide

theorem role_query_lower_bound
    (program : ReadOnlyQuery.Program (Fin 4) Nat Role)
    (correct : ∀ header, (ReadOnlyQuery.run header program).answer = referenceRole header) :
    4 ≤ (ReadOnlyQuery.run registeredHeader program).reads.length := by
  let keys := (ReadOnlyQuery.run registeredHeader program).reads.map Prod.fst
  have all : ∀ key : Fin 4, key ∈ keys := by
    intro key
    exact must_read_changed_coordinate referenceRole program correct registeredHeader key
      (separatingValue key) (each_registered_coordinate_matters key)
  have complete : keys.toFinset = Finset.univ := by
    ext key
    simp [all key]
  calc
    4 = (Finset.univ : Finset (Fin 4)).card := by decide
    _ = keys.toFinset.card := congrArg Finset.card complete.symm
    _ ≤ keys.length := List.toFinset_card_le keys
    _ = (ReadOnlyQuery.run registeredHeader program).reads.length := List.length_map _

theorem role_query_worst_case_exact :
    (ReadOnlyQuery.run registeredHeader roleQuery).reads.length = 4 := by decide

theorem role_query_worst_case_optimal
    (program : ReadOnlyQuery.Program (Fin 4) Nat Role)
    (correct : ∀ header, (ReadOnlyQuery.run header program).answer = referenceRole header) :
    (ReadOnlyQuery.run registeredHeader roleQuery).reads.length ≤
      (ReadOnlyQuery.run registeredHeader program).reads.length := by
  rw [role_query_worst_case_exact]
  exact role_query_lower_bound program correct

/-! Sequence consumers observe logical length or absence of a sequence;
they need not distinguish compound from registered callable. The stronger
role lower bound alone therefore cannot establish sequence optimality.
For this weaker observer the following independent lower bound gives a
4/3 worst-case bound, in the same coordinate-query model. -/

def referenceSequence (header : Header) : Option Nat :=
  if referenceRole header = .ordinary then
    some (header 0 - if header 1 = 5 then 1 else 0)
  else none

def sequenceQuery : ReadOnlyQuery.Program (Fin 4) Nat (Option Nat) :=
  .read 0 fun arity =>
    if arity = 0 then .pure (some 0)
    else .read 1 fun head =>
      let ordinary := some (arity - if head = 5 then 1 else 0)
      if arity = 2 ∧ head = 1 then .pure none
      else if arity = 3 then
        if head = 2 ∨ head = 3 then .pure none
        else .read 2 fun domainArity =>
          if domainArity = 2 then .read 3 fun domainHead =>
            .pure (if domainHead = 4 then none else ordinary)
          else .pure ordinary
      else .pure ordinary

set_option maxHeartbeats 1000000 in
theorem sequence_query_correct (header : Header) :
    (ReadOnlyQuery.run header sequenceQuery).answer = referenceSequence header := by
  by_cases arityZero : header 0 = 0
  · simp [sequenceQuery, referenceSequence, referenceRole, ReadOnlyQuery.run, arityZero]
  by_cases arityTwo : header 0 = 2
  · by_cases headCompound : header 1 = 1 <;>
      simp_all [sequenceQuery, referenceSequence, referenceRole, ReadOnlyQuery.run]
  by_cases arityThree : header 0 = 3
  · by_cases headPartial : header 1 = 2 <;>
      by_cases headNullary : header 1 = 3 <;>
      by_cases domainPair : header 2 = 2 <;>
      by_cases domainIdentity : header 3 = 4 <;>
      simp_all [sequenceQuery, referenceSequence, referenceRole, ReadOnlyQuery.run]
  · simp [sequenceQuery, referenceSequence, referenceRole, ReadOnlyQuery.run,
      arityZero, arityTwo, arityThree]

theorem sequence_query_read_bound (header : Header) :
    (ReadOnlyQuery.run header sequenceQuery).reads.length ≤ 4 := by
  by_cases arityZero : header 0 = 0
  · simp [sequenceQuery, ReadOnlyQuery.run, arityZero]
  by_cases arityTwo : header 0 = 2
  · by_cases headCompound : header 1 = 1 <;>
      simp_all [sequenceQuery, ReadOnlyQuery.run]
  by_cases arityThree : header 0 = 3
  · by_cases headPartial : header 1 = 2 <;>
      by_cases headNullary : header 1 = 3 <;>
      by_cases domainPair : header 2 = 2 <;>
      simp_all [sequenceQuery, ReadOnlyQuery.run]
  · simp [sequenceQuery, ReadOnlyQuery.run, arityZero, arityTwo, arityThree]

def ordinarySequenceHeader : Header := ![3, 0, 2, 0]
def sequenceSeparatingValue : Fin 4 → Nat := ![4, 2, 0, 4]

theorem sequence_coordinate_matters (key : Fin 4)
    (needed : key ∈ ({0, 1, 3} : Finset (Fin 4))) :
    referenceSequence (Function.update ordinarySequenceHeader key (sequenceSeparatingValue key)) ≠
      referenceSequence ordinarySequenceHeader := by
  fin_cases key <;> (try simp at needed) <;> decide

theorem sequence_query_lower_bound
    (program : ReadOnlyQuery.Program (Fin 4) Nat (Option Nat))
    (correct : ∀ header, (ReadOnlyQuery.run header program).answer = referenceSequence header) :
    3 ≤ (ReadOnlyQuery.run ordinarySequenceHeader program).reads.length := by
  let keys := (ReadOnlyQuery.run ordinarySequenceHeader program).reads.map Prod.fst
  let needed : Finset (Fin 4) := {0, 1, 3}
  have included : needed ⊆ keys.toFinset := by
    intro key member
    apply List.mem_toFinset.mpr
    exact must_read_changed_coordinate referenceSequence program correct ordinarySequenceHeader
      key (sequenceSeparatingValue key) (sequence_coordinate_matters key member)
  calc
    3 = needed.card := by decide
    _ ≤ keys.toFinset.card := Finset.card_le_card included
    _ ≤ keys.length := List.toFinset_card_le keys
    _ = (ReadOnlyQuery.run ordinarySequenceHeader program).reads.length := List.length_map _

theorem sequence_query_near_optimal (header : Header)
    (program : ReadOnlyQuery.Program (Fin 4) Nat (Option Nat))
    (correct : ∀ current, (ReadOnlyQuery.run current program).answer = referenceSequence current) :
    3 * (ReadOnlyQuery.run header sequenceQuery).reads.length ≤
      4 * (ReadOnlyQuery.run ordinarySequenceHeader program).reads.length := by
  have ours := sequence_query_read_bound header
  have lower := sequence_query_lower_bound program correct
  omega

inductive Residence where
  | materialized
  | contextual
  | persistent
  deriving DecidableEq

def derivedContext (residence : Residence) (frame emptyFrame : Frame) (openTerm : Bool) :
    Residence × Frame :=
  if residence = .persistent then (.contextual, frame)
  else if openTerm then (residence, frame)
  else (.materialized, emptyFrame)

theorem derived_node_is_not_persistent (residence : Residence)
    (frame emptyFrame : Frame) (openTerm : Bool) :
    (derivedContext residence frame emptyFrame openTerm).1 ≠ .persistent := by
  cases residence <;> cases openTerm <;> simp [derivedContext]

theorem open_derived_node_keeps_frame (residence : Residence) (frame emptyFrame : Frame) :
    (derivedContext residence frame emptyFrame true).2 = frame := by
  cases residence <;> simp [derivedContext]

theorem persistent_source_gives_execution_owned_node (frame emptyFrame : Frame)
    (openTerm : Bool) :
    derivedContext .persistent frame emptyFrame openTerm = (.contextual, frame) := by
  simp [derivedContext]

end Mettapedia.Machines.ContextualSequenceObservation

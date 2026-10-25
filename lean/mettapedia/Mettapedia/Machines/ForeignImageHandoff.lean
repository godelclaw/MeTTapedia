import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Scoped handoff of an already decoded foreign image

The reference reads every binding image, then reads the result again. The
target retains the binding images and selects an eligible image of the same
foreign source in the same read scope. Selection never changes the bindings.

Source trees have data, open variables, identity-bearing resources and marked
occurrences. Separate constructor reads carry independent positions; logical
variable leaves carry identities from the read map. Data and logical variables
are admitted for handoff. Data observations ignore
allocation positions; logical variables retain the identities assigned by the
read's common variable map. Resource and marked observations retain positions.
The negative examples show why source identity, scope and admission matter.

The scope includes an answer revision, presentation policy, receiver owner and
logical variable-map identity.
Variable names in this presentation already identify that map's logical cells.
A heap is fixed within that scope; extending a native variable map must preserve
its established identities. Native non-mutating reads, compound identity,
summary flags and owner lifetime remain implementation obligations. The work
model counts decoded nodes and candidate inspections, not C instructions,
physical allocations, allocation failures or total-runtime optimality.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ForeignImageHandoff

inductive Source where
  | datum (value : Nat)
  | cell (head tail : Source)
  | openVar (name : Nat)
  | resource (token : Nat)
  | marked (value : Source)
  deriving DecidableEq, Repr

def Source.nodes : Source → Nat
  | .datum _ | .openVar _ | .resource _ => 1
  | .cell head tail => 1 + head.nodes + tail.nodes
  | .marked value => 1 + value.nodes

def Source.reusableData : Source → Bool
  | .datum _ | .openVar _ => true
  | .cell head tail => head.reusableData && tail.reusableData
  | .resource _ | .marked _ => false

/-- An opaque handle can have ordinary-looking native syntax. Its creation
history carries information absent from that syntax's structural summary. -/
def Source.shapeData : Source → Bool
  | .datum _ | .openVar _ | .resource _ => true
  | .cell head tail => head.shapeData && tail.shapeData
  | .marked _ => false

def Source.registrations : Source → Nat
  | .datum _ | .openVar _ => 0
  | .resource _ => 1
  | .cell head tail => head.registrations + tail.registrations
  | .marked value => value.registrations

theorem reusable_of_shape_and_no_registration (source : Source)
    (shape : source.shapeData = true) (quiet : source.registrations = 0) :
    source.reusableData = true := by
  induction source with
  | datum value => rfl
  | openVar name => rfl
  | resource token => simp [Source.registrations] at quiet
  | marked value ih => simp [Source.shapeData] at shape
  | cell head tail left right =>
      obtain ⟨headShape, tailShape⟩ := Bool.and_eq_true_iff.mp shape
      have headQuiet : head.registrations = 0 := by
        simp only [Source.registrations] at quiet; omega
      have tailQuiet : tail.registrations = 0 := by
        simp only [Source.registrations] at quiet; omega
      exact Bool.and_eq_true_iff.mpr
        ⟨left headShape headQuiet, right tailShape tailQuiet⟩

inductive Image where
  | datum (position value : Nat)
  | cell (position : Nat) (head tail : Image)
  | openVar (identity name : Nat)
  | resource (position token : Nat)
  | marked (position : Nat) (value : Image)
  deriving DecidableEq, Repr

inductive View where
  | datum (value : Nat)
  | cell (head tail : View)
  | openVar (identity name : Nat)
  | resource (identity token : Nat)
  | marked (identity : Nat) (value : View)
  deriving DecidableEq, Repr

def Image.observe : Image → View
  | .datum _ value => .datum value
  | .cell _ head tail => .cell head.observe tail.observe
  | .openVar identity name => .openVar identity name
  | .resource identity token => .resource identity token
  | .marked identity value => .marked identity value.observe

/-- This recursive summary models facts established compositionally by the
constructors. It does not replace the native summary-correspondence obligation. -/
def Image.shapeData : Image → Bool
  | .datum _ _ | .openVar _ _ | .resource _ _ => true
  | .cell _ head tail => head.shapeData && tail.shapeData
  | .marked _ _ => false

/-- Independent decoder with explicit fresh positions. -/
def decode : Source → Nat → Image
  | .datum value, start => .datum start value
  | .openVar name, _ => .openVar name name
  | .resource token, start => .resource start token
  | .cell head tail, start =>
      .cell start (decode head (start + 1))
        (decode tail (start + 1 + head.nodes))
  | .marked value, start => .marked start (decode value (start + 1))

theorem shapeData_decode (source : Source) (start : Nat) :
    (decode source start).shapeData = source.shapeData := by
  induction source generalizing start with
  | datum value => rfl
  | openVar name => rfl
  | resource token => rfl
  | marked value ih => rfl
  | cell head tail left right =>
      simp only [decode, Image.shapeData, Source.shapeData, left, right]

/-- Decoding with the same logical variable identities produces the same
complete data observation, including
order and repeated children, under the actual admission summary. -/
theorem scoped_decode_observation (source : Source)
    (closed : source.reusableData = true) (first second : Nat) :
    (decode source first).observe = (decode source second).observe := by
  induction source generalizing first second with
  | datum value => rfl
  | openVar name => rfl
  | resource token => simp [Source.reusableData] at closed
  | marked value ih => simp [Source.reusableData] at closed
  | cell head tail left right =>
      obtain ⟨headClosed, tailClosed⟩ := Bool.and_eq_true_iff.mp closed
      simp only [decode, Image.observe,
        left headClosed (first + 1) (second + 1),
        right tailClosed (first + 1 + head.nodes) (second + 1 + head.nodes)]

structure Scope where
  revision : Nat
  presentation : Nat
  owner : Nat
  variableMap : Nat
  deriving DecidableEq, Repr

abbrev Heap := Scope → Nat → Source

structure Record where
  scope : Scope
  source : Nat
  image : Image
  registrations : Nat
  deriving DecidableEq, Repr

def readRecord (heap : Heap) (scope : Scope) (source start : Nat) : Record :=
  ⟨scope, source, decode (heap scope source) start, (heap scope source).registrations⟩

def Valid (heap : Heap) (record : Record) : Prop :=
  ∃ start, record.image = decode (heap record.scope record.source) start ∧
    record.registrations = (heap record.scope record.source).registrations

theorem readRecord_valid (heap : Heap) (scope : Scope) (source start : Nat) :
    Valid heap (readRecord heap scope source start) := ⟨start, rfl, rfl⟩

def admitted (scope : Scope) (source : Nat) (record : Record) : Bool :=
  decide (record.scope = scope ∧ record.source = source) &&
    (record.image.shapeData && decide (record.registrations = 0))

/-- Source identity is compared, not merely a structural discriminator.
The first admitted record wins, without changing the retained record list. -/
def select (scope : Scope) (source : Nat) : List Record → Option Image
  | [] => none
  | record :: rest =>
      if admitted scope source record then some record.image
      else select scope source rest

theorem admitted_observation (heap : Heap) (scope : Scope) (source start : Nat)
    (record : Record) (valid : Valid heap record)
    (accepted : admitted scope source record = true) :
    record.image.observe = (decode (heap scope source) start).observe := by
  obtain ⟨identity, reusable⟩ := Bool.and_eq_true_iff.mp accepted
  obtain ⟨shape, quiet⟩ := Bool.and_eq_true_iff.mp reusable
  obtain ⟨sameScope, sameSource⟩ := of_decide_eq_true identity
  obtain ⟨prior, image, effects⟩ := valid
  have noRegistration : (heap record.scope record.source).registrations = 0 :=
    effects.symm.trans (of_decide_eq_true quiet)
  have closed := reusable_of_shape_and_no_registration _
    ((shapeData_decode _ _).symm.trans (image ▸ shape)) noRegistration
  rw [image]
  rw [sameScope, sameSource] at closed ⊢
  apply scoped_decode_observation
  exact closed

theorem selected_observation (heap : Heap) (scope : Scope) (source start : Nat)
    (records : List Record) (valid : ∀ record ∈ records, Valid heap record)
    (image : Image) (selected : select scope source records = some image) :
    image.observe = (decode (heap scope source) start).observe := by
  induction records with
  | nil => simp [select] at selected
  | cons record rest ih =>
      by_cases accepted : admitted scope source record = true
      · simp only [select, accepted, ↓reduceIte, Option.some.injEq] at selected
        subst image
        exact admitted_observation heap scope source start record
          (valid record (by simp)) accepted
      · simp only [select, accepted, Bool.false_eq_true, ↓reduceIte] at selected
        exact ih (fun entry member => valid entry (by simp [member])) selected

def readBindings (heap : Heap) (scope : Scope) : List Nat → Nat → List Record
  | [], _ => []
  | source :: rest, start =>
      readRecord heap scope source start ::
        readBindings heap scope rest (start + (heap scope source).nodes)

theorem readBindings_valid (heap : Heap) (scope : Scope)
    (sources : List Nat) (start : Nat) :
    ∀ record ∈ readBindings heap scope sources start, Valid heap record := by
  induction sources generalizing start with
  | nil => simp [readBindings]
  | cons source rest ih =>
      intro record member
      simp only [readBindings, List.mem_cons] at member
      rcases member with rfl | tail
      · exact readRecord_valid heap scope source start
      · exact ih _ record tail

def handoff (heap : Heap) (scope : Scope) (source start : Nat)
    (records : List Record) : Image :=
  match select scope source records with
  | some image => image
  | none => decode (heap scope source) start

/-- Complete ordered binding observations and the returned value agree.
The reference really decodes the result again; the target selects or decodes. -/
theorem handoff_readBindings_observation (heap : Heap) (scope : Scope)
    (sources : List Nat) (bindingStart resultSource resultStart : Nat) :
    let records := readBindings heap scope sources bindingStart
    (records.map (fun record => record.image.observe),
      (handoff heap scope resultSource resultStart records).observe) =
    (records.map (fun record => record.image.observe),
      (decode (heap scope resultSource) resultStart).observe) := by
  dsimp only
  apply congrArg (fun value =>
    ((readBindings heap scope sources bindingStart).map
      (fun record => record.image.observe), value))
  unfold handoff
  split
  · rename_i image selected
    exact selected_observation heap scope resultSource resultStart _
      (readBindings_valid heap scope sources bindingStart) image selected
  · rfl

/-- A later logical state assigns a complete observation to each existing
variable identity. The shared image does not capture one such assignment. -/
def View.withBindings (bindings : Nat → View) : View → View
  | .datum value => .datum value
  | .cell head tail => .cell (head.withBindings bindings) (tail.withBindings bindings)
  | .openVar identity _ => bindings identity
  | .resource identity token => .resource identity token
  | .marked identity value => .marked identity (value.withBindings bindings)

/-- Handoff preserves every later binding observation, not only the state at
the moment the image was selected. Rollback may supply another assignment. -/
theorem handoff_preserves_live_bindings (heap : Heap) (scope : Scope)
    (sources : List Nat) (bindingStart resultSource resultStart : Nat)
    (bindings : Nat → View) :
    ((handoff heap scope resultSource resultStart
      (readBindings heap scope sources bindingStart)).observe).withBindings bindings =
    ((decode (heap scope resultSource) resultStart).observe).withBindings bindings := by
  have pair := handoff_readBindings_observation heap scope sources
    bindingStart resultSource resultStart
  have value := congrArg Prod.snd pair
  exact congrArg (View.withBindings bindings) value

def Image.visits : Image → Nat
  | .datum _ _ | .openVar _ _ | .resource _ _ => 1
  | .cell _ head tail => 1 + head.visits + tail.visits
  | .marked _ value => 1 + value.visits

theorem decode_visits (source : Source) (start : Nat) :
    (decode source start).visits = source.nodes := by
  induction source generalizing start <;>
    simp_all [decode, Image.visits, Source.nodes]

def selectionVisits (scope : Scope) (source : Nat) : List Record → Nat
  | [] => 0
  | record :: rest =>
      1 + if admitted scope source record then 0 else selectionVisits scope source rest

theorem selectionVisits_le_length (scope : Scope) (source : Nat)
    (records : List Record) : selectionVisits scope source records ≤ records.length := by
  induction records with
  | nil => exact Nat.le_refl 0
  | cons record rest ih =>
      simp only [selectionVisits, List.length_cons]
      split <;> omega

/-- The saved result decode has a precise size; dispatch is charged separately.
This is a sufficient cost condition, not an assertion that dispatch is free. -/
theorem selected_handoff_work_le_reference (bindingWork resultNodes dispatch : Nat)
    (worthwhile : dispatch ≤ resultNodes) :
    bindingWork + dispatch ≤ bindingWork + resultNodes := by omega

def sampleScope : Scope := ⟨1, 0, 7, 4⟩
def nextScope : Scope := ⟨2, 0, 7, 4⟩

theorem ordered_duplicate_data_survive :
    (decode (.cell (.datum 5) (.cell (.datum 5) (.datum 0))) 10).observe =
      (decode (.cell (.datum 5) (.cell (.datum 5) (.datum 0))) 90).observe := by decide

theorem identity_resources_are_not_reusable :
    (decode (.resource 8) 10).shapeData = true ∧
      admitted sampleScope 1 (readRecord (fun _ _ => .resource 8) sampleScope 1 10) = false ∧
      (decode (.resource 8) 10).observe ≠ (decode (.resource 8) 90).observe := by decide

theorem open_images_reuse_fixed_variable_identity :
    (decode (.openVar 3) 10).observe = (decode (.openVar 3) 90).observe ∧
      (decode (.openVar 3) 10).shapeData = true ∧
      (decode (.marked (.datum 7)) 10).shapeData = false := by decide

theorem foreign_identity_is_required :
    let heap : Heap := fun _ source => .datum source
    let old := readRecord heap sampleScope 1 10
    old.image.shapeData = true ∧ admitted sampleScope 2 old = false ∧
      old.image.observe ≠ (decode (heap sampleScope 2) 90).observe := by decide

theorem answer_scope_is_required :
    let heap : Heap := fun scope _ => .datum scope.revision
    let old := readRecord heap sampleScope 1 10
    old.image.shapeData = true ∧ admitted nextScope 1 old = false ∧
      old.image.observe ≠ (decode (heap nextScope 1) 90).observe := by decide

theorem presentation_and_owner_are_scoped :
    let record := readRecord (fun _ _ => .datum 3) sampleScope 1 10
    admitted ⟨1, 1, 7, 4⟩ 1 record = false ∧
      admitted ⟨1, 0, 8, 4⟩ 1 record = false := by decide

theorem a_different_variable_map_reopens_the_read :
    let heap : Heap := fun scope _ => .openVar scope.variableMap
    let record := readRecord heap sampleScope 1 10
    admitted ⟨1, 0, 7, 5⟩ 1 record = false ∧
      record.image.observe ≠ (decode (heap ⟨1, 0, 7, 5⟩ 1) 90).observe := by decide

#print axioms scoped_decode_observation
#print axioms admitted_observation
#print axioms selected_observation
#print axioms handoff_readBindings_observation
#print axioms handoff_preserves_live_bindings
#print axioms decode_visits
#print axioms selectionVisits_le_length
#print axioms selected_handoff_work_le_reference
#print axioms identity_resources_are_not_reusable
#print axioms foreign_identity_is_required
#print axioms answer_scope_is_required
#print axioms a_different_variable_map_reopens_the_read

end Mettapedia.Machines.ForeignImageHandoff

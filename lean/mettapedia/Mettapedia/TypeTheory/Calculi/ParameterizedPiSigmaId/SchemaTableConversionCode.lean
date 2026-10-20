import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AlgebraicSchema
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.DeclarationComputation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionCode

/-!
# Finite replay of selected algebraic schema instances

A submission cites an original table position and a finite list of arguments.
Replay checks the position, the selected policy and the exact schema arity.
The independent root evidence retains that position and its simultaneous
substitution. Equal equations in different rows remain different receipts.

These are scoped term codes, not a byte parser or an inductive admission
algorithm. A root decoder alone grants neither typing nor normalization.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace SchemaTableConversionCode

open AlgebraicSchema Declaration StructuralConversionCode

variable {Head : Type} {n m : Nat}

/-- The row address is checked against the original table, before any
selection or endpoint comparison. Arguments are explicit finite syntax. -/
structure Code (Head : Type) (n : Nat) where
  row : Nat
  arguments : List (Tm Head n)
  deriving DecidableEq, Repr

/-- Selected root evidence is stated without reference to decoding. -/
inductive Evidence (table : SchemaTable Head) (enabled : Fin table.length → Bool) :
    {n : Nat} → Tm Head n → Tm Head n → Type where
  | instantiate {n : Nat} (index : Fin table.length) (permitted : enabled index = true)
      (substitution : Sub Head (table.get index).1 n) :
      Evidence table enabled
        (subst substitution (table.get index).2.1)
        (subst substitution (table.get index).2.2)

/-- Increasing permissions retains the same source occurrence and complete
assignment. It does not search for an equal replacement citation. -/
def Evidence.weakenPermissions {table : SchemaTable Head}
    {small large : Fin table.length → Bool}
    (included : ∀ index, small index = true → large index = true)
    {left right : Tm Head n} : Evidence table small left right → Evidence table large left right
  | .instantiate index permitted substitution =>
      .instantiate index (included index permitted) substitution

/-- Substitution acts on the actual row witness and all its arguments. -/
def retained (table : SchemaTable Head) (enabled : Fin table.length → Bool) :
    ProofRelevantRootComputation Head where
  Evidence := Evidence table enabled
  rename := by
    intro n m rho left right evidence
    cases evidence with
    | instantiate index permitted substitution =>
        simpa only [rename_subst] using
          Evidence.instantiate index permitted (fun i => rename rho (substitution i))
  substitute := by
    intro n m sigma left right evidence
    cases evidence with
    | instantiate index permitted substitution =>
        simpa only [subst_comp] using
          Evidence.instantiate index permitted (fun i => subst sigma (substitution i))

abbrev root (table : SchemaTable Head) (enabled : Fin table.length → Bool) :
    RootComputation Head := (retained table enabled).support

theorem root_mono {table : SchemaTable Head} {small large : Fin table.length → Bool}
    (included : ∀ index, small index = true → large index = true)
    {left right : Tm Head n} (step : (root table small).step left right) :
    (root table large).step left right := by
  obtain ⟨evidence⟩ := step
  exact ⟨evidence.weakenPermissions included⟩

/-- Checked finite arguments give the ordinary capture-safe substitution. -/
def argumentSub {arity : Nat} (arguments : List (Tm Head n))
    (length : arguments.length = arity) : Sub Head arity n :=
  fun index => arguments[index.val]'(by omega)

@[simp] theorem argumentSub_ofFn {arity : Nat} (substitution : Sub Head arity n) :
    argumentSub (List.ofFn substitution) (by simp) = substitution := by
  funext index
  simp [argumentSub]

/-- Parsed data retains its selected row as well as the instantiated terms. -/
structure Instance (table : SchemaTable Head) (enabled : Fin table.length → Bool)
    (n : Nat) where
  index : Fin table.length
  permitted : enabled index = true
  substitution : Sub Head (table.get index).1 n

def Instance.endpoints {table : SchemaTable Head} {enabled : Fin table.length → Bool}
    (parsed : Instance table enabled n) : Tm Head n × Tm Head n :=
  (subst parsed.substitution (table.get parsed.index).2.1,
   subst parsed.substitution (table.get parsed.index).2.2)

def Instance.evidence {table : SchemaTable Head} {enabled : Fin table.length → Bool}
    (parsed : Instance table enabled n) :
    Evidence table enabled parsed.endpoints.1 parsed.endpoints.2 :=
  .instantiate parsed.index parsed.permitted parsed.substitution

def decodeInstance (table : SchemaTable Head) (enabled : Fin table.length → Bool)
    (code : Code Head n) : Option (Instance table enabled n) :=
  if bound : code.row < table.length then
    let index : Fin table.length := ⟨code.row, bound⟩
    if permitted : enabled index = true then
      if length : code.arguments.length = (table.get index).1 then
        some ⟨index, permitted, argumentSub code.arguments length⟩
      else none
    else none
  else none

def decode (table : SchemaTable Head) (enabled : Fin table.length → Bool)
    (code : Code Head n) : Option (Tm Head n × Tm Head n) :=
  (decodeInstance table enabled code).map Instance.endpoints

def encode (table : SchemaTable Head) (index : Fin table.length)
    (substitution : Sub Head (table.get index).1 n) : Code Head n :=
  ⟨index.val, List.ofFn substitution⟩

/-- No matching or search is needed to replay a cited substitution instance. -/
theorem decode_encode (table : SchemaTable Head) (enabled : Fin table.length → Bool)
    (index : Fin table.length) (permitted : enabled index = true)
    (substitution : Sub Head (table.get index).1 n) :
    decode table enabled (encode table index substitution) =
      some (subst substitution (table.get index).2.1,
        subst substitution (table.get index).2.2) := by
  simp [decode, decodeInstance, encode, index.isLt, permitted, Instance.endpoints]

/-- A generator may identify its canonical schema with a row whose dependent
arity is hidden by table lookup. Replay still consumes the same ordinal and
finite argument list, without proof casts in the submitted syntax. -/
theorem decode_at (table : SchemaTable Head) (enabled : Fin table.length → Bool)
    (index : Fin table.length) (permitted : enabled index = true)
    {arity : Nat} {left right : Tm Head arity}
    (row : table.get index = ⟨arity, left, right⟩)
    (substitution : Sub Head arity n) :
    decode table enabled ⟨index.val, List.ofFn substitution⟩ =
      some (subst substitution left, subst substitution right) := by
  generalize found : table.get index = entry at row
  obtain ⟨rowArity, rowLeft, rowRight⟩ := entry
  cases row
  have encoded := decode_encode (n := n) table enabled index permitted
  unfold encode at encoded
  rw [found] at encoded
  exact encoded substitution

theorem decode_sound (table : SchemaTable Head) (enabled : Fin table.length → Bool)
    (code : Code Head n) {left right : Tm Head n}
    (decoded : decode table enabled code = some (left, right)) :
    (root table enabled).step left right := by
  cases found : decodeInstance table enabled code with
  | none => simp [decode, found] at decoded
  | some parsed =>
      have equal : parsed.endpoints = (left, right) := by
        simpa [decode, found] using decoded
      have evidence := parsed.evidence
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
      exact ⟨evidence⟩

theorem decode_complete (table : SchemaTable Head) (enabled : Fin table.length → Bool)
    {left right : Tm Head n} (step : (root table enabled).step left right) :
    ∃ code, decode table enabled code = some (left, right) := by
  obtain ⟨evidence⟩ := step
  cases evidence with
  | instantiate index permitted substitution =>
      exact ⟨encode table index substitution, decode_encode table enabled index permitted substitution⟩

/-- The maintained structural checker can now consume the selected table. -/
def rootDecoder (table : SchemaTable Head) (enabled : Fin table.length → Bool) :
    RootDecoder (root table enabled) where
  Code := Code Head
  decode := decode table enabled
  sound := decode_sound table enabled
  complete := decode_complete table enabled

/-- Selecting every occurrence recovers the independently stated family of
schema instances. The comparison forgets occurrence evidence only at this
logical-support boundary. -/
theorem all_roots_iff (table : SchemaTable Head) {left right : Tm Head n} :
    (root table (fun _ => true)).step left right ↔
      SchemaStep table.family left right := by
  constructor
  · rintro ⟨evidence⟩
    cases evidence with
    | instantiate index _ substitution =>
        exact .instantiate (List.get_mem table index) substitution
  · intro step
    cases step with
    | @instantiate arity schemaLeft schemaRight member substitution =>
        obtain ⟨index, equal⟩ := List.mem_iff_get.mp member
        have evidence := Evidence.instantiate (table := table)
          (enabled := fun _ => true) (n := n) index rfl
        rw [equal] at evidence
        exact ⟨evidence substitution⟩

/-- Logical support is witnessed by a permitted original occurrence.
This predicate may forget which equal row was cited; retained evidence stays
in `Evidence`. No filtered table or replacement ordinal is introduced. -/
def selectedFamily (table : SchemaTable Head) (enabled : Fin table.length → Bool) :
    SchemaFamily Head :=
  fun {arity} left right => ∃ index, enabled index = true ∧
    table.get index = ⟨arity, left, right⟩

theorem selected_roots_iff (table : SchemaTable Head) (enabled : Fin table.length → Bool)
    {left right : Tm Head n} :
    (root table enabled).step left right ↔ SchemaStep (selectedFamily table enabled) left right := by
  constructor
  · rintro ⟨evidence⟩
    cases evidence with
    | instantiate index permitted substitution =>
        exact .instantiate ⟨index, permitted, rfl⟩ substitution
  · intro step
    cases step with
    | instantiate source substitution =>
        obtain ⟨index, permitted, same⟩ := source
        have evidence := Evidence.instantiate (table := table) (n := n) index permitted
        rw [same] at evidence
        exact ⟨evidence substitution⟩

/-- An independently proved schema presentation supplies a decoder for its
original root relation. The executable data and replay remain the common
ordered-table implementation. -/
def presentedDecoder (table : SchemaTable Head) (original : RootComputation Head)
    (presents : ∀ {ambient : Nat} {left right : Tm Head ambient},
      original.step left right ↔ SchemaStep table.family left right) :
    RootDecoder original where
  Code := Code Head
  decode := decode table (fun _ => true)
  sound := fun code _ _ accepted =>
    presents.mpr ((all_roots_iff table).mp (decode_sound table _ code accepted))
  complete := fun step =>
    decode_complete table _ ((all_roots_iff table).mpr (presents.mp step))

def Code.mapArguments (map : Tm Head n → Tm Head m) (code : Code Head n) : Code Head m :=
  ⟨code.row, code.arguments.map map⟩

@[simp] theorem Code.mapArguments_id (code : Code Head n) :
    code.mapArguments id = code := by
  cases code
  simp [mapArguments]

theorem Code.mapArguments_comp {k : Nat} (first : Tm Head n → Tm Head m)
    (second : Tm Head m → Tm Head k) (code : Code Head n) :
    (code.mapArguments first).mapArguments second = code.mapArguments (second ∘ first) := by
  simp [mapArguments, List.map_map]

private theorem argumentSub_map {arity : Nat} (map : Tm Head n → Tm Head m)
    (arguments : List (Tm Head n)) (length : arguments.length = arity) :
    argumentSub (arguments.map map) (by simpa using length) =
      fun index => map (argumentSub arguments length index) := by
  funext index
  simp [argumentSub]

/-- Changing every argument commutes with replay when that change commutes
with simultaneous schema instantiation. Refusals are preserved as well. -/
theorem decode_mapArguments (table : SchemaTable Head) (enabled : Fin table.length → Bool)
    (map : Tm Head n → Tm Head m)
    (commutes : ∀ {arity : Nat} (substitution : Sub Head arity n) (term : Tm Head arity),
      subst (fun index => map (substitution index)) term = map (subst substitution term))
    (code : Code Head n) :
    decode table enabled (code.mapArguments map) =
      (decode table enabled code).map (fun endpoints => (map endpoints.1, map endpoints.2)) := by
  by_cases bound : code.row < table.length
  · by_cases permitted : enabled ⟨code.row, bound⟩ = true
    · by_cases length : code.arguments.length = (table.get ⟨code.row, bound⟩).1
      · simp [decode, decodeInstance, Code.mapArguments, bound, permitted, length,
          Instance.endpoints, argumentSub_map, commutes]
      · simp only [List.get_eq_getElem] at length
        simp [decode, decodeInstance, Code.mapArguments, bound, permitted, length, List.length_map]
    · simp [decode, decodeInstance, Code.mapArguments, bound, permitted]
  · simp [decode, decodeInstance, Code.mapArguments, bound]

def Code.rename (rho : Ren n m) (code : Code Head n) : Code Head m :=
  code.mapArguments (Presentation.rename rho)

def Code.substitute (sigma : Sub Head n m) (code : Code Head n) : Code Head m :=
  code.mapArguments (subst sigma)

theorem decode_rename (table : SchemaTable Head) (enabled : Fin table.length → Bool)
    (rho : Ren n m) (code : Code Head n) :
    decode table enabled (code.rename rho) =
      (decode table enabled code).map
        (fun endpoints => (rename rho endpoints.1, rename rho endpoints.2)) :=
  decode_mapArguments table enabled (rename rho)
    (fun _ _ => by rw [rename_subst]) code

theorem decode_substitute (table : SchemaTable Head) (enabled : Fin table.length → Bool)
    (sigma : Sub Head n m) (code : Code Head n) :
    decode table enabled (code.substitute sigma) =
      (decode table enabled code).map
        (fun endpoints => (subst sigma endpoints.1, subst sigma endpoints.2)) :=
  decode_mapArguments table enabled (subst sigma)
    (fun _ _ => by rw [subst_comp]) code

end SchemaTableConversionCode
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

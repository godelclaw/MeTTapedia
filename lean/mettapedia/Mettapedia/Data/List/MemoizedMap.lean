import Mathlib.Data.List.Basic

/-!
# Ordered mapping with one retained computation

The retained entry stores a function value, while reconstruction runs once for
every input occurrence. Equal keys therefore share work without identifying
outputs or their provenance. The account counts calls of `compute`; key
comparison and reconstruction are separate costs.
-/

set_option autoImplicit false

namespace List.MemoizedMap

universe u v w z
variable {Input : Type u} {Key : Type v} {Value : Type w} {Output : Type z}

structure Entry (Key : Type v) (Value : Type w) where
  key : Key
  value : Value
  deriving Repr, DecidableEq

def Valid (compute : Key → Value) (cache : Option (Entry Key Value)) : Prop :=
  ∀ entry, cache = some entry → entry.value = compute entry.key

@[simp] theorem valid_none (compute : Key → Value) : Valid compute none := by
  intro entry impossible
  contradiction

def access [DecidableEq Key] (compute : Key → Value) (key : Key)
    (cache : Option (Entry Key Value)) : Value × Entry Key Value × Nat :=
  match cache with
  | some entry =>
      if entry.key = key then (entry.value, entry, 0)
      else (compute key, ⟨key, compute key⟩, 1)
  | none => (compute key, ⟨key, compute key⟩, 1)

theorem access_exact [DecidableEq Key] (compute : Key → Value) (key : Key)
    (cache : Option (Entry Key Value)) (valid : Valid compute cache) :
    (access compute key cache).1 = compute key ∧
      Valid compute (some (access compute key cache).2.1) ∧
      (access compute key cache).2.1.key = key := by
  cases cache with
  | none => simp [access, Valid]
  | some entry =>
      have same := valid entry rfl
      by_cases hit : entry.key = key
      · simp [access, hit, Valid, same]
      · simp [access, hit, Valid]

def run [DecidableEq Key] (key : Input → Key) (compute : Key → Value)
    (reconstruct : Input → Value → Output) :
    List Input → Option (Entry Key Value) → List Output × Option (Entry Key Value) × Nat
  | [], cache => ([], cache, 0)
  | input :: rest, cache =>
      let (value, next, calls) := access compute (key input) cache
      let (outputs, final, later) := run key compute reconstruct rest (some next)
      (reconstruct input value :: outputs, final, calls + later)

theorem run_exact [DecidableEq Key] (key : Input → Key) (compute : Key → Value)
    (reconstruct : Input → Value → Output) (inputs : List Input)
    (cache : Option (Entry Key Value)) (valid : Valid compute cache) :
    (run key compute reconstruct inputs cache).1 =
      inputs.map (fun input => reconstruct input (compute (key input))) ∧
      Valid compute (run key compute reconstruct inputs cache).2.1 := by
  induction inputs generalizing cache with
  | nil => exact ⟨rfl, valid⟩
  | cons input rest ih =>
      have step := access_exact compute (key input) cache valid
      have later := ih _ step.2.1
      simp only [run, List.map_cons]
      exact ⟨by rw [step.1, later.1], later.2⟩

theorem calls_le_length [DecidableEq Key] (key : Input → Key) (compute : Key → Value)
    (reconstruct : Input → Value → Output) (inputs : List Input)
    (cache : Option (Entry Key Value)) :
    (run key compute reconstruct inputs cache).2.2 ≤ inputs.length := by
  induction inputs generalizing cache with
  | nil => simp [run]
  | cons input rest ih =>
      have later := ih (some (access compute (key input) cache).2.1)
      have current : (access compute (key input) cache).2.2 ≤ 1 := by
        cases cache with
        | none => simp [access]
        | some entry => simp only [access]; split <;> simp
      change (access compute (key input) cache).2.2 +
        (run key compute reconstruct rest (some (access compute (key input) cache).2.1)).2.2 ≤
          rest.length + 1
      omega

theorem access_changed_key [DecidableEq Key] (compute : Key → Value)
    (entry : Entry Key Value) (key : Key) (changed : entry.key ≠ key) :
    access compute key (some entry) = (compute key, ⟨key, compute key⟩, 1) := by
  simp [access, changed]

theorem adjacent_same_key_calls [DecidableEq Key] (key : Input → Key)
    (compute : Key → Value) (reconstruct : Input → Value → Output)
    (first second : Input) (same : key first = key second) :
    (run key compute reconstruct [first, second] none).2.2 = 1 := by
  simp [run, access, same]

/-- Reconstruction sees both distinct input occurrences even when their
expensive key computation is shared. -/
example : run Prod.snd (fun key : Nat => key + 10)
    (fun (input : Nat × Nat) value => (input.1, value)) [(3, 7), (9, 7), (3, 7)] none =
      ([(3, 17), (9, 17), (3, 17)], some ⟨7, 17⟩, 1) := by decide

/-- The one-entry bound does not pretend to retain evicted keys. -/
example : (run id (fun key : Nat => key) (fun _ value => value) [1, 2, 1] none).2.2 = 3 := by decide

end List.MemoizedMap

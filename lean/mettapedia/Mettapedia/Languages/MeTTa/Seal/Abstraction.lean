import Mettapedia.Languages.MeTTa.Seal.Observation
import Mathlib.Data.List.Dedup

/-!
# Representation independence for sealed modules

A module implements an abstract data type with a seal: an abstract value leaves
the module as a sealed value (a handle with the module's nickname) and comes back
through `unseal`; a sealed value the module did not issue gives no result.

**Theorem** (`sealed_indistinguishable`). If two implementations of an abstract
data type are related by a simulation (related arguments give equal data and
related abstract values), their sealed modules are bisimilar under partial
bijections of handles. So no client parametric for identity, and therefore no
printing client, tells them apart (`Bisim.indistinguishable`): this is the
statement "a client without the unsealer cannot tell the implementations
apart", for the observer model of `Seal.Observation`.

**Instance** (`sets_indistinguishable`). Finite sets of integers kept without
duplicates, and kept with duplicates that `elements` removes. Their contents
differ for the same set (`[1]` against `[1, 1]`), and `elements` returns
members in different orders.

**What each excluded channel breaks**, on this same pair, with a printing
client (`Controls`):
* content equality of sealed values (a runtime `==` that compares contents,
  as HE and CeTTa compare state cells today): distinguishes;
* an exported unsealer, or a foreign function that reads a sealed value's
  memory: distinguishes;
* the cost of a call (timing): distinguishes;
* reflection on the module's code: distinguishes.

Simplification of the model: a request `(op a₁ … aₙ)` is read as its data
arguments and its sealed arguments, each in order; the interleaving of the two
kinds is not observed by the operation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Seal

/-- A result of an abstract operation: one new abstract value, or a multiset of
data. -/
inductive Out (T : Type) where
  | abstract (t : T)
  | plain (vs : Multiset Shown)

/-- An abstract data type: a carrier and operations, named by symbols, on data
arguments and abstract arguments. -/
structure Adt where
  Carrier : Type
  apply : String → List Shown → List Carrier → Out Carrier

/-- The private state of a sealed module: the content of each issued handle, and
the next handle. -/
structure SealedState (T : Type) where
  store : Nat → Option T
  next : Nat

/-- Read one argument: data without handles as data; a sealed value of this
module, by nickname and issued handle, as its content. A handle inside data, a
sealed value of another nickname, or a handle never issued gives nothing. -/
def readOne {T : Type} (nick : String) (store : Nat → Option T) : Shown → Option (Shown ⊕ T)
  | .boxed n h => if n = nick then (store h).map Sum.inr else none
  | .sym name => some (.inl (.sym name))
  | .num value => some (.inl (.num value))
  | .nil => some (.inl .nil)
  | .cons a b => if (Shown.cons a b).handles = [] then some (.inl (.cons a b)) else none

/-- Read the arguments of a request, written as a list: its data arguments and
its abstract arguments, each in order. -/
def readArgs {T : Type} (nick : String) (store : Nat → Option T) : Shown → Option (List Shown × List T)
  | .nil => some ([], [])
  | .cons a rest =>
      match readOne nick store a, readArgs nick store rest with
      | some (.inl d), some (ds, xs) => some (d :: ds, xs)
      | some (.inr t), some (ds, xs) => some (ds, t :: xs)
      | _, _ => none
  | .sym _ => none
  | .num _ => none
  | .boxed _ _ => none

/-- Answer an operation's result: a new abstract value is sealed under a fresh
handle; data is returned as it is. -/
def answer {T : Type} (nick : String) (s : SealedState T) : Out T → Multiset Shown × SealedState T
  | .abstract t => ({.boxed nick s.next}, ⟨Function.update s.store s.next (some t), s.next + 1⟩)
  | .plain vs => (vs, s)

/-- The module that implements an abstract data type with a seal. -/
def Adt.sealed (A : Adt) (nick : String) : Impl where
  State := SealedState A.Carrier
  init := ⟨fun _ => none, 0⟩
  call s q :=
    match q with
    | .cons (.sym op) args =>
        match readArgs nick s.store args with
        | some (ds, xs) => answer nick s (A.apply op ds xs)
        | none => (0, s)
    | _ => (0, s)

theorem Adt.sealed_call (A : Adt) (nick : String) (s : SealedState A.Carrier) (op : String)
    (args : Shown) :
    (A.sealed nick).call s (.cons (.sym op) args) =
      match readArgs nick s.store args with
      | some (ds, xs) => answer nick s (A.apply op ds xs)
      | none => (0, s) := rfl

/-- Related results: equal data without handles, or related abstract values. -/
inductive OutRel {T₁ T₂ : Type} (S : T₁ → T₂ → Prop) : Out T₁ → Out T₂ → Prop
  | plain (vs : Multiset Shown) : (∀ v ∈ vs, v.handles = []) → OutRel S (.plain vs) (.plain vs)
  | abstract {t₁ t₂} : S t₁ t₂ → OutRel S (.abstract t₁) (.abstract t₂)

/-- A simulation: the same data and related abstract arguments give related
results. -/
def Adt.Simulation (A₁ A₂ : Adt) (S : A₁.Carrier → A₂.Carrier → Prop) : Prop :=
  ∀ op ds xs ys, List.Forall₂ S xs ys → OutRel S (A₁.apply op ds xs) (A₂.apply op ds ys)

/-- Related arguments read by `readOne`. -/
def OneRel {T₁ T₂ : Type} (S : T₁ → T₂ → Prop) : Shown ⊕ T₁ → Shown ⊕ T₂ → Prop
  | .inl d₁, .inl d₂ => d₁ = d₂
  | .inr t₁, .inr t₂ => S t₁ t₂
  | _, _ => False

/-- The bisimulation of sealed modules: the issued handles correspond one to
one, and corresponding handles hold related contents. -/
structure SealedRel {T₁ T₂ : Type} (S : T₁ → T₂ → Prop) (s₁ : SealedState T₁)
    (s₂ : SealedState T₂) (R : Nat → Nat → Prop) : Prop where
  bij : PartialBijection R
  bounded : ∀ a b, R a b → a < s₁.next ∧ b < s₂.next
  stored : ∀ a b, R a b → ∃ t₁ t₂, s₁.store a = some t₁ ∧ s₂.store b = some t₂ ∧ S t₁ t₂

section Reading

variable {T₁ T₂ : Type} {S : T₁ → T₂ → Prop} {s₁ : SealedState T₁} {s₂ : SealedState T₂}
  {R : Nat → Nat → Prop}

theorem readOne_rel (sr : SealedRel S s₁ s₂ R) (nick : String) {v₁ v₂ : Shown}
    (rel : Shown.Rel R v₁ v₂) :
    Option.Rel (OneRel S) (readOne nick s₁.store v₁) (readOne nick s₂.store v₂) := by
  cases rel with
  | sym name => exact .some rfl
  | num value => exact .some rfl
  | nil => exact .some rfl
  | @cons a₁ b₁ a₂ b₂ relA relB =>
      simp only [readOne]
      by_cases plain : (Shown.cons a₁ b₁).handles = []
      · have same := (Shown.Rel.cons relA relB).eq_of_plain plain
        rw [same]
        simp only [plain, ↓reduceIte]
        exact .some rfl
      · have plain₂ : (Shown.cons a₂ b₂).handles ≠ [] := by
          intro empty
          have lengths := (Shown.Rel.cons relA relB).handles.length_eq
          rw [empty, List.length_nil, List.length_eq_zero_iff] at lengths
          exact plain lengths
        simp only [plain, plain₂, ↓reduceIte]
        exact .none
  | @boxed nick' h₁ h₂ related =>
      simp only [readOne]
      by_cases mine : nick' = nick
      · rw [if_pos mine, if_pos mine]
        obtain ⟨t₁, t₂, at₁, at₂, st⟩ := sr.stored h₁ h₂ related
        rw [at₁, at₂]
        exact .some st
      · rw [if_neg mine, if_neg mine]
        exact .none

/-- Related arguments read to the same data and related abstract values. -/
def ArgsRel (S : T₁ → T₂ → Prop) (p₁ : List Shown × List T₁) (p₂ : List Shown × List T₂) : Prop :=
  p₁.1 = p₂.1 ∧ List.Forall₂ S p₁.2 p₂.2

theorem readArgs_rel (sr : SealedRel S s₁ s₂ R) (nick : String) {a₁ a₂ : Shown}
    (rel : Shown.Rel R a₁ a₂) :
    Option.Rel (ArgsRel S) (readArgs nick s₁.store a₁) (readArgs nick s₂.store a₂) := by
  induction rel with
  | sym name => exact .none
  | num value => exact .none
  | nil => exact .some ⟨rfl, .nil⟩
  | boxed nick' related => exact .none
  | @cons x₁ y₁ x₂ y₂ relX _ _ ihY =>
      simp only [readArgs]
      have one := readOne_rel sr nick relX
      generalize readOne nick s₁.store x₁ = o₁ at one ⊢
      generalize readOne nick s₂.store x₂ = o₂ at one ⊢
      generalize readArgs nick s₁.store y₁ = r₁ at ihY ⊢
      generalize readArgs nick s₂.store y₂ = r₂ at ihY ⊢
      cases one with
      | none => exact .none
      | some oneRel =>
          rename_i z₁ z₂
          cases ihY with
          | none => cases z₁ <;> cases z₂ <;> exact .none
          | some restRel =>
              rename_i p₁ p₂
              obtain ⟨ds₁, xs₁⟩ := p₁
              obtain ⟨ds₂, xs₂⟩ := p₂
              obtain ⟨sameDs, relXs⟩ := restRel
              cases z₁ <;> cases z₂ <;> simp only [OneRel] at oneRel
              · subst oneRel
                exact .some ⟨congrArg _ sameDs, relXs⟩
              · exact .some ⟨sameDs, .cons oneRel relXs⟩

end Reading

/-- One call of the two sealed modules, from related states on related
requests. -/
theorem sealed_call_rel {A₁ A₂ : Adt} {S : A₁.Carrier → A₂.Carrier → Prop}
    (sim : A₁.Simulation A₂ S) (nick : String) {s₁ : SealedState A₁.Carrier}
    {s₂ : SealedState A₂.Carrier} {R : Nat → Nat → Prop} (sr : SealedRel S s₁ s₂ R)
    {q₁ q₂ : Shown} (rel : Shown.Rel R q₁ q₂) :
    ∃ R', (∀ a b, R a b → R' a b) ∧
      SealedRel S ((A₁.sealed nick).call s₁ q₁).2 ((A₂.sealed nick).call s₂ q₂).2 R' ∧
      Multiset.Rel (Shown.Rel R') ((A₁.sealed nick).call s₁ q₁).1 ((A₂.sealed nick).call s₂ q₂).1 := by
  have keep : ∃ R', (∀ a b, R a b → R' a b) ∧ SealedRel S s₁ s₂ R' ∧
      Multiset.Rel (Shown.Rel R') (0 : Multiset Shown) 0 :=
    ⟨R, fun _ _ r => r, sr, Multiset.Rel.zero⟩
  rcases rel with name | value | _ | ⟨relHead, relArgs⟩ | ⟨nick', related⟩
  · exact keep
  · exact keep
  · exact keep
  · rcases relHead with op | value | _ | ⟨_, _⟩ | ⟨_, _⟩
    · rename_i args₁ args₂
      rw [Adt.sealed_call, Adt.sealed_call]
      have read := readArgs_rel sr nick relArgs
      generalize readArgs nick s₁.store args₁ = r₁ at read ⊢
      generalize readArgs nick s₂.store args₂ = r₂ at read ⊢
      cases read with
      | none => exact keep
      | some argsRel =>
          rename_i p₁ p₂
          obtain ⟨ds₁, xs₁⟩ := p₁
          obtain ⟨ds₂, xs₂⟩ := p₂
          obtain ⟨sameDs, relXs⟩ := argsRel
          simp only at sameDs relXs
          subst sameDs
          dsimp only
          have out := sim op ds₁ xs₁ xs₂ relXs
          generalize A₁.apply op ds₁ xs₁ = out₁ at out ⊢
          generalize A₂.apply op ds₁ xs₂ = out₂ at out ⊢
          cases out with
          | plain vs plain =>
              dsimp only [answer]
              exact ⟨R, fun _ _ r => r, sr,
                Multiset.rel_refl_of_refl_on fun v member => Shown.Rel.refl_of_plain R (plain v member)⟩
          | @abstract t₁ t₂ st =>
              dsimp only [answer]
              refine ⟨fun a b => R a b ∨ (a = s₁.next ∧ b = s₂.next), fun a b r => Or.inl r, ?_, ?_⟩
              · refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
                · rintro a b b' (r | ⟨ha, hb⟩) (r' | ⟨ha', hb'⟩)
                  · exact sr.bij.functional a b b' r r'
                  · exact absurd ha' (Nat.ne_of_lt (sr.bounded a b r).1)
                  · exact absurd ha (Nat.ne_of_lt (sr.bounded a b' r').1)
                  · rw [hb, hb']
                · rintro a a' b (r | ⟨ha, hb⟩) (r' | ⟨ha', hb'⟩)
                  · exact sr.bij.injective a a' b r r'
                  · exact absurd hb' (Nat.ne_of_lt (sr.bounded a b r).2)
                  · exact absurd hb (Nat.ne_of_lt (sr.bounded a' b r').2)
                  · rw [ha, ha']
                · rintro a b (r | ⟨rfl, rfl⟩)
                  · have bound := sr.bounded a b r
                    exact ⟨Nat.lt_succ_of_lt bound.1, Nat.lt_succ_of_lt bound.2⟩
                  · exact ⟨Nat.lt_succ_self _, Nat.lt_succ_self _⟩
                · rintro a b (r | ⟨rfl, rfl⟩)
                  · obtain ⟨u₁, u₂, at₁, at₂, su⟩ := sr.stored a b r
                    have bound := sr.bounded a b r
                    refine ⟨u₁, u₂, ?_, ?_, su⟩
                    · show Function.update s₁.store s₁.next (some t₁) a = some u₁
                      rw [Function.update_of_ne (Nat.ne_of_lt bound.1)]
                      exact at₁
                    · show Function.update s₂.store s₂.next (some t₂) b = some u₂
                      rw [Function.update_of_ne (Nat.ne_of_lt bound.2)]
                      exact at₂
                  · exact ⟨t₁, t₂, by simp, by simp, st⟩
              · exact Multiset.Rel.cons (Shown.Rel.boxed nick (Or.inr ⟨rfl, rfl⟩)) Multiset.Rel.zero
    all_goals exact keep
  · exact keep

/-- **Sealed modules of simulating implementations are bisimilar**, under partial
bijections of handles. -/
def sealedBisim {A₁ A₂ : Adt} {S : A₁.Carrier → A₂.Carrier → Prop} (sim : A₁.Simulation A₂ S)
    (nick : String) : Bisim PartialBijection (A₁.sealed nick) (A₂.sealed nick) where
  rel s₁ s₂ R := SealedRel S s₁ s₂ R
  adm _ _ _ sr := sr.bij
  start := ⟨fun _ _ => False, ⟨⟨fun _ _ _ r => r.elim, fun _ _ _ r => r.elim⟩,
    fun _ _ r => r.elim, fun _ _ r => r.elim⟩⟩
  step _ _ _ _ _ sr rel := sealed_call_rel sim nick sr rel

/-- Fewer relations to respect means more clients. -/
theorem Indistinguishable.weaken {Adm Adm' : (Nat → Nat → Prop) → Prop}
    (contained : ∀ R, Adm R → Adm' R) {I₁ I₂ : Impl} (same : Indistinguishable Adm I₁ I₂) :
    Indistinguishable Adm' I₁ I₂ :=
  fun o param fuel => same o (fun R adm h₁ h₂ hist => param R (contained R adm) h₁ h₂ hist) fuel

/-- **Representation independence through sealing.** No client that compares
sealed values by identity, and so no printing client, tells apart the sealed
modules of two simulating implementations. -/
theorem sealed_indistinguishable {A₁ A₂ : Adt} {S : A₁.Carrier → A₂.Carrier → Prop}
    (sim : A₁.Simulation A₂ S) (nick : String) :
    Indistinguishable PartialBijection (A₁.sealed nick) (A₂.sealed nick) :=
  (sealedBisim sim nick).indistinguishable partialBijection_closed

theorem sealed_indistinguishable_printing {A₁ A₂ : Adt} {S : A₁.Carrier → A₂.Carrier → Prop}
    (sim : A₁.Simulation A₂ S) (nick : String) :
    Indistinguishable AnyRelation (A₁.sealed nick) (A₂.sealed nick) :=
  (sealed_indistinguishable sim nick).weaken fun _ _ => trivial

/-! ## Finite sets, kept with and without duplicates -/

/-- A representation of finite sets of integers. -/
structure SetRep where
  empty : List Int
  insert : Int → List Int → List Int
  elements : List Int → List Int

/-- `(empty)`, `(insert N S)` and `(elements S)`; anything else answers nothing. -/
def SetRep.answer (r : SetRep) (op : String) : List (List Int) → List Shown → Out (List Int)
  | [], [] => if op = "empty" then .abstract r.empty else .plain 0
  | [s], [.num n] => if op = "insert" then .abstract (r.insert n s) else .plain 0
  | [s], [] => if op = "elements" then .plain ((r.elements s).map Shown.num : List Shown) else .plain 0
  | _, _ => .plain 0

abbrev SetRep.adt (r : SetRep) : Adt where
  Carrier := List Int
  apply op ds xs := r.answer op xs ds

/-- Sets without duplicates. -/
def noDuplicates : SetRep where
  empty := []
  insert n s := if n ∈ s then s else n :: s
  elements s := s

/-- Sets with duplicates; `elements` removes them. -/
def withDuplicates : SetRep where
  empty := []
  insert n s := n :: s
  elements s := s.dedup

/-- The same set: the first representation has no duplicates and the same
members. -/
def sameSet (t₁ t₂ : List Int) : Prop := t₁.Nodup ∧ ∀ x, x ∈ t₁ ↔ x ∈ t₂

theorem nums_plain (l : List Int) : ∀ v ∈ ((l.map Shown.num : List Shown) : Multiset Shown),
    v.handles = [] := by
  intro v member
  obtain ⟨n, _, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp member)
  rfl

theorem sets_simulation : noDuplicates.adt.Simulation withDuplicates.adt sameSet := by
  intro op ds xs ys rel
  have zero : OutRel sameSet (.plain 0 : Out (List Int)) (.plain 0) :=
    OutRel.plain 0 (by simp)
  show OutRel sameSet (noDuplicates.answer op xs ds) (withDuplicates.answer op ys ds)
  cases rel with
  | nil =>
      rcases ds with _ | ⟨d, rest⟩
      · simp only [SetRep.answer, noDuplicates, withDuplicates]
        split_ifs
        · exact OutRel.abstract ⟨List.nodup_nil, fun _ => Iff.rfl⟩
        · exact zero
      · exact zero
  | @cons t₁ t₂ rest₁ rest₂ same tail =>
      cases tail with
      | cons _ _ => exact zero
      | nil =>
          rcases ds with _ | ⟨d, _ | ⟨e, rest⟩⟩
          · simp only [SetRep.answer, noDuplicates, withDuplicates]
            split_ifs
            · have perm : t₁.Perm t₂.dedup :=
                (List.perm_ext_iff_of_nodup same.1 (List.nodup_dedup t₂)).mpr
                  fun x => (same.2 x).trans List.mem_dedup.symm
              have equal : ((t₁.map Shown.num : List Shown) : Multiset Shown) =
                  ((t₂.dedup.map Shown.num : List Shown) : Multiset Shown) :=
                Multiset.coe_eq_coe.mpr (perm.map Shown.num)
              rw [equal]
              exact OutRel.plain _ (nums_plain _)
            · exact zero
          · cases d with
            | num n =>
                simp only [SetRep.answer, noDuplicates, withDuplicates]
                split_ifs with insert member
                · refine OutRel.abstract ⟨same.1, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
                  · exact List.mem_cons_of_mem n ((same.2 x).mp hx)
                  · rcases List.mem_cons.mp hx with rfl | later
                    · exact member
                    · exact (same.2 x).mpr later
                · refine OutRel.abstract ⟨List.nodup_cons.mpr ⟨member, same.1⟩, fun x => ?_⟩
                  simp only [List.mem_cons]
                  exact or_congr Iff.rfl (same.2 x)
                · exact zero
            | _ => exact zero
          · cases d <;> exact zero

/-- **Sets with and without duplicates are indistinguishable** through their
seals, even by clients that compare sealed values by identity. -/
theorem sets_indistinguishable :
    Indistinguishable PartialBijection (noDuplicates.adt.sealed "set") (withDuplicates.adt.sealed "set") :=
  sealed_indistinguishable sets_simulation "set"

/-! ## Controls: what each excluded channel breaks -/

namespace Controls

/-- Integers as a MeTTa list. -/
def intList : List Int → Shown
  | [] => .nil
  | n :: rest => .cons (.num n) (intList rest)

/-- A set module that answers one more request than the abstract data type:
the channel under test. -/
def withChannel (r : SetRep) (channel : String → List (List Int) → Option (Out (List Int))) :
    Impl :=
  ({ Carrier := List Int, apply := fun op ds xs => (channel op xs).getD (r.answer op xs ds) } : Adt).sealed
    "set"

/-- A runtime `==` that compares sealed contents. -/
def contentEquality (op : String) : List (List Int) → Option (Out (List Int))
  | [s, t] => if op = "same-content" then
      some (.plain {.sym (if s = t then "True" else "False")}) else none
  | _ => none

/-- An exported unsealer, or a foreign function that reads a sealed value's
memory. -/
def rawRead (op : String) : List (List Int) → Option (Out (List Int))
  | [s] => if op = "raw" then some (.plain {intList s}) else none
  | _ => none

/-- The cost of `elements`: one step per stored entry. -/
def timing (op : String) : List (List Int) → Option (Out (List Int))
  | [s] => if op = "steps" then some (.plain {.num s.length}) else none
  | _ => none

/-- Reflection on the module's code: the text of its `insert`. -/
def reflection (code : String) (op : String) : List (List Int) → Option (Out (List Int))
  | [] => if op = "reflect" then some (.plain {.sym code}) else none
  | _ => none

/-- `(empty)`, then `(insert 1 S)` twice, then a probe on the results. -/
def script (probe : Template) : List Template :=
  [ .lit (.cons (.sym "empty") .nil),
    .cons (.lit (.sym "insert")) (.cons (.lit (.num 1)) (.cons (.pick 0 0 []) (.lit .nil))),
    .cons (.lit (.sym "insert")) (.cons (.lit (.num 1)) (.cons (.pick 1 0 []) (.lit .nil))),
    probe ]

/-- A printing client that runs the script and says whether the last answer is
`expected`. It neither compares sealed values nor sees their contents. -/
def scriptClient (probe : Template) (expected : Shown) : PrintingClient where
  strategy printed := (script probe)[printed.length]?
  verdict printed := decide ((printed.getLast?.bind List.head?) = some expected)

def probeSameContent : Template :=
  .cons (.lit (.sym "same-content")) (.cons (.pick 1 0 []) (.cons (.pick 2 0 []) (.lit .nil)))
def probeRaw : Template := .cons (.lit (.sym "raw")) (.cons (.pick 2 0 []) (.lit .nil))
def probeSteps : Template := .cons (.lit (.sym "steps")) (.cons (.pick 2 0 []) (.lit .nil))
def probeReflect : Template := .cons (.lit (.sym "reflect")) (.lit .nil)

/-- The empty start of a set module. -/
def start : SealedState (List Int) := ⟨fun _ => none, 0⟩

/-- **Content equality distinguishes.** With a runtime `==` that compares sealed
contents, `{1}` inserted twice is `[1]` for one module and `[1, 1]` for the
other. -/
theorem contentEquality_distinguishes :
    outcomes (scriptClient probeSameContent (.sym "True")).observer
        (withChannel noDuplicates contentEquality) 5 start [] = {true} ∧
      outcomes (scriptClient probeSameContent (.sym "True")).observer
        (withChannel withDuplicates contentEquality) 5 start [] = {false} := by
  constructor
  all_goals
    refine outcomes_single_eq (by rfl) (by rfl) ?_
    refine outcomes_single_eq (by rfl) (by rfl) ?_
    refine outcomes_single_eq (by rfl) (by rfl) ?_
    refine outcomes_single_eq (by rfl) (by rfl) ?_
    refine outcomes_stop_eq (by rfl) ?_
    rfl

/-- **An exported unsealer, or a foreign read, distinguishes.** -/
theorem rawRead_distinguishes :
    outcomes (scriptClient probeRaw (intList [1])).observer
        (withChannel noDuplicates rawRead) 5 start [] = {true} ∧
      outcomes (scriptClient probeRaw (intList [1])).observer
        (withChannel withDuplicates rawRead) 5 start [] = {false} := by
  constructor
  all_goals
    refine outcomes_single_eq (by rfl) (by rfl) ?_
    refine outcomes_single_eq (by rfl) (by rfl) ?_
    refine outcomes_single_eq (by rfl) (by rfl) ?_
    refine outcomes_single_eq (by rfl) (by rfl) ?_
    refine outcomes_stop_eq (by rfl) ?_
    rfl

/-- **Timing distinguishes**: the cost of reading the set depends on the
representation. -/
theorem timing_distinguishes :
    outcomes (scriptClient probeSteps (.num 1)).observer
        (withChannel noDuplicates timing) 5 start [] = {true} ∧
      outcomes (scriptClient probeSteps (.num 1)).observer
        (withChannel withDuplicates timing) 5 start [] = {false} := by
  constructor
  all_goals
    refine outcomes_single_eq (by rfl) (by rfl) ?_
    refine outcomes_single_eq (by rfl) (by rfl) ?_
    refine outcomes_single_eq (by rfl) (by rfl) ?_
    refine outcomes_single_eq (by rfl) (by rfl) ?_
    refine outcomes_stop_eq (by rfl) ?_
    rfl

/-- **Reflection distinguishes**: the two modules' code differs. -/
theorem reflection_distinguishes :
    outcomes (scriptClient probeReflect (.sym "dedup-insert")).observer
        (withChannel noDuplicates (reflection "dedup-insert")) 5 start [] = {true} ∧
      outcomes (scriptClient probeReflect (.sym "dedup-insert")).observer
        (withChannel withDuplicates (reflection "cons-insert")) 5 start [] = {false} := by
  constructor
  all_goals
    refine outcomes_single_eq (by rfl) (by rfl) ?_
    refine outcomes_single_eq (by rfl) (by rfl) ?_
    refine outcomes_single_eq (by rfl) (by rfl) ?_
    refine outcomes_single_eq (by rfl) (by rfl) ?_
    refine outcomes_stop_eq (by rfl) ?_
    rfl

/-- **Without a channel, the same client sees the same thing.** The set modules
of the theorem answer the probes with nothing; the run is the same for both. -/
theorem no_channel_same :
    outcomes (scriptClient probeSameContent (.sym "True")).observer
        (noDuplicates.adt.sealed "set") 5 start [] =
      outcomes (scriptClient probeSameContent (.sym "True")).observer
        (withDuplicates.adt.sealed "set") 5 start [] :=
  sealed_indistinguishable_printing sets_simulation "set" _
    (scriptClient probeSameContent (.sym "True")).parametric 5

end Controls

end Mettapedia.Languages.MeTTa.Seal

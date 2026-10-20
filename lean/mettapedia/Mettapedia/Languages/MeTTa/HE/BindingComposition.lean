import Mettapedia.Languages.MeTTa.HE.Matching
import Mettapedia.Languages.MeTTa.HE.EqualityClosure
import Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge
import Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory

/-!
# Binding Composition: Monotonic Extension Under Pattern Matching

Proves that `simpleMatch` **extends** seed bindings monotonically: the result
bindings contain all seed entries plus new ones from the match. This is the
correct abstraction — not individual lookup preservation, but a general
extension relation.

## Architecture

Ported from the translation proof at `HEPeTTaSound.lean:491-714` where
`HEBindingsExtends` + `simpleMatch_extends` were proved as private lemmas.
Now promoted to HE core infrastructure for reuse by:
- candidate selection correctness
- cache/materialization preservation
- co-reference preservation under rematch

## Key Results

- `Bindings.Extends` — monotonicity: all seed lookups preserved
- `extends_refl` / `extends_trans` — preorder
- `extends_assign_of_lookup_none` — assigning a fresh var extends
- `simpleMatch_extends` — THE mutual induction: simpleMatch extends bindings
- `simpleMatch_preserves_seed` — corollary: seed lookup preserved

## Connection to CeTTa

Maps to `space_match_backend.c`: seed bindings from prior context survive rematch.
Maps to `table_store.c`: goal bindings survive materialization.
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-- Ground atoms: no variables anywhere.  The substrate for the
bindings-irrelevance induction (design-note T10): on ground atoms,
official result *atoms* are independent of the incoming bindings
thread, which is what lets the master absorption theorem be stated on
result atoms across equation steps in element position. -/
inductive GroundAtom : Atom → Prop where
  | symbol (s : String) : GroundAtom (.symbol s)
  | grounded (g : GroundedValue) : GroundAtom (.grounded g)
  | expression {es : List Atom} (h : ∀ e ∈ es, GroundAtom e) :
      GroundAtom (.expression es)

theorem GroundAtom.not_var {v : String} : ¬ GroundAtom (.var v) := by
  rintro ⟨⟩

theorem GroundAtom.elem {es : List Atom} {e : Atom}
    (h : GroundAtom (.expression es)) (h_mem : e ∈ es) : GroundAtom e := by
  cases h with
  | expression h_elems => exact h_elems e h_mem

/-- Positive and negative examples. -/
example : GroundAtom (.expression [.symbol "f", .grounded (.int 5)]) :=
  .expression (by
    intro e he
    rcases List.mem_cons.mp he with rfl | he'
    · exact .symbol _
    rcases List.mem_cons.mp he' with rfl | he''
    · exact .grounded _
    · cases he'')

example : ¬ GroundAtom (.expression [.symbol "f", .var "x"]) := by
  intro h
  exact GroundAtom.not_var (v := "x") (h.elem (by simp))

/-- Bindings with ground assignment values and no equalities. -/
def GroundBindings (b : Bindings) : Prop :=
  (∀ p ∈ b.assignments, GroundAtom p.2) ∧ b.equalities = []

theorem GroundBindings.empty : GroundBindings Bindings.empty :=
  ⟨by simp [Bindings.empty], rfl⟩

theorem GroundBindings.assign {b : Bindings} {v : String} {val : Atom}
    (hb : GroundBindings b) (hval : GroundAtom val) :
    GroundBindings (b.assign v val) := by
  refine ⟨?_, hb.2⟩
  intro p hp
  simp only [Bindings.assign] at hp
  split at hp
  · obtain ⟨q, hq, hpq⟩ := List.mem_map.mp hp
    split at hpq
    · exact hpq ▸ hval
    · exact hpq ▸ hb.1 q hq
  · rcases List.mem_append.mp hp with h | h
    · exact hb.1 p h
    · simp at h
      rw [h]
      exact hval

open Mettapedia.Languages.MeTTa.SubstitutionAlgebra in
theorem GroundAtom.vars_eq_nil {atom : Atom} (ground : GroundAtom atom) :
    Mettapedia.Languages.MeTTa.SubstitutionAlgebra.vars atom = [] := by
  induction ground with
  | symbol => rfl
  | grounded => rfl
  | @expression atoms children ih =>
      change vars.varsList atoms = []
      have lists : ∀ xs : List Atom, (∀ x ∈ xs, vars x = []) → vars.varsList xs = [] := by
        intro xs
        induction xs with
        | nil => intro _; rfl
        | cons head tail rest =>
            intro each
            simp only [vars.varsList, each head (by simp), List.nil_append]
            exact rest (fun x hx => each x (by simp [hx]))
      exact lists atoms ih

/-- Ground assignment values cannot create a class dependency. Equality edges
only identify names and do not introduce value dependencies by themselves. -/
theorem GroundBindings.hasLoop_false {b : Bindings} (hb : GroundBindings b) :
    b.hasLoop = false :=
  b.hasLoop_false_of_assignment_vars_nil (fun entry member => (hb.1 entry member).vars_eq_nil)

/-! ## §1: The extension relation -/

/-- `result` **extends** `seed`: every lookup in `seed` is preserved in `result`.
    This is the monotonicity invariant for pattern matching. -/
def Bindings.Extends (seed result : Bindings) : Prop :=
  ∀ x a, seed.lookup x = some a → result.lookup x = some a

/-- Extension is reflexive. -/
theorem Bindings.extends_refl (b : Bindings) : b.Extends b :=
  fun _ _ h => h

/-- Extension is transitive. -/
theorem Bindings.extends_trans {b₁ b₂ b₃ : Bindings}
    (h₁₂ : b₁.Extends b₂) (h₂₃ : b₂.Extends b₃) : b₁.Extends b₃ :=
  fun x a hx => h₂₃ x a (h₁₂ x a hx)

/-! ## §2: Assignment extends when variable is fresh -/

theorem isBound_false_of_lookup_none {b : Bindings} {v : String}
    (h : b.lookup v = none) : b.isBound v = false := by
  simp [Bindings.isBound, h]

theorem lookup_assign_of_lookup_none
    (b : Bindings) (v : String) (a : Atom)
    (hnone : b.lookup v = none) :
    (b.assign v a).lookup v = some a := by
  have hnotbound := isBound_false_of_lookup_none hnone
  simp only [Bindings.assign, Bindings.lookup, hnotbound, Bool.false_eq_true, ↓reduceIte,
    List.lookup_append, Bindings.lookup] at hnone ⊢
  simp [hnone]

/-- Assigning to a fresh variable extends the bindings. -/
theorem extends_assign_of_lookup_none
    (b : Bindings) (v : String) (a : Atom)
    (hnone : b.lookup v = none) :
    b.Extends (b.assign v a) := by
  intro x val hx
  have hnotbound := isBound_false_of_lookup_none hnone
  simp only [Bindings.assign, Bindings.lookup, hnotbound, Bool.false_eq_true, ↓reduceIte,
    List.lookup_append] at hx ⊢
  simp [hx]

/-- Assigning to a fresh variable doesn't affect other lookups. -/
theorem assign_lookup_ne (b : Bindings) (v : String) (a : Atom)
    (w : String) (hne : w ≠ v) (hnone : b.lookup v = none) :
    (b.assign v a).lookup w = b.lookup w := by
  have hnotbound := isBound_false_of_lookup_none hnone
  simp only [Bindings.assign, Bindings.lookup, hnotbound, Bool.false_eq_true,
    ↓reduceIte, List.lookup_append]
  cases hw : (b.assignments.lookup w) with
  | some val => rfl
  | none => simp [hne]

/-! ## §3: simpleMatch extends — the mutual induction

Ported from `HEPeTTaSound.lean:656-714`. The proof is by induction on fuel,
with mutual cases for `simpleMatch` and `simpleMatchList`. -/

/-- **THE theorem**: `simpleMatch` and `simpleMatchList` both extend their
    input bindings. Proved by mutual induction on fuel. -/
theorem simpleMatch_extends (fuel : Nat) :
    (∀ lhs target b qb,
      simpleMatch lhs target b fuel = some qb →
      b.Extends qb) ∧
    (∀ ps ts b qb,
      simpleMatch.simpleMatchList ps ts b fuel = some qb →
      b.Extends qb) := by
  induction fuel with
  | zero =>
    exact ⟨fun _ _ _ _ h => by simp [simpleMatch] at h,
           fun ps ts b qb h => by
             cases ps <;> cases ts <;>
               simp [simpleMatch.simpleMatchList, simpleMatch] at h
             subst h; exact Bindings.extends_refl _⟩
  | succ n ih =>
    obtain ⟨ih_match, ih_list⟩ := ih
    have hpat : ∀ lhs target b qb,
        simpleMatch lhs target b (n + 1) = some qb →
        b.Extends qb := by
      intro lhs target b qb hmatch
      cases lhs with
      | var v =>
        cases hlookup : b.lookup v <;>
          simp [simpleMatch, hlookup] at hmatch
        · subst hmatch; exact extends_assign_of_lookup_none b v target hlookup
        · obtain ⟨_, rfl⟩ := hmatch; exact Bindings.extends_refl _
      | symbol s =>
        cases target <;> simp [simpleMatch] at hmatch
        obtain ⟨_, rfl⟩ := hmatch; exact Bindings.extends_refl _
      | grounded g =>
        cases target <;> simp [simpleMatch] at hmatch
        obtain ⟨_, rfl⟩ := hmatch; exact Bindings.extends_refl _
      | expression ps =>
        cases target <;> simp [simpleMatch] at hmatch
        exact ih_list ps _ b qb hmatch.2
    have hlist : ∀ ps ts b qb,
        simpleMatch.simpleMatchList ps ts b (n + 1) = some qb →
        b.Extends qb := by
      intro ps'
      induction ps' with
      | nil =>
        intro ts' b' qb' h'
        cases ts' <;>
          simp [simpleMatch.simpleMatchList] at h'
        subst h'; exact Bindings.extends_refl _
      | cons p' ps' ihps =>
        intro ts' b' qb' h'
        cases ts' with
        | nil => simp [simpleMatch.simpleMatchList] at h'
        | cons t' ts' =>
          unfold simpleMatch.simpleMatchList at h'
          cases hhd : simpleMatch p' t' b' (n + 1) with
          | none => simp [hhd] at h'
          | some b'' =>
            simp [hhd] at h'
            exact Bindings.extends_trans (hpat p' t' b' b'' hhd) (ihps ts' b'' qb' h')
    exact ⟨hpat, hlist⟩

/-! ## §4: Corollaries -/

/-- **Seed preservation**: if `simpleMatch` succeeds, every seed binding
    is preserved in the result. This is a direct corollary of `simpleMatch_extends`. -/
theorem simpleMatch_preserves_seed (pattern target : Atom) (seed : Bindings)
    (fuel : Nat) (result : Bindings)
    (hmatch : simpleMatch pattern target seed fuel = some result)
    (v : String) (val : Atom) (hseed : seed.lookup v = some val) :
    result.lookup v = some val :=
  (simpleMatch_extends fuel).1 pattern target seed result hmatch v val hseed

/-- Seed preservation for `simpleMatchList`. -/
theorem simpleMatchList_preserves_seed (ps ts : List Atom) (seed : Bindings)
    (fuel : Nat) (result : Bindings)
    (hmatch : simpleMatch.simpleMatchList ps ts seed fuel = some result)
    (v : String) (val : Atom) (hseed : seed.lookup v = some val) :
    result.lookup v = some val :=
  (simpleMatch_extends fuel).2 ps ts seed result hmatch v val hseed

/-! ## Recursive merge frames

Actual bidirectional matching may reconcile aliases and add constraints. It
preserves the private read frame below, rather than a chosen layout of the
whole binding record. The shared fuel induction covers every recursive
matcher, list matcher, merge and insertion branch.
-/

namespace FreshPrivateMerge

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra (vars)

def Avoids (keys : String → Prop) (atom : Atom) : Prop :=
  ∀ name ∈ vars atom, ¬keys name

structure ReadFrame (keys : String → Prop) (saved : String → Option Atom)
    (bindings : Bindings) : Prop where
  values : ∀ key value, (key, value) ∈ bindings.assignments → Avoids keys value
  equalities : ∀ left right, (left, right) ∈ bindings.equalities → ¬keys left ∧ ¬keys right
  reads : ∀ key, keys key → bindings.lookup key = saved key

theorem avoids_var {keys : String → Prop} {name : String} :
    Avoids keys (.var name) ↔ ¬keys name := by simp [Avoids, vars]

theorem avoids_expression {keys : String → Prop} {atoms : List Atom} :
    Avoids keys (.expression atoms) ↔ ∀ atom ∈ atoms, Avoids keys atom := by
  simp only [Avoids, vars]
  induction atoms with
  | nil => simp [vars.varsList]
  | cons first rest ih =>
    simpa only [vars.varsList, List.forall_mem_append, List.forall_mem_cons] using
      and_congr Iff.rfl ih

theorem ReadFrame.empty (keys : String → Prop) :
    ReadFrame keys (fun _ => none) Bindings.empty := by
  refine ⟨?_, ?_, ?_⟩
  · intro key value member; simp [Bindings.empty] at member
  · intro left right member; simp [Bindings.empty] at member
  · intro key _; rfl

theorem ReadFrame.lookup_value {keys : String → Prop} {saved : String → Option Atom}
    {bindings : Bindings} (frame : ReadFrame keys saved bindings)
    {key : String} {value : Atom} (found : bindings.lookup key = some value) :
    Avoids keys value := by
  obtain ⟨before, after, same, _⟩ := List.lookup_eq_some_iff.mp found
  exact frame.values key value (by rw [same]; simp)

theorem ReadFrame.class_value {keys : String → Prop} {saved : String → Option Atom}
    {bindings : Bindings} (frame : ReadFrame keys saved bindings)
    {key : String} {value : Atom} (member : value ∈ bindings.classValues key) :
    Avoids keys value := by
  obtain ⟨name, _, found⟩ := List.mem_filterMap.mp member
  exact frame.lookup_value found

theorem ReadFrame.none_key {keys : String → Prop} {bindings : Bindings}
    (frame : ReadFrame keys (fun _ => none) bindings)
    {key : String} {value : Atom} (member : (key, value) ∈ bindings.assignments) :
    ¬keys key := by
  intro owned
  have different := List.lookup_eq_none_iff.mp (frame.reads key owned) (key, value) member
  simp at different

theorem ReadFrame.assign {keys : String → Prop} {saved : String → Option Atom}
    {bindings : Bindings} (frame : ReadFrame keys saved bindings)
    {key : String} {value : Atom} (fresh : bindings.lookup key = none)
    (outside : ¬keys key) (allowed : Avoids keys value) :
    ReadFrame keys saved (bindings.assign key value) := by
  have unbound := isBound_false_of_lookup_none fresh
  refine ⟨?_, ?_, ?_⟩
  · intro name atom member
    simp only [Bindings.assign, unbound, Bool.false_eq_true, ↓reduceIte] at member
    rcases List.mem_append.mp member with old | added
    · exact frame.values name atom old
    · cases List.mem_singleton.mp added
      exact allowed
  · exact frame.equalities
  · intro name owned
    rw [assign_lookup_ne bindings key value name (fun same => outside (same ▸ owned)) fresh]
    exact frame.reads name owned

theorem ReadFrame.addEquality {keys : String → Prop} {saved : String → Option Atom}
    {bindings : Bindings} (frame : ReadFrame keys saved bindings)
    {left right : String} (leftOutside : ¬keys left) (rightOutside : ¬keys right) :
    ReadFrame keys saved (bindings.addEquality left right) := by
  refine ⟨frame.values, ?_, frame.reads⟩
  intro a b member
  rcases List.mem_append.mp member with old | added
  · exact frame.equalities a b old
  · cases List.mem_singleton.mp added
    exact ⟨leftOutside, rightOutside⟩

private theorem lookup_none_of_class_empty {bindings : Bindings} {key : String}
    (empty : bindings.classValues key = []) : bindings.lookup key = none := by
  have unbound := EqualityClosure.isBound_eq_false_of_classValues_nil empty
  cases found : bindings.lookup key with
  | none => rfl
  | some value => simp [Bindings.isBound, found] at unbound

private theorem fold_flatMap_preserves {α : Type} (P : Bindings → Prop)
    (step : Bindings → α → List Bindings) (items : List α) (seeds : List Bindings)
    (initial : ∀ seed ∈ seeds, P seed)
    (next : ∀ item ∈ items, ∀ seed, P seed → ∀ out ∈ step seed item, P out) :
    ∀ out ∈ items.foldl (fun acc item => acc.flatMap (fun seed => step seed item)) seeds,
      P out := by
  induction items generalizing seeds with
  | nil => exact initial
  | cons item items ih =>
    apply ih
    · intro out member
      obtain ⟨seed, stored, emitted⟩ := List.mem_flatMap.mp member
      exact next item (by simp) seed (initial seed stored) out emitted
    · intro item member
      exact next item (by simp [member])

theorem frame_family (keys : String → Prop) (fuel : Nat) :
    (∀ left right out, Avoids keys left → Avoids keys right →
      out ∈ matchAtoms left right fuel → ReadFrame keys (fun _ => none) out) ∧
    (∀ left right seeds out,
      (∀ atom ∈ left, Avoids keys atom) → (∀ atom ∈ right, Avoids keys atom) →
      (∀ seed ∈ seeds, ReadFrame keys (fun _ => none) seed) →
      out ∈ matchAtomsList left right seeds fuel → ReadFrame keys (fun _ => none) out) ∧
    (∀ saved left right out, ReadFrame keys saved left → ReadFrame keys (fun _ => none) right →
      out ∈ mergeBindings left right fuel → ReadFrame keys saved out) ∧
    (∀ saved before key value out, ReadFrame keys saved before → ¬keys key → Avoids keys value →
      out ∈ addVarBinding before key value fuel → ReadFrame keys saved out) ∧
    (∀ saved before left right out, ReadFrame keys saved before → ¬keys left → ¬keys right →
      out ∈ addVarEquality before left right fuel → ReadFrame keys saved out) := by
  induction fuel with
  | zero =>
    simp [matchAtoms, matchAtomsList, mergeBindings, addVarBinding, addVarEquality]
  | succ fuel ih =>
    obtain ⟨matched, listed, merged, assigned, equated⟩ := ih
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro left right out leftAllowed rightAllowed member
      cases left with
      | var name =>
        have outside := avoids_var.mp leftAllowed
        cases right with
        | var other =>
          have stored : out = Bindings.empty.addEquality name other := by
            exact (show out = Bindings.empty.addEquality name other ∧ out.hasLoop = false from
              by simpa [matchAtoms, getMetaType, Atom.variableType] using member).1
          subst out
          exact (ReadFrame.empty keys).addEquality outside (avoids_var.mp rightAllowed)
        | symbol value =>
          have stored : out = Bindings.empty.assign name (.symbol value) := by
            exact (show out = Bindings.empty.assign name (.symbol value) ∧ out.hasLoop = false from
              by simpa [matchAtoms, getMetaType, Atom.variableType, Atom.symbolType] using member).1
          subst out
          exact (ReadFrame.empty keys).assign rfl outside rightAllowed
        | grounded value =>
          have stored : out = Bindings.empty.assign name (.grounded value) := by
            exact (show out = Bindings.empty.assign name (.grounded value) ∧ out.hasLoop = false from
              by simpa [matchAtoms, getMetaType, Atom.variableType, Atom.groundedType] using member).1
          subst out
          exact (ReadFrame.empty keys).assign rfl outside rightAllowed
        | expression value =>
          have stored : out = Bindings.empty.assign name (.expression value) := by
            exact (show out = Bindings.empty.assign name (.expression value) ∧ out.hasLoop = false from
              by simpa [matchAtoms, getMetaType, Atom.variableType, Atom.expressionType] using member).1
          subst out
          exact (ReadFrame.empty keys).assign rfl outside rightAllowed
      | symbol name =>
        cases right with
        | var other =>
          have stored : out = Bindings.empty.assign other (.symbol name) := by
            exact (show out = Bindings.empty.assign other (.symbol name) ∧ out.hasLoop = false from
              by simpa [matchAtoms, getMetaType, Atom.variableType, Atom.symbolType] using member).1
          subst out
          exact (ReadFrame.empty keys).assign rfl (avoids_var.mp rightAllowed) leftAllowed
        | symbol other =>
          have stored : out = Bindings.empty :=
            (show (name = other ∧ out = Bindings.empty) ∧ out.hasLoop = false from
              by simpa [matchAtoms, getMetaType, Atom.symbolType] using member).1.2
          subst out
          exact ReadFrame.empty keys
        | grounded | expression =>
          all_goals simp [matchAtoms, getMetaType, Atom.symbolType, Atom.groundedType,
            Atom.expressionType] at member
      | grounded value =>
        cases right with
        | var other =>
          have stored : out = Bindings.empty.assign other (.grounded value) := by
            exact (show out = Bindings.empty.assign other (.grounded value) ∧ out.hasLoop = false from
              by simpa [matchAtoms, getMetaType, Atom.variableType, Atom.groundedType] using member).1
          subst out
          exact (ReadFrame.empty keys).assign rfl (avoids_var.mp rightAllowed) leftAllowed
        | grounded other =>
          have stored : out = Bindings.empty :=
            (show (value = other ∧ out = Bindings.empty) ∧ out.hasLoop = false from
              by simpa [matchAtoms, getMetaType, Atom.groundedType] using member).1.2
          subst out
          exact ReadFrame.empty keys
        | symbol | expression =>
          all_goals simp [matchAtoms, getMetaType, Atom.symbolType, Atom.groundedType,
            Atom.expressionType] at member
      | expression atoms =>
        cases right with
        | var other =>
          have stored : out = Bindings.empty.assign other (.expression atoms) := by
            exact (show out = Bindings.empty.assign other (.expression atoms) ∧ out.hasLoop = false from
              by simpa [matchAtoms, getMetaType, Atom.variableType, Atom.expressionType] using member).1
          subst out
          exact (ReadFrame.empty keys).assign rfl (avoids_var.mp rightAllowed) leftAllowed
        | expression others =>
          have stored : out ∈ matchAtomsList atoms others [Bindings.empty] fuel := by
            have raw := (show out ∈ (if atoms.length = others.length then
                matchAtomsList atoms others [Bindings.empty] fuel else []) ∧ out.hasLoop = false from
              by simpa [matchAtoms, getMetaType, Atom.expressionType] using member).1
            split at raw
            · exact raw
            · simp at raw
          exact listed atoms others [Bindings.empty] out
            (avoids_expression.mp leftAllowed) (avoids_expression.mp rightAllowed)
            (by intro seed present; obtain rfl := List.mem_singleton.mp present; exact ReadFrame.empty keys)
            stored
        | symbol | grounded =>
          all_goals simp [matchAtoms, getMetaType, Atom.symbolType, Atom.groundedType,
            Atom.expressionType] at member
    · intro left right seeds out leftAllowed rightAllowed initial member
      cases left with
      | nil =>
        cases right with
        | nil => exact initial out member
        | cons => simp [matchAtomsList] at member
      | cons first rest =>
        cases right with
        | nil => simp [matchAtomsList] at member
        | cons second others =>
          apply listed rest others _ out
            (fun atom present => leftAllowed atom (by simp [present]))
            (fun atom present => rightAllowed atom (by simp [present])) ?_ member
          intro next present
          obtain ⟨seed, seedMember, found⟩ := List.mem_flatMap.mp present
          obtain ⟨result, resultMember, built⟩ := List.mem_flatMap.mp found
          exact merged _ seed result next (initial seed seedMember)
            (matched first second result (leftAllowed first (by simp))
              (rightAllowed second (by simp)) resultMember) built
    · intro saved left right out leftFrame rightFrame member
      change out ∈ right.equalities.foldl
        (fun acc edge => acc.flatMap (fun seed => addVarEquality seed edge.1 edge.2 fuel))
        (right.assignments.foldl
          (fun acc entry => acc.flatMap (fun seed => addVarBinding seed entry.1 entry.2 fuel))
          [left]) at member
      refine fold_flatMap_preserves (ReadFrame keys saved)
        (fun seed (edge : String × String) => addVarEquality seed edge.1 edge.2 fuel)
        right.equalities
        (right.assignments.foldl
          (fun acc entry => acc.flatMap (fun seed => addVarBinding seed entry.1 entry.2 fuel))
          [left]) ?_ ?_ out member
      · apply fold_flatMap_preserves (ReadFrame keys saved)
          (fun seed entry => addVarBinding seed entry.1 entry.2 fuel) right.assignments [left]
        · intro seed present; obtain rfl := List.mem_singleton.mp present; exact leftFrame
        · intro entry present seed frame result found
          exact assigned saved seed entry.1 entry.2 result frame (rightFrame.none_key present)
            (rightFrame.values entry.1 entry.2 present) found
      · intro edge present seed frame result found
        obtain ⟨leftOutside, rightOutside⟩ := rightFrame.equalities edge.1 edge.2 present
        exact equated saved seed edge.1 edge.2 result frame leftOutside rightOutside found
    · intro saved before key value out frame outside allowed member
      simp only [addVarBinding] at member
      cases values : before.classValues key with
      | nil =>
        simp only [values, List.mem_singleton] at member
        subst out
        exact frame.assign (lookup_none_of_class_empty values) outside allowed
      | cons first rest =>
        simp only [values] at member
        have firstAllowed : Avoids keys first := frame.class_value (key := key) (by rw [values]; simp)
        have restAllowed : ∀ atom ∈ rest, Avoids keys atom := by
          intro atom present
          exact frame.class_value (key := key) (by rw [values]; simp [present])
        split at member
        · split at member
          · obtain rfl := List.mem_singleton.mp member
            exact frame
          · obtain ⟨result, selected, joined⟩ := List.mem_flatMap.mp member
            exact merged saved before result out frame
              (matched first value result firstAllowed allowed selected) joined
        · obtain ⟨result, selected, joined⟩ := List.mem_flatMap.mp member
          apply merged saved before result out frame ?_ joined
          apply listed _ _ [Bindings.empty] result ?_ ?_ ?_ selected
          · intro atom present
            have same := List.eq_of_mem_replicate present
            exact same ▸ firstAllowed
          · intro atom present
            rcases List.mem_append.mp present with old | last
            · exact restAllowed atom old
            · obtain rfl := List.mem_singleton.mp last
              exact allowed
          · intro seed present
            obtain rfl := List.mem_singleton.mp present
            exact ReadFrame.empty keys
    · intro saved before left right out frame leftOutside rightOutside member
      have joinedFrame := frame.addEquality leftOutside rightOutside
      simp only [addVarEquality] at member
      split at member
      · obtain rfl := List.mem_singleton.mp member
        exact joinedFrame
      · cases values : (before.addEquality left right).classValues left with
        | nil => simp [values] at member
        | cons first rest =>
          have firstAllowed : Avoids keys first := joinedFrame.class_value (key := left) (by rw [values]; simp)
          have restAllowed : ∀ atom ∈ rest, Avoids keys atom := by
            intro atom present
            exact joinedFrame.class_value (key := left) (by rw [values]; simp [present])
          cases rest with
          | nil =>
            simp only [values] at member
            obtain ⟨result, selected, mergedMember⟩ := List.mem_flatMap.mp member
            exact merged saved _ result out joinedFrame
              (listed _ _ [Bindings.empty] result (by simp) (by simp)
                (by intro seed present; obtain rfl := List.mem_singleton.mp present; exact ReadFrame.empty keys)
                selected) mergedMember
          | cons second others =>
            cases others with
            | nil =>
              simp only [values] at member
              obtain ⟨result, selected, mergedMember⟩ := List.mem_flatMap.mp member
              exact merged saved _ result out joinedFrame
                (matched first second result firstAllowed (restAllowed second (by simp)) selected) mergedMember
            | cons third others =>
              simp only [values] at member
              obtain ⟨result, selected, mergedMember⟩ := List.mem_flatMap.mp member
              apply merged saved _ result out joinedFrame ?_ mergedMember
              apply listed _ _ [Bindings.empty] result ?_ restAllowed ?_ selected
              · intro atom present
                have same := List.eq_of_mem_replicate present
                exact same ▸ firstAllowed
              · intro seed present
                obtain rfl := List.mem_singleton.mp present
                exact ReadFrame.empty keys

end FreshPrivateMerge

namespace BindingComposition

-- Structural depth measures for HE atoms and atom lists.
mutual

def atomDepth : Atom → Nat
  | .symbol _ => 0
  | .var _ => 0
  | .grounded _ => 0
  | .expression es => listDepth es + 1

def listDepth : List Atom → Nat
  | [] => 0
  | a :: as => max (atomDepth a) (listDepth as)

end

/-- No variable occurring inside an assignment value has another direct
assignment in the same HE binding set. -/
def AssignmentValuesIndependent (b : Bindings) : Prop :=
  ∀ ⦃v a⦄, b.lookup v = some a → b.hasAssignedVar a = false

/-- On assignment-independent bindings, recursive `resolve` agrees with a
single direct lookup as soon as it has one unfold step available. -/
@[simp] theorem resolve_eq_lookup_of_assignmentValuesIndependent {b : Bindings}
    (hindependent : AssignmentValuesIndependent b) (v : String) (fuel : Nat) :
    b.resolve v (fuel + 1) = b.lookup v := by
  cases h : b.lookup v with
  | none => simp [Bindings.resolve, h]
  | some a =>
      have hstable : b.hasAssignedVar a = false := hindependent h
      simp [Bindings.resolve, Bindings.resolveAtomAux, h, hstable]

end BindingComposition

/-! ## Ground one-way matching and native constraint matching

These laws concern binding operations and ground patterns only. They do not
use an evaluator judgment or an executable-to-source adequacy premise.
-/

/-- Merging any bindings with the empty bindings (on the right) is the
identity, at any positive fuel: the merge folds over the right side's
(empty) assignment and equality lists. -/
theorem mergeBindings_empty_right (b : Bindings) (n : Nat) :
    mergeBindings b Bindings.empty (n + 1) = [b] := by
  simp [mergeBindings, Bindings.empty]

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-- Fresh-variable `addVarBinding` is plain assignment. -/
theorem addVarBinding_fresh {b : Bindings} {v : String} {val : Atom}
    (h : b.lookup v = none) (hEq : b.equalities = []) (n : Nat) :
    addVarBinding b v val (n + 1) = [b.assign v val] := by
  simp [addVarBinding, Bindings.classValues_no_equalities hEq, h]

/-- Bound-to-the-same-value `addVarBinding` is the identity. -/
theorem addVarBinding_same {b : Bindings} {v : String} {val : Atom}
    (h : b.lookup v = some val) (hEq : b.equalities = []) (n : Nat) :
    addVarBinding b v val (n + 1) = [b] := by
  simp [addVarBinding, Bindings.classValues_no_equalities hEq, h,
    Bindings.valuesConsistent]

/-- On equality-free bindings, class-wide addition is exactly the original
direct-lookup algorithm. -/
theorem addVarBinding_no_equalities {b : Bindings} {v : String} {val : Atom}
    (hEq : b.equalities = []) (n : Nat) :
    addVarBinding b v val (n + 1) =
      match b.lookup v with
      | none => [b.assign v val]
      | some prev =>
          if prev == val then [b]
          else (matchAtoms prev val n).flatMap fun mb => mergeBindings b mb n := by
  cases hlook : b.lookup v <;>
    simp [addVarBinding, Bindings.classValues_no_equalities hEq, hlook,
      Bindings.valuesConsistent]

/-- Merging a single fresh assignment: the same case split as
`simpleMatch`'s variable case (fresh → extend; bound-same → unchanged). -/
theorem mergeBindings_single_assign {b : Bindings} {v : String} {val : Atom}
    (n : Nat) :
    mergeBindings b (Bindings.empty.assign v val) (n + 2) =
      addVarBinding b v val (n + 1) := by
  simp [mergeBindings, Bindings.assign, Bindings.empty, Bindings.isBound,
    Bindings.lookup]

/-- Fresh single-assignment merge is just the expected assignment. -/
theorem mergeBindings_single_assign_fresh {b : Bindings} {v : String} {val : Atom}
    (h : b.lookup v = none) (hEq : b.equalities = []) (n : Nat) :
    mergeBindings b (Bindings.empty.assign v val) (n + 2) = [b.assign v val] := by
  rw [mergeBindings_single_assign]
  exact addVarBinding_fresh h hEq n

/-- Re-merging the same single assignment is the identity. -/
theorem mergeBindings_single_assign_same {b : Bindings} {v : String} {val : Atom}
    (h : b.lookup v = some val) (hEq : b.equalities = []) (n : Nat) :
    mergeBindings b (Bindings.empty.assign v val) (n + 2) = [b] := by
  rw [mergeBindings_single_assign]
  exact addVarBinding_same h hEq n

/-- Empty bindings merged with a single assignment reproduce that assignment
once enough fuel is available for the inner `addVarBinding`. -/
theorem mergeBindings_empty_single_assign {v : String} {val : Atom} (n : Nat) :
    mergeBindings Bindings.empty (Bindings.empty.assign v val) (n + 2) =
      [Bindings.empty.assign v val] := by
  rw [mergeBindings_single_assign]
  exact addVarBinding_fresh (by simp [Bindings.empty, Bindings.lookup]) rfl n

/-- At fuel 1, `addVarBinding` is a deterministic single-step compatibility
check: fresh extends, same-value keeps, different-value fails. -/
theorem addVarBinding_fuel1 (b : Bindings) (v : String) (val : Atom)
    (hEq : b.equalities = []) :
    addVarBinding b v val 1 =
      match b.lookup v with
      | none => [b.assign v val]
      | some prev => if prev == val then [b] else [] := by
  rw [addVarBinding_no_equalities hEq 0]
  cases b.lookup v <;> simp [matchAtoms]

private theorem addVarBinding_fuel1_no_equalities
    {b result : Bindings} {v : String} {val : Atom}
    (hEq : b.equalities = []) (hmem : result ∈ addVarBinding b v val 1) :
    result.equalities = [] := by
  rw [addVarBinding_fuel1 b v val hEq] at hmem
  cases hlook : b.lookup v with
  | none =>
      simp [hlook] at hmem
      subst result
      simpa [Bindings.assign] using hEq
  | some prev =>
      by_cases hsame : prev == val
      · simp [hlook, hsame] at hmem
        subst result
        exact hEq
      · simp [hlook, hsame] at hmem

/-- One deterministic ground-merge fold step: thread a list of candidate
bindings through one assignment, failing on incompatible rebinding. -/
private def detfoldStep (acc : List Bindings) (x : String × Atom) : List Bindings :=
  acc.flatMap fun (b : Bindings) =>
    match b.lookup x.1 with
    | none => [b.assign x.1 x.2]
    | some prev => if prev == x.2 then [b] else []

/-- Deterministic ground-merge helper: merge a list of assignments into a seed,
failing on the first incompatible rebinding. This is the algebraic view of
`mergeBindings` on the ground fragment. -/
private def mergeGroundAssignments? (b : Bindings) :
    List (String × Atom) → Option Bindings
  | [] => some b
  | (v, val) :: rest =>
      match b.lookup v with
      | none => mergeGroundAssignments? (b.assign v val) rest
      | some prev =>
          if prev == val then
            mergeGroundAssignments? b rest
          else
            none

/-- Deterministic assignment merging never changes the equality component. -/
private theorem mergeGroundAssignments_equalities
    {b out : Bindings} {assigns : List (String × Atom)}
    (h : mergeGroundAssignments? b assigns = some out) :
    out.equalities = b.equalities := by
  induction assigns generalizing b with
  | nil =>
      simp [mergeGroundAssignments?] at h
      subst out
      rfl
  | cons pair rest ih =>
      rcases pair with ⟨v, val⟩
      cases hlook : b.lookup v with
      | none =>
          apply (ih (b := b.assign v val) (by
            simpa [mergeGroundAssignments?, hlook] using h)).trans
          rfl
      | some prev =>
          by_cases hsame : prev == val
          · exact ih (by simpa [mergeGroundAssignments?, hlook, hsame] using h)
          · simp [mergeGroundAssignments?, hlook, hsame] at h

/-- The fuel-1 `addVarBinding` fold is definitionally the deterministic
lookup/compare fold used by `mergeGroundAssignments?`. -/
private theorem fold_addVarBinding_fuel1_eq
    (acc : List Bindings) (assigns : List (String × Atom))
    (haccEq : ∀ b ∈ acc, b.equalities = []) :
    List.foldl
      (fun acc x => acc.flatMap fun b => addVarBinding b x.1 x.2 1)
      acc assigns =
    List.foldl detfoldStep acc assigns := by
  induction assigns generalizing acc with
  | nil => rfl
  | cons pair assigns ih =>
      rcases pair with ⟨v, val⟩
      simp only [List.foldl_cons]
      have hstep :
          acc.flatMap (fun b => addVarBinding b v val 1) =
            detfoldStep acc (v, val) := by
        unfold detfoldStep
        apply List.flatMap_congr
        intro b hb
        exact addVarBinding_fuel1 b v val (haccEq b hb)
      rw [hstep]
      apply ih
      intro out hout
      rcases List.mem_flatMap.mp hout with ⟨b, hb, hout⟩
      have hbEq := haccEq b hb
      cases hlook : b.lookup v with
      | none =>
          simp [hlook] at hout
          subst out
          simp [Bindings.assign, hbEq]
      | some prev =>
          by_cases hsame : prev == val
          · simp [hlook, hsame] at hout
            subst out
            exact hbEq
          · simp [hlook, hsame] at hout

/-- Once the deterministic ground-merge fold has no candidate bindings left,
it stays empty. -/
private theorem detfold_nil
    (assigns : List (String × Atom)) :
    List.foldl detfoldStep [] assigns = [] := by
  induction assigns with
  | nil => rfl
  | cons pair assigns ih =>
      rcases pair with ⟨v, val⟩
      simp [detfoldStep, ih]

/-- The deterministic ground-merge helper exactly matches the explicit
deterministic assignment fold. -/
private theorem mergeGroundAssignments_toList_eq_detfold
    (b : Bindings) (assigns : List (String × Atom)) :
    (mergeGroundAssignments? b assigns).toList =
      List.foldl detfoldStep [b] assigns := by
  induction assigns generalizing b with
  | nil => rfl
  | cons pair assigns ih =>
      rcases pair with ⟨v, val⟩
      cases hlook : b.lookup v with
      | none =>
          simp [mergeGroundAssignments?, detfoldStep, hlook]
          simpa [detfoldStep, hlook] using ih (b.assign v val)
      | some prev =>
          by_cases hsame : prev = val
          · have hbeq : (prev == val) = true := by simp [hsame]
            simp [mergeGroundAssignments?, detfoldStep, hlook, hsame]
            simpa [detfoldStep, hlook, hsame] using ih b
          · have hbeq : (prev == val) = false := by simp [hsame]
            simp [mergeGroundAssignments?, detfoldStep, hlook, hsame, hbeq, detfold_nil]

/-- Deterministic ground-merge composes over appended assignment lists. -/
private theorem mergeGroundAssignments_append
    (b : Bindings) (xs ys : List (String × Atom)) :
    mergeGroundAssignments? b (xs ++ ys) =
      match mergeGroundAssignments? b xs with
      | some b' => mergeGroundAssignments? b' ys
      | none => none := by
  induction xs generalizing b with
  | nil => rfl
  | cons pair xs ih =>
      rcases pair with ⟨v, val⟩
      cases hlook : b.lookup v with
      | none =>
          simp [mergeGroundAssignments?, hlook, ih]
      | some prev =>
          by_cases hsame : prev == val
          · simp [mergeGroundAssignments?, hlook, hsame, ih]
          · simp [mergeGroundAssignments?, hlook, hsame]

private theorem lookup_none_of_not_mem_keys
    {xs : List (String × Atom)} {v : String}
    (h : v ∉ xs.map Prod.fst) :
    List.lookup v xs = none := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      rcases x with ⟨k, a⟩
      have hk : v ≠ k := by
        intro hvk
        apply h
        simp [hvk]
      have htail : v ∉ xs.map Prod.fst := by
        intro hmem
        apply h
        simp [hmem]
      have hne : (v == k) = false := by
        simp [hk]
      simp [List.lookup_cons, hne, ih htail]

/-- On a right fragment with distinct keys, successful deterministic ground
merge is extensional: each lookup in the result comes from the right fragment
if present there, otherwise from the left seed. -/
private theorem mergeGroundAssignments_lookup_spec
    {left out : Bindings} {assigns : List (String × Atom)}
    (hkeys : (assigns.map Prod.fst).Nodup)
    (hmerge : mergeGroundAssignments? left assigns = some out) :
    ∀ x,
      out.lookup x =
        match List.lookup x assigns with
        | some a => some a
        | none => left.lookup x := by
  induction assigns generalizing left out with
  | nil =>
      intro x
      simp [mergeGroundAssignments?] at hmerge
      rcases hmerge with rfl
      rfl
  | cons pair assigns ih =>
      rcases pair with ⟨v, val⟩
      have hnotmem : v ∉ assigns.map Prod.fst := by
        simpa using (List.nodup_cons.mp hkeys).1
      have hkeys' : (assigns.map Prod.fst).Nodup := by
        simpa using (List.nodup_cons.mp hkeys).2
      cases hlook : left.lookup v with
      | none =>
          simp [mergeGroundAssignments?, hlook] at hmerge
          intro x
          by_cases hxeq : x = v
          · subst x
            have htailNone : List.lookup v assigns = none :=
              lookup_none_of_not_mem_keys hnotmem
            have hseed :
                out.lookup v =
                  match List.lookup v assigns with
                  | some a => some a
                  | none => (left.assign v val).lookup v :=
              ih hkeys' hmerge v
            rw [htailNone] at hseed
            simpa [lookup_assign_of_lookup_none left v val hlook] using hseed
          · have htail :
              out.lookup x =
                match List.lookup x assigns with
                | some a => some a
                | none => (left.assign v val).lookup x :=
              ih hkeys' hmerge x
            have hlookup :
                (left.assign v val).lookup x = left.lookup x :=
              assign_lookup_ne left v val x hxeq hlook
            have hcons : List.lookup x ((v, val) :: assigns) = List.lookup x assigns := by
              have hbeq : (x == v) = false := by simp [hxeq]
              simp [List.lookup_cons, hbeq]
            rw [hcons]
            simpa [hlookup] using htail
      | some prev =>
          by_cases hsame : prev = val
          · simp [mergeGroundAssignments?, hlook, hsame] at hmerge
            intro x
            by_cases hxeq : x = v
            · subst x
              have htailNone : List.lookup v assigns = none :=
                lookup_none_of_not_mem_keys hnotmem
              have htail :
                  out.lookup v =
                    match List.lookup v assigns with
                    | some a => some a
                    | none => left.lookup v :=
                ih hkeys' hmerge v
              rw [htailNone] at htail
              simpa [List.lookup_cons, hlook, hsame] using htail
            · have htail :
                out.lookup x =
                  match List.lookup x assigns with
                    | some a => some a
                    | none => left.lookup x :=
                ih hkeys' hmerge x
              have hcons : List.lookup x ((v, val) :: assigns) = List.lookup x assigns := by
                have hbeq : (x == v) = false := by simp [hxeq]
                simp [List.lookup_cons, hbeq]
              rw [hcons]
              exact htail
          · simp [mergeGroundAssignments?, hlook, hsame] at hmerge

/-- Package the deterministic helper at the bindings level. -/
private def mergeGround? (left right : Bindings) : Option Bindings :=
  match right.equalities with
  | [] => mergeGroundAssignments? left right.assignments
  | _ :: _ => none

/-- On canonical right-hand fragments, successful `mergeGround?` is extensional:
lookups in the result come from the right fragment when present there, and
otherwise from the left seed. -/
private theorem mergeGround_lookup_spec
    {left right out : Bindings}
    (hrightEq : right.equalities = [])
    (hkeys : (right.assignments.map Prod.fst).Nodup)
    (hmerge : mergeGround? left right = some out) :
    ∀ x,
      out.lookup x =
        match right.lookup x with
        | some a => some a
        | none => left.lookup x := by
  cases right with
  | mk assignments equalities =>
      cases hrightEq
      simpa [mergeGround?, Bindings.lookup] using
        (mergeGroundAssignments_lookup_spec (left := left) (out := out)
          (assigns := assignments) hkeys hmerge)

/-- Successful assignment-list merge is compatible on overlaps: whenever both
the left seed and the right assignment fragment bind the same variable, they
bind it to the same atom. -/
private theorem mergeGroundAssignments_overlap_agree
    {assigns : List (String × Atom)} {left out : Bindings}
    {x : String} {aL aR : Atom}
    (hkeys : (assigns.map Prod.fst).Nodup)
    (hmerge : mergeGroundAssignments? left assigns = some out)
    (hleft : left.lookup x = some aL)
    (hright : List.lookup x assigns = some aR) :
    aL = aR := by
  induction assigns generalizing left out x aL aR with
  | nil =>
      simp at hright
  | cons pair assigns ih =>
      rcases pair with ⟨v, val⟩
      have hnotmem : v ∉ assigns.map Prod.fst := by
        simpa using (List.nodup_cons.mp hkeys).1
      have hkeys' : (assigns.map Prod.fst).Nodup := by
        simpa using (List.nodup_cons.mp hkeys).2
      cases hlook : left.lookup v with
      | none =>
          have hmerge' :
              mergeGroundAssignments? (left.assign v val) assigns = some out := by
            simpa [mergeGroundAssignments?, hlook] using hmerge
          by_cases hxeq : x = v
          · subst hxeq
            have : False := by
              simp [hlook] at hleft
            exact False.elim this
          · have htail :
              List.lookup x assigns = some aR := by
                have hbeq : (x == v) = false := by simp [hxeq]
                simpa [List.lookup_cons, hbeq] using hright
            have hleft' :
                (left.assign v val).lookup x = some aL := by
              simpa [assign_lookup_ne left v val x hxeq hlook] using hleft
            exact ih hkeys' hmerge' hleft' htail
      | some prev =>
          by_cases hsame : prev = val
          · have hmerge' :
                mergeGroundAssignments? left assigns = some out := by
              simpa [mergeGroundAssignments?, hlook, hsame] using hmerge
            by_cases hxeq : x = v
            · subst hxeq
              have hhead : val = aR := by
                simp at hright
                simpa using hright
              have hprev : prev = aL := by simpa [hlook] using hleft
              rw [← hprev, hsame, hhead]
            · have htail :
                List.lookup x assigns = some aR := by
                  have hbeq : (x == v) = false := by simp [hxeq]
                  simpa [List.lookup_cons, hbeq] using hright
              exact ih hkeys' hmerge' hleft htail
          · have : False := by
              simp [mergeGroundAssignments?, hlook, hsame] at hmerge
            exact False.elim this

/-- Deterministic assignment-list merge succeeds whenever every overlap between
the seed and the assignment list already agrees on its value. This is the
existence half paired with `mergeGroundAssignments_overlap_agree`. -/
private theorem mergeGroundAssignments_exists_of_overlap_agree
    {assigns : List (String × Atom)} {left : Bindings}
    (hkeys : (assigns.map Prod.fst).Nodup)
    (hag :
      ∀ {x aL aR}, left.lookup x = some aL → List.lookup x assigns = some aR → aL = aR) :
    ∃ out, mergeGroundAssignments? left assigns = some out := by
  induction assigns generalizing left with
  | nil =>
      exact ⟨left, rfl⟩
  | cons pair assigns ih =>
      rcases pair with ⟨v, val⟩
      have hnotmem : v ∉ assigns.map Prod.fst := by
        simpa using (List.nodup_cons.mp hkeys).1
      have hkeys' : (assigns.map Prod.fst).Nodup := by
        simpa using (List.nodup_cons.mp hkeys).2
      cases hlook : left.lookup v with
      | none =>
          have hag' :
              ∀ {x aL aR},
                (left.assign v val).lookup x = some aL →
                List.lookup x assigns = some aR →
                aL = aR := by
            intro x aL aR hx htail
            by_cases hxeq : x = v
            · subst x
              have htailNone : List.lookup v assigns = none :=
                lookup_none_of_not_mem_keys hnotmem
              rw [htailNone] at htail
              cases htail
            · have hleft' : left.lookup x = some aL := by
                simpa [assign_lookup_ne left v val x hxeq hlook] using hx
              have hcons : List.lookup x ((v, val) :: assigns) = some aR := by
                have hbeq : (x == v) = false := by simp [hxeq]
                simpa [List.lookup_cons, hbeq] using htail
              exact hag hleft' hcons
          obtain ⟨out, hout⟩ := ih hkeys' hag'
          exact ⟨out, by simpa [mergeGroundAssignments?, hlook] using hout⟩
      | some prev =>
          have hsame : prev = val := by
            have hhead : List.lookup v ((v, val) :: assigns) = some val := by
              simp
            exact hag hlook hhead
          have hag' :
              ∀ {x aL aR},
                left.lookup x = some aL →
                List.lookup x assigns = some aR →
                aL = aR := by
            intro x aL aR hx htail
            have hcons : List.lookup x ((v, val) :: assigns) = some aR := by
              by_cases hxeq : x = v
              · subst x
                have : False := by
                  have htailNone : List.lookup v assigns = none :=
                    lookup_none_of_not_mem_keys hnotmem
                  rw [htailNone] at htail
                  cases htail
                exact False.elim this
              · have hbeq : (x == v) = false := by simp [hxeq]
                simpa [List.lookup_cons, hbeq] using htail
            exact hag hx hcons
          obtain ⟨out, hout⟩ := ih hkeys' hag'
          exact ⟨out, by simpa [mergeGroundAssignments?, hlook, hsame] using hout⟩

/-- Assigning a fresh key does not change which later right-hand assignments
look fresh, provided that key does not reappear later in the list. -/
private theorem filter_fresh_assign_eq
    {assigns : List (String × Atom)} {left : Bindings} {v : String} {val : Atom}
    (hlookup : left.lookup v = none)
    (hnotmem : v ∉ assigns.map Prod.fst) :
    assigns.filter (fun p => ((left.assign v val).lookup p.1).isNone) =
      assigns.filter (fun p => (left.lookup p.1).isNone) := by
  induction assigns with
  | nil => rfl
  | cons pair assigns ih =>
      rcases pair with ⟨w, a⟩
      have hwne : w ≠ v := by
        intro hwv
        subst hwv
        exact hnotmem (by simp)
      have hnotmem' : v ∉ assigns.map Prod.fst := by
        intro hv
        exact hnotmem (by simp [hv])
      have hnoneEq :
          ((left.assign v val).lookup w).isNone = (left.lookup w).isNone := by
        rw [assign_lookup_ne left v val w hwne hlookup]
      cases hfresh : (left.lookup w).isNone <;>
        simp [hnoneEq, hfresh, ih hnotmem']

/-- On a no-equalities seed, deterministic assignment-list merge under overlap
agreement produces exactly the seed assignments followed by the assignments
that were genuinely fresh at the seed, in their original right-hand order. -/
private theorem mergeGroundAssignments_eq_append_fresh_of_overlap_agree
    {assigns : List (String × Atom)} {left : Bindings}
    (hEq : left.equalities = [])
    (hkeys : (assigns.map Prod.fst).Nodup)
    (hag :
      ∀ {x aL aR}, left.lookup x = some aL → List.lookup x assigns = some aR → aL = aR) :
    mergeGroundAssignments? left assigns =
      some
        { assignments := left.assignments ++
            assigns.filter (fun p => (left.lookup p.1).isNone)
        , equalities := [] } := by
  induction assigns generalizing left with
  | nil =>
      cases left
      cases hEq
      simp [mergeGroundAssignments?]
  | cons pair assigns ih =>
      rcases pair with ⟨v, val⟩
      have hnotmem : v ∉ assigns.map Prod.fst := by
        simpa using (List.nodup_cons.mp hkeys).1
      have hkeys' : (assigns.map Prod.fst).Nodup := by
        simpa using (List.nodup_cons.mp hkeys).2
      cases hlook : left.lookup v with
      | none =>
          have hnotbound : left.isBound v = false := by
            simp [Bindings.isBound, hlook]
          have hEq' : (left.assign v val).equalities = [] := by
            simpa [Bindings.assign, hnotbound] using hEq
          have hag' :
              ∀ {x aL aR},
                (left.assign v val).lookup x = some aL →
                List.lookup x assigns = some aR →
                aL = aR := by
            intro x aL aR hx hright
            by_cases hxeq : x = v
            · subst x
              have htailNone : List.lookup v assigns = none :=
                lookup_none_of_not_mem_keys hnotmem
              rw [htailNone] at hright
              cases hright
            · have hleft' : left.lookup x = some aL := by
                simpa [assign_lookup_ne left v val x hxeq hlook] using hx
              have hcons : List.lookup x ((v, val) :: assigns) = some aR := by
                have hbeq : (x == v) = false := by simp [hxeq]
                simpa [List.lookup_cons, hbeq] using hright
              exact hag hleft' hcons
          have hfilter :
              assigns.filter (fun p => ((left.assign v val).lookup p.1).isNone) =
                assigns.filter (fun p => (left.lookup p.1).isNone) :=
            filter_fresh_assign_eq hlook hnotmem
          simp [mergeGroundAssignments?, hlook]
          rw [ih hEq' hkeys' hag', hfilter]
          simp [Bindings.assign, hnotbound, List.append_assoc]
      | some prev =>
          have hsame : prev = val := by
            have hhead : List.lookup v ((v, val) :: assigns) = some val := by
              simp
            exact hag hlook hhead
          have hag' :
              ∀ {x aL aR},
                left.lookup x = some aL →
                List.lookup x assigns = some aR →
                aL = aR := by
            intro x aL aR hx hright
            have hcons : List.lookup x ((v, val) :: assigns) = some aR := by
              by_cases hxeq : x = v
              · subst x
                have : False := by
                  have htailNone : List.lookup v assigns = none :=
                    lookup_none_of_not_mem_keys hnotmem
                  rw [htailNone] at hright
                  cases hright
                exact False.elim this
              · have hbeq : (x == v) = false := by simp [hxeq]
                simpa [List.lookup_cons, hbeq] using hright
            exact hag hx hcons
          simpa [mergeGroundAssignments?, hlook, hsame] using ih hEq hkeys' hag'

/-- Successful deterministic ground merge is compatible on overlaps:
whenever both the left seed and the right fragment bind the same variable,
they bind it to the same atom. This is the local agreement law the later
seed-composition proof needs. -/
private theorem mergeGround_overlap_agree
    {left right out : Bindings} {x : String} {aL aR : Atom}
    (hrightEq : right.equalities = [])
    (hkeys : (right.assignments.map Prod.fst).Nodup)
    (hmerge : mergeGround? left right = some out)
    (hleft : left.lookup x = some aL)
    (hright : right.lookup x = some aR) :
    aL = aR := by
  cases right with
  | mk assignments equalities =>
      cases hrightEq
      simpa [mergeGround?, Bindings.lookup] using
        (mergeGroundAssignments_overlap_agree
          (assigns := assignments) (left := left) (out := out)
          (x := x) (aL := aL) (aR := aR)
          hkeys hmerge hleft hright)

/-- The overlap-agreement criterion is also sufficient at the bindings level:
when a no-equalities right fragment with distinct keys agrees with the left
seed on every shared variable, deterministic ground merge succeeds. -/
private theorem mergeGround_exists_of_overlap_agree
    {left right : Bindings}
    (hrightEq : right.equalities = [])
    (hkeys : (right.assignments.map Prod.fst).Nodup)
    (hag :
      ∀ {x aL aR}, left.lookup x = some aL → right.lookup x = some aR → aL = aR) :
    ∃ out, mergeGround? left right = some out := by
  cases right with
  | mk assignments equalities =>
      cases hrightEq
      have hag' :
          ∀ {x aL aR},
            left.lookup x = some aL →
            List.lookup x assignments = some aR →
            aL = aR := by
        intro x aL aR hleft hright
        exact hag hleft (by simpa [Bindings.lookup] using hright)
      simpa [mergeGround?, Bindings.lookup] using
        (mergeGroundAssignments_exists_of_overlap_agree
          (assigns := assignments) (left := left) hkeys hag')

/-- A successful deterministic merge with a canonical right-hand fragment
preserves every lookup from that right fragment in the result. -/
private theorem mergeGround_extends_right_of_nodup
    {left right out : Bindings}
    (hrightEq : right.equalities = [])
    (hkeys : (right.assignments.map Prod.fst).Nodup)
    (hmerge : mergeGround? left right = some out) :
    right.Extends out := by
  intro x a hx
  have hout :=
    mergeGround_lookup_spec (left := left) (right := right) (out := out)
      hrightEq hkeys hmerge x
  rw [hx] at hout
  simpa using hout

/-- A successful deterministic merge with a canonical right-hand fragment also
preserves every lookup already present in the left seed. -/
private theorem mergeGround_extends_left_of_nodup
    {left right out : Bindings}
    (hrightEq : right.equalities = [])
    (hkeys : (right.assignments.map Prod.fst).Nodup)
    (hmerge : mergeGround? left right = some out) :
    left.Extends out := by
  intro x a hx
  by_cases hrightx : ∃ aR, right.lookup x = some aR
  · rcases hrightx with ⟨aR, hrightLook⟩
    have hagree : a = aR :=
      mergeGround_overlap_agree hrightEq hkeys hmerge hx hrightLook
    have hout :=
      mergeGround_lookup_spec (left := left) (right := right) (out := out)
        hrightEq hkeys hmerge x
    rw [hrightLook] at hout
    simpa [hagree] using hout
  · have hrightNone : right.lookup x = none := by
      cases hlook : right.lookup x with
      | none =>
          rfl
      | some aR =>
          exfalso
          exact hrightx ⟨aR, hlook⟩
    have hout :=
      mergeGround_lookup_spec (left := left) (right := right) (out := out)
        hrightEq hkeys hmerge x
    rw [hrightNone] at hout
    simpa [hx] using hout

/-- If a seed `b` merges successfully with a canonical ground fragment `mb`,
and the resulting bindings in turn merge successfully with a second canonical
ground fragment `fr`, then the middle merge `mb ⋆ fr` exists on its own. This
isolates the overlap-agreement content of seeded composition before the final
equation-level factorization law. -/
private theorem mergeGround_mid_exists_of_seeded
    {b mb c fr x : Bindings}
    (hmbEq : mb.equalities = [])
    (hmbKeys : (mb.assignments.map Prod.fst).Nodup)
    (hfrEq : fr.equalities = [])
    (hfrKeys : (fr.assignments.map Prod.fst).Nodup)
    (hc : mergeGround? b mb = some c)
    (hx : mergeGround? c fr = some x) :
    ∃ g, mergeGround? mb fr = some g := by
  have hmbc : mb.Extends c := mergeGround_extends_right_of_nodup hmbEq hmbKeys hc
  have hag :
      ∀ {v aM aF}, mb.lookup v = some aM → fr.lookup v = some aF → aM = aF := by
    intro v aM aF hmbLook hfrLook
    have hcLook : c.lookup v = some aM := hmbc v aM hmbLook
    exact mergeGround_overlap_agree hfrEq hfrKeys hx hcLook hfrLook
  exact mergeGround_exists_of_overlap_agree hfrEq hfrKeys hag

private theorem lookup_filter_some_of_nodup
    {xs : List (String × Atom)} {pred : (String × Atom) → Bool}
    {v : String} {a : Atom}
    (hkeys : (xs.map Prod.fst).Nodup)
    (h : List.lookup v (xs.filter pred) = some a) :
    List.lookup v xs = some a := by
  induction xs with
  | nil =>
      simp at h
  | cons x xs ih =>
      rcases x with ⟨k, b⟩
      have hkeys' : (xs.map Prod.fst).Nodup := by
        simpa using (List.nodup_cons.mp hkeys).2
      by_cases hk : v == k
      · have hvk : v = k := by simpa using hk
        subst k
        have hnotmem : v ∉ xs.map Prod.fst := by
          simpa using (List.nodup_cons.mp hkeys).1
        by_cases hpred : pred (v, b)
        · simp [hpred] at h
          simpa using h
        · simp [hpred] at h
          have htailNone : List.lookup v xs = none := lookup_none_of_not_mem_keys hnotmem
          have htailSome : List.lookup v xs = some a := ih hkeys' h
          rw [htailNone] at htailSome
          cases htailSome
      · by_cases hpred : pred (k, b)
        · have h' : List.lookup v (List.filter pred xs) = some a := by
            simpa [List.lookup_cons, hk, hpred] using h
          simpa [List.lookup_cons, hk] using ih hkeys' h'
        · have h' : List.lookup v (List.filter pred xs) = some a := by
            simpa [List.lookup_cons, hk, hpred] using h
          simpa [List.lookup_cons, hk] using ih hkeys' h'

private theorem keys_nodup_filter
    {xs : List (String × Atom)} {pred : (String × Atom) → Bool}
    (hkeys : (xs.map Prod.fst).Nodup) :
    ((xs.filter pred).map Prod.fst).Nodup := by
  induction xs with
  | nil =>
      simp
  | cons pair xs ih =>
      rcases pair with ⟨k, a⟩
      have hnotmem : k ∉ xs.map Prod.fst := by
        simpa using (List.nodup_cons.mp hkeys).1
      have hkeys' : (xs.map Prod.fst).Nodup := by
        simpa using (List.nodup_cons.mp hkeys).2
      by_cases hpred : pred (k, a)
      · have hnotmem' : k ∉ (xs.filter pred).map Prod.fst := by
          intro hkmem
          rcases List.mem_map.mp hkmem with ⟨p, hp, hpk⟩
          have hp' : p ∈ xs := List.mem_of_mem_filter hp
          rcases p with ⟨k', a'⟩
          simp at hpk
          subst k'
          exact hnotmem (List.mem_map.mpr ⟨(k, a'), hp', rfl⟩)
        simpa [List.filter_cons, hpred] using List.Nodup.cons hnotmem' (ih hkeys')
      · simpa [List.filter_cons, hpred] using ih hkeys'

private theorem filter_lookup_none_of_extends
    {xs : List (String × Atom)} {base ext : Bindings}
    (hext : base.Extends ext) :
    (xs.filter (fun p => (base.lookup p.1).isNone)).filter
        (fun p => (ext.lookup p.1).isNone) =
      xs.filter (fun p => (ext.lookup p.1).isNone) := by
  induction xs with
  | nil => rfl
  | cons pair xs ih =>
      rcases pair with ⟨v, a⟩
      cases hExt : (ext.lookup v).isNone with
      | false =>
          cases hBase : (base.lookup v).isNone <;>
            simp [hExt, hBase, ih]
      | true =>
          have hExtNone : ext.lookup v = none := by
            cases hlook : ext.lookup v <;> simp [hlook] at hExt ⊢
          have hBase : (base.lookup v).isNone = true := by
            cases hlook : base.lookup v with
            | none =>
                simp
            | some b =>
                have hpush : ext.lookup v = some b := hext v b hlook
                rw [hExtNone] at hpush
                cases hpush
          simp [hExt, hBase, ih]

/-- At the bindings level, deterministic ground-merge composes over
concatenated assignment fragments when both fragments have no equalities. -/
private theorem mergeGround_concat
    (left mid right : Bindings)
    (hmid : mid.equalities = []) (hright : right.equalities = []) :
    mergeGround? left { assignments := mid.assignments ++ right.assignments, equalities := [] } =
      match mergeGround? left mid with
      | some leftmid => mergeGround? leftmid right
      | none => none := by
  cases mid with
  | mk midAssignments midEqualities =>
      cases right with
      | mk rightAssignments rightEqualities =>
          cases hmid
          cases hright
          simp [mergeGround?, mergeGroundAssignments_append]

/-- On the no-equalities fragment, `mergeGround?` exactly reproduces
`mergeBindings` at fuel 2. -/
private theorem mergeGround_toList_eq_mergeBindings_two
    (left right : Bindings) (hLeftEq : left.equalities = [])
    (hEq : right.equalities = []) :
    (mergeGround? left right).toList = mergeBindings left right 2 := by
  cases right with
  | mk assignments equalities =>
      cases hEq
      simp only [mergeGround?, mergeBindings, List.foldl_nil]
      rw [mergeGroundAssignments_toList_eq_detfold]
      exact (fold_addVarBinding_fuel1_eq [left] assignments (by simp [hLeftEq])).symm

/-- At fuel 2, merging a concatenated ground/no-equalities fragment is the
same as merging the first fragment, then the second. -/
private theorem mergeBindings_two_concat
    (left mid right : Bindings)
    (hleft : left.equalities = []) (hmid : mid.equalities = [])
    (hright : right.equalities = []) :
    mergeBindings left { assignments := mid.assignments ++ right.assignments, equalities := [] } 2 =
      (mergeBindings left mid 2).flatMap fun leftmid =>
        mergeBindings leftmid right 2 := by
  rw [← mergeGround_toList_eq_mergeBindings_two left
      { assignments := mid.assignments ++ right.assignments, equalities := [] } hleft rfl]
  rw [mergeGround_concat left mid right hmid hright]
  rw [← mergeGround_toList_eq_mergeBindings_two left mid hleft hmid]
  cases hmerge : mergeGround? left mid with
  | none =>
      simp
  | some leftmid =>
      have hleftmid : leftmid.equalities = [] := by
        have hmga : mergeGroundAssignments? left mid.assignments = some leftmid := by
          simpa [mergeGround?, hmid] using hmerge
        exact (mergeGroundAssignments_equalities hmga).trans hleft
      simp [mergeGround_toList_eq_mergeBindings_two leftmid right hleftmid hright]

/-- On the no-equalities fragment, membership in `mergeBindings ... 2` is
equivalent to the deterministic ground-merge helper returning that result. -/
private theorem mem_mergeBindings_two_iff
    {left right result : Bindings} (hLeftEq : left.equalities = [])
    (hEq : right.equalities = []) :
    result ∈ mergeBindings left right 2 ↔ mergeGround? left right = some result := by
  rw [← mergeGround_toList_eq_mergeBindings_two left right hLeftEq hEq]
  cases hmerge : mergeGround? left right with
  | none =>
      simp
  | some b =>
      simp [eq_comm]

/-- The empty bindings have no loop. -/
theorem hasLoop_empty : Bindings.empty.hasLoop = false := by
  exact Bindings.hasLoop_empty

/-! ## Fuel monotonicity for the matcher family

Membership in any of the five matcher functions' results is preserved
under additional fuel (fuel only gates recursion depth; all branch
conditions are fuel-independent).  Proven as one simultaneous induction
on fuel; the list function carries accumulator-monotonicity in the same
statement (its recursion grows the accumulator). -/

/-- Pointwise list inclusion: every member of `xs` is a member of `ys`. -/
def Sub (xs ys : List Bindings) : Prop := ∀ x ∈ xs, x ∈ ys

theorem Sub.refl (xs : List Bindings) : Sub xs xs := fun _ h => h

/-- `matchAtomsList` distributes over a `flatMap`-built accumulator. This is
the structural reason seeded official matching can later be factored
seed-by-seed. -/
private theorem matchAtomsList_flatMap_acc
    {α : Type} (lefts rights : List Atom) (acc : List α)
    (f : α → List Bindings) (fuel : Nat) :
    matchAtomsList lefts rights (acc.flatMap f) fuel =
      acc.flatMap (fun a => matchAtomsList lefts rights (f a) fuel) := by
  induction fuel generalizing lefts rights acc f with
  | zero =>
      simp [matchAtomsList]
  | succ n ih =>
      cases lefts with
      | nil =>
          cases rights with
          | nil =>
              simp [matchAtomsList]
          | cons right rights =>
              simp [matchAtomsList]
      | cons left lefts =>
          cases rights with
          | nil =>
              simp [matchAtomsList]
          | cons right rights =>
              simp only [matchAtomsList]
              rw [List.flatMap_assoc]
              simpa using
                ih lefts rights acc
                  (fun a =>
                    (f a).flatMap fun b =>
                      (matchAtoms left right n).flatMap fun mb =>
                        mergeBindings b mb n)

/-- Membership form of `matchAtomsList_flatMap_acc`: seeded official matching
decomposes seed-by-seed over a `flatMap`-built accumulator. -/
private theorem mem_matchAtomsList_flatMap_acc
    {α : Type} {lefts rights : List Atom} {acc : List α}
    {f : α → List Bindings} {fuel : Nat} {x : Bindings} :
    x ∈ matchAtomsList lefts rights (acc.flatMap f) fuel ↔
      ∃ a ∈ acc, x ∈ matchAtomsList lefts rights (f a) fuel := by
  rw [matchAtomsList_flatMap_acc lefts rights acc f fuel]
  simp

/-- `matchAtomsList` decomposes an accumulator into singleton-seeded runs. -/
private theorem matchAtomsList_seedwise
    (lefts rights : List Atom) (seeds : List Bindings) (fuel : Nat) :
    matchAtomsList lefts rights seeds fuel =
      seeds.flatMap (fun b => matchAtomsList lefts rights [b] fuel) := by
  simpa using
    (matchAtomsList_flatMap_acc lefts rights seeds (fun b => [b]) fuel)

/-- Membership form of `matchAtomsList_seedwise`. -/
private theorem mem_matchAtomsList_seedwise
    {lefts rights : List Atom} {seeds : List Bindings}
    {fuel : Nat} {x : Bindings} :
    x ∈ matchAtomsList lefts rights seeds fuel ↔
      ∃ b ∈ seeds, x ∈ matchAtomsList lefts rights [b] fuel := by
  rw [matchAtomsList_seedwise lefts rights seeds fuel]
  simp

theorem flatMap_sub {xs xs' : List Bindings}
    {f g : Bindings → List Bindings}
    (h_xs : Sub xs xs') (h_fg : ∀ a ∈ xs, Sub (f a) (g a)) :
    Sub (xs.flatMap f) (xs'.flatMap g) := by
  intro x hx
  obtain ⟨a, ha, hfa⟩ := List.mem_flatMap.mp hx
  exact List.mem_flatMap.mpr ⟨a, h_xs a ha, h_fg a ha x hfa⟩

private theorem foldl_flatMap_sub {α : Type} (l : List α)
    {step step' : List Bindings → α → List Bindings}
    (h_step : ∀ acc acc' a, Sub acc acc' → Sub (step acc a) (step' acc' a)) :
    ∀ {acc acc' : List Bindings}, Sub acc acc' →
      Sub (l.foldl step acc) (l.foldl step' acc') := by
  induction l with
  | nil => intro acc acc' h; simpa using h
  | cons a as ih =>
      intro acc acc' h
      simp only [List.foldl_cons]
      exact ih (h_step acc acc' a h)

/-- The simultaneous fuel-monotonicity statement. -/
theorem matcher_mono : ∀ n : Nat,
    (∀ l r, Sub (matchAtoms l r n) (matchAtoms l r (n + 1))) ∧
    (∀ ls rs acc acc', Sub acc acc' →
      Sub (matchAtomsList ls rs acc n) (matchAtomsList ls rs acc' (n + 1))) ∧
    (∀ a b, Sub (mergeBindings a b n) (mergeBindings a b (n + 1))) ∧
    (∀ b v val, Sub (addVarBinding b v val n) (addVarBinding b v val (n + 1))) ∧
    (∀ b a c, Sub (addVarEquality b a c n) (addVarEquality b a c (n + 1))) := by
  intro n
  induction n with
  | zero =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
        first
          | (intro l r x hx; simp [matchAtoms] at hx)
          | (intro ls rs acc acc' h x hx; simp [matchAtomsList] at hx)
          | (intro a b x hx; simp [mergeBindings] at hx)
          | (intro b v val x hx; simp [addVarBinding] at hx)
          | (intro b a c x hx; simp [addVarEquality] at hx)
  | succ n ih =>
      obtain ⟨ihA, ihL, ihM, ihB, ihE⟩ := ih
      have subRefl : ∀ xs : List Bindings, Sub xs xs := Sub.refl
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · -- matchAtoms: same branch taken at both fuels; recursive branch via ihL
        intro l r x hx
        simp only [matchAtoms, List.mem_filter, beq_iff_eq,
          Bool.and_eq_true] at hx ⊢
        refine ⟨?_, hx.2⟩
        have hx1 := hx.1
        -- walk the paired if-levels: identical constants close by `exact`,
        -- off-diagonals by contradiction; only the expression level
        -- (where the fuel occurs) survives
        repeat'
          first
            | exact hx1
            | exact absurd ‹_› ‹_›
            | (split at hx1 <;> split <;>
                first
                  | exact hx1
                  | exact absurd ‹_› ‹_›
                  | skip)
        -- leftover: the expression diagonal (plus one stray off-diagonal)
        all_goals
          first
            | contradiction
            | (split at hx1
               · -- expression/expression arm: the inner length-ite
                 split at hx1
                 · rename_i hlen
                   rw [if_pos hlen]
                   exact ihL _ _ _ _ (subRefl _) x hx1
                 · rename_i hlen
                   rw [if_neg hlen]
                   exact hx1
               · -- catchall arm: both sides empty
                 exact hx1)
      · -- matchAtomsList
        intro ls rs acc acc' hacc x hx
        simp only [matchAtomsList] at hx ⊢
        split at hx
        · exact hacc x hx
        · rename_i l1 ls1 r1 rs1
          exact ihL _ _ _ _
            (flatMap_sub hacc
              (fun a _ => flatMap_sub (ihA l1 r1) (fun bnd _ => ihM a bnd)))
            x hx
        · exact absurd hx (by simp)
      · -- mergeBindings
        intro a b x hx
        simp only [mergeBindings] at hx ⊢
        refine foldl_flatMap_sub b.equalities
          (fun acc acc' p h => flatMap_sub h (fun bd _ => ihE bd p.1 p.2)) ?_ x hx
        exact foldl_flatMap_sub b.assignments
          (fun acc acc' p h => flatMap_sub h (fun bd _ => ihB bd p.1 p.2))
          (subRefl [a])
      · -- addVarBinding
        intro b v val x hx
        simp only [addVarBinding] at hx ⊢
        cases hvalues : b.classValues v with
        | nil =>
            simp [hvalues] at hx ⊢
            exact hx
        | cons first rest =>
            simp only [hvalues] at hx ⊢
            by_cases hclass : Bindings.valuesConsistent (first :: rest) = true
            · rw [if_pos hclass] at hx ⊢
              by_cases hsame : first = val
              · have hbeq : (first == val) = true := by simp [hsame]
                rw [if_pos hbeq] at hx ⊢
                exact hx
              · have hbeq : ¬ (first == val) = true := by simpa using hsame
                rw [if_neg hbeq] at hx ⊢
                exact flatMap_sub (ihA first val) (fun mb _ => ihM b mb) x hx
            · rw [if_neg hclass] at hx ⊢
              exact flatMap_sub (ihL _ _ _ _ (subRefl _))
                (fun mb _ => ihM b mb) x hx
      · -- addVarEquality
        intro b a c x hx
        simp only [addVarEquality] at hx ⊢
        cases hvalues : (b.addEquality a c).classValues a with
        | nil =>
            simp [hvalues] at hx ⊢
            exact hx
        | cons first rest =>
            simp only [hvalues] at hx ⊢
            by_cases hall : Bindings.valuesConsistent (first :: rest) = true
            · rw [if_pos hall] at hx ⊢
              exact hx
            · rw [if_neg hall] at hx ⊢
              cases rest with
              | nil => simp [Bindings.valuesConsistent] at hall
              | cons second tail =>
                  cases tail with
                  | nil =>
                      exact flatMap_sub (ihA first second)
                        (fun mb _ => ihM (b.addEquality a c) mb) x hx
                  | cons third tail =>
                      exact flatMap_sub (ihL _ _ _ _ (subRefl _))
                        (fun mb _ => ihM (b.addEquality a c) mb) x hx

/-- `matchAtoms` is monotone in fuel. -/
private theorem matchAtoms_mono_add
    (l r : Atom) (fuel extra : Nat) :
    Sub (matchAtoms l r fuel) (matchAtoms l r (fuel + extra)) := by
  induction extra with
  | zero =>
      simpa using Sub.refl (matchAtoms l r fuel)
  | succ extra ih =>
      have hstep := (matcher_mono (fuel + extra)).1 l r
      exact fun x hx => hstep x (ih x hx)

/-- `matchAtomsList` is monotone in fuel when the accumulator is fixed. -/
private theorem matchAtomsList_mono_add
    (ls rs : List Atom) (acc : List Bindings) (fuel extra : Nat) :
    Sub (matchAtomsList ls rs acc fuel) (matchAtomsList ls rs acc (fuel + extra)) := by
  induction extra with
  | zero =>
      simpa using Sub.refl (matchAtomsList ls rs acc fuel)
  | succ extra ih =>
      have hstep := (matcher_mono (fuel + extra)).2.1 ls rs acc acc (Sub.refl _)
      exact fun x hx => hstep x (ih x hx)

/-- `mergeBindings` is monotone in fuel. -/
private theorem mergeBindings_mono_add
    (left right : Bindings) (fuel extra : Nat) :
    Sub (mergeBindings left right fuel) (mergeBindings left right (fuel + extra)) := by
  induction extra with
  | zero =>
      simpa using Sub.refl (mergeBindings left right fuel)
  | succ extra ih =>
      have hstep := (matcher_mono (fuel + extra)).2.2.1 left right
      exact fun x hx => hstep x (ih x hx)

/-- A bridged head-step seed and a bridged tail run can be reassembled into a
single official `matchAtomsList` witness at a common larger fuel. -/
private theorem matchAtomsList_cons_of_head_tail
    {t p : Atom} {ts ps : List Atom}
    {b b' qb : Bindings} {fuelHead fuelTail : Nat}
    (hhead :
      b' ∈ (matchAtoms t p fuelHead).flatMap (fun mb => mergeBindings b mb fuelHead))
    (htail : qb ∈ matchAtomsList ts ps [b'] fuelTail) :
    ∃ fuel, qb ∈ matchAtomsList (t :: ts) (p :: ps) [b] (fuel + 1) := by
  let fuel := max fuelHead fuelTail
  have hHeadLe : fuelHead ≤ fuel := by
    dsimp [fuel]
    exact Nat.le_max_left _ _
  have hTailLe : fuelTail ≤ fuel := by
    dsimp [fuel]
    exact Nat.le_max_right _ _
  have hHeadEq : fuelHead + (fuel - fuelHead) = fuel :=
    Nat.add_sub_of_le hHeadLe
  have hTailEq : fuelTail + (fuel - fuelTail) = fuel :=
    Nat.add_sub_of_le hTailLe
  have hhead_sub :
      Sub
        ((matchAtoms t p fuelHead).flatMap fun mb => mergeBindings b mb fuelHead)
        ((matchAtoms t p fuel).flatMap fun mb => mergeBindings b mb fuel) := by
    refine flatMap_sub ?_ ?_
    · simpa [hHeadEq] using
        (matchAtoms_mono_add t p fuelHead (fuel - fuelHead))
    intro mb hmb
    simpa [hHeadEq] using
      (mergeBindings_mono_add b mb fuelHead (fuel - fuelHead))
  have hhead' :
      b' ∈ (matchAtoms t p fuel).flatMap (fun mb => mergeBindings b mb fuel) :=
    hhead_sub b' hhead
  have htail' :
      qb ∈ matchAtomsList ts ps [b'] fuel := by
    have hsub := matchAtomsList_mono_add ts ps [b'] fuelTail (fuel - fuelTail)
    simpa [hTailEq] using hsub qb htail
  have hseeded :
      qb ∈ matchAtomsList ts ps
        ((matchAtoms t p fuel).flatMap fun mb => mergeBindings b mb fuel) fuel := by
    rw [matchAtomsList_seedwise ts ps
        ((matchAtoms t p fuel).flatMap fun mb => mergeBindings b mb fuel) fuel]
    exact List.mem_flatMap.mpr ⟨b', hhead', htail'⟩
  refine ⟨fuel, ?_⟩
  simpa [matchAtomsList] using hseeded

/-- If each successful element match at a fixed `fuel` can be witnessed by an
official head-step from the same seed, then successful `simpleMatchList`
threading at that `fuel` can be witnessed by official `matchAtomsList`
threading from `[seed]`.  This packages the exact inner induction shape the
ground matcher bridge needs later. -/
private theorem simpleMatchList_ground_seeded_of_elem_bridge
    (fuel : Nat)
    (hElem :
      ∀ {p t b qb},
        GroundAtom t →
        simpleMatch p t b fuel = some qb →
          ∃ fuel',
            qb ∈ (matchAtoms t p fuel').flatMap (fun mb => mergeBindings b mb fuel')) :
    ∀ {ps ts b qb},
      (∀ t ∈ ts, GroundAtom t) →
      simpleMatch.simpleMatchList ps ts b fuel = some qb →
        ∃ fuel', qb ∈ matchAtomsList ts ps [b] fuel' := by
  intro ps
  induction ps with
  | nil =>
      intro ts b qb hground hmatch
      cases ts with
      | nil =>
          simp [simpleMatch.simpleMatchList] at hmatch
          subst hmatch
          refine ⟨1, ?_⟩
          simp [matchAtomsList]
      | cons t ts =>
          simp [simpleMatch.simpleMatchList] at hmatch
  | cons p ps ih =>
      intro ts b qb hground hmatch
      cases ts with
      | nil =>
          simp [simpleMatch.simpleMatchList] at hmatch
      | cons t ts =>
          unfold simpleMatch.simpleMatchList at hmatch
          cases hhd : simpleMatch p t b fuel with
          | none =>
              simp [hhd] at hmatch
          | some b' =>
              simp [hhd] at hmatch
              have ht : GroundAtom t := hground t (by simp)
              obtain ⟨fuelHead, hhead⟩ := hElem ht hhd
              obtain ⟨fuelTail, htail⟩ := ih
                (fun a ha => hground a (by simp [ha])) hmatch
              obtain ⟨fuel', hwhole⟩ := matchAtomsList_cons_of_head_tail hhead htail
              exact ⟨fuel' + 1, hwhole⟩

/-! ## Ground-results invariants

Matching a ground left atom produces bindings whose assignment values are
ground and whose equality list is empty — hence loop-free (no assignment value contains a variable dependency).  These invariants are what make the
bindings algebra of the bridge factorization tractable. -/

/-- Explicit key-uniqueness side invariant for bindings assignments.
This is documented in `Types.lean` and is the missing premise the
ground-merge algebra needs to speak honestly about canonical results. -/
private def Bindings.KeysNodup (b : Bindings) : Prop :=
  (b.assignments.map Prod.fst).Nodup

private theorem lookup_none_not_mem_keys
    {xs : List (String × Atom)} {v : String}
    (h : List.lookup v xs = none) :
    v ∉ xs.map Prod.fst := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rcases x with ⟨k, a⟩
      by_cases hk : v == k
      · have : False := by
          simp [List.lookup_cons, hk] at h
        exact False.elim this
      · have htail : List.lookup v xs = none := by
          simpa [List.lookup_cons, hk] using h
        have hneq : v ≠ k := by
          simpa using hk
        simp [hneq, ih htail]

private theorem Bindings.KeysNodup.empty :
    Bindings.KeysNodup Bindings.empty := by
  simp [Bindings.KeysNodup, Bindings.empty]

private theorem Bindings.KeysNodup.assign
    {b : Bindings} {v : String} {val : Atom}
    (hkeys : Bindings.KeysNodup b) :
    Bindings.KeysNodup (b.assign v val) := by
  unfold Bindings.KeysNodup at hkeys ⊢
  by_cases hbound : b.isBound v
  · have hmap :
        List.map (Prod.fst ∘ fun x => if x.1 = v then (x.1, val) else x) b.assignments =
          List.map Prod.fst b.assignments := by
      induction b.assignments with
      | nil => rfl
      | cons x xs ih =>
          rcases x with ⟨k, a⟩
          by_cases hk : k = v
          · simp [hk, ih]
          · simp [hk, ih]
    simp [Bindings.assign, hbound]
    rw [hmap]
    exact hkeys
  · have hlookup_none : b.lookup v = none := by
      unfold Bindings.isBound at hbound
      cases hlook : b.lookup v <;> simp [hlook] at hbound
      case none => exact rfl
    have hnotmem : v ∉ b.assignments.map Prod.fst :=
      lookup_none_not_mem_keys hlookup_none
    simp [Bindings.assign, hbound]
    rw [← List.concat_eq_append]
    exact List.Nodup.concat hnotmem hkeys

/-- Ground bindings together with the documented key-uniqueness discipline.
This is the honest strengthening needed for extensional merge laws. -/
private def GroundBindingsCanon (b : Bindings) : Prop :=
  GroundBindings b ∧ Bindings.KeysNodup b

private theorem GroundBindingsCanon.empty : GroundBindingsCanon Bindings.empty :=
  ⟨GroundBindings.empty, Bindings.KeysNodup.empty⟩

private theorem GroundBindingsCanon.assign {b : Bindings} {v : String} {val : Atom}
    (hb : GroundBindingsCanon b) (hval : GroundAtom val) :
    GroundBindingsCanon (b.assign v val) := by
  exact ⟨GroundBindings.assign hb.1 hval, Bindings.KeysNodup.assign hb.2⟩

/-- If a suffix assignment list has pairwise-distinct keys, is fresh with
respect to a seed, and the seed carries no equalities, then the deterministic
ground-merge helper just appends that suffix.  This is the canonical
empty-seed/seed-extension behavior the later factorization algebra relies on. -/
private theorem mergeGroundAssignments_append_fresh
    {seed : Bindings} {rest : List (String × Atom)}
    (hEq : seed.equalities = [])
    (hkeysSeed : Bindings.KeysNodup seed)
    (hkeysRest : (rest.map Prod.fst).Nodup)
    (hfresh : ∀ v, v ∈ rest.map Prod.fst → seed.lookup v = none) :
    mergeGroundAssignments? seed rest =
      some { assignments := seed.assignments ++ rest, equalities := [] } := by
  induction rest generalizing seed with
  | nil =>
      cases seed
      cases hEq
      simp [mergeGroundAssignments?]
  | cons pair rest ih =>
      rcases pair with ⟨v, val⟩
      have hlookup : seed.lookup v = none := hfresh v (by simp)
      have hnotbound : seed.isBound v = false := by
        simp [Bindings.isBound, hlookup]
      have hnotmemRest : v ∉ rest.map Prod.fst := by
        simpa using (List.nodup_cons.mp hkeysRest).1
      have hkeysRest' : (rest.map Prod.fst).Nodup := by
        simpa using (List.nodup_cons.mp hkeysRest).2
      have hEq' : (seed.assign v val).equalities = [] := by
        simpa [Bindings.assign, hnotbound] using hEq
      have hfresh' : ∀ w, w ∈ rest.map Prod.fst → (seed.assign v val).lookup w = none := by
        intro w hw
        have hwSeed : seed.lookup w = none := hfresh w (by simp [hw])
        have hwne : w ≠ v := by
          intro hwv
          subst hwv
          exact hnotmemRest hw
        simpa [hwSeed] using assign_lookup_ne seed v val w hwne hlookup
      simp [mergeGroundAssignments?, hlookup]
      simpa [Bindings.assign, hnotbound, List.append_assoc] using
        (ih hEq' (Bindings.KeysNodup.assign hkeysSeed) hkeysRest' hfresh')

/-- Canonical ground bindings merge into the empty seed without change. -/
private theorem mergeGround_empty_left_of_canon
    {b : Bindings} (hb : GroundBindingsCanon b) :
    mergeGround? Bindings.empty b = some b := by
  rcases b with ⟨assignments, equalities⟩
  have hEq : equalities = [] := hb.1.2
  cases hEq
  simp [mergeGround?, Bindings.empty]
  exact mergeGroundAssignments_append_fresh
    (seed := Bindings.empty)
    (rest := assignments)
    rfl
    Bindings.KeysNodup.empty
    hb.2
    (by
      intro v hv
      simp [Bindings.empty, Bindings.lookup])

/-- At fuel 2, canonical ground bindings merged into the empty seed reproduce
the same bindings as a singleton result. -/
private theorem mergeBindings_empty_left_two_of_canon
    {b : Bindings} (hb : GroundBindingsCanon b) :
    mergeBindings Bindings.empty b 2 = [b] := by
  rw [← mergeGround_toList_eq_mergeBindings_two Bindings.empty b rfl hb.1.2]
  simp [mergeGround_empty_left_of_canon hb]

/-- Canonical ground bindings survive re-merging into the empty seed at any
fuel at least `2`. This packages the empty-seed self-membership fact in the
shape later head/tail reassembly lemmas want. -/
private theorem mergeBindings_empty_left_mem_of_canon
    {b : Bindings} (hb : GroundBindingsCanon b) (extra : Nat) :
    b ∈ mergeBindings Bindings.empty b (2 + extra) := by
  have hbase : b ∈ mergeBindings Bindings.empty b 2 := by
    rw [mergeBindings_empty_left_two_of_canon hb]
    simp
  have hsub := mergeBindings_mono_add Bindings.empty b 2 extra
  exact hsub b hbase

/-- Ground/canonical head reassembly into an empty-seeded official list run:
if a canonical ground head match `mb` is available and the tail runs from
`[mb]`, then the whole run can be rebuilt from the empty seed at some common
fuel. This is the exact assembly shape the singleton-seed factorization uses
after composing merges. -/
private theorem matchAtomsList_cons_of_head_tail_empty_ground
    {t p : Atom} {ts ps : List Atom}
    {mb qb : Bindings} {fuelHead fuelTail : Nat}
    (hmbCanon : GroundBindingsCanon mb)
    (hhead : mb ∈ matchAtoms t p fuelHead)
    (htail : qb ∈ matchAtomsList ts ps [mb] fuelTail) :
    ∃ fuel, qb ∈ matchAtomsList (t :: ts) (p :: ps) [Bindings.empty] (fuel + 1) := by
  let fuel := max (max fuelHead fuelTail) 2
  have hHeadLe : fuelHead ≤ fuel := by
    dsimp [fuel]
    exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hTailLe : fuelTail ≤ fuel := by
    dsimp [fuel]
    exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have hhead' : mb ∈ matchAtoms t p fuel := by
    have hEq : fuelHead + (fuel - fuelHead) = fuel := Nat.add_sub_of_le hHeadLe
    simpa [hEq] using
      (matchAtoms_mono_add t p fuelHead (fuel - fuelHead)) mb hhead
  have htail' : qb ∈ matchAtomsList ts ps [mb] fuel := by
    have hEq : fuelTail + (fuel - fuelTail) = fuel := Nat.add_sub_of_le hTailLe
    simpa [hEq] using
      (matchAtomsList_mono_add ts ps [mb] fuelTail (fuel - fuelTail)) qb htail
  have hFuelGe2 : 2 ≤ fuel := by
    dsimp [fuel]
    exact Nat.le_max_right _ _
  obtain ⟨extra, hExtra⟩ := Nat.exists_eq_add_of_le hFuelGe2
  have hseed : mb ∈ mergeBindings Bindings.empty mb fuel := by
    rw [hExtra]
    exact mergeBindings_empty_left_mem_of_canon hmbCanon extra
  have hheadSeed :
      mb ∈ (matchAtoms t p fuel).flatMap
        (fun mb0 => mergeBindings Bindings.empty mb0 fuel) :=
    List.mem_flatMap.mpr ⟨mb, hhead', hseed⟩
  exact matchAtomsList_cons_of_head_tail hheadSeed htail'

private theorem lookup_some_mem_assignments {xs : List (String × Atom)}
    {v : String} {a : Atom} (h : List.lookup v xs = some a) :
    (v, a) ∈ xs := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
      rcases x with ⟨k, b⟩
      by_cases hk : v == k
      · have hvk : v = k := by simpa using hk
        simp [List.lookup_cons, hk] at h
        subst hvk
        subst h
        simp
      · simp [List.lookup_cons, hk] at h
        simpa using Or.inr (ih h)

private theorem lookup_some_of_mem_assignment {xs : List (String × Atom)}
    {v : String} {a : Atom} (hmem : (v, a) ∈ xs) :
    ∃ a', List.lookup v xs = some a' := by
  induction xs with
  | nil => cases hmem
  | cons x xs ih =>
      rcases x with ⟨k, b⟩
      simp at hmem
      rcases hmem with h | h
      · rcases h with ⟨rfl, rfl⟩
        refine ⟨a, ?_⟩
        simp
      · by_cases hk : v == k
        · exact ⟨b, by simp [List.lookup_cons, hk]⟩
        · rcases ih h with ⟨a', ha'⟩
          exact ⟨a', by simp [List.lookup_cons, hk, ha']⟩

private theorem lookup_ground {b : Bindings} (hb : GroundBindings b)
    {v : String} {a : Atom} (h : b.lookup v = some a) : GroundAtom a := by
  exact hb.1 (v, a) (lookup_some_mem_assignments h)

/-- A ground atom has no variable occurrence, including inside compound values. -/
theorem GroundAtom.not_occurs {atom : Atom} (ground : GroundAtom atom) {name : String} :
    ¬Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.AtomOccurs atom name := by
  intro occurrence
  induction ground with
  | symbol => cases occurrence
  | grounded => cases occurrence
  | expression children ih =>
      cases occurrence with
      | expression member occurrence => exact ih _ member occurrence

private theorem hasAssignedVarAux_false_of_ground :
    ∀ (fuel : Nat) {a : Atom}, GroundAtom a →
      ∀ b : Bindings, b.hasAssignedVarAux fuel a = false := by
  intro fuel
  induction fuel with
  | zero => intro a ha b; rfl
  | succ n ih =>
      intro a ha b
      cases a with
      | var v => exact (GroundAtom.not_var ha).elim
      | symbol s => rfl
      | grounded g => rfl
      | expression es =>
          simp only [Bindings.hasAssignedVarAux]
          rw [List.any_eq_false]
          intro e he
          simp [ih (GroundAtom.elem ha he) b]

private theorem hasAssignedVar_false_of_ground {a : Atom}
    (ha : GroundAtom a) (b : Bindings) : b.hasAssignedVar a = false := by
  unfold Bindings.hasAssignedVar
  exact hasAssignedVarAux_false_of_ground _ ha b

private theorem resolveAtomAux_eq_of_ground :
    ∀ (fuel : Nat) (a : Atom), GroundAtom a →
      ∀ (visited : List String) (b₁ b₂ : Bindings),
        b₁.resolveAtomAux fuel visited a = b₂.resolveAtomAux fuel visited a := by
  intro fuel
  induction fuel with
  | zero => intro a ha visited b₁ b₂; rfl
  | succ n ih =>
      intro a ha visited b₁ b₂
      cases a with
      | var v => exact (GroundAtom.not_var ha).elim
      | symbol s => rfl
      | grounded g => rfl
      | expression es =>
          have hground : ∀ e ∈ es, GroundAtom e := by
            cases ha with
            | expression h => exact h
          clear ha
          have hmap :
              es.mapM (b₁.resolveAtomAux n visited) =
                es.mapM (b₂.resolveAtomAux n visited) := by
            induction es with
            | nil => rfl
            | cons e es ihEs =>
                have he : GroundAtom e := hground e (by simp)
                have hes : ∀ a ∈ es, GroundAtom a := by
                  intro a ha
                  exact hground a (by simp [ha])
                simp only [List.mapM_cons]
                rw [ih e he visited b₁ b₂, ihEs hes]
          simp only [Bindings.resolveAtomAux]
          rw [hmap]

/-- Once the factorization theorem is known for singleton seeds, it lifts
immediately to arbitrary seed lists via `matchAtomsList_seedwise`. -/
private theorem matchAtomsList_lift_singleton_factor
    {lefts rights : List Atom} {fuel : Nat}
    (hsingle :
      ∀ {b x : Bindings},
        GroundBindings b →
        x ∈ matchAtomsList lefts rights [b] fuel →
          ∃ fr,
            fr ∈ matchAtomsList lefts rights [Bindings.empty] fuel ∧
            x ∈ mergeBindings b fr 2) :
    ∀ {seeds : List Bindings} {x : Bindings},
      (∀ b ∈ seeds, GroundBindings b) →
      x ∈ matchAtomsList lefts rights seeds fuel →
        ∃ b ∈ seeds, ∃ fr,
          fr ∈ matchAtomsList lefts rights [Bindings.empty] fuel ∧
          x ∈ mergeBindings b fr 2 := by
  intro seeds x hseeds hx
  obtain ⟨b, hb, hx_single⟩ := (mem_matchAtomsList_seedwise).mp hx
  obtain ⟨fr, hfr, hmerge⟩ := hsingle (hseeds b hb) hx_single
  exact ⟨b, hb, fr, hfr, hmerge⟩

/-! ## Ground-result preservation for the official matcher

When the scrutinee side of the official matcher is ground, every
successful matcher result contains only ground assignment values and no
equalities.  This is the key invariant needed to factor the official
matcher through the coarse one-way matcher on ground targets. -/

theorem matcher_ground : ∀ n : Nat,
    (∀ left right result,
      GroundAtom left →
      result ∈ matchAtoms left right n →
      GroundBindings result) ∧
    (∀ lefts rights acc result,
      (∀ p ∈ lefts, GroundAtom p) →
      (∀ b ∈ acc, GroundBindings b) →
      result ∈ matchAtomsList lefts rights acc n →
      GroundBindings result) ∧
    (∀ left right result,
      GroundBindings left →
      GroundBindings right →
      result ∈ mergeBindings left right n →
      GroundBindings result) ∧
    (∀ b v val result,
      GroundBindings b →
      GroundAtom val →
      result ∈ addVarBinding b v val n →
      GroundBindings result) := by
  intro n
  induction n with
  | zero =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro left right result hleft hmem
        simp [matchAtoms] at hmem
      · intro lefts rights acc result hlefts hacc hmem
        simp [matchAtomsList] at hmem
      · intro left right result hleft hright hmem
        simp [mergeBindings] at hmem
      · intro b v val result hb hval hmem
        simp [addVarBinding] at hmem
  | succ n ih =>
      obtain ⟨ihA, ihL, ihM, ihB⟩ := ih
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro left right result hleft hmem
        cases left with
        | var v =>
            exact (GroundAtom.not_var hleft).elim
        | symbol s =>
            cases right with
            | var v =>
                have hmem' := by
                  simpa [matchAtoms, getMetaType, Atom.symbolType] using hmem
                rcases hmem' with ⟨⟨_, rfl⟩, _⟩
                exact GroundBindings.assign GroundBindings.empty (.symbol s)
            | symbol t =>
                have hmem' := by
                  simpa [matchAtoms, getMetaType, Atom.symbolType] using hmem
                rcases hmem' with ⟨⟨_, rfl⟩, _⟩
                exact GroundBindings.empty
            | grounded g =>
                simp [matchAtoms, getMetaType, Atom.symbolType, Atom.groundedType] at hmem
            | expression es =>
                simp [matchAtoms, getMetaType, Atom.symbolType, Atom.expressionType] at hmem
        | grounded g =>
            cases right with
            | var v =>
                have hmem' := by
                  simpa [matchAtoms, getMetaType, Atom.groundedType] using hmem
                rcases hmem' with ⟨⟨_, rfl⟩, _⟩
                exact GroundBindings.assign GroundBindings.empty (.grounded g)
            | symbol s =>
                simp [matchAtoms, getMetaType, Atom.groundedType, Atom.symbolType] at hmem
            | grounded h =>
                have hmem' := by
                  simpa [matchAtoms, getMetaType, Atom.groundedType] using hmem
                rcases hmem' with ⟨⟨_, rfl⟩, _⟩
                exact GroundBindings.empty
            | expression es =>
                simp [matchAtoms, getMetaType, Atom.groundedType, Atom.expressionType] at hmem
        | expression lefts =>
            cases right with
            | var v =>
                have hmem' := by
                  simpa [matchAtoms, getMetaType, Atom.expressionType] using hmem
                rcases hmem' with ⟨⟨_, rfl⟩, _⟩
                exact GroundBindings.assign GroundBindings.empty hleft
            | symbol s =>
                simp [matchAtoms, getMetaType, Atom.expressionType, Atom.symbolType] at hmem
            | grounded g =>
                simp [matchAtoms, getMetaType, Atom.expressionType, Atom.groundedType] at hmem
            | expression rights =>
                have hchild : ∀ p ∈ lefts, GroundAtom p := by
                  intro p hp
                  exact GroundAtom.elem hleft hp
                have hmem' := by
                  simpa [matchAtoms, getMetaType, Atom.expressionType] using hmem
                rcases hmem' with ⟨⟨_, hraw⟩, _⟩
                exact ihL lefts rights [Bindings.empty] result hchild
                  (by
                    intro b hb
                    simp at hb
                    rcases hb with rfl
                    exact GroundBindings.empty)
                  hraw
      · intro lefts rights acc result hlefts hacc hmem
        cases lefts with
        | nil =>
            cases rights with
            | nil =>
                simpa [matchAtomsList] using hacc result hmem
            | cons r rs =>
                simp [matchAtomsList] at hmem
        | cons left lefts =>
            cases rights with
            | nil =>
                simp [matchAtomsList] at hmem
            | cons right rights =>
                simp only [matchAtomsList] at hmem
                have hnext : ∀ b ∈ acc.flatMap (fun a => (matchAtoms left right n).flatMap fun mb =>
                    mergeBindings a mb n), GroundBindings b := by
                  intro b hb
                  rcases List.mem_flatMap.mp hb with ⟨a, ha, hb⟩
                  rcases List.mem_flatMap.mp hb with ⟨mb, hmb, hmerge⟩
                  have hga : GroundBindings a := hacc a ha
                  have hgm : GroundBindings mb := ihA left right mb (hlefts left (by simp)) hmb
                  exact ihM a mb b hga hgm hmerge
                exact ihL lefts rights _ result
                  (by
                    intro p hp
                    exact hlefts p (by simp [hp]))
                  hnext
                  hmem
      · intro left right result hleft hright hmem
        have hassign :
            ∀ (assigns : List (String × Atom)) (acc : List Bindings) result,
              (∀ p : String × Atom, p ∈ assigns → GroundAtom p.2) →
              (∀ b ∈ acc, GroundBindings b) →
              result ∈ List.foldl
                (fun acc (v, val) => acc.flatMap fun b => addVarBinding b v val n) acc assigns →
              GroundBindings result := by
          intro assigns
          induction assigns with
          | nil =>
              intro acc result hground hacc hres
              simpa using hacc result hres
          | cons pair assigns ihAssigns =>
              rcases pair with ⟨v, val⟩
              intro acc result hground hacc hres
              simp only [List.foldl_cons] at hres
              have hval : GroundAtom val := hground (v, val) (by simp)
              have hacc' : ∀ b ∈ acc.flatMap (fun b => addVarBinding b v val n), GroundBindings b := by
                intro b hb
                rcases List.mem_flatMap.mp hb with ⟨b0, hb0, hb1⟩
                exact ihB b0 v val b (hacc b0 hb0) hval hb1
              exact ihAssigns _ _ (by
                intro p hp
                exact hground p (by simp [hp])) hacc' hres
        have heqs : right.equalities = [] := hright.2
        simp only [mergeBindings, heqs, List.foldl_nil] at hmem
        exact hassign right.assignments [left] result hright.1
          (by
            intro b hb
            simp at hb
            rcases hb with rfl
            exact hleft)
          hmem
      · intro b v val result hb hval hmem
        rw [addVarBinding_no_equalities hb.2 n] at hmem
        cases hlook : b.lookup v with
        | none =>
            simp [hlook] at hmem
            rcases hmem with rfl
            exact GroundBindings.assign hb hval
        | some prev =>
            simp only [hlook] at hmem
            split at hmem <;> rename_i hsame
            · simp at hmem
              rcases hmem with rfl
              exact hb
            · rcases List.mem_flatMap.mp hmem with ⟨mb, hmb, hmerge⟩
              have hprev : GroundAtom prev := lookup_ground hb hlook
              have hmb : GroundBindings mb := ihA prev val mb hprev hmb
              exact ihM b mb result hb hmb hmerge

/-- Filtering by `!hasLoop` is inert on lists of ground bindings. -/
private theorem filter_hasLoop_eq_self (xs : List Bindings)
    (hxs : ∀ b ∈ xs, GroundBindings b) :
    xs.filter (fun b => !b.hasLoop) = xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      have hb : GroundBindings b := hxs b (by simp)
      have htail : ∀ b' ∈ xs, GroundBindings b' := by
        intro b' hb'
        exact hxs b' (by simp [hb'])
      simp [GroundBindings.hasLoop_false hb, ih htail]

/-- On ground-left expression matching, the top-level `hasLoop` filter is
inert: every list result is already loop-free by `matcher_ground`. -/
theorem matchAtoms_ground_expr_filter_free
    (lefts rights : List Atom) (n : Nat)
    (hlefts : ∀ p ∈ lefts, GroundAtom p) :
    matchAtoms (.expression lefts) (.expression rights) (n + 1) =
      if lefts.length == rights.length then
        matchAtomsList lefts rights [Bindings.empty] n
      else [] := by
  have hmatchers := matcher_ground n
  rcases hmatchers with ⟨_, hList, _, _⟩
  simp [matchAtoms, getMetaType, Atom.expressionType]
  intro b hlen hb
  exact GroundBindings.hasLoop_false <|
    hList lefts rights [Bindings.empty] b hlefts
      (by
        intro b' hb'
        simp at hb'
        rcases hb' with rfl
        exact GroundBindings.empty)
      hb

/-- Ground scrutinee against a variable pattern is exact assignment, with the
top-level `hasLoop` filter inert by groundness. -/
theorem matchAtoms_ground_var_exact
    (left : Atom) (v : String) (n : Nat)
    (hleft : GroundAtom left) :
    matchAtoms left (.var v) (n + 1) = [Bindings.empty.assign v left] := by
  cases left with
  | var w =>
      exact (GroundAtom.not_var hleft).elim
  | symbol s =>
      have hloop :
          (Bindings.empty.assign v (.symbol s)).hasLoop = false :=
        GroundBindings.hasLoop_false
          (GroundBindings.assign GroundBindings.empty (.symbol s))
      simp [matchAtoms, getMetaType, Atom.symbolType, Atom.variableType, hloop]
  | grounded g =>
      have hloop :
          (Bindings.empty.assign v (.grounded g)).hasLoop = false :=
        GroundBindings.hasLoop_false
          (GroundBindings.assign GroundBindings.empty (.grounded g))
      simp [matchAtoms, getMetaType, Atom.groundedType, Atom.variableType, hloop]
  | expression es =>
      have hloop :
          (Bindings.empty.assign v (.expression es)).hasLoop = false :=
        GroundBindings.hasLoop_false
          (GroundBindings.assign GroundBindings.empty hleft)
      simp [matchAtoms, getMetaType, Atom.expressionType, Atom.variableType, hloop]

/-- On the ground fragment, any successful official atom match returns the
empty bindings and therefore witnesses actual atom equality.  The list form is
specialized to the empty seed because that is the official matcher shape used
by `matchAtoms` on expression nodes. -/
private theorem ground_matchAtoms_mem_empty_eq : ∀ n : Nat,
    (∀ left right result,
      GroundAtom left →
      GroundAtom right →
      result ∈ matchAtoms left right (n + 1) →
        result = Bindings.empty ∧ left = right) ∧
    (∀ lefts rights result,
      (∀ p ∈ lefts, GroundAtom p) →
      (∀ p ∈ rights, GroundAtom p) →
      result ∈ matchAtomsList lefts rights [Bindings.empty] (n + 1) →
        result = Bindings.empty ∧ lefts = rights) := by
  intro n
  induction n with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro left right result hleft hright hmem
        cases left with
        | var v =>
            exact (GroundAtom.not_var hleft).elim
        | symbol s =>
            cases right with
            | var v =>
                exact (GroundAtom.not_var hright).elim
            | symbol t =>
                have hmem' : (s = t ∧ result = Bindings.empty) ∧ result.hasLoop = false := by
                  simpa [matchAtoms, getMetaType, Atom.symbolType] using hmem
                rcases hmem' with ⟨⟨hst, rfl⟩, _⟩
                exact ⟨rfl, by simpa using hst⟩
            | grounded g =>
                simp [matchAtoms, getMetaType, Atom.symbolType, Atom.groundedType] at hmem
            | expression es =>
                simp [matchAtoms, getMetaType, Atom.symbolType, Atom.expressionType] at hmem
        | grounded g =>
            cases right with
            | var v =>
                exact (GroundAtom.not_var hright).elim
            | symbol s =>
                simp [matchAtoms, getMetaType, Atom.groundedType, Atom.symbolType] at hmem
            | grounded h =>
                have hmem' : (g = h ∧ result = Bindings.empty) ∧ result.hasLoop = false := by
                  simpa [matchAtoms, getMetaType, Atom.groundedType] using hmem
                rcases hmem' with ⟨⟨hgh, rfl⟩, _⟩
                exact ⟨rfl, by simpa using hgh⟩
            | expression es =>
                simp [matchAtoms, getMetaType, Atom.groundedType, Atom.expressionType] at hmem
        | expression ls =>
            cases right with
            | var v =>
                exact (GroundAtom.not_var hright).elim
            | symbol s =>
                simp [matchAtoms, getMetaType, Atom.expressionType, Atom.symbolType] at hmem
            | grounded g =>
                simp [matchAtoms, getMetaType, Atom.expressionType, Atom.groundedType] at hmem
            | expression rs =>
                simp [matchAtoms, getMetaType, Atom.expressionType, matchAtomsList] at hmem
      · intro lefts rights result hlefts hrights hmem
        cases lefts with
        | nil =>
            cases rights with
            | nil =>
                simp [matchAtomsList] at hmem
                exact ⟨hmem, rfl⟩
            | cons r rs =>
                simp [matchAtomsList] at hmem
        | cons l ls =>
            cases rights with
            | nil =>
                simp [matchAtomsList] at hmem
            | cons r rs =>
                simp [matchAtomsList] at hmem
  | succ n ih =>
      obtain ⟨ihA, ihL⟩ := ih
      refine ⟨?_, ?_⟩
      · intro left right result hleft hright hmem
        cases left with
        | var v =>
            exact (GroundAtom.not_var hleft).elim
        | symbol s =>
            cases right with
            | var v =>
                exact (GroundAtom.not_var hright).elim
            | symbol t =>
                have hmem' : (s = t ∧ result = Bindings.empty) ∧ result.hasLoop = false := by
                  simpa [matchAtoms, getMetaType, Atom.symbolType] using hmem
                rcases hmem' with ⟨⟨hst, rfl⟩, _⟩
                exact ⟨rfl, by simpa using hst⟩
            | grounded g =>
                simp [matchAtoms, getMetaType, Atom.symbolType, Atom.groundedType] at hmem
            | expression es =>
                simp [matchAtoms, getMetaType, Atom.symbolType, Atom.expressionType] at hmem
        | grounded g =>
            cases right with
            | var v =>
                exact (GroundAtom.not_var hright).elim
            | symbol s =>
                simp [matchAtoms, getMetaType, Atom.groundedType, Atom.symbolType] at hmem
            | grounded h =>
                have hmem' : (g = h ∧ result = Bindings.empty) ∧ result.hasLoop = false := by
                  simpa [matchAtoms, getMetaType, Atom.groundedType] using hmem
                rcases hmem' with ⟨⟨hgh, rfl⟩, _⟩
                exact ⟨rfl, by simpa using hgh⟩
            | expression es =>
                simp [matchAtoms, getMetaType, Atom.groundedType, Atom.expressionType] at hmem
        | expression ls =>
            cases right with
            | var v =>
                exact (GroundAtom.not_var hright).elim
            | symbol s =>
                simp [matchAtoms, getMetaType, Atom.expressionType, Atom.symbolType] at hmem
            | grounded g =>
                simp [matchAtoms, getMetaType, Atom.expressionType, Atom.groundedType] at hmem
            | expression rs =>
                have hls : ∀ p ∈ ls, GroundAtom p := by
                  intro p hp
                  exact GroundAtom.elem hleft hp
                have hrs : ∀ p ∈ rs, GroundAtom p := by
                  intro p hp
                  exact GroundAtom.elem hright hp
                have hmemExpr :
                    (ls.length = rs.length ∧
                      result ∈ matchAtomsList ls rs [Bindings.empty] (n + 1)) ∧
                        result.hasLoop = false := by
                  simpa [matchAtoms, getMetaType, Atom.expressionType] using hmem
                obtain ⟨hres, hEq⟩ := ihL ls rs result hls hrs hmemExpr.1.2
                exact ⟨hres, by simp [hEq]⟩
      · intro lefts rights result hlefts hrights hmem
        cases lefts with
        | nil =>
            cases rights with
            | nil =>
                simpa [matchAtomsList] using hmem
            | cons r rs =>
                simp [matchAtomsList] at hmem
        | cons l ls =>
            cases rights with
            | nil =>
                simp [matchAtomsList] at hmem
            | cons r rs =>
                have hl : GroundAtom l := hlefts l (by simp)
                have hr : GroundAtom r := hrights r (by simp)
                have hmem' := by
                  simpa [matchAtomsList] using hmem
                obtain ⟨headRes, hhead, htail⟩ :=
                  (mem_matchAtomsList_flatMap_acc
                    (lefts := ls) (rights := rs)
                    (acc := matchAtoms l r (n + 1))
                    (f := fun mb => mergeBindings Bindings.empty mb (n + 1))
                    (fuel := n + 1) (x := result)).mp hmem'
                obtain ⟨hheadRes, hlr⟩ := ihA l r headRes hl hr hhead
                subst hheadRes
                have htail' : result ∈ matchAtomsList ls rs [Bindings.empty] (n + 1) := by
                  simpa [mergeBindings_empty_right Bindings.empty n] using htail
                obtain ⟨hres, hEqTail⟩ := ihL ls rs result
                  (fun p hp => hlefts p (by simp [hp]))
                  (fun p hp => hrights p (by simp [hp]))
                  htail'
                exact ⟨hres, by simp [hlr, hEqTail]⟩

/-- If both the queried atom and the pattern are ground, any successful
official match is the empty binding witness and therefore certifies literal
atom equality. -/
theorem matchAtoms_ground_rigid_exact
    {left right : Atom} {result : Bindings} {n : Nat}
    (hleft : GroundAtom left)
    (hright : GroundAtom right)
    (hmem : result ∈ matchAtoms left right (n + 1)) :
    result = Bindings.empty ∧ left = right :=
  (ground_matchAtoms_mem_empty_eq n).1 left right result hleft hright hmem

/-- Two different ground atoms never officially match. -/
private theorem matchAtoms_ground_ne_nil
    {left right : Atom} {n : Nat}
    (hleft : GroundAtom left) (hright : GroundAtom right)
    (hneq : left ≠ right) :
    matchAtoms left right (n + 1) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro result hmem
  obtain ⟨_, heq⟩ := (ground_matchAtoms_mem_empty_eq n).1 left right result hleft hright hmem
  exact hneq heq

/-- Ground/canonical bindings stay canonical through one-way variable binding
on a ground value.  On the ground fragment, the conflicting-rebinding branch
cannot recover via deeper matching, so the only surviving outcomes are the
fresh-assign and same-value cases. -/
private theorem addVarBinding_canon
    {b result : Bindings} {v : String} {val : Atom} {fuel : Nat}
    (hb : GroundBindingsCanon b) (hval : GroundAtom val)
    (hres : result ∈ addVarBinding b v val fuel) :
    GroundBindingsCanon result := by
  cases fuel with
  | zero =>
      simp [addVarBinding] at hres
  | succ n =>
      rw [addVarBinding_no_equalities hb.1.2 n] at hres
      cases hlook : b.lookup v with
      | none =>
          simp [hlook] at hres
          rcases hres with rfl
          exact GroundBindingsCanon.assign hb hval
      | some prev =>
          have hprev : GroundAtom prev := lookup_ground hb.1 hlook
          by_cases hsame : prev == val
          · simp [hlook, hsame] at hres
            rcases hres with rfl
            exact hb
          · have hneq : prev ≠ val := by
              intro heq
              exact hsame (by simp [heq])
            cases n with
            | zero =>
                simp [hlook, hsame, matchAtoms] at hres
            | succ k =>
                have hmatchNil : matchAtoms prev val (k + 1) = [] :=
                  matchAtoms_ground_ne_nil hprev hval hneq
                simp [hlook, hsame, hmatchNil] at hres

/-- Folding `addVarBinding` over a canonical accumulator and a ground
assignment list preserves canonicality. -/
private theorem fold_addVarBinding_canon
    (acc : List Bindings) (assigns : List (String × Atom)) (fuel : Nat)
    (hacc : ∀ b ∈ acc, GroundBindingsCanon b)
    (hassigns : ∀ p ∈ assigns, GroundAtom p.2) :
    ∀ b ∈ assigns.foldl
        (fun acc (v, val) => acc.flatMap fun b => addVarBinding b v val fuel) acc,
      GroundBindingsCanon b := by
  induction assigns generalizing acc with
  | nil =>
      simpa
  | cons pair assigns ih =>
      rcases pair with ⟨v, val⟩
      have hval : GroundAtom val := hassigns (v, val) (by simp)
      have hacc' :
          ∀ b ∈ acc.flatMap (fun b => addVarBinding b v val fuel),
            GroundBindingsCanon b := by
        intro b hb
        rcases List.mem_flatMap.mp hb with ⟨b0, hb0, hstep⟩
        exact addVarBinding_canon (hacc b0 hb0) hval hstep
      simp only [List.foldl_cons]
      exact ih _ hacc' (fun p hp => hassigns p (List.mem_cons_of_mem _ hp))

/-- Merging canonical ground bindings preserves canonicality.  The right side's
equalities list is empty on this fragment, so only the assignment fold matters. -/
private theorem mergeBindings_canon
    {left right result : Bindings} {fuel : Nat}
    (hleft : GroundBindingsCanon left) (hright : GroundBindingsCanon right)
    (hres : result ∈ mergeBindings left right fuel) :
    GroundBindingsCanon result := by
  cases fuel with
  | zero =>
      simp [mergeBindings] at hres
  | succ n =>
      have hafter :
          ∀ b ∈ right.assignments.foldl
              (fun acc (v, val) => acc.flatMap fun b => addVarBinding b v val n) [left],
            GroundBindingsCanon b := by
        exact fold_addVarBinding_canon [left] right.assignments n
          (by
            intro b hb
            simp at hb
            rcases hb with rfl
            exact hleft)
          hright.1.1
      simp [mergeBindings, hright.1.2] at hres
      exact hafter result hres

/-- On ground scrutinees, the official matcher and singleton-seeded official
list matcher produce canonical bindings: ground assignment values, no
equalities, and no duplicate assignment keys.  This is the exact amount of
canonicality the later factorization proof needs. -/
private theorem matcher_ground_singleton_canon : ∀ n : Nat,
    (∀ left right result,
      GroundAtom left →
      result ∈ matchAtoms left right n →
      GroundBindingsCanon result) ∧
    (∀ lefts rights b result,
      (∀ p ∈ lefts, GroundAtom p) →
      GroundBindingsCanon b →
      result ∈ matchAtomsList lefts rights [b] n →
      GroundBindingsCanon result) := by
  intro n
  induction n with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro left right result hleft hmem
        simp [matchAtoms] at hmem
      · intro lefts rights b result hlefts hb hmem
        simp [matchAtomsList] at hmem
  | succ n ih =>
      obtain ⟨ihA, ihL⟩ := ih
      refine ⟨?_, ?_⟩
      · intro left right result hleft hmem
        cases left with
        | var v =>
            exact (GroundAtom.not_var hleft).elim
        | symbol s =>
            cases right with
            | var v =>
                have hmem' := by
                  simpa [matchAtoms, getMetaType, Atom.symbolType] using hmem
                rcases hmem' with ⟨⟨_, rfl⟩, _⟩
                exact GroundBindingsCanon.assign GroundBindingsCanon.empty (GroundAtom.symbol s)
            | symbol t =>
                have hmem' := by
                  simpa [matchAtoms, getMetaType, Atom.symbolType] using hmem
                rcases hmem' with ⟨⟨_, rfl⟩, _⟩
                exact GroundBindingsCanon.empty
            | grounded g =>
                simp [matchAtoms, getMetaType, Atom.symbolType, Atom.groundedType] at hmem
            | expression es =>
                simp [matchAtoms, getMetaType, Atom.symbolType, Atom.expressionType] at hmem
        | grounded g =>
            cases right with
            | var v =>
                have hmem' := by
                  simpa [matchAtoms, getMetaType, Atom.groundedType] using hmem
                rcases hmem' with ⟨⟨_, rfl⟩, _⟩
                exact GroundBindingsCanon.assign GroundBindingsCanon.empty (GroundAtom.grounded g)
            | symbol s =>
                simp [matchAtoms, getMetaType, Atom.groundedType, Atom.symbolType] at hmem
            | grounded h =>
                have hmem' := by
                  simpa [matchAtoms, getMetaType, Atom.groundedType] using hmem
                rcases hmem' with ⟨⟨_, rfl⟩, _⟩
                exact GroundBindingsCanon.empty
            | expression es =>
                simp [matchAtoms, getMetaType, Atom.groundedType, Atom.expressionType] at hmem
        | expression lefts =>
            cases right with
            | var v =>
                have hmem' := by
                  simpa [matchAtoms, getMetaType, Atom.expressionType] using hmem
                rcases hmem' with ⟨⟨_, rfl⟩, _⟩
                exact GroundBindingsCanon.assign GroundBindingsCanon.empty hleft
            | symbol s =>
                simp [matchAtoms, getMetaType, Atom.expressionType, Atom.symbolType] at hmem
            | grounded g =>
                simp [matchAtoms, getMetaType, Atom.expressionType, Atom.groundedType] at hmem
            | expression rights =>
                have hchild : ∀ p ∈ lefts, GroundAtom p := by
                  intro p hp
                  exact GroundAtom.elem hleft hp
                have hmem' := by
                  simpa [matchAtoms, getMetaType, Atom.expressionType] using hmem
                rcases hmem' with ⟨⟨_, hraw⟩, _⟩
                exact ihL lefts rights Bindings.empty result hchild GroundBindingsCanon.empty hraw
      · intro lefts rights b result hlefts hb hmem
        cases lefts with
        | nil =>
            cases rights with
            | nil =>
                simp [matchAtomsList] at hmem
                subst hmem
                exact hb
            | cons r rs =>
                simp [matchAtomsList] at hmem
        | cons l ls =>
            cases rights with
            | nil =>
                simp [matchAtomsList] at hmem
            | cons r rs =>
                have hl : GroundAtom l := hlefts l (by simp)
                have hmem' := by
                  simpa [matchAtomsList] using hmem
                obtain ⟨mb, hmb, htailAcc⟩ :=
                  (mem_matchAtomsList_flatMap_acc
                    (lefts := ls) (rights := rs)
                    (acc := matchAtoms l r n)
                    (f := fun mb => mergeBindings b mb n)
                    (fuel := n) (x := result)).mp hmem'
                obtain ⟨b', hb', htail⟩ :=
                  (mem_matchAtomsList_seedwise
                    (lefts := ls) (rights := rs)
                    (seeds := mergeBindings b mb n)
                    (fuel := n) (x := result)).mp htailAcc
                have hmbCanon : GroundBindingsCanon mb := ihA l r mb hl hmb
                have hb'Canon : GroundBindingsCanon b' := mergeBindings_canon hb hmbCanon hb'
                exact ihL ls rs b' result
                  (fun p hp => hlefts p (by simp [hp]))
                  hb'Canon
                  htail

private theorem matchAtoms_ground_canon
    {left right : Atom} {result : Bindings} {n : Nat}
    (hleft : GroundAtom left)
    (hmem : result ∈ matchAtoms left right n) :
    GroundBindingsCanon result :=
  (matcher_ground_singleton_canon n).1 left right result hleft hmem

/-- On the ground-query fragment, every official matcher result has only ground
assignment values and no equality constraints. This is exactly the bounded
the G3 interface needs: equalities can only arise when the queried atom itself still
contains variables. -/
theorem matchAtoms_ground_bindings
    {left right : Atom} {result : Bindings} {n : Nat}
    (hleft : GroundAtom left)
    (hmem : result ∈ matchAtoms left right n) :
    GroundBindings result :=
  (matchAtoms_ground_canon hleft hmem).1

private theorem matchAtomsList_ground_empty_canon
    {lefts rights : List Atom} {result : Bindings} {n : Nat}
    (hlefts : ∀ p ∈ lefts, GroundAtom p)
    (hmem : result ∈ matchAtomsList lefts rights [Bindings.empty] n) :
    GroundBindingsCanon result :=
  (matcher_ground_singleton_canon n).2 lefts rights Bindings.empty result
    hlefts GroundBindingsCanon.empty hmem

/-- Fuel-1 `addVarBinding` preserves an already-built prefix and installs the
new assignment at its fresh key.  This is the right-hand extension step for
deterministic ground merges. -/
private theorem addVarBinding_fuel1_extends_prefix
    {pref b result : Bindings} {v : String} {val a : Atom} {x : String}
    (hlookup_none : pref.lookup v = none)
    (hext : pref.Extends b)
    (hbEq : b.equalities = [])
    (hres : result ∈ addVarBinding b v val 1)
    (hx : (pref.assign v val).lookup x = some a) :
    result.lookup x = some a := by
  rw [addVarBinding_fuel1 b v val hbEq] at hres
  cases hlook : b.lookup v with
  | none =>
      simp [hlook] at hres
      rcases hres with rfl
      by_cases hxeq : x = v
      · subst hxeq
        have hxv : a = val := by
          have := hx
          simpa [lookup_assign_of_lookup_none pref x val hlookup_none] using this.symm
        subst hxv
        exact lookup_assign_of_lookup_none b x a hlook
      · have hpref : pref.lookup x = some a := by
          simpa [assign_lookup_ne pref v val x hxeq hlookup_none] using hx
        have hb : b.lookup x = some a := hext x a hpref
        simpa [assign_lookup_ne b v val x hxeq hlook] using hb
  | some prev =>
      by_cases hsame : prev == val
      · simp [hlook, hsame] at hres
        rcases hres with rfl
        by_cases hxeq : x = v
        · subst hxeq
          have hxv : a = val := by
            have := hx
            simpa [lookup_assign_of_lookup_none pref x val hlookup_none] using this.symm
          subst hxv
          simpa [hlook] using hsame
        · have hpref : pref.lookup x = some a := by
            simpa [assign_lookup_ne pref v val x hxeq hlookup_none] using hx
          exact hext x a hpref
      · simp [hlook, hsame] at hres

/-- Folding fuel-1 `addVarBinding` over a list of fresh assignments preserves
the whole accumulated right-hand fragment in every surviving result. -/
private theorem fold_addVarBinding_fuel1_extends_prefix
    (acc : List Bindings) (pref : Bindings) (rest : List (String × Atom))
    (hEq : pref.equalities = [])
    (hkeys : Bindings.KeysNodup pref)
    (hrestKeys : (rest.map Prod.fst).Nodup)
    (hfresh : ∀ v, v ∈ rest.map Prod.fst → pref.lookup v = none)
    (hacc : ∀ b ∈ acc, pref.Extends b)
    (haccEq : ∀ b ∈ acc, b.equalities = []) :
    ∀ result ∈ List.foldl
        (fun acc x => acc.flatMap fun b => addVarBinding b x.1 x.2 1)
        acc rest,
      ({ assignments := pref.assignments ++ rest, equalities := [] } : Bindings).Extends result := by
  induction rest generalizing acc pref with
  | nil =>
      intro result hresult
      have hpref : ({ assignments := pref.assignments, equalities := [] } : Bindings) = pref := by
        rw [← hEq]
      rw [List.append_nil, hpref]
      exact hacc result hresult
  | cons pair rest ih =>
      rcases pair with ⟨v, val⟩
      have hlookup : pref.lookup v = none := hfresh v (by simp)
      have hnotbound : pref.isBound v = false := by
        simp [Bindings.isBound, hlookup]
      have hnotmemRest : v ∉ rest.map Prod.fst := by
        simpa using (List.nodup_cons.mp hrestKeys).1
      have hkeysRest : (rest.map Prod.fst).Nodup := by
        simpa using (List.nodup_cons.mp hrestKeys).2
      have hEq' : (pref.assign v val).equalities = [] := by
        simpa [Bindings.assign, hnotbound] using hEq
      have hfresh' : ∀ w, w ∈ rest.map Prod.fst → (pref.assign v val).lookup w = none := by
        intro w hw
        have hwne : w ≠ v := by
          intro hwv
          subst hwv
          exact hnotmemRest hw
        simpa [hfresh w (by simp [hw])] using assign_lookup_ne pref v val w hwne hlookup
      have hacc' : ∀ b ∈ acc.flatMap (fun b => addVarBinding b v val 1), (pref.assign v val).Extends b := by
        intro b hb x a hx
        rcases List.mem_flatMap.mp hb with ⟨b0, hb0, hstep⟩
        exact addVarBinding_fuel1_extends_prefix hlookup (hacc b0 hb0)
          (haccEq b0 hb0) hstep hx
      have haccEq' :
          ∀ b ∈ acc.flatMap (fun b => addVarBinding b v val 1), b.equalities = [] := by
        intro b hb
        rcases List.mem_flatMap.mp hb with ⟨b0, hb0, hstep⟩
        exact addVarBinding_fuel1_no_equalities (haccEq b0 hb0) hstep
      intro result hresult
      simp only [List.foldl_cons] at hresult
      have htail :=
        ih (acc.flatMap fun b => addVarBinding b v val 1) (pref.assign v val)
          hEq' (Bindings.KeysNodup.assign hkeys) hkeysRest hfresh' hacc'
          haccEq'
          result hresult
      simpa [Bindings.assign, hnotbound, List.append_assoc] using htail

/-- Any successful fuel-2 merge with a canonical right-hand fragment preserves
that entire fragment inside the result.  This is the honest pointwise form of
"seeded official matching still contains the official fragment". -/
private theorem mergeBindings_two_extends_right_of_canon
    {left right result : Bindings}
    (hleftEq : left.equalities = [])
    (hright : GroundBindingsCanon right)
    (hres : result ∈ mergeBindings left right 2) :
    right.Extends result := by
  rcases hright with ⟨hground, hkeys⟩
  have hres' :
      result ∈ List.foldl
        (fun acc x => acc.flatMap fun b => addVarBinding b x.1 x.2 1)
        [left] right.assignments := by
    simpa [mergeBindings, hground.2] using hres
  have hfold :
      ({ assignments := [] ++ right.assignments, equalities := [] } : Bindings).Extends result := by
    exact
      (fold_addVarBinding_fuel1_extends_prefix [left] Bindings.empty right.assignments
        rfl Bindings.KeysNodup.empty hkeys
        (by
          intro v hv
          simp [Bindings.empty, Bindings.lookup])
        (by
          intro b hb
          rcases List.mem_singleton.mp hb with rfl
          intro x a hx
          simp [Bindings.empty, Bindings.lookup] at hx)
        (by
          intro b hb
          rcases List.mem_singleton.mp hb with rfl
          exact hleftEq)
        result hres')
  have hright : ({ assignments := right.assignments, equalities := [] } : Bindings) = right := by
    rw [← hground.2]
  rw [List.nil_append, hright] at hfold
  exact hfold

/-- Any successful fuel-1 `addVarBinding` step preserves every lookup already
present in the seed bindings. -/
private theorem addVarBinding_fuel1_extends_seed
    {seed result : Bindings} {v : String} {val : Atom}
    (hSeedEq : seed.equalities = [])
    (hres : result ∈ addVarBinding seed v val 1) :
    seed.Extends result := by
  rw [addVarBinding_fuel1 seed v val hSeedEq] at hres
  cases hlook : seed.lookup v with
  | none =>
      simp [hlook] at hres
      rcases hres with rfl
      exact extends_assign_of_lookup_none seed v val hlook
  | some prev =>
      by_cases hsame : prev == val
      · simp [hlook, hsame] at hres
        rcases hres with rfl
        exact fun _ _ h => h
      · simp [hlook, hsame] at hres

/-- Folding fuel-1 `addVarBinding` over any assignment list preserves the
original seed through every surviving result. -/
private theorem fold_addVarBinding_fuel1_extends_seed
    (seed : Bindings) (acc : List Bindings) (assigns : List (String × Atom))
    (hacc : ∀ b ∈ acc, seed.Extends b)
    (haccEq : ∀ b ∈ acc, b.equalities = []) :
    ∀ result ∈ List.foldl
        (fun acc x => acc.flatMap fun b => addVarBinding b x.1 x.2 1)
        acc assigns,
      seed.Extends result := by
  induction assigns generalizing acc with
  | nil =>
      intro result hresult
      exact hacc result hresult
  | cons pair assigns ih =>
      rcases pair with ⟨v, val⟩
      have hacc' :
          ∀ b ∈ acc.flatMap (fun b => addVarBinding b v val 1), seed.Extends b := by
        intro b hb
        rcases List.mem_flatMap.mp hb with ⟨b0, hb0, hstep⟩
        exact Bindings.extends_trans (hacc b0 hb0)
          (addVarBinding_fuel1_extends_seed (haccEq b0 hb0) hstep)
      have haccEq' :
          ∀ b ∈ acc.flatMap (fun b => addVarBinding b v val 1), b.equalities = [] := by
        intro b hb
        rcases List.mem_flatMap.mp hb with ⟨b0, hb0, hstep⟩
        exact addVarBinding_fuel1_no_equalities (haccEq b0 hb0) hstep
      intro result hresult
      simp only [List.foldl_cons] at hresult
      exact ih _ hacc' haccEq' result hresult

/-- Any successful fuel-2 merge preserves every lookup already present in the
left seed bindings on the ground/no-equalities fragment. -/
private theorem mergeBindings_two_extends_left
    {left right result : Bindings}
    (hleftEq : left.equalities = [])
    (hright : GroundBindings right)
    (hres : result ∈ mergeBindings left right 2) :
    left.Extends result := by
  intro x a hx
  have hseed : left.Extends result :=
    by
      have hres' :
          result ∈ List.foldl
            (fun acc x => acc.flatMap fun b => addVarBinding b x.1 x.2 1)
            [left] right.assignments := by
        simpa [mergeBindings, hright.2] using hres
      exact fold_addVarBinding_fuel1_extends_seed left [left] right.assignments
        (by
          intro b hb
          rcases List.mem_singleton.mp hb with rfl
          exact fun _ _ h => h)
        (by
          intro b hb
          rcases List.mem_singleton.mp hb with rfl
          exact hleftEq)
        result hres'
  exact hseed x a hx

/-- On ground seeds and ground values, positive-fuel `addVarBinding` collapses
to the deterministic fuel-1 case.  Conflicting rebinding cannot recover via a
deeper matcher call because two different ground atoms never match. -/
  private theorem addVarBinding_ground_eq_fuel1
    {b : Bindings} {v : String} {val : Atom} (fuel : Nat)
    (hb : GroundBindings b) (hval : GroundAtom val) :
    addVarBinding b v val (fuel + 1) = addVarBinding b v val 1 := by
  rw [addVarBinding_no_equalities hb.2 fuel,
    addVarBinding_no_equalities hb.2 0]
  cases hlook : b.lookup v with
  | none =>
      rfl
  | some prev =>
      have hprev : GroundAtom prev := lookup_ground hb hlook
      by_cases hsame : prev == val
      · simp [hsame]
      · have hneq : prev ≠ val := by
          intro heq
          exact hsame (by simp [heq])
        cases fuel with
        | zero =>
            rfl
        | succ n =>
            have hmatchNil : matchAtoms prev val (n + 1) = [] :=
              matchAtoms_ground_ne_nil hprev hval hneq
            simp only [hsame]
            rw [hmatchNil]
            simp [matchAtoms]

/-- On a ground accumulator and a ground value, one positive-fuel
`addVarBinding` step is exactly the deterministic ground-merge step. -/
private theorem flatMap_addVarBinding_ground_eq_detfold
    (acc : List Bindings) (v : String) (val : Atom) (fuel : Nat)
    (hacc : ∀ b ∈ acc, GroundBindings b) (hval : GroundAtom val) :
    acc.flatMap (fun b => addVarBinding b v val (fuel + 1)) =
      detfoldStep acc (v, val) := by
  induction acc with
  | nil => rfl
  | cons b acc ih =>
      have hb : GroundBindings b := hacc b (by simp)
      have hacc' : ∀ b' ∈ acc, GroundBindings b' := by
        intro b' hb'
        exact hacc b' (by simp [hb'])
      simp [detfoldStep, addVarBinding_ground_eq_fuel1 fuel hb hval,
        addVarBinding_fuel1 b v val hb.2, ih hacc']

/-- Deterministic ground-merge preserves the ground-bindings invariant. -/
private theorem detfoldStep_ground
    {acc : List Bindings} {v : String} {val : Atom}
    (hacc : ∀ b ∈ acc, GroundBindings b) (hval : GroundAtom val) :
    ∀ b ∈ detfoldStep acc (v, val), GroundBindings b := by
  intro b hb
  rcases List.mem_flatMap.mp hb with ⟨b0, hb0, hstep⟩
  have hb0g : GroundBindings b0 := hacc b0 hb0
  cases hlook : b0.lookup v with
  | none =>
      simp [hlook] at hstep
      rcases hstep with rfl
      exact GroundBindings.assign hb0g hval
  | some prev =>
      by_cases hsame : prev == val
      · simp [hlook, hsame] at hstep
        rcases hstep with rfl
        exact hb0g
      · simp [hlook, hsame] at hstep

/-- Folding positive-fuel `addVarBinding` over a ground accumulator and ground
assignment list collapses to the deterministic ground-merge fold. -/
private theorem fold_addVarBinding_ground_eq_detfold
    (assigns : List (String × Atom)) (acc : List Bindings) (fuel : Nat)
    (hassigns : ∀ p ∈ assigns, GroundAtom p.2)
    (hacc : ∀ b ∈ acc, GroundBindings b) :
    List.foldl
      (fun acc x => acc.flatMap fun b => addVarBinding b x.1 x.2 (fuel + 1))
      acc assigns =
    List.foldl detfoldStep acc assigns := by
  induction assigns generalizing acc with
  | nil => rfl
  | cons pair assigns ih =>
      rcases pair with ⟨v, val⟩
      have hval : GroundAtom val := hassigns (v, val) (by simp)
      have hstep :
          acc.flatMap (fun b => addVarBinding b v val (fuel + 1)) =
            detfoldStep acc (v, val) :=
        flatMap_addVarBinding_ground_eq_detfold acc v val fuel hacc hval
      have hnext : ∀ b ∈ detfoldStep acc (v, val), GroundBindings b := by
        intro b hb
        exact detfoldStep_ground hacc hval b hb
      rw [List.foldl_cons, List.foldl_cons, hstep]
      exact ih (detfoldStep acc (v, val))
        (fun p hp => hassigns p (by simp [hp]))
        hnext

/-- On the ground/no-equalities fragment, positive-fuel `mergeBindings`
collapses to the deterministic helper `mergeGround?`. -/
private theorem mergeBindings_ground_eq_mergeGround
    {left right : Bindings} (fuel : Nat)
    (hleft : GroundBindings left) (hright : GroundBindings right) :
    mergeBindings left right (fuel + 2) = (mergeGround? left right).toList := by
  rcases hright with ⟨hassigns, heqs⟩
  cases right with
  | mk assignments equalities =>
      cases heqs
      simp [mergeBindings, mergeGround?]
      rw [fold_addVarBinding_ground_eq_detfold assignments [left] fuel
        (by simpa using hassigns)
        (by
          intro b hb
          simp at hb
          rcases hb with rfl
          exact hleft)]
      simpa using (mergeGroundAssignments_toList_eq_detfold left assignments).symm

/-- Membership in a positive-fuel ground merge is equivalent to the
deterministic ground-merge helper returning that result. -/
private theorem mem_mergeBindings_ground_iff
    {left right result : Bindings} {fuel : Nat}
    (hleft : GroundBindings left) (hright : GroundBindings right) :
    result ∈ mergeBindings left right (fuel + 2) ↔
      mergeGround? left right = some result := by
  rw [mergeBindings_ground_eq_mergeGround fuel hleft hright]
  cases hmerge : mergeGround? left right with
  | none =>
      simp
  | some b =>
      simp [eq_comm]

/-- Deterministic ground merges stabilize once fuel reaches `2`: any successful
run at fuel `k + 2` is already the same successful run at fuel `2`. This is
the public fuel-collapse fact later ground-fragment replay proofs use when they
want the canonical seeded merge witness without carrying larger local merge
budgets around. -/
theorem mergeBindings_ground_to_two
    {left right result : Bindings} {fuel : Nat}
    (hleft : GroundBindings left) (hright : GroundBindings right)
    (hmem : result ∈ mergeBindings left right (fuel + 2)) :
    result ∈ mergeBindings left right 2 := by
  have hdet :
      mergeGround? left right = some result :=
    (mem_mergeBindings_ground_iff
      (left := left) (right := right) (result := result) (fuel := fuel)
      hleft hright).mp hmem
  exact
    (mem_mergeBindings_ground_iff
      (left := left) (right := right) (result := result) (fuel := 0)
      hleft hright).mpr hdet

/-- Variant of `mergeBindings_ground_to_two` with an explicit lower-bound
assumption on the caller's fuel. -/
theorem mergeBindings_ground_of_ge_two
    {left right result : Bindings} {fuel : Nat}
    (hleft : GroundBindings left) (hright : GroundBindings right)
    (hfuel : 2 ≤ fuel)
    (hmem : result ∈ mergeBindings left right fuel) :
    result ∈ mergeBindings left right 2 := by
  cases fuel with
  | zero =>
      omega
  | succ fuel =>
      cases fuel with
      | zero =>
          omega
      | succ k =>
          simpa using
            (mergeBindings_ground_to_two
              (left := left) (right := right) (result := result) (fuel := k)
              hleft hright hmem)

/-- A seeded official head match on a ground scrutinee factors through the
same head binding merged at fuel 2.  This removes fuel-skew from the
head-step part of the matcher bridge; the remaining bottleneck is the
list-level singleton-seed factorization. -/
private theorem matchAtoms_ground_seed_factor
    {left x : Bindings} {scrutinee pattern : Atom} {fuel : Nat}
    (hground : GroundAtom scrutinee) (hb : GroundBindings left)
    (hx :
      x ∈ (matchAtoms scrutinee pattern fuel).flatMap
        (fun mb => mergeBindings left mb fuel)) :
    ∃ mb,
      mb ∈ matchAtoms scrutinee pattern fuel ∧
      x ∈ mergeBindings left mb 2 := by
  obtain ⟨mb, hmb, hmerge⟩ := List.mem_flatMap.mp hx
  have hmbGround : GroundBindings mb :=
    (matcher_ground fuel).1 scrutinee pattern mb hground hmb
  cases fuel with
  | zero =>
      simp [matchAtoms] at hmb
  | succ n =>
      refine ⟨mb, hmb, ?_⟩
      cases n with
      | zero =>
          have hsub := mergeBindings_mono_add left mb 1 1
          exact hsub x hmerge
      | succ k =>
          have hdet :
              mergeGround? left mb = some x :=
            (mem_mergeBindings_ground_iff (left := left) (right := mb)
              (result := x) (fuel := k) hb hmbGround).mp hmerge
          exact
            (mem_mergeBindings_ground_iff (left := left) (right := mb)
              (result := x) (fuel := 0) hb hmbGround).mpr hdet

/-- Exact inversion of an empty-seeded official cons-run on the ground
fragment: the implicit head seed produced by the empty merge is really the
head matcher result itself, so the run decomposes to a canonical head witness
and a tail run from `[mb]` at the same inner fuel. -/
private theorem matchAtomsList_empty_cons_inv_ground
    {t p : Atom} {ts ps : List Atom} {result : Bindings} {fuel : Nat}
    (ht : GroundAtom t)
    (hmem : result ∈ matchAtomsList (t :: ts) (p :: ps) [Bindings.empty] (fuel + 1)) :
    ∃ mb,
      mb ∈ matchAtoms t p fuel ∧
      result ∈ matchAtomsList ts ps [mb] fuel := by
  have hmem' : result ∈
      matchAtomsList ts ps
        ((matchAtoms t p fuel).flatMap fun mb => mergeBindings Bindings.empty mb fuel)
        fuel := by
    simpa [matchAtomsList] using hmem
  obtain ⟨mb, hmb, htailAcc⟩ :=
    (mem_matchAtomsList_flatMap_acc
      (lefts := ts) (rights := ps)
      (acc := matchAtoms t p fuel)
      (f := fun mb => mergeBindings Bindings.empty mb fuel)
      (fuel := fuel) (x := result)).mp hmem'
  obtain ⟨b', hb', htail⟩ :=
    (mem_matchAtomsList_seedwise
      (lefts := ts) (rights := ps)
      (seeds := mergeBindings Bindings.empty mb fuel)
      (fuel := fuel) (x := result)).mp htailAcc
  have hheadSeeded :
      b' ∈ (matchAtoms t p fuel).flatMap
        (fun mb => mergeBindings Bindings.empty mb fuel) :=
    List.mem_flatMap.mpr ⟨mb, hmb, hb'⟩
  obtain ⟨mb0, hmb0, hb'2⟩ :=
    matchAtoms_ground_seed_factor ht GroundBindings.empty hheadSeeded
  have hmb0Canon : GroundBindingsCanon mb0 := matchAtoms_ground_canon ht hmb0
  have hb'det :
      mergeGround? Bindings.empty mb0 = some b' := by
    exact
      (mem_mergeBindings_ground_iff
        (left := Bindings.empty) (right := mb0) (result := b')
        (fuel := 0) GroundBindings.empty hmb0Canon.1).mp hb'2
  have hb'eq : b' = mb0 := by
    rw [mergeGround_empty_left_of_canon hmb0Canon] at hb'det
    injection hb'det with hEq
    symm
    exact hEq
  exact ⟨b', by simpa [hb'eq] using hmb0, htail⟩

/-- Empty-seed cons inversion on the ground fragment: an official list-matcher
run on `(t :: ts)` against `(p :: ps)` decomposes into a head witness for
`matchAtoms t p` and a tail run seeded by that exact head bindings value. This
is the structural public inverse the staged G3 ground agreement proof needs. -/
theorem matchAtomsList_ground_empty_cons_inv
    {t p : Atom} {ts ps : List Atom} {result : Bindings} {fuel : Nat}
    (ht : GroundAtom t)
    (hmem : result ∈ matchAtomsList (t :: ts) (p :: ps) [Bindings.empty] (fuel + 1)) :
    ∃ mb,
      mb ∈ matchAtoms t p fuel ∧
      result ∈ matchAtomsList ts ps [mb] fuel := by
  exact matchAtomsList_empty_cons_inv_ground ht hmem

/-- Deterministic ground merge composes at the equation level on the canonical
ground fragment: if `c` is the result of merging `mb` into `b`, and `x` is the
result of merging `fr` into `c`, then the middle merge `mb ⋆ fr` exists as a
concrete bindings value `g`, and merging `g` into `b` reproduces `x`. -/
private theorem mergeGround_seed_compose
    {b mb c fr x : Bindings}
    (hb : GroundBindings b)
    (hmbCanon : GroundBindingsCanon mb)
    (hfrCanon : GroundBindingsCanon fr)
    (hc : mergeGround? b mb = some c)
    (hx : mergeGround? c fr = some x) :
    ∃ g,
      mergeGround? mb fr = some g ∧
      mergeGround? b g = some x := by
  let restAssigns := fr.assignments.filter (fun p => (mb.lookup p.1).isNone)
  let rest : Bindings := { assignments := restAssigns, equalities := [] }
  let g : Bindings := { assignments := mb.assignments ++ restAssigns, equalities := [] }
  have hmbExt : mb.Extends c :=
    mergeGround_extends_right_of_nodup hmbCanon.1.2 hmbCanon.2 hc
  have hmid :
      mergeGround? mb fr = some g := by
    have hag :
        ∀ {v aM aF},
          mb.lookup v = some aM →
          List.lookup v fr.assignments = some aF →
          aM = aF := by
      intro v aM aF hmbLook hfrLook
      have hcLook : c.lookup v = some aM := hmbExt v aM hmbLook
      exact mergeGround_overlap_agree hfrCanon.1.2 hfrCanon.2 hx hcLook
        (by simpa [Bindings.lookup] using hfrLook)
    simpa [mergeGround?, hfrCanon.1.2, g, restAssigns] using
      (mergeGroundAssignments_eq_append_fresh_of_overlap_agree
        (left := mb) (assigns := fr.assignments)
        hmbCanon.1.2 hfrCanon.2 hag)
  have hcmem :
      c ∈ mergeBindings b mb 2 :=
    (mem_mergeBindings_ground_iff
      (left := b) (right := mb) (result := c) (fuel := 0) hb hmbCanon.1).mpr hc
  have hcg : GroundBindings c := by
    have hmatchers := matcher_ground 2
    rcases hmatchers with ⟨_hA, _hL, hM, _hB⟩
    exact hM b mb c hb hmbCanon.1 hcmem
  have hrestMerge :
      mergeGround? c rest = some x := by
    have hrest :
        mergeGround? c rest =
          some
            { assignments := c.assignments ++
                restAssigns.filter (fun p => (c.lookup p.1).isNone)
            , equalities := [] } := by
      have hag :
          ∀ {v aL aR},
            c.lookup v = some aL →
            List.lookup v restAssigns = some aR →
            aL = aR := by
        intro v aL aR hcLook hrestLook
        have hfrLook : List.lookup v fr.assignments = some aR :=
          lookup_filter_some_of_nodup hfrCanon.2 hrestLook
        exact mergeGround_overlap_agree hfrCanon.1.2 hfrCanon.2 hx hcLook
          (by simpa [Bindings.lookup] using hfrLook)
      simpa [mergeGround?, rest, restAssigns] using
        (mergeGroundAssignments_eq_append_fresh_of_overlap_agree
          (left := c) (assigns := restAssigns)
          hcg.2 (keys_nodup_filter hfrCanon.2) hag)
    have hx' :
        x =
          { assignments := c.assignments ++
              fr.assignments.filter (fun p => (c.lookup p.1).isNone)
          , equalities := [] } := by
      have hfull :
          mergeGround? c fr =
            some
              { assignments := c.assignments ++
                  fr.assignments.filter (fun p => (c.lookup p.1).isNone)
              , equalities := [] } := by
        have hag :
            ∀ {v aL aR},
              c.lookup v = some aL →
              List.lookup v fr.assignments = some aR →
              aL = aR := by
          intro v aL aR hcLook hfrLook
          exact mergeGround_overlap_agree hfrCanon.1.2 hfrCanon.2 hx hcLook
            (by simpa [Bindings.lookup] using hfrLook)
        simpa [mergeGround?, hfrCanon.1.2] using
          (mergeGroundAssignments_eq_append_fresh_of_overlap_agree
            (left := c) (assigns := fr.assignments)
            hcg.2 hfrCanon.2 hag)
      have : some x =
          some
            { assignments := c.assignments ++
                fr.assignments.filter (fun p => (c.lookup p.1).isNone)
            , equalities := [] } := by
        rw [← hx, hfull]
      injection this
    have hfilter :
        restAssigns.filter (fun p => (c.lookup p.1).isNone) =
          fr.assignments.filter (fun p => (c.lookup p.1).isNone) := by
      simpa [restAssigns] using
        (filter_lookup_none_of_extends
          (xs := fr.assignments) (base := mb) (ext := c) hmbExt)
    rw [hrest, hx', hfilter]
  refine ⟨g, hmid, ?_⟩
  have hconcat := mergeGround_concat b mb rest hmbCanon.1.2 rfl
  simpa [g, rest, restAssigns, hc, hrestMerge] using hconcat

/-- Transport a singleton-seeded official list run across an already-factored
ground seed: if `seed` is obtained by merging canonical `delta` into `base`,
then any official run from `[seed]` factors through a run from `[delta]`,
possibly at a larger fuel, with the same final merge into `base`. -/
private theorem matchAtomsList_seed_transport_ground : ∀ fuel : Nat,
    ∀ {lefts rights base delta seed x},
      (∀ t ∈ lefts, GroundAtom t) →
      GroundBindings base →
      GroundBindingsCanon delta →
      seed ∈ mergeBindings base delta 2 →
      x ∈ matchAtomsList lefts rights [seed] fuel →
        ∃ fuel', ∃ fr,
          fr ∈ matchAtomsList lefts rights [delta] fuel' ∧
          x ∈ mergeBindings base fr 2 := by
  intro fuel
  induction fuel with
  | zero =>
      intro lefts rights base delta seed x hlefts hbase hdelta hseed hmem
      simp [matchAtomsList] at hmem
  | succ n ih =>
      intro lefts rights base delta seed x hlefts hbase hdelta hseed hmem
      have hseedGround : GroundBindings seed := by
        have hmatchers := matcher_ground 2
        rcases hmatchers with ⟨_hA, _hL, hM, _hB⟩
        exact hM base delta seed hbase hdelta.1 hseed
      cases lefts with
      | nil =>
          cases rights with
          | nil =>
              simp [matchAtomsList] at hmem
              subst hmem
              refine ⟨1, delta, ?_, hseed⟩
              simp [matchAtomsList]
          | cons r rs =>
              simp [matchAtomsList] at hmem
      | cons t ts =>
          cases rights with
          | nil =>
              simp [matchAtomsList] at hmem
          | cons p ps =>
              have ht : GroundAtom t := hlefts t (by simp)
              have htsGround : ∀ a ∈ ts, GroundAtom a := by
                intro a ha
                exact hlefts a (by simp [ha])
              have htailAcc :
                  x ∈ matchAtomsList ts ps
                    ((matchAtoms t p n).flatMap fun mb => mergeBindings seed mb n) n := by
                simpa [matchAtomsList] using hmem
              obtain ⟨c, hcAcc, htail⟩ :=
                (mem_matchAtomsList_seedwise
                  (lefts := ts) (rights := ps)
                  (seeds := (matchAtoms t p n).flatMap fun mb => mergeBindings seed mb n)
                  (fuel := n) (x := x)).mp htailAcc
              obtain ⟨mb, hmb, hcSeed2⟩ :=
                matchAtoms_ground_seed_factor ht hseedGround hcAcc
              have hmbCanon : GroundBindingsCanon mb := matchAtoms_ground_canon ht hmb
              have hseedEq :
                  mergeGround? base delta = some seed :=
                (mem_mergeBindings_ground_iff
                  (left := base) (right := delta) (result := seed)
                  (fuel := 0) hbase hdelta.1).mp hseed
              have hcSeedEq :
                  mergeGround? seed mb = some c :=
                (mem_mergeBindings_ground_iff
                  (left := seed) (right := mb) (result := c)
                  (fuel := 0) hseedGround hmbCanon.1).mp hcSeed2
              obtain ⟨g, hgEq, hcBaseEq⟩ :=
                mergeGround_seed_compose hbase hdelta hmbCanon hseedEq hcSeedEq
              have hgMem2 :
                  g ∈ mergeBindings delta mb 2 :=
                (mem_mergeBindings_ground_iff
                  (left := delta) (right := mb) (result := g)
                  (fuel := 0) hdelta.1 hmbCanon.1).mpr hgEq
              have hgCanon : GroundBindingsCanon g :=
                mergeBindings_canon hdelta hmbCanon hgMem2
              have hcBaseMem :
                  c ∈ mergeBindings base g 2 :=
                (mem_mergeBindings_ground_iff
                  (left := base) (right := g) (result := c)
                  (fuel := 0) hbase hgCanon.1).mpr hcBaseEq
              obtain ⟨fuelTail, fr, hfr, hmergeFinal⟩ :=
                ih (lefts := ts) (rights := ps)
                  (base := base) (delta := g) (seed := c) (x := x)
                  htsGround hbase hgCanon hcBaseMem htail
              let fuelHead := max n 2
              have hmb' : mb ∈ matchAtoms t p fuelHead := by
                have hEq : n + (fuelHead - n) = fuelHead := by
                  dsimp [fuelHead]
                  exact Nat.add_sub_of_le (Nat.le_max_left _ _)
                simpa [hEq, fuelHead] using
                  (matchAtoms_mono_add t p n (fuelHead - n)) mb hmb
              have hgMemHead : g ∈ mergeBindings delta mb fuelHead := by
                have hEq : 2 + (fuelHead - 2) = fuelHead := by
                  dsimp [fuelHead]
                  exact Nat.add_sub_of_le (Nat.le_max_right _ _)
                simpa [hEq, fuelHead] using
                  (mergeBindings_mono_add delta mb 2 (fuelHead - 2)) g hgMem2
              have hhead :
                  g ∈ (matchAtoms t p fuelHead).flatMap
                    (fun mb0 => mergeBindings delta mb0 fuelHead) :=
                List.mem_flatMap.mpr ⟨mb, hmb', hgMemHead⟩
              obtain ⟨fuelWhole, hwhole⟩ := matchAtomsList_cons_of_head_tail hhead hfr
              exact ⟨fuelWhole + 1, fr, by simpa using hwhole, hmergeFinal⟩

/-- Reverse seeded-composition on the ground fragment: if a canonical ground
head fragment `mb` merges with a canonical ground tail fragment `frTail` to
produce `fr`, and `fr` in turn merges into a ground seed `seed` to produce
`x`, then there is an intermediate seeded head result `c = seed ⋆ mb` such
that the tail fragment still merges from `c` to exactly the same final `x`.

This is the converse algebraic direction to `mergeGround_seed_compose`, and it
is the missing merge fact needed to rebuild seeded official list runs from an
empty-seeded official factor plus a final seed merge. -/
private theorem mergeGround_seed_decompose
    {seed mb frTail fr x : Bindings}
    (hseed : GroundBindings seed)
    (hmbCanon : GroundBindingsCanon mb)
    (hfrTailCanon : GroundBindingsCanon frTail)
    (hmid : mergeGround? mb frTail = some fr)
    (hx : mergeGround? seed fr = some x) :
    ∃ c,
      mergeGround? seed mb = some c ∧
      mergeGround? c frTail = some x := by
  have hfrMem :
      fr ∈ mergeBindings mb frTail 2 :=
    (mem_mergeBindings_ground_iff
      (left := mb) (right := frTail) (result := fr) (fuel := 0)
      hmbCanon.1 hfrTailCanon.1).mpr hmid
  have hfrCanon : GroundBindingsCanon fr :=
    mergeBindings_canon hmbCanon hfrTailCanon hfrMem
  have hmbExtFr : mb.Extends fr :=
    mergeGround_extends_left_of_nodup hfrTailCanon.1.2 hfrTailCanon.2 hmid
  have hagSeedMb :
      ∀ {v aS aM},
        seed.lookup v = some aS →
        mb.lookup v = some aM →
        aS = aM := by
    intro v aS aM hseedLook hmbLook
    have hfrLook : fr.lookup v = some aM := hmbExtFr v aM hmbLook
    exact mergeGround_overlap_agree hfrCanon.1.2 hfrCanon.2 hx hseedLook hfrLook
  obtain ⟨c, hc⟩ :=
    mergeGround_exists_of_overlap_agree hmbCanon.1.2 hmbCanon.2 hagSeedMb
  have hseedExtC : seed.Extends c :=
    mergeGround_extends_left_of_nodup hmbCanon.1.2 hmbCanon.2 hc
  have hmbExtC : mb.Extends c :=
    mergeGround_extends_right_of_nodup hmbCanon.1.2 hmbCanon.2 hc
  have hfrTailExtFr : frTail.Extends fr :=
    mergeGround_extends_right_of_nodup hfrTailCanon.1.2 hfrTailCanon.2 hmid
  have hagCTail :
      ∀ {v aC aF},
        c.lookup v = some aC →
        frTail.lookup v = some aF →
        aC = aF := by
    intro v aC aF hcLook htailLook
    have hfrLook : fr.lookup v = some aF := hfrTailExtFr v aF htailLook
    by_cases hmbv : ∃ aM, mb.lookup v = some aM
    · rcases hmbv with ⟨aM, hmbLook⟩
      have hcSpec :=
        mergeGround_lookup_spec
          (left := seed) (right := mb) (out := c)
          hmbCanon.1.2 hmbCanon.2 hc v
      rw [hmbLook] at hcSpec
      have haCM : aC = aM := by
        simpa [hcLook] using hcSpec
      have haMF : aM = aF :=
        mergeGround_overlap_agree hfrTailCanon.1.2 hfrTailCanon.2 hmid hmbLook htailLook
      exact haCM.trans haMF
    · have hmbNone : mb.lookup v = none := by
        cases hlook : mb.lookup v with
        | none =>
            rfl
        | some aM =>
            exfalso
            exact hmbv ⟨aM, hlook⟩
      have hcSpec :=
        mergeGround_lookup_spec
          (left := seed) (right := mb) (out := c)
          hmbCanon.1.2 hmbCanon.2 hc v
      rw [hmbNone] at hcSpec
      have hseedLook : seed.lookup v = some aC := by
        simpa [hcLook] using hcSpec.symm
      exact mergeGround_overlap_agree hfrCanon.1.2 hfrCanon.2 hx hseedLook hfrLook
  obtain ⟨x', hx'⟩ :=
    mergeGround_exists_of_overlap_agree hfrTailCanon.1.2 hfrTailCanon.2 hagCTail
  obtain ⟨g, hg, hseedg⟩ :=
    mergeGround_seed_compose hseed hmbCanon hfrTailCanon hc hx'
  have hsameFr : g = fr := by
    rw [hmid] at hg
    injection hg with hEq
    exact hEq.symm
  rw [hsameFr] at hseedg
  rw [hx] at hseedg
  injection hseedg with hEq
  exact ⟨c, hc, hEq ▸ hx'⟩

/-- Converse seed transport on the ground fragment: if an official empty-seeded
list run produces `fr`, and merging `fr` into a ground seed `base` yields
`x`, then there is also a seeded official list run from `[base]` that yields
the same final `x` (possibly at a larger fuel).

This is the reverse direction to `matchAtomsList_seed_transport_ground`, and
is the key algebraic bridge from empty-seeded official matches to seeded
official matches. -/
theorem matchAtomsList_empty_factor_to_seeded_ground : ∀ fuel : Nat,
    ∀ {lefts rights base fr x},
      (∀ t ∈ lefts, GroundAtom t) →
      GroundBindings base →
      fr ∈ matchAtomsList lefts rights [Bindings.empty] fuel →
      x ∈ mergeBindings base fr 2 →
        ∃ fuel', x ∈ matchAtomsList lefts rights [base] fuel' := by
  intro fuel lefts
  induction lefts generalizing fuel with
  | nil =>
      intro rights base fr x hlefts hbase hfr hx
      cases rights with
      | nil =>
          cases fuel with
          | zero =>
              simp [matchAtomsList] at hfr
          | succ n =>
              have hfrEq : fr = Bindings.empty := by
                simpa [matchAtomsList] using hfr
              subst hfrEq
              have hxDet : mergeGround? base Bindings.empty = some x := by
                exact
                  (mem_mergeBindings_ground_iff
                    (left := base) (right := Bindings.empty) (result := x)
                    (fuel := 0) hbase GroundBindings.empty).mp hx
              have hxEq : x = base := by
                simp [mergeGround?] at hxDet
                injection hxDet with hEq
                exact hEq.symm
              subst hxEq
              refine ⟨1, ?_⟩
              simp [matchAtomsList]
      | cons r rs =>
          cases fuel <;> simp [matchAtomsList] at hfr
  | cons t ts ih =>
      intro rights base fr x hlefts hbase hfr hx
      cases rights with
      | nil =>
          cases fuel <;> simp [matchAtomsList] at hfr
      | cons p ps =>
          cases fuel with
          | zero =>
              simp [matchAtomsList] at hfr
          | succ n =>
              have ht : GroundAtom t := hlefts t (by simp)
              have htsGround : ∀ u ∈ ts, GroundAtom u := by
                intro u hu
                exact hlefts u (by simp [hu])
              obtain ⟨mbHead, hhead, htail⟩ :=
                matchAtomsList_ground_empty_cons_inv
                  (t := t) (p := p) (ts := ts) (ps := ps)
                  (result := fr) (fuel := n) ht hfr
              have hmbCanon : GroundBindingsCanon mbHead :=
                matchAtoms_ground_canon ht hhead
              have hseedHead :
                  mbHead ∈ mergeBindings mbHead Bindings.empty 2 := by
                rw [mergeBindings_empty_right mbHead 1]
                simp
              obtain ⟨fuelTail, frTail, hfrTail, hfrMerge⟩ :=
                matchAtomsList_seed_transport_ground n
                  (lefts := ts) (rights := ps)
                  (base := mbHead) (delta := Bindings.empty)
                  (seed := mbHead) (x := fr)
                  htsGround hmbCanon.1 GroundBindingsCanon.empty
                  hseedHead htail
              have hfrTailCanon : GroundBindingsCanon frTail :=
                matchAtomsList_ground_empty_canon htsGround hfrTail
              have hfrCanon : GroundBindingsCanon fr :=
                matchAtomsList_ground_empty_canon hlefts hfr
              have hfrMergeEq : mergeGround? mbHead frTail = some fr := by
                exact
                  (mem_mergeBindings_ground_iff
                    (left := mbHead) (right := frTail) (result := fr)
                    (fuel := 0) hmbCanon.1 hfrTailCanon.1).mp hfrMerge
              have hxEq : mergeGround? base fr = some x := by
                exact
                  (mem_mergeBindings_ground_iff
                    (left := base) (right := fr) (result := x)
                    (fuel := 0) hbase hfrCanon.1).mp hx
              obtain ⟨c, hcEq, hxTailEq⟩ :=
                mergeGround_seed_decompose hbase hmbCanon hfrTailCanon hfrMergeEq hxEq
              have hcMem :
                  c ∈ mergeBindings base mbHead 2 :=
                (mem_mergeBindings_ground_iff
                  (left := base) (right := mbHead) (result := c)
                  (fuel := 0) hbase hmbCanon.1).mpr hcEq
              have hcGround : GroundBindings c := by
                have hmatchers := matcher_ground 2
                rcases hmatchers with ⟨_hA, _hL, hM, _hB⟩
                exact hM base mbHead c hbase hmbCanon.1 hcMem
              have hxTailMem :
                  x ∈ mergeBindings c frTail 2 :=
                (mem_mergeBindings_ground_iff
                  (left := c) (right := frTail) (result := x)
                  (fuel := 0) hcGround hfrTailCanon.1).mpr hxTailEq
              obtain ⟨fuelTail', htailSeeded⟩ :=
                ih (fuel := fuelTail) (rights := ps)
                  (base := c) (fr := frTail) (x := x) htsGround
                  hcGround hfrTail hxTailMem
              let fuelHead := max n 2
              have hHeadLe : n ≤ fuelHead := by
                dsimp [fuelHead]
                exact Nat.le_max_left _ _
              have hhead' : mbHead ∈ matchAtoms t p fuelHead := by
                have hEq : n + (fuelHead - n) = fuelHead :=
                  Nat.add_sub_of_le hHeadLe
                simpa [hEq] using
                  (matchAtoms_mono_add t p n (fuelHead - n)) mbHead hhead
              have hcMem' : c ∈ mergeBindings base mbHead fuelHead := by
                have hEq : 2 + (fuelHead - 2) = fuelHead := by
                  dsimp [fuelHead]
                  exact Nat.add_sub_of_le (Nat.le_max_right _ _)
                simpa [hEq] using
                  (mergeBindings_mono_add base mbHead 2 (fuelHead - 2)) c hcMem
              have hheadSeeded :
                  c ∈ (matchAtoms t p fuelHead).flatMap
                    (fun mb => mergeBindings base mb fuelHead) :=
                List.mem_flatMap.mpr ⟨mbHead, hhead', hcMem'⟩
              obtain ⟨fuelWhole, hwhole⟩ :=
                matchAtomsList_cons_of_head_tail hheadSeeded htailSeeded
              exact ⟨fuelWhole + 1, hwhole⟩

/-- Singleton-seed factorization on the ground fragment: any official list run
from `[b]` factors through an empty-seeded run at some (possibly larger) fuel,
with the same final merge back into `b` at fuel 2. -/
private theorem matchAtomsList_singleton_factor_ground
    {lefts rights : List Atom} {b x : Bindings} {fuel : Nat}
    (hlefts : ∀ t ∈ lefts, GroundAtom t)
    (hb : GroundBindings b)
    (hmem : x ∈ matchAtomsList lefts rights [b] fuel) :
    ∃ fuel', ∃ fr,
      fr ∈ matchAtomsList lefts rights [Bindings.empty] fuel' ∧
      x ∈ mergeBindings b fr 2 := by
  have hseed : b ∈ mergeBindings b Bindings.empty 2 := by
    rw [mergeBindings_empty_right b 1]
    simp
  simpa using
    (matchAtomsList_seed_transport_ground fuel
      (lefts := lefts) (rights := rights)
      (base := b) (delta := Bindings.empty) (seed := b) (x := x)
      hlefts hb GroundBindingsCanon.empty hseed hmem)

/-- Ground-seeded list bridge: if each successful element match from a ground
seed has an official witness, then successful `simpleMatchList` threading from
a ground seed also has an official seeded list witness, and recursive seeds stay
ground by `matcher_ground`. -/
private theorem simpleMatchList_ground_seeded_of_elem_bridge_ground
    (fuel : Nat)
    (hElem :
      ∀ {p t b qb},
        GroundBindings b →
        GroundAtom t →
        simpleMatch p t b fuel = some qb →
          ∃ fuel',
            qb ∈ (matchAtoms t p fuel').flatMap (fun mb => mergeBindings b mb fuel')) :
    ∀ {ps ts b qb},
      GroundBindings b →
      (∀ t ∈ ts, GroundAtom t) →
      simpleMatch.simpleMatchList ps ts b fuel = some qb →
        ∃ fuel', qb ∈ matchAtomsList ts ps [b] fuel' := by
  intro ps
  induction ps with
  | nil =>
      intro ts b qb hb hground hmatch
      cases ts with
      | nil =>
          simp [simpleMatch.simpleMatchList] at hmatch
          subst hmatch
          refine ⟨1, ?_⟩
          simp [matchAtomsList]
      | cons t ts =>
          simp [simpleMatch.simpleMatchList] at hmatch
  | cons p ps ih =>
      intro ts b qb hb hground hmatch
      cases ts with
      | nil =>
          simp [simpleMatch.simpleMatchList] at hmatch
      | cons t ts =>
          unfold simpleMatch.simpleMatchList at hmatch
          cases hhd : simpleMatch p t b fuel with
          | none =>
              simp [hhd] at hmatch
          | some b' =>
              simp [hhd] at hmatch
              have ht : GroundAtom t := hground t (by simp)
              obtain ⟨fuelHead, hhead⟩ := hElem hb ht hhd
              have hb' : GroundBindings b' := by
                rcases List.mem_flatMap.mp hhead with ⟨mb, hmb, hmerge⟩
                have hmatchers := matcher_ground fuelHead
                rcases hmatchers with ⟨hA, _hL, hM, _hB⟩
                have hmbGround : GroundBindings mb := hA t p mb ht hmb
                exact hM b mb b' hb hmbGround hmerge
              obtain ⟨fuelTail, htail⟩ := ih hb'
                (fun a ha => hground a (by simp [ha])) hmatch
              obtain ⟨fuel', hwhole⟩ := matchAtomsList_cons_of_head_tail hhead htail
              exact ⟨fuel' + 1, hwhole⟩

/-- Bridge helper: a successful one-way variable match against a ground target
is witnessed by the official matcher plus a merge of the produced singleton
binding into the seed. -/
theorem simpleMatch_ground_var_bridge
    {target : Atom} {b qb : Bindings} {v : String} {fuel : Nat}
    (hb : GroundBindings b)
    (hground : GroundAtom target)
    (hmatch : simpleMatch (.var v) target b fuel = some qb) :
    ∃ fuel',
      Bindings.empty.assign v target ∈ matchAtoms target (.var v) fuel' ∧
      qb ∈ mergeBindings b (Bindings.empty.assign v target) fuel' := by
  cases fuel with
  | zero =>
      simp [simpleMatch] at hmatch
  | succ n =>
      cases hlook : b.lookup v with
      | none =>
          simp [simpleMatch, hlook] at hmatch
          rcases hmatch with rfl
          refine ⟨2, ?_, ?_⟩
          · rw [matchAtoms_ground_var_exact target v 1 hground]
            simp
          · rw [mergeBindings_single_assign_fresh hlook hb.2 0]
            simp
      | some prev =>
          simp only [simpleMatch, hlook] at hmatch
          split at hmatch <;> rename_i heq
          · simp at hmatch
            rcases hmatch with rfl
            have hprev : prev = target := by simpa using heq
            refine ⟨2, ?_, ?_⟩
            · rw [matchAtoms_ground_var_exact target v 1 hground]
              simp
            · rw [mergeBindings_single_assign_same (hprev.symm ▸ hlook) hb.2 0]
              simp
          · simp at hmatch

/-- Bridge helper: a successful symbol-pattern match against a ground target
is witnessed by the official matcher's empty binding result. -/
theorem simpleMatch_ground_symbol_bridge
    {target : Atom} {b qb : Bindings} {s : String} {fuel : Nat}
    (hground : GroundAtom target)
    (hmatch : simpleMatch (.symbol s) target b fuel = some qb) :
    ∃ fuel',
      Bindings.empty ∈ matchAtoms target (.symbol s) fuel' ∧
      qb ∈ mergeBindings b Bindings.empty fuel' := by
  cases fuel with
  | zero =>
      simp [simpleMatch] at hmatch
  | succ n =>
      cases target with
      | var v =>
          exact (GroundAtom.not_var hground).elim
      | symbol t =>
          simp [simpleMatch] at hmatch
          rcases hmatch with ⟨hst, rfl⟩
          refine ⟨1, ?_, ?_⟩
          · subst hst
            simp [matchAtoms, getMetaType, Atom.symbolType, Bindings.hasLoop_empty]
          · rw [mergeBindings_empty_right b 0]
            simp
      | grounded g =>
          simp [simpleMatch] at hmatch
      | expression es =>
          simp [simpleMatch] at hmatch

/-- Bridge helper: a successful grounded-value pattern match against a ground
target is witnessed by the official matcher's empty binding result. -/
theorem simpleMatch_ground_grounded_bridge
    {target : Atom} {b qb : Bindings} {g : GroundedValue} {fuel : Nat}
    (hground : GroundAtom target)
    (hmatch : simpleMatch (.grounded g) target b fuel = some qb) :
    ∃ fuel',
      Bindings.empty ∈ matchAtoms target (.grounded g) fuel' ∧
      qb ∈ mergeBindings b Bindings.empty fuel' := by
  cases fuel with
  | zero =>
      simp [simpleMatch] at hmatch
  | succ n =>
      cases target with
      | var v =>
          exact (GroundAtom.not_var hground).elim
      | symbol s =>
          simp [simpleMatch] at hmatch
      | grounded h =>
          simp [simpleMatch] at hmatch
          rcases hmatch with ⟨hgh, rfl⟩
          refine ⟨1, ?_, ?_⟩
          · subst hgh
            simp [matchAtoms, getMetaType, Atom.groundedType, Bindings.hasLoop_empty]
          · rw [mergeBindings_empty_right b 0]
            simp
      | expression es =>
          simp [simpleMatch] at hmatch

/-- `simpleMatch` and `simpleMatchList` are monotone in fuel on successful
runs: once a match succeeds, one extra unit of fuel preserves the same
result.  This is the fuel-skew shim the failure bridge needs, because the
official `matchAtomsList` recursion spends one unit of fuel differently from
the coarse threaded matcher. -/
private theorem simpleMatch_mono_succ (fuel : Nat) :
    (∀ pattern target b qb,
      simpleMatch pattern target b fuel = some qb →
      simpleMatch pattern target b (fuel + 1) = some qb) ∧
    (∀ ps ts b qb,
      simpleMatch.simpleMatchList ps ts b fuel = some qb →
      simpleMatch.simpleMatchList ps ts b (fuel + 1) = some qb) := by
  induction fuel with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro pattern target b qb h
        simp [simpleMatch] at h
      · intro ps ts b qb h
        cases ps <;> cases ts <;>
          simp [simpleMatch.simpleMatchList, simpleMatch] at h ⊢
        · simpa [simpleMatch.simpleMatchList] using h
  | succ n ih =>
      obtain ⟨ihAtom, ihList⟩ := ih
      have hAtomSucc :
          ∀ pattern target b qb,
            simpleMatch pattern target b (n + 1) = some qb →
            simpleMatch pattern target b (n + 2) = some qb := by
        intro pattern target b qb h
        cases pattern with
        | var v =>
            cases hlook : b.lookup v <;>
              simpa [simpleMatch, hlook] using h
        | symbol s =>
            cases target with
            | var v =>
                simp [simpleMatch] at h
            | symbol t =>
                simp [simpleMatch] at h ⊢
                exact h
            | grounded g =>
                simp [simpleMatch] at h
            | expression es =>
                simp [simpleMatch] at h
        | grounded g =>
            cases target with
            | var v =>
                simp [simpleMatch] at h
            | symbol s =>
                simp [simpleMatch] at h
            | grounded h' =>
                simp [simpleMatch] at h ⊢
                exact h
            | expression es =>
                simp [simpleMatch] at h
        | expression ps =>
            cases target with
            | var v =>
                simp [simpleMatch] at h
            | symbol s =>
                simp [simpleMatch] at h
            | grounded g =>
                simp [simpleMatch] at h
            | expression ts =>
                cases hneq : (ps.length != ts.length) with
                | true =>
                    simp [simpleMatch, hneq] at h
                | false =>
                    simp [simpleMatch, hneq] at h ⊢
                    exact ihList ps ts b qb h
      have hListSucc :
          ∀ ps ts b qb,
            simpleMatch.simpleMatchList ps ts b (n + 1) = some qb →
            simpleMatch.simpleMatchList ps ts b (n + 2) = some qb := by
        intro ps
        induction ps with
        | nil =>
            intro ts b qb h
            cases ts <;> simp [simpleMatch.simpleMatchList] at h ⊢
            · simpa [simpleMatch.simpleMatchList] using h
        | cons p ps ihps =>
            intro ts b qb h
            cases ts with
            | nil =>
                simp [simpleMatch.simpleMatchList] at h
            | cons t ts =>
                unfold simpleMatch.simpleMatchList at h ⊢
                cases hhd : simpleMatch p t b (n + 1) with
                | none =>
                    simp [hhd] at h
                | some b' =>
                    simp [hhd] at h
                    have hhd' : simpleMatch p t b (n + 2) = some b' :=
                      hAtomSucc p t b b' hhd
                    have htail' : simpleMatch.simpleMatchList ps ts b' (n + 2) = some qb :=
                      ihps ts b' qb h
                    simp [hhd', htail']
      exact ⟨hAtomSucc, hListSucc⟩

/-- Contrapositive of `simpleMatch_mono_succ`: if a match fails at fuel
`n+1`, it already failed at fuel `n`.  This is the downward fuel step used to
line up coarse list failures with the official list matcher's inner fuel. -/
private theorem simpleMatch_none_pred (fuel : Nat) :
    (∀ pattern target b,
      simpleMatch pattern target b (fuel + 1) = none →
      simpleMatch pattern target b fuel = none) ∧
    (∀ ps ts b,
      simpleMatch.simpleMatchList ps ts b (fuel + 1) = none →
      simpleMatch.simpleMatchList ps ts b fuel = none) := by
  obtain ⟨hAtomSucc, hListSucc⟩ := simpleMatch_mono_succ fuel
  refine ⟨?_, ?_⟩
  · intro pattern target b hnone
    cases hprev : simpleMatch pattern target b fuel with
    | none =>
        rfl
    | some qb =>
        have hsucc : simpleMatch pattern target b (fuel + 1) = some qb :=
          hAtomSucc pattern target b qb hprev
        rw [hsucc] at hnone
        exact hnone
  · intro ps ts b hnone
    cases hprev : simpleMatch.simpleMatchList ps ts b fuel with
    | none =>
        rfl
    | some qb =>
        have hsucc : simpleMatch.simpleMatchList ps ts b (fuel + 1) = some qb :=
          hListSucc ps ts b qb hprev
        rw [hsucc] at hnone
        exact hnone

/-- Failure leaf: on a ground target, a conflicting seeded variable match has
no official seeded witness at the same fuel. -/
private theorem simpleMatch_ground_var_no_match
    {target : Atom} {b : Bindings} {v : String} {fuel : Nat}
    (hb : GroundBindings b)
    (hground : GroundAtom target)
    (hmatch : simpleMatch (.var v) target b fuel = none) :
    (matchAtoms target (.var v) fuel).flatMap
      (fun mb => mergeBindings b mb fuel) = [] := by
  cases fuel with
  | zero =>
      simp [matchAtoms]
  | succ n =>
      cases hlook : b.lookup v with
      | none =>
          simp [simpleMatch, hlook] at hmatch
      | some prev =>
          simp only [simpleMatch, hlook] at hmatch
          split at hmatch <;> rename_i hsame
          · simp at hmatch
          · have hprev : GroundAtom prev := lookup_ground hb hlook
            have hneq : prev ≠ target := by
              intro heq
              exact hsame (by simp [heq])
            cases n with
            | zero =>
                rw [matchAtoms_ground_var_exact target v 0 hground]
                simp [mergeBindings, addVarBinding, Bindings.empty, Bindings.assign,
                  Bindings.isBound, Bindings.lookup]
            | succ k =>
                rw [matchAtoms_ground_var_exact target v (k + 1) hground]
                have hmerge :
                    mergeBindings b (Bindings.empty.assign v target) (k + 2) = [] := by
                  rw [mergeBindings_single_assign (b := b) (v := v) (val := target) k]
                  cases k with
                  | zero =>
                      rw [addVarBinding_no_equalities hb.2 0]
                      simp [hlook, hsame, matchAtoms]
                  | succ m =>
                      have hmatchNil : matchAtoms prev target (m + 1) = [] :=
                        matchAtoms_ground_ne_nil hprev hground hneq
                      rw [addVarBinding_no_equalities hb.2 (m + 1)]
                      simp [hlook, hsame, hmatchNil]
                simpa using hmerge

/-- Failure leaf: on a ground target, a symbol-pattern mismatch has no
official seeded witness at the same fuel. -/
private theorem simpleMatch_ground_symbol_no_match
    {target : Atom} {b : Bindings} {s : String} {fuel : Nat}
    (hground : GroundAtom target)
    (hmatch : simpleMatch (.symbol s) target b fuel = none) :
    (matchAtoms target (.symbol s) fuel).flatMap
      (fun mb => mergeBindings b mb fuel) = [] := by
  cases fuel with
  | zero =>
      simp [matchAtoms]
  | succ n =>
      cases target with
      | var v =>
          exact (GroundAtom.not_var hground).elim
      | symbol t =>
          simp [simpleMatch] at hmatch
          have hst : s ≠ t := by simpa using hmatch
          by_cases hts : t = s
          · exact False.elim (hst hts.symm)
          · simp [matchAtoms, getMetaType, Atom.symbolType, hts]
      | grounded g =>
          simp [matchAtoms, getMetaType, Atom.groundedType, Atom.symbolType]
      | expression es =>
          simp [matchAtoms, getMetaType, Atom.expressionType, Atom.symbolType]

/-- Failure leaf: on a ground target, a grounded-pattern mismatch has no
official seeded witness at the same fuel. -/
private theorem simpleMatch_ground_grounded_no_match
    {target : Atom} {b : Bindings} {g : GroundedValue} {fuel : Nat}
    (hground : GroundAtom target)
    (hmatch : simpleMatch (.grounded g) target b fuel = none) :
    (matchAtoms target (.grounded g) fuel).flatMap
      (fun mb => mergeBindings b mb fuel) = [] := by
  cases fuel with
  | zero =>
      simp [matchAtoms]
  | succ n =>
      cases target with
      | var v =>
          exact (GroundAtom.not_var hground).elim
      | symbol s =>
          simp [matchAtoms, getMetaType, Atom.symbolType, Atom.groundedType]
      | grounded h =>
          simp [simpleMatch] at hmatch
          have hgh : g ≠ h := by simpa using hmatch
          by_cases hhg : h = g
          · exact False.elim (hgh hhg.symm)
          · simp [matchAtoms, getMetaType, Atom.groundedType, hhg]
      | expression es =>
          simp [matchAtoms, getMetaType, Atom.expressionType, Atom.groundedType]

/-- If the seeded official list matcher on ground scrutinees factors through
the empty-seeded run plus a final seed merge, then the full ground
`simpleMatch`/`matchAtoms` bridge follows by fuel induction. This isolates the
remaining hard part to the singleton-seed factorization theorem. -/
private theorem simpleMatch_ground_official_of_factor
    (hFactor :
      ∀ {lefts rights b x fuelList},
        (∀ t ∈ lefts, GroundAtom t) →
        GroundBindings b →
        x ∈ matchAtomsList lefts rights [b] fuelList →
          ∃ fuel', ∃ fr,
            fr ∈ matchAtomsList lefts rights [Bindings.empty] fuel' ∧
            x ∈ mergeBindings b fr 2) :
    ∀ fuel : Nat,
      (∀ p t b qb,
        GroundBindings b →
        GroundAtom t →
        simpleMatch p t b fuel = some qb →
          ∃ fuel',
            qb ∈ (matchAtoms t p fuel').flatMap (fun mb => mergeBindings b mb fuel')) ∧
      (∀ ps ts b qb,
        GroundBindings b →
        (∀ t ∈ ts, GroundAtom t) →
        simpleMatch.simpleMatchList ps ts b fuel = some qb →
          ∃ fuel', qb ∈ matchAtomsList ts ps [b] fuel') := by
  intro fuel
  induction fuel with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro p t b qb hb hground hmatch
        simp [simpleMatch] at hmatch
      · intro ps ts b qb hb hground hmatch
        cases ps with
        | nil =>
            cases ts with
            | nil =>
                simp [simpleMatch.simpleMatchList] at hmatch
                subst hmatch
                refine ⟨1, ?_⟩
                simp [matchAtomsList]
            | cons t ts =>
                simp [simpleMatch.simpleMatchList] at hmatch
        | cons p ps =>
            cases ts with
            | nil =>
                simp [simpleMatch.simpleMatchList] at hmatch
            | cons t ts =>
                simp [simpleMatch.simpleMatchList, simpleMatch] at hmatch
  | succ n ih =>
      obtain ⟨ihElem, ihList⟩ := ih
      have hElemSucc :
          ∀ p t b qb,
            GroundBindings b →
            GroundAtom t →
            simpleMatch p t b (n + 1) = some qb →
              ∃ fuel',
                qb ∈ (matchAtoms t p fuel').flatMap (fun mb => mergeBindings b mb fuel') := by
        intro p t b qb hb hground hmatch
        cases p with
        | var v =>
            obtain ⟨fuel', hmb, hmerge⟩ := simpleMatch_ground_var_bridge hb hground hmatch
            refine ⟨fuel', ?_⟩
            exact List.mem_flatMap.mpr ⟨Bindings.empty.assign v t, hmb, hmerge⟩
        | symbol s =>
            obtain ⟨fuel', hmb, hmerge⟩ := simpleMatch_ground_symbol_bridge hground hmatch
            refine ⟨fuel', ?_⟩
            exact List.mem_flatMap.mpr ⟨Bindings.empty, hmb, hmerge⟩
        | grounded g =>
            obtain ⟨fuel', hmb, hmerge⟩ := simpleMatch_ground_grounded_bridge hground hmatch
            refine ⟨fuel', ?_⟩
            exact List.mem_flatMap.mpr ⟨Bindings.empty, hmb, hmerge⟩
        | expression ps =>
            cases t with
            | var w =>
                exact (GroundAtom.not_var hground).elim
            | symbol s =>
                simp [simpleMatch] at hmatch
            | grounded g =>
                simp [simpleMatch] at hmatch
            | expression ts =>
                have hts : GroundAtom (.expression ts) := hground
                have htsGround : ∀ a ∈ ts, GroundAtom a := by
                  intro a ha
                  exact GroundAtom.elem hts ha
                cases hneq : (ps.length != ts.length) with
                | true =>
                    simp [simpleMatch, hneq] at hmatch
                | false =>
                    have hlen : ps.length = ts.length := by
                      simpa using hneq
                    simp [simpleMatch, hneq] at hmatch
                    obtain ⟨fuelSeeded, hseeded⟩ := ihList ps ts b qb hb htsGround hmatch
                    obtain ⟨fuelFact, fr, hfr, hmerge2⟩ := hFactor htsGround hb hseeded
                    let fuel0 := max fuelFact 2
                    have hFuelFactLe : fuelFact ≤ fuel0 := by
                      dsimp [fuel0]
                      exact Nat.le_max_left _ _
                    have hFuel0Ge2 : 2 ≤ fuel0 := by
                      dsimp [fuel0]
                      exact Nat.le_max_right _ _
                    have hfr' : fr ∈ matchAtomsList ts ps [Bindings.empty] fuel0 := by
                      have hsub := matchAtomsList_mono_add ts ps [Bindings.empty] fuelFact (fuel0 - fuelFact)
                      have hEq : fuelFact + (fuel0 - fuelFact) = fuel0 :=
                        Nat.add_sub_of_le hFuelFactLe
                      simpa [hEq] using hsub fr hfr
                    have hexpr : fr ∈ matchAtoms (.expression ts) (.expression ps) (fuel0 + 1) := by
                      rw [matchAtoms_ground_expr_filter_free ts ps fuel0 htsGround]
                      have hbeq : (ts.length == ps.length) = true := by
                        simp [hlen]
                      simpa [hbeq] using hfr'
                    have hmerge' : qb ∈ mergeBindings b fr (fuel0 + 1) := by
                      have hsub := mergeBindings_mono_add b fr 2 (fuel0 - 1)
                      have hEq : 2 + (fuel0 - 1) = fuel0 + 1 := by
                        omega
                      simpa [hEq] using hsub qb hmerge2
                    refine ⟨fuel0 + 1, ?_⟩
                    exact List.mem_flatMap.mpr ⟨fr, hexpr, hmerge'⟩
      have hListSucc :
          ∀ ps ts b qb,
            GroundBindings b →
            (∀ t ∈ ts, GroundAtom t) →
            simpleMatch.simpleMatchList ps ts b (n + 1) = some qb →
              ∃ fuel', qb ∈ matchAtomsList ts ps [b] fuel' := by
        have hElemSucc' :
            ∀ {p t b qb},
              GroundBindings b →
              GroundAtom t →
              simpleMatch p t b (n + 1) = some qb →
                ∃ fuel',
                  qb ∈ (matchAtoms t p fuel').flatMap (fun mb => mergeBindings b mb fuel') := by
          intro p t b qb hb hground hmatch
          exact hElemSucc p t b qb hb hground hmatch
        intro ps ts b qb hb hground hmatch
        exact simpleMatchList_ground_seeded_of_elem_bridge_ground (n + 1) hElemSucc' hb hground hmatch
      exact ⟨hElemSucc, hListSucc⟩

/-- Full success bridge for one-way `simpleMatch` on the ground fragment:
every successful coarse match is witnessed by an official matcher result
merged back into the same seed. -/
private theorem simpleMatch_ground_official
    {p t : Atom} {seed out : Bindings} {fuel : Nat}
    (hb : GroundBindings seed)
    (ht : GroundAtom t)
    (hmatch : simpleMatch p t seed fuel = some out) :
    ∃ fuel',
      out ∈ (matchAtoms t p fuel').flatMap (fun mb => mergeBindings seed mb fuel') := by
  exact
    (simpleMatch_ground_official_of_factor
      (fun {lefts rights b x fuelList} hlefts hb hmem =>
        matchAtomsList_singleton_factor_ground hlefts hb hmem) fuel).1
      p t seed out hb ht hmatch

/-- Full success bridge for `simpleMatchList` on the ground fragment:
every successful coarse threaded match has an official seeded list-matcher
witness, possibly at a larger fuel. -/
private theorem simpleMatchList_ground_official
    {ps ts : List Atom} {seed out : Bindings} {fuel : Nat}
    (hb : GroundBindings seed)
    (hts : ∀ t ∈ ts, GroundAtom t)
    (hmatch : simpleMatch.simpleMatchList ps ts seed fuel = some out) :
    ∃ fuel', out ∈ matchAtomsList ts ps [seed] fuel' := by
  exact
    (simpleMatch_ground_official_of_factor
      (fun {lefts rights b x fuelList} hlefts hb hmem =>
        matchAtomsList_singleton_factor_ground hlefts hb hmem) fuel).2
      ps ts seed out hb hts hmatch

/-- Empty-seed success bridge on the ground fragment: when a coarse one-way
match succeeds against a ground target from the empty seed, the resulting
bindings themselves appear as an official `matchAtoms` result at some fuel
at least `2`.  This packages away the empty-seed merge bookkeeping and is
the reusable matcher-facing endpoint for later sugar-rule certifications. -/
theorem simpleMatch_ground_matchAtoms
    {pattern target : Atom} {mb : Bindings} {fuel : Nat}
    (hground : GroundAtom target)
    (hmatch : simpleMatch pattern target Bindings.empty fuel = some mb) :
    ∃ fuel', mb ∈ matchAtoms target pattern fuel' ∧ 2 ≤ fuel' := by
  obtain ⟨fuel', hbridge⟩ :=
    simpleMatch_ground_official GroundBindings.empty hground hmatch
  rcases List.mem_flatMap.mp hbridge with ⟨mb0, hmb0, hmerge0⟩
  have hmbCanon : GroundBindingsCanon mb0 := matchAtoms_ground_canon hground hmb0
  let fuel0 := fuel' + 2
  have hmb0' : mb0 ∈ matchAtoms target pattern fuel0 := by
    dsimp [fuel0]
    exact (matchAtoms_mono_add target pattern fuel' 2) mb0 hmb0
  have hmerge0' : mb ∈ mergeBindings Bindings.empty mb0 fuel0 := by
    dsimp [fuel0]
    exact (mergeBindings_mono_add Bindings.empty mb0 fuel' 2) mb hmerge0
  have hmergeDet : mergeGround? Bindings.empty mb0 = some mb := by
    exact
      (mem_mergeBindings_ground_iff
        (left := Bindings.empty) (right := mb0) (result := mb) (fuel := fuel')
        GroundBindings.empty hmbCanon.1).mp hmerge0'
  have hmergeId : mergeGround? Bindings.empty mb0 = some mb0 :=
    mergeGround_empty_left_of_canon hmbCanon
  have hsame : mb = mb0 := by
    rw [hmergeId] at hmergeDet
    injection hmergeDet with hEq
    exact hEq.symm
  refine ⟨fuel0, ?_, ?_⟩
  · simpa [hsame] using hmb0'
  · dsimp [fuel0]
    omega

/-- Empty-seed no-match bridge on the ground fragment for the non-expression
pattern cases: if coarse one-way matching fails, the official matcher also
has no results (at the same fuel).  The expression-pattern case is excluded
here and treated separately later because it depends on the list-level
earlier-branch failure bridge. -/
private theorem simpleMatch_ground_matchAtoms_nil_nonexpr
    {pattern target : Atom} {fuel : Nat}
    (hground : GroundAtom target)
    (h_nonexpr : ¬ ∃ ps, pattern = .expression ps)
    (hmatch : simpleMatch pattern target Bindings.empty fuel = none) :
    matchAtoms target pattern fuel = [] := by
  cases fuel with
  | zero =>
      simp [matchAtoms]
  | succ n =>
      cases pattern with
      | var v =>
          simp [simpleMatch, Bindings.empty, Bindings.lookup] at hmatch
      | symbol s =>
          cases target with
          | var v =>
              exact (GroundAtom.not_var hground).elim
          | symbol t =>
              simp [simpleMatch] at hmatch
              have hst : s ≠ t := by simpa using hmatch
              have hneq : t ≠ s := by
                intro hts
                exact hst hts.symm
              simp [matchAtoms, getMetaType, Atom.symbolType, hneq]
          | grounded g =>
              simp [matchAtoms, getMetaType, Atom.symbolType, Atom.groundedType]
          | expression es =>
              simp [matchAtoms, getMetaType, Atom.symbolType, Atom.expressionType]
      | grounded g =>
          cases target with
          | var v =>
              exact (GroundAtom.not_var hground).elim
          | symbol s =>
              simp [matchAtoms, getMetaType, Atom.symbolType, Atom.groundedType]
          | grounded h =>
              simp [simpleMatch] at hmatch
              have hgh : g ≠ h := by simpa using hmatch
              have hneq : h ≠ g := by
                intro hhg
                exact hgh hhg.symm
              simp [matchAtoms, getMetaType, Atom.groundedType, hneq]
          | expression es =>
              simp [matchAtoms, getMetaType, Atom.expressionType, Atom.groundedType]
      | expression ps =>
          exact False.elim (h_nonexpr ⟨ps, rfl⟩)

/-- Empty-seed no-match bridge on the full ground fragment: if coarse one-way
matching fails, there exists some official matcher fuel witnessing failure
too.  Non-expression patterns can reuse the same fuel; expression patterns
use fuel `1`, whose inner official list matcher has zero fuel and so yields
no candidates. -/
theorem simpleMatch_ground_matchAtoms_nil
    {pattern target : Atom} {fuel : Nat}
    (hground : GroundAtom target)
    (hmatch : simpleMatch pattern target Bindings.empty fuel = none) :
    ∃ fuel', matchAtoms target pattern fuel' = [] := by
  cases pattern with
  | var v =>
      refine ⟨fuel, ?_⟩
      exact simpleMatch_ground_matchAtoms_nil_nonexpr hground
        (by intro h; rcases h with ⟨ps, hps⟩; cases hps)
        hmatch
  | symbol s =>
      refine ⟨fuel, ?_⟩
      exact simpleMatch_ground_matchAtoms_nil_nonexpr hground
        (by intro h; rcases h with ⟨ps, hps⟩; cases hps)
        hmatch
  | grounded g =>
      refine ⟨fuel, ?_⟩
      exact simpleMatch_ground_matchAtoms_nil_nonexpr hground
        (by intro h; rcases h with ⟨ps, hps⟩; cases hps)
        hmatch
  | expression ps =>
      refine ⟨1, ?_⟩
      cases target with
      | var v =>
          exact (GroundAtom.not_var hground).elim
      | symbol s =>
          simp [matchAtoms, getMetaType, Atom.symbolType, Atom.expressionType]
      | grounded g =>
          simp [matchAtoms, getMetaType, Atom.groundedType, Atom.expressionType]
      | expression ts =>
          have hinner : matchAtomsList ts ps [Bindings.empty] 0 = [] := by
            simp [matchAtomsList]
          simp [matchAtoms, getMetaType, Atom.expressionType, hinner]


end Mettapedia.Languages.MeTTa.HE

/-! ## Complete solution theory of the native matching algebra

These laws use only the HE matcher and the structural atom model. Comparisons
with other runtimes consume them downstream.
-/

namespace Mettapedia.Languages.MeTTa.HE.BindingComposition

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-! ## Fold plumbing for `mergeBindings` -/

private theorem stepFold_solution {β : Type} {Con : β → (String → Metta.Atom) → Prop}
    {f : Bindings → β → List Bindings}
    (hstep : ∀ {bb : Bindings} {p : β} {out : Bindings}, out ∈ f bb p →
      ∀ μ : String → Metta.Atom,
        (HEBindingSatisfied μ out ↔ (HEBindingSatisfied μ bb ∧ Con p μ))) :
    ∀ (entries : List β) (init : List Bindings) (out : Bindings),
      out ∈ entries.foldl (fun acc p => acc.flatMap fun bb => f bb p) init →
      ∃ seed ∈ init, ∀ μ : String → Metta.Atom,
        (HEBindingSatisfied μ out ↔
          (HEBindingSatisfied μ seed ∧ ∀ p ∈ entries, Con p μ)) := by
  intro entries
  induction entries with
  | nil =>
      intro init out h
      exact ⟨out, by simpa using h, fun μ => by simp⟩
  | cons p entries ih =>
      intro init out h
      rw [List.foldl_cons] at h
      obtain ⟨seed1, hseed1, hiff⟩ := ih _ _ h
      obtain ⟨seed0, hseed0, hstep1⟩ := List.mem_flatMap.mp hseed1
      refine ⟨seed0, hseed0, fun μ => ?_⟩
      rw [hiff μ, hstep hstep1 μ, List.forall_mem_cons]
      tauto

/-! ## The fuel-indexed solution pack

The five executable functions recurse mutually on one strictly decreasing
fuel, so their solution characterizations are proven by one simultaneous
induction on fuel — mirroring `DeclMatchSpec.matchSoundPair`. -/

private theorem solutionPack :
    ∀ fuel : Nat,
      (∀ {l r : Atom} {b : Bindings}, b ∈ matchAtoms l r fuel →
        ∀ μ : String → Metta.Atom,
          (HEBindingSatisfied μ b ↔
            applyClassSolution μ (encodeModelAtom l) =
              applyClassSolution μ (encodeModelAtom r))) ∧
      (∀ {ls rs : List Atom} {acc : List Bindings} {out : Bindings},
        out ∈ matchAtomsList ls rs acc fuel →
        ∃ seed ∈ acc, ∀ μ : String → Metta.Atom,
          (HEBindingSatisfied μ out ↔
            (HEBindingSatisfied μ seed ∧
              (encodeModelAtoms ls).map (applyClassSolution μ) =
                (encodeModelAtoms rs).map (applyClassSolution μ)))) ∧
      (∀ {left right out : Bindings}, out ∈ mergeBindings left right fuel →
        ∀ μ : String → Metta.Atom,
          (HEBindingSatisfied μ out ↔
            (HEBindingSatisfied μ left ∧ HEBindingSatisfied μ right))) ∧
      (∀ {b : Bindings} {v : String} {val : Atom} {out : Bindings},
        out ∈ addVarBinding b v val fuel →
        ∀ μ : String → Metta.Atom,
          (HEBindingSatisfied μ out ↔
            (HEBindingSatisfied μ b ∧
              μ v = applyClassSolution μ (encodeModelAtom val)))) ∧
      (∀ {b : Bindings} {a c : String} {out : Bindings},
        out ∈ addVarEquality b a c fuel →
        ∀ μ : String → Metta.Atom,
          (HEBindingSatisfied μ out ↔
            (HEBindingSatisfied μ b ∧ μ a = μ c)))
  | 0 => by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro l r b h
        simp [matchAtoms] at h
      · intro ls rs acc out h
        simp [matchAtomsList] at h
      · intro left right out h
        simp [mergeBindings] at h
      · intro b v val out h
        simp [addVarBinding] at h
      · intro b a c out h
        simp [addVarEquality] at h
  | fuel + 1 => by
      obtain ⟨ihA, ihB, ihC, ihD, ihE⟩ := solutionPack fuel
      -- The merge/add layer first: it only consumes the IH at `fuel`.
      have hD : ∀ {b : Bindings} {v : String} {val : Atom} {out : Bindings},
          out ∈ addVarBinding b v val (fuel + 1) →
          ∀ μ : String → Metta.Atom,
            (HEBindingSatisfied μ out ↔
              (HEBindingSatisfied μ b ∧
                μ v = applyClassSolution μ (encodeModelAtom val))) := by
        intro b v val out h
        simp only [addVarBinding] at h
        split at h
        · -- fresh class: no value anywhere in the class
          next hcv =>
            simp only [List.mem_singleton] at h
            subst h
            exact hesat_assign_of_not_isBound
              (EqualityClosure.isBound_eq_false_of_classValues_nil hcv)
        · next first rest hcv =>
            split at h
            · -- consistent class values
              split at h
              · -- proposed value equals the carried value: no change
                next hbeq =>
                  simp only [List.mem_singleton] at h
                  subst h
                  have hval : first = val := eq_of_beq hbeq
                  subst hval
                  intro μ
                  constructor
                  · intro hs
                    exact ⟨hs, hs.eq_applyClassSolution_of_mem_classValues
                      (by rw [hcv]; exact List.mem_cons_self ..)⟩
                  · exact fun hs => hs.1
              · -- conflicting value: reconcile through the matcher, merge back
                next hbeq =>
                  obtain ⟨mb, hmb, hmrg⟩ := List.mem_flatMap.mp h
                  intro μ
                  rw [ihC hmrg μ, ihA hmb μ]
                  have hfirst : HEBindingSatisfied μ b →
                      μ v = applyClassSolution μ (encodeModelAtom first) :=
                    fun hs => hs.eq_applyClassSolution_of_mem_classValues
                      (by rw [hcv]; exact List.mem_cons_self ..)
                  constructor
                  · rintro ⟨hs, hfv⟩
                    exact ⟨hs, (hfirst hs).trans hfv⟩
                  · rintro ⟨hs, hvv⟩
                    exact ⟨hs, (hfirst hs).symm.trans hvv⟩
            · -- inconsistent class values: reconcile the whole class plus `val`
              next hcons =>
                obtain ⟨mb, hmb, hmrg⟩ := List.mem_flatMap.mp h
                obtain ⟨seed, hseed, hiffL⟩ := ihB hmb
                simp only [List.mem_singleton] at hseed
                subst hseed
                intro μ
                rw [ihC hmrg μ, hiffL μ]
                simp only [hesat_empty_iff, true_and,
                  solutionTheory_encodeModelAtoms_eq_map,
                  List.map_map, List.map_replicate, List.append_eq]
                rw [replicate_eq_map_iff μ first (rest ++ [val])]
                have hfirst : HEBindingSatisfied μ b →
                    μ v = applyClassSolution μ (encodeModelAtom first) :=
                  fun hs => hs.eq_applyClassSolution_of_mem_classValues
                    (by rw [hcv]; exact List.mem_cons_self ..)
                have hrest : HEBindingSatisfied μ b →
                    ∀ o ∈ rest, applyClassSolution μ (encodeModelAtom o) =
                      applyClassSolution μ (encodeModelAtom first) :=
                  fun hs o ho =>
                    (hs.eq_applyClassSolution_of_mem_classValues
                      (by rw [hcv]; exact List.mem_cons_of_mem _ ho)).symm.trans
                      (hfirst hs)
                constructor
                · rintro ⟨hs, hall⟩
                  have hval := hall val
                    (List.mem_append_right _ (by simp))
                  exact ⟨hs, (hfirst hs).trans hval.symm⟩
                · rintro ⟨hs, hvv⟩
                  refine ⟨hs, fun o ho => ?_⟩
                  rcases List.mem_append.mp ho with ho | ho
                  · exact hrest hs o ho
                  · simp only [List.mem_singleton] at ho
                    subst ho
                    exact ((hfirst hs).symm.trans hvv).symm
      have hE : ∀ {b : Bindings} {a c : String} {out : Bindings},
          out ∈ addVarEquality b a c (fuel + 1) →
          ∀ μ : String → Metta.Atom,
            (HEBindingSatisfied μ out ↔
              (HEBindingSatisfied μ b ∧ μ a = μ c)) := by
        intro b a c out h
        simp only [addVarEquality] at h
        split at h
        · -- joined class already consistent
          simp only [List.mem_singleton] at h
          subst h
          exact hesat_addEquality
        · next hcons =>
            split at h
            · -- no values at all: `valuesConsistent [] = true`, contradiction
              simp at h
            · -- exactly two conflicting values
              next first second hcv =>
                obtain ⟨mb, hmb, hmrg⟩ := List.mem_flatMap.mp h
                intro μ
                rw [ihC hmrg μ, ihA hmb μ, hesat_addEquality μ]
                have hpair : HEBindingSatisfied μ (b.addEquality a c) →
                    applyClassSolution μ (encodeModelAtom first) =
                      applyClassSolution μ (encodeModelAtom second) := by
                  intro hs
                  have h1 := hs.eq_applyClassSolution_of_mem_classValues
                    (v := a) (by rw [hcv]; exact List.mem_cons_self ..)
                  have h2 := hs.eq_applyClassSolution_of_mem_classValues
                    (v := a) (by
                      rw [hcv]
                      exact List.mem_cons_of_mem _ (List.mem_cons_self ..))
                  exact h1.symm.trans h2
                constructor
                · rintro ⟨hs, -⟩
                  exact hs
                · rintro ⟨hsb, hac⟩
                  have hs := (hesat_addEquality μ).mpr ⟨hsb, hac⟩
                  exact ⟨⟨hsb, hac⟩, hpair hs⟩
            · -- three or more conflicting values
              next first rest hnotpair hcv =>
                obtain ⟨mb, hmb, hmrg⟩ := List.mem_flatMap.mp h
                obtain ⟨seed, hseed, hiffL⟩ := ihB hmb
                simp only [List.mem_singleton] at hseed
                subst hseed
                intro μ
                rw [ihC hmrg μ, hiffL μ, hesat_addEquality μ]
                simp only [hesat_empty_iff, true_and,
                  solutionTheory_encodeModelAtoms_eq_map,
                  List.map_map, List.map_replicate]
                rw [replicate_eq_map_iff μ first rest]
                have hall : HEBindingSatisfied μ (b.addEquality a c) →
                    ∀ o ∈ rest, applyClassSolution μ (encodeModelAtom o) =
                      applyClassSolution μ (encodeModelAtom first) := by
                  intro hs o ho
                  have h1 := hs.eq_applyClassSolution_of_mem_classValues
                    (v := a) (by rw [hcv]; exact List.mem_cons_self ..)
                  have h2 := hs.eq_applyClassSolution_of_mem_classValues
                    (v := a) (by rw [hcv]; exact List.mem_cons_of_mem _ ho)
                  exact h2.symm.trans h1
                constructor
                · rintro ⟨hs, -⟩
                  exact hs
                · intro hs
                  have hsat := (hesat_addEquality μ).mpr hs
                  exact ⟨hs, hall hsat⟩
      have hC : ∀ {left right out : Bindings},
          out ∈ mergeBindings left right (fuel + 1) →
          ∀ μ : String → Metta.Atom,
            (HEBindingSatisfied μ out ↔
              (HEBindingSatisfied μ left ∧ HEBindingSatisfied μ right)) := by
        intro left right out h
        simp only [mergeBindings] at h
        obtain ⟨mid, hmid, hiffE⟩ :=
          stepFold_solution (f := fun bb p => addVarEquality bb p.1 p.2 fuel)
            (Con := fun p μ => μ p.1 = μ p.2)
            (fun hstep μ => ihE hstep μ) right.equalities _ out h
        obtain ⟨seed, hseed, hiffA⟩ :=
          stepFold_solution (f := fun bb p => addVarBinding bb p.1 p.2 fuel)
            (Con := fun p μ =>
              μ p.1 = applyClassSolution μ (encodeModelAtom p.2))
            (fun hstep μ => ihD hstep μ) right.assignments [left] mid hmid
        simp only [List.mem_singleton] at hseed
        subst hseed
        intro μ
        rw [hiffE μ, hiffA μ]
        constructor
        · rintro ⟨⟨hl, hassigns⟩, heqs⟩
          exact ⟨hl,
            ⟨fun x value hx => hassigns (x, value) hx,
             fun x y hx => heqs (x, y) hx⟩⟩
        · rintro ⟨hl, hr⟩
          exact ⟨⟨hl, fun p hp => hr.1 p.1 p.2 (by simpa using hp)⟩,
            fun p hp => hr.2 p.1 p.2 (by simpa using hp)⟩
      -- The matcher layer, mirroring `matchSoundPair`'s case skeleton.
      have hB : ∀ {ls rs : List Atom} {acc : List Bindings} {out : Bindings},
          out ∈ matchAtomsList ls rs acc (fuel + 1) →
          ∃ seed ∈ acc, ∀ μ : String → Metta.Atom,
            (HEBindingSatisfied μ out ↔
              (HEBindingSatisfied μ seed ∧
                (encodeModelAtoms ls).map (applyClassSolution μ) =
                  (encodeModelAtoms rs).map (applyClassSolution μ))) := by
        intro ls rs acc out h
        cases ls <;> cases rs <;> simp [matchAtomsList] at h
        case nil.nil =>
          exact ⟨out, h, fun μ => by simp⟩
        case cons.cons l ls r rs =>
          obtain ⟨seed1, hseed1, hiff⟩ := ihB h
          obtain ⟨a, ha, hseed1'⟩ := List.mem_flatMap.mp hseed1
          obtain ⟨bH, hbH, hmrg⟩ := List.mem_flatMap.mp hseed1'
          refine ⟨a, ha, fun μ => ?_⟩
          rw [hiff μ, ihC hmrg μ, ihA hbH μ]
          simp only [encodeModelAtoms_cons, List.map_cons, List.cons.injEq]
          tauto
      have hA : ∀ {l r : Atom} {b : Bindings}, b ∈ matchAtoms l r (fuel + 1) →
          ∀ μ : String → Metta.Atom,
            (HEBindingSatisfied μ b ↔
              applyClassSolution μ (encodeModelAtom l) =
                applyClassSolution μ (encodeModelAtom r)) := by
        intro l r b h
        cases l with
        | symbol s =>
            cases r with
            | symbol t =>
                by_cases hst : s = t
                · subst hst
                  simp [matchAtoms, getMetaType, Atom.symbolType] at h
                  have hb : b = Bindings.empty := by simpa using h.1
                  subst hb
                  simp
                · simp [matchAtoms, getMetaType, Atom.symbolType, hst] at h
            | var v =>
                simp [matchAtoms, getMetaType, Atom.symbolType,
                  Atom.variableType] at h
                have hb : b = Bindings.empty.assign v (.symbol s) := by
                  simpa using h.1
                subst hb
                intro μ
                rw [hesat_assign_of_not_isBound (by rfl) μ]
                simp [eq_comm]
            | grounded g =>
                simp [matchAtoms, getMetaType, Atom.symbolType,
                  Atom.groundedType] at h
            | expression es =>
                simp [matchAtoms, getMetaType, Atom.symbolType,
                  Atom.expressionType] at h
        | var v =>
            cases r with
            | symbol s =>
                simp [matchAtoms, getMetaType, Atom.symbolType,
                  Atom.variableType] at h
                have hb : b = Bindings.empty.assign v (.symbol s) := by
                  simpa using h.1
                subst hb
                intro μ
                rw [hesat_assign_of_not_isBound (by rfl) μ]
                simp
            | var w =>
                simp [matchAtoms, getMetaType, Atom.variableType] at h
                have hb : b = Bindings.empty.addEquality v w := by
                  simpa using h.1
                subst hb
                intro μ
                rw [hesat_addEquality μ]
                simp
            | grounded g =>
                simp [matchAtoms, getMetaType, Atom.variableType,
                  Atom.groundedType] at h
                have hb : b = Bindings.empty.assign v (.grounded g) := by
                  simpa using h.1
                subst hb
                intro μ
                rw [hesat_assign_of_not_isBound (by rfl) μ]
                simp
            | expression es =>
                simp [matchAtoms, getMetaType, Atom.variableType,
                  Atom.expressionType] at h
                have hb : b = Bindings.empty.assign v (.expression es) := by
                  simpa using h.1
                subst hb
                intro μ
                rw [hesat_assign_of_not_isBound (by rfl) μ]
                simp
        | grounded g =>
            cases r with
            | symbol s =>
                simp [matchAtoms, getMetaType, Atom.symbolType,
                  Atom.groundedType] at h
            | var v =>
                simp [matchAtoms, getMetaType, Atom.variableType,
                  Atom.groundedType] at h
                have hb : b = Bindings.empty.assign v (.grounded g) := by
                  simpa using h.1
                subst hb
                intro μ
                rw [hesat_assign_of_not_isBound (by rfl) μ]
                simp [eq_comm]
            | grounded hG =>
                by_cases hg : g = hG
                · subst hg
                  simp [matchAtoms, getMetaType, Atom.groundedType] at h
                  have hb : b = Bindings.empty := by simpa using h.1
                  subst hb
                  simp
                · simp [matchAtoms, getMetaType, Atom.groundedType, hg] at h
            | expression es =>
                simp [matchAtoms, getMetaType, Atom.expressionType,
                  Atom.groundedType] at h
        | expression ls =>
            cases r with
            | symbol s =>
                simp [matchAtoms, getMetaType, Atom.symbolType,
                  Atom.expressionType] at h
            | var v =>
                simp [matchAtoms, getMetaType, Atom.variableType,
                  Atom.expressionType] at h
                have hb : b = Bindings.empty.assign v (.expression ls) := by
                  simpa using h.1
                subst hb
                intro μ
                rw [hesat_assign_of_not_isBound (by rfl) μ]
                simp [eq_comm]
            | grounded g =>
                simp [matchAtoms, getMetaType, Atom.expressionType,
                  Atom.groundedType] at h
            | expression rs =>
                by_cases hlen : ls.length = rs.length
                · simp [matchAtoms, getMetaType, Atom.expressionType,
                    hlen] at h
                  rcases h with ⟨hList, -⟩
                  obtain ⟨seed, hseed, hiff⟩ := ihB hList
                  simp only [List.mem_singleton] at hseed
                  subst hseed
                  intro μ
                  rw [hiff μ]
                  simp [Metta.Atom.expr.injEq]
                · simp [matchAtoms, getMetaType, Atom.expressionType,
                    hlen] at h
      exact ⟨hA, hB, hC, hD, hE⟩

/-! ## Exported solution characterizations -/

/-- **Solution soundness of the executable HE matcher**: every returned
binding set presents exactly the solution set of the input equation. -/
theorem matchAtoms_solution_iff {l r : Atom} {b : Bindings} {fuel : Nat}
    (h : b ∈ matchAtoms l r fuel) (μ : String → Metta.Atom) :
    HEBindingSatisfied μ b ↔
      MettaEquationSatisfied μ (encodeModelAtom l, encodeModelAtom r) :=
  (solutionPack fuel).1 h μ

/-- A raw list result presents exactly one incoming seed together with all
component equations.  This law does not promote the result to an accepted
expression match. -/
theorem matchAtomsList_solution_iff
    {ls rs : List Atom} {acc : List Bindings} {out : Bindings} {fuel : Nat}
    (h : out ∈ matchAtomsList ls rs acc fuel) :
    ∃ seed ∈ acc, ∀ μ : String → Metta.Atom,
      HEBindingSatisfied μ out ↔
        HEBindingSatisfied μ seed ∧
          MettaAtomListsSatisfied μ (encodeModelAtoms ls) (encodeModelAtoms rs) :=
  (solutionPack fuel).2.1 h

/-- With a singleton incoming frontier, the selected seed is determined. -/
theorem matchAtomsList_singleton_solution_iff
    {ls rs : List Atom} {seed out : Bindings} {fuel : Nat}
    (h : out ∈ matchAtomsList ls rs [seed] fuel)
    (μ : String → Metta.Atom) :
    HEBindingSatisfied μ out ↔
      HEBindingSatisfied μ seed ∧
        MettaAtomListsSatisfied μ (encodeModelAtoms ls) (encodeModelAtoms rs) := by
  obtain ⟨selected, hselected, hiff⟩ := matchAtomsList_solution_iff h
  simp only [List.mem_singleton] at hselected
  subst selected
  exact hiff μ

/-- Merging presents exactly solution intersection. -/
theorem mergeBindings_solution_iff {left right out : Bindings} {fuel : Nat}
    (h : out ∈ mergeBindings left right fuel) (μ : String → Metta.Atom) :
    HEBindingSatisfied μ out ↔
      (HEBindingSatisfied μ left ∧ HEBindingSatisfied μ right) :=
  (solutionPack fuel).2.2.1 h μ

/-- `addVarBinding` presents exactly one added value constraint. -/
theorem addVarBinding_solution_iff {b : Bindings} {v : String} {val : Atom}
    {out : Bindings} {fuel : Nat}
    (h : out ∈ addVarBinding b v val fuel) (μ : String → Metta.Atom) :
    HEBindingSatisfied μ out ↔
      (HEBindingSatisfied μ b ∧
        μ v = applyClassSolution μ (encodeModelAtom val)) :=
  (solutionPack fuel).2.2.2.1 h μ

/-- `addVarEquality` presents exactly one added equality constraint. -/
theorem addVarEquality_solution_iff {b : Bindings} {a c : String}
    {out : Bindings} {fuel : Nat}
    (h : out ∈ addVarEquality b a c fuel) (μ : String → Metta.Atom) :
    HEBindingSatisfied μ out ↔
      (HEBindingSatisfied μ b ∧ μ a = μ c) :=
  (solutionPack fuel).2.2.2.2 h μ

end Mettapedia.Languages.MeTTa.HE.BindingComposition

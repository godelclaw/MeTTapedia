import Mettapedia.Languages.ProcessCalculi.MORK.MM2FunctionCalls
import Mettapedia.Languages.ProcessCalculi.MORK.PhysicalSupportHeadFaithfulness

/-!
# Synchronous call is not locally eliminable in the kernel

A *local elimination* of the call sink replaces a caller by call-free atoms chosen from the
caller alone, and leaves every call-free atom unchanged.  Extension and translation are
compared by what they report in every context: the semantic counterpart of operational
soundness, rather than syntactic conditions on the expansion.

The window: the caller `(exec () (,) (O (call f a $r (+ (g $r)))))`, the watcher
`(exec () (, (g $z)) (O (+ (out $z))))` and an equation `(= (f a) N)`.  In the extension the
call returns within the caller's firing, so the watcher reports `(out N)`; without the
watcher nothing is reported.

The argument.  Every executable whose key is below the watcher's reads only atoms of arity
at most two, so neither the watcher nor the equation is visible before the watcher fires.
Until then, the runs with and without the watcher agree outside the watcher, and they agree
with the expansion's own run outside the context.  If that run never lets the watcher fire,
both contexts report alike.  If it does, the value is chosen fresh for that finite stretch:
when the watcher fires, `(g N)` is absent, so it reports nothing — and the two runs
coincide afterwards — or something other than `(out N)`.

This module first presents a kernel step as a list of insertions and removals that does not
depend on the space, which makes atoms that a firing cannot read inert: projecting them away
commutes with the step.

Reports are compared up to the kernel's identification of atoms: `(out x)` is reported when a
reachable configuration holds an atom with its key (`ReportsKey`, `SourceReportsKey`).

Results:

* `call_not_locally_eliminable`: for every expansion of the caller, for every build profile,
  registry and external state, some value `N` makes the expansion's reports differ from the
  extension's beside the watcher and `(= (f a) N)`, or beside `(= (f a) N)` alone.  The
  expansion is any list of kernel atoms, chosen without seeing the context, so the theorem
  covers expansions that create symbols, read code or loop.
* `target_alternatives`: the kernel half — whatever the expansion, the two contexts report
  alike, or the one with the watcher reports something other than `(out N)`, or the one
  without it reports at all.
* `source_with_reports`, `source_without_silent`: the extension's half — exactly `(out N)`
  beside the watcher, nothing without it.
* `relocation_closes_window`: locality is necessary.  The compositional translation that moves
  every executable of the context one level up and turns the caller into a join with the
  equation of `f` reports exactly as the extension does on the whole window family.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.CallLocality

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Mainline
open Mettapedia.Languages.ProcessCalculi.MORK.FunctionCalls
open Mettapedia.Languages.ProcessCalculi.MORK.Expressiveness

/-! ## A step as operations on the space -/

/-- One change to a support list. -/
inductive SpaceOp where
  | ins (atom : Atom)
  | del (atom : Atom)

def applyOp (space : List Atom) : SpaceOp → List Atom
  | .ins atom => morkInsertSupport space atom
  | .del atom => morkEraseSupport space atom

def applyOps (space : List Atom) (ops : List SpaceOp) : List Atom := ops.foldl applyOp space

theorem applyOps_append (space : List Atom) (first second : List SpaceOp) :
    applyOps space (first ++ second) = applyOps (applyOps space first) second :=
  List.foldl_append ..

theorem union_ops : ∀ (space staged : List Atom),
    morkUnionSupport space staged = applyOps space (staged.map .ins)
  | _, [] => rfl
  | space, atom :: rest => by
      simp only [morkUnionSupport, List.foldl_cons, List.map_cons, applyOps] at *
      exact union_ops (morkInsertSupport space atom) rest

theorem subtract_ops : ∀ (space staged : List Atom),
    morkSubtractSupport space staged = applyOps space (staged.map .del)
  | _, [] => rfl
  | space, atom :: rest => by
      simp only [morkSubtractSupport, List.foldl_cons, List.map_cons, applyOps] at *
      exact subtract_ops (morkEraseSupport space atom) rest

/-- An effect of a firing that does not depend on the space: the operations it applies
and the external state it leaves, or the fault. -/
abbrev Effect := Except MainlineFault (List SpaceOp × ExternalState)

/-- Apply an effect to a space. -/
def Effect.on (effect : Effect) (space : List Atom) : Except MainlineFault (List Atom × ExternalState) :=
  effect.map fun result => (applyOps space result.1, result.2)

/-- **Every sink's finalization is a space-independent effect.** -/
theorem finalize_effect (prims : Primitives) (input : InputSpec) (rows : List Subst)
    (external : ExternalState) (sink : MainlineSink) :
    ∃ effect : Effect, ∀ space,
      finalizeMainlineSink prims input rows (space, external) sink = effect.on space := by
  cases sink with
  | core sink =>
      cases sink with
      | add body => exact ⟨.ok ([], external), fun _ => rfl⟩
      | remove body =>
          exact ⟨.ok ((staged input rows body).map .del, external), fun space => by
            simp [finalizeMainlineSink, Effect.on, subtract_ops, Except.map]⟩
      | head count body =>
          by_cases fine : ((instances input rows body).map morkSupportKey).Nodup ∨
              (staged input rows body).length < count
          · exact ⟨.ok ((compactExtremaList true count (staged input rows body)).map .ins, external),
              fun space => by
                simp [finalizeMainlineSink, fine, Effect.on, finalizeRuleScopedSink, union_ops,
                  Except.map]⟩
          · exact ⟨.error (.extremaDuplicate body), fun space => by
              simp [finalizeMainlineSink, fine, Effect.on, Except.map]⟩
      | tail count body =>
          by_cases fine : ((instances input rows body).map morkSupportKey).Nodup ∨
              (staged input rows body).length < count
          · exact ⟨.ok ((compactExtremaList false count (staged input rows body)).map .ins, external),
              fun space => by
                simp [finalizeMainlineSink, fine, Effect.on, finalizeRuleScopedSink, union_ops,
                  Except.map]⟩
          · exact ⟨.error (.extremaDuplicate body), fun space => by
              simp [finalizeMainlineSink, fine, Effect.on, Except.map]⟩
  | unify body =>
      cases batch : staged input rows body with
      | nil => exact ⟨.ok ([], external), fun space => by
          simp [finalizeMainlineSink, batch, Effect.on, Except.map, applyOps]⟩
      | cons first rest =>
          cases unified : prims.unify (first :: rest) with
          | none => exact ⟨.ok ([], external), fun space => by
              simp [finalizeMainlineSink, batch, unified, Effect.on, Except.map, applyOps]⟩
          | some general => exact ⟨.ok ([.ins general], external), fun space => by
              simp [finalizeMainlineSink, batch, unified, Effect.on, Except.map, applyOps, applyOp]⟩
  | antiUnify body =>
      by_cases single : (instances input rows body).length = 1
      · exact ⟨.error (.antiUnifySingleRow body), fun space => by
          simp [finalizeMainlineSink, single, Effect.on, Except.map]⟩
      · cases batch : staged input rows body with
        | nil => exact ⟨.ok ([], external), fun space => by
            simp [finalizeMainlineSink, single, batch, Effect.on, Except.map, applyOps]⟩
        | cons first rest =>
            cases general : prims.antiUnify (first :: rest) with
            | none => exact ⟨.ok ([], external), fun space => by
                simp [finalizeMainlineSink, single, batch, general, Effect.on, Except.map, applyOps]⟩
            | some value => exact ⟨.ok ([.ins value], external), fun space => by
                simp [finalizeMainlineSink, single, batch, general, Effect.on, Except.map, applyOps,
                  applyOp]⟩
  | aggregate kind context count payload =>
      cases writes : aggregateWrites prims input rows kind context count payload with
      | error fault => exact ⟨.error fault, fun space => by
          simp [finalizeMainlineSink, writes, Effect.on, Except.map]⟩
      | ok values => exact ⟨.ok ((written values).map .ins, external), fun space => by
          simp [finalizeMainlineSink, writes, Effect.on, Except.map, union_ops]⟩
  | act file body =>
      exact ⟨.ok ([], { external with
        files := Function.update external.files file (some (staged input rows body)) }), fun _ => rfl⟩
  | pure template result call =>
      cases writes : pureWrites prims input rows template result call with
      | error fault => exact ⟨.error fault, fun space => by
          simp [finalizeMainlineSink, writes, Effect.on, Except.map]⟩
      | ok values => exact ⟨.ok ((written values).map .ins, external), fun space => by
          simp [finalizeMainlineSink, writes, Effect.on, Except.map, union_ops]⟩
  | z3 solver statement =>
      exact ⟨.ok ([], { external with
        solvers := Function.update external.solvers solver
          (some ((external.solvers solver).getD [] ++ staged input rows statement)) }), fun _ => rfl⟩
  | wasm program body => exact ⟨.ok ([], external), fun _ => rfl⟩

/-- **Finalizing a whole output is a space-independent effect.** -/
theorem finalizeAll_effect (prims : Primitives) (input : InputSpec) (rows : List Subst) :
    ∀ (sinks : List MainlineSink) (external : ExternalState),
      ∃ effect : Effect, ∀ space,
        sinks.foldlM (finalizeMainlineSink prims input rows) (space, external) = effect.on space
  | [], external => ⟨.ok ([], external), fun _ => rfl⟩
  | sink :: rest, external => by
      obtain ⟨first, firstOn⟩ := finalize_effect prims input rows external sink
      cases first with
      | error fault =>
          exact ⟨.error fault, fun space => by
            simp only [List.foldlM_cons, firstOn space, Effect.on, Except.map, bind, Except.bind]⟩
      | ok result =>
          obtain ⟨ops, middle⟩ := result
          obtain ⟨tail, tailOn⟩ := finalizeAll_effect prims input rows rest middle
          cases tail with
          | error fault =>
              exact ⟨.error fault, fun space => by
                simp only [List.foldlM_cons, firstOn space, Effect.on, Except.map, bind, Except.bind]
                rw [tailOn]; rfl⟩
          | ok tailResult =>
              obtain ⟨more, after⟩ := tailResult
              exact ⟨.ok (ops ++ more, after), fun space => by
                simp only [List.foldlM_cons, firstOn space, Effect.on, Except.map, bind, Except.bind]
                rw [tailOn]
                simp [Effect.on, Except.map, applyOps_append]⟩

theorem eager_ops (prims : Primitives) (input : InputSpec) (rows : List Subst) :
    ∀ (sinks : List MainlineSink) (space : List Atom),
      sinks.foldl (fun current sink => morkUnionSupport current (eagerOutputs prims input rows sink))
          space =
        applyOps space (sinks.flatMap fun sink => (eagerOutputs prims input rows sink).map .ins)
  | [], _ => rfl
  | sink :: rest, space => by
      rw [List.foldl_cons, List.flatMap_cons, applyOps_append, ← union_ops]
      exact eager_ops prims input rows rest _

/-- **Applying an output is a space-independent effect.** -/
theorem applyMainlineSinks_effect (prims : Primitives) (input : InputSpec) (rows : List Subst)
    (external : ExternalState) (sinks : List MainlineSink) :
    ∃ effect : Effect, ∀ space,
      applyMainlineSinks prims input rows space external sinks = effect.on space := by
  obtain ⟨finalized, finalizedOn⟩ := finalizeAll_effect prims input rows sinks external
  refine ⟨finalized.map fun result =>
      ((sinks.flatMap fun sink => (eagerOutputs prims input rows sink).map SpaceOp.ins) ++ result.1,
        result.2), fun space => ?_⟩
  simp only [applyMainlineSinks, eager_ops, finalizedOn]
  cases finalized with
  | error fault => rfl
  | ok result => simp [Effect.on, Except.map, applyOps_append]

theorem templates_ops (input : InputSpec) (rows : List Subst) :
    ∀ (templates : List Atom) (space : List Atom),
      templates.foldl (fun current template => morkUnionSupport current (staged input rows template))
          space =
        applyOps space (templates.flatMap fun template => (staged input rows template).map .ins)
  | [], _ => rfl
  | template :: rest, space => by
      rw [List.foldl_cons, List.flatMap_cons, applyOps_append, ← union_ops]
      exact templates_ops input rows rest _

/-- **A firing is its rows followed by a space-independent effect** on the live space. -/
theorem fireDirective_effect (prims : Primitives) (external : ExternalState)
    (directive : MainlineDirective) :
    ∃ effect : List Subst → Effect, ∀ space,
      fireDirective prims external space directive =
        match mainlineRows prims external (factorTag directive.atom)
            (morkInsertSupport (morkEraseSupport space directive.atom) directive.atom)
            directive.input with
        | .error fault => .error fault
        | .ok solved => (effect solved).on (morkEraseSupport space directive.atom) := by
  obtain ⟨atom, input, output⟩ := directive
  cases output with
  | compat templates =>
      refine ⟨fun solved => .ok (templates.flatMap fun template =>
          (staged input.coverage (solved.map (inputRow (inputSpecVariables input.coverage))) template).map
            SpaceOp.ins, external), fun space => ?_⟩
      simp only [fireDirective, bind, Except.bind]
      cases mainlineRows prims external (factorTag atom)
          (morkInsertSupport (morkEraseSupport space atom) atom) input with
      | error fault => rfl
      | ok solved => simp [Effect.on, Except.map, templates_ops, pure, Except.pure]
  | sinks sinks =>
      refine ⟨fun solved => Classical.choose (applyMainlineSinks_effect prims input.coverage
          (solved.map (inputRow (inputSpecVariables input.coverage))) external sinks), fun space => ?_⟩
      simp only [fireDirective, bind, Except.bind]
      cases mainlineRows prims external (factorTag atom)
          (morkInsertSupport (morkEraseSupport space atom) atom) input with
      | error fault => rfl
      | ok solved =>
          exact Classical.choose_spec (applyMainlineSinks_effect prims input.coverage
            (solved.map (inputRow (inputSpecVariables input.coverage))) external sinks) _

/-! ## Atoms a firing cannot see

`hide` marks atoms by physical key.  Projecting them away commutes with every space
operation, so two spaces that agree outside the hidden atoms stay in agreement under any
sequence of insertions and removals. -/

section Hidden

variable (hide : Atom → Bool)

/-- A marking of atoms that depends only on the physical key. -/
def KeyInvariant : Prop := ∀ x y, morkSupportKey x = morkSupportKey y → hide x = hide y

/-- The atoms of a space that are not hidden. -/
def proj (space : List Atom) : List Atom := space.filter fun atom => !hide atom

theorem proj_proj (space : List Atom) : proj hide (proj hide space) = proj hide space := by
  simp [proj, List.filter_filter]

theorem proj_append (first second : List Atom) :
    proj hide (first ++ second) = proj hide first ++ proj hide second := List.filter_append ..

variable {hide}

theorem contains_proj_visible (keyInv : KeyInvariant hide) (space : List Atom) (atom : Atom)
    (visible : hide atom = false) :
    morkSupportContains (proj hide space) atom = morkSupportContains space atom := by
  apply Bool.eq_iff_iff.mpr
  rw [morkSupportContains_eq_true_iff_key_mem, morkSupportContains_eq_true_iff_key_mem]
  constructor
  · intro member
    obtain ⟨other, otherMember, sameKey⟩ := List.mem_map.1 member
    exact List.mem_map.2 ⟨other, (List.mem_filter.1 otherMember).1, sameKey⟩
  · intro member
    obtain ⟨other, otherMember, sameKey⟩ := List.mem_map.1 member
    refine List.mem_map.2 ⟨other, List.mem_filter.2 ⟨otherMember, ?_⟩, sameKey⟩
    rw [keyInv other atom sameKey, visible]
    rfl

theorem contains_proj_hidden (keyInv : KeyInvariant hide) (space : List Atom) (atom : Atom)
    (hidden : hide atom = true) : morkSupportContains (proj hide space) atom = false := by
  apply Bool.eq_false_iff.mpr
  intro present
  rw [morkSupportContains_eq_true_iff_key_mem] at present
  obtain ⟨other, otherMember, sameKey⟩ := List.mem_map.1 present
  have visible := (List.mem_filter.1 otherMember).2
  rw [keyInv other atom sameKey, hidden] at visible
  cases visible

theorem proj_insert (keyInv : KeyInvariant hide) (space : List Atom) (atom : Atom) :
    proj hide (morkInsertSupport space atom) =
      proj hide (morkInsertSupport (proj hide space) atom) := by
  cases hidden : hide atom with
  | true =>
      have absent := contains_proj_hidden keyInv space atom hidden
      unfold morkInsertSupport
      rw [absent]
      simp only [Bool.false_eq_true, if_false, proj_append, proj_proj]
      split <;> simp [proj, hidden]
  | false =>
      have same := contains_proj_visible keyInv space atom hidden
      unfold morkInsertSupport
      rw [same]
      split
      · rw [proj_proj]
      · rw [proj_append, proj_append, proj_proj]

theorem proj_erase (space : List Atom) (atom : Atom) :
    proj hide (morkEraseSupport space atom) = proj hide (morkEraseSupport (proj hide space) atom) := by
  simp only [proj, morkEraseSupport, List.filter_filter]
  congr 1
  funext other
  cases hide other <;> cases sameMorkSupportAtom other atom <;> rfl

theorem proj_applyOp (keyInv : KeyInvariant hide) (space : List Atom) (op : SpaceOp) :
    proj hide (applyOp space op) = proj hide (applyOp (proj hide space) op) := by
  cases op with
  | ins atom => exact proj_insert keyInv space atom
  | del atom => exact proj_erase space atom

theorem proj_applyOps (keyInv : KeyInvariant hide) :
    ∀ (ops : List SpaceOp) (space : List Atom),
      proj hide (applyOps space ops) = proj hide (applyOps (proj hide space) ops)
  | [], space => by simp [applyOps, proj_proj]
  | op :: rest, space => by
      simp only [applyOps, List.foldl_cons]
      have first := proj_applyOps keyInv rest (applyOp space op)
      have second := proj_applyOps keyInv rest (applyOp (proj hide space) op)
      simp only [applyOps] at first second
      rw [first, second, proj_applyOp keyInv space op]

/-- Two spaces that agree outside the hidden atoms agree after the same operations. -/
theorem proj_applyOps_congr (keyInv : KeyInvariant hide) {left right : List Atom}
    (agree : proj hide left = proj hide right) (ops : List SpaceOp) :
    proj hide (applyOps left ops) = proj hide (applyOps right ops) := by
  rw [proj_applyOps keyInv ops left, proj_applyOps keyInv ops right, agree]

/-- Whether a hidden key is present after some operations depends monotonically on whether it
was present before, and on nothing else. -/
theorem contains_applyOps_mono (keyInv : KeyInvariant hide) (watched : Atom) (hidden : hide watched = true) :
    ∀ (ops : List SpaceOp) {left right : List Atom},
      proj hide left = proj hide right →
      (morkSupportContains right watched = true → morkSupportContains left watched = true) →
      morkSupportContains (applyOps right ops) watched = true →
        morkSupportContains (applyOps left ops) watched = true
  | [], _, _, _, mono, present => mono present
  | op :: rest, left, right, agree, mono, present => by
      simp only [applyOps, List.foldl_cons] at present ⊢
      have stepAgree : proj hide (applyOp left op) = proj hide (applyOp right op) := by
        have congr := proj_applyOps_congr keyInv agree [op]
        simpa only [applyOps, List.foldl_cons, List.foldl_nil] using congr
      refine contains_applyOps_mono keyInv watched hidden rest stepAgree ?_ present
      intro presentRight
      cases op with
      | ins atom =>
          simp only [applyOp] at presentRight ⊢
          rw [morkSupportContains_eq_true_iff_key_mem] at presentRight ⊢
          unfold morkInsertSupport at presentRight ⊢
          by_cases same : morkSupportKey atom = morkSupportKey watched
          · split
            · rename_i containsLeft
              rw [morkSupportContains_eq_true_iff_key_mem, same] at containsLeft
              exact containsLeft
            · simp [same]
          · have unchangedRight : morkSupportKey watched ∈ right.map morkSupportKey := by
              split at presentRight
              · exact presentRight
              · simp only [List.map_append, List.mem_append, List.map_cons, List.map_nil,
                  List.mem_singleton] at presentRight
                rcases presentRight with inRight | equal
                · exact inRight
                · exact absurd equal.symm same
            have inLeft := (morkSupportContains_eq_true_iff_key_mem _ _).1
              (mono ((morkSupportContains_eq_true_iff_key_mem _ _).2 unchangedRight))
            split
            · exact inLeft
            · simp [inLeft]
      | del atom =>
          simp only [applyOp] at presentRight ⊢
          rw [morkSupportContains_eq_true_iff_key_mem] at presentRight ⊢
          simp only [morkEraseSupport, List.mem_map, List.mem_filter] at presentRight ⊢
          obtain ⟨other, ⟨otherMember, distinct⟩, sameKey⟩ := presentRight
          have inLeft := (morkSupportContains_eq_true_iff_key_mem _ _).1
            (mono ((morkSupportContains_eq_true_iff_key_mem _ _).2 (List.mem_map.2 ⟨other, otherMember, sameKey⟩)))
          obtain ⟨leftOther, leftMember, leftKey⟩ := List.mem_map.1 inLeft
          refine ⟨leftOther, ⟨leftMember, ?_⟩, leftKey⟩
          simp only [sameMorkSupportAtom, Bool.not_eq_true', decide_eq_false_iff_not] at distinct ⊢
          rw [leftKey, ← sameKey]
          exact distinct

end Hidden

/-! ## Selection, rows and steps under projection -/

theorem lexLt_total_of_ne : ∀ (a b : List ℕ), a ≠ b → lexLt a b = false → lexLt b a = true
  | [], [], distinct, _ => absurd rfl distinct
  | [], _ :: _, _, below => by simp [lexLt] at below
  | _ :: _, [], _, _ => rfl
  | x :: xs, y :: ys, distinct, below => by
      unfold lexLt at below ⊢
      by_cases lt : x < y
      · simp [lt] at below
      · by_cases gt : y < x
        · simp [gt]
        · have equal : x = y := by omega
          subst equal
          simp only [lt, if_false] at below ⊢
          exact lexLt_total_of_ne xs ys (fun same => distinct (by rw [same])) below

/-- A compact key starts with a byte. -/
theorem compactKey_head {atom : Atom} {key : List ℕ} (encoded : morkCompactKey? atom = some key) :
    ∃ first rest, key = first :: rest ∧ first < 256 := by
  unfold morkCompactKey? at encoded
  obtain ⟨⟨bytes, environment⟩, encodedAtom, rfl⟩ := Option.map_eq_some_iff.mp encoded
  cases atom with
  | expression children =>
      have short : children.length < 64 := by
        simp only [morkCompactEncodeAtom] at encodedAtom
        split_ifs at encodedAtom with bound
        · exact bound
      obtain ⟨tail, _, equal⟩ := encode_expression encodedAtom
      exact ⟨children.length, tail, equal, by omega⟩
  | grounded _ => simp [morkCompactEncodeAtom] at encodedAtom
  | symbol name =>
      simp only [morkCompactEncodeAtom] at encodedAtom
      split_ifs at encodedAtom with bounds
      simp only [Option.some.injEq, Prod.mk.injEq] at encodedAtom
      exact ⟨_, _, encodedAtom.1.symm, by omega⟩
  | var name =>
      simp only [morkCompactEncodeAtom] at encodedAtom
      split at encodedAtom
      · split_ifs at encodedAtom with bound
        simp only [Option.some.injEq, Prod.mk.injEq] at encodedAtom
        exact ⟨_, _, encodedAtom.1.symm, by omega⟩
      · split_ifs at encodedAtom
        simp only [Option.some.injEq, Prod.mk.injEq] at encodedAtom
        exact ⟨_, _, encodedAtom.1.symm, by omega⟩

/-- Equal total keys with a representable side are equal physical keys. -/
theorem supportKey_eq_of_totalKey_eq {left right : Atom} {key : List ℕ}
    (representable : morkCompactKey? right = some key)
    (same : totalMorkCompactKey left = totalMorkCompactKey right) :
    morkSupportKey left = morkSupportKey right := by
  unfold totalMorkCompactKey at same
  rw [representable, Option.getD_some] at same
  cases leftKey : morkCompactKey? left with
  | none =>
      rw [leftKey, Option.getD_none] at same
      obtain ⟨first, rest, keyEq, small⟩ := compactKey_head representable
      rw [keyEq] at same
      injection same with headEq
      omega
  | some k =>
      rw [leftKey, Option.getD_some] at same
      simp [morkSupportKey, leftKey, representable, same]

section HiddenSteps

variable {hide : Atom → Bool}

theorem rawFact_atom {space : List Atom} {raw : RawExecFact}
    (member : raw ∈ WQComputable.cRawExecFacts space) :
    raw.atom ∈ space ∧ extractRawExecFact raw.atom = some raw := by
  obtain ⟨atom, atomMember, extracted⟩ := List.mem_filterMap.1 member
  have atomEq := extractRawExecFact_atom_eq extracted
  rw [atomEq]
  exact ⟨atomMember, extracted⟩

/-- **A visible least executable stays least when hidden atoms are projected away.** -/
theorem select_proj {space : List Atom} {raw : RawExecFact} (nodup : MorkSupportNodup space)
    (selected : selectNextScheduled (WQComputable.cRawExecFacts space) = some raw)
    (visible : hide raw.atom = false) {key : List ℕ} (representable : morkCompactKey? raw.atom = some key) :
    selectNextScheduled (WQComputable.cRawExecFacts (proj hide space)) = some raw := by
  obtain ⟨atomMember, extracted⟩ := rawFact_atom (selectNextScheduled_mem selected)
  apply selectNextScheduled_eq_some_of_mem_of_strict_minimum
  · exact List.mem_filterMap.2 ⟨raw.atom, List.mem_filter.2 ⟨atomMember, by simp [visible]⟩, extracted⟩
  · intro candidate candidateMember distinct
    obtain ⟨candidateAtomMember, candidateExtracted⟩ := rawFact_atom candidateMember
    have inSpace : candidate ∈ WQComputable.cRawExecFacts space :=
      List.mem_filterMap.2 ⟨candidate.atom, (List.mem_filter.1 candidateAtomMember).1, candidateExtracted⟩
    have notBelow := selectNextScheduled_least selected candidate inSpace
    apply lexLt_total_of_ne _ _ _ notBelow
    intro sameKey
    change totalMorkCompactKey candidate.atom = totalMorkCompactKey raw.atom at sameKey
    have physical := supportKey_eq_of_totalKey_eq representable sameKey
    have atomsEq := List.inj_on_of_nodup_map nodup (List.mem_filter.1 candidateAtomMember).1
      atomMember physical
    apply distinct
    have := candidateExtracted
    rw [atomsEq, extracted] at this
    exact (Option.some.inj this).symm

theorem filterMap_proj {β : Type} (f : Atom → Option β)
    (noneOfHidden : ∀ atom, hide atom = true → f atom = none) :
    ∀ space : List Atom, space.filterMap f = (proj hide space).filterMap f
  | [] => rfl
  | atom :: rest => by
      have restEq := filterMap_proj f noneOfHidden rest
      cases hidden : hide atom with
      | true =>
          simp only [proj, List.filter_cons, hidden, Bool.not_true, Bool.false_eq_true, if_false,
            List.filterMap_cons, noneOfHidden atom hidden]
          exact restEq
      | false =>
          simp only [proj, List.filter_cons, hidden, Bool.not_false, if_true, List.filterMap_cons]
          rw [restEq]
          rfl

theorem conjunctionRows_proj (tag : ℕ → String) :
    ∀ (patterns : List Atom), (∀ pattern ∈ patterns, ∀ atom, hide atom = true → ∀ θ index,
        unifyOption θ [(pattern, renameApart (tag index) atom)] = none) →
      ∀ (space : List Atom) (index : ℕ) (θ : Subst),
        conjunctionRows tag space index θ patterns = conjunctionRows tag (proj hide space) index θ patterns
  | [], _, _, _, _ => rfl
  | pattern :: rest, clash, space, index, θ => by
      simp only [conjunctionRows]
      rw [filterMap_proj (fun stored => unifyOption θ [(pattern, renameApart (tag index) stored)])
        (fun atom hidden => clash pattern List.mem_cons_self atom hidden θ index) space]
      congr 1
      funext next
      exact conjunctionRows_proj tag rest (fun other member => clash other (List.mem_cons_of_mem _ member))
        space (index + 1) next

/-- Two steps that fired the same directive with the same effect, or aborted alike. -/
def StepAgree (left right : List Atom) (raw : RawExecFact) : StepOutcome → StepOutcome → Prop
  | .next leftAfter leftExternal, .next rightAfter rightExternal =>
      leftExternal = rightExternal ∧ ∃ ops : List SpaceOp,
        leftAfter = applyOps (morkEraseSupport left raw.atom) ops ∧
          rightAfter = applyOps (morkEraseSupport right raw.atom) ops
  | .aborted leftFault, .aborted rightFault => leftFault = rightFault
  | _, _ => False

theorem decodeDirective_atom {profile : BuildProfile} {raw : RawExecFact} {directive : MainlineDirective}
    (decoded : decodeDirective profile raw = .ok (some directive)) : directive.atom = raw.atom := by
  unfold decodeDirective at decoded
  split at decoded
  · rename_i input output _ _
    cases output with
    | error fault => simp [bind, Except.bind] at decoded
    | ok output =>
        cases input with
        | error fault => simp [bind, Except.bind] at decoded
        | ok input =>
            simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at decoded
            rw [← decoded]
  · simp at decoded

/-- **A step that cannot see the hidden atoms acts alike on spaces that agree outside them.** -/
theorem step_agree (keyInv : KeyInvariant hide) (profile : BuildProfile) (prims : Primitives)
    (external : ExternalState) {left right : List Atom} {raw : RawExecFact}
    (agree : proj hide left = proj hide right)
    (selLeft : selectNextScheduled (WQComputable.cRawExecFacts left) = some raw)
    (selRight : selectNextScheduled (WQComputable.cRawExecFacts right) = some raw)
    (unread : ∀ directive, decodeDirective profile raw = .ok (some directive) →
      ∀ tag read, mainlineRows prims external tag read directive.input =
        mainlineRows prims external tag (proj hide read) directive.input) :
    StepAgree left right raw (mainlineStep profile prims external left)
      (mainlineStep profile prims external right) := by
  unfold mainlineStep
  rw [selLeft, selRight]
  dsimp only
  cases decoded : decodeDirective profile raw with
  | error fault => simp [StepAgree]
  | ok result =>
      cases result with
      | none => simp only [StepAgree, true_and]; exact ⟨[], rfl, rfl⟩
      | some directive =>
          dsimp only
          have atomEq := decodeDirective_atom decoded
          obtain ⟨effect, effectOn⟩ := fireDirective_effect prims external directive
          rw [effectOn left, effectOn right]
          have readAgree : proj hide (morkInsertSupport (morkEraseSupport left directive.atom) directive.atom) =
              proj hide (morkInsertSupport (morkEraseSupport right directive.atom) directive.atom) := by
            rw [proj_insert keyInv, proj_insert keyInv (morkEraseSupport right directive.atom),
              proj_erase, proj_erase right, agree]
          have rowsAgree := unread directive decoded (factorTag directive.atom)
          rw [rowsAgree (morkInsertSupport (morkEraseSupport left directive.atom) directive.atom),
            rowsAgree (morkInsertSupport (morkEraseSupport right directive.atom) directive.atom), readAgree]
          cases mainlineRows prims external (factorTag directive.atom)
              (proj hide (morkInsertSupport (morkEraseSupport right directive.atom) directive.atom))
              directive.input with
          | error fault => simp [StepAgree]
          | ok solved =>
              dsimp only
              cases effect solved with
              | error fault => simp [StepAgree, Effect.on, Except.map]
              | ok result =>
                  obtain ⟨ops, after⟩ := result
                  simp only [Effect.on, Except.map, StepAgree, true_and]
                  exact ⟨ops, by rw [atomEq], by rw [atomEq]⟩

end HiddenSteps

/-! ## Below the watcher, nothing reads an atom of arity three or more -/

theorem encode_expression_short {environment : List String} {children : List Atom}
    {result : List ℕ × List String}
    (encoded : morkCompactEncodeAtom environment (.expression children) = some result) :
    children.length < 64 := by
  simp only [morkCompactEncodeAtom] at encoded
  split_ifs at encoded with bound
  · exact bound

/-- An atom with the physical key of an expression is an expression of the same length. -/
theorem expression_of_same_key {atom : Atom} {children : List Atom}
    (same : morkSupportKey atom = morkSupportKey (.expression children)) :
    ∃ others, atom = .expression others ∧ others.length = children.length := by
  unfold morkSupportKey at same
  cases expressionKey : morkCompactKey? (.expression children) with
  | none =>
      rw [expressionKey] at same
      cases atomKey : morkCompactKey? atom with
      | none =>
          rw [atomKey] at same
          injection same with equal
          exact ⟨children, equal, rfl⟩
      | some k => rw [atomKey] at same; cases same
  | some key =>
      rw [expressionKey] at same
      cases atomKey : morkCompactKey? atom with
      | none => rw [atomKey] at same; cases same
      | some k =>
          rw [atomKey] at same
          injection same with keyEq
          subst keyEq
          unfold morkCompactKey? at expressionKey atomKey
          obtain ⟨⟨expressionBytes, _⟩, expressionEncoded, expressionEq⟩ :=
            Option.map_eq_some_iff.mp expressionKey
          obtain ⟨expressionTail, _, expressionBytesEq⟩ := encode_expression expressionEncoded
          have short := encode_expression_short expressionEncoded
          obtain ⟨⟨atomBytes, _⟩, atomEncoded, atomEq⟩ := Option.map_eq_some_iff.mp atomKey
          simp only at expressionEq atomEq expressionBytesEq
          have bytesSame : atomBytes = expressionBytes := atomEq.trans expressionEq.symm
          cases atom with
          | expression others =>
              obtain ⟨atomTail, _, atomBytesEq⟩ := encode_expression atomEncoded
              simp only at atomBytesEq
              rw [atomBytesEq, expressionBytesEq] at bytesSame
              injection bytesSame with lengthEq
              exact ⟨others, rfl, lengthEq⟩
          | _ =>
              obtain ⟨first, rest, atomBytesEq, large⟩ :=
                encode_head_ge_of_not_expression atomEncoded (by intro children; simp)
              rw [atomBytesEq, expressionBytesEq] at bytesSame
              injection bytesSame with headEq
              omega

/-- **Expressions of different lengths never unify.** -/
theorem unifyOption_length_clash (θ : Subst) (tag : String) {patterns children : List Atom}
    (different : patterns.length ≠ children.length) :
    unifyOption θ [(.expression patterns, renameApart tag (.expression children))] = none := by
  unfold unifyOption unifyUnder renameApart
  simp only [List.map_cons, List.map_nil, applySubst]
  generalize (equationsVars [(Atom.expression (applySubst.applySubstList θ patterns),
    Atom.expression (applySubst.applySubstList θ (applySubst.applySubstList
      ((atomFreeVars (.expression children)).map fun name => (name, Atom.var (tag ++ name))) children)))]).length = budget
  have lengths : (applySubst.applySubstList θ patterns).length ≠
      (applySubst.applySubstList θ (applySubst.applySubstList
        ((atomFreeVars (.expression children)).map fun name => (name, Atom.var (tag ++ name))) children)).length := by
    simp only [applySubstList_length]
    exact different
  have notEqual : Atom.expression (applySubst.applySubstList θ patterns) ≠
      Atom.expression (applySubst.applySubstList θ (applySubst.applySubstList
        ((atomFreeVars (.expression children)).map fun name => (name, Atom.var (tag ++ name))) children)) := by
    intro equal
    injection equal with listsEq
    exact lengths (by rw [listsEq])
  cases budget with
  | zero => simp [solveEquations, solveWithin, notEqual, lengths]
  | succ budget => simp [solveEquations, solveWithin, notEqual, lengths]

/-- **Below the watcher an executable has at most one conjunct of arity at most two, or the
empty product.** -/
theorem decode_below_watcher (profile : BuildProfile) {raw : RawExecFact}
    (extracted : extractRawExecFact raw.atom = some raw)
    (below : lexLt (totalMorkCompactKey raw.atom) (totalMorkCompactKey watcherExec) = true)
    {directive : MainlineDirective} (decoded : decodeDirective profile raw = .ok (some directive)) :
    (∃ patterns, directive.input = .compat patterns ∧
        ∀ pattern ∈ patterns, ∃ children, pattern = .expression children ∧ children.length ≤ 2) ∨
      directive.input = .explicit [] := by
  obtain ⟨atom, loc, inputExpr, templateExpr⟩ := raw
  have shape : atom = .expression [.symbol "exec", loc, inputExpr, templateExpr] := by
    unfold extractRawExecFact at extracted
    split at extracted
    · rename_i matchedLoc matchedInput matchedTemplate shapeEq
      simp only [Option.some.injEq, RawExecFact.mk.injEq, true_and] at extracted
      obtain ⟨rfl, rfl, rfl⟩ := extracted
      exact shapeEq
    · cases extracted
  simp only at below
  subst shape
  -- The input decodes.
  unfold decodeDirective at decoded
  simp only at decoded
  cases inputDecoded : decodeInput profile inputExpr with
  | none => rw [inputDecoded] at decoded; split at decoded <;> simp_all
  | some inputResult =>
  cases outputDecoded : decodeOutput profile (kernelOutput loc inputExpr templateExpr) with
  | none => rw [inputDecoded, outputDecoded] at decoded; simp at decoded
  | some outputResult =>
  rw [inputDecoded, outputDecoded] at decoded
  cases outputResult with
  | error fault => simp [bind, Except.bind] at decoded
  | ok output =>
  cases inputResult with
  | error fault => simp [bind, Except.bind] at decoded
  | ok input =>
  simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at decoded
  subst decoded
  simp only
  -- Read the key.
  rw [watcherKey] at below
  unfold totalMorkCompactKey at below
  cases key : morkCompactKey? (.expression [.symbol "exec", loc, inputExpr, templateExpr]) with
  | none => rw [key] at below; simp [lexLt_cons] at below
  | some k =>
  rw [key, Option.getD_some] at below
  unfold morkCompactKey? at key
  obtain ⟨⟨bytes, environment⟩, encoded, rfl⟩ := Option.map_eq_some_iff.mp key
  obtain ⟨tail₀, list₀, bytesEq⟩ := encode_expression encoded
  simp only at bytesEq
  subst bytesEq
  obtain ⟨b₁, e₁, t₁, encExec, list₁, tail₀Eq⟩ := encodeList_cons list₀
  rw [encode_exec_symbol] at encExec
  simp only [Option.some.injEq, Prod.mk.injEq] at encExec
  obtain ⟨rfl, rfl⟩ := encExec
  subst tail₀Eq
  obtain ⟨b₂, e₂, t₂, encLoc, list₂, t₁Eq⟩ := encodeList_cons list₁
  subst t₁Eq
  rw [show (List.length [Atom.symbol "exec", loc, inputExpr, templateExpr]) :: ([196, 101, 120, 101, 99] ++
      (b₂ ++ t₂)) = [4, 196, 101, 120, 101, 99] ++ (b₂ ++ t₂) from rfl,
    show ([4, 196, 101, 120, 101, 99, 0, 2, 193, 44, 2, 193, 103, 192, 2, 193, 79, 2, 193, 43, 2, 195,
      111, 117, 116, 128] : List ℕ) = [4, 196, 101, 120, 101, 99] ++
      [0, 2, 193, 44, 2, 193, 103, 192, 2, 193, 79, 2, 193, 43, 2, 195, 111, 117, 116, 128] from rfl,
    lexLt_append_left] at below
  -- The location is `()`.
  have locUnit : loc = .expression [] ∧ b₂ = [0] ∧ e₂ = [] := by
    cases loc with
    | expression children =>
        obtain ⟨tailLoc, listLoc, b₂Eq⟩ := encode_expression encLoc
        simp only at b₂Eq listLoc
        subst b₂Eq
        cases children with
        | nil =>
            simp only [morkCompactEncodeAtom.encodeList, Option.some.injEq, Prod.mk.injEq] at listLoc
            obtain ⟨rfl, rfl⟩ := listLoc
            exact ⟨rfl, rfl, rfl⟩
        | cons child more => simp [lexLt_cons] at below
    | _ =>
        obtain ⟨first, more, b₂Eq, large⟩ :=
          encode_head_ge_of_not_expression encLoc (by intro children; simp)
        subst b₂Eq
        have : (0 : ℕ) < first := by omega
        simp [lexLt_cons, this] at below
  obtain ⟨rfl, rfl, rfl⟩ := locUnit
  simp only [List.cons_append, List.nil_append, lexLt_cons, Nat.lt_irrefl, gt_iff_lt,
    ↓reduceIte] at below
  -- The input expression.
  obtain ⟨b₃, e₃, t₃, encInput, list₃, t₂Eq⟩ := encodeList_cons list₂
  subst t₂Eq
  cases inputExpr with
  | expression parts =>
      obtain ⟨tailInput, listInput, b₃Eq⟩ := encode_expression encInput
      simp only at b₃Eq listInput
      subst b₃Eq
      cases parts with
      | nil => simp [decodeInput] at inputDecoded
      | cons head rest =>
          cases rest with
          | nil =>
              -- `(h)`: the empty conjunction or the empty product.
              cases head with
              | symbol name =>
                  by_cases comma : name = ","
                  · subst comma
                    simp only [decodeInput, Option.some.injEq, Except.ok.injEq] at inputDecoded
                    subst inputDecoded
                    exact Or.inl ⟨[], rfl, by simp⟩
                  · by_cases product : name = "I"
                    · subst product
                      simp only [decodeInput, decodeAll, Except.map, Option.some.injEq,
                        Except.ok.injEq] at inputDecoded
                      subst inputDecoded
                      exact Or.inr rfl
                    · simp [decodeInput, comma, product] at inputDecoded
              | _ => simp [decodeInput] at inputDecoded
          | cons pattern more =>
              cases more with
              | cons another others =>
                  simp [List.cons_append, lexLt_cons] at below
              | nil =>
                  obtain ⟨bHead, eHead, tHead, encHead, listPattern, tailInputEq⟩ := encodeList_cons listInput
                  subst tailInputEq
                  obtain ⟨bPattern, ePattern, tPattern, encPattern, _, tHeadEq⟩ := encodeList_cons listPattern
                  subst tHeadEq
                  simp only [List.length_cons, List.length_nil, List.cons_append,
                    List.append_assoc, lexLt_cons, Nat.lt_irrefl, gt_iff_lt, ↓reduceIte] at below
                  cases head with
                  | symbol name =>
                      simp only [morkCompactEncodeAtom] at encHead
                      split_ifs at encHead with bounds
                      simp only [Option.some.injEq, Prod.mk.injEq] at encHead
                      obtain ⟨rfl, rfl⟩ := encHead
                      by_cases comma : name = ","
                      · subst comma
                        simp only [decodeInput, Option.some.injEq, Except.ok.injEq] at inputDecoded
                        subst inputDecoded
                        refine Or.inl ⟨[pattern], rfl, ?_⟩
                        intro member memberIn
                        simp only [List.mem_singleton] at memberIn
                        subst memberIn
                        simp only [show morkUtf8Bytes "," = [44] from rfl, List.map_cons, List.map_nil,
                          List.length_singleton, List.cons_append, List.nil_append, lexLt_cons,
                          Nat.lt_irrefl, gt_iff_lt, ↓reduceIte] at below
                        cases member with
                        | expression children =>
                            obtain ⟨tailPattern, _, bPatternEq⟩ := encode_expression encPattern
                            simp only at bPatternEq
                            subst bPatternEq
                            refine ⟨children, rfl, ?_⟩
                            by_contra large
                            have : 2 < children.length := by omega
                            simp [List.cons_append, lexLt_cons, this] at below
                            omega
                        | _ =>
                            obtain ⟨first, rest, bEq, large⟩ :=
                              encode_head_ge_of_not_expression encPattern (by intro children; simp)
                            subst bEq
                            have : (2 : ℕ) < first := by omega
                            simp [List.cons_append, lexLt_cons, this] at below
                            omega
                      · by_cases product : name = "I"
                        · subst product
                          simp [show morkUtf8Bytes "I" = [73] from rfl, lexLt_cons] at below
                        · simp [decodeInput, comma, product] at inputDecoded
                  | _ => simp [decodeInput] at inputDecoded
  | _ => simp [decodeInput] at inputDecoded

/-! ## The window's hidden atoms -/

/-- The atoms with the physical key of `target`. -/
def keyOf (target : Atom) (atom : Atom) : Bool := sameMorkSupportAtom atom target

theorem keyOf_keyInvariant (target : Atom) : KeyInvariant (keyOf target) := by
  intro x y same
  simp [keyOf, sameMorkSupportAtom, same]

theorem keyOf_wide {target : Atom} {children : List Atom} (shape : target = .expression children)
    (large : 3 ≤ children.length) :
    ∀ atom, keyOf target atom = true → ∃ others, atom = .expression others ∧ 3 ≤ others.length := by
  intro atom hidden
  simp only [keyOf, sameMorkSupportAtom, decide_eq_true_eq] at hidden
  subst shape
  obtain ⟨others, rfl, len⟩ := expression_of_same_key hidden
  exact ⟨others, rfl, by omega⟩

theorem watcher_wide : ∀ atom, keyOf watcherExec atom = true →
    ∃ others, atom = .expression others ∧ 3 ≤ others.length :=
  keyOf_wide (children := [.symbol "exec", .expression [], .expression [.symbol ",", gPattern],
    .expression [.symbol "O", .expression [.symbol "+", outOf (.var "z")]]]) rfl (by decide)

theorem equation_wide (value : Atom) : ∀ atom, keyOf (equationOf value) atom = true →
    ∃ others, atom = .expression others ∧ 3 ≤ others.length :=
  keyOf_wide (children := [.symbol "=", .expression [.symbol "f", .symbol "a"], value]) rfl (by simp)

/-- **Below the watcher no input reads an atom of arity three or more.** -/
theorem unread_below_watcher (profile : BuildProfile) (prims : Primitives) (external : ExternalState)
    {hide : Atom → Bool}
    (wide : ∀ atom, hide atom = true → ∃ others, atom = .expression others ∧ 3 ≤ others.length)
    {raw : RawExecFact} (extracted : extractRawExecFact raw.atom = some raw)
    (below : lexLt (totalMorkCompactKey raw.atom) (totalMorkCompactKey watcherExec) = true) :
    ∀ directive, decodeDirective profile raw = .ok (some directive) →
      ∀ tag read, mainlineRows prims external tag read directive.input =
        mainlineRows prims external tag (proj hide read) directive.input := by
  intro directive decoded tag read
  rcases decode_below_watcher profile extracted below decoded with ⟨patterns, inputEq, short⟩ | inputEq
  · rw [inputEq]
    simp only [mainlineRows]
    rw [conjunctionRows_proj tag patterns (by
      intro pattern member atom hidden θ index
      obtain ⟨children, rfl, small⟩ := short pattern member
      obtain ⟨others, rfl, large⟩ := wide atom hidden
      exact unifyOption_length_clash θ _ (by omega)) read 0 []]
  · rw [inputEq]
    rfl

/-- Hidden atoms that are not executables do not change the executables. -/
theorem rawFacts_proj_of_inert {hide : Atom → Bool}
    (inert : ∀ atom, hide atom = true → extractRawExecFact atom = none) (space : List Atom) :
    WQComputable.cRawExecFacts (proj hide space) = WQComputable.cRawExecFacts space := by
  unfold WQComputable.cRawExecFacts
  exact (filterMap_proj extractRawExecFact inert space).symm

theorem equation_inert (value : Atom) : ∀ atom, keyOf (equationOf value) atom = true →
    extractRawExecFact atom = none := by
  intro atom hidden
  simp only [keyOf, sameMorkSupportAtom, decide_eq_true_eq] at hidden
  unfold equationOf at hidden
  obtain ⟨others, rfl, len⟩ := expression_of_same_key hidden
  unfold extractRawExecFact
  split
  · rename_i loc input template shapeEq
    injection shapeEq with listEq
    rw [listEq] at len
    simp at len
  · rfl

/-- **A visible least executable of the hidden-free part is least overall** when every hidden
executable is above it. -/
theorem select_of_proj {hide : Atom → Bool} {space : List Atom} {raw : RawExecFact}
    (nodup : MorkSupportNodup space)
    (selected : selectNextScheduled (WQComputable.cRawExecFacts (proj hide space)) = some raw)
    (above : ∀ other ∈ WQComputable.cRawExecFacts space, hide other.atom = true →
      lexLt (totalMorkCompactKey raw.atom) (totalMorkCompactKey other.atom) = true)
    {key : List ℕ} (representable : morkCompactKey? raw.atom = some key) :
    selectNextScheduled (WQComputable.cRawExecFacts space) = some raw := by
  obtain ⟨projMember, extracted⟩ := rawFact_atom (selectNextScheduled_mem selected)
  apply selectNextScheduled_eq_some_of_mem_of_strict_minimum
  · exact List.mem_filterMap.2 ⟨raw.atom, (List.mem_filter.1 projMember).1, extracted⟩
  · intro candidate candidateMember distinct
    obtain ⟨candidateAtomMember, candidateExtracted⟩ := rawFact_atom candidateMember
    cases hidden : hide candidate.atom with
    | true => exact above candidate candidateMember hidden
    | false =>
        have inProj : candidate ∈ WQComputable.cRawExecFacts (proj hide space) :=
          List.mem_filterMap.2 ⟨candidate.atom, List.mem_filter.2 ⟨candidateAtomMember, by simp [hidden]⟩,
            candidateExtracted⟩
        have notBelow := selectNextScheduled_least selected candidate inProj
        apply lexLt_total_of_ne _ _ _ notBelow
        intro sameKey
        change totalMorkCompactKey candidate.atom = totalMorkCompactKey raw.atom at sameKey
        have physical := supportKey_eq_of_totalKey_eq representable sameKey
        have atomsEq := List.inj_on_of_nodup_map nodup candidateAtomMember
          (List.mem_filter.1 projMember).1 physical
        apply distinct
        have := candidateExtracted
        rw [atomsEq, extracted] at this
        exact (Option.some.inj this).symm

theorem applyOps_nodup : ∀ (ops : List SpaceOp) (space : List Atom), MorkSupportNodup space →
    MorkSupportNodup (applyOps space ops)
  | [], _, nodup => nodup
  | op :: rest, space, nodup => by
      simp only [applyOps, List.foldl_cons]
      apply applyOps_nodup rest
      cases op with
      | ins atom => exact morkInsertSupport_nodup space atom nodup
      | del atom => exact morkEraseSupport_nodup space atom nodup

/-- Configurations: a space and the external state. -/
abbrev Config := List Atom × ExternalState

/-- Two configurations that agree outside the atoms with `target`'s key. -/
structure Twin (target : Atom) (left right : Config) : Prop where
  agree : proj (keyOf target) left.1 = proj (keyOf target) right.1
  external : left.2 = right.2
  nodupLeft : MorkSupportNodup left.1
  nodupRight : MorkSupportNodup right.1

/-- **One step of twins that fire the same unseeing executable keeps them twins.** -/
theorem twin_step (profile : BuildProfile) (prims : Primitives) {target : Atom} {left right : Config}
    {raw : RawExecFact} (twin : Twin target left right)
    (selLeft : selectNextScheduled (WQComputable.cRawExecFacts left.1) = some raw)
    (selRight : selectNextScheduled (WQComputable.cRawExecFacts right.1) = some raw)
    (unread : ∀ directive, decodeDirective profile raw = .ok (some directive) →
      ∀ tag read, mainlineRows prims left.2 tag read directive.input =
        mainlineRows prims left.2 tag (proj (keyOf target) read) directive.input) :
    (∃ fault, mainlineStep profile prims left.2 left.1 = .aborted fault ∧
        mainlineStep profile prims right.2 right.1 = .aborted fault) ∨
      (∃ left' right' : Config, ∃ ops : List SpaceOp,
        mainlineStep profile prims left.2 left.1 = .next left'.1 left'.2 ∧
        mainlineStep profile prims right.2 right.1 = .next right'.1 right'.2 ∧
        left'.1 = applyOps (morkEraseSupport left.1 raw.atom) ops ∧
        right'.1 = applyOps (morkEraseSupport right.1 raw.atom) ops ∧
        Twin target left' right') := by
  have agreeStep := step_agree (keyOf_keyInvariant target) profile prims left.2 twin.agree selLeft
    selRight unread
  rw [twin.external] at agreeStep ⊢
  generalize leftOutcome : mainlineStep profile prims right.2 left.1 = outcomeLeft at agreeStep
  generalize rightOutcome : mainlineStep profile prims right.2 right.1 = outcomeRight at agreeStep
  cases outcomeLeft with
  | quiescent => cases outcomeRight <;> simp [StepAgree] at agreeStep
  | aborted fault =>
      cases outcomeRight with
      | aborted fault' =>
          simp only [StepAgree] at agreeStep
          exact Or.inl ⟨fault, rfl, by rw [agreeStep]⟩
      | _ => simp [StepAgree] at agreeStep
  | next leftAfter leftExternal =>
      cases outcomeRight with
      | next rightAfter rightExternal =>
          simp only [StepAgree] at agreeStep
          obtain ⟨externalEq, ops, leftEq, rightEq⟩ := agreeStep
          refine Or.inr ⟨(leftAfter, leftExternal), (rightAfter, rightExternal), ops, rfl, rfl, leftEq,
            rightEq, ⟨?_, externalEq, ?_, ?_⟩⟩
          · simp only [leftEq, rightEq]
            apply proj_applyOps_congr (keyOf_keyInvariant target)
            rw [proj_erase, proj_erase right.1, twin.agree]
          · rw [leftEq]
            exact applyOps_nodup ops _ (morkEraseSupport_nodup _ _ twin.nodupLeft)
          · rw [rightEq]
            exact applyOps_nodup ops _ (morkEraseSupport_nodup _ _ twin.nodupRight)
      | _ => simp [StepAgree] at agreeStep

/-! ## Runs and the phase before the watcher -/

/-- The configuration after `n` steps, while every step continues. -/
def runN (profile : BuildProfile) (prims : Primitives) : ℕ → Config → Option Config
  | 0, c => some c
  | n + 1, c =>
      match mainlineStep profile prims c.2 c.1 with
      | .next space after => runN profile prims n (space, after)
      | _ => none

/-- `(out x)` is reported: present in some configuration that the run reaches. -/
def Reports (profile : BuildProfile) (prims : Primitives) (start : Config) (x : Atom) : Prop :=
  ∃ n c, runN profile prims n start = some c ∧ outOf x ∈ c.1

/-- The selected executable of a configuration is below the watcher. -/
def Below (c : Config) : Prop :=
  ∃ raw, selectNextScheduled (WQComputable.cRawExecFacts c.1) = some raw ∧
    lexLt (totalMorkCompactKey raw.atom) (totalMorkCompactKey watcherExec) = true

/-- The run with the watcher, the run without it and the expansion's own run, during the
phase: they agree outside the watcher and outside the equation, and the run without the
watcher has it only if the run with it does. -/
structure PhaseRel (value : Atom) (own withW withoutW : Config) : Prop where
  watcherTwin : Twin watcherExec withW withoutW
  equationTwin : Twin (equationOf value) withoutW own
  watcherMono : morkSupportContains withoutW.1 watcherExec = true →
    morkSupportContains withW.1 watcherExec = true

theorem watcher_representable : morkCompactKey? watcherExec = some
    [4, 196, 101, 120, 101, 99, 0, 2, 193, 44, 2, 193, 103, 192, 2, 193, 79, 2, 193, 43, 2, 195,
      111, 117, 116, 128] := by decide

theorem representable_of_below {atom : Atom}
    (below : lexLt (totalMorkCompactKey atom) (totalMorkCompactKey watcherExec) = true) :
    ∃ key, morkCompactKey? atom = some key := by
  cases encoded : morkCompactKey? atom with
  | some key => exact ⟨key, rfl⟩
  | none =>
      rw [watcherKey] at below
      unfold totalMorkCompactKey at below
      rw [encoded, Option.getD_none] at below
      simp [lexLt_cons] at below

theorem not_watcherKey_of_below {atom : Atom}
    (below : lexLt (totalMorkCompactKey atom) (totalMorkCompactKey watcherExec) = true) :
    keyOf watcherExec atom = false := by
  apply Bool.eq_false_iff.mpr
  intro same
  simp only [keyOf, sameMorkSupportAtom, decide_eq_true_eq] at same
  obtain ⟨key, encoded⟩ := representable_of_below below
  have totalEq : totalMorkCompactKey atom = totalMorkCompactKey watcherExec := by
    unfold morkSupportKey at same
    rw [encoded, watcher_representable] at same
    injection same with keyEq
    simp [totalMorkCompactKey, encoded, watcher_representable, keyEq]
  rw [totalEq, lexLt_irrefl] at below
  cases below

theorem totalKey_of_watcherKey {atom : Atom} (same : keyOf watcherExec atom = true) :
    totalMorkCompactKey atom = totalMorkCompactKey watcherExec := by
  simp only [keyOf, sameMorkSupportAtom, decide_eq_true_eq] at same
  unfold morkSupportKey at same
  rw [watcher_representable] at same
  cases encoded : morkCompactKey? atom with
  | none => rw [encoded] at same; cases same
  | some k =>
      rw [encoded] at same
      injection same with keyEq
      simp [totalMorkCompactKey, encoded, watcher_representable, keyEq]

/-- **One step during the phase**: the three runs fire the same executable, which sees neither
the watcher nor the equation, and stay related, or they all abort alike. -/
theorem phase_step (profile : BuildProfile) (prims : Primitives) (value : Atom)
    {own withW withoutW : Config} (rel : PhaseRel value own withW withoutW) (below : Below own) :
    (∃ fault, mainlineStep profile prims own.2 own.1 = .aborted fault ∧
        mainlineStep profile prims withW.2 withW.1 = .aborted fault ∧
        mainlineStep profile prims withoutW.2 withoutW.1 = .aborted fault) ∨
      (∃ own' withW' withoutW' : Config,
        mainlineStep profile prims own.2 own.1 = .next own'.1 own'.2 ∧
        mainlineStep profile prims withW.2 withW.1 = .next withW'.1 withW'.2 ∧
        mainlineStep profile prims withoutW.2 withoutW.1 = .next withoutW'.1 withoutW'.2 ∧
        PhaseRel value own' withW' withoutW') := by
  obtain ⟨raw, selOwn, rawBelow⟩ := below
  obtain ⟨key, representable⟩ := representable_of_below rawBelow
  obtain ⟨_, extracted⟩ := rawFact_atom (selectNextScheduled_mem selOwn)
  -- Selection without the watcher: the equation is not an executable.
  have selWithout : selectNextScheduled (WQComputable.cRawExecFacts withoutW.1) = some raw := by
    rw [← rawFacts_proj_of_inert (equation_inert value) withoutW.1, rel.equationTwin.agree,
      rawFacts_proj_of_inert (equation_inert value) own.1]
    exact selOwn
  -- Selection with the watcher: the watcher is above.
  have visibleW := not_watcherKey_of_below rawBelow
  have selProjWithout := select_proj rel.watcherTwin.nodupRight selWithout visibleW representable
  have selWith : selectNextScheduled (WQComputable.cRawExecFacts withW.1) = some raw := by
    apply select_of_proj rel.watcherTwin.nodupLeft (hide := keyOf watcherExec) _ _ representable
    · rw [rel.watcherTwin.agree]; exact selProjWithout
    · intro other _ hidden
      rw [totalKey_of_watcherKey hidden]
      exact rawBelow
  have unreadW := unread_below_watcher profile prims withW.2 watcher_wide extracted rawBelow
  have unreadEq := unread_below_watcher profile prims withoutW.2 (equation_wide value) extracted rawBelow
  rcases twin_step profile prims rel.equationTwin selWithout selOwn unreadEq with
    ⟨fault, abortWithout, abortOwn⟩ | ⟨withoutW', own', opsEq, stepWithout, stepOwn, _, _, twinEq'⟩
  · rcases twin_step profile prims rel.watcherTwin selWith selWithout unreadW with
      ⟨fault', abortWith, abortWithout'⟩ | ⟨_, _, _, _, stepWithout', _, _, _⟩
    · rw [abortWithout] at abortWithout'
      injection abortWithout' with faultEq
      subst faultEq
      exact Or.inl ⟨fault, abortOwn, abortWith, abortWithout⟩
    · rw [abortWithout] at stepWithout'
      cases stepWithout'
  · rcases twin_step profile prims rel.watcherTwin selWith selWithout unreadW with
      ⟨_, _, abortWithout'⟩ | ⟨withW', withoutW'', opsW, stepWith, stepWithout', withEq, withoutEq, twinW'⟩
    · rw [stepWithout] at abortWithout'
      cases abortWithout'
    · rw [stepWithout] at stepWithout'
      injection stepWithout' with spaceEq externalEq
      have sameConfig : withoutW' = withoutW'' := Prod.ext spaceEq externalEq
      subst sameConfig
      refine Or.inr ⟨own', withW', withoutW', stepOwn, stepWith, stepWithout, ⟨twinW', twinEq', ?_⟩⟩
      intro present
      rw [withEq]
      rw [withoutEq] at present
      have mono := contains_applyOps_mono (keyOf_keyInvariant watcherExec) watcherExec
        (by simp [keyOf, sameMorkSupportAtom]) (.del raw.atom :: opsW) rel.watcherTwin.agree
        rel.watcherMono
      simp only [applyOps, List.foldl_cons, applyOp] at mono
      exact mono present

/-- `runN` after one continuing step. -/
theorem runN_succ_next {profile : BuildProfile} {prims : Primitives} {c c' : Config} {n : ℕ}
    (step : mainlineStep profile prims c.2 c.1 = .next c'.1 c'.2) :
    runN profile prims (n + 1) c = runN profile prims n c' := by
  simp [runN, step]

/-- **The phase simulation**: while the expansion's own run stays below the watcher, the run
with the watcher and the run without it follow it, step for step. -/
theorem phase_simulation (profile : BuildProfile) (prims : Primitives) (value : Atom) :
    ∀ (n : ℕ) (own withW withoutW c0 : Config), PhaseRel value own withW withoutW →
      runN profile prims n own = some c0 →
      (∀ k < n, ∀ ck, runN profile prims k own = some ck → Below ck) →
      ∃ c1 c2, runN profile prims n withW = some c1 ∧ runN profile prims n withoutW = some c2 ∧
        PhaseRel value c0 c1 c2
  | 0, own, withW, withoutW, c0, rel, run, _ => by
      simp only [runN, Option.some.injEq] at run
      subst run
      exact ⟨withW, withoutW, rfl, rfl, rel⟩
  | n + 1, own, withW, withoutW, c0, rel, run, phase => by
      have belowOwn : Below own := phase 0 (Nat.succ_pos n) own rfl
      rcases phase_step profile prims value rel belowOwn with
        ⟨fault, abortOwn, _, _⟩ | ⟨own', withW', withoutW', stepOwn, stepW, stepWithout, rel'⟩
      · simp [runN, abortOwn] at run
      · rw [runN_succ_next stepOwn] at run
        rw [runN_succ_next stepW, runN_succ_next stepWithout]
        exact phase_simulation profile prims value n own' withW' withoutW' c0 rel' run
          (fun k lt ck runK => phase (k + 1) (by omega) ck (by rw [runN_succ_next stepOwn]; exact runK))

/-! ## An atom with the watcher's key is the watcher

The compact encoding is self-delimiting: the first byte of an item says whether it is an
expression (its arity), a variable reference, a new variable or a symbol (its length).
Reading the watcher's key byte by byte recovers the watcher, up to the name of its one
variable. -/

/-- The UTF-8 bytes of a symbol, as naturals. -/
abbrev symbolBytes (name : String) : List ℕ := (morkUtf8Bytes name).map UInt8.toNat

theorem encode_symbol_bytes {environment environment' : List String} {name : String} {bytes : List ℕ}
    (encoded : morkCompactEncodeAtom environment (.symbol name) = some (bytes, environment')) :
    bytes = (192 + (symbolBytes name).length) :: symbolBytes name ∧ environment' = environment ∧
      0 < (symbolBytes name).length ∧ (symbolBytes name).length < 64 := by
  simp only [morkCompactEncodeAtom] at encoded
  split_ifs at encoded with bounds
  simp only [Option.some.injEq, Prod.mk.injEq] at encoded
  exact ⟨encoded.1.symm, encoded.2.symm, bounds.1, bounds.2⟩

theorem encode_var_bytes {environment environment' : List String} {name : String} {bytes : List ℕ}
    (encoded : morkCompactEncodeAtom environment (.var name) = some (bytes, environment')) :
    (∃ index, compactVariableIndex name environment = some index ∧ bytes = [128 + index] ∧
        environment' = environment ∧ index < 64) ∨
      (compactVariableIndex name environment = none ∧ bytes = [192] ∧
        environment' = environment ++ [name]) := by
  simp only [morkCompactEncodeAtom] at encoded
  split at encoded
  · rename_i index found
    split_ifs at encoded with bound
    simp only [Option.some.injEq, Prod.mk.injEq] at encoded
    exact Or.inl ⟨index, found, encoded.1.symm, encoded.2.symm, bound⟩
  · rename_i notFound
    split_ifs at encoded
    simp only [Option.some.injEq, Prod.mk.injEq] at encoded
    exact Or.inr ⟨notFound, encoded.1.symm, encoded.2.symm⟩

/-- An item whose bytes start with a symbol tag is that symbol. -/
theorem decode_symbol {environment environment' : List String} {atom : Atom} {bytes rest tail : List ℕ}
    {first : ℕ} (length : ℕ) (encoded : morkCompactEncodeAtom environment atom = some (bytes, environment'))
    (prefixEq' : bytes ++ tail = first :: rest) (firstEq : first = 192 + length) (positive : 0 < length)
    (short : length < 64) :
    ∃ name, atom = .symbol name ∧ symbolBytes name = rest.take length ∧ tail = rest.drop length ∧
      environment' = environment := by
  subst firstEq
  have prefixEq := prefixEq'
  cases atom with
  | symbol name =>
      obtain ⟨bytesEq, envEq, _, _⟩ := encode_symbol_bytes encoded
      rw [bytesEq] at prefixEq
      simp only [List.cons_append, List.cons.injEq] at prefixEq
      obtain ⟨lengthEq, restEq⟩ := prefixEq
      have sameLength : (symbolBytes name).length = length := by omega
      refine ⟨name, rfl, ?_, ?_, envEq⟩
      · rw [← restEq, ← sameLength, List.take_left]
      · rw [← restEq, ← sameLength, List.drop_left]
  | expression children =>
      obtain ⟨childTail, _, bytesEq⟩ := encode_expression encoded
      have bound := encode_expression_short encoded
      simp only at bytesEq
      rw [bytesEq] at prefixEq
      simp only [List.cons_append, List.cons.injEq] at prefixEq
      omega
  | var name =>
      rcases encode_var_bytes encoded with ⟨index, _, bytesEq, _, small⟩ | ⟨_, bytesEq, _⟩ <;>
        · rw [bytesEq] at prefixEq
          simp only [List.cons_append, List.cons.injEq] at prefixEq
          omega
  | grounded _ => simp [morkCompactEncodeAtom] at encoded

/-- An item whose bytes start with the new-variable tag is a new variable. -/
theorem decode_newVar {environment environment' : List String} {atom : Atom} {bytes rest tail : List ℕ}
    (encoded : morkCompactEncodeAtom environment atom = some (bytes, environment'))
    (prefixEq : bytes ++ tail = 192 :: rest) :
    ∃ name, atom = .var name ∧ compactVariableIndex name environment = none ∧ tail = rest ∧
      environment' = environment ++ [name] := by
  cases atom with
  | var name =>
      rcases encode_var_bytes encoded with ⟨index, _, bytesEq, _, small⟩ | ⟨notFound, bytesEq, envEq⟩
      · rw [bytesEq] at prefixEq
        simp only [List.cons_append, List.cons.injEq] at prefixEq
        omega
      · rw [bytesEq] at prefixEq
        simp only [List.cons_append, List.nil_append, List.cons.injEq] at prefixEq
        exact ⟨name, rfl, notFound, prefixEq.2, envEq⟩
  | symbol name =>
      obtain ⟨bytesEq, _, positive, _⟩ := encode_symbol_bytes encoded
      rw [bytesEq] at prefixEq
      simp only [List.cons_append, List.cons.injEq] at prefixEq
      omega
  | expression children =>
      obtain ⟨childTail, _, bytesEq⟩ := encode_expression encoded
      have bound := encode_expression_short encoded
      simp only at bytesEq
      rw [bytesEq] at prefixEq
      simp only [List.cons_append, List.cons.injEq] at prefixEq
      omega
  | grounded _ => simp [morkCompactEncodeAtom] at encoded

/-- An item whose bytes start with a variable reference is that earlier variable. -/
theorem decode_varRef {environment environment' : List String} {atom : Atom} {bytes rest tail : List ℕ}
    {index : ℕ} (encoded : morkCompactEncodeAtom environment atom = some (bytes, environment'))
    (prefixEq : bytes ++ tail = (128 + index) :: rest) (small : index < 64) :
    ∃ name, atom = .var name ∧ compactVariableIndex name environment = some index ∧ tail = rest ∧
      environment' = environment := by
  cases atom with
  | var name =>
      rcases encode_var_bytes encoded with ⟨found, foundEq, bytesEq, envEq, _⟩ | ⟨_, bytesEq, _⟩
      · rw [bytesEq] at prefixEq
        simp only [List.cons_append, List.nil_append, List.cons.injEq] at prefixEq
        have indexEq : found = index := by omega
        subst indexEq
        exact ⟨name, rfl, foundEq, prefixEq.2, envEq⟩
      · rw [bytesEq] at prefixEq
        simp only [List.cons_append, List.cons.injEq] at prefixEq
        omega
  | symbol name =>
      obtain ⟨bytesEq, _, positive, _⟩ := encode_symbol_bytes encoded
      rw [bytesEq] at prefixEq
      simp only [List.cons_append, List.cons.injEq] at prefixEq
      omega
  | expression children =>
      obtain ⟨childTail, _, bytesEq⟩ := encode_expression encoded
      have bound := encode_expression_short encoded
      simp only at bytesEq
      rw [bytesEq] at prefixEq
      simp only [List.cons_append, List.cons.injEq] at prefixEq
      omega
  | grounded _ => simp [morkCompactEncodeAtom] at encoded

/-- An item whose bytes start with an arity is an expression of that arity. -/
theorem decode_expression {environment environment' : List String} {atom : Atom} {bytes rest tail : List ℕ}
    {arity : ℕ} (encoded : morkCompactEncodeAtom environment atom = some (bytes, environment'))
    (prefixEq : bytes ++ tail = arity :: rest) (small : arity < 64) :
    ∃ children childBytes, atom = .expression children ∧ children.length = arity ∧
      morkCompactEncodeAtom.encodeList environment children = some (childBytes, environment') ∧
      childBytes ++ tail = rest := by
  cases atom with
  | expression children =>
      obtain ⟨childBytes, list, bytesEq⟩ := encode_expression encoded
      simp only at bytesEq list
      rw [bytesEq] at prefixEq
      simp only [List.cons_append, List.cons.injEq] at prefixEq
      exact ⟨children, childBytes, rfl, prefixEq.1, list, prefixEq.2⟩
  | symbol name =>
      obtain ⟨bytesEq, _, _, _⟩ := encode_symbol_bytes encoded
      rw [bytesEq] at prefixEq
      simp only [List.cons_append, List.cons.injEq] at prefixEq
      omega
  | var name =>
      rcases encode_var_bytes encoded with ⟨index, _, bytesEq, _, _⟩ | ⟨_, bytesEq, _⟩ <;>
        · rw [bytesEq] at prefixEq
          simp only [List.cons_append, List.cons.injEq] at prefixEq
          omega
  | grounded _ => simp [morkCompactEncodeAtom] at encoded

theorem encodeList_nil {environment environment' : List String} {bytes : List ℕ}
    (encoded : morkCompactEncodeAtom.encodeList environment [] = some (bytes, environment')) :
    bytes = [] ∧ environment' = environment := by
  simp only [morkCompactEncodeAtom.encodeList, Option.some.injEq, Prod.mk.injEq] at encoded
  exact ⟨encoded.1.symm, encoded.2.symm⟩

/-- Split the encoding of a list of children: the first child's bytes, then the rest's. -/
theorem encodeList_split {environment environment' : List String} {child : Atom} {children : List Atom}
    {bytes tail : List ℕ}
    (encoded : morkCompactEncodeAtom.encodeList environment (child :: children) = some (bytes, environment')) :
    ∃ first environment₁ others,
      morkCompactEncodeAtom environment child = some (first, environment₁) ∧
      morkCompactEncodeAtom.encodeList environment₁ children = some (others, environment') ∧
      bytes ++ tail = first ++ (others ++ tail) := by
  obtain ⟨first, environment₁, others, encChild, encRest, bytesEq⟩ := encodeList_cons encoded
  simp only at bytesEq encRest
  exact ⟨first, environment₁, others, encChild, encRest, by rw [bytesEq, List.append_assoc]⟩

theorem exists_of_length_four {α : Type} : ∀ {items : List α}, items.length = 4 →
    ∃ a b c d, items = [a, b, c, d]
  | [a, b, c, d], _ => ⟨a, b, c, d, rfl⟩

theorem exists_of_length_two {α : Type} : ∀ {items : List α}, items.length = 2 → ∃ a b, items = [a, b]
  | [a, b], _ => ⟨a, b, rfl⟩

/-- The watcher with its variable named `name`. -/
def watcherWith (name : String) : Atom :=
  .expression [.symbol "exec", .expression [],
    .expression [.symbol ",", .expression [.symbol "g", .var name]],
    .expression [.symbol "O", .expression [.symbol "+", outOf (.var name)]]]

theorem watcherExec_eq : watcherExec = watcherWith "z" := rfl

theorem symbol_of_bytes {name : String} {expected : String} (bytesEq : symbolBytes name = symbolBytes expected) :
    name = expected := morkUtf8NatBytes_injective bytesEq

/-- **An atom with the watcher's key is the watcher, up to the name of its variable.** -/
theorem watcherKey_inversion {atom : Atom} (same : keyOf watcherExec atom = true) :
    ∃ name, atom = watcherWith name := by
  have key : morkCompactKey? atom = some
      [4, 196, 101, 120, 101, 99, 0, 2, 193, 44, 2, 193, 103, 192, 2, 193, 79, 2, 193, 43, 2, 195,
        111, 117, 116, 128] := by
    simp only [keyOf, sameMorkSupportAtom, decide_eq_true_eq] at same
    unfold morkSupportKey at same
    rw [watcher_representable] at same
    cases encoded : morkCompactKey? atom with
    | none => rw [encoded] at same; cases same
    | some k => rw [encoded] at same; injection same with keyEq; rw [keyEq]
  clear same
  unfold morkCompactKey? at key
  obtain ⟨⟨bytes, environment⟩, encoded, bytesEq⟩ := Option.map_eq_some_iff.mp key
  simp only at bytesEq
  subst bytesEq
  clear key
  -- the exec expression
  obtain ⟨parts, partBytes, rfl, partsLength, partsEncoded, partsEq⟩ :=
    decode_expression (tail := []) (arity := 4)
      (rest := [196, 101, 120, 101, 99, 0, 2, 193, 44, 2, 193, 103, 192, 2, 193, 79, 2, 193, 43, 2, 195,
        111, 117, 116, 128]) encoded rfl (by decide)
  clear encoded
  simp only [List.append_nil] at partsEq
  subst partsEq
  obtain ⟨execSymbol, location, input, output, rfl⟩ := exists_of_length_four partsLength
  -- `exec`
  obtain ⟨b₁, e₁, r₁, enc₁, list₁, split₁⟩ := encodeList_split (tail := []) partsEncoded
  simp only [List.append_nil] at split₁
  obtain ⟨execName, rfl, execBytes, tail₁, env₁⟩ := decode_symbol 4 enc₁ split₁.symm rfl (by decide) (by decide)
  have execEq : execName = "exec" := symbol_of_bytes (by rw [execBytes]; rfl)
  subst execEq env₁
  -- `()`
  obtain ⟨b₂, e₂, r₂, enc₂, list₂, split₂⟩ := encodeList_split (tail := []) list₁
  simp only [List.append_nil] at split₂ tail₁
  rw [tail₁] at split₂
  obtain ⟨locChildren, locBytes, rfl, locLength, locEncoded, locSplit⟩ :=
    decode_expression enc₂ (show b₂ ++ r₂ = 0 :: _ from by simpa using split₂.symm) (by decide)
  have locNil : locChildren = [] := List.eq_nil_of_length_eq_zero locLength
  subst locNil
  obtain ⟨locBytesNil, env₂⟩ := encodeList_nil locEncoded
  subst locBytesNil env₂
  simp only [List.nil_append] at locSplit
  -- the input `(, (g $x))`
  obtain ⟨b₃, e₃, r₃, enc₃, list₃, split₃⟩ := encodeList_split (tail := []) list₂
  simp only [List.append_nil] at split₃
  rw [locSplit] at split₃
  obtain ⟨inputChildren, inputBytes, rfl, inputLength, inputEncoded, inputSplit⟩ :=
    decode_expression enc₃ split₃.symm (by decide)
  obtain ⟨comma, gPart, rfl⟩ := exists_of_length_two inputLength
  obtain ⟨b₄, e₄, r₄, enc₄, list₄, split₄⟩ := encodeList_split (tail := r₃) inputEncoded
  rw [inputSplit] at split₄
  obtain ⟨commaName, rfl, commaBytes, tail₄, env₄⟩ := decode_symbol 1 enc₄ split₄.symm rfl (by decide) (by decide)
  have commaEq : commaName = "," := symbol_of_bytes (by rw [commaBytes]; rfl)
  subst commaEq env₄
  obtain ⟨b₅, e₅, r₅, enc₅, list₅, split₅⟩ := encodeList_split (tail := r₃) list₄
  rw [tail₄] at split₅
  obtain ⟨gChildren, gBytes, rfl, gLength, gEncoded, gSplit⟩ :=
    decode_expression enc₅ (by simpa using split₅.symm) (by decide)
  obtain ⟨gSymbol, firstVar, rfl⟩ := exists_of_length_two gLength
  obtain ⟨b₆, e₆, r₆, enc₆, list₆, split₆⟩ := encodeList_split (tail := r₅ ++ r₃) gEncoded
  rw [gSplit] at split₆
  obtain ⟨gName, rfl, gNameBytes, tail₆, env₆⟩ := decode_symbol 1 enc₆ split₆.symm rfl (by decide) (by decide)
  have gEq : gName = "g" := symbol_of_bytes (by rw [gNameBytes]; rfl)
  subst gEq env₆
  obtain ⟨b₇, e₇, r₇, enc₇, list₇, split₇⟩ := encodeList_split (tail := r₅ ++ r₃) list₆
  rw [tail₆] at split₇
  obtain ⟨name, rfl, fresh, tail₇, env₇⟩ := decode_newVar enc₇ (by simpa using split₇.symm)
  subst env₇
  obtain ⟨r₇Nil, e₇Eq⟩ := encodeList_nil list₇
  subst r₇Nil e₇Eq
  obtain ⟨r₅Nil, e₅Eq⟩ := encodeList_nil list₅
  subst r₅Nil e₅Eq
  -- the output `(O (+ (out $x)))`
  obtain ⟨b₈, e₈, r₈, enc₈, list₈, split₈⟩ := encodeList_split (tail := []) list₃
  simp only [List.append_nil, List.nil_append] at split₈ tail₇
  rw [tail₇] at split₈
  obtain ⟨outputChildren, outputBytes, rfl, outputLength, outputEncoded, outputSplit⟩ :=
    decode_expression enc₈ split₈.symm (by decide)
  obtain ⟨oSymbol, addSink, rfl⟩ := exists_of_length_two outputLength
  obtain ⟨b₉, e₉, r₉, enc₉, list₉, split₉⟩ := encodeList_split (tail := r₈) outputEncoded
  rw [outputSplit] at split₉
  obtain ⟨oName, rfl, oBytes, tail₉, env₉⟩ := decode_symbol 1 enc₉ split₉.symm rfl (by decide) (by decide)
  have oEq : oName = "O" := symbol_of_bytes (by rw [oBytes]; rfl)
  subst oEq env₉
  obtain ⟨b₁₀, e₁₀, r₁₀, enc₁₀, list₁₀, split₁₀⟩ := encodeList_split (tail := r₈) list₉
  rw [tail₉] at split₁₀
  obtain ⟨addChildren, addBytes, rfl, addLength, addEncoded, addSplit⟩ :=
    decode_expression enc₁₀ (by simpa using split₁₀.symm) (by decide)
  obtain ⟨plus, outPart, rfl⟩ := exists_of_length_two addLength
  obtain ⟨b₁₁, e₁₁, r₁₁, enc₁₁, list₁₁, split₁₁⟩ := encodeList_split (tail := r₁₀ ++ r₈) addEncoded
  rw [addSplit] at split₁₁
  obtain ⟨plusName, rfl, plusBytes, tail₁₁, env₁₁⟩ := decode_symbol 1 enc₁₁ split₁₁.symm rfl (by decide) (by decide)
  have plusEq : plusName = "+" := symbol_of_bytes (by rw [plusBytes]; rfl)
  subst plusEq env₁₁
  obtain ⟨b₁₂, e₁₂, r₁₂, enc₁₂, list₁₂, split₁₂⟩ := encodeList_split (tail := r₁₀ ++ r₈) list₁₁
  rw [tail₁₁] at split₁₂
  obtain ⟨outChildren, outBytes, rfl, outLength, outEncoded, outSplit⟩ :=
    decode_expression enc₁₂ (by simpa using split₁₂.symm) (by decide)
  obtain ⟨outSymbol, reference, rfl⟩ := exists_of_length_two outLength
  obtain ⟨b₁₃, e₁₃, r₁₃, enc₁₃, list₁₃, split₁₃⟩ := encodeList_split (tail := r₁₂ ++ (r₁₀ ++ r₈)) outEncoded
  rw [outSplit] at split₁₃
  obtain ⟨outName, rfl, outNameBytes, tail₁₃, env₁₃⟩ := decode_symbol 3 enc₁₃ split₁₃.symm rfl (by decide) (by decide)
  have outEq : outName = "out" := symbol_of_bytes (by rw [outNameBytes]; rfl)
  subst outEq env₁₃
  obtain ⟨b₁₄, e₁₄, r₁₄, enc₁₄, list₁₄, split₁₄⟩ := encodeList_split (tail := r₁₂ ++ (r₁₀ ++ r₈)) list₁₃
  rw [tail₁₃] at split₁₄
  obtain ⟨other, rfl, found, _, _⟩ := decode_varRef (index := 0) enc₁₄ (by simpa using split₁₄.symm) (by decide)
  have otherEq : other = name := by
    simp only [compactVariableIndex, List.nil_append] at found
    split_ifs at found with same
    · exact same
    · simp at found
  subst otherEq
  exact ⟨other, rfl⟩

/-! ## Unification introduces no symbol -/

theorem lookup_mem {σ : Subst} {name : String} {value : Atom} (found : Subst.lookup σ name = some value) :
    ∃ binding ∈ σ, binding.2 = value := by
  unfold Subst.lookup at found
  obtain ⟨binding, findEq, rfl⟩ := Option.map_eq_some_iff.mp found
  exact ⟨binding, List.mem_of_find?_eq_some findEq, rfl⟩

/-- A symbol of a substitution instance occurs in the atom or in a value of the substitution. -/
theorem occurs_applySubst {name : String} (σ : Subst) :
    ∀ atom : Atom, Occurs (.symbol name) (applySubst σ atom) →
      Occurs (.symbol name) atom ∨ ∃ binding ∈ σ, Occurs (.symbol name) binding.2
  | .var v, inside => by
      simp only [applySubst] at inside
      cases found : Subst.lookup σ v with
      | none =>
          rw [found, Option.getD_none] at inside
          cases inside
      | some value =>
          rw [found, Option.getD_some] at inside
          obtain ⟨binding, member, valueEq⟩ := lookup_mem found
          exact Or.inr ⟨binding, member, valueEq ▸ inside⟩
  | .symbol _, inside => Or.inl (by simpa [applySubst] using inside)
  | .grounded _, inside => by simp [applySubst] at inside; cases inside
  | .expression children, inside => by
      simp only [applySubst] at inside
      cases inside with
      | child member childInside =>
          obtain ⟨original, originalMember, rfl⟩ := listCase children member
          rcases occurs_applySubst σ original childInside with inOriginal | inValue
          · exact Or.inl (.child originalMember inOriginal)
          · exact Or.inr inValue
where
  listCase : ∀ (children : List Atom) {child : Atom}, child ∈ applySubst.applySubstList σ children →
      ∃ original ∈ children, child = applySubst σ original
    | [], _, member => by simp [applySubst.applySubstList] at member
    | first :: rest, child, member => by
        simp only [applySubst.applySubstList, List.mem_cons] at member
        rcases member with rfl | inRest
        · exact ⟨first, List.mem_cons_self, rfl⟩
        · obtain ⟨original, originalMember, childEq⟩ := listCase rest inRest
          exact ⟨original, List.mem_cons_of_mem _ originalMember, childEq⟩

/-- An atom in which a symbol does not occur. -/
def SymbolFree (name : String) (atom : Atom) : Prop := ¬ Occurs (.symbol name) atom

theorem symbolFree_applySubst {name : String} {σ : Subst} {atom : Atom} (free : SymbolFree name atom)
    (valuesFree : ∀ binding ∈ σ, SymbolFree name binding.2) : SymbolFree name (applySubst σ atom) := by
  intro inside
  rcases occurs_applySubst σ atom inside with inAtom | ⟨binding, member, inValue⟩
  · exact free inAtom
  · exact valuesFree binding member inValue

theorem symbolFree_child {name : String} {children : List Atom} {child : Atom}
    (free : SymbolFree name (.expression children)) (member : child ∈ children) : SymbolFree name child :=
  fun inside => free (.child member inside)

/-- Equations and a substitution in which a symbol does not occur. -/
def EquationsFree (name : String) (equations : Equations) (θ : Subst) : Prop :=
  (∀ equation ∈ equations, SymbolFree name equation.1 ∧ SymbolFree name equation.2) ∧
    ∀ binding ∈ θ, SymbolFree name binding.2

theorem equationsFree_eliminate {name variableName : String} {value : Atom} {rest : Equations} {θ : Subst}
    (free : EquationsFree name rest θ) (valueFree : SymbolFree name value) :
    EquationsFree name (substituteEquations variableName value rest) (bindSolved θ variableName value) := by
  have single : ∀ binding ∈ [(variableName, value)], SymbolFree name binding.2 := by
    intro binding member
    simp only [List.mem_singleton] at member
    subst member
    exact valueFree
  refine ⟨?_, ?_⟩
  · intro equation member
    simp only [substituteEquations, List.mem_map] at member
    obtain ⟨original, originalMember, rfl⟩ := member
    exact ⟨symbolFree_applySubst (free.1 original originalMember).1 single,
      symbolFree_applySubst (free.1 original originalMember).2 single⟩
  · intro binding member
    simp only [bindSolved, List.mem_cons, List.mem_map] at member
    rcases member with rfl | ⟨original, originalMember, rfl⟩
    · exact valueFree
    · exact symbolFree_applySubst (free.2 original originalMember) single

theorem solveWithin_symbolFree (name : String) (eliminate : Equations → Subst → Unification)
    (good : ∀ next θ' θ'', EquationsFree name next θ' → eliminate next θ' = .solved θ'' →
      ∀ binding ∈ θ'', SymbolFree name binding.2) :
    ∀ (fuel : ℕ) (equations : Equations) (θ θ' : Subst), EquationsFree name equations θ →
      solveWithin eliminate fuel equations θ = .solved θ' → ∀ binding ∈ θ', SymbolFree name binding.2
  | 0, _, _, _, _, solved => by simp [solveWithin] at solved
  | _ + 1, [], θ, θ', free, solved => by
      simp only [solveWithin, Unification.solved.injEq] at solved
      subst solved
      exact free.2
  | fuel + 1, (left, right) :: rest, θ, θ', free, solved => by
      have headFree := free.1 (left, right) List.mem_cons_self
      have restFree : EquationsFree name rest θ :=
        ⟨fun equation member => free.1 equation (List.mem_cons_of_mem _ member), free.2⟩
      by_cases same : left = right
      · simp only [solveWithin, same, if_true] at solved
        exact solveWithin_symbolFree name eliminate good fuel rest θ θ' restFree solved
      · simp only [solveWithin, same, if_false] at solved
        cases left with
        | var variableName =>
            simp only at solved
            split at solved
            · cases solved
            · exact good _ _ _ (equationsFree_eliminate restFree headFree.2) solved
        | symbol symbolName =>
            cases right with
            | var variableName =>
                simp only at solved
                split at solved
                · cases solved
                · exact good _ _ _ (equationsFree_eliminate restFree headFree.1) solved
            | _ => simp at solved
        | grounded value =>
            cases right with
            | var variableName =>
                simp only at solved
                split at solved
                · cases solved
                · exact good _ _ _ (equationsFree_eliminate restFree headFree.1) solved
            | _ => simp at solved
        | expression lefts =>
            cases right with
            | var variableName =>
                simp only at solved
                split at solved
                · cases solved
                · exact good _ _ _ (equationsFree_eliminate restFree headFree.1) solved
            | expression rights =>
                simp only at solved
                split at solved
                · apply solveWithin_symbolFree name eliminate good fuel _ θ θ' _ solved
                  refine ⟨?_, free.2⟩
                  intro equation member
                  rcases List.mem_append.1 member with zipped | inRest
                  · obtain ⟨leftChild, rightChild⟩ := equation
                    have members := List.of_mem_zip zipped
                    exact ⟨symbolFree_child headFree.1 members.1, symbolFree_child headFree.2 members.2⟩
                  · exact restFree.1 equation inRest
                · cases solved
            | _ => simp at solved

theorem solveEquations_symbolFree (name : String) :
    ∀ (budget : ℕ) (equations : Equations) (θ θ' : Subst), EquationsFree name equations θ →
      solveEquations budget equations θ = .solved θ' → ∀ binding ∈ θ', SymbolFree name binding.2
  | 0, equations, θ, θ', free, solved =>
      solveWithin_symbolFree name _ (fun _ _ _ _ solved => by simp at solved) _ equations θ θ' free solved
  | budget + 1, equations, θ, θ', free, solved =>
      solveWithin_symbolFree name _ (fun next θ₁ θ₂ nextFree solved₂ =>
        solveEquations_symbolFree name budget next θ₁ θ₂ nextFree solved₂) _ equations θ θ' free solved

/-- **Unification introduces no symbol.** -/
theorem unifyOption_symbolFree {name : String} {θ θ' : Subst} {equations : Equations}
    (free : EquationsFree name equations θ) (solved : unifyOption θ equations = some θ') :
    ∀ binding ∈ θ', SymbolFree name binding.2 := by
  unfold unifyOption at solved
  split at solved
  · rename_i result unified
    simp only [Option.some.injEq] at solved
    subst solved
    unfold unifyUnder at unified
    apply solveEquations_symbolFree name _ _ θ result _ unified
    refine ⟨?_, free.2⟩
    intro equation member
    simp only [List.mem_map] at member
    obtain ⟨original, originalMember, rfl⟩ := member
    exact ⟨symbolFree_applySubst (free.1 original originalMember).1 free.2,
      symbolFree_applySubst (free.1 original originalMember).2 free.2⟩
  · cases solved

theorem symbolFree_renameApart {name tag : String} {atom : Atom} (free : SymbolFree name atom) :
    SymbolFree name (renameApart tag atom) := by
  apply symbolFree_applySubst free
  intro binding member
  simp only [List.mem_map] at member
  obtain ⟨_, _, rfl⟩ := member
  intro inside
  cases inside

/-! ## Keys of reports -/

theorem encode_outOf {environment environment' : List String} {x : Atom} {bytes : List ℕ}
    (encoded : morkCompactEncodeAtom environment (outOf x) = some (bytes, environment')) :
    ∃ xBytes, morkCompactEncodeAtom environment x = some (xBytes, environment') ∧
      bytes = [2, 195, 111, 117, 116] ++ xBytes := by
  unfold outOf at encoded
  obtain ⟨tail, list, bytesEq⟩ := encode_expression encoded
  obtain ⟨b₁, e₁, t₁, enc₁, list₁, tailEq⟩ := encodeList_cons list
  obtain ⟨outBytesEq, envEq, _, _⟩ := encode_symbol_bytes enc₁
  have outBytes : b₁ = [195, 111, 117, 116] := by rw [outBytesEq]; rfl
  subst outBytes envEq
  obtain ⟨b₂, e₂, t₂, enc₂, list₂, t₁Eq⟩ := encodeList_cons list₁
  obtain ⟨t₂Nil, e₂Eq⟩ := encodeList_nil list₂
  simp only at t₂Nil e₂Eq bytesEq tailEq t₁Eq
  subst t₂Nil e₂Eq
  refine ⟨b₂, enc₂, ?_⟩
  rw [bytesEq, tailEq, t₁Eq]
  simp

/-- **Two reports with the key of `(out N)` for a symbol `N` report `N` itself.** -/
theorem out_key_symbol {x : Atom} {value : String}
    (same : morkSupportKey (outOf x) = morkSupportKey (outOf (.symbol value))) : x = .symbol value := by
  unfold morkSupportKey at same
  cases left : morkCompactKey? (outOf x) with
  | none =>
      cases right : morkCompactKey? (outOf (.symbol value)) with
      | none =>
          rw [left, right] at same
          injection same with atomsEq
          unfold outOf at atomsEq
          injection atomsEq with listEq
          injection listEq with _ restEq
          injection restEq
      | some k => rw [left, right] at same; cases same
  | some k =>
      cases right : morkCompactKey? (outOf (.symbol value)) with
      | none => rw [left, right] at same; cases same
      | some k' =>
          rw [left, right] at same
          injection same with keyEq
          subst keyEq
          unfold morkCompactKey? at left right
          obtain ⟨⟨leftBytes, _⟩, leftEncoded, leftEq⟩ := Option.map_eq_some_iff.mp left
          obtain ⟨⟨rightBytes, _⟩, rightEncoded, rightEq⟩ := Option.map_eq_some_iff.mp right
          obtain ⟨xBytes, xEncoded, leftBytesEq⟩ := encode_outOf leftEncoded
          obtain ⟨vBytes, vEncoded, rightBytesEq⟩ := encode_outOf rightEncoded
          simp only at leftEq rightEq
          have bytesSame : xBytes = vBytes := by
            have := leftEq.trans rightEq.symm
            rw [leftBytesEq, rightBytesEq] at this
            exact List.append_cancel_left this
          subst bytesSame
          obtain ⟨vBytesEq, _, positive, short⟩ := encode_symbol_bytes vEncoded
          obtain ⟨name, rfl, nameBytes, _, _⟩ :=
            decode_symbol (symbolBytes value).length xEncoded (tail := []) (by rw [List.append_nil, vBytesEq])
              rfl positive short
          rw [List.take_of_length_le (le_refl _)] at nameBytes
          rw [symbol_of_bytes nameBytes]

theorem g_out_key_ne (y x : Atom) :
    morkSupportKey (.expression [.symbol "g", y]) ≠ morkSupportKey (outOf x) := by
  intro same
  unfold morkSupportKey at same
  cases left : morkCompactKey? (.expression [.symbol "g", y]) with
  | none =>
      cases right : morkCompactKey? (outOf x) with
      | none =>
          rw [left, right] at same
          injection same with atomsEq
          unfold outOf at atomsEq
          injection atomsEq with listEq
          injection listEq with headEq
          injection headEq with nameEq
          exact absurd nameEq (by decide)
      | some k => rw [left, right] at same; cases same
  | some k =>
      cases right : morkCompactKey? (outOf x) with
      | none => rw [left, right] at same; cases same
      | some k' =>
          rw [left, right] at same
          injection same with keyEq
          subst keyEq
          unfold morkCompactKey? at left right
          obtain ⟨⟨leftBytes, _⟩, leftEncoded, leftEq⟩ := Option.map_eq_some_iff.mp left
          obtain ⟨⟨rightBytes, _⟩, rightEncoded, rightEq⟩ := Option.map_eq_some_iff.mp right
          obtain ⟨xBytes, _, rightBytesEq⟩ := encode_outOf rightEncoded
          obtain ⟨tail, list, leftBytesEq⟩ := encode_expression leftEncoded
          obtain ⟨b₁, e₁, t₁, enc₁, _, tailEq⟩ := encodeList_cons list
          obtain ⟨gBytesEq, _, _, _⟩ := encode_symbol_bytes enc₁
          have gBytes : b₁ = [193, 103] := by rw [gBytesEq]; rfl
          simp only at leftEq rightEq leftBytesEq tailEq
          have := leftEq.trans rightEq.symm
          rw [leftBytesEq, tailEq, gBytes, rightBytesEq] at this
          simp at this

theorem equation_out_key_ne (value x : Atom) :
    morkSupportKey (equationOf value) ≠ morkSupportKey (outOf x) := by
  intro same
  unfold outOf at same
  obtain ⟨others, otherEq, len⟩ := expression_of_same_key same
  unfold equationOf at otherEq
  injection otherEq with listEq
  rw [← listEq] at len
  simp at len

/-! ## Fresh symbols -/

/-- The symbols occurring in an atom. -/
def symbolsOf : Atom → List String
  | .symbol name => [name]
  | .var _ => []
  | .grounded _ => []
  | .expression children => symbolsList children
where
  symbolsList : List Atom → List String
    | [] => []
    | child :: rest => symbolsOf child ++ symbolsList rest

theorem mem_symbolsOf {name : String} : ∀ {atom : Atom}, Occurs (.symbol name) atom → name ∈ symbolsOf atom
  | _, .here => by simp [symbolsOf]
  | .expression children, .child member inside => by
      simp only [symbolsOf]
      exact listCase children member (mem_symbolsOf inside)
where
  listCase : ∀ (children : List Atom) {child : Atom}, child ∈ children → name ∈ symbolsOf child →
      name ∈ symbolsOf.symbolsList children
    | [], _, member, _ => by simp at member
    | first :: rest, child, member, inChild => by
        simp only [symbolsOf.symbolsList, List.mem_append]
        rcases List.mem_cons.1 member with rfl | inRest
        · exact Or.inl inChild
        · exact Or.inr (listCase rest inRest inChild)

/-- A symbol longer than every symbol of some atoms. -/
def freshSymbolFor (atoms : List Atom) : String :=
  String.ofList (List.replicate (((atoms.flatMap symbolsOf).map String.length).foldl max 0 + 2) 'v')

theorem le_foldl_max : ∀ (values : List ℕ) (start value : ℕ), (value ∈ values ∨ value ≤ start) →
    value ≤ values.foldl max start
  | [], _, _, h => by simpa using h
  | head :: rest, start, value, h => by
      simp only [List.foldl_cons]
      apply le_foldl_max rest
      rcases h with member | small
      · rcases List.mem_cons.1 member with rfl | inRest
        · exact Or.inr (le_max_right _ _)
        · exact Or.inl inRest
      · exact Or.inr (le_trans small (le_max_left _ _))

theorem freshSymbol_not_occurs {atoms : List Atom} {atom : Atom} (member : atom ∈ atoms) :
    SymbolFree (freshSymbolFor atoms) atom := by
  intro inside
  have inSymbols := mem_symbolsOf inside
  have bound : (freshSymbolFor atoms).length ≤ ((atoms.flatMap symbolsOf).map String.length).foldl max 0 :=
    le_foldl_max _ 0 _ (Or.inl (List.mem_map.2 ⟨_, List.mem_flatMap.2 ⟨atom, member, inSymbols⟩, rfl⟩))
  simp [freshSymbolFor] at bound

theorem freshSymbol_ne_g (atoms : List Atom) : freshSymbolFor atoms ≠ "g" := by
  intro same
  have lengths := congrArg String.length same
  have gLength : "g".length = 1 := rfl
  simp [freshSymbolFor] at lengths
  omega

/-! ## The watcher fires -/

/-- `(g $name)`. -/
def gWith (name : String) : Atom := .expression [.symbol "g", .var name]

/-- The watcher's scheduler shell. -/
def watcherRaw (name : String) : RawExecFact :=
  ⟨watcherWith name, .expression [], .expression [.symbol ",", gWith name],
    .expression [.symbol "O", .expression [.symbol "+", outOf (.var name)]]⟩

theorem extract_watcherWith (name : String) : extractRawExecFact (watcherWith name) = some (watcherRaw name) := rfl

/-- The watcher's directive. -/
def watcherDirective (name : String) : MainlineDirective :=
  ⟨watcherWith name, .compat [gWith name], .sinks [.core (.add (outOf (.var name)))]⟩

theorem decode_watcherWith (profile : BuildProfile) (name : String) :
    decodeDirective profile (watcherRaw name) = .ok (some (watcherDirective name)) := rfl

/-- The rows the watcher's outputs see. -/
def watcherRows (name : String) (space : List Atom) : List Subst :=
  (conjunctionRows (factorTag (watcherWith name))
      (morkInsertSupport (morkEraseSupport space (watcherWith name)) (watcherWith name)) 0 [] [gWith name]).map
    (inputRow (inputSpecVariables (MainlineInput.compat [gWith name]).coverage))

/-- **The watcher's firing**: it leaves, and every row writes its report. -/
theorem fire_watcher (prims : Primitives) (external : ExternalState) (space : List Atom) (name : String) :
    fireDirective prims external space (watcherDirective name) =
      .ok (morkUnionSupport (morkEraseSupport space (watcherWith name))
        (staged (MainlineInput.compat [gWith name]).coverage (watcherRows name space) (outOf (.var name))),
        external) := by
  simp [fireDirective, watcherDirective, mainlineRows, watcherRows, applyMainlineSinks, eagerOutputs,
    finalizeMainlineSink, bind, Except.bind, pure, Except.pure]

theorem staged_nil (input : InputSpec) (template : Atom) : staged input [] template = [] := rfl

/-- The watcher with no rows only leaves. -/
theorem step_watcher_no_rows (profile : BuildProfile) (prims : Primitives) (c : Config) (name : String)
    (selected : selectNextScheduled (WQComputable.cRawExecFacts c.1) = some (watcherRaw name))
    (noRows : watcherRows name c.1 = []) :
    mainlineStep profile prims c.2 c.1 = .next (morkEraseSupport c.1 (watcherWith name)) c.2 := by
  simp only [mainlineStep, selected, decode_watcherWith, fire_watcher, noRows, staged_nil]
  rfl

/-- The watcher with a row writes the report of that row. -/
theorem step_watcher_row (profile : BuildProfile) (prims : Primitives) (c : Config) (name : String)
    (selected : selectNextScheduled (WQComputable.cRawExecFacts c.1) = some (watcherRaw name))
    {row : Subst} (member : row ∈ watcherRows name c.1) :
    ∃ after, mainlineStep profile prims c.2 c.1 = .next after c.2 ∧
      ∃ atom ∈ after, morkSupportKey atom = morkSupportKey (applySubst row (outOf (.var name))) := by
  refine ⟨morkUnionSupport (morkEraseSupport c.1 (watcherWith name))
      (staged (MainlineInput.compat [gWith name]).coverage (watcherRows name c.1) (outOf (.var name))),
    by simp only [mainlineStep, selected, decode_watcherWith, fire_watcher], ?_⟩
  have instanceMember : applySubst row (outOf (.var name)) ∈
      instances (MainlineInput.compat [gWith name]).coverage (watcherRows name c.1) (outOf (.var name)) := by
    unfold instances
    refine List.mem_filterMap.2 ⟨row, member, ?_⟩
    simp only [instantiateRuleTemplateAtom?]
    rw [if_pos]
    -- the input binds the watcher's variable in every row
    simp only [watcherRows, List.mem_map] at member
    obtain ⟨θ, _, rfl⟩ := member
    simp [ruleTemplateCovered, ruleTemplatesCovered, outOf, inputSpecVariables, inputRow,
      MainlineInput.coverage, gWith, atomFreeVars, atomFreeVars.atomFreeVarsList,
      inputSpecUsesVariable, Subst.lookup]
  have stagedContains := contains_of_mem _ _ instanceMember
  have inStaged : morkSupportContains (staged (MainlineInput.compat [gWith name]).coverage (watcherRows name c.1)
      (outOf (.var name))) (applySubst row (outOf (.var name))) = true := by
    unfold staged
    exact morkSupportContains_morkUnionSupport_of_staged_contains_core [] _ _ stagedContains
  have unionContains := morkSupportContains_morkUnionSupport_of_staged_contains_core
    (morkEraseSupport c.1 (watcherWith name)) _ _ inStaged
  rw [morkSupportContains_eq_true_iff_key_mem] at unionContains
  obtain ⟨atom, atomMember, keyEq⟩ := List.mem_map.1 unionContains
  exact ⟨atom, atomMember, keyEq⟩

/-! ## When the phase ends -/

theorem foldl_select_isSome {α : Type} [SchedulerKey α] : ∀ (facts : List α) (best : Option α),
    best.isSome = true ∨ facts ≠ [] →
      (facts.foldl (fun best fact =>
        match best with
        | none => some fact
        | some current =>
          if lexLt (SchedulerKey.key fact) (SchedulerKey.key current) then some fact else some current)
        best).isSome = true
  | [], best, h => by simpa using h
  | fact :: rest, best, _ => by
      simp only [List.foldl_cons]
      apply foldl_select_isSome rest
      left
      cases best with
      | none => rfl
      | some current => by_cases lt : lexLt (SchedulerKey.key fact) (SchedulerKey.key current) <;> simp [lt]

theorem select_exists {α : Type} [SchedulerKey α] {facts : List α} {fact : α} (member : fact ∈ facts) :
    ∃ selected, selectNextScheduled facts = some selected := by
  have := foldl_select_isSome facts none (Or.inr (List.ne_nil_of_mem member))
  exact Option.isSome_iff_exists.mp this

/-- When the phase is over, no executable is below the watcher. -/
theorem not_below_facts {c : Config} (notBelow : ¬ Below c) :
    ∀ fact ∈ WQComputable.cRawExecFacts c.1,
      lexLt (totalMorkCompactKey fact.atom) (totalMorkCompactKey watcherExec) = false := by
  intro fact member
  cases below : lexLt (totalMorkCompactKey fact.atom) (totalMorkCompactKey watcherExec) with
  | false => rfl
  | true =>
      exfalso
      obtain ⟨selected, selectedEq⟩ := select_exists member
      apply notBelow
      refine ⟨selected, selectedEq, ?_⟩
      have least := selectNextScheduled_least selectedEq fact member
      change lexLt (totalMorkCompactKey fact.atom) (totalMorkCompactKey selected.atom) = false at least
      by_cases sameKey : totalMorkCompactKey fact.atom = totalMorkCompactKey selected.atom
      · rw [← sameKey]; exact below
      · exact lexLt_trans _ _ _ (lexLt_total_of_ne _ _ sameKey least) below

theorem proj_self_of_absent {target : Atom} {space : List Atom}
    (absent : morkSupportContains space target = false) : proj (keyOf target) space = space := by
  apply List.filter_eq_self.mpr
  intro atom member
  simp only [keyOf, sameMorkSupportAtom, Bool.not_eq_true', decide_eq_false_iff_not]
  intro same
  have present : morkSupportContains space target = true := by
    rw [morkSupportContains_eq_true_iff_key_mem]
    exact List.mem_map.2 ⟨atom, member, same⟩
  rw [present] at absent
  cases absent

theorem erase_eq_proj {target other : Atom} (same : keyOf target other = true) (space : List Atom) :
    morkEraseSupport space other = proj (keyOf target) space := by
  simp only [keyOf, sameMorkSupportAtom, decide_eq_true_eq] at same
  unfold morkEraseSupport proj
  congr 1
  funext atom
  simp [keyOf, sameMorkSupportAtom, same]

theorem mem_of_mem_proj {hide : Atom → Bool} {space : List Atom} {atom : Atom}
    (member : atom ∈ proj hide space) : atom ∈ space := (List.mem_filter.1 member).1

theorem keyOf_false_of_mem_proj {target : Atom} {space : List Atom} {atom : Atom}
    (member : atom ∈ proj (keyOf target) space) : keyOf target atom = false := by
  simpa using (List.mem_filter.1 member).2

theorem mem_proj_of_mem {hide : Atom → Bool} {space : List Atom} {atom : Atom}
    (member : atom ∈ space) (visible : hide atom = false) : atom ∈ proj hide space :=
  List.mem_filter.2 ⟨member, by simp [visible]⟩

/-- The executables of the runs with and without the watcher, other than watchers, are above it. -/
theorem above_of_rel {value : Atom} {c0 c1 c2 : Config} (rel : PhaseRel value c0 c1 c2) (notBelow : ¬ Below c0) :
    (∀ fact ∈ WQComputable.cRawExecFacts c2.1, keyOf watcherExec fact.atom = false →
        lexLt (totalMorkCompactKey watcherExec) (totalMorkCompactKey fact.atom) = true) ∧
      ∀ fact ∈ WQComputable.cRawExecFacts c1.1, keyOf watcherExec fact.atom = false →
        lexLt (totalMorkCompactKey watcherExec) (totalMorkCompactKey fact.atom) = true := by
  have inOwn : ∀ fact ∈ WQComputable.cRawExecFacts c2.1, keyOf watcherExec fact.atom = false →
      lexLt (totalMorkCompactKey watcherExec) (totalMorkCompactKey fact.atom) = true := by
    intro fact member notW
    obtain ⟨atomMember, extracted⟩ := rawFact_atom member
    have notEq : keyOf (equationOf value) fact.atom = false := by
      cases eqKey : keyOf (equationOf value) fact.atom with
      | false => rfl
      | true => rw [equation_inert value _ eqKey] at extracted; cases extracted
    have inOwnProj : fact.atom ∈ proj (keyOf (equationOf value)) c0.1 := by
      rw [← rel.equationTwin.agree]
      exact mem_proj_of_mem atomMember notEq
    have ownMember : fact ∈ WQComputable.cRawExecFacts c0.1 :=
      List.mem_filterMap.2 ⟨fact.atom, mem_of_mem_proj inOwnProj, extracted⟩
    have notBelowFact := not_below_facts notBelow fact ownMember
    apply lexLt_total_of_ne _ _ _ notBelowFact
    intro sameKey
    have physical := supportKey_eq_of_totalKey_eq watcher_representable sameKey
    simp [keyOf, sameMorkSupportAtom, physical] at notW
  refine ⟨inOwn, ?_⟩
  intro fact member notW
  obtain ⟨atomMember, extracted⟩ := rawFact_atom member
  have inWithoutProj : fact.atom ∈ proj (keyOf watcherExec) c2.1 := by
    rw [← rel.watcherTwin.agree]
    exact mem_proj_of_mem atomMember notW
  exact inOwn fact (List.mem_filterMap.2 ⟨fact.atom, mem_of_mem_proj inWithoutProj, extracted⟩) notW

/-- **A present watcher is selected** when every other executable is above it. -/
theorem select_watcher {c : Config} {name : String} (nodup : MorkSupportNodup c.1)
    (member : watcherWith name ∈ c.1) (isWatcher : keyOf watcherExec (watcherWith name) = true)
    (above : ∀ fact ∈ WQComputable.cRawExecFacts c.1, keyOf watcherExec fact.atom = false →
      lexLt (totalMorkCompactKey watcherExec) (totalMorkCompactKey fact.atom) = true) :
    selectNextScheduled (WQComputable.cRawExecFacts c.1) = some (watcherRaw name) := by
  apply selectNextScheduled_eq_some_of_mem_of_strict_minimum
  · exact List.mem_filterMap.2 ⟨watcherWith name, member, extract_watcherWith name⟩
  · intro candidate candidateMember distinct
    obtain ⟨candidateAtomMember, candidateExtracted⟩ := rawFact_atom candidateMember
    change lexLt (totalMorkCompactKey (watcherWith name)) (totalMorkCompactKey candidate.atom) = true
    rw [totalKey_of_watcherKey isWatcher]
    cases watcherKey : keyOf watcherExec candidate.atom with
    | false => exact above candidate candidateMember watcherKey
    | true =>
        exfalso
        apply distinct
        simp only [keyOf, sameMorkSupportAtom, decide_eq_true_eq] at watcherKey isWatcher
        have atomsEq := List.inj_on_of_nodup_map nodup candidateAtomMember member
          (watcherKey.trans isWatcher.symm)
        have := candidateExtracted
        rw [atomsEq, extract_watcherWith] at this
        exact (Option.some.inj this).symm

theorem inputVariables_watcher (name : String) :
    inputSpecVariables (MainlineInput.compat [gWith name]).coverage = [name] := by
  simp [MainlineInput.coverage, inputSpecVariables, atomFreeVars.atomFreeVarsList]
  simp [gWith, atomFreeVars, atomFreeVars.atomFreeVarsList]

theorem watcher_clash_wide (name tag : String) (θ : Subst) {atom : Atom}
    (wide : ∃ others, atom = .expression others ∧ 3 ≤ others.length) :
    unifyOption θ [(gWith name, renameApart tag atom)] = none := by
  obtain ⟨others, rfl, large⟩ := wide
  exact unifyOption_length_clash θ tag (by simp; omega)

/-- **A watcher's row comes from a narrow stored atom other than itself.** -/
theorem watcherRow_source {name : String} {space : List Atom} {row : Subst}
    (member : row ∈ watcherRows name space) :
    ∃ atom θ, atom ∈ morkEraseSupport space (watcherWith name) ∧
      unifyOption [] [(gWith name, renameApart (factorTag (watcherWith name) 0) atom)] = some θ ∧
      row = [(name, applySubst θ (.var name))] := by
  simp only [watcherRows, conjunctionRows, List.flatMap_singleton', List.mem_map, List.mem_filterMap,
    inputVariables_watcher] at member
  obtain ⟨θ, ⟨atom, atomMember, unified⟩, rowEq⟩ := member
  have notSelf : atom ≠ watcherWith name := by
    rintro rfl
    have clash := watcher_clash_wide name (factorTag (watcherWith name) 0) [] (atom := watcherWith name)
      ⟨_, rfl, by simp⟩
    rw [clash] at unified
    cases unified
  have inErase : atom ∈ morkEraseSupport space (watcherWith name) := by
    unfold morkInsertSupport at atomMember
    split at atomMember
    · exact atomMember
    · rcases List.mem_append.1 atomMember with inLive | inSingle
      · exact inLive
      · simp at inSingle; exact absurd inSingle notSelf
  exact ⟨atom, θ, inErase, unified, by rw [← rowEq]; simp [inputRow]⟩

/-- The value a row of the watcher reports carries no symbol its stored atom lacks. -/
theorem watcherRow_value_free {name valueName tag : String} {atom : Atom} {θ : Subst}
    (atomFree : SymbolFree valueName atom) (notG : valueName ≠ "g")
    (unified : unifyOption [] [(gWith name, renameApart tag atom)] = some θ) :
    SymbolFree valueName (applySubst θ (.var name)) := by
  have patternFree : SymbolFree valueName (gWith name) := by
    intro inside
    have := mem_symbolsOf inside
    simp [symbolsOf, symbolsOf.symbolsList, gWith] at this
    exact notG this
  have valuesFree := unifyOption_symbolFree (θ := []) (equations := [(gWith name, renameApart tag atom)])
    ⟨by
      intro equation member
      simp only [List.mem_singleton] at member
      subst member
      exact ⟨patternFree, symbolFree_renameApart atomFree⟩, by simp⟩ unified
  simp only [applySubst]
  cases found : Subst.lookup θ name with
  | none => simp only [Option.getD_none]; intro inside; cases inside
  | some value =>
      simp only [Option.getD_some]
      obtain ⟨binding, bindingMember, rfl⟩ := lookup_mem found
      exact valuesFree binding bindingMember

/-- What the run with the watcher and the run without it do when the phase ends. -/
inductive TauOutcome (profile : BuildProfile) (prims : Primitives) (valueName : String)
    (c1 c2 : Config) : Prop
  /-- No watcher remains: the runs coincide. -/
  | same : c1 = c2 → TauOutcome profile prims valueName c1 c2
  /-- Both watchers fire without rows: the runs coincide afterwards. -/
  | bothLeave (after : Config) :
      mainlineStep profile prims c1.2 c1.1 = .next after.1 after.2 →
      mainlineStep profile prims c2.2 c2.1 = .next after.1 after.2 → TauOutcome profile prims valueName c1 c2
  /-- Only the run with the watcher has one; it fires without rows and becomes the other run. -/
  | withLeaves : mainlineStep profile prims c1.2 c1.1 = .next c2.1 c2.2 →
      TauOutcome profile prims valueName c1 c2
  /-- The watcher reports something other than `(out N)`. -/
  | spurious (after : List Atom) (x : Atom) :
      mainlineStep profile prims c1.2 c1.1 = .next after c1.2 →
      (∃ atom ∈ after, morkSupportKey atom = morkSupportKey (outOf x)) →
      morkSupportKey (outOf x) ≠ morkSupportKey (outOf (.symbol valueName)) →
      TauOutcome profile prims valueName c1 c2
  /-- The run without the watcher reports. -/
  | freeReports (after : List Atom) (x : Atom) :
      mainlineStep profile prims c2.2 c2.1 = .next after c2.2 →
      (∃ atom ∈ after, morkSupportKey atom = morkSupportKey (outOf x)) →
      TauOutcome profile prims valueName c1 c2

theorem contains_witness {space : List Atom} {target : Atom}
    (present : morkSupportContains space target = true) : ∃ atom ∈ space, keyOf target atom = true := by
  rw [morkSupportContains_eq_true_iff_key_mem] at present
  obtain ⟨atom, member, keyEq⟩ := List.mem_map.1 present
  exact ⟨atom, member, by simp [keyOf, sameMorkSupportAtom, keyEq]⟩

theorem watcher_instance (name : String) (value : Atom) :
    applySubst [(name, value)] (outOf (.var name)) = outOf value := by
  simp [applySubst, outOf, applySubst.applySubstList, Subst.lookup]

/-- **The end of the phase**: with the value fresh for the expansion's own run, the run with
the watcher and the run without it coincide, possibly one step apart, or one of them makes a
report that tells it apart from the extension. -/
theorem tau_outcome (profile : BuildProfile) (prims : Primitives) (valueName : String)
    {c0 c1 c2 : Config} (rel : PhaseRel (.symbol valueName) c0 c1 c2) (notBelow : ¬ Below c0)
    (fresh : ∀ atom ∈ c0.1, SymbolFree valueName atom) (notG : valueName ≠ "g") :
    TauOutcome profile prims valueName c1 c2 := by
  obtain ⟨aboveWithout, aboveWith⟩ := above_of_rel rel notBelow
  have freshWithout : ∀ atom ∈ c2.1, keyOf (equationOf (.symbol valueName)) atom = false →
      SymbolFree valueName atom := by
    intro atom member notEq
    have inOwn : atom ∈ proj (keyOf (equationOf (.symbol valueName))) c0.1 := by
      rw [← rel.equationTwin.agree]
      exact mem_proj_of_mem member notEq
    exact fresh atom (mem_of_mem_proj inOwn)
  -- A row's report is not `(out N)` when the stored atoms are fresh.
  have reportFree : ∀ {name : String} {space : List Atom} {row : Subst},
      (∀ atom ∈ morkEraseSupport space (watcherWith name),
        keyOf (equationOf (.symbol valueName)) atom = false → SymbolFree valueName atom) →
      row ∈ watcherRows name space →
      ∃ x, applySubst row (outOf (.var name)) = outOf x ∧
        morkSupportKey (outOf x) ≠ morkSupportKey (outOf (.symbol valueName)) := by
    intro name space row spaceFree member
    obtain ⟨atom, θ, atomMember, unified, rfl⟩ := watcherRow_source member
    have notEq : keyOf (equationOf (.symbol valueName)) atom = false := by
      cases eqKey : keyOf (equationOf (.symbol valueName)) atom with
      | false => rfl
      | true =>
          rw [watcher_clash_wide name _ [] (equation_wide _ atom eqKey)] at unified
          cases unified
    have valueFree := watcherRow_value_free (spaceFree atom atomMember notEq) notG unified
    refine ⟨applySubst θ (.var name), watcher_instance name _, ?_⟩
    intro same
    exact valueFree (by rw [out_key_symbol same]; exact .here)
  have reportAny : ∀ {name : String} {space : List Atom} {row : Subst}, row ∈ watcherRows name space →
      ∃ x, applySubst row (outOf (.var name)) = outOf x := by
    intro name space row member
    obtain ⟨atom, θ, _, _, rfl⟩ := watcherRow_source member
    exact ⟨_, watcher_instance name _⟩
  by_cases withW : morkSupportContains c1.1 watcherExec = true
  · obtain ⟨w1, w1Member, w1Key⟩ := contains_witness withW
    obtain ⟨y1, rfl⟩ := watcherKey_inversion w1Key
    have sel1 := select_watcher rel.watcherTwin.nodupLeft w1Member w1Key aboveWith
    have live1 := erase_eq_proj w1Key c1.1
    by_cases withoutW : morkSupportContains c2.1 watcherExec = true
    · -- Both runs have a watcher.
      obtain ⟨w2, w2Member, w2Key⟩ := contains_witness withoutW
      obtain ⟨y2, rfl⟩ := watcherKey_inversion w2Key
      have sel2 := select_watcher rel.watcherTwin.nodupRight w2Member w2Key aboveWithout
      have live2 := erase_eq_proj w2Key c2.1
      by_cases rows2 : watcherRows y2 c2.1 = []
      · by_cases rows1 : watcherRows y1 c1.1 = []
        · apply TauOutcome.bothLeave (morkEraseSupport c2.1 (watcherWith y2), c2.2)
          · rw [step_watcher_no_rows profile prims c1 y1 sel1 rows1, live1, rel.watcherTwin.agree, ← live2,
              rel.watcherTwin.external]
          · exact step_watcher_no_rows profile prims c2 y2 sel2 rows2
        · obtain ⟨row, rowMember⟩ := List.exists_mem_of_ne_nil _ rows1
          obtain ⟨after, step, atom, atomMember, keyEq⟩ := step_watcher_row profile prims c1 y1 sel1 rowMember
          have spaceFree : ∀ atom ∈ morkEraseSupport c1.1 (watcherWith y1),
              keyOf (equationOf (.symbol valueName)) atom = false → SymbolFree valueName atom := by
            intro atom member notEq
            rw [live1, rel.watcherTwin.agree] at member
            exact freshWithout atom (mem_of_mem_proj member) notEq
          obtain ⟨x, instanceEq, notReport⟩ := reportFree spaceFree rowMember
          rw [instanceEq] at keyEq
          exact TauOutcome.spurious after x step ⟨atom, atomMember, keyEq⟩ notReport
      · obtain ⟨row, rowMember⟩ := List.exists_mem_of_ne_nil _ rows2
        obtain ⟨after, step, atom, atomMember, keyEq⟩ := step_watcher_row profile prims c2 y2 sel2 rowMember
        obtain ⟨x, instanceEq⟩ := reportAny rowMember
        rw [instanceEq] at keyEq
        exact TauOutcome.freeReports after x step ⟨atom, atomMember, keyEq⟩
    · -- Only the run with the watcher has one.
      have absent : morkSupportContains c2.1 watcherExec = false := by simpa using withoutW
      have projWithout := proj_self_of_absent absent
      by_cases rows1 : watcherRows y1 c1.1 = []
      · apply TauOutcome.withLeaves
        rw [step_watcher_no_rows profile prims c1 y1 sel1 rows1, live1, rel.watcherTwin.agree, projWithout,
          rel.watcherTwin.external]
      · obtain ⟨row, rowMember⟩ := List.exists_mem_of_ne_nil _ rows1
        obtain ⟨after, step, atom, atomMember, keyEq⟩ := step_watcher_row profile prims c1 y1 sel1 rowMember
        have spaceFree : ∀ atom ∈ morkEraseSupport c1.1 (watcherWith y1),
            keyOf (equationOf (.symbol valueName)) atom = false → SymbolFree valueName atom := by
          intro atom member notEq
          rw [live1, rel.watcherTwin.agree, projWithout] at member
          exact freshWithout atom member notEq
        obtain ⟨x, instanceEq, notReport⟩ := reportFree spaceFree rowMember
        rw [instanceEq] at keyEq
        exact TauOutcome.spurious after x step ⟨atom, atomMember, keyEq⟩ notReport
  · -- No watcher remains.
    have absent1 : morkSupportContains c1.1 watcherExec = false := by simpa using withW
    have absent2 : morkSupportContains c2.1 watcherExec = false := by
      cases present : morkSupportContains c2.1 watcherExec with
      | false => rfl
      | true => exact absurd (rel.watcherMono present) withW
    apply TauOutcome.same
    have spaces : c1.1 = c2.1 := by
      rw [← proj_self_of_absent absent1, rel.watcherTwin.agree, proj_self_of_absent absent2]
    exact Prod.ext spaces rel.watcherTwin.external

/-! ## Reports -/

/-- `(out x)` is reported: some configuration the run reaches holds an atom with its key. -/
def ReportsKey (profile : BuildProfile) (prims : Primitives) (start : Config) (x : Atom) : Prop :=
  ∃ n c, runN profile prims n start = some c ∧ ∃ atom ∈ c.1, morkSupportKey atom = morkSupportKey (outOf x)

theorem out_not_watcherKey {x atom : Atom} (keyEq : morkSupportKey atom = morkSupportKey (outOf x)) :
    keyOf watcherExec atom = false := by
  cases watcherKey : keyOf watcherExec atom with
  | false => rfl
  | true =>
      exfalso
      simp only [keyOf, sameMorkSupportAtom, decide_eq_true_eq] at watcherKey
      have same : morkSupportKey (outOf x) = morkSupportKey watcherExec := keyEq.symm.trans watcherKey
      unfold outOf at same
      obtain ⟨others, othersEq, len⟩ := expression_of_same_key same
      injection othersEq with listEq
      rw [← listEq] at len
      simp at len

/-- Twins outside the watcher hold the same reports. -/
theorem reports_twin {c1 c2 : Config} (twin : Twin watcherExec c1 c2) (x : Atom) :
    (∃ atom ∈ c1.1, morkSupportKey atom = morkSupportKey (outOf x)) ↔
      ∃ atom ∈ c2.1, morkSupportKey atom = morkSupportKey (outOf x) := by
  constructor
  · rintro ⟨atom, member, keyEq⟩
    have inProj := mem_proj_of_mem member (out_not_watcherKey keyEq)
    rw [twin.agree] at inProj
    exact ⟨atom, mem_of_mem_proj inProj, keyEq⟩
  · rintro ⟨atom, member, keyEq⟩
    have inProj := mem_proj_of_mem member (out_not_watcherKey keyEq)
    rw [← twin.agree] at inProj
    exact ⟨atom, mem_of_mem_proj inProj, keyEq⟩

theorem runN_add (profile : BuildProfile) (prims : Primitives) :
    ∀ (first second : ℕ) (c : Config),
      runN profile prims (first + second) c = (runN profile prims first c).bind (runN profile prims second)
  | 0, second, c => by simp [runN]
  | first + 1, second, c => by
      rw [show first + 1 + second = (first + second) + 1 by omega]
      simp only [runN]
      cases mainlineStep profile prims c.2 c.1 with
      | next space after => exact runN_add profile prims first second (space, after)
      | _ => rfl

theorem runN_none_add {profile : BuildProfile} {prims : Primitives} {n : ℕ} {c : Config}
    (stopped : runN profile prims n c = none) (more : ℕ) : runN profile prims (n + more) c = none := by
  rw [runN_add, stopped]
  rfl

/-! ## The starting spaces -/

/-- A list loaded as a space: repeated physical keys are dropped. -/
def support (atoms : List Atom) : List Atom := atoms.foldl morkInsertSupport []

theorem support_eq_applyOps (start atoms : List Atom) :
    atoms.foldl morkInsertSupport start = applyOps start (atoms.map .ins) := by
  induction atoms generalizing start with
  | nil => rfl
  | cons atom rest ih => simp [applyOps, applyOp, ih]

theorem support_nodup (atoms : List Atom) : MorkSupportNodup (support atoms) := by
  unfold support
  rw [support_eq_applyOps]
  exact applyOps_nodup _ [] (by simp [MorkSupportNodup])

theorem proj_support_cons {target : Atom} (rest : List Atom) :
    proj (keyOf target) (support (target :: rest)) = proj (keyOf target) (support rest) := by
  unfold support
  simp only [List.foldl_cons]
  rw [support_eq_applyOps, support_eq_applyOps]
  apply proj_applyOps_congr (keyOf_keyInvariant target)
  simp [morkInsertSupport, morkSupportContains, morkSupportFind?, proj, keyOf, sameMorkSupportAtom]

theorem contains_insertAll : ∀ (atoms : List Atom) (start : List Atom) (target : Atom),
    morkSupportContains start target = true →
      morkSupportContains (atoms.foldl morkInsertSupport start) target = true
  | [], _, _, present => present
  | atom :: rest, start, target, present => by
      simp only [List.foldl_cons]
      exact contains_insertAll rest _ target (morkSupportContains_morkInsertSupport_of_contains start atom target present)

/-- The three starting configurations. -/
def ownStart (external : ExternalState) (expansion : List Atom) : Config := (support expansion, external)
def withStart (external : ExternalState) (expansion : List Atom) (value : Atom) : Config :=
  (support (watcherExec :: equationOf value :: expansion), external)
def withoutStart (external : ExternalState) (expansion : List Atom) (value : Atom) : Config :=
  (support (equationOf value :: expansion), external)

theorem start_rel (external : ExternalState) (expansion : List Atom) (value : Atom) :
    PhaseRel value (ownStart external expansion) (withStart external expansion value)
      (withoutStart external expansion value) := by
  refine ⟨⟨proj_support_cons _, rfl, support_nodup _, support_nodup _⟩,
    ⟨proj_support_cons _, rfl, support_nodup _, support_nodup _⟩, ?_⟩
  intro _
  simp only [withStart, support, List.foldl_cons]
  apply contains_insertAll
  apply contains_insertAll [equationOf value]
  simp [morkInsertSupport, morkSupportContains, morkSupportFind?, sameMorkSupportAtom]

/-! ## The target: both contexts report alike, or one of them misreports -/

/-- **For every expansion of the caller there is a value for which the run with the watcher and
the run without it report alike, or the run with it reports something other than `(out N)`, or
the run without it reports at all.** -/
theorem target_alternatives (profile : BuildProfile) (prims : Primitives) (external : ExternalState)
    (expansion : List Atom) :
    ∃ valueName : String, valueName ≠ "g" ∧
      ((∀ x, ReportsKey profile prims (withStart external expansion (.symbol valueName)) x ↔
          ReportsKey profile prims (withoutStart external expansion (.symbol valueName)) x) ∨
        (∃ x, ReportsKey profile prims (withStart external expansion (.symbol valueName)) x ∧
          morkSupportKey (outOf x) ≠ morkSupportKey (outOf (.symbol valueName))) ∨
        ∃ x, ReportsKey profile prims (withoutStart external expansion (.symbol valueName)) x) := by
  classical
  let own := ownStart external expansion
  by_cases forever : ∀ n, ∃ c, runN profile prims n own = some c ∧ Below c
  · -- The watcher never fires: the two runs agree at every step.
    refine ⟨"v", by decide, Or.inl fun x => ?_⟩
    have atStep : ∀ n, ∃ c1 c2, runN profile prims n (withStart external expansion (.symbol "v")) = some c1 ∧
        runN profile prims n (withoutStart external expansion (.symbol "v")) = some c2 ∧
        Twin watcherExec c1 c2 := by
      intro n
      obtain ⟨c0, run0, _⟩ := forever n
      obtain ⟨c1, c2, run1, run2, rel⟩ := phase_simulation profile prims (.symbol "v") n own _ _ c0
        (start_rel external expansion (.symbol "v")) run0
        (fun k _ ck runK => by obtain ⟨c, runC, below⟩ := forever k; rw [runK] at runC; cases runC; exact below)
      exact ⟨c1, c2, run1, run2, rel.watcherTwin⟩
    constructor
    · rintro ⟨n, c, run, reported⟩
      obtain ⟨c1, c2, run1, run2, twin⟩ := atStep n
      rw [run] at run1; cases run1
      exact ⟨n, c2, run2, (reports_twin twin x).1 reported⟩
    · rintro ⟨n, c, run, reported⟩
      obtain ⟨c1, c2, run1, run2, twin⟩ := atStep n
      rw [run] at run2; cases run2
      exact ⟨n, c1, run1, (reports_twin twin x).2 reported⟩
  · -- The phase ends at the least step where the own run stops being below the watcher.
    push Not at forever
    let τ := Nat.find forever
    have τSpec := Nat.find_spec forever
    have τMin : ∀ k < τ, ∃ c, runN profile prims k own = some c ∧ Below c := by
      intro k lt
      have := Nat.find_min forever lt
      push Not at this
      exact this
    have belowBefore : ∀ k < τ, ∀ ck, runN profile prims k own = some ck → Below ck := by
      intro k lt ck runK
      obtain ⟨c, runC, below⟩ := τMin k lt
      rw [runK] at runC; cases runC; exact below
    cases ownAt : runN profile prims τ own with
    | none =>
        -- The own run aborted while still below the watcher; the others abort with it.
        refine ⟨"v", by decide, Or.inl fun x => ?_⟩
        have τPos : 0 < τ := by
          rcases Nat.eq_zero_or_pos τ with zero | pos
          · have := ownAt; rw [zero] at this; simp [runN] at this
          · exact pos
        obtain ⟨τ', τEq⟩ : ∃ τ', τ = τ' + 1 := ⟨τ - 1, by omega⟩
        obtain ⟨c', run', below'⟩ := τMin τ' (by omega)
        obtain ⟨c1', c2', run1', run2', rel'⟩ := phase_simulation profile prims (.symbol "v") τ' own _ _ c'
          (start_rel external expansion (.symbol "v")) run' (fun k lt ck runK => belowBefore k (by omega) ck runK)
        have stopped : runN profile prims τ (withStart external expansion (.symbol "v")) = none ∧
            runN profile prims τ (withoutStart external expansion (.symbol "v")) = none := by
          rcases phase_step profile prims (.symbol "v") rel' below' with
            ⟨fault, _, abort1, abort2⟩ | ⟨own'', _, _, stepOwn, _, _, _⟩
          · rw [τEq, runN_add, runN_add, run1', run2']
            simp [runN, abort1, abort2]
          · exfalso
            rw [τEq, runN_add, run'] at ownAt
            simp [runN, stepOwn] at ownAt
        have atStep : ∀ n, n < τ → ∃ c1 c2, runN profile prims n (withStart external expansion (.symbol "v")) = some c1 ∧
            runN profile prims n (withoutStart external expansion (.symbol "v")) = some c2 ∧ Twin watcherExec c1 c2 := by
          intro n lt
          obtain ⟨c0, run0, _⟩ := τMin n lt
          obtain ⟨c1, c2, run1, run2, rel⟩ := phase_simulation profile prims (.symbol "v") n own _ _ c0
            (start_rel external expansion (.symbol "v")) run0 (fun k lt' ck runK => belowBefore k (by omega) ck runK)
          exact ⟨c1, c2, run1, run2, rel.watcherTwin⟩
        constructor
        · rintro ⟨n, c, run, reported⟩
          by_cases lt : n < τ
          · obtain ⟨c1, c2, run1, run2, twin⟩ := atStep n lt
            rw [run] at run1; cases run1
            exact ⟨n, c2, run2, (reports_twin twin x).1 reported⟩
          · have := runN_none_add stopped.1 (n - τ)
            rw [show τ + (n - τ) = n by omega, run] at this
            cases this
        · rintro ⟨n, c, run, reported⟩
          by_cases lt : n < τ
          · obtain ⟨c1, c2, run1, run2, twin⟩ := atStep n lt
            rw [run] at run2; cases run2
            exact ⟨n, c1, run1, (reports_twin twin x).2 reported⟩
          · have := runN_none_add stopped.2 (n - τ)
            rw [show τ + (n - τ) = n by omega, run] at this
            cases this
    | some c0 =>
        have notBelow : ¬ Below c0 := fun below => τSpec c0 ownAt below
        let valueName := freshSymbolFor c0.1
        refine ⟨valueName, freshSymbol_ne_g c0.1, ?_⟩
        obtain ⟨c1, c2, run1, run2, rel⟩ := phase_simulation profile prims (.symbol valueName) τ own _ _ c0
          (start_rel external expansion (.symbol valueName)) ownAt belowBefore
        have before : ∀ n, n < τ → ∃ c1 c2,
            runN profile prims n (withStart external expansion (.symbol valueName)) = some c1 ∧
            runN profile prims n (withoutStart external expansion (.symbol valueName)) = some c2 ∧
            Twin watcherExec c1 c2 := by
          intro n lt
          obtain ⟨c0', run0, _⟩ := τMin n lt
          obtain ⟨c1', c2', run1', run2', rel'⟩ := phase_simulation profile prims (.symbol valueName) n own _ _ c0'
            (start_rel external expansion (.symbol valueName)) run0 (fun k lt' ck runK => belowBefore k (by omega) ck runK)
          exact ⟨c1', c2', run1', run2', rel'.watcherTwin⟩
        -- Shorthands for the two runs.
        set withRun := withStart external expansion (.symbol valueName)
        set withoutRun := withoutStart external expansion (.symbol valueName)
        rcases tau_outcome profile prims valueName rel notBelow
            (fun atom member => freshSymbol_not_occurs member) (freshSymbol_ne_g c0.1) with
          same | ⟨after, step1, step2⟩ | step1 | ⟨after, x, step1, reported, notReport⟩ | ⟨after, x, step2, reported⟩
        · -- The runs coincide from the end of the phase.
          refine Or.inl fun x => ⟨?_, ?_⟩
          · rintro ⟨n, c, run, reported⟩
            by_cases lt : n < τ
            · obtain ⟨c1', c2', run1', run2', twin⟩ := before n lt
              rw [run] at run1'; cases run1'
              exact ⟨n, c2', run2', (reports_twin twin x).1 reported⟩
            · refine ⟨n, c, ?_, reported⟩
              rw [show n = τ + (n - τ) by omega, runN_add, run2, ← same]
              rw [show n = τ + (n - τ) by omega, runN_add, run1] at run
              exact run
          · rintro ⟨n, c, run, reported⟩
            by_cases lt : n < τ
            · obtain ⟨c1', c2', run1', run2', twin⟩ := before n lt
              rw [run] at run2'; cases run2'
              exact ⟨n, c1', run1', (reports_twin twin x).2 reported⟩
            · refine ⟨n, c, ?_, reported⟩
              rw [show n = τ + (n - τ) by omega, runN_add, run1, same]
              rw [show n = τ + (n - τ) by omega, runN_add, run2] at run
              exact run
        · -- Both watchers fire without rows.
          refine Or.inl fun x => ⟨?_, ?_⟩
          · rintro ⟨n, c, run, reported⟩
            by_cases lt : n < τ
            · obtain ⟨c1', c2', run1', run2', twin⟩ := before n lt
              rw [run] at run1'; cases run1'
              exact ⟨n, c2', run2', (reports_twin twin x).1 reported⟩
            · by_cases atTau : n = τ
              · subst atTau
                rw [run1] at run; cases run
                exact ⟨τ, c2, run2, (reports_twin rel.watcherTwin x).1 reported⟩
              · refine ⟨n, c, ?_, reported⟩
                rw [show n = τ + 1 + (n - τ - 1) by omega, runN_add, runN_add, run2]
                rw [show n = τ + 1 + (n - τ - 1) by omega, runN_add, runN_add, run1] at run
                simp only [Option.bind_some, runN, step1, step2] at run ⊢
                exact run
          · rintro ⟨n, c, run, reported⟩
            by_cases lt : n < τ
            · obtain ⟨c1', c2', run1', run2', twin⟩ := before n lt
              rw [run] at run2'; cases run2'
              exact ⟨n, c1', run1', (reports_twin twin x).2 reported⟩
            · by_cases atTau : n = τ
              · subst atTau
                rw [run2] at run; cases run
                exact ⟨τ, c1, run1, (reports_twin rel.watcherTwin x).2 reported⟩
              · refine ⟨n, c, ?_, reported⟩
                rw [show n = τ + 1 + (n - τ - 1) by omega, runN_add, runN_add, run1]
                rw [show n = τ + 1 + (n - τ - 1) by omega, runN_add, runN_add, run2] at run
                simp only [Option.bind_some, runN, step1, step2] at run ⊢
                exact run
        · -- Only the run with the watcher has one; it becomes the other run one step later.
          refine Or.inl fun x => ⟨?_, ?_⟩
          · rintro ⟨n, c, run, reported⟩
            by_cases lt : n < τ
            · obtain ⟨c1', c2', run1', run2', twin⟩ := before n lt
              rw [run] at run1'; cases run1'
              exact ⟨n, c2', run2', (reports_twin twin x).1 reported⟩
            · by_cases atTau : n = τ
              · subst atTau
                rw [run1] at run; cases run
                exact ⟨τ, c2, run2, (reports_twin rel.watcherTwin x).1 reported⟩
              · refine ⟨n - 1, c, ?_, reported⟩
                rw [show n - 1 = τ + (n - τ - 1) by omega, runN_add, run2]
                rw [show n = τ + 1 + (n - τ - 1) by omega, runN_add, runN_add, run1] at run
                simp only [Option.bind_some, runN, step1] at run
                exact run
          · rintro ⟨n, c, run, reported⟩
            by_cases lt : n < τ
            · obtain ⟨c1', c2', run1', run2', twin⟩ := before n lt
              rw [run] at run2'; cases run2'
              exact ⟨n, c1', run1', (reports_twin twin x).2 reported⟩
            · refine ⟨n + 1, c, ?_, reported⟩
              rw [show n + 1 = τ + 1 + (n - τ) by omega, runN_add, runN_add, run1]
              rw [show n = τ + (n - τ) by omega, runN_add, run2] at run
              simp only [Option.bind_some, runN, step1]
              exact run
        · -- The watcher reports something other than `(out N)`.
          refine Or.inr (Or.inl ⟨x, ⟨τ + 1, (after, c1.2), ?_, reported⟩, notReport⟩)
          rw [runN_add, run1]
          simp [runN, step1]
        · -- The run without the watcher reports.
          refine Or.inr (Or.inr ⟨x, τ + 1, (after, c2.2), ?_, reported⟩)
          rw [runN_add, run2]
          simp [runN, step2]

/-! ## The extension on the window -/

theorem key_ne_of_length_ne {left right : List Atom} (lengths : left.length ≠ right.length) :
    morkSupportKey (.expression left) ≠ morkSupportKey (.expression right) := by
  intro same
  obtain ⟨others, othersEq, len⟩ := expression_of_same_key same
  injection othersEq with listEq
  subst listEq
  exact lengths len

theorem same_false_of_length_ne {left right : List Atom} (lengths : left.length ≠ right.length) :
    sameMorkSupportAtom (.expression left) (.expression right) = false := by
  simp [sameMorkSupportAtom, key_ne_of_length_ne lengths]

/-- The caller's scheduler shell. -/
def callerRaw : RawExecFact :=
  ⟨commaCaller, .expression [], .expression [.symbol ","], .expression [.symbol "O", callAtom]⟩

theorem extract_caller : extractRawExecFact commaCaller = some callerRaw := rfl

theorem extract_equation (value : Atom) : extractRawExecFact (equationOf value) = none := rfl

theorem extract_g (value : Atom) : extractRawExecFact (.expression [.symbol "g", value]) = none := rfl

theorem extract_out (value : Atom) : extractRawExecFact (outOf value) = none := rfl

theorem select_caller_first :
    selectNextScheduled [watcherRaw "z", callerRaw] = some callerRaw := by
  simp only [selectNextScheduled, List.foldl_cons, List.foldl_nil]
  rw [if_pos (by decide)]


/-- `(g N)`. -/
def gOf (value : Atom) : Atom := .expression [.symbol "g", value]

theorem same_watcher_equation (value : Atom) : sameMorkSupportAtom watcherExec (equationOf value) = false :=
  same_false_of_length_ne (by simp)
theorem same_equation_watcher (value : Atom) : sameMorkSupportAtom (equationOf value) watcherExec = false :=
  same_false_of_length_ne (by simp)
theorem same_equation_caller (value : Atom) : sameMorkSupportAtom (equationOf value) commaCaller = false :=
  same_false_of_length_ne (by simp)
theorem same_watcher_caller : sameMorkSupportAtom watcherExec commaCaller = false := by decide
theorem same_caller_self : sameMorkSupportAtom commaCaller commaCaller = true := by simp [sameMorkSupportAtom]
theorem same_watcher_self : sameMorkSupportAtom watcherExec watcherExec = true := by simp [sameMorkSupportAtom]
theorem same_watcher_g (value : Atom) : sameMorkSupportAtom watcherExec (gOf value) = false :=
  same_false_of_length_ne (by simp)
theorem same_g_watcher (value : Atom) : sameMorkSupportAtom (gOf value) watcherExec = false :=
  same_false_of_length_ne (by simp)
theorem same_equation_g (value other : Atom) : sameMorkSupportAtom (equationOf value) (gOf other) = false :=
  same_false_of_length_ne (by simp)
theorem same_equation_out (value other : Atom) : sameMorkSupportAtom (equationOf value) (outOf other) = false :=
  same_false_of_length_ne (by simp)
theorem same_g_out (value other : Atom) : sameMorkSupportAtom (gOf value) (outOf other) = false := by
  simp [sameMorkSupportAtom, gOf, g_out_key_ne]

theorem support_with (value : Atom) :
    support [watcherExec, equationOf value, commaCaller] = [watcherExec, equationOf value, commaCaller] := by
  simp [support, morkInsertSupport, morkSupportContains, morkSupportFind?, same_watcher_equation,
    same_watcher_caller, same_equation_caller]

theorem support_without (value : Atom) :
    support [equationOf value, commaCaller] = [equationOf value, commaCaller] := by
  simp [support, morkInsertSupport, morkSupportContains, morkSupportFind?, same_equation_caller]

/-- The caller's directive in the extension. -/
def callerDirective : CallingDirective :=
  ⟨commaCaller, .compat [], .sinks [.call (.symbol "f") (.symbol "a") "r"
    [.core (.add (.expression [.symbol "g", .var "r"]))]]⟩

theorem decode_caller (profile : BuildProfile) :
    decodeCallingDirective profile callerRaw = .ok (some callerDirective) := rfl

theorem insert_absent {space : List Atom} {atom : Atom}
    (absent : ∀ other ∈ space, sameMorkSupportAtom other atom = false) :
    morkInsertSupport space atom = space ++ [atom] := by
  have none : space.find? (fun other => sameMorkSupportAtom other atom) = none :=
    List.find?_eq_none.2 fun other member => by simp [absent other member]
  simp [morkInsertSupport, morkSupportContains, morkSupportFind?, none]

theorem caller_fires {table : ProviderTable} (noF : table "f" = none) (prims : Primitives)
    (external : ExternalState) (context : List Atom) (value : Atom)
    (contextEquations : equationResults (context ++ [commaCaller]) (.symbol "f") (.symbol "a") = [value])
    (notCaller : ∀ atom ∈ context, sameMorkSupportAtom atom commaCaller = false)
    (notG : ∀ atom ∈ context, sameMorkSupportAtom atom (gOf value) = false) :
    fireCalling prims table external (context ++ [commaCaller]) callerDirective =
      .ok (context ++ [gOf value], external) := by
  have live : morkEraseSupport (context ++ [commaCaller]) commaCaller = context := by
    simp only [morkEraseSupport, List.filter_append, List.filter_cons, List.filter_nil, same_caller_self]
    simp only [Bool.not_true, Bool.false_eq_true, if_false, List.append_nil]
    exact List.filter_eq_self.2 fun atom member => by simp [notCaller atom member]
  have read : morkInsertSupport context commaCaller = context ++ [commaCaller] := insert_absent notCaller
  have gInsert : morkInsertSupport context (gOf value) = context ++ [gOf value] := insert_absent notG
  have rowNil : inputRow (inputSpecVariables (CallingInput.compat []).coverage) [] = [] := rfl
  have covered : ∀ value : Atom, ruleTemplateCovered (CallingInput.compat []).coverage [("r", value)]
      (.expression [.symbol "g", .var "r"]) = true := fun _ => rfl
  have instance_g : applySubst [("r", value)] (.expression [.symbol "g", .var "r"]) = gOf value := by
    simp [applySubst, applySubst.applySubstList, Subst.lookup, gOf]
  have single : morkInsertSupport [] (gOf value) = [gOf value] := rfl
  simp only [fireCalling, callerDirective, live, read]
  simp [single, callingRows, conjunctionRows, applyCallingSinks, callingEager, finalizeCallingSink, FunctionCalls.callRows,
    rowNil, applySubst_symbol, resolveCall, noF, contextEquations, applyMainlineSinks, eagerOutputs,
    finalizeMainlineSink, staged, instances, instantiateRuleTemplateAtom?, covered, instance_g, morkUnionSupport,
    gInsert, bind, Except.bind, pure, Except.pure]


/-! ## The extension's runs on the window -/

/-- Runs of the extension as partial configurations, as `runN`. -/
def callingRunN (profile : BuildProfile) (prims : Primitives) (table : ProviderTable) : ℕ → Config → Option Config
  | 0, c => some c
  | n + 1, c =>
      match callingStep profile prims table c.2 c.1 with
      | .next space after => callingRunN profile prims table n (space, after)
      | _ => none

/-- The extension reports `(out x)`, up to the kernel's identification of atoms. -/
def SourceReportsKey (profile : BuildProfile) (prims : Primitives) (table : ProviderTable) (start : Config)
    (x : Atom) : Prop :=
  ∃ n c, callingRunN profile prims table n start = some c ∧
    ∃ atom ∈ c.1, morkSupportKey atom = morkSupportKey (outOf x)

theorem select_single {α : Type} [SchedulerKey α] (fact : α) : selectNextScheduled [fact] = some fact := rfl

theorem cRaw_with (value : Atom) :
    WQComputable.cRawExecFacts [watcherExec, equationOf value, commaCaller] = [watcherRaw "z", callerRaw] := rfl

theorem cRaw_without (value : Atom) :
    WQComputable.cRawExecFacts [equationOf value, commaCaller] = [callerRaw] := rfl

theorem equations_with (value : Atom) :
    equationResults ([watcherExec, equationOf value] ++ [commaCaller]) (.symbol "f") (.symbol "a") = [value] := by
  simp [equationResults, equationOf, watcherExec, commaCaller]

theorem equations_without (value : Atom) :
    equationResults ([equationOf value] ++ [commaCaller]) (.symbol "f") (.symbol "a") = [value] := by
  simp [equationResults, equationOf, commaCaller]

theorem source_step_caller_with {table : ProviderTable} (noF : table "f" = none) (profile : BuildProfile)
    (prims : Primitives) (external : ExternalState) (value : Atom) :
    callingStep profile prims table external [watcherExec, equationOf value, commaCaller] =
      .next [watcherExec, equationOf value, gOf value] external := by
  have fired := caller_fires noF prims external [watcherExec, equationOf value] value (equations_with value)
    (by simp [same_watcher_caller, same_equation_caller]) (by simp [same_watcher_g, same_equation_g])
  simp only [List.cons_append, List.nil_append] at fired
  simp only [callingStep, cRaw_with, select_caller_first, decode_caller, fired]

theorem source_step_caller_without {table : ProviderTable} (noF : table "f" = none) (profile : BuildProfile)
    (prims : Primitives) (external : ExternalState) (value : Atom) :
    callingStep profile prims table external [equationOf value, commaCaller] =
      .next [equationOf value, gOf value] external := by
  have fired := caller_fires noF prims external [equationOf value] value (equations_without value)
    (by simp [same_equation_caller]) (by simp [same_equation_g])
  simp only [List.cons_append, List.nil_append] at fired
  simp only [callingStep, cRaw_without, select_single, decode_caller, fired]

theorem cRaw_watcher_g (value : Atom) :
    WQComputable.cRawExecFacts [watcherExec, equationOf value, gOf value] = [watcherRaw "z"] := rfl

theorem watcherRows_source (valueName : String) :
    watcherRows "z" [watcherExec, equationOf (.symbol valueName), gOf (.symbol valueName)] =
      [[("z", .symbol valueName)]] := by
  have erased : morkEraseSupport [watcherExec, equationOf (.symbol valueName), gOf (.symbol valueName)]
      (watcherWith "z") = [equationOf (.symbol valueName), gOf (.symbol valueName)] := by
    rw [← watcherExec_eq]
    simp [morkEraseSupport, same_watcher_self, same_equation_watcher, same_g_watcher]
  have inserted : morkInsertSupport [equationOf (.symbol valueName), gOf (.symbol valueName)] (watcherWith "z") =
      [equationOf (.symbol valueName), gOf (.symbol valueName), watcherExec] := by
    rw [← watcherExec_eq]
    exact insert_absent (by simp [same_equation_watcher, same_g_watcher])
  unfold watcherRows
  rw [erased, inserted]
  rfl

theorem source_step_watcher {table : ProviderTable} (profile : BuildProfile) (prims : Primitives)
    (external : ExternalState) (valueName : String) :
    callingStep profile prims table external
        [watcherExec, equationOf (.symbol valueName), gOf (.symbol valueName)] =
      .next [equationOf (.symbol valueName), gOf (.symbol valueName), outOf (.symbol valueName)] external := by
  have erased : morkEraseSupport [watcherExec, equationOf (.symbol valueName), gOf (.symbol valueName)]
      (watcherWith "z") = [equationOf (.symbol valueName), gOf (.symbol valueName)] := by
    rw [← watcherExec_eq]
    simp [morkEraseSupport, same_watcher_self, same_equation_watcher, same_g_watcher]
  have stagedOut : staged (MainlineInput.compat [gWith "z"]).coverage [[("z", .symbol valueName)]]
      (outOf (.var "z")) = [outOf (.symbol valueName)] := rfl
  have union : morkUnionSupport [equationOf (.symbol valueName), gOf (.symbol valueName)]
      [outOf (.symbol valueName)] =
      [equationOf (.symbol valueName), gOf (.symbol valueName), outOf (.symbol valueName)] :=
    insert_absent (by simp [same_equation_out, same_g_out])
  simp only [callingStep, cRaw_watcher_g, select_single,
    decodeCallingDirective_of_decodeDirective (decode_watcherWith profile "z"), fireCalling_base,
    fire_watcher, erased, watcherRows_source, stagedOut, union]

theorem source_quiescent_with {table : ProviderTable} (profile : BuildProfile) (prims : Primitives)
    (external : ExternalState) (value : Atom) :
    callingStep profile prims table external [equationOf value, gOf value, outOf value] = .quiescent := rfl

theorem source_quiescent_without {table : ProviderTable} (profile : BuildProfile) (prims : Primitives)
    (external : ExternalState) (value : Atom) :
    callingStep profile prims table external [equationOf value, gOf value] = .quiescent := rfl

theorem watcher_out_key_ne (x : Atom) : morkSupportKey watcherExec ≠ morkSupportKey (outOf x) :=
  key_ne_of_length_ne (by simp [outOf])

theorem caller_out_key_ne (x : Atom) : morkSupportKey commaCaller ≠ morkSupportKey (outOf x) :=
  key_ne_of_length_ne (by simp)

theorem start_with_source (external : ExternalState) (value : Atom) :
    withStart external [commaCaller] value = ([watcherExec, equationOf value, commaCaller], external) := by
  simp only [withStart, support_with]

theorem start_without_source (external : ExternalState) (value : Atom) :
    withoutStart external [commaCaller] value = ([equationOf value, commaCaller], external) := by
  simp only [withoutStart, support_without]

/-- **The extension with the watcher reports exactly `(out N)`.** -/
theorem source_with_reports {table : ProviderTable} (noF : table "f" = none) (profile : BuildProfile)
    (prims : Primitives) (external : ExternalState) (valueName : String) (x : Atom) :
    SourceReportsKey profile prims table (withStart external [commaCaller] (.symbol valueName)) x ↔
      morkSupportKey (outOf x) = morkSupportKey (outOf (.symbol valueName)) := by
  rw [start_with_source]
  constructor
  · rintro ⟨n, c, run, atom, member, keyEq⟩
    match n with
    | 0 =>
        simp only [callingRunN, Option.some.injEq] at run
        subst run
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact absurd keyEq (watcher_out_key_ne x)
        · exact absurd keyEq (equation_out_key_ne _ x)
        · exact absurd keyEq (caller_out_key_ne x)
    | 1 =>
        simp only [callingRunN, source_step_caller_with noF, Option.some.injEq] at run
        subst run
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact absurd keyEq (watcher_out_key_ne x)
        · exact absurd keyEq (equation_out_key_ne _ x)
        · exact absurd keyEq (g_out_key_ne _ x)
    | 2 =>
        simp only [callingRunN, source_step_caller_with noF, source_step_watcher, Option.some.injEq] at run
        subst run
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact absurd keyEq (equation_out_key_ne _ x)
        · exact absurd keyEq (g_out_key_ne _ x)
        · exact keyEq.symm
    | n + 3 =>
        simp [callingRunN, source_step_caller_with noF, source_step_watcher, source_quiescent_with] at run
  · intro keyEq
    refine ⟨2, ([equationOf (.symbol valueName), gOf (.symbol valueName), outOf (.symbol valueName)], external),
      ?_, outOf (.symbol valueName), by simp, keyEq.symm⟩
    simp only [callingRunN, source_step_caller_with noF, source_step_watcher]

/-- **The extension without the watcher reports nothing.** -/
theorem source_without_silent {table : ProviderTable} (noF : table "f" = none) (profile : BuildProfile)
    (prims : Primitives) (external : ExternalState) (valueName : String) (x : Atom) :
    ¬ SourceReportsKey profile prims table (withoutStart external [commaCaller] (.symbol valueName)) x := by
  rw [start_without_source]
  rintro ⟨n, c, run, atom, member, keyEq⟩
  match n with
  | 0 =>
      simp only [callingRunN, Option.some.injEq] at run
      subst run
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact equation_out_key_ne _ x keyEq
      · exact caller_out_key_ne x keyEq
  | 1 =>
      simp only [callingRunN, source_step_caller_without noF, Option.some.injEq] at run
      subst run
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact equation_out_key_ne _ x keyEq
      · exact g_out_key_ne _ x keyEq
  | n + 2 =>
      simp [callingRunN, source_step_caller_without noF, source_quiescent_without] at run

/-- **Synchronous call is not locally eliminable in the kernel.**  For every expansion of the
caller, chosen without seeing the context, some value `N` makes the expansion report differently
from the caller beside the watcher and `(= (f a) N)`, or beside `(= (f a) N)` alone.  Reports are
compared up to the kernel's identification of atoms, for every build profile, registry and
external state, and for every way the extension resolves `f` through the space's equations. -/
theorem call_not_locally_eliminable {table : ProviderTable} (noF : table "f" = none) (profile : BuildProfile)
    (prims : Primitives) (external : ExternalState) (expansion : List Atom) :
    ∃ valueName : String,
      ¬ ((∀ x, ReportsKey profile prims (withStart external expansion (.symbol valueName)) x ↔
            SourceReportsKey profile prims table (withStart external [commaCaller] (.symbol valueName)) x) ∧
         (∀ x, ReportsKey profile prims (withoutStart external expansion (.symbol valueName)) x ↔
            SourceReportsKey profile prims table (withoutStart external [commaCaller] (.symbol valueName)) x)) := by
  obtain ⟨valueName, _, alternatives⟩ := target_alternatives profile prims external expansion
  refine ⟨valueName, fun ⟨withSame, withoutSame⟩ => ?_⟩
  rcases alternatives with same | ⟨x, reported, notValue⟩ | ⟨x, reported⟩
  · have sourceReports := (source_with_reports noF profile prims external valueName (.symbol valueName)).2 rfl
    have targetWith := (withSame _).2 sourceReports
    exact source_without_silent noF profile prims external valueName _ ((withoutSame _).1 ((same _).1 targetWith))
  · exact notValue ((source_with_reports noF profile prims external valueName x).1 ((withSame x).1 reported))
  · exact source_without_silent noF profile prims external valueName x ((withoutSame x).1 reported)
/-! ## Locality is necessary: relocating the context's executables closes the window -/

/-- Move an executable one level up, to `(s L)`; other atoms are kept. -/
def relocate : Atom → Atom
  | .expression [.symbol "exec", location, input, output] =>
      .expression [.symbol "exec", .expression [.symbol "s", location], input, output]
  | atom => atom

/-- The caller as a join with the equation of `f`: `(exec () (, (= (f a) $r)) (O (+ (g $r))))`. -/
def joinCaller : Atom :=
  .expression [.symbol "exec", .expression [],
    .expression [.symbol ",", .expression [.symbol "=", .expression [.symbol "f", .symbol "a"], .var "r"]],
    .expression [.symbol "O", .expression [.symbol "+", .expression [.symbol "g", .var "r"]]]]

/-- The watcher, relocated: `(exec (s ()) (, (g $z)) (O (+ (out $z))))`. -/
def raisedWatcher : Atom := relocate watcherExec

theorem raisedWatcher_eq : raisedWatcher =
    .expression [.symbol "exec", .expression [.symbol "s", .expression []],
      .expression [.symbol ",", gWith "z"], .expression [.symbol "O", .expression [.symbol "+", outOf (.var "z")]]] := rfl

def joinRaw : RawExecFact :=
  ⟨joinCaller, .expression [],
    .expression [.symbol ",", .expression [.symbol "=", .expression [.symbol "f", .symbol "a"], .var "r"]],
    .expression [.symbol "O", .expression [.symbol "+", .expression [.symbol "g", .var "r"]]]⟩

def raisedRaw : RawExecFact :=
  ⟨raisedWatcher, .expression [.symbol "s", .expression []], .expression [.symbol ",", gWith "z"],
    .expression [.symbol "O", .expression [.symbol "+", outOf (.var "z")]]⟩

theorem same_raised_equation (value : Atom) : sameMorkSupportAtom raisedWatcher (equationOf value) = false :=
  same_false_of_length_ne (by simp)
theorem same_equation_raised (value : Atom) : sameMorkSupportAtom (equationOf value) raisedWatcher = false :=
  same_false_of_length_ne (by simp)
theorem same_raised_join : sameMorkSupportAtom raisedWatcher joinCaller = false := by decide
theorem same_equation_join (value : Atom) : sameMorkSupportAtom (equationOf value) joinCaller = false :=
  same_false_of_length_ne (by simp)
theorem same_join_self : sameMorkSupportAtom joinCaller joinCaller = true := by simp [sameMorkSupportAtom]
theorem same_raised_self : sameMorkSupportAtom raisedWatcher raisedWatcher = true := by simp [sameMorkSupportAtom]
theorem same_raised_g (value : Atom) : sameMorkSupportAtom raisedWatcher (gOf value) = false :=
  same_false_of_length_ne (by simp)
theorem same_g_raised (value : Atom) : sameMorkSupportAtom (gOf value) raisedWatcher = false :=
  same_false_of_length_ne (by simp)

theorem select_join_first : selectNextScheduled [raisedRaw, joinRaw] = some joinRaw := by
  simp only [selectNextScheduled, List.foldl_cons, List.foldl_nil]
  rw [if_pos (by decide)]

/-- The relocated contexts with the caller's join. -/
def raisedWithStart (external : ExternalState) (value : Atom) : Config :=
  (support [raisedWatcher, equationOf value, joinCaller], external)
def raisedWithoutStart (external : ExternalState) (value : Atom) : Config :=
  (support [equationOf value, joinCaller], external)

theorem raised_support_with (value : Atom) :
    support [raisedWatcher, equationOf value, joinCaller] = [raisedWatcher, equationOf value, joinCaller] := by
  simp [support, morkInsertSupport, morkSupportContains, morkSupportFind?, same_raised_equation,
    same_raised_join, same_equation_join]

theorem raised_support_without (value : Atom) :
    support [equationOf value, joinCaller] = [equationOf value, joinCaller] := by
  simp [support, morkInsertSupport, morkSupportContains, morkSupportFind?, same_equation_join]

theorem join_fires (prims : Primitives) (external : ExternalState) (context : List Atom) (valueName : String)
    (notJoin : ∀ atom ∈ context, sameMorkSupportAtom atom joinCaller = false)
    (notG : ∀ atom ∈ context, sameMorkSupportAtom atom (gOf (.symbol valueName)) = false)
    (rows : conjunctionRows (factorTag joinCaller) (context ++ [joinCaller]) 0 []
      [.expression [.symbol "=", .expression [.symbol "f", .symbol "a"], .var "r"]] =
        [[("r", .symbol valueName)]]) :
    fireDirective prims external (context ++ [joinCaller])
        ⟨joinCaller, .compat [.expression [.symbol "=", .expression [.symbol "f", .symbol "a"], .var "r"]],
          .sinks [.core (.add (.expression [.symbol "g", .var "r"]))]⟩ =
      .ok (context ++ [gOf (.symbol valueName)], external) := by
  have live : morkEraseSupport (context ++ [joinCaller]) joinCaller = context := by
    simp only [morkEraseSupport, List.filter_append, List.filter_cons, List.filter_nil, same_join_self]
    simp only [Bool.not_true, Bool.false_eq_true, if_false, List.append_nil]
    exact List.filter_eq_self.2 fun atom member => by simp [notJoin atom member]
  have read : morkInsertSupport context joinCaller = context ++ [joinCaller] := insert_absent notJoin
  have gInsert : morkInsertSupport context (gOf (.symbol valueName)) = context ++ [gOf (.symbol valueName)] :=
    insert_absent notG
  have stagedG : staged (MainlineInput.compat
      [.expression [.symbol "=", .expression [.symbol "f", .symbol "a"], .var "r"]]).coverage
      [[("r", .symbol valueName)]] (.expression [.symbol "g", .var "r"]) = [gOf (.symbol valueName)] := rfl
  have inputRows : ([[("r", Atom.symbol valueName)]] : List Subst).map (inputRow (inputSpecVariables
      (MainlineInput.compat [.expression [.symbol "=", .expression [.symbol "f", .symbol "a"], .var "r"]]).coverage)) =
      [[("r", .symbol valueName)]] := rfl
  simp only [fireDirective, live, read, mainlineRows, rows, bind, Except.bind, inputRows, applyMainlineSinks,
    List.foldl_cons, List.foldl_nil, eagerOutputs, stagedG, List.foldlM_cons, List.foldlM_nil,
    finalizeMainlineSink, pure, Except.pure, morkUnionSupport, gInsert]

def joinDirective : MainlineDirective :=
  ⟨joinCaller, .compat [.expression [.symbol "=", .expression [.symbol "f", .symbol "a"], .var "r"]],
    .sinks [.core (.add (.expression [.symbol "g", .var "r"]))]⟩

def raisedDirective : MainlineDirective :=
  ⟨raisedWatcher, .compat [gWith "z"], .sinks [.core (.add (outOf (.var "z")))]⟩

theorem decode_join (profile : BuildProfile) : decodeDirective profile joinRaw = .ok (some joinDirective) := rfl

theorem decode_raised (profile : BuildProfile) : decodeDirective profile raisedRaw = .ok (some raisedDirective) := rfl

theorem raised_step_join_with (profile : BuildProfile) (prims : Primitives) (external : ExternalState)
    (valueName : String) :
    mainlineStep profile prims external [raisedWatcher, equationOf (.symbol valueName), joinCaller] =
      .next [raisedWatcher, equationOf (.symbol valueName), gOf (.symbol valueName)] external := by
  have fired := join_fires prims external [raisedWatcher, equationOf (.symbol valueName)] valueName
    (by simp [same_raised_join, same_equation_join]) (by simp [same_raised_g, same_equation_g]) rfl
  simp only [List.cons_append, List.nil_append] at fired
  have sel : selectNextScheduled (WQComputable.cRawExecFacts
      [raisedWatcher, equationOf (.symbol valueName), joinCaller]) = some joinRaw := select_join_first
  simp only [mainlineStep, sel, decode_join, joinDirective, fired]

theorem raised_step_join_without (profile : BuildProfile) (prims : Primitives) (external : ExternalState)
    (valueName : String) :
    mainlineStep profile prims external [equationOf (.symbol valueName), joinCaller] =
      .next [equationOf (.symbol valueName), gOf (.symbol valueName)] external := by
  have fired := join_fires prims external [equationOf (.symbol valueName)] valueName
    (by simp [same_equation_join]) (by simp [same_equation_g]) rfl
  simp only [List.cons_append, List.nil_append] at fired
  have sel : selectNextScheduled (WQComputable.cRawExecFacts
      [equationOf (.symbol valueName), joinCaller]) = some joinRaw := rfl
  simp only [mainlineStep, sel, decode_join, joinDirective, fired]

theorem raised_step_watcher (profile : BuildProfile) (prims : Primitives) (external : ExternalState)
    (valueName : String) :
    mainlineStep profile prims external [raisedWatcher, equationOf (.symbol valueName), gOf (.symbol valueName)] =
      .next [equationOf (.symbol valueName), gOf (.symbol valueName), outOf (.symbol valueName)] external := by
  have live : morkEraseSupport [raisedWatcher, equationOf (.symbol valueName), gOf (.symbol valueName)]
      raisedWatcher = [equationOf (.symbol valueName), gOf (.symbol valueName)] := by
    simp [morkEraseSupport, same_raised_self, same_equation_raised, same_g_raised]
  have read : morkInsertSupport [equationOf (.symbol valueName), gOf (.symbol valueName)] raisedWatcher =
      [equationOf (.symbol valueName), gOf (.symbol valueName), raisedWatcher] :=
    insert_absent (by simp [same_equation_raised, same_g_raised])
  have union : morkUnionSupport [equationOf (.symbol valueName), gOf (.symbol valueName)]
      [outOf (.symbol valueName)] =
      [equationOf (.symbol valueName), gOf (.symbol valueName), outOf (.symbol valueName)] :=
    insert_absent (by simp [same_equation_out, same_g_out])
  have rows : conjunctionRows (factorTag raisedWatcher)
      [equationOf (.symbol valueName), gOf (.symbol valueName), raisedWatcher] 0 [] [gWith "z"] =
      [[("z", .symbol valueName)]] := rfl
  have stagedOut : staged (MainlineInput.compat [gWith "z"]).coverage [[("z", .symbol valueName)]]
      (outOf (.var "z")) = [outOf (.symbol valueName)] := rfl
  have inputRows : ([[("z", Atom.symbol valueName)]] : List Subst).map
      (inputRow (inputSpecVariables (MainlineInput.compat [gWith "z"]).coverage)) = [[("z", .symbol valueName)]] := rfl
  have sel : selectNextScheduled (WQComputable.cRawExecFacts
      [raisedWatcher, equationOf (.symbol valueName), gOf (.symbol valueName)]) = some raisedRaw := rfl
  simp only [mainlineStep, sel, decode_raised, raisedDirective, fireDirective, live, read, mainlineRows, rows,
    bind, Except.bind, inputRows, applyMainlineSinks, List.foldl_cons, List.foldl_nil, eagerOutputs, stagedOut,
    List.foldlM_cons, List.foldlM_nil, finalizeMainlineSink, pure, Except.pure, union]

theorem raised_quiescent_with (profile : BuildProfile) (prims : Primitives) (external : ExternalState)
    (value : Atom) : mainlineStep profile prims external [equationOf value, gOf value, outOf value] = .quiescent := rfl

theorem raised_quiescent_without (profile : BuildProfile) (prims : Primitives) (external : ExternalState)
    (value : Atom) : mainlineStep profile prims external [equationOf value, gOf value] = .quiescent := rfl

theorem raised_out_key_ne (x : Atom) : morkSupportKey raisedWatcher ≠ morkSupportKey (outOf x) :=
  key_ne_of_length_ne (by simp)

theorem join_out_key_ne (x : Atom) : morkSupportKey joinCaller ≠ morkSupportKey (outOf x) :=
  key_ne_of_length_ne (by simp)

theorem raised_start_with (external : ExternalState) (value : Atom) :
    raisedWithStart external value = ([raisedWatcher, equationOf value, joinCaller], external) := by
  simp only [raisedWithStart, raised_support_with]

theorem raised_start_without (external : ExternalState) (value : Atom) :
    raisedWithoutStart external value = ([equationOf value, joinCaller], external) := by
  simp only [raisedWithoutStart, raised_support_without]

/-- The configurations the relocated run with the watcher reaches. -/
theorem raised_runs_with (profile : BuildProfile) (prims : Primitives) (external : ExternalState)
    (valueName : String) (n : ℕ) (c : Config)
    (run : runN profile prims n ([raisedWatcher, equationOf (.symbol valueName), joinCaller], external) = some c) :
    c = ([raisedWatcher, equationOf (.symbol valueName), joinCaller], external) ∨
      c = ([raisedWatcher, equationOf (.symbol valueName), gOf (.symbol valueName)], external) ∨
      c = ([equationOf (.symbol valueName), gOf (.symbol valueName), outOf (.symbol valueName)], external) := by
  rcases n with _ | _ | _ | n
  · simp only [runN, Option.some.injEq] at run
    exact Or.inl run.symm
  · simp only [runN, raised_step_join_with, Option.some.injEq] at run
    exact Or.inr (Or.inl run.symm)
  · simp only [runN, raised_step_join_with, raised_step_watcher, Option.some.injEq] at run
    exact Or.inr (Or.inr run.symm)
  · simp [runN, raised_step_join_with, raised_step_watcher, raised_quiescent_with] at run

/-- The configurations the relocated run without the watcher reaches. -/
theorem raised_runs_without (profile : BuildProfile) (prims : Primitives) (external : ExternalState)
    (valueName : String) (n : ℕ) (c : Config)
    (run : runN profile prims n ([equationOf (.symbol valueName), joinCaller], external) = some c) :
    c = ([equationOf (.symbol valueName), joinCaller], external) ∨
      c = ([equationOf (.symbol valueName), gOf (.symbol valueName)], external) := by
  rcases n with _ | _ | n
  · simp only [runN, Option.some.injEq] at run
    exact Or.inl run.symm
  · simp only [runN, raised_step_join_without, Option.some.injEq] at run
    exact Or.inr run.symm
  · simp [runN, raised_step_join_without, raised_quiescent_without] at run

theorem raised_with_reports (profile : BuildProfile) (prims : Primitives) (external : ExternalState)
    (valueName : String) (x : Atom) :
    ReportsKey profile prims (raisedWithStart external (.symbol valueName)) x ↔
      morkSupportKey (outOf x) = morkSupportKey (outOf (.symbol valueName)) := by
  rw [raised_start_with]
  constructor
  · rintro ⟨n, c, run, atom, member, keyEq⟩
    rcases raised_runs_with profile prims external valueName n c run with rfl | rfl | rfl <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    · rcases member with rfl | rfl | rfl
      · exact absurd keyEq (raised_out_key_ne x)
      · exact absurd keyEq (equation_out_key_ne _ x)
      · exact absurd keyEq (join_out_key_ne x)
    · rcases member with rfl | rfl | rfl
      · exact absurd keyEq (raised_out_key_ne x)
      · exact absurd keyEq (equation_out_key_ne _ x)
      · exact absurd keyEq (g_out_key_ne _ x)
    · rcases member with rfl | rfl | rfl
      · exact absurd keyEq (equation_out_key_ne _ x)
      · exact absurd keyEq (g_out_key_ne _ x)
      · exact keyEq.symm
  · intro keyEq
    refine ⟨2, ([equationOf (.symbol valueName), gOf (.symbol valueName), outOf (.symbol valueName)], external),
      ?_, outOf (.symbol valueName), by simp, keyEq.symm⟩
    simp only [runN, raised_step_join_with, raised_step_watcher]

theorem raised_without_silent (profile : BuildProfile) (prims : Primitives) (external : ExternalState)
    (valueName : String) (x : Atom) :
    ¬ ReportsKey profile prims (raisedWithoutStart external (.symbol valueName)) x := by
  rw [raised_start_without]
  rintro ⟨n, c, run, atom, member, keyEq⟩
  rcases raised_runs_without profile prims external valueName n c run with rfl | rfl <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  · rcases member with rfl | rfl
    · exact equation_out_key_ne _ x keyEq
    · exact join_out_key_ne x keyEq
  · rcases member with rfl | rfl
    · exact equation_out_key_ne _ x keyEq
    · exact g_out_key_ne _ x keyEq

/-- **Relocation closes the window.**  The translation that moves every executable of the
context one level up, to `(s L)`, and turns the caller into a join with the equation of `f`
reports exactly what the extension reports, beside the watcher and without it, for every value.
It is compositional but not the identity on call-free atoms: locality is what the window uses. -/
theorem relocation_closes_window {table : ProviderTable} (noF : table "f" = none) (profile : BuildProfile)
    (prims : Primitives) (external : ExternalState) (valueName : String) :
    (∀ x, ReportsKey profile prims (raisedWithStart external (.symbol valueName)) x ↔
        SourceReportsKey profile prims table (withStart external [commaCaller] (.symbol valueName)) x) ∧
      ∀ x, ReportsKey profile prims (raisedWithoutStart external (.symbol valueName)) x ↔
        SourceReportsKey profile prims table (withoutStart external [commaCaller] (.symbol valueName)) x :=
  ⟨fun x => (raised_with_reports profile prims external valueName x).trans
      (source_with_reports noF profile prims external valueName x).symm,
    fun x => iff_of_false (raised_without_silent profile prims external valueName x)
      (source_without_silent noF profile prims external valueName x)⟩

end Mettapedia.Languages.ProcessCalculi.MORK.CallLocality

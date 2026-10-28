import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.CommutativeMatching

/-!
# Stored code is data: reading and taking never run it, and `eval` is a commit

A space can hold code: an atom whose subterms would have effects if evaluated, such as
`(add-atom &bank x)`. The Data comonad says how such atoms behave: read from a space they are
completed values, and running one needs `eval`, the counit. This module states that law for the
commits of `transform`, proves it for the compiled semantics, and shows what fails without it.

## Effects of code

Terms are those of `CommutativeMatching`. Three symbols are distinguished (`CodeSyms`): `emit` (an
`add-atom`: `emit(region, atom)` places `atom` at `region`), `quote`, and `placed`, the label of a
placed atom. `effects t` is what evaluating `t` does under MeTTa's default strategy: an `emit`
places its atom (its atom argument is not evaluated), a quotation does nothing, any other node
evaluates both children.

## The law, for the compiled semantics

* **What a firing makes is its template's instances** (`made_is_instance`): every occurrence a
  compiled commit makes carries a value equal, modulo `E`, to an instance of a template pattern.
  Nothing a source read or took contributes to what is made except through the template's
  variables, as data.
* **Hence stored code never writes outside the reader's own text** (`no_hidden_write`): with a sound
  matcher and sound keys, every made label is covered by the static make keys of the transform,
  whatever code the store holds.

## Without the law: evaluating instances

`eagerFootprint` adds to a footprint the effects of everything it makes: the instances are
evaluated where they land. This is MeTTa's default for code substituted into the argument of an
untyped constructor, and it is what the Prime draft does with source code passed through typed
`Atom` parameters into a body (probed; the probe in which code held as data ran an `add-atom` is
one instance).

* **It breaks static footprints** (`DataControls.eager_breaks_static`): a transform that reads stored
  code and makes `got(code)` makes, under eager instantiation, the code's placed atom, which its
  static footprint does not cover. Under the compiled semantics it makes only `got(code)`
  (`DataControls.data_copies_code`).
* **Quotation restores the law** (`eagerFootprint_eq_of_guarded`): when every variable of the template
  sits under `quote` and the template's own text has no unquoted `emit`, eager instantiation makes
  exactly what the compiled semantics makes.

## `eval` is a commit with a footprint

`evalTransform` is evaluation as a transform: take a request `req(code, nil)` and, for every effect of
the code, make it, in one commit. **Every row takes exactly one request, keeps nothing, queries nothing,
and makes exactly the effects of the requested code** (`evalTransform_row`, through
`everyFootprint_eval`). So running stored code is an explicit commit whose footprint is the code's
effects. Instances: evaluating `add-atom &bank bal` places `bal` at `bank`
(`DataControls.eval_runs_code`); evaluating quoted code runs nothing
(`DataControls.eval_quoted_runs_nothing`): one `eval` removes exactly one level of quotation. Its
static make keys are `any` (`DataControls.eval_static_any`): which regions an `eval` writes depends on
the code, so a footprint precise for an `eval` is known only once the code is (see
`HigherOrderFootprints`).

## What the comonad does and does not buy

The Data comonad of the Prime candidates is the product comonad with `eval` as counit; its laws are
definitional there. The content in the commit basis is operational: effects of stored code occur
only at an `eval` commit, and that is what keeps static footprints sound.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Reflection

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources.Commutative

universe uO uV uT uP uF

/-! ## Template instances -/

section Instances

variable {O : Type uO} [DecidableEq O] {V : Type uV} {T : Type uT} {P : Type uP}

/-- Keys that are the template patterns themselves: a pattern covers the values it solves. -/
def instanceKeys (L : TermLayer V T P) : RegionKeys T P P where
  covers q t := ∃ σ, L.Solves σ q t
  keys p := [p]
  apart _ _ := false
  apart_sound := by
    intro k k' apart
    cases apart

theorem instanceKeys_sound (L : TermLayer V T P) : (instanceKeys L).Sound L :=
  fun σ p _ solves => ⟨p, List.mem_singleton_self p, σ, solves⟩

/-- The static make keys of a source list are the keys of its template. -/
theorem static_makes {K : Type*} (R : RegionKeys T P K) (template : List P) :
    ∀ src : SourceList V T P, (src.static R template).makes = template.flatMap R.keys
  | .done => rfl
  | .cons s rest => by
      cases s <;> simp [SourceList.static, Source.static, static_makes R template rest]
  | .absent query rest => by simp [SourceList.static, static_makes R template rest]
  | .every rest => by simp [SourceList.static, static_makes R template rest]

variable {L : TermLayer V T P} {m : Matcher V T P} {label : O → T} {S : Finset O}

/-- **What a firing makes is its template's instances.** Every occurrence made by a compiled commit
carries a value that some template pattern solves, under some substitution. -/
theorem made_is_instance (sound : Matcher.Sound L m) {t : Transform V T P} {c : Commit O T}
    (fires : Fires L m label S t c) {o : O} (made : o ∈ c.made) :
    ∃ q ∈ t.template, ∃ σ, L.Solves σ q (label o) := by
  obtain ⟨x, member, -, commit⟩ := fires
  have within := static_covers (R := instanceKeys L) sound (instanceKeys_sound L) member
  obtain ⟨q, inKeys, σ, solves⟩ := commit.made_covered within made
  rw [static_makes] at inKeys
  simp only [instanceKeys, List.flatMap_singleton'] at inKeys
  exact ⟨q, by simpa using inKeys, σ, solves⟩

/-- **Stored code never writes outside the reader's own text.** With a sound matcher and sound keys,
every label a compiled commit makes is covered by the transform's static make keys. -/
theorem no_hidden_write {K : Type*} {R : RegionKeys T P K} (sound : Matcher.Sound L m)
    (keysSound : R.Sound L) {t : Transform V T P} {c : Commit O T} (fires : Fires L m label S t c)
    {o : O} (made : o ∈ c.made) : R.CoveredBy (t.static R).makes (label o) := by
  obtain ⟨x, member, -, commit⟩ := fires
  exact commit.made_covered (static_covers sound keysSound member) made

end Instances

/-! ## Effects of code -/

/-- The distinguished symbols of code. -/
structure CodeSyms (F : Type uF) where
  emit : F
  quote : F
  placed : F

section Effects

variable {F : Type uF} [DecidableEq F] (cs : CodeSyms F)

/-- **What evaluating a term does** under MeTTa's default strategy: an `emit` places its atom, a
quotation does nothing, any other node evaluates both children. -/
def effects : Tm F → List (Tm F)
  | .leaf _ => []
  | .node f l r =>
      if f = cs.quote then [] else if f = cs.emit then [.node cs.placed l r] else effects l ++ effects r

@[simp] theorem effects_quote (l r : Tm F) : effects cs (.node cs.quote l r) = [] := by
  simp [effects]

/-- A footprint whose made values are evaluated where they land: their effects are made too. -/
def eagerFootprint {O : Type uO} (fp : Footprint O (Tm F)) : Footprint O (Tm F) :=
  { fp with makes := fp.makes + fp.makes.bind fun t => (effects cs t : Multiset (Tm F)) }

variable {V : Type uV}

/-- A template pattern is **guarded** when every variable sits under `quote` and its own text has no
unquoted `emit`. -/
def Guarded : Pat V F → Prop
  | .var _ => False
  | .leaf _ => True
  | .node f p q => f = cs.quote ∨ (f ≠ cs.emit ∧ Guarded p ∧ Guarded q)

variable {cs}

/-- An instance of a guarded pattern has no effects. -/
theorem effects_inst_of_guarded (σ : Subst V (Tm F)) :
    ∀ {p : Pat V F} {u : Tm F}, Guarded cs p → p.inst σ = some u → effects cs u = []
  | .var _, _, guarded, _ => guarded.elim
  | .leaf a, u, _, inst => by
      simp only [Pat.inst, Option.some.injEq] at inst
      subst inst
      rfl
  | .node f p q, u, guarded, inst => by
      obtain ⟨l, r, instP, instQ, rfl⟩ := Pat.inst_node_eq_some.mp inst
      rcases guarded with isQuote | ⟨notEmit, guardedP, guardedQ⟩
      · subst isQuote
        exact effects_quote cs l r
      · by_cases isQuote : f = cs.quote
        · subst isQuote
          exact effects_quote cs l r
        · simp only [effects, isQuote, notEmit, if_false,
            effects_inst_of_guarded σ guardedP instP, effects_inst_of_guarded σ guardedQ instQ,
            List.append_nil]

variable [DecidableEq V] {O : Type uO} [DecidableEq O] {label : O → Tm F} {S : Finset O}

/-- **Quotation restores the law.** For a transform whose template patterns are all guarded, eager
instantiation makes exactly what the compiled semantics makes, for every row (syntactic layer). -/
theorem eagerFootprint_eq_of_guarded {t : Transform V (Tm F) (Pat V F)}
    (guarded : ∀ q ∈ t.template, Guarded cs q) {x : Subst V (Tm F) × List (Pick O (Tm F))}
    (member : x ∈ t.rows (termLayer (fun _ => false)) (cmatch (fun _ => false)) label S) :
    eagerFootprint cs (footprintOf x.2) = footprintOf x.2 := by
  have within := static_covers (R := instanceKeys (termLayer (V := V) (fun _ : F => false)))
    (cmatch_sound (comm := fun _ => false)) (instanceKeys_sound _) member
  have noEffects : ∀ v ∈ (footprintOf x.2).makes, effects cs v = [] := by
    intro v made
    obtain ⟨q, inKeys, σ, ⟨u, inst, same⟩⟩ := within.makes v made
    rw [static_makes] at inKeys
    simp only [instanceKeys, List.flatMap_singleton'] at inKeys
    have equal : u = v := ceq_noComm_iff.mp same
    subst equal
    exact effects_inst_of_guarded σ (guarded q (by simpa using inKeys)) inst
  have key : (footprintOf x.2).makes.bind (fun t => (effects cs t : Multiset (Tm F))) = 0 :=
    Multiset.eq_zero_of_forall_notMem fun a member => by
      obtain ⟨v, made, inEff⟩ := Multiset.mem_bind.mp member
      rw [noEffects v made] at inEff
      simp at inEff
  unfold eagerFootprint
  rw [key, add_zero]

end Effects

/-! ## `eval` as a transform, in general -/

section EvalTransform

variable {F : Type uF} [DecidableEq F] (cs : CodeSyms F) (req nilS : F)

/-- What the `let` source of evaluation computes: the effects of the requested code. -/
def requestedEffects (σ : Subst ℕ (Tm F)) : List (Tm F) :=
  match σ 0 with
  | some c => effects cs c
  | none => []

/-- **Evaluation as a transform**: take a request `req(code, nil)` and, for every effect of the code,
make it, in one commit. -/
def evalTransform : Transform ℕ (Tm F) (Pat ℕ F) :=
  ⟨.cons (.take (.node req (.var 0) (.leaf nilS)))
    (.every (.cons (.letBind (.var 1) (requestedEffects cs)) .done)), [.var 1]⟩

/-- The substitution a request binds. -/
def requestSubst (c : Tm F) : Subst ℕ (Tm F) := Function.update (fun _ => none) 0 (some c)

variable {cs req nilS}

theorem rawMatch_request (t : Tm F) :
    rawMatch (fun _ => false) (.node req (.var 0) (.leaf nilS)) (fun _ => none) t =
      match t with
      | .node g c r => if req = g ∧ r = .leaf nilS then [requestSubst c] else []
      | .leaf _ => [] := by
  cases t with
  | leaf a => simp [rawMatch]
  | node g c r =>
      by_cases same : req = g
      · subst same
        by_cases nilR : r = .leaf nilS
        · subst nilR
          simp [rawMatch, requestSubst]
        · simp [rawMatch, nilR]
      · simp [rawMatch, same]

theorem mem_cmatch_request {t : Tm F} {τ : Subst ℕ (Tm F)} :
    τ ∈ cmatch (fun _ => false) (.node req (.var 0) (.leaf nilS)) (fun _ => none) t ↔
      ∃ c, t = .node req c (.leaf nilS) ∧ τ = requestSubst c := by
  unfold cmatch
  rw [rawMatch_request]
  cases t with
  | leaf a => simp
  | node g c r =>
      dsimp only
      by_cases both : req = g ∧ r = .leaf nilS
      · obtain ⟨rfl, rfl⟩ := both
        rw [if_pos ⟨rfl, rfl⟩, List.pwFilter_cons_of_pos (by simp), List.pwFilter_nil]
        simp
      · rw [if_neg both]
        simp only [List.pwFilter_nil, List.not_mem_nil, false_iff, not_exists, not_and]
        intro c' same
        simp only [Tm.node.injEq] at same
        exact absurd ⟨same.1.symm, same.2.2⟩ both

theorem cmatch_var_free {σ : Subst ℕ (Tm F)} {v : ℕ} (free : σ v = none) (t : Tm F) :
    cmatch (fun _ => false) (.var v) σ t = [Function.update σ v (some t)] := by
  unfold cmatch
  simp only [rawMatch, free]
  rw [List.pwFilter_cons_of_pos (by simp), List.pwFilter_nil]

variable {O : Type uO} [DecidableEq O] {label : O → Tm F} {S : Finset O}

/-- The rows of the `every` suffix of evaluation: one per effect of the code, each making it. -/
theorem mem_rows_evalSuffix {c : Tm F} {y : Subst ℕ (Tm F) × List (Pick O (Tm F))} :
    y ∈ rows (termLayer (fun _ => false)) (cmatch (fun _ => false)) label S [.var 1]
        (.cons (.letBind (.var 1) (requestedEffects cs)) .done) (requestSubst c) ↔
      ∃ i v, (effects cs c)[i]? = some v ∧
        y = (Function.update (requestSubst c) 1 (some v), [.result i, .make {v}]) := by
  have free : requestSubst c 1 = none := by simp [requestSubst]
  rw [mem_rows_cons]
  constructor
  · rintro ⟨x, inStep, z, inRest, rfl⟩
    obtain ⟨i, v, at_i, τ, answer, rfl⟩ := mem_stepRows_letBind.mp inStep
    rw [cmatch_var_free free] at answer
    rw [List.mem_singleton] at answer
    subst answer
    rw [rows_done] at inRest
    simp only [instTemplate, List.mapM_cons, List.mapM_nil] at inRest
    have instV : (termLayer (V := ℕ) (fun _ : F => false)).inst
        (Function.update (requestSubst c) 1 (some v)) (.var 1) = some v := by
      simp [termLayer, Pat.inst]
    simp only [instV] at inRest
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, Multiset.mem_singleton]
      at inRest
    subst inRest
    refine ⟨i, v, ?_, rfl⟩
    simpa [requestedEffects, requestSubst] using at_i
  · rintro ⟨i, v, at_i, rfl⟩
    refine ⟨(Function.update (requestSubst c) 1 (some v), .result i), ?_,
      (Function.update (requestSubst c) 1 (some v), [.make {v}]), ?_, rfl⟩
    · refine mem_stepRows_letBind.mpr ⟨i, v, ?_, _, ?_, rfl⟩
      · simpa [requestedEffects, requestSubst] using at_i
      · rw [cmatch_var_free free]
        exact List.mem_singleton_self _
    · rw [rows_done]
      have instV : (termLayer (V := ℕ) (fun _ : F => false)).inst
          (Function.update (requestSubst c) 1 (some v)) (.var 1) = some v := by
        simp [termLayer, Pat.inst]
      simp [instTemplate, instV]

/-- **The footprint of evaluating code**: the `every` suffix takes, keeps and reads nothing, and makes
exactly the effects of the code. -/
theorem everyFootprint_eval (c : Tm F) :
    let fp := everyFootprint (termLayer (fun _ => false)) (cmatch (fun _ => false)) label S [.var 1]
      (.cons (.letBind (.var 1) (requestedEffects cs)) .done) (requestSubst c)
    fp.takes = 0 ∧ fp.keeps = 0 ∧ fp.queries = 0 ∧ ∀ v, v ∈ fp.makes ↔ v ∈ effects cs c := by
  intro fp
  have shape : ∀ y ∈ rows (termLayer (fun _ => false)) (cmatch (fun _ => false)) label S [.var 1]
      (.cons (.letBind (.var 1) (requestedEffects cs)) .done) (requestSubst c),
      ∃ v ∈ effects cs c, footprintOf y.2 = ⟨0, 0, 0, {v}⟩ := by
    intro y member
    obtain ⟨i, v, at_i, rfl⟩ := mem_rows_evalSuffix.mp member
    refine ⟨v, List.mem_of_getElem? at_i, ?_⟩
    simp [footprintOf]
  have noRegions : complRegions (cmatch (fun _ => false))
      (.cons (.letBind (.var 1) (requestedEffects cs)) .done : SourceList ℕ (Tm F) (Pat ℕ F))
      (requestSubst c) = [] := rfl
  refine ⟨?_, ?_, ?_, fun v => ?_⟩
  · simp only [fp, everyFootprint, noRegions, Footprint.takes_add, Footprint.takes_sum]
    simp only [complQueries, List.map_nil, add_zero]
    refine Multiset.eq_zero_of_forall_notMem fun o member => ?_
    obtain ⟨b, inMap, inB⟩ := Multiset.mem_join.mp member
    obtain ⟨fp', inMap', rfl⟩ := Multiset.mem_map.mp inMap
    obtain ⟨y, inFilter, rfl⟩ := Multiset.mem_map.mp inMap'
    obtain ⟨v, -, same⟩ := shape y (Multiset.mem_of_mem_filter inFilter)
    rw [same] at inB
    simp at inB
  · simp only [fp, everyFootprint, noRegions, Footprint.keeps_add, Footprint.keeps_sum]
    simp only [complQueries, List.map_nil, add_zero]
    refine Multiset.eq_zero_of_forall_notMem fun o member => ?_
    obtain ⟨b, inMap, inB⟩ := Multiset.mem_join.mp member
    obtain ⟨fp', inMap', rfl⟩ := Multiset.mem_map.mp inMap
    obtain ⟨y, inFilter, rfl⟩ := Multiset.mem_map.mp inMap'
    obtain ⟨v, -, same⟩ := shape y (Multiset.mem_of_mem_filter inFilter)
    rw [same] at inB
    simp at inB
  · simp only [fp, everyFootprint, noRegions, Footprint.queries_add, Footprint.queries_sum]
    simp only [complQueries, List.map_nil, Multiset.coe_nil, add_zero]
    refine Multiset.eq_zero_of_forall_notMem fun r member => ?_
    obtain ⟨b, inMap, inB⟩ := Multiset.mem_join.mp member
    obtain ⟨fp', inMap', rfl⟩ := Multiset.mem_map.mp inMap
    obtain ⟨y, inFilter, rfl⟩ := Multiset.mem_map.mp inMap'
    obtain ⟨v, -, same⟩ := shape y (Multiset.mem_of_mem_filter inFilter)
    rw [same] at inB
    simp at inB
  · simp only [fp, everyFootprint, noRegions, Footprint.makes_add, Footprint.makes_sum]
    simp only [complQueries, add_zero]
    constructor
    · intro member
      obtain ⟨b, inMap, inB⟩ := Multiset.mem_join.mp member
      obtain ⟨fp', inMap', rfl⟩ := Multiset.mem_map.mp inMap
      obtain ⟨y, inFilter, rfl⟩ := Multiset.mem_map.mp inMap'
      obtain ⟨w, effect, same⟩ := shape y (Multiset.mem_of_mem_filter inFilter)
      rw [same] at inB
      simp only [Multiset.mem_singleton] at inB
      subst inB
      exact effect
    · intro effect
      obtain ⟨i, at_i⟩ := List.mem_iff_getElem?.mp effect
      have member := mem_rows_evalSuffix (cs := cs) (label := label) (S := S)
        (y := (Function.update (requestSubst c) 1 (some v), [.result i, .make {v}])) |>.mpr
        ⟨i, v, at_i, rfl⟩
      refine Multiset.mem_join.mpr ⟨{v}, Multiset.mem_map.mpr ⟨⟨0, 0, 0, {v}⟩,
        Multiset.mem_map.mpr ⟨_, Multiset.mem_filter.mpr ⟨member, ?_⟩, by simp [footprintOf]⟩, rfl⟩,
        Multiset.mem_singleton_self v⟩
      simp [footprintOf, Footprint.Linear]

/-- **`eval` is a commit with a footprint.** Every row of the evaluation transform takes exactly one
request `req(code, nil)` from the store, keeps nothing, queries nothing, and makes exactly the
effects of the requested code. -/
theorem evalTransform_row {x : Subst ℕ (Tm F) × List (Pick O (Tm F))}
    (member : x ∈ (evalTransform cs req nilS).rows (termLayer (fun _ => false))
      (cmatch (fun _ => false)) label S) :
    ∃ o ∈ S, ∃ c, label o = .node req c (.leaf nilS) ∧ (footprintOf x.2).takes = {o} ∧
      (footprintOf x.2).keeps = 0 ∧ (footprintOf x.2).queries = 0 ∧
      ∀ v, v ∈ (footprintOf x.2).makes ↔ v ∈ effects cs c := by
  obtain ⟨y, inStep, z, inRest, rfl⟩ := mem_rows_cons.mp member
  obtain ⟨o, inS, τ, answer, rfl⟩ := mem_stepRows_take.mp inStep
  obtain ⟨c, labelled, rfl⟩ := mem_cmatch_request.mp answer
  rw [rows_every, Multiset.mem_singleton] at inRest
  subst inRest
  have parts := everyFootprint_eval (cs := cs) (label := label) (S := S) c
  simp only at parts
  obtain ⟨takes, keeps, reads, makes⟩ := parts
  refine ⟨o, inS, c, labelled, ?_, ?_, ?_, fun v => ?_⟩ <;>
    simp only [evalTransform, footprintOf_cons, footprint_take, footprint_amalgam, footprintOf_nil,
      add_zero, Footprint.takes_add, Footprint.keeps_add, Footprint.queries_add, Footprint.makes_add]
  · rw [takes, add_zero]
  · rw [keeps, add_zero]
  · rw [reads, add_zero]
  · rw [zero_add]
    exact makes v

end EvalTransform

/-! ## Controls -/

namespace DataControls

/-- Symbols of the code controls. -/
inductive CSig where
  | stored | got | emit | quote | placed | bank | bal | req | nil
  deriving DecidableEq, Repr

open CSig

/-- The code symbols. -/
def syms : CodeSyms CSig := ⟨.emit, .quote, .placed⟩

/-- Occurrences: a value and a serial number. -/
abbrev Occ := Tm CSig × ℕ

/-- The label of an occurrence is its value. -/
def lbl : Occ → Tm CSig := Prod.fst

theorem supply : ∀ (X : Finset Occ) (t : Tm CSig), ∃ o, o ∉ X ∧ lbl o = t := by
  intro X t
  obtain ⟨n, notIn⟩ := Infinite.exists_notMem_finset (X.image Prod.snd)
  exact ⟨(t, n), fun member => notIn (Finset.mem_image.mpr ⟨_, member, rfl⟩), rfl⟩

/-- The syntactic layer and matcher. -/
abbrev Ls : TermLayer ℕ (Tm CSig) (Pat ℕ CSig) := termLayer (fun _ => false)
abbrev ms : Matcher ℕ (Tm CSig) (Pat ℕ CSig) := cmatch (fun _ => false)
/-- Head keys. -/
abbrev headR : RegionKeys (Tm CSig) (Pat ℕ CSig) (Key CSig) := regionKeys headKeys

/-- A unary node. -/
def un (f : CSig) (x : Tm CSig) : Tm CSig := .node f x (.leaf .nil)
/-- The code `(add-atom &bank bal)`. -/
def code : Tm CSig := .node .emit (.leaf .bank) (.leaf .bal)
/-- Its effect: `bal` placed at `bank`. -/
def placedBal : Tm CSig := .node .placed (.leaf .bank) (.leaf .bal)

/-- Read stored code and make `got(code)`. -/
def copyCode : Transform ℕ (Tm CSig) (Pat ℕ CSig) :=
  ⟨.cons (.read (.node .stored (.var 0) (.leaf .nil))) .done, [.node .got (.var 0) (.leaf .nil)]⟩

/-- The same, with the code under `quote` in the template. -/
def copyQuoted : Transform ℕ (Tm CSig) (Pat ℕ CSig) :=
  ⟨.cons (.read (.node .stored (.var 0) (.leaf .nil))) .done,
    [.node .got (.node .quote (.var 0) (.leaf .nil)) (.leaf .nil)]⟩

/-- A store holding the code. -/
def holding : Finset Occ := {(un .stored code, 0)}

theorem effects_code : effects syms code = [placedBal] := by decide

theorem copy_row :
    ∃ x ∈ copyCode.rows Ls ms lbl holding, (footprintOf x.2).Linear ∧
      (footprintOf x.2).makes = {un .got code} :=
  exists_of_not_forall (by decide)
where
  exists_of_not_forall {α : Type} {s : Multiset α} {p : α → Prop}
      (h : ¬ ∀ x ∈ s, ¬ p x) : ∃ x ∈ s, p x := by
    by_contra none
    exact h fun x member holds => none ⟨x, member, holds⟩

/-- **The compiled semantics copies code as data**: every row of `copyCode` makes exactly
`got(code)`, and its static make keys cover that. -/
theorem data_copies_code :
    (∀ x ∈ copyCode.rows Ls ms lbl holding, (footprintOf x.2).makes = {un .got code}) ∧
      headR.CoveredBy (copyCode.static headR).makes (un .got code) :=
  ⟨by decide, ⟨.head .got, by decide, rfl⟩⟩

/-- **Eager instantiation breaks static footprints.** Evaluated where it lands, the copy also places
`bal` at `bank`, a label the static make keys of `copyCode` do not cover. -/
theorem eager_breaks_static :
    ∃ x ∈ copyCode.rows Ls ms lbl holding,
      placedBal ∈ (eagerFootprint syms (footprintOf x.2)).makes ∧
        ¬ headR.CoveredBy (copyCode.static headR).makes placedBal := by
  obtain ⟨x, member, -, makes⟩ := copy_row
  refine ⟨x, member, ?_, ?_⟩
  · simp only [eagerFootprint, makes]
    decide
  · rintro ⟨k, inKeys, covers⟩
    simp only [Transform.static, copyCode, SourceList.static, Source.static, headR, regionKeys,
      headKeys, List.flatMap_cons, List.flatMap_nil, List.append_nil] at inKeys
    simp only [StaticFootprint.makes_add, List.nil_append, List.mem_singleton] at inKeys
    subst inKeys
    cases covers

/-- **Quotation restores the law**: under eager instantiation the quoted copy makes what the
compiled semantics makes. -/
theorem quoted_copy_eager_eq :
    ∀ x ∈ copyQuoted.rows Ls ms lbl holding,
      eagerFootprint syms (footprintOf x.2) = footprintOf x.2 :=
  fun _ member => eagerFootprint_eq_of_guarded (cs := syms)
    (by
      intro q inTemplate
      simp only [copyQuoted, List.mem_singleton] at inTemplate
      subst inTemplate
      exact Or.inr ⟨by decide, Or.inl rfl, trivial⟩) member

/-- Evaluation as a transform, for the control symbols. -/
def evalT : Transform ℕ (Tm CSig) (Pat ℕ CSig) := evalTransform syms .req .nil

/-- A request to evaluate the code. -/
def request : Finset Occ := {(un .req code, 0)}

/-- A request to evaluate the quoted code. -/
def quotedRequest : Finset Occ := {(un .req (un .quote code), 0)}

/-- **`eval` runs the code, as one commit**: it takes the request and makes the code's effect. -/
theorem eval_runs_code :
    ∃ x ∈ evalT.rows Ls ms lbl request, (footprintOf x.2).Linear ∧
      (footprintOf x.2).takes = {(un .req code, 0)} ∧ (footprintOf x.2).makes = {placedBal} :=
  copy_row.exists_of_not_forall (by decide)

/-- **Evaluating quoted code runs nothing**: the commit takes the request and makes nothing. -/
theorem eval_quoted_runs_nothing :
    ∀ x ∈ evalT.rows Ls ms lbl quotedRequest, (footprintOf x.2).makes = 0 := by
  decide

/-- **The static make keys of `eval` are `any`**: which regions it writes depends on the code. -/
theorem eval_static_any : (evalT.static headR).makes = [.any] := rfl

end DataControls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Reflection

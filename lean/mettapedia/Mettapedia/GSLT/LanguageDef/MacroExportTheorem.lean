import Mettapedia.GSLT.LanguageDef.MacroExportCorrect

/-!
# The readable export of every admitted rule is correct

`export_correct`: for any admitted rule, any written arguments, any distinct
names the exporter chose, any caller code and any state, running the block
`lower` produces has exactly the outcome of the source use: the same value or
fault, the same memory, trace and consumption of external replies, and the
same private frame.

The proof composes three parts. The exported block's acquisition items
capture the evaluated arguments exactly as the source contract does
(`acquire_runs`); the exported template corresponds to the source template
under those captures (`MacroExportCorrect.lower_sim`), and corresponding
terms behave the same (`MacroExportCorrect.sim_agrees`); the items the
exporter adds after the template only check types or name the result.
-/

namespace Mettapedia.GSLT.LanguageDef.MacroExportTheorem

open Mettapedia.GSLT.LanguageDef.MacroExportPlan
open Mettapedia.GSLT.LanguageDef.MacroExportStateful
open Mettapedia.GSLT.LanguageDef.MacroExportCorrect

set_option autoImplicit false

/-! ## Running block items -/

/-- Block items run in order, threading the environment. -/
def runItems (ctx : Ctx) : Env → List Marked → State → Out (Env × State)
  | env, [], st => .ok (env, st)
  | env, x :: xs, st => do
      let (env, _, st) ← statement ctx env x st
      runItems ctx env xs st

theorem statements_prefix (ctx : Ctx) : ∀ (env : Env) (xs ys : List Marked) (st : State), ys ≠ [] →
    statements ctx env (xs ++ ys) st = (do let (env, st) ← runItems ctx env xs st; statements ctx env ys st)
  | env, [], ys, st, _ => by simp [runItems, bind, Except.bind]
  | env, x :: xs, ys, st, hys => by
      obtain ⟨y, zs, hyz⟩ := List.exists_cons_of_ne_nil (show xs ++ ys ≠ [] by simp [hys])
      rw [List.cons_append, hyz]
      simp only [statements, runItems]
      rw [← hyz]
      cases statement ctx env x st with
      | error => rfl
      | ok r =>
          obtain ⟨e, v, s⟩ := r
          exact statements_prefix ctx e xs ys s hys

section Agreement

variable (profile : Profile) (written : List Atom) (operands : Nat → Operand)

/-- A source run of items, seen with the acquisition locals behind it. -/
def extendRun (acq : Env) : Out (Env × State) → Out (Env × State)
  | .ok (e, s) => .ok (e ++ acq, s)
  | .error err => .error err

theorem runItems_agree {params : Nat → Option Param} {acq : Env} : ∀ {items items' : List Marked},
    List.Forall₂ (Agrees profile written operands params acq .stmt) items items' →
    ∀ env, Separate env acq → ∀ st,
      runItems (ctxOf profile written operands fun _ => none) (env ++ acq) items' st =
          extendRun acq (runItems (ctxOf profile written operands params) env items st) ∧
        ∀ e s, runItems (ctxOf profile written operands params) env items st = .ok (e, s) → Separate e acq
  | [], [], .nil, env, sep, st => ⟨rfl, fun e s h => by cases h; exact sep⟩
  | a :: _, _ :: _, .cons h hs, env, sep, st => by
      simp only [runItems]
      rw [(h env sep st).1]
      cases hr : statement (ctxOf profile written operands params) env a st with
      | error e => exact ⟨rfl, fun _ _ h => by cases h⟩
      | ok r =>
          obtain ⟨e, v, st'⟩ := r
          exact runItems_agree hs e ((h env sep st).2 e v st' hr) st'

end Agreement

/-! ## The acquisition items -/

theorem admittedType_shape {t : Marked} {place : Bool} {supply : List String} {ty : Marked}
    {item : Option Marked} {supply' : List String}
    (h : admittedType t place supply = some (ty, item, supply')) :
    (item = none ∨ ∃ rest, item = some (.list (.symbol "typedef" :: rest))) ∧
      ∃ pre, supply = pre ++ supply' := by
  unfold admittedType at h
  split at h
  all_goals try simp only at h
  all_goals try split_ifs at h
  all_goals first
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h
       obtain ⟨-, rfl, rfl⟩ := h
       exact ⟨.inl rfl, [], rfl⟩)
    | (rcases supply with _ | ⟨al, rest⟩
       · simp at h
       · simp only [Option.some.injEq, Prod.mk.injEq] at h
         obtain ⟨-, rfl, rfl⟩ := h
         exact ⟨.inr ⟨_, rfl⟩, [al], rfl⟩)
    | simp at h

theorem acquire_syntax {rule : Rule} {written : List Atom} {i : Nat} {a : Argument}
    {rest : List (Nat × Argument)} {supply : List String} {items : List Marked}
    {slotList : List (Nat × Marked)} {supply' : List String}
    (h : acquire rule written ((i, a) :: rest) supply = some (items, slotList, supply'))
    (hc : a.category = .syntax) :
    ∃ slots, acquire rule written rest supply = some (items, slots, supply') ∧
      slotList = (i, .operand i) :: slots := by
  simp only [acquire, if_pos hc, bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨items', slots', s'⟩, h1, h2⟩ := h
  cases h2
  exact ⟨slots', h1, rfl⟩

theorem acquire_evaluated {rule : Rule} {written : List Atom} {i : Nat} {a : Argument}
    {rest : List (Nat × Argument)} {supply : List String} {items : List Marked}
    {slotList : List (Nat × Marked)} {supply' : List String}
    (h : acquire rule written ((i, a) :: rest) supply = some (items, slotList, supply'))
    (hc : a.category ≠ .syntax) :
    ∃ n s ty item s2 initial message itemsRest slots,
      supply = n :: s ∧
      admittedType (instantiate (fun k => .operand k) (fun _ => "") a.ctype)
        (decide (a.category ≠ .value)) s = some (ty, item, s2) ∧
      acquire rule written rest s2 = some (itemsRest, slots, supply') ∧
      (a.category = .value → initial = .operand i) ∧
      (a.category ≠ .value → initial = .inner i ∨ initial = .list [.symbol "&", .operand i]) ∧
      items = .list [.symbol "var", .symbol "__auto_type", .name n, initial] ::
        (item.toList ++ [admission (.name n) ty message] ++ itemsRest) ∧
      slotList = (i, if a.category ≠ .value then .list [.symbol "*", .name n] else .name n) :: slots := by
  simp only [acquire, if_neg hc] at h
  by_cases ho : a.once = true
  · simp only [ho, Bool.not_true, Bool.false_eq_true, if_false] at h
    cases supply with
    | nil => simp [bind, Option.bind] at h
    | cons n s =>
        simp only [bind, Option.bind_eq_some_iff, pure] at h
        obtain ⟨⟨n', s'⟩, hn, ⟨ty, item, s2⟩, h1, ⟨itemsRest, slots, s3⟩, h2, h3⟩ := h
        simp only [Option.some.injEq, Prod.mk.injEq] at hn
        obtain ⟨rfl, rfl⟩ := hn
        simp only [Option.some.injEq, Prod.mk.injEq] at h3
        obtain ⟨h3a, h3b, rfl⟩ := h3
        subst h3a
        refine ⟨n, s, ty, item, s2, _, _, itemsRest, slots, rfl, h1, h2, ?_, ?_, rfl, h3b.symm⟩
        · intro hv; simp [hv]
        · intro hv
          rw [if_pos hv]
          split
          · exact .inl rfl
          · exact .inr rfl
  · simp [ho, bind, Option.bind] at h

/-! ## Running the acquisition -/

theorem slotAgrees_append {acq : Env} {i : Nat} {q : Option Param} {x : Marked} (more : Env)
    (h : SlotAgrees acq i q x) : SlotAgrees (acq ++ more) i q x := by
  cases h with
  | code => exact .code
  | value v n bound => exact .value v n (lookup_append_some acq more n _ bound)
  | place l n bound => exact .place l n (lookup_append_some acq more n _ bound)

theorem runItems_skip (ctx : Ctx) (env : Env) (item : Option Marked) (check : Marked)
    (rest : List Marked) (st : State)
    (hitem : item = none ∨ ∃ r, item = some (.list (.symbol "typedef" :: r)))
    (hcheck : ∃ r, check = .list (.symbol "_Static_assert" :: r)) :
    runItems ctx env (item.toList ++ [check] ++ rest) st = runItems ctx env rest st := by
  obtain ⟨c, rfl⟩ := hcheck
  rcases hitem with rfl | ⟨r, rfl⟩
  · simp [runItems, statement, bind, Except.bind]
  · simp [runItems, statement, bind, Except.bind]

theorem declare_value (ctx : Ctx) (env : Env) (n : String) (i : Nat) (st : State) :
    statement ctx env (.list [.symbol "var", .symbol "__auto_type", .name n, .operand i]) st =
      match callerValue ctx i st with
      | .ok (v, st1) => .ok ((n, .value v) :: env, .void, st1)
      | .error e => .error e := by
  simp only [statement, value]
  cases callerValue ctx i st <;> rfl

theorem declare_place (ctx : Ctx) (env : Env) (n : String) (i : Nat) (st : State) (initial : Marked)
    (hinit : initial = .inner i ∨ initial = .list [.symbol "&", .operand i]) :
    statement ctx env (.list [.symbol "var", .symbol "__auto_type", .name n, initial]) st =
      match callerPlace ctx i st with
      | .ok (l, st1) => .ok ((n, .value (.ptr l)) :: env, .void, st1)
      | .error e => .error e := by
  rcases hinit with rfl | rfl
  · simp only [statement, value]
    cases callerPlace ctx i st <;> rfl
  · simp only [statement]
    rw [value.eq_7 _ _ _ _ (fun _ h => by cases h)]
    simp only [place]
    cases callerPlace ctx i st <;> rfl

theorem callerValue_frame {ctx : Ctx} {i : Nat} {st st' : State} {v : Val}
    (h : callerValue ctx i st = .ok (v, st')) : st'.next = st.next ∧ st'.frame = st.frame := by
  unfold callerValue at h
  split at h
  · cases h; exact ⟨rfl, rfl⟩
  · cases h

theorem callerPlace_frame {ctx : Ctx} {i : Nat} {st st' : State} {l : Loc}
    (h : callerPlace ctx i st = .ok (l, st')) : st'.next = st.next ∧ st'.frame = st.frame := by
  unfold callerPlace at h
  split at h
  · cases h; exact ⟨rfl, rfl⟩
  · cases h

/-- The source capture touches only caller-visible state, and binds only its
own slots. -/
theorem acquireArguments_frame (profile : Profile) (written : List Atom) (operands : Nat → Operand) :
    ∀ (slotsL : List (Nat × Argument)) (params : Nat → Option Param) (st : State)
      (params' : Nat → Option Param) (st' : State),
    acquireArguments profile written operands slotsL params st = .ok (params', st') →
    st'.next = st.next ∧ st'.frame = st.frame ∧ ∀ k, k ∉ slotsL.map Prod.fst → params' k = params k
  | [], params, st, params', st', h => by cases h; exact ⟨rfl, rfl, fun _ _ => rfl⟩
  | (i, a) :: rest, params, st, params', st', h => by
      have frame : ∀ (q : Param) (st1 : State), st1.next = st.next → st1.frame = st.frame →
          acquireArguments profile written operands rest (fun k => if k = i then some q else params k) st1 =
            .ok (params', st') →
          st'.next = st.next ∧ st'.frame = st.frame ∧
            ∀ k, k ∉ ((i, a) :: rest).map Prod.fst → params' k = params k := by
        intro q st1 hn hf hr
        obtain ⟨h1, h2, h3⟩ := acquireArguments_frame profile written operands rest _ st1 params' st' hr
        refine ⟨h1.trans hn, h2.trans hf, fun k hk => ?_⟩
        simp only [List.map_cons, List.mem_cons, not_or] at hk
        rw [h3 k hk.2]; simp [hk.1]
      simp only [acquireArguments] at h
      split at h
      · exact frame _ st rfl rfl h
      · split at h
        · rename_i v st1 hv
          obtain ⟨hn, hf⟩ := callerValue_frame hv
          exact frame _ st1 hn hf h
        · cases h
      · split at h
        · rename_i l st1 hl
          obtain ⟨hn, hf⟩ := callerPlace_frame hl
          exact frame _ st1 hn hf h
        · cases h
      · split at h
        · rename_i l st1 hl
          obtain ⟨hn, hf⟩ := callerPlace_frame hl
          exact frame _ st1 hn hf h
        · cases h

/-- What running the acquisition items produced, against the source capture:
every acquisition local is a name the exporter consumed, and every slot holds
what the source captured for it. -/
structure Captured (pre : List String) (slotList : List (Nat × Marked)) (params : Nat → Option Param)
    (bound : Env) : Prop where
  names : ∀ n b, bound.lookup n = some b → n ∈ pre
  slots : ∀ i x, (i, x) ∈ slotList → SlotAgrees bound i (params i) x

theorem lookup_none_of_names {pre : List String} {bound : Env} {n : String}
    (names : ∀ m b, bound.lookup m = some b → m ∈ pre) (hn : n ∉ pre) : bound.lookup n = none := by
  cases h : bound.lookup n with
  | none => rfl
  | some b => exact absurd (names n b h) hn

theorem captured_cons {preT preR : List String} {n : String} {i : Nat} {x : Marked}
    {slots : List (Nat × Marked)} {params : Nat → Option Param} {bound : Env} {w : Val}
    (hnR : n ∉ preR) (cap : Captured preR slots params bound)
    (hx : SlotAgrees [(n, .value w)] i (params i) x) :
    Captured (n :: (preT ++ preR)) ((i, x) :: slots) params (bound ++ [(n, .value w)]) := by
  have hb : bound.lookup n = none := lookup_none_of_names cap.names hnR
  refine ⟨fun m b hm => ?_, fun j y hjy => ?_⟩
  · cases hl : bound.lookup m with
    | some c => exact List.mem_cons_of_mem _ (List.mem_append_right _ (cap.names m c hl))
    | none =>
        rw [lookup_append_none bound _ m hl] at hm
        by_cases hmn : m = n
        · subst hmn; exact List.mem_cons_self
        · have : (m == n) = false := by simpa using hmn
          simp [List.lookup, this] at hm
  · rcases List.mem_cons.mp hjy with hj | hj
    · simp only [Prod.mk.injEq] at hj
      obtain ⟨rfl, rfl⟩ := hj
      revert hx
      generalize params j = q
      intro hx
      cases hx with
      | code => exact .code
      | value v m bnd =>
          refine .value v m ?_
          have : m = n := by
            by_cases hmn : m = n
            · exact hmn
            · have : (m == n) = false := by simpa using hmn
              simp [List.lookup, this] at bnd
          subst this
          rw [lookup_append_none bound _ m hb]; exact bnd
      | place l m bnd =>
          refine .place l m ?_
          have : m = n := by
            by_cases hmn : m = n
            · exact hmn
            · have : (m == n) = false := by simpa using hmn
              simp [List.lookup, this] at bnd
          subst this
          rw [lookup_append_none bound _ m hb]; exact bnd
    · exact slotAgrees_append _ (cap.slots j y hj)

/-- Running the exported acquisition items captures exactly what the source
use captures, in the same order, with the same effects on caller state. -/
theorem acquire_runs (profile : Profile) (written : List Atom) (operands : Nat → Operand) (rule : Rule) :
    ∀ (slotsL : List (Nat × Argument)) (supply : List String) (items : List Marked)
      (slotList : List (Nat × Marked)) (supply' : List String),
    acquire rule written slotsL supply = some (items, slotList, supply') →
    supply.Nodup → (slotsL.map Prod.fst).Nodup →
    ∃ pre, supply = pre ++ supply' ∧ slotList.map Prod.fst = slotsL.map Prod.fst ∧
      ∀ (env : Env) (params : Nat → Option Param) (st : State),
        match acquireArguments profile written operands slotsL params st with
        | .error e => runItems (ctxOf profile written operands fun _ => none) env items st = .error e
        | .ok (params', st') => ∃ bound : Env,
            runItems (ctxOf profile written operands fun _ => none) env items st = .ok (bound ++ env, st') ∧
            Captured pre slotList params' bound
  | [], supply, items, slotList, supply', h, _, _ => by
      simp only [acquire, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨[], rfl, rfl, fun env params st => ?_⟩
      simp only [acquireArguments]
      exact ⟨[], rfl, { names := fun _ _ h => by simp at h, slots := fun _ _ h => by simp at h }⟩
  | (i, a) :: rest, supply, items, slotList, supply', h, hnd, hidx => by
      have hidx' : (rest.map Prod.fst).Nodup := (List.nodup_cons.mp hidx).2
      have hi : i ∉ rest.map Prod.fst := (List.nodup_cons.mp hidx).1
      by_cases hc : a.category = .syntax
      · obtain ⟨slots, hrest, rfl⟩ := acquire_syntax h hc
        obtain ⟨pre, hsup, hmap, hsem⟩ :=
          acquire_runs profile written operands rule rest supply items slots supply' hrest hnd hidx'
        refine ⟨pre, hsup, by simp [hmap], fun env params st => ?_⟩
        have hsrc : acquireArguments profile written operands ((i, a) :: rest) params st =
            acquireArguments profile written operands rest
              (fun k => if k = i then some .syntax else params k) st := by
          simp only [acquireArguments, hc]
        rw [hsrc]
        have hs := hsem env (fun k => if k = i then some .syntax else params k) st
        revert hs
        cases hA : acquireArguments profile written operands rest
            (fun k => if k = i then some .syntax else params k) st with
        | error e => exact id
        | ok r =>
          obtain ⟨params', st'⟩ := r
          rintro ⟨bound, hrun, cap⟩
          refine ⟨bound, hrun, cap.names, fun j x hjx => ?_⟩
          rcases List.mem_cons.mp hjx with hj | hj
          · simp only [Prod.mk.injEq] at hj
            obtain ⟨rfl, rfl⟩ := hj
            rw [(acquireArguments_frame profile written operands rest _ st params' st' hA).2.2 j hi]
            simp only [if_true]
            exact .code
          · exact cap.slots j x hj
      · obtain ⟨n, s, ty, item, s2, initial, message, itemsRest, slots, rfl, hty, hrest, hinitV, hinitP,
          rfl, rfl⟩ := acquire_evaluated h hc
        obtain ⟨hitem, preT, hs⟩ := admittedType_shape hty
        have hn : n ∉ s := (List.nodup_cons.mp hnd).1
        have hnds : s.Nodup := (List.nodup_cons.mp hnd).2
        have hnds2 : s2.Nodup := by rw [hs] at hnds; exact (List.nodup_append.mp hnds).2.1
        obtain ⟨preR, hs2, hmap, hsem⟩ :=
          acquire_runs profile written operands rule rest s2 itemsRest slots supply' hrest hnds2 hidx'
        have hnR : n ∉ preR := fun h => hn (by rw [hs, hs2]; simp [h])
        refine ⟨n :: (preT ++ preR), by rw [hs, hs2]; simp, by simp [hmap], fun env params st => ?_⟩
        have skip : ∀ env' st', runItems (ctxOf profile written operands fun _ => none) env'
            (item.toList ++ [admission (.name n) ty message] ++ itemsRest) st' =
              runItems (ctxOf profile written operands fun _ => none) env' itemsRest st' :=
          fun env' st' => runItems_skip _ env' item _ itemsRest st' hitem ⟨_, rfl⟩
        generalize hxs : (if a.category ≠ .value then Marked.list [.symbol "*", .name n] else .name n) = xslot
        -- after one capture, the rest runs as the source's rest
        have after : ∀ (q : Param) (w : Val) (st1 : State),
            SlotAgrees [(n, .value w)] i (some q) xslot →
            match acquireArguments profile written operands rest
                (fun k => if k = i then some q else params k) st1 with
            | .error e => runItems (ctxOf profile written operands fun _ => none) ((n, .value w) :: env)
                (item.toList ++ [admission (.name n) ty message] ++ itemsRest) st1 = .error e
            | .ok (params', st') => ∃ bound : Env,
                runItems (ctxOf profile written operands fun _ => none) ((n, .value w) :: env)
                  (item.toList ++ [admission (.name n) ty message] ++ itemsRest) st1 = .ok (bound ++ env, st') ∧
                Captured (n :: (preT ++ preR)) ((i, xslot) :: slots) params' bound := by
          intro q w st1 hagree
          have hs1 := hsem ((n, .value w) :: env) (fun k => if k = i then some q else params k) st1
          revert hs1
          cases hA : acquireArguments profile written operands rest
              (fun k => if k = i then some q else params k) st1 with
          | error e => intro h; rw [skip]; exact h
          | ok r =>
            obtain ⟨params', st'⟩ := r
            rintro ⟨bound, hrun, cap⟩
            have hpi : params' i = some q := by
              rw [(acquireArguments_frame profile written operands rest _ st1 params' st' hA).2.2 i hi]
              simp
            refine ⟨bound ++ [(n, .value w)], by rw [skip, hrun]; simp, captured_cons hnR cap ?_⟩
            rw [hpi]; exact hagree
        by_cases hval : a.category = .value
        · obtain rfl := hinitV hval
          have hsrc : acquireArguments profile written operands ((i, a) :: rest) params st =
              match callerValue (ctxOf profile written operands params) i st with
              | .ok (v, st) => acquireArguments profile written operands rest
                  (fun k => if k = i then some (.value v) else params k) st
              | .error e => .error e := by
            simp only [acquireArguments, hval]; rfl
          rw [hsrc]
          simp only [runItems]
          rw [declare_value, show callerValue (ctxOf profile written operands fun _ => none) i st =
            callerValue (ctxOf profile written operands params) i st from rfl]
          cases hv : callerValue (ctxOf profile written operands params) i st with
          | error e => rfl
          | ok r =>
            obtain ⟨v, st1⟩ := r
            exact after (.value v) v st1
              (by rw [← hxs, if_neg (by simp [hval])]; exact .value v n (by simp))
        · have hplace := hinitP hval
          have hsrc : acquireArguments profile written operands ((i, a) :: rest) params st =
              match callerPlace (ctxOf profile written operands params) i st with
              | .ok (l, st) => acquireArguments profile written operands rest
                  (fun k => if k = i then some (.place l) else params k) st
              | .error e => .error e := by
            cases hcat : a.category <;> simp_all [acquireArguments] <;> rfl
          rw [hsrc]
          simp only [runItems]
          rw [declare_place _ _ _ _ _ _ hplace, show callerPlace (ctxOf profile written operands fun _ => none) i st =
            callerPlace (ctxOf profile written operands params) i st from rfl]
          cases hl : callerPlace (ctxOf profile written operands params) i st with
          | error e => rfl
          | ok r =>
            obtain ⟨l, st1⟩ := r
            exact after (.place l) (.ptr l) st1
              (by rw [← hxs, if_pos hval]; exact .place l n (by simp))

/-! ## What the exporter adds after the template -/

/-- An item C checks at compile time and does not run. -/
def CompileTime (m : Marked) : Prop := ∃ rest, m = .list (.symbol "_Static_assert" :: rest)

/-- No item, or a typedef. -/
def TypedefItem (item : Option Marked) : Prop :=
  item = none ∨ ∃ rest, item = some (.list (.symbol "typedef" :: rest))

/-- The items an expression's last template item becomes: itself, when it is a
name declared with the result type; its value held by a fresh temporary, then
checked and named; or itself after a type check. -/
inductive Tail (last : Marked) : List Marked → Prop where
  | itself (s : String) (spelled : spelling? last = some s) : Tail last [last]
  | temporary (r : String) (item : Option Marked) (check : Marked) (typedef : TypedefItem item)
      (static : CompileTime check) :
      Tail last (.list [.symbol "var", .symbol "__auto_type", .name r, last] :: (item.toList ++ [check, .name r]))
  | checked (item : Option Marked) (check : Marked) (plain : spelling? last ≠ none ∨ effectFree last = true)
      (typedef : TypedefItem item) (static : CompileTime check) :
      Tail last (item.toList ++ [check, last])

theorem bodyItems_last {rule : Rule} {written : List Atom} {declared : Marked} {all : List Marked}
    {last : Marked} {supply : List String} {tail : List Marked} {s : List String}
    (hexpr : rule.expression = true)
    (h : bodyItems rule written declared all [last] supply = some (tail, s)) : Tail last tail := by
  rw [bodyItems.eq_2, if_pos hexpr] at h
  split_ifs at h with hdecl hspell
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    cases hsp : spelling? last with
    | some s' => exact .itself s' hsp
    | none => simp [declaresResult, hsp] at hdecl
  · cases supply with
    | nil => simp [bind, Option.bind] at h
    | cons r s' =>
        simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨_, rfl, ⟨ty, item, s''⟩, hty, h⟩ := h
        simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact .temporary r item _ (admittedType_shape hty).1 ⟨_, rfl⟩
  · simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨_, rfl, ⟨ty, item, s''⟩, hty, h⟩ := h
    simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine .checked item _ ?_ (admittedType_shape hty).1 ⟨_, rfl⟩
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', not_and, Bool.not_eq_false] at hspell
    by_cases hn : spelling? last = none
    · exact .inr (hspell hn)
    · exact .inl hn

theorem bodyItems_expr {rule : Rule} {written : List Atom} {declared : Marked} {all : List Marked}
    (hexpr : rule.expression = true) :
    ∀ (xs : List Marked) (last : Marked) (supply : List String) (template : List Marked) (s : List String),
    bodyItems rule written declared all (xs ++ [last]) supply = some (template, s) →
    ∃ tail, template = xs ++ tail ∧ Tail last tail
  | [], last, supply, template, s, h => ⟨template, rfl, bodyItems_last hexpr (by simpa using h)⟩
  | x :: xs, last, supply, template, s, h => by
      rw [List.cons_append, bodyItems.eq_3 _ _ _ _ _ _ _ (by simp)] at h
      simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨items, s'⟩, h1, h2⟩ := h
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨rfl, -⟩ := h2
      obtain ⟨tail, rfl, ht⟩ := bodyItems_expr hexpr xs last supply items s' h1
      exact ⟨tail, rfl, ht⟩

theorem bodyItems_stmt {rule : Rule} {written : List Atom} {declared : Marked} {all : List Marked}
    (hstmt : rule.expression = false) :
    ∀ (xs : List Marked) (supply : List String) (template : List Marked) (s : List String),
    bodyItems rule written declared all xs supply = some (template, s) → template = xs
  | [], supply, template, s, h => by simp only [bodyItems, Option.some.injEq, Prod.mk.injEq] at h; exact h.1.symm
  | [last], supply, template, s, h => by
      rw [bodyItems.eq_2] at h
      simp only [hstmt, Bool.false_eq_true, if_false, Option.some.injEq, Prod.mk.injEq] at h
      exact h.1.symm
  | x :: y :: rest, supply, template, s, h => by
      rw [bodyItems.eq_3 _ _ _ _ _ _ _ (by simp)] at h
      simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨items, s'⟩, h1, h2⟩ := h
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨rfl, -⟩ := h2
      rw [bodyItems_stmt hstmt (y :: rest) supply items s' h1]

/-! ## The added items run as the template's last item -/

/-- A block item's value and state. -/
def outcome (r : Out (Env × Val × State)) : Out (Val × State) := r.map fun x => x.2

theorem runItems_compileTime (ctx : Ctx) (env : Env) (item : Option Marked) (check : Marked) (st : State)
    (hi : TypedefItem item) (hc : CompileTime check) :
    runItems ctx env (item.toList ++ [check]) st = .ok (env, st) := by
  obtain ⟨c, rfl⟩ := hc
  rcases hi with rfl | ⟨r, rfl⟩
  · simp [runItems, statement, bind, Except.bind]
  · simp [runItems, statement, bind, Except.bind]

theorem statements_skip (ctx : Ctx) (env : Env) (item : Option Marked) (check : Marked)
    (rest : List Marked) (st : State) (hi : TypedefItem item) (hc : CompileTime check) (hrest : rest ≠ []) :
    statements ctx env (item.toList ++ check :: rest) st = statements ctx env rest st := by
  rw [show item.toList ++ check :: rest = (item.toList ++ [check]) ++ rest by simp,
    statements_prefix ctx env _ rest st hrest, runItems_compileTime ctx env item check st hi hc]
  rfl

theorem stmtHead_of_spelling {m : Marked} {s : String} (h : spelling? m = some s) : stmtHead m = false := by
  cases m <;> simp_all [spelling?, stmtHead]

/-- A block item that is an expression or a block yields what its value does. -/
theorem statement_as_value (ctx : Ctx) (env : Env) (m : Marked) (st : State)
    (h : stmtHead m = false ∨ isBlockForm m = true) :
    outcome (statement ctx env m st) = value ctx env m st := by
  rcases h with h | h
  · rw [statement_expr _ _ _ _ h]
    unfold outcome
    cases value ctx env m st <;> rfl
  · unfold isBlockForm at h
    split at h
    · rename_i items
      simp only [statement, value, outcome]
      cases statements ctx env items st <;> rfl
    · cases h

theorem tail_value (ctx : Ctx) (env : Env) {last : Marked} {tail : List Marked} (st : State)
    (h : Tail last tail) (hb : stmtHead last = true → isBlockForm last = true) :
    outcome (statements ctx env tail st) = value ctx env last st := by
  cases h with
  | itself s spelled =>
      simp only [statements]
      exact statement_as_value ctx env last st (.inl (stmtHead_of_spelling spelled))
  | temporary r item check typedef static =>
      rw [statements.eq_3 _ _ _ _ _ (by simp)]
      simp only [statement]
      cases hv : value ctx env last st with
      | error => rfl
      | ok p =>
          obtain ⟨v, s⟩ := p
          simp only [bind, Except.bind, pure, Except.pure]
          rw [statements_skip _ _ _ _ _ _ typedef static (by simp)]
          simp only [statements, statement_expr _ _ _ _ (rfl : stmtHead (.name r) = false), value, lookup,
            List.lookup, beq_self_eq_true, outcome]
          rfl
  | checked item check plain typedef static =>
      rw [statements_skip _ _ _ _ _ _ typedef static (by simp)]
      simp only [statements]
      refine statement_as_value ctx env last st (.inl ?_)
      cases hs : stmtHead last
      · rfl
      · have hbl := hb hs
        rcases plain with hp | hp
        · obtain ⟨s, hsp⟩ := Option.ne_none_iff_exists'.mp hp
          rw [stmtHead_of_spelling hsp] at hs; cases hs
        · unfold isBlockForm at hbl
          split at hbl
          · simp [effectFree, effects] at hp
          · cases hbl

theorem isBlockForm_src (L : Nat → String) (t : Marked) : isBlockForm (src L t) = isBlockForm t := by
  cases t with
  | list items =>
      rw [src_list]
      rcases items with _ | ⟨hd, rest⟩
      · rfl
      · cases hd with
        | symbol s => by_cases hs : s = "block" <;> simp [isBlockForm, src, instantiate, hs]
        | _ => simp [isBlockForm, src, instantiate]
  | _ => simp [isBlockForm, src, instantiate]

/-- In value position, the only statement form is a block. -/
theorem value_stmtHead_block {args : List Argument} {nlocals : Nat} {t : Marked}
    (hadm : admittedAt args nlocals .value t = true) (hs : stmtHead t = true) : isBlockForm t = true := by
  cases t with
  | list items =>
      rcases items with _ | ⟨hd, rest⟩
      · simp [stmtHead] at hs
      · cases hd with
        | symbol s =>
            rw [admittedAt.eq_11 args nlocals .value s rest (by simp)] at hadm
            simp only [stmtHead, Bool.or_eq_true, beq_iff_eq] at hs
            rcases hs with (((h | h) | h) | h) | h <;> subst h <;>
              simp [opOf, Op.all, Op.spelling, admittedOp, isBlockForm] at hadm ⊢
        | _ => simp [stmtHead] at hs
  | _ => simp [stmtHead] at hs

/-! ## The lowering, step by step -/

theorem lower_some {rule : Rule} {written : List Atom} {supply : List String} {block : Marked}
    (h : lower rule written supply = some block) :
    ∃ acquired slotList s1 template,
      acquire rule written (List.zip (List.range rule.arguments.length) rule.arguments) supply =
        some (acquired, slotList, s1) ∧
      rule.locals.length ≤ s1.length ∧
      bodyItems rule written
          (instantiate (fun k => (slotList.lookup k).getD (.operand k))
            (fun j => (s1.take rule.locals.length).getD j "") rule.result)
          (bodyView (tgt (fun k => (slotList.lookup k).getD (.operand k))
            (fun j => (s1.take rule.locals.length).getD j "") rule.body)).2
          (bodyView (tgt (fun k => (slotList.lookup k).getD (.operand k))
            (fun j => (s1.take rule.locals.length).getD j "") rule.body)).2
          (s1.drop rule.locals.length) = some (template, []) ∧
      block = assemble acquired template (bodyView (tgt (fun k => (slotList.lookup k).getD (.operand k))
            (fun j => (s1.take rule.locals.length).getD j "") rule.body)).1 := by
  unfold lower at h
  by_cases hg : rule.gnu = true
  · by_cases hl : written.length = rule.arguments.length
    · simp only [hg, hl, Bool.not_true, Bool.false_eq_true, if_false, ne_eq, not_true_eq_false] at h
      simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨acquired, slotList, s1⟩, hacq, h⟩ := h
      by_cases hk : rule.locals.length ≤ s1.length
      · simp only [hk, if_true, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨_, rfl, ⟨template, s3⟩, hb, h⟩ := h
        by_cases hs : s3 = []
        · subst hs
          simp only [not_true_eq_false, if_false, pure, Option.some.injEq] at h
          exact ⟨acquired, slotList, s1, template, hacq, hk, hb, h.symm⟩
        · simp [hs] at h
      · simp [hk] at h
    · simp [hg, hl] at h
  · simp [hg] at h

/-- The local names `lower` chooses for the template's locals. -/
def chosenLocals (rule : Rule) (written : List Atom) (supply : List String) : List String :=
  match acquire rule written (List.zip (List.range rule.arguments.length) rule.arguments) supply with
  | some (_, _, rest) => rest.take rule.locals.length
  | none => []

theorem acquireArguments_syntax (profile : Profile) (written : List Atom) (operands : Nat → Operand) :
    ∀ (slotsL : List (Nat × Argument)) (params : Nat → Option Param) (st : State)
      (params' : Nat → Option Param) (st' : State),
    acquireArguments profile written operands slotsL params st = .ok (params', st') →
    (slotsL.map Prod.fst).Nodup →
    ∀ i a, (i, a) ∈ slotsL → a.category = .syntax → params' i = some .syntax
  | [], _, _, _, _, _, _, _, _, h, _ => by simp at h
  | (j, b) :: rest, params, st, params', st', h, hnd, i, a, hmem, hc => by
      have hj : j ∉ rest.map Prod.fst := (List.nodup_cons.mp hnd).1
      have hnd' := (List.nodup_cons.mp hnd).2
      have step : ∀ (q : Param) (st1 : State),
          acquireArguments profile written operands rest (fun k => if k = j then some q else params k) st1 =
            .ok (params', st') → params' j = some q ∧
            ((i, a) ∈ rest → params' i = some .syntax) := by
        intro q st1 hr
        refine ⟨?_, fun hm => acquireArguments_syntax profile written operands rest _ st1 params' st' hr hnd' i a hm hc⟩
        rw [(acquireArguments_frame profile written operands rest _ st1 params' st' hr).2.2 j hj]
        simp
      rcases List.mem_cons.mp hmem with he | hm
      · simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        simp only [acquireArguments, hc] at h
        exact (step _ st h).1
      · simp only [acquireArguments] at h
        split at h
        · exact (step _ st h).2 hm
        · split at h
          · exact (step _ _ h).2 hm
          · cases h
        · split at h
          · exact (step _ _ h).2 hm
          · cases h
        · split at h
          · exact (step _ _ h).2 hm
          · cases h

theorem lookup_of_mem_fst {α β : Type} [BEq α] [LawfulBEq α] : ∀ (l : List (α × β)) (k : α),
    k ∈ l.map Prod.fst → ∃ x, l.lookup k = some x ∧ (k, x) ∈ l
  | [], _, h => by simp at h
  | (a, b) :: rest, k, h => by
      by_cases hk : k = a
      · subst hk; exact ⟨b, by simp [List.lookup], List.mem_cons_self⟩
      · have hb : (k == a) = false := by simpa using hk
        have hm : k ∈ rest.map Prod.fst := by
          simp only [List.map_cons, List.mem_cons] at h
          exact h.resolve_left hk
        obtain ⟨x, hx, hmem⟩ := lookup_of_mem_fst rest k hm
        exact ⟨x, by simp [List.lookup, hb, hx], List.mem_cons_of_mem _ hmem⟩

theorem value_blockOf (ctx : Ctx) (env : Env) (xs ys : List Marked) (st : State) (hys : ys ≠ []) :
    value ctx env (blockOf (xs ++ ys)) st =
      (do let (env, st1) ← runItems ctx env xs st
          let (_, v, s) ← statements ctx env ys st1
          pure (v, release st.next s)) := by
  simp only [blockOf, value, statements_prefix ctx env xs ys st hys]
  cases runItems ctx env xs st with
  | error => rfl
  | ok r => rfl

theorem statement_blockOf (ctx : Ctx) (env : Env) (xs ys : List Marked) (st : State) (hys : ys ≠ []) :
    statement ctx env (blockOf (xs ++ ys)) st =
      (do let (env', st1) ← runItems ctx env xs st
          let (_, v, s) ← statements ctx env' ys st1
          pure (env, v, release st.next s)) := by
  simp only [blockOf, statement, statements_prefix ctx env xs ys st hys]
  cases runItems ctx env xs st with
  | error => rfl
  | ok r => rfl

theorem mem_zip_range {α : Type} (l : List α) (i : Nat) (a : α) (h : l[i]? = some a) :
    (i, a) ∈ List.zip (List.range l.length) l := by
  obtain ⟨hi, hia⟩ := List.getElem?_eq_some_iff.mp h
  rw [List.mem_iff_getElem?]
  exact ⟨i, by simp [hi, hia]⟩

theorem admittedItems_append {args : List Argument} {n : Nat} :
    ∀ (xs ys : List Marked),
      admittedItems args n (xs ++ ys) = (admittedItems args n xs && admittedItems args n ys)
  | [], ys => by simp [admittedItems, admittedOp]
  | x :: xs, ys => by
      have := admittedItems_append (args := args) (n := n) xs ys
      simp only [admittedItems] at this ⊢
      simp only [List.cons_append, admittedOp, this, Bool.and_assoc]

theorem bodyView_plain {m : Marked} (h : isBlockForm m = false) : bodyView m = (false, [m]) := by
  unfold bodyView; split
  · simp [isBlockForm] at h
  · rfl

theorem Tail.ne_nil {last : Marked} {tail : List Marked} (h : Tail last tail) : tail ≠ [] := by
  cases h <;> simp

theorem assemble_plain (acquired template : List Marked) :
    assemble acquired template false = blockOf (acquired ++ template) := by
  unfold assemble
  simp only [Bool.not_false, if_true, ite_self]

theorem assemble_block (acquired template : List Marked) (ht : template ≠ []) :
    assemble acquired template true = blockOf (acquired ++ template) ∧ acquired = [] ∨
      assemble acquired template true = blockOf (acquired ++ [blockOf template]) := by
  unfold assemble
  simp only [ht, if_false]
  by_cases ha : acquired = []
  · subst ha; exact .inl ⟨rfl, rfl⟩
  · have : acquired.length ≠ 0 := by simpa using ha
    simp [this]

/-- A fault while acquiring ends the whole block, whatever follows. -/
theorem statements_of_runItems_error (ctx : Ctx) : ∀ (env : Env) (xs ys : List Marked) (st : State) (e : Fault),
    runItems ctx env xs st = .error e → statements ctx env (xs ++ ys) st = .error e
  | env, [], ys, st, e, h => by simp [runItems] at h
  | env, x :: xs, ys, st, e, h => by
      simp only [runItems] at h
      cases hx : statement ctx env x st with
      | error e' =>
          rw [hx] at h
          have : e' = e := by cases h; rfl
          subst this
          rcases hrest : xs ++ ys with _ | ⟨y, zs⟩
          · rw [List.cons_append, hrest]; simp only [statements, hx]
          · rw [List.cons_append, hrest, statements.eq_3 _ _ _ _ _ (by simp), hx]; rfl
      | ok r =>
          obtain ⟨env', v, st'⟩ := r
          rw [hx] at h
          simp only [bind, Except.bind] at h
          have := statements_of_runItems_error ctx env' xs ys st' e h
          rcases xs with _ | ⟨x', xs'⟩
          · simp [runItems] at h
          · rw [List.cons_append, statements.eq_3 _ _ _ _ _ (by simp), hx]
            simp only [bind, Except.bind]
            simpa using this

theorem assemble_any (acquired template : List Marked) (b : Bool) :
    ∃ Y, assemble acquired template b = blockOf (acquired ++ Y) := by
  unfold assemble
  dsimp only
  split_ifs
  all_goals exact ⟨_, rfl⟩

theorem outcome_eq_cases {T S : Out (Env × Val × State)} (h : outcome T = outcome S) :
    (∃ e, T = .error e ∧ S = .error e) ∨ (∃ eT eS v s, T = .ok (eT, v, s) ∧ S = .ok (eS, v, s)) := by
  cases T with
  | error e =>
      cases S with
      | error e' => simp only [outcome, Except.map, Except.error.injEq] at h; exact .inl ⟨e, rfl, h ▸ rfl⟩
      | ok r => simp [outcome, Except.map] at h
  | ok r =>
      cases S with
      | error e' => simp [outcome, Except.map] at h
      | ok r' =>
          obtain ⟨eT, v, s⟩ := r
          obtain ⟨eS, v', s'⟩ := r'
          simp only [outcome, Except.map, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .inr ⟨eT, eS, v, s, rfl, rfl⟩

/-! ## The theorem -/

theorem export_correct (profile : Profile) (written : List Atom) (operands : Nat → Operand)
    (rule : Rule) (supply : List String) (block : Marked) (st : State)
    (lowered : lower rule written supply = some block) (distinct : supply.Nodup)
    (admitted : admittedRule rule = true) :
    runBlock profile written operands rule.expression block st =
      invoke profile written operands rule (chosenLocals rule written supply) st := by
  obtain ⟨acquired, slotList, s1, template, hacq, hk, hbody, rfl⟩ := lower_some lowered
  have hchosen : chosenLocals rule written supply = s1.take rule.locals.length := by
    simp only [chosenLocals, hacq]
  rw [hchosen]
  unfold invoke runBlock slotsOf
  obtain ⟨L, hL⟩ : ∃ L : Nat → String, L = fun j => (s1.take rule.locals.length).getD j "" := ⟨_, rfl⟩
  obtain ⟨σT, hσ⟩ : ∃ σT : Nat → Marked, σT = fun k => (slotList.lookup k).getD (.operand k) := ⟨_, rfl⟩
  rw [← hL, ← hσ] at hbody
  rw [← hL, ← hσ]
  dsimp only
  have hidx : ((List.zip (List.range rule.arguments.length) rule.arguments).map Prod.fst).Nodup := by
    simp only [List.map_fst_zip, List.length_range, le_refl]; exact List.nodup_range
  obtain ⟨pre, hsup, hmap, hsem⟩ :=
    acquire_runs profile written operands rule _ supply acquired slotList s1 hacq distinct hidx
  have hrun := hsem [] (fun _ => none) st
  -- what the acquisition gives the template
  have mkLow : ∀ params st1 bound,
      acquireArguments profile written operands (List.zip (List.range rule.arguments.length) rule.arguments)
        (fun _ => none) st = .ok (params, st1) →
      Captured pre slotList params bound → Lowering rule.arguments rule.locals.length params bound σT L := by
    intro params st1 bound hA cap
    refine ⟨fun i hi => ?_, fun i hs => ?_, fun j hj => ?_⟩
    · have hmem : i ∈ slotList.map Prod.fst := by
        rw [hmap, List.map_fst_zip (by simp)]; exact List.mem_range.mpr hi
      obtain ⟨x, hx, hxm⟩ := lookup_of_mem_fst slotList i hmem
      have : σT i = x := by rw [hσ]; simp [hx]
      rw [this]; exact cap.slots i x hxm
    · unfold slotIs at hs
      cases ha : rule.arguments[i]? with
      | none => rw [ha] at hs; cases hs
      | some a =>
          rw [ha] at hs
          have hc : a.category = .syntax := by simpa using hs
          exact acquireArguments_syntax profile written operands _ _ st params st1 hA hidx i a
            (mem_zip_range _ i a ha) hc
    · have hjn : j < (s1.take rule.locals.length).length := by simp; omega
      have hin : L j ∈ s1 := by
        rw [hL]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjn, Option.getD_some]
        exact List.mem_of_mem_take (List.getElem_mem hjn)
      have hnot : L j ∉ pre := by
        intro hp
        rw [hsup] at distinct
        exact (List.nodup_append.mp distinct).2.2 _ hp _ hin rfl
      exact lookup_none_of_names cap.names hnot
  -- a fault while acquiring is the source's fault
  have faultCase : ∀ (X : List Marked) (e : Fault), X ≠ [] →
      runItems (ctxOf profile written operands fun _ => none) [] acquired st = .error e →
      (if rule.expression = true then
          value { profile := profile, written := written, operands := operands, params := fun _ => none } []
            (blockOf (acquired ++ X)) st
        else
          Except.map (fun x => (Val.void, x.2.2))
            (statement { profile := profile, written := written, operands := operands, params := fun _ => none } []
              (blockOf (acquired ++ X)) st)) = .error e := by
    intro X e hX hr
    split
    · rw [value_blockOf _ _ _ _ _ hX]; simp only [ctxOf] at hr; rw [hr]; rfl
    · rw [statement_blockOf _ _ _ _ _ hX]; simp only [ctxOf] at hr; rw [hr]; rfl
  have hsize : ∀ m : Marked, sizeOf m < sizeOf m + 1 := fun m => Nat.lt_succ_self _
  by_cases hblk : isBlockForm rule.body = true
  · -- a block template
    obtain ⟨bitems, hb⟩ : ∃ items, rule.body = .list (.symbol "block" :: items) := by
      generalize rule.body = b at hblk ⊢
      unfold isBlockForm at hblk
      split at hblk
      · exact ⟨_, rfl⟩
      · cases hblk
    have htgtb : tgt σT L rule.body = .list (.symbol "block" :: bitems.map (tgt σT L)) := by
      rw [hb, tgt_head _ _ (by decide)]
    have hsrcb : instantiate (fun i => Marked.arg i) L rule.body =
        .list (.symbol "block" :: bitems.map (src L)) := by
      rw [hb]; exact src_list L _
    rw [htgtb] at hbody ⊢
    rw [hsrcb]
    simp only [bodyView] at hbody ⊢
    unfold admittedRule at admitted
    rw [hb] at admitted
    simp only at admitted
    rcases hrev : bitems.reverse with _ | ⟨last, earlier⟩
    · rw [hrev] at admitted; cases admitted
    rw [hrev] at admitted
    have hbi : bitems = earlier.reverse ++ [last] := by
      rw [← List.reverse_reverse bitems, hrev]; simp
    simp only [Bool.and_eq_true] at admitted
    obtain ⟨hE, hlast⟩ := admitted
    have hmapb : bitems.map (tgt σT L) = earlier.reverse.map (tgt σT L) ++ [tgt σT L last] := by
      rw [hbi, List.map_append]; rfl
    -- the template the exporter wrote, and its correspondence to the source block
    have shape : template ≠ [] ∧ ∀ (params : Nat → Option Param) (bound : Env),
        Lowering rule.arguments rule.locals.length params bound σT L → ∀ s : State,
        outcome (statements (ctxOf profile written operands fun _ => none) ([] ++ bound) template s) =
          outcome (statements (ctxOf profile written operands params) [] (bitems.map (src L)) s) := by
      by_cases hexpr : rule.expression = true
      · rw [if_pos hexpr] at hlast
        rw [hmapb] at hbody
        obtain ⟨tail, rfl, htail⟩ := bodyItems_expr hexpr _ _ _ _ _ hbody
        refine ⟨by simp [htail.ne_nil], fun params bound low s => ?_⟩
        have simE := items_of (.inr rfl) earlier.reverse
          (fun x _ p hp => lower_sim low _ x (hsize x) p hp) hE
        obtain ⟨simL, hkL⟩ := lower_sim low _ last (hsize last) .value hlast
        have hbt : stmtHead (tgt σT L last) = true → isBlockForm (tgt σT L last) = true := fun h => by
          rw [hkL.block]; exact value_stmtHead_block hlast (hkL.stmt ▸ h)
        have hss : stmtHead (src L last) = false ∨ isBlockForm (src L last) = true := by
          cases h : stmtHead last
          · exact .inl (by rw [stmtHead_src]; exact h)
          · exact .inr (by rw [isBlockForm_src]; exact value_stmtHead_block hlast h)
        rw [statements_prefix _ _ _ _ _ htail.ne_nil, hbi, List.map_append,
          statements_prefix _ _ _ _ _ (by simp)]
        have hra := runItems_agree profile written operands (sims_agrees profile written operands simE)
          [] (fun _ _ _ => rfl) s
        rw [hra.1]
        cases hR : runItems (ctxOf profile written operands params) [] (earlier.reverse.map (src L)) s with
        | error e => rfl
        | ok r =>
            obtain ⟨e, s'⟩ := r
            simp only [extendRun, bind, Except.bind]
            rw [tail_value _ _ s' htail hbt,
              (sim_agrees profile written operands simL) e (hra.2 e s' hR) s']
            simp only [List.map_cons, List.map_nil, statements]
            exact (statement_as_value _ _ _ _ hss).symm
      · have hexpr' : rule.expression = false := by simpa using hexpr
        rw [if_neg hexpr] at hlast
        obtain rfl := bodyItems_stmt hexpr' _ _ _ _ hbody
        refine ⟨by rw [hbi]; simp, fun params bound low s => ?_⟩
        have hall : admittedItems rule.arguments rule.locals.length bitems = true := by
          rw [hbi, admittedItems_append, hE, hlast]; rfl
        have simB := items_of (.inr rfl) bitems (fun x _ p hp => lower_sim low _ x (hsize x) p hp) hall
        rw [statements_agree profile written operands (sims_agrees profile written operands simB) [] (fun _ _ _ => rfl) s]
        unfold outcome
        cases statements (ctxOf profile written operands params) [] (bitems.map (src L)) s <;> rfl
    obtain ⟨htne, core⟩ := shape
    revert hrun
    cases hA : acquireArguments profile written operands (List.zip (List.range rule.arguments.length) rule.arguments)
        (fun _ => none) st with
    | error e =>
        intro hrun
        rcases assemble_block acquired template htne with ⟨heq, -⟩ | heq <;> rw [heq]
        · exact faultCase _ e htne hrun
        · exact faultCase _ e (by simp) hrun
    | ok r =>
        obtain ⟨params, st1⟩ := r
        rintro ⟨bound, hrunok, cap⟩
        have low := mkLow params st1 bound hA cap
        have hnext := (acquireArguments_frame profile written operands _ _ st params st1 hA).1
        have hc := core params bound low st1
        simp only [List.nil_append] at hc
        simp only [List.append_nil] at hrunok
        rcases outcome_eq_cases hc with ⟨e, hT, hS⟩ | ⟨eT, eS, v, s, hT, hS⟩
        all_goals rcases assemble_block acquired template htne with ⟨heq, hacq0⟩ | heq <;> rw [heq]
        all_goals first
          | (subst hacq0
             simp only [runItems, Except.ok.injEq, Prod.mk.injEq] at hrunok
             obtain ⟨rfl, rfl⟩ := hrunok
             simp only [List.nil_append, blockOf]
             split
             · simp only [value, hT, hS, bind, Except.bind, Except.map, pure, Except.pure, release_release]
             · simp only [statement, hT, hS, bind, Except.bind, Except.map, pure, Except.pure, release_release])
          | (split
             · rw [value_blockOf _ _ _ _ _ (by simp), hrunok]
               simp only [bind, Except.bind, statements, blockOf, statement, hT, hS, value, Except.map, pure,
                 Except.pure]
             · rw [statement_blockOf _ _ _ _ _ (by simp), hrunok]
               simp only [bind, Except.bind, statements, blockOf, statement, hT, hS, Except.map, pure,
                 Except.pure])
  · -- a template that is not a block
    have hblk' : isBlockForm rule.body = false := by simpa using hblk
    have hadm : (if rule.expression = true then admittedAt rule.arguments rule.locals.length .value rule.body
        else admittedItems rule.arguments rule.locals.length [rule.body]) = true := by
      have h := admitted
      unfold admittedRule at h
      split at h
      · next items heq => rw [heq] at hblk'; simp [isBlockForm] at hblk'
      · exact h
    revert hrun
    cases hA : acquireArguments profile written operands (List.zip (List.range rule.arguments.length) rule.arguments)
        (fun _ => none) st with
    | error e =>
        intro hrun
        obtain ⟨Y, hY⟩ := assemble_any acquired template (bodyView (tgt σT L rule.body)).1
        rw [hY]
        have hs := statements_of_runItems_error _ [] acquired Y st e hrun
        split
        · simp only [blockOf, value]; simp only [ctxOf] at hs; rw [hs]; rfl
        · simp only [blockOf, statement]; simp only [ctxOf] at hs; rw [hs]; rfl
    | ok r =>
        obtain ⟨params, st1⟩ := r
        rintro ⟨bound, hrunok, cap⟩
        have low := mkLow params st1 bound hA cap
        simp only [List.append_nil] at hrunok
        by_cases hexpr : rule.expression = true
        · rw [if_pos hexpr] at hadm
          obtain ⟨simB, hkB⟩ := lower_sim low _ rule.body (hsize _) .value hadm
          have hpl : isBlockForm (tgt σT L rule.body) = false := by rw [hkB.block]; exact hblk'
          rw [bodyView_plain hpl] at hbody ⊢
          obtain ⟨tail, htemp, htail⟩ := bodyItems_expr hexpr [] _ _ _ _ (by simpa using hbody)
          simp only [List.nil_append] at htemp
          subst htemp
          simp only [assemble_plain, hexpr, if_true]
          rw [value_blockOf _ _ _ _ _ htail.ne_nil, hrunok]
          simp only [bind, Except.bind]
          have hbt : stmtHead (tgt σT L rule.body) = true → isBlockForm (tgt σT L rule.body) = true :=
            fun h => by rw [hkB.block]; exact value_stmtHead_block hadm (hkB.stmt ▸ h)
          have ht := tail_value (ctxOf profile written operands fun _ => none) bound st1 htail hbt
          have hv := (sim_agrees profile written operands simB) [] (fun _ _ _ => rfl) st1
          simp only [List.nil_append] at hv
          rw [hv] at ht
          cases hT : statements (ctxOf profile written operands fun _ => none) bound template st1 with
          | error e =>
              rw [hT] at ht
              simp only [outcome, Except.map] at ht
              simp only [ctxOf] at ht
              rw [← ht]; rfl
          | ok r =>
              obtain ⟨eT, v, s⟩ := r
              rw [hT] at ht
              simp only [outcome, Except.map] at ht
              simp only [ctxOf] at ht
              rw [← ht]; rfl
        · have hexpr' : rule.expression = false := by simpa using hexpr
          rw [if_neg hexpr] at hadm
          have hitem : (if stmtHead rule.body then admittedAt rule.arguments rule.locals.length .stmt rule.body
              else admittedAt rule.arguments rule.locals.length .value rule.body) = true := by
            simp only [admittedItems, admittedOp, Bool.and_eq_true] at hadm; exact hadm.1
          have simB := item_sim (fun p hp => lower_sim low _ rule.body (hsize _) p hp) hitem
          have hkB : HeadKept rule.body (tgt σT L rule.body) := by
            split at hitem
            · exact (lower_sim low _ rule.body (hsize _) .stmt hitem).2
            · exact (lower_sim low _ rule.body (hsize _) .value hitem).2
          have hpl : isBlockForm (tgt σT L rule.body) = false := by rw [hkB.block]; exact hblk'
          rw [bodyView_plain hpl] at hbody ⊢
          obtain rfl := bodyItems_stmt hexpr' _ _ _ _ hbody
          simp only [assemble_plain, hexpr', Bool.false_eq_true, if_false]
          rw [statement_blockOf _ _ _ _ _ (by simp), hrunok]
          have hs := ((sim_agrees profile written operands simB) [] (fun _ _ _ => rfl) st1).1
          simp only [List.nil_append] at hs
          simp only [statements, ctxOf, bind, Except.bind] at hs ⊢
          rw [hs]
          cases statement { profile := profile, written := written, operands := operands, params := params } []
            (instantiate (fun i => Marked.arg i) L rule.body) st1 <;> rfl


/-! ## Recorded exports -/

/-- A recorded export the kernel admits: its target is exactly the lowering
of its source, its rule is in the fragment the theorem covers, and the names
the exporter picked are distinct. -/
def admitUse (ruleAtom useAtom : Atom) : Bool :=
  checkUse ruleAtom useAtom &&
    match decodeRule ruleAtom, decodeUse useAtom with
    | some rule, some use => admittedRule rule && decide use.picked.Nodup
    | _, _ => false

/-- An admitted recorded export behaves as its source use: the C Cesta
recorded is the lowered block, and that block, run from any state with any
caller code and any replies, has the source use's outcome. -/
theorem recorded_export_correct (ruleAtom useAtom : Atom) (h : admitUse ruleAtom useAtom = true) :
    ∃ rule use block, decodeRule ruleAtom = some rule ∧ decodeUse useAtom = some use ∧
      lower rule use.written use.picked = some block ∧
      (fill use.written block).map Atom.tokens = some use.target.tokens ∧
      ∀ (profile : Profile) (operands : Nat → Operand) (st : State),
        runBlock profile use.written operands rule.expression block st =
          invoke profile use.written operands rule (chosenLocals rule use.written use.picked) st := by
  unfold admitUse checkUse at h
  cases hr : decodeRule ruleAtom with
  | none => simp [hr] at h
  | some rule =>
      cases hu : decodeUse useAtom with
      | none => simp [hr, hu] at h
      | some use =>
          simp only [hr, hu, Bool.and_eq_true, decide_eq_true_eq] at h
          obtain ⟨⟨_, hlow⟩, hadm, hnd⟩ := h
          cases hl : lower rule use.written use.picked with
          | none => simp [hl] at hlow
          | some block =>
              rw [hl] at hlow
              simp only at hlow
              cases hf : fill use.written block with
              | none => simp [hf] at hlow
              | some atom =>
                  rw [hf] at hlow
                  refine ⟨rule, use, block, rfl, rfl, hl, ?_, fun profile operands st =>
                    export_correct profile use.written operands rule use.picked block st hl hnd hadm⟩
                  rw [hf]; simpa using hlow

end Mettapedia.GSLT.LanguageDef.MacroExportTheorem

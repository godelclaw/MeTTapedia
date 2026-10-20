import Mettapedia.GSLT.LanguageDef.MacroExportTheorem

/-!
# Header export: one C function or function-like macro per instance

`cesta export-header` writes a concrete instance of a rule as a `static
inline` function, or, for rules that take code, as a function-like macro.
`lowerFunction` and `lowerMacro` state those lowerings as functions of the
rule, the instance's type parameters and the names chosen; `checkFunction` and
`checkMacro` decide that a recorded definition is exactly that lowering.

`function_correct`: the function's body, run with its parameters holding the
values and places a call supplies, has the outcome of the rule's template run
with those captured values and places. The call itself is ordinary C: its
arguments are evaluated in an order C leaves unspecified and converted to the
parameter types, and the function returns the value of its final `return`
expression. `MacroExportLowering` records what that costs a caller.
`probe_macro_correct` gives the meaning of the exported probe macro at a use.
-/

namespace Mettapedia.GSLT.LanguageDef.MacroExportHeader

open Mettapedia.GSLT.LanguageDef.MacroExportPlan
open Mettapedia.GSLT.LanguageDef.MacroExportStateful
open Mettapedia.GSLT.LanguageDef.MacroExportCorrect
open Mettapedia.GSLT.LanguageDef.MacroExportTheorem

set_option autoImplicit false

/-! ## Function export -/

mutual
  /-- A parameter's declarator: the name, or a pointer to it for a place, at
  the declarator's `TypeSlot`. Stacked pointers are one `**` or `***` node;
  elsewhere a pointer is parenthesized. The count is the number of slots. -/
  def withParameter (name : Marked) (place : Bool) : Marked → Marked × Nat
    | .symbol "TypeSlot" =>
        (if place then .list [.symbol "c:ParenthesizedDeclarator", .list [.symbol "*", name]] else name, 1)
    | .list [.symbol "*", .symbol "TypeSlot"] =>
        if place then (.list [.symbol "**", name], 1) else (.list [.symbol "*", name], 1)
    | .list [.symbol "**", .symbol "TypeSlot"] =>
        if place then (.list [.symbol "***", name], 1) else (.list [.symbol "**", name], 1)
    | .list items =>
        let (out, uses) := withParameterMany name place items
        (.list out, uses)
    | m => (m, 0)
  def withParameterMany (name : Marked) (place : Bool) : List Marked → List Marked × Nat
    | [] => ([], 0)
    | m :: rest =>
        let (a, n) := withParameter name place m
        let (as, k) := withParameterMany name place rest
        (a :: as, n + k)
end

/-- The declaration of the parameter for an argument. -/
def parameter (a : Argument) (n : String) : Option Marked :=
  let place := a.category != .value
  match instantiate (fun k => .operand k) (fun _ => "") a.ctype with
  | .list [.symbol "CType", specs] =>
      some (.list [specs, if place then .list [.symbol "*", .name n] else .name n])
  | .list [.symbol "CType", specs, decl] =>
      let (d, uses) := withParameter (.name n) place decl
      if uses = 1 then some (.list [specs, d]) else none
  | _ => none

/-- The arguments a function takes as parameters, with their slots. -/
def evaluated (rule : Rule) : List (Nat × Argument) :=
  (slotsOf rule).filter fun s => s.2.category != .syntax

/-- Each slot as the function body reads it: a parameter name, its target for
a place, or the instance's type for a type parameter. -/
def functionSlots (rule : Rule) (paramNames : List String) (k : Nat) : Marked :=
  match ((evaluated rule).map Prod.fst |>.zip paramNames).lookup k with
  | some n => match rule.arguments[k]? with
    | some a => if a.category = .value then .name n else .list [.symbol "*", .name n]
    | none => .operand k
  | none => .operand k

/-- The parts of an exported function: parameters, the template's items (the
last is returned for an expression), and the result type. -/
structure FunctionParts where
  params : List Marked
  items : List Marked
  result : Marked

def lowerFunctionParts (rule : Rule) (names : List String) : Option FunctionParts := do
  let ev := evaluated rule
  if names.length ≠ ev.length + rule.locals.length then none
  let paramNames := names.take ev.length
  let localNames := names.drop ev.length
  let σT := functionSlots rule paramNames
  let L := fun j => localNames.getD j ""
  let params ← (ev.zip paramNames).mapM fun s => parameter s.1.2 s.2
  let body := addressOfObject (instantiate σT L rule.body)
  let result ← if rule.expression then
      match instantiate σT L rule.result with
      | .list [.symbol "CType", specs] => some specs
      | _ => none
    else some (.symbol "void")
  pure { params, items := (bodyView body).2, result }

/-- The definition as Cesta hands it to the C printer. -/
def functionAtom (fname : String) (expression : Bool) (p : FunctionParts) : Marked :=
  let items := if expression then
      match p.items.reverse with
      | last :: earlier => earlier.reverse ++ [.list [.symbol "return", last]]
      | [] => []
    else p.items
  .list ([.symbol "fn", .list [.symbol "static", .list [.symbol "inline", p.result]], .symbol fname,
    .list (if p.params.isEmpty then [.symbol "void"] else p.params)] ++ items)

/-! ## Macro export -/

def isStaticCheck : Marked → Bool
  | .list [.symbol "_Static_assert", _, _] => true
  | _ => false

/-- A static assertion as an expression: a `sizeof` of a structure holding
it, whose member takes the macro's name. -/
def staticCheckPart (fname : String) (item : Marked) : Marked :=
  .list [.symbol "cast", .symbol "void", .list [.symbol "sizeof", .symbol "type",
    .list [.symbol "struct", item, .list [.symbol "char", .symbol fname]]]]

def commaJoin : List Marked → Option Marked
  | [] => none
  | p :: rest => some (rest.foldl (fun acc q => .list [.symbol ",", acc, q]) p)

/-- The one expression an exported macro stands for, with syntax parameters
as the caller's code. Evaluated parameters require acquisition, which this
textual substitution cannot provide. -/
def lowerMacro (rule : Rule) (fname : String) : Option Marked :=
  if !rule.arguments.all (fun a => a.category == .syntax) then none
  else if !rule.locals.isEmpty then none
  else
    let body := instantiate (fun i => .operand i) (fun _ => "") rule.body
    let (isBlock, items) := bodyView body
    if rule.expression && isBlock then none
    else commaJoin (items.map fun item => if isStaticCheck item then staticCheckPart fname item else item)

/-- A successful textual macro export has no evaluated argument whose
acquisition could be lost by substitution. -/
theorem lowerMacro_syntax_only (rule : Rule) (fname : String) (body : Marked)
    (h : lowerMacro rule fname = some body) :
    ∀ a ∈ rule.arguments, a.category = .syntax := by
  cases checked : rule.arguments.all (fun a => a.category == .syntax) with
  | false => simp [lowerMacro, checked] at h
  | true =>
      simp only [List.all_eq_true, beq_iff_eq] at checked
      exact checked

/-! ## Admission of a recorded header definition -/

/-- A header plan record of `cesta export-header --plan`. -/
structure HeaderUse where
  label : String
  function : Bool
  name : String
  types : List (String × Atom)
  picked : List String
  emitted : Atom

def typePair : Atom → Option (String × Atom)
  | .list [.symbol k, t] => some (k, t)
  | _ => none

def decodeHeader : Atom → Option HeaderUse
  | .list [.symbol "header", .symbol "cesta-header-plan/1", .list [.symbol "rule", .text _, .text _, .text label],
      .list [.symbol kind, .symbol name], .list (.symbol "types" :: types), .list (.symbol "picked" :: picked),
      .list [.symbol field, emitted]] => do
      let function ← match kind, field with
        | "function", "definition" => some true
        | "macro", "expression" => some false
        | _, _ => none
      let types ← types.mapM typePair
      let picked ← picked.mapM fun a => match a with
        | .text s => some s
        | _ => none
      pure { label, function, name, types, picked, emitted }
  | _ => none

/-- What each argument slot is written as in the definition: a type
parameter's type, a macro parameter's name, or nothing. -/
def headerWritten (rule : Rule) (use : HeaderUse) : List Atom :=
  let rec go : List Argument → List String → List Atom
    | [], _ => []
    | a :: rest, names => match use.types.lookup a.name with
      | some t => t :: go rest names
      | none => if use.function then .symbol "" :: go rest names
        else match names with
          | n :: more => .symbol n :: go rest more
          | [] => .symbol "" :: go rest []
  go rule.arguments use.picked

def checkHeader (ruleAtom useAtom : Atom) : Bool :=
  match decodeRule ruleAtom, decodeHeader useAtom with
  | some rule, some use =>
      rule.label == use.label && admittedRule rule && decide use.picked.Nodup &&
        let written := headerWritten rule use
        let lowered := if use.function then
            (lowerFunctionParts rule use.picked).map (functionAtom use.name rule.expression)
          else lowerMacro rule use.name
        match lowered with
        | some m => match fill written m with
          | some atom => atom.tokens == use.emitted.tokens
          | none => false
        | none => false
  | _, _ => false

/-! ## The function body runs as the template -/

/-- The template run with arguments already captured; its private objects
end with it. -/
def runTemplate (profile : Profile) (written : List Atom) (operands : Nat → Operand) (rule : Rule)
    (params : Nat → Option Param) (locals : List String) (st : State) : Out (Val × State) :=
  let ctx := ctxOf profile written operands params
  let body := instantiate (fun i => .arg i) (fun j => locals.getD j "") rule.body
  let run := if rule.expression then value ctx [] body st
    else (statement ctx [] body st).map fun x => (.void, x.2.2)
  run.map fun x => (x.1, release st.next x.2)

/-- The exported function's body, run with its parameters bound in `env`. -/
def runFunction (profile : Profile) (written : List Atom) (operands : Nat → Operand) (expression : Bool)
    (items : List Marked) (env : Env) (st : State) : Out (Val × State) :=
  let ctx := ctxOf profile written operands fun _ => none
  if expression then value ctx env (blockOf items) st
  else (statement ctx env (blockOf items) st).map fun x => (.void, x.2.2)

/-- What a call supplies: each parameter holds the captured value, or a
pointer to the captured place, of its argument slot; nothing else is bound;
type parameters are syntax. -/
structure Bound (rule : Rule) (paramNames : List String) (params : Nat → Option Param) (env : Env) : Prop where
  slots : ∀ k a n, ((k, a), n) ∈ (evaluated rule).zip paramNames →
    (a.category = .value → ∃ v, params k = some (.value v) ∧ env.lookup n = some (.value v)) ∧
    (a.category ≠ .value → ∃ l, params k = some (.place l) ∧ env.lookup n = some (.value (.ptr l)))
  types : ∀ k a, (k, a) ∈ slotsOf rule → a.category = .syntax → params k = some .syntax
  only : ∀ n b, env.lookup n = some b → n ∈ paramNames

theorem admittedOp_block_value_stmt {args : List Argument} {n : Nat} :
    ∀ xs : List Marked, admittedOp args n .value .block xs = admittedOp args n .stmt .block xs
  | [] => by simp [admittedOp]
  | x :: xs => by simp only [admittedOp, admittedOp_block_value_stmt xs]

theorem item_of_value {args : List Argument} {n : Nat} {t : Marked} (h : admittedAt args n .value t = true) :
    (if stmtHead t then admittedAt args n .stmt t else admittedAt args n .value t) = true := by
  by_cases hs : stmtHead t = true
  · rw [if_pos hs]
    have hb := value_stmtHead_block h hs
    unfold isBlockForm at hb
    split at hb
    · rename_i items
      rw [admittedAt.eq_11 args n .value "block" items (by simp)] at h
      rw [admittedAt.eq_11 args n .stmt "block" items (by simp)]
      have hop : opOf "block" = some .block := by decide
      simp only [hop] at h ⊢
      rw [← admittedOp_block_value_stmt]; exact h
    · cases hb
  · rw [if_neg hs]; exact h

theorem lookup_zip_fst {ev : List (Nat × Argument)} {ps : List String} {k : Nat} {n : String}
    (h : ((ev.map Prod.fst).zip ps).lookup k = some n) : ∃ a, ((k, a), n) ∈ ev.zip ps := by
  induction ev generalizing ps with
  | nil => simp at h
  | cons s ev ih =>
      cases ps with
      | nil => simp at h
      | cons q ps =>
          obtain ⟨j, a⟩ := s
          by_cases hk : k = j
          · subst hk
            simp [] at h
            subst h
            exact ⟨a, by simp⟩
          · have hb : (k == j) = false := by simpa using hk
            simp only [List.map_cons, List.zip_cons_cons, List.lookup, hb] at h
            obtain ⟨b, hb'⟩ := ih h
            exact ⟨b, List.mem_cons_of_mem _ hb'⟩

theorem lookup_zip_fst_some {ev : List (Nat × Argument)} {ps : List String} {k : Nat} {a : Argument}
    (hlen : ev.length ≤ ps.length) (hk : (k, a) ∈ ev) : ((ev.map Prod.fst).zip ps).lookup k ≠ none := by
  induction ev generalizing ps with
  | nil => simp at hk
  | cons s ev ih =>
      cases ps with
      | nil => simp at hlen
      | cons q ps =>
          obtain ⟨j, b⟩ := s
          by_cases hkj : k = j
          · subst hkj; simp []
          · have hb : (k == j) = false := by simpa using hkj
            simp only [List.map_cons, List.zip_cons_cons, List.lookup, hb]
            rcases List.mem_cons.mp hk with he | hm
            · simp only [Prod.mk.injEq] at he; exact absurd he.1 hkj
            · exact ih (by simpa using hlen) hm

theorem slots_get {rule : Rule} {k : Nat} {a : Argument} (h : (k, a) ∈ slotsOf rule) :
    rule.arguments[k]? = some a := by
  unfold slotsOf at h
  rw [List.mem_iff_getElem] at h
  obtain ⟨m, hm, he⟩ := h
  simp only [List.length_zip, List.length_range, Nat.min_self] at hm
  simp only [List.getElem_zip, List.getElem_range, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  simp

theorem evaluated_mem {rule : Rule} {k : Nat} {a : Argument} :
    (k, a) ∈ evaluated rule ↔ (k, a) ∈ slotsOf rule ∧ a.category ≠ .syntax := by
  simp [evaluated, List.mem_filter]

theorem lowerFunctionParts_items {rule : Rule} {names : List String} {parts : FunctionParts}
    (h : lowerFunctionParts rule names = some parts) :
    names.length = (evaluated rule).length + rule.locals.length ∧
      parts.items = (bodyView (tgt (functionSlots rule (names.take (evaluated rule).length))
        (fun j => (names.drop (evaluated rule).length).getD j "") rule.body)).2 := by
  unfold lowerFunctionParts at h
  by_cases hl : names.length = (evaluated rule).length + rule.locals.length
  · refine ⟨hl, ?_⟩
    simp only [hl, ne_eq, not_true_eq_false, if_false, bind, Option.bind_eq_some_iff] at h
    obtain ⟨ps, -, h⟩ := h
    split at h
    · split at h
      · simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at h
        obtain ⟨_, -, rfl⟩ := h; rfl
      · simp at h
    · simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨_, -, rfl⟩ := h; rfl
  · simp [hl] at h

/-- **The exported function's body runs as the rule's template.** For any
admitted rule and the parts `lowerFunctionParts` gives with distinct names,
and any parameter values and places a call supplies, running the body has the
outcome of the template with those captured arguments. -/
theorem function_correct (profile : Profile) (written : List Atom) (operands : Nat → Operand) (rule : Rule)
    (names : List String) (parts : FunctionParts) (st : State) (params : Nat → Option Param) (env : Env)
    (lowered : lowerFunctionParts rule names = some parts) (distinct : names.Nodup)
    (admitted : admittedRule rule = true)
    (bound : Bound rule (names.take (evaluated rule).length) params env) :
    runFunction profile written operands rule.expression parts.items env st =
      runTemplate profile written operands rule params (names.drop (evaluated rule).length) st := by
  obtain ⟨hlen, hitems⟩ := lowerFunctionParts_items lowered
  rw [hitems]
  generalize hP : names.take (evaluated rule).length = paramNames at bound ⊢
  generalize hD : names.drop (evaluated rule).length = localNames
  have hlenP : paramNames.length = (evaluated rule).length := by
    rw [← hP]; simp; omega
  have hlenD : localNames.length = rule.locals.length := by rw [← hD]; simp; omega
  have hdisj : ∀ x, x ∈ paramNames → x ∉ localNames := by
    intro x hx hy
    rw [← hP] at hx; rw [← hD] at hy
    have := List.nodup_append.mp ((List.take_append_drop (evaluated rule).length names).symm ▸ distinct)
    exact this.2.2 _ hx _ hy rfl
  -- the slots the body reads
  have low : Lowering rule.arguments rule.locals.length params env (functionSlots rule paramNames)
      (fun j => localNames.getD j "") := by
    refine ⟨fun i hi => ?_, fun i hs => ?_, fun j hj => ?_⟩
    · obtain ⟨a, ha⟩ : ∃ a, rule.arguments[i]? = some a := ⟨_, List.getElem?_eq_getElem hi⟩
      have hmem : (i, a) ∈ slotsOf rule := by
        unfold slotsOf; exact mem_zip_range _ i a ha
      unfold functionSlots
      cases hl : ((evaluated rule).map Prod.fst |>.zip paramNames).lookup i with
      | some n =>
          obtain ⟨b, hb⟩ := lookup_zip_fst hl
          have hbm : (i, b) ∈ evaluated rule := (List.of_mem_zip hb).1
          have hb' := slots_get (evaluated_mem.mp hbm).1
          rw [ha] at hb'; cases hb'
          simp only [ha]
          obtain ⟨hv, hpl⟩ := bound.slots i a n hb
          by_cases hc : a.category = .value
          · obtain ⟨v, hpv, hev⟩ := hv hc
            rw [if_pos hc, hpv]; exact .value v n hev
          · obtain ⟨l, hpl', hel⟩ := hpl hc
            rw [if_neg hc, hpl']; exact .place l n hel
      | none =>
          have hsyn : a.category = .syntax := by
            by_contra hc
            exact lookup_zip_fst_some (by omega) (evaluated_mem.mpr ⟨hmem, hc⟩) hl
          rw [bound.types i a hmem hsyn]; exact .code
    · unfold slotIs at hs
      cases ha : rule.arguments[i]? with
      | none => rw [ha] at hs; cases hs
      | some a =>
          rw [ha] at hs
          exact bound.types i a (by unfold slotsOf; exact mem_zip_range _ i a ha) (by simpa using hs)
    · cases he : env.lookup (localNames.getD j "") with
      | none => rfl
      | some b =>
          have hin := bound.only _ b he
          have hloc : localNames.getD j "" ∈ localNames := by
            simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show j < localNames.length by omega),
              Option.getD_some]
            exact List.getElem_mem _
          exact absurd hloc (hdisj _ hin)
  have hsize : ∀ m : Marked, sizeOf m < sizeOf m + 1 := fun m => Nat.lt_succ_self _
  have sep : Separate [] env := fun _ _ _ => rfl
  unfold runFunction runTemplate
  by_cases hblk : isBlockForm rule.body = true
  · -- a block template: the function body is its items
    obtain ⟨bitems, hb⟩ : ∃ items, rule.body = .list (.symbol "block" :: items) := by
      generalize rule.body = b at hblk ⊢
      unfold isBlockForm at hblk
      split at hblk
      · exact ⟨_, rfl⟩
      · cases hblk
    have htgtb : tgt (functionSlots rule paramNames) (fun j => localNames.getD j "") rule.body =
        .list (.symbol "block" :: bitems.map (tgt (functionSlots rule paramNames) (fun j => localNames.getD j ""))) := by
      rw [hb, tgt_head _ _ (by decide)]
    have hsrcb : instantiate (fun i => Marked.arg i) (fun j => localNames.getD j "") rule.body =
        .list (.symbol "block" :: bitems.map (src (fun j => localNames.getD j ""))) := by
      rw [hb]; exact src_list _ _
    rw [htgtb, hsrcb]
    simp only [bodyView]
    have hall : admittedItems rule.arguments rule.locals.length bitems = true := by
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
      rw [hbi, admittedItems_append, hE, Bool.true_and]
      split at hlast
      · simp only [admittedItems, admittedOp, Bool.and_true]; exact item_of_value hlast
      · exact hlast
    have simB := items_of (.inr rfl) bitems (fun x _ p hp => lower_sim low _ x (hsize x) p hp) hall
    have hst := statements_agree profile written operands (sims_agrees profile written operands simB) [] sep st
    simp only [List.nil_append] at hst
    split
    · simp only [blockOf, value]
      rw [hst]
      cases statements (ctxOf profile written operands params) [] (bitems.map (src fun j => localNames.getD j "")) st with
      | error => rfl
      | ok r => simp [extend, bind, Except.bind, pure, Except.pure, Except.map, release_release]
    · simp only [blockOf, statement]
      rw [hst]
      cases statements (ctxOf profile written operands params) [] (bitems.map (src fun j => localNames.getD j "")) st with
      | error => rfl
      | ok r => simp [extend, bind, Except.bind, pure, Except.pure, Except.map, release_release]
  · -- a single template item
    have hblk' : isBlockForm rule.body = false := by simpa using hblk
    have hadm : (if rule.expression = true then admittedAt rule.arguments rule.locals.length .value rule.body
        else admittedItems rule.arguments rule.locals.length [rule.body]) = true := by
      have h := admitted
      unfold admittedRule at h
      split at h
      · next items heq => rw [heq] at hblk'; simp [isBlockForm] at hblk'
      · exact h
    split
    · rename_i hexpr
      rw [if_pos hexpr] at hadm
      obtain ⟨simB, hkB⟩ := lower_sim low _ rule.body (hsize _) .value hadm
      have hpl : isBlockForm (tgt (functionSlots rule paramNames) (fun j => localNames.getD j "") rule.body) = false := by
        rw [hkB.block]; exact hblk'
      have hs : stmtHead rule.body = false := by
        cases h : stmtHead rule.body
        · rfl
        · rw [value_stmtHead_block hadm h] at hblk'; cases hblk'
      rw [bodyView_plain hpl]
      simp only [blockOf, value, statements]
      rw [statement_expr _ _ _ _ (by rw [hkB.stmt]; exact hs)]
      have hv := (sim_agrees profile written operands simB) [] sep st
      simp only [List.nil_append] at hv
      rw [hv]
      cases value (ctxOf profile written operands params) [] (src (fun j => localNames.getD j "") rule.body) st with
      | error => rfl
      | ok r => simp [bind, Except.bind, pure, Except.pure, Except.map]
    · rename_i hexpr
      rw [if_neg hexpr] at hadm
      have hitem : (if stmtHead rule.body then admittedAt rule.arguments rule.locals.length .stmt rule.body
          else admittedAt rule.arguments rule.locals.length .value rule.body) = true := by
        simp only [admittedItems, admittedOp, Bool.and_eq_true] at hadm; exact hadm.1
      have simB := item_sim (fun p hp => lower_sim low _ rule.body (hsize _) p hp) hitem
      have hkB : HeadKept rule.body (tgt (functionSlots rule paramNames) (fun j => localNames.getD j "") rule.body) := by
        split at hitem
        · exact (lower_sim low _ rule.body (hsize _) .stmt hitem).2
        · exact (lower_sim low _ rule.body (hsize _) .value hitem).2
      have hpl : isBlockForm (tgt (functionSlots rule paramNames) (fun j => localNames.getD j "") rule.body) = false := by
        rw [hkB.block]; exact hblk'
      rw [bodyView_plain hpl]
      simp only [blockOf, statement, statements]
      have hs := ((sim_agrees profile written operands simB) [] sep st).1
      simp only [List.nil_append] at hs
      rw [hs]
      cases statement (ctxOf profile written operands params) [] (src (fun j => localNames.getD j "") rule.body) st with
      | error => rfl
      | ok r => simp [extend, bind, Except.bind, pure, Except.pure, Except.map]

/-- The function body behaves as the source use whose arguments are code that
yields the values and places the call supplies, with no effect: so every law
stated for the use holds for the exported function. -/
theorem function_as_use (profile : Profile) (written : List Atom) (operands : Nat → Operand) (rule : Rule)
    (names : List String) (parts : FunctionParts) (st : State) (params : Nat → Option Param) (env : Env)
    (lowered : lowerFunctionParts rule names = some parts) (distinct : names.Nodup)
    (admitted : admittedRule rule = true)
    (bound : Bound rule (names.take (evaluated rule).length) params env)
    (supplied : acquireArguments profile written operands (slotsOf rule) (fun _ => none) st = .ok (params, st)) :
    runFunction profile written operands rule.expression parts.items env st =
      invoke profile written operands rule (names.drop (evaluated rule).length) st := by
  rw [function_correct profile written operands rule names parts st params env lowered distinct admitted bound]
  unfold invoke runTemplate
  rw [supplied]

/-- A recorded header function the kernel admits is the lowering of its rule,
and its body, given the values and places a call supplies, runs as the rule's
template. -/
theorem recorded_function_correct (ruleAtom useAtom : Atom) (h : checkHeader ruleAtom useAtom = true) :
    ∃ rule use parts, decodeRule ruleAtom = some rule ∧ decodeHeader useAtom = some use ∧
      (use.function = true →
        lowerFunctionParts rule use.picked = some parts ∧
        (fill (headerWritten rule use) (functionAtom use.name rule.expression parts)).map Atom.tokens =
          some use.emitted.tokens ∧
        ∀ (profile : Profile) (written : List Atom) (operands : Nat → Operand) (st : State)
          (params : Nat → Option Param) (env : Env),
          Bound rule (use.picked.take (evaluated rule).length) params env →
          runFunction profile written operands rule.expression parts.items env st =
            runTemplate profile written operands rule params (use.picked.drop (evaluated rule).length) st) := by
  unfold checkHeader at h
  cases hr : decodeRule ruleAtom with
  | none => simp [hr] at h
  | some rule =>
      cases hu : decodeHeader useAtom with
      | none => simp [hr, hu] at h
      | some use =>
          simp only [hr, hu, Bool.and_eq_true, decide_eq_true_eq] at h
          obtain ⟨⟨⟨_, hadm⟩, hnd⟩, hlow⟩ := h
          by_cases hf : use.function = true
          · simp only [hf, if_true] at hlow
            cases hl : lowerFunctionParts rule use.picked with
            | none => simp [hl] at hlow
            | some parts =>
                simp only [hl, Option.map_some] at hlow
                cases hfl : fill (headerWritten rule use) (functionAtom use.name rule.expression parts) with
                | none => simp [hfl] at hlow
                | some atom =>
                    simp only [hfl] at hlow
                    refine ⟨rule, use, parts, rfl, rfl, fun _ => ⟨hl, by rw [hfl]; simpa using hlow, ?_⟩⟩
                    intro profile written operands st params env bound
                    exact function_correct profile written operands rule use.picked parts st params env hl hnd hadm
                      bound
          · exact ⟨rule, use, ⟨[], [], .symbol ""⟩, rfl, rfl, fun h' => absurd h' hf⟩

end Mettapedia.GSLT.LanguageDef.MacroExportHeader

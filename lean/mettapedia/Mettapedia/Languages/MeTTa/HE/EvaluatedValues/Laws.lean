import Mettapedia.Languages.MeTTa.HE.EvaluatedValues.Calculus

/-!
# Laws of the rules that read the mark

The laws here hold for both rules that read the evaluated mark,
`rustEqualToInput` and `evaluatedValues`, under hypotheses saying which
results are values. A value (an atomic atom, or an expression whose root is
marked) is a trivial computation: evaluated again, it returns itself once.

* `eval_value`, `eval_self_isValue` — values return themselves; an answer
  equal to the evaluated term is a value.
* `ValueResults` — every result of a term is a value. It holds for values,
  for terms whose results keep their erasure (`ValueResults.of_self`), for
  untyped calls whose replies return values and whose arguments keep their
  erasure (`ValueResults.call`), and, under `evaluatedValues`, for untyped
  calls whose replies return values whatever the arguments
  (`ValueResults.call_stuck`; the class of all code-free terms is in
  `CodeFree`).
* `eval_kleisli_idempotent` — on such terms evaluation is a projection:
  `kbind (eval e) eval = eval e`.
* `eval_call_untyped` — an untyped call is the bind of its arguments' results
  with the call on each combination (applicative compositionality), under
  every rule.
* `eval_twice` — call-time choice: when `e` has value results, `(twice e)`
  returns `(pair v v)` once for each result `v` of `e`.
* `eval_alias` — definitional transparency up to marks on arguments with value
  results.
* `eval_superpose_collapse`, `eval_unique`, `unique_nodup`, `unique_support` —
  on a term with value results, collapse then superpose is the identity and
  `unique` keeps the first result of each erasure.

Under `rustEqualToInput` a stuck call whose arguments were reduced is not a
value, and the alias law and collapse-then-superpose fail on it
(`Probes.rust_violates_alias`, `Probes.rust_violates_superpose_collapse`).

Call-time choice is the semantics of nondeterministic functional logic
programming (CRWL; González-Moreno, Hortalá-González, López-Fraguas,
Rodríguez-Artalejo, J. Logic Programming 1999; Curry and Toy): a parameter is
shared, so both occurrences of `$x` in `(pair $x $x)` see the same choice.
Run-time choice (term rewriting; Hussmann, J. Logic Programming 1992) re-chooses
at every occurrence; HE gives it to `Atom` parameters, whose arguments are
passed as written. The `reevaluate` rule is neither on stuck results: it keeps
call-time choice for the parameter and then re-chooses whenever a value passes
through a return. Sharing a value instead of re-running it is the
lazy-nondeterminism discipline of Fischer, Kiselyov and Shan (ICFP 2009).
-/

namespace Mettapedia.Languages.MeTTa.HE.EvaluatedValues

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-! ## Unfolding the fixed point -/

@[simp] theorem argDemand_value_run (ev : Evaluator) (c : MAtom) :
    (argDemand (.value, c)).run ev = ev c := by
  simp only [argDemand, Demand.run_need]
  cases ev c <;> rfl

@[simp] theorem argDemand_atom_run (ev : Evaluator) (c : MAtom) :
    (argDemand (.atom, c)).run ev = some [c] := rfl

theorem withModes_nil (cs : List MAtom) : withModes [] cs = cs.map fun c => (.value, c) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [withModes, ih]

/-- One unfolding of the evaluator on an expression whose mark is not read. -/
theorem eval_expr_open (rule : ReturnRule) (P : Program) {m : Bool} (cs : List MAtom)
    (h : (rule.honorsMark && m) = false) :
    eval rule P (.expr m cs) =
      ((optTraverse (withModes (P.elementModes cs) cs) fun p => (argDemand p).run (eval rule P)).bind
        fun rss => optFlatMap (combos rss) fun vs => (P.callDemand rule.marksStuck vs).run (eval rule P)).map
        (List.map (MAtom.markIf (MAtom.expr m cs).erase)) := by
  rw [eval_fix, stepDemand_expr_open P cs h]
  simp [Program.argsDemand]

/-- An answer with the erasure of the evaluated term is a value, under every
rule: every rule records that mark. -/
theorem eval_self_isValue {rule : ReturnRule} {P : Program} {t : MAtom} {R : List MAtom}
    (h : eval rule P t = some R) : ∀ r ∈ R, r.erase = t.erase → r.isValue = true := by
  rw [eval_fix] at h
  cases t with
  | expr m cs =>
    by_cases hm : (rule.honorsMark && m) = true
    · simp only [stepDemand, ReturnRule.keeps, hm, ↓reduceIte, Demand.run_done,
        Option.some.injEq] at h
      subst h
      intro r hr _
      simp only [List.mem_singleton] at hr
      subst hr
      simp only [Bool.and_eq_true] at hm
      exact hm.2
    · rw [stepDemand_expr_open P cs (by simpa using hm), Demand.run_map] at h
      obtain ⟨R₀, -, rfl⟩ := Option.map_eq_some_iff.mp h
      intro r hr hre
      obtain ⟨r₀, -, rfl⟩ := List.mem_map.mp hr
      exact MAtom.isValue_markIf_of_erase (by simpa using hre)
  | _ =>
    simp only [stepDemand, ReturnRule.keeps, Bool.false_eq_true, ↓reduceIte, openStep,
      Demand.run_done, Option.some.injEq] at h
    subst h
    intro r hr _
    simp only [List.mem_singleton] at hr
    subst hr
    rfl

/-- Every result of `t` under `rule` is a value. -/
def ValueResults (rule : ReturnRule) (P : Program) (t : MAtom) : Prop :=
  ∀ R, eval rule P t = some R → ∀ r ∈ R, r.isValue = true

theorem ValueResults.of_isValue {rule : ReturnRule} (hmark : rule.honorsMark = true) (P : Program)
    {v : MAtom} (hv : v.isValue = true) : ValueResults rule P v := by
  intro R h r hr
  rw [eval_value hmark P hv] at h
  cases h
  simp only [List.mem_singleton] at hr
  subst hr
  exact hv

/-- A term whose results all have its own erasure has value results. -/
theorem ValueResults.of_self {rule : ReturnRule} {P : Program} {t : MAtom}
    (h : ∀ R, eval rule P t = some R → ∀ r ∈ R, r.erase = t.erase) :
    ValueResults rule P t :=
  fun R hR r hr => eval_self_isValue hR r hr (h R hR r hr)

theorem map_markIf_of_values (a : Atom) {R : List MAtom} (hR : ∀ r ∈ R, r.isValue = true) :
    R.map (MAtom.markIf a) = R := by
  conv => rhs; rw [← List.map_id R]
  exact List.map_congr_left fun r hr => MAtom.markIf_of_isValue a (hR r hr)

theorem flatMap_singleton_eq_map {α β : Type} (l : List α) (f : α → β) :
    l.flatMap (fun a => [f a]) = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-! ## T1: projection -/

/-- **Projection law.** On a term whose results are values, evaluating the
results again yields exactly those results. -/
theorem eval_kleisli_idempotent {rule : ReturnRule} (hmark : rule.honorsMark = true) (P : Program)
    (t : MAtom) (ht : ValueResults rule P t) :
    kbind (eval rule P t) (eval rule P) = eval rule P t := by
  cases h : eval rule P t with
  | none => rfl
  | some R =>
    simp only [kbind, Option.bind_some]
    rw [optFlatMap_eq_some (g := fun r => [r]) fun r hr => eval_value hmark P (ht R h r hr)]
    simp

/-- Each value result, evaluated again, is its own single result. -/
theorem eval_result_stable {rule : ReturnRule} (hmark : rule.honorsMark = true) {P : Program}
    {t : MAtom} {R : List MAtom} (ht : ValueResults rule P t)
    (h : eval rule P t = some R) : ∀ r ∈ R, eval rule P r = some [r] :=
  fun r hr => eval_value hmark P (ht R h r hr)

/-! ## T2: compositionality and call-time choice -/

theorem elementModes_untyped {P : Program} {f : String} (es : List MAtom)
    (hprim : Prim.ofName f = none) (hdecl : P.decl? f = none) :
    P.elementModes (.symbol f :: es) = [.value] := by
  simp [Program.elementModes, Program.paramModes, hprim, hdecl]

theorem callDemand_untyped (P : Program) (ms : Bool) {f : String} (args : List MAtom)
    (hprim : Prim.ofName f = none) : P.callDemand ms (.symbol f :: args) =
      P.queryDemand ms (.symbol f :: args) := by
  simp [Program.callDemand, hprim]

/-- **Applicative compositionality.** An untyped call evaluates its arguments,
takes every combination of their results, and calls the head on each
combination of values. -/
theorem eval_call_untyped (rule : ReturnRule) (P : Program) {m : Bool} {f : String}
    (es : List MAtom) (hm : (rule.honorsMark && m) = false) (hprim : Prim.ofName f = none)
    (hdecl : P.decl? f = none) :
    eval rule P (.expr m (.symbol f :: es)) =
      ((optTraverse es (eval rule P)).bind fun Rs =>
        optFlatMap (combos Rs) fun vs =>
          (P.queryDemand rule.marksStuck (.symbol f :: vs)).run (eval rule P)).map
        (List.map (MAtom.markIf (MAtom.expr m (.symbol f :: es)).erase)) := by
  rw [eval_expr_open rule P _ hm, elementModes_untyped es hprim hdecl]
  simp only [withModes, withModes_nil, optTraverse_cons, argDemand_value_run, optTraverse_map]
  rw [eval_nonexpr rule P (by simp)]
  simp only [Option.bind_some]
  cases optTraverse es (eval rule P) with
  | none => rfl
  | some Rs =>
    simp only [Option.map_some, Option.bind_some, combos_cons, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, optFlatMap_map]
    congr 2
    funext vs
    rw [callDemand_untyped P _ vs hprim]

theorem combos_single {α : Type} (R : List α) : combos [R] = R.map fun v => [v] := by
  induction R with
  | nil => rfl
  | cons r R ih => simpa using ih

/-- The head symbol of an equation's left-hand side. -/
def headSymbol? : Atom → Option String
  | .expression (.symbol f :: _) => some f
  | _ => none

/-- The equations whose left-hand side is headed by `f`, in stored order. -/
def Program.defn (P : Program) (f : String) : List (Atom × Atom) :=
  P.equations.filter fun eq => headSymbol? eq.1 == some f

/-- Every left-hand side is a symbol-headed expression. -/
def Program.SymbolHeaded (P : Program) : Prop :=
  ∀ eq ∈ P.equations, (headSymbol? eq.1).isSome

theorem matchAtom_head_ne {l : Atom} {g f : String} (hl : headSymbol? l = some g) (hgf : g ≠ f)
    (m : Bool) (vs : List MAtom) (σ : Subst) : matchAtom l (.expr m (.symbol f :: vs)) σ = none := by
  match l, hl with
  | .expression (.symbol g' :: ps), hl =>
    simp only [headSymbol?, Option.some.injEq] at hl
    subst hl
    simp [matchAtom, matchList, hgf]

/-- Only the definition of the head can answer a call. -/
theorem replies_eq_defn {P : Program} (hP : P.SymbolHeaded) (m : Bool) (f : String)
    (vs : List MAtom) : P.replies (.expr m (.symbol f :: vs)) =
      (P.defn f).filterMap fun eq =>
        (matchAtom eq.1 (.expr m (.symbol f :: vs)) []).map fun σ => (code eq.2).subst σ := by
  simp only [Program.replies, Program.defn, List.filterMap_filter]
  apply List.filterMap_congr
  intro eq heq
  split
  · rfl
  · rename_i hne
    obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp (hP eq heq)
    have hgf : g ≠ f := by
      intro hgf
      subst hgf
      simp [hg] at hne
    simp [matchAtom_head_ne hg hgf]

theorem forall₂_values_of_optTraverse {rule : ReturnRule} {P : Program} {es : List MAtom}
    {Rs : List (List MAtom)}
    (hes : ∀ e ∈ es, ValueResults rule P e)
    (h : optTraverse es (eval rule P) = some Rs) {vs : List MAtom}
    (hvs : vs ∈ combos Rs) : ∀ v ∈ vs, v.isValue = true := by
  have h₁ := forall₂_of_optTraverse h
  have h₂ := forall₂_mem_of_mem_combos hvs
  intro v hv
  obtain ⟨R, hR, hvR⟩ := forall₂_exists_left h₂ hv
  obtain ⟨e, hemem, he⟩ := forall₂_exists_right h₁ hR
  exact hes e hemem R he v hvR

theorem map_erase_of_combos {rule : ReturnRule} {P : Program} :
    ∀ {es : List MAtom} {Rs : List (List MAtom)} {vs : List MAtom},
      (∀ e ∈ es, ∀ R, eval rule P e = some R → ∀ v ∈ R, v.erase = e.erase) →
      List.Forall₂ (fun a b => eval rule P a = some b) es Rs →
      List.Forall₂ (· ∈ ·) vs Rs → vs.map MAtom.erase = es.map MAtom.erase
  | [], [], [], _, .nil, .nil => rfl
  | _ :: _, _ :: _, _ :: _, hes, .cons heR hrest, .cons hvR hvrest => by
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨hes _ List.mem_cons_self _ heR _ hvR,
      map_erase_of_combos (fun e he => hes e (List.mem_cons_of_mem _ he)) hrest hvrest⟩

/-- **Which untyped calls return values.** A call of an untyped head returns
only values when each argument's results keep the argument's erasure (so a
stuck or refused call is the evaluated term itself) and every reply other
than `NotReducible` has value results. Reduced arguments break the first
condition under the Rust rule (`Probes.fr_h_values`); an `Atom` result breaks the second by
design (`Probes.ga_result_is_code`). -/
theorem ValueResults.call {rule : ReturnRule} {P : Program} {f : String} {es : List MAtom}
    (hprim : Prim.ofName f = none) (hdecl : P.decl? f = none)
    (hes : ∀ e ∈ es, ∀ R, eval rule P e = some R → ∀ v ∈ R, v.erase = e.erase)
    (hrep : ∀ vs, vs.map MAtom.erase = es.map MAtom.erase →
      ∀ r ∈ P.replies (.expr false (.symbol f :: vs)), ¬ r.erase = Atom.notReducible →
        ValueResults rule P r) :
    ValueResults rule P (.expr false (.symbol f :: es)) := by
  intro R h r hr
  rw [eval_call_untyped rule P es (by simp) hprim hdecl] at h
  obtain ⟨R₀, h₀, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨Rs, hRs, hR₀⟩ := Option.bind_eq_some_iff.mp h₀
  obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
  rw [MAtom.isValue_markIf_iff]
  obtain ⟨vs, hvs, Q, hQ, hr₀Q⟩ := mem_of_optFlatMap hR₀ hr₀
  have hvse : vs.map MAtom.erase = es.map MAtom.erase :=
    map_erase_of_combos hes (forall₂_of_optTraverse hRs) (forall₂_mem_of_mem_combos hvs)
  have hcall : (MAtom.expr rule.marksStuck (.symbol f :: vs)).erase =
      (MAtom.expr false (.symbol f :: es)).erase := by simp [hvse]
  unfold Program.queryDemand at hQ
  split at hQ
  · simp only [Demand.run_done, Option.some.injEq] at hQ
    subst hQ
    simp only [List.mem_singleton] at hr₀Q
    subst hr₀Q
    exact Or.inl hcall
  · rename_i r₁ rs hreps
    rw [Demand.run_forEach] at hQ
    obtain ⟨rr, hrr, Q', hQ', hr₀Q'⟩ := mem_of_optFlatMap hQ hr₀Q
    have hmem : rr ∈ P.replies (.expr false (.symbol f :: vs)) := by rw [hreps]; exact hrr
    simp only [Program.callResultMode, Program.resultMode, hdecl, returnDemand] at hQ'
    split at hQ'
    · simp only [Demand.run_done, Option.some.injEq] at hQ'
      subst hQ'
      simp only [List.mem_singleton] at hr₀Q'
      subst hr₀Q'
      exact Or.inl hcall
    · rename_i hnr
      simp only [Demand.run_need, Demand.run_done] at hQ'
      have hQ'' : eval rule P rr = some Q' := by
        cases h' : eval rule P rr <;> simp_all
      exact Or.inr (hrep vs hvse rr hmem hnr Q' hQ'' r₀ hr₀Q')

/-- **Which untyped calls return values under `evaluatedValues`.** A stuck
call is a value whatever its arguments reduced to, so an untyped call returns
only values as soon as every reply other than `NotReducible` has value
results. Returning code takes an `Atom` result, `collapse` or `car-atom`
(`Probes.ga_result_is_code`). -/
theorem ValueResults.call_stuck {P : Program} {f : String} {es : List MAtom}
    (hprim : Prim.ofName f = none) (hdecl : P.decl? f = none)
    (hrep : ∀ vs, ∀ r ∈ P.replies (.expr false (.symbol f :: vs)),
      ¬ r.erase = Atom.notReducible → ValueResults .evaluatedValues P r) :
    ValueResults .evaluatedValues P (.expr false (.symbol f :: es)) := by
  intro R h r hr
  rw [eval_call_untyped .evaluatedValues P es (by simp) hprim hdecl] at h
  obtain ⟨R₀, h₀, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨Rs, hRs, hR₀⟩ := Option.bind_eq_some_iff.mp h₀
  obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
  rw [MAtom.isValue_markIf_iff]
  obtain ⟨vs, hvs, Q, hQ, hr₀Q⟩ := mem_of_optFlatMap hR₀ hr₀
  unfold Program.queryDemand at hQ
  split at hQ
  · simp only [Demand.run_done, Option.some.injEq] at hQ
    subst hQ
    simp only [List.mem_singleton] at hr₀Q
    subst hr₀Q
    exact Or.inr rfl
  · rename_i r₁ rs hreps
    rw [Demand.run_forEach] at hQ
    obtain ⟨rr, hrr, Q', hQ', hr₀Q'⟩ := mem_of_optFlatMap hQ hr₀Q
    have hmem : rr ∈ P.replies (.expr false (.symbol f :: vs)) := by rw [hreps]; exact hrr
    simp only [Program.callResultMode, Program.resultMode, hdecl, returnDemand] at hQ'
    split at hQ'
    · simp only [Demand.run_done, Option.some.injEq] at hQ'
      subst hQ'
      simp only [List.mem_singleton] at hr₀Q'
      subst hr₀Q'
      exact Or.inr rfl
    · rename_i hnr
      simp only [Demand.run_need, Demand.run_done] at hQ'
      have hQ'' : eval .evaluatedValues P rr = some Q' := by
        cases h' : eval .evaluatedValues P rr <;> simp_all
      exact Or.inr (hrep vs rr hmem hnr Q' hQ'' r₀ hr₀Q')

/-- A call on values with no applicable equation is a value with exactly
those arguments. -/
theorem eval_stuck_call {rule : ReturnRule} (hmark : rule.honorsMark = true) (P : Program)
    {f : String} (vs : List MAtom)
    (hvs : ∀ v ∈ vs, v.isValue = true) (hprim : Prim.ofName f = none) (hdecl : P.decl? f = none)
    (hnone : P.replies (.expr false (.symbol f :: vs)) = []) :
    eval rule P (.expr false (.symbol f :: vs)) =
      some [.expr true (.symbol f :: vs)] := by
  rw [eval_call_untyped rule P vs (by simp) hprim hdecl,
    optTraverse_eq_some (g := fun v => [v]) fun v hv => eval_value hmark P (hvs v hv)]
  simp [combos_singletons, Program.queryDemand, hnone, MAtom.markIf, MAtom.mark]

/-- **Call-time choice.** If `tw` is defined by the single equation
`(tw $x) = (pr $x $x)`, `pr` has no equations, and `e` has value results, then
`(tw e)` returns `(pr v v)` once for each result `v` of `e`. -/
theorem eval_twice {rule : ReturnRule} (hmark : rule.honorsMark = true) {P : Program}
    (hP : P.SymbolHeaded) {tw pr x : String}
    (htw : Prim.ofName tw = none) (hpr : Prim.ofName pr = none)
    (hdtw : P.decl? tw = none) (hdpr : P.decl? pr = none)
    (hdef : P.defn tw = [(.expression [.symbol tw, .var x], .expression [.symbol pr, .var x, .var x])])
    (hstuck : P.defn pr = []) (e : MAtom) (hval : ValueResults rule P e) :
    eval rule P (.expr false [.symbol tw, e]) =
      (eval rule P e).map (List.map fun v => .expr true [.symbol pr, v, v]) := by
  rw [eval_call_untyped rule P [e] (by simp) htw hdtw]
  simp only [optTraverse_cons, optTraverse_nil, Option.map_some]
  cases he : eval rule P e with
  | none => rfl
  | some R =>
    simp only [Option.bind_some, combos_single, optFlatMap_map]
    have hcall : ∀ v ∈ R, (P.queryDemand rule.marksStuck [.symbol tw, v]).run (eval rule P) =
        some [.expr true [.symbol pr, v, v]] := by
      intro v hv
      have hrep : P.replies (.expr false [.symbol tw, v]) = [.expr false [.symbol pr, v, v]] := by
        rw [replies_eq_defn hP, hdef]
        simp [matchAtom, matchList, Subst.lookup_cons]
      have hvv : ∀ w ∈ [v, v], w.isValue = true := by
        intro w hw
        simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hw
        subst hw
        exact hval R he w hv
      have hstuckv : P.replies (.expr false [.symbol pr, v, v]) = [] := by
        rw [replies_eq_defn hP, hstuck]
        rfl
      have hne : ¬ (Atom.expression [Atom.symbol pr, v.erase, v.erase] = Atom.notReducible) := by
        simp [Atom.notReducible]
      simp only [Program.queryDemand, hrep, Program.callResultMode, Program.resultMode, hdtw,
        returnDemand, MAtom.erase_expr, MAtom.erase_symbol, List.map_cons, List.map_nil, hne,
        ↓reduceIte, Demand.run_forEach, optFlatMap_cons, optFlatMap_nil, Demand.run_need,
        Demand.run_done]
      rw [eval_stuck_call hmark P [v, v] hvv hpr hdpr hstuckv]
      simp
    rw [optFlatMap_eq_some (g := fun v => [.expr true [.symbol pr, v, v]]) hcall,
      flatMap_singleton_eq_map, Option.map_some, map_markIf_of_values _ (by simp [MAtom.isValue])]
    rfl

/-! ## T3: definitional transparency -/

theorem matchList_vars {xs : List String} (hxs : xs.Nodup) :
    ∀ {vs : List MAtom} {σ₀ : Subst}, xs.length = vs.length → (∀ x ∈ xs, σ₀.lookup x = none) →
      ∃ σ, matchList (xs.map .var) vs σ₀ = some σ ∧
        List.Forall₂ (fun x v => σ.lookup x = some v) xs vs ∧
        ∀ y, y ∉ xs → σ.lookup y = σ₀.lookup y := by
  induction xs with
  | nil =>
    intro vs σ₀ hlen _
    cases vs with
    | nil => exact ⟨σ₀, by simp [matchList], .nil, fun _ _ => rfl⟩
    | cons _ _ => simp at hlen
  | cons x xs ih =>
    intro vs σ₀ hlen hfresh
    cases vs with
    | nil => simp at hlen
    | cons v vs =>
      have hx : x ∉ xs := (List.nodup_cons.mp hxs).1
      have hxs' : xs.Nodup := (List.nodup_cons.mp hxs).2
      have hfx : σ₀.lookup x = none := hfresh x List.mem_cons_self
      have hfresh' : ∀ y ∈ xs, Subst.lookup ((x, v) :: σ₀) y = none := by
        intro y hy
        have hyx : y ≠ x := fun h => hx (h ▸ hy)
        simp [Subst.lookup_cons, hyx, hfresh y (List.mem_cons_of_mem _ hy)]
      obtain ⟨σ, hσ, hfa, hrest⟩ := ih hxs' (by simpa using hlen) hfresh'
      refine ⟨σ, ?_, .cons ?_ hfa, ?_⟩
      · simp [matchList, matchAtom, hfx, hσ]
      · rw [hrest x hx]; simp [Subst.lookup_cons]
      · intro y hy
        have hyx : y ≠ x := fun h => hy (h ▸ List.mem_cons_self)
        have hyxs : y ∉ xs := fun h => hy (List.mem_cons_of_mem _ h)
        rw [hrest y hyxs]
        simp [Subst.lookup_cons, hyx]

theorem subst_vars {σ : Subst} {xs : List String} {vs : List MAtom}
    (h : List.Forall₂ (fun x v => σ.lookup x = some v) xs vs) :
    (xs.map fun x => code (.var x)).map (MAtom.subst σ) = vs := by
  induction h with
  | nil => rfl
  | cons hxv _ ih => simp only [List.map_cons, code_var, MAtom.subst_var, hxv]; simpa using ih

theorem touched_vars {σ : Subst} {xs : List String} {vs : List MAtom}
    (h : List.Forall₂ (fun x v => σ.lookup x = some v) xs vs) (hne : xs ≠ []) :
    (xs.map fun x => code (.var x)).any (MAtom.touched σ) = true := by
  cases h with
  | nil => exact absurd rfl hne
  | cons hxv _ => simp [hxv]

/-- **Definitional transparency (alias law).** If `g` is defined by the single
equation `(g x₁ … xₙ) = (h x₁ … xₙ)` with distinct variables, both heads are
untyped, and every argument has value results, then a call of `g` and the
same call of `h` make the same observation: the same results up to marks, in
the same order. (Marks may differ: the alias evaluates `h` on the argument
values, so a stuck answer of `h` is the evaluated term there.) -/
theorem eval_alias {rule : ReturnRule} (hmark : rule.honorsMark = true) {P : Program}
    (hP : P.SymbolHeaded) {g h : String} {xs : List String}
    (hxs : xs.Nodup) (hg : Prim.ofName g = none) (hh : Prim.ofName h = none)
    (hdg : P.decl? g = none) (hdh : P.decl? h = none)
    (hdef : P.defn g =
      [(.expression (.symbol g :: xs.map .var), .expression (.symbol h :: xs.map .var))])
    (es : List MAtom) (hlen : es.length = xs.length) (hes : ∀ e ∈ es, ValueResults rule P e) :
    (eval rule P (.expr false (.symbol g :: es))).map (List.map MAtom.erase) =
      (eval rule P (.expr false (.symbol h :: es))).map (List.map MAtom.erase) := by
  rw [eval_call_untyped rule P es (by simp) hg hdg, eval_call_untyped rule P es (by simp) hh hdh]
  have hcomp : ∀ a : Atom, (List.map MAtom.erase ∘ List.map (MAtom.markIf a)) =
      List.map MAtom.erase := fun a => by funext l; simp [Function.comp_def]
  cases hRs : optTraverse es (eval rule P) with
  | none => rfl
  | some Rs =>
    simp only [Option.bind_some, Option.map_map, hcomp]
    rw [optFlatMap_mapResults, optFlatMap_mapResults]
    apply optFlatMap_congr
    intro vs hvs
    have hvals := forall₂_values_of_optTraverse hes hRs hvs
    have hlenvs : xs.length = vs.length := by
      rw [← hlen, (forall₂_of_optTraverse hRs).length_eq,
        (forall₂_mem_of_mem_combos hvs).length_eq]
    obtain ⟨σ, hσ, hfa, -⟩ := matchList_vars hxs (σ₀ := []) hlenvs (by simp)
    have hrep : P.replies (.expr false (.symbol g :: vs)) = [.expr false (.symbol h :: vs)] := by
      rw [replies_eq_defn hP, hdef]
      simp only [List.filterMap_cons, List.filterMap_nil, matchAtom, matchList, ↓reduceIte]
      rw [show (xs.map Atom.var) = xs.map Atom.var from rfl]
      simp only [hσ, Option.map_some, code_expression, List.map_cons, code_symbol, List.map_map]
      have hsub := subst_vars hfa
      simp only [Function.comp_def] at hsub ⊢
      simp only [MAtom.subst_expr, List.map_cons, MAtom.subst_symbol, List.any_cons,
        MAtom.touched_symbol, Bool.false_or, Bool.false_and, hsub]
    have hne : ¬ (Atom.expression (Atom.symbol h :: vs.map MAtom.erase) = Atom.notReducible) := by
      simp [Atom.notReducible]
    have hL : (P.queryDemand rule.marksStuck (.symbol g :: vs)).run (eval rule P) =
        eval rule P (.expr false (.symbol h :: vs)) := by
      simp only [Program.queryDemand, hrep, Program.callResultMode, Program.resultMode, hdg,
        returnDemand, MAtom.erase_expr, MAtom.erase_symbol, List.map_cons, hne, ↓reduceIte,
        Demand.run_forEach, optFlatMap_cons, optFlatMap_nil, Demand.run_need, Demand.run_done]
      cases eval rule P (.expr false (.symbol h :: vs)) <;> simp
    rw [hL, eval_call_untyped rule P vs (by simp) hh hdh,
      optTraverse_eq_some (g := fun v => [v]) fun v hv => eval_value hmark P (hvals v hv)]
    simp only [Option.bind_some, combos_singletons, optFlatMap_cons, optFlatMap_nil]
    cases (P.queryDemand rule.marksStuck (.symbol h :: vs)).run (eval rule P) with
    | none => rfl
    | some r => simp [List.map_map, Function.comp_def]

/-! ## T4, T5: collapse, superpose and unique -/

theorem eval_prim_call (rule : ReturnRule) (P : Program) {m : Bool} {f : String} {p : Prim}
    (hm : (rule.honorsMark && m) = false) (hp : Prim.ofName f = some p) (a : MAtom)
    (hmode : p.params = [.atom]) :
    eval rule P (.expr m [.symbol f, a]) =
      ((primDemand p [a] (P.queryDemand rule.marksStuck [.symbol f, a])).run (eval rule P)).map
        (List.map (MAtom.markIf (MAtom.expr m [.symbol f, a]).erase)) := by
  rw [eval_expr_open rule P _ hm]
  simp only [Program.elementModes, Program.paramModes, hp, hmode, withModes, optTraverse_cons,
    argDemand_value_run, argDemand_atom_run, optTraverse_nil]
  rw [eval_nonexpr rule P (by simp)]
  simp [Program.callDemand, hp]

theorem eval_collapse (rule : ReturnRule) (P : Program) {m : Bool}
    (hm : (rule.honorsMark && m) = false) (e : MAtom) :
    eval rule P (.expr m [.symbol "collapse", e]) =
      (eval rule P e).map fun R =>
        [(MAtom.expr false R).markIf (MAtom.expr m [.symbol "collapse", e]).erase] := by
  rw [eval_prim_call rule P hm rfl e rfl]
  simp only [primDemand, Demand.run_need, Demand.run_done]
  cases eval rule P e <;> rfl

theorem eval_superpose_values {rule : ReturnRule} (hmark : rule.honorsMark = true) (P : Program)
    {m : Bool} (hm : (rule.honorsMark && m) = false)
    {b : Bool} {R : List MAtom} (hR : ∀ r ∈ R, r.isValue = true) :
    eval rule P (.expr m [.symbol "superpose", .expr b R]) = some R := by
  rw [eval_prim_call rule P hm rfl _ rfl]
  simp only [primDemand, Demand.run_forEach, Demand.run_need, Demand.run_done]
  rw [optFlatMap_eq_some (g := fun r => [r]) fun r hr => by
    rw [eval_value hmark P (hR r hr)]; rfl]
  simp only [List.flatMap_singleton', Option.map_some, Option.some.injEq]
  exact map_markIf_of_values _ hR

/-- The program text `(let $c (collapse e) (superpose $c))`. -/
def letCollapseSuperpose (c : String) (e : MAtom) : MAtom :=
  .expr false [.symbol "let", .var c, .expr false [.symbol "collapse", e],
    .expr false [.symbol "superpose", .var c]]

theorem markIf_expr (a : Atom) (m : Bool) (cs : List MAtom) :
    ∃ b, (MAtom.expr m cs).markIf a = .expr b cs := by
  unfold MAtom.markIf
  split
  · exact ⟨true, rfl⟩
  · exact ⟨m, rfl⟩

/-- **Collapse then superpose is the identity** on a term with value results. -/
theorem eval_superpose_collapse {rule : ReturnRule} (hmark : rule.honorsMark = true) (P : Program)
    (c : String) (e : MAtom) (he : ValueResults rule P e) :
    eval rule P (letCollapseSuperpose c e) = eval rule P e := by
  rw [letCollapseSuperpose, eval_expr_open rule P _ (by simp)]
  simp only [Program.elementModes, Program.paramModes, Prim.ofName, Prim.params, withModes,
    optTraverse_cons, argDemand_value_run, argDemand_atom_run, optTraverse_nil]
  rw [eval_nonexpr rule P (by simp), eval_collapse rule P (by simp)]
  cases hR' : eval rule P e with
  | none => rfl
  | some R =>
    have hR := he R hR'
    obtain ⟨b, hb⟩ := markIf_expr (MAtom.expr false [.symbol "collapse", e]).erase false R
    simp only [Option.map_some, Option.bind_some]
    rw [hb]
    simp only [Option.map_some, combos_cons, combos_nil, List.map_cons,
      List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil, optFlatMap_cons,
      optFlatMap_nil, Program.callDemand, Prim.ofName, primDemand, MAtom.erase_var, matchAtom,
      Subst.lookup_nil, Demand.run_need, Demand.run_done]
    simp only [MAtom.subst_expr, Bool.false_and, List.map_cons, MAtom.subst_symbol,
      MAtom.subst_var, Subst.lookup_cons, ↓reduceIte, Option.getD_some, List.map_nil]
    rw [eval_superpose_values hmark P (by simp) hR]
    simp only [Option.bind_some, Option.map_some, Option.some.injEq]
    exact map_markIf_of_values _ hR

/-- **Unique.** On a term with value results, `(unique e)` returns the first
result of each erasure. -/
theorem eval_unique {rule : ReturnRule} (hmark : rule.honorsMark = true) (P : Program) (e : MAtom)
    (he : ValueResults rule P e) :
    eval rule P (.expr false [.symbol "unique", e]) =
      (eval rule P e).map dedupErase := by
  rw [eval_prim_call rule P (by simp) rfl e rfl]
  simp only [primDemand, Demand.run_need, Demand.run_forEach, Demand.run_done]
  cases hR' : eval rule P e with
  | none => rfl
  | some R =>
    have hR := he R hR'
    have hD : ∀ r ∈ dedupErase R, r.isValue = true :=
      fun r hr => hR r ((dedupErase_sublist R).subset hr)
    simp only [Option.bind_some]
    rw [optFlatMap_eq_some (g := fun r => [r]) fun r hr => by
      rw [eval_value hmark P (hD r hr)]; rfl]
    simp only [List.flatMap_singleton', Option.map_some, Option.some.injEq]
    exact map_markIf_of_values _ hD

/-- The results of `(unique e)` are pairwise distinct up to erasure. -/
theorem unique_nodup {rule : ReturnRule} (hmark : rule.honorsMark = true) {P : Program} {e : MAtom}
    (he : ValueResults rule P e) {U : List MAtom}
    (h : eval rule P (.expr false [.symbol "unique", e]) = some U) :
    (U.map MAtom.erase).Nodup := by
  rw [eval_unique hmark P e he] at h
  obtain ⟨R, -, rfl⟩ := Option.map_eq_some_iff.mp h
  exact dedupErase_nodup R

/-- `(unique e)` and `e` have the same results up to erasure. -/
theorem unique_support {rule : ReturnRule} (hmark : rule.honorsMark = true) {P : Program}
    {e : MAtom} (he : ValueResults rule P e) {R : List MAtom}
    (h : eval rule P e = some R) :
    ∃ U, eval rule P (.expr false [.symbol "unique", e]) = some U ∧
      U.Sublist R ∧ ∀ a, a ∈ U.map MAtom.erase ↔ a ∈ R.map MAtom.erase :=
  ⟨dedupErase R, by rw [eval_unique hmark P e he, h]; rfl, dedupErase_sublist R,
    mem_dedupErase_iff R⟩

end Mettapedia.Languages.MeTTa.HE.EvaluatedValues

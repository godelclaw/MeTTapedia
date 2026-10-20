import Mettapedia.Languages.MeTTa.HE.EvaluatedValues.Laws
import Mathlib.Data.Multiset.Bind

/-!
# Evaluation contexts and linear unfolding

For a rule that reads the mark, an expression with a hole in a value
position is an evaluation context in the sense of call-by-value: evaluating
`C[e]` is the same as evaluating `e` and then `C[v]` for every result `v`, as
multisets (`eval_plugAll`). This is Moggi's let-floating law
`C[e] = let x ⇐ e in C[x]` for the nondeterminism monad of finite multisets.
Here it is proved, for both `rustEqualToInput` and `evaluatedValues`, for
arguments `e` whose results all have the erasure of `e` (nondeterministic
stuck calls such as `(fr a)`, and values): then `C[e]` and every `C[v]` are
the same term up to marks, so each level marks the same answers.

For an argument that reduces, the Rust rule breaks the law: in `C[e]` a
stuck call whose argument was reduced is not the evaluated term and is
returned unmarked, while in `C[v]` it is. `(g (fr (h)))` has 4 answers and its
unfolding `(wrap (fr (h)))` has 2 (`Probes.rust_violates_alias`). Under
`evaluatedValues` the stuck call is marked, and the law holds for every
code-free argument (`eval_plugAll_codeFree`).

Consequence (`unfold_preserves_eval`, and `unfold_preserves_eval_codeFree` for
the repaired rule): if `g` is defined by one equation `(g $x) = rhs` in which
`$x` occurs once, under value positions only, then unfolding a call `(g e)`
to `rhs[$x := e]` preserves the multiset of results. The law needs
linearity: `(twice e)` and its unfolding `(pair e e)` differ, because the
unfolding chooses twice: `(twice (fr a))` has 2 answers and
`(pair (fr a) (fr a))` has 4 (`Probes.twice_fr_obs`, `Probes.pair_fr_obs`).
For the linear `pairit`, the unfolding is exact (`Probes.pairit_unfold`),
while under `reevaluate` it changes 8 answers into 4.

The statements are made in the direction that holds unconditionally: when the
context's result converges, so does the composite. In the other direction an
argument without results makes the composite empty while a divergent sibling
in the context makes `C[e]` diverge.
-/

namespace Mettapedia.Languages.MeTTa.HE.EvaluatedValues

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-! ## Multisets of combinations -/

theorem coe_flatMap {α β : Type} (l : List α) (f : α → List β) :
    ((l.flatMap f : List β) : Multiset β) = (l : Multiset α).bind fun a => (f a : Multiset β) :=
  (Multiset.coe_bind l f).symm

/-- A flat-mapped position splits the combinations. -/
theorem combos_mid_flatMap {α β : Type} (A : List (List α)) (L : List β) (f : β → List α)
    (C : List (List α)) :
    ((combos (A ++ L.flatMap f :: C) : List (List α)) : Multiset (List α)) =
      (L : Multiset β).bind fun v => (combos (A ++ f v :: C) : Multiset (List α)) := by
  induction A with
  | nil =>
    rw [List.nil_append, combos_cons, List.flatMap_assoc, coe_flatMap]
    rfl
  | cons a A ih =>
    have lhs : ((combos ((a :: A) ++ L.flatMap f :: C) : List (List α)) : Multiset (List α)) =
        (a : Multiset α).bind fun y => Multiset.map (y :: ·)
          ((L : Multiset β).bind fun v => (combos (A ++ f v :: C) : Multiset (List α))) := by
      rw [List.cons_append, combos_cons, coe_flatMap]
      refine Multiset.bind_congr fun y _ => ?_
      rw [← Multiset.map_coe, ih]
    have rhs : ∀ v, ((combos ((a :: A) ++ f v :: C) : List (List α)) : Multiset (List α)) =
        (a : Multiset α).bind fun y => Multiset.map (y :: ·)
          (combos (A ++ f v :: C) : Multiset (List α)) := by
      intro v
      rw [List.cons_append, combos_cons, coe_flatMap]
      refine Multiset.bind_congr fun y _ => ?_
      rw [← Multiset.map_coe]
    rw [lhs]
    simp only [rhs, Multiset.map_bind]
    exact Multiset.bind_bind _ _

theorem flatMap_singleton_self {α : Type} (L : List α) : L.flatMap (fun v => [v]) = L := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [ih]

theorem combos_mid_perm {α : Type} (A : List (List α)) {L L' : List α} (C : List (List α))
    (h : (L : Multiset α) = L') :
    ((combos (A ++ L :: C) : List (List α)) : Multiset (List α)) = combos (A ++ L' :: C) := by
  have h₁ := combos_mid_flatMap A L (fun v => [v]) C
  have h₂ := combos_mid_flatMap A L' (fun v => [v]) C
  rw [flatMap_singleton_self] at h₁ h₂
  rw [h₁, h₂, h]

theorem optFlatMap_eq_some_iff {α β : Type} {l : List α} {f : α → Option (List β)}
    {R : List β} :
    optFlatMap l f = some R ↔ (∀ a ∈ l, (f a).isSome) ∧ R = l.flatMap fun a => (f a).getD [] := by
  induction l generalizing R with
  | nil =>
    simp only [optFlatMap_nil, Option.some.injEq, List.flatMap_nil]
    exact ⟨fun h => ⟨by simp, h.symm⟩, fun h => h.2.symm⟩
  | cons a l ih =>
    simp only [optFlatMap_cons, List.mem_cons, forall_eq_or_imp, List.flatMap_cons]
    cases hfa : f a with
    | none => simp
    | some r =>
      cases hrest : optFlatMap l f with
      | none =>
        simp only [Option.bind_some, Option.map_none, reduceCtorEq, Option.isSome_some,
          true_and, Option.getD_some, false_iff, not_and]
        intro hall
        have := (ih (R := l.flatMap fun a => (f a).getD [])).mpr ⟨hall, rfl⟩
        rw [hrest] at this
        cases this
      | some rs =>
        obtain ⟨hall, rfl⟩ := (ih (R := rs)).mp hrest
        simp only [Option.bind_some, Option.map_some, Option.some.injEq, Option.isSome_some,
          true_and, Option.getD_some]
        exact ⟨fun h => ⟨hall, h.symm⟩, fun h => h.2.symm⟩

theorem optFlatMap_perm {α β : Type} {l₁ l₂ : List α} {f : α → Option (List β)}
    (hl : (l₁ : Multiset α) = l₂) {R₁ : List β} (h : optFlatMap l₁ f = some R₁) :
    ∃ R₂, optFlatMap l₂ f = some R₂ ∧ (R₁ : Multiset β) = R₂ := by
  obtain ⟨hall, rfl⟩ := optFlatMap_eq_some_iff.mp h
  have hmem : ∀ a, a ∈ l₁ ↔ a ∈ l₂ := fun a => by
    rw [← Multiset.mem_coe, hl, Multiset.mem_coe]
  refine ⟨l₂.flatMap fun a => (f a).getD [],
    optFlatMap_eq_some_iff.mpr ⟨fun a ha => hall a ((hmem a).mpr ha), rfl⟩, ?_⟩
  rw [coe_flatMap, coe_flatMap, hl]

/-! ## Frames -/

/-- One level of an evaluation context: `(head left… □ right…)`, unmarked. -/
structure Frame where
  head : MAtom
  left : List MAtom
  right : List MAtom

/-- Fill the hole. -/
def Frame.plug (fr : Frame) (x : MAtom) : MAtom :=
  .expr false (fr.head :: (fr.left ++ x :: fr.right))

/-- The hole is a value position of the frame's head. -/
def Frame.Strict (P : Program) (fr : Frame) : Prop :=
  ((P.paramModes fr.head).drop fr.left.length).head? ≠ some .atom

/-- Fill a context, outermost frame first. -/
def plugAll : List Frame → MAtom → MAtom
  | [], x => x
  | fr :: frs, x => fr.plug (plugAll frs x)

/-- What a frame does with the results of its hole; `mk` is applied to every
answer (the evaluator applies `markIf` of the evaluated term). -/
noncomputable def Frame.continue (rule : ReturnRule) (P : Program) (fr : Frame)
    (mk : MAtom → MAtom) (RX : List MAtom) : Option (List MAtom) :=
  (optTraverse (withModes (.value :: P.paramModes fr.head) (fr.head :: fr.left))
      fun p => (argDemand p).run (eval rule P)).bind fun Rs₁ =>
    (optTraverse (withModes ((P.paramModes fr.head).drop fr.left.length).tail fr.right)
        fun p => (argDemand p).run (eval rule P)).bind fun Rs₂ =>
      (optFlatMap (combos (Rs₁ ++ RX :: Rs₂))
          fun vs => (P.callDemand rule.marksStuck vs).run (eval rule P)).map (List.map mk)

theorem erase_plugAll_congr {x y : MAtom} (h : x.erase = y.erase) :
    ∀ C : List Frame, (plugAll C x).erase = (plugAll C y).erase
  | [] => h
  | fr :: C => by simp [plugAll, Frame.plug, erase_plugAll_congr h C]

theorem withModes_append : ∀ (ms : List ParamMode) (l₁ l₂ : List MAtom),
    withModes ms (l₁ ++ l₂) = withModes ms l₁ ++ withModes (ms.drop l₁.length) l₂
  | ms, [], l₂ => by simp [withModes]
  | [], c :: l₁, l₂ => by
    simp only [List.cons_append, withModes, withModes_append [] l₁ l₂, List.drop_nil]
  | m :: ms, c :: l₁, l₂ => by
    simp only [List.cons_append, withModes, withModes_append ms l₁ l₂, List.length_cons,
      List.drop_succ_cons]

theorem withModes_hole {ms : List ParamMode} (h : ms.head? ≠ some .atom) (x : MAtom)
    (r : List MAtom) : withModes ms (x :: r) = (.value, x) :: withModes ms.tail r := by
  cases ms with
  | nil => rfl
  | cons m ms =>
    cases m with
    | value => rfl
    | atom => simp at h

theorem optTraverse_append {α β : Type} (l₁ l₂ : List α) (f : α → Option β) :
    optTraverse (l₁ ++ l₂) f =
      (optTraverse l₁ f).bind fun a => (optTraverse l₂ f).map fun b => a ++ b := by
  induction l₁ with
  | nil => cases h : optTraverse l₂ f <;> simp [h]
  | cons a l₁ ih =>
    simp only [List.cons_append, optTraverse_cons, ih]
    cases f a with
    | none => rfl
    | some b =>
      cases optTraverse l₁ f with
      | none => rfl
      | some bs => cases optTraverse l₂ f <;> rfl

/-- **A frame evaluates its hole first.** -/
theorem frame_eval (rule : ReturnRule) (P : Program) {fr : Frame} (hfr : fr.Strict P)
    (X : MAtom) :
    eval rule P (fr.plug X) =
      (eval rule P X).bind (fr.continue rule P (MAtom.markIf (fr.plug X).erase)) := by
  rw [Frame.plug, eval_expr_open rule P _ (by simp)]
  simp only [Program.elementModes, withModes]
  rw [withModes_append, withModes_hole hfr]
  unfold Frame.continue
  simp only [optTraverse_cons, optTraverse_append, withModes, argDemand_value_run]
  cases eval rule P fr.head <;>
    cases optTraverse (withModes (P.paramModes fr.head) fr.left)
      (fun p => (argDemand p).run (eval rule P)) <;>
    cases eval rule P X <;>
    cases optTraverse (withModes (List.drop fr.left.length (P.paramModes fr.head)).tail fr.right)
      (fun p => (argDemand p).run (eval rule P)) <;>
    simp

theorem Frame.continue_perm {rule : ReturnRule} {P : Program} (fr : Frame) (mk : MAtom → MAtom)
    {L L' : List MAtom} (hL : (L : Multiset MAtom) = L') {R : List MAtom}
    (h : fr.continue rule P mk L = some R) :
    ∃ R', fr.continue rule P mk L' = some R' ∧ (R : Multiset MAtom) = R' := by
  unfold Frame.continue at h ⊢
  obtain ⟨Rs₁, h₁, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨Rs₂, h₂, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨R₀, h₀, rfl⟩ := Option.map_eq_some_iff.mp h
  have hc := combos_mid_perm Rs₁ Rs₂ hL
  obtain ⟨R₁, hR₁, hR₀₁⟩ := optFlatMap_perm hc h₀
  refine ⟨R₁.map mk, ?_, ?_⟩
  · rw [h₁, Option.bind_some, h₂, Option.bind_some, hR₁]
    rfl
  · rw [← Multiset.map_coe, ← Multiset.map_coe, hR₀₁]

theorem Frame.continue_flatMap {rule : ReturnRule} {P : Program} (fr : Frame)
    (mk : MAtom → MAtom) (L : List MAtom) (g : MAtom → List MAtom) {R : List MAtom}
    (h : fr.continue rule P mk (L.flatMap g) = some R) :
    ∃ R', optFlatMap L (fun v => fr.continue rule P mk (g v)) = some R' ∧
      (R : Multiset MAtom) = R' := by
  unfold Frame.continue at h
  obtain ⟨Rs₁, h₁, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨Rs₂, h₂, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨R₀, h₀, rfl⟩ := Option.map_eq_some_iff.mp h
  have hc : ((combos (Rs₁ ++ L.flatMap g :: Rs₂) : List (List MAtom)) : Multiset (List MAtom)) =
      (L.flatMap fun v => combos (Rs₁ ++ g v :: Rs₂) : List (List MAtom)) := by
    rw [combos_mid_flatMap, coe_flatMap]
  obtain ⟨R₁, hR₁, hR₀₁⟩ := optFlatMap_perm hc h₀
  rw [optFlatMap_flatMap] at hR₁
  have hcont : (fun v => fr.continue rule P mk (g v)) = fun v =>
      (optFlatMap (combos (Rs₁ ++ g v :: Rs₂))
        fun vs => (P.callDemand rule.marksStuck vs).run (eval rule P)).map (List.map mk) := by
    funext v
    simp only [Frame.continue]
    rw [h₁, Option.bind_some, h₂, Option.bind_some]
  refine ⟨R₁.map mk, ?_, ?_⟩
  · rw [hcont, ← optFlatMap_mapResults, hR₁]
    rfl
  · rw [← Multiset.map_coe, ← Multiset.map_coe, hR₀₁]

/-! ## The context law -/

/-- **Evaluation contexts.** Under `evaluatedValues`, for an argument whose
results all have its own erasure, when `C[e]` converges its results are, as a
multiset, those of `C[v]` over the results `v` of `e`. -/
theorem eval_plugAll {rule : ReturnRule} (hmark : rule.honorsMark = true) (P : Program) :
    ∀ (C : List Frame), (∀ fr ∈ C, fr.Strict P) → ∀ (e : MAtom),
      (∀ R, eval rule P e = some R → ∀ v ∈ R, v.erase = e.erase) →
      ∀ {R : List MAtom}, eval rule P (plugAll C e) = some R →
      ∃ R', kbind (eval rule P e) (fun v => eval rule P (plugAll C v)) =
        some R' ∧ (R : Multiset MAtom) = R' := by
  intro C
  induction C with
  | nil =>
    intro _ e hself R h
    refine ⟨R, ?_, rfl⟩
    simp only [plugAll] at h ⊢
    rw [← h]
    exact eval_kleisli_idempotent hmark P e (ValueResults.of_self hself)
  | cons fr C ih =>
    intro hC e hself R h
    have hfr := hC fr List.mem_cons_self
    simp only [plugAll] at h
    rw [frame_eval _ P hfr] at h
    obtain ⟨RX, hX, hcont⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨R'', hR'', hXR''⟩ := ih (fun f hf => hC f (List.mem_cons_of_mem _ hf)) e hself hX
    obtain ⟨Re, he, hRe⟩ := Option.bind_eq_some_iff.mp hR''
    obtain ⟨hall, rfl⟩ := optFlatMap_eq_some_iff.mp hRe
    obtain ⟨R₂, hR₂, hRR₂⟩ := fr.continue_perm _ hXR'' hcont
    obtain ⟨R₃, hR₃, hR₂₃⟩ := fr.continue_flatMap _ Re _ hR₂
    refine ⟨R₃, ?_, hRR₂.trans hR₂₃⟩
    simp only [kbind, he, Option.bind_some, plugAll]
    rw [← hR₃]
    apply optFlatMap_congr
    intro v hv
    rw [frame_eval _ P hfr]
    have hplug : (fr.plug (plugAll C v)).erase = (fr.plug (plugAll C e)).erase :=
      erase_plugAll_congr (hself Re he v hv) (fr :: C)
    obtain ⟨Rv, hRv⟩ := Option.isSome_iff_exists.mp (hall v hv)
    simp [hRv, hplug]

/-! ## Linear unfolding -/

/-- No sibling of the context mentions `x`. -/
def Frame.Avoids (x : String) (fr : Frame) : Prop :=
  ∀ c ∈ fr.head :: (fr.left ++ fr.right), c.touched [(x, .var x)] = false

theorem touched_single (x : String) (v w : MAtom) :
    ∀ c : MAtom, c.touched [(x, v)] = c.touched [(x, w)] := by
  intro c
  induction c using MAtom.induction with
  | var y =>
    simp only [MAtom.touched_var, Subst.lookup_cons, Subst.lookup_nil]
    split <;> rfl
  | expr m cs ih =>
    simp only [MAtom.touched_expr]
    induction cs with
    | nil => rfl
    | cons c cs ihcs =>
      simp [ih c List.mem_cons_self, ihcs fun d hd => ih d (List.mem_cons_of_mem _ hd)]
  | _ => rfl

theorem plugAll_subst (x : String) (v : MAtom) :
    ∀ (C : List Frame), (∀ fr ∈ C, fr.Avoids x) →
      (plugAll C (.var x)).subst [(x, v)] = plugAll C v := by
  intro C
  induction C with
  | nil => intro _; simp [plugAll, Subst.lookup_cons]
  | cons fr C ih =>
    intro hC
    have hav := hC fr List.mem_cons_self
    have hsib : ∀ c ∈ fr.head :: (fr.left ++ fr.right), c.subst [(x, v)] = c := fun c hc =>
      MAtom.subst_of_not_touched _ c (by rw [touched_single x v (.var x)]; exact hav c hc)
    simp only [plugAll, Frame.plug, MAtom.subst_expr, Bool.false_and, List.map_cons,
      List.map_append]
    have hl : fr.left.map (MAtom.subst [(x, v)]) = fr.left := by
      conv => rhs; rw [← List.map_id fr.left]
      exact List.map_congr_left fun c hc =>
        hsib c (List.mem_cons_of_mem _ (List.mem_append_left _ hc))
    have hr : fr.right.map (MAtom.subst [(x, v)]) = fr.right := by
      conv => rhs; rw [← List.map_id fr.right]
      exact List.map_congr_left fun c hc =>
        hsib c (List.mem_cons_of_mem _ (List.mem_append_right _ hc))
    rw [ih fun f hf => hC f (List.mem_cons_of_mem _ hf), hsib fr.head List.mem_cons_self, hl, hr]

/-- **Call-time choice for one-parameter definitions.** If `g` is defined by
the single equation `(g $x) = rhs` with `rhs = C[$x]` for an evaluation context
`C` not mentioning `$x` elsewhere, then `(g e)` evaluates `e` once and runs
the body on each of its results; answers equal to the call `(g e)` itself are
marked. -/
theorem eval_unfold_call (rule : ReturnRule) {P : Program} (hP : P.SymbolHeaded) {g x : String}
    {rhs : Atom}
    (C : List Frame) (hne : C ≠ []) (hav : ∀ fr ∈ C, fr.Avoids x)
    (hrhs : code rhs = plugAll C (.var x)) (hg : Prim.ofName g = none)
    (hdg : P.decl? g = none) (hdef : P.defn g = [(.expression [.symbol g, .var x], rhs)])
    (e : MAtom) :
    eval rule P (.expr false [.symbol g, e]) =
      kbind (eval rule P e) fun v =>
        (eval rule P (plugAll C v)).map
          (List.map (MAtom.markIf (MAtom.expr false [.symbol g, e]).erase)) := by
  rw [eval_call_untyped rule P [e] (by simp) hg hdg]
  simp only [optTraverse_cons, optTraverse_nil, Option.map_some]
  cases he : eval rule P e with
  | none => rfl
  | some Re =>
    simp only [Option.bind_some, combos_single, optFlatMap_map, kbind]
    rw [optFlatMap_mapResults]
    apply optFlatMap_congr
    intro v _
    have hrep : P.replies (.expr false [.symbol g, v]) = [plugAll C v] := by
      rw [replies_eq_defn hP, hdef]
      simp only [List.filterMap_cons, List.filterMap_nil, matchAtom, matchList, ↓reduceIte,
        Subst.lookup_nil, Option.map_some, hrhs]
      rw [plugAll_subst x v C hav]
    obtain ⟨fr, C', rfl⟩ := List.exists_cons_of_ne_nil hne
    have hne' : ¬ (plugAll (fr :: C') v).erase = Atom.notReducible := by
      simp [plugAll, Frame.plug, Atom.notReducible]
    simp only [Program.queryDemand, hrep, Program.callResultMode, Program.resultMode, hdg,
      returnDemand, hne', ↓reduceIte, Demand.run_forEach, optFlatMap_cons, optFlatMap_nil,
      Demand.run_need, Demand.run_done]
    cases eval rule P (plugAll (fr :: C') v) <;> simp

/-- **Linear unfolding preserves evaluation.** Under the hypotheses of
`eval_unfold_call`, for an argument whose results all have its own erasure,
if the unfolded body `rhs[$x := e]` converges, then the call `(g e)`
converges to the same multiset of observed results. -/
theorem unfold_preserves_eval {rule : ReturnRule} (hmark : rule.honorsMark = true) {P : Program}
    (hP : P.SymbolHeaded) {g x : String} {rhs : Atom}
    (C : List Frame) (hC : ∀ fr ∈ C, fr.Strict P) (hne : C ≠ []) (hav : ∀ fr ∈ C, fr.Avoids x)
    (hrhs : code rhs = plugAll C (.var x)) (hg : Prim.ofName g = none)
    (hdg : P.decl? g = none) (hdef : P.defn g = [(.expression [.symbol g, .var x], rhs)])
    (e : MAtom) (hself : ∀ R, eval rule P e = some R → ∀ v ∈ R, v.erase = e.erase)
    {R : List MAtom} (h : eval rule P ((code rhs).subst [(x, e)]) = some R) :
    ∃ R', eval rule P (.expr false [.symbol g, e]) = some R' ∧
      ((R.map MAtom.erase : List Atom) : Multiset Atom) = R'.map MAtom.erase := by
  rw [hrhs, plugAll_subst x e C hav] at h
  obtain ⟨R'', hR'', hRR''⟩ := eval_plugAll hmark P C hC e hself h
  refine ⟨R''.map (MAtom.markIf (MAtom.expr false [.symbol g, e]).erase), ?_, ?_⟩
  · rw [eval_unfold_call rule hP C hne hav hrhs hg hdg hdef e]
    obtain ⟨Re, he, hRe⟩ := Option.bind_eq_some_iff.mp hR''
    simp only [kbind, he, Option.bind_some] at hRe ⊢
    rw [← optFlatMap_mapResults, hRe]
    rfl
  · rw [List.map_map]
    simp only [Function.comp_def, MAtom.erase_markIf]
    rw [← Multiset.map_coe, ← Multiset.map_coe, hRR'']

end Mettapedia.Languages.MeTTa.HE.EvaluatedValues

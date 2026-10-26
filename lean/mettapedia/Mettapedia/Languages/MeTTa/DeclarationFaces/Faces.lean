import Mettapedia.Languages.MeTTa.DeclarationFaces.Confluence

/-!
# The operational and extensional faces of an admitted declaration, and their agreement

**Operational face.** MeTTa evaluates a term by steps. The order is not part of the meaning: a
`Strategy` is any choice among steps that leaves no reducible term unreduced. Two instances:
innermost steps (arguments first, the draft's applicative order, `innermostStrategy`) and
outermost steps (`outermostStrategy`). `evalTm` is the executable innermost evaluator with MeTTa's
results: every argument's results are combined, every matching equation contributes, a call that
no equation matches is kept as inert data, and the results form a list read as a multiset.

**Extensional face.** The defined symbols denote functions on normal forms (`Admitted.model`), a
term is read in that model (`interp`), and each sort denotes its data (`Signature.Denotes`).

For an admitted declaration and a closed sorted term:
* every strategy terminates, and its only outcome is the normal form (`Admitted.strategy_outcome`);
* the evaluator returns exactly one result, the normal form (`Admitted.evalTm_closed`);
* the normal form is constructor data of the term's sort (`Admitted.normalForm_value`);
* every defined function is total on the data of its argument sorts at every instance of its
  scheme (`Admitted.model_total`), every equation holds in the model (`Admitted.model_equation`),
  and the model is the only interpretation of the defined symbols on normal forms in which every
  equation holds, on data of the declared sorts (`Admitted.model_unique`);
* the term read in the model is its normal form (`Admitted.interp_eq_normalForm`).

The extensional face is thus fixed by the equations alone: it is their unique solution on the data
of the declared sorts, independent of any evaluation order.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.DeclarationFaces

open Tm Relation
open Mettapedia.Logic.Relation (IsNormal exists_normalForm_of_acc accessible_transitiveClosure)

universe u

variable {S : Type u} {P : Program S}

/-! ## Strategies -/

/-- **An evaluation strategy**: a choice among steps that leaves no reducible term unreduced. -/
structure Strategy (P : Program S) where
  step : Tm S → Tm S → Prop
  sound : ∀ {s t}, step s t → Step P s t
  complete : ∀ {s t}, Step P s t → ∃ t', step s t'

/-- **Innermost steps**: a call is reduced only when its arguments take no step. -/
inductive InnermostStep (P : Program S) : Tm S → Tm S → Prop where
  | root {f : S} {args : List (Tm S)} {t : Tm S} :
      (∀ a ∈ args, IsNormal (Step P) a) → RootStep P (.app f args) t → InnermostStep P (.app f args) t
  | arg (f : S) (args : List (Tm S)) (i : Nat) (lt : i < args.length) {t : Tm S} :
      InnermostStep P args[i] t → InnermostStep P (.app f args) (.app f (args.set i t))

/-- **Outermost steps**: an argument is reduced only when the call itself takes no root step. -/
inductive OutermostStep (P : Program S) : Tm S → Tm S → Prop where
  | root {s t : Tm S} : RootStep P s t → OutermostStep P s t
  | arg (f : S) (args : List (Tm S)) (i : Nat) (lt : i < args.length) {t : Tm S} :
      (∀ u, ¬ RootStep P (.app f args) u) → OutermostStep P args[i] t →
      OutermostStep P (.app f args) (.app f (args.set i t))

theorem InnermostStep.step {s t : Tm S} (h : InnermostStep P s t) : Step P s t := by
  induction h with
  | root _ root => exact .root root
  | arg f args i lt _ ih => exact .arg f args i lt ih

theorem OutermostStep.step {s t : Tm S} (h : OutermostStep P s t) : Step P s t := by
  induction h with
  | root root => exact .root root
  | arg f args i lt _ _ ih => exact .arg f args i lt ih

theorem innermost_complete (headed : P.Headed) :
    ∀ {s t : Tm S}, Step P s t → ∃ t', InnermostStep P s t' := by
  intro s
  induction s using Tm.induction' with
  | var x => intro t step; exact absurd step (Step.not_var headed)
  | app f args ih =>
      intro t step
      by_cases normalArgs : ∀ a ∈ args, IsNormal (Step P) a
      · cases step with
        | root root => exact ⟨t, .root normalArgs root⟩
        | arg _ _ i lt inner => exact absurd inner (normalArgs _ (List.getElem_mem lt) _)
      · push Not at normalArgs
        obtain ⟨a, aMember, notNormal⟩ := normalArgs
        simp only [IsNormal, not_forall, not_not] at notNormal
        obtain ⟨b, stepA⟩ := notNormal
        obtain ⟨i, lt, rfl⟩ := List.getElem_of_mem aMember
        obtain ⟨b', inner⟩ := ih _ aMember stepA
        exact ⟨_, .arg f args i lt inner⟩

theorem outermost_complete (headed : P.Headed) :
    ∀ {s t : Tm S}, Step P s t → ∃ t', OutermostStep P s t' := by
  intro s
  induction s using Tm.induction' with
  | var x => intro t step; exact absurd step (Step.not_var headed)
  | app f args ih =>
      intro t step
      by_cases rootRedex : ∃ u, RootStep P (.app f args) u
      · obtain ⟨u, root⟩ := rootRedex
        exact ⟨u, .root root⟩
      · push Not at rootRedex
        cases step with
        | root root => exact absurd root (rootRedex t)
        | arg _ _ i lt inner =>
            obtain ⟨b', outer⟩ := ih _ (List.getElem_mem lt) inner
            exact ⟨_, .arg f args i lt rootRedex outer⟩

/-- The innermost strategy, the draft's applicative order. -/
def innermostStrategy (headed : P.Headed) : Strategy P where
  step := InnermostStep P
  sound := InnermostStep.step
  complete := innermost_complete headed

/-- The outermost strategy. -/
def outermostStrategy (headed : P.Headed) : Strategy P where
  step := OutermostStep P
  sound := OutermostStep.step
  complete := outermost_complete headed

/-! ## Every strategy agrees -/

namespace Admitted

variable [DecidableEq S] {sig : Signature S}

/-- **Every strategy terminates** at every term of an admitted declaration. -/
theorem strategy_terminates (adm : Admitted sig P) (r : Strategy P) (t : Tm S) :
    Acc (fun target source => r.step source target) t :=
  Subrelation.accessible (fun h => r.sound h) (adm.stronglyNormalizing t)

/-- **Every strategy has exactly one outcome, the normal form.** -/
theorem strategy_outcome (adm : Admitted sig P) (r : Strategy P) (t u : Tm S) :
    (ReflTransGen r.step t u ∧ IsNormal r.step u) ↔ u = adm.normalForm t := by
  have toSteps : ∀ {a b}, ReflTransGen r.step a b → ReflTransGen (Step P) a b := by
    intro a b h
    induction h with
    | refl => exact .refl
    | tail _ last ih => exact ih.tail (r.sound last)
  have normalOf : ∀ {a}, IsNormal r.step a → IsNormal (Step P) a := fun normal b step => by
    obtain ⟨b', h⟩ := r.complete step
    exact normal b' h
  constructor
  · rintro ⟨steps, normal⟩
    exact adm.normalForm_unique ⟨toSteps steps, normalOf normal⟩
  · rintro rfl
    obtain ⟨n, steps, normal⟩ := exists_normalForm_of_acc (adm.strategy_terminates r t)
    rw [← adm.normalForm_unique ⟨toSteps steps, normalOf normal⟩]
    exact ⟨steps, normal⟩

end Admitted

/-! ## The executable evaluator -/

/-- Apply a partial function to every element; fail when it fails on one. -/
def mapOpt {α β : Type*} (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | a :: as => (f a).bind fun b => (mapOpt f as).map (b :: ·)

theorem mapOpt_spec {α β : Type*} {f : α → Option β} :
    ∀ {as : List α} {bs : List β}, mapOpt f as = some bs → Pointwise (fun a b => f a = some b) as bs
  | [], bs, h => by simp only [mapOpt, Option.some.injEq] at h; subst h; exact Pointwise.nil
  | a :: as, bs, h => by
      simp only [mapOpt, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rest, hrest, rfl⟩ := h
      exact Pointwise.cons_iff.mpr ⟨hb, mapOpt_spec hrest⟩

theorem mapOpt_of_spec {α β : Type*} {f : α → Option β} :
    ∀ {as : List α} {bs : List β}, Pointwise (fun a b => f a = some b) as bs → mapOpt f as = some bs
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
      obtain ⟨hb, hrest⟩ := Pointwise.cons_iff.mp h
      simp [mapOpt, hb, mapOpt_of_spec hrest]
  | [], _ :: _, h => by simp [Pointwise] at h
  | _ :: _, [], h => by simp [Pointwise] at h

/-- Every choice of one element from each list. -/
def choices {α : Type*} : List (List α) → List (List α)
  | [] => [[]]
  | rs :: rss => rs.flatMap fun r => (choices rss).map (r :: ·)

theorem mem_choices {α : Type*} : ∀ {rss : List (List α)} {vs : List α}, vs ∈ choices rss →
    Pointwise (fun rs v => v ∈ rs) rss vs
  | [], vs, h => by simp only [choices, List.mem_singleton] at h; subst h; exact Pointwise.nil
  | rs :: rss, vs, h => by
      simp only [choices, List.mem_flatMap, List.mem_map] at h
      obtain ⟨r, hr, rest, hrest, rfl⟩ := h
      exact Pointwise.cons_iff.mpr ⟨hr, mem_choices hrest⟩

theorem choices_singletons {α : Type*} : ∀ (vs : List α), choices (vs.map fun v => [v]) = [vs]
  | [] => rfl
  | v :: vs => by simp [choices, choices_singletons vs]

variable [DecidableEq S]

/-- **The MeTTa evaluator**, innermost, with fuel: evaluate every argument; for every choice of
argument results, every equation whose left side matches contributes the evaluation of its
instantiated right side; a call that no equation matches stays as inert data. `none` means the
fuel ran out. -/
def evalTm (P : Program S) : Nat → Tm S → Option (List (Tm S))
  | 0, _ => none
  | _ + 1, .var x => some [.var x]
  | n + 1, .app f args =>
      (mapOpt (evalTm P n) args).bind fun results =>
        (mapOpt (fun vs =>
          match rootResults P (.app f vs) with
          | [] => some [.app f vs]
          | rs => (mapOpt (evalTm P n) rs).map List.flatten) (choices results)).map List.flatten

/-- What the evaluator's soundness uses. -/
structure Executable (P : Program S) : Prop where
  headed : P.Headed
  leftLinear : P.LeftLinear
  rightBound : P.RightBound

theorem mem_flatten_of_mapOpt {α β : Type*} {f : α → Option (List β)} {as : List α}
    {bss : List (List β)} (h : mapOpt f as = some bss) {b : β} (hb : b ∈ bss.flatten) :
    ∃ a ∈ as, ∃ bs, f a = some bs ∧ b ∈ bs := by
  obtain ⟨len, each⟩ := mapOpt_spec h
  obtain ⟨bs, hbs, hb⟩ := List.mem_flatten.mp hb
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hbs
  exact ⟨as[i]'(len ▸ hi), List.getElem_mem _, bss[i], each i (len ▸ hi) hi, hb⟩

/-- **The evaluator is sound**: every result is a normal form reached by steps. -/
theorem evalTm_sound (exec : Executable P) : ∀ (n : Nat) {t : Tm S} {rs : List (Tm S)},
    evalTm P n t = some rs → ∀ r ∈ rs, ReflTransGen (Step P) t r ∧ IsNormal (Step P) r
  | 0, t, rs, h, _, _ => by simp [evalTm] at h
  | n + 1, .var x, rs, h, r, hr => by
      simp only [evalTm, Option.some.injEq] at h
      subst h
      simp only [List.mem_singleton] at hr
      subst hr
      exact ⟨.refl, var_normal exec.headed x⟩
  | n + 1, .app f args, rs, h, r, hr => by
      simp only [evalTm, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨results, hresults, bss, hbss, rfl⟩ := h
      obtain ⟨vs, hvs, bs, hbs, hr⟩ := mem_flatten_of_mapOpt hbss hr
      obtain ⟨len, each⟩ := mapOpt_spec hresults
      obtain ⟨len', inside⟩ := mem_choices hvs
      have argSteps : ∀ i (hi : i < args.length) (hj : i < vs.length),
          ReflTransGen (Step P) args[i] vs[i] ∧ IsNormal (Step P) vs[i] := by
        intro i hi hj
        exact evalTm_sound exec n (each i hi (len ▸ hi)) _ (inside i (len ▸ hi) hj)
      have toCall : ReflTransGen (Step P) (.app f args) (.app f vs) :=
        steps_args f args vs (len.trans len') fun i hi hj => (argSteps i hi hj).1
      cases hrs : rootResults P (.app f vs) with
      | nil =>
          simp only [hrs, Option.some.injEq] at hbs
          subst hbs
          simp only [List.mem_singleton] at hr
          subst hr
          refine ⟨toCall, fun target step => ?_⟩
          cases step with
          | root root =>
              have := (mem_rootResults_iff exec.leftLinear exec.rightBound).mpr root
              rw [hrs] at this
              cases this
          | arg _ _ i lt inner => exact (argSteps i (by omega) lt).2 _ inner
      | cons r0 rs0 =>
          simp only [hrs, Option.map_eq_some_iff] at hbs
          obtain ⟨cs, hcs, rfl⟩ := hbs
          obtain ⟨r', hr', ds, hds, hr⟩ := mem_flatten_of_mapOpt hcs hr
          have root : RootStep P (.app f vs) r' :=
            (mem_rootResults_iff exec.leftLinear exec.rightBound).mp (by rw [hrs]; exact hr')
          obtain ⟨steps, normal⟩ := evalTm_sound exec n hds r hr
          exact ⟨toCall.trans (ReflTransGen.head (Step.root root) steps), normal⟩

/-- An evaluation that finishes finishes the same way with more fuel. -/
theorem evalTm_succ : ∀ (n : Nat) {t : Tm S} {rs : List (Tm S)}, evalTm P n t = some rs →
    evalTm P (n + 1) t = some rs
  | 0, t, rs, h => by simp [evalTm] at h
  | n + 1, .var x, rs, h => by simpa [evalTm] using h
  | n + 1, .app f args, rs, h => by
      have lift : ∀ {as : List (Tm S)} {bs : List (List (Tm S))}, mapOpt (evalTm P n) as = some bs →
          mapOpt (evalTm P (n + 1)) as = some bs := fun h' =>
        mapOpt_of_spec ⟨(mapOpt_spec h').1, fun i hi hj => evalTm_succ n ((mapOpt_spec h').2 i hi hj)⟩
      simp only [evalTm, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h ⊢
      obtain ⟨results, hresults, bss, hbss, rfl⟩ := h
      refine ⟨results, lift hresults, bss, ?_, rfl⟩
      apply mapOpt_of_spec
      refine ⟨(mapOpt_spec hbss).1, fun i hi hj => ?_⟩
      have := (mapOpt_spec hbss).2 i hi hj
      simp only at this ⊢
      cases hrs : rootResults P (.app f (choices results)[i]) with
      | nil => simp only [hrs] at this ⊢; exact this
      | cons r rs' =>
          simp only [hrs, Option.map_eq_some_iff] at this ⊢
          obtain ⟨cs, hcs, heq⟩ := this
          exact ⟨cs, lift hcs, heq⟩

theorem evalTm_mono {n m : Nat} (le : n ≤ m) {t : Tm S} {rs : List (Tm S)}
    (h : evalTm P n t = some rs) : evalTm P m t = some rs := by
  induction le with
  | refl => exact h
  | step _ ih => exact evalTm_succ _ ih

omit [DecidableEq S] in
/-- Finitely many evaluations that each finish with some fuel all finish with one fuel. -/
theorem common_fuel {α : Type*} (g : Nat → α → Option (List (Tm S)))
    (mono : ∀ {n m} {a : α} {rs}, n ≤ m → g n a = some rs → g m a = some rs) :
    ∀ (as : List α), (∀ a ∈ as, ∃ n, (g n a).isSome) → ∃ N, ∀ a ∈ as, (g N a).isSome
  | [], _ => ⟨0, by simp⟩
  | a :: as, h => by
      obtain ⟨n, hn⟩ := h a List.mem_cons_self
      obtain ⟨N, hN⟩ := common_fuel g mono as fun b hb => h b (List.mem_cons_of_mem a hb)
      refine ⟨max n N, fun b hb => ?_⟩
      rcases List.mem_cons.mp hb with rfl | later
      · obtain ⟨rs, hrs⟩ := Option.isSome_iff_exists.mp hn
        simp [mono (Nat.le_max_left n N) hrs]
      · obtain ⟨rs, hrs⟩ := Option.isSome_iff_exists.mp (hN b later)
        simp [mono (Nat.le_max_right n N) hrs]

theorem mapOpt_isSome {α β : Type*} {f : α → Option β} :
    ∀ {as : List α}, (∀ a ∈ as, (f a).isSome) → (mapOpt f as).isSome
  | [], _ => rfl
  | a :: as, h => by
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h a List.mem_cons_self)
      obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.mp
        (mapOpt_isSome (as := as) fun c hc => h c (List.mem_cons_of_mem a hc))
      simp [mapOpt, hb, hbs]

/-- **The evaluator finishes** on every term from which steps and parts terminate. -/
theorem evalTm_terminates (exec : Executable P) {t : Tm S}
    (acc : Acc (TransGen (Below P)) t) : ∃ n, (evalTm P n t).isSome := by
  induction acc with
  | intro t _ ih =>
  cases t with
  | var x => exact ⟨1, by simp [evalTm]⟩
  | app f args =>
      have argsFuel : ∃ N, ∀ a ∈ args, (evalTm P N a).isSome :=
        common_fuel (evalTm P) (fun le h => evalTm_mono le h) args
          fun a ha => ih a (.single (Or.inr (Sub.arg f ha)))
      obtain ⟨N₁, hN₁⟩ := argsFuel
      obtain ⟨results, hresults⟩ := Option.isSome_iff_exists.mp (mapOpt_isSome hN₁)
      let calls := (choices results).flatMap fun vs => rootResults P (.app f vs)
      have callsFuel : ∃ N, ∀ r ∈ calls, (evalTm P N r).isSome := by
        apply common_fuel (evalTm P) (fun le h => evalTm_mono le h)
        intro r hr
        simp only [calls, List.mem_flatMap] at hr
        obtain ⟨vs, hvs, hr⟩ := hr
        apply ih r
        obtain ⟨len, each⟩ := mapOpt_spec hresults
        obtain ⟨len', inside⟩ := mem_choices hvs
        have toCall : ReflTransGen (Step P) (.app f args) (.app f vs) :=
          steps_args f args vs (len.trans len') fun i hi hj =>
            (evalTm_sound exec N₁ (each i hi (len ▸ hi)) _ (inside i (len ▸ hi) hj)).1
        have root := (mem_rootResults_iff exec.leftLinear exec.rightBound).mp hr
        have chain : TransGen (Step P) (.app f args) r :=
          TransGen.tail' toCall (Step.root root)
        have : ∀ {a b}, TransGen (Step P) a b → TransGen (Below P) b a := by
          intro a b h
          induction h with
          | single step => exact .single (Or.inl step)
          | tail _ step ih' => exact TransGen.head (Or.inl step) ih'
        exact this chain
      obtain ⟨N₂, hN₂⟩ := callsFuel
      refine ⟨max N₁ N₂ + 1, ?_⟩
      have argsAt : mapOpt (evalTm P (max N₁ N₂)) args = some results := by
        apply mapOpt_of_spec
        obtain ⟨len, each⟩ := mapOpt_spec hresults
        exact ⟨len, fun i hi hj => evalTm_mono (Nat.le_max_left _ _) (each i hi hj)⟩
      simp only [evalTm, argsAt, Option.bind_some, Option.isSome_map]
      apply mapOpt_isSome
      intro vs hvs
      cases hrs : rootResults P (.app f vs) with
      | nil => simp
      | cons r0 rs0 =>
          simp only [Option.isSome_map]
          apply mapOpt_isSome
          intro r hr
          have member : r ∈ calls := by
            simp only [calls, List.mem_flatMap]
            exact ⟨vs, hvs, by rw [hrs]; exact hr⟩
          obtain ⟨out, hout⟩ := Option.isSome_iff_exists.mp (hN₂ r member)
          simp [evalTm_mono (Nat.le_max_right N₁ N₂) hout]

/-! ## One result -/

/-- No equation of a program matches the term. -/
theorem rootResults_eq_nil {P : Program S} {t : Tm S}
    (none' : ∀ e ∈ P, matchTm e.lhs t = none) : rootResults P t = [] := by
  simp only [rootResults, List.filterMap_eq_nil_iff, Option.map_eq_none_iff]
  exact none'

/-- **A call has at most one result** in a linear, non-overlapping program. -/
theorem rootResults_length_le_one (linear : P.LeftLinear) (nonOverlap : P.NonOverlapping)
    (t : Tm S) : (rootResults P t).length ≤ 1 := by
  induction P with
  | nil => simp [rootResults]
  | cons e rest ih =>
      have linearRest : Program.LeftLinear rest := fun e' h => linear e' (List.mem_cons_of_mem e h)
      obtain ⟨headApart, restApart⟩ := List.pairwise_cons.mp nonOverlap
      cases hm : matchTm e.lhs t with
      | none =>
          have : rootResults (e :: rest) t = rootResults rest t := by
            simp [rootResults, hm]
          rw [this]
          exact ih linearRest restApart
      | some bindings =>
          obtain ⟨keys, inst⟩ := matchTm_sound e.lhs t bindings hm
          have instance' := inst _ (agrees_lookup (by rw [keys]; exact linear e List.mem_cons_self))
          have restNil : rootResults rest t = [] := by
            apply rootResults_eq_nil
            intro e' he'
            cases hm' : matchTm e'.lhs t with
            | none => rfl
            | some bindings' =>
                obtain ⟨keys', inst'⟩ := matchTm_sound e'.lhs t bindings' hm'
                have instance'' := inst' _ (agrees_lookup (by rw [keys']; exact linearRest e' he'))
                exact absurd (instance'.trans instance''.symm) (headApart e' he' _ _)
          have : rootResults (e :: rest) t = [e.rhs.subst (lookup bindings)] := by
            simp only [rootResults] at restNil ⊢
            simp [hm, restNil]
          rw [this]; simp

/-- **The evaluator returns one result** for a linear, non-overlapping program. -/
theorem evalTm_singleton (linear : P.LeftLinear) (nonOverlap : P.NonOverlapping) :
    ∀ (n : Nat) {t : Tm S} {rs : List (Tm S)}, evalTm P n t = some rs → rs.length = 1
  | 0, t, rs, h => by simp [evalTm] at h
  | n + 1, .var x, rs, h => by simp only [evalTm, Option.some.injEq] at h; subst h; rfl
  | n + 1, .app f args, rs, h => by
      simp only [evalTm, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨results, hresults, bss, hbss, rfl⟩ := h
      obtain ⟨len, each⟩ := mapOpt_spec hresults
      have singletons : ∀ i (hi : i < results.length), ∃ v, results[i] = [v] := by
        intro i hi
        have := evalTm_singleton linear nonOverlap n (each i (len ▸ hi) hi)
        exact List.length_eq_one_iff.mp this
      choose vOf hvOf using singletons
      let vs := (List.finRange results.length).map fun i => vOf i.1 i.2
      have hres : results = vs.map fun v => [v] := by
        apply List.ext_getElem (by simp [vs])
        intro i h₁ h₂
        simp [vs, hvOf i h₁]
      rw [hres, choices_singletons] at hbss
      obtain ⟨blen, beach⟩ := mapOpt_spec hbss
      have one : bss.length = 1 := by simpa using blen.symm
      obtain ⟨bs, rfl⟩ := List.length_eq_one_iff.mp one
      have hb := beach 0 (by simp) (by simp)
      simp only [List.getElem_cons_zero, List.flatten_singleton] at hb ⊢
      cases hrs : rootResults P (.app f vs) with
      | nil => simp only [hrs, Option.some.injEq] at hb; subst hb; rfl
      | cons r tail =>
          have le := rootResults_length_le_one linear nonOverlap (.app f vs)
          rw [hrs] at le
          cases tail with
          | cons _ _ => simp at le
          | nil =>
              simp only [hrs, Option.map_eq_some_iff] at hb
              obtain ⟨cs, hcs, rfl⟩ := hb
              obtain ⟨clen, ceach⟩ := mapOpt_spec hcs
              have cone : cs.length = 1 := by simpa using clen.symm
              obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp cone
              simpa using evalTm_singleton linear nonOverlap n (ceach 0 (by simp) (by simp))

/-! ## The extensional model -/

mutual
/-- **Read a term in an interpretation** of the defined symbols, with values for its variables;
symbols that head no equation are constructors and read as themselves. -/
def interp (P : Program S) (g : S → List (Tm S) → Tm S) (ρ : String → Tm S) : Tm S → Tm S
  | .var x => ρ x
  | .app c args => if P.definesB c then g c (interpList P g ρ args) else .app c (interpList P g ρ args)
/-- Read a list of terms. -/
def interpList (P : Program S) (g : S → List (Tm S) → Tm S) (ρ : String → Tm S) :
    List (Tm S) → List (Tm S)
  | [] => []
  | a :: as => interp P g ρ a :: interpList P g ρ as
end

instance (P : Program S) : DecidablePred P.Defines := fun c =>
  decidable_of_iff (P.definesB c = true) Program.definesB_iff

theorem interpList_eq (g : S → List (Tm S) → Tm S) (ρ : String → Tm S) (args : List (Tm S)) :
    interpList P g ρ args = args.map (interp P g ρ) := by
  induction args with
  | nil => rfl
  | cons a as ih => simp [interpList, ih]

@[simp] theorem interp_var (g : S → List (Tm S) → Tm S) (ρ : String → Tm S) (x : String) :
    interp P g ρ (.var x) = ρ x := by simp [interp]

theorem interp_app (g : S → List (Tm S) → Tm S) (ρ : String → Tm S) (c : S) (args : List (Tm S)) :
    interp P g ρ (.app c args) =
      if P.Defines c then g c (args.map (interp P g ρ)) else .app c (args.map (interp P g ρ)) := by
  simp only [interp, interpList_eq]
  by_cases h : P.Defines c
  · rw [if_pos (Program.definesB_iff.mpr h), if_pos h]
  · rw [if_neg (fun hb => h (Program.definesB_iff.mp hb)), if_neg h]

/-- Reading an instance is reading the term with the instantiating terms read. -/
theorem interp_subst (g : S → List (Tm S) → Tm S) (ρ σ : String → Tm S) :
    ∀ t : Tm S, interp P g ρ (t.subst σ) = interp P g (fun x => interp P g ρ (σ x)) t := by
  intro t
  induction t using Tm.induction' with
  | var x => simp
  | app c args ih =>
      rw [subst_app, interp_app, interp_app, List.map_map]
      have : args.map (interp P g ρ ∘ subst σ) = args.map (interp P g (fun x => interp P g ρ (σ x))) :=
        List.map_congr_left fun a ha => ih a ha
      rw [this]

/-- The data of a sort: **the set a sort denotes.** -/
def Signature.Denotes (sig : Signature S) (τ : Sort') : Set (Tm S) := {v | sig.IsValueOf v τ}

namespace Admitted

variable {sig : Signature S}

/-- **The model of a defined symbol**: the normal form of its call. -/
noncomputable def model (adm : Admitted sig P) (f : S) (vs : List (Tm S)) : Tm S :=
  adm.normalForm (.app f vs)

/-- A constructor applied to normal forms is normal. -/
theorem app_normal (adm : Admitted sig P) {c : S} (undefined : ¬ P.Defines c) {args : List (Tm S)}
    (normal : ∀ a ∈ args, IsNormal (Step P) a) : IsNormal (Step P) (.app c args) := by
  intro t step
  obtain ⟨i, lt, a, stepAt, rfl⟩ := step.app_of_not_defines adm.typed.headed undefined
  exact normal _ (List.getElem_mem lt) _ stepAt

/-- **Reading a term in the model gives the normal form** of its instance, at normal values of
its variables. -/
theorem interp_eq_normalForm (adm : Admitted sig P) {ρ : String → Tm S}
    (normal : ∀ x, IsNormal (Step P) (ρ x)) :
    ∀ t : Tm S, interp P adm.model ρ t = adm.normalForm (t.subst ρ) := by
  intro t
  induction t using Tm.induction' with
  | var x => simp [adm.normalForm_of_normal (normal x)]
  | app c args ih =>
      rw [interp_app, subst_app]
      have argsNF : args.map (interp P adm.model ρ) = args.map (fun a => adm.normalForm (a.subst ρ)) :=
        List.map_congr_left fun a ha => ih a ha
      rw [argsNF]
      have toNF : ReflTransGen (Step P) (.app c (args.map (subst ρ)))
          (.app c (args.map fun a => adm.normalForm (a.subst ρ))) :=
        steps_args c _ _ (by simp) fun i hi hj => by
          simpa using (adm.normalForm_spec (args[i]'(by simpa using hi) |>.subst ρ)).1
      split
      · exact (adm.normalForm_of_steps toNF).symm
      · rename_i undefined
        apply adm.normalForm_unique
        refine ⟨toNF, adm.app_normal undefined fun a ha => ?_⟩
        obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
        exact (adm.normalForm_spec _).2

/-- **Every defined function is total** on the data of its argument sorts, at every instance of
its scheme, with a value in the data of its result sort. -/
theorem model_total (adm : Admitted sig P) {fd : FunDecl S} (hfd : fd ∈ sig.funs)
    (θ : String → Sort') {vs : List (Tm S)}
    (values : Pointwise sig.IsValueOf vs (fd.args.map (Tm.subst θ))) :
    adm.model fd.name vs ∈ sig.Denotes (fd.result.subst θ) := by
  apply adm.normalForm_value
  exact .call θ hfd (by simpa using values.1) fun i hi hj => by
    have := (values.2 i hi (by simpa using hj)).2
    simpa only [List.getElem_map] using this

/-- **Every equation holds in the model**, at all normal values of its variables. -/
theorem model_equation (adm : Admitted sig P) {e : Equation S} (he : e ∈ P)
    {ρ : String → Tm S} (normal : ∀ x, IsNormal (Step P) (ρ x)) :
    interp P adm.model ρ e.lhs = interp P adm.model ρ e.rhs := by
  rw [adm.interp_eq_normalForm normal, adm.interp_eq_normalForm normal]
  exact adm.normalForm_of_steps (.single (.root (.rule ρ he)))

/-- Data reads as itself in every interpretation. -/
theorem interp_data (adm : Admitted sig P) (g : S → List (Tm S) → Tm S) (ρ : String → Tm S) :
    ∀ {v : Tm S}, sig.IsData v → interp P g ρ v = v := by
  intro v data
  induction data with
  | @app c args isCtor _ ih =>
      rw [interp_app, if_neg (Signature.not_defines_ctor adm.wellFormed adm.typed isCtor)]
      congr 1
      conv_rhs => rw [← List.map_id args]
      exact List.map_congr_left ih

/-- **The model is the unique solution of the equations** on data of the declared sorts: any
interpretation of the defined symbols with normal values in which every equation holds, at all
normal values of its variables, agrees with the model on every call of a declared function on
data of its argument sorts. -/
theorem model_unique (adm : Admitted sig P) (g : S → List (Tm S) → Tm S)
    (normalValues : ∀ f vs, (∀ v ∈ vs, IsNormal (Step P) v) → IsNormal (Step P) (g f vs))
    (equations : ∀ e ∈ P, ∀ ρ : String → Tm S, (∀ x, IsNormal (Step P) (ρ x)) →
      interp P g ρ e.lhs = interp P g ρ e.rhs)
    {fd : FunDecl S} (hfd : fd ∈ sig.funs) (θ : String → Sort') {vs : List (Tm S)}
    (values : Pointwise sig.IsValueOf vs (fd.args.map (Tm.subst θ))) :
    g fd.name vs = adm.model fd.name vs := by
  have readNormal : ∀ t : Tm S, IsNormal (Step P) (interp P g Tm.var t) := by
    intro t
    induction t using Tm.induction' with
    | var x => simpa using var_normal adm.typed.headed x
    | app c args ih =>
        rw [interp_app]
        split
        · exact normalValues c _ fun v hv => by
            obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
            exact ih a ha
        · rename_i undefined
          exact adm.app_normal undefined fun v hv => by
            obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
            exact ih a ha
  have stepInvariant : ∀ {s t : Tm S}, Step P s t → interp P g Tm.var s = interp P g Tm.var t := by
    intro s t step
    induction step with
    | root root =>
        obtain ⟨e, he, σ, rfl, rfl⟩ := root.exists_rule
        rw [interp_subst, interp_subst]
        exact equations e he _ fun x => readNormal (σ x)
    | @arg c args i lt b _ ih =>
        rw [interp_app, interp_app]
        have : (args.set i b).map (interp P g Tm.var) = args.map (interp P g Tm.var) := by
          apply List.ext_getElem (by simp)
          intro j h₁ h₂
          by_cases same : i = j
          · subst same; simp [ih]
          · simp [List.getElem_set_ne same]
        rw [this]
  have stepsInvariant : ∀ {s t : Tm S}, ReflTransGen (Step P) s t →
      interp P g Tm.var s = interp P g Tm.var t := by
    intro s t steps
    induction steps with
    | refl => rfl
    | tail _ last ih => exact ih.trans (stepInvariant last)
  have valueData : ∀ v ∈ vs, sig.IsData v := fun v hv => by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
    exact (values.2 i hi (by simpa [values.1] using hi)).1
  have call := stepsInvariant (adm.normalForm_spec (.app fd.name vs)).1
  have defined : P.Defines fd.name := by
    by_contra undefined
    have nf := adm.normalForm_of_normal (adm.app_normal undefined fun v hv =>
      IsValue.normal adm.typed.headed
        (Signature.IsData.isValue adm.wellFormed adm.typed (valueData v hv)))
    have total := adm.model_total hfd θ values
    have hdata := total.1
    unfold model at hdata
    rw [nf] at hdata
    cases hdata with
    | app isCtor _ => exact adm.wellFormed.disjoint fd hfd isCtor
  rw [interp_app, if_pos defined] at call
  have nfData : sig.IsData (adm.normalForm (.app fd.name vs)) := (adm.model_total hfd θ values).1
  rw [interp_data adm g Tm.var nfData] at call
  have argsRead : vs.map (interp P g Tm.var) = vs := by
    conv_rhs => rw [← List.map_id vs]
    exact List.map_congr_left fun v hv => interp_data adm g Tm.var (valueData v hv)
  rw [argsRead] at call
  exact call

end Admitted

end Mettapedia.Languages.MeTTa.DeclarationFaces

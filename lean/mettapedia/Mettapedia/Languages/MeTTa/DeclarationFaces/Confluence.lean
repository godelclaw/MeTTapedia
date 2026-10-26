import Mettapedia.Languages.MeTTa.DeclarationFaces.Admission
import Mathlib.Data.List.Pairwise

/-!
# Confluence of an admitted declaration, and unique normal forms

For an admitted declaration the steps of MeTTa evaluation are confluent on every term
(`Admitted.confluent`): two steps from one term can always be joined (`Admitted.localConfluence`),
and with strong normalization Newman's lemma gives confluence of finite reductions
(`Mettapedia.Logic.Relation.confluent_of_accessible_forks`).

The two steps meet in one of three ways.

* **Both at one call** (`RootStep.deterministic`): non-overlap makes them one equation, and an
  instance of a left side determines the instance of the right side.
* **One at a call, one inside an argument**: a left side's arguments are constructor patterns, so
  a step inside an argument happens inside the term bound to one pattern variable
  (`step_pattern_instance`); the call stays a call of the same equation, and the right side catches
  up by rewriting every occurrence of that variable (`steps_subst`).
* **Both inside arguments**: at one argument by induction; at two arguments they commute.

Every term then has exactly one normal form (`Admitted.normalForm`), and a closed sorted term's
normal form is constructor data of its sort (`Admitted.normalForm_data`).

Negative example: with the overlapping equations `(f Z) = Z` and `(f $x) = (S Z)`, the term
`(f Z)` reaches two distinct normal forms (`Examples.overlap_two_normal_forms`), so no confluence
holds.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.DeclarationFaces

open Tm Relation
open Mettapedia.Logic.Relation (IsNormal Confluent confluent_of_accessible_forks
  exists_normalForm_of_acc)

universe u

variable {S : Type u} {P : Program S}

/-! ## An instance of a term determines the instantiating terms of its variables -/

theorem subst_agree_of_eq {σ τ : String → Tm S} :
    ∀ t : Tm S, t.subst σ = t.subst τ → ∀ x ∈ t.vars, σ x = τ x := by
  intro t
  induction t using Tm.induction' with
  | var name => intro same x member; simp at member same; subst member; exact same
  | app head args ih =>
      intro same x member
      simp only [subst_app, app.injEq, true_and] at same
      simp only [vars_app, List.mem_flatMap] at member
      obtain ⟨a, aMember, xMember⟩ := member
      exact ih a aMember (List.map_inj_left.mp same a aMember) x xMember

/-! ## Calls -/

/-- In a non-overlapping program, distinct equations have no common instance. -/
theorem Program.NonOverlapping.apart [DecidableEq S] (nonOverlap : P.NonOverlapping)
    {e e' : Equation S} (he : e ∈ P) (he' : e' ∈ P) (ne : e ≠ e') (σ τ : String → Tm S) :
    e.lhs.subst σ ≠ e'.lhs.subst τ := by
  have : Std.Symm (fun e e' : Equation S => ∀ σ τ : String → Tm S, e.lhs.subst σ ≠ e'.lhs.subst τ) :=
    ⟨fun _ _ h σ τ same => h τ σ same.symm⟩
  exact List.Pairwise.forall nonOverlap he he' ne σ τ

/-- **A call has at most one result** in a non-overlapping program whose right sides use only their
left side's variables. -/
theorem RootStep.deterministic [DecidableEq S] (nonOverlap : P.NonOverlapping)
    (bound : P.RightBound) {s t t' : Tm S} (step : RootStep P s t) (step' : RootStep P s t') :
    t = t' := by
  obtain ⟨e, he, σ, rfl, rfl⟩ := step.exists_rule
  obtain ⟨e', he', σ', same, rfl⟩ := step'.exists_rule
  by_cases equal : e = e'
  · subst equal
    apply subst_congr
    intro x hx
    exact subst_agree_of_eq e.lhs same x (bound e he x hx)
  · exact absurd same (nonOverlap.apart he he' equal σ σ')

/-! ## Steps inside patterns -/

theorem Step.not_var {s : Tm S} (headed : P.Headed) {x : String} : ¬ Step P (.var x) s :=
  fun step => var_normal headed x s step

/-- Positions of distinct arguments of a linear term carry disjoint variables. -/
theorem vars_disjoint_of_nodup {args : List (Tm S)} (nodup : (args.flatMap vars).Nodup)
    {i j : Nat} (hi : i < args.length) (hj : j < args.length) (ne : i ≠ j) {x : String}
    (hx : x ∈ args[i].vars) : x ∉ args[j].vars := by
  rw [List.nodup_flatMap] at nodup
  obtain ⟨_, pairwise⟩ := nodup
  rcases Nat.lt_or_gt_of_ne ne with lt | gt
  · exact fun hy => List.pairwise_iff_getElem.mp pairwise i j hi hj lt hx hy
  · exact fun hy => List.pairwise_iff_getElem.mp pairwise j i hj hi gt hy hx

/-- Replacing the instance of one argument of a linear list by its instance at an updated
substitution is instantiating the whole list at the updated substitution. -/
theorem map_subst_set_update {ps : List (Tm S)} (nodup : (ps.flatMap vars).Nodup)
    {i : Nat} (hi : i < ps.length) {x : String} (hx : x ∈ ps[i].vars) (σ : String → Tm S)
    (w : Tm S) :
    (ps.map (subst σ)).set i (ps[i].subst (Function.update σ x w)) =
      ps.map (subst (Function.update σ x w)) := by
  apply List.ext_getElem (by simp)
  intro j h₁ h₂
  by_cases same : i = j
  · subst same; simp
  · simp only [List.getElem_set_ne same, List.getElem_map]
    apply subst_congr
    intro y hy
    have ne : y ≠ x := fun h => vars_disjoint_of_nodup nodup hi (by simpa using h₂) same hx (h ▸ hy)
    simp [Function.update_of_ne ne]

/-- **A step inside an instance of a linear constructor pattern** is a step inside the term bound
to one of its variables. -/
theorem step_pattern_instance (headed : P.Headed) :
    ∀ {p : Tm S}, EveryCall (fun g _ => ¬ P.Defines g) p → p.Linear → ∀ {σ : String → Tm S}
      {u : Tm S}, Step P (p.subst σ) u →
        ∃ x ∈ p.vars, ∃ w, Step P (σ x) w ∧ u = p.subst (Function.update σ x w) := by
  intro p noDefined
  induction noDefined with
  | var x =>
      intro _ σ u step
      exact ⟨x, by simp, u, by simpa using step, by simp⟩
  | @app c args undefined _ ih =>
      intro linear σ u step
      rw [subst_app] at step
      obtain ⟨i, lt, a, stepAt, rfl⟩ := step.app_of_not_defines headed undefined
      have hi : i < args.length := by simpa using lt
      have nodup : (args.flatMap vars).Nodup := by simpa [Linear] using linear
      have argLinear : args[i].Linear := by
        rw [List.nodup_flatMap] at nodup
        exact nodup.1 _ (List.getElem_mem hi)
      obtain ⟨x, hx, w, stepX, rfl⟩ := ih _ (List.getElem_mem hi) argLinear (by simpa using stepAt)
      refine ⟨x, by simpa using ⟨args[i], List.getElem_mem hi, hx⟩, w, stepX, ?_⟩
      rw [subst_app, map_subst_set_update nodup hi hx σ w]

/-! ## Many steps -/

theorem steps_set {f : S} {args : List (Tm S)} {i : Nat} (lt : i < args.length) {a b : Tm S}
    (steps : ReflTransGen (Step P) a b) :
    ReflTransGen (Step P) (.app f (args.set i a)) (.app f (args.set i b)) := by
  induction steps with
  | refl => exact .refl
  | @tail b c _ last ih =>
      refine ih.tail ?_
      have := Step.arg f (args.set i b) i (by simpa using lt) (t := c) (by simpa using last)
      simpa using this

/-- Arguments that reduce, each to its own result, make a call that reduces. -/
theorem steps_args (f : S) : ∀ (args args' : List (Tm S)), args.length = args'.length →
    (∀ i (hi : i < args.length) (hj : i < args'.length), ReflTransGen (Step P) args[i] args'[i]) →
      ReflTransGen (Step P) (.app f args) (.app f args') := by
  suffices ∀ (n : Nat) (args args' : List (Tm S)), args.length = args'.length →
      (∀ i (hi : i < args.length) (hj : i < args'.length), ReflTransGen (Step P) args[i] args'[i]) →
      (∀ i (hi : i < args.length) (hj : i < args'.length), n ≤ i → args[i] = args'[i]) →
      ReflTransGen (Step P) (.app f args) (.app f args') by
    intro args args' len each
    exact this args.length args args' len each fun i hi _ le => absurd hi (by omega)
  intro n
  induction n with
  | zero =>
      intro args args' len _ same
      have : args = args' := List.ext_getElem len fun i hi hj => same i hi hj (Nat.zero_le _)
      subst this
      exact .refl
  | succ n ih =>
      intro args args' len each same
      by_cases hn : n < args.length
      · have hn' : n < args'.length := len ▸ hn
        let middle := args.set n args'[n]
        have first : ReflTransGen (Step P) (.app f args) (.app f middle) := by
          have := steps_set (f := f) hn (each n hn hn')
          simpa [middle] using this
        have second : ReflTransGen (Step P) (.app f middle) (.app f args') := by
          apply ih middle args' (by simp [middle, len])
          · intro i hi hj
            by_cases h : n = i
            · subst h; simp [middle]; exact .refl
            · simp only [middle, List.getElem_set_ne h]; exact each i (by simpa [middle] using hi) hj
          · intro i hi hj le
            by_cases h : n = i
            · subst h; simp [middle]
            · simp only [middle, List.getElem_set_ne h]
              exact same i (by simpa [middle] using hi) hj (by omega)
        exact first.trans second
      · apply ih args args' len each
        intro i hi hj _
        exact absurd hi (by omega)

/-- **Instances by reducing substitutions reduce.** -/
theorem steps_subst {σ τ : String → Tm S} (each : ∀ x, ReflTransGen (Step P) (σ x) (τ x)) :
    ∀ t : Tm S, ReflTransGen (Step P) (t.subst σ) (t.subst τ) := by
  intro t
  induction t using Tm.induction' with
  | var name => simpa using each name
  | app head args ih =>
      simp only [subst_app]
      exact steps_args head _ _ (by simp) fun i hi hj => by
        have hi' : i < args.length := by simpa using hi
        simpa using ih (args[i]'hi') (List.getElem_mem hi')

/-! ## Local confluence and confluence -/

/-- What the confluence proof uses of an admitted program. Root steps need only be deterministic:
non-overlap gives that, and so do overlaps whose right sides agree (weak orthogonality). -/
structure Orthogonal (P : Program S) : Prop where
  headed : P.Headed
  bound : P.RightBound
  rootDeterministic : ∀ {s t t' : Tm S}, RootStep P s t → RootStep P s t' → t = t'
  constructorPatterns : ∀ e ∈ P, ∃ f ps, e.lhs = .app f ps ∧
    ∀ p ∈ ps, EveryCall (fun g _ => ¬ P.Defines g) p
  leftLinear : P.LeftLinear

/-- A call by an equation joins a step inside one of its arguments. -/
theorem Orthogonal.root_arg_join (orth : Orthogonal P) {s t₁ : Tm S}
    (root : RootStep P s t₁) {f : S} {args : List (Tm S)} (hs : s = .app f args) {i : Nat}
    (lt : i < args.length) {a : Tm S} (stepAt : Step P args[i] a) :
    Join (ReflTransGen (Step P)) t₁ (.app f (args.set i a)) := by
  obtain ⟨e, he, σ, rfl, rfl⟩ := root.exists_rule
  obtain ⟨f', ps, hlhs, patterns⟩ := orth.constructorPatterns e he
  rw [hlhs, subst_app] at hs
  obtain ⟨rfl, rfl⟩ := Tm.app.inj hs
  have hi : i < ps.length := by simpa using lt
  have nodup : (ps.flatMap vars).Nodup := by
    have := orth.leftLinear e he
    rw [hlhs] at this
    simpa [Linear] using this
  have argLinear : ps[i].Linear := by
    rw [List.nodup_flatMap] at nodup
    exact nodup.1 _ (List.getElem_mem hi)
  obtain ⟨x, hx, w, stepX, rfl⟩ :=
    step_pattern_instance orth.headed (patterns _ (List.getElem_mem hi)) argLinear
      (by simpa using stepAt)
  refine ⟨e.rhs.subst (Function.update σ x w), ?_, ?_⟩
  · apply steps_subst
    intro y
    by_cases same : y = x
    · subst same; simpa using ReflTransGen.single stepX
    · rw [Function.update_of_ne same]
  · apply ReflTransGen.single
    apply Step.root
    have := RootStep.rule (P := P) (Function.update σ x w) he
    rw [hlhs, subst_app] at this
    rw [map_subst_set_update nodup hi hx σ w]
    exact this

/-- **Local confluence**: two steps from one term can be joined. -/
theorem Orthogonal.localConfluence (orth : Orthogonal P) :
    ∀ {s t₁ t₂ : Tm S}, Step P s t₁ → Step P s t₂ → Join (ReflTransGen (Step P)) t₁ t₂ := by
  intro s t₁ t₂ step₁
  induction step₁ generalizing t₂ with
  | root root₁ =>
      intro step₂
      cases step₂ with
      | root root₂ =>
          rw [orth.rootDeterministic root₁ root₂]
          exact ⟨t₂, .refl, .refl⟩
      | arg f args i lt stepAt => exact orth.root_arg_join root₁ rfl lt stepAt
  | @arg f args i lt a stepAt₁ ih =>
      intro step₂
      cases step₂ with
      | root root₂ =>
          obtain ⟨c, h₁, h₂⟩ := orth.root_arg_join root₂ rfl lt stepAt₁
          exact ⟨c, h₂, h₁⟩
      | arg _ _ j lt' stepAt₂ =>
          rename_i b
          by_cases same : i = j
          · subst same
            obtain ⟨c, h₁, h₂⟩ := ih stepAt₂
            exact ⟨_, steps_set lt h₁, steps_set lt h₂⟩
          · refine ⟨.app f ((args.set i a).set j b), ?_, ?_⟩
            · apply ReflTransGen.single
              have := Step.arg f (args.set i a) j (by simpa using lt') (t := b)
                (by simpa [List.getElem_set_ne same] using stepAt₂)
              exact this
            · apply ReflTransGen.single
              rw [List.set_comm a b same]
              have := Step.arg f (args.set j b) i (by simpa using lt) (t := a)
                (by simpa [List.getElem_set_ne (Ne.symm same)] using stepAt₁)
              exact this

/-- **Confluence** of an orthogonal, descending program. -/
theorem Orthogonal.confluent (orth : Orthogonal P) {c : Certificate S}
    (descends : P.Descends c) : Confluent (Step P) :=
  confluent_of_accessible_forks (descends.stronglyNormalizing orth.headed orth.bound)
    fun _ _ _ h₁ h₂ => orth.localConfluence h₁ h₂

/-! ## Admitted declarations -/

namespace Admitted

variable [DecidableEq S] {sig : Signature S}

/-- An admitted program is orthogonal. -/
theorem orthogonal (adm : Admitted sig P) : Orthogonal P where
  headed := adm.typed.headed
  bound := adm.rightBound
  rootDeterministic := fun h h' => RootStep.deterministic adm.nonOverlapping adm.rightBound h h'
  constructorPatterns := by
    intro e he
    obtain ⟨fd, _, ps, _, hlhs, patterns, _⟩ := adm.typed e he
    refine ⟨fd.name, ps, hlhs, fun p hp => ?_⟩
    have pattern := patterns p hp
    clear hp hlhs patterns
    induction pattern with
    | var x => exact .var x
    | ctor isCtor _ ih =>
        exact .app (Signature.not_defines_ctor adm.wellFormed adm.typed isCtor) ih
  leftLinear := adm.leftLinear

/-- **Every term of an admitted declaration is strongly normalizing.** -/
theorem stronglyNormalizing (adm : Admitted sig P) : ∀ t, SN P t := adm.terminating

/-- **The steps of an admitted declaration are confluent**, on every term. -/
theorem confluent (adm : Admitted sig P) : Confluent (Step P) :=
  confluent_of_accessible_forks adm.terminating fun _ _ _ h₁ h₂ => adm.orthogonal.localConfluence h₁ h₂

/-- A normal form of a term: a reduct that takes no step. -/
def IsNormalFormOf (P : Program S) (t n : Tm S) : Prop :=
  ReflTransGen (Step P) t n ∧ IsNormal (Step P) n

/-- **Every term has exactly one normal form.** -/
theorem existsUnique_normalForm (adm : Admitted sig P) (t : Tm S) :
    ∃! n, IsNormalFormOf P t n := by
  obtain ⟨n, steps, normal⟩ := exists_normalForm_of_acc (adm.stronglyNormalizing t)
  refine ⟨n, ⟨steps, normal⟩, fun m ⟨steps', normal'⟩ => ?_⟩
  obtain ⟨c, h₁, h₂⟩ := adm.confluent t m n steps' steps
  exact (normal'.reflTransGen_eq h₁).symm.trans (normal.reflTransGen_eq h₂)

/-- **The normal form** of a term. -/
noncomputable def normalForm (adm : Admitted sig P) (t : Tm S) : Tm S :=
  (adm.existsUnique_normalForm t).exists.choose

theorem normalForm_spec (adm : Admitted sig P) (t : Tm S) :
    IsNormalFormOf P t (adm.normalForm t) :=
  (adm.existsUnique_normalForm t).exists.choose_spec

/-- Every normal form of a term is the normal form. -/
theorem normalForm_unique (adm : Admitted sig P) {t n : Tm S} (h : IsNormalFormOf P t n) :
    n = adm.normalForm t :=
  (adm.existsUnique_normalForm t).unique h (adm.normalForm_spec t)

/-- Reducts have the same normal form. -/
theorem normalForm_of_steps (adm : Admitted sig P) {s t : Tm S}
    (steps : ReflTransGen (Step P) s t) : adm.normalForm s = adm.normalForm t := by
  have := adm.normalForm_spec t
  exact (adm.normalForm_unique ⟨steps.trans this.1, this.2⟩).symm

/-- A normal term is its own normal form. -/
theorem normalForm_of_normal (adm : Admitted sig P) {n : Tm S} (normal : IsNormal (Step P) n) :
    adm.normalForm n = n :=
  (adm.normalForm_unique ⟨.refl, normal⟩).symm

/-- **The normal form of a closed sorted term is constructor data of its sort.** -/
theorem normalForm_value (adm : Admitted sig P) {t : Tm S} {τ : Sort'}
    (typed : HasSort sig Ctx.empty t τ) : sig.IsValueOf (adm.normalForm t) τ := by
  have spec := adm.normalForm_spec t
  have typedNF := HasSort.steps adm.wellFormed adm.typed adm.rightBound spec.1 typed
  exact ⟨HasSort.data_of_normal adm.covers typedNF spec.2, typedNF⟩

end Admitted

/-! ## Examples -/

namespace Examples

/-- `(= (f Z) Z)` and `(= (f $x) (S Z))`. -/
def overlapping : Program String :=
  [⟨.app "f" [.app "Z" []], .app "Z" []⟩, ⟨.app "f" [.var "x"], .app "S" [.app "Z" []]⟩]

theorem z_normal : IsNormal (Step overlapping) (.app "Z" []) := by
  intro t step
  cases step with
  | root root =>
      obtain ⟨e, he, σ, same, _⟩ := root.exists_rule
      simp only [overlapping, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> simp [subst] at same
  | arg _ _ i lt _ => simp at lt

theorem sz_normal : IsNormal (Step overlapping) (.app "S" [.app "Z" []]) := by
  intro t step
  cases step with
  | root root =>
      obtain ⟨e, he, σ, same, _⟩ := root.exists_rule
      simp only [overlapping, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> simp [subst] at same
  | arg _ _ i lt inner =>
      have : i = 0 := by simp at lt; omega
      subst this
      exact z_normal _ (by simpa using inner)

/-- **Negative example**: with overlapping equations, `(f Z)` has two distinct normal forms. -/
theorem overlap_two_normal_forms :
    Admitted.IsNormalFormOf overlapping (.app "f" [.app "Z" []]) (.app "Z" []) ∧
      Admitted.IsNormalFormOf overlapping (.app "f" [.app "Z" []]) (.app "S" [.app "Z" []]) ∧
      (.app "Z" [] : Tm String) ≠ .app "S" [.app "Z" []] := by
  refine ⟨⟨.single (.root ?_), z_normal⟩, ⟨.single (.root ?_), sz_normal⟩, by decide⟩
  · have h := RootStep.rule (P := overlapping)
      (e := ⟨.app "f" [.app "Z" []], .app "Z" []⟩) Tm.var (by simp [overlapping])
    simpa using h
  · have h := RootStep.rule (P := overlapping)
      (e := ⟨.app "f" [.var "x"], .app "S" [.app "Z" []]⟩) (fun _ => .app "Z" [])
      (by simp [overlapping])
    simpa using h

end Examples

end Mettapedia.Languages.MeTTa.DeclarationFaces

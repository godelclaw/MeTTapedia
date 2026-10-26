import Mettapedia.Languages.MeTTa.DeclarationFaces.Faces

/-!
# Agreement within an execution scope

An **execution scope** is one signature with one program: the rules a run may use. Every
agreement theorem is relative to a scope that admission accepted.

**The main theorem** (`Admitted.faces_agree`): for an admitted scope and a closed sorted term, its
normal form is constructor data of the term's sort; every evaluation strategy terminates with that
normal form as its only outcome; the executable evaluator returns exactly that one result; and the
term read in the extensional model is that normal form.

**The scope is part of the statement.**
* *Extension* (`step_append_iff`, `Admitted.normalForm_append`): adding equations for symbols a
  term does not mention leaves its steps, hence its normal form, unchanged; admitting a new
  declaration on top of an admitted scope keeps every old meaning.
* *Substitution and context* (`Step.subst`, `HasSort.weaken`): steps are stable under
  instantiation, and sorts under extension of the context.
* *A rule outside the scope breaks agreement* (`Controls`): the admitted addition plus the rule
  `(= (add $n Z) Z)` is refused as an overlap, and evaluation in that larger scope returns two
  results for `(add (S Z) Z)`, one of which is not the theory's normal form.
* *Dependencies* (`Controls`): `double` written once over two scopes that define `add`
  differently has different meanings; a result about `double` is a result about its scope.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.DeclarationFaces

open Tm Relation
open Mettapedia.Logic.Relation (IsNormal accessible_transitiveClosure)

universe u

variable {S : Type u} {P : Program S}

/-! ## The main theorem -/

namespace Admitted

variable [DecidableEq S] {sig : Signature S}

/-- What the evaluator uses of an admitted program. -/
theorem executable (adm : Admitted sig P) : Executable P :=
  ⟨adm.typed.headed, adm.leftLinear, adm.rightBound⟩

/-- **The evaluator returns exactly the normal form**, on every term of an admitted scope. -/
theorem evalTm_result (adm : Admitted sig P) (t : Tm S) :
    (∃ n, evalTm P n t = some [adm.normalForm t]) ∧
      ∀ n rs, evalTm P n t = some rs → rs = [adm.normalForm t] := by
  have result : ∀ n rs, evalTm P n t = some rs → rs = [adm.normalForm t] := by
    intro n rs h
    obtain ⟨r, rfl⟩ := List.length_eq_one_iff.mp
      (evalTm_singleton adm.leftLinear adm.nonOverlapping n h)
    obtain ⟨steps, normal⟩ := evalTm_sound adm.executable n h r List.mem_cons_self
    rw [adm.normalForm_unique ⟨steps, normal⟩]
  obtain ⟨n, hn⟩ := evalTm_terminates adm.executable
    (accessible_transitiveClosure (acc_below (adm.stronglyNormalizing t)))
  obtain ⟨rs, hrs⟩ := Option.isSome_iff_exists.mp hn
  exact ⟨⟨n, by rw [hrs, result n rs hrs]⟩, result⟩

/-- **The faces of an admitted scope agree on a closed sorted term.** Its normal form is data of
its sort; every strategy terminates with exactly that outcome; the executable evaluator returns
that one result; and the extensional model reads the term as that value. -/
theorem faces_agree (adm : Admitted sig P) {t : Tm S} {τ : Sort'}
    (typed : HasSort sig Ctx.empty t τ) :
    adm.normalForm t ∈ sig.Denotes τ ∧
      (∀ (r : Strategy P) (u : Tm S),
        (ReflTransGen r.step t u ∧ IsNormal r.step u) ↔ u = adm.normalForm t) ∧
      (∃ n, evalTm P n t = some [adm.normalForm t]) ∧
      (∀ n rs, evalTm P n t = some rs → rs = [adm.normalForm t]) ∧
      interp P adm.model Tm.var t = adm.normalForm t := by
  refine ⟨adm.normalForm_value typed, fun r u => adm.strategy_outcome r t u, (adm.evalTm_result t).1,
    (adm.evalTm_result t).2, ?_⟩
  rw [adm.interp_eq_normalForm (fun x => var_normal adm.typed.headed x), subst_id]

/-- **The obligation of an execution lane.** On an admitted scope, a lane whose results are normal
forms reached by steps returns nothing but the normal form, whatever its order, sharing or
representation; if it also returns some result, it returns exactly the normal form. A lane earns the
agreement theorems by discharging these two obligations against `Step`. -/
theorem sound_lane (adm : Admitted sig P) (run : Tm S → List (Tm S))
    (sound : ∀ t r, r ∈ run t → ReflTransGen (Step P) t r ∧ IsNormal (Step P) r) :
    ∀ t, ∀ r ∈ run t, r = adm.normalForm t := fun t r hr =>
  adm.normalForm_unique (sound t r hr)

/-- A sound lane that answers on a closed sorted term answers with data of the term's sort. -/
theorem sound_lane_value (adm : Admitted sig P) (run : Tm S → List (Tm S))
    (sound : ∀ t r, r ∈ run t → ReflTransGen (Step P) t r ∧ IsNormal (Step P) r)
    {t : Tm S} {τ : Sort'} (typed : HasSort sig Ctx.empty t τ) {r : Tm S} (hr : r ∈ run t) :
    r ∈ sig.Denotes τ := by
  rw [adm.sound_lane run sound t r hr]
  exact adm.normalForm_value typed

end Admitted

/-! ## Substitution and context -/

/-- **Steps are stable under instantiation.** -/
theorem Step.subst (σ : String → Tm S) {s t : Tm S} (step : Step P s t) :
    Step P (s.subst σ) (t.subst σ) := by
  induction step with
  | root root =>
      obtain ⟨e, he, τ, rfl, rfl⟩ := root.exists_rule
      rw [subst_subst, subst_subst]
      exact .root (.rule _ he)
  | @arg f args i lt b _ ih =>
      rw [subst_app, subst_app, List.map_set]
      exact .arg f (args.map (Tm.subst σ)) i (by simpa using lt) (by simpa using ih)

/-- **Sorts are stable under extension of the context.** -/
theorem HasSort.weaken {sig : Signature S} {Γ Δ : Ctx} (extends' : ∀ x τ, Γ x = some τ → Δ x = some τ) :
    ∀ {t : Tm S} {τ : Sort'}, HasSort sig Γ t τ → HasSort sig Δ t τ := by
  intro t τ typed
  induction typed with
  | var h => exact .var (extends' _ _ h)
  | ctor θ hd hc len _ ih => exact .ctor θ hd hc len ih
  | call θ hfd len _ ih => exact .call θ hfd len ih

/-! ## Extension of a scope -/

/-- A step of a scope is a step of every larger scope. -/
theorem Step.root_or_arg_append {Q : Program S} {s t : Tm S} (step : Step P s t) :
    Step (P ++ Q) s t := by
  induction step with
  | root root =>
      obtain ⟨e, he, σ, rfl, rfl⟩ := root.exists_rule
      exact .root (.rule σ (List.mem_append_left Q he))
  | arg f args i lt _ ih => exact .arg f args i lt ih

/-- A symbol occurs in a term. -/
inductive Occurs (f : S) : Tm S → Prop where
  | head (args : List (Tm S)) : Occurs f (.app f args)
  | arg {g : S} {args : List (Tm S)} {a : Tm S} : a ∈ args → Occurs f a → Occurs f (.app g args)

/-- A term mentions no symbol that heads an equation of `Q`. -/
def FreshFor (Q : Program S) (t : Tm S) : Prop := ∀ e ∈ Q, ∀ f, e.lhs.head? = some f → ¬ Occurs f t

theorem occurs_instance (l : Tm S) (σ : String → Tm S) {f : S} (h : l.head? = some f) :
    Occurs f (l.subst σ) := by
  cases l with
  | var _ => simp [head?] at h
  | app g args =>
      simp only [head?, Option.some.injEq] at h
      subst h
      rw [subst_app]
      exact .head _

/-- **Headed equations for symbols a term does not mention take no step at it**: the steps of the
extended scope at such a term are exactly the steps of the original scope. -/
theorem step_append_iff {Q : Program S} (headedQ : Q.Headed) :
    ∀ {t u : Tm S}, FreshFor Q t → (Step (P ++ Q) t u ↔ Step P t u) := by
  intro t u fresh
  constructor
  · intro step
    induction step with
    | root root =>
        obtain ⟨e, he, σ, rfl, rfl⟩ := root.exists_rule
        rcases List.mem_append.mp he with inP | inQ
        · exact .root (.rule σ inP)
        · exfalso
          obtain ⟨f, args, hl⟩ := headedQ e inQ
          have hf : e.lhs.head? = some f := by simp [hl, head?]
          exact fresh e inQ f hf (occurs_instance _ σ hf)
    | arg f args i lt _ ih =>
        exact .arg f args i lt (ih fun e he g hg occ =>
          fresh e he g hg (.arg (List.getElem_mem lt) occ))
  · intro step
    induction step with
    | root root =>
        obtain ⟨e, he, σ, rfl, rfl⟩ := root.exists_rule
        exact .root (.rule σ (List.mem_append_left Q he))
    | arg f args i lt _ ih =>
        exact .arg f args i lt (ih fun e he g hg occ =>
          fresh e he g hg (.arg (List.getElem_mem lt) occ))

/-- An occurrence in an instance is an occurrence in the term or in an instantiating term. -/
theorem occurs_subst {f : S} (σ : String → Tm S) :
    ∀ {t : Tm S}, Occurs f (t.subst σ) → Occurs f t ∨ ∃ x ∈ t.vars, Occurs f (σ x) := by
  intro t
  induction t using Tm.induction' with
  | var x => intro h; exact .inr ⟨x, by simp, by simpa using h⟩
  | app g args ih =>
      intro h
      rw [subst_app] at h
      cases h with
      | head _ => exact .inl (.head _)
      | arg member occ =>
          obtain ⟨a, ha, rfl⟩ := List.mem_map.mp member
          rcases ih a ha occ with inA | ⟨x, hx, occX⟩
          · exact .inl (.arg ha inA)
          · exact .inr ⟨x, by simpa using ⟨a, ha, hx⟩, occX⟩

/-- An occurrence in an instantiating term of a variable of the term is an occurrence in the
instance. -/
theorem occurs_of_var {f : S} (σ : String → Tm S) :
    ∀ {t : Tm S} {x : String}, x ∈ t.vars → Occurs f (σ x) → Occurs f (t.subst σ) := by
  intro t
  induction t using Tm.induction' with
  | var y => intro x hx occ; simp at hx; subst hx; simpa using occ
  | app g args ih =>
      intro x hx occ
      simp only [vars_app, List.mem_flatMap] at hx
      obtain ⟨a, ha, hxa⟩ := hx
      rw [subst_app]
      exact .arg (List.mem_map_of_mem ha) (ih a ha hxa occ)

/-- **Freshness is kept by the steps of a scope whose right sides mention no new head.** -/
theorem FreshFor.step {Q : Program S} (rightFresh : ∀ e ∈ P, FreshFor Q e.rhs)
    (bound : P.RightBound) : ∀ {s t : Tm S}, Step P s t → FreshFor Q s → FreshFor Q t := by
  intro s t step
  induction step with
  | root root =>
      obtain ⟨e, he, σ, rfl, rfl⟩ := root.exists_rule
      intro fresh e' he' f hf occ
      rcases occurs_subst σ occ with inRhs | ⟨x, hx, occX⟩
      · exact rightFresh e he e' he' f hf inRhs
      · exact fresh e' he' f hf (occurs_of_var σ (bound e he x hx) occX)
  | @arg g args i lt b _ ih =>
      intro fresh e' he' f hf occ
      cases occ with
      | head _ => exact fresh e' he' _ hf (.head _)
      | arg member occ' =>
          rcases List.mem_or_eq_of_mem_set member with old | new
          · exact fresh e' he' f hf (.arg old occ')
          · subst new
            exact ih (fun e'' he'' f' hf' occ'' =>
              fresh e'' he'' f' hf' (.arg (List.getElem_mem lt) occ'')) e' he' f hf occ'

/-- **Admitting new declarations keeps every old meaning**: when both a scope and its extension are
admitted, the extension's equations are headed by symbols an old term does not mention, and the old
right sides do not mention them either, the old term has the same normal form in both scopes. -/
theorem Admitted.normalForm_append [DecidableEq S] {sig sig' : Signature S} {Q : Program S}
    (adm : Admitted sig P) (adm' : Admitted sig' (P ++ Q)) (headedQ : Q.Headed)
    (rightFresh : ∀ e ∈ P, FreshFor Q e.rhs) {t : Tm S} (fresh : FreshFor Q t) :
    adm'.normalForm t = adm.normalForm t := by
  have spec := adm.normalForm_spec t
  have freshAlong : ∀ {u}, ReflTransGen (Step P) t u → FreshFor Q u := by
    intro u steps
    induction steps with
    | refl => exact fresh
    | tail _ last ih => exact FreshFor.step rightFresh adm.rightBound last ih
  symm
  apply adm'.normalForm_unique
  refine ⟨?_, fun u step => spec.2 u ((step_append_iff headedQ (freshAlong spec.1)).mp step)⟩
  have lift : ∀ {a b}, ReflTransGen (Step P) a b → ReflTransGen (Step (P ++ Q)) a b := by
    intro a b h
    induction h with
    | refl => exact .refl
    | tail _ last ih => exact ih.tail last.root_or_arg_append
  exact lift spec.1

end Mettapedia.Languages.MeTTa.DeclarationFaces

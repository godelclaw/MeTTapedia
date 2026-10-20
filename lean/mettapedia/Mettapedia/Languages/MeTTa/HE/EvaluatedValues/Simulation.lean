import Mettapedia.Languages.MeTTa.HE.EvaluatedValues.Laws

/-!
# Evaluation steps agree up to marks

One step of evaluation, with its mark not read (`openStep`), depends on the
terms it handles only through their erasures, and it never creates a mark on
a node except at the root of a result. This file states that precisely as a
`Demand.Rel` between the steps of two terms with equal erasures, carrying
along a predicate `Stab` that every marked node of the left-hand term
satisfies.

* `Sim Stab t u` — equal erasures, and every marked node of `t` is in `Stab`.
* `SimBelow Stab t u` — the same, except that the root mark of `t` is not
  checked: a result equal to the evaluated term is marked at the root by the
  step itself, and only the caller can say why that mark is justified.
* `openStep_sim` — the main lemma.

With `Stab` trivial this is mark-blindness of `reevaluate`; with `Stab` the
stable atoms of a program it drives the conservativity theorem.
-/

namespace Mettapedia.Languages.MeTTa.HE.EvaluatedValues

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-! ## List and option facts -/

theorem forall₂_map_eq {α β γ : Type} {R : α → β → Prop} {f : α → γ} {g : β → γ}
    {l₁ : List α} {l₂ : List β} (h : List.Forall₂ R l₁ l₂) (hfg : ∀ a b, R a b → f a = g b) :
    l₁.map f = l₂.map g := by
  induction h with
  | nil => rfl
  | cons hab _ ih => simp [hfg _ _ hab, ih]

theorem forall₂_of_map_eq {α β γ : Type} {f : α → γ} {g : β → γ} :
    ∀ {l₁ : List α} {l₂ : List β}, l₁.map f = l₂.map g →
      List.Forall₂ (fun a b => f a = g b) l₁ l₂
  | [], [], _ => .nil
  | _ :: _, _ :: _, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    exact .cons h.1 (forall₂_of_map_eq h.2)
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem forall₂_imp_mem_left {α β : Type} {R S : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) (hRS : ∀ a b, a ∈ l₁ → R a b → S a b) : List.Forall₂ S l₁ l₂ := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih =>
    exact .cons (hRS _ _ List.mem_cons_self hab)
      (ih fun a b ha h => hRS a b (List.mem_cons_of_mem _ ha) h)

theorem Option.rel_some_iff {α β : Type} {S : α → β → Prop} {a : α} {b : β} :
    Option.Rel S (some a) (some b) ↔ S a b :=
  ⟨fun h => by cases h; assumption, .some⟩

theorem Option.not_rel_none_some {α β : Type} {S : α → β → Prop} {b : β} :
    ¬ Option.Rel S (none : Option α) (some b) := fun h => by cases h

theorem Option.not_rel_some_none {α β : Type} {S : α → β → Prop} {a : α} :
    ¬ Option.Rel S (some a) (none : Option β) := fun h => by cases h

theorem forall₂_filterMap {α β γ : Type} {S : β → γ → Prop} {f : α → Option β}
    {g : α → Option γ} :
    ∀ {l : List α}, (∀ a ∈ l, Option.Rel S (f a) (g a)) →
      List.Forall₂ S (l.filterMap f) (l.filterMap g)
  | [], _ => .nil
  | a :: l, h => by
    have ih := forall₂_filterMap (l := l) fun b hb => h b (List.mem_cons_of_mem _ hb)
    have ha := h a List.mem_cons_self
    simp only [List.filterMap_cons]
    cases hf : f a with
    | none =>
      cases hg : g a with
      | none => exact ih
      | some c => rw [hf, hg] at ha; exact absurd ha Option.not_rel_none_some
    | some b =>
      cases hg : g a with
      | none => rw [hf, hg] at ha; exact absurd ha Option.not_rel_some_none
      | some c => rw [hf, hg] at ha; exact .cons (Option.rel_some_iff.mp ha) ih

/-! ## The relations -/

section Relations

variable (Stab : Atom → Prop)

/-- Every marked node of `t` is admitted by `Stab`. -/
def MarksIn (t : MAtom) : Prop := ∀ a ∈ t.marks, Stab a

/-- Equal erasures, and the marks of the left term are admitted. -/
def Sim (t u : MAtom) : Prop := t.erase = u.erase ∧ MarksIn Stab t

/-- Equal erasures, and the marks strictly below the root of the left term
are admitted. -/
def SimBelow (t u : MAtom) : Prop := t.erase = u.erase ∧ ∀ a ∈ t.childMarks, Stab a

/-- Substitutions binding the same names, in the same order, to `Sim` terms. -/
def SubstSim (σ τ : Subst) : Prop :=
  List.Forall₂ (fun p q => p.1 = q.1 ∧ Sim Stab p.2 q.2) σ τ

end Relations

variable {Stab : Atom → Prop}

theorem MarksIn.of_code (a : Atom) : MarksIn Stab (code a) := by
  intro b hb
  simp at hb

theorem Sim.code (a : Atom) : Sim Stab (code a) (code a) := ⟨rfl, MarksIn.of_code a⟩

theorem marksIn_expr_iff {m : Bool} {cs : List MAtom} :
    MarksIn Stab (.expr m cs) ↔
      (m = true → Stab (.expression (cs.map MAtom.erase))) ∧ ∀ c ∈ cs, MarksIn Stab c := by
  simp only [MarksIn, MAtom.marks_expr, List.mem_append, List.mem_flatMap]
  constructor
  · intro h
    refine ⟨fun hm => h _ (Or.inl (by simp [hm])), fun c hc a ha => h a (Or.inr ⟨c, hc, ha⟩)⟩
  · rintro ⟨h₁, h₂⟩ a (ha | ⟨c, hc, ha⟩)
    · split at ha
      · simp only [List.mem_singleton] at ha; subst ha; exact h₁ (by assumption)
      · simp at ha
    · exact h₂ c hc a ha

theorem Sim.erase_eq {t u : MAtom} (h : Sim Stab t u) : t.erase = u.erase := h.1

/-- Children of `Sim` expressions are pairwise `Sim`. -/
theorem Sim.children {m m' : Bool} {cs cs' : List MAtom}
    (h : Sim Stab (.expr m cs) (.expr m' cs')) : List.Forall₂ (Sim Stab) cs cs' := by
  obtain ⟨he, hm⟩ := h
  simp only [MAtom.erase_expr, Atom.expression.injEq] at he
  have hc := (marksIn_expr_iff.mp hm).2
  exact forall₂_imp_mem_left (forall₂_of_map_eq he) fun a b ha hab => ⟨hab, hc a ha⟩

theorem sim_expr_false {cs cs' : List MAtom} (b : Bool) (h : List.Forall₂ (Sim Stab) cs cs') :
    Sim Stab (.expr false cs) (.expr b cs') := by
  refine ⟨?_, marksIn_expr_iff.mpr ⟨by simp, fun c hc => ?_⟩⟩
  · simp only [MAtom.erase_expr, Atom.expression.injEq]
    exact forall₂_map_eq h fun _ _ hab => hab.1
  · obtain ⟨c', -, hcc'⟩ := forall₂_exists_left h hc
    exact hcc'.2

theorem Sim.simBelow_mark {t u : MAtom} (h : Sim Stab t u) : SimBelow Stab t.mark u.mark := by
  refine ⟨by simp [h.1], fun a ha => h.2 a ?_⟩
  rw [MAtom.childMarks_mark] at ha
  exact MAtom.childMarks_sub_marks t a ha

theorem Sim.simBelow_markIf (a : Atom) {t u : MAtom} (h : Sim Stab t u) :
    SimBelow Stab (t.markIf a) (u.markIf a) := by
  refine ⟨by simp [h.1], fun b hb => h.2 b ?_⟩
  rw [MAtom.childMarks_markIf] at hb
  exact MAtom.childMarks_sub_marks t b hb

theorem SimBelow.sim {t u : MAtom} (h : SimBelow Stab t u) (hroot : Stab t.erase) :
    Sim Stab t u := by
  refine ⟨h.1, fun a ha => ?_⟩
  rcases MAtom.marks_sub t a ha with rfl | ha
  · exact hroot
  · exact h.2 a ha

theorem Sim.simBelow {t u : MAtom} (h : Sim Stab t u) : SimBelow Stab t u :=
  ⟨h.1, fun a ha => h.2 a (MAtom.childMarks_sub_marks t a ha)⟩

/-- Erasure-equal terms have the same outer constructor. -/
theorem erase_eq_symbol {u : MAtom} {s : String} (h : (MAtom.symbol s).erase = u.erase) :
    u = .symbol s := by
  cases u <;> simp_all

theorem erase_eq_var {u : MAtom} {x : String} (h : (MAtom.var x).erase = u.erase) :
    u = .var x := by
  cases u <;> simp_all

theorem erase_eq_grounded {u : MAtom} {g : GroundedValue}
    (h : (MAtom.grounded g).erase = u.erase) : u = .grounded g := by
  cases u <;> simp_all

theorem erase_eq_expr {u : MAtom} {m : Bool} {cs : List MAtom}
    (h : (MAtom.expr m cs).erase = u.erase) : ∃ m' cs', u = .expr m' cs' := by
  cases u <;> simp_all

/-! ## Substitution and matching -/

theorem SubstSim.lookup {σ τ : Subst} (h : SubstSim Stab σ τ) (x : String) :
    Option.Rel (Sim Stab) (σ.lookup x) (τ.lookup x) := by
  induction h with
  | nil => exact .none
  | @cons p q σ τ hpq _ ih =>
    obtain ⟨y, a⟩ := p
    obtain ⟨y', b⟩ := q
    obtain ⟨rfl, hab⟩ := hpq
    simp only [Subst.lookup_cons]
    split
    · exact .some hab
    · exact ih

theorem SubstSim.marksIn {σ τ : Subst} (h : SubstSim Stab σ τ) {x : String} {a : MAtom}
    (hx : σ.lookup x = some a) : MarksIn Stab a := by
  have := h.lookup x
  rw [hx] at this
  cases hτ : τ.lookup x with
  | none => rw [hτ] at this; exact absurd this Option.not_rel_some_none
  | some b => rw [hτ] at this; exact (Option.rel_some_iff.mp this).2

theorem erase_subst_congr {σ τ : Subst} (hστ : SubstSim Stab σ τ) :
    ∀ t u : MAtom, t.erase = u.erase → (t.subst σ).erase = (u.subst τ).erase := by
  intro t
  induction t using MAtom.induction with
  | symbol s => intro u h; rw [erase_eq_symbol h]; rfl
  | grounded g => intro u h; rw [erase_eq_grounded h]; rfl
  | var x =>
    intro u h
    rw [erase_eq_var h]
    have hl := hστ.lookup x
    simp only [MAtom.subst_var]
    cases h₁ : σ.lookup x with
    | none =>
      cases h₂ : τ.lookup x with
      | none => rfl
      | some b => rw [h₁, h₂] at hl; exact absurd hl Option.not_rel_none_some
    | some a =>
      cases h₂ : τ.lookup x with
      | none => rw [h₁, h₂] at hl; exact absurd hl Option.not_rel_some_none
      | some b => rw [h₁, h₂] at hl; exact (Option.rel_some_iff.mp hl).1
  | expr m cs ih =>
    intro u h
    obtain ⟨m', cs', rfl⟩ := erase_eq_expr h
    simp only [MAtom.erase_expr, Atom.expression.injEq] at h
    simp only [MAtom.subst_expr, MAtom.erase_expr, List.map_map, Atom.expression.injEq]
    exact forall₂_map_eq (forall₂_imp_mem_left (S := fun a b => a ∈ cs ∧ a.erase = b.erase)
      (forall₂_of_map_eq h) fun a b ha hab => ⟨ha, hab⟩) fun a b hab => ih a hab.1 b hab.2

theorem marksIn_subst {σ : Subst} (hσ : ∀ x a, σ.lookup x = some a → MarksIn Stab a) :
    ∀ t : MAtom, MarksIn Stab t → MarksIn Stab (t.subst σ) := by
  intro t
  induction t using MAtom.induction with
  | var x =>
    intro _
    simp only [MAtom.subst_var]
    cases h : σ.lookup x with
    | none => exact fun a ha => by simp at ha
    | some a => exact hσ x a h
  | expr m cs ih =>
    intro ht
    obtain ⟨hroot, hcs⟩ := marksIn_expr_iff.mp ht
    simp only [MAtom.subst_expr]
    refine marksIn_expr_iff.mpr ⟨fun hm => ?_, fun c hc => ?_⟩
    · simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hm
      have hid : cs.map (MAtom.subst σ) = cs := by
        conv => rhs; rw [← List.map_id cs]
        refine List.map_congr_left fun c hc => MAtom.subst_of_not_touched σ c ?_
        simp only [List.any_eq_false, Bool.not_eq_true] at hm
        exact hm.2 c hc
      rw [hid]
      exact hroot hm.1
    · obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.mp hc
      exact ih c₀ hc₀ (hcs c₀ hc₀)
  | _ => intro h; simpa using h

theorem Sim.subst {σ τ : Subst} (hστ : SubstSim Stab σ τ) {t u : MAtom} (h : Sim Stab t u) :
    Sim Stab (t.subst σ) (u.subst τ) :=
  ⟨erase_subst_congr hστ t u h.1, marksIn_subst (fun _ _ hx => hστ.marksIn hx) t h.2⟩

theorem matchAtom_sim :
    ∀ (p : Atom) {t u : MAtom} {σ τ : Subst}, Sim Stab t u → SubstSim Stab σ τ →
      Option.Rel (SubstSim Stab) (matchAtom p t σ) (matchAtom p u τ) := by
  intro p
  induction p using atomInduction with
  | var x =>
    intro t u σ τ htu hστ
    have hl := hστ.lookup x
    simp only [matchAtom]
    cases h₁ : σ.lookup x with
    | none =>
      cases h₂ : τ.lookup x with
      | none => exact .some (.cons ⟨rfl, htu⟩ hστ)
      | some b => rw [h₁, h₂] at hl; exact absurd hl Option.not_rel_none_some
    | some a =>
      cases h₂ : τ.lookup x with
      | none => rw [h₁, h₂] at hl; exact absurd hl Option.not_rel_some_none
      | some b =>
        rw [h₁, h₂] at hl
        have hab := (Option.rel_some_iff.mp hl).1
        simp only
        rw [hab, htu.1]
        split
        · exact .some hστ
        · exact .none
  | symbol s =>
    intro t u σ τ htu hστ
    cases t with
    | symbol s' =>
      rw [erase_eq_symbol htu.1]
      simp only [matchAtom]
      split
      · exact .some hστ
      · exact .none
    | var _ => rw [erase_eq_var htu.1]; exact .none
    | grounded _ => rw [erase_eq_grounded htu.1]; exact .none
    | expr m cs =>
      obtain ⟨m', cs', rfl⟩ := erase_eq_expr htu.1
      exact .none
  | grounded g =>
    intro t u σ τ htu hστ
    cases t with
    | grounded g' =>
      rw [erase_eq_grounded htu.1]
      simp only [matchAtom]
      split
      · exact .some hστ
      · exact .none
    | var _ => rw [erase_eq_var htu.1]; exact .none
    | symbol _ => rw [erase_eq_symbol htu.1]; exact .none
    | expr m cs =>
      obtain ⟨m', cs', rfl⟩ := erase_eq_expr htu.1
      exact .none
  | expression ps ih =>
    intro t u σ τ htu hστ
    cases t with
    | expr m ts =>
      obtain ⟨m', us, rfl⟩ := erase_eq_expr htu.1
      have hts := htu.children
      simp only [matchAtom]
      clear htu
      induction ps generalizing ts us σ τ with
      | nil =>
        cases hts with
        | nil => exact .some hστ
        | cons _ _ => exact .none
      | cons p ps ihps =>
        cases hts with
        | nil => exact .none
        | @cons t u ts us htu hrest =>
          simp only [matchList]
          have hp := ih p List.mem_cons_self htu hστ
          cases h₁ : matchAtom p t σ with
          | none =>
            cases h₂ : matchAtom p u τ with
            | none => exact .none
            | some _ => rw [h₁, h₂] at hp; exact absurd hp Option.not_rel_none_some
          | some σ' =>
            cases h₂ : matchAtom p u τ with
            | none => rw [h₁, h₂] at hp; exact absurd hp Option.not_rel_some_none
            | some τ' =>
              rw [h₁, h₂] at hp
              have hστ' := Option.rel_some_iff.mp hp
              apply ihps (fun q hq => ih q (List.mem_cons_of_mem _ hq)) <;> assumption
    | var _ => rw [erase_eq_var htu.1]; exact .none
    | symbol _ => rw [erase_eq_symbol htu.1]; exact .none
    | grounded _ => rw [erase_eq_grounded htu.1]; exact .none

theorem dedupAux_sim : ∀ (seen : List Atom) {R S : List MAtom}, List.Forall₂ (Sim Stab) R S →
    List.Forall₂ (Sim Stab) (dedupAux seen R) (dedupAux seen S)
  | _, _, _, .nil => .nil
  | seen, r :: _, s :: _, .cons hrs hrest => by
    simp only [dedupAux, hrs.1]
    split
    · exact dedupAux_sim seen hrest
    · exact .cons hrs (dedupAux_sim _ hrest)

theorem dedupErase_sim {R S : List MAtom} (h : List.Forall₂ (Sim Stab) R S) :
    List.Forall₂ (Sim Stab) (dedupErase R) (dedupErase S) :=
  dedupAux_sim [] h

/-! ## Modes depend on erasures -/

theorem paramModes_congr (P : Program) {t u : MAtom} (h : t.erase = u.erase) :
    P.paramModes t = P.paramModes u := by
  cases t with
  | symbol s => rw [erase_eq_symbol h]
  | var x => rw [erase_eq_var h]
  | grounded g => rw [erase_eq_grounded h]
  | expr m cs => obtain ⟨m', cs', rfl⟩ := erase_eq_expr h; rfl

theorem resultMode_congr (P : Program) {t u : MAtom} (h : t.erase = u.erase) :
    P.resultMode t = P.resultMode u := by
  cases t with
  | symbol s => rw [erase_eq_symbol h]
  | var x => rw [erase_eq_var h]
  | grounded g => rw [erase_eq_grounded h]
  | expr m cs => obtain ⟨m', cs', rfl⟩ := erase_eq_expr h; rfl

theorem elementModes_congr (P : Program) {cs cs' : List MAtom}
    (h : List.Forall₂ (Sim Stab) cs cs') : P.elementModes cs = P.elementModes cs' := by
  cases h with
  | nil => rfl
  | cons hc _ => simp [Program.elementModes, paramModes_congr P hc.1]

theorem callResultMode_congr (P : Program) {cs cs' : List MAtom}
    (h : List.Forall₂ (Sim Stab) cs cs') : P.callResultMode cs = P.callResultMode cs' := by
  cases h with
  | nil => rfl
  | cons hc _ => simp [Program.callResultMode, resultMode_congr P hc.1]

theorem withModes_sim : ∀ (ms : List ParamMode) {cs cs' : List MAtom},
    List.Forall₂ (Sim Stab) cs cs' →
      List.Forall₂ (fun p q => p.1 = q.1 ∧ Sim Stab p.2 q.2) (withModes ms cs) (withModes ms cs')
  | _, _, _, .nil => by simp [withModes]
  | [], _, _, .cons hc hrest => .cons ⟨rfl, hc⟩ (withModes_sim [] hrest)
  | _ :: ms, _, _, .cons hc hrest => .cons ⟨rfl, hc⟩ (withModes_sim ms hrest)

/-! ## The step relation -/

/-- The relation on demand trees used throughout: related questions are `Sim`,
related replies are lists of `Sim` terms. -/
abbrev StepRel (Stab : Atom → Prop) {α β : Type} (A : α → β → Prop) :
    Demand α → Demand β → Prop :=
  Demand.Rel (Sim Stab) (List.Forall₂ (Sim Stab)) A

theorem needDone_sim {t u : MAtom} (h : Sim Stab t u) :
    StepRel Stab (List.Forall₂ (Sim Stab)) (.need t .done) (.need u .done) :=
  .need h fun _ _ hrs => .done hrs

theorem argDemand_sim {p q : ParamMode × MAtom} (h : p.1 = q.1 ∧ Sim Stab p.2 q.2) :
    StepRel Stab (List.Forall₂ (Sim Stab)) (argDemand p) (argDemand q) := by
  obtain ⟨mode, t⟩ := p
  obtain ⟨mode', u⟩ := q
  obtain ⟨rfl, htu⟩ := h
  cases mode with
  | value => exact needDone_sim htu
  | atom => exact .done (.cons htu .nil)

theorem needDone_below {t u : MAtom} (h : Sim Stab t u) :
    StepRel Stab (List.Forall₂ (SimBelow Stab)) (.need t .done) (.need u .done) :=
  .need h fun _ _ hrs => .done (hrs.imp fun _ _ hab => hab.simBelow)

theorem simBelow_expr {cs cs' : List MAtom} (b b' : Bool) (h : List.Forall₂ (Sim Stab) cs cs') :
    SimBelow Stab (.expr b cs) (.expr b' cs') := by
  refine ⟨?_, fun a ha => ?_⟩
  · simp only [MAtom.erase_expr, Atom.expression.injEq]
    exact forall₂_map_eq h fun _ _ hab => hab.1
  · simp only [MAtom.childMarks, List.mem_flatMap] at ha
    obtain ⟨c, hc, ha⟩ := ha
    obtain ⟨c', -, hcc'⟩ := forall₂_exists_left h hc
    exact hcc'.2 a ha

theorem SimBelow.markIf (a : Atom) {t u : MAtom} (h : SimBelow Stab t u) :
    SimBelow Stab (t.markIf a) (u.markIf a) :=
  ⟨by simp [h.1], fun b hb => h.2 b (by rwa [MAtom.childMarks_markIf] at hb)⟩

theorem returnDemand_sim (mode : ResultMode) {call call' r r' : MAtom}
    (hcall : SimBelow Stab call call') (hr : Sim Stab r r') :
    StepRel Stab (List.Forall₂ (SimBelow Stab)) (returnDemand mode call r)
      (returnDemand mode call' r') := by
  simp only [returnDemand, hr.1]
  split
  · exact .done (.cons hcall .nil)
  · cases mode with
    | evaluate => exact needDone_below hr
    | atom => exact .done (.cons hr.simBelow .nil)

theorem replies_sim (P : Program) {vs ws : List MAtom} (h : List.Forall₂ (Sim Stab) vs ws) :
    List.Forall₂ (Sim Stab) (P.replies (.expr false vs)) (P.replies (.expr false ws)) := by
  unfold Program.replies
  refine forall₂_filterMap fun eq _ => ?_
  have hm := matchAtom_sim (Stab := Stab) eq.1 (sim_expr_false false h) (σ := []) (τ := []) .nil
  cases h₁ : matchAtom eq.1 (.expr false vs) [] with
  | none =>
    cases h₂ : matchAtom eq.1 (.expr false ws) [] with
    | none => exact .none
    | some _ => rw [h₁, h₂] at hm; exact absurd hm Option.not_rel_none_some
  | some σ =>
    cases h₂ : matchAtom eq.1 (.expr false ws) [] with
    | none => rw [h₁, h₂] at hm; exact absurd hm Option.not_rel_some_none
    | some τ =>
      rw [h₁, h₂] at hm
      exact .some ((Sim.code eq.2).subst (Option.rel_some_iff.mp hm))

theorem queryDemand_sim (P : Program) (ms ms' : Bool) {vs ws : List MAtom}
    (h : List.Forall₂ (Sim Stab) vs ws) :
    StepRel Stab (List.Forall₂ (SimBelow Stab)) (P.queryDemand ms vs) (P.queryDemand ms' ws) := by
  have hrep := replies_sim P h
  have hcall := simBelow_expr ms ms' h
  unfold Program.queryDemand
  rw [callResultMode_congr P h]
  generalize P.replies (.expr false vs) = R at hrep ⊢
  generalize P.replies (.expr false ws) = S at hrep ⊢
  cases hrep with
  | nil => exact .done (.cons hcall .nil)
  | cons hrs hrest =>
    exact Demand.Rel.forEach (.cons hrs hrest) fun r r' hr => returnDemand_sim _ hcall hr

theorem primDemand_sim (p : Prim) {args args' : List MAtom}
    (h : List.Forall₂ (Sim Stab) args args') {fb fb' : Demand (List MAtom)}
    (hfb : StepRel Stab (List.Forall₂ (SimBelow Stab)) fb fb') :
    StepRel Stab (List.Forall₂ (SimBelow Stab)) (primDemand p args fb)
      (primDemand p args' fb') := by
  cases p with
  | carAtom =>
    match args, args', h with
    | [], [], .nil => exact hfb
    | [a], [a'], .cons ha .nil =>
      cases a with
      | expr m es =>
        obtain ⟨m', es', rfl⟩ := erase_eq_expr ha.1
        cases hes : ha.children with
        | nil => exact hfb
        | cons hc _ => exact .done (.cons hc.simBelow .nil)
      | symbol _ => rw [erase_eq_symbol ha.1]; exact hfb
      | var _ => rw [erase_eq_var ha.1]; exact hfb
      | grounded _ => rw [erase_eq_grounded ha.1]; exact hfb
    | _ :: _ :: _, _ :: _ :: _, .cons _ (.cons _ _) => exact hfb
  | collapse =>
    match args, args', h with
    | [], [], .nil => exact hfb
    | [_], [_], .cons ha .nil =>
      exact .need ha fun r s hrs => .done (.cons (sim_expr_false false hrs).simBelow .nil)
    | _ :: _ :: _, _ :: _ :: _, .cons _ (.cons _ _) => exact hfb
  | unique =>
    match args, args', h with
    | [], [], .nil => exact hfb
    | [_], [_], .cons ha .nil =>
      exact .need ha fun r s hrs =>
        Demand.Rel.forEach (dedupErase_sim hrs) fun _ _ hab => needDone_below hab
    | _ :: _ :: _, _ :: _ :: _, .cons _ (.cons _ _) => exact hfb
  | superpose =>
    match args, args', h with
    | [], [], .nil => exact hfb
    | [a], [a'], .cons ha .nil =>
      cases a with
      | expr m es =>
        obtain ⟨m', es', rfl⟩ := erase_eq_expr ha.1
        exact Demand.Rel.forEach ha.children fun _ _ hab => needDone_below hab
      | symbol _ => rw [erase_eq_symbol ha.1]; exact hfb
      | var _ => rw [erase_eq_var ha.1]; exact hfb
      | grounded _ => rw [erase_eq_grounded ha.1]; exact hfb
    | a :: _ :: _, a' :: _ :: _, .cons _ (.cons _ _) =>
      cases a <;> cases a' <;> exact hfb
  | let_ =>
    match args, args', h with
    | [], [], .nil => exact hfb
    | [_], [_], .cons _ .nil => exact hfb
    | [_, _], [_, _], .cons _ (.cons _ .nil) => exact hfb
    | [pat, val, body], [pat', val', body'], .cons hpat (.cons hval (.cons hbody .nil)) =>
      simp only [primDemand]
      rw [hpat.1]
      have hm := matchAtom_sim (Stab := Stab) pat'.erase hval (σ := []) (τ := []) .nil
      cases h₁ : matchAtom pat'.erase val [] with
      | none =>
        cases h₂ : matchAtom pat'.erase val' [] with
        | none => exact .done .nil
        | some _ => rw [h₁, h₂] at hm; exact absurd hm Option.not_rel_none_some
      | some σ =>
        cases h₂ : matchAtom pat'.erase val' [] with
        | none => rw [h₁, h₂] at hm; exact absurd hm Option.not_rel_some_none
        | some τ =>
          rw [h₁, h₂] at hm
          exact needDone_below (hbody.subst (Option.rel_some_iff.mp hm))
    | _ :: _ :: _ :: _ :: _, _ :: _ :: _ :: _ :: _, .cons _ (.cons _ (.cons _ (.cons _ _))) =>
      exact hfb

theorem callDemand_sim (P : Program) (ms ms' : Bool) {vs ws : List MAtom}
    (h : List.Forall₂ (Sim Stab) vs ws) :
    StepRel Stab (List.Forall₂ (SimBelow Stab)) (P.callDemand ms vs) (P.callDemand ms' ws) := by
  have hq := queryDemand_sim P ms ms' h
  cases h with
  | nil => exact hq
  | @cons c c' args args' hc hrest =>
    cases c with
    | symbol f =>
      rw [erase_eq_symbol hc.1] at hq ⊢
      simp only [Program.callDemand]
      cases hp : Prim.ofName f with
      | none => exact hq
      | some p => exact primDemand_sim p hrest hq
    | var x => rw [erase_eq_var hc.1] at hq ⊢; exact hq
    | grounded g => rw [erase_eq_grounded hc.1] at hq ⊢; exact hq
    | expr m cs =>
      obtain ⟨m', cs', rfl⟩ := erase_eq_expr hc.1
      exact hq

theorem argsDemand_sim (P : Program) {cs cs' : List MAtom} (h : List.Forall₂ (Sim Stab) cs cs') :
    StepRel Stab (List.Forall₂ (List.Forall₂ (Sim Stab))) (P.argsDemand cs) (P.argsDemand cs') := by
  unfold Program.argsDemand
  rw [elementModes_congr P h]
  exact Demand.Rel.traverse (withModes_sim _ h) fun _ _ hpq => argDemand_sim hpq

/-- **Step simulation.** When the mark is not read, one step of two terms with
equal erasures, under any two rules, asks `Sim` questions and, given `Sim`
replies, returns results that are `Sim` except possibly at their root marks,
which the rules set differently. -/
theorem openStep_sim (P : Program) (r₁ r₂ : ReturnRule) {t u : MAtom} (h : Sim Stab t u) :
    StepRel Stab (List.Forall₂ (SimBelow Stab)) (openStep r₁ P t) (openStep r₂ P u) := by
  cases t with
  | expr m cs =>
    obtain ⟨m', cs', rfl⟩ := erase_eq_expr h.1
    simp only [openStep]
    refine Demand.Rel.map (A := List.Forall₂ (SimBelow Stab)) ?_ fun R S hRS => ?_
    · exact (argsDemand_sim P h.children).bind fun rss rss' hr =>
        Demand.Rel.forEach (forall₂_combos hr) fun _ _ hvw => callDemand_sim P _ _ hvw
    · rw [show (MAtom.expr m' cs').erase = (MAtom.expr m cs).erase from h.1.symm]
      exact List.forall₂_map_left_iff.mpr (List.forall₂_map_right_iff.mpr
        (hRS.imp fun _ _ hab => hab.markIf _))
  | symbol s =>
    rw [erase_eq_symbol h.1]
    exact .done (.cons ⟨rfl, fun a ha => by simp [MAtom.childMarks] at ha⟩ .nil)
  | var x =>
    rw [erase_eq_var h.1]
    exact .done (.cons ⟨rfl, fun a ha => by simp [MAtom.childMarks] at ha⟩ .nil)
  | grounded g =>
    rw [erase_eq_grounded h.1]
    exact .done (.cons ⟨rfl, fun a ha => by simp [MAtom.childMarks] at ha⟩ .nil)

end Mettapedia.Languages.MeTTa.HE.EvaluatedValues

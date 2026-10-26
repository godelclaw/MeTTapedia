import Mettapedia.Languages.MeTTa.DeclarationFaces.Controls
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.Computation

/-!
# The deterministic lane computes the same values on admitted declarations

The tree has a second semantics of authored equations: deterministic equation programs
(`GSLT.LanguageDef.DeterministicEquations`), evaluated call by value with the **first** equation
whose left side matches, and with a call that no equation matches **failing**. MeTTa's evaluation
takes **every** matching equation, and keeps an unmatched call as inert data. The two differ on
overlapping equations (first match against all matches) and at missing cases (failure against inert
data).

On admitted declarations the differences vanish: non-overlap leaves at most one equation to match,
and coverage leaves no closed sorted call unmatched. **The deterministic evaluator computes MeTTa's
normal form** (`Admitted.deterministic_evaluates`): every closed sorted term evaluates, with enough
fuel, to the translation of its normal form, and by the lane's own determinism to nothing else.

The translation (`dt`) writes every application, constants included, as an expression headed by its
symbol; a constructor is then a call that no equation and no primitive handles, which the lane
returns as data. Matching agrees exactly with MeTTa's matching, binding for binding (`matchTerm_dt`).
The lane's execution correspondence with compiled MeTTa code
(`DeterministicEquations.MeTTaExecutionCorrespondence`) then applies to admitted declarations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.DeclarationFaces

open Tm Relation
open Mettapedia.Logic.Relation (IsNormal accessible_transitiveClosure)
open Mettapedia.GSLT.LanguageDef

universe u

variable {S : Type u} [DecidableEq S] (name : S → String)

/-! ## Translation -/

mutual
/-- **The lane's term of a term**: an application is an expression headed by its symbol. -/
def dt : Tm S → DeterministicEquations.Term
  | .var x => .var x
  | .app f args => .expr (.sym (name f) :: dtList args)
/-- The lane's terms of a list of terms. -/
def dtList : List (Tm S) → List DeterministicEquations.Term
  | [] => []
  | a :: as => dt a :: dtList as
end

omit [DecidableEq S] in
theorem dtList_eq (args : List (Tm S)) : dtList name args = args.map (dt name) := by
  induction args with
  | nil => rfl
  | cons a as ih => simp [dtList, ih]

omit [DecidableEq S] in
theorem dt_app (f : S) (args : List (Tm S)) :
    dt name (.app f args) = .expr (.sym (name f) :: args.map (dt name)) := by
  simp [dt, dtList_eq]

/-- Bindings translated value by value. -/
def mapB (b : List (String × Tm S)) : DeterministicEquations.Env := b.map fun pr => (pr.1, dt name pr.2)

variable {name}

mutual
/-- **Matching agrees exactly**: the lane's matcher on translations returns the translated bindings
of MeTTa's matcher. -/
theorem matchTerm_dt (inj : Function.Injective name) : ∀ p t : Tm S,
    DeterministicEquations.matchTerm (dt name p) (dt name t) = (matchTm p t).map (mapB name)
  | .var x, t => by simp [dt, DeterministicEquations.matchTerm, matchTm, mapB]
  | .app f ps, .var y => by simp [dt, DeterministicEquations.matchTerm, matchTm]
  | .app f ps, .app g ts => by
      simp only [dt, DeterministicEquations.matchTerm, DeterministicEquations.matchTerms, matchTm]
      by_cases same : f = g
      · subst same
        simp only [if_true]
        rw [matchTerms_dt inj ps ts]
        cases matchList ps ts with
        | none => rfl
        | some b => rfl
      · have : name f ≠ name g := fun h => same (inj h)
        simp [same, this]
/-- Matching of lists agrees exactly. -/
theorem matchTerms_dt (inj : Function.Injective name) : ∀ ps ts : List (Tm S),
    DeterministicEquations.matchTerms (dtList name ps) (dtList name ts) =
      (matchList ps ts).map (mapB name)
  | [], [] => by simp [dtList, DeterministicEquations.matchTerms, matchList, mapB]
  | [], t :: ts => by simp [dtList, DeterministicEquations.matchTerms, matchList]
  | p :: ps, [] => by simp [dtList, DeterministicEquations.matchTerms, matchList]
  | p :: ps, t :: ts => by
      simp only [dtList, DeterministicEquations.matchTerms, matchList]
      rw [matchTerm_dt inj p t, matchTerms_dt inj ps ts]
      cases matchTm p t with
      | none => rfl
      | some a =>
          cases matchList ps ts with
          | none => rfl
          | some b => simp [mapB]
end

omit [DecidableEq S] in
theorem lookup_mapB {b : List (String × Tm S)} {x : String} (hx : x ∈ b.map Prod.fst) :
    (mapB name b).lookup x = some (dt name (lookup b x)) := by
  induction b with
  | nil => simp at hx
  | cons pr rest ih =>
      obtain ⟨key, value⟩ := pr
      by_cases same : key = x
      · subst same
        simp [mapB, DeterministicEquations.Env.lookup, lookup]
      · simp only [List.map_cons, List.mem_cons] at hx
        rcases hx with h | h
        · exact absurd h.symm same
        · have hb : (key == x) = false := by simp [same]
          have := ih h
          simp only [mapB, DeterministicEquations.Env.lookup, List.map_cons, List.find?_cons, hb]
            at this ⊢
          simpa [lookup, same] using this

variable (name)

/-- **The lane's equation of an equation.** -/
def dEq (e : Equation S) : DeterministicEquations.Equation :=
  match e.lhs with
  | .app f ps => ⟨"equation", name f, ps.map (dt name), dt name e.rhs⟩
  | .var x => ⟨"equation", "", [.var x], dt name e.rhs⟩

/-- **The lane's program of a program.** -/
def dP (P : Program S) : DeterministicEquations.Program := P.map (dEq name)

/-- The host with no primitive. -/
def noHost : DeterministicEquations.Host := ⟨fun _ _ => .unhandled⟩

variable {name}

omit [DecidableEq S] in
theorem dEq_app {e : Equation S} {f : S} {ps : List (Tm S)} (hl : e.lhs = .app f ps) :
    dEq name e = ⟨"equation", name f, ps.map (dt name), dt name e.rhs⟩ := by
  simp [dEq, hl]

/-! ## Selection and definitions -/

/-- **The lane selects the matching equation**: in a linear, non-overlapping, headed program, the
first equation whose translated left side matches is the one MeTTa's call uses. -/
theorem select_dP (inj : Function.Injective name) {P : Program S} (headed : P.Headed)
    (linear : P.LeftLinear) (nonOverlap : P.NonOverlapping) {e : Equation S} (he : e ∈ P)
    {f : S} {ps vs : List (Tm S)} (hl : e.lhs = .app f ps) {b : List (String × Tm S)}
    (hm : matchTm e.lhs (.app f vs) = some b) :
    (dP name P).select (name f) (vs.map (dt name)) = some (dEq name e, mapB name b) := by
  have instanceOf : ∀ {e' : Equation S}, e' ∈ P → ∀ {b'}, matchTm e'.lhs (.app f vs) = some b' →
      e'.lhs.subst (lookup b') = .app f vs := by
    intro e' he' b' hm'
    obtain ⟨keys, inst⟩ := matchTm_sound e'.lhs _ b' hm'
    exact inst _ (agrees_lookup (by rw [keys]; exact linear e' he'))
  unfold dP DeterministicEquations.Program.select
  induction P with
  | nil => cases he
  | cons e₀ rest ih =>
      simp only [List.map_cons, List.findSome?_cons]
      by_cases same : e₀ = e
      · subst same
        rw [dEq_app hl]
        have hlen : ps.length = vs.length := by
          have := instanceOf he hm
          rw [hl, subst_app] at this
          simpa using congrArg List.length (Tm.app.inj this).2
        simp only [List.length_map, hlen, and_self, if_true]
        rw [← dtList_eq, ← dtList_eq, matchTerms_dt inj]
        rw [hl] at hm
        simp only [matchTm, if_true] at hm
        simp [hm]
      · have he' : e ∈ rest := by
          rcases List.mem_cons.mp he with h | h
          · exact absurd h.symm same
          · exact h
        have headNone : (if (dEq name e₀).head = name f ∧ (dEq name e₀).params.length = (vs.map (dt name)).length
            then (DeterministicEquations.matchTerms (dEq name e₀).params (vs.map (dt name))).map
              (fun σ => (dEq name e₀, σ))
            else none) = none := by
          obtain ⟨g, qs, hl₀⟩ := headed e₀ List.mem_cons_self
          rw [dEq_app hl₀]
          split
          · rename_i cond
            obtain ⟨hname, _⟩ := cond
            have hg : g = f := inj hname
            subst hg
            rw [← dtList_eq, ← dtList_eq, matchTerms_dt inj]
            cases hq : matchList qs vs with
            | none => rfl
            | some b₀ =>
                exfalso
                have hm₀ : matchTm e₀.lhs (.app g vs) = some b₀ := by
                  rw [hl₀]; simpa [matchTm] using hq
                have i₀ := instanceOf List.mem_cons_self hm₀
                have i₁ := instanceOf he hm
                exact (List.pairwise_cons.mp nonOverlap).1 e he' _ _ (i₀.trans i₁.symm)
          · rfl
        rw [headNone]
        exact ih (fun e' h => headed e' (List.mem_cons_of_mem _ h))
          (fun e' h => linear e' (List.mem_cons_of_mem _ h)) (List.pairwise_cons.mp nonOverlap).2 he'
          (fun {_} h' {_} hm' => instanceOf (List.mem_cons_of_mem _ h') hm')

omit [DecidableEq S] in
theorem definesAt_dP {P : Program S} {e : Equation S} (he : e ∈ P) {f : S} {ps : List (Tm S)}
    (hl : e.lhs = .app f ps) : (dP name P).definesAt (name f) ps.length = true := by
  simp only [dP, DeterministicEquations.Program.definesAt, List.any_map, List.any_eq_true,
    Function.comp_apply, Bool.and_eq_true, beq_iff_eq]
  exact ⟨e, he, by simp [dEq_app hl]⟩

omit [DecidableEq S] in
theorem defines_dP_false (inj : Function.Injective name) {P : Program S} (headed : P.Headed) {c : S}
    (undefined : ¬ P.Defines c) : (dP name P).defines (name c) = false := by
  simp only [dP, DeterministicEquations.Program.defines, List.any_map, List.any_eq_false,
    Function.comp_apply, beq_iff_eq]
  intro e he same
  obtain ⟨f, ps, hl⟩ := headed e he
  rw [dEq_app hl] at same
  have := inj same
  subst this
  exact undefined ⟨e, he, by simp [hl, head?]⟩

/-! ## Bindings are parts of the matched term -/

mutual
theorem matchTm_values_parts : ∀ (p t : Tm S) (b : List (String × Tm S)), matchTm p t = some b →
    ∀ pr ∈ b, ReflTransGen Sub t pr.2
  | .var x, t, b, h, pr, hpr => by
      simp only [matchTm, Option.some.injEq] at h
      subst h
      simp only [List.mem_singleton] at hpr
      subst hpr
      exact .refl
  | .app f ps, .app g ts, b, h, pr, hpr => by
      simp only [matchTm] at h
      split at h
      · rename_i same
        subst same
        obtain ⟨t, ht, parts⟩ := matchList_values_parts ps ts b h pr hpr
        exact ReflTransGen.head (Sub.arg f ht) parts
      · cases h
  | .app _ _, .var _, b, h, _, _ => by simp [matchTm] at h
theorem matchList_values_parts : ∀ (ps ts : List (Tm S)) (b : List (String × Tm S)),
    matchList ps ts = some b → ∀ pr ∈ b, ∃ t ∈ ts, ReflTransGen Sub t pr.2
  | [], [], b, h, pr, hpr => by
      simp only [matchList, Option.some.injEq] at h
      subst h
      cases hpr
  | p :: ps, t :: ts, b, h, pr, hpr => by
      simp only [matchList] at h
      split at h
      · rename_i first rest hFirst hRest
        simp only [Option.some.injEq] at h
        subst h
        rcases List.mem_append.mp hpr with inFirst | inRest
        · exact ⟨t, List.mem_cons_self, matchTm_values_parts p t first hFirst pr inFirst⟩
        · obtain ⟨t', ht', parts⟩ := matchList_values_parts ps ts rest hRest pr inRest
          exact ⟨t', List.mem_cons_of_mem t ht', parts⟩
      · cases h
  | [], _ :: _, b, h, _, _ => by simp [matchList] at h
  | _ :: _, [], b, h, _, _ => by simp [matchList] at h
end

omit [DecidableEq S] in
/-- A part of a normal term is normal. -/
theorem normal_of_subStar {P : Program S} {whole part : Tm S} (normal : IsNormal (Step P) whole)
    (inside : ReflTransGen Sub whole part) : IsNormal (Step P) part := by
  intro target step
  obtain ⟨whole', wholeStep, _⟩ := step.lift_subStar inside
  exact normal _ wholeStep

omit [DecidableEq S] in
/-- A bound variable is bound to the value of some binding. -/
theorem lookup_mem {b : List (String × Tm S)} {x : String} (hx : x ∈ b.map Prod.fst) :
    ∃ pr ∈ b, lookup b x = pr.2 := by
  induction b with
  | nil => simp at hx
  | cons pr rest ih =>
      obtain ⟨key, value⟩ := pr
      by_cases same : key = x
      · exact ⟨(key, value), List.mem_cons_self, by simp [lookup, same]⟩
      · simp only [List.map_cons, List.mem_cons] at hx
        rcases hx with h | h
        · exact absurd h.symm same
        · obtain ⟨q, hq, hval⟩ := ih h
          exact ⟨q, List.mem_cons_of_mem _ hq, by simp [lookup, same, hval]⟩

theorem forall₂_map_of_forall {α β γ : Type*} {R : β → γ → Prop} (f : α → β) (g : α → γ) :
    ∀ l : List α, (∀ a ∈ l, R (f a) (g a)) → List.Forall₂ R (l.map f) (l.map g)
  | [], _ => .nil
  | a :: l, h => .cons (h a List.mem_cons_self)
      (forall₂_map_of_forall f g l fun b hb => h b (List.mem_cons_of_mem a hb))

omit [DecidableEq S] in
/-- The arguments of a sorted application have sorts. -/
theorem HasSort.arg_typed {sig : Signature S} {Γ : Ctx} {h : S} {args : List (Tm S)} {τ : Sort'}
    (typed : HasSort sig Γ (.app h args) τ) : ∀ a ∈ args, ∃ τa, HasSort sig Γ a τa := by
  intro a ha
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  rcases HasSort.app_inv typed with ⟨d, _, fields, _, θ, _, len, typedArgs⟩ |
      ⟨fd, _, _, θ, _, len, typedArgs⟩
  · exact ⟨_, typedArgs i hi (by simpa [← len] using hi)⟩
  · exact ⟨_, typedArgs i hi (by simpa [← len] using hi)⟩

omit [DecidableEq S] in
/-- A chain of steps, read as a chain of steps and parts from its end to its start. -/
theorem below_of_transGen_step {P : Program S} {a c : Tm S} (h : TransGen (Step P) a c) :
    TransGen (Below P) c a := by
  induction h with
  | single step => exact .single (Or.inl step)
  | tail _ step ih => exact TransGen.head (Or.inl step) ih

/-! ## The deterministic lane computes the normal form -/

namespace Admitted

variable {sig : Signature S} {P : Program S}

/-- The lane's evaluation of a term with variables bound to normal forms, for the closed sorted
instance it stands for. -/
theorem deterministic_evaluates_gen (adm : Admitted sig P) (inj : Function.Injective name)
    (ordinary : ∀ f : S, name f ≠ "let" ∧ name f ≠ "metta-nullary") :
    ∀ (u : Tm S), Acc (TransGen (Below P)) u → ∀ {τ : Sort'}, HasSort sig Ctx.empty u τ →
      ∀ (t : Tm S) (b : List (String × Tm S)), t.subst (lookup b) = u →
        (∀ x ∈ t.vars, x ∈ b.map Prod.fst) → (∀ pr ∈ b, IsNormal (Step P) pr.2) →
        DeterministicEquations.Evaluates (dP name P) noHost (mapB name b) (dt name t)
          (dt name (adm.normalForm u)) := by
  intro u acc
  induction acc with
  | intro u _ ih =>
  intro τ typed t b hu covered normalB
  cases t with
  | var x =>
      simp only [subst_var] at hu
      subst hu
      have hx := covered x (by simp)
      obtain ⟨pr, hpr, hval⟩ := lookup_mem hx
      have normalX : IsNormal (Step P) (lookup b x) := hval ▸ normalB pr hpr
      rw [adm.normalForm_of_normal normalX]
      exact DeterministicEquations.Evaluates.variable (lookup_mapB hx)
  | app h args =>
      rw [subst_app] at hu
      subst hu
      have notSpecial : ¬ DeterministicEquations.Special (name h) (args.map (dt name)) := by
        simp only [DeterministicEquations.Special, not_or, not_and]
        exact ⟨fun e => absurd e (ordinary h).1, fun e => absurd e (ordinary h).2⟩
      let vsT := args.map fun a => adm.normalForm (a.subst (lookup b))
      have argTyped := HasSort.arg_typed typed
      have children : List.Forall₂ (DeterministicEquations.Evaluates (dP name P) noHost (mapB name b))
          (args.map (dt name)) (vsT.map (dt name)) := by
        simp only [vsT, List.map_map]
        apply forall₂_map_of_forall
        intro a ha
        obtain ⟨τa, typedA⟩ := argTyped _ (List.mem_map_of_mem ha)
        exact ih _ (.single (Or.inr (Sub.arg h (List.mem_map_of_mem ha)))) typedA a b rfl
          (fun x hx => covered x (by simpa using ⟨a, ha, hx⟩)) normalB
      have toCall : ReflTransGen (Step P) (.app h (args.map (Tm.subst (lookup b)))) (.app h vsT) :=
        steps_args h _ _ (by simp [vsT]) fun i hi hj => by
          simpa [vsT] using (adm.normalForm_spec (args[i]'(by simpa using hi) |>.subst (lookup b))).1
      have vsNormal : ∀ v ∈ vsT, IsNormal (Step P) v := by
        intro v hv
        obtain ⟨a, _, rfl⟩ := List.mem_map.mp hv
        exact (adm.normalForm_spec _).2
      by_cases defined : P.Defines h
      · have typedCall := HasSort.steps adm.wellFormed adm.typed adm.rightBound toCall typed
        rcases HasSort.app_inv typedCall with ⟨d, hd, fields, hc, _, _, _⟩ |
            ⟨fd, hfd, hname, θ, rfl, len, typedArgs⟩
        · exact absurd defined (Signature.not_defines_ctor adm.wellFormed adm.typed
            (Signature.mem_ctorNames.mpr ⟨d, hd, fields, hc⟩))
        · have values : Pointwise sig.IsValueOf vsT (fd.args.map (Tm.subst θ)) := by
            refine ⟨len, fun i hi hj => ⟨?_, typedArgs i hi hj⟩⟩
            have hi' : i < args.length := by simpa [vsT] using hi
            obtain ⟨τa, typedA⟩ := argTyped _ (List.mem_map_of_mem (List.getElem_mem hi'))
            have hv : vsT[i] = adm.normalForm ((args[i]'hi').subst (lookup b)) := by simp [vsT]
            rw [hv]
            exact (adm.normalForm_value typedA).1
          obtain ⟨e, he, σ', hσ'⟩ := adm.covers fd hfd θ vsT values
          obtain ⟨f, ps, hl⟩ := adm.typed.headed e he
          have hf : f = h := by
            have := hσ'
            rw [hl, subst_app] at this
            exact (Tm.app.inj this).1.trans hname
          subst hf
          rw [hname] at hσ'
          obtain ⟨b', hm, _⟩ := matchTm_complete e.lhs σ'
          rw [hσ'] at hm
          obtain ⟨keys', inst⟩ := matchTm_sound e.lhs _ b' hm
          have lhsInst : e.lhs.subst (lookup b') = .app f vsT :=
            inst _ (agrees_lookup (by rw [keys']; exact adm.leftLinear e he))
          have rootStep : RootStep P (.app f vsT) (e.rhs.subst (lookup b')) := by
            rw [← lhsInst]; exact .rule _ he
          have chainSteps : TransGen (Step P) (.app f (args.map (Tm.subst (lookup b))))
              (e.rhs.subst (lookup b')) := TransGen.tail' toCall (.root rootStep)
          have chain : TransGen (Below P) (e.rhs.subst (lookup b'))
              (.app f (args.map (Tm.subst (lookup b)))) := below_of_transGen_step chainSteps
          have typedRhs := HasSort.rootStep adm.wellFormed adm.typed adm.rightBound rootStep typedCall
          have normalB' : ∀ pr ∈ b', IsNormal (Step P) pr.2 := by
            intro pr hpr
            rw [hl] at hm
            simp only [matchTm, if_true] at hm
            obtain ⟨v, hv, parts⟩ := matchList_values_parts ps vsT b' hm pr hpr
            exact normal_of_subStar (vsNormal v hv) parts
          have body := ih _ chain typedRhs e.rhs b' rfl
            (fun x hx => by rw [keys']; exact adm.rightBound e he x hx) normalB'
          have sameNF : adm.normalForm (e.rhs.subst (lookup b')) =
              adm.normalForm (.app f (args.map (Tm.subst (lookup b)))) :=
            (adm.normalForm_of_steps (toCall.tail (Step.root rootStep))).symm
          rw [← sameNF, dt_app]
          have hlen : ps.length = vsT.length := by
            have := lhsInst
            rw [hl, subst_app] at this
            simpa using congrArg List.length (Tm.app.inj this).2
          refine DeterministicEquations.Evaluates.call notSpecial children ?_
          refine DeterministicEquations.Applies.equation (equation := dEq name e)
            (environment := mapB name b') ?_ ?_ ?_
          · rw [List.length_map, ← hlen]; exact definesAt_dP he hl
          · exact select_dP inj adm.typed.headed adm.leftLinear adm.nonOverlapping he hl hm
          · rw [dEq_app hl]; exact body
      · have nf : adm.normalForm (.app h (args.map (Tm.subst (lookup b)))) = .app h vsT :=
          (adm.normalForm_unique ⟨toCall, adm.app_normal defined vsNormal⟩).symm
        rw [nf, dt_app, dt_app]
        exact DeterministicEquations.Evaluates.call notSpecial children
          (DeterministicEquations.Applies.constructor (defines_dP_false inj adm.typed.headed defined) rfl)

/-- **The deterministic lane computes MeTTa's normal form** on every closed sorted term of an admitted
declaration, for an injective naming that avoids the lane's two special forms; by the lane's
determinism it computes nothing else. -/
theorem deterministic_evaluates (adm : Admitted sig P) (inj : Function.Injective name)
    (ordinary : ∀ f : S, name f ≠ "let" ∧ name f ≠ "metta-nullary") {t : Tm S} {τ : Sort'}
    (typed : HasSort sig Ctx.empty t τ) :
    DeterministicEquations.Evaluates (dP name P) noHost [] (dt name t) (dt name (adm.normalForm t)) := by
  have := adm.deterministic_evaluates_gen inj ordinary t
    (accessible_transitiveClosure (acc_below (adm.stronglyNormalizing t))) typed t []
    (by rw [subst_closed (HasSort.closed_of_empty typed)])
    (fun x hx => by rw [HasSort.closed_of_empty typed] at hx; cases hx) (by simp)
  simpa [mapB] using this

end Admitted

/-! ## Controls: outside admission the lanes disagree -/

namespace Controls

open Mettapedia.Languages.MeTTa.DeclarationFaces.Controls (num predPartial overlapping addProgram add_adm)

/-- **Positive**: the deterministic lane computes `(add 2 3)` to `5`, as the general theorem says. -/
example : DeterministicEquations.eval (dP id addProgram) noHost 20 []
    (dt id (.app "add" [num 2, num 3])) = .value (dt id (num 5)) := by rfl

/-- **Negative (missing case)**: the deterministic lane fails on `(pred Z)`, while MeTTa keeps it as
inert data. -/
example : DeterministicEquations.eval (dP id predPartial) noHost 10 [] (dt id (.app "pred" [num 0])) =
      .failure ∧
    evalTm predPartial 10 (.app "pred" [num 0]) = some [.app "pred" [num 0]] :=
  ⟨by rfl, by decide⟩

/-- **Negative (overlap)**: the deterministic lane takes the first equation and answers `Z`; MeTTa takes
both and answers `Z` and `(S Z)`. -/
example : DeterministicEquations.eval (dP id overlapping) noHost 10 [] (dt id (.app "f" [num 0])) =
      .value (dt id (num 0)) ∧
    evalTm overlapping 10 (.app "f" [num 0]) = some [num 0, num 1] :=
  ⟨by rfl, by decide⟩

end Controls

end Mettapedia.Languages.MeTTa.DeclarationFaces

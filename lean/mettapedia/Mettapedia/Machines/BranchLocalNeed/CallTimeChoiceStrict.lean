import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceSource

/-!
# Strict positions

In call-by-push-value terms an operation that inspects a value needs a value,
not a suspension. The core makes two kinds of strict position explicit:

* **activation** (`strictRun`): the operand is forced to weak head normal form
  before it is executed; `force_okWhnf` states that forcing never yields an
  implicit suspension, so activation always dispatches on a value;
* **primitive arguments** (`strictPrim`, built by `normChain`): every argument is
  normalized before the primitive sees it; `normalized_okNormal` states that a
  normalized value contains no implicit suspension, and `strictPrim_normal`
  that every answer of a strict primitive is the primitive applied to such
  normal forms.

The source translation uses these forms in every profile
(`Expr.toCore_activate`, `Expr.toCore_prim`). A primitive applied to an equation
parameter therefore receives the parameter's normal form, as it would receive
the normal form of the same term written directly or bound by `let`; it never
receives the parameter's suspension.

Strictness is a property of the position, not of a binding discipline. How an
argument is bound (evaluated first, suspended and shared, or suspended and
rerun) and how a variable is resolved to its binder (the variable map `r` of
the translation, which a lexical or an implicit scoping discipline determines)
only change the computations that produce the arguments; `strictPrim_normal` and
`strictRun_forces` hold for all such computations. `prim_normal_every_binding`
and `activate_whnf_every_binding` state the consequence for every profile and
every variable map.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BranchLocalNeed.CallTimeChoice

/-- Every value answer in a result list satisfies `p`. -/
def OkAll (p : Val Nat → Prop) (L : List Result) : Prop :=
  ∀ r ∈ L, ∀ w, r.1 = .ok w → p w

theorem OkAll.nil (p : Val Nat → Prop) : OkAll p [] := by
  intro r hr; simp at hr

theorem OkAll.append {p : Val Nat → Prop} {L₁ L₂ : List Result} (h₁ : OkAll p L₁)
    (h₂ : OkAll p L₂) : OkAll p (L₁ ++ L₂) := by
  intro r hr w hw
  rcases List.mem_append.mp hr with hr | hr
  · exact h₁ r hr w hw
  · exact h₂ r hr w hw

theorem OkAll.cons_stop {p : Val Nat → Prop} {o : Outcome} {σ : Store} {L : List Result}
    (ho : o.isOk = false) (h : OkAll p L) : OkAll p ((o, σ) :: L) := by
  intro r hr w hw
  rcases List.mem_cons.mp hr with rfl | hr
  · simp only at hw; subst hw; simp [Outcome.isOk] at ho
  · exact h r hr w hw

theorem OkAll.singleton {p : Val Nat → Prop} {w : Val Nat} {σ : Store} (h : p w) :
    OkAll p [(.ok w, σ)] := by
  intro r hr w' hw
  simp only [List.mem_singleton] at hr
  subst hr
  simp only [Outcome.ok.injEq] at hw
  subst hw
  exact h

/-! ## Forcing yields weak head normal forms -/

/-- What forcing, committing and following guarantee. -/
def WhnfMotive : Goal → List Result → Prop
  | .forceVal _ _, L => OkAll (fun w => w.isCell = false) L
  | .commitK _ _, L => OkAll (fun w => w.isCell = false) L
  | .followK _, L => OkAll (fun w => w.isCell = false) L
  | .eval _ _ M, L => ∀ v, M = .force v → OkAll (fun w => w.isCell = false) L
  | _, _ => True

theorem whnf_invariant (P : Program) :
    ∀ g L, Derives P g L → WhnfMotive g L := by
  intro g L h
  induction h with
  | force _ ih =>
      intro v' _
      exact ih
  | forceWhnf hw => exact OkAll.singleton hw
  | forceDone _ _ _ ih => exact ih
  | forceBlackhole _ _ => exact OkAll.cons_stop rfl (OkAll.nil _)
  | forcePending _ _ _ _ _ ih => exact ih
  | forceThunk _ _ _ _ ih => exact ih
  | commitNil => exact OkAll.nil _
  | commitOk _ _ ih₁ ih₂ => exact OkAll.append ih₁ ih₂
  | commitStop hs _ ih => exact OkAll.cons_stop hs ih
  | followNil => exact OkAll.nil _
  | followOk _ _ ih₁ ih₂ => exact OkAll.append ih₁ ih₂
  | followStop hs _ ih => exact OkAll.cons_stop hs ih
  | ret => intro v h; cases h
  | seq => intro v h; cases h
  | need => intro v h; cases h
  | delay => intro v h; cases h
  | caseConHit => intro v h; cases h
  | caseConMiss => intro v h; cases h
  | caseAppHit => intro v h; cases h
  | caseAppMiss => intro v h; cases h
  | call => intro v h; cases h
  | callNone => intro v h; cases h
  | callRule => intro v h; cases h
  | callRuleNone => intro v h; cases h
  | choose => intro v h; cases h
  | fail => intro v h; cases h
  | emit => intro v h; cases h
  | quote => intro v h; cases h
  | runCode => intro v h; cases h
  | runOther => intro v h; cases h
  | prim => intro v h; cases h
  | altsNil => trivial
  | altsCons => trivial
  | seqKNil => trivial
  | seqKOk => trivial
  | seqKStop => trivial

/-- **Forcing never yields an implicit suspension.** Every value answer of
`force` is a symbol, an application or a code value. -/
theorem force_okWhnf {P : Program} {σ : Store} {v : Val Nat} {L : List Result}
    (h : Derives P (.forceVal σ v) L) : OkAll (fun w => w.isCell = false) L :=
  whnf_invariant P _ _ h

/-! ## Consumer normalization yields normal forms -/

/-- The pieces of the normalization body. -/
def normK : Comp := .caseApp (.var 0) (.seq (.call normHead [.var 0])
  (.seq (.call normHead [.var 2]) (.ret (.app (.var 1) (.var 0))))) (.ret (.var 0))
def normApp : Comp := .seq (.call normHead [.var 0])
  (.seq (.call normHead [.var 2]) (.ret (.app (.var 1) (.var 0))))
def normApp2 : Comp := .seq (.call normHead [.var 2]) (.ret (.app (.var 1) (.var 0)))
def normApp3 : Comp := .ret (.app (.var 1) (.var 0))

theorem normBody_eq : normBody = .seq (.force (.var 0)) normK := rfl
theorem normK_eq : normK = .caseApp (.var 0) normApp (.ret (.var 0)) := rfl
theorem normApp_eq : normApp = .seq (.call normHead [.var 0]) normApp2 := rfl
theorem normApp2_eq : normApp2 = .seq (.call normHead [.var 2]) normApp3 := rfl

abbrev IsNormal (w : Val Nat) : Prop := w.noSusp = true
abbrev IsWhnf (w : Val Nat) : Prop := w.isCell = false

/-- What the normalization program guarantees at each of its stages. -/
def NormMotive : Goal → List Result → Prop
  | .eval _ ρ M, L =>
      (∀ a, M = .call normHead [a] → OkAll IsNormal L) ∧
      (M = normBody → OkAll IsNormal L) ∧
      (M = normK → (∃ w ρ', ρ = w :: ρ' ∧ IsWhnf w) → OkAll IsNormal L) ∧
      (M = normApp → OkAll IsNormal L) ∧
      (M = normApp2 → (∃ f ρ', ρ = f :: ρ' ∧ IsNormal f) → OkAll IsNormal L) ∧
      (M = normApp3 → (∃ x f ρ', ρ = x :: f :: ρ' ∧ IsNormal x ∧ IsNormal f) →
        OkAll IsNormal L) ∧
      (∀ v, M = .force v → OkAll IsWhnf L)
  | .seqK n ρ rs, L =>
      (n = normK → OkAll IsWhnf rs → OkAll IsNormal L) ∧
      (n = normApp2 → OkAll IsNormal rs → OkAll IsNormal L) ∧
      (n = normApp3 → (∃ f ρ', ρ = f :: ρ' ∧ IsNormal f) → OkAll IsNormal rs →
        OkAll IsNormal L)
  | .alts _ bs, L => (∀ b ∈ bs, b.1 = normBody) → OkAll IsNormal L
  | .forceVal _ _, L => OkAll IsWhnf L
  | .commitK _ _, L => OkAll IsWhnf L
  | .followK _, L => OkAll IsWhnf L

theorem normK_ne_normBody : normK ≠ normBody := by decide
theorem normApp_ne_normBody : normApp ≠ normBody := by decide
theorem normApp2_ne_normBody : normApp2 ≠ normBody := by decide

theorem norm_invariant (P : Program) (hP : candidates P normHead 1 = [normRule]) :
    ∀ g L, Derives P g L → NormMotive g L := by
  intro g L h
  induction h with
  | @ret σ ρ v =>
      refine ⟨fun a h => (by cases h), fun h => (by cases h), fun h => (by cases h),
        fun h => (by cases h), fun h => (by cases h), ?_, fun v h => (by cases h)⟩
      intro hv ⟨x, f, ρ', hρ, hx, hf⟩
      cases hv
      subst hρ
      apply OkAll.singleton
      show Val.noSusp (.app f x) = true
      simp only [Val.noSusp, Bool.and_eq_true]
      exact ⟨hf, hx⟩
  | @seq σ ρ m n L₁ L h₁ h₂ ih₁ ih₂ =>
      refine ⟨fun a h => (by cases h), ?_, fun h => (by cases h), ?_, ?_, fun h => (by cases h),
        fun v h => (by cases h)⟩
      · intro hM
        rw [normBody_eq] at hM
        cases hM
        exact ih₂.1 rfl (ih₁.2.2.2.2.2.2 _ rfl)
      · intro hM
        rw [normApp_eq] at hM
        cases hM
        exact ih₂.2.1 rfl (ih₁.1 _ rfl)
      · intro hM hρ
        rw [normApp2_eq] at hM
        cases hM
        exact ih₂.2.2 rfl hρ (ih₁.1 _ rfl)
  | need => exact ⟨fun a h => (by cases h), fun h => (by cases h), fun h => (by cases h),
      fun h => (by cases h), fun h => (by cases h), fun h => (by cases h), fun v h => (by cases h)⟩
  | delay => exact ⟨fun a h => (by cases h), fun h => (by cases h), fun h => (by cases h),
      fun h => (by cases h), fun h => (by cases h), fun h => (by cases h), fun v h => (by cases h)⟩
  | force _ ih =>
      refine ⟨fun a h => (by cases h), fun h => (by cases h), fun h => (by cases h),
        fun h => (by cases h), fun h => (by cases h), fun h => (by cases h), ?_⟩
      intro v _
      exact ih
  | caseConHit => exact ⟨fun a h => (by cases h), fun h => (by cases h), fun h => (by cases h),
      fun h => (by cases h), fun h => (by cases h), fun h => (by cases h), fun v h => (by cases h)⟩
  | caseConMiss => exact ⟨fun a h => (by cases h), fun h => (by cases h), fun h => (by cases h),
      fun h => (by cases h), fun h => (by cases h), fun h => (by cases h), fun v h => (by cases h)⟩
  | @caseAppHit σ ρ v hit miss f x L hm _ ih =>
      refine ⟨fun a h => (by cases h), fun h => (by cases h), ?_, fun h => (by cases h),
        fun h => (by cases h), fun h => (by cases h), fun v h => (by cases h)⟩
      intro hM _
      rw [normK_eq] at hM
      cases hM
      exact ih.2.2.2.1 rfl
  | @caseAppMiss σ ρ v hit miss L hm hmiss ih =>
      refine ⟨fun a h => (by cases h), fun h => (by cases h), ?_, fun h => (by cases h),
        fun h => (by cases h), fun h => (by cases h), fun v h => (by cases h)⟩
      intro hM ⟨w, ρ', hρ, hw⟩
      rw [normK_eq] at hM
      cases hM
      subst hρ
      cases hmiss
      apply OkAll.singleton
      have hw0 : (VExp.var 0).eval (w :: ρ') = w := rfl
      rw [hw0] at hm
      show Val.noSusp w = true
      cases w with
      | sym c => rfl
      | app f x => simp [Val.matchApp] at hm
      | need ℓ => simp [IsWhnf, Val.isCell] at hw
      | thunk ℓ => simp [IsWhnf, Val.isCell] at hw
      | code ℓ => rfl
  | @call σ ρ f args L hc _ ih =>
      refine ⟨?_, fun h => (by cases h), fun h => (by cases h), fun h => (by cases h),
        fun h => (by cases h), fun h => (by cases h), fun v h => (by cases h)⟩
      intro a hM
      cases hM
      apply ih
      intro b hb
      simp only [List.length_singleton, hP, List.map_cons, List.map_nil,
        List.mem_singleton] at hb
      subst hb
      rfl
  | @callNone σ ρ f args hc =>
      refine ⟨?_, fun h => (by cases h), fun h => (by cases h), fun h => (by cases h),
        fun h => (by cases h), fun h => (by cases h), fun v h => (by cases h)⟩
      intro a hM
      cases hM
      simp [hP] at hc
  | callRule => exact ⟨fun a h => (by cases h), fun h => (by cases h), fun h => (by cases h),
      fun h => (by cases h), fun h => (by cases h), fun h => (by cases h), fun v h => (by cases h)⟩
  | callRuleNone => exact ⟨fun a h => (by cases h), fun h => (by cases h), fun h => (by cases h),
      fun h => (by cases h), fun h => (by cases h), fun h => (by cases h), fun v h => (by cases h)⟩
  | choose => exact ⟨fun a h => (by cases h), fun h => (by cases h), fun h => (by cases h),
      fun h => (by cases h), fun h => (by cases h), fun h => (by cases h), fun v h => (by cases h)⟩
  | fail => exact ⟨fun a h => (by cases h), fun h => (by cases h), fun h => (by cases h),
      fun h => (by cases h), fun h => (by cases h), fun h => (by cases h), fun v h => (by cases h)⟩
  | emit => exact ⟨fun a h => (by cases h), fun h => (by cases h), fun h => (by cases h),
      fun h => (by cases h), fun h => (by cases h), fun h => (by cases h), fun v h => (by cases h)⟩
  | quote => exact ⟨fun a h => (by cases h), fun h => (by cases h), fun h => (by cases h),
      fun h => (by cases h), fun h => (by cases h), fun h => (by cases h), fun v h => (by cases h)⟩
  | runCode => exact ⟨fun a h => (by cases h), fun h => (by cases h), fun h => (by cases h),
      fun h => (by cases h), fun h => (by cases h), fun h => (by cases h), fun v h => (by cases h)⟩
  | runOther => exact ⟨fun a h => (by cases h), fun h => (by cases h), fun h => (by cases h),
      fun h => (by cases h), fun h => (by cases h), fun h => (by cases h), fun v h => (by cases h)⟩
  | prim => exact ⟨fun a h => (by cases h), fun h => (by cases h), fun h => (by cases h),
      fun h => (by cases h), fun h => (by cases h), fun h => (by cases h), fun v h => (by cases h)⟩
  | altsNil => intro _; exact OkAll.nil _
  | @altsCons σ m ρ bs L₁ L₂ _ _ ih₁ ih₂ =>
      intro hb
      have hm : m = normBody := hb (m, ρ) (by simp)
      subst hm
      exact OkAll.append (ih₁.2.1 rfl) (ih₂ fun b hb' => hb b (by simp [hb']))
  | seqKNil => exact ⟨fun _ _ => OkAll.nil _, fun _ _ => OkAll.nil _, fun _ _ _ => OkAll.nil _⟩
  | @seqKOk n ρ w σ rs L₁ L₂ _ _ ih₁ ih₂ =>
      refine ⟨?_, ?_, ?_⟩
      · intro hn hrs
        subst hn
        have hw : IsWhnf w := hrs (.ok w, σ) List.mem_cons_self w rfl
        exact OkAll.append (ih₁.2.2.1 rfl ⟨w, ρ, rfl, hw⟩)
          (ih₂.1 rfl fun r hr => hrs r (by simp [hr]))
      · intro hn hrs
        subst hn
        have hw : IsNormal w := hrs (.ok w, σ) List.mem_cons_self w rfl
        exact OkAll.append (ih₁.2.2.2.2.1 rfl ⟨w, ρ, rfl, hw⟩)
          (ih₂.2.1 rfl fun r hr => hrs r (by simp [hr]))
      · intro hn ⟨f, ρ', hρ, hf⟩ hrs
        subst hn
        have hw : IsNormal w := hrs (.ok w, σ) List.mem_cons_self w rfl
        subst hρ
        exact OkAll.append (ih₁.2.2.2.2.2.1 rfl ⟨w, f, ρ', rfl, hw, hf⟩)
          (ih₂.2.2 rfl ⟨f, ρ', rfl, hf⟩ fun r hr => hrs r (by simp [hr]))
  | @seqKStop n ρ o σ rs L₂ hs _ ih =>
      refine ⟨?_, ?_, ?_⟩
      · intro hn hrs
        exact OkAll.cons_stop hs (ih.1 hn fun r hr => hrs r (by simp [hr]))
      · intro hn hrs
        exact OkAll.cons_stop hs (ih.2.1 hn fun r hr => hrs r (by simp [hr]))
      · intro hn hρ hrs
        exact OkAll.cons_stop hs (ih.2.2 hn hρ fun r hr => hrs r (by simp [hr]))
  | forceWhnf hw => exact OkAll.singleton hw
  | forceDone _ _ _ ih => exact ih
  | forceBlackhole _ _ => exact OkAll.cons_stop rfl (OkAll.nil _)
  | forcePending _ _ _ _ _ ih => exact ih
  | forceThunk _ _ _ _ ih => exact ih
  | commitNil => exact OkAll.nil _
  | commitOk _ _ ih₁ ih₂ => exact OkAll.append ih₁ ih₂
  | commitStop hs _ ih => exact OkAll.cons_stop hs ih
  | followNil => exact OkAll.nil _
  | followOk _ _ ih₁ ih₂ => exact OkAll.append ih₁ ih₂
  | followStop hs _ ih => exact OkAll.cons_stop hs ih

/-- The normalization program is the only rule of its head in an observed
program whose own rules avoid that head. -/
theorem candidates_observed_normHead (P : Program) (hP : ∀ r ∈ P, r.head ≠ normHead) :
    candidates (observed P) normHead 1 = [normRule] := by
  have hfilter : P.filter (fun r => r.head == normHead && r.arity == 1) = [] := by
    rw [List.filter_eq_nil_iff]
    intro r hr
    simp [hP r hr]
  simp [candidates, observed, normRule, hfilter]

/-- **Normalization yields normal forms.** Every value answer of a normalizing
strict position contains no implicit suspension. -/
theorem normalized_okNormal {P : Program} (hP : candidates P normHead 1 = [normRule])
    {σ : Store} {ρ : List (Val Nat)} {m : Comp} {L : List Result}
    (h : Derives P (.eval σ ρ (normalized m)) L) : OkAll IsNormal L := by
  cases h with
  | seq _ hk =>
      have key : ∀ (rs L : List Result),
          Derives P (.seqK (.call normHead [.var 0]) ρ rs) L → OkAll IsNormal L := by
        intro rs
        induction rs with
        | nil => intro L hL; cases hL; exact OkAll.nil _
        | cons r rest ih =>
            intro L hL
            cases hL with
            | seqKOk h₁ h₂ =>
                exact OkAll.append ((norm_invariant P hP _ _ h₁).1 _ rfl) (ih _ h₂)
            | seqKStop hs h₂ => exact OkAll.cons_stop hs (ih _ h₂)
      exact key _ _ hk

/-! ## Strict primitives -/

/-- A primitive applied, in a strict position, to argument computations. -/
def strictPrim (op : Prim) (ms : List Comp) : Comp :=
  normChain ms (fun k => .prim op (varsDesc k)) 0

theorem varsDesc_eval_normal {ρ : List (Val Nat)} {k : Nat}
    (h : ∀ i < k, IsNormal (ρ.getD i (.sym 0))) :
    ∀ n ∈ (varsDesc k).map (·.eval ρ), IsNormal n := by
  intro n hn
  simp only [varsDesc, List.map_map, List.mem_map, List.mem_reverse, List.mem_range,
    Function.comp_apply] at hn
  obtain ⟨i, hi, rfl⟩ := hn
  exact h i hi

theorem normChain_prim {P : Program} (hP : candidates P normHead 1 = [normRule]) (op : Prim) :
    ∀ (ms : List Comp) (done : Nat) (σ : Store) (ρ : List (Val Nat)) (L : List Result),
      (∀ i < done, IsNormal (ρ.getD i (.sym 0))) →
      Derives P (.eval σ ρ (normChain ms (fun k => .prim op (varsDesc k)) done)) L →
      ∀ r ∈ L, ∀ w, r.1 = .ok w →
        ∃ ns, (∀ n ∈ ns, IsNormal n) ∧ op.apply ns = some w := by
  intro ms
  induction ms with
  | nil =>
      intro done σ ρ L hρ h r hr w hw
      cases h
      simp only [List.mem_singleton] at hr
      subst hr
      refine ⟨(varsDesc done).map (·.eval ρ), varsDesc_eval_normal hρ, ?_⟩
      simp only [primOutcome] at hw
      cases happ : op.apply ((varsDesc done).map (·.eval ρ)) with
      | none => rw [happ] at hw; cases hw
      | some v => rw [happ] at hw; cases hw; rfl
  | cons m ms ih =>
      intro done σ ρ L hρ h
      cases h with
      | @seq _ _ _ _ L₁ _ h₁ h₂ =>
          have hnorm := normalized_okNormal hP h₁
          have key : ∀ (rs L : List Result), OkAll IsNormal rs →
              Derives P (.seqK (normChain ms (fun k => .prim op (varsDesc k)) (done + 1)) ρ rs) L →
              ∀ r ∈ L, ∀ w, r.1 = .ok w →
                ∃ ns, (∀ n ∈ ns, IsNormal n) ∧ op.apply ns = some w := by
            intro rs
            induction rs with
            | nil => intro L _ hL; cases hL; simp
            | cons r rest ihr =>
                intro L hrs hL
                cases hL with
                | @seqKOk _ _ w' σ' _ La Lb ha hb =>
                    intro r hr w hw
                    rcases List.mem_append.mp hr with hr | hr
                    · have hw' : IsNormal w' := hrs (.ok w', σ') List.mem_cons_self w' rfl
                      refine ih (done + 1) σ' (w' :: ρ) La ?_ ha r hr w hw
                      intro i hi
                      cases i with
                      | zero => simpa using hw'
                      | succ i => simpa using hρ i (by omega)
                    · exact ihr Lb (fun r' hr' => hrs r' (by simp [hr'])) hb r hr w hw
                | seqKStop hs hb =>
                    intro r hr w hw
                    rcases List.mem_cons.mp hr with rfl | hr
                    · simp only at hw; subst hw; simp [Outcome.isOk] at hs
                    · exact ihr _ (fun r' hr' => hrs r' (by simp [hr'])) hb r hr w hw
          exact key L₁ L hnorm h₂

/-- **A strict primitive sees only normal forms.** Every value answer of a
primitive in a strict position is the primitive applied to argument values
that contain no implicit suspension. -/
theorem strictPrim_normal {P : Program} (hP : candidates P normHead 1 = [normRule])
    (op : Prim) (ms : List Comp) {σ : Store} {ρ : List (Val Nat)} {L : List Result}
    (h : Derives P (.eval σ ρ (strictPrim op ms)) L) :
    ∀ r ∈ L, ∀ w, r.1 = .ok w → ∃ ns, (∀ n ∈ ns, IsNormal n) ∧ op.apply ns = some w :=
  normChain_prim hP op ms 0 σ ρ L (fun i hi => absurd hi (Nat.not_lt_zero i)) h

/-! ## Strict activation -/

/-- **Strict activation dispatches on a weak head normal form.** The value that
`run` receives in `strictRun m` is a result of forcing, hence never an
implicit suspension. -/
theorem strictRun_forces {P : Program} {σ : Store} {ρ : List (Val Nat)} {m : Comp}
    {L : List Result} (h : Derives P (.eval σ ρ (strictRun m)) L) :
    ∃ L₁, Derives P (.eval σ ρ m) L₁ ∧
      Derives P (.seqK (.seq (.force (.var 0)) (.run (.var 0))) ρ L₁) L ∧
      ∀ r ∈ L₁, ∀ w σ', r = (.ok w, σ') →
        ∀ L', Derives P (.eval σ' (w :: ρ) (.force (.var 0))) L' →
          OkAll IsWhnf L' := by
  cases h with
  | @seq _ _ _ _ L₁ _ h₁ h₂ =>
      refine ⟨L₁, h₁, h₂, ?_⟩
      intro r _ w σ' _ L' hL'
      cases hL' with
      | force hf => exact force_okWhnf hf

/-! ## The source translation uses the strict forms -/

theorem Args.toCoreStrict_eq' (p : Profile) (r : Nat → Nat) (op : Prim) :
    ∀ (args : Args) (done : Nat),
      Args.toCoreStrict p r done args (fun k => .prim op (varsDesc k)) =
        normChain (args.strictComps p r done) (fun k => .prim op (varsDesc k)) done
  | .nil, _ => rfl
  | .cons a rest, done => by
      simp only [Args.toCoreStrict, Args.strictComps, normChain,
        Args.toCoreStrict_eq' p r op rest (done + 1)]

/-- In every profile, a primitive call translates to a strict primitive. -/
theorem Expr.toCore_prim (p : Profile) (r : Nat → Nat) (op : Prim) (args : Args) :
    (Expr.prim op args).toCore p r = strictPrim op (args.strictComps p r 0) := by
  simp only [Expr.toCore, strictPrim, Args.toCoreStrict_eq']

/-- In every profile, an activation translates to a strict activation. -/
theorem Expr.toCore_activate (p : Profile) (r : Nat → Nat) (e : Expr) :
    (Expr.activate e).toCore p r = strictRun (e.toCore p r) := by
  simp only [Expr.toCore]

/-! ## Every binding discipline -/

/-- **A primitive sees normal forms under every binding discipline.** For every
argument-passing profile and every variable map, every value answer of a
primitive call is the primitive applied to argument values that contain no
implicit suspension. In particular no primitive ever receives a memoized or an
ordinary suspension, whether its argument is written directly, bound to an
equation parameter or bound by `let`. -/
theorem prim_normal_every_binding (p : Profile) (r : Nat → Nat) {P : Program}
    (hP : candidates P normHead 1 = [normRule]) (op : Prim) (args : Args)
    {σ : Store} {ρ : List (Val Nat)} {L : List Result}
    (h : Derives P (.eval σ ρ ((Expr.prim op args).toCore p r)) L) :
    ∀ res ∈ L, ∀ w, res.1 = .ok w → ∃ ns, (∀ n ∈ ns, IsNormal n) ∧ op.apply ns = some w := by
  rw [Expr.toCore_prim] at h
  exact strictPrim_normal hP op _ h

/-- **An activation dispatches on a weak head normal form under every binding
discipline.** For every profile and every variable map, the operand of an
activation is evaluated, then forced, and every forced value is a symbol, an
application or code: a code operand is executed, never left as a residual
because it is still suspended. -/
theorem activate_whnf_every_binding (p : Profile) (r : Nat → Nat) {P : Program} (e : Expr)
    {σ : Store} {ρ : List (Val Nat)} {L : List Result}
    (h : Derives P (.eval σ ρ ((Expr.activate e).toCore p r)) L) :
    ∃ L₁, Derives P (.eval σ ρ (e.toCore p r)) L₁ ∧
      Derives P (.seqK (.seq (.force (.var 0)) (.run (.var 0))) ρ L₁) L ∧
      ∀ res ∈ L₁, ∀ w σ', res = (.ok w, σ') →
        ∀ L', Derives P (.eval σ' (w :: ρ) (.force (.var 0))) L' → OkAll IsWhnf L' := by
  rw [Expr.toCore_activate] at h
  exact strictRun_forces h

end Mettapedia.Machines.BranchLocalNeed.CallTimeChoice

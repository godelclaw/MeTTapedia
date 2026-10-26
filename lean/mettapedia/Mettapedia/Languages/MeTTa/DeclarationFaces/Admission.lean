import Mettapedia.Languages.MeTTa.DeclarationFaces.Sorting
import Mettapedia.Languages.MeTTa.DeclarationFaces.LexicographicDescent

/-!
# The admission boundary: decidable checks for one declaration

`admit sig P` checks a signature and a program and either admits them or names the first
condition that fails, with the equation or function at fault (`Refusal`). Every check is a
computation, and each is proved sound (`admit_sound`): an admitted declaration has every property
the agreement theorems use (`Admitted`).

* **Signature** (`Signature.WellFormed`, decided directly): distinct names, no function is a
  constructor, field sorts within their datatype's parameters.
* **Typing and constructor discipline** (`checkEquation`): the left side is a declared function
  applied to constructor patterns; the sorts of the pattern variables are inferred from the
  function's argument sorts (`inferPattern`), and the right side is checked at the result sort
  (`checkTm`), instantiating polymorphic schemes by matching sorts.
* **Linearity** and **bound right sides**, decided directly.
* **Non-overlap** (`clash`): two left sides that differ at a position where both have a symbol have
  no common instance (`clash_sound`).
* **Coverage** (`coversRows`): the pattern matrix of each function is split on the constructors of
  each column's datatype, as in the compilation of pattern matching; a column whose rows are all
  variables is dropped. Sound for every instance of a polymorphic scheme (`coversRows_sound`).
* **Descent**: structural (`firstNotDescending`), with ranks from the order of the function
  declarations and the recursion position of each function found by search (`inferCertificate`);
  failing that, lexicographic (`firstNotLexDescending`), with an order of argument positions found by
  search (`inferLexCertificate`); failing that, lexicographic with ranks by strongly connected
  component, for mutual recursion (`sccOrder`). Each gives termination (`terminating_of_verdict`).

Positive and negative examples are in `DeclarationFaces.Controls`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.DeclarationFaces

open Tm

universe u

variable {S : Type u} [DecidableEq S] {sig : Signature S}

/-! ## Signatures, linearity, bound right sides -/

instance (sig : Signature S) : Decidable sig.WellFormed :=
  decidable_of_iff ((sig.data.map (·.name)).Nodup ∧ sig.ctorNames.Nodup ∧
      (sig.funs.map (·.name)).Nodup ∧ (∀ fd ∈ sig.funs, fd.name ∉ sig.ctorNames) ∧
      (∀ d ∈ sig.data, d.params.Nodup ∧ ∀ cf ∈ d.ctors, ∀ s ∈ cf.2, ∀ a ∈ s.vars, a ∈ d.params))
    ⟨fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩, fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩⟩

instance (t : Tm S) : Decidable t.Linear := inferInstanceAs (Decidable t.vars.Nodup)

/-! ## Non-overlap -/

mutual
/-- Two terms differ at a position where both have a symbol: they have no common instance. -/
def clash : Tm S → Tm S → Bool
  | .app f ps, .app g qs => !(decide (f = g)) || clashList ps qs
  | .var _, _ => false
  | .app _ _, .var _ => false
/-- Two lists of terms clash at some position, or have different lengths. -/
def clashList : List (Tm S) → List (Tm S) → Bool
  | [], [] => false
  | p :: ps, q :: qs => clash p q || clashList ps qs
  | [], _ :: _ => true
  | _ :: _, [] => true
end

mutual
/-- **Clashing terms have no common instance.** -/
theorem clash_sound : ∀ (p q : Tm S), clash p q = true →
    ∀ σ τ : String → Tm S, p.subst σ ≠ q.subst τ
  | .app f ps, .app g qs, h, σ, τ, same => by
      simp only [clash, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
      simp only [subst, app.injEq] at same
      rcases h with ne | inner
      · exact ne same.1
      · exact clashList_sound ps qs inner σ τ same.2
  | .var _, _, h, _, _, _ => by simp [clash] at h
  | .app _ _, .var _, h, _, _, _ => by simp [clash] at h
/-- Clashing lists have no common instance. -/
theorem clashList_sound : ∀ (ps qs : List (Tm S)), clashList ps qs = true →
    ∀ σ τ : String → Tm S, substList σ ps ≠ substList τ qs
  | [], [], h, _, _, _ => by simp [clashList] at h
  | p :: ps, q :: qs, h, σ, τ, same => by
      simp only [clashList, Bool.or_eq_true] at h
      simp only [substList, List.cons.injEq] at same
      rcases h with h | h
      · exact clash_sound p q h σ τ same.1
      · exact clashList_sound ps qs h σ τ same.2
  | [], _ :: _, _, _, _, same => by simp [substList] at same
  | _ :: _, [], _, _, _, same => by simp [substList] at same
end

/-- **No two equations have a common instance of their left sides.** The relation is irreflexive,
so an equation listed twice overlaps with itself. -/
def Program.NonOverlapping (P : Program S) : Prop :=
  P.Pairwise fun e e' => ∀ σ τ : String → Tm S, e.lhs.subst σ ≠ e'.lhs.subst τ

/-- The first pair of equations whose left sides do not clash. -/
def firstOverlap : Program S → Option (Equation S × Equation S)
  | [] => none
  | e :: rest =>
      match rest.find? (fun e' => !clash e.lhs e'.lhs) with
      | some e' => some (e, e')
      | none => firstOverlap rest

/-- Every two equations of the program have clashing left sides. -/
def Program.Clashing (P : Program S) : Prop := P.Pairwise fun e e' => clash e.lhs e'.lhs = true

theorem clashing_of_firstOverlap : ∀ {P : Program S}, firstOverlap P = none → P.Clashing := by
  intro P
  induction P with
  | nil => intro _; exact List.Pairwise.nil
  | cons e rest ih =>
      intro none'
      simp only [firstOverlap] at none'
      split at none'
      · cases none'
      · rename_i noClash
        refine List.Pairwise.cons (fun e' member => ?_) (ih none')
        have := List.find?_eq_none.mp noClash e' member
        simpa using this

theorem nonOverlapping_of_firstOverlap : ∀ {P : Program S}, firstOverlap P = none →
    P.NonOverlapping := by
  intro P
  induction P with
  | nil => intro _; exact List.Pairwise.nil
  | cons e rest ih =>
      intro none'
      simp only [firstOverlap] at none'
      split at none'
      · cases none'
      · rename_i noClash
        refine List.Pairwise.cons (fun e' member σ τ => ?_) (ih none')
        have := List.find?_eq_none.mp noClash e' member
        simp only [Bool.not_eq_true', Bool.not_eq_false] at this
        exact clash_sound _ _ (by simpa using this) σ τ

/-! ## Constructors of a sort -/

/-- Bind the parameters of a datatype to sorts. -/
def bindParams (params : List String) (sorts : List Sort') : String → Sort' :=
  Tm.lookup (params.zip sorts)

theorem bindParams_getElem : ∀ {params : List String} {sorts : List Sort'}, params.Nodup →
    ∀ (len : params.length = sorts.length) (j : Nat) (hj : j < params.length),
      bindParams params sorts params[j] = sorts[j]'(by rw [← len]; exact hj)
  | [], _, _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | p :: ps, [], _, len, _, _ => by simp at len
  | p :: ps, s :: ss, nodup, len, j, hj => by
      cases j with
      | zero => simp [bindParams, Tm.lookup]
      | succ k =>
          simp only [List.nodup_cons] at nodup
          have hk : k < ps.length := by simpa using hj
          have ne : p ≠ ps[k] := fun h => nodup.1 (h ▸ List.getElem_mem hk)
          simp only [bindParams, List.zip_cons_cons, Tm.lookup, ne, if_false, List.getElem_cons_succ]
          exact bindParams_getElem nodup.2 (by simpa using len) k (by simpa using hj)

theorem map_bindParams {params : List String} {sorts : List Sort'} (nodup : params.Nodup)
    (len : params.length = sorts.length) : params.map (fun a => bindParams params sorts a) = sorts := by
  apply List.ext_getElem (by simpa using len)
  intro j h₁ h₂
  simpa using bindParams_getElem nodup len j (by simpa using h₁)

/-- **The constructors of a sort**, with their field sorts at the sort's arguments; none at a sort
variable or a sort that is not a declared datatype at its number of parameters. -/
def Signature.ctorsAt (sig : Signature S) : Sort' → Option (List (S × List Sort'))
  | .var _ => none
  | .app D sorts =>
      match sig.data.find? (fun d => decide (d.name = D)) with
      | none => none
      | some d =>
          if d.params.length = sorts.length then
            some (d.ctors.map fun cf => (cf.1, cf.2.map (Tm.subst (bindParams d.params sorts))))
          else none

namespace Signature

omit [DecidableEq S] in
theorem ctorsAt_spec (wf : sig.WellFormed) {τ : Sort'} {cs : List (S × List Sort')}
    (h : sig.ctorsAt τ = some cs) : ∃ d ∈ sig.data, ∃ θ : String → Sort', τ = d.sort.subst θ ∧
      cs = d.ctors.map fun cf => (cf.1, cf.2.map (Tm.subst θ)) := by
  cases τ with
  | var _ => simp [ctorsAt] at h
  | app D sorts =>
      simp only [ctorsAt] at h
      split at h
      · cases h
      · rename_i d found
        split at h
        · rename_i len
          simp only [Option.some.injEq] at h
          obtain ⟨member, named⟩ := List.find?_some found |> fun hp => (⟨List.mem_of_find?_eq_some found, hp⟩ : _ ∧ _)
          simp only [decide_eq_true_eq] at named
          refine ⟨d, member, bindParams d.params sorts, ?_, h.symm⟩
          simp only [DataDecl.sort, subst_app, List.map_map, named]
          congr 1
          exact (map_bindParams (wf.params d member).1 len).symm
        · cases h

omit [DecidableEq S] in
/-- A value of an instance of a datatype sort is a constructor of that datatype applied to values
of its field sorts at the instance. -/
theorem ctorsAt_value (wf : sig.WellFormed) {τ : Sort'} {cs : List (S × List Sort')}
    (h : sig.ctorsAt τ = some cs) {Γ : Ctx} {θ : String → Sort'} {c : S} {us : List (Tm S)}
    (isCtor : c ∈ sig.ctorNames) (typed : HasSort sig Γ (.app c us) (τ.subst θ)) :
    ∃ cf ∈ cs, cf.1 = c ∧ Pointwise (HasSort sig Γ) us (cf.2.map (Tm.subst θ)) := by
  obtain ⟨d, hd, θ0, rfl, rfl⟩ := ctorsAt_spec wf h
  rcases HasSort.app_inv typed with ⟨d', hd', fields, hc, θ', hsort, len, typedArgs⟩ |
      ⟨fd, hfd, hname, _, _, _⟩
  · rw [subst_subst] at hsort
    have names : d.name = d'.name := by
      simp only [DataDecl.sort, subst_app, app.injEq] at hsort
      exact hsort.1
    obtain rfl := List.inj_on_of_nodup_map wf.dataNames hd hd' names
    have agree := DataDecl.sort_subst_inj d hsort
    refine ⟨(c, fields.map (Tm.subst θ0)), List.mem_map.mpr ⟨_, hc, rfl⟩, rfl, ?_⟩
    refine ⟨by simpa using len, fun i hi hj => ?_⟩
    have := typedArgs i hi (by simpa using hj)
    simp only [List.getElem_map] at this ⊢
    rw [subst_subst]
    convert this using 1
    apply subst_congr
    intro a ha
    exact agree a ((wf.params d hd).2 (c, fields) hc (fields[i]'(by simpa using hj)) (List.getElem_mem _) a ha)
  · exact absurd isCtor (hname ▸ wf.disjoint fd hfd)

end Signature

/-! ## Typing of equations -/

mutual
/-- Infer the sorts of the variables of a constructor pattern checked at a sort. -/
def inferPattern (sig : Signature S) : Tm S → Sort' → Option (List (String × Sort'))
  | .var x, τ => some [(x, τ)]
  | .app c qs, τ =>
      match sig.ctorsAt τ with
      | none => none
      | some cs =>
          match cs.find? (fun cf => decide (cf.1 = c)) with
          | none => none
          | some cf => inferPatterns sig qs cf.2
/-- Infer the sorts of the variables of a list of patterns checked at a list of sorts. -/
def inferPatterns (sig : Signature S) : List (Tm S) → List Sort' → Option (List (String × Sort'))
  | [], [] => some []
  | q :: qs, τ :: τs =>
      match inferPattern sig q τ, inferPatterns sig qs τs with
      | some a, some b => some (a ++ b)
      | _, _ => none
  | [], _ :: _ => none
  | _ :: _, [] => none
end

/-- The context of a list of bindings. -/
def ctxOf (bindings : List (String × Sort')) : Ctx := fun x =>
  (bindings.find? (fun pair => decide (pair.1 = x))).map (·.2)

theorem ctxOf_of_mem {bindings : List (String × Sort')} (distinct : (bindings.map Prod.fst).Nodup)
    {pair : String × Sort'} (member : pair ∈ bindings) : ctxOf bindings pair.1 = some pair.2 := by
  induction bindings with
  | nil => cases member
  | cons first rest ih =>
      simp only [List.map_cons, List.nodup_cons] at distinct
      rcases List.mem_cons.mp member with rfl | later
      · simp [ctxOf]
      · have ne : first.1 ≠ pair.1 := fun h => distinct.1 (h ▸ List.mem_map_of_mem later)
        have := ih distinct.2 later
        simp only [ctxOf, List.find?_cons, ne, decide_false] at this ⊢
        exact this

mutual
/-- **Pattern inference is sound**: the inferred bindings name exactly the pattern's variables,
and in every context that gives them their inferred sorts the pattern has the sort. -/
theorem inferPattern_sound (wf : sig.WellFormed) : ∀ (p : Tm S) (τ : Sort')
    (bindings : List (String × Sort')), inferPattern sig p τ = some bindings →
      bindings.map Prod.fst = p.vars ∧ IsPattern sig p ∧
        ∀ Γ : Ctx, (∀ pair ∈ bindings, Γ pair.1 = some pair.2) → HasSort sig Γ p τ
  | .var x, τ, bindings, h => by
      simp only [inferPattern, Option.some.injEq] at h
      subst h
      exact ⟨by simp, .var x, fun Γ hΓ => .var (by simpa using hΓ (x, τ) (by simp))⟩
  | .app c qs, τ, bindings, h => by
      simp only [inferPattern] at h
      split at h
      · cases h
      · rename_i cs hcs
        split at h
        · cases h
        · rename_i cf hcf
          obtain ⟨d, hd, θ, rfl, rfl⟩ := Signature.ctorsAt_spec wf hcs
          have cfMember := List.mem_of_find?_eq_some hcf
          have cfName : cf.1 = c := by simpa using List.find?_some hcf
          obtain ⟨⟨c', fields⟩, hc, rfl⟩ := List.mem_map.mp cfMember
          simp only at cfName
          subst cfName
          obtain ⟨keys, patterns, typed⟩ := inferPatterns_sound wf qs _ bindings h
          refine ⟨by simpa [varsList_eq] using keys,
            .ctor (Signature.mem_ctorNames.mpr ⟨d, hd, fields, hc⟩) patterns, fun Γ hΓ => ?_⟩
          obtain ⟨len, each⟩ := typed Γ hΓ
          exact .ctor θ hd hc (by simpa using len) fun i hi hj => by
            have := each i hi (by simpa using hj)
            simpa using this
/-- Inference for lists of patterns is sound. -/
theorem inferPatterns_sound (wf : sig.WellFormed) : ∀ (ps : List (Tm S)) (τs : List Sort')
    (bindings : List (String × Sort')), inferPatterns sig ps τs = some bindings →
      bindings.map Prod.fst = varsList ps ∧ (∀ p ∈ ps, IsPattern sig p) ∧
        ∀ Γ : Ctx, (∀ pair ∈ bindings, Γ pair.1 = some pair.2) → Pointwise (HasSort sig Γ) ps τs
  | [], [], bindings, h => by
      simp only [inferPatterns, Option.some.injEq] at h
      subst h
      exact ⟨rfl, by simp, fun _ _ => ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩⟩
  | q :: qs, τ :: τs, bindings, h => by
      simp only [inferPatterns] at h
      split at h
      · rename_i a b ha hb
        simp only [Option.some.injEq] at h
        subst h
        obtain ⟨keys₁, pattern₁, typed₁⟩ := inferPattern_sound wf q τ a ha
        obtain ⟨keys₂, pattern₂, typed₂⟩ := inferPatterns_sound wf qs τs b hb
        refine ⟨by simp [varsList, keys₁, keys₂], ?_, fun Γ hΓ => ?_⟩
        · intro p member
          rcases List.mem_cons.mp member with rfl | later
          · exact pattern₁
          · exact pattern₂ p later
        · have t₁ := typed₁ Γ fun pair m => hΓ pair (List.mem_append_left _ m)
          obtain ⟨len, each⟩ := typed₂ Γ fun pair m => hΓ pair (List.mem_append_right _ m)
          refine ⟨by simp [len], fun i hi hj => ?_⟩
          cases i with
          | zero => simpa using t₁
          | succ k => simpa using each k (by simpa using hi) (by simpa using hj)
      · cases h
  | [], _ :: _, bindings, h => by simp [inferPatterns] at h
  | _ :: _, [], bindings, h => by simp [inferPatterns] at h
end

/-- The instance of a function's scheme at a call: its result sort matched against the expected
sort, and its argument sorts matched against the sorts of variable arguments. -/
def callInstance (Γ : Ctx) (fd : FunDecl S) (args : List (Tm S)) (τ : Sort') : String → Sort' :=
  Tm.lookup (((matchTm fd.result τ).getD []) ++
    ((args.zip fd.args).filterMap fun pair =>
      match pair.1 with
      | .var x => (Γ x).bind fun τx => matchTm pair.2 τx
      | .app _ _ => none).flatten)

mutual
/-- **Check a term at a sort**: a variable by its context entry; an application of a constructor
of the sort's datatype by its field sorts; an application of a declared function at the instance
of its scheme that `callInstance` finds, verified. -/
def checkTm (sig : Signature S) (Γ : Ctx) : Tm S → Sort' → Bool
  | .var x, τ => decide (Γ x = some τ)
  | .app h args, τ =>
      (match sig.ctorsAt τ with
        | some cs =>
            match cs.find? (fun cf => decide (cf.1 = h)) with
            | some cf => checkList sig Γ args cf.2
            | none => false
        | none => false) ||
      (match sig.funs.find? (fun fd => decide (fd.name = h)) with
        | some fd =>
            decide (fd.result.subst (callInstance Γ fd args τ) = τ) &&
              checkList sig Γ args (fd.args.map (Tm.subst (callInstance Γ fd args τ)))
        | none => false)
/-- Check a list of terms at a list of sorts. -/
def checkList (sig : Signature S) (Γ : Ctx) : List (Tm S) → List Sort' → Bool
  | [], [] => true
  | t :: ts, τ :: τs => checkTm sig Γ t τ && checkList sig Γ ts τs
  | [], _ :: _ => false
  | _ :: _, [] => false
end

mutual
/-- **The check is sound.** -/
theorem checkTm_sound (wf : sig.WellFormed) (Γ : Ctx) : ∀ (t : Tm S) (τ : Sort'),
    checkTm sig Γ t τ = true → HasSort sig Γ t τ
  | .var x, τ, h => by simp only [checkTm, decide_eq_true_eq] at h; exact .var h
  | .app h args, τ, hc => by
      simp only [checkTm, Bool.or_eq_true] at hc
      rcases hc with hc | hc
      · split at hc
        · rename_i cs hcs
          split at hc
          · rename_i cf hcf
            obtain ⟨d, hd, θ, rfl, rfl⟩ := Signature.ctorsAt_spec wf hcs
            have cfMember := List.mem_of_find?_eq_some hcf
            have cfName : cf.1 = h := by simpa using List.find?_some hcf
            obtain ⟨⟨c', fields⟩, hcm, rfl⟩ := List.mem_map.mp cfMember
            simp only at cfName
            subst cfName
            obtain ⟨len, each⟩ := checkList_sound wf Γ args _ hc
            exact .ctor θ hd hcm (by simpa using len) fun i hi hj => by
              have := each i hi (by simpa using hj)
              simpa using this
          · cases hc
        · cases hc
      · split at hc
        · rename_i fd hfd
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
          obtain ⟨result, rest⟩ := hc
          have fdMember := List.mem_of_find?_eq_some hfd
          have fdName : fd.name = h := by simpa using List.find?_some hfd
          subst fdName
          obtain ⟨len, each⟩ := checkList_sound wf Γ args _ rest
          rw [← result]
          exact .call _ fdMember (by simpa using len) fun i hi hj => by
            have := each i hi (by simpa using hj)
            simpa using this
        · cases hc
/-- The check of lists is sound. -/
theorem checkList_sound (wf : sig.WellFormed) (Γ : Ctx) : ∀ (ts : List (Tm S)) (τs : List Sort'),
    checkList sig Γ ts τs = true → Pointwise (HasSort sig Γ) ts τs
  | [], [], _ => ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | t :: ts, τ :: τs, h => by
      simp only [checkList, Bool.and_eq_true] at h
      have first := checkTm_sound wf Γ t τ h.1
      obtain ⟨len, each⟩ := checkList_sound wf Γ ts τs h.2
      refine ⟨by simp [len], fun i hi hj => ?_⟩
      cases i with
      | zero => simpa using first
      | succ k => simpa using each k (by simpa using hi) (by simpa using hj)
  | [], _ :: _, h => by simp [checkList] at h
  | _ :: _, [], h => by simp [checkList] at h
end

/-- **Check one equation**: its left side is a declared function applied to patterns whose
variable sorts are inferred, without repetition, and its right side checks at the result sort. -/
def checkEquation (sig : Signature S) (e : Equation S) : Bool :=
  match e.lhs with
  | .app f ps =>
      match sig.funs.find? (fun fd => decide (fd.name = f)) with
      | some fd =>
          match inferPatterns sig ps fd.args with
          | some bindings =>
              decide (bindings.map Prod.fst).Nodup && checkTm sig (ctxOf bindings) e.rhs fd.result
          | none => false
      | none => false
  | .var _ => false

theorem checkEquation_sound (wf : sig.WellFormed) {e : Equation S}
    (h : checkEquation sig e = true) : sig.TypesEquation e := by
  unfold checkEquation at h
  split at h
  · rename_i f ps hlhs
    split at h
    · rename_i fd hfd
      split at h
      · rename_i bindings hb
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        have fdMember := List.mem_of_find?_eq_some hfd
        have fdName : fd.name = f := by simpa using List.find?_some hfd
        subst fdName
        obtain ⟨_, patterns, typed⟩ := inferPatterns_sound wf ps fd.args bindings hb
        exact ⟨fd, fdMember, ps, ctxOf bindings, hlhs, patterns,
          typed _ fun pair member => ctxOf_of_mem h.1 member, checkTm_sound wf _ _ _ h.2⟩
      · cases h
    · cases h
  · cases h

/-! ## Coverage -/

/-- A pattern matches a term, without naming bindings. -/
inductive Matches : Tm S → Tm S → Prop where
  | var (x : String) (t : Tm S) : Matches (.var x) t
  | app (c : S) {ps ts : List (Tm S)} : ps.length = ts.length →
      (∀ i (hi : i < ps.length) (hj : i < ts.length), Matches ps[i] ts[i]) →
      Matches (.app c ps) (.app c ts)

theorem matchList_isSome : ∀ {ps ts : List (Tm S)}, ps.length = ts.length →
    (∀ i (hi : i < ps.length) (hj : i < ts.length), (matchTm ps[i] ts[i]).isSome) →
      (matchList ps ts).isSome
  | [], [], _, _ => by simp [matchList]
  | p :: ps, t :: ts, len, each => by
      have first := each 0 (by simp) (by simp)
      have rest := matchList_isSome (ps := ps) (ts := ts) (by simpa using len)
        fun i hi hj => each (i + 1) (by simpa using hi) (by simpa using hj)
      simp only [List.getElem_cons_zero] at first
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp first
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp rest
      simp [matchList, ha, hb]
  | [], _ :: _, len, _ => by simp at len
  | _ :: _, [], len, _ => by simp at len

theorem Matches.isSome {p t : Tm S} (m : Matches p t) : (matchTm p t).isSome := by
  induction m with
  | var x t => simp [matchTm]
  | app c len _ ih => simpa [matchTm] using matchList_isSome len ih

/-- A linear pattern that matches a term has the term as an instance. -/
theorem Matches.exists_subst {p t : Tm S} (m : Matches p t) (linear : p.Linear) :
    ∃ σ, p.subst σ = t :=
  (matchTm_isSome_iff linear).mp m.isSome

/-- Every row's head is a variable. -/
def allVarHeads (rows : List (List (Tm S))) : Bool :=
  rows.all fun row => match row with
    | .var _ :: _ => true
    | _ => false

/-- The rows with their first column dropped, for rows whose head is a variable. -/
def defaultRows (rows : List (List (Tm S))) : List (List (Tm S)) :=
  rows.filterMap fun row => match row with
    | .var _ :: rest => some rest
    | _ => none

/-- The rows that a value with head constructor `c` of `k` fields may match, with the fields in
place of the first column. -/
def specialize (c : S) (k : Nat) : List (List (Tm S)) → List (List (Tm S))
  | [] => []
  | row :: rows =>
      match row with
      | .app c' qs :: rest =>
          if c' = c ∧ qs.length = k then (qs ++ rest) :: specialize c k rows
          else specialize c k rows
      | .var _ :: rest => (List.replicate k (.var "_") ++ rest) :: specialize c k rows
      | [] => specialize c k rows

/-- **The coverage check** of a pattern matrix at column sorts, with fuel. -/
def coversRows (sig : Signature S) : Nat → List (List (Tm S)) → List Sort' → Bool
  | 0, _, _ => false
  | _ + 1, rows, [] => !rows.isEmpty
  | n + 1, rows, σ :: σs =>
      if allVarHeads rows then coversRows sig n (defaultRows rows) σs
      else
        match sig.ctorsAt σ with
        | none => false
        | some cs => cs.all fun cf => coversRows sig n (specialize cf.1 cf.2.length rows) (cf.2 ++ σs)

theorem Pointwise.cons_iff {α β : Type*} {R : α → β → Prop} {a : α} {as : List α} {b : β}
    {bs : List β} : Pointwise R (a :: as) (b :: bs) ↔ R a b ∧ Pointwise R as bs := by
  constructor
  · rintro ⟨len, each⟩
    exact ⟨each 0 (by simp) (by simp), by simpa using len,
      fun i hi hj => each (i + 1) (by simpa using hi) (by simpa using hj)⟩
  · rintro ⟨first, len, each⟩
    refine ⟨by simp [len], fun i hi hj => ?_⟩
    cases i with
    | zero => simpa using first
    | succ k => simpa using each k (by simpa using hi) (by simpa using hj)

theorem Pointwise.append_iff {α β : Type*} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β} {as' : List α} {bs' : List β}, as.length = bs.length →
      (Pointwise R (as ++ as') (bs ++ bs') ↔ Pointwise R as bs ∧ Pointwise R as' bs')
  | [], [], as', bs', _ => by
      simp only [List.nil_append]
      exact ⟨fun h => ⟨⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩, h⟩, fun h => h.2⟩
  | a :: as, b :: bs, as', bs', len => by
      simp only [List.cons_append, Pointwise.cons_iff]
      rw [Pointwise.append_iff (by simpa using len)]
      tauto
  | [], _ :: _, _, _, len => by simp at len
  | _ :: _, [], _, _, len => by simp at len

theorem Pointwise.length {α β : Type*} {R : α → β → Prop} {as : List α} {bs : List β}
    (h : Pointwise R as bs) : as.length = bs.length := h.1

theorem Pointwise.nil {α β : Type*} {R : α → β → Prop} : Pointwise R ([] : List α) ([] : List β) :=
  ⟨rfl, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩

omit [DecidableEq S] in
theorem Pointwise.replicate_var (k : Nat) {ts : List (Tm S)} (len : ts.length = k) :
    Pointwise Matches (List.replicate k (Tm.var "_" : Tm S)) ts :=
  ⟨by simp [len], fun _ _ _ => by simpa using Matches.var "_" _⟩

omit [DecidableEq S] in
theorem mem_defaultRows {rows : List (List (Tm S))} {row' : List (Tm S)}
    (member : row' ∈ defaultRows rows) : ∃ x, (.var x :: row') ∈ rows := by
  simp only [defaultRows, List.mem_filterMap] at member
  obtain ⟨row, rowMember, h⟩ := member
  split at h
  · rename_i x rest
    cases h
    exact ⟨x, rowMember⟩
  · cases h

theorem mem_specialize {c : S} {k : Nat} : ∀ {rows : List (List (Tm S))} {row' : List (Tm S)},
    row' ∈ specialize c k rows →
      (∃ qs rest, qs.length = k ∧ row' = qs ++ rest ∧ (.app c qs :: rest) ∈ rows) ∨
        (∃ x rest, row' = List.replicate k (.var "_") ++ rest ∧ (.var x :: rest) ∈ rows)
  | [], _, member => by simp [specialize] at member
  | row :: rows, row', member => by
      have later : ∀ {row'' : List (Tm S)}, row'' ∈ specialize c k rows →
          (∃ qs rest, qs.length = k ∧ row'' = qs ++ rest ∧ (.app c qs :: rest) ∈ row :: rows) ∨
            (∃ x rest, row'' = List.replicate k (.var "_") ++ rest ∧
              (.var x :: rest) ∈ row :: rows) := by
        intro row'' h
        rcases mem_specialize h with ⟨qs, rest, len, same, m⟩ | ⟨x, rest, same, m⟩
        · exact .inl ⟨qs, rest, len, same, List.mem_cons_of_mem _ m⟩
        · exact .inr ⟨x, rest, same, List.mem_cons_of_mem _ m⟩
      simp only [specialize] at member
      split at member
      · rename_i c' qs rest
        split at member
        · rename_i cond
          obtain ⟨rfl, len⟩ := cond
          rcases List.mem_cons.mp member with rfl | m
          · exact .inl ⟨qs, rest, len, rfl, List.mem_cons_self⟩
          · exact later m
        · exact later member
      · rename_i x rest
        rcases List.mem_cons.mp member with rfl | m
        · exact .inr ⟨x, rest, rfl, List.mem_cons_self⟩
        · exact later m
      · exact later member

theorem specialize_length {c : S} {k : Nat} {n : Nat} : ∀ {rows : List (List (Tm S))},
    (∀ row ∈ rows, row.length = n + 1) → ∀ row' ∈ specialize c k rows, row'.length = k + n := by
  intro rows lengths row' member
  rcases mem_specialize member with ⟨qs, rest, len, rfl, m⟩ | ⟨x, rest, rfl, m⟩
  · have := lengths _ m
    simp only [List.length_cons, Nat.add_right_cancel_iff] at this
    simp [len, this]
  · have := lengths _ m
    simp only [List.length_cons, Nat.add_right_cancel_iff] at this
    simp [this]

/-- **The coverage check is sound**: when it succeeds, every list of values of the column sorts,
at any instance of them, is matched by some row. -/
theorem coversRows_sound {sig : Signature S} (wf : sig.WellFormed) : ∀ (n : Nat)
    (rows : List (List (Tm S))) (cols : List Sort'), coversRows sig n rows cols = true →
      (∀ row ∈ rows, row.length = cols.length) → ∀ (θ : String → Sort') (vs : List (Tm S)),
        Pointwise sig.IsValueOf vs (cols.map (Tm.subst θ)) → ∃ row ∈ rows, Pointwise Matches row vs
  | 0, _, _, h, _, _, _, _ => by simp [coversRows] at h
  | n + 1, rows, [], h, lengths, θ, vs, values => by
      simp only [coversRows, Bool.not_eq_true', List.isEmpty_eq_false_iff_exists_mem] at h
      obtain ⟨row, member⟩ := h
      have rowNil : row = [] := List.eq_nil_of_length_eq_zero (lengths row member)
      have vsNil : vs = [] := List.eq_nil_of_length_eq_zero (by simpa using values.length)
      subst rowNil vsNil
      exact ⟨[], member, Pointwise.nil⟩
  | n + 1, rows, σ :: σs, h, lengths, θ, vs, values => by
      cases vs with
      | nil => simp [Pointwise] at values
      | cons v vs =>
      simp only [List.map_cons, Pointwise.cons_iff] at values
      obtain ⟨⟨vData, vTyped⟩, restValues⟩ := values
      simp only [coversRows] at h
      split at h
      · rename_i allVar
        have defaultLengths : ∀ row ∈ defaultRows rows, row.length = σs.length := by
          intro row' member
          obtain ⟨x, m⟩ := mem_defaultRows member
          simpa using lengths _ m
        obtain ⟨row', member, matches'⟩ :=
          coversRows_sound wf n _ σs h defaultLengths θ vs restValues
        obtain ⟨x, m⟩ := mem_defaultRows member
        exact ⟨_, m, Pointwise.cons_iff.mpr ⟨Matches.var x v, matches'⟩⟩
      · split at h
        · cases h
        · rename_i cs hcs
          cases vData with
          | @app c us isCtor usData =>
          obtain ⟨cf, cfMember, cfName, usTyped⟩ := Signature.ctorsAt_value wf hcs isCtor vTyped
          have sub := List.all_eq_true.mp h cf cfMember
          have usLen : us.length = cf.2.length := by simpa using usTyped.length
          have specLengths : ∀ row ∈ specialize cf.1 cf.2.length rows,
              row.length = (cf.2 ++ σs).length := by
            intro row' member
            rw [List.length_append]
            exact specialize_length (n := σs.length) (fun row m => by simpa using lengths row m) row' member
          have newValues : Pointwise sig.IsValueOf (us ++ vs) ((cf.2 ++ σs).map (Tm.subst θ)) := by
            rw [List.map_append, Pointwise.append_iff (by simpa using usLen)]
            refine ⟨⟨by simpa using usLen, fun i hi hj => ⟨usData _ (List.getElem_mem hi), ?_⟩⟩,
              restValues⟩
            exact usTyped.2 i hi hj
          obtain ⟨row', member, matches'⟩ :=
            coversRows_sound wf n _ _ sub specLengths θ (us ++ vs) newValues
          rcases mem_specialize member with ⟨qs, rest, len, rfl, m⟩ | ⟨x, rest, rfl, m⟩
          · rw [Pointwise.append_iff (by rw [len, usLen])] at matches'
            refine ⟨_, m, Pointwise.cons_iff.mpr ⟨?_, matches'.2⟩⟩
            rw [← cfName]
            exact Matches.app _ matches'.1.1 matches'.1.2
          · rw [Pointwise.append_iff (by simp [usLen])] at matches'
            exact ⟨_, m, Pointwise.cons_iff.mpr ⟨Matches.var x _, matches'.2⟩⟩

/-- The number of symbols and variables of a term. -/
def Tm.size : Tm S → Nat
  | .var _ => 1
  | .app _ args => 1 + sizeList args
where
  sizeList : List (Tm S) → Nat
    | [] => 0
    | a :: as => Tm.size a + sizeList as

/-- The rows of a function: the argument patterns of its equations of the right length. -/
def functionRows (P : Program S) (fd : FunDecl S) : List (List (Tm S)) :=
  P.filterMap fun e => match e.lhs with
    | .app f ps => if f = fd.name ∧ ps.length = fd.args.length then some ps else none
    | .var _ => none

/-- Fuel for the coverage check: enough for every split of the matrix. -/
def coverFuel (rows : List (List (Tm S))) (cols : List Sort') : Nat :=
  let total := (rows.flatten.map Tm.size).sum
  (total + 1) * (total + cols.length + 1) + 1

/-- The coverage check of one function. -/
def coversFun (sig : Signature S) (P : Program S) (fd : FunDecl S) : Bool :=
  coversRows sig (coverFuel (functionRows P fd) fd.args) (functionRows P fd) fd.args

/-- **Coverage from the check**, for linear left sides. -/
theorem covers_of_check {sig : Signature S} {P : Program S} (wf : sig.WellFormed)
    (linear : P.LeftLinear) (checked : ∀ fd ∈ sig.funs, coversFun sig P fd = true) :
    sig.Covers P := by
  intro fd hfd θ args values
  have lengths : ∀ row ∈ functionRows P fd, row.length = fd.args.length := by
    intro row member
    simp only [functionRows, List.mem_filterMap] at member
    obtain ⟨e, _, h⟩ := member
    split at h
    · split at h
      · rename_i cond; cases h; exact cond.2
      · cases h
    · cases h
  obtain ⟨row, member, matches'⟩ :=
    coversRows_sound wf _ _ _ (checked fd hfd) lengths θ args values
  simp only [functionRows, List.mem_filterMap] at member
  obtain ⟨e, eMember, h⟩ := member
  split at h
  · rename_i f ps hlhs
    split at h
    · rename_i cond
      cases h
      obtain ⟨hf, _⟩ := cond
      subst hf
      have m : Matches e.lhs (.app _ args) := hlhs ▸ Matches.app _ matches'.1 matches'.2
      obtain ⟨σ, hσ⟩ := m.exists_subst (linear e eMember)
      exact ⟨e, eMember, σ, hσ⟩
    · cases h
  · cases h

/-! ## Structural descent -/

mutual
/-- The proper parts of a term. -/
def properSubterms : Tm S → List (Tm S)
  | .var _ => []
  | .app _ args => subtermsList args
/-- The parts of the terms of a list, themselves included. -/
def subtermsList : List (Tm S) → List (Tm S)
  | [] => []
  | a :: as => (a :: properSubterms a) ++ subtermsList as
end

section
omit [DecidableEq S]

mutual
theorem mem_properSubterms : ∀ (p : Tm S) {u : Tm S}, u ∈ properSubterms p → ProperSub p u
  | .var _, _, h => by simp [properSubterms] at h
  | .app f args, u, h => by
      simp only [properSubterms] at h
      obtain ⟨a, aMember, part⟩ := mem_subtermsList args h
      rcases part with rfl | inner
      · exact .single (Sub.arg f aMember)
      · exact Relation.TransGen.head (Sub.arg f aMember) inner
theorem mem_subtermsList : ∀ (args : List (Tm S)) {u : Tm S}, u ∈ subtermsList args →
    ∃ a ∈ args, u = a ∨ ProperSub a u
  | [], _, h => by simp [subtermsList] at h
  | a :: as, u, h => by
      simp only [subtermsList, List.cons_append, List.mem_cons, List.mem_append] at h
      rcases h with rfl | inner | later
      · exact ⟨u, List.mem_cons_self, .inl rfl⟩
      · exact ⟨a, List.mem_cons_self, .inr (mem_properSubterms a inner)⟩
      · obtain ⟨b, bMember, part⟩ := mem_subtermsList as later
        exact ⟨b, List.mem_cons_of_mem a bMember, part⟩
end

end

/-- Some equation is headed by the symbol, as a computation. -/
def Program.definesB (P : Program S) (g : S) : Bool := P.any fun e => decide (e.lhs.head? = some g)

theorem Program.definesB_iff {P : Program S} {g : S} : P.definesB g = true ↔ P.Defines g := by
  simp [Program.definesB, Program.Defines]

/-- The descent of one call, as a computation. -/
def callDescendsB (P : Program S) (c : Certificate S) (f : S) (ps : List (Tm S)) (g : S)
    (us : List (Tm S)) : Bool :=
  !P.definesB g || decide (c.rank g < c.rank f) ||
    (decide (g = f) &&
      match ps[c.position f]?, us[c.position f]? with
      | some p, some u => decide (u ∈ properSubterms p)
      | _, _ => false)

theorem callDescendsB_sound {P : Program S} {c : Certificate S} {f : S} {ps : List (Tm S)} {g : S}
    {us : List (Tm S)} (h : callDescendsB P c f ps g us = true) : CallDescends P c f ps g us := by
  simp only [callDescendsB, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true,
    decide_eq_true_eq] at h
  rcases h with (undefined | lower) | ⟨same, recursive⟩
  · left
    intro defined
    rw [← Program.definesB_iff, undefined] at defined
    cases defined
  · exact .inr (.inl lower)
  · right; right
    refine ⟨same, ?_⟩
    split at recursive
    · rename_i p u hp hu
      simp only [decide_eq_true_eq] at recursive
      obtain ⟨hpLt, rfl⟩ := List.getElem?_eq_some_iff.mp hp
      obtain ⟨huLt, rfl⟩ := List.getElem?_eq_some_iff.mp hu
      exact ⟨huLt, hpLt, mem_properSubterms _ recursive⟩
    · cases recursive

mutual
/-- Every call of a term passes a test. -/
def everyCallB (Q : S → List (Tm S) → Bool) : Tm S → Bool
  | .var _ => true
  | .app g us => Q g us && everyCallListB Q us
/-- Every call of every term of a list passes a test. -/
def everyCallListB (Q : S → List (Tm S) → Bool) : List (Tm S) → Bool
  | [] => true
  | u :: us => everyCallB Q u && everyCallListB Q us
end

section
omit [DecidableEq S]

mutual
theorem everyCallB_sound (Q : S → List (Tm S) → Bool) : ∀ t : Tm S, everyCallB Q t = true →
    EveryCall (fun g us => Q g us = true) t
  | .var x, _ => .var x
  | .app g us, h => by
      simp only [everyCallB, Bool.and_eq_true] at h
      exact .app h.1 (everyCallListB_sound Q us h.2)
theorem everyCallListB_sound (Q : S → List (Tm S) → Bool) : ∀ us : List (Tm S),
    everyCallListB Q us = true → ∀ u ∈ us, EveryCall (fun g us => Q g us = true) u
  | [], _ => fun _ member => absurd member List.not_mem_nil
  | u :: us, h => by
      simp only [everyCallListB, Bool.and_eq_true] at h
      intro v member
      rcases List.mem_cons.mp member with same | later
      · rw [same]; exact everyCallB_sound Q u h.1
      · exact everyCallListB_sound Q us h.2 v later
end

end

omit [DecidableEq S] in
theorem EveryCall.mono {Q Q' : S → List (Tm S) → Prop} (imp : ∀ g us, Q g us → Q' g us) :
    ∀ {t : Tm S}, EveryCall Q t → EveryCall Q' t := by
  intro t every
  induction every with
  | var x => exact .var x
  | app holds _ ih => exact .app (imp _ _ holds) ih

/-- The equations of a program descend under a certificate, as a computation. -/
def descendsCheck (P : Program S) (c : Certificate S) : Bool :=
  P.all fun e => match e.lhs with
    | .app f ps => everyCallB (callDescendsB P c f ps) e.rhs
    | .var _ => false

/-- The first equation that does not descend. -/
def firstNotDescending (P : Program S) (c : Certificate S) : Option (Equation S) :=
  P.find? fun e => !(match e.lhs with
    | .app f ps => everyCallB (callDescendsB P c f ps) e.rhs
    | .var _ => false)

theorem descends_of_check {P : Program S} {c : Certificate S}
    (h : firstNotDescending P c = none) : P.Descends c := by
  intro e eMember
  have := List.find?_eq_none.mp h e eMember
  simp only [Bool.not_eq_true', Bool.not_eq_false] at this
  split at this
  · rename_i f ps hlhs
    exact ⟨f, ps, hlhs, EveryCall.mono (fun g us h => callDescendsB_sound h)
      (everyCallB_sound _ _ this)⟩
  · cases this

/-- The rank of a symbol: its place among the declared functions. -/
def rankOf (sig : Signature S) (g : S) : Nat := (sig.funs.map (·.name)).idxOf g

/-- A recursion position for a function: the first argument position at which all its equations
descend, if any. -/
def inferPosition (sig : Signature S) (P : Program S) (fd : FunDecl S) : Nat :=
  ((List.range fd.args.length).find? fun i =>
      P.all fun e => match e.lhs with
        | .app g ps => !(decide (g = fd.name)) ||
            everyCallB (callDescendsB P ⟨rankOf sig, fun _ => i⟩ fd.name ps) e.rhs
        | .var _ => true).getD 0

/-- **The inferred certificate**: ranks by declaration order, positions by search. -/
def inferCertificate (sig : Signature S) (P : Program S) : Certificate S where
  rank := rankOf sig
  position := fun f => match sig.funs.find? (fun fd => decide (fd.name = f)) with
    | some fd => inferPosition sig P fd
    | none => 0

/-! ## Lexicographic descent -/

/-- Lexicographic descent along the positions of caller and callee, as a computation. -/
def lexDescB (ps us : List (Tm S)) : List ℕ → List ℕ → Bool
  | i :: L, j :: M => decide (i < ps.length) && decide (j < us.length) &&
      ((decide (L.length = M.length) && decide (keyAt us j ∈ properSubterms (keyAt ps i))) ||
        (decide (keyAt us j = keyAt ps i) && lexDescB ps us L M))
  | _, _ => false

theorem lexDescB_sound {ps us : List (Tm S)} : ∀ L M, lexDescB ps us L M = true → LexDesc ps us L M
  | i :: L, j :: M, h => by
      simp only [lexDescB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hp, hu⟩, ⟨len, here⟩ | ⟨same, rest⟩⟩ := h
      · exact .here hp hu len (mem_properSubterms _ here)
      · exact .next hp hu same (lexDescB_sound L M rest)
  | [], _, h => by simp [lexDescB] at h
  | _ :: _, [], h => by simp [lexDescB] at h

/-- The lexicographic descent of one call, as a computation. -/
def lexCallDescendsB (P : Program S) (c : LexCertificate S) (f : S) (ps : List (Tm S)) (g : S)
    (us : List (Tm S)) : Bool :=
  !P.definesB g || decide (c.rank g < c.rank f) ||
    (decide (c.rank g = c.rank f) && lexDescB ps us (c.positions f) (c.positions g))

theorem lexCallDescendsB_sound {P : Program S} {c : LexCertificate S} {f : S} {ps : List (Tm S)}
    {g : S} {us : List (Tm S)} (h : lexCallDescendsB P c f ps g us = true) :
    LexCallDescends P c f ps g us := by
  simp only [lexCallDescendsB, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true,
    decide_eq_true_eq] at h
  rcases h with (undefined | lower) | ⟨same, lex⟩
  · left
    intro defined
    rw [← Program.definesB_iff, undefined] at defined
    cases defined
  · exact .inr (.inl lower)
  · exact .inr (.inr ⟨same, lexDescB_sound _ _ lex⟩)

/-- The first equation that does not descend lexicographically. -/
def firstNotLexDescending (P : Program S) (c : LexCertificate S) : Option (Equation S) :=
  P.find? fun e => !(match e.lhs with
    | .app f ps => everyCallB (lexCallDescendsB P c f ps) e.rhs
    | .var _ => false)

theorem lexDescends_of_check {P : Program S} {c : LexCertificate S}
    (h : firstNotLexDescending P c = none) : P.LexDescends c := by
  intro e eMember
  have := List.find?_eq_none.mp h e eMember
  simp only [Bool.not_eq_true', Bool.not_eq_false] at this
  split at this
  · rename_i f ps hlhs
    exact ⟨f, ps, hlhs, EveryCall.mono (fun g us h => lexCallDescendsB_sound h)
      (everyCallB_sound _ _ this)⟩
  · cases this

/-- Every order of a list. -/
def insertEverywhere (a : ℕ) : List ℕ → List (List ℕ)
  | [] => [[a]]
  | b :: l => (a :: b :: l) :: (insertEverywhere a l).map (b :: ·)

/-- All orders of a list. -/
def perms : List ℕ → List (List ℕ)
  | [] => [[]]
  | a :: l => (perms l).flatMap (insertEverywhere a)

/-- Lexicographic positions for a function: the first order of its argument positions along which all
its equations descend, if any. -/
def inferLexPositions (sig : Signature S) (P : Program S) (fd : FunDecl S) : List ℕ :=
  ((perms (List.range fd.args.length)).find? fun L =>
      P.all fun e => match e.lhs with
        | .app g ps => !(decide (g = fd.name)) ||
            everyCallB (lexCallDescendsB P ⟨rankOf sig, fun _ => L⟩ fd.name ps) e.rhs
        | .var _ => true).getD []

/-- **The inferred lexicographic certificate.** -/
def inferLexCertificate (sig : Signature S) (P : Program S) : LexCertificate S where
  rank := rankOf sig
  positions := fun f => match sig.funs.find? (fun fd => decide (fd.name = f)) with
    | some fd => inferLexPositions sig P fd
    | none => []

mutual
/-- The heads of the applications in a term. -/
def callHeads : Tm S → List S
  | .var _ => []
  | .app g us => g :: callHeadsList us
/-- The heads of the applications in a list of terms. -/
def callHeadsList : List (Tm S) → List S
  | [] => []
  | u :: us => callHeads u ++ callHeadsList us
end

/-- The defined symbols an equation of `f` calls. -/
def calleesOf (P : Program S) (f : S) : List S :=
  ((P.filter fun e => decide (e.lhs.head? = some f)).flatMap fun e => callHeads e.rhs).filter
    (P.definesB ·)

/-- Apply a step to a list a number of times. -/
def iterateList (step : List S → List S) : ℕ → List S → List S
  | 0, xs => xs
  | n + 1, xs => iterateList step n (step xs)

/-- The defined symbols reachable from `f`, `f` included, by iterating the call relation. -/
def reachStar (P : Program S) (f : S) : List S :=
  iterateList (fun xs => (xs ++ xs.flatMap (calleesOf P)).dedup) (P.length + 1) [f]

/-- **Ranks by strongly connected component**: the number of symbols a symbol reaches. Symbols that
call each other reach the same symbols; a symbol reaches strictly more than any symbol it calls that
does not call it back. -/
def sccRank (P : Program S) (f : S) : ℕ := (reachStar P f).length

/-- A certificate with ranks by component and one order of positions for every symbol, cut to its
number of arguments. -/
def sccCertificate (sig : Signature S) (P : Program S) (L : List ℕ) : LexCertificate S where
  rank := sccRank P
  positions := fun f => match sig.funs.find? (fun fd => decide (fd.name = f)) with
    | some fd => L.filter (· < fd.args.length)
    | none => []

/-- The largest number of arguments of a declared function. -/
def maxArity (sig : Signature S) : ℕ := (sig.funs.map fun fd => fd.args.length).foldr max 0

/-- An order of positions along which the whole program descends with ranks by component. -/
def sccOrder (sig : Signature S) (P : Program S) : Option (List ℕ) :=
  (perms (List.range (maxArity sig))).find? fun L =>
    (firstNotLexDescending P (sccCertificate sig P L)).isNone

/-- **The termination verdict**: structural descent, else lexicographic descent with ranks by
declaration order, else lexicographic descent with ranks by component (mutual recursion); otherwise
the first equation that does not descend structurally. -/
def terminationVerdict (sig : Signature S) (P : Program S) : Option (Equation S) :=
  match firstNotDescending P (inferCertificate sig P) with
  | none => none
  | some e =>
      match firstNotLexDescending P (inferLexCertificate sig P) with
      | none => none
      | some _ =>
          match sccOrder sig P with
          | some _ => none
          | none => some e

theorem terminating_of_verdict {sig : Signature S} {P : Program S} (headed : P.Headed)
    (bound : P.RightBound) (h : terminationVerdict sig P = none) : ∀ t, SN P t := by
  unfold terminationVerdict at h
  split at h
  · rename_i structural
    exact (descends_of_check structural).stronglyNormalizing headed bound
  · split at h
    · rename_i lexicographic
      exact (lexDescends_of_check lexicographic).stronglyNormalizing headed bound
    · split at h
      · rename_i L found
        have checked := List.find?_some found
        simp only [Option.isNone_iff_eq_none] at checked
        exact (lexDescends_of_check checked).stronglyNormalizing headed bound
      · cases h

/-! ## Admission -/

/-- **Why a declaration is refused.** -/
inductive Refusal (S : Type u) where
  /-- The signature is not well formed. -/
  | signature
  /-- The equation is not a declared function on constructor patterns, or does not check. -/
  | untyped (e : Equation S)
  /-- A variable occurs twice in the left side. -/
  | nonlinear (e : Equation S)
  /-- The right side uses a variable its left side does not bind. -/
  | unboundRight (e : Equation S)
  /-- The left sides of the two equations may have a common instance. -/
  | overlap (e e' : Equation S)
  /-- Some call of the function on values matches no equation. -/
  | missingCase (f : S)
  /-- The equation makes a call that does not descend. -/
  | notStructural (e : Equation S)
  deriving DecidableEq

/-- **Everything the agreement theorems use**, for a signature and a program. -/
structure Admitted (sig : Signature S) (P : Program S) : Prop where
  wellFormed : sig.WellFormed
  typed : sig.TypesProgram P
  leftLinear : P.LeftLinear
  rightBound : P.RightBound
  nonOverlapping : P.NonOverlapping
  clashing : P.Clashing
  covers : sig.Covers P
  terminating : ∀ t, SN P t

/-- **The admission check**: `none` admits; otherwise the first failing condition. -/
def admit (sig : Signature S) (P : Program S) : Option (Refusal S) :=
  if ¬ sig.WellFormed then some .signature
  else match P.find? (fun e => !decide e.lhs.Linear) with
  | some e => some (.nonlinear e)
  | none =>
  match P.find? (fun e => !decide (∀ x ∈ e.rhs.vars, x ∈ e.lhs.vars)) with
  | some e => some (.unboundRight e)
  | none =>
  match P.find? (fun e => !checkEquation sig e) with
  | some e => some (.untyped e)
  | none =>
  match firstOverlap P with
  | some (e, e') => some (.overlap e e')
  | none =>
  match sig.funs.find? (fun fd => !coversFun sig P fd) with
  | some fd => some (.missingCase fd.name)
  | none =>
  match terminationVerdict sig P with
  | some e => some (.notStructural e)
  | none => none

/-- **Admission is sound.** -/
theorem admit_sound {sig : Signature S} {P : Program S} (h : admit sig P = none) :
    Admitted sig P := by
  unfold admit at h
  split at h
  · cases h
  rename_i wf
  simp only [not_not] at wf
  split at h
  · cases h
  rename_i noNonlinear
  split at h
  · cases h
  rename_i noUnbound
  split at h
  · cases h
  rename_i noUntyped
  split at h
  · cases h
  rename_i noOverlap
  split at h
  · cases h
  rename_i noMissing
  split at h
  · cases h
  rename_i noDescent
  have linear : P.LeftLinear := fun e member => by
    have := List.find?_eq_none.mp noNonlinear e member
    simpa using this
  have typed : sig.TypesProgram P := fun e member => checkEquation_sound wf (by
    have := List.find?_eq_none.mp noUntyped e member
    simpa using this)
  have bound : P.RightBound := fun e member => by
    have := List.find?_eq_none.mp noUnbound e member
    simpa using this
  exact
    { wellFormed := wf
      typed := typed
      leftLinear := linear
      rightBound := bound
      nonOverlapping := nonOverlapping_of_firstOverlap noOverlap
      clashing := clashing_of_firstOverlap noOverlap
      covers := covers_of_check wf linear fun fd member => by
        have := List.find?_eq_none.mp noMissing fd member
        simpa using this
      terminating := terminating_of_verdict typed.headed bound noDescent }

end Mettapedia.Languages.MeTTa.DeclarationFaces

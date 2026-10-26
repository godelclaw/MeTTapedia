import Mettapedia.Languages.MeTTa.DeclarationFaces.Controls
import Mettapedia.OSLF.Framework.GeneralCanonicalAgreement

/-!
# The same declarations as a GSLT presentation

A declaration is also a language definition of the module form (`presentation`): its equations
become unconditional rewrite rules between patterns (`encRule`), its terms are patterns (`enc`).

* **The root reducts of the presentation are exactly MeTTa's calls**
  (`mem_rootReducts_presentation_iff`): a pattern is a root reduct of the encoding of a term exactly
  when it is the encoding of a root step of the term. As lists they are MeTTa's call results,
  encoded, with the same order and multiplicities (`rootReducts_presentation`): an encoded pattern
  matches in at most one way (`matchPattern_length_le_one`). The proofs read the presentation's own
  matcher and its merging of bindings (`matchPattern`, `mergeBindings`); no new matcher is
  introduced.
* **The canonical one-step semantics of the presentation is MeTTa's root step**
  (`canonical_step_iff_rootStep`), through the existing exact one-layer theorem
  `NonrecursiveReduction.step_iff_mem_rootReducts`: every rule of the presentation is unconditional and
  binder-free.
* **So is the compiled general semantics** (`general_step_iff_rootStep`), at every language for which the
  existing decidable root profile holds, through the existing first-order agreement theorem
  `GeneralCanonicalAgreement.RootProfile.general_step_iff_canonical`.
* **MeTTa's evaluation is the congruence closure of the presentation's step**
  (`step_iff_congruence`): a presentation rewrites at the root, and evaluation under symbols is its
  closure under argument positions, as congruence premises would author it.

Positive example: the encodings of `(add (S Z) Z)` and `(S (add Z Z))` are related by the canonical
step of the presentation of addition (`Examples.add_canonical_step`). Negative example: the encoding
of a constructor term has no root reduct (`Examples.value_no_root_reduct`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.DeclarationFaces

open Tm
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern RewriteRule LanguageDef)
open Mettapedia.OSLF.MeTTaIL.Match (matchPattern matchArgs applyBindings mergeBindings Bindings
  binderFree binderFreeList ruleDepthAligned_of_binderFree)
open Mettapedia.OSLF.MeTTaIL.NonrecursiveReduction (rootReducts step_iff_mem_rootReducts
  isUnconditionalAligned)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator)

universe u

variable {S : Type u} (name : S → String)

/-! ## Encoding -/

mutual
/-- **The pattern of a term**: a variable is a metavariable, an application is an application. -/
def enc : Tm S → Pattern
  | .var x => .fvar x
  | .app f args => .apply (name f) (encList args)
/-- The patterns of a list of terms. -/
def encList : List (Tm S) → List Pattern
  | [] => []
  | a :: as => enc a :: encList as
end

theorem encList_eq (args : List (Tm S)) : encList name args = args.map (enc name) := by
  induction args with
  | nil => rfl
  | cons a as ih => simp [encList, ih]

@[simp] theorem enc_var (x : String) : enc name (.var x : Tm S) = .fvar x := by simp [enc]

theorem enc_app (f : S) (args : List (Tm S)) :
    enc name (.app f args) = .apply (name f) (args.map (enc name)) := by simp [enc, encList_eq]

/-- **Encoding is injective** for an injective naming of symbols. -/
theorem enc_injective (inj : Function.Injective name) : Function.Injective (enc name : Tm S → Pattern) := by
  intro s
  induction s using Tm.induction' with
  | var x =>
      intro t same
      cases t with
      | var y => simp only [enc_var, Pattern.fvar.injEq] at same; rw [same]
      | app g bs => simp [enc_app] at same
  | app f args ih =>
      intro t same
      cases t with
      | var y => simp [enc_app] at same
      | app g bs =>
          simp only [enc_app, Pattern.apply.injEq] at same
          obtain ⟨hname, hargs⟩ := same
          obtain rfl := inj hname
          congr 1
          have len : args.length = bs.length := by simpa using congrArg List.length hargs
          apply List.ext_getElem len
          intro i h₁ h₂
          apply ih _ (List.getElem_mem h₁)
          have := congrArg (fun l => l[i]?) hargs
          simpa [h₁, h₂] using this

/-- Encodings have no binders. -/
theorem binderFree_enc : ∀ t : Tm S, binderFree (enc name t) = true := by
  intro t
  induction t using Tm.induction' with
  | var x => simp [binderFree]
  | app f args ih =>
      rw [enc_app]
      simp only [binderFree]
      suffices ∀ l : List (Tm S), (∀ a ∈ l, binderFree (enc name a) = true) →
          binderFreeList (l.map (enc name)) = true from this args ih
      intro l h
      induction l with
      | nil => simp [binderFreeList]
      | cons a as ih' =>
          simp only [List.map_cons, binderFreeList, Bool.and_eq_true]
          exact ⟨h a List.mem_cons_self, ih' fun b hb => h b (List.mem_cons_of_mem a hb)⟩

/-! ## Bindings that agree with a substitution -/

/-- Every binding gives a variable the encoding of the substitution's term. -/
def Consistent (σ : String → Tm S) (b : Bindings) : Prop := ∀ pr ∈ b, pr.2 = enc name (σ pr.1)

/-- The keys of a list of bindings. -/
def keys (b : Bindings) : List String := b.map Prod.fst

/-- One step of merging bindings. -/
theorem mergeBindings_cons (acc : Bindings) (x : String) (v : Pattern) (rest : Bindings) :
    mergeBindings acc ((x, v) :: rest) =
      match acc.find? (·.1 == x) with
      | none => mergeBindings ((x, v) :: acc) rest
      | some (_, existing) => if existing = v then mergeBindings acc rest else none := by
  cases hf : acc.find? (·.1 == x) with
  | none => simp [mergeBindings, List.foldlM_cons, hf]
  | some q =>
      obtain ⟨y, existing⟩ := q
      by_cases he : existing = v
      · simp [mergeBindings, List.foldlM_cons, hf, he]
      · simp [mergeBindings, List.foldlM_cons, hf, he]

theorem mergeBindings_nil (acc : Bindings) : mergeBindings acc [] = some acc := rfl

theorem find?_key {b : Bindings} {x : String} {q : String × Pattern}
    (h : b.find? (·.1 == x) = some q) : q.1 = x ∧ q ∈ b :=
  ⟨by simpa using List.find?_some h, List.mem_of_find?_eq_some h⟩

/-- **Merging consistent bindings succeeds**, with a consistent result containing both. -/
theorem merge_consistent {σ : String → Tm S} :
    ∀ (b2 acc : Bindings), Consistent name σ acc → Consistent name σ b2 →
      ∃ m, mergeBindings acc b2 = some m ∧ Consistent name σ m ∧ (∀ pr ∈ acc, pr ∈ m) ∧
        ∀ x ∈ keys b2, x ∈ keys m := by
  intro b2
  induction b2 with
  | nil => intro acc hacc _; exact ⟨acc, rfl, hacc, fun _ h => h, by simp [keys]⟩
  | cons pr rest ih =>
      intro acc hacc hb
      obtain ⟨x, v⟩ := pr
      have hv : v = enc name (σ x) := hb (x, v) List.mem_cons_self
      have hrest : Consistent name σ rest := fun p hp => hb p (List.mem_cons_of_mem _ hp)
      rw [mergeBindings_cons]
      cases hf : acc.find? (·.1 == x) with
      | none =>
          have hacc' : Consistent name σ ((x, v) :: acc) := by
            intro p hp
            rcases List.mem_cons.mp hp with rfl | old
            · exact hv
            · exact hacc p old
          obtain ⟨m, hm, hcons, hsub, hkeys⟩ := ih _ hacc' hrest
          refine ⟨m, hm, hcons, fun p hp => hsub p (List.mem_cons_of_mem _ hp), ?_⟩
          intro y hy
          simp only [keys, List.map_cons, List.mem_cons] at hy
          rcases hy with rfl | later
          · exact List.mem_map_of_mem (f := Prod.fst) (hsub _ List.mem_cons_self)
          · exact hkeys y later
      | some q =>
          obtain ⟨y, existing⟩ := q
          obtain ⟨key, member⟩ := find?_key hf
          simp only at key
          subst key
          have same : existing = v := by
            have h1 := hacc _ member
            simp only at h1
            rw [h1, hv]
          simp only [same, if_true]
          obtain ⟨m, hm, hcons, hsub, hkeys⟩ := ih acc hacc hrest
          refine ⟨m, hm, hcons, hsub, ?_⟩
          intro z hz
          simp only [keys, List.map_cons, List.mem_cons] at hz
          rcases hz with rfl | later
          · exact List.mem_map_of_mem (f := Prod.fst) (hsub _ member)
          · exact hkeys z later

/-- **A merge contains only bindings of its two sides.** -/
theorem merge_sub : ∀ (b2 acc m : Bindings), mergeBindings acc b2 = some m →
    ∀ pr ∈ m, pr ∈ acc ∨ pr ∈ b2 := by
  intro b2
  induction b2 with
  | nil => intro acc m h pr hp; rw [mergeBindings_nil] at h; cases h; exact .inl hp
  | cons pr rest ih =>
      intro acc m h p hp
      obtain ⟨x, v⟩ := pr
      rw [mergeBindings_cons] at h
      cases hf : acc.find? (·.1 == x) with
      | none =>
          rw [hf] at h
          rcases ih _ m h p hp with old | later
          · rcases List.mem_cons.mp old with rfl | old'
            · exact .inr List.mem_cons_self
            · exact .inl old'
          · exact .inr (List.mem_cons_of_mem _ later)
      | some q =>
          rw [hf] at h
          obtain ⟨y, existing⟩ := q
          dsimp only at h
          by_cases same : existing = v
          · rw [if_pos same] at h
            rcases ih _ m h p hp with old | later
            · exact .inl old
            · exact .inr (List.mem_cons_of_mem _ later)
          · rw [if_neg same] at h; cases h

/-- A merge keeps every binding of its first side. -/
theorem merge_keys_left : ∀ (b2 acc m : Bindings), mergeBindings acc b2 = some m →
    ∀ pr ∈ acc, pr ∈ m := by
  intro b2
  induction b2 with
  | nil => intro acc m h pr hp; rw [mergeBindings_nil] at h; cases h; exact hp
  | cons pr rest ih =>
      intro acc m h p hp
      obtain ⟨x, v⟩ := pr
      rw [mergeBindings_cons] at h
      cases hf : acc.find? (·.1 == x) with
      | none => rw [hf] at h; exact ih _ m h p (List.mem_cons_of_mem _ hp)
      | some q =>
          rw [hf] at h
          obtain ⟨y, existing⟩ := q
          dsimp only at h
          by_cases same : existing = v
          · rw [if_pos same] at h; exact ih _ m h p hp
          · rw [if_neg same] at h; cases h

/-- A merge keeps every key of its second side. -/
theorem merge_keys_right : ∀ (b2 acc m : Bindings), mergeBindings acc b2 = some m →
    ∀ x ∈ keys b2, x ∈ keys m := by
  intro b2
  induction b2 with
  | nil => intro acc m _ x hx; simp [keys] at hx
  | cons pr rest ih =>
      intro acc m h y hy
      obtain ⟨x, v⟩ := pr
      rw [mergeBindings_cons] at h
      simp only [keys, List.map_cons, List.mem_cons] at hy
      cases hf : acc.find? (·.1 == x) with
      | none =>
          rw [hf] at h
          rcases hy with rfl | later
          · exact List.mem_map_of_mem (f := Prod.fst)
              (merge_keys_left rest _ m h (y, v) List.mem_cons_self)
          · exact ih _ m h y later
      | some q =>
          rw [hf] at h
          obtain ⟨z, existing⟩ := q
          dsimp only at h
          by_cases same : existing = v
          · rw [if_pos same] at h
            rcases hy with rfl | later
            · obtain ⟨key, member⟩ := find?_key hf
              simp only at key
              subst key
              exact List.mem_map_of_mem (f := Prod.fst) (merge_keys_left rest _ m h _ member)
            · exact ih _ m h y later
          · rw [if_neg same] at h; cases h

/-- **Instantiating a rule's right side by consistent bindings** is encoding the instance. -/
theorem applyBindings_enc {σ : String → Tm S} {b : Bindings} (consistent : Consistent name σ b) :
    ∀ r : Tm S, (∀ x ∈ r.vars, x ∈ keys b) → applyBindings b (enc name r) = enc name (r.subst σ) := by
  intro r
  induction r using Tm.induction' with
  | var x =>
      intro covered
      have hx : x ∈ keys b := covered x (by simp)
      obtain ⟨p, hp, hkey⟩ := List.mem_map.mp hx
      cases hf : b.find? (·.1 == x) with
      | none =>
          have := List.find?_eq_none.mp hf p hp
          simp [hkey] at this
      | some q =>
          have key : q.1 = x := by simpa using List.find?_some hf
          have value := consistent q (List.mem_of_find?_eq_some hf)
          simp only [enc_var, applyBindings, hf, subst_var]
          rw [value, key]
  | app f args ih =>
      intro covered
      rw [enc_app, subst_app, enc_app, List.map_map]
      simp only [applyBindings, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact ih a ha fun x hx => covered x (by simpa using ⟨a, ha, hx⟩)

/-! ## Matching -/

mutual
/-- **Matching is complete**: an instance of a term matches its encoding with consistent bindings
covering its variables. -/
theorem matchPattern_complete (σ : String → Tm S) : ∀ p : Tm S,
    ∃ b ∈ matchPattern (enc name p) (enc name (p.subst σ)),
      Consistent name σ b ∧ ∀ x ∈ p.vars, x ∈ keys b
  | .var x => ⟨[(x, enc name (σ x))], by simp [matchPattern], by simp [Consistent], by simp [keys]⟩
  | .app f args => by
      obtain ⟨b, hb, hcons, hkeys⟩ := matchArgs_complete σ args
      refine ⟨b, ?_, hcons, by simpa [varsList_eq] using hkeys⟩
      rw [subst_app, enc_app, enc_app, List.map_map]
      simp only [matchPattern, beq_self_eq_true, Bool.true_and, List.length_map]
      simpa [encList_eq, List.map_map] using hb
/-- Matching of argument lists is complete. -/
theorem matchArgs_complete (σ : String → Tm S) : ∀ args : List (Tm S),
    ∃ b ∈ matchArgs (encList name args) (encList name (args.map (Tm.subst σ))),
      Consistent name σ b ∧ ∀ x ∈ varsList args, x ∈ keys b
  | [] => ⟨[], by simp [encList, matchArgs], by simp [Consistent], by simp [varsList]⟩
  | a :: as => by
      obtain ⟨hb, hhb, hcons₁, hkeys₁⟩ := matchPattern_complete σ a
      obtain ⟨tb, htb, hcons₂, hkeys₂⟩ := matchArgs_complete σ as
      obtain ⟨m, hm, hcons, hsub, hkeys⟩ := merge_consistent name tb hb hcons₁ hcons₂
      refine ⟨m, ?_, hcons, ?_⟩
      · simp only [encList, List.map_cons, matchArgs, List.mem_flatMap, List.mem_filterMap]
        exact ⟨hb, hhb, tb, htb, hm⟩
      · intro x hx
        simp only [varsList, List.mem_append] at hx
        rcases hx with inA | inAs
        · obtain ⟨p, hp, hkey⟩ := List.mem_map.mp (hkeys₁ x inA)
          exact hkey ▸ List.mem_map_of_mem (hsub p hp)
        · exact hkeys x (hkeys₂ x inAs)
end

theorem matchPattern_fvar (x : String) (q : Pattern) : matchPattern (.fvar x) q = [[(x, q)]] := by
  simp [matchPattern]

theorem matchPattern_apply_fvar (c : String) (ps : List Pattern) (y : String) :
    matchPattern (.apply c ps) (.fvar y) = [] := by
  simp [matchPattern]

theorem matchPattern_apply_apply (c d : String) (ps qs : List Pattern) :
    matchPattern (.apply c ps) (.apply d qs) =
      if c = d ∧ ps.length = qs.length then matchArgs ps qs else [] := by
  simp [matchPattern]

theorem matchArgs_cons (p : Pattern) (ps : List Pattern) (q : Pattern) (qs : List Pattern) :
    matchArgs (p :: ps) (q :: qs) =
      (matchPattern p q).flatMap fun hb => (matchArgs ps qs).filterMap fun tb => mergeBindings hb tb := by
  simp [matchArgs]

theorem matchArgs_nil_nil : matchArgs ([] : List Pattern) [] = [[]] := by simp [matchArgs]

theorem matchArgs_nil_cons (q : Pattern) (qs : List Pattern) : matchArgs [] (q :: qs) = [] := by
  simp [matchArgs]

theorem matchArgs_cons_nil (p : Pattern) (ps : List Pattern) : matchArgs (p :: ps) [] = [] := by
  simp [matchArgs]

variable {name}

mutual
/-- **Matching is sound** for linear patterns: a match of an encoded pattern against an encoded term
comes from an instance, with consistent bindings whose keys are exactly the pattern's variables. -/
theorem matchPattern_sound (inj : Function.Injective name) : ∀ (p t : Tm S) (b : Bindings),
    b ∈ matchPattern (enc name p) (enc name t) → p.vars.Nodup →
      ∃ σ, p.subst σ = t ∧ Consistent name σ b ∧ (∀ x ∈ keys b, x ∈ p.vars) ∧ ∀ x ∈ p.vars, x ∈ keys b
  | .var x, t, b, h, _ => by
      rw [enc_var, matchPattern_fvar, List.mem_singleton] at h
      subst h
      exact ⟨fun _ => t, rfl, by simp [Consistent], by simp [keys], by simp [keys]⟩
  | .app f ps, .var y, b, h, _ => by
      rw [enc_app, enc_var, matchPattern_apply_fvar] at h
      cases h
  | .app f ps, .app g ts, b, h, nodup => by
      rw [enc_app, enc_app, matchPattern_apply_apply] at h
      split at h
      · rename_i cond
        obtain ⟨hname, _⟩ := cond
        obtain rfl := inj hname
        rw [← encList_eq, ← encList_eq] at h
        obtain ⟨σ, hσ, hcons, hkeys, hcover⟩ := matchArgs_sound inj ps ts b h (by simpa [varsList_eq] using nodup)
        refine ⟨σ, ?_, hcons, fun x hx => by simpa [varsList_eq] using hkeys x hx,
          fun x hx => hcover x (by simpa [varsList_eq] using hx)⟩
        rw [subst_app, ← substList_eq, hσ]
      · cases h
/-- Matching of lists is sound for linear lists of patterns. -/
theorem matchArgs_sound (inj : Function.Injective name) : ∀ (ps ts : List (Tm S)) (b : Bindings),
    b ∈ matchArgs (encList name ps) (encList name ts) → (varsList ps).Nodup →
      ∃ σ, substList σ ps = ts ∧ Consistent name σ b ∧ (∀ x ∈ keys b, x ∈ varsList ps) ∧
        ∀ x ∈ varsList ps, x ∈ keys b
  | [], [], b, h, _ => by
      simp only [encList, matchArgs_nil_nil, List.mem_singleton] at h
      subst h
      exact ⟨Tm.var, rfl, by simp [Consistent], by simp [keys], by simp [varsList]⟩
  | [], t :: ts, b, h, _ => by simp [encList, matchArgs_nil_cons] at h
  | p :: ps, [], b, h, _ => by simp [encList, matchArgs_cons_nil] at h
  | p :: ps, t :: ts, b, h, nodup => by
      simp only [encList, matchArgs_cons, List.mem_flatMap, List.mem_filterMap] at h
      obtain ⟨hb, hhb, tb, htb, hm⟩ := h
      simp only [varsList, List.nodup_append] at nodup
      obtain ⟨nodupP, nodupPs, disjoint⟩ := nodup
      obtain ⟨σ₁, h₁, hcons₁, hkeys₁, hcover₁⟩ := matchPattern_sound inj p t hb hhb nodupP
      obtain ⟨σ₂, h₂, hcons₂, hkeys₂, hcover₂⟩ := matchArgs_sound inj ps ts tb htb nodupPs
      classical
      let σ : String → Tm S := fun x => if x ∈ p.vars then σ₁ x else σ₂ x
      have onP : ∀ x ∈ p.vars, σ x = σ₁ x := fun x hx => by simp [σ, hx]
      have onPs : ∀ x ∈ varsList ps, σ x = σ₂ x := fun x hx => by
        have : x ∉ p.vars := fun hp => disjoint x hp x hx rfl
        simp [σ, this]
      refine ⟨σ, ?_, ?_, ?_, ?_⟩
      · simp only [substList]
        rw [subst_congr p onP, h₁, show substList σ ps = substList σ₂ ps by
          rw [substList_eq, substList_eq]
          exact List.map_congr_left fun a ha => subst_congr a fun x hx =>
            onPs x (by simpa [varsList_eq] using ⟨a, ha, hx⟩), h₂]
      · intro pr hpr
        rcases merge_sub tb hb b hm pr hpr with fromHead | fromTail
        · rw [hcons₁ pr fromHead, onP pr.1 (hkeys₁ pr.1 (List.mem_map_of_mem fromHead))]
        · rw [hcons₂ pr fromTail, onPs pr.1 (hkeys₂ pr.1 (List.mem_map_of_mem fromTail))]
      · intro x hx
        obtain ⟨pr, hpr, rfl⟩ := List.mem_map.mp hx
        simp only [varsList, List.mem_append]
        rcases merge_sub tb hb b hm pr hpr with fromHead | fromTail
        · exact .inl (hkeys₁ _ (List.mem_map_of_mem fromHead))
        · exact .inr (hkeys₂ _ (List.mem_map_of_mem fromTail))
      · intro x hx
        simp only [varsList, List.mem_append] at hx
        rcases hx with inP | inPs
        · obtain ⟨pr, hpr, rfl⟩ := List.mem_map.mp (hcover₁ x inP)
          exact List.mem_map_of_mem (merge_keys_left tb hb b hm pr hpr)
        · exact merge_keys_right tb hb b hm x (hcover₂ x inPs)
end

/-! ## At most one match -/

mutual
/-- An encoded pattern matches an encoded term in at most one way: encodings have no collection
nodes, so the matcher's choices of the multiset case never arise. -/
theorem matchPattern_length_le_one : ∀ (p t : Tm S),
    (matchPattern (enc name p) (enc name t)).length ≤ 1
  | .var x, t => by simp [matchPattern_fvar]
  | .app f ps, .var y => by simp [enc_app, matchPattern_apply_fvar]
  | .app f ps, .app g ts => by
      rw [enc_app, enc_app, matchPattern_apply_apply]
      split
      · rw [← encList_eq, ← encList_eq]; exact matchArgs_length_le_one ps ts
      · simp
/-- Argument lists match in at most one way. -/
theorem matchArgs_length_le_one : ∀ (ps ts : List (Tm S)),
    (matchArgs (encList name ps) (encList name ts)).length ≤ 1
  | [], [] => by simp [encList, matchArgs_nil_nil]
  | [], t :: ts => by simp [encList, matchArgs_nil_cons]
  | p :: ps, [] => by simp [encList, matchArgs_cons_nil]
  | p :: ps, t :: ts => by
      simp only [encList, matchArgs_cons]
      have h₁ := matchPattern_length_le_one p t
      have h₂ := matchArgs_length_le_one ps ts
      generalize matchPattern (enc name p) (enc name t) = A at h₁ ⊢
      generalize matchArgs (encList name ps) (encList name ts) = B at h₂ ⊢
      rcases A with _ | ⟨a, _ | ⟨a', A⟩⟩
      · simp
      · rcases B with _ | ⟨b, _ | ⟨b', B⟩⟩
        · simp
        · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.filterMap_cons,
            List.filterMap_nil]
          split <;> simp
        · simp at h₂
      · simp at h₁
end

/-! ## The presentation -/

variable (name)

/-- **The rewrite rule of an equation**: unconditional, between the encoded sides. -/
def encRule (e : Equation S) : RewriteRule :=
  { name := "equation", typeContext := [], premises := [], left := enc name e.lhs,
    right := enc name e.rhs }

/-- **The presentation of a program**: its equations as rewrite rules. -/
def presentation (P : Program S) : LanguageDef :=
  { name := "declaration", types := [], terms := [], equations := [],
    rewrites := P.map (encRule name) }

variable {name}

/-- **The root reducts of the presentation are exactly MeTTa's root steps.** -/
theorem mem_rootReducts_presentation_iff (inj : Function.Injective name) {P : Program S}
    (linear : P.LeftLinear) (bound : P.RightBound) (s : Tm S) (u : Pattern) :
    u ∈ rootReducts (presentation name P) (enc name s) ↔ ∃ t, u = enc name t ∧ RootStep P s t := by
  simp only [rootReducts, presentation, List.flatMap_map, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨e, he, b, hb, rfl⟩
    obtain ⟨σ, hσ, hcons, _, hcover⟩ := matchPattern_sound inj e.lhs s b hb (linear e he)
    refine ⟨e.rhs.subst σ, ?_, hσ ▸ RootStep.rule σ he⟩
    exact applyBindings_enc name hcons e.rhs fun x hx => hcover x (bound e he x hx)
  · rintro ⟨t, rfl, step⟩
    obtain ⟨e, he, σ, rfl, rfl⟩ := step.exists_rule
    obtain ⟨b, hb, hcons, hcover⟩ := matchPattern_complete name σ e.lhs
    exact ⟨e, he, b, hb, applyBindings_enc name hcons e.rhs fun x hx => hcover x (bound e he x hx)⟩

/-- **The root reducts of the presentation are MeTTa's call results, encoded, as lists**: with the
same order and the same multiplicities. -/
theorem rootReducts_presentation (inj : Function.Injective name) [DecidableEq S] {P : Program S}
    (linear : P.LeftLinear) (bound : P.RightBound) (s : Tm S) :
    rootReducts (presentation name P) (enc name s) = (rootResults P s).map (enc name) := by
  simp only [rootReducts, presentation, rootResults, List.flatMap_map]
  induction P with
  | nil => rfl
  | cons e rest ih =>
      have linear' : Program.LeftLinear rest := fun e' h => linear e' (List.mem_cons_of_mem e h)
      have bound' : Program.RightBound rest := fun e' h => bound e' (List.mem_cons_of_mem e h)
      simp only [List.flatMap_cons, List.filterMap_cons, ih linear' bound']
      have one := matchPattern_length_le_one (name := name) e.lhs s
      cases hm : matchTm e.lhs s with
      | none =>
          have empty : matchPattern (enc name e.lhs) (enc name s) = [] := by
            apply List.eq_nil_iff_forall_not_mem.mpr
            intro b hb
            obtain ⟨σ, hσ, _, _, _⟩ := matchPattern_sound inj e.lhs s b hb (linear e List.mem_cons_self)
            obtain ⟨b', hb', _⟩ := matchTm_complete e.lhs σ
            rw [hσ, hm] at hb'
            cases hb'
          simp only [encRule] at empty ⊢
          simp [empty]
      | some bindings =>
          obtain ⟨keys', inst⟩ := matchTm_sound e.lhs s bindings hm
          have linearE := linear e List.mem_cons_self
          have agree := agrees_lookup (by rw [keys']; exact linearE)
          have hs : e.lhs.subst (lookup bindings) = s := inst _ agree
          obtain ⟨b, hb, hcons, hcover⟩ := matchPattern_complete name (lookup bindings) e.lhs
          rw [hs] at hb
          have single : matchPattern (enc name e.lhs) (enc name s) = [b] := by
            match h : matchPattern (enc name e.lhs) (enc name s), one with
            | [], _ => rw [h] at hb; cases hb
            | [c], _ => rw [h, List.mem_singleton] at hb; rw [hb]
            | _ :: _ :: _, le => simp at le
          simp only [encRule, single, List.map_cons, List.map_nil, Option.map_some,
            List.cons_append, List.nil_append]
          congr 1
          exact applyBindings_enc name hcons e.rhs fun x hx => hcover x (bound e List.mem_cons_self x hx)

/-- Every rule of the presentation is unconditional and binder-free. -/
theorem presentation_unconditional (P : Program S) :
    isUnconditionalAligned (presentation name P) = true := by
  simp only [isUnconditionalAligned, presentation, List.all_map, List.all_eq_true,
    Function.comp_apply, Bool.and_eq_true]
  intro e _
  exact ⟨rfl, ruleDepthAligned_of_binderFree _ (binderFree_enc name _) (binderFree_enc name _)⟩

/-- **The canonical one-step semantics of the presentation is MeTTa's root step.** -/
theorem canonical_step_iff_rootStep (inj : Function.Injective name) {P : Program S}
    (linear : P.LeftLinear) (bound : P.RightBound) (base : BasePremiseEvaluator) (s : Tm S)
    (u : Pattern) :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step base (presentation name P) (enc name s) u ↔
      ∃ t, u = enc name t ∧ RootStep P s t :=
  (step_iff_mem_rootReducts base _ (presentation_unconditional P) _ _).trans
    (mem_rootReducts_presentation_iff inj linear bound s u)

open Mettapedia.OSLF.Framework.GeneralCanonicalAgreement in
/-- **The compiled general semantics of the presentation is MeTTa's root step**, wherever the
existing decidable root profile holds and the source is well sorted. -/
theorem general_step_iff_rootStep (inj : Function.Injective name) {P : Program S}
    (linear : P.LeftLinear) (bound : P.RightBound)
    {type : Mettapedia.OSLF.MeTTaIL.Syntax.TypeExpr}
    (profile : RootProfile (presentation name P) type)
    (boundTypes : List Mettapedia.OSLF.MeTTaIL.Syntax.TypeExpr) {s : Tm S} {u : Pattern}
    (typed : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      (rootPlan (presentation name P)).snapshot.language
      (rootPlan (presentation name P)).snapshot.free boundTypes type (enc name s)) :
    (Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceSemantics.gslt (rootPlan (presentation name P))
        boundTypes type).Step (enc name s) u ↔
      ∃ t, u = enc name t ∧ RootStep P s t :=
  (profile.general_step_iff_rootReducts boundTypes typed).trans
    (mem_rootReducts_presentation_iff inj linear bound s u)

/-- The closure of a relation under argument positions. -/
inductive Congruence (R : Tm S → Tm S → Prop) : Tm S → Tm S → Prop where
  | root {s t : Tm S} : R s t → Congruence R s t
  | arg (f : S) (args : List (Tm S)) (i : Nat) (lt : i < args.length) {t : Tm S} :
      Congruence R args[i] t → Congruence R (.app f args) (.app f (args.set i t))

/-- **MeTTa's evaluation is the congruence closure of the presentation's canonical step.** -/
theorem step_iff_congruence (inj : Function.Injective name) {P : Program S}
    (linear : P.LeftLinear) (bound : P.RightBound) (base : BasePremiseEvaluator) (s t : Tm S) :
    Step P s t ↔ Congruence (fun a b =>
      Mettapedia.OSLF.MeTTaIL.ContextualStep.Step base (presentation name P) (enc name a) (enc name b)) s t := by
  constructor
  · intro step
    induction step with
    | root root => exact .root ((canonical_step_iff_rootStep inj linear bound base _ _).mpr ⟨_, rfl, root⟩)
    | arg f args i lt _ ih => exact .arg f args i lt ih
  · intro congruence
    induction congruence with
    | root canonical =>
        obtain ⟨t', same, root⟩ := (canonical_step_iff_rootStep inj linear bound base _ _).mp canonical
        rw [enc_injective name inj same]
        exact .root root
    | arg f args i lt _ ih => exact .arg f args i lt ih

/-! ## Examples -/

namespace Examples

open Controls

/-- **Positive example**: the canonical step of the presentation of addition relates
`(add (S Z) Z)` to `(S (add Z Z))`. -/
theorem add_canonical_step (base : BasePremiseEvaluator) :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step base (presentation id Controls.addProgram)
      (enc id (.app "add" [num 1, num 0])) (enc id (.app "S" [.app "add" [num 0, num 0]])) := by
  apply (canonical_step_iff_rootStep Function.injective_id add_adm.leftLinear add_adm.rightBound
    base _ _).mpr
  refine ⟨_, rfl, ?_⟩
  have := RootStep.rule (P := Controls.addProgram)
    (e := ⟨.app "add" [.app "S" [.var "m"], .var "n"], .app "S" [.app "add" [.var "m", .var "n"]]⟩)
    (fun x => if x = "m" then num 0 else num 0) (by simp [Controls.addProgram])
  simpa [num] using this

/-- **Negative example**: the encoding of a constructor term has no root reduct. -/
theorem value_no_root_reduct :
    rootReducts (presentation id Controls.addProgram) (enc id (num 1)) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro u hu
  obtain ⟨t, _, root⟩ := (mem_rootReducts_presentation_iff Function.injective_id add_adm.leftLinear
    add_adm.rightBound _ u).mp hu
  have value : IsValue Controls.addProgram (num 1) :=
    (show addSig.IsData (num 1) from .app (by decide) fun a ha => by
      simp [num] at ha; subst ha; exact .app (by decide) (by simp)).isValue add_adm.wellFormed
      add_adm.typed
  exact value.normal add_adm.typed.headed t (.root root)

end Examples

end Mettapedia.Languages.MeTTa.DeclarationFaces

import Mettapedia.Languages.MeTTa.DeclarationFaces.Intensional

/-!
# Admission implies the orthogonality test of the λΠ-modulo theory

For every admitted declaration and every injective naming of symbols, the translated rules pass the
tree's decidable orthogonality test (`Admitted.orthogonalCheck_translation`), so the theory of the
declaration is confluent and the normal-form fiber and adequacy hold with no further hypothesis
(`Admitted.normalFormFiber'`, `Admitted.dedukti_normalForm_iff'`).

The test asks five things of each translated rule, and each comes from admission:

* the left side is a constant applied to patterns (`algebraic_tr_app`), from the constructor
  discipline;
* its pattern variables are distinct (`patternVars_tr`), from linearity;
* the right side uses only them (`usesOnly_tr`), from bound right sides;
* no headed proper part of a left side can be an instance of a left side: such a part is a partial
  application of the defined head, too short to be an instance of any equation of that head (all have
  its declared number of arguments), or an application of a constructor, which heads no equation
  (`mem_subpatterns_spine`, `clashes_of_heads`);
* two left sides clash (`clashes_tr_of_clash`), from the non-overlap check.

Two applications of constants clash when their heads or their numbers of arguments differ: a common
instance would have one head and one depth of application (`clashes_false_heads`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.DeclarationFaces

open Tm
open Mettapedia.GSLT.LanguageDef.LF (Term)
open Mettapedia.GSLT.Dedukti (algebraic patternVars subpatterns usesOnly clashes ruleChecked
  orthogonalCheck headConst)
open Mettapedia.Logic.Relation (Confluent DecidedOn)

universe u

/-! ## Spines -/

theorem spine_cons (head a : Term) (as : List Term) : spine head (a :: as) = spine (.app head a) as :=
  rfl

/-- The number of applications along the function position. -/
def appDepth : Term → Nat
  | .app function _ => appDepth function + 1
  | _ => 0

theorem appDepth_spine : ∀ (args : List Term) (head : Term),
    appDepth (spine head args) = appDepth head + args.length
  | [], head => rfl
  | a :: as, head => by
      rw [spine_cons, appDepth_spine as (.app head a)]
      simp [appDepth]; omega

/-- **Terms that do not clash have one head and one depth of application.** -/
theorem clashes_false_heads : ∀ (s t : Term), clashes s t = false → ∀ a b : String,
    headConst s = some a → headConst t = some b → appDepth s = appDepth t ∧ a = b := by
  intro s
  induction s with
  | con a =>
      intro t h a' b ha hb
      simp only [headConst, Option.some.injEq] at ha
      subst ha
      cases t with
      | con b' =>
          simp only [headConst, Option.some.injEq] at hb
          subst hb
          simp only [clashes, bne_eq_false_iff_eq] at h
          exact ⟨rfl, h⟩
      | app _ _ => simp [clashes] at h
      | _ => simp [headConst] at hb
  | app f x ihf _ =>
      intro t h a b ha hb
      cases t with
      | app f' x' =>
          simp only [clashes, Bool.or_eq_false_iff] at h
          simp only [headConst] at ha hb
          obtain ⟨depth, same⟩ := ihf f' h.1 a b ha hb
          exact ⟨by simp [appDepth, depth], same⟩
      | con _ => simp [clashes] at h
      | _ => simp [headConst] at hb
  | _ => intro t _ a b ha; simp [headConst] at ha

/-- **Applications of constants with different heads or numbers of arguments clash.** -/
theorem clashes_of_heads {a b : String} {xs ys : List Term} (differ : a ≠ b ∨ xs.length ≠ ys.length) :
    clashes (spine (.con a) xs) (spine (.con b) ys) = true := by
  cases h : clashes (spine (.con a) xs) (spine (.con b) ys) with
  | true => rfl
  | false =>
      exfalso
      obtain ⟨depth, same⟩ := clashes_false_heads _ _ h a b (headConst_spine a xs) (headConst_spine b ys)
      rw [appDepth_spine, appDepth_spine] at depth
      simp [appDepth] at depth
      rcases differ with ne | ne
      · exact ne same
      · exact ne depth

/-- Some pair at one position clashes. -/
def clashesPairs : List Term → List Term → Bool
  | x :: xs, y :: ys => clashes x y || clashesPairs xs ys
  | _, _ => false

theorem clashes_spine_same_length : ∀ (xs ys : List Term) (h h' : Term), xs.length = ys.length →
    clashes (spine h xs) (spine h' ys) = (clashes h h' || clashesPairs xs ys)
  | [], [], h, h', _ => by simp [spine, clashesPairs]
  | x :: xs, y :: ys, h, h', len => by
      rw [spine_cons, spine_cons, clashes_spine_same_length xs ys (.app h x) (.app h' y)
        (by simpa using len)]
      simp only [clashes, clashesPairs, Bool.or_assoc]
  | [], _ :: _, _, _, len => by simp at len
  | _ :: _, [], _, _, len => by simp at len

/-! ## Clashes transfer to translations -/

section Translation

variable {S : Type u} [DecidableEq S] (name : S → String)

theorem clashList_spec : ∀ (ps qs : List (Tm S)), clashList ps qs = true →
    ps.length ≠ qs.length ∨ ∃ i, ∃ (hi : i < ps.length) (hj : i < qs.length), clash ps[i] qs[i] = true
  | [], [], h => by simp [clashList] at h
  | p :: ps, q :: qs, h => by
      simp only [clashList, Bool.or_eq_true] at h
      rcases h with h | h
      · exact .inr ⟨0, by simp, by simp, by simpa using h⟩
      · rcases clashList_spec ps qs h with len | ⟨i, hi, hj, hc⟩
        · exact .inl (by simpa using len)
        · exact .inr ⟨i + 1, by simpa using hi, by simpa using hj, by simpa using hc⟩
  | [], _ :: _, _ => .inl (by simp)
  | _ :: _, [], _ => .inl (by simp)

theorem clashesPairs_of_getElem : ∀ (xs ys : List Term) (i : Nat) (hi : i < xs.length)
    (hj : i < ys.length), clashes xs[i] ys[i] = true → clashesPairs xs ys = true
  | x :: xs, y :: ys, 0, _, _, h => by simp only [clashesPairs, Bool.or_eq_true]; exact .inl h
  | x :: xs, y :: ys, i + 1, hi, hj, h => by
      simp only [clashesPairs, Bool.or_eq_true]
      exact .inr (clashesPairs_of_getElem xs ys i (by simpa using hi) (by simpa using hj) (by simpa using h))
  | [], _, _, hi, _, _ => absurd hi (Nat.not_lt_zero _)
  | _ :: _, [], _, _, hj, _ => absurd hj (Nat.not_lt_zero _)

/-- **Clashing terms translate to clashing terms**, at any indices of variables. -/
theorem clashes_tr_of_clash (inj : Function.Injective name) (ix ix' : String → Nat) :
    ∀ p q : Tm S, clash p q = true → clashes (trWith name ix p) (trWith name ix' q) = true := by
  intro p
  induction p using Tm.induction' with
  | var x => intro q h; simp [clash] at h
  | app f ps ih =>
      intro q h
      cases q with
      | var y => simp [clash] at h
      | app g qs =>
          simp only [clash, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
          rw [trWith_app, trWith_app]
          rcases h with ne | inner
          · exact clashes_of_heads (.inl fun same => ne (inj same))
          · by_cases hlen : ps.length = qs.length
            · rcases clashList_spec ps qs inner with len | ⟨i, hi, hj, hc⟩
              · exact absurd hlen len
              · rw [clashes_spine_same_length _ _ _ _ (by simpa using hlen)]
                simp only [Bool.or_eq_true]
                right
                apply clashesPairs_of_getElem _ _ i (by simpa using hi) (by simpa using hj)
                simpa using ih _ (List.getElem_mem hi) _ hc
            · exact clashes_of_heads (.inr (by simpa using hlen))

end Translation

/-! ## The parts of a translation -/

theorem algebraic_spine_cons (b : Bool) : ∀ (as : List Term) (h a : Term),
    algebraic b (spine h (a :: as)) = (algebraic true h && (a :: as).all (algebraic false))
  | [], h, a => by simp [spine, algebraic]
  | a' :: as, h, a => by
      rw [spine_cons, algebraic_spine_cons b as (.app h a) a']
      simp [algebraic, Bool.and_assoc]

theorem patternVars_spine : ∀ (as : List Term) (h : Term),
    patternVars (spine h as) = patternVars h ++ as.flatMap patternVars
  | [], h => by simp [spine]
  | a :: as, h => by
      rw [spine_cons, patternVars_spine as (.app h a)]
      simp [patternVars]

theorem usesOnly_spine (allowed : List Nat) (depth : Nat) : ∀ (as : List Term) (h : Term),
    usesOnly allowed depth (spine h as) = (usesOnly allowed depth h && as.all (usesOnly allowed depth))
  | [], h => by simp [spine]
  | a :: as, h => by
      rw [spine_cons, usesOnly_spine allowed depth as (.app h a)]
      simp [Mettapedia.GSLT.Dedukti.usesOnly, Bool.and_assoc]

theorem mem_subpatterns_spine : ∀ (as : List Term) (h part : Term), part ∈ subpatterns (spine h as) →
    part ∈ subpatterns h ∨ (∃ k < as.length, part = spine h (as.take k)) ∨
      ∃ a ∈ as, part = a ∨ part ∈ subpatterns a
  | [], h, part, hp => .inl (by simpa [spine] using hp)
  | a :: as, h, part, hp => by
      rw [spine_cons] at hp
      rcases mem_subpatterns_spine as (.app h a) part hp with inHead | ⟨k, hk, rfl⟩ | ⟨b, hb, hpart⟩
      · simp only [subpatterns, List.mem_cons, List.mem_append] at inHead
        rcases inHead with rfl | rfl | inH | inA
        · exact .inr (.inl ⟨0, by simp, by simp [spine]⟩)
        · exact .inr (.inr ⟨part, List.mem_cons_self, .inl rfl⟩)
        · exact .inl inH
        · exact .inr (.inr ⟨a, List.mem_cons_self, .inr inA⟩)
      · exact .inr (.inl ⟨k + 1, by simpa using hk, by simp [spine_cons]⟩)
      · exact .inr (.inr ⟨b, List.mem_cons_of_mem a hb, hpart⟩)

section Parts

variable {S : Type u} (name : S → String)

theorem algebraic_false_tr (ix : String → Nat) : ∀ t : Tm S, algebraic false (trWith name ix t) = true := by
  intro t
  induction t using Tm.induction' with
  | var x => simp [trWith, algebraic]
  | app f args ih =>
      rw [trWith_app]
      cases args with
      | nil => simp [spine, algebraic]
      | cons a as =>
          simp only [List.map_cons]
          rw [algebraic_spine_cons]
          simp only [algebraic, Bool.true_and, List.all_eq_true]
          intro b hb
          rcases List.mem_cons.mp hb with rfl | hb'
          · exact ih a List.mem_cons_self
          · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb'
            exact ih c (List.mem_cons_of_mem a hc)

theorem algebraic_tr_app (ix : String → Nat) (f : S) (args : List (Tm S)) :
    algebraic true (trWith name ix (.app f args)) = true := by
  rw [trWith_app]
  cases args with
  | nil => simp [spine, algebraic]
  | cons a as =>
      simp only [List.map_cons]
      rw [algebraic_spine_cons]
      simp only [algebraic, Bool.true_and, List.all_eq_true]
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact algebraic_false_tr name ix a
      · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb'
        exact algebraic_false_tr name ix c

theorem patternVars_tr (ix : String → Nat) : ∀ t : Tm S, patternVars (trWith name ix t) = t.vars.map ix := by
  intro t
  induction t using Tm.induction' with
  | var x => simp [trWith, patternVars]
  | app f args ih =>
      rw [trWith_app, patternVars_spine]
      simp only [patternVars, List.nil_append, vars_app, List.flatMap_map, List.map_flatMap]
      exact List.flatMap_congr fun a ha => ih a ha

theorem usesOnly_tr (ix : String → Nat) (allowed : List Nat) : ∀ t : Tm S,
    (∀ x ∈ t.vars, ix x ∈ allowed) → usesOnly allowed 0 (trWith name ix t) = true := by
  intro t
  induction t using Tm.induction' with
  | var x => intro h; simpa [trWith, Mettapedia.GSLT.Dedukti.usesOnly] using h x (by simp)
  | app f args ih =>
      intro h
      rw [trWith_app, usesOnly_spine]
      simp only [Mettapedia.GSLT.Dedukti.usesOnly, Bool.true_and, List.all_eq_true]
      intro b hb
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
      exact ih c hc fun x hx => h x (by simpa using ⟨c, hc, hx⟩)

/-- A part headed by a constant of a set: a constant of the set applied to terms. -/
def HeadedIn (C : String → Prop) (part : Term) : Prop := ∃ c ys, C c ∧ part = spine (.con c) ys

/-- **Every headed part of the translation of a constructor pattern is headed by a constructor.** -/
theorem parts_of_pattern {sig : Signature S} (ix : String → Nat) :
    ∀ {p : Tm S}, IsPattern sig p → ∀ part, (part = trWith name ix p ∨ part ∈ subpatterns (trWith name ix p)) →
      algebraic true part = true → HeadedIn (fun c => ∃ k ∈ sig.ctorNames, name k = c) part := by
  intro p pattern
  induction pattern with
  | var x =>
      intro part hp headed
      rcases hp with rfl | hp
      · simp [trWith, algebraic] at headed
      · simp [trWith, subpatterns] at hp
  | @ctor c args isCtor _ ih =>
      intro part hp headed
      rw [trWith_app] at hp
      rcases hp with rfl | hp
      · exact ⟨name c, _, ⟨c, isCtor, rfl⟩, rfl⟩
      · rcases mem_subpatterns_spine _ _ part hp with inCon | ⟨k, _, rfl⟩ | ⟨b, hb, hpart⟩
        · simp [subpatterns] at inCon
        · exact ⟨name c, _, ⟨c, isCtor, rfl⟩, rfl⟩
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb
          exact ih q hq part hpart headed

end Parts

/-! ## The test -/

section Test

variable {S : Type u} [DecidableEq S] {name : S → String}

mutual
theorem clash_comm : ∀ p q : Tm S, clash p q = clash q p
  | .var _, .var _ => rfl
  | .var _, .app _ _ => rfl
  | .app _ _, .var _ => rfl
  | .app f ps, .app g qs => by
      simp only [clash, clashList_comm ps qs]
      by_cases h : f = g
      · subst h; rfl
      · have h' : g ≠ f := fun e => h e.symm
        simp [h, h']
theorem clashList_comm : ∀ ps qs : List (Tm S), clashList ps qs = clashList qs ps
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | p :: ps, q :: qs => by simp only [clashList, clash_comm p q, clashList_comm ps qs]
end

/-- Indices of the variables of a linear left side are distinct. -/
theorem nodup_map_idxOf {l : List String} (nodup : l.Nodup) : (l.map fun x => l.idxOf x).Nodup := by
  apply List.Nodup.map_on _ nodup
  intro x hx y hy same
  have hx' := List.idxOf_lt_length_iff.mpr hx
  have hy' := List.idxOf_lt_length_iff.mpr hy
  calc x = l[l.idxOf x] := (List.getElem_idxOf hx').symm
    _ = l[l.idxOf y] := by simp only [same]
    _ = y := List.getElem_idxOf hy'

namespace Admitted

variable {sig : Signature S} {P : Program S}

/-- **Admission implies the orthogonality test** of the translated rules, for every injective naming. -/
theorem orthogonalCheck_translation (adm : Admitted sig P) (inj : Function.Injective name) :
    orthogonalCheck (P.map (trRule name)) = true := by
  have shape : ∀ e ∈ P, ∃ fd ∈ sig.funs, ∃ ps : List (Tm S), e.lhs = .app fd.name ps ∧
      ps.length = fd.args.length ∧ ∀ p ∈ ps, IsPattern sig p := by
    intro e he
    obtain ⟨fd, hfd, ps, Γ, hl, patterns, ⟨len, _⟩, _⟩ := adm.typed e he
    exact ⟨fd, hfd, ps, hl, len, patterns⟩
  have otherLhs : ∀ other ∈ P.map (trRule name), ∃ fd ∈ sig.funs, ∃ ys : List Term,
      ys.length = fd.args.length ∧ other.lhs = spine (.con (name fd.name)) ys := by
    intro other hother
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp hother
    obtain ⟨fd', hfd', ps', hl', len', _⟩ := shape e' he'
    refine ⟨fd', hfd', ps'.map (trWith name e'.index), by simpa using len', ?_⟩
    show trWith name e'.index e'.lhs = _
    rw [hl', trWith_app]
  simp only [orthogonalCheck, List.all_eq_true]
  intro rule hrule
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hrule
  obtain ⟨fd, hfd, ps, hl, len, patterns⟩ := shape e he
  have lhsTr : (trRule name e).lhs = spine (.con (name fd.name)) (ps.map (trWith name e.index)) := by
    show trWith name e.index e.lhs = _
    rw [hl, trWith_app]
  have linear : e.lhs.vars.Nodup := adm.leftLinear e he
  simp only [ruleChecked, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true']
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · show algebraic true (trWith name e.index e.lhs) = true
    rw [hl]
    exact algebraic_tr_app name e.index fd.name ps
  · show (patternVars (trWith name e.index e.lhs)).Nodup
    rw [patternVars_tr]
    exact nodup_map_idxOf linear
  · show usesOnly (patternVars (trWith name e.index e.lhs)) 0 (trWith name e.index e.rhs) = true
    rw [patternVars_tr]
    exact usesOnly_tr name e.index _ e.rhs fun x hx =>
      List.mem_map_of_mem (adm.rightBound e he x hx)
  · intro part hpart
    rw [lhsTr] at hpart
    rcases mem_subpatterns_spine _ _ part hpart with inCon | ⟨k, hk, rfl⟩ | ⟨b, hb, hb'⟩
    · simp [subpatterns] at inCon
    · right
      intro other hother
      obtain ⟨fd', hfd', ys, ylen, hother'⟩ := otherLhs other hother
      rw [hother']
      apply clashes_of_heads
      by_cases same : fd.name = fd'.name
      · obtain rfl := adm.wellFormed.fun_unique hfd hfd' same
        right
        simp only [List.length_take, List.length_map] at hk ⊢
        omega
      · exact .inl fun h => same (inj h)
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hb
      cases headed : algebraic true part with
      | false => exact .inl rfl
      | true =>
          right
          obtain ⟨c, ys, ⟨k, isCtor, rfl⟩, rfl⟩ :=
            parts_of_pattern name e.index (patterns p hp) part hb' headed
          intro other hother
          obtain ⟨fd', hfd', zs, _, hother'⟩ := otherLhs other hother
          rw [hother']
          refine clashes_of_heads (.inl fun h => ?_)
          have := inj h
          subst this
          exact adm.wellFormed.disjoint fd' hfd' isCtor
  · intro other hother
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp hother
    by_cases same : e = e'
    · exact .inl (congrArg _ same)
    · right
      have symm : Std.Symm (fun e e' : Equation S => clash e.lhs e'.lhs = true) :=
        ⟨fun a b h => by rw [clash_comm]; exact h⟩
      have hc : clash e.lhs e'.lhs = true := List.Pairwise.forall adm.clashing he he' same
      exact clashes_tr_of_clash name inj e.index e'.index _ _ hc

/-- **The theory of every admitted declaration is confluent.** -/
theorem dedukti_confluent' (adm : Admitted sig P) (inj : Function.Injective name) :
    Confluent (Mettapedia.GSLT.Dedukti.Step (declTheory name P)) :=
  dedukti_confluent name (adm.orthogonalCheck_translation inj)

/-- **The normal-form fiber of every admitted declaration**: conversion in its theory on the
translations of closed sorted terms is decided by normalizing both sides. -/
theorem normalFormFiber' (adm : Admitted sig P) (inj : Function.Injective name) (ix : String → Nat) :
    DecidedOn (Mettapedia.GSLT.Dedukti.Step (declTheory name P)) (trWith name ix '' ClosedSorted sig) :=
  adm.normalFormFiber name inj (adm.orthogonalCheck_translation inj) ix

/-- **Adequacy for every admitted declaration**, in both directions. -/
theorem dedukti_normalForm_iff' (adm : Admitted sig P) (inj : Function.Injective name)
    (ix : String → Nat) {t : Tm S} {τ : Sort'} (typed : HasSort sig Ctx.empty t τ) (m : Term) :
    Mettapedia.Logic.Relation.IsNormalFormOf (Mettapedia.GSLT.Dedukti.Step (declTheory name P))
        (trWith name ix t) m ↔
      m = trWith name ix (adm.normalForm t) :=
  adm.dedukti_normalForm_iff name inj (adm.orthogonalCheck_translation inj) ix typed m

end Admitted

end Test

end Mettapedia.Languages.MeTTa.DeclarationFaces

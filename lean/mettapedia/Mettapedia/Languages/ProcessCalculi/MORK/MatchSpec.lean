import Mettapedia.Languages.ProcessCalculi.MORK.Space

/-!
# MORK Match Specification

Relational specification for finite one-way `matchAtom`: variables, symbols,
grounded values and nested expressions. Repeated variables must agree with
their captured binding. This relation does not specify bidirectional or cyclic
unification.
-/

namespace Mettapedia.Languages.ProcessCalculi.MORK

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-- Relational spec for atom matching. -/
inductive MatchAtomRel : Subst → Atom → Atom → Subst → Prop where
  /-- Fresh variable bind. -/
  | var_fresh {σ : Subst} {v : String} {a : Atom}
      (hlookup : σ.lookup v = none) :
      MatchAtomRel σ (.var v) a ((v, a) :: σ)
  /-- Already-bound variable must match the same atom. -/
  | var_bound {σ : Subst} {v : String} {a : Atom}
      (hlookup : σ.lookup v = some a) :
      MatchAtomRel σ (.var v) a σ
  /-- Symbols match only identical symbols. -/
  | symbol {σ : Subst} {s : String} :
      MatchAtomRel σ (.symbol s) (.symbol s) σ
  /-- Grounded values match only identical grounded values. -/
  | grounded {σ : Subst} {g : GroundedValue} :
      MatchAtomRel σ (.grounded g) (.grounded g) σ
  /-- Empty expression matches empty expression. -/
  | expr_nil {σ : Subst} :
      MatchAtomRel σ (.expression []) (.expression []) σ
  /-- Non-empty expression matches element-wise. -/
  | expr_cons {σ σ' σ'' : Subst} {p c : Atom} {ps cs : List Atom}
      (hhead : MatchAtomRel σ p c σ')
      (htail : MatchAtomRel σ' (.expression ps) (.expression cs) σ'') :
      MatchAtomRel σ (.expression (p :: ps)) (.expression (c :: cs)) σ''

/-- Soundness of executable `matchAtom` w.r.t. `MatchAtomRel`.
    Every successful `matchAtom` call corresponds to a `MatchAtomRel` derivation. -/
theorem matchAtom_sound {σ : Subst} {pat conc : Atom} {σ' : Subst}
    (h : matchAtom σ pat conc = some σ') :
    MatchAtomRel σ pat conc σ' := by
  match pat, conc with
  | .var v, a =>
    simp only [matchAtom] at h
    cases hlookup : σ.lookup v with
    | none =>
        simp [hlookup] at h; cases h
        exact MatchAtomRel.var_fresh hlookup
    | some a' =>
        by_cases heq : a == a'
        · simp [hlookup, heq] at h; cases h
          have hca := Atom.eq_of_beq_eq_true (by simpa using heq)
          subst hca; exact MatchAtomRel.var_bound hlookup
        · simp [hlookup, heq] at h
  | .symbol s, .symbol t =>
    simp only [matchAtom] at h
    split at h <;> simp_all
    exact MatchAtomRel.symbol
  | .symbol _, .var _ => simp [matchAtom] at h
  | .symbol _, .grounded _ => simp [matchAtom] at h
  | .symbol _, .expression _ => simp [matchAtom] at h
  | .grounded g, .grounded g' =>
    simp only [matchAtom] at h
    split at h <;> simp_all
    exact MatchAtomRel.grounded
  | .grounded _, .symbol _ => simp [matchAtom] at h
  | .grounded _, .var _ => simp [matchAtom] at h
  | .grounded _, .expression _ => simp [matchAtom] at h
  | .expression ps, .expression cs =>
    simp only [matchAtom] at h
    exact matchAtomList_sound h
  | .expression _, .symbol _ => simp [matchAtom] at h
  | .expression _, .var _ => simp [matchAtom] at h
  | .expression _, .grounded _ => simp [matchAtom] at h
where
  matchAtomList_sound : ∀ {σ : Subst} {ps cs : List Atom} {σ' : Subst},
      matchAtom.matchAtomList σ ps cs = some σ' →
      MatchAtomRel σ (.expression ps) (.expression cs) σ'
    | σ, [], [], σ', h => by
        simp [matchAtom.matchAtomList] at h; cases h; exact MatchAtomRel.expr_nil
    | σ, p :: ps, c :: cs, σ', h => by
        simp [matchAtom.matchAtomList] at h
        cases hm : matchAtom σ p c with
        | none => simp [hm] at h
        | some σ'' =>
          simp [hm] at h
          exact MatchAtomRel.expr_cons
            (matchAtom_sound hm)
            (matchAtomList_sound h)
    | _, [], _ :: _, _, h => by simp [matchAtom.matchAtomList] at h
    | _, _ :: _, [], _, h => by simp [matchAtom.matchAtomList] at h

/-- Completeness of executable `matchAtom` for `MatchAtomRel`.
    Every `MatchAtomRel` derivation is witnessed by `matchAtom`. -/
theorem matchAtom_complete {σ : Subst} {pat conc : Atom} {σ' : Subst}
    (h : MatchAtomRel σ pat conc σ') :
    matchAtom σ pat conc = some σ' := by
  induction h with
  | var_fresh hlookup =>
      simp [matchAtom, hlookup]
  | var_bound hlookup =>
      simp [matchAtom, hlookup]
  | symbol =>
      simp [matchAtom]
  | grounded =>
      simp [matchAtom]
  | expr_nil =>
      simp [matchAtom, matchAtom.matchAtomList]
  | expr_cons _ _ ih_head ih_tail =>
      simp only [matchAtom, matchAtom.matchAtomList, ih_head]
      simp only [matchAtom] at ih_tail
      exact ih_tail

/-- Exact characterization: `matchAtom σ pat conc = some σ' ↔ MatchAtomRel σ pat conc σ'`. -/
theorem matchAtom_iff {σ : Subst} {pat conc : Atom} {σ' : Subst} :
    matchAtom σ pat conc = some σ' ↔ MatchAtomRel σ pat conc σ' :=
  ⟨matchAtom_sound, matchAtom_complete⟩

/-! ## Substitution stability lemmas

The roundtrip property (`matchAtom σ pat conc = some σ' → applySubst σ' pat = conc`)
requires two supporting lemmas:

1. `matchAtom` only extends the substitution in a lookup-stable way: existing
   lookup results are preserved.
2. Applying a ground-producing substitution is stable under lookup extension. -/

/-- Lookup-level extension: σ' extends σ when every existing lookup is preserved.
    Uses fully-qualified `Subst.lookup` to avoid dot-notation resolving to
    `List.lookup` for cons expressions. -/
def Subst.lookupExtends (σ' σ : Subst) : Prop :=
  ∀ v a, Subst.lookup σ v = some a → Subst.lookup σ' v = some a

theorem Subst.lookupExtends_refl (σ : Subst) : σ.lookupExtends σ :=
  fun _ _ h => h

theorem Subst.lookupExtends_trans {σ₁ σ₂ σ₃ : Subst}
    (h₁₂ : σ₂.lookupExtends σ₁) (h₂₃ : σ₃.lookupExtends σ₂) :
    σ₃.lookupExtends σ₁ :=
  fun v a hv => h₂₃ v a (h₁₂ v a hv)

/-- Prepending a fresh binding preserves existing lookups. -/
theorem Subst.lookupExtends_cons_fresh {σ : Subst} {w : String} {b : Atom}
    (hfresh : Subst.lookup σ w = none) :
    Subst.lookupExtends ((w, b) :: σ) σ := by
  intro v a hva
  by_cases hwv : w = v
  · subst hwv; rw [hfresh] at hva; cases hva
  · show Subst.lookup ((w, b) :: σ) v = some a
    unfold Subst.lookup
    simp only [List.find?_cons]
    have hneq : (w == v) = false := beq_eq_false_iff_ne.mpr hwv
    simp only [hneq]
    exact hva

/-- `matchAtom` preserves existing lookups: σ' from matching extends σ. -/
theorem matchAtom_lookupExtends {σ : Subst} {pat conc : Atom} {σ' : Subst}
    (h : matchAtom σ pat conc = some σ') :
    σ'.lookupExtends σ := by
  match pat, conc with
  | .var v, a =>
    simp only [matchAtom] at h
    cases hlookup : Subst.lookup σ v with
    | none =>
      simp [hlookup] at h; subst h
      exact Subst.lookupExtends_cons_fresh hlookup
    | some a' =>
      by_cases heq : a == a'
      · simp [hlookup, heq] at h; subst h; exact Subst.lookupExtends_refl _
      · simp [hlookup, heq] at h
  | .symbol s, .symbol t =>
    simp only [matchAtom] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; exact Subst.lookupExtends_refl _
    · simp at h
  | .grounded g, .grounded g' =>
    simp only [matchAtom] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; exact Subst.lookupExtends_refl _
    · simp at h
  | .expression ps, .expression cs =>
    simp only [matchAtom] at h
    exact matchAtomList_lookupExtends h
  | .symbol _, .var _ => simp [matchAtom] at h
  | .symbol _, .grounded _ => simp [matchAtom] at h
  | .symbol _, .expression _ => simp [matchAtom] at h
  | .grounded _, .var _ => simp [matchAtom] at h
  | .grounded _, .symbol _ => simp [matchAtom] at h
  | .grounded _, .expression _ => simp [matchAtom] at h
  | .expression _, .var _ => simp [matchAtom] at h
  | .expression _, .symbol _ => simp [matchAtom] at h
  | .expression _, .grounded _ => simp [matchAtom] at h
where
  matchAtomList_lookupExtends {σ : Subst} {ps cs : List Atom} {σ' : Subst}
      (h : matchAtom.matchAtomList σ ps cs = some σ') :
      σ'.lookupExtends σ := by
    match ps, cs with
    | [], [] =>
      simp [matchAtom.matchAtomList] at h; cases h; exact Subst.lookupExtends_refl σ
    | [], _ :: _ => simp [matchAtom.matchAtomList] at h
    | _ :: _, [] => simp [matchAtom.matchAtomList] at h
    | p :: ps, c :: cs =>
      simp only [matchAtom.matchAtomList] at h
      cases hm : matchAtom σ p c with
      | none => simp [hm] at h
      | some σ_mid =>
        simp [hm] at h
        exact Subst.lookupExtends_trans
          (matchAtom_lookupExtends hm)
          (matchAtomList_lookupExtends h)

/-- If `applySubst σ a` is ground, then any lookup-extension σ' gives the same result. -/
theorem applySubst_ground_ext {σ σ' : Subst} {a : Atom}
    (hext : σ'.lookupExtends σ)
    (hg : isGroundAtom (applySubst σ a) = true) :
    applySubst σ' a = applySubst σ a := by
  match a with
  | .var v =>
    cases hlookup : Subst.lookup σ v with
    | none => simp only [applySubst, hlookup] at hg; cases hg
    | some b => simp only [applySubst, hlookup, hext v b hlookup]
  | .symbol s => rfl
  | .grounded g => rfl
  | .expression es =>
    simp only [applySubst] at hg ⊢
    congr 1
    exact applySubstList_ground_ext hext hg
where
  applySubstList_ground_ext {σ σ' : Subst} {es : List Atom}
      (hext : σ'.lookupExtends σ)
      (hg : isGroundAtom.isGroundList (applySubst.applySubstList σ es) = true) :
      applySubst.applySubstList σ' es = applySubst.applySubstList σ es := by
    match es with
    | [] => rfl
    | a :: as =>
      simp only [applySubst.applySubstList]
      simp only [applySubst.applySubstList, isGroundAtom.isGroundList,
                  Bool.and_eq_true] at hg
      congr 1
      · exact applySubst_ground_ext hext hg.1
      · exact applySubstList_ground_ext hext hg.2

/-! ## Roundtrip: match then substitute recovers the ground atom -/

/-- General roundtrip: `matchAtom σ pat conc = some σ' → applySubst σ' pat = conc`
    when `conc` is ground. Works for any initial σ.

    The proof uses `matchAtom_lookupExtends` to thread σ stability through the
    expression-cons case, and `applySubst_ground_ext` to transfer head-match
    results across the tail-match's σ extension. -/
theorem matchAtom_applySubst_ground :
    ∀ (σ : Subst) (pat conc : Atom) (σ' : Subst),
    matchAtom σ pat conc = some σ' →
    isGroundAtom conc = true →
    applySubst σ' pat = conc := by
  intro σ pat conc σ' hm hg
  match pat, conc with
  | .var v, a =>
    simp only [matchAtom] at hm
    cases hlookup : σ.lookup v with
    | none =>
      simp [hlookup] at hm; cases hm
      simp [applySubst, Subst.lookup, List.find?]
    | some a' =>
      by_cases heq : a == a'
      · simp [hlookup, heq] at hm; cases hm
        have ha : a = a' := eq_of_beq heq
        simp [applySubst, hlookup, ha]
      · simp [hlookup, heq] at hm
  | .symbol s, .symbol t =>
    simp only [matchAtom] at hm; split at hm <;> simp_all [applySubst]
  | .grounded g, .grounded g' =>
    simp only [matchAtom] at hm; split at hm <;> simp_all [applySubst]
  | .expression ps, .expression cs =>
    simp only [matchAtom] at hm
    simp only [applySubst]
    congr 1
    exact matchAtomList_applySubst_ground hm hg
  | .symbol _, .var _ => simp [matchAtom] at hm
  | .symbol _, .grounded _ => simp [matchAtom] at hm
  | .symbol _, .expression _ => simp [matchAtom] at hm
  | .grounded _, .var _ => simp [matchAtom] at hm
  | .grounded _, .symbol _ => simp [matchAtom] at hm
  | .grounded _, .expression _ => simp [matchAtom] at hm
  | .expression _, .var _ => simp [matchAtom] at hm
  | .expression _, .symbol _ => simp [matchAtom] at hm
  | .expression _, .grounded _ => simp [matchAtom] at hm
where
  matchAtomList_applySubst_ground {σ : Subst} {ps cs : List Atom} {σ' : Subst}
      (hm : matchAtom.matchAtomList σ ps cs = some σ')
      (hg : isGroundAtom (.expression cs) = true) :
      applySubst.applySubstList σ' ps = cs := by
    match ps, cs with
    | [], [] =>
      simp [matchAtom.matchAtomList] at hm; cases hm
      simp [applySubst.applySubstList]
    | [], _ :: _ => simp [matchAtom.matchAtomList] at hm
    | _ :: _, [] => simp [matchAtom.matchAtomList] at hm
    | p :: ps, c :: cs =>
      simp only [matchAtom.matchAtomList] at hm
      cases hm_head : matchAtom σ p c with
      | none => simp [hm_head] at hm
      | some σ_mid =>
        simp [hm_head] at hm
        simp only [applySubst.applySubstList]
        -- Ground decomposition
        simp only [isGroundAtom, isGroundAtom.isGroundList, Bool.and_eq_true] at hg
        -- Head: applySubst σ_mid p = c, then stable under extension to σ'
        have hhead_rt := matchAtom_applySubst_ground σ p c σ_mid hm_head hg.1
        have htail_ext := matchAtom_lookupExtends.matchAtomList_lookupExtends hm
        have hhead_ground : isGroundAtom (applySubst σ_mid p) = true := by
          rw [hhead_rt]; exact hg.1
        have hhead_stable := applySubst_ground_ext htail_ext hhead_ground
        -- Tail: recursive call
        have htail_ground : isGroundAtom (.expression cs) = true := by
          simp [isGroundAtom]; exact hg.2
        have htail_rt := matchAtomList_applySubst_ground hm htail_ground
        have hhead_final : applySubst σ' p = c := by rw [hhead_stable, hhead_rt]
        simp only [hhead_final, htail_rt]

/-- The independent match derivation materializes its own ground subject. -/
theorem MatchAtomRel.applySubst_ground {seed after : Subst} {pattern value : Atom}
    (matched : MatchAtomRel seed pattern value after) (ground : isGroundAtom value = true) :
    applySubst after pattern = value :=
  matchAtom_applySubst_ground seed pattern value after (matchAtom_complete matched) ground

/-- Every variable visited in a successful structural match has an actual
capture in the final substitution, including repeated variables. -/
theorem MatchAtomRel.lookup_covered {seed after : Subst} {pattern subject : Atom}
    (matched : MatchAtomRel seed pattern subject after) :
    ∀ name ∈ atomFreeVars pattern, ∃ value, after.lookup name = some value := by
  induction matched with
  | @var_fresh seed name value fresh =>
      intro other member
      have same : other = name := by simpa only [atomFreeVars,List.mem_singleton] using member
      subst other
      exact ⟨value,by simp [Subst.lookup]⟩
  | @var_bound seed name value found =>
      intro other member
      have same : other = name := by simpa only [atomFreeVars,List.mem_singleton] using member
      subst other
      exact ⟨value,found⟩
  | symbol | grounded | expr_nil => simp [atomFreeVars,atomFreeVars.atomFreeVarsList]
  | expr_cons first tail headIH tailIH =>
      intro name member
      simp only [atomFreeVars,atomFreeVars.atomFreeVarsList,List.mem_append] at member
      rcases member with head | rest
      · obtain ⟨value,found⟩ := headIH name head
        exact ⟨value,matchAtom_lookupExtends (matchAtom_complete tail) name value found⟩
      · exact tailIH name rest

section Canaries

#check @MatchAtomRel
#check @matchAtom_sound
#check @matchAtom_complete
#check @matchAtom_iff

end Canaries

end Mettapedia.Languages.ProcessCalculi.MORK


namespace Mettapedia.Languages.ProcessCalculi.MORK

/-- Original source freshness observes guest variables inside captured Atom
values. It does not use freshness of their inert ground-data representation. -/
inductive SourceGuardHolds (substitution : Subst) : SourceGuard → Prop where
  | unbound {name : String} {subject : MeTTa.OSLFCore.Atom}
      (unbound : substitution.lookup name = none)
      (fresh : name ∉ atomFreeVars (applySubst substitution subject)) :
      SourceGuardHolds substitution (.freshness name subject)
  | captured {name resolved : String} {subject : MeTTa.OSLFCore.Atom}
      (captured : substitution.lookup name = some (.var resolved))
      (fresh : resolved ∉ atomFreeVars (applySubst substitution subject)) :
      SourceGuardHolds substitution (.freshness name subject)

@[simp] theorem matchSourceGuard_exact (substitution : Subst) (guard : SourceGuard) :
    matchSourceGuard substitution guard = true ↔ SourceGuardHolds substitution guard := by
  constructor
  · intro checked
    cases guard with
    | freshness name subject =>
      cases selected : substitution.lookup name with
      | none =>
          have fresh : name ∉ atomFreeVars (applySubst substitution subject) := by
            simpa [matchSourceGuard, selected, isAtomFresh] using checked
          exact .unbound selected fresh
      | some value =>
          cases value with
          | var resolved =>
              have fresh : resolved ∉ atomFreeVars (applySubst substitution subject) := by
                simpa [matchSourceGuard, selected, isAtomFresh] using checked
              exact .captured selected fresh
          | symbol _ | grounded _ | expression _ =>
              simp [matchSourceGuard, selected] at checked
  · intro held
    cases held with
    | unbound absent fresh => simp [matchSourceGuard, absent, isAtomFresh, fresh]
    | captured present fresh => simp [matchSourceGuard, present, isAtomFresh, fresh]

theorem matchSourceGuard_refused_exact (substitution : Subst) (guard : SourceGuard) :
    matchSourceGuard substitution guard = false ↔ ¬ SourceGuardHolds substitution guard := by
  rw [← matchSourceGuard_exact]
  exact Bool.eq_false_iff

@[simp] theorem matchSourceGuards_exact (substitution : Subst) (guards : List SourceGuard) :
    matchSourceGuards substitution guards = true ↔
      ∀ guard ∈ guards, SourceGuardHolds substitution guard := by
  simp only [matchSourceGuards, List.all_eq_true, matchSourceGuard_exact]

end Mettapedia.Languages.ProcessCalculi.MORK

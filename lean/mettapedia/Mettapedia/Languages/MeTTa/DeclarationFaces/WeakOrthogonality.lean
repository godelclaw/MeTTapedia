import Mettapedia.Languages.MeTTa.DeclarationFaces.Comprehension

/-!
# The orthogonality alternative: overlaps whose results agree

Confluence uses only that a call has at most one result as a term (`Orthogonal.rootDeterministic`).
Non-overlap gives that; so do equations that overlap with agreeing right sides, as the parallel
disjunction does:

    (= (or True $x) True)    (= (or $x True) True)    (= (or False False) False)

The first two share the instance `(or True True)`, and both give `True`.

* Admission refuses the declaration as an overlap (`or_refused`).
* Its root steps are deterministic (`or_rootDeterministic`), so with its descent it is confluent
  (`or_confluent`) and every term has one normal form.
* **The multiset of results is not a function of the term's value**: the evaluator returns
  `True` twice for `(or True True)`, once per matching equation (`or_true_true_twice`), while
  `(or True False)` gives it once. Read as a set, the results agree with the normal form; read as a
  bag, they count the equations that matched.

So agreeing overlaps are admissible exactly for the set reading of results; MeTTa's results are
multisets, so admission refuses them unless the bag reading is quotiented to its support.

**A decidable check** (`agreeingCheck`, `rootDeterministic_of_agreeingCheck`): two left sides with
disjoint variables either clash, or have a unifier computed by `unify`, at which their right sides
must be equal. Every common instance factors through that unifier (`unify_factor`), so the check
makes root steps deterministic, and with termination the program is confluent
(`confluent_of_agreeingCheck`). The parallel disjunction, written with disjoint variables, passes it
(`or_agreeing`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.DeclarationFaces

open Tm

universe u

variable {S : Type u} [DecidableEq S]

mutual
/-- **Unify two terms**, binding the variable of each side to the other side's subterm. -/
def unify : Tm S → Tm S → Option (List (String × Tm S))
  | .var x, t => some [(x, t)]
  | .app f ps, .var y => some [(y, .app f ps)]
  | .app f ps, .app g qs => if f = g then unifyList ps qs else none
/-- Unify two lists of terms position by position. -/
def unifyList : List (Tm S) → List (Tm S) → Option (List (String × Tm S))
  | [], [] => some []
  | p :: ps, q :: qs =>
      match unify p q, unifyList ps qs with
      | some a, some b => some (a ++ b)
      | _, _ => none
  | _, _ => none
end

mutual
/-- **Every common instance factors through the unifier**: a substitution that makes two terms equal
sends each binding's value to the substitution's value at its variable. -/
theorem unify_factor (ρ : String → Tm S) : ∀ (p q : Tm S) (b : List (String × Tm S)),
    unify p q = some b → p.subst ρ = q.subst ρ → ∀ pr ∈ b, pr.2.subst ρ = ρ pr.1
  | .var x, t, b, h, same, pr, hpr => by
      simp only [unify, Option.some.injEq] at h
      subst h
      simp only [List.mem_singleton] at hpr
      subst hpr
      simpa using same.symm
  | .app f ps, .var y, b, h, same, pr, hpr => by
      simp only [unify, Option.some.injEq] at h
      subst h
      simp only [List.mem_singleton] at hpr
      subst hpr
      simpa using same
  | .app f ps, .app g qs, b, h, same, pr, hpr => by
      simp only [unify] at h
      split at h
      · rename_i hfg
        subst hfg
        simp only [subst, app.injEq, true_and] at same
        exact unifyList_factor ρ ps qs b h same pr hpr
      · cases h
/-- Factoring for lists. -/
theorem unifyList_factor (ρ : String → Tm S) : ∀ (ps qs : List (Tm S)) (b : List (String × Tm S)),
    unifyList ps qs = some b → substList ρ ps = substList ρ qs → ∀ pr ∈ b, pr.2.subst ρ = ρ pr.1
  | [], [], b, h, _, pr, hpr => by
      simp only [unifyList, Option.some.injEq] at h
      subst h
      cases hpr
  | p :: ps, q :: qs, b, h, same, pr, hpr => by
      simp only [unifyList] at h
      split at h
      · rename_i a c ha hc
        simp only [Option.some.injEq] at h
        subst h
        simp only [substList, List.cons.injEq] at same
        rcases List.mem_append.mp hpr with inA | inC
        · exact unify_factor ρ p q a ha same.1 pr inA
        · exact unifyList_factor ρ ps qs c hc same.2 pr inC
      · cases h
  | [], _ :: _, b, h, _, _, _ => by simp [unifyList] at h
  | _ :: _, [], b, h, _, _, _ => by simp [unifyList] at h
end

mutual
/-- **Unification fails only where no common instance exists.** -/
theorem unify_complete_none : ∀ {p q : Tm S}, unify p q = none → ∀ ρ : String → Tm S,
    p.subst ρ = q.subst ρ → False
  | .var x, t, h, _, _ => by simp [unify] at h
  | .app f ps, .var y, h, _, _ => by simp [unify] at h
  | .app f ps, .app g qs, h, ρ, same => by
      simp only [unify] at h
      simp only [subst, app.injEq] at same
      split at h
      · rename_i hfg
        exact unifyList_complete_none h ρ same.2
      · rename_i hfg
        exact hfg same.1
/-- Unification of lists fails only where no common instance exists. -/
theorem unifyList_complete_none : ∀ {ps qs : List (Tm S)}, unifyList ps qs = none →
    ∀ ρ : String → Tm S, substList ρ ps = substList ρ qs → False
  | [], [], h, _, _ => by simp [unifyList] at h
  | p :: ps, q :: qs, h, ρ, same => by
      simp only [unifyList] at h
      simp only [substList, List.cons.injEq] at same
      split at h
      · cases h
      · rename_i none'
        cases hp : unify p q with
        | none => exact unify_complete_none hp ρ same.1
        | some a =>
            cases hq : unifyList ps qs with
            | none => exact unifyList_complete_none hq ρ same.2
            | some c => exact none' a c hp hq
  | [], q :: qs, _, ρ, same => by simp [substList] at same
  | p :: ps, [], _, ρ, same => by simp [substList] at same
end

/-- Instantiating by the unifier and then by a common instance is instantiating by the common
instance. -/
theorem subst_unifier {ρ : String → Tm S} {p q : Tm S} {b : List (String × Tm S)}
    (h : unify p q = some b) (same : p.subst ρ = q.subst ρ) (r : Tm S) :
    (r.subst (lookup b)).subst ρ = r.subst ρ := by
  rw [subst_subst]
  apply subst_congr
  intro x _
  have key : ∀ (bs : List (String × Tm S)), (∀ pr ∈ bs, pr.2.subst ρ = ρ pr.1) →
      (lookup bs x).subst ρ = ρ x := by
    intro bs hbs
    induction bs with
    | nil => simp [lookup]
    | cons pr rest ih =>
        obtain ⟨key, value⟩ := pr
        simp only [lookup]
        split
        · rename_i hk
          subst hk
          exact hbs _ List.mem_cons_self
        · exact ih fun q hq => hbs q (List.mem_cons_of_mem _ hq)
  exact key b (unify_factor ρ p q b h same)

/-- The test of one pair of equations: their left sides clash, or have disjoint variables and right
sides that agree at the unifier. -/
def agreeingPair (e e' : Equation S) : Bool :=
  clash e.lhs e'.lhs ||
    (decide (∀ x ∈ e.lhs.vars, x ∉ e'.lhs.vars) &&
      match unify e.lhs e'.lhs with
      | some b => decide (e.rhs.subst (lookup b) = e'.rhs.subst (lookup b))
      | none => true)

/-- **The agreeing-overlap check**: every pair of distinct equations passes the pair test. -/
def agreeingCheck (P : Program S) : Prop := P.Pairwise fun e e' => agreeingPair e e' = true

instance (P : Program S) : Decidable (agreeingCheck P) := by unfold agreeingCheck; infer_instance

/-- A pair that passes the test agrees on every common instance of its left sides. -/
theorem agreeingPair_sound {e e' : Equation S} (h : agreeingPair e e' = true)
    (bound : ∀ x ∈ e.rhs.vars, x ∈ e.lhs.vars) (bound' : ∀ x ∈ e'.rhs.vars, x ∈ e'.lhs.vars)
    (σ τ : String → Tm S) (same : e.lhs.subst σ = e'.lhs.subst τ) :
    e.rhs.subst σ = e'.rhs.subst τ := by
  simp only [agreeingPair, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with clashing | ⟨disjoint, agree⟩
  · exact absurd same (clash_sound _ _ clashing σ τ)
  · classical
    let ρ : String → Tm S := fun x => if x ∈ e.lhs.vars then σ x else τ x
    have onL : e.lhs.subst ρ = e.lhs.subst σ := subst_congr _ fun x hx => by simp [ρ, hx]
    have onL' : e'.lhs.subst ρ = e'.lhs.subst τ := subst_congr _ fun x hx => by
      have : x ∉ e.lhs.vars := fun h => disjoint x h hx
      simp [ρ, this]
    have onR : e.rhs.subst ρ = e.rhs.subst σ := subst_congr _ fun x hx => by simp [ρ, bound x hx]
    have onR' : e'.rhs.subst ρ = e'.rhs.subst τ := subst_congr _ fun x hx => by
      have : x ∉ e.lhs.vars := fun h => disjoint x h (bound' x hx)
      simp [ρ, this]
    have common : e.lhs.subst ρ = e'.lhs.subst ρ := by rw [onL, onL', same]
    cases hu : unify e.lhs e'.lhs with
    | none =>
        exfalso
        have := unify_complete_none hu ρ common
        exact this
    | some b =>
        rw [hu] at agree
        simp only [decide_eq_true_eq] at agree
        rw [← onR, ← onR', ← subst_unifier hu common e.rhs, agree, subst_unifier hu common e'.rhs]

/-- **The check makes root steps deterministic.** -/
theorem rootDeterministic_of_agreeingCheck {P : Program S} (bound : P.RightBound)
    (check : agreeingCheck P) {s t t' : Tm S} (h : RootStep P s t) (h' : RootStep P s t') : t = t' := by
  obtain ⟨e, he, σ, rfl, rfl⟩ := h.exists_rule
  obtain ⟨e', he', σ', same, rfl⟩ := h'.exists_rule
  by_cases equal : e = e'
  · subst equal
    apply subst_congr
    intro x hx
    exact subst_agree_of_eq e.lhs same x (bound e he x hx)
  · let R : Equation S → Equation S → Prop := fun e e' =>
      ∀ σ τ : String → Tm S, e.lhs.subst σ = e'.lhs.subst τ → e.rhs.subst σ = e'.rhs.subst τ
    have symm : Std.Symm R := ⟨fun a b hab σ τ hst => (hab τ σ hst.symm).symm⟩
    have pairwise : P.Pairwise R := List.Pairwise.imp_of_mem
      (fun {a b} ha hb hab => agreeingPair_sound hab (bound a ha) (bound b hb)) check
    exact List.Pairwise.forall pairwise he he' equal σ σ' same

/-- **Agreeing overlaps with termination give confluence.** -/
theorem confluent_of_agreeingCheck {P : Program S} (headed : P.Headed) (bound : P.RightBound)
    (patterns : ∀ e ∈ P, ∃ f ps, e.lhs = .app f ps ∧ ∀ p ∈ ps, EveryCall (fun g _ => ¬ P.Defines g) p)
    (linear : P.LeftLinear) (check : agreeingCheck P) (sn : ∀ t, SN P t) :
    Mettapedia.Logic.Relation.Confluent (Step P) :=
  Mettapedia.Logic.Relation.confluent_of_accessible_forks sn fun _ _ _ h₁ h₂ =>
    (Orthogonal.mk headed bound (rootDeterministic_of_agreeingCheck bound check) patterns linear).localConfluence
      h₁ h₂

end Mettapedia.Languages.MeTTa.DeclarationFaces

namespace Mettapedia.Languages.MeTTa.DeclarationFaces.Controls

open Tm

/-- `(: or (-> Bool Bool Bool))`. -/
def orSig : Signature String := ⟨[boolData], [⟨"or", [.app "Bool" [], .app "Bool" []], .app "Bool" []⟩]⟩

/-- Truth. -/
abbrev tt : Tm String := .app "True" []
/-- Falsity. -/
abbrev ff : Tm String := .app "False" []

/-- The parallel disjunction. -/
def orProgram : Program String :=
  [⟨.app "or" [tt, .var "x"], tt⟩, ⟨.app "or" [.var "x", tt], tt⟩, ⟨.app "or" [ff, ff], ff⟩]

/-- **Admission refuses the overlap**, naming the pair. -/
theorem or_refused : admit orSig orProgram = some (.overlap orProgram[0] orProgram[1]) := by decide

/-- **The root steps of the parallel disjunction are deterministic**: its overlaps agree. -/
theorem or_rootDeterministic {s t t' : Tm String} (h : RootStep orProgram s t)
    (h' : RootStep orProgram s t') : t = t' := by
  obtain ⟨e, he, σ, rfl, rfl⟩ := h.exists_rule
  obtain ⟨e', he', σ', same, rfl⟩ := h'.exists_rule
  simp only [orProgram, List.mem_cons, List.not_mem_nil, or_false] at he he'
  rcases he with rfl | rfl | rfl <;> rcases he' with rfl | rfl | rfl <;>
    simp_all [subst, substList]

theorem or_descends : orProgram.Descends (inferCertificate orSig orProgram) :=
  descends_of_check (by decide)

/-- The parallel disjunction is orthogonal in the sense the confluence proof uses. -/
theorem or_orthogonal : Orthogonal orProgram where
  headed := by
    intro e he
    simp only [orProgram, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> exact ⟨_, _, rfl⟩
  bound := by
    intro e he x hx
    simp only [orProgram, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> simp at hx
  rootDeterministic := or_rootDeterministic
  constructorPatterns := by
    have undefined : ∀ c, c ≠ "or" → ¬ orProgram.Defines c := by
      rintro c hc ⟨e, he, h⟩
      simp only [orProgram, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl <;> simp [head?] at h <;> exact hc h.symm
    intro e he
    simp only [orProgram, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · refine ⟨"or", _, rfl, fun p hp => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact .app (undefined _ (by decide)) (by simp)
      · exact .var _
    · refine ⟨"or", _, rfl, fun p hp => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact .var _
      · exact .app (undefined _ (by decide)) (by simp)
    · refine ⟨"or", _, rfl, fun p hp => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> exact .app (undefined _ (by decide)) (by simp)
  leftLinear := by
    intro e he
    simp only [orProgram, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> decide

/-- **The parallel disjunction is confluent**, although admission refuses it. -/
theorem or_confluent : Mettapedia.Logic.Relation.Confluent (Step orProgram) :=
  or_orthogonal.confluent or_descends

/-- **Its results as a multiset count the matching equations**: `(or True True)` gives `True` twice,
`(or True False)` once. -/
theorem or_true_true_twice :
    evalTm orProgram 5 (.app "or" [tt, tt]) = some [tt, tt] ∧
      evalTm orProgram 5 (.app "or" [tt, ff]) = some [tt] := by
  decide

/-- The parallel disjunction with the variables of its two overlapping equations kept apart. -/
def orProgram' : Program String :=
  [⟨.app "or" [tt, .var "x"], tt⟩, ⟨.app "or" [.var "y", tt], tt⟩, ⟨.app "or" [ff, ff], ff⟩]

/-- **The parallel disjunction passes the agreeing-overlap check**, though it fails non-overlap. -/
theorem or_agreeing : agreeingCheck orProgram' ∧ admit orSig orProgram' = some (.overlap orProgram'[0] orProgram'[1]) := by
  decide

/-- **An overlap that disagrees fails the check**: `(f Z) = Z` against `(f $x) = (S Z)`. -/
theorem overlap_not_agreeing : ¬ agreeingCheck overlapping := by decide

end Mettapedia.Languages.MeTTa.DeclarationFaces.Controls

import Mettapedia.Languages.ProcessCalculi.MORK.MM2MainlineProviders

/-!
# The support model is the kernel on ground stored atoms

The support model (`Space`, `MM2RuleScopedExecution`) matches patterns one way and
finalizes sinks in their authored order; the kernel (`Mainline`) unifies patterns with
stored atoms and writes the instances of every `+` sink first.  This module proves that
the two fire a comma conjunction with `+` and `-` sinks identically when

* every stored atom of the read copy is ground, or has a head symbol that differs from
  every pattern's (`MatchFragment`), and
* every `+` sink precedes every `-` sink.

The core is that the kernel's unifier, run on equations whose right sides are ground,
steps through them as one-way matching does (`solveWithin_corr`): an unbound variable is
eliminated by binding it, an already-bound variable or a constant either agrees with the
stored atom or clashes with it (`ground_clash`).  Hence `unifyOption_ground_matches`, the
row correspondence `conjunctionRows_corr`, and `fireDirective_eq_ruleScoped_ground`.

Outside the fragment the two differ: a stored variable meets any pattern term in the kernel
(`unification_separates`), and an add that follows a remove of the same instance survives
in the support model only.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.Mainline

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable (cmatchAtom cmatchAtomList)

/-! ## Unification against ground atoms is one-way matching -/

/-- Every binding of `σ` is ground. -/
def GroundValues (σ : Subst) : Prop := ∀ binding ∈ σ, isGroundAtom binding.2 = true

/-- Two substitutions with the same lookups. -/
def SameLookup (σ τ : Subst) : Prop := ∀ name, Subst.lookup σ name = Subst.lookup τ name

theorem lookup_cons (name other : String) (value : Atom) (σ : Subst) :
    Subst.lookup ((name, value) :: σ) other = if name = other then some value else Subst.lookup σ other := by
  by_cases same : name = other
  · subst same; simp [Subst.lookup]
  · have different : (name == other) = false := by simpa using same
    simp [Subst.lookup, List.find?, different, same]

theorem SameLookup.cons {σ τ : Subst} (same : SameLookup σ τ) (name : String) (value : Atom) :
    SameLookup ((name, value) :: σ) ((name, value) :: τ) := by
  intro other
  rw [lookup_cons, lookup_cons, same other]

theorem GroundValues.cons {σ : Subst} (ground : GroundValues σ) {name : String} {value : Atom}
    (groundValue : isGroundAtom value = true) : GroundValues ((name, value) :: σ) := by
  intro binding member
  rcases List.mem_cons.1 member with rfl | inside
  · exact groundValue
  · exact ground binding inside

theorem lookup_ground {σ : Subst} (ground : GroundValues σ) {name : String} {value : Atom}
    (found : Subst.lookup σ name = some value) : isGroundAtom value = true := by
  unfold Subst.lookup at found
  cases search : σ.find? (fun p => p.1 == name) with
  | none => rw [search] at found; cases found
  | some binding =>
      rw [search] at found
      simp only [Option.map_some, Option.some.injEq] at found
      subst found
      exact ground binding (List.mem_of_find?_eq_some search)

theorem applySubst_congr {σ τ : Subst} (same : SameLookup σ τ) : ∀ atom : Atom, applySubst σ atom = applySubst τ atom
  | .var name => by simp [applySubst, same name]
  | .symbol _ => rfl
  | .grounded _ => rfl
  | .expression children => by
      simp only [applySubst]
      congr 1
      exact listCase children
where
  listCase : ∀ children : List Atom, applySubst.applySubstList σ children = applySubst.applySubstList τ children
    | [] => rfl
    | child :: rest => by
        simp only [applySubst.applySubstList, applySubst_congr same child, listCase rest]

/-- A substituted atom that is a variable was that variable, unbound. -/
theorem applySubst_eq_var {σ : Subst} (ground : GroundValues σ) {atom : Atom} {name : String}
    (isVar : applySubst σ atom = .var name) : atom = .var name ∧ Subst.lookup σ name = none := by
  cases atom with
  | var other =>
      cases found : Subst.lookup σ other with
      | none =>
          simp only [applySubst, found, Option.getD_none, Atom.var.injEq] at isVar
          subst isVar
          exact ⟨rfl, found⟩
      | some value =>
          simp only [applySubst, found, Option.getD_some] at isVar
          have := lookup_ground ground found
          rw [isVar] at this
          simp [isGroundAtom] at this
  | symbol _ => simp [applySubst] at isVar
  | grounded _ => simp [applySubst] at isVar
  | expression _ => simp [applySubst] at isVar


theorem bindSolved_ground {θ : Subst} (ground : GroundValues θ) (name : String) {value : Atom} :
    bindSolved θ name value = (name, value) :: θ := by
  unfold bindSolved
  congr 1
  conv => rhs; rw [← List.map_id θ]
  apply List.map_congr_left
  intro binding member
  simp [applySubst_of_ground _ _ (ground binding member)]

/-- Substituting one more binding after a ground-valued substitution is substituting both. -/
theorem applySubst_compose {σ : Subst} (ground : GroundValues σ) {name : String}
    (unbound : Subst.lookup σ name = none) (value : Atom) :
    ∀ atom : Atom, applySubst [(name, value)] (applySubst σ atom) = applySubst ((name, value) :: σ) atom
  | .var other => by
      cases found : Subst.lookup σ other with
      | some bound =>
          have distinct : name ≠ other := by
            rintro rfl
            rw [unbound] at found
            cases found
          simp only [applySubst, found, Option.getD_some, lookup_cons, distinct, if_false]
          exact applySubst_of_ground _ _ (lookup_ground ground found)
      | none =>
          simp only [applySubst, found, Option.getD_none, lookup_cons]
          by_cases same : name = other
          · simp [same]
          · simp [same, Subst.lookup]
  | .symbol _ => rfl
  | .grounded _ => rfl
  | .expression children => by
      simp only [applySubst]
      congr 1
      exact listCase children
where
  listCase : ∀ children : List Atom,
      applySubst.applySubstList [(name, value)] (applySubst.applySubstList σ children) =
        applySubst.applySubstList ((name, value) :: σ) children
    | [] => rfl
    | child :: rest => by
        simp only [applySubst.applySubstList, applySubst_compose ground unbound value child, listCase rest]

theorem isGround_expression {children : List Atom} (ground : isGroundAtom (.expression children) = true) :
    ∀ child ∈ children, isGroundAtom child = true := by
  intro child member
  simp only [isGroundAtom] at ground
  exact listCase children ground child member
where
  listCase : ∀ children : List Atom, isGroundAtom.isGroundList children = true →
      ∀ child ∈ children, isGroundAtom child = true
    | [], _, _, member => absurd member List.not_mem_nil
    | head :: rest, ground, child, member => by
        simp only [isGroundAtom.isGroundList, Bool.and_eq_true] at ground
        rcases List.mem_cons.1 member with rfl | inside
        · exact ground.1
        · exact listCase rest ground.2 child inside

/-- **A pattern whose isInstance is the stored atom matches it without new bindings.** -/
theorem cmatch_of_applySubst_eq {σ : Subst} (ground : GroundValues σ) :
    ∀ (pattern stored : Atom), applySubst σ pattern = stored → isGroundAtom stored = true →
      cmatchAtom σ pattern stored = some σ
  | .var name, stored, isInstance, storedGround => by
      cases found : Subst.lookup σ name with
      | none =>
          simp only [applySubst, found, Option.getD_none] at isInstance
          subst isInstance
          simp [isGroundAtom] at storedGround
      | some bound =>
          simp only [applySubst, found, Option.getD_some] at isInstance
          subst isInstance
          simp [cmatchAtom, found]
  | .symbol name, stored, isInstance, _ => by
      subst isInstance
      simp [cmatchAtom, applySubst]
  | .grounded value, stored, isInstance, _ => by
      subst isInstance
      simp [cmatchAtom, applySubst]
  | .expression children, stored, isInstance, storedGround => by
      subst isInstance
      simp only [cmatchAtom, applySubst]
      exact listCase children (isGround_expression storedGround)
where
  listCase : ∀ children : List Atom, (∀ child ∈ applySubst.applySubstList σ children, isGroundAtom child = true) →
      cmatchAtomList σ children (applySubst.applySubstList σ children) = some σ
    | [], _ => by simp [cmatchAtomList, applySubst.applySubstList]
    | child :: rest, ground' => by
        simp only [applySubst.applySubstList, cmatchAtomList]
        rw [cmatch_of_applySubst_eq ground child _ rfl (ground' _ (by simp [applySubst.applySubstList]))]
        exact listCase rest fun other member => ground' other (by simp [applySubst.applySubstList, member])

/-! ### Two different ground atoms clash -/

theorem solveWithin_skip (eliminate : Equations → Subst → Unification) (fuel : ℕ) (atom : Atom)
    (rest : Equations) (θ : Subst) :
    solveWithin eliminate (fuel + 1) ((atom, atom) :: rest) θ = solveWithin eliminate fuel rest θ := by
  simp [solveWithin]

theorem ground_clash (eliminate : Equations → Subst → Unification) :
    ∀ (fuel : ℕ) (left right : Atom) (rest : Equations) (θ : Subst),
      isGroundAtom left = true → isGroundAtom right = true → left ≠ right →
      equationsSize ((left, right) :: rest) < fuel →
      solveWithin eliminate fuel ((left, right) :: rest) θ = .clash := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel ih =>
    intro left right rest θ leftGround rightGround distinct small
    cases fuel with
    | zero => exact absurd small (Nat.not_lt_zero _)
    | succ fuel =>
      simp only [solveWithin, distinct, if_false]
      cases left with
      | var name => simp [isGroundAtom] at leftGround
      | symbol a =>
          cases right with
          | var name => simp [isGroundAtom] at rightGround
          | _ => rfl
      | grounded a =>
          cases right with
          | var name => simp [isGroundAtom] at rightGround
          | _ => rfl
      | expression lefts =>
          cases right with
          | var name => simp [isGroundAtom] at rightGround
          | symbol _ => rfl
          | grounded _ => rfl
          | expression rights =>
              simp only
              split
              · rename_i sameLength
                have childrenDistinct : lefts ≠ rights := fun same => distinct (by rw [same])
                have zipSmall : equationsSize (lefts.zip rights ++ rest) < fuel := by
                  rw [equationsSize_append, equationsSize_zip _ _ sameLength]
                  simp only [equationsSize, atomSize] at small
                  omega
                exact zipCase fuel ih lefts rights fuel le_rfl sameLength childrenDistinct
                  (isGround_expression leftGround) (isGround_expression rightGround) zipSmall
              · rfl
where
  zipCase (fuel : ℕ) (ih : ∀ smaller < fuel + 1, ∀ (left right : Atom) (rest : Equations) (θ : Subst),
      isGroundAtom left = true → isGroundAtom right = true → left ≠ right →
      equationsSize ((left, right) :: rest) < smaller →
      solveWithin eliminate smaller ((left, right) :: rest) θ = .clash) {rest : Equations} {θ : Subst} :
      ∀ (lefts rights : List Atom) (budget : ℕ), budget ≤ fuel → lefts.length = rights.length → lefts ≠ rights →
        (∀ x ∈ lefts, isGroundAtom x = true) → (∀ x ∈ rights, isGroundAtom x = true) →
        equationsSize (lefts.zip rights ++ rest) < budget →
        solveWithin eliminate budget (lefts.zip rights ++ rest) θ = .clash
    | [], [], _, _, _, distinct, _, _, _ => absurd rfl distinct
    | [], _ :: _, _, _, sameLength, _, _, _, _ => by simp at sameLength
    | _ :: _, [], _, _, sameLength, _, _, _, _ => by simp at sameLength
    | left :: lefts, right :: rights, budget, bounded, sameLength, distinct, leftsGround, rightsGround, small => by
        simp only [List.zip_cons_cons, List.cons_append]
        by_cases same : left = right
        · subst same
          cases budget with
          | zero => exact absurd small (Nat.not_lt_zero _)
          | succ budget =>
              rw [solveWithin_skip]
              have tailDistinct : lefts ≠ rights := fun equal => distinct (by rw [equal])
              apply zipCase fuel ih lefts rights budget (by omega) (by simpa using sameLength) tailDistinct
                (fun x member => leftsGround x (by simp [member]))
                (fun x member => rightsGround x (by simp [member]))
              simp only [List.zip_cons_cons, List.cons_append, equationsSize] at small
              have := atomSize_pos left
              omega
        · apply ih budget (by omega) left right _ θ (leftsGround left (by simp))
            (rightsGround right (by simp)) same
          simpa using small

/-! ### The solver on matching problems -/

/-- Equations whose right sides are ground. -/
def RightGround (equations : Equations) : Prop :=
  ∀ equation ∈ equations, isGroundAtom equation.2 = true

/-- Apply a substitution to the left sides. -/
def applyLeft (σ : Subst) (equations : Equations) : Equations :=
  equations.map fun equation => (applySubst σ equation.1, equation.2)

/-- One-way matching of each left side against its right side, in order. -/
def cmatchEqs : Subst → Equations → Option Subst
  | σ, [] => some σ
  | σ, (left, right) :: rest => (cmatchAtom σ left right).bind fun next => cmatchEqs next rest

/-- A unifier outcome and a matcher outcome that agree. -/
inductive Corr : Unification → Option Subst → Prop
  | clash : Corr .clash none
  | solved {θ σ : Subst} : SameLookup θ σ → GroundValues θ → GroundValues σ → Corr (.solved θ) (some σ)

theorem cmatchAtomList_length_ne (σ : Subst) :
    ∀ (lefts rights : List Atom), lefts.length ≠ rights.length → cmatchAtomList σ lefts rights = none
  | [], [], different => absurd rfl different
  | [], _ :: _, _ => by simp [cmatchAtomList]
  | _ :: _, [], _ => by simp [cmatchAtomList]
  | left :: lefts, right :: rights, different => by
      simp only [cmatchAtomList]
      cases cmatchAtom σ left right with
      | none => rfl
      | some next => exact cmatchAtomList_length_ne next lefts rights (by simpa using different)

theorem cmatchEqs_zip (rest : Equations) :
    ∀ (σ : Subst) (lefts rights : List Atom), lefts.length = rights.length →
      cmatchEqs σ (lefts.zip rights ++ rest) = (cmatchAtomList σ lefts rights).bind fun next => cmatchEqs next rest
  | σ, [], [], _ => by simp [cmatchAtomList]
  | _, [], _ :: _, sameLength => by simp at sameLength
  | _, _ :: _, [], sameLength => by simp at sameLength
  | σ, left :: lefts, right :: rights, sameLength => by
      simp only [List.zip_cons_cons, List.cons_append, cmatchEqs, cmatchAtomList]
      cases cmatchAtom σ left right with
      | none => rfl
      | some next => exact cmatchEqs_zip rest next lefts rights (by simpa using sameLength)

theorem applyLeft_zip_append (σ : Subst) (rest : Equations) :
    ∀ (lefts rights : List Atom),
      applyLeft σ (lefts.zip rights ++ rest) = (applySubst.applySubstList σ lefts).zip rights ++ applyLeft σ rest
  | [], _ => by simp [applyLeft, applySubst.applySubstList]
  | _ :: _, [] => by simp [applyLeft, applySubst.applySubstList]
  | left :: lefts, right :: rights => by
      simp only [List.zip_cons_cons, List.cons_append, applyLeft, List.map_cons, applySubst.applySubstList]
      congr 1
      exact applyLeft_zip_append σ rest lefts rights

theorem length_applySubstList (σ : Subst) :
    ∀ children : List Atom, (applySubst.applySubstList σ children).length = children.length
  | [] => rfl
  | _ :: rest => by simp [applySubst.applySubstList, length_applySubstList σ rest]

/-- Eliminating an unbound variable of the left sides is extending the substitution. -/
theorem applyLeft_substitute {σ : Subst} (ground : GroundValues σ) {name : String}
    (unbound : Subst.lookup σ name = none) (value : Atom)
    {rest : Equations} (restGround : RightGround rest) :
    substituteEquations name value (applyLeft σ rest) = applyLeft ((name, value) :: σ) rest := by
  unfold substituteEquations applyLeft
  rw [List.map_map]
  apply List.map_congr_left
  intro equation member
  simp only [Function.comp_apply, Prod.mk.injEq]
  exact ⟨applySubst_compose ground unbound value equation.1,
    applySubst_of_ground _ _ (restGround equation member)⟩

/-- Matching against a ground atom binds ground values. -/
theorem cmatch_groundValues {σ : Subst} (ground : GroundValues σ) :
    ∀ (pattern stored : Atom) {next : Subst}, isGroundAtom stored = true →
      cmatchAtom σ pattern stored = some next → GroundValues next
  | .var name, stored, next, storedGround, matched => by
      cases found : Subst.lookup σ name with
      | none =>
          simp only [cmatchAtom, found, Option.some.injEq] at matched
          subst matched
          exact ground.cons storedGround
      | some bound =>
          simp only [cmatchAtom, found] at matched
          split at matched
          · cases matched; exact ground
          · cases matched
  | .symbol _, stored, next, _, matched => by
      cases stored <;> simp [cmatchAtom] at matched
      obtain ⟨-, rfl⟩ := matched
      exact ground
  | .grounded _, stored, next, _, matched => by
      cases stored <;> simp [cmatchAtom] at matched
      obtain ⟨-, rfl⟩ := matched
      exact ground
  | .expression children, stored, next, storedGround, matched => by
      cases stored with
      | expression storedChildren =>
          simp only [cmatchAtom] at matched
          exact listCase ground children storedChildren (isGround_expression storedGround) matched
      | _ => simp [cmatchAtom] at matched
where
  listCase {σ : Subst} (ground : GroundValues σ) : ∀ (children storedChildren : List Atom) {next : Subst},
      (∀ child ∈ storedChildren, isGroundAtom child = true) →
      cmatchAtomList σ children storedChildren = some next → GroundValues next
    | [], [], next, _, matched => by simp only [cmatchAtomList, Option.some.injEq] at matched; subst matched; exact ground
    | [], _ :: _, _, _, matched => by simp [cmatchAtomList] at matched
    | _ :: _, [], _, _, matched => by simp [cmatchAtomList] at matched
    | child :: children, storedChild :: storedChildren, next, storedGround, matched => by
        simp only [cmatchAtomList] at matched
        cases first : cmatchAtom σ child storedChild with
        | none => rw [first] at matched; cases matched
        | some middle =>
            rw [first] at matched
            exact listCase (cmatch_groundValues ground child storedChild (storedGround _ (by simp)) first)
              children storedChildren (fun other member => storedGround other (by simp [member])) matched

theorem mem_freeVarsList_of_mem {w : String} {child : Atom} :
    ∀ {children : List Atom}, child ∈ children → w ∈ atomFreeVars child →
      w ∈ atomFreeVars.atomFreeVarsList children
  | [], member, _ => absurd member List.not_mem_nil
  | head :: rest, member, occurs => by
      simp only [atomFreeVars.atomFreeVarsList, List.mem_append]
      rcases List.mem_cons.1 member with rfl | inside
      · exact Or.inl occurs
      · exact Or.inr (mem_freeVarsList_of_mem inside occurs)

/-- **The solver steps through a matching problem as the one-way matcher does.** -/
theorem solveWithin_corr (eliminate : Equations → Subst → Unification) (bound : ℕ)
    (good : ∀ (equations : Equations) (σ θ : Subst), RightGround equations → GroundValues σ →
      GroundValues θ → SameLookup θ σ → (equationsVars (applyLeft σ equations)).length < bound →
      Corr (eliminate (applyLeft σ equations) θ) (cmatchEqs σ equations)) :
    ∀ (fuel : ℕ) (equations : Equations) (σ θ : Subst), RightGround equations → GroundValues σ →
      GroundValues θ → SameLookup θ σ → equationsSize (applyLeft σ equations) < fuel →
      (equationsVars (applyLeft σ equations)).length ≤ bound →
      Corr (solveWithin eliminate fuel (applyLeft σ equations) θ) (cmatchEqs σ equations)
  | 0, _, _, _, _, _, _, _, small, _ => absurd small (Nat.not_lt_zero _)
  | _ + 1, [], σ, θ, _, groundσ, groundθ, same, _, _ => by
      simp only [applyLeft, List.map_nil, solveWithin, cmatchEqs]
      exact .solved same groundθ groundσ
  | fuel + 1, (left, right) :: rest, σ, θ, rightGround, groundσ, groundθ, same, small, bounded => by
      have rightG : isGroundAtom right = true := rightGround (left, right) (by simp)
      have restGround : RightGround rest := fun equation member => rightGround equation (by simp [member])
      have applied : applyLeft σ ((left, right) :: rest) = (applySubst σ left, right) :: applyLeft σ rest := rfl
      have restVars : (equationsVars (applyLeft σ rest)).length ≤ bound :=
        le_trans (equationsVars_length_le_of_subset (fun w member => by
          obtain ⟨equation, equationMember, occurs⟩ := mem_equationsVars.1 member
          exact mem_equationsVars.2 ⟨equation, by rw [applied]; exact List.mem_cons_of_mem _ equationMember,
            occurs⟩)) bounded
      have restSmall : equationsSize (applyLeft σ rest) < fuel := by
        rw [applied] at small
        simp only [equationsSize] at small
        have := atomSize_pos right
        omega
      by_cases isInstance : applySubst σ left = right
      · -- The left side is already the right side: both skip it.
        rw [applied, isInstance, solveWithin_skip]
        simp only [cmatchEqs, cmatch_of_applySubst_eq groundσ left right isInstance rightG, Option.bind_some]
        exact solveWithin_corr eliminate bound good fuel rest σ θ restGround groundσ groundθ same restSmall
          restVars
      · cases left with
        | var name =>
            cases found : Subst.lookup σ name with
            | some bound' =>
                -- A bound variable stands for a ground value other than the right side.
                have boundGround := lookup_ground groundσ found
                have value : applySubst σ (.var name) = bound' := by simp [applySubst, found]
                rw [applied, value, ground_clash eliminate (fuel + 1) bound' right _ θ boundGround rightG
                  (by rwa [← value]) (by rwa [applied, value] at small)]
                have different : (right == bound') = false := by
                  simp only [beq_eq_false_iff_ne]
                  intro equal
                  exact isInstance (by rw [value, equal])
                simp only [cmatchEqs, cmatchAtom, found, different, Bool.false_eq_true, if_false,
                  Option.bind_none]
                exact .clash
            | none =>
                -- An unbound variable is eliminated by both.
                have value : applySubst σ (.var name) = .var name := by simp [applySubst, found]
                have notVar : Atom.var name ≠ right := by rwa [← value]
                have freeVars : atomFreeVars right = [] := atomFreeVars_of_ground right rightG
                rw [applied, value]
                simp only [solveWithin, notVar, if_false, freeVars, List.contains_nil, Bool.false_eq_true]
                rw [bindSolved_ground groundθ, applyLeft_substitute groundσ found right restGround]
                simp only [cmatchEqs, cmatchAtom, found, Option.bind_some]
                apply good rest ((name, right) :: σ) ((name, right) :: θ) restGround (groundσ.cons rightG)
                  (groundθ.cons rightG) (same.cons name right)
                rw [← applyLeft_substitute groundσ found right restGround]
                have lower := equationsVars_substitute_lt name right (applyLeft σ rest)
                  (by simp [freeVars]) (.var name, right) (Or.inl (by simp [atomFreeVars]))
                  (fun w member => by simp [freeVars] at member)
                rw [applied, value] at bounded
                omega
        | symbol leftName =>
            have value : applySubst σ (.symbol leftName) = .symbol leftName := rfl
            rw [applied, value, ground_clash eliminate (fuel + 1) (.symbol leftName) right _ θ rfl rightG
              (by rwa [← value]) (by rwa [applied, value] at small)]
            cases right with
            | symbol rightName =>
                have different : (leftName == rightName) = false := by
                  simp only [beq_eq_false_iff_ne]
                  intro equal
                  exact isInstance (by rw [value, equal])
                simp only [cmatchEqs, cmatchAtom, different, Bool.false_eq_true, if_false, Option.bind_none]
                exact .clash
            | _ => simp only [cmatchEqs, cmatchAtom, Option.bind_none]; exact .clash
        | grounded leftValue =>
            have value : applySubst σ (.grounded leftValue) = .grounded leftValue := rfl
            rw [applied, value, ground_clash eliminate (fuel + 1) (.grounded leftValue) right _ θ rfl rightG
              (by rwa [← value]) (by rwa [applied, value] at small)]
            cases right with
            | grounded rightValue =>
                have different : (leftValue == rightValue) = false := by
                  simp only [beq_eq_false_iff_ne]
                  intro equal
                  exact isInstance (by rw [value, equal])
                simp only [cmatchEqs, cmatchAtom, different, Bool.false_eq_true, if_false, Option.bind_none]
                exact .clash
            | _ => simp only [cmatchEqs, cmatchAtom, Option.bind_none]; exact .clash
        | expression lefts =>
            have value : applySubst σ (.expression lefts) = .expression (applySubst.applySubstList σ lefts) := rfl
            cases right with
            | var name => simp [isGroundAtom] at rightG
            | symbol _ =>
                rw [applied, value]
                simp only [solveWithin]
                rw [if_neg (by simp)]
                simp only [cmatchEqs, cmatchAtom, Option.bind_none]
                exact .clash
            | grounded _ =>
                rw [applied, value]
                simp only [solveWithin]
                rw [if_neg (by simp)]
                simp only [cmatchEqs, cmatchAtom, Option.bind_none]
                exact .clash
            | expression rights =>
                rw [applied, value]
                simp only [solveWithin]
                rw [if_neg (by rwa [← value])]
                simp only [length_applySubstList]
                split
                · rename_i sameLength
                  rw [← applyLeft_zip_append]
                  simp only [cmatchEqs, cmatchAtom]
                  rw [← cmatchEqs_zip rest σ lefts rights sameLength]
                  have zipGround : RightGround (lefts.zip rights ++ rest) := by
                    intro equation member
                    rcases List.mem_append.1 member with inZip | inRest
                    · exact isGround_expression rightG _ (List.of_mem_zip inZip).2
                    · exact restGround equation inRest
                  apply solveWithin_corr eliminate bound good fuel _ σ θ zipGround groundσ groundθ same
                  · rw [applyLeft_zip_append, equationsSize_append,
                      equationsSize_zip _ _ (by rw [length_applySubstList]; exact sameLength)]
                    rw [applied, value] at small
                    simp only [equationsSize, atomSize] at small
                    omega
                  · rw [applyLeft_zip_append]
                    refine le_trans (equationsVars_length_le_of_subset fun w member => ?_) bounded
                    obtain ⟨equation, equationMember, occurs⟩ := mem_equationsVars.1 member
                    rw [applied, value]
                    rcases List.mem_append.1 equationMember with inZip | inRest
                    · refine mem_equationsVars.2 ⟨_, List.mem_cons_self .., ?_⟩
                      rcases occurs with occurs | occurs
                      · exact Or.inl (by
                          simp only [atomFreeVars]
                          exact mem_freeVarsList_of_mem (List.of_mem_zip inZip).1 occurs)
                      · exact Or.inr (by
                          simp only [atomFreeVars]
                          exact mem_freeVarsList_of_mem (List.of_mem_zip inZip).2 occurs)
                    · exact mem_equationsVars.2 ⟨equation, List.mem_cons_of_mem _ inRest, occurs⟩
                · rename_i differentLength
                  simp only [cmatchEqs, cmatchAtom, cmatchAtomList_length_ne σ lefts rights differentLength,
                    Option.bind_none]
                  exact .clash

theorem solveEquations_corr : ∀ (budget : ℕ) (equations : Equations) (σ θ : Subst),
    RightGround equations → GroundValues σ → GroundValues θ → SameLookup θ σ →
    (equationsVars (applyLeft σ equations)).length ≤ budget →
    Corr (solveEquations budget (applyLeft σ equations) θ) (cmatchEqs σ equations)
  | 0, equations, σ, θ, rightGround, groundσ, groundθ, same, bounded => by
      simp only [solveEquations]
      exact solveWithin_corr _ 0 (fun _ _ _ _ _ _ _ small => absurd small (Nat.not_lt_zero _))
        _ equations σ θ rightGround groundσ groundθ same (Nat.lt_succ_self _) bounded
  | budget + 1, equations, σ, θ, rightGround, groundσ, groundθ, same, bounded => by
      simp only [solveEquations]
      exact solveWithin_corr _ (budget + 1)
        (fun next σ' θ' nextGround groundσ' groundθ' same' small =>
          solveEquations_corr budget next σ' θ' nextGround groundσ' groundθ' same' (by omega))
        _ equations σ θ rightGround groundσ groundθ same (Nat.lt_succ_self _) bounded

/-- Unifier and matcher outcomes on one pattern that agree. -/
inductive OptionCorr : Option Subst → Option Subst → Prop
  | none : OptionCorr none none
  | some {θ σ : Subst} : SameLookup θ σ → GroundValues θ → GroundValues σ → OptionCorr (some θ) (some σ)

/-- **Unifying a pattern with a ground atom is matching it one way.** -/
theorem unifyOption_ground_matches {θ σ : Subst} (groundθ : GroundValues θ) (groundσ : GroundValues σ)
    (same : SameLookup θ σ) (pattern stored : Atom) (storedGround : isGroundAtom stored = true) :
    OptionCorr (unifyOption θ [(pattern, stored)]) (cmatchAtom σ pattern stored) := by
  have applied : [(pattern, stored)].map (fun equation => (applySubst θ equation.1, applySubst θ equation.2)) =
      applyLeft σ [(pattern, stored)] := by
    simp [applyLeft, applySubst_congr same pattern, applySubst_of_ground _ _ storedGround]
  have corr := solveEquations_corr (equationsVars (applyLeft σ [(pattern, stored)])).length
    [(pattern, stored)] σ θ (by simp [RightGround, storedGround]) groundσ groundθ same le_rfl
  have matched : cmatchEqs σ [(pattern, stored)] = cmatchAtom σ pattern stored := by
    simp only [cmatchEqs]
    cases cmatchAtom σ pattern stored <;> rfl
  rw [matched] at corr
  unfold unifyOption unifyUnder
  simp only [applied]
  revert corr
  generalize solveEquations (equationsVars (applyLeft σ [(pattern, stored)])).length
    (applyLeft σ [(pattern, stored)]) θ = result
  generalize cmatchAtom σ pattern stored = matchedResult
  intro corr
  cases corr with
  | clash => exact .none
  | solved sameLookup groundθ' groundσ' => exact .some sameLookup groundθ' groundσ'

/-! ### Stored atoms a pattern cannot reach -/

/-- A pattern and a stored atom whose head symbols differ. -/
def HeadClash (pattern stored : Atom) : Prop :=
  ∃ (patternHead storedHead : String) (patternRest storedRest : List Atom),
    pattern = .expression (.symbol patternHead :: patternRest) ∧
      stored = .expression (.symbol storedHead :: storedRest) ∧ patternHead ≠ storedHead

theorem applySubst_head (σ : Subst) (head : String) (rest : List Atom) :
    applySubst σ (.expression (.symbol head :: rest)) =
      .expression (.symbol head :: applySubst.applySubstList σ rest) := rfl

theorem solveWithin_headClash (eliminate : Equations → Subst → Unification) (fuel : ℕ)
    {patternHead storedHead : String} (distinct : patternHead ≠ storedHead)
    (patternRest storedRest : List Atom) (θ : Subst) :
    solveWithin eliminate (fuel + 2)
        [(.expression (.symbol patternHead :: patternRest), .expression (.symbol storedHead :: storedRest))] θ =
      .clash := by
  have notEqual : Atom.expression (.symbol patternHead :: patternRest) ≠
      .expression (.symbol storedHead :: storedRest) := by
    intro same
    injection same with lists
    injection lists with heads
    injection heads with names
    exact distinct names
  simp only [solveWithin, notEqual, if_false, List.length_cons, Nat.add_right_cancel_iff]
  split
  · simp only [List.zip_cons_cons, List.cons_append, solveWithin]
    rw [if_neg (by simpa using distinct)]
  · rfl

/-- **A stored atom whose head differs from the pattern's never unifies with it.** -/
theorem unifyOption_headClash (θ : Subst) (tag : String) {pattern stored : Atom}
    (clash : HeadClash pattern stored) : unifyOption θ [(pattern, renameApart tag stored)] = none := by
  obtain ⟨patternHead, storedHead, patternRest, storedRest, rfl, rfl, distinct⟩ := clash
  unfold unifyOption unifyUnder renameApart
  simp only [List.map_cons, List.map_nil, applySubst_head]
  have budgets : ∀ (budget : ℕ) (left right : List Atom),
      solveEquations budget [(.expression (.symbol patternHead :: left),
        .expression (.symbol storedHead :: right))] θ = .clash := by
    intro budget left right
    cases budget <;>
    · simp only [solveEquations, equationsSize, atomSize, atomSize.atomSizeList]
      rw [show 1 + atomSize.atomSizeList left + 1 + (1 + atomSize.atomSizeList right + 1) + 0 + 1 =
        (atomSize.atomSizeList left + atomSize.atomSizeList right + 3) + 2 by omega]
      exact solveWithin_headClash _ _ distinct left right θ
  rw [budgets]

theorem cmatchAtom_headClash (σ : Subst) {pattern stored : Atom} (clash : HeadClash pattern stored) :
    cmatchAtom σ pattern stored = none := by
  obtain ⟨patternHead, storedHead, patternRest, storedRest, rfl, rfl, distinct⟩ := clash
  have different : (patternHead == storedHead) = false := by simpa using distinct
  simp [cmatchAtom, cmatchAtomList, different]

/-! ### Rows -/

/-- Every stored atom of the read copy is ground, or no pattern can reach it. -/
def MatchFragment (patterns read : List Atom) : Prop :=
  ∀ stored ∈ read, isGroundAtom stored = true ∨ ∀ pattern ∈ patterns, HeadClash pattern stored

/-- Rows of the kernel and of the one-way matcher that agree. -/
def RowCorr (θ σ : Subst) : Prop := SameLookup θ σ ∧ GroundValues θ ∧ GroundValues σ

theorem filterMap_corr (θ σ : Subst) (corrStart : RowCorr θ σ) (pattern : Atom) (tag : String) :
    ∀ (read : List Atom), (∀ stored ∈ read, isGroundAtom stored = true ∨ HeadClash pattern stored) →
      List.Forall₂ (fun θ' found => RowCorr θ' found.1)
        (read.filterMap fun stored => unifyOption θ [(pattern, renameApart tag stored)])
        (read.filterMap fun stored => (cmatchAtom σ pattern stored).map (·, stored))
  | [], _ => .nil
  | stored :: rest, fragment => by
      have restCorr := filterMap_corr θ σ corrStart pattern tag rest
        (fun other member => fragment other (by simp [member]))
      rcases fragment stored (by simp) with ground | clash
      · rw [List.filterMap_cons, List.filterMap_cons, renameApart_ground tag stored ground]
        have corr := unifyOption_ground_matches corrStart.2.1 corrStart.2.2 corrStart.1 pattern stored ground
        revert corr
        generalize unifyOption θ [(pattern, stored)] = unified
        generalize cmatchAtom σ pattern stored = matched
        intro corr
        cases corr with
        | none => exact restCorr
        | some sameLookup groundθ groundσ => exact .cons ⟨sameLookup, groundθ, groundσ⟩ restCorr
      · rw [List.filterMap_cons, List.filterMap_cons, unifyOption_headClash θ tag clash,
          cmatchAtom_headClash σ clash]
        exact restCorr

theorem forall₂_flatMap {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop}
    {f : α → List γ} {g : β → List δ} (step : ∀ a b, R a b → List.Forall₂ S (f a) (g b)) :
    ∀ {as : List α} {bs : List β}, List.Forall₂ R as bs → List.Forall₂ S (as.flatMap f) (bs.flatMap g)
  | [], [], .nil => .nil
  | a :: as, b :: bs, .cons related rest => by
      simp only [List.flatMap_cons]
      exact List.rel_append (step a b related) (forall₂_flatMap step rest)

/-- **The kernel's conjunction rows are the one-way matcher's**, row by row, on the matching
fragment. -/
theorem conjunctionRows_corr (tag : ℕ → String) (read : List Atom) :
    ∀ (patterns : List Atom) (index : ℕ) (θ σ : Subst) (witnesses : List Atom),
      MatchFragment patterns read → RowCorr θ σ →
      List.Forall₂ RowCorr (conjunctionRows tag read index θ patterns)
        ((Conformance.Computable.cmatchPattern.go read patterns σ witnesses).map Prod.fst)
  | [], _, θ, σ, _, _, corr => by
      simp only [conjunctionRows, Conformance.Computable.cmatchPattern.go, List.map_cons, List.map_nil]
      exact .cons corr .nil
  | pattern :: rest, index, θ, σ, witnesses, fragment, corr => by
      simp only [conjunctionRows, Conformance.Computable.cmatchPattern.go, List.map_flatMap]
      have restFragment : MatchFragment rest read := by
        intro stored member
        rcases fragment stored member with ground | clash
        · exact Or.inl ground
        · exact Or.inr fun other inRest => clash other (by simp [inRest])
      apply forall₂_flatMap (R := fun θ' found => RowCorr θ' found.1)
      · intro θ' found related
        exact conjunctionRows_corr tag read rest (index + 1) θ' found.1 (found.2 :: witnesses) restFragment related
      · exact filterMap_corr θ σ corr pattern (tag index) read fun stored member =>
          (fragment stored member).imp id fun clash => clash pattern (by simp)

/-! ### The bound variables of a match -/

/-- A matcher binds exactly the variables it was given and the pattern's. -/
theorem cmatch_domain {σ : Subst} : ∀ (pattern stored : Atom) {next : Subst},
    cmatchAtom σ pattern stored = some next →
    ∀ name, (Subst.lookup next name).isSome = true ↔
      (Subst.lookup σ name).isSome = true ∨ name ∈ atomFreeVars pattern
  | .var bound, stored, next, matched, name => by
      cases found : Subst.lookup σ bound with
      | none =>
          simp only [cmatchAtom, found, Option.some.injEq] at matched
          subst matched
          rw [lookup_cons]
          by_cases same : bound = name
          · subst same; simp [found, atomFreeVars]
          · simp [same, atomFreeVars, Ne.symm same]
      | some value =>
          simp only [cmatchAtom, found] at matched
          split at matched
          · cases matched
            by_cases same : bound = name
            · subst same; simp [found, atomFreeVars]
            · simp [atomFreeVars, Ne.symm same]
          · cases matched
  | .symbol _, stored, next, matched, name => by
      cases stored <;> simp [cmatchAtom] at matched
      obtain ⟨-, rfl⟩ := matched
      simp [atomFreeVars]
  | .grounded _, stored, next, matched, name => by
      cases stored <;> simp [cmatchAtom] at matched
      obtain ⟨-, rfl⟩ := matched
      simp [atomFreeVars]
  | .expression children, stored, next, matched, name => by
      cases stored with
      | expression storedChildren =>
          simp only [cmatchAtom] at matched
          simp only [atomFreeVars]
          exact listCase name children storedChildren matched
      | _ => simp [cmatchAtom] at matched
where
  listCase (name : String) : ∀ (children storedChildren : List Atom) {σ next : Subst},
      cmatchAtomList σ children storedChildren = some next →
      ((Subst.lookup next name).isSome = true ↔
        (Subst.lookup σ name).isSome = true ∨ name ∈ atomFreeVars.atomFreeVarsList children)
    | [], [], σ, next, matched => by
        simp only [cmatchAtomList, Option.some.injEq] at matched
        subst matched
        simp [atomFreeVars.atomFreeVarsList]
    | [], _ :: _, _, _, matched => by simp [cmatchAtomList] at matched
    | _ :: _, [], _, _, matched => by simp [cmatchAtomList] at matched
    | child :: children, storedChild :: storedChildren, σ, next, matched => by
        simp only [cmatchAtomList] at matched
        cases first : cmatchAtom σ child storedChild with
        | none => rw [first] at matched; cases matched
        | some middle =>
            rw [first] at matched
            rw [listCase name children storedChildren matched, cmatch_domain child storedChild first name]
            simp only [atomFreeVars.atomFreeVarsList, List.mem_append]
            tauto

theorem go_domain (read : List Atom) :
    ∀ (patterns : List Atom) (σ : Subst) (witnesses : List Atom),
      ∀ found ∈ Conformance.Computable.cmatchPattern.go read patterns σ witnesses,
        ∀ name, (Subst.lookup found.1 name).isSome = true ↔
          (Subst.lookup σ name).isSome = true ∨ name ∈ atomFreeVars.atomFreeVarsList patterns
  | [], σ, witnesses, found, member, name => by
      simp only [Conformance.Computable.cmatchPattern.go, List.mem_singleton] at member
      subst member
      simp [atomFreeVars.atomFreeVarsList]
  | pattern :: rest, σ, witnesses, found, member, name => by
      simp only [Conformance.Computable.cmatchPattern.go, List.mem_flatMap, List.mem_filterMap,
        Option.map_eq_some_iff] at member
      obtain ⟨⟨middle, stored⟩, ⟨stored', storedMember, middle', matched, pairEq⟩, inner⟩ := member
      cases pairEq
      rw [go_domain read rest middle (stored :: witnesses) found inner name,
        cmatch_domain pattern stored matched name]
      simp only [atomFreeVars.atomFreeVarsList, List.mem_append]
      tauto

theorem lookup_nil (name : String) : Subst.lookup [] name = none := rfl

theorem lookup_inputRow (θ : Subst) (name : String) :
    ∀ names : List String,
      Subst.lookup (inputRow names θ) name = if name ∈ names then some (applySubst θ (.var name)) else none
  | [] => by simp [inputRow, lookup_nil]
  | first :: rest => by
      simp only [inputRow, List.map_cons, lookup_cons]
      by_cases same : first = name
      · subst same; simp
      · rw [if_neg same]
        have := lookup_inputRow θ name rest
        simp only [inputRow] at this
        rw [this]
        simp [Ne.symm same]

theorem inputRow_sameLookup {θ σ : Subst} {names : List String} (same : SameLookup θ σ)
    (domain : ∀ name, (Subst.lookup σ name).isSome = true ↔ name ∈ names) :
    SameLookup (inputRow names θ) σ := by
  intro name
  rw [lookup_inputRow]
  by_cases member : name ∈ names
  · rw [if_pos member]
    obtain ⟨value, found⟩ := Option.isSome_iff_exists.1 ((domain name).2 member)
    simp [applySubst, same name, found]
  · rw [if_neg member]
    cases found : Subst.lookup σ name with
    | none => rfl
    | some _ => exact absurd ((domain name).1 (by simp [found])) member

/-! ### Staging depends on lookups only -/

theorem ruleTemplateCovered_congr {σ τ : Subst} (same : SameLookup σ τ) (input : InputSpec) :
    ∀ template : Atom, ruleTemplateCovered input σ template = ruleTemplateCovered input τ template
  | .var name => by simp [ruleTemplateCovered, same name]
  | .symbol _ => rfl
  | .grounded _ => rfl
  | .expression children => by
      simp only [ruleTemplateCovered]
      exact listCase children
where
  listCase : ∀ children : List Atom,
      ruleTemplatesCovered input σ children = ruleTemplatesCovered input τ children
    | [] => rfl
    | child :: rest => by
        simp only [ruleTemplatesCovered, ruleTemplateCovered_congr same input child, listCase rest]

theorem instantiate_congr {σ τ : Subst} (same : SameLookup σ τ) (input : InputSpec) (template : Atom) :
    instantiateRuleTemplateAtom? input σ template = instantiateRuleTemplateAtom? input τ template := by
  simp only [instantiateRuleTemplateAtom?, ruleTemplateCovered_congr same input template,
    applySubst_congr same template]

theorem foldl_stage_congr (input : InputSpec) (sink : Sink) :
    ∀ {rows rows' : List Subst} (staged : List Atom), List.Forall₂ SameLookup rows rows' →
      rows.foldl (stageRuleScopedSink input sink) staged = rows'.foldl (stageRuleScopedSink input sink) staged
  | [], [], _, .nil => rfl
  | row :: rows, row' :: rows', staged, .cons same rest => by
      simp only [List.foldl_cons]
      have step : stageRuleScopedSink input sink staged row = stageRuleScopedSink input sink staged row' := by
        simp only [stageRuleScopedSink, instantiate_congr same input sink.atom]
      rw [step]
      exact foldl_stage_congr input sink _ rest

theorem batch_congr (input : InputSpec) {rows rows' : List Subst} (related : List.Forall₂ SameLookup rows rows') :
    ∀ (sinks : List Sink) (space : List Atom),
      cApplyRuleScopedSinkBatch input rows space sinks = cApplyRuleScopedSinkBatch input rows' space sinks
  | [], _ => rfl
  | sink :: rest, space => by
      simp only [cApplyRuleScopedSinkBatch, foldl_stage_congr input sink [] related]
      exact batch_congr input related rest _

theorem forall₂_map_left {α β γ : Type} {R : γ → β → Prop} {S : α → β → Prop} (f : α → γ) :
    ∀ {as : List α} {bs : List β}, List.Forall₂ S as bs → (∀ a b, S a b → b ∈ bs → R (f a) b) →
      List.Forall₂ R (as.map f) bs
  | [], [], .nil, _ => .nil
  | a :: as, b :: bs, .cons related rest, step => by
      simp only [List.map_cons]
      exact .cons (step a b related (by simp))
        (forall₂_map_left f rest fun a' b' related' member => step a' b' related' (by simp [member]))

/-! ### The bridge -/

/-- **The kernel fires a comma conjunction with add and remove sinks as the support model
does**, when every stored atom of the read copy is ground or out of every pattern's reach
and every add precedes every remove. -/
theorem fireDirective_eq_ruleScoped_ground (prims : Primitives) (external : ExternalState)
    (space : List Atom) (atom loc : Atom) (priority : ℕ) (name : String) (patterns : List Atom)
    (adds rest : List Sink) (eager : ∀ sink ∈ adds, writesEagerly sink = true)
    (removes : ∀ sink ∈ rest, ∃ body, sink = .remove body)
    (fragment : MatchFragment patterns (morkInsertSupport (morkEraseSupport space atom) atom)) :
    fireDirective prims external space
        ⟨atom, .compat patterns, .sinks ((adds ++ rest).map MainlineSink.core)⟩ =
      .ok (cFireRuleScopedSourceExecFact space
        ⟨atom, loc, ⟨priority, name, .compat ⟨patterns⟩, [], ⟨adds ++ rest⟩⟩⟩, external) := by
  set read := morkInsertSupport (morkEraseSupport space atom) atom with readEq
  set input : InputSpec := .compat ⟨patterns⟩
  have corr := conjunctionRows_corr (factorTag atom) read patterns 0 [] [] [] fragment
    ⟨fun _ => rfl, fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩
  have related : List.Forall₂ SameLookup
      ((conjunctionRows (factorTag atom) read 0 [] patterns).map (inputRow (inputSpecVariables input)))
      ((Conformance.Computable.cmatchPattern.go read patterns [] []).map Prod.fst) := by
    apply forall₂_map_left _ corr
    intro θ σ rowCorr member
    apply inputRow_sameLookup rowCorr.1
    intro varName
    obtain ⟨found, foundMember, rfl⟩ := List.mem_map.1 member
    rw [go_domain read patterns [] [] found foundMember varName]
    simp [lookup_nil, input, inputSpecVariables]
  unfold fireDirective
  simp only [MainlineInput.coverage, mainlineRows, bind, Except.bind]
  rw [applyMainlineSinks_core prims _ _ _ external adds rest eager removes]
  unfold cFireRuleScopedSourceExecFact cApplyRuleScopedTemplate
  simp only [cMatchInputSpecMork, Conformance.Computable.cmatchPattern, matchSourceGuards, List.all_nil,
    List.filter_true]
  congr 2
  exact batch_congr input related _ _

/-! ### The fragment is inhabited -/

/-- `(exec 0 (, (edge $x $y)) (O (+ (path $x $y)) (- (edge $x $y))))`. -/
def edgeDirective : Atom :=
  .expression [.symbol "exec", .symbol "0",
    .expression [.symbol ",", .expression [.symbol "edge", .var "x", .var "y"]],
    .expression [.symbol "O", .expression [.symbol "+", .expression [.symbol "path", .var "x", .var "y"]],
      .expression [.symbol "-", .expression [.symbol "edge", .var "x", .var "y"]]]]

/-- A read copy in the fragment: a ground fact and the directive itself, whose head `exec`
no pattern `(edge …)` reaches. -/
theorem edge_matchFragment :
    MatchFragment [.expression [.symbol "edge", .var "x", .var "y"]]
      [.expression [.symbol "edge", .symbol "a", .symbol "b"], edgeDirective] := by
  intro stored member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact Or.inl rfl
  · refine Or.inr fun pattern patternMember => ?_
    simp only [List.mem_singleton] at patternMember
    subst patternMember
    exact ⟨"edge", "exec", _, _, rfl, rfl, by decide⟩

end Mettapedia.Languages.ProcessCalculi.MORK.Mainline

import Mettapedia.Languages.MeTTa.EquationKernel.Hygiene

/-!
# Computed matching: steps without left-side bindings

The bindings of a step's left-side variables are a function of the left side
and the subatom (`getD_agree_of_subst_eq`), so a certificate need not supply
them. `matchAtom` computes them by one-way matching; variables of the subject
are constants. A compressed step supplies only its citation, its position and
the bindings of variables that occur only on the right side.

The compressed row is checked by expanding it into an ordinary step row with
the computed bindings, so the matcher is not part of the trust base: a wrong
matcher could only cause refusals (`compressed_claim_sound`). Its
completeness (`matchAtom_complete`) gives every step a compressed form that
the checker accepts (`compressed_step_complete`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.EquationKernel

open Mettapedia.Languages.MeTTa.OSLFCore (Atom Atomspace)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra (Var Subst subst vars)

/-! ## One-way matching -/

mutual

/-- Extend bindings so that the pattern's instance is the target, if possible.
Earlier bindings are kept; a repeated variable must meet the same atom. -/
def matchAtom : Atom → Atom → Bindings → Option Bindings
  | .var name, target, bindings =>
      match bindings.lookup name with
      | none => some ((name, target) :: bindings)
      | some bound => if bound = target then some bindings else none
  | .expression patterns, .expression targets, bindings => matchAtoms patterns targets bindings
  | .expression _, _, _ => none
  | .symbol name, target, bindings => if Atom.symbol name = target then some bindings else none
  | .grounded value, target, bindings => if Atom.grounded value = target then some bindings else none

def matchAtoms : List Atom → List Atom → Bindings → Option Bindings
  | [], [], bindings => some bindings
  | pattern :: patterns, target :: targets, bindings =>
      (matchAtom pattern target bindings).bind (matchAtoms patterns targets)
  | _, _, _ => none

end

/-- Bindings agree with a substitution, as replacements, on their keys. -/
def Bindings.AgreesWith (bindings : Bindings) (σ : Subst) : Prop :=
  ∀ name value, bindings.lookup name = some value → value = (σ name).getD (.var name)

/-- Every key of the bindings is a variable of the pattern, or an earlier key. -/
def Bindings.Covers (bindings : Bindings) (names : List Var) : Prop :=
  ∀ name, name ∈ names → bindings.lookup name ≠ none

theorem lookup_cons (name key : Var) (value : Atom) (rest : Bindings) :
    ((key, value) :: rest).lookup name = if name = key then some value else rest.lookup name := by
  by_cases same : name = key
  · subst same
    simp [List.lookup]
  · have different : (name == key) = false := by simpa using same
    simp [List.lookup, different, same]

/-- Keys of the extended bindings come from the earlier bindings or the pattern. -/
def Bindings.KeysFrom (extended bindings : Bindings) (names : List Var) : Prop :=
  ∀ name, extended.lookup name ≠ none → bindings.lookup name ≠ none ∨ name ∈ names

mutual

theorem matchAtom_complete (σ : Subst) :
    ∀ (pattern : Atom) (bindings : Bindings), bindings.AgreesWith σ →
      ∃ extended, matchAtom pattern (subst σ pattern) bindings = some extended ∧
        extended.AgreesWith σ ∧ extended.Covers (vars pattern) ∧
        extended.KeysFrom bindings (vars pattern) ∧
        ∀ name, bindings.lookup name ≠ none → extended.lookup name = bindings.lookup name
  | .var name, bindings, agrees => by
      cases bound : bindings.lookup name with
      | none =>
          refine ⟨(name, subst σ (.var name)) :: bindings, ?_, ?_, ?_, ?_, ?_⟩
          · simp [matchAtom, bound]
          · intro key value found
            rw [lookup_cons] at found
            split_ifs at found with same
            · cases found
              subst same
              simp [subst]
            · exact agrees key value found
          · intro key member
            simp only [vars, List.mem_singleton] at member
            subst member
            simp
          · intro key present
            rw [lookup_cons] at present
            split_ifs at present with same
            · exact .inr (by simp [vars, same])
            · exact .inl present
          · intro key present
            rw [lookup_cons]
            split_ifs with same
            · subst same
              exact absurd bound present
            · rfl
      | some value =>
          have same : value = subst σ (.var name) := by
            simpa [subst] using agrees name value bound
          refine ⟨bindings, ?_, agrees, ?_, fun _ present => .inl present, fun _ _ => rfl⟩
          · simp [matchAtom, bound, same]
          · intro key member
            simp only [vars, List.mem_singleton] at member
            subst member
            simp [bound]
  | .symbol name, bindings, agrees =>
      ⟨bindings, by simp [matchAtom, subst], agrees, by simp [Bindings.Covers, vars],
        fun _ present => .inl present, fun _ _ => rfl⟩
  | .grounded value, bindings, agrees =>
      ⟨bindings, by simp [matchAtom, subst], agrees, by simp [Bindings.Covers, vars],
        fun _ present => .inl present, fun _ _ => rfl⟩
  | .expression patterns, bindings, agrees => by
      obtain ⟨extended, matched, extendedAgrees, covers, keysFrom, keeps⟩ :=
        matchAtoms_complete σ patterns bindings agrees
      refine ⟨extended, ?_, extendedAgrees, ?_, ?_, keeps⟩
      · rw [subst_expression]
        simpa [matchAtom] using matched
      · intro key member
        rw [vars_expression] at member
        exact covers key member
      · intro key present
        rw [vars_expression]
        exact keysFrom key present

theorem matchAtoms_complete (σ : Subst) :
    ∀ (patterns : List Atom) (bindings : Bindings), bindings.AgreesWith σ →
      ∃ extended, matchAtoms patterns (patterns.map (subst σ)) bindings = some extended ∧
        extended.AgreesWith σ ∧ extended.Covers (patterns.flatMap vars) ∧
        extended.KeysFrom bindings (patterns.flatMap vars) ∧
        ∀ name, bindings.lookup name ≠ none → extended.lookup name = bindings.lookup name
  | [], bindings, agrees =>
      ⟨bindings, by simp [matchAtoms], agrees, by simp [Bindings.Covers],
        fun _ present => .inl present, fun _ _ => rfl⟩
  | pattern :: patterns, bindings, agrees => by
      obtain ⟨middle, first, middleAgrees, middleCovers, middleKeys, middleKeeps⟩ :=
        matchAtom_complete σ pattern bindings agrees
      obtain ⟨extended, rest, extendedAgrees, extendedCovers, extendedKeys, extendedKeeps⟩ :=
        matchAtoms_complete σ patterns middle middleAgrees
      refine ⟨extended, ?_, extendedAgrees, ?_, ?_, ?_⟩
      · simp [matchAtoms, first, rest]
      · intro key member
        rcases (by simpa [List.flatMap_cons] using member :
            key ∈ vars pattern ∨ ∃ child ∈ patterns, key ∈ vars child) with here | ⟨child, childMember, inner⟩
        · have present := middleCovers key here
          rw [extendedKeeps key present]
          exact present
        · exact extendedCovers key (List.mem_flatMap.mpr ⟨child, childMember, inner⟩)
      · intro key present
        rcases extendedKeys key present with earlier | there
        · rcases middleKeys key earlier with older | here
          · exact .inl older
          · exact .inr (List.mem_flatMap.mpr ⟨pattern, List.mem_cons_self .., here⟩)
        · exact .inr (List.mem_flatMap.mpr (by
            obtain ⟨child, member, inner⟩ := List.mem_flatMap.mp there
            exact ⟨child, List.mem_cons_of_mem _ member, inner⟩))
      · intro key present
        rw [extendedKeeps key (by rw [middleKeeps key present]; exact present), middleKeeps key present]

end

theorem lookup_append (name : Var) (front back : Bindings) :
    (front ++ back).lookup name = (front.lookup name).or (back.lookup name) := by
  induction front with
  | nil => simp
  | cons head rest ih =>
      rcases head with ⟨key, value⟩
      simp only [List.cons_append, lookup_cons, ih]
      split_ifs <;> simp

/-- Covering bindings that agree with a substitution give its instances. -/
theorem subst_toSubst_of_agrees {bindings : Bindings} {σ : Subst} {atom : Atom}
    (agrees : bindings.AgreesWith σ) (covers : bindings.Covers (vars atom)) :
    subst bindings.toSubst atom = subst σ atom := by
  apply subst_congr_getD
  intro name member
  have present := covers name member
  obtain ⟨value, found⟩ := Option.ne_none_iff_exists'.mp present
  simp [Bindings.toSubst, found, agrees name value found]

/-! ## Compressed step rows -/

/-- The bindings of a compressed step: computed left-side bindings, then the
supplied right-only bindings. -/
def compressedBindings (current : Atom) (path : List Nat) (citation : Citation) (extra : Bindings) :
    Option Bindings :=
  match equationSides citation.equation, subatom? current path with
  | some (left, _), some focus => (matchAtom left focus []).map (· ++ extra)
  | _, _ => none

/-- The claim of a compressed step row: the claim of the ordinary step row
with the computed bindings. -/
def compressedClaim? (program : List Atom) (table : List Claim) (prior : Nat) (citation : Citation)
    (path : List Nat) (extra : Bindings) : Option Claim :=
  match table[prior]? with
  | some (_, current) =>
      (compressedBindings current path citation extra).bind fun bindings =>
        (Row.step prior citation path bindings).claim? program table
  | none => none

/-- Soundness needs no property of the matcher: an accepted compressed row is
an accepted ordinary row. -/
theorem compressed_claim_sound {program : List Atom} {table : List Claim} {prior : Nat}
    {citation : Citation} {path : List Nat} {extra : Bindings} {claim : Claim}
    (computed : compressedClaim? program table prior citation path extra = some claim) :
    ∃ bindings, Row.Valid program table (.step prior citation path bindings) claim := by
  unfold compressedClaim? at computed
  split at computed
  · obtain ⟨bindings, _, stepped⟩ := Option.bind_eq_some_iff.mp computed
    exact ⟨bindings, (Row.claim?_exact _ _ _ _).mp stepped⟩
  · cases computed

/-- Every step has a compressed form: citation, position and the bindings of
the right-only variables suffice. -/
theorem compressed_step_complete {program : List Atom} {table : List Claim} {prior : Nat}
    {citation : Citation} {path : List Nat} {bindings : Bindings} {claim : Claim} {left right : Atom}
    (sides : equationSides citation.equation = some (left, right))
    (valid : Row.Valid program table (.step prior citation path bindings) claim) :
    compressedClaim? program table prior citation path
      (bindingsOn bindings.toSubst (rightOnly left right)) = some claim := by
  cases valid with
  | @step _ _ _ _ source current left' right' next atPrior equation cited found replaced =>
      have same := (equationSides_eq_some.mpr equation).symm.trans sides
      simp only [Option.some.injEq, Prod.mk.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      let σ := bindings.toSubst
      obtain ⟨matched, matchedEq, agrees, covers, keysFrom, _⟩ :=
        matchAtom_complete σ left' [] (by intro _ _ found; cases found)
      let combined := matched ++ bindingsOn σ (rightOnly left' right')
      have combinedLeft : subst combined.toSubst left' = subst σ left' := by
        apply subst_congr_getD
        intro name member
        obtain ⟨value, found⟩ := Option.ne_none_iff_exists'.mp (covers name member)
        simp [combined, Bindings.toSubst, lookup_append, found, agrees name value found]
      have combinedRight : subst combined.toSubst right' = subst σ right' := by
        apply subst_congr_getD
        intro name member
        by_cases onLeft : name ∈ vars left'
        · obtain ⟨value, found⟩ := Option.ne_none_iff_exists'.mp (covers name onLeft)
          simp [combined, Bindings.toSubst, lookup_append, found, agrees name value found]
        · have absent : matched.lookup name = none := by
            by_contra present
            rcases keysFrom name present with earlier | here
            · exact earlier rfl
            · exact onLeft here
          have rightMember : name ∈ rightOnly left' right' := by simp [rightOnly, member, onLeft]
          have extraFound := lookup_bindingsOn σ _ name rightMember
          simp only [combined, Bindings.toSubst, lookup_append, absent, Option.none_or]
          simp only [Bindings.toSubst] at extraFound
          rw [extraFound]
      have matchedAt : matchAtom left' (subst bindings.toSubst left') [] = some matched := matchedEq
      unfold compressedClaim? compressedBindings
      simp only [atPrior, sides, found, matchedAt, Option.map_some, Option.bind_some]
      apply (Row.claim?_exact _ _ _ _).mpr
      exact .step atPrior equation cited (combinedLeft ▸ found) (combinedRight ▸ replaced)

/-! ## Sites given as patterns

A site may be given as a pattern over the current atom in which one hole
variable occurs once; the pattern's other variables stand for the parts the
step keeps. Matching the pattern against the current atom binds the hole to
the subatom and the other variables to the kept parts, so the substitution
carries the position. The result replaces the hole's binding. The checker
re-substitutes and compares, so neither matcher is trusted
(`contextClaim_sound`), and every step has such a site
(`contextClaim_complete`): the current atom with a fresh hole at the step's
position. A pattern may also abstract kept arguments by variables, which
matching then binds. -/

/-- Variables of the atoms a context keeps. -/
def Context.keptVars : Context → List Var
  | .hole => []
  | .arg left inner right => left.flatMap vars ++ inner.keptVars ++ right.flatMap vars

theorem Context.vars_fill (context : Context) (atom : Atom) :
    ∀ name, name ∈ vars (context.fill atom) ↔ name ∈ context.keptVars ∨ name ∈ vars atom := by
  induction context with
  | hole => intro name; simp [Context.keptVars, Context.fill]
  | arg left inner right ih =>
      intro name
      simp only [Context.fill, Context.keptVars, vars_expression, List.flatMap_append,
        List.flatMap_cons, List.mem_append, ih]
      tauto

theorem Context.count_fill (context : Context) (atom : Atom) (name : Var) :
    (vars (context.fill atom)).count name =
      (context.keptVars).count name + (vars atom).count name := by
  induction context with
  | hole => simp [Context.keptVars, Context.fill]
  | arg left inner right ih =>
      simp only [Context.fill, Context.keptVars, vars_expression, List.flatMap_append,
        List.flatMap_cons, List.count_append, ih]
      omega

/-- An atom in which a name occurs exactly once is a context filled with
that variable, and the context keeps no other occurrence. -/
theorem exists_hole_context (hole : Var) :
    ∀ pattern : Atom, (vars pattern).count hole = 1 →
      ∃ context : Context, pattern = context.fill (.var hole) ∧ hole ∉ context.keptVars
  | .var name, once => by
      have same : name = hole := by
        by_contra different
        simp [vars, List.count_cons] at once
        exact different once
      subst same
      exact ⟨.hole, rfl, by simp [Context.keptVars]⟩
  | .symbol _, once => by simp [vars] at once
  | .grounded _, once => by simp [vars] at once
  | .expression atoms, once => by
      rw [vars_expression] at once
      obtain ⟨left, child, right, split, leftNone, childOnce, rightNone⟩ :=
        exists_unique_child hole atoms once
      obtain ⟨inner, childFill, innerFree⟩ := exists_hole_context hole child childOnce
      refine ⟨.arg left inner right, ?_, ?_⟩
      · rw [split, childFill]
        rfl
      · intro member
        simp only [Context.keptVars, List.mem_append] at member
        rcases member with (inLeft | inInner) | inRight
        · exact absurd (List.count_pos_iff.mpr inLeft) (by omega)
        · exact innerFree inInner
        · exact absurd (List.count_pos_iff.mpr inRight) (by omega)
termination_by pattern => sizeOf pattern
decreasing_by
  subst split
  simp_wf
  have : sizeOf child < sizeOf (left ++ child :: right) := List.sizeOf_lt_of_mem (by simp)
  omega
where
  exists_unique_child (hole : Var) :
      ∀ atoms : List Atom, (atoms.flatMap vars).count hole = 1 →
        ∃ left child right, atoms = left ++ child :: right ∧ (left.flatMap vars).count hole = 0 ∧
          (vars child).count hole = 1 ∧ (right.flatMap vars).count hole = 0
    | [], once => by simp at once
    | atom :: rest, once => by
        simp only [List.flatMap_cons, List.count_append] at once
        by_cases here : (vars atom).count hole = 1
        · exact ⟨[], atom, rest, rfl, by simp, here, by omega⟩
        · have later : (rest.flatMap vars).count hole = 1 := by omega
          have none : (vars atom).count hole = 0 := by omega
          obtain ⟨left, child, right, split, leftNone, childOnce, rightNone⟩ :=
            exists_unique_child hole rest later
          exact ⟨atom :: left, child, right, by simp [split], by simp [List.flatMap_cons, none, leftNone],
            childOnce, rightNone⟩

theorem Context.substitute_congr (context : Context) {σ τ : Subst}
    (agree : ∀ name ∈ context.keptVars, (σ name).getD (.var name) = (τ name).getD (.var name)) :
    context.substitute σ = context.substitute τ := by
  induction context with
  | hole => rfl
  | arg left inner right ih =>
      simp only [Context.substitute]
      have keep : ∀ child, child ∈ left ∨ child ∈ right → subst σ child = subst τ child := by
        intro child member
        apply subst_congr_getD
        intro name inner'
        apply agree
        simp only [Context.keptVars, List.mem_append, List.mem_flatMap]
        rcases member with here | there
        · exact .inl (.inl ⟨child, here, inner'⟩)
        · exact .inr ⟨child, there, inner'⟩
      rw [List.map_congr_left (fun child member => keep child (.inl member)),
        List.map_congr_left (fun child member => keep child (.inr member)),
        ih (fun name member => agree name (by simp [Context.keptVars, member]))]

/-- The claim of a step whose site is a pattern with one hole. -/
def contextClaim? (program : List Atom) (table : List Claim) (prior : Nat) (citation : Citation)
    (pattern : Atom) (hole : Var) (extra : Bindings) : Option Claim :=
  match table[prior]?, equationSides citation.equation with
  | some (source, current), some (left, right) =>
      if (vars pattern).count hole = 1 ∧ citation.copy < program.count citation.equation then
        match matchAtom pattern current [] with
        | some around =>
            match around.lookup hole with
            | some focus =>
                match matchAtom left focus [] with
                | some inner =>
                    let σ := (inner ++ extra).toSubst
                    if subst (Bindings.toSubst ((hole, subst σ left) :: around)) pattern = current then
                      some (source, subst (Bindings.toSubst ((hole, subst σ right) :: around)) pattern)
                    else none
                | none => none
            | none => none
        | none => none
      else none
  | _, _ => none

/-- An accepted pattern site is a step of the judgment, whatever the
matchers computed. -/
theorem contextClaim_sound {program : List Atom} {table : List Claim} {prior : Nat}
    {citation : Citation} {pattern : Atom} {hole : Var} {extra : Bindings} {source target : Atom}
    (accepted : contextClaim? program table prior citation pattern hole extra = some (source, target)) :
    ∃ current, table[prior]? = some (source, current) ∧ Step (spaceOf program) current target := by
  unfold contextClaim? at accepted
  split at accepted
  · rename_i source' current left right atPrior sides
    split_ifs at accepted with conditions
    split at accepted
    · rename_i around _
      split at accepted
      · rename_i focus _
        split at accepted
        · rename_i inner _
          dsimp only at accepted
          split_ifs at accepted with recovered
          simp only [Option.some.injEq, Prod.mk.injEq] at accepted
          obtain ⟨rfl, rfl⟩ := accepted
          refine ⟨current, atPrior, ?_⟩
          obtain ⟨context, shape, free⟩ := exists_hole_context hole pattern conditions.1
          have stored := (Citation.valid_spaceOf.mpr conditions.2).mem
          rw [equationSides_eq_some.mp sides] at stored
          let σ := (inner ++ extra).toSubst
          have sameContext : context.substitute (Bindings.toSubst ((hole, subst σ left) :: around)) =
              context.substitute (Bindings.toSubst ((hole, subst σ right) :: around)) := by
            apply Context.substitute_congr
            intro name member
            have different : name ≠ hole := fun same => free (same ▸ member)
            simp [Bindings.toSubst, lookup_cons, different]
          rw [shape, Context.substitute_fill] at recovered ⊢
          have holeLeft : subst (Bindings.toSubst ((hole, subst σ left) :: around)) (.var hole) =
              subst σ left := by simp [subst, Bindings.toSubst]
          have holeRight : subst (Bindings.toSubst ((hole, subst σ right) :: around)) (.var hole) =
              subst σ right := by simp [subst, Bindings.toSubst]
          rw [holeLeft] at recovered
          rw [holeRight, ← sameContext, ← recovered]
          exact .rewrite _ σ stored
        · cases accepted
      · cases accepted
    · cases accepted
  · cases accepted

/-- A name longer than every name of a list, hence not in it. -/
def freshName (names : List Var) : Var :=
  String.ofList (List.replicate ((names.map String.length).sum + 1) 'h')

theorem le_sum_of_mem_nat : ∀ {numbers : List Nat} {number : Nat}, number ∈ numbers → number ≤ numbers.sum
  | [], _, member => absurd member List.not_mem_nil
  | head :: rest, number, member => by
      rcases List.mem_cons.mp member with rfl | later
      · simp
      · have := le_sum_of_mem_nat later
        simp only [List.sum_cons]
        omega

theorem freshName_not_mem (names : List Var) : freshName names ∉ names := by
  intro member
  have bound : (freshName names).length ≤ (names.map String.length).sum :=
    le_sum_of_mem_nat (List.mem_map.mpr ⟨_, member, rfl⟩)
  simp [freshName] at bound
  omega

theorem Context.substitute_empty (context : Context) :
    context.substitute SubstitutionAlgebra.empty = context := by
  induction context with
  | hole => rfl
  | arg left inner right ih =>
      simp only [Context.substitute, ih]
      congr 1
      · exact (List.map_congr_left fun child _ => SubstitutionAlgebra.subst_empty child).trans
          (List.map_id left)
      · exact (List.map_congr_left fun child _ => SubstitutionAlgebra.subst_empty child).trans
          (List.map_id right)

theorem Context.keptVars_subset (context : Context) (atom : Atom) :
    ∀ name ∈ context.keptVars, name ∈ vars (context.fill atom) :=
  fun name member => (Context.vars_fill context atom name).mpr (.inl member)

/-- Every step has a site given as a pattern: the current atom with a fresh
hole at the step's position. -/
theorem contextClaim_complete {program : List Atom} {table : List Claim} {prior : Nat}
    {citation : Citation} {path : List Nat} {bindings : Bindings} {claim : Claim} {left right : Atom}
    (sides : equationSides citation.equation = some (left, right))
    (valid : Row.Valid program table (.step prior citation path bindings) claim) :
    ∃ pattern hole, contextClaim? program table prior citation pattern hole
      (bindingsOn bindings.toSubst (rightOnly left right)) = some claim := by
  cases valid with
  | @step _ _ _ _ source current left' right' next atPrior equation cited found replaced =>
      have same := (equationSides_eq_some.mpr equation).symm.trans sides
      simp only [Option.some.injEq, Prod.mk.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      let σ := bindings.toSubst
      obtain ⟨context, _, fill, replace⟩ := exists_context_of_subatom? found
      rw [replace] at replaced
      cases replaced
      let hole := freshName (vars current)
      have holeAbsent : hole ∉ vars current := freshName_not_mem _
      have holeFree : hole ∉ context.keptVars := fun member =>
        holeAbsent (fill ▸ Context.keptVars_subset context _ hole member)
      refine ⟨context.fill (.var hole), hole, ?_⟩
      have once : (vars (context.fill (.var hole))).count hole = 1 := by
        rw [Context.count_fill, List.count_eq_zero_of_not_mem holeFree]
        simp [vars]
      -- matching the pattern against the current atom
      let ρ : Subst := fun name => if name = hole then some (subst σ left') else none
      have ρContext : context.substitute ρ = context := by
        refine (Context.substitute_congr context (τ := SubstitutionAlgebra.empty) ?_).trans
          (Context.substitute_empty context)
        intro name member
        have different : name ≠ hole := fun equal => holeFree (equal ▸ member)
        simp [ρ, different, SubstitutionAlgebra.empty]
      have ρPattern : subst ρ (context.fill (.var hole)) = current := by
        rw [Context.substitute_fill, ρContext, ← fill]
        simp [ρ, subst, σ]
      obtain ⟨around, aroundEq, aroundAgrees, aroundCovers, _, _⟩ :=
        matchAtom_complete ρ (context.fill (.var hole)) [] (by intro _ _ found; cases found)
      rw [ρPattern] at aroundEq
      have holeBound : around.lookup hole = some (subst σ left') := by
        have present := aroundCovers hole (by
          rw [Context.vars_fill]
          exact .inr (by simp [vars]))
        obtain ⟨value, found'⟩ := Option.ne_none_iff_exists'.mp present
        rw [found', aroundAgrees hole value found']
        simp [ρ]
      -- matching the left side against the subatom
      obtain ⟨inner, innerEq, innerAgrees, innerCovers, innerKeys, _⟩ :=
        matchAtom_complete σ left' [] (by intro _ _ found; cases found)
      let combined := inner ++ bindingsOn σ (rightOnly left' right')
      have combinedLeft : subst combined.toSubst left' = subst σ left' := by
        apply subst_congr_getD
        intro name member
        obtain ⟨value, found'⟩ := Option.ne_none_iff_exists'.mp (innerCovers name member)
        simp [combined, Bindings.toSubst, lookup_append, found', innerAgrees name value found']
      have combinedRight : subst combined.toSubst right' = subst σ right' := by
        apply subst_congr_getD
        intro name member
        by_cases onLeft : name ∈ vars left'
        · obtain ⟨value, found'⟩ := Option.ne_none_iff_exists'.mp (innerCovers name onLeft)
          simp [combined, Bindings.toSubst, lookup_append, found', innerAgrees name value found']
        · have absent : inner.lookup name = none := by
            by_contra present
            rcases innerKeys name present with earlier | here
            · exact earlier rfl
            · exact onLeft here
          have rightMember : name ∈ rightOnly left' right' := by simp [rightOnly, member, onLeft]
          have extraFound := lookup_bindingsOn σ _ name rightMember
          simp only [combined, Bindings.toSubst, lookup_append, absent, Option.none_or]
          simp only [Bindings.toSubst] at extraFound
          rw [extraFound]
      -- the kept parts are bound to themselves
      have keptSame : ∀ value : Atom,
          context.substitute (Bindings.toSubst ((hole, value) :: around)) = context := by
        intro value
        refine (Context.substitute_congr context (τ := SubstitutionAlgebra.empty) ?_).trans
          (Context.substitute_empty context)
        intro name member
        have different : name ≠ hole := fun equal => holeFree (equal ▸ member)
        have kept := aroundCovers name (by
          rw [Context.vars_fill]
          exact .inl member)
        obtain ⟨bound, found'⟩ := Option.ne_none_iff_exists'.mp kept
        have agreed := aroundAgrees name bound found'
        simp only [ρ, different, if_false, Option.getD_none] at agreed
        simp [Bindings.toSubst, lookup_cons, different, found', agreed, SubstitutionAlgebra.empty]
      have innerAt : matchAtom left' (subst σ left') [] = some inner := innerEq
      unfold contextClaim?
      simp only [atPrior, sides, once, Citation.valid_spaceOf.mp cited, and_self, if_true, aroundEq,
        holeBound, innerAt]
      have recovered : subst (Bindings.toSubst ((hole, subst combined.toSubst left') :: around))
          (context.fill (.var hole)) = current := by
        rw [Context.substitute_fill, keptSame, combinedLeft, ← fill]
        simp [subst, Bindings.toSubst, σ]
      have target : subst (Bindings.toSubst ((hole, subst combined.toSubst right') :: around))
          (context.fill (.var hole)) = context.fill (subst σ right') := by
        rw [Context.substitute_fill, keptSame, combinedRight]
        simp [subst, Bindings.toSubst]
      simp only [combined] at recovered target
      rw [if_pos recovered, target]

end Mettapedia.Languages.MeTTa.EquationKernel

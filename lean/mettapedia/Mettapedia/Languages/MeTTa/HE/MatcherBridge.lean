import Mettapedia.Languages.MeTTa.HE.EvalSpec
import Mettapedia.Languages.MeTTa.HE.SmallStepMaster
import Mettapedia.Languages.MeTTa.HE.BindingComposition

/-!
# Historical control-shell mathematics over the ground matcher

The independent ground-matcher laws live in `BindingComposition`. This owner
retains constructor algebra for the historical `EvalSpec` and `MinimalMeTTa`
judgments. These theorems do not infer historical source meaning from stable
execution of the maintained invocation worker. Actual selected-frame source
and retained-worker results live in `RecursiveSemanticSoundness` and
`FirstSuccessSourceExecution`.
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open private mergeGround? GroundBindingsCanon matchAtoms_ground_canon
  mergeGround_lookup_spec lookup_ground hasAssignedVar_false_of_ground
  simpleMatch_ground_matchAtoms_nil_nonexpr mergeGroundAssignments?
  mergeGroundAssignments_equalities
  from Mettapedia.Languages.MeTTa.HE.BindingComposition

private def collectVarsListAux (es : List Atom) (fuel : Nat) : List String :=
  match es with
  | [] => []
  | a :: as => collectVars a fuel ++ collectVarsListAux as fuel


private theorem collectVarsList_eq_aux (es : List Atom) (fuel : Nat) :
    collectVars.collectVarsList es fuel = collectVarsListAux es fuel := by
  induction es with
  | nil =>
      rfl
  | cons a as ih =>
      simp [collectVars.collectVarsList, collectVarsListAux, ih]


private theorem collectVars_expr_eq_aux (es : List Atom) (fuel : Nat) :
    collectVars (.expression es) (fuel + 1) = collectVarsListAux es fuel := by
  simp [collectVars, collectVarsList_eq_aux]


/-- On ground matcher bindings, `Bindings.apply` depends only on the lookups
of variables that syntactically occur in the atom being substituted.

Positive example:
- if `b₂` agrees with `b₁` on every variable in `body`, then applying either
  bindings set to `body` yields the same substituted atom.

Negative example:
- this theorem is intentionally restricted to *ground* `b₁`; without that,
  a variable in `body` could resolve through an extra indirection not
  mentioned syntactically in `body` itself. -/
private theorem apply_eq_of_lookup_eq_on_collectVars :
    ∀ fuel : Nat,
      (∀ {a : Atom} {b₁ b₂ : Bindings},
        GroundBindings b₁ →
        (∀ v, v ∈ collectVars a fuel → b₂.lookup v = b₁.lookup v) →
        b₂.apply a fuel = b₁.apply a fuel) ∧
      (∀ {es : List Atom} {b₁ b₂ : Bindings},
        GroundBindings b₁ →
        (∀ v, v ∈ collectVarsListAux es fuel → b₂.lookup v = b₁.lookup v) →
        es.map (b₂.apply · fuel) = es.map (b₁.apply · fuel)) := by
  intro fuel
  induction fuel with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro a b₁ b₂ _ _
        simp [Bindings.apply]
      · intro es b₁ b₂ _ _
        induction es with
        | nil => rfl
        | cons a as ih => simp [Bindings.apply]
  | succ n ih =>
      obtain ⟨ihAtom, ihList⟩ := ih
      have hAtom :
          ∀ {a : Atom} {b₁ b₂ : Bindings},
            GroundBindings b₁ →
            (∀ v, v ∈ collectVars a (n + 1) → b₂.lookup v = b₁.lookup v) →
            b₂.apply a (n + 1) = b₁.apply a (n + 1) := by
        intro a b₁ b₂ hb hagree
        cases a with
        | symbol s =>
            simp [Bindings.apply]
        | grounded g =>
            simp [Bindings.apply]
        | var v =>
            have hlookEq : b₂.lookup v = b₁.lookup v := by
              exact hagree v (by simp [collectVars])
            cases h₁ : b₁.lookup v with
            | none =>
                have h₂ : b₂.lookup v = none := by
                  rw [h₁] at hlookEq
                  exact hlookEq
                simp [Bindings.apply, Bindings.resolve, h₁, h₂]
            | some val =>
                have h₂ : b₂.lookup v = some val := by
                  rw [h₁] at hlookEq
                  exact hlookEq
                have hground : GroundAtom val := lookup_ground hb h₁
                cases n with
                | zero =>
                    simp [Bindings.apply, Bindings.resolve,
                      Bindings.resolveAtomAux, h₁, h₂]
                | succ m =>
                    have hstable₁ := hasAssignedVar_false_of_ground hground b₁
                    have hstable₂ := hasAssignedVar_false_of_ground hground b₂
                    simp [Bindings.apply, Bindings.resolve,
                      Bindings.resolveAtomAux, h₁, h₂, hstable₁, hstable₂]
        | expression es =>
            have hvars :
                ∀ v, v ∈ collectVarsListAux es n → b₂.lookup v = b₁.lookup v := by
              intro v hv
              exact hagree v (by simpa [collectVars_expr_eq_aux es n] using hv)
            have hmap := ihList (es := es) (b₁ := b₁) (b₂ := b₂) hb hvars
            simpa [Bindings.apply] using congrArg Atom.expression hmap
      have hList :
          ∀ {es : List Atom} {b₁ b₂ : Bindings},
            GroundBindings b₁ →
            (∀ v, v ∈ collectVarsListAux es (n + 1) → b₂.lookup v = b₁.lookup v) →
            es.map (b₂.apply · (n + 1)) = es.map (b₁.apply · (n + 1)) := by
        intro es b₁ b₂ hb hagree
        induction es with
        | nil =>
            rfl
        | cons a as ihEs =>
            have hHead :
                b₂.apply a (n + 1) = b₁.apply a (n + 1) := by
              apply hAtom hb
              intro v hv
              exact hagree v (by simp [collectVarsListAux, hv])
            have hTail :
                as.map (b₂.apply · (n + 1)) = as.map (b₁.apply · (n + 1)) := by
              exact ihEs
                (fun v hv => hagree v (by simp [collectVarsListAux, hv]))
            simp [hHead, hTail]
      exact ⟨hAtom, hList⟩


private theorem apply_eq_of_lookup_eq_on_collectVars_atom
    {a : Atom} {b₁ b₂ : Bindings} {fuel : Nat}
    (hb₁ : GroundBindings b₁)
    (hagree : ∀ v, v ∈ collectVars a fuel → b₂.lookup v = b₁.lookup v) :
    b₂.apply a fuel = b₁.apply a fuel :=
  (apply_eq_of_lookup_eq_on_collectVars fuel).1 hb₁ hagree


/-- If a deterministic no-equalities merge adds only bindings on variable
names absent from a body, then substituting that body is unchanged compared
to substituting with the original ground matcher bindings alone. -/
private theorem apply_eq_of_mergeGround_irrel
    {body : Atom} {mb qb merged : Bindings} {fuel : Nat}
    (hmb : GroundBindings mb)
    (hqbEq : qb.equalities = [])
    (hqbKeys : (qb.assignments.map Prod.fst).Nodup)
    (hmerge : mergeGround? mb qb = some merged)
    (habsent : ∀ v, v ∈ collectVars body fuel → qb.lookup v = none) :
    merged.apply body fuel = mb.apply body fuel := by
  apply apply_eq_of_lookup_eq_on_collectVars_atom hmb
  intro v hv
  have hspec :=
    mergeGround_lookup_spec (left := mb) (right := qb) (out := merged)
      hqbEq hqbKeys hmerge v
  simpa [habsent v hv] using hspec

/-! ## First consumers of the completed matcher bridge -/

/-- On the ground fragment, a successful coarse one-way match from the empty
seed induces the official `unify_match` instruction step with the same
substituted success branch.  This is the matcher-side core theorem later
control-form certifications consume. -/
theorem minimalStep_absorbs_unify_match_ground
    {space : Space} {d : GroundedDispatch}
    {target pattern thenBranch elseBranch : Atom} {mb : Bindings} {fuel : Nat}
    (hground : GroundAtom target)
    (hmatch : simpleMatch pattern target Bindings.empty fuel = some mb) :
    MinimalStep d space
      (.expression [.symbol "unify", target, pattern, thenBranch, elseBranch])
      Bindings.empty space (mb.applyDefault thenBranch, mb) := by
  obtain ⟨fuel0, hmb, hFuel0⟩ := simpleMatch_ground_matchAtoms hground hmatch
  have hmbCanon : GroundBindingsCanon mb := matchAtoms_ground_canon hground hmb
  have hmbGround : GroundBindings mb := hmbCanon.1
  have hnoLoop : mb.hasLoop = false :=
    GroundBindings.hasLoop_false hmbGround
  have hmergeRight : mb ∈ mergeBindings mb Bindings.empty fuel0 := by
    cases fuel0 with
    | zero =>
        omega
    | succ n =>
        rw [mergeBindings_empty_right mb n]
        simp
  exact MinimalStep.unify_match space target pattern thenBranch elseBranch Bindings.empty
    mb mb fuel0 hmb hmergeRight hnoLoop

/-- Ground-fragment no-match absorption for `unify`, on the non-expression
pattern cases.  When coarse one-way matching from the empty seed fails, the
official `unify` instruction takes its `unify_no_match` branch and returns
the else-branch unchanged with empty bindings.  Expression patterns are
excluded here; they need the list-level failure bridge still to come. -/
theorem minimalStep_absorbs_unify_no_match_ground_nonexpr
    {space : Space} {d : GroundedDispatch}
    {target pattern thenBranch elseBranch : Atom} {fuel : Nat}
    (hground : GroundAtom target)
    (h_nonexpr : ¬ ∃ ps, pattern = .expression ps)
    (hmatch : simpleMatch pattern target Bindings.empty fuel = none) :
    MinimalStep d space
      (.expression [.symbol "unify", target, pattern, thenBranch, elseBranch])
      Bindings.empty space (elseBranch, Bindings.empty) := by
  exact MinimalStep.unify_no_match space target pattern thenBranch elseBranch
    Bindings.empty fuel
    (simpleMatch_ground_matchAtoms_nil_nonexpr hground h_nonexpr hmatch)

/-- Ground-fragment no-match absorption for `unify`, with no pattern-shape
restriction: when coarse one-way matching from the empty seed fails, the
official `unify` instruction takes its `unify_no_match` branch at some fuel
and returns the else-branch unchanged with empty bindings. -/
theorem minimalStep_absorbs_unify_no_match_ground
    {space : Space} {d : GroundedDispatch}
    {target pattern thenBranch elseBranch : Atom} {fuel : Nat}
    (hground : GroundAtom target)
    (hmatch : simpleMatch pattern target Bindings.empty fuel = none) :
    MinimalStep d space
      (.expression [.symbol "unify", target, pattern, thenBranch, elseBranch])
      Bindings.empty space (elseBranch, Bindings.empty) := by
  obtain ⟨fuel0, hnil⟩ := simpleMatch_ground_matchAtoms_nil hground hmatch
  exact MinimalStep.unify_no_match space target pattern thenBranch elseBranch
    Bindings.empty fuel0 hnil

/-- **F3, `let` substitution half on the ground fragment.**  The verbatim
upstream rhs of `let`,
`(unify <value> <pattern> <template> Empty)`, takes an official
`unify_match` step whenever the coarse one-way matcher succeeds on a ground
value.  This is the first end-to-end consumer of the completed matcher
bridge. -/
theorem minimalStep_absorbs_let_subst_ground
    {space : Space} {d : GroundedDispatch}
    {pt value body : Atom} {mb : Bindings} {fuel : Nat}
    (hground : GroundAtom value)
    (hmatch : simpleMatch pt value Bindings.empty fuel = some mb) :
    MinimalStep d space (.expression [.symbol "unify", value, pt, body, Atom.empty])
      Bindings.empty space (mb.applyDefault body, mb) :=
  minimalStep_absorbs_unify_match_ground hground hmatch

/-- **F3, `switch-internal` first-branch hit on the ground fragment.**
The verbatim upstream `switch-internal` rhs delegates its head branch to a
`unify`; when the coarse one-way matcher succeeds on a ground scrutinee, that
`unify` takes the official `unify_match` step to the chosen branch's returned
template.  This is the success-half core that the later `HES_SwitchMinimal`
certification will compose through the surrounding recursion. -/
theorem minimalStep_absorbs_switch_internal_head_match_ground
    {space : Space} {d : GroundedDispatch}
    {scrut pt template : Atom} {tail : List Atom} {mb : Bindings} {fuel : Nat}
    (hground : GroundAtom scrut)
    (hmatch : simpleMatch pt scrut Bindings.empty fuel = some mb) :
    MinimalStep d space
      (.expression [.symbol "unify", scrut, pt,
        .expression [.symbol "return", template],
        .expression [.symbol "chain",
          .expression [.symbol "eval",
            .expression [.symbol "switch-minimal", scrut, .expression tail]],
          .var "ret",
          .expression [.symbol "return", .var "ret"]]])
      Bindings.empty space
      (mb.applyDefault (.expression [.symbol "return", template]), mb) :=
  minimalStep_absorbs_unify_match_ground hground hmatch

/-- **F3, `switch-internal` head miss on the ground/non-expression fragment.**
When the head branch's coarse one-way matcher fails from the empty seed, the
official `unify` takes its no-match branch and returns the recursive else
branch unchanged.  This is the first failure-side consumer on the exact
upstream `switch-internal` shape; the expression-pattern case is excluded
until the list-level earlier-branch failure bridge lands. -/
theorem minimalStep_absorbs_switch_internal_head_no_match_ground_nonexpr
    {space : Space} {d : GroundedDispatch}
    {scrut pt template : Atom} {tail : List Atom} {fuel : Nat}
    (hground : GroundAtom scrut)
    (h_nonexpr : ¬ ∃ ps, pt = .expression ps)
    (hmatch : simpleMatch pt scrut Bindings.empty fuel = none) :
    MinimalStep d space
      (.expression [.symbol "unify", scrut, pt,
        .expression [.symbol "return", template],
        .expression [.symbol "chain",
          .expression [.symbol "eval",
            .expression [.symbol "switch-minimal", scrut, .expression tail]],
          .var "ret",
          .expression [.symbol "return", .var "ret"]]])
      Bindings.empty space
      (.expression [.symbol "chain",
        .expression [.symbol "eval",
          .expression [.symbol "switch-minimal", scrut, .expression tail]],
        .var "ret",
        .expression [.symbol "return", .var "ret"]],
        Bindings.empty) :=
  minimalStep_absorbs_unify_no_match_ground_nonexpr hground h_nonexpr hmatch

/-- **F3, `switch-internal` head miss on the full ground fragment.**
When the head branch's coarse one-way matcher fails from the empty seed, the
official `unify` takes its no-match branch and returns the recursive else
branch unchanged.  This packages the completed empty-seed failure bridge in
the exact upstream `switch-internal` shape. -/
theorem minimalStep_absorbs_switch_internal_head_no_match_ground
    {space : Space} {d : GroundedDispatch}
    {scrut pt template : Atom} {tail : List Atom} {fuel : Nat}
    (hground : GroundAtom scrut)
    (hmatch : simpleMatch pt scrut Bindings.empty fuel = none) :
    MinimalStep d space
      (.expression [.symbol "unify", scrut, pt,
        .expression [.symbol "return", template],
        .expression [.symbol "chain",
          .expression [.symbol "eval",
            .expression [.symbol "switch-minimal", scrut, .expression tail]],
          .var "ret",
          .expression [.symbol "return", .var "ret"]]])
      Bindings.empty space
      (.expression [.symbol "chain",
        .expression [.symbol "eval",
          .expression [.symbol "switch-minimal", scrut, .expression tail]],
        .var "ret",
        .expression [.symbol "return", .var "ret"]],
        Bindings.empty) :=
  minimalStep_absorbs_unify_no_match_ground hground hmatch



/-- The verbatim upstream function type annotation for `unify`. -/
private def unifyFunctionType : Atom :=
  .expression [.symbol "->", Atom.atomType, Atom.atomType,
    Atom.atomType, Atom.atomType, Atom.undefinedType]

/-- Source-syntax `unify` atom in the upstream stdlib shape. -/
private def unifyExpr (target pattern thenBranch elseBranch : Atom) : Atom :=
  .expression [.symbol "unify", target, pattern, thenBranch, elseBranch]

/-- The verbatim upstream function type annotation for `let`. -/
private def letFunctionType : Atom :=
  .expression [.symbol "->", Atom.atomType, Atom.undefinedType,
    Atom.atomType, Atom.undefinedType]

/-- Source-syntax `let` atom in the upstream stdlib shape. -/
private def letExpr (pt value body : Atom) : Atom :=
  .expression [.symbol "let", pt, value, body]

/-- The verbatim upstream rhs for `let`: a `unify` over the evaluated value. -/
private def letUnifyRhs (pt value body : Atom) : Atom :=
  .expression [.symbol "unify", value, pt, body, Atom.empty]

/-- If the space presents `let` with exactly its stdlib function type, then
the official type-cast path evaluates the head symbol to itself at that type.

Positive example:
- `(: let (-> Atom %Undefined% Atom %Undefined%))` gives the expected head step.

Negative example:
- without the exact annotation, this theorem does not apply; the typed
  function-path shell is an explicit hypothesis boundary, not folklore. -/
private theorem evalAtom_let_head_typed
    {space : Space} {d : GroundedDispatch} {live : List Atom}
    (h_types : getAtomTypes space (.symbol "let") = [letFunctionType]) :
    EvalAtom space d (live := live) (.symbol "let") letFunctionType Bindings.empty
      (.symbol "let", Bindings.empty) := by
  refine EvalAtom.type_cast _ _ _ _ 10 rfl ?_ (Or.inl rfl) ?_
  · simp [letFunctionType, getMetaType, Atom.atomType,
      Atom.symbolType, Atom.undefinedType, Atom.variableType]
  · rw [typeCast]
    simp only [rawTypeLookup]
    rw [h_types]
    have hmatch : matchAtoms letFunctionType letFunctionType 10 = [Bindings.empty] := by
      decide
    have hmerge : mergeBindings Bindings.empty Bindings.empty 10 = [Bindings.empty] := by
      simpa using mergeBindings_empty_right Bindings.empty 9
    have hflat :
        List.flatMap (fun mb => mergeBindings Bindings.empty mb 10)
          (matchAtoms letFunctionType letFunctionType 10) = [Bindings.empty] := by
      rw [hmatch]
      simp [hmerge]
    have hmt : matchTypes letFunctionType letFunctionType Bindings.empty 10 = [Bindings.empty] := by
      unfold matchTypes
      have hcond :
          (letFunctionType == Atom.undefinedType || letFunctionType == Atom.atomType ||
              letFunctionType == Atom.undefinedType || letFunctionType == Atom.atomType) = false := by
        decide
      simp [hcond, hflat]
    rw [typeCast.typeCastLoop, hmt]
    simp

/-- Seeded companion to `evalAtom_let_head_typed`: the typed `let` head
evaluates to itself under any incoming bindings thread, not just
`Bindings.empty`.  This is the head-side boundary the source-progress half
of `HES_Let` will need once value evaluation has already shifted the
bindings thread. -/
private theorem evalAtom_let_head_typed_seeded
    {space : Space} {d : GroundedDispatch} {live : List Atom} {seed : Bindings}
    (h_types : getAtomTypes space (.symbol "let") = [letFunctionType]) :
    EvalAtom space d (live := live) (.symbol "let") letFunctionType seed
      (.symbol "let", seed) := by
  refine EvalAtom.type_cast _ _ _ _ 10 rfl ?_ (Or.inl rfl) ?_
  · simp [letFunctionType, getMetaType, Atom.atomType,
      Atom.symbolType, Atom.undefinedType, Atom.variableType]
  · rw [typeCast]
    simp only [rawTypeLookup]
    rw [h_types]
    have hmatch : matchAtoms letFunctionType letFunctionType 10 = [Bindings.empty] := by
      decide
    have hmerge : mergeBindings seed Bindings.empty 10 = [seed] := by
      simpa using mergeBindings_empty_right seed 9
    have hflat :
        List.flatMap (fun mb => mergeBindings seed mb 10)
          (matchAtoms letFunctionType letFunctionType 10) = [seed] := by
      rw [hmatch]
      simp [hmerge]
    have hmt : matchTypes letFunctionType letFunctionType seed 10 = [seed] := by
      unfold matchTypes
      have hcond :
          (letFunctionType == Atom.undefinedType || letFunctionType == Atom.atomType ||
              letFunctionType == Atom.undefinedType || letFunctionType == Atom.atomType) = false := by
        decide
      simp [hcond, hflat]
    rw [typeCast.typeCastLoop, hmt]
    simp

/-- Any atom can be evaluated against the expected type `Atom`, producing
itself with unchanged bindings. -/
private theorem evalAtom_atom_type
    {space : Space} {d : GroundedDispatch} {live : List Atom} (a : Atom) (b : Bindings) :
    EvalAtom space d (live := live) a Atom.atomType b (a, b) := by
  by_cases h : isEmptyOrError a = true
  · exact EvalAtom.empty_or_error _ _ _ h
  · exact EvalAtom.type_pass _ _ _ (by simpa using h) (Or.inl rfl)

/-- If the space presents `unify` with exactly its stdlib function type, then
the official type-cast path evaluates the head symbol to itself at that type
under any incoming bindings thread. -/
private theorem evalAtom_unify_head_typed_seeded
    {space : Space} {d : GroundedDispatch} {live : List Atom} {seed : Bindings}
    (h_types : getAtomTypes space (.symbol "unify") = [unifyFunctionType]) :
    EvalAtom space d (live := live) (.symbol "unify") unifyFunctionType seed
      (.symbol "unify", seed) := by
  refine EvalAtom.type_cast _ _ _ _ 10 rfl ?_ (Or.inl rfl) ?_
  · simp [unifyFunctionType, getMetaType, Atom.atomType,
      Atom.symbolType, Atom.undefinedType, Atom.variableType]
  · rw [typeCast]
    simp only [rawTypeLookup]
    rw [h_types]
    have hmatch : matchAtoms unifyFunctionType unifyFunctionType 10 = [Bindings.empty] := by
      decide
    have hmerge : mergeBindings seed Bindings.empty 10 = [seed] := by
      simpa using mergeBindings_empty_right seed 9
    have hflat :
        List.flatMap (fun mb => mergeBindings seed mb 10)
          (matchAtoms unifyFunctionType unifyFunctionType 10) = [seed] := by
      rw [hmatch]
      simp [hmerge]
    have hmt : matchTypes unifyFunctionType unifyFunctionType seed 10 = [seed] := by
      unfold matchTypes
      have hcond :
          (unifyFunctionType == Atom.undefinedType || unifyFunctionType == Atom.atomType ||
              unifyFunctionType == Atom.undefinedType || unifyFunctionType == Atom.atomType) = false := by
        decide
      simp [hcond, hflat]
    rw [typeCast.typeCastLoop, hmt]
    simp

/-- The four `unify` arguments officially interpret to themselves on the
Atom-typed fragment, under an arbitrary incoming bindings thread.  We keep the
bare-`Error` exclusions explicit because the typed function path filters on
error-shaped intermediate tuple shells. -/
private theorem interpretArgs_unify_self_seeded
    {space : Space} {d : GroundedDispatch} {live : List Atom}
    {target pattern thenBranch elseBranch : Atom} {seed : Bindings}
    (_h_pattern_nerr : pattern ≠ Atom.symbol "Error")
    (_h_then_nerr : thenBranch ≠ Atom.symbol "Error")
    (_h_else_nerr : elseBranch ≠ Atom.symbol "Error") :
    InterpretArgs space d (live := live) [target, pattern, thenBranch, elseBranch]
      [Atom.atomType, Atom.atomType, Atom.atomType, Atom.atomType]
      seed
      (argumentPacket [target, pattern, thenBranch, elseBranch], seed) := by
  have h_target {scope : List Atom} : EvalAtom space d (live := scope) target Atom.atomType seed (target, seed) :=
    evalAtom_atom_type target seed
  have h_pattern {scope : List Atom} : EvalAtom space d (live := scope) pattern Atom.atomType seed (pattern, seed) :=
    evalAtom_atom_type pattern seed
  have h_then {scope : List Atom} : EvalAtom space d (live := scope) thenBranch Atom.atomType seed (thenBranch, seed) :=
    evalAtom_atom_type thenBranch seed
  have h_else {scope : List Atom} : EvalAtom space d (live := scope) elseBranch Atom.atomType seed (elseBranch, seed) :=
    evalAtom_atom_type elseBranch seed
  have h_tail_else {scope : List Atom} : InterpretArgs space d (live := scope) [elseBranch] [Atom.atomType]
      seed (argumentPacket [elseBranch], seed) := by
    exact InterpretArgs.cons_ok elseBranch [] Atom.atomType [] seed
      (elseBranch, seed) (argumentPacket [], seed)
      h_else (Or.inr rfl) InterpretArgs.nil rfl
  have h_tail_then {scope : List Atom} : InterpretArgs space d (live := scope) [thenBranch, elseBranch]
      [Atom.atomType, Atom.atomType] seed
      (argumentPacket [thenBranch, elseBranch], seed) := by
    refine InterpretArgs.cons_ok thenBranch [elseBranch] Atom.atomType
      [Atom.atomType] seed
      (thenBranch, seed) (argumentPacket [elseBranch], seed)
      h_then (Or.inr rfl) h_tail_else ?_
    simp
  have h_tail_pattern {scope : List Atom} : InterpretArgs space d (live := scope) [pattern, thenBranch, elseBranch]
      [Atom.atomType, Atom.atomType, Atom.atomType] seed
      (argumentPacket [pattern, thenBranch, elseBranch], seed) := by
    refine InterpretArgs.cons_ok pattern [thenBranch, elseBranch] Atom.atomType
      [Atom.atomType, Atom.atomType] seed
      (pattern, seed) (argumentPacket [thenBranch, elseBranch], seed)
      h_pattern (Or.inr rfl) h_tail_then ?_
    simp
  refine InterpretArgs.cons_ok target [pattern, thenBranch, elseBranch] Atom.atomType
    [Atom.atomType, Atom.atomType, Atom.atomType] seed
    (target, seed) (argumentPacket [pattern, thenBranch, elseBranch], seed)
    h_target (Or.inr rfl) h_tail_pattern ?_
  simp

/-- The official typed function-path shell for the verbatim upstream `unify`
source form on the self-evaluating Atom-typed fragment. -/
private theorem interpretFunction_unify_self_seeded
    {space : Space} {d : GroundedDispatch} {live : List Atom}
    {target pattern thenBranch elseBranch : Atom} {seed : Bindings}
    (h_types : getAtomTypes space (.symbol "unify") = [unifyFunctionType])
    (_h_target_nerr : target ≠ Atom.symbol "Error")
    (h_pattern_nerr : pattern ≠ Atom.symbol "Error")
    (h_then_nerr : thenBranch ≠ Atom.symbol "Error")
    (h_else_nerr : elseBranch ≠ Atom.symbol "Error") :
    InterpretFunction space d (live := live) (unifyExpr target pattern thenBranch elseBranch)
      unifyFunctionType Atom.undefinedType seed
      (unifyExpr target pattern thenBranch elseBranch, seed) := by
  have h_head {scope : List Atom} : EvalAtom space d (live := scope) (.symbol "unify") unifyFunctionType seed
      (.symbol "unify", seed) :=
    evalAtom_unify_head_typed_seeded h_types
  have h_tail {scope : List Atom} : InterpretArgs space d (live := scope) [target, pattern, thenBranch, elseBranch]
      [Atom.atomType, Atom.atomType, Atom.atomType, Atom.atomType]
      seed
      (argumentPacket [target, pattern, thenBranch, elseBranch], seed) :=
    interpretArgs_unify_self_seeded
      h_pattern_nerr h_then_nerr h_else_nerr
  refine InterpretFunction.head_ok_tail_ok
    (unifyExpr target pattern thenBranch elseBranch)
    unifyFunctionType Atom.undefinedType seed
    (.symbol "unify") [target, pattern, thenBranch, elseBranch]
    [Atom.atomType, Atom.atomType, Atom.atomType, Atom.atomType]
    (.symbol "unify", seed)
    (argumentPacket [target, pattern, thenBranch, elseBranch], seed)
    rfl rfl h_head rfl h_tail ?_
  simp

/-- Outer official `unify` shell, relative to the explicit typed-function path
and a supplied official `MettaCall` witness for the raw branch result. -/
private theorem evalAtom_absorbs_unify_shell_of_interp
    {space : Space} {d : GroundedDispatch}
    {target pattern thenBranch elseBranch : Atom} {seed : Bindings}
    {interpResult final : ResultPair}
    {succs : List Bindings} {fuel : Nat}
    (h_op_type : unifyFunctionType ∈ getAtomTypes space (.symbol "unify"))
    (h_check : checkIfFunctionTypeIsApplicable
      (unifyExpr target pattern thenBranch elseBranch)
      unifyFunctionType Atom.undefinedType
      space seed fuel = .inr succs)
    (h_check_b : seed ∈ succs)
    (h_interp : InterpretFunction space d (live := [Atom.undefinedType])
      (unifyExpr target pattern thenBranch elseBranch)
      unifyFunctionType Atom.undefinedType seed interpResult)
    (h_call : MettaCall space d interpResult.1
      Atom.undefinedType interpResult.2 final) :
    EvalAtom space d (unifyExpr target pattern thenBranch elseBranch)
      Atom.undefinedType seed final := by
  have h_unify_nerr : (.symbol "unify") ≠ Atom.symbol "Error" := by
    simp
  by_cases h_final_err : isErrorAtom final.1 = true
  · refine EvalAtom.interpret_error _ _ _ _ ?_ ?_ rfl ?_ ?_ h_final_err
    · exact isEmptyOrError_expr_false
        (pattern :: thenBranch :: [elseBranch]) h_unify_nerr
    · simp [unifyExpr, getMetaType, Atom.undefinedType, Atom.atomType,
        Atom.expressionType, Atom.variableType]
    · intro h_unit
      simp [unifyExpr, Atom.unit] at h_unit
    · refine InterpretExpression.function_path _ _ _
        (.symbol "unify") [target, pattern, thenBranch, elseBranch]
        unifyFunctionType Atom.undefinedType seed
        interpResult final fuel
        rfl h_op_type ?_ succs h_check h_check_b rfl h_interp h_call
      rfl
  · refine EvalAtom.interpret_success _ _ _ _ ?_ ?_ rfl ?_ ?_ ?_
    · exact isEmptyOrError_expr_false
        (pattern :: thenBranch :: [elseBranch]) h_unify_nerr
    · simp [unifyExpr, getMetaType, Atom.undefinedType, Atom.atomType,
        Atom.expressionType, Atom.variableType]
    · intro h_unit
      simp [unifyExpr, Atom.unit] at h_unit
    · refine InterpretExpression.function_path _ _ _
        (.symbol "unify") [target, pattern, thenBranch, elseBranch]
        unifyFunctionType Atom.undefinedType seed
        interpResult final fuel
        rfl h_op_type ?_ succs h_check h_check_b rfl h_interp h_call
      rfl
    · simpa using h_final_err

/-- Typed official evaluator form of the primitive `unify` success branch,
under the exact stdlib `unify` annotation and the self-evaluating Atom-typed
argument shell. The merge premise is the operation's actual alias-exposed
incoming record. -/
theorem evalAtom_realizes_unify_match_ground_seeded_typed
    {space : Space} {d : GroundedDispatch}
    {seed mb merged : Bindings}
    {target pattern thenBranch elseBranch : Atom} {fuel : Nat}
    {succs : List Bindings} {fuelShell : Nat}
    (h_types : getAtomTypes space (.symbol "unify") = [unifyFunctionType])
    (h_target_nerr : target ≠ Atom.symbol "Error")
    (h_pattern_nerr : pattern ≠ Atom.symbol "Error")
    (h_then_nerr : thenBranch ≠ Atom.symbol "Error")
    (h_else_nerr : elseBranch ≠ Atom.symbol "Error")
    (h_check : checkIfFunctionTypeIsApplicable
      (unifyExpr target pattern thenBranch elseBranch)
      unifyFunctionType Atom.undefinedType
      space seed fuelShell = .inr succs)
    (h_check_b : seed ∈ succs)
    (hmatch : mb ∈ matchAtoms target pattern fuel)
    (hmerge : merged ∈ mergeBindings mb
      (Spec.Type.Presentation.BindingTheory.aliasConstraints seed) fuel)
    (h_no_loop : merged.hasLoop = false) :
    EvalAtom space d
      (unifyExpr target pattern thenBranch elseBranch)
      Atom.undefinedType seed
      (merged.applyFull thenBranch (merged.resolutionFuel thenBranch), merged) := by
  have h_interp : InterpretFunction space d (live := [Atom.undefinedType])
      (unifyExpr target pattern thenBranch elseBranch)
      unifyFunctionType Atom.undefinedType seed
      (unifyExpr target pattern thenBranch elseBranch, seed) :=
    interpretFunction_unify_self_seeded h_types
      h_target_nerr h_pattern_nerr h_then_nerr h_else_nerr
  have h_raw :
      (merged.applyFull thenBranch (merged.resolutionFuel thenBranch), merged) ∈
        unifySuccessResults target pattern thenBranch seed fuel := by
    refine List.mem_flatMap.mpr ?_
    refine ⟨mb, hmatch, ?_⟩
    exact List.mem_filterMap.mpr ⟨merged, hmerge, by simp [h_no_loop]⟩
  have h_call : MettaCall space d
      (unifyExpr target pattern thenBranch elseBranch)
      Atom.undefinedType seed
      (merged.applyFull thenBranch (merged.resolutionFuel thenBranch), merged) :=
    MettaCall.unify_success_raw
      (unifyExpr target pattern thenBranch elseBranch)
      Atom.undefinedType seed
      target pattern thenBranch elseBranch
      (merged.applyFull thenBranch (merged.resolutionFuel thenBranch), merged) fuel
      rfl (by simp [unifyExpr, isErrorAtom]) h_raw
  have h_op_type : unifyFunctionType ∈ getAtomTypes space (.symbol "unify") := by
    rw [h_types]
    simp
  exact evalAtom_absorbs_unify_shell_of_interp
    h_op_type h_check h_check_b h_interp h_call

/-- Historical typed judgment for the primitive `unify` no-match branch,
under the exact stdlib `unify` annotation and the self-evaluating Atom-typed
argument shell. -/
theorem evalAtom_realizes_unify_no_match_ground_seeded_typed
    {space : Space} {d : GroundedDispatch}
    {seed : Bindings}
    {target pattern thenBranch elseBranch : Atom} {fuel : Nat}
    {succs : List Bindings} {fuelShell : Nat}
    (h_types : getAtomTypes space (.symbol "unify") = [unifyFunctionType])
    (h_target_nerr : target ≠ Atom.symbol "Error")
    (h_pattern_nerr : pattern ≠ Atom.symbol "Error")
    (h_then_nerr : thenBranch ≠ Atom.symbol "Error")
    (h_else_nerr : elseBranch ≠ Atom.symbol "Error")
    (h_check : checkIfFunctionTypeIsApplicable
      (unifyExpr target pattern thenBranch elseBranch)
      unifyFunctionType Atom.undefinedType
      space seed fuelShell = .inr succs)
    (h_check_b : seed ∈ succs)
    (hmatch : matchAtoms target pattern fuel = []) :
    EvalAtom space d
      (unifyExpr target pattern thenBranch elseBranch)
      Atom.undefinedType seed
      (elseBranch, seed) := by
  have h_interp : InterpretFunction space d (live := [Atom.undefinedType])
      (unifyExpr target pattern thenBranch elseBranch)
      unifyFunctionType Atom.undefinedType seed
      (unifyExpr target pattern thenBranch elseBranch, seed) :=
    interpretFunction_unify_self_seeded h_types
      h_target_nerr h_pattern_nerr h_then_nerr h_else_nerr
  have h_call : MettaCall space d
      (unifyExpr target pattern thenBranch elseBranch)
      Atom.undefinedType seed
      (elseBranch, seed) := by
    have h_empty : unifySuccessResults target pattern thenBranch seed fuel = [] := by
      simp [unifySuccessResults, hmatch]
    exact MettaCall.unify_no_match_raw
      (unifyExpr target pattern thenBranch elseBranch)
      Atom.undefinedType seed
      target pattern thenBranch elseBranch fuel
      rfl (by simp [unifyExpr, isErrorAtom]) h_empty
  have h_op_type : unifyFunctionType ∈ getAtomTypes space (.symbol "unify") := by
    rw [h_types]
    simp
  exact evalAtom_absorbs_unify_shell_of_interp
    h_op_type h_check h_check_b h_interp h_call

/-- Typed specialisation for `let`'s raw `unify` rhs under the exact stdlib
`unify` annotation.  This removes the abstract evaluator boundary from the
historical `let` constructor proof while keeping the head/argument shell explicit. -/
theorem evalAtom_realizes_let_subst_ground_seeded_typed
    {space : Space} {d : GroundedDispatch}
    {seed mb merged : Bindings}
    {pt value body : Atom} {fuel : Nat}
    {succs : List Bindings} {fuelShell : Nat}
    (h_types : getAtomTypes space (.symbol "unify") = [unifyFunctionType])
    (h_value_nerr : value ≠ Atom.symbol "Error")
    (h_pt_nerr : pt ≠ Atom.symbol "Error")
    (h_body_nerr : body ≠ Atom.symbol "Error")
    (_hground : GroundAtom value)
    (h_check : checkIfFunctionTypeIsApplicable
      (unifyExpr value pt body Atom.empty)
      unifyFunctionType Atom.undefinedType
      space seed fuelShell = .inr succs)
    (h_check_b : seed ∈ succs)
    (hmatch : mb ∈ matchAtoms value pt fuel)
    (hmerge : merged ∈ mergeBindings mb
      (Spec.Type.Presentation.BindingTheory.aliasConstraints seed) fuel)
    (h_no_loop : merged.hasLoop = false) :
    EvalAtom space d
      (.expression [.symbol "unify", value, pt, body, Atom.empty])
      Atom.undefinedType seed
      (merged.applyFull body (merged.resolutionFuel body), merged) := by
  have h_empty_nerr : Atom.empty ≠ Atom.symbol "Error" := by
    decide
  simpa [unifyExpr] using
    evalAtom_realizes_unify_match_ground_seeded_typed
      (space := space) (d := d) (seed := seed) (mb := mb) (merged := merged)
      (target := value) (pattern := pt) (thenBranch := body) (elseBranch := Atom.empty)
      (fuel := fuel) (succs := succs) (fuelShell := fuelShell)
      h_types h_value_nerr h_pt_nerr h_body_nerr h_empty_nerr
      h_check h_check_b hmatch hmerge h_no_loop

/-- The three `let` arguments officially interpret to themselves on the
fragment needed by the sugar proof: pattern/body are merely required not to be
the bare `Error` symbol, while the value uses the proven quiescent
self-evaluation theorem. -/
private theorem interpretArgs_let_self
    {space : Space} {d : GroundedDispatch} {live : List Atom} {fuel : Nat}
    {pt value body : Atom}
    (_h_value_nerr : value ≠ Atom.symbol "Error")
    (_h_body_nerr : body ≠ Atom.symbol "Error")
    (h_value_q : SelfEvalQuiescent space d fuel value) :
    InterpretArgs space d (live := live) [pt, value, body]
      [Atom.atomType, Atom.undefinedType, Atom.atomType]
      Bindings.empty
      (argumentPacket [pt, value, body], Bindings.empty) := by
  have h_pt {scope : List Atom} : EvalAtom space d (live := scope) pt Atom.atomType Bindings.empty
      (pt, Bindings.empty) :=
    evalAtom_atom_type pt Bindings.empty
  have h_value {scope : List Atom} : EvalAtom space d (live := scope) value Atom.undefinedType Bindings.empty
      (value, Bindings.empty) :=
    selfEval_of_quiescent value h_value_q Bindings.empty
  have h_body {scope : List Atom} : EvalAtom space d (live := scope) body Atom.atomType Bindings.empty
      (body, Bindings.empty) :=
    evalAtom_atom_type body Bindings.empty
  have h_tail_body {scope : List Atom} : InterpretArgs space d (live := scope) [body] [Atom.atomType]
      Bindings.empty (argumentPacket [body], Bindings.empty) := by
    exact InterpretArgs.cons_ok body [] Atom.atomType [] Bindings.empty
      (body, Bindings.empty) (argumentPacket [], Bindings.empty)
      h_body (Or.inr rfl) InterpretArgs.nil rfl
  have h_tail_value {scope : List Atom} : InterpretArgs space d (live := scope) [value, body]
      [Atom.undefinedType, Atom.atomType] Bindings.empty
      (argumentPacket [value, body], Bindings.empty) := by
    refine InterpretArgs.cons_ok value [body] Atom.undefinedType
      [Atom.atomType] Bindings.empty
      (value, Bindings.empty) (argumentPacket [body], Bindings.empty)
      h_value (Or.inr rfl) h_tail_body ?_
    simp
  refine InterpretArgs.cons_ok pt [value, body] Atom.atomType
    [Atom.undefinedType, Atom.atomType] Bindings.empty
    (pt, Bindings.empty) (argumentPacket [value, body], Bindings.empty)
    h_pt (Or.inr rfl) h_tail_value ?_
  simp

/-- Seeded companion to `interpretArgs_let_self`: the three `let` arguments
interpret to themselves under an arbitrary incoming bindings thread when the
value is in the quiescent self-evaluation fragment. -/
private theorem interpretArgs_let_self_seeded
    {space : Space} {d : GroundedDispatch} {live : List Atom} {fuel : Nat}
    {pt value body : Atom} {seed : Bindings}
    (_h_value_nerr : value ≠ Atom.symbol "Error")
    (_h_body_nerr : body ≠ Atom.symbol "Error")
    (h_value_q : SelfEvalQuiescent space d fuel value) :
    InterpretArgs space d (live := live) [pt, value, body]
      [Atom.atomType, Atom.undefinedType, Atom.atomType]
      seed
      (argumentPacket [pt, value, body], seed) := by
  have h_pt {scope : List Atom} : EvalAtom space d (live := scope) pt Atom.atomType seed (pt, seed) :=
    evalAtom_atom_type pt seed
  have h_value {scope : List Atom} : EvalAtom space d (live := scope) value Atom.undefinedType seed
      (value, seed) :=
    selfEval_of_quiescent value h_value_q seed
  have h_body {scope : List Atom} : EvalAtom space d (live := scope) body Atom.atomType seed
      (body, seed) :=
    evalAtom_atom_type body seed
  have h_tail_body {scope : List Atom} : InterpretArgs space d (live := scope) [body] [Atom.atomType]
      seed (argumentPacket [body], seed) := by
    exact InterpretArgs.cons_ok body [] Atom.atomType [] seed
      (body, seed) (argumentPacket [], seed)
      h_body (Or.inr rfl) InterpretArgs.nil rfl
  have h_tail_value {scope : List Atom} : InterpretArgs space d (live := scope) [value, body]
      [Atom.undefinedType, Atom.atomType] seed
      (argumentPacket [value, body], seed) := by
    refine InterpretArgs.cons_ok value [body] Atom.undefinedType
      [Atom.atomType] seed
      (value, seed) (argumentPacket [body], seed)
      h_value (Or.inr rfl) h_tail_body ?_
    simp
  refine InterpretArgs.cons_ok pt [value, body] Atom.atomType
    [Atom.undefinedType, Atom.atomType] seed
    (pt, seed) (argumentPacket [value, body], seed)
    h_pt (Or.inr rfl) h_tail_value ?_
  simp

/-- The official typed function-path shell for the verbatim upstream `let`
source form on the certified fragment.  This is the outer function wrapper
that the later `HES_Let` theorem will spend before taking the equation-match
step into the `unify` rhs. -/
theorem interpretFunction_let_self
    {space : Space} {d : GroundedDispatch} {live : List Atom} {fuel : Nat}
    {pt value body : Atom}
    (h_types : getAtomTypes space (.symbol "let") = [letFunctionType])
    (_h_pt_nerr : pt ≠ Atom.symbol "Error")
    (h_value_nerr : value ≠ Atom.symbol "Error")
    (h_body_nerr : body ≠ Atom.symbol "Error")
    (h_value_q : SelfEvalQuiescent space d fuel value) :
    InterpretFunction space d (live := live) (letExpr pt value body)
      letFunctionType Atom.undefinedType Bindings.empty
      (letExpr pt value body, Bindings.empty) := by
  have h_head {scope : List Atom} : EvalAtom space d (live := scope) (.symbol "let") letFunctionType Bindings.empty
      (.symbol "let", Bindings.empty) :=
    evalAtom_let_head_typed h_types
  have h_tail {scope : List Atom} : InterpretArgs space d (live := scope) [pt, value, body]
      [Atom.atomType, Atom.undefinedType, Atom.atomType]
      Bindings.empty
      (argumentPacket [pt, value, body], Bindings.empty) :=
    interpretArgs_let_self h_value_nerr h_body_nerr h_value_q
  refine InterpretFunction.head_ok_tail_ok
    (letExpr pt value body) letFunctionType Atom.undefinedType Bindings.empty
    (.symbol "let") [pt, value, body]
    [Atom.atomType, Atom.undefinedType, Atom.atomType]
    (.symbol "let", Bindings.empty)
    (argumentPacket [pt, value, body], Bindings.empty)
    rfl rfl h_head rfl h_tail ?_
  simp

/-- Seeded typed function-path shell for the verbatim upstream `let` syntax
form.  This is the incoming-bindings companion to `interpretFunction_let_self`
that the source-progress side of `HES_Let` will need after the value
evaluation has already produced a non-empty bindings thread. -/
theorem interpretFunction_let_self_seeded
    {space : Space} {d : GroundedDispatch} {live : List Atom} {fuel : Nat}
    {pt value body : Atom} {seed : Bindings}
    (h_types : getAtomTypes space (.symbol "let") = [letFunctionType])
    (_h_pt_nerr : pt ≠ Atom.symbol "Error")
    (h_value_nerr : value ≠ Atom.symbol "Error")
    (h_body_nerr : body ≠ Atom.symbol "Error")
    (h_value_q : SelfEvalQuiescent space d fuel value) :
    InterpretFunction space d (live := live) (letExpr pt value body)
      letFunctionType Atom.undefinedType seed
      (letExpr pt value body, seed) := by
  have h_head {scope : List Atom} : EvalAtom space d (live := scope) (.symbol "let") letFunctionType seed
      (.symbol "let", seed) :=
    evalAtom_let_head_typed_seeded h_types
  have h_tail {scope : List Atom} : InterpretArgs space d (live := scope) [pt, value, body]
      [Atom.atomType, Atom.undefinedType, Atom.atomType]
      seed
      (argumentPacket [pt, value, body], seed) :=
    interpretArgs_let_self_seeded h_value_nerr h_body_nerr h_value_q
  refine InterpretFunction.head_ok_tail_ok
    (letExpr pt value body) letFunctionType Atom.undefinedType seed
    (.symbol "let") [pt, value, body]
    [Atom.atomType, Atom.undefinedType, Atom.atomType]
    (.symbol "let", seed)
    (argumentPacket [pt, value, body], seed)
    rfl rfl h_head rfl h_tail ?_
  simp

/-- Source-progress companion to the quiescent `let` shell: if the bound
value has already been officially evaluated to a non-empty/non-error atom,
then the `let` function path rebuilds around that evaluated value and threads
its bindings forward into the body position. -/
private theorem interpretFunction_let_of_value_eval_ok
    {space : Space} {d : GroundedDispatch} {live : List Atom}
    {pt value body : Atom} {valueResult : ResultPair}
    (h_types : getAtomTypes space (.symbol "let") = [letFunctionType])
    (_h_pt_nerr : pt ≠ Atom.symbol "Error")
    (_h_value_nerr : valueResult.1 ≠ Atom.symbol "Error")
    (_h_body_nerr : body ≠ Atom.symbol "Error")
    (h_value : EvalAtom space d (live := [body, Atom.atomType, pt, .symbol "let"] ++ live) value Atom.undefinedType Bindings.empty valueResult)
    (h_value_ok : isEmptyOrError valueResult.1 = false) :
    InterpretFunction space d (live := live) (letExpr pt value body)
      letFunctionType Atom.undefinedType Bindings.empty
      (letExpr pt valueResult.1 body, valueResult.2) := by
  have h_head {scope : List Atom} : EvalAtom space d (live := scope) (.symbol "let") letFunctionType Bindings.empty
      (.symbol "let", Bindings.empty) :=
    evalAtom_let_head_typed h_types
  have h_pt {scope : List Atom} : EvalAtom space d (live := scope) pt Atom.atomType Bindings.empty
      (pt, Bindings.empty) :=
    evalAtom_atom_type pt Bindings.empty
  have h_body {scope : List Atom} : EvalAtom space d (live := scope) body Atom.atomType valueResult.2
      (body, valueResult.2) :=
    evalAtom_atom_type body valueResult.2
  have h_tail_body {scope : List Atom} : InterpretArgs space d (live := scope) [body] [Atom.atomType]
      valueResult.2 (argumentPacket [body], valueResult.2) := by
    exact InterpretArgs.cons_ok body [] Atom.atomType [] valueResult.2
      (body, valueResult.2) (argumentPacket [], valueResult.2)
      h_body (Or.inr rfl) InterpretArgs.nil rfl
  have h_tail_value : InterpretArgs space d (live := pt :: .symbol "let" :: live) [value, body]
      [Atom.undefinedType, Atom.atomType] Bindings.empty
      (argumentPacket [valueResult.1, body], valueResult.2) := by
    refine InterpretArgs.cons_ok value [body] Atom.undefinedType
      [Atom.atomType] Bindings.empty
      valueResult (argumentPacket [body], valueResult.2)
      h_value (Or.inl h_value_ok) h_tail_body ?_
    simp
  refine InterpretFunction.head_ok_tail_ok
    (letExpr pt value body) letFunctionType Atom.undefinedType Bindings.empty
    (.symbol "let") [pt, value, body]
    [Atom.atomType, Atom.undefinedType, Atom.atomType]
    (.symbol "let", Bindings.empty)
    (argumentPacket [pt, valueResult.1, body], valueResult.2)
    rfl rfl h_head rfl ?_ ?_
  · refine InterpretArgs.cons_ok pt [value, body] Atom.atomType
      [Atom.undefinedType, Atom.atomType] Bindings.empty
      (pt, Bindings.empty) (argumentPacket [valueResult.1, body], valueResult.2)
      h_pt (Or.inr rfl) h_tail_value ?_
    simp
  · simp

/-- Error/Empty propagation companion to the quiescent `let` shell: if the
bound value already officially evaluates to a changed Empty/Error result, the
`let` function path propagates that result immediately without touching the
body. -/
private theorem interpretFunction_let_of_value_eval_bad
    {space : Space} {d : GroundedDispatch} {live : List Atom}
    {pt value body : Atom} {valueResult : ResultPair}
    (h_types : getAtomTypes space (.symbol "let") = [letFunctionType])
    (h_value : EvalAtom space d (live := [body, Atom.atomType, pt, .symbol "let"] ++ live) value Atom.undefinedType Bindings.empty valueResult)
    (h_value_bad : isEmptyOrError valueResult.1 = true)
    (h_changed : valueResult.1 ≠ value) :
    InterpretFunction space d (live := live) (letExpr pt value body)
      letFunctionType Atom.undefinedType Bindings.empty
      valueResult := by
  have h_head {scope : List Atom} : EvalAtom space d (live := scope) (.symbol "let") letFunctionType Bindings.empty
      (.symbol "let", Bindings.empty) :=
    evalAtom_let_head_typed h_types
  have h_pt {scope : List Atom} : EvalAtom space d (live := scope) pt Atom.atomType Bindings.empty
      (pt, Bindings.empty) :=
    evalAtom_atom_type pt Bindings.empty
  have h_tail_value : InterpretArgs space d (live := pt :: .symbol "let" :: live) [value, body]
      [Atom.undefinedType, Atom.atomType] Bindings.empty valueResult := by
    exact InterpretArgs.head_changed_error value [body]
      Atom.undefinedType [Atom.atomType] Bindings.empty valueResult
      h_value h_value_bad h_changed
  refine InterpretFunction.head_ok_tail_error
    (letExpr pt value body) letFunctionType Atom.undefinedType Bindings.empty
    (.symbol "let") [pt, value, body]
    [Atom.atomType, Atom.undefinedType, Atom.atomType]
    (.symbol "let", Bindings.empty) valueResult
    rfl rfl h_head rfl ?_ (argumentsSucceeded_false_of_error h_value_bad)
  exact InterpretArgs.cons_tail_error pt [value, body]
    Atom.atomType [Atom.undefinedType, Atom.atomType]
    Bindings.empty
    (pt, Bindings.empty) valueResult
    h_pt (Or.inr rfl) h_tail_value (argumentsSucceeded_false_of_error h_value_bad)

/-- Generic equation-call wrapper for the verbatim upstream `let` syntax
form. The raw matched rhs crosses the ordinary call-return boundary before
it is composed into `MettaCall`; the protocol reply restores this source call. -/
theorem mettaCall_absorbs_let_equation
    {space : Space} {d : GroundedDispatch}
    {pt value body rhs : Atom} {qb merged : Bindings}
    {final : ResultPair} {fuel : Nat}
    (h_not_exec : d.isExecutable (.symbol "let") = false)
    {avoid : List String}
    (h_cover : CoversEvaluation avoid [] (letExpr pt value body) Atom.undefinedType Bindings.empty)
    (h_query : (rhs, qb) ∈ queryEquationsAvoiding avoid space
      (letExpr pt value body) fuel)
    (h_merge : merged ∈ mergeBindings qb Bindings.empty fuel)
    (h_no_loop : merged.hasLoop = false)
    (h_return : OrdinaryCallReturnRel space d (letExpr pt value body)
      (merged.applyFull rhs fuel) Atom.undefinedType merged final) :
    MettaCall space d (letExpr pt value body) Atom.undefinedType
      Bindings.empty final :=
  MettaCall.equation_match _ _ _ rhs qb merged final fuel
    (by simp [letExpr, isErrorAtom])
    (by
      refine ⟨?_, ?_⟩
      · simpa [letExpr] using h_not_exec
      · simp)
    h_cover h_query h_merge h_no_loop h_return

/-- Seeded equation-call wrapper for the verbatim upstream `let` syntax
form.  Once the typed function-path shell has already threaded some incoming
bindings through the value evaluation, the same equation-match packaging
still applies at that seed. -/
theorem mettaCall_absorbs_let_equation_seeded
    {space : Space} {d : GroundedDispatch}
    {pt value body rhs : Atom} {seed qb merged : Bindings}
    {final : ResultPair} {fuel : Nat}
    (h_not_exec : d.isExecutable (.symbol "let") = false)
    {avoid : List String}
    (h_cover : CoversEvaluation avoid [] (letExpr pt value body) Atom.undefinedType seed)
    (h_query : (rhs, qb) ∈ queryEquationsAvoiding avoid space
      (letExpr pt value body) fuel)
    (h_merge : merged ∈ mergeBindings qb seed fuel)
    (h_no_loop : merged.hasLoop = false)
    (h_return : OrdinaryCallReturnRel space d (letExpr pt value body)
      (merged.applyFull rhs fuel) Atom.undefinedType merged final) :
    MettaCall space d (letExpr pt value body) Atom.undefinedType
      seed final :=
  MettaCall.equation_match _ _ _ rhs qb merged final fuel
    (by simp [letExpr, isErrorAtom])
    (by
      refine ⟨?_, ?_⟩
      · simpa [letExpr] using h_not_exec
      · simp)
    h_cover h_query h_merge h_no_loop h_return

/-- Generic outer official `let` shell, parameterized by the actual
`InterpretFunction` result.  This is the right theorem boundary for the
source-progress half: once the `let` function path has been derived honestly,
the remaining official `EvalAtom` judgment is just the usual function-path +
`MettaCall` composition. -/
theorem evalAtom_absorbs_let_shell_of_interp
    {space : Space} {d : GroundedDispatch}
    {pt value body : Atom} {seed : Bindings}
    {interpResult final : ResultPair}
    {succs : List Bindings} {fuel : Nat}
    (h_op_type : letFunctionType ∈ getAtomTypes space (.symbol "let"))
    (h_check : checkIfFunctionTypeIsApplicable
      (letExpr pt value body) letFunctionType Atom.undefinedType
      space seed fuel = .inr succs)
    (h_check_b : seed ∈ succs)
    (h_interp : InterpretFunction space d (live := [Atom.undefinedType]) (letExpr pt value body)
      letFunctionType Atom.undefinedType seed interpResult)
    (h_call : MettaCall space d interpResult.1
      Atom.undefinedType interpResult.2 final) :
    EvalAtom space d (letExpr pt value body)
      Atom.undefinedType seed final := by
  by_cases h_final_err : isErrorAtom final.1 = true
  · refine EvalAtom.interpret_error _ _ _ _ ?_ ?_ rfl ?_ ?_ h_final_err
    · exact isEmptyOrError_expr_false [pt, value, body] (by simp)
    · simp [letExpr, getMetaType, Atom.undefinedType, Atom.atomType,
        Atom.expressionType, Atom.variableType]
    · intro h_unit
      simp [letExpr, Atom.unit] at h_unit
    · refine InterpretExpression.function_path _ _ _
        (.symbol "let") [pt, value, body]
        letFunctionType Atom.undefinedType seed
        interpResult final fuel
        rfl h_op_type ?_ succs h_check h_check_b rfl h_interp h_call
      rfl
  · refine EvalAtom.interpret_success _ _ _ _ ?_ ?_ rfl ?_ ?_ ?_
    · exact isEmptyOrError_expr_false [pt, value, body] (by simp)
    · simp [letExpr, getMetaType, Atom.undefinedType, Atom.atomType,
        Atom.expressionType, Atom.variableType]
    · intro h_unit
      simp [letExpr, Atom.unit] at h_unit
    · refine InterpretExpression.function_path _ _ _
        (.symbol "let") [pt, value, body]
        letFunctionType Atom.undefinedType seed
        interpResult final fuel
        rfl h_op_type ?_ succs h_check h_check_b rfl h_interp h_call
      rfl
    · simpa using h_final_err

/-- The outer official `let` shell, relative to the explicit typed-function
path and equation-match hypotheses.  This theorem packages the exact remaining
boundary around the already-proven `unify` core: once the source `let`
function path and its equation-call are supplied, the full official
`EvalAtom` judgment follows. -/
theorem evalAtom_absorbs_let_shell
    {space : Space} {d : GroundedDispatch}
    {pt value body : Atom} {final : ResultPair}
    {succs : List Bindings} {fuel : Nat}
    (h_op_type : letFunctionType ∈ getAtomTypes space (.symbol "let"))
    (h_check : checkIfFunctionTypeIsApplicable
      (letExpr pt value body) letFunctionType Atom.undefinedType
      space Bindings.empty fuel = .inr succs)
    (h_check_b : Bindings.empty ∈ succs)
    (h_interp : InterpretFunction space d (live := [Atom.undefinedType]) (letExpr pt value body)
      letFunctionType Atom.undefinedType Bindings.empty
      (letExpr pt value body, Bindings.empty))
    (h_call : MettaCall space d (letExpr pt value body)
      Atom.undefinedType Bindings.empty final)
    (h_final_ok : isErrorAtom final.1 = false) :
    EvalAtom space d (letExpr pt value body)
      Atom.undefinedType Bindings.empty final := by
  refine EvalAtom.interpret_success _ _ _ _ ?_ ?_ rfl ?_ ?_ h_final_ok
  · exact isEmptyOrError_expr_false [pt, value, body] (by simp)
  · simp [letExpr, getMetaType, Atom.undefinedType, Atom.atomType,
      Atom.expressionType, Atom.variableType]
  · intro h_unit
    simp [letExpr, Atom.unit] at h_unit
  · refine InterpretExpression.function_path _ _ _
      (.symbol "let") [pt, value, body]
      letFunctionType Atom.undefinedType Bindings.empty
      (letExpr pt value body, Bindings.empty) final fuel
      rfl h_op_type ?_ succs h_check h_check_b rfl h_interp h_call
    rfl

/-- Error-side companion to `evalAtom_absorbs_let_shell`: when the outer
typed-function path and equation-call are supplied and the final result is
error-shaped, the full official `EvalAtom` judgment follows on the error
branch rather than the success branch. -/
theorem evalAtom_absorbs_let_shell_error
    {space : Space} {d : GroundedDispatch}
    {pt value body : Atom} {final : ResultPair}
    {succs : List Bindings} {fuel : Nat}
    (h_op_type : letFunctionType ∈ getAtomTypes space (.symbol "let"))
    (h_check : checkIfFunctionTypeIsApplicable
      (letExpr pt value body) letFunctionType Atom.undefinedType
      space Bindings.empty fuel = .inr succs)
    (h_check_b : Bindings.empty ∈ succs)
    (h_interp : InterpretFunction space d (live := [Atom.undefinedType]) (letExpr pt value body)
      letFunctionType Atom.undefinedType Bindings.empty
      (letExpr pt value body, Bindings.empty))
    (h_call : MettaCall space d (letExpr pt value body)
      Atom.undefinedType Bindings.empty final)
    (h_final_err : isErrorAtom final.1 = true) :
    EvalAtom space d (letExpr pt value body)
      Atom.undefinedType Bindings.empty final := by
  refine EvalAtom.interpret_error _ _ _ _ ?_ ?_ rfl ?_ ?_ h_final_err
  · exact isEmptyOrError_expr_false [pt, value, body] (by simp)
  · simp [letExpr, getMetaType, Atom.undefinedType, Atom.atomType,
      Atom.expressionType, Atom.variableType]
  · intro h_unit
    simp [letExpr, Atom.unit] at h_unit
  · refine InterpretExpression.function_path _ _ _
      (.symbol "let") [pt, value, body]
      letFunctionType Atom.undefinedType Bindings.empty
      (letExpr pt value body, Bindings.empty) final fuel
      rfl h_op_type ?_ succs h_check h_check_b rfl h_interp h_call
    rfl

/-- Source-progress shell for `let` on the non-empty/non-error value-result
fragment.  Once the bound value has an official evaluation result and the
continuation `let` form at that result is officially callable, the whole
original `let` expression officially evaluates to the same final result. -/
theorem evalAtom_absorbs_let_value_eval_ok
    {space : Space} {d : GroundedDispatch}
    {pt value body valueAtom : Atom} {valueBindings : Bindings}
    {final : ResultPair}
    {succs : List Bindings} {fuel : Nat}
    (h_types : getAtomTypes space (.symbol "let") = [letFunctionType])
    (h_check : checkIfFunctionTypeIsApplicable
      (letExpr pt value body) letFunctionType Atom.undefinedType
      space Bindings.empty fuel = .inr succs)
    (h_check_b : Bindings.empty ∈ succs)
    (h_pt_nerr : pt ≠ Atom.symbol "Error")
    (h_value_nerr : valueAtom ≠ Atom.symbol "Error")
    (h_body_nerr : body ≠ Atom.symbol "Error")
    (h_value : EvalAtom space d (live := [body, Atom.atomType, pt, .symbol "let", Atom.undefinedType]) value Atom.undefinedType Bindings.empty
      (valueAtom, valueBindings))
    (h_value_ok : isEmptyOrError valueAtom = false)
    (h_call : MettaCall space d (letExpr pt valueAtom body)
      Atom.undefinedType valueBindings final) :
    EvalAtom space d (letExpr pt value body)
      Atom.undefinedType Bindings.empty final := by
  have h_interp :
      InterpretFunction space d (live := [Atom.undefinedType]) (letExpr pt value body)
        letFunctionType Atom.undefinedType Bindings.empty
        (letExpr pt valueAtom body, valueBindings) :=
    interpretFunction_let_of_value_eval_ok
      h_types h_pt_nerr h_value_nerr h_body_nerr h_value h_value_ok
  have h_op_type : letFunctionType ∈ getAtomTypes space (.symbol "let") := by
    rw [h_types]
    simp
  exact evalAtom_absorbs_let_shell_of_interp
    h_op_type h_check h_check_b h_interp h_call

/-- Source-progress shell for `let` on the changed Empty/Error value-result
fragment.  If evaluating the bound value already produces a changed
Empty/Error result, the `let` propagates that result without touching the
body. -/
theorem evalAtom_absorbs_let_value_eval_bad
    {space : Space} {d : GroundedDispatch}
    {pt value body valueAtom : Atom} {valueBindings : Bindings}
    {final : ResultPair}
    {succs : List Bindings} {fuel : Nat}
    (h_types : getAtomTypes space (.symbol "let") = [letFunctionType])
    (h_check : checkIfFunctionTypeIsApplicable
      (letExpr pt value body) letFunctionType Atom.undefinedType
      space Bindings.empty fuel = .inr succs)
    (h_check_b : Bindings.empty ∈ succs)
    (h_value : EvalAtom space d (live := [body, Atom.atomType, pt, .symbol "let", Atom.undefinedType]) value Atom.undefinedType Bindings.empty
      (valueAtom, valueBindings))
    (h_value_bad : isEmptyOrError valueAtom = true)
    (h_changed : valueAtom ≠ value)
    (h_call : MettaCall space d valueAtom
      Atom.undefinedType valueBindings final) :
    EvalAtom space d (letExpr pt value body)
      Atom.undefinedType Bindings.empty final := by
  have h_interp :
      InterpretFunction space d (live := [Atom.undefinedType]) (letExpr pt value body)
        letFunctionType Atom.undefinedType Bindings.empty
        (valueAtom, valueBindings) :=
    interpretFunction_let_of_value_eval_bad
      h_types h_value h_value_bad h_changed
  have h_op_type : letFunctionType ∈ getAtomTypes space (.symbol "let") := by
    rw [h_types]
    simp
  exact evalAtom_absorbs_let_shell_of_interp
    h_op_type h_check h_check_b h_interp h_call

/-- Source-progress half of `HES_Let`, non-error fragment: if the bound value
takes a certified fragment step, any official evaluation of the successor
value can be lifted back to an official evaluation of the original `let`
provided the continuation `let` form at the evaluated value is officially
callable. -/
theorem evalAtom_absorbs_let_source_frag_ok
    {space : Space} {d : GroundedDispatch}
    {fuel fuelShell : Nat}
    {pt value value' body : Atom} {valueResult final : ResultPair}
    {succs : List Bindings}
    (h_empty_no_eqs : NoEquationMatch space Atom.empty)
    (h_frag : FragStep space d fuel value value' [body, Atom.atomType, pt, .symbol "let", Atom.undefinedType])
    (h_types : getAtomTypes space (.symbol "let") = [letFunctionType])
    (h_check : checkIfFunctionTypeIsApplicable
      (letExpr pt value body) letFunctionType Atom.undefinedType
      space Bindings.empty fuelShell = .inr succs)
    (h_check_b : Bindings.empty ∈ succs)
    (h_pt_nerr : pt ≠ Atom.symbol "Error")
    (h_value_nerr : valueResult.1 ≠ Atom.symbol "Error")
    (h_body_nerr : body ≠ Atom.symbol "Error")
    (h_eval' : EvalAtom space d (live := [body, Atom.atomType, pt, .symbol "let", Atom.undefinedType]) value' Atom.undefinedType Bindings.empty valueResult)
    (h_value_ok : isEmptyOrError valueResult.1 = false)
    (h_call : ∀ {rb},
      EvalAtom space d (live := [body, Atom.atomType, pt, .symbol "let", Atom.undefinedType]) value Atom.undefinedType Bindings.empty (valueResult.1, rb) →
      MettaCall space d (letExpr pt valueResult.1 body)
        Atom.undefinedType rb final) :
    ∃ rb,
      EvalAtom space d (letExpr pt value body)
        Atom.undefinedType Bindings.empty (final.1, rb) := by
  obtain ⟨rb, h_value⟩ := evalAtom_absorbs_fragStep h_empty_no_eqs h_frag h_eval'
  refine ⟨final.2, ?_⟩
  exact evalAtom_absorbs_let_value_eval_ok
    h_types h_check h_check_b h_pt_nerr h_value_nerr h_body_nerr
    h_value h_value_ok (h_call h_value)

/-- Source-progress half of `HES_Let`, changed Empty/Error fragment: if the
bound value takes a certified fragment step and the lifted official
evaluation already yields a changed Empty/Error result, the original `let`
propagates that result immediately. -/
theorem evalAtom_absorbs_let_source_frag_bad
    {space : Space} {d : GroundedDispatch}
    {fuel fuelShell : Nat}
    {pt value value' body : Atom} {valueResult final : ResultPair}
    {succs : List Bindings}
    (h_empty_no_eqs : NoEquationMatch space Atom.empty)
    (h_frag : FragStep space d fuel value value' [body, Atom.atomType, pt, .symbol "let", Atom.undefinedType])
    (h_types : getAtomTypes space (.symbol "let") = [letFunctionType])
    (h_check : checkIfFunctionTypeIsApplicable
      (letExpr pt value body) letFunctionType Atom.undefinedType
      space Bindings.empty fuelShell = .inr succs)
    (h_check_b : Bindings.empty ∈ succs)
    (h_eval' : EvalAtom space d (live := [body, Atom.atomType, pt, .symbol "let", Atom.undefinedType]) value' Atom.undefinedType Bindings.empty valueResult)
    (h_value_bad : isEmptyOrError valueResult.1 = true)
    (h_changed : valueResult.1 ≠ value)
    (h_call : ∀ {rb},
      EvalAtom space d (live := [body, Atom.atomType, pt, .symbol "let", Atom.undefinedType]) value Atom.undefinedType Bindings.empty (valueResult.1, rb) →
      MettaCall space d valueResult.1 Atom.undefinedType rb final) :
    ∃ rb,
      EvalAtom space d (letExpr pt value body)
        Atom.undefinedType Bindings.empty (final.1, rb) := by
  obtain ⟨rb, h_value⟩ := evalAtom_absorbs_fragStep h_empty_no_eqs h_frag h_eval'
  refine ⟨final.2, ?_⟩
  exact evalAtom_absorbs_let_value_eval_bad
    h_types h_check h_check_b h_value h_value_bad h_changed (h_call h_value)

/-- Step-shaped source-progress certification theorem for `HES_Let` on the
non-error fragment.

This ties `evalAtom_absorbs_let_source_frag_ok` back to the coarse
`HESmallStep.let_source` rule, without pretending the continuation call on the
evaluated value has already been discharged automatically. -/
theorem evalAtom_absorbs_let_source_frag_rule_ok
    {space : Space} {d : GroundedDispatch}
    {fuelStep fuelShell : Nat}
    {pt value value' body valueAtom : Atom}
    {valueBindings : Bindings} {final : ResultPair}
    {succs : List Bindings}
    (_h_step : HESmallStep space d fuelStep
      (letExpr pt value body) (letExpr pt value' body))
    (h_empty_no_eqs : NoEquationMatch space Atom.empty)
    (h_frag : FragStep space d fuelStep value value' [body, Atom.atomType, pt, .symbol "let", Atom.undefinedType])
    (h_types : getAtomTypes space (.symbol "let") = [letFunctionType])
    (h_check : checkIfFunctionTypeIsApplicable
      (letExpr pt value body) letFunctionType Atom.undefinedType
      space Bindings.empty fuelShell = .inr succs)
    (h_check_b : Bindings.empty ∈ succs)
    (h_pt_nerr : pt ≠ Atom.symbol "Error")
    (h_value_nerr : valueAtom ≠ Atom.symbol "Error")
    (h_body_nerr : body ≠ Atom.symbol "Error")
    (h_eval' : EvalAtom space d (live := [body, Atom.atomType, pt, .symbol "let", Atom.undefinedType]) value' Atom.undefinedType Bindings.empty
      (valueAtom, valueBindings))
    (h_value_ok : isEmptyOrError valueAtom = false)
    (h_call : ∀ {rb},
      EvalAtom space d (live := [body, Atom.atomType, pt, .symbol "let", Atom.undefinedType]) value Atom.undefinedType Bindings.empty (valueAtom, rb) →
      MettaCall space d (letExpr pt valueAtom body)
        Atom.undefinedType rb final) :
    ∃ rb,
      EvalAtom space d (letExpr pt value body)
        Atom.undefinedType Bindings.empty (final.1, rb) := by
  exact evalAtom_absorbs_let_source_frag_ok
    h_empty_no_eqs h_frag h_types h_check h_check_b
    h_pt_nerr h_value_nerr h_body_nerr h_eval' h_value_ok h_call

/-- Step-shaped source-progress certification theorem for `HES_Let` on the
changed Empty/Error fragment.

This ties `evalAtom_absorbs_let_source_frag_bad` back to the coarse
`HESmallStep.let_source` rule.  If the lifted value evaluation already
produces a changed Empty/Error result, the original source `let` propagates
that result immediately. -/
theorem evalAtom_absorbs_let_source_frag_rule_bad
    {space : Space} {d : GroundedDispatch}
    {fuelStep fuelShell : Nat}
    {pt value value' body valueAtom : Atom}
    {valueBindings : Bindings} {final : ResultPair}
    {succs : List Bindings}
    (_h_step : HESmallStep space d fuelStep
      (letExpr pt value body) (letExpr pt value' body))
    (h_empty_no_eqs : NoEquationMatch space Atom.empty)
    (h_frag : FragStep space d fuelStep value value' [body, Atom.atomType, pt, .symbol "let", Atom.undefinedType])
    (h_types : getAtomTypes space (.symbol "let") = [letFunctionType])
    (h_check : checkIfFunctionTypeIsApplicable
      (letExpr pt value body) letFunctionType Atom.undefinedType
      space Bindings.empty fuelShell = .inr succs)
    (h_check_b : Bindings.empty ∈ succs)
    (h_eval' : EvalAtom space d (live := [body, Atom.atomType, pt, .symbol "let", Atom.undefinedType]) value' Atom.undefinedType Bindings.empty
      (valueAtom, valueBindings))
    (h_value_bad : isEmptyOrError valueAtom = true)
    (h_changed : valueAtom ≠ value)
    (h_call : ∀ {rb},
      EvalAtom space d (live := [body, Atom.atomType, pt, .symbol "let", Atom.undefinedType]) value Atom.undefinedType Bindings.empty (valueAtom, rb) →
      MettaCall space d valueAtom Atom.undefinedType rb final) :
    ∃ rb,
      EvalAtom space d (letExpr pt value body)
        Atom.undefinedType Bindings.empty (final.1, rb) := by
  exact evalAtom_absorbs_let_source_frag_bad
    h_empty_no_eqs h_frag h_types h_check h_check_b
    h_eval' h_value_bad h_changed h_call

/-- Full ground-success `let` wrapper through the verbatim stdlib helper
route, with the query-side freshness assumptions made explicit.

This theorem spends:
- the typed/equational outer `let` shell,
- the seeded `unify` realization boundary, and
- the body-side non-interference lemma for query-local fresh variables.

It is the honest substitution-half certification theorem for source `let`
on the stated fragment: the outer query bindings may be non-empty, but they
must not affect the user body's actual variables. -/
theorem evalAtom_absorbs_let_subst_ground_shell
    {space : Space} {d : GroundedDispatch}
    {pt value body rhs : Atom}
    {qb mb merged : Bindings}
    {succs succsUnify : List Bindings}
    {fuelShell fuelQuery fuelUnify fuelUnifyShell : Nat}
    (h_types : getAtomTypes space (.symbol "let") = [letFunctionType])
    (h_unify_types : getAtomTypes space (.symbol "unify") = [unifyFunctionType])
    (h_check : checkIfFunctionTypeIsApplicable
      (letExpr pt value body) letFunctionType Atom.undefinedType
      space Bindings.empty fuelShell = .inr succs)
    (h_check_b : Bindings.empty ∈ succs)
    (h_unify_check : checkIfFunctionTypeIsApplicable
      (unifyExpr value pt body Atom.empty)
      unifyFunctionType Atom.undefinedType
      space qb fuelUnifyShell = .inr succsUnify)
    (h_unify_check_b : qb ∈ succsUnify)
    (h_not_exec : d.isExecutable (.symbol "let") = false)
    (h_pt_nerr : pt ≠ Atom.symbol "Error")
    (h_value_nerr : value ≠ Atom.symbol "Error")
    (h_body_nerr : body ≠ Atom.symbol "Error")
    (h_value_q : SelfEvalQuiescent space d fuelShell value)
    (hground : GroundAtom value)
    {avoid : List String}
    (h_cover : CoversEvaluation avoid [] (letExpr pt value body) Atom.undefinedType Bindings.empty)
    (h_query : (rhs, qb) ∈ queryEquationsAvoiding avoid space
      (letExpr pt value body) fuelQuery)
    (h_query_merge : qb ∈ mergeBindings qb Bindings.empty fuelQuery)
    (h_query_no_loop : qb.hasLoop = false)
    (h_rhs : qb.applyFull rhs fuelQuery = letUnifyRhs pt value body)
    (hqbEq : qb.equalities = [])
    (hqbKeys : (qb.assignments.map Prod.fst).Nodup)
    (hbody_irrel : ∀ v, v ∈ atomVariables body → qb.lookup v = none)
    (hmatch : mb ∈ matchAtoms value pt fuelUnify)
    (hmerge : merged ∈ mergeBindings mb
      (Spec.Type.Presentation.BindingTheory.aliasConstraints qb) fuelUnify)
    (hmerge_det : mergeGround? mb qb = some merged)
    (h_unify_no_loop : merged.hasLoop = false)
    (h_final_ok : isErrorAtom (mb.applyDefault body) = false) :
    EvalAtom space d (letExpr pt value body)
      Atom.undefinedType Bindings.empty
      (mb.applyDefault body, merged) := by
  have h_interp :
      InterpretFunction space d (live := [Atom.undefinedType]) (letExpr pt value body)
        letFunctionType Atom.undefinedType Bindings.empty
        (letExpr pt value body, Bindings.empty) :=
    interpretFunction_let_self h_types h_pt_nerr h_value_nerr h_body_nerr h_value_q
  have hmbGround : GroundBindings mb :=
    (matchAtoms_ground_canon hground hmatch).1
  have h_body_eq : merged.applyDefault body = mb.applyDefault body := by
    let fuel := merged.resolutionFuel body + mb.resolutionFuel body
    have same : merged.apply body fuel = mb.apply body fuel :=
      apply_eq_of_mergeGround_irrel hmbGround hqbEq hqbKeys hmerge_det
        (fun name member => hbody_irrel name (collectVars_subset_atomVariables body fuel name member))
    have first := merged.applyCovered_stable body (merged.resolutionFuel body)
      (mb.resolutionFuel body) (merged.applyCovered_resolutionFuel body)
    have second := mb.applyCovered_stable body (mb.resolutionFuel body)
      (merged.resolutionFuel body) (mb.applyCovered_resolutionFuel body)
    rw [Nat.add_comm] at second
    exact first.symm.trans (same.trans second)
  have h_merged_eq : merged.equalities = [] := by
    have h_assignments : mergeGroundAssignments? mb qb.assignments = some merged := by
      simpa [mergeGround?, hqbEq] using hmerge_det
    exact (mergeGroundAssignments_equalities h_assignments).trans hmbGround.2
  have h_full_body_eq :
      merged.applyFull body (merged.resolutionFuel body) = mb.applyDefault body := by
    rw [Bindings.applyFull_no_equalities h_merged_eq]
    exact h_body_eq
  have h_eval_rhs :
      EvalAtom space d (qb.applyFull rhs fuelQuery)
        Atom.undefinedType qb
        (mb.applyDefault body, merged) := by
    rw [h_rhs]
    have h_unify :
        EvalAtom space d (letUnifyRhs pt value body)
          Atom.undefinedType qb
          (merged.applyFull body (merged.resolutionFuel body), merged) :=
      evalAtom_realizes_let_subst_ground_seeded_typed
        h_unify_types h_value_nerr h_pt_nerr h_body_nerr
        hground h_unify_check h_unify_check_b hmatch hmerge h_unify_no_loop
    simpa [letUnifyRhs, h_full_body_eq] using h_unify
  have h_call :
      MettaCall space d (letExpr pt value body)
        Atom.undefinedType Bindings.empty
        (mb.applyDefault body, merged) :=
    mettaCall_absorbs_let_equation h_not_exec h_cover h_query h_query_merge
      h_query_no_loop
      (.evaluated _ _ _ _ _
        (by rw [h_rhs]; simp [letUnifyRhs, Atom.notReducible])
        (by rw [h_rhs]; rfl) h_eval_rhs)
  have h_op_type : letFunctionType ∈ getAtomTypes space (.symbol "let") := by
    rw [h_types]
    simp
  exact evalAtom_absorbs_let_shell h_op_type h_check h_check_b
    h_interp h_call h_final_ok

/-- Seeded outer official `let` shell, relative to the explicit typed-function
path and equation-match hypotheses.  This is the incoming-bindings companion
to `evalAtom_absorbs_let_shell`, keeping the shell theorem honest when the
value-evaluation side has already produced a non-empty bindings thread. -/
theorem evalAtom_absorbs_let_shell_seeded
    {space : Space} {d : GroundedDispatch}
    {pt value body : Atom} {seed : Bindings} {final : ResultPair}
    {succs : List Bindings} {fuel : Nat}
    (h_op_type : letFunctionType ∈ getAtomTypes space (.symbol "let"))
    (h_check : checkIfFunctionTypeIsApplicable
      (letExpr pt value body) letFunctionType Atom.undefinedType
      space seed fuel = .inr succs)
    (h_check_b : seed ∈ succs)
    (h_interp : InterpretFunction space d (live := [Atom.undefinedType]) (letExpr pt value body)
      letFunctionType Atom.undefinedType seed
      (letExpr pt value body, seed))
    (h_call : MettaCall space d (letExpr pt value body)
      Atom.undefinedType seed final)
    (h_final_ok : isErrorAtom final.1 = false) :
    EvalAtom space d (letExpr pt value body)
      Atom.undefinedType seed final := by
  refine EvalAtom.interpret_success _ _ _ _ ?_ ?_ rfl ?_ ?_ h_final_ok
  · exact isEmptyOrError_expr_false [pt, value, body] (by simp)
  · simp [letExpr, getMetaType, Atom.undefinedType, Atom.atomType,
      Atom.expressionType, Atom.variableType]
  · intro h_unit
    simp [letExpr, Atom.unit] at h_unit
  · refine InterpretExpression.function_path _ _ _
      (.symbol "let") [pt, value, body]
      letFunctionType Atom.undefinedType seed
      (letExpr pt value body, seed) final fuel
      rfl h_op_type ?_ succs h_check h_check_b rfl h_interp h_call
    rfl

/-- Seeded error-side companion to `evalAtom_absorbs_let_shell_seeded`.
This keeps the outer `let` shell honest when the value-evaluation side has
already shifted the bindings thread and the eventual result is error-shaped. -/
theorem evalAtom_absorbs_let_shell_seeded_error
    {space : Space} {d : GroundedDispatch}
    {pt value body : Atom} {seed : Bindings} {final : ResultPair}
    {succs : List Bindings} {fuel : Nat}
    (h_op_type : letFunctionType ∈ getAtomTypes space (.symbol "let"))
    (h_check : checkIfFunctionTypeIsApplicable
      (letExpr pt value body) letFunctionType Atom.undefinedType
      space seed fuel = .inr succs)
    (h_check_b : seed ∈ succs)
    (h_interp : InterpretFunction space d (live := [Atom.undefinedType]) (letExpr pt value body)
      letFunctionType Atom.undefinedType seed
      (letExpr pt value body, seed))
    (h_call : MettaCall space d (letExpr pt value body)
      Atom.undefinedType seed final)
    (h_final_err : isErrorAtom final.1 = true) :
    EvalAtom space d (letExpr pt value body)
      Atom.undefinedType seed final := by
  refine EvalAtom.interpret_error _ _ _ _ ?_ ?_ rfl ?_ ?_ h_final_err
  · exact isEmptyOrError_expr_false [pt, value, body] (by simp)
  · simp [letExpr, getMetaType, Atom.undefinedType, Atom.atomType,
      Atom.expressionType, Atom.variableType]
  · intro h_unit
    simp [letExpr, Atom.unit] at h_unit
  · refine InterpretExpression.function_path _ _ _
      (.symbol "let") [pt, value, body]
      letFunctionType Atom.undefinedType seed
      (letExpr pt value body, seed) final fuel
      rfl h_op_type ?_ succs h_check h_check_b rfl h_interp h_call
    rfl

/-- Step-shaped substitution-side certification theorem for `HES_Let` on the
ground fragment.

This is a thin wrapper over `evalAtom_absorbs_let_subst_ground_shell`: it
ties that shell theorem back to the coarse `HESmallStep.let_subst` rule,
without pretending the source-progress half of `let` is already certified.

Positive example:
- a coarse `let_subst` step with a ground quiescent value and an irrelevant
  query-local binding layer yields the official evaluation of the whole
  source `let` to the substituted body result.

Negative example:
- if the query-local bindings can affect variables actually occurring in the
  user body, this theorem does not apply; that no-capture boundary remains
  explicit in `hbody_irrel`. -/
theorem evalAtom_absorbs_let_subst_ground_rule
    {space : Space} {d : GroundedDispatch}
    {pt value body rhs : Atom}
    {qb mb merged : Bindings}
    {succs succsUnify : List Bindings}
    {fuelStep fuelShell fuelQuery fuelUnify fuelUnifyShell : Nat}
    (_h_step : HESmallStep space d fuelStep
      (letExpr pt value body) (mb.applyDefault body))
    (h_types : getAtomTypes space (.symbol "let") = [letFunctionType])
    (h_unify_types : getAtomTypes space (.symbol "unify") = [unifyFunctionType])
    (h_check : checkIfFunctionTypeIsApplicable
      (letExpr pt value body) letFunctionType Atom.undefinedType
      space Bindings.empty fuelShell = .inr succs)
    (h_check_b : Bindings.empty ∈ succs)
    (h_unify_check : checkIfFunctionTypeIsApplicable
      (unifyExpr value pt body Atom.empty)
      unifyFunctionType Atom.undefinedType
      space qb fuelUnifyShell = .inr succsUnify)
    (h_unify_check_b : qb ∈ succsUnify)
    (h_not_exec : d.isExecutable (.symbol "let") = false)
    (h_pt_nerr : pt ≠ Atom.symbol "Error")
    (h_value_nerr : value ≠ Atom.symbol "Error")
    (h_body_nerr : body ≠ Atom.symbol "Error")
    (h_value_q : SelfEvalQuiescent space d fuelShell value)
    (hground : GroundAtom value)
    {avoid : List String}
    (h_cover : CoversEvaluation avoid [] (letExpr pt value body) Atom.undefinedType Bindings.empty)
    (h_query : (rhs, qb) ∈ queryEquationsAvoiding avoid space
      (letExpr pt value body) fuelQuery)
    (h_query_merge : qb ∈ mergeBindings qb Bindings.empty fuelQuery)
    (h_query_no_loop : qb.hasLoop = false)
    (h_rhs : qb.applyFull rhs fuelQuery = letUnifyRhs pt value body)
    (hqbEq : qb.equalities = [])
    (hqbKeys : (qb.assignments.map Prod.fst).Nodup)
    (hbody_irrel : ∀ v, v ∈ atomVariables body → qb.lookup v = none)
    (hmatch : mb ∈ matchAtoms value pt fuelUnify)
    (hmerge : merged ∈ mergeBindings mb
      (Spec.Type.Presentation.BindingTheory.aliasConstraints qb) fuelUnify)
    (hmerge_det : mergeGround? mb qb = some merged)
    (h_unify_no_loop : merged.hasLoop = false)
    (h_final_ok : isErrorAtom (mb.applyDefault body) = false) :
    EvalAtom space d (letExpr pt value body)
      Atom.undefinedType Bindings.empty
      (mb.applyDefault body, merged) := by
  simpa [letExpr] using
    (evalAtom_absorbs_let_subst_ground_shell
      (pt := pt) (value := value) (body := body) (rhs := rhs)
      (qb := qb) (mb := mb) (merged := merged)
      (succs := succs) (succsUnify := succsUnify)
      (fuelShell := fuelShell) (fuelQuery := fuelQuery)
      (fuelUnify := fuelUnify) (fuelUnifyShell := fuelUnifyShell)
      h_types h_unify_types h_check h_check_b h_unify_check h_unify_check_b
      h_not_exec h_pt_nerr h_value_nerr h_body_nerr
      h_value_q hground h_cover h_query h_query_merge h_query_no_loop h_rhs
      hqbEq hqbKeys hbody_irrel hmatch hmerge hmerge_det
      h_unify_no_loop h_final_ok)

/-! ## F3a: Primitive `switch-minimal` Selector Core

The stdlib helper route for `switch-minimal` is still useful context, but the
coarse rule itself is really about one simpler semantic fact: scanning the raw
branch list left-to-right, skipping malformed branches, and choosing the first
well-formed branch whose pattern matches the raw scrutinee.

We record that selector directly here, in the same one-way matcher language as
`HESmallStep.switch_minimal_match`.  This keeps the eventual primitive-route
certification honest and local: the recursive selector proof should spend these
facts instead of reproving the branch scan from scratch.

The selector itself now lives in `Matching.lean` so the control-side bridge,
runtime contracts, and future primitive evaluator route can all point at the
same shared kernel rather than a private local copy. -/

/-- Positive example: if a particular well-formed branch is the first one
whose pattern matches the raw scrutinee, the coarse selector returns exactly
that branch's substituted template.

Negative example: malformed earlier branches do not block the match; they are
skipped by the selector and therefore need no "earlier failure" witness. -/
theorem selectSwitchTemplateCoarse_of_prefix_match
    {scrut pt template : Atom} {pre post : List Atom}
    {mb : Bindings} {fuel : Nat}
    (h_match : simpleMatch pt scrut Bindings.empty fuel = some mb)
    (h_earlier : ∀ branch ∈ pre, ∀ pt' template',
      branch = Atom.expression [pt', template'] →
      simpleMatch pt' scrut Bindings.empty fuel = none) :
    selectSwitchTemplateCoarse scrut
      (pre ++ Atom.expression [pt, template] :: post) fuel =
      mb.applyDefault template := by
  induction pre with
  | nil =>
      simp [selectSwitchTemplateCoarse, selectSwitchResultPair?, h_match]
  | cons head rest ih =>
      have h_rest :
          ∀ branch ∈ rest, ∀ pt' template',
            branch = Atom.expression [pt', template'] →
            simpleMatch pt' scrut Bindings.empty fuel = none := by
        intro branch hmem pt' template' hshape
        exact h_earlier branch (by simp [hmem]) pt' template' hshape
      cases h_head : head with
      | symbol s =>
          simp [selectSwitchTemplateCoarse, selectSwitchResultPair?]
          exact ih h_rest
      | var v =>
          simp [selectSwitchTemplateCoarse, selectSwitchResultPair?]
          exact ih h_rest
      | grounded g =>
          simp [selectSwitchTemplateCoarse, selectSwitchResultPair?]
          exact ih h_rest
      | expression hs =>
          cases hs with
          | nil =>
              simp [selectSwitchTemplateCoarse, selectSwitchResultPair?]
              exact ih h_rest
          | cons a hs1 =>
              cases hs1 with
              | nil =>
                  simp [selectSwitchTemplateCoarse, selectSwitchResultPair?]
                  exact ih h_rest
              | cons b hs2 =>
                  cases hs2 with
                  | nil =>
                      have h_fail : simpleMatch a scrut Bindings.empty fuel = none :=
                        h_earlier (Atom.expression [a, b]) (by
                          simp [h_head]) a b rfl
                      simp [selectSwitchTemplateCoarse, selectSwitchResultPair?, h_fail]
                      exact ih h_rest
                  | cons c hs3 =>
                      simp [selectSwitchTemplateCoarse, selectSwitchResultPair?]
                      exact ih h_rest

/-- Indexed companion to `selectSwitchTemplateCoarse_of_prefix_match`.
This is the exact first-match theorem shape that the coarse
`HESmallStep.switch_minimal_match` constructor already carries: a selected
well-formed branch at index `i`, a successful match there, and failure of all
earlier well-formed branches. -/
theorem selectSwitchTemplateCoarse_of_index_match
    {scrut : Atom} {branches : List Atom} {i : Nat}
    {pt template : Atom} {mb : Bindings} {fuel : Nat}
    (h_branch : branches[i]? = some (.expression [pt, template]))
    (h_match : simpleMatch pt scrut Bindings.empty fuel = some mb)
    (h_earlier : ∀ j < i, ∀ pt' template',
      branches[j]? = some (.expression [pt', template']) →
      simpleMatch pt' scrut Bindings.empty fuel = none) :
    selectSwitchTemplateCoarse scrut branches fuel =
      mb.applyDefault template := by
  rcases (List.getElem?_eq_some_iff.mp h_branch) with ⟨hi, hget⟩
  have hsplit :
      branches =
        List.take i branches ++ Atom.expression [pt, template] ::
          List.drop (i + 1) branches := by
    calc
      branches = List.take i branches ++ List.drop i branches := by
        symm
        exact List.take_append_drop i branches
      _ = List.take i branches ++ branches[i] :: List.drop (i + 1) branches := by
        rw [List.drop_eq_getElem_cons hi]
      _ = List.take i branches ++ Atom.expression [pt, template] ::
            List.drop (i + 1) branches := by
        rw [hget]
  have h_prefix :
      ∀ branch ∈ List.take i branches, ∀ pt' template',
        branch = Atom.expression [pt', template'] →
        simpleMatch pt' scrut Bindings.empty fuel = none := by
    intro branch hmem pt' template' hshape
    rcases (List.mem_iff_getElem.mp hmem) with ⟨j, hj, hj_eq⟩
    have htake_len : (List.take i branches).length = i := by
      rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
    have hj_lt_i : j < i := by
      simpa [htake_len] using hj
    have hj_lt_len : j < branches.length := lt_trans hj_lt_i hi
    have hj_eq_branch : branches[j] = branch := by
      have htakej :
          (List.take i branches)[j] = branches[j] :=
        List.getElem_take (xs := branches) (j := i) (i := j) (h := hj)
      exact htakej.symm.trans hj_eq
    have hj_some :
        branches[j]? = some (Atom.expression [pt', template']) := by
      simp [List.getElem?_eq_getElem hj_lt_len, hj_eq_branch, hshape]
    exact h_earlier j hj_lt_i pt' template' hj_some
  rw [hsplit]
  exact selectSwitchTemplateCoarse_of_prefix_match h_match h_prefix

/-- If every well-formed branch fails to match the raw scrutinee, the coarse
selector returns the `NotReducible` sentinel.

Positive example: a branch list of only malformed branches returns
`NotReducible`.

Negative example: as soon as some well-formed branch matches, this theorem no
longer applies and `selectSwitchTemplateCoarse_of_prefix_match` becomes the
relevant fact instead. -/
theorem selectSwitchTemplateCoarse_notReducible_of_all_fail
    {scrut : Atom} {branches : List Atom} {fuel : Nat}
    (h_all_fail : ∀ branch ∈ branches, ∀ pt template,
      branch = Atom.expression [pt, template] →
      simpleMatch pt scrut Bindings.empty fuel = none) :
    selectSwitchTemplateCoarse scrut branches fuel = Atom.notReducible := by
  induction branches with
  | nil =>
      simp [selectSwitchTemplateCoarse, selectSwitchResultPair?]
  | cons head rest ih =>
      have h_rest :
          ∀ branch ∈ rest, ∀ pt template,
            branch = Atom.expression [pt, template] →
            simpleMatch pt scrut Bindings.empty fuel = none := by
        intro branch hmem pt template hshape
        exact h_all_fail branch (by simp [hmem]) pt template hshape
      cases h_head : head with
      | symbol s =>
          simp [selectSwitchTemplateCoarse, selectSwitchResultPair?]
          exact ih h_rest
      | var v =>
          simp [selectSwitchTemplateCoarse, selectSwitchResultPair?]
          exact ih h_rest
      | grounded g =>
          simp [selectSwitchTemplateCoarse, selectSwitchResultPair?]
          exact ih h_rest
      | expression hs =>
          cases hs with
          | nil =>
              simp [selectSwitchTemplateCoarse, selectSwitchResultPair?]
              exact ih h_rest
          | cons a hs1 =>
              cases hs1 with
              | nil =>
                  simp [selectSwitchTemplateCoarse, selectSwitchResultPair?]
                  exact ih h_rest
              | cons b hs2 =>
                  cases hs2 with
                  | nil =>
                      have h_head_fail :
                          simpleMatch a scrut Bindings.empty fuel = none :=
                        h_all_fail (Atom.expression [a, b]) (by
                          simp [h_head]) a b rfl
                      simp [selectSwitchTemplateCoarse, selectSwitchResultPair?, h_head_fail]
                      exact ih h_rest
                  | cons c hs3 =>
                      simp [selectSwitchTemplateCoarse, selectSwitchResultPair?]
                      exact ih h_rest

/-- Indexed companion to `selectSwitchTemplateCoarse_notReducible_of_all_fail`.
If every indexed well-formed branch fails to match the raw scrutinee, the
coarse selector returns `NotReducible`. -/
theorem selectSwitchTemplateCoarse_notReducible_of_index_fail
    {scrut : Atom} {branches : List Atom} {fuel : Nat}
    (h_all_fail : ∀ (i : Nat) (pt template : Atom),
      branches[i]? = some (Atom.expression [pt, template]) →
      simpleMatch pt scrut Bindings.empty fuel = none) :
    selectSwitchTemplateCoarse scrut branches fuel = Atom.notReducible := by
  apply selectSwitchTemplateCoarse_notReducible_of_all_fail
  intro branch hmem pt template hshape
  rcases (List.mem_iff_getElem.mp hmem) with ⟨i, hi, hi_eq⟩
  have hi_some :
      branches[i]? = some (Atom.expression [pt, template]) := by
    simp [List.getElem?_eq_getElem hi, hi_eq, hshape]
  exact h_all_fail i pt template hi_some

/-- Positive selector-to-coarse-step bridge: the indexed witness carried by
`HESmallStep.switch_minimal_match` produces a coarse step whose result is
exactly the primitive first-match selector result.  This keeps later
`switch-minimal` packaging aligned with the primitive selector interface rather
than only the raw `mb.applyDefault template` witness. -/
theorem step_switchMinimal_to_selector_of_index_match
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {scrut : Atom} {branches : List Atom} {i : Nat}
    {pt template : Atom} {mb : Bindings}
    (h_branch : branches[i]? = some (.expression [pt, template]))
    (h_match : simpleMatch pt scrut Bindings.empty fuel = some mb)
    (h_earlier : ∀ j < i, ∀ pt' template',
      branches[j]? = some (.expression [pt', template']) →
      simpleMatch pt' scrut Bindings.empty fuel = none) :
    HESmallStep space d fuel
      (.expression [.symbol "switch-minimal", scrut, .expression branches])
      (selectSwitchTemplateCoarse scrut branches fuel) := by
  have hsel :
      selectSwitchTemplateCoarse scrut branches fuel =
        mb.applyDefault template :=
    selectSwitchTemplateCoarse_of_index_match h_branch h_match h_earlier
  rw [hsel]
  exact HESmallStep.switch_minimal_match rfl h_branch h_match h_earlier

/-- Converse selector witness on the honest non-sentinel fragment: if the
primitive first-match selector returns some atom other than `NotReducible`,
then that result really came from a well-formed matching branch, together
with the exact indexed earlier-failure witness carried by the coarse
`switch_minimal_match` rule.  The sentinel case stays explicit because a
matching template may itself literally be `NotReducible`, so equality to the
sentinel alone is not enough to recover a coarse witness. -/
theorem selectSwitchTemplateCoarse_exists_of_ne_notReducible
    {scrut : Atom} {branches : List Atom} {fuel : Nat} {result : Atom}
    (hsel : selectSwitchTemplateCoarse scrut branches fuel = result)
    (hred : result ≠ Atom.notReducible) :
    ∃ (i : Nat) (pt template : Atom) (mb : Bindings),
      branches[i]? = some (.expression [pt, template]) ∧
      simpleMatch pt scrut Bindings.empty fuel = some mb ∧
      (∀ j < i, ∀ pt' template',
        branches[j]? = some (.expression [pt', template']) →
        simpleMatch pt' scrut Bindings.empty fuel = none) ∧
      result = mb.applyDefault template := by
  induction branches generalizing result with
  | nil =>
      simp [selectSwitchTemplateCoarse, selectSwitchResultPair?] at hsel
      exact False.elim (hred hsel.symm)
  | cons head tail ih =>
      cases h_head : head with
      | symbol s =>
          have hsel_tail : selectSwitchTemplateCoarse scrut tail fuel = result := by
            simpa [selectSwitchTemplateCoarse, selectSwitchResultPair?, h_head] using hsel
          rcases ih hsel_tail hred with
            ⟨i, pt, template, mb, h_branch, h_match, h_earlier, h_result⟩
          refine ⟨i + 1, pt, template, mb, ?_, h_match, ?_, h_result⟩
          · simpa using h_branch
          · intro j hj pt' template' h_branch_j
            cases j with
            | zero =>
                simp at h_branch_j
            | succ j' =>
                have hj' : j' < i := Nat.lt_of_succ_lt_succ hj
                exact h_earlier j' hj' pt' template' (by simpa using h_branch_j)
      | var v =>
          have hsel_tail : selectSwitchTemplateCoarse scrut tail fuel = result := by
            simpa [selectSwitchTemplateCoarse, selectSwitchResultPair?, h_head] using hsel
          rcases ih hsel_tail hred with
            ⟨i, pt, template, mb, h_branch, h_match, h_earlier, h_result⟩
          refine ⟨i + 1, pt, template, mb, ?_, h_match, ?_, h_result⟩
          · simpa using h_branch
          · intro j hj pt' template' h_branch_j
            cases j with
            | zero =>
                simp at h_branch_j
            | succ j' =>
                have hj' : j' < i := Nat.lt_of_succ_lt_succ hj
                exact h_earlier j' hj' pt' template' (by simpa using h_branch_j)
      | grounded g =>
          have hsel_tail : selectSwitchTemplateCoarse scrut tail fuel = result := by
            simpa [selectSwitchTemplateCoarse, selectSwitchResultPair?, h_head] using hsel
          rcases ih hsel_tail hred with
            ⟨i, pt, template, mb, h_branch, h_match, h_earlier, h_result⟩
          refine ⟨i + 1, pt, template, mb, ?_, h_match, ?_, h_result⟩
          · simpa using h_branch
          · intro j hj pt' template' h_branch_j
            cases j with
            | zero =>
                simp at h_branch_j
            | succ j' =>
                have hj' : j' < i := Nat.lt_of_succ_lt_succ hj
                exact h_earlier j' hj' pt' template' (by simpa using h_branch_j)
      | expression hs =>
          cases hs with
          | nil =>
              have hsel_tail : selectSwitchTemplateCoarse scrut tail fuel = result := by
                simpa [selectSwitchTemplateCoarse, selectSwitchResultPair?, h_head] using hsel
              rcases ih hsel_tail hred with
                ⟨i, pt, template, mb, h_branch, h_match, h_earlier, h_result⟩
              refine ⟨i + 1, pt, template, mb, ?_, h_match, ?_, h_result⟩
              · simpa using h_branch
              · intro j hj pt' template' h_branch_j
                cases j with
                | zero =>
                    simp at h_branch_j
                | succ j' =>
                    have hj' : j' < i := Nat.lt_of_succ_lt_succ hj
                    exact h_earlier j' hj' pt' template' (by simpa using h_branch_j)
          | cons a hs1 =>
              cases hs1 with
              | nil =>
                  have hsel_tail : selectSwitchTemplateCoarse scrut tail fuel = result := by
                    simpa [selectSwitchTemplateCoarse, selectSwitchResultPair?, h_head] using hsel
                  rcases ih hsel_tail hred with
                    ⟨i, pt, template, mb, h_branch, h_match, h_earlier, h_result⟩
                  refine ⟨i + 1, pt, template, mb, ?_, h_match, ?_, h_result⟩
                  · simpa using h_branch
                  · intro j hj pt' template' h_branch_j
                    cases j with
                    | zero =>
                        simp at h_branch_j
                    | succ j' =>
                        have hj' : j' < i := Nat.lt_of_succ_lt_succ hj
                        exact h_earlier j' hj' pt' template' (by simpa using h_branch_j)
              | cons b hs2 =>
                  cases hs2 with
                  | nil =>
                      cases h_match0 : simpleMatch a scrut Bindings.empty fuel with
                      | none =>
                          have hsel_tail :
                              selectSwitchTemplateCoarse scrut tail fuel = result := by
                            simpa [selectSwitchTemplateCoarse, selectSwitchResultPair?, h_head, h_match0] using hsel
                          rcases ih hsel_tail hred with
                            ⟨i, pt, template, mb, h_branch, h_match, h_earlier, h_result⟩
                          refine ⟨i + 1, pt, template, mb, ?_, h_match, ?_, h_result⟩
                          · simpa using h_branch
                          · intro j hj pt' template' h_branch_j
                            cases j with
                            | zero =>
                                have h_pair :
                                    Atom.expression [a, b] =
                                      Atom.expression [pt', template'] := by
                                  simpa [h_head] using h_branch_j
                                cases h_pair
                                simpa using h_match0
                            | succ j' =>
                                have hj' : j' < i := Nat.lt_of_succ_lt_succ hj
                                exact h_earlier j' hj' pt' template'
                                  (by simpa using h_branch_j)
                      | some mb0 =>
                          refine ⟨0, a, b, mb0, ?_, h_match0, ?_, ?_⟩
                          · simp
                          · intro j hj
                            exact False.elim (Nat.not_lt_zero _ hj)
                          · simpa [selectSwitchTemplateCoarse, selectSwitchResultPair?, h_head, h_match0] using hsel.symm
                  | cons c hs3 =>
                      have hsel_tail : selectSwitchTemplateCoarse scrut tail fuel = result := by
                        simpa [selectSwitchTemplateCoarse, selectSwitchResultPair?, h_head] using hsel
                      rcases ih hsel_tail hred with
                        ⟨i, pt, template, mb, h_branch, h_match, h_earlier, h_result⟩
                      refine ⟨i + 1, pt, template, mb, ?_, h_match, ?_, h_result⟩
                      · simpa using h_branch
                      · intro j hj pt' template' h_branch_j
                        cases j with
                        | zero =>
                            simp at h_branch_j
                        | succ j' =>
                            have hj' : j' < i := Nat.lt_of_succ_lt_succ hj
                            exact h_earlier j' hj' pt' template' (by simpa using h_branch_j)

/-- Selector-to-coarse-step converse on the honest non-sentinel fragment.
If the primitive selector returns some atom other than `NotReducible`, then
the coarse `switch-minimal` relation really does have a visible match step to
that result. -/
theorem step_switchMinimal_of_selector_ne_notReducible
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {scrut : Atom} {branches : List Atom} {result : Atom}
    (hsel : selectSwitchTemplateCoarse scrut branches fuel = result)
    (hred : result ≠ Atom.notReducible) :
    HESmallStep space d fuel
      (.expression [.symbol "switch-minimal", scrut, .expression branches])
      result := by
  rcases selectSwitchTemplateCoarse_exists_of_ne_notReducible hsel hred with
    ⟨i, pt, template, mb, h_branch, h_match, h_earlier, h_result⟩
  rw [h_result]
  exact HESmallStep.switch_minimal_match rfl h_branch h_match h_earlier

/-! ## F3b: Direct Executable `switch-minimal` Results

The coarse selector witnesses above describe which branch should be chosen.
The executable evaluator now exposes that choice through
`switchMinimalResults`, so we record the corresponding direct membership fact
before packaging it into `MettaCall`/`EvalAtom` shells. -/

/-- Positive executable witness for the direct `switch-minimal` lane: if a
particular well-formed branch is the first one whose pattern matches the raw
scrutinee, and the surviving merged bindings are loop-free, then the
observable executable result set contains exactly that branch result (with the
stdlib `NotReducible -> Empty` post-processing). -/
theorem switchMinimalResults_mem_of_prefix_match
    {scrut pt template : Atom} {pre post : List Atom}
    {mb : Bindings} {n : Nat}
    (h_match : simpleMatch pt scrut Bindings.empty (n + 1) = some mb)
    (h_no_loop : mb.hasLoop = false)
    (h_earlier : ∀ branch ∈ pre, ∀ pt' template',
      branch = Atom.expression [pt', template'] →
      simpleMatch pt' scrut Bindings.empty (n + 1) = none) :
    ((if mb.applyDefault template == Atom.notReducible
        then Atom.empty else mb.applyDefault template), mb)
      ∈ switchMinimalResults scrut
          (pre ++ Atom.expression [pt, template] :: post)
          Bindings.empty (n + 1) := by
  induction pre with
  | nil =>
      simp [switchMinimalResults, switchMinimalRawResults, h_match,
        mergeBindings_empty_right, h_no_loop]
  | cons head rest ih =>
      have h_rest :
          ∀ branch ∈ rest, ∀ pt' template',
            branch = Atom.expression [pt', template'] →
            simpleMatch pt' scrut Bindings.empty (n + 1) = none := by
        intro branch hmem pt' template' hshape
        exact h_earlier branch (by simp [hmem]) pt' template' hshape
      cases h_head : head with
      | symbol s =>
          simpa [switchMinimalResults, switchMinimalRawResults, h_head] using
            ih h_rest
      | var v =>
          simpa [switchMinimalResults, switchMinimalRawResults, h_head] using
            ih h_rest
      | grounded g =>
          simpa [switchMinimalResults, switchMinimalRawResults, h_head] using
            ih h_rest
      | expression hs =>
          cases hs with
          | nil =>
              simpa [switchMinimalResults, switchMinimalRawResults, h_head] using
                ih h_rest
          | cons a hs =>
              cases hs with
              | nil =>
                  simpa [switchMinimalResults, switchMinimalRawResults, h_head] using
                    ih h_rest
              | cons b hs' =>
                  cases hs' with
                  | nil =>
                      have h_miss : simpleMatch a scrut Bindings.empty (n + 1) = none := by
                        exact h_earlier head (by simp) a b h_head
                      simpa [switchMinimalResults, switchMinimalRawResults, h_head, h_miss] using
                        ih h_rest
                  | cons c hs'' =>
                      simpa [switchMinimalResults, switchMinimalRawResults, h_head] using
                        ih h_rest

/-- Indexed companion to `switchMinimalResults_mem_of_prefix_match`, matching
the exact witness shape carried by `HESmallStep.switch_minimal_match`. -/
theorem switchMinimalResults_mem_of_index_match
    {scrut : Atom} {branches : List Atom} {i : Nat}
    {pt template : Atom} {mb : Bindings} {n : Nat}
    (h_branch : branches[i]? = some (.expression [pt, template]))
    (h_match : simpleMatch pt scrut Bindings.empty (n + 1) = some mb)
    (h_no_loop : mb.hasLoop = false)
    (h_earlier : ∀ j < i, ∀ pt' template',
      branches[j]? = some (.expression [pt', template']) →
      simpleMatch pt' scrut Bindings.empty (n + 1) = none) :
    ((if mb.applyDefault template == Atom.notReducible
        then Atom.empty else mb.applyDefault template), mb)
      ∈ switchMinimalResults scrut branches Bindings.empty (n + 1) := by
  rcases (List.getElem?_eq_some_iff.mp h_branch) with ⟨hi, hget⟩
  have hsplit :
      branches =
        List.take i branches ++ Atom.expression [pt, template] ::
          List.drop (i + 1) branches := by
    calc
      branches = List.take i branches ++ List.drop i branches := by
        symm
        exact List.take_append_drop i branches
      _ = List.take i branches ++ branches[i] :: List.drop (i + 1) branches := by
        rw [List.drop_eq_getElem_cons hi]
      _ = List.take i branches ++ Atom.expression [pt, template] ::
            List.drop (i + 1) branches := by
        rw [hget]
  have h_prefix :
      ∀ branch ∈ List.take i branches, ∀ pt' template',
        branch = Atom.expression [pt', template'] →
        simpleMatch pt' scrut Bindings.empty (n + 1) = none := by
    intro branch hmem pt' template' hshape
    rcases (List.mem_iff_getElem.mp hmem) with ⟨j, hj, hj_eq⟩
    have htake_len : (List.take i branches).length = i := by
      rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
    have hj_lt_i : j < i := by
      simpa [htake_len] using hj
    have hj_lt_len : j < branches.length := lt_trans hj_lt_i hi
    have hj_eq_branch : branches[j] = branch := by
      have htakej :
          (List.take i branches)[j] = branches[j] :=
        List.getElem_take (xs := branches) (j := i) (i := j) (h := hj)
      exact htakej.symm.trans hj_eq
    have hj_some :
        branches[j]? = some (Atom.expression [pt', template']) := by
      simp [List.getElem?_eq_getElem hj_lt_len, hj_eq_branch, hshape]
    exact h_earlier j hj_lt_i pt' template' hj_some
  rw [hsplit]
  exact switchMinimalResults_mem_of_prefix_match h_match h_no_loop h_prefix

/-! ## F3: `switch-minimal` / `switch-internal` Typed Function + Equation Shells

The matcher bridge and `unify` realization now give us the branch-local core
of `switch-internal`. The next honest outer layer is the typed/equational
source-syntax shell shared by `switch-minimal` and `switch-internal`: both are
stdlib equations whose heads carry the same binary function type
`(-> Atom Expression Atom)`. We expose that shell explicitly so the later
recursive branch proof can spend real interface theorems rather than rebuild
the function/equation plumbing ad hoc. -/

/-- The shared stdlib function type for `switch-minimal` and
`switch-internal`. -/
private def switchBinaryFunctionType : Atom :=
  .expression [.symbol "->", Atom.atomType, Atom.expressionType, Atom.atomType]

/-- Source-syntax `switch-minimal` atom in the upstream stdlib shape. -/
private def switchMinimalExpr (scrut : Atom) (branches : List Atom) : Atom :=
  .expression [.symbol "switch-minimal", scrut, .expression branches]

/-- Source-syntax `switch-internal` atom in the upstream stdlib shape. -/
private def switchInternalExpr (scrut headBranch : Atom) (tail : List Atom) : Atom :=
  .expression [.symbol "switch-internal", scrut,
    .expression [headBranch, .expression tail]]

/-- The recursive else-branch used by the upstream `switch-internal` helper. -/
private def switchInternalElseChain (scrut : Atom) (tail : List Atom) : Atom :=
  .expression [.symbol "chain",
    .expression [.symbol "eval", switchMinimalExpr scrut tail],
    .var "ret",
    .expression [.symbol "return", .var "ret"]]

/-- The verbatim upstream `unify` core inside `switch-internal`. -/
private def switchInternalUnify
    (scrut pt template : Atom) (tail : List Atom) : Atom :=
  .expression [.symbol "unify", scrut, pt,
    .expression [.symbol "return", template],
    switchInternalElseChain scrut tail]

/-- The verbatim upstream `function` body for `switch-internal`. -/
private def switchInternalBody
    (scrut pt template : Atom) (tail : List Atom) : Atom :=
  .expression [.symbol "function", switchInternalUnify scrut pt template tail]

/-- Alpha-renamed variant of the recursive else-branch used by
`switch-internal`: the local chain binder may be any fresh variable name,
not just the unsuffixed source spelling.  This matches the real
`queryEquations` route, which freshens all equation-local variables. -/
private def switchInternalElseChainVar
    (retVar : String) (scrut : Atom) (tail : List Atom) : Atom :=
  .expression [.symbol "chain",
    .expression [.symbol "eval", switchMinimalExpr scrut tail],
    .var retVar,
    .expression [.symbol "return", .var retVar]]

/-- Alpha-renamed variant of the upstream `unify` core inside
`switch-internal`, parameterized by the freshened local binder used in the
recursive else branch. -/
private def switchInternalUnifyVar
    (retVar : String) (scrut pt template : Atom) (tail : List Atom) : Atom :=
  .expression [.symbol "unify", scrut, pt,
    .expression [.symbol "return", template],
    switchInternalElseChainVar retVar scrut tail]

/-- Alpha-renamed variant of the verbatim upstream `function` body for
`switch-internal`, parameterized by the freshened local binder. -/
private def switchInternalBodyVar
    (retVar : String) (scrut pt template : Atom) (tail : List Atom) : Atom :=
  .expression [.symbol "function", switchInternalUnifyVar retVar scrut pt template tail]

private theorem switchInternalElseChainVar_ret
    (scrut : Atom) (tail : List Atom) :
    switchInternalElseChainVar "ret" scrut tail = switchInternalElseChain scrut tail := rfl

private theorem switchInternalUnifyVar_ret
    (scrut pt template : Atom) (tail : List Atom) :
    switchInternalUnifyVar "ret" scrut pt template tail =
      switchInternalUnify scrut pt template tail := rfl

private theorem switchInternalBodyVar_ret
    (scrut pt template : Atom) (tail : List Atom) :
    switchInternalBodyVar "ret" scrut pt template tail =
      switchInternalBody scrut pt template tail := rfl

/-- If the space presents `switch-minimal` with exactly its stdlib function
type, then the official type-cast path evaluates the head symbol to itself at
that type. -/
private theorem evalAtom_switchMinimal_head_typed
    {space : Space} {d : GroundedDispatch} {live : List Atom}
    (h_types : getAtomTypes space (.symbol "switch-minimal") = [switchBinaryFunctionType]) :
    EvalAtom space d (live := live) (.symbol "switch-minimal") switchBinaryFunctionType Bindings.empty
      (.symbol "switch-minimal", Bindings.empty) := by
  refine EvalAtom.type_cast _ _ _ _ 10 rfl ?_ (Or.inl rfl) ?_
  · simp [switchBinaryFunctionType, getMetaType, Atom.atomType,
      Atom.symbolType, Atom.variableType]
  · rw [typeCast]
    simp only [rawTypeLookup]
    rw [h_types]
    decide

/-- If the space presents `switch-internal` with exactly its stdlib function
type, then the official type-cast path evaluates the head symbol to itself at
that type. -/
private theorem evalAtom_switchInternal_head_typed
    {space : Space} {d : GroundedDispatch} {live : List Atom}
    (h_types : getAtomTypes space (.symbol "switch-internal") = [switchBinaryFunctionType]) :
    EvalAtom space d (live := live) (.symbol "switch-internal") switchBinaryFunctionType Bindings.empty
      (.symbol "switch-internal", Bindings.empty) := by
  refine EvalAtom.type_cast _ _ _ _ 10 rfl ?_ (Or.inl rfl) ?_
  · simp [switchBinaryFunctionType, getMetaType, Atom.atomType,
      Atom.symbolType, Atom.variableType]
  · rw [typeCast]
    simp only [rawTypeLookup]
    rw [h_types]
    decide

/-- Any non-empty, non-error-headed expression can be evaluated against the
expected type `Expression`, producing itself with unchanged bindings. -/
private theorem evalAtom_expr_type_self
    {space : Space} {d : GroundedDispatch} {live : List Atom}
    (head : Atom) (tail : List Atom) (b : Bindings)
    (h_head_nerr : head ≠ Atom.symbol "Error") :
    EvalAtom space d (live := live) (.expression (head :: tail)) Atom.expressionType b
      (.expression (head :: tail), b) := by
  exact EvalAtom.type_pass _ _ _ (isEmptyOrError_expr_false tail h_head_nerr)
    (Or.inr (Or.inl rfl))

/-- Shared argument-shell lemma for the binary switch helpers:
the first argument is interpreted at type `Atom`, and the second at type
`Expression`, both self-evaluating on the certified fragment. -/
private theorem interpretArgs_switch_binary_self
    {space : Space} {d : GroundedDispatch} {live : List Atom}
    {scrut head : Atom} {tail : List Atom}
    (h_head_nerr : head ≠ Atom.symbol "Error") :
    InterpretArgs space d (live := live) [scrut, .expression (head :: tail)]
      [Atom.atomType, Atom.expressionType]
      Bindings.empty
      (argumentPacket [scrut, .expression (head :: tail)], Bindings.empty) := by
  have h_scrut {scope : List Atom} : EvalAtom space d (live := scope) scrut Atom.atomType Bindings.empty
      (scrut, Bindings.empty) :=
    evalAtom_atom_type scrut Bindings.empty
  have h_cases {scope : List Atom} : EvalAtom space d (live := scope) (.expression (head :: tail))
      Atom.expressionType Bindings.empty
      (.expression (head :: tail), Bindings.empty) :=
    evalAtom_expr_type_self head tail Bindings.empty h_head_nerr
  have h_tail {scope : List Atom} : InterpretArgs space d (live := scope) [.expression (head :: tail)]
      [Atom.expressionType] Bindings.empty
      (argumentPacket [.expression (head :: tail)], Bindings.empty) := by
    exact InterpretArgs.cons_ok (.expression (head :: tail)) [] Atom.expressionType []
      Bindings.empty
      (.expression (head :: tail), Bindings.empty)
      (argumentPacket [], Bindings.empty)
      h_cases (Or.inr rfl) InterpretArgs.nil rfl
  refine InterpretArgs.cons_ok scrut [.expression (head :: tail)] Atom.atomType
    [Atom.expressionType] Bindings.empty
    (scrut, Bindings.empty) (argumentPacket [.expression (head :: tail)], Bindings.empty)
    h_scrut (Or.inr rfl) h_tail ?_
  simp

/-- Typed function-path shell for the verbatim upstream `switch-minimal`
source form on the fragment where the raw-cases expression is non-empty and
not error-shaped. -/
theorem interpretFunction_switchMinimal_self
    {space : Space} {d : GroundedDispatch} {live : List Atom}
    {scrut headBranch : Atom} {tail : List Atom}
    (h_types : getAtomTypes space (.symbol "switch-minimal") = [switchBinaryFunctionType])
    (_h_scrut_nerr : scrut ≠ Atom.symbol "Error")
    (h_head_nerr : headBranch ≠ Atom.symbol "Error") :
    InterpretFunction space d (live := live) (switchMinimalExpr scrut (headBranch :: tail))
      switchBinaryFunctionType Atom.undefinedType Bindings.empty
      (switchMinimalExpr scrut (headBranch :: tail), Bindings.empty) := by
  have h_head {scope : List Atom} : EvalAtom space d (live := scope) (.symbol "switch-minimal")
      switchBinaryFunctionType Bindings.empty
      (.symbol "switch-minimal", Bindings.empty) :=
    evalAtom_switchMinimal_head_typed h_types
  have h_tail {scope : List Atom} : InterpretArgs space d (live := scope) [scrut, .expression (headBranch :: tail)]
      [Atom.atomType, Atom.expressionType]
      Bindings.empty
      (argumentPacket [scrut, .expression (headBranch :: tail)], Bindings.empty) :=
    interpretArgs_switch_binary_self h_head_nerr
  refine InterpretFunction.head_ok_tail_ok
    (switchMinimalExpr scrut (headBranch :: tail))
    switchBinaryFunctionType Atom.undefinedType Bindings.empty
    (.symbol "switch-minimal") [scrut, .expression (headBranch :: tail)]
    [Atom.atomType, Atom.expressionType]
    (.symbol "switch-minimal", Bindings.empty)
    (argumentPacket [scrut, .expression (headBranch :: tail)], Bindings.empty)
    rfl rfl h_head rfl h_tail ?_
  simp

/-- Typed function-path shell for the verbatim upstream `switch-internal`
source form on the fragment where the deconsed head branch is itself not the
bare `Error` symbol.  In the intended use that head is a branch pair
expression, so this side condition is immediate. -/
theorem interpretFunction_switchInternal_self
    {space : Space} {d : GroundedDispatch} {live : List Atom}
    {scrut headBranch : Atom} {tail : List Atom}
    (h_types : getAtomTypes space (.symbol "switch-internal") = [switchBinaryFunctionType])
    (_h_scrut_nerr : scrut ≠ Atom.symbol "Error")
    (h_head_nerr : headBranch ≠ Atom.symbol "Error") :
    InterpretFunction space d (live := live) (switchInternalExpr scrut headBranch tail)
      switchBinaryFunctionType Atom.undefinedType Bindings.empty
      (switchInternalExpr scrut headBranch tail, Bindings.empty) := by
  have h_head {scope : List Atom} : EvalAtom space d (live := scope) (.symbol "switch-internal")
      switchBinaryFunctionType Bindings.empty
      (.symbol "switch-internal", Bindings.empty) :=
    evalAtom_switchInternal_head_typed h_types
  have h_tail {scope : List Atom} : InterpretArgs space d (live := scope) [scrut, .expression [headBranch, .expression tail]]
      [Atom.atomType, Atom.expressionType]
      Bindings.empty
      (argumentPacket [scrut, .expression [headBranch, .expression tail]], Bindings.empty) :=
    interpretArgs_switch_binary_self h_head_nerr
  refine InterpretFunction.head_ok_tail_ok
    (switchInternalExpr scrut headBranch tail)
    switchBinaryFunctionType Atom.undefinedType Bindings.empty
    (.symbol "switch-internal") [scrut, .expression [headBranch, .expression tail]]
    [Atom.atomType, Atom.expressionType]
    (.symbol "switch-internal", Bindings.empty)
    (argumentPacket [scrut, .expression [headBranch, .expression tail]], Bindings.empty)
    rfl rfl h_head rfl h_tail ?_
  simp

/-- Direct `MettaCall` wrapper for the exact-shape upstream
`switch-minimal` source form.  After the evaluator-side refactor,
`switch-minimal` no longer reaches the generic equation lane; its official
observable behavior is the dedicated `switchMinimalResults` kernel. -/
theorem mettaCall_absorbs_switchMinimal_direct
    {space : Space} {d : GroundedDispatch}
    {scrut : Atom} {branches : List Atom} {type_ : Atom}
    {final : ResultPair} {fuel : Nat}
    (h_result : final ∈ switchMinimalResults scrut branches Bindings.empty fuel) :
    MettaCall space d (switchMinimalExpr scrut branches) type_
      Bindings.empty final :=
  MettaCall.switch_minimal_result _ _ _ scrut branches final fuel
    rfl
    (by simp [switchMinimalExpr, isErrorAtom])
    h_result

/-- Generic equation-call wrapper for the verbatim upstream `switch-internal`
source form. -/
theorem mettaCall_absorbs_switchInternal_equation
    {space : Space} {d : GroundedDispatch}
    {scrut headBranch : Atom} {tail : List Atom}
    {type_ rhs : Atom} {qb merged : Bindings}
    {final : ResultPair} {fuel : Nat}
    (h_not_exec : d.isExecutable (.symbol "switch-internal") = false)
    {avoid : List String}
    (h_cover : CoversEvaluation avoid [] (switchInternalExpr scrut headBranch tail) type_ Bindings.empty)
    (h_query : (rhs, qb) ∈ queryEquationsAvoiding avoid space
      (switchInternalExpr scrut headBranch tail) fuel)
    (h_merge : merged ∈ mergeBindings qb Bindings.empty fuel)
    (h_no_loop : merged.hasLoop = false)
    (h_return : OrdinaryCallReturnRel space d (switchInternalExpr scrut headBranch tail)
      (merged.applyFull rhs fuel) type_ merged final) :
    MettaCall space d (switchInternalExpr scrut headBranch tail) type_
      Bindings.empty final :=
  MettaCall.equation_match _ _ _ rhs qb merged final fuel
    (by simp [switchInternalExpr, isErrorAtom])
    (by
      refine ⟨?_, ?_⟩
      · simpa [switchInternalExpr] using h_not_exec
      · simp)
    h_cover h_query h_merge h_no_loop h_return

/-- Outer official shell for `switch-minimal`, relative to the explicit typed
function-path and equation-call hypotheses.  This isolates the remaining
recursive branch-selection content from the already-settled source-syntax
typed/equational plumbing. -/
theorem evalAtom_absorbs_switchMinimal_shell
    {space : Space} {d : GroundedDispatch}
    {scrut headBranch : Atom} {tail : List Atom} {final : ResultPair}
    {succs : List Bindings} {fuel : Nat}
    (h_op_type : switchBinaryFunctionType ∈ getAtomTypes space (.symbol "switch-minimal"))
    (h_check : checkIfFunctionTypeIsApplicable
      (switchMinimalExpr scrut (headBranch :: tail)) switchBinaryFunctionType Atom.undefinedType
      space Bindings.empty fuel = .inr succs)
    (h_check_b : Bindings.empty ∈ succs)
    (h_interp : InterpretFunction space d (live := [Atom.atomType]) (switchMinimalExpr scrut (headBranch :: tail))
      switchBinaryFunctionType Atom.undefinedType Bindings.empty
      (switchMinimalExpr scrut (headBranch :: tail), Bindings.empty))
    (h_call : MettaCall space d (switchMinimalExpr scrut (headBranch :: tail))
      Atom.atomType Bindings.empty final)
    (h_final_ok : isErrorAtom final.1 = false) :
    EvalAtom space d (switchMinimalExpr scrut (headBranch :: tail))
      Atom.undefinedType Bindings.empty final := by
  refine EvalAtom.interpret_success _ _ _ _ ?_ ?_ rfl ?_ ?_ h_final_ok
  · exact isEmptyOrError_expr_false [scrut, .expression (headBranch :: tail)] (by simp)
  · simp [switchMinimalExpr, getMetaType, Atom.undefinedType, Atom.atomType,
      Atom.expressionType, Atom.variableType]
  · intro h_unit
    simp [switchMinimalExpr, Atom.unit] at h_unit
  · refine InterpretExpression.function_path _ _ _
      (.symbol "switch-minimal") [scrut, .expression (headBranch :: tail)]
      switchBinaryFunctionType Atom.atomType Bindings.empty
      (switchMinimalExpr scrut (headBranch :: tail), Bindings.empty) final fuel
      rfl h_op_type ?_ succs h_check h_check_b ?_ h_interp h_call
    · rfl
    · decide

/-- Honest direct outer shell for exact-shape `switch-minimal`: once the
typed function-path checks have admitted the source form, any executable
result already present in `switchMinimalResults` is an official `EvalAtom`
result of the whole call.  This is the dedicated executable route that
replaces the old equation-wrapper fiction. -/
theorem evalAtom_absorbs_switchMinimal_direct_shell
    {space : Space} {d : GroundedDispatch}
    {scrut headBranch : Atom} {tail : List Atom} {final : ResultPair}
    {succs : List Bindings} {fuelCheck fuelCall : Nat}
    (h_types : getAtomTypes space (.symbol "switch-minimal") = [switchBinaryFunctionType])
    (h_check : checkIfFunctionTypeIsApplicable
      (switchMinimalExpr scrut (headBranch :: tail)) switchBinaryFunctionType Atom.undefinedType
      space Bindings.empty fuelCheck = .inr succs)
    (h_check_b : Bindings.empty ∈ succs)
    (h_scrut_nerr : scrut ≠ Atom.symbol "Error")
    (h_head_nerr : headBranch ≠ Atom.symbol "Error")
    (h_result : final ∈ switchMinimalResults scrut (headBranch :: tail) Bindings.empty fuelCall)
    (h_final_ok : isErrorAtom final.1 = false) :
    EvalAtom space d (switchMinimalExpr scrut (headBranch :: tail))
      Atom.undefinedType Bindings.empty final := by
  have h_interp :
      InterpretFunction space d (live := [Atom.atomType]) (switchMinimalExpr scrut (headBranch :: tail))
        switchBinaryFunctionType Atom.undefinedType Bindings.empty
        (switchMinimalExpr scrut (headBranch :: tail), Bindings.empty) :=
    interpretFunction_switchMinimal_self h_types h_scrut_nerr h_head_nerr
  have h_call :
      MettaCall space d (switchMinimalExpr scrut (headBranch :: tail))
        Atom.atomType Bindings.empty final :=
    mettaCall_absorbs_switchMinimal_direct h_result
  have h_op_type : switchBinaryFunctionType ∈ getAtomTypes space (.symbol "switch-minimal") := by
    rw [h_types]
    simp
  exact evalAtom_absorbs_switchMinimal_shell
    h_op_type h_check h_check_b h_interp h_call h_final_ok

/-- Honest direct success-side rule theorem for the non-sentinel ground
fragment of coarse `switch-minimal`: when the selected branch is the first
matching well-formed branch, its substituted template is an official direct
evaluator result of the whole `switch-minimal` call. -/
theorem evalAtom_absorbs_switchMinimal_match_ground_rule
    {space : Space} {d : GroundedDispatch}
    {scrut headBranch : Atom} {tail : List Atom}
    {i : Nat} {pt template : Atom} {mb : Bindings}
    {succs : List Bindings} {fuelStep fuelShell : Nat}
    (_h_step : HESmallStep space d fuelStep
      (switchMinimalExpr scrut (headBranch :: tail)) (mb.applyDefault template))
    (h_types : getAtomTypes space (.symbol "switch-minimal") = [switchBinaryFunctionType])
    (h_check : checkIfFunctionTypeIsApplicable
      (switchMinimalExpr scrut (headBranch :: tail))
      switchBinaryFunctionType Atom.undefinedType
      space Bindings.empty fuelShell = .inr succs)
    (h_check_b : Bindings.empty ∈ succs)
    (h_scrut_nerr : scrut ≠ Atom.symbol "Error")
    (h_head_nerr : headBranch ≠ Atom.symbol "Error")
    (hground : GroundAtom scrut)
    (h_branch : (headBranch :: tail)[i]? = some (.expression [pt, template]))
    (h_match : simpleMatch pt scrut Bindings.empty fuelStep = some mb)
    (h_earlier : ∀ j < i, ∀ pt' template',
      (headBranch :: tail)[j]? = some (.expression [pt', template']) →
      simpleMatch pt' scrut Bindings.empty fuelStep = none)
    (h_not_reducible : mb.applyDefault template ≠ Atom.notReducible)
    (h_final_ok : isErrorAtom (mb.applyDefault template) = false) :
    EvalAtom space d (switchMinimalExpr scrut (headBranch :: tail))
      Atom.undefinedType Bindings.empty
      (mb.applyDefault template, mb) := by
  cases fuelStep with
  | zero =>
      simp [simpleMatch] at h_match
  | succ n =>
      obtain ⟨fuel0, hmb, _⟩ := simpleMatch_ground_matchAtoms hground h_match
      have hmbCanon : GroundBindingsCanon mb := matchAtoms_ground_canon hground hmb
      have hnoLoop : mb.hasLoop = false :=
        GroundBindings.hasLoop_false hmbCanon.1
      have h_result :
          ((if mb.applyDefault template == Atom.notReducible
              then Atom.empty else mb.applyDefault template), mb)
            ∈ switchMinimalResults scrut (headBranch :: tail) Bindings.empty (n + 1) :=
        switchMinimalResults_mem_of_index_match h_branch h_match hnoLoop h_earlier
      have h_result' :
          (mb.applyDefault template, mb) ∈
            switchMinimalResults scrut (headBranch :: tail) Bindings.empty (n + 1) := by
        simpa [h_not_reducible] using h_result
      exact evalAtom_absorbs_switchMinimal_direct_shell
        h_types h_check h_check_b h_scrut_nerr h_head_nerr h_result' h_final_ok

/-- Outer official shell for `switch-internal`, relative to the explicit
typed function-path and equation-call hypotheses.  This isolates the
recursive head-hit/head-miss proof from the already-settled typed/equational
syntax layer. -/
theorem evalAtom_absorbs_switchInternal_shell
    {space : Space} {d : GroundedDispatch}
    {scrut headBranch : Atom} {tail : List Atom} {final : ResultPair}
    {succs : List Bindings} {fuel : Nat}
    (h_op_type : switchBinaryFunctionType ∈ getAtomTypes space (.symbol "switch-internal"))
    (h_check : checkIfFunctionTypeIsApplicable
      (switchInternalExpr scrut headBranch tail) switchBinaryFunctionType
      Atom.undefinedType space Bindings.empty fuel = .inr succs)
    (h_check_b : Bindings.empty ∈ succs)
    (h_interp : InterpretFunction space d (live := [Atom.atomType]) (switchInternalExpr scrut headBranch tail)
      switchBinaryFunctionType Atom.undefinedType Bindings.empty
      (switchInternalExpr scrut headBranch tail, Bindings.empty))
    (h_call : MettaCall space d (switchInternalExpr scrut headBranch tail)
      Atom.atomType Bindings.empty final)
    : EvalAtom space d (switchInternalExpr scrut headBranch tail)
      Atom.undefinedType Bindings.empty final := by
  have h_interp_call : InterpretExpression space d
      (switchInternalExpr scrut headBranch tail) Atom.undefinedType Bindings.empty final := by
    refine InterpretExpression.function_path _ _ _
      (.symbol "switch-internal") [scrut, .expression [headBranch, .expression tail]]
      switchBinaryFunctionType Atom.atomType Bindings.empty
      (switchInternalExpr scrut headBranch tail, Bindings.empty) final fuel
      rfl h_op_type ?_ succs h_check h_check_b ?_ h_interp h_call
    · rfl
    · decide
  have h_running : isEmptyOrError (switchInternalExpr scrut headBranch tail) = false :=
    isEmptyOrError_expr_false
      [scrut, .expression [headBranch, .expression tail]] (by simp)
  have h_no_pass : ¬(Atom.undefinedType = Atom.atomType ∨
      Atom.undefinedType = getMetaType (switchInternalExpr scrut headBranch tail) ∨
      getMetaType (switchInternalExpr scrut headBranch tail) = Atom.variableType) := by
    simp [switchInternalExpr, getMetaType, Atom.undefinedType, Atom.atomType,
      Atom.expressionType, Atom.variableType]
  have h_no_unit : switchInternalExpr scrut headBranch tail ≠ Atom.unit := by
    simp [switchInternalExpr, Atom.unit]
  by_cases h_error : isErrorAtom final.1 = true
  · exact .interpret_error _ _ _ _ h_running h_no_pass rfl h_no_unit h_interp_call h_error
  · exact .interpret_success _ _ _ _ h_running h_no_pass rfl h_no_unit h_interp_call
      (by simpa using h_error)



/-- Applying bindings to a `(return ...)` wrapper preserves the head symbol
and substitutes only inside the payload. Structural coverage makes this
boundary independent of an arbitrary numerical fuel skew. -/
private theorem applyDefault_return_shape
    (b : Bindings) (payload : Atom) :
    b.applyDefault (.expression [.symbol "return", payload]) =
      .expression [.symbol "return", b.applyDefault payload] := by
  rw [Bindings.applyDefault_expression]
  simp

/-- An Atom-typed equation body crosses the ordinary return protocol before
being held as data. A raw `NotReducible` restores the actual switch invocation;
ordinary, Empty and Error bodies retain their value. Every branch keeps `qb`.
This is an equation-shell observation, separate from executing the stdlib's
minimal control body. -/
theorem evalAtom_absorbs_switchInternal_return_shell
    {space : Space} {d : GroundedDispatch}
    {scrut headBranch rhs body : Atom} {tail : List Atom}
    {qb : Bindings}
    {succs : List Bindings}
    {fuelShell fuelQuery : Nat}
    (h_types : getAtomTypes space (.symbol "switch-internal") = [switchBinaryFunctionType])
    (h_check : checkIfFunctionTypeIsApplicable
      (switchInternalExpr scrut headBranch tail)
      switchBinaryFunctionType Atom.undefinedType
      space Bindings.empty fuelShell = .inr succs)
    (h_check_b : Bindings.empty ∈ succs)
    (h_not_exec : d.isExecutable (.symbol "switch-internal") = false)
    (h_scrut_nerr : scrut ≠ Atom.symbol "Error")
    (h_head_nerr : headBranch ≠ Atom.symbol "Error")
    {avoid : List String}
    (h_cover : CoversEvaluation avoid [] (switchInternalExpr scrut headBranch tail) Atom.atomType Bindings.empty)
    (h_query : (rhs, qb) ∈ queryEquationsAvoiding avoid space
      (switchInternalExpr scrut headBranch tail) fuelQuery)
    (h_query_merge : qb ∈ mergeBindings qb Bindings.empty fuelQuery)
    (h_query_no_loop : qb.hasLoop = false)
    (h_rhs : qb.applyFull rhs fuelQuery = body)
    : EvalAtom space d
      (switchInternalExpr scrut headBranch tail)
      Atom.undefinedType Bindings.empty
      ((if body = Atom.notReducible then switchInternalExpr scrut headBranch tail else body), qb) := by
  have h_interp :
      InterpretFunction space d (live := [Atom.atomType]) (switchInternalExpr scrut headBranch tail)
        switchBinaryFunctionType Atom.undefinedType Bindings.empty
        (switchInternalExpr scrut headBranch tail, Bindings.empty) :=
    interpretFunction_switchInternal_self h_types h_scrut_nerr h_head_nerr
  have h_return : OrdinaryCallReturnRel space d
      (switchInternalExpr scrut headBranch tail) (qb.applyFull rhs fuelQuery)
      Atom.atomType qb
      ((if body = Atom.notReducible then switchInternalExpr scrut headBranch tail else body), qb) := by
    rw [h_rhs]
    exact OrdinaryCallReturnRel.atom_type _ _ _
  have h_call := mettaCall_absorbs_switchInternal_equation
    h_not_exec h_cover h_query h_query_merge h_query_no_loop h_return
  have h_op_type : switchBinaryFunctionType ∈ getAtomTypes space (.symbol "switch-internal") := by
    rw [h_types]
    simp
  exact evalAtom_absorbs_switchInternal_shell
    h_op_type h_check h_check_b h_interp h_call

/-! ## Ordinary switch-return controls -/

namespace SwitchReturnControls

private def call : Atom := switchInternalExpr (.symbol "subject") (.symbol "branch") []

private def source (body : Atom) : Space := Space.ofList
  [.expression [.symbol ":", .symbol "switch-internal", switchBinaryFunctionType],
   .expression [.symbol "=", call, body]]

private def errorBody : Atom := .expression [.symbol "Error", .symbol "detail"]

/-- The same real typed/equational shell handles data, protocol and stopped
replies. The source is a closed equation, so its query bindings are empty. -/
private theorem observed (body : Atom)
    (chosen : body = Atom.notReducible ∨ body = .symbol "value" ∨
      body = Atom.empty ∨ body = errorBody) :
    EvalAtom (source body) GroundedDispatch.none call Atom.undefinedType Bindings.empty
      ((if body = Atom.notReducible then call else body), Bindings.empty) := by
  apply evalAtom_absorbs_switchInternal_return_shell
    (rhs := body) (qb := Bindings.empty) (succs := [Bindings.empty])
    (fuelShell := 20) (fuelQuery := 20) (avoid := [])
  all_goals rcases chosen with rfl | rfl | rfl | rfl
  all_goals first
    | decide
    | (intro name member
       simp [equationScope, atomListVariables, atomVariables,
         switchInternalExpr, Atom.atomType, Bindings.names, Bindings.empty] at member)

/-- A protocol equation reply restores the invocation even with Atom demand. -/
example : EvalAtom (source Atom.notReducible) GroundedDispatch.none call
    Atom.undefinedType Bindings.empty (call, Bindings.empty) := by
  simpa using observed Atom.notReducible (Or.inl rfl)

/-- An ordinary equation reply is held at the Atom demand. -/
example : EvalAtom (source (.symbol "value")) GroundedDispatch.none call
    Atom.undefinedType Bindings.empty (.symbol "value", Bindings.empty) := by
  simpa [Atom.notReducible] using observed (.symbol "value") (Or.inr (Or.inl rfl))

/-- Empty remains a stopped reply, not a request to restore the call. -/
example : EvalAtom (source Atom.empty) GroundedDispatch.none call
    Atom.undefinedType Bindings.empty (Atom.empty, Bindings.empty) := by
  simpa [Atom.empty, Atom.notReducible] using
    observed Atom.empty (Or.inr (Or.inr (Or.inl rfl)))

/-- Error retains its complete diagnostic atom through the same shell. -/
example : EvalAtom (source errorBody) GroundedDispatch.none call
    Atom.undefinedType Bindings.empty (errorBody, Bindings.empty) := by
  simpa [errorBody, Atom.notReducible] using
    observed errorBody (Or.inr (Or.inr (Or.inr rfl)))

end SwitchReturnControls

/-! ## Alias-aware success readout controls -/

namespace HistoricalUnifyReadoutControls

private def aliasSeed : Bindings := Bindings.empty.addEquality "left" "right"
private def pending : Atom := .expression [.symbol "pair", .var "right", .var "right"]
private def observed : Atom := .expression [.symbol "pair", .var "left", .var "left"]

/-- A ground success retains the alias frame and reads both pending uses through it. -/
theorem success_keeps_alias_correlation :
    unifySuccessResults (.symbol "a") (.symbol "a") pending aliasSeed 4 =
      [(observed, aliasSeed)] := by decide

/-- Assignment-only substitution cannot supply this equality-bearing result. -/
theorem assignment_only_result_refused :
    (aliasSeed.applyDefault pending, aliasSeed) ∉
      unifySuccessResults (.symbol "a") (.symbol "a") pending aliasSeed 4 := by decide

end HistoricalUnifyReadoutControls

end Mettapedia.Languages.MeTTa.HE

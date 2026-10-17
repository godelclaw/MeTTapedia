import Mettapedia.OSLF.MeTTaIL.ContextSubstitution

/-!
# Rule occurrence contexts

An authored rule can state which binder variables a metavariable may use and
which terms supply those dependencies at each occurrence. This module reads
those declarations from the existing rule carrier. The address checks are
structural; sorted elaboration and rule execution use the resulting data.
-/

namespace Mettapedia.OSLF.MeTTaIL.RuleBinding

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextSubstitution

set_option autoImplicit false

/-- The metavariable at a child address of an existing pattern, if any.
The address immediately after a collection's explicit elements selects its
rest variable. Constructor arguments and collection elements keep their order. -/
def occurrenceAt? : Pattern → List Nat → Option String
  | .fvar name, [] => some name
  | .apply _ args, index :: path =>
      (args[index]?).bind (occurrenceAt? · path)
  | .lambda _ body, 0 :: path => occurrenceAt? body path
  | .multiLambda _ _ body, 0 :: path => occurrenceAt? body path
  | .subst body _, 0 :: path => occurrenceAt? body path
  | .subst _ replacement, 1 :: path => occurrenceAt? replacement path
  | .collection _ elements rest, index :: path =>
      if index < elements.length then
        (elements[index]?).bind (occurrenceAt? · path)
      else if index == elements.length && path.isEmpty then rest else none
  | _, _ => none

/-- Count the object binders on a metavariable occurrence address. This is
independent of the supplied value's ambient context. -/
def occurrenceDepthAt? : Pattern → List Nat → Nat → Option Nat
  | .fvar _, [], depth => some depth
  | .apply _ args, index :: path, depth =>
      (args[index]?).bind (occurrenceDepthAt? · path depth)
  | .lambda _ body, 0 :: path, depth => occurrenceDepthAt? body path (depth + 1)
  | .multiLambda arity _ body, 0 :: path, depth =>
      occurrenceDepthAt? body path (depth + arity)
  | .subst body _, 0 :: path, depth => occurrenceDepthAt? body path (depth + 1)
  | .subst _ replacement, 1 :: path, depth =>
      occurrenceDepthAt? replacement path depth
  | .collection _ elements rest, index :: path, depth =>
      if index < elements.length then
        (elements[index]?).bind (occurrenceDepthAt? · path depth)
      else if index == elements.length && path.isEmpty && rest.isSome then
        some depth
      else none
  | _, _, _ => none

/-- Follow the uniquely nested bodies of quantified premises. -/
def quantifiedBody? : Nat → Premise → Option Premise
  | 0, premise => some premise
  | count + 1, .forAll _ _ body => quantifiedBody? count body
  | _ + 1, _ => none

/-- Read one original rule component without manufacturing an expression. -/
def sitePattern? (rule : RewriteRule) : RulePatternSite → Option Pattern
  | .left => some rule.left
  | .right => some rule.right
  | .premise index quantifiers argument => do
      let premise ← rule.premises[index]?
      match ← quantifiedBody? quantifiers premise with
      | .freshness condition =>
          if argument == 0 then some condition.term else none
      | .congruence source target =>
          if argument == 0 then some source
          else if argument == 1 then some target else none
      | .scopedStep step =>
          if argument == 0 then some step.source
          else if argument == 1 then some step.target else none
      | .relationQuery _ args => args[argument]?
      | .forAll _ _ _ => none

/-- The binders supplied by the selected premise itself. These precede any
binders encountered while following a child address within its endpoint. -/
def siteBinderDepth? (rule : RewriteRule) : RulePatternSite → Option Nat
  | .left | .right => some 0
  | .premise index quantifiers argument => do
      let premise ← rule.premises[index]?
      match ← quantifiedBody? quantifiers premise with
      | .freshness _ => if argument == 0 then some 0 else none
      | .congruence _ _ => if argument < 2 then some 0 else none
      | .scopedStep step =>
          if argument < 2 then some step.binders.length else none
      | .relationQuery _ args => if argument < args.length then some 0 else none
      | .forAll _ _ _ => none

/-- The complete local depth of an authored occurrence is the premise-local
prefix followed by constructor binders along its exact endpoint address. -/
def occurrenceDepthAtSite? (rule : RewriteRule) (site : RulePatternSite)
    (path : List Nat) : Option Nat := do
  let pattern ← sitePattern? rule site
  let localDepth ← siteBinderDepth? rule site
  occurrenceDepthAt? pattern path localDepth

/-- A scoped premise contributes its binder prefix to both endpoint sites. -/
theorem siteBinderDepth?_scopedStep (rule : RewriteRule) (index : Nat)
    (step : ScopedStepPremise)
    (hpremise : rule.premises[index]? = some (.scopedStep step))
    (argument : Nat) (hargument : argument < 2) :
    siteBinderDepth? rule (.premise index 0 argument) =
      some step.binders.length := by
  simp [siteBinderDepth?, hpremise, quantifiedBody?, hargument]

/-- The new site calculation is definitionally the old calculation at the
rule redex. -/
theorem occurrenceDepthAtSite?_left (rule : RewriteRule) (path : List Nat) :
    occurrenceDepthAtSite? rule .left path =
      occurrenceDepthAt? rule.left path 0 := rfl

/-- The contractum keeps the same root-depth convention. -/
theorem occurrenceDepthAtSite?_right (rule : RewriteRule) (path : List Nat) :
    occurrenceDepthAtSite? rule .right path =
      occurrenceDepthAt? rule.right path 0 := rfl

/-- An ordinary congruence premise opens no additional binder, exactly as in
the previous declaration checker. -/
theorem occurrenceDepthAtSite?_congruence (rule : RewriteRule)
    (index argument : Nat) (source target : Pattern) (path : List Nat)
    (hpremise : rule.premises[index]? = some (.congruence source target))
    (hargument : argument < 2) :
    occurrenceDepthAtSite? rule (.premise index 0 argument) path =
      occurrenceDepthAt?
        (if argument == 0 then source else target) path 0 := by
  cases argument with
  | zero => simp [occurrenceDepthAtSite?, siteBinderDepth?,
      sitePattern?, quantifiedBody?, hpremise]
  | succ argument =>
      have hzero : argument = 0 := by omega
      subst argument
      simp [occurrenceDepthAtSite?, siteBinderDepth?,
        sitePattern?, quantifiedBody?, hpremise]

/-- Check a claimed occurrence against the actual rule, including a rest
name when the address points to the collection's rest slot. -/
def occurrenceDeclared (rule : RewriteRule) (row : MetavariableOccurrence) : Bool :=
  (sitePattern? rule row.site).bind (occurrenceAt? · row.path) == some row.name

/-- Find a metavariable's dependency sorts in the one canonical rule spec.
Duplicate declarations are not accepted as a choice of the first row. -/
def dependencies? (spec : RuleBindingSpec) (name : String) : Option (List TypeExpr) :=
  match spec.dependencies.filter (fun entry => entry.1 == name) with
  | [(_, dependencies)] => some dependencies
  | _ => none

/-- Admit the current executable binding profile only when it covers the rule
context exactly and every explicit occurrence names a unique, actual site
with locally scoped, metavariable-free dependency arguments. The generic
typed substitution allows richer arguments; those require recursive rule
instantiation before the executable profile can accept them. This also checks
annotations not reached by one particular match. -/
def admittedFor (rule : RewriteRule) (spec : RuleBindingSpec) : Bool :=
  decide (rule.typeContext.map Prod.fst).Nodup &&
  decide (spec.dependencies.map Prod.fst).Nodup &&
  decide ((spec.occurrences.map fun row => (row.name, row.site, row.path)).Nodup) &&
  (rule.typeContext.length == spec.dependencies.length) &&
  rule.typeContext.all (fun entry =>
    spec.dependencies.any (fun declared => declared.1 == entry.1)) &&
  spec.occurrences.all (fun row =>
    occurrenceDeclared rule row &&
      match dependencies? spec row.name,
        occurrenceDepthAtSite? rule row.site row.path with
      | some dependencies, some depth =>
          row.arguments.length == dependencies.length &&
            row.arguments.all (fun argument => argument.isGroundAt depth)
      | _, _ => false)

/-- Every dependency sort in this rule's binding declaration is named by the
authored language. The ordinary language validator checks the result sorts in
`typeContext`, but does not yet inspect this newer declaration field. -/
def dependencySortsDeclared (lang : LanguageDef) (spec : RuleBindingSpec) : Bool :=
  spec.dependencies.all fun (_, sorts) =>
    sorts.all fun sort => sort.baseNames.all fun name => name ∈ lang.typeNames

/-- Structural validation of an authored language and every rewrite binding
declaration. This does not assert that the chosen premise interpreter supports
all premise forms; that is a separate execution-profile check. -/
def bindingDeclarationsValid (lang : LanguageDef) : Bool :=
  lang.validate.isEmpty && lang.rewrites.all fun rule =>
    match rule.bindings with
    | none => false
    | some spec => admittedFor rule spec && dependencySortsDeclared lang spec

/-- A ready presentation supplies a structurally admitted binding declaration
for each authored rewrite rule. -/
theorem bindingDeclarationsValid_rule {lang : LanguageDef}
    (hready : bindingDeclarationsValid lang = true) {rule : RewriteRule}
    (hmem : rule ∈ lang.rewrites) :
    ∃ spec, rule.bindings = some spec ∧ admittedFor rule spec = true ∧
      dependencySortsDeclared lang spec = true := by
  simp only [bindingDeclarationsValid, Bool.and_eq_true] at hready
  have hall : (lang.rewrites.all fun rule =>
      match rule.bindings with
      | none => false
      | some spec => admittedFor rule spec && dependencySortsDeclared lang spec) = true :=
    hready.2
  have hrule := List.all_eq_true.mp hall rule hmem
  cases hspec : rule.bindings with
  | none => simp [hspec] at hrule
  | some spec =>
      simp only [hspec, Bool.and_eq_true] at hrule
      exact ⟨spec, rfl, hrule.1, hrule.2⟩

/-- Select an authored occurrence substitution. The empty spine is inferred
only for a declared variable with no bound dependencies and no explicit row.
The producer check belongs to ordered rule admission, not to this lookup. -/
def arguments? (rule : RewriteRule) (spec : RuleBindingSpec)
    (name : String) (site : RulePatternSite) (path : List Nat) :
    Option (List Pattern) := do
  let dependencies ← dependencies? spec name
  guard (occurrenceDeclared rule { name, site, path, arguments := [] })
  let matching := spec.occurrences.filter
    (fun row => row.name == name && row.site == site && row.path == path)
  match matching with
  | [] => if dependencies.isEmpty then some [] else none
  | [row] =>
      if occurrenceDeclared rule row && row.arguments.length == dependencies.length
      then some row.arguments else none
  | _ => none

/-- The empty dependency inference is independent of binder depth. -/
theorem arguments?_empty_of_declared (rule : RewriteRule)
    (spec : RuleBindingSpec) (name : String) (site : RulePatternSite)
    (path : List Nat) (hdependencies : dependencies? spec name = some [])
    (hsite : occurrenceDeclared rule
      { name, site, path, arguments := [] } = true)
    (hrows : spec.occurrences.filter
      (fun row => row.name == name && row.site == site && row.path == path) = []) :
    arguments? rule spec name site path = some [] := by
  simp [arguments?, hdependencies, hsite, hrows]

/-- Every accepted explicit row addresses its claimed metavariable and has
one argument per declared dependency. -/
theorem arguments?_explicit_contract (rule : RewriteRule)
    (spec : RuleBindingSpec) (name : String) (site : RulePatternSite)
    (path : List Nat) (row : MetavariableOccurrence)
    (dependencySorts : List TypeExpr)
    (hdeps : dependencies? spec name = some dependencySorts)
    (harity : row.arguments.length = dependencySorts.length)
    (hrows : spec.occurrences.filter
      (fun candidate => candidate.name == name && candidate.site == site &&
        candidate.path == path) = [row])
    (hdeclared : occurrenceDeclared rule row = true) :
    arguments? rule spec name site path = some row.arguments := by
  have hmem : row ∈ spec.occurrences.filter
      (fun candidate => candidate.name == name && candidate.site == site &&
        candidate.path == path) := by
    rw [hrows]
    simp
  have hmatch : (row.name = name ∧ row.site = site) ∧ row.path = path := by
    simpa only [Bool.and_eq_true, beq_iff_eq] using (List.mem_filter.mp hmem).2
  rcases hmatch with ⟨⟨hname, hsiteEq⟩, hpath⟩
  have hsite : occurrenceDeclared rule
      { name, site, path, arguments := [] } = true := by
    simpa [occurrenceDeclared, hname, hsiteEq, hpath] using hdeclared
  simp [arguments?, hdeps, hrows, hdeclared, harity, hsite]

/-- The erased runtime value carries its dependency context and ambient
context explicitly. Its body is read in `dependencies ++ ambient`. -/
structure ContextualValue where
  dependencies : List TypeExpr
  ambient : Nat
  body : Pattern
deriving Repr, DecidableEq

/-- Supply the dependency arguments at an occurrence `depth` binders below
the ambient context. The fallback of `List.getD` is unreachable after the
arity check in `instantiateValue?`. -/
def occurrenceAssignment (dependencies depth : Nat)
    (arguments : List Pattern) : Assignment :=
  fun index => if index < dependencies then arguments.getD index (.bvar 0)
    else .bvar (depth + (index - dependencies))

/-- Instantiate an already captured value, checking the exact source and
destination contexts and every argument supplied by this occurrence. -/
def instantiateValue? (value : ContextualValue) (ambient depth : Nat)
    (arguments : List Pattern) : Option Pattern := do
  if value.ambient != ambient then none else
  if arguments.length != value.dependencies.length then none else
  if !(value.body.isWellScopedAt (value.dependencies.length + ambient)) then none else
  if !(arguments.all (fun argument => argument.isWellScopedAt (depth + ambient))) then
    none
  else
    let result := substitute
      (occurrenceAssignment value.dependencies.length depth arguments) value.body
    if result.isWellScopedAt (depth + ambient) then some result else none

/-- Every returned raw result is scoped at its destination occurrence,
regardless of the source value or the supplied argument shapes. -/
theorem instantiateValue?_scoped (value : ContextualValue) (ambient depth : Nat)
    (arguments : List Pattern) (result : Pattern)
    (h : instantiateValue? value ambient depth arguments = some result) :
    result.isWellScopedAt (depth + ambient) = true := by
  unfold instantiateValue? at h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h <;> try cases h
  dsimp only at h
  split at h <;> cases h
  assumption

/-- An injective spine of local variables permits recovering a body from
one pattern occurrence. Nonvariable occurrence substitutions still instantiate,
but are not claimed to be invertible by this matching procedure. -/
def variableSpine? (depth : Nat) (arguments : List Pattern) : Option (List Nat) := do
  let indices ← arguments.mapM (fun argument =>
    match argument with
    | .bvar index => if index < depth then some index else none
    | _ => none)
  if indices.Nodup then some indices else none

/-- Inverse of the variable spine on selected variables. Unselected local
variables receive an out-of-context index and fail the scope check. Ambient
variables retain their own context segment. -/
def recoveryAssignment (depth dependencies ambient : Nat)
    (indices : List Nat) : Assignment :=
  fun index =>
    if index < depth then
      if index ∈ indices then .bvar (indices.idxOf index)
      else .bvar (dependencies + ambient)
    else .bvar (dependencies + (index - depth))

/-- Recover a scoped value by inverse occurrence substitution, then check
that its forward instantiation is exactly the supplied term. This rejects
dependence on an unselected local binder. -/
def recoverValue? (dependencies : List TypeExpr) (ambient depth : Nat)
    (arguments : List Pattern) (target : Pattern) : Option ContextualValue := do
  if !(target.isWellScopedAt (depth + ambient)) then none else
  let indices ← variableSpine? depth arguments
  if indices.length != dependencies.length then none else
  let value : ContextualValue :=
    { dependencies, ambient,
      body := substitute (recoveryAssignment depth dependencies.length ambient indices) target }
  if instantiateValue? value ambient depth arguments == some target then some value else none

/-- Recovery is checked against the exact forward occurrence substitution.
In particular, every accepted repeated occurrence instantiates to the
original supplied value in its own local context. -/
theorem recoverValue?_forward (dependencies : List TypeExpr) (ambient depth : Nat)
    (arguments : List Pattern) (target : Pattern) (value : ContextualValue)
    (h : recoverValue? dependencies ambient depth arguments target = some value) :
    instantiateValue? value ambient depth arguments = some target := by
  unfold recoverValue? at h
  split at h <;> try cases h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  rcases h with ⟨indices, hindices, h⟩
  split at h <;> try cases h
  split at h <;> cases h
  simp only [beq_iff_eq] at *
  assumption

/-- Successful recovery retains the exact declared dependency context and
caller ambient context rather than deriving either from an occurrence depth. -/
theorem recoverValue?_context (dependencies : List TypeExpr) (ambient depth : Nat)
    (arguments : List Pattern) (target : Pattern) (value : ContextualValue)
    (h : recoverValue? dependencies ambient depth arguments target = some value) :
    value.dependencies = dependencies ∧ value.ambient = ambient := by
  unfold recoverValue? at h
  split at h <;> try cases h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  rcases h with ⟨indices, hindices, h⟩
  split at h <;> try cases h
  split at h <;> cases h
  exact ⟨rfl, rfl⟩

/-- Actual occurrence-depth lookup at every suffix of the current authored
address. This is a structural invariant, not a matching or permission judgment. -/
def DepthCoherent (rule : RewriteRule) (site : RulePatternSite) (path : List Nat)
    (depth : Nat) (schema : Pattern) : Prop :=
  ∀ suffix, RuleBinding.occurrenceDepthAtSite? rule site (path ++ suffix) =
    RuleBinding.occurrenceDepthAt? schema suffix depth

theorem depthCoherent_of_site (rule : RewriteRule) (site : RulePatternSite) (schema : Pattern)
    (depth : Nat) (patternFound : RuleBinding.sitePattern? rule site = some schema)
    (depthFound : RuleBinding.siteBinderDepth? rule site = some depth) :
    DepthCoherent rule site [] depth schema := by
  intro suffix
  simp only [List.nil_append, RuleBinding.occurrenceDepthAtSite?, patternFound, depthFound,
    Option.bind_eq_bind, Option.bind_some]

theorem depthCoherent_left (rule : RewriteRule) : DepthCoherent rule .left [] 0 rule.left := by
  intro suffix
  rfl

theorem depthCoherent_right (rule : RewriteRule) : DepthCoherent rule .right [] 0 rule.right := by
  intro suffix
  rfl

theorem DepthCoherent.fvar {rule : RewriteRule} {site : RulePatternSite}
    {path : List Nat} {depth : Nat} {name : String}
    (coherent : DepthCoherent rule site path depth (.fvar name)) :
    RuleBinding.occurrenceDepthAtSite? rule site path = some depth := by
  simpa only [List.append_nil, RuleBinding.occurrenceDepthAt?] using coherent []

theorem DepthCoherent.lambda {rule : RewriteRule} {site : RulePatternSite}
    {path : List Nat} {depth : Nat} {display : Option String} {body : Pattern}
    (coherent : DepthCoherent rule site path depth (.lambda display body)) :
    DepthCoherent rule site (path ++ [0]) (depth + 1) body := by
  intro suffix
  simpa only [List.append_assoc, List.singleton_append, RuleBinding.occurrenceDepthAt?] using coherent (0 :: suffix)

theorem DepthCoherent.multiLambda {rule : RewriteRule} {site : RulePatternSite}
    {path : List Nat} {depth arity : Nat} {display : List String} {body : Pattern}
    (coherent : DepthCoherent rule site path depth (.multiLambda arity display body)) :
    DepthCoherent rule site (path ++ [0]) (depth + arity) body := by
  intro suffix
  simpa only [List.append_assoc, List.singleton_append, RuleBinding.occurrenceDepthAt?] using coherent (0 :: suffix)

theorem DepthCoherent.substitutionBody {rule : RewriteRule} {site : RulePatternSite}
    {path : List Nat} {depth : Nat} {body replacement : Pattern}
    (coherent : DepthCoherent rule site path depth (.subst body replacement)) :
    DepthCoherent rule site (path ++ [0]) (depth + 1) body := by
  intro suffix
  simpa only [List.append_assoc, List.singleton_append, RuleBinding.occurrenceDepthAt?] using coherent (0 :: suffix)

theorem DepthCoherent.substitutionReplacement {rule : RewriteRule} {site : RulePatternSite}
    {path : List Nat} {depth : Nat} {body replacement : Pattern}
    (coherent : DepthCoherent rule site path depth (.subst body replacement)) :
    DepthCoherent rule site (path ++ [1]) depth replacement := by
  intro suffix
  simpa only [List.append_assoc, List.singleton_append, RuleBinding.occurrenceDepthAt?] using coherent (1 :: suffix)

theorem DepthCoherent.constructorChild {rule : RewriteRule} {site : RulePatternSite}
    {path : List Nat} {depth index : Nat} {label : String} {patterns : List Pattern} {pattern : Pattern}
    (coherent : DepthCoherent rule site path depth (.apply label patterns))
    (selected : patterns[index]? = some pattern) :
    DepthCoherent rule site (path ++ [index]) depth pattern := by
  intro suffix
  simpa only [List.append_assoc, List.singleton_append, RuleBinding.occurrenceDepthAt?, selected,
    Option.bind_some] using coherent (index :: suffix)

theorem DepthCoherent.collectionChild {rule : RewriteRule} {site : RulePatternSite}
    {path : List Nat} {depth index : Nat} {kind : CollType} {patterns : List Pattern} {rest : Option String} {pattern : Pattern}
    (coherent : DepthCoherent rule site path depth (.collection kind patterns rest))
    (selected : patterns[index]? = some pattern) :
    DepthCoherent rule site (path ++ [index]) depth pattern := by
  intro suffix
  have within := (List.getElem?_eq_some_iff.mp selected).1
  simpa only [List.append_assoc, List.singleton_append, RuleBinding.occurrenceDepthAt?, if_pos within,
    selected, Option.bind_some] using coherent (index :: suffix)

theorem DepthCoherent.collectionRest {rule : RewriteRule} {site : RulePatternSite}
    {path : List Nat} {depth : Nat} {kind : CollType} {patterns : List Pattern} {name : String}
    (coherent : DepthCoherent rule site path depth (.collection kind patterns (some name))) :
    RuleBinding.occurrenceDepthAtSite? rule site (path ++ [patterns.length]) = some depth := by
  simpa only [RuleBinding.occurrenceDepthAt?, lt_self_iff_false, if_false, beq_self_eq_true,
    List.isEmpty_nil, Bool.and_true, Option.isSome_some, if_true] using coherent [patterns.length]

/-- Each cursor index is the physical child address in the authored row. -/
def ArgumentsDepthCoherent (rule : RewriteRule) (site : RulePatternSite) (path : List Nat)
    (depth index : Nat) (patterns : List Pattern) : Prop :=
  ∀ offset pattern, patterns[offset]? = some pattern →
    DepthCoherent rule site (path ++ [index + offset]) depth pattern

theorem ArgumentsDepthCoherent.head {rule : RewriteRule} {site : RulePatternSite}
    {path : List Nat} {depth index : Nat} {first : Pattern} {patterns : List Pattern}
    (coherent : ArgumentsDepthCoherent rule site path depth index (first :: patterns)) :
    DepthCoherent rule site (path ++ [index]) depth first := by
  simpa only [Nat.add_zero] using coherent 0 first rfl

theorem ArgumentsDepthCoherent.tail {rule : RewriteRule} {site : RulePatternSite}
    {path : List Nat} {depth index : Nat} {first : Pattern} {patterns : List Pattern}
    (coherent : ArgumentsDepthCoherent rule site path depth index (first :: patterns)) :
    ArgumentsDepthCoherent rule site path depth (index + 1) patterns := by
  intro offset pattern selected
  have found := coherent (offset + 1) pattern (by simpa using selected)
  simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using found

theorem DepthCoherent.constructorArguments {rule : RewriteRule} {site : RulePatternSite}
    {path : List Nat} {depth : Nat} {label : String} {patterns : List Pattern}
    (coherent : DepthCoherent rule site path depth (.apply label patterns)) :
    ArgumentsDepthCoherent rule site path depth 0 patterns := by
  intro offset pattern selected
  simpa only [Nat.zero_add] using coherent.constructorChild selected

theorem DepthCoherent.collectionArguments {rule : RewriteRule} {site : RulePatternSite}
    {path : List Nat} {depth : Nat} {kind : CollType} {patterns : List Pattern} {rest : Option String}
    (coherent : DepthCoherent rule site path depth (.collection kind patterns rest)) :
    ArgumentsDepthCoherent rule site path depth 0 patterns := by
  intro offset pattern selected
  simpa only [Nat.zero_add] using coherent.collectionChild selected

end Mettapedia.OSLF.MeTTaIL.RuleBinding

/-! ## Free-name coverage of the original operations -/

namespace Mettapedia.OSLF.MeTTaIL.RuleBinding

open Mettapedia.OSLF.MeTTaIL.Syntax
open ContextSubstitution

def patternsFreeWithin (footprint : List String) (patterns : List Pattern) : Prop :=
  ∀ pattern ∈ patterns, ∀ name ∈ pattern.freeFvarNames, name ∈ footprint
theorem recovery_free_names (dependencies depth ambient : Nat) (indices : List Nat) (target : Pattern) :
    (ContextSubstitution.substitute (recoveryAssignment depth dependencies ambient indices) target).freeFvarNames =
      target.freeFvarNames := by
  apply substitute_free_names
  intro index
  simp only [recoveryAssignment]
  split
  · split <;> simp only [Pattern.freeFvarNames]
  · simp only [Pattern.freeFvarNames]

theorem recovered_body_free_names (dependencies : List TypeExpr) (ambient depth : Nat)
    (arguments : List Pattern) (target : Pattern) (value : ContextualValue)
    (recovered : recoverValue? dependencies ambient depth arguments target = some value) :
    value.body.freeFvarNames = target.freeFvarNames := by
  unfold recoverValue? at recovered
  split at recovered <;> try cases recovered
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at recovered
  rcases recovered with ⟨indices, _found, recovered⟩
  split at recovered <;> try cases recovered
  split at recovered <;> cases recovered
  exact recovery_free_names dependencies.length depth ambient indices target
theorem occurrence_assignment_free_within (footprint : List String)
    (dependencies depth : Nat) (arguments : List Pattern)
    (covered : patternsFreeWithin footprint arguments) :
    ∀ index, ∀ name ∈ (occurrenceAssignment dependencies depth arguments index).freeFvarNames,
      name ∈ footprint := by
  intro index name occurs
  simp only [occurrenceAssignment] at occurs
  split at occurs
  · rw [List.getD_eq_getElem?_getD] at occurs
    cases found : arguments[index]? with
    | none => simp only [found, Option.getD_none, Pattern.freeFvarNames, List.not_mem_nil] at occurs
    | some argument =>
        simp only [found, Option.getD_some] at occurs
        exact covered argument (List.mem_of_getElem? found) name occurs
  · simp only [Pattern.freeFvarNames, List.not_mem_nil] at occurs

theorem instantiate_value_free_within (footprint : List String)
    (value : ContextualValue) (ambient depth : Nat) (arguments : List Pattern) (result : Pattern)
    (body : ∀ name ∈ value.body.freeFvarNames, name ∈ footprint)
    (inputs : patternsFreeWithin footprint arguments)
    (success : instantiateValue? value ambient depth arguments = some result) :
    ∀ name ∈ result.freeFvarNames, name ∈ footprint := by
  unfold instantiateValue? at success
  split at success <;> try cases success
  split at success <;> try cases success
  split at success <;> try cases success
  split at success <;> try cases success
  dsimp only at success
  split at success <;> cases success
  exact substitute_free_within footprint value.body _
    (occurrence_assignment_free_within footprint value.dependencies.length depth arguments inputs) body

#print axioms Mettapedia.OSLF.MeTTaIL.RuleBinding.patternsFreeWithin
#print axioms Mettapedia.OSLF.MeTTaIL.RuleBinding.recovery_free_names
#print axioms Mettapedia.OSLF.MeTTaIL.RuleBinding.recovered_body_free_names
#print axioms Mettapedia.OSLF.MeTTaIL.RuleBinding.occurrence_assignment_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.RuleBinding.instantiate_value_free_within

end Mettapedia.OSLF.MeTTaIL.RuleBinding


namespace Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.Syntax
set_option autoImplicit false

/-- The declared object-binder context of an original rule endpoint. -/
def siteBinders? (rule : RewriteRule) : RulePatternSite → Option (List TypeExpr)
  | .left | .right => some []
  | .premise index quantifiers argument => do
      let premise ← rule.premises[index]?
      match ← quantifiedBody? quantifiers premise with
      | .freshness _ => if argument == 0 then some [] else none
      | .congruence _ _ => if argument < 2 then some [] else none
      | .scopedStep step => if argument < 2 then some step.binders else none
      | .relationQuery _ args => if argument < args.length then some [] else none
      | .forAll _ _ _ => none

/-- Sorting retains precisely the context counted by occurrence admission. -/
theorem siteBinders?_length (rule : RewriteRule) (site : RulePatternSite) :
    (siteBinders? rule site).map List.length = siteBinderDepth? rule site := by
  cases site with
  | left => rfl
  | right => rfl
  | premise index quantifiers argument =>
      simp only [siteBinders?, siteBinderDepth?]
      cases found : rule.premises[index]? with
      | none => rfl
      | some premise =>
          cases body : quantifiedBody? quantifiers premise with
          | none => simp [body]
          | some inner =>
              cases inner <;> simp [body]

/-- Both sides of an actual scoped premise retain its complete declaration. -/
theorem siteBinders?_scopedStep (rule : RewriteRule) (index : Nat)
    (step : ScopedStepPremise)
    (found : rule.premises[index]? = some (.scopedStep step))
    (argument : Nat) (valid : argument < 2) :
    siteBinders? rule (.premise index 0 argument) = some step.binders := by
  simp [siteBinders?, found, quantifiedBody?, valid]

end Mettapedia.OSLF.MeTTaIL.RuleBinding

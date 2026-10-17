import Mettapedia.GSLT.LanguageDef.MacroTemplateNames

/-!
# Definition-site ports and caller shadowing

Acquisition resolves a namespaced native binding in the definition environment
and stores its declaration identity under a separate alias. Calling through
that alias resolves the saved identity even when the caller shadows the
original spelling. Independent alias freshness is needed: shadowing the alias
itself would redirect the lookup, as the negative control demonstrates.

This is the binding-resolver contract for native-symbol ports. It does not
prove C pointer representation, compiler preprocessing, source-to-C printing,
native namespace admission or arbitrary program effects.
-/

namespace Mettapedia.GSLT.LanguageDef.MacroDefinitionPorts

open MacroTemplateNames (Namespace)

set_option autoImplicit false

abbrev Key := Namespace × String
abbrev Environment := List (Key × Nat)

def lookup : Environment → Key → Option Nat
  | [], _ => none
  | (bound, declaration) :: rest, key =>
      if bound = key then some declaration else lookup rest key

structure Port where
  printedKey : Key
  declaration : Nat
  deriving DecidableEq, Repr

def acquire (environment : Environment) (native ownedKey : Key) : Option Port :=
  (lookup environment native).map (fun declaration => ⟨ownedKey, declaration⟩)

def install (port : Port) (environment : Environment) : Environment :=
  (port.printedKey, port.declaration) :: environment

def keys (environment : Environment) : List Key := environment.map Prod.fst

/-- Definition keys must be unique; every used DefinitionRef must resolve
in that independently supplied definition registry. -/
def admitReferences (definitions : Environment) (references : List Key) : Bool :=
  decide ((keys definitions).Nodup ∧
    ∀ reference ∈ references, (lookup definitions reference).isSome = true)

theorem admitted_reference_resolves (definitions : Environment) (references : List Key)
    (checked : admitReferences definitions references = true)
    (reference : Key) (used : reference ∈ references) :
    ∃ declaration, lookup definitions reference = some declaration := by
  have admission : (keys definitions).Nodup ∧
      ∀ reference ∈ references, (lookup definitions reference).isSome = true := by
    simpa [admitReferences] using checked
  have found := admission.2 reference used
  cases resolved : lookup definitions reference with
  | none => simp [resolved] at found
  | some declaration => exact ⟨declaration, rfl⟩

theorem acquire_reflects {environment : Environment} {native ownedKey : Key} {port : Port}
    (acquired : acquire environment native ownedKey = some port) :
    port.printedKey = ownedKey ∧ lookup environment native = some port.declaration := by
  unfold acquire at acquired
  cases found : lookup environment native with
  | none => simp [found] at acquired
  | some declaration =>
      simp only [found, Option.map_some, Option.some.injEq] at acquired
      subst port
      exact ⟨rfl, rfl⟩

theorem acquire_complete {environment : Environment} {native ownedKey : Key} {declaration : Nat}
    (resolved : lookup environment native = some declaration) :
    acquire environment native ownedKey = some ⟨ownedKey, declaration⟩ := by
  simp [acquire, resolved]

theorem acquire_missing {environment : Environment} {native ownedKey : Key}
    (missing : lookup environment native = none) :
    acquire environment native ownedKey = none := by
  simp [acquire, missing]

theorem lookup_install (port : Port) (environment : Environment) :
    lookup (install port environment) port.printedKey = some port.declaration := by
  simp [install, lookup]

theorem lookup_fresh_prefix (caller environment : Environment) (key : Key)
    (fresh : key ∉ keys caller) :
    lookup (caller ++ environment) key = lookup environment key := by
  induction caller with
  | nil => rfl
  | cons binding rest ih =>
      rcases binding with ⟨bound, declaration⟩
      have parts : key ≠ bound ∧ key ∉ keys rest := by
        simpa [keys] using fresh
      simp [lookup, Ne.symm parts.1, ih parts.2]

theorem caller_preserves_port (caller environment : Environment) (port : Port)
    (fresh : port.printedKey ∉ keys caller) :
    lookup (caller ++ install port environment) port.printedKey = some port.declaration := by
  rw [lookup_fresh_prefix caller _ port.printedKey fresh, lookup_install]

/-- The caller may shadow the original native key. It cannot redirect an
acquired alias whose name is fresh in that caller frame. -/
theorem acquired_port_preserves_definition {definition caller residual : Environment}
    {native ownedKey : Key} {port : Port}
    (acquired : acquire definition native ownedKey = some port)
    (fresh : ownedKey ∉ keys caller) :
    lookup (caller ++ install port residual) ownedKey = lookup definition native := by
  have reflected := acquire_reflects acquired
  have actualFresh : port.printedKey ∉ keys caller := reflected.1 ▸ fresh
  have saved := caller_preserves_port caller residual port actualFresh
  simpa only [reflected.1, reflected.2] using saved

def admitAlias (caller : Environment) (ownedKey : Key) : Bool :=
  decide (ownedKey ∉ keys caller)

theorem admitted_port_preserves_definition {definition caller residual : Environment}
    {native ownedKey : Key} {port : Port}
    (acquired : acquire definition native ownedKey = some port)
    (checked : admitAlias caller ownedKey = true) :
    lookup (caller ++ install port residual) ownedKey = lookup definition native := by
  apply acquired_port_preserves_definition acquired
  simpa [admitAlias] using checked

def original : Key := (.ordinary, "provider")
def owned : Key := (.ordinary, "cesta_owned_provider")
def global : Environment := [(original, 17)]
def shadowingCaller : Environment := [(original, 42)]

example : acquire global original owned = some ⟨owned, 17⟩ := by decide
example : lookup (shadowingCaller ++ install ⟨owned, 17⟩ []) owned = some 17 := by decide
example : lookup shadowingCaller original = some 42 := by decide
example : admitAlias [(owned, 42)] owned = false := by decide
example : lookup ([(owned, 42)] ++ install ⟨owned, 17⟩ []) owned = some 42 := by decide

#print axioms acquire_reflects
#print axioms lookup_fresh_prefix
#print axioms acquired_port_preserves_definition
#print axioms admitted_port_preserves_definition
#print axioms admitted_reference_resolves

end Mettapedia.GSLT.LanguageDef.MacroDefinitionPorts

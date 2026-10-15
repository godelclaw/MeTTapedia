import Mettapedia.OSLF.NativeTypes.Runtime.Description
import Mettapedia.OSLF.NativeTypes.Runtime.Interface

open Mettapedia.OSLF.Framework

/-!
# Invariant atomic observations in the public native checker

An atomic observation supplies its equation-invariant meaning, executable
test and completion proof. Adding these observations retains the original
generated constructor leaves and the original operational backend. Both
kinds of leaves use the same compositional checker and admission rules.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Runtime.Atoms

open Mettapedia.OSLF.NativeTypes.Runtime.Description Mettapedia.OSLF.NativeTypes.Decision.Reference.Core
open Mettapedia.OSLF.NativeTypes.Decision.Admission

def tests (driver : Driver) {Atom : Type}
    (observations : Atom → Test driver.system driver.admitted) :
    Sum driver.Leaf Atom → Test driver.system driver.admitted
  | .inl leaf => driver.tests leaf
  | .inr atom => observations atom

def admission (driver : Driver) {Atom : Type} (atomic : LeafAdmission Atom) :
    LeafAdmission (Sum driver.Leaf Atom) where
  admitted
    | .inl leaf => driver.leafAdmission.admitted leaf
    | .inr atom => atomic.admitted atom
  probe
    | .inl leaf => driver.leafAdmission.probe leaf
    | .inr atom => atomic.probe atom
  exact leaf := by
    cases leaf with
    | inl leaf => exact driver.leafAdmission.exact leaf
    | inr atom => exact atomic.exact atom

def extend (driver : Driver) {Atom : Type}
    (observations : Atom → Test driver.system driver.admitted)
    (atomic : LeafAdmission Atom) : Driver where
  generated := driver.generated
  profile := driver.profile
  expected := driver.expected
  system := driver.system
  admitted := driver.admitted
  render := driver.render
  render_injective := driver.render_injective
  decode := driver.decode
  decode_complete := driver.decode_complete
  backend := driver.backend
  Leaf := Sum driver.Leaf Atom
  tests := tests driver observations
  leafAdmission := admission driver atomic
  lookup name := (driver.lookup name).map Sum.inl

def structural {Leaf Atom : Type} : Formula Leaf → Formula (Sum Leaf Atom)
  | .atom leaf => .atom (.inl leaf)
  | .top => .top
  | .bottom => .bottom
  | .conj first second => .conj (structural first) (structural second)
  | .disj first second => .disj (structural first) (structural second)
  | .neg formula => .neg (structural formula)
  | .imp first second => .imp (structural first) (structural second)
  | .possibility formula => .possibility (structural formula)
  | .outgoingUniversal formula => .outgoingUniversal (structural formula)

theorem structural_denotation (driver : Driver) {Atom : Type}
    (observations : Atom → Test driver.system driver.admitted)
    (formula : driver.Formula) :
    denotation (tests driver observations) (structural formula) =
      denotation driver.tests formula := by
  induction formula with
  | atom leaf => rfl
  | top => rfl
  | bottom => rfl
  | conj first second firstIH secondIH =>
    simp only [structural, denotation, firstIH, secondIH]
  | disj first second firstIH secondIH =>
    simp only [structural, denotation, firstIH, secondIH]
  | neg formula ih => simp only [structural, denotation, ih]
  | imp first second firstIH secondIH =>
    simp only [structural, denotation, firstIH, secondIH]
  | possibility formula ih => simp only [structural, denotation, ih]
  | outgoingUniversal formula ih => simp only [structural, denotation, ih]

theorem structural_meaning (driver : Driver) {Atom : Type}
    (observations : Atom → Test driver.system driver.admitted)
    (atomic : LeafAdmission Atom) (formula : driver.Formula)
    (raw : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) :
    Meaning (extend driver observations atomic) (structural formula) raw ↔
      Meaning driver formula raw := by
  change (∃ source, driver.admitted source ∧ driver.render source = raw ∧
    denotation (tests driver observations) (structural formula) source) ↔ _
  rw [structural_denotation]
  rfl

theorem atomic_meaning (driver : Driver) {Atom : Type}
    (observations : Atom → Test driver.system driver.admitted)
    (atomic : LeafAdmission Atom) (atom : Atom)
    (raw : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) :
    Meaning (extend driver observations atomic) (.atom (.inr atom)) raw ↔
      ∃ source, driver.admitted source ∧ driver.render source = raw ∧
        (observations atom).predicate source := Iff.rfl

theorem structural_formation (driver : Driver) {Atom : Type}
    (atomic : LeafAdmission Atom) (formula : driver.Formula) :
    Formed driver.generated.logicFragment (admission driver atomic) (structural formula) ↔
      Formed driver.generated.logicFragment driver.leafAdmission formula := by
  rw [← firstRefusal_exact, ← firstRefusal_exact]
  have same : firstRefusal driver.generated.logicFragment (admission driver atomic) (structural formula) =
      firstRefusal driver.generated.logicFragment driver.leafAdmission formula := by
    induction formula with
    | atom leaf => rfl
    | top => rfl
    | bottom => rfl
    | conj first second firstIH secondIH =>
      simp only [structural, firstRefusal, firstIH, secondIH]
    | disj first second firstIH secondIH =>
      simp only [structural, firstRefusal, firstIH, secondIH]
    | neg formula ih => simp only [structural, firstRefusal, ih]
    | imp first second firstIH secondIH =>
      simp only [structural, firstRefusal, firstIH, secondIH]
    | possibility formula ih => simp only [structural, firstRefusal, ih]
    | outgoingUniversal formula ih => simp only [structural, firstRefusal, ih]
  rw [same]

/-- A decidable atomic observation retains its independently specified,
equation-invariant native meaning. Its evaluation is one primitive job. -/
structure Observation (driver : Driver) where
  predicate : GSLTTypeSynthesis.EquationPredicate driver.system
  accepts : driver.system.Term → Bool
  exact : ∀ source, accepts source = true ↔ predicate source

def Observation.test {driver : Driver} (observation : Observation driver) :
    Test driver.system driver.admitted :=
  Test.ofBoolean observation.predicate observation.accepts observation.exact

def Observation.leaf {driver : Driver} (observation : Observation driver) :
    Mettapedia.OSLF.NativeTypes.Decision.Machine.LeafBackend driver.system driver.admitted :=
  Mettapedia.OSLF.NativeTypes.Decision.Machine.LeafBackend.ofBoolean
    observation.predicate observation.accepts observation.exact

def installed (base : Mettapedia.OSLF.NativeTypes.Runtime.Installed) {Atom : Type}
    (observations : Atom → Observation base.native) (atomic : LeafAdmission Atom) :
    Mettapedia.OSLF.NativeTypes.Runtime.Installed where
  native := extend base.native (fun atom => (observations atom).test) atomic
  runtime := {
    cursor := base.runtime.cursor
    leaves := fun leaf => match leaf with
      | .inl leaf => base.runtime.leaves leaf
      | .inr atom => (observations atom).leaf
    leaf_meaning := by
      intro leaf
      cases leaf with
      | inl leaf => exact base.runtime.leaf_meaning leaf
      | inr atom => rfl}

theorem installed_structural_meaning (base : Mettapedia.OSLF.NativeTypes.Runtime.Installed) {Atom : Type}
    (observations : Atom → Observation base.native) (atomic : LeafAdmission Atom)
    (formula : base.native.Formula) (raw : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) :
    Meaning (installed base observations atomic).native (structural formula) raw ↔
      Meaning base.native formula raw :=
  structural_meaning base.native (fun atom => (observations atom).test) atomic formula raw

end Mettapedia.OSLF.NativeTypes.Runtime.Atoms

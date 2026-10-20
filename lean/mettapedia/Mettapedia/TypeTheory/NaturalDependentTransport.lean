import Mettapedia.TypeTheory.NaturalAlgebra

/-!
# Dependent elimination across natural-number representations

A representation equivalence preserving zero and successor transports dependent
elimination, not just nondependent iteration. The beta laws below are semantic
equalities: a representation selected using choice does not thereby acquire a
computational decoder, nor do these equalities extend an object language's
definitional conversion rules.

The vector application uses the existing indexed-polynomial fixed point. Its
negative control shows why a quotient observation such as parity does not in
general transport length-indexed families.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.NaturalDependentTransport

universe u v w

variable {Carrier : Type u}

private theorem transport_section {Index : Sort u} (family : Index → Sort v)
    (dependentFunction : ∀ index, family index) {first second : Index} (same : first = second) :
    same ▸ dependentFunction first = dependentFunction second := by
  cases same
  rfl

private theorem transport_reindexed {Index : Sort u} (family : Index → Sort v)
    (index : Nat → Index) (dependentFunction : ∀ n, family (index n))
    {first second : Nat} (same : first = second) :
    congrArg index same ▸ dependentFunction first = dependentFunction second := by
  cases same
  rfl

private theorem transport_cancel {Index : Sort u} (family : Index → Sort v)
    {first second : Index} (same : first = second) (value : family second) :
    same ▸ same.symm ▸ value = value := by
  cases same
  rfl

/-- Dependent recursion along the forward representation. Constructor equations
transport values into the fibres expected by the next recursive call. -/
def alongNaturals (representation : Nat ≃ Carrier)
    (zero : Carrier) (successor : Carrier → Carrier)
    (zero_eq : representation 0 = zero)
    (successor_eq : ∀ n, representation (n + 1) = successor (representation n))
    (family : Carrier → Sort v) (atZero : family zero)
    (atSuccessor : ∀ value, family value → family (successor value)) :
    ∀ n, family (representation n) :=
  Nat.rec (zero_eq.symm ▸ atZero)
    (fun n previous => (successor_eq n).symm ▸ atSuccessor (representation n) previous)

/-- A dependent eliminator over all represented naturals. It is computational
exactly when the supplied equivalence and branch operations are computational. -/
def eliminate (representation : Nat ≃ Carrier)
    (zero : Carrier) (successor : Carrier → Carrier)
    (zero_eq : representation 0 = zero)
    (successor_eq : ∀ n, representation (n + 1) = successor (representation n))
    (family : Carrier → Sort v) (atZero : family zero)
    (atSuccessor : ∀ value, family value → family (successor value))
    (value : Carrier) : family value :=
  representation.apply_symm_apply value ▸
    alongNaturals representation zero successor zero_eq successor_eq
      family atZero atSuccessor (representation.symm value)

@[simp] theorem eliminate_representation (representation : Nat ≃ Carrier)
    (zero : Carrier) (successor : Carrier → Carrier)
    (zero_eq : representation 0 = zero)
    (successor_eq : ∀ n, representation (n + 1) = successor (representation n))
    (family : Carrier → Sort v) (atZero : family zero)
    (atSuccessor : ∀ value, family value → family (successor value)) (n : Nat) :
    eliminate representation zero successor zero_eq successor_eq family atZero atSuccessor
      (representation n) =
    alongNaturals representation zero successor zero_eq successor_eq family atZero atSuccessor n := by
  exact transport_reindexed family representation
    (alongNaturals representation zero successor zero_eq successor_eq family atZero atSuccessor)
    (representation.symm_apply_apply n)

@[simp] theorem eliminate_zero (representation : Nat ≃ Carrier)
    (zero : Carrier) (successor : Carrier → Carrier)
    (zero_eq : representation 0 = zero)
    (successor_eq : ∀ n, representation (n + 1) = successor (representation n))
    (family : Carrier → Sort v) (atZero : family zero)
    (atSuccessor : ∀ value, family value → family (successor value)) :
    eliminate representation zero successor zero_eq successor_eq family atZero atSuccessor zero =
      atZero := by
  subst zero
  rw [eliminate_representation]
  rfl

@[simp] theorem eliminate_successor (representation : Nat ≃ Carrier)
    (zero : Carrier) (successor : Carrier → Carrier)
    (zero_eq : representation 0 = zero)
    (successor_eq : ∀ n, representation (n + 1) = successor (representation n))
    (family : Carrier → Sort v) (atZero : family zero)
    (atSuccessor : ∀ value, family value → family (successor value)) (value : Carrier) :
    eliminate representation zero successor zero_eq successor_eq family atZero atSuccessor
      (successor value) =
    atSuccessor value
      (eliminate representation zero successor zero_eq successor_eq family atZero atSuccessor value) := by
  obtain ⟨n, rfl⟩ := representation.surjective value
  have transported := transport_section family
    (eliminate representation zero successor zero_eq successor_eq family atZero atSuccessor)
    (successor_eq n)
  rw [eliminate_representation] at transported
  rw [← transported, eliminate_representation]
  exact transport_cancel family (successor_eq n) _

/-- Constructor equations determine the whole dependent section uniquely. -/
theorem eliminate_unique (representation : Nat ≃ Carrier)
    (zero : Carrier) (successor : Carrier → Carrier)
    (zero_eq : representation 0 = zero)
    (successor_eq : ∀ n, representation (n + 1) = successor (representation n))
    (family : Carrier → Sort v) (atZero : family zero)
    (atSuccessor : ∀ value, family value → family (successor value))
    (other : ∀ value, family value)
    (other_zero : other zero = atZero)
    (other_successor : ∀ value, other (successor value) = atSuccessor value (other value)) :
    other = eliminate representation zero successor zero_eq successor_eq family atZero atSuccessor := by
  funext value
  obtain ⟨n, rfl⟩ := representation.surjective value
  induction n with
  | zero =>
    have transported := transport_section family other zero_eq
    rw [eliminate_representation]
    unfold alongNaturals
    rw [← other_zero, ← transported]
    cases zero_eq
    rfl
  | succ n hypothesis =>
    rw [successor_eq, other_successor, eliminate_successor, hypothesis]

/-- A fibre map commuting with both branches commutes with dependent elimination.
No injectivity or surjectivity of the fibre map is needed. -/
theorem eliminate_naturality (representation : Nat ≃ Carrier)
    (zero : Carrier) (successor : Carrier → Carrier)
    (zero_eq : representation 0 = zero)
    (successor_eq : ∀ n, representation (n + 1) = successor (representation n))
    (first : Carrier → Sort v) (second : Carrier → Sort w)
    (firstZero : first zero) (firstSuccessor : ∀ value, first value → first (successor value))
    (secondZero : second zero) (secondSuccessor : ∀ value, second value → second (successor value))
    (map : ∀ value, first value → second value)
    (map_zero : map zero firstZero = secondZero)
    (map_successor : ∀ value result,
      map (successor value) (firstSuccessor value result) =
        secondSuccessor value (map value result)) (value : Carrier) :
    map value
      (eliminate representation zero successor zero_eq successor_eq
        first firstZero firstSuccessor value) =
    eliminate representation zero successor zero_eq successor_eq
      second secondZero secondSuccessor value := by
  have uniqueness := eliminate_unique representation zero successor zero_eq successor_eq
    second secondZero secondSuccessor
    (fun value => map value (eliminate representation zero successor zero_eq successor_eq
      first firstZero firstSuccessor value))
    (by simpa using map_zero)
    (by
      intro value
      simpa using (map_successor value
        (eliminate representation zero successor zero_eq successor_eq first firstZero firstSuccessor value)))
  exact congrFun uniqueness value

open NaturalAlgebra

/-- Dependent elimination specialized to a zero/successor algebra isomorphism. -/
def algebraEliminate {algebra : Algebra Carrier} (representation : Iso natAlgebra algebra)
    (family : Carrier → Sort v) (atZero : family algebra.zero)
    (atSuccessor : ∀ value, family value → family (algebra.succ value)) :
    ∀ value, family value :=
  eliminate representation.toEquiv algebra.zero algebra.succ representation.map_zero
    representation.map_succ family atZero atSuccessor

@[simp] theorem algebraEliminate_zero {algebra : Algebra Carrier}
    (representation : Iso natAlgebra algebra)
    (family : Carrier → Sort v) (atZero : family algebra.zero)
    (atSuccessor : ∀ value, family value → family (algebra.succ value)) :
    algebraEliminate representation family atZero atSuccessor algebra.zero = atZero :=
  eliminate_zero _ _ _ _ _ _ _ _

@[simp] theorem algebraEliminate_successor {algebra : Algebra Carrier}
    (representation : Iso natAlgebra algebra)
    (family : Carrier → Sort v) (atZero : family algebra.zero)
    (atSuccessor : ∀ value, family value → family (algebra.succ value)) (value : Carrier) :
    algebraEliminate representation family atZero atSuccessor (algebra.succ value) =
      atSuccessor value (algebraEliminate representation family atZero atSuccessor value) :=
  eliminate_successor _ _ _ _ _ _ _ _ _

/-- Change of natural-number representation preserves the dependent recursor,
including its branch data. The casts are the constructor-preservation laws of
the algebra isomorphism, not new object-language conversion rules. -/
theorem algebraEliminate_iso {Other : Type w}
    {source : Algebra Carrier} {target : Algebra Other}
    (representation : Iso natAlgebra source) (route : Iso source target)
    (family : Other → Sort v) (atZero : family target.zero)
    (atSuccessor : ∀ value, family value → family (target.succ value)) (value : Carrier) :
    algebraEliminate representation (fun value => family (route.toEquiv value))
      (route.map_zero.symm ▸ atZero)
      (fun value result => (route.map_succ value).symm ▸
        atSuccessor (route.toEquiv value) result) value =
    algebraEliminate (representation.trans route) family atZero atSuccessor
      (route.toEquiv value) := by
  have zeroCase :
      algebraEliminate (representation.trans route) family atZero atSuccessor
        (route.toEquiv source.zero) = route.map_zero.symm ▸ atZero := by
    have equation := transport_section family
      (algebraEliminate (representation.trans route) family atZero atSuccessor)
      route.map_zero.symm
    rw [algebraEliminate_zero] at equation
    exact equation.symm
  have successorCase : ∀ value,
      algebraEliminate (representation.trans route) family atZero atSuccessor
        (route.toEquiv (source.succ value)) =
      (route.map_succ value).symm ▸ atSuccessor (route.toEquiv value)
        (algebraEliminate (representation.trans route) family atZero atSuccessor
          (route.toEquiv value)) := by
    intro value
    have equation := transport_section family
      (algebraEliminate (representation.trans route) family atZero atSuccessor)
      (route.map_succ value).symm
    rw [algebraEliminate_successor] at equation
    exact equation.symm
  exact (congrFun (eliminate_unique representation.toEquiv source.zero source.succ
    representation.map_zero representation.map_succ
    (fun value => family (route.toEquiv value)) (route.map_zero.symm ▸ atZero)
    (fun value result => (route.map_succ value).symm ▸ atSuccessor (route.toEquiv value) result)
    (fun value => algebraEliminate (representation.trans route) family atZero atSuccessor
      (route.toEquiv value)) zeroCase successorCase) value).symm

end Mettapedia.TypeTheory.NaturalDependentTransport

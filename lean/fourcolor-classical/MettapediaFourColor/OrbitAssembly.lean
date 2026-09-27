import MettapediaFourColor.ClassicalAssembly
import MettapediaFourColor.Orbit10.Coverage

/-!
# Classical assembly consuming the shared arity-ten presentation

The arity-ten coverage theorem is reconstructed from the pinned reference
presentation with its periodic hubcap certificate shared. Reducibility and
the other six arities remain explicit hypotheses. The reduction argument
still consumes the GSLT colouring-witness reconstruction.
-/

namespace FourColor.OrbitAssembly

/-- Arity ten is discharged by the presentation using the periodic certificate. -/
theorem no_minimalCounterExample_of_checks (hred : Reducibility)
    (e5 : ExcludedArity (RedpartSound theRedpart) 5)
    (e6 : ExcludedArity (RedpartSound theRedpart) 6)
    (e7 : ExcludedArity (RedpartSound theRedpart) 7)
    (e8 : ExcludedArity (RedpartSound theRedpart) 8)
    (e9 : ExcludedArity (RedpartSound theRedpart) 9)
    (e11 : ExcludedArity (RedpartSound theRedpart) 11)
    {D : Type} [Finite D] (G : Hypermap D) : ¬ G.MinimalCounterExample :=
  ClassicalAssembly.no_minimalCounterExample_of_checks hred
    e5 e6 e7 e8 e9 Orbit10.exclude10 e11 G

/-- The real-plane conclusion now requires six presentation inputs instead of seven. -/
theorem fourColorTheorem_of_checks (hred : Reducibility)
    (e5 : ExcludedArity (RedpartSound theRedpart) 5)
    (e6 : ExcludedArity (RedpartSound theRedpart) 6)
    (e7 : ExcludedArity (RedpartSound theRedpart) 7)
    (e8 : ExcludedArity (RedpartSound theRedpart) 8)
    (e9 : ExcludedArity (RedpartSound theRedpart) 9)
    (e11 : ExcludedArity (RedpartSound theRedpart) 11) : FourColorTheorem :=
  ClassicalAssembly.fourColorTheorem_of_checks hred
    e5 e6 e7 e8 e9 Orbit10.exclude10 e11

end FourColor.OrbitAssembly

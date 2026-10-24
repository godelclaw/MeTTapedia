import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.Tower
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeConversion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.RussellTarskiBoundary
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.PairSpine
/-!
# A family into a universe is a family into every higher universe

With `A : 𝒰₀` and `F : Π (x : A). 𝒰₀` in context, the dependent function type
`Π (x : A). 𝒰₀` is usable at `Π (x : A). 𝒰₁`: the domains are equal and the
codomain `𝒰₀` is below `𝒰₁`. So `F` itself is typed at `Π (x : A). 𝒰₁`, with no
η-expansion needed, and `F` and its η-expansion `λ x. F x`, equal at
`Π (x : A). 𝒰₀`, are equal at `Π (x : A). 𝒰₁` too. Usable at is not equal to:
the two function types are not equal types (`Below.pi_codomain_raise`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open Mettapedia.TypeTheory.UniverseLevel
open TowerModel

/-- The universes at levels 0 and 1. -/
abbrev universe₀ {n : Nat} : Tm Tower.Head n := .head (.sort Tower.zero)
abbrev universe₁ {n : Nat} : Tm Tower.Head n := .head (.sort (.succ Tower.zero))

/-- `A : 𝒰₀`, then `F : Π (x : A). 𝒰₀`. -/
abbrev familyContext : Ctx Tower.Head 2 :=
  .snoc (.snoc .nil universe₀) (.pi (.var 0) universe₀)

theorem familyContext_formed : CtxFormed Tower.rules familyContext :=
  .snoc (.snoc .nil ⟨_, LevelTower.IsUniverse.sort _, .headType (LevelTower.HeadTyping.sort _)⟩)
    ⟨_, LevelTower.IsUniverse.sort _,
      .piForm (.var 0) (LevelTower.IsUniverse.sort _) (.headType (LevelTower.HeadTyping.sort _))
        (LevelTower.IsUniverse.sort _) (LevelTower.Join.sorts _ _)⟩

/-- The η-expansion of `F` is typed at `Π (x : A). 𝒰₁`. -/
theorem etaExpansion_typed_at_raised_codomain :
    Typed Tower.rules familyContext (.lam (.app (.var 1) (.var 0)))
      (.pi (.var 1) universe₁) := by
  refine .lamIntro (u := .sort (.max Tower.zero (.succ (.succ Tower.zero))))
    (.piForm (.var 1) (.sort _) (.headType (.sort _)) (.sort _) (.sorts _ _)) (.sort _) ?_
  have applied : Typed Tower.rules (.snoc familyContext (.var 1))
      (.app (.var 1) (.var 0)) universe₀ :=
    .appElim (A := .var 2) (B := universe₀) (.var 1) (.var 0)
  exact .cumul applied (fun _ => Nat.le_succ _)

/-- `Π (x : A). 𝒰₀` is usable at `Π (x : A). 𝒰₁`. -/
theorem family_types_below :
    Below Tower.rules familyContext (.pi (.var 1) universe₀) (.pi (.var 1) universe₁) :=
  .subPi (u := .sort (.max Tower.zero (.succ Tower.zero)))
    (u' := .sort (.max Tower.zero (.succ (.succ Tower.zero)))) (w := .sort Tower.zero)
    (.piForm (.var 1) (LevelTower.IsUniverse.sort _) (.headType (LevelTower.HeadTyping.sort _))
      (LevelTower.IsUniverse.sort _) (LevelTower.Join.sorts _ _)) (LevelTower.IsUniverse.sort _)
    (.piForm (.var 1) (LevelTower.IsUniverse.sort _) (.headType (LevelTower.HeadTyping.sort _))
      (LevelTower.IsUniverse.sort _) (LevelTower.Join.sorts _ _)) (LevelTower.IsUniverse.sort _)
    (.refl (.var 1)) (LevelTower.IsUniverse.sort _) (.subUniv (fun _ => Nat.le_succ _))

/-- `F` itself is typed at `Π (x : A). 𝒰₁`. -/
theorem family_typed_at_raised_codomain :
    Typed Tower.rules familyContext (.var 0) (.pi (.var 1) universe₁) :=
  .sub (.var 0) family_types_below

/-- `F` and its η-expansion are equal at `Π (x : A). 𝒰₀`, and both, and their
equality, hold at `Π (x : A). 𝒰₁`. -/
theorem family_and_eta_expansion_at_raised_codomain :
    Equal Tower.rules familyContext (.var 0) (.lam (.app (.var 1) (.var 0)))
        (.pi (.var 1) universe₀) ∧
      Typed Tower.rules familyContext (.lam (.app (.var 1) (.var 0)))
        (.pi (.var 1) universe₁) ∧
      Typed Tower.rules familyContext (.var 0) (.pi (.var 1) universe₁) ∧
      Equal Tower.rules familyContext (.var 0) (.lam (.app (.var 1) (.var 0)))
        (.pi (.var 1) universe₁) := by
  have equal : Equal Tower.rules familyContext (.var 0) (.lam (.app (.var 1) (.var 0)))
      (.pi (.var 1) universe₀) := by
    have lamTyped : Typed Tower.rules familyContext (.lam (.app (.var 1) (.var 0)))
        (.pi (.var 1) universe₀) :=
      .lamIntro (u := .sort (.max Tower.zero (.succ Tower.zero)))
        (.piForm (.var 1) (.sort _) (.headType (.sort _)) (.sort _) (.sorts _ _)) (.sort _)
        (.appElim (A := .var 2) (B := universe₀) (.var 1) (.var 0))
    have familyTyped : Typed Tower.rules familyContext (.pi (.var 1) universe₀)
        (.head (.sort (.max Tower.zero (.succ Tower.zero)))) :=
      .piForm (.var 1) (LevelTower.IsUniverse.sort _) (.headType (LevelTower.HeadTyping.sort _))
        (LevelTower.IsUniverse.sort _) (LevelTower.Join.sorts _ _)
    have piTyped : Typed Tower.rules (.snoc familyContext (.var 1)) (.pi (.var 2) universe₀)
        (.head (.sort (.max Tower.zero (.succ Tower.zero)))) :=
      familyTyped.weaken (extension := .var 1)
    have beta : Equal Tower.rules (.snoc familyContext (.var 1))
        (.app (.lam (.app (.var 2) (.var 0))) (.var 0)) (.app (.var 1) (.var 0)) universe₀ :=
      .betaPi (A := .var 2) (B := universe₀) (body := .app (.var 2) (.var 0)) (a := .var 0)
        piTyped (LevelTower.IsUniverse.sort _)
        (.appElim (A := .var 3) (B := universe₀) (.var 2) (.var 0)) (.var 0)
    exact .etaPi (.var 0) lamTyped (.symm beta)
  exact ⟨equal, etaExpansion_typed_at_raised_codomain, family_typed_at_raised_codomain,
    .subEq equal family_types_below⟩

end Normalization

/-! ## A dependent pair spine supplied as an unknown term -/

namespace DependentPairSpine

open Mettapedia.TypeTheory.UniverseLevel

def sourceLevel : LevelExpr Nat := .param 0

/-- A type, followed by two elements of that very type. The second pair is
dependent on the first projection, rather than a homogeneous product. -/
def bundleType {n : Nat} : Tower.Tm n :=
  .sigma (.head (.sort sourceLevel)) (.sigma (.var 0) (.var 1))

def context : Tower.Ctx 1 := .snoc .nil bundleType

theorem bundleType_formed {n : Nat} {Γ : Tower.Ctx n} :
    Typed Tower.rules Γ bundleType
      (.head (.sort (.max (.succ sourceLevel) (.max sourceLevel sourceLevel)))) :=
  .sigmaForm (.headType (.sort _)) (.sort _)
    (.sigmaForm (.var 0) (.sort _) (.var 1) (.sort _) (.sorts _ _))
    (.sort _) (.sorts _ _)

theorem neutral_spine : PairSpine.TypedSpine Tower.rules context 2 (.var 0) bundleType := by
  have supplied : Typed Tower.rules context (.var 0) bundleType := .var 0
  have inner : Typed Tower.rules context
      (.sigma (.fst (.var 0)) (.fst (.var 1)))
      (.head (.sort (.max sourceLevel sourceLevel))) :=
    .sigmaForm (.fstElim supplied) (.sort _) (.fstElim (.var 1)) (.sort _) (.sorts _ _)
  exact .succ bundleType_formed (.sort _) supplied
    (.succ inner (.sort _) (.sndElim supplied) (.zero (.sndElim (.sndElim supplied))))

/-- Pair eta reconstructs both dependent layers of an unknown supplied
bundle. Its type component, first element and final element are all retained. -/
theorem neutral_expansion_equal :
    Equal Tower.rules context (PairSpine.expand 2 (.var 0)) (.var 0) bundleType :=
  neutral_spine.expand_typed_and_equal.2

/-- The eta reconstruction has a checked proof term in the object identity
type, with the original unknown bundle as its right endpoint. -/
theorem neutral_identity_witness :
    Typed Tower.rules context (.refl (PairSpine.expand 2 (.var 0)))
      (.id bundleType (PairSpine.expand 2 (.var 0)) (.var 0)) :=
  neutral_spine.expand_identity bundleType_formed (.sort _)

/-- The same object proof is valid after every substitution for the actual
universe parameter. No fixed valuation or constructor bundle is required. -/
theorem neutral_identity_levels (theta : Nat → LevelExpr Nat) :
    Typed Tower.rules (RussellTarski.substLevelsCtx theta context)
      (.refl (PairSpine.expand 2 (.var 0)))
      (.id (RussellTarski.substLevelsTm theta bundleType)
        (PairSpine.expand 2 (.var 0)) (.var 0)) := by
  have morphism := RussellTarski.levelSubstMorphism theta
  have instantiated := (neutral_spine.mapHead morphism).expand_identity
    (bundleType_formed.mapHead morphism) (morphism.isUniverse (.sort _))
  simpa only [RussellTarski.substLevelsCtx, RussellTarski.substLevelsTm,
    Tm.mapHead, PairSpine.mapHead_expand] using instantiated

/-- A closed level instance exercises the actual universe-map morphism on
the unknown dependent pair spine. -/
theorem neutral_identity_zero :
    Typed Tower.rules (RussellTarski.substLevelsCtx (fun _ => .const 0) context)
      (.refl (PairSpine.expand 2 (.var 0)))
      (.id (RussellTarski.substLevelsTm (fun _ => .const 0) bundleType)
        (PairSpine.expand 2 (.var 0)) (.var 0)) := by
  have instantiated := (neutral_spine.mapHead
    (RussellTarski.levelSubstMorphism (fun _ => .const 0))).expand_identity
      (bundleType_formed.mapHead (RussellTarski.levelSubstMorphism (fun _ => .const 0)))
      (.sort _)
  simpa only [RussellTarski.substLevelsCtx, RussellTarski.substLevelsTm,
    Tm.mapHead, PairSpine.mapHead_expand] using instantiated

/-- Typed projection comparisons include the complete dependent tail. -/
theorem neutral_readout_comparison : PairSpine.ReadoutEqual Tower.rules context 1 (.var 0)
    (PairSpine.expand 1 (.var 0)) bundleType := by
  have supplied : Typed Tower.rules context (.var 0) bundleType := .var 0
  have first := Derivable.fstElim supplied
  have rest := Derivable.sndElim supplied
  have paired := Derivable.pairIntro bundleType_formed (.sort _) first rest
  refine ⟨.head (.sort sourceLevel), .sigma (.var 0) (.var 1), rfl,
    supplied, paired, ?_, ?_⟩
  · exact .symm (.betaFst bundleType_formed (.sort _) first rest)
  · exact .symm (.betaSnd bundleType_formed (.sort _) first rest)

theorem neutral_readout_reconstructs : Equal Tower.rules context (.var 0)
    (PairSpine.expand 1 (.var 0)) bundleType := PairSpine.equal_of_readout neutral_readout_comparison


/-- The eta proof equates distinct raw syntax; it is not a reflexivity check
on an already expanded input. -/
theorem neutral_expansion_distinct :
    PairSpine.expand 2 (.var 0 : Tower.Tm 1) ≠ .var 0 := by decide

private theorem variable_irreducible {n : Nat} (index : Fin n) {target : Tower.Tm n} :
    ¬ StepCore Tower.rules.computation Tower.rules.headEq (.var index) target := by
  intro step
  cases step with
  | root impossible => cases impossible

private theorem pair_not_reaches_variable {n : Nat} {first second target : Tower.Tm n}
    (steps : TypedEquality.Reduces Tower.rules (.pair first second) target) :
    ∃ first' second', target = .pair first' second' := by
  induction steps with
  | refl => exact ⟨_, _, rfl⟩
  | tail previous step ih =>
      obtain ⟨first', second', rfl⟩ := ih
      cases step with
      | root impossible => cases impossible
      | congPairFst inner => exact ⟨_, _, rfl⟩
      | congPairSnd inner => exact ⟨_, _, rfl⟩

/-- Raw beta/projection conversion does not supply pair eta, even though the
same neutral terms are equal in the explicitly eta-enriched judgment. -/
theorem neutral_expansion_not_raw_convertible :
    ¬ Conv Tower.rules.headEq (PairSpine.expand 2 (.var 0 : Tower.Tm 1))
      (.var 0) Tower.rules.computation := by
  intro conversion
  obtain ⟨common, left, right⟩ := LevelTower.churchRosser conversion
  have fixed : common = (.var 0 : Tower.Tm 1) := by
    clear left
    induction right with
    | refl => rfl
    | tail previous step ih =>
        subst ih
        exact (variable_irreducible 0 step).elim
  obtain ⟨first, second, shape⟩ := pair_not_reaches_variable left
  rw [fixed] at shape
  cases shape

#print axioms neutral_expansion_equal
#print axioms neutral_identity_witness
#print axioms neutral_identity_levels
#print axioms neutral_identity_zero
#print axioms neutral_readout_reconstructs
#print axioms neutral_expansion_not_raw_convertible

end DependentPairSpine
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

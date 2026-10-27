import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Semantics
import Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax
import Mettapedia.OSLF.NativeTypes.Generation.PropositionalCodes

/-!
# Embedding the front door, its queries and the propositional codes

The front-door formulas read over a GSLT with atomic tests, steps modulo its equations, and a spatial
theory of indexed splits. Their atoms are tests, not formers, so they embed as free variables. Each
atom has two variables, one holding where the test holds and one where it fails, since generated
formulas are in negation normal form and have no negated variables.

- **Front-door formulas** (`sat_ofCore`): negation and implication are translated by polarity, the
  possibility and the outgoing universal become the modalities for all steps, and a separating
  conjunction becomes the split of a collection kind. The embedding is exact, at both polarities, over
  any native structure whose steps are the GSLT's and whose splits of each kind used are the spatial
  theory's (`SplitsRealized`).
- **Queries** embed through their elaboration (`ofQuery`, `ofQuery_ok`).
- **Propositional codes** (`sat_ofExpression`): their leaves become paired variables, and they embed
  exactly over every native structure.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.Embeddings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (gsltDiamond_spec)
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core (Test denotation)
open Mettapedia.OSLF.NativeTypes.Decision.Spatial (SpatialTheory)

universe u w

/-! ## Front-door formulas -/

section FrontDoor

variable {Leaf : Type w} {m : ℕ} (positive negative : Leaf → Fin m) (kindOf : ℕ → CollType)

/-- **A front-door formula as a generated formula**, at a polarity: the formula itself at `true`, its
negation at `false`. -/
def ofCore : Bool → Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Formula Leaf → Formula m
  | true, .atom leaf => .var (positive leaf)
  | false, .atom leaf => .var (negative leaf)
  | true, .top => .top
  | false, .top => .bot
  | true, .bottom => .bot
  | false, .bottom => .top
  | true, .conj left right => .and (ofCore true left) (ofCore true right)
  | false, .conj left right => .or (ofCore false left) (ofCore false right)
  | true, .disj left right => .or (ofCore true left) (ofCore true right)
  | false, .disj left right => .and (ofCore false left) (ofCore false right)
  | polarity, .neg inner => ofCore (!polarity) inner
  | true, .imp premise conclusion => .or (ofCore false premise) (ofCore true conclusion)
  | false, .imp premise conclusion => .and (ofCore true premise) (ofCore false conclusion)
  | true, .possibility inner => .possibly .any (ofCore true inner)
  | false, .possibility inner => .necessarily .any (ofCore false inner)
  | true, .outgoingUniversal inner => .necessarily .any (ofCore true inner)
  | false, .outgoingUniversal inner => .possibly .any (ofCore false inner)
  | true, .separating index left right => .split (kindOf index) (ofCore true left) (ofCore true right)
  | false, .separating index left right => .everySplit (kindOf index) (ofCore false left) (ofCore false right)

variable {system : Mettapedia.GSLT.GSLT.{u}}

/-- **The structure realizes the separating conjunctions a formula uses**: the splits of each kind used
are the spatial theory's splits at the index. -/
def SplitsRealized (S : NativeStructure system.Term) (spatial : SpatialTheory system) :
    Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Formula Leaf → Prop
  | .atom _ | .top | .bottom => True
  | .conj left right | .disj left right | .imp left right =>
    SplitsRealized S spatial left ∧ SplitsRealized S spatial right
  | .neg inner | .possibility inner | .outgoingUniversal inner => SplitsRealized S spatial inner
  | .separating index left right =>
    (∀ whole first second, S.split whole (kindOf index) first second ↔ spatial.Split index whole first second) ∧
      SplitsRealized S spatial left ∧ SplitsRealized S spatial right

/-- **The formula's atoms are among the covered tests.** -/
def AtomsCovered (covered : Leaf → Prop) : Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Formula Leaf → Prop
  | .atom leaf => covered leaf
  | .top | .bottom => True
  | .conj left right | .disj left right | .imp left right | .separating _ left right =>
    AtomsCovered covered left ∧ AtomsCovered covered right
  | .neg inner | .possibility inner | .outgoingUniversal inner => AtomsCovered covered inner

theorem atomsCovered_all : ∀ (formula : Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Formula Leaf),
    AtomsCovered (fun _ => True) formula
  | .atom _ | .top | .bottom => trivial
  | .conj left right | .disj left right | .imp left right | .separating _ left right =>
    ⟨atomsCovered_all left, atomsCovered_all right⟩
  | .neg inner | .possibility inner | .outgoingUniversal inner => atomsCovered_all inner

/-- **The structure realizes the separating conjunctions a formula uses on a region**: at the region's elements the
splits of each kind used are the spatial theory's splits at the index, and their parts stay in the region. -/
def SplitsRealizedOn (region : system.Term → Prop) (S : NativeStructure system.Term) (spatial : SpatialTheory system) :
    Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Formula Leaf → Prop
  | .atom _ | .top | .bottom => True
  | .conj left right | .disj left right | .imp left right =>
    SplitsRealizedOn region S spatial left ∧ SplitsRealizedOn region S spatial right
  | .neg inner | .possibility inner | .outgoingUniversal inner => SplitsRealizedOn region S spatial inner
  | .separating index left right =>
    (∀ whole, region whole → ∀ first second,
      (S.split whole (kindOf index) first second ↔ spatial.Split index whole first second)) ∧
    (∀ whole first second, region whole → spatial.Split index whole first second → region first ∧ region second) ∧
      SplitsRealizedOn region S spatial left ∧ SplitsRealizedOn region S spatial right

/-- Realized everywhere, realized on every region where the theory's splits stay. -/
theorem SplitsRealized.on {S : NativeStructure system.Term} {spatial : SpatialTheory system} :
    ∀ {formula : Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Formula Leaf},
      SplitsRealized kindOf S spatial formula → SplitsRealizedOn kindOf (fun _ => True) S spatial formula
  | .atom _, _ | .top, _ | .bottom, _ => trivial
  | .conj left right, realized | .disj left right, realized | .imp left right, realized =>
    ⟨SplitsRealized.on (formula := left) realized.1, SplitsRealized.on (formula := right) realized.2⟩
  | .neg inner, realized | .possibility inner, realized | .outgoingUniversal inner, realized =>
    SplitsRealized.on (formula := inner) realized
  | .separating _ left right, realized =>
    ⟨fun whole _ first second => realized.1 whole first second, fun _ _ _ _ _ => ⟨trivial, trivial⟩,
      SplitsRealized.on (formula := left) realized.2.1, SplitsRealized.on (formula := right) realized.2.2⟩

variable {positive negative kindOf}

/-- **Front-door formulas embed exactly on a region closed under steps**, at both polarities, over a structure whose
steps from the region are the GSLT's and whose splits there are the spatial theory's. -/
theorem sat_ofCore_on {admitted : system.Term → Prop} (tests : Leaf → Test system admitted)
    (spatial : SpatialTheory system) {S : NativeStructure system.Term} (region : system.Term → Prop)
    (covered : Leaf → Prop)
    (steps : ∀ source, region source → ∀ target, (S.step source .any target ↔ system.Step source target))
    (closed : ∀ source target, region source → system.Step source target → region target) {env : Env system.Term m}
    (onPositive : ∀ leaf, covered leaf → ∀ term, region term →
      (term ∈ env (positive leaf) ↔ (tests leaf).predicate.1 term))
    (onNegative : ∀ leaf, covered leaf → ∀ term, region term →
      (term ∈ env (negative leaf) ↔ ¬ (tests leaf).predicate.1 term)) :
    ∀ (formula : Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Formula Leaf) (polarity : Bool),
      AtomsCovered covered formula → SplitsRealizedOn kindOf region S spatial formula → ∀ term, region term →
        (S.sat env (ofCore positive negative kindOf polarity formula) term ↔
          cond polarity ((denotation tests formula spatial).1 term) (¬ (denotation tests formula spatial).1 term))
  | .atom leaf, polarity, atoms, _, term, inside => by
    cases polarity
    · exact onNegative leaf atoms term inside
    · exact onPositive leaf atoms term inside
  | .top, polarity, _, _, _, _ => by cases polarity <;> simp [ofCore, NativeStructure.sat, denotation]
  | .bottom, polarity, _, _, _, _ => by cases polarity <;> simp [ofCore, NativeStructure.sat, denotation]
  | .conj left right, polarity, atoms, realized, term, inside => by
    have first := fun polarity =>
      sat_ofCore_on tests spatial region covered steps closed onPositive onNegative
        left polarity atoms.1 realized.1 term inside
    have second := fun polarity =>
      sat_ofCore_on tests spatial region covered steps closed onPositive onNegative
        right polarity atoms.2 realized.2 term inside
    cases polarity
    · simp only [ofCore, NativeStructure.sat, first false, second false, cond]
      exact not_and_or.symm
    · simp only [ofCore, NativeStructure.sat, first true, second true, cond]
      rfl
  | .disj left right, polarity, atoms, realized, term, inside => by
    have first := fun polarity =>
      sat_ofCore_on tests spatial region covered steps closed onPositive onNegative
        left polarity atoms.1 realized.1 term inside
    have second := fun polarity =>
      sat_ofCore_on tests spatial region covered steps closed onPositive onNegative
        right polarity atoms.2 realized.2 term inside
    cases polarity
    · simp only [ofCore, NativeStructure.sat, first false, second false, cond]
      exact not_or.symm
    · simp only [ofCore, NativeStructure.sat, first true, second true, cond]
      rfl
  | .neg inner, polarity, atoms, realized, term, inside => by
    have holds := fun polarity =>
      sat_ofCore_on tests spatial region covered steps closed onPositive onNegative
        inner polarity atoms realized term inside
    cases polarity
    · rw [show ofCore positive negative kindOf false (.neg inner) = ofCore positive negative kindOf true inner from rfl,
        holds true]
      exact not_not.symm
    · rw [show ofCore positive negative kindOf true (.neg inner) = ofCore positive negative kindOf false inner from rfl,
        holds false]
      rfl
  | .imp premise conclusion, polarity, atoms, realized, term, inside => by
    have first := fun polarity =>
      sat_ofCore_on tests spatial region covered steps closed onPositive onNegative
        premise polarity atoms.1 realized.1 term inside
    have second := fun polarity =>
      sat_ofCore_on tests spatial region covered steps closed onPositive onNegative
        conclusion polarity atoms.2 realized.2 term inside
    cases polarity
    · simp only [ofCore, NativeStructure.sat, first true, second false, cond]
      exact Classical.not_imp.symm
    · simp only [ofCore, NativeStructure.sat, first false, second true, cond]
      exact imp_iff_not_or.symm
  | .possibility inner, polarity, atoms, realized, term, inside => by
    have holds := fun polarity next (nextInside : region next) =>
      sat_ofCore_on tests spatial region covered steps closed onPositive onNegative
        inner polarity atoms realized next nextInside
    have diamond := gsltDiamond_spec system (denotation tests inner spatial).1 term
    cases polarity
    · change (∀ next, S.step term .any next → S.sat env (ofCore positive negative kindOf false inner) next) ↔
        ¬ Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltDiamond system (denotation tests inner spatial).1 term
      rw [diamond]
      constructor
      · rintro every ⟨next, stepped, holdsAt⟩
        exact (holds false next (closed term next inside stepped)).mp
          (every next ((steps term inside next).mpr stepped)) holdsAt
      · intro none next step
        have stepped := (steps term inside next).mp step
        exact (holds false next (closed term next inside stepped)).mpr fun holdsAt => none ⟨next, stepped, holdsAt⟩
    · change (∃ next, S.step term .any next ∧ S.sat env (ofCore positive negative kindOf true inner) next) ↔
        Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltDiamond system (denotation tests inner spatial).1 term
      rw [diamond]
      constructor
      · rintro ⟨next, step, holdsAt⟩
        have stepped := (steps term inside next).mp step
        exact ⟨next, stepped, (holds true next (closed term next inside stepped)).mp holdsAt⟩
      · rintro ⟨next, stepped, holdsAt⟩
        exact ⟨next, (steps term inside next).mpr stepped, (holds true next (closed term next inside stepped)).mpr holdsAt⟩
  | .outgoingUniversal inner, polarity, atoms, realized, term, inside => by
    have holds := fun polarity next (nextInside : region next) =>
      sat_ofCore_on tests spatial region covered steps closed onPositive onNegative
        inner polarity atoms realized next nextInside
    cases polarity
    · change (∃ next, S.step term .any next ∧ S.sat env (ofCore positive negative kindOf false inner) next) ↔
        ¬ ∀ next, system.Step term next → (denotation tests inner spatial).1 next
      constructor
      · rintro ⟨next, step, holdsAt⟩ every
        have stepped := (steps term inside next).mp step
        exact (holds false next (closed term next inside stepped)).mp holdsAt (every next stepped)
      · intro notEvery
        obtain ⟨next, stepped, fails⟩ : ∃ next, system.Step term next ∧ ¬ (denotation tests inner spatial).1 next := by
          by_contra none
          exact notEvery fun next stepped => by_contra fun fails => none ⟨next, stepped, fails⟩
        exact ⟨next, (steps term inside next).mpr stepped, (holds false next (closed term next inside stepped)).mpr fails⟩
    · change (∀ next, S.step term .any next → S.sat env (ofCore positive negative kindOf true inner) next) ↔
        ∀ next, system.Step term next → (denotation tests inner spatial).1 next
      constructor
      · intro every next stepped
        exact (holds true next (closed term next inside stepped)).mp (every next ((steps term inside next).mpr stepped))
      · intro every next step
        have stepped := (steps term inside next).mp step
        exact (holds true next (closed term next inside stepped)).mpr (every next stepped)
  | .separating index left right, polarity, atoms, realized, term, inside => by
    have first := fun polarity part (partInside : region part) =>
      sat_ofCore_on tests spatial region covered steps closed onPositive onNegative
        left polarity atoms.1 realized.2.2.1 part partInside
    have second := fun polarity part (partInside : region part) =>
      sat_ofCore_on tests spatial region covered steps closed onPositive onNegative
        right polarity atoms.2 realized.2.2.2 part partInside
    have splits := realized.1 term inside
    have parts := fun firstPart secondPart => realized.2.1 term firstPart secondPart inside
    cases polarity
    · change (∀ firstPart secondPart, S.split term (kindOf index) firstPart secondPart →
          S.sat env (ofCore positive negative kindOf false left) firstPart ∨
            S.sat env (ofCore positive negative kindOf false right) secondPart) ↔
        ¬ ∃ firstPart secondPart, spatial.Split index term firstPart secondPart ∧
          (denotation tests left spatial).1 firstPart ∧ (denotation tests right spatial).1 secondPart
      constructor
      · rintro every ⟨firstPart, secondPart, split, holdsLeft, holdsRight⟩
        obtain ⟨leftInside, rightInside⟩ := parts firstPart secondPart split
        rcases every firstPart secondPart ((splits firstPart secondPart).mpr split) with fails | fails
        · exact (first false firstPart leftInside).mp fails holdsLeft
        · exact (second false secondPart rightInside).mp fails holdsRight
      · intro none firstPart secondPart split
        have split' := (splits firstPart secondPart).mp split
        obtain ⟨leftInside, rightInside⟩ := parts firstPart secondPart split'
        by_cases holdsLeft : (denotation tests left spatial).1 firstPart
        · exact .inr ((second false secondPart rightInside).mpr fun holdsRight =>
            none ⟨firstPart, secondPart, split', holdsLeft, holdsRight⟩)
        · exact .inl ((first false firstPart leftInside).mpr holdsLeft)
    · change (∃ firstPart secondPart, S.split term (kindOf index) firstPart secondPart ∧
          S.sat env (ofCore positive negative kindOf true left) firstPart ∧
            S.sat env (ofCore positive negative kindOf true right) secondPart) ↔
        ∃ firstPart secondPart, spatial.Split index term firstPart secondPart ∧
          (denotation tests left spatial).1 firstPart ∧ (denotation tests right spatial).1 secondPart
      constructor
      · rintro ⟨firstPart, secondPart, split, holdsLeft, holdsRight⟩
        have split' := (splits firstPart secondPart).mp split
        obtain ⟨leftInside, rightInside⟩ := parts firstPart secondPart split'
        exact ⟨firstPart, secondPart, split', (first true firstPart leftInside).mp holdsLeft,
          (second true secondPart rightInside).mp holdsRight⟩
      · rintro ⟨firstPart, secondPart, split', holdsLeft, holdsRight⟩
        obtain ⟨leftInside, rightInside⟩ := parts firstPart secondPart split'
        exact ⟨firstPart, secondPart, (splits firstPart secondPart).mpr split',
          (first true firstPart leftInside).mpr holdsLeft, (second true secondPart rightInside).mpr holdsRight⟩

/-- **Front-door formulas embed exactly**, at both polarities, over a structure with the GSLT's steps
and the spatial theory's splits. -/
theorem sat_ofCore {admitted : system.Term → Prop} (tests : Leaf → Test system admitted)
    (spatial : SpatialTheory system) {S : NativeStructure system.Term}
    (steps : ∀ source target, S.step source .any target ↔ system.Step source target) {env : Env system.Term m}
    (onPositive : ∀ leaf term, term ∈ env (positive leaf) ↔ (tests leaf).predicate.1 term)
    (onNegative : ∀ leaf term, term ∈ env (negative leaf) ↔ ¬ (tests leaf).predicate.1 term)
    (formula : Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Formula Leaf) (polarity : Bool)
    (realized : SplitsRealized kindOf S spatial formula) (term : system.Term) :
    S.sat env (ofCore positive negative kindOf polarity formula) term ↔
      cond polarity ((denotation tests formula spatial).1 term) (¬ (denotation tests formula spatial).1 term) :=
  sat_ofCore_on tests spatial (fun _ => True) (fun _ => True) (fun source _ target => steps source target)
    (fun _ _ _ _ => trivial) (fun leaf _ term _ => onPositive leaf term) (fun leaf _ term _ => onNegative leaf term)
    formula polarity (atomsCovered_all formula) realized.on term trivial

end FrontDoor

/-! ## Queries -/

section Queries

open Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax (Query elaborate)
open Mettapedia.OSLF.NativeTypes.Runtime.Description (Driver)

variable {m : ℕ}

/-- **A query as a generated formula**, through its elaboration. -/
def ofQuery (driver : Driver) (positive negative : driver.Leaf → Fin m) (kindOf : ℕ → CollType) (query : Query) :
    Except String (Formula m) :=
  (elaborate driver query).map (ofCore positive negative kindOf true)

/-- An elaborated query embeds as its formula does. -/
theorem ofQuery_ok {driver : Driver} {positive negative : driver.Leaf → Fin m} {kindOf : ℕ → CollType}
    {query : Query} {formula : driver.Formula} (elaborated : elaborate driver query = .ok formula) :
    ofQuery driver positive negative kindOf query = .ok (ofCore positive negative kindOf true formula) := by
  simp [ofQuery, elaborated, Except.map]

end Queries

/-! ## Propositional codes -/

section Codes

open Mettapedia.OSLF.NativeTypes.Generation.PropositionalCodes (Expression rawMeaning)

variable {m : ℕ} (positive negative : ℕ → Fin m)

/-- **A propositional code as a generated formula**, at a polarity. -/
def ofExpression : Bool → Expression → Formula m
  | true, .leaf index => .var (positive index)
  | false, .leaf index => .var (negative index)
  | true, .top => .top
  | false, .top => .bot
  | true, .bottom => .bot
  | false, .bottom => .top
  | true, .conjunction first second => .and (ofExpression true first) (ofExpression true second)
  | false, .conjunction first second => .or (ofExpression false first) (ofExpression false second)
  | true, .disjunction first second => .or (ofExpression true first) (ofExpression true second)
  | false, .disjunction first second => .and (ofExpression false first) (ofExpression false second)
  | true, .implication first second => .or (ofExpression false first) (ofExpression true second)
  | false, .implication first second => .and (ofExpression true first) (ofExpression false second)
  | polarity, .negation inner => ofExpression (!polarity) inner

variable {positive negative}

/-- **Propositional codes embed exactly**, over every native structure. -/
theorem sat_ofExpression {generated : Mettapedia.OSLF.NativeTypes.Generation.Generated} {bound : List TypeExpr}
    (leaves : Mettapedia.OSLF.NativeTypes.SortProfiles.Source.LeafCodes generated bound)
    (S : NativeStructure Pattern) {env : Env Pattern m}
    (onPositive : ∀ index term, term ∈ env (positive index) ↔ (leaves index).2.2.meaning term)
    (onNegative : ∀ index term, term ∈ env (negative index) ↔ ¬ (leaves index).2.2.meaning term) :
    ∀ (expression : Expression) (polarity : Bool) (term : Pattern),
      S.sat env (ofExpression positive negative polarity expression) term ↔
        cond polarity (rawMeaning leaves expression term) (¬ rawMeaning leaves expression term)
  | .leaf index, polarity, term => by
    cases polarity
    · exact onNegative index term
    · exact onPositive index term
  | .top, polarity, _ => by cases polarity <;> simp [ofExpression, NativeStructure.sat, rawMeaning]
  | .bottom, polarity, _ => by cases polarity <;> simp [ofExpression, NativeStructure.sat, rawMeaning]
  | .conjunction first second, polarity, term => by
    have left := fun polarity => sat_ofExpression leaves S onPositive onNegative first polarity term
    have right := fun polarity => sat_ofExpression leaves S onPositive onNegative second polarity term
    cases polarity
    · simp only [ofExpression, NativeStructure.sat, left false, right false, cond, rawMeaning]
      exact not_and_or.symm
    · simp only [ofExpression, NativeStructure.sat, left true, right true, cond, rawMeaning]
  | .disjunction first second, polarity, term => by
    have left := fun polarity => sat_ofExpression leaves S onPositive onNegative first polarity term
    have right := fun polarity => sat_ofExpression leaves S onPositive onNegative second polarity term
    cases polarity
    · simp only [ofExpression, NativeStructure.sat, left false, right false, cond, rawMeaning]
      exact not_or.symm
    · simp only [ofExpression, NativeStructure.sat, left true, right true, cond, rawMeaning]
  | .implication first second, polarity, term => by
    have left := fun polarity => sat_ofExpression leaves S onPositive onNegative first polarity term
    have right := fun polarity => sat_ofExpression leaves S onPositive onNegative second polarity term
    cases polarity
    · simp only [ofExpression, NativeStructure.sat, left true, right false, cond, rawMeaning]
      exact Classical.not_imp.symm
    · simp only [ofExpression, NativeStructure.sat, left false, right true, cond, rawMeaning]
      exact imp_iff_not_or.symm
  | .negation inner, polarity, term => by
    have holds := fun polarity => sat_ofExpression leaves S onPositive onNegative inner polarity term
    cases polarity
    · rw [show ofExpression positive negative false (.negation inner) = ofExpression positive negative true inner from rfl,
        holds true]
      simp [rawMeaning]
    · rw [show ofExpression positive negative true (.negation inner) = ofExpression positive negative false inner from rfl,
        holds false]
      simp [rawMeaning]

end Codes

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.Embeddings

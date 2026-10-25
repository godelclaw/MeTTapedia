import Mettapedia.GSLT.Dedukti.GenericPureTypeSystem
import Mettapedia.TypeTheory.HypercubeProfileStratification

/-!
# Sort-renaming spans above the two-sort hypercube

The calculus of constructions and the historical kind-result curriculum
profile disagree on the result of the `(Kind, Type)` product.  A functional
target can receive both by moving their two source sorts to different strata.
Such a target is a comparison span, but it is not a commuting join of the
shared source fragment.

The obstruction is exact.  If the two translations into a functional target
agree on the shared `Type` and `Kind`, functionality identifies their images.
The translated `Type : Kind` axiom and `(Type, Type, Type)` rule then give a
self-typed sort.  Transporting the maintained Hurkens derivation supplies the
corresponding inconsistency witness in the generic target.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.HypercubeSortRenaming

open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFProfile
open Mettapedia.GSLT.Dedukti


universe u

/-! ## A genuine three-stratum comparison target -/

/-- Three distinct strata used to keep the two branch translations
functional.  No claim that this finite profile is ECC or CIC is made. -/
inductive Stratum where
  | prop
  | type0
  | type1
  deriving DecidableEq, Repr

abbrev Rule := Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.ProductRule Stratum

def propPropProp : Rule := ⟨.prop, .prop, .prop⟩
def propType0Type0 : Rule := ⟨.prop, .type0, .type0⟩
def type0PropProp : Rule := ⟨.type0, .prop, .prop⟩
def type0Type0Type0 : Rule := ⟨.type0, .type0, .type0⟩
def type0Type1Type1 : Rule := ⟨.type0, .type1, .type1⟩
def type1Type0Type1 : Rule := ⟨.type1, .type0, .type1⟩
def type1Type1Type1 : Rule := ⟨.type1, .type1, .type1⟩

def comparisonAxioms : List (Stratum × Stratum) :=
  [(.prop, .type0), (.type0, .type1)]

def comparisonProducts : List Rule :=
  [propPropProp, propType0Type0, type0PropProp, type0Type0Type0,
    type0Type1Type1, type1Type0Type1, type1Type1Type1]

def comparisonAxiomTarget? : Stratum → Option Stratum
  | .prop => some .type0
  | .type0 => some .type1
  | .type1 => none

def comparisonResult? : Stratum → Stratum → Option Stratum
  | .prop, .prop => some .prop
  | .prop, .type0 => some .type0
  | .type0, .prop => some .prop
  | .type0, .type0 => some .type0
  | .type0, .type1 => some .type1
  | .type1, .type0 => some .type1
  | .type1, .type1 => some .type1
  | _, _ => none

/-- A functional target containing shifted images of both source profiles. -/
def comparisonProfile : Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.Profile Stratum where
  Axiom := fun source target => comparisonAxiomTarget? source = some target
  Product := fun rule => comparisonResult? rule.domain rule.codomain = some rule.result

theorem comparisonProfile_functional : Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.Functional comparisonProfile := by
  constructor
  · intro source first second firstKnown secondKnown
    exact Option.some.inj (firstKnown.symm.trans secondKnown)
  · intro first second firstKnown secondKnown sameDomain sameCodomain
    change comparisonResult? first.domain first.codomain = some first.result at firstKnown
    change comparisonResult? second.domain second.codomain = some second.result at secondKnown
    rw [sameDomain, sameCodomain] at firstKnown
    exact Option.some.inj (firstKnown.symm.trans secondKnown)

/-- The comparison target has no self-typed stratum. -/
theorem comparisonProfile_no_self_axiom (sort : Stratum) :
    ¬ comparisonProfile.Axiom sort sort := by
  cases sort <;> simp [comparisonProfile, comparisonAxiomTarget?]

def cocSort : Srt → Stratum
  | .type => .prop
  | .kind => .type0

def prototypeSort : Srt → Stratum
  | .type => .type0
  | .kind => .type1

/-- CoC enters the lower two strata. -/
def cocToComparison :
    Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.Morphism (Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.TwoSort.ofLFProfile constructions) comparisonProfile where
  onSort := cocSort
  axiom_preserved := by
    intro first second known
    cases first <;> cases second <;>
      simp [Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.TwoSort.ofLFProfile, constructions, typeAxiom, comparisonProfile,
        comparisonAxiomTarget?, cocSort] at known ⊢
  product_preserved := by
    intro rule known
    rcases rule with ⟨domain, codomain, result⟩
    cases domain <;> cases codomain <;> cases result <;>
      simp_all [Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.TwoSort.ofLFProfile,
        Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.TwoSort.toLFRule, constructions,
        Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.ProductRule.map, comparisonProfile,
        comparisonResult?, typeTypeType, typeKindKind, kindTypeType,
        kindKindKind, cocSort]

/-- The historical prototype enters the upper two strata. -/
def prototypeToComparison :
    Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.Morphism (Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.TwoSort.ofLFProfile mettaKernelKindResultPrototype)
      comparisonProfile where
  onSort := prototypeSort
  axiom_preserved := by
    intro first second known
    cases first <;> cases second <;>
      simp [Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.TwoSort.ofLFProfile, mettaKernelKindResultPrototype, typeAxiom,
        comparisonProfile, comparisonAxiomTarget?, prototypeSort] at known ⊢
  product_preserved := by
    intro rule known
    rcases rule with ⟨domain, codomain, result⟩
    cases domain <;> cases codomain <;> cases result <;>
      simp_all [Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.TwoSort.ofLFProfile,
        Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.TwoSort.toLFRule, mettaKernelKindResultPrototype,
        Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.ProductRule.map, comparisonProfile,
        comparisonResult?, typeTypeType, typeKindKind, kindTypeKind,
        kindKindKind, prototypeSort]

/-- The translations deliberately disagree on the shared lower sort. -/
theorem comparison_maps_disagree_on_type :
    cocToComparison.onSort .type ≠ prototypeToComparison.onSort .type := by
  decide

/-- They also disagree on the shared upper sort. -/
theorem comparison_maps_disagree_on_kind :
    cocToComparison.onSort .kind ≠ prototypeToComparison.onSort .kind := by
  decide

/-! The existing source derivations really transport through the two maps. -/

abbrev cocPolymorphicIdentityTarget : Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.Term Stratum :=
  Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.Term.map cocSort (Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.TwoSort.ofLFTerm Example.polymorphicIdentity)

abbrev cocPolymorphicIdentityTypeTarget : Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.Term Stratum :=
  Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.Term.map cocSort (Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.TwoSort.ofLFTerm Example.polymorphicIdentityType)

theorem coc_polymorphicIdentity_transports :
    Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.Derives comparisonProfile []
      (.term cocPolymorphicIdentityTarget cocPolymorphicIdentityTypeTarget .prop) := by
  simpa [Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.mapContext,
    Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.Judgment.map,
    Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.TwoSort.ofLFContext,
    Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.TwoSort.ofLFJudgment,
    cocToComparison, cocSort] using
    (Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.TwoSort.ofLFDerives Example.polymorphicIdentity_typed).map cocToComparison

def prototypeTypeOperator : PTerm :=
  .pi kindKindKind (.sort .type) (.sort .type)

theorem prototypeTypeOperator_typed :
    Mettapedia.GSLT.Dedukti.Derives mettaKernelKindResultPrototype []
      (.type prototypeTypeOperator .kind) := by
  exact .pi (.sort rfl) (.sort rfl) (by
    simp [mettaKernelKindResultPrototype, kindKindKind])

abbrev prototypeTypeOperatorTarget : Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.Term Stratum :=
  Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.Term.map prototypeSort (Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.TwoSort.ofLFTerm prototypeTypeOperator)

theorem prototype_typeOperator_transports :
    Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.Derives comparisonProfile []
      (.type prototypeTypeOperatorTarget .type1) := by
  simpa [Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.mapContext,
    Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.Judgment.map,
    Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.TwoSort.ofLFContext,
    Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.TwoSort.ofLFJudgment,
    prototypeToComparison, prototypeSort] using
    (Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.TwoSort.ofLFDerives prototypeTypeOperator_typed).map prototypeToComparison

/-! ## The commuting obstruction -/

/-- If two sort-renaming morphisms into a functional target agree on the
shared source sorts, the conflicting product results force those images to be
equal. -/
theorem commuting_functional_cocone_collapses
    {TargetSort : Type u} {target : Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.Profile TargetSort}
    (fromCoc : Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.Morphism (Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.TwoSort.ofLFProfile constructions) target)
    (fromPrototype :
      Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.Morphism (Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.TwoSort.ofLFProfile mettaKernelKindResultPrototype) target)
    (agreesType : fromCoc.onSort .type = fromPrototype.onSort .type)
    (agreesKind : fromCoc.onSort .kind = fromPrototype.onSort .kind)
    (functional : Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.Functional target) :
    fromCoc.onSort .type = fromCoc.onSort .kind := by
  have cocRule :
      (Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.TwoSort.ofLFProfile constructions).Product (Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.TwoSort.ofLFRule kindTypeType) := by
    simp [Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.TwoSort.ofLFProfile,
      Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.TwoSort.ofLFRule,
      Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.TwoSort.toLFRule,
      constructions, kindTypeType, typeTypeType, typeKindKind, kindKindKind]
  have prototypeRule :
      (Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.TwoSort.ofLFProfile mettaKernelKindResultPrototype).Product
        (Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.TwoSort.ofLFRule kindTypeKind) := by
    simp [Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.TwoSort.ofLFProfile,
      Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.TwoSort.ofLFRule,
      Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.TwoSort.toLFRule,
      mettaKernelKindResultPrototype, kindTypeKind, typeTypeType,
      typeKindKind, kindKindKind]
  have results := functional.2
    (fromCoc.product_preserved cocRule)
    (fromPrototype.product_preserved prototypeRule)
    agreesKind agreesType
  exact results.trans agreesKind.symm

/-- The collapsed image has a self-typing axiom. -/
theorem commuting_cocone_self_axiom
    {TargetSort : Type u} {target : Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.Profile TargetSort}
    (fromCoc : Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.Morphism (Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.TwoSort.ofLFProfile constructions) target)
    (fromPrototype :
      Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.Morphism (Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.TwoSort.ofLFProfile mettaKernelKindResultPrototype) target)
    (agreesType : fromCoc.onSort .type = fromPrototype.onSort .type)
    (agreesKind : fromCoc.onSort .kind = fromPrototype.onSort .kind)
    (functional : Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.Functional target) :
    target.Axiom (fromCoc.onSort .type) (fromCoc.onSort .type) := by
  have sourceAxiom : (Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.TwoSort.ofLFProfile constructions).Axiom .type .kind := by
    simp [Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.TwoSort.ofLFProfile, constructions, typeAxiom]
  have mapped := fromCoc.axiom_preserved sourceAxiom
  rw [← commuting_functional_cocone_collapses fromCoc fromPrototype
    agreesType agreesKind functional] at mapped
  exact mapped

/-- The collapsed image also contains the product rule needed by the
`Type : Type` paradox. -/
theorem commuting_cocone_self_product
    {TargetSort : Type u} {target : Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.Profile TargetSort}
    (fromCoc : Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.Morphism (Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.TwoSort.ofLFProfile constructions) target) :
    target.Product
      ⟨fromCoc.onSort .type, fromCoc.onSort .type, fromCoc.onSort .type⟩ := by
  have sourceRule :
      (Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.TwoSort.ofLFProfile constructions).Product (Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.TwoSort.ofLFRule typeTypeType) := by
    simp [Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.TwoSort.ofLFProfile,
      Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.TwoSort.ofLFRule,
      Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.TwoSort.toLFRule,
      constructions, typeTypeType, typeKindKind, kindTypeType, kindKindKind]
  simpa [Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.TwoSort.ofLFRule,
    typeTypeType, Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.ProductRule.map] using
    fromCoc.product_preserved sourceRule

def collapsedTypeInTypeMorphism
    {TargetSort : Type u} {target : Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.Profile TargetSort} (point : TargetSort)
    (selfAxiom : target.Axiom point point)
    (selfProduct : target.Product ⟨point, point, point⟩) :
    Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.Morphism
      (Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.TwoSort.ofLFProfile TypeInTypeParadox.typeInType) target where
  onSort := fun _ => point
  axiom_preserved := by intro first second known; exact selfAxiom
  product_preserved := by
    intro rule known
    simpa [Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.ProductRule.map] using selfProduct

abbrev collapsedParadox {TargetSort : Type u} (point : TargetSort) :
    Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.Term TargetSort :=
  Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.Term.map (fun _ => point) (Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.TwoSort.ofLFTerm TypeInTypeParadox.paradoxTerm)

abbrev collapsedFalsum {TargetSort : Type u} (point : TargetSort) :
    Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.Term TargetSort :=
  Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.Term.map (fun _ => point) (Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.TwoSort.ofLFTerm TypeInTypeParadox.falsumTerm)

/-- **A faithful commuting merge cannot be recovered merely by adding
sorts.** Any functional commuting cocone carries the concrete Hurkens proof
of `Π p : u. p` at its collapsed sort `u`. -/
theorem commuting_functional_cocone_inconsistent
    {TargetSort : Type u} {target : Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.Profile TargetSort}
    (fromCoc : Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.Morphism (Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.TwoSort.ofLFProfile constructions) target)
    (fromPrototype :
      Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.Morphism (Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.TwoSort.ofLFProfile mettaKernelKindResultPrototype) target)
    (agreesType : fromCoc.onSort .type = fromPrototype.onSort .type)
    (agreesKind : fromCoc.onSort .kind = fromPrototype.onSort .kind)
    (functional : Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.Functional target) :
    Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.Derives target []
      (.term (collapsedParadox (fromCoc.onSort .type))
        (collapsedFalsum (fromCoc.onSort .type)) (fromCoc.onSort .type)) := by
  let selfAxiom := commuting_cocone_self_axiom fromCoc fromPrototype
    agreesType agreesKind functional
  let selfProduct := commuting_cocone_self_product fromCoc
  let collapse := collapsedTypeInTypeMorphism (fromCoc.onSort .type)
    selfAxiom selfProduct
  have source := Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.TwoSort.ofLFDerives TypeInTypeParadox.typeInType_inconsistent
  simpa [collapse, collapsedTypeInTypeMorphism, collapsedParadox,
    collapsedFalsum, Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.mapContext,
    Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.Judgment.map,
    Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.TwoSort.ofLFContext,
    Mettapedia.GSLT.Dedukti.GenericPureTypeSystem.TwoSort.ofLFJudgment] using
      source.map collapse

namespace Controls

/-- Finite controls for the shifted comparison span and its noncommutation. -/
def verdicts : List (String × Bool) :=
  [("CoC Type enters Prop", decide (cocSort .type = .prop)),
   ("CoC Kind enters Type0", decide (cocSort .kind = .type0)),
   ("prototype Type enters Type0", decide (prototypeSort .type = .type0)),
   ("prototype Kind enters Type1", decide (prototypeSort .kind = .type1)),
   ("shared Type does not commute", decide (cocSort .type ≠ prototypeSort .type)),
   ("shared Kind does not commute", decide (cocSort .kind ≠ prototypeSort .kind)),
   ("Prop is not self typed", decide (comparisonAxiomTarget? .prop ≠ some .prop)),
   ("Type0 is not self typed", decide (comparisonAxiomTarget? .type0 ≠ some .type0)),
   ("Type1 has no successor axiom", decide (comparisonAxiomTarget? .type1 = none))]

theorem all_verdicts : verdicts.all (fun entry => entry.2) = true := by
  decide +kernel

end Controls

#print axioms comparisonProfile_functional
#print axioms coc_polymorphicIdentity_transports
#print axioms prototype_typeOperator_transports
#print axioms commuting_functional_cocone_collapses
#print axioms commuting_functional_cocone_inconsistent
#print axioms Controls.all_verdicts

end Mettapedia.TypeTheory.HypercubeSortRenaming

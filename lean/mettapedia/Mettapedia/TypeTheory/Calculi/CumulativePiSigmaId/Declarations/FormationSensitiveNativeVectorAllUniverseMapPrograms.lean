import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAllUniverses
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.RecursorDerivation

/-!
# Object programs mapping native Vector All evidence across universes

The existing Vector eliminator maps supplied All evidence between two result
annotations, retaining each head witness and recursively mapping its tail.
Independent typing replay is in the UniverseMaps companion. No identity
eliminator, inverse law or new computation rule is introduced here.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation Declaration RussellTarski
open NativeNaturalVectorFamilies
open TypedEquality.Normalization
open NativeVectorAll.CanonicalAdequacy

def functionType {n : Nat} (source target : LevelExpr Nat)
    (element predicate length vector : Tower.Tm n) : Tower.Tm n :=
  .pi (Canonical.allTypeAtUniverse source element predicate length vector)
    (rename wk (Canonical.allTypeAtUniverse target element predicate length vector))

def motive {n : Nat} (source target : LevelExpr Nat)
    (element predicate : Tower.Tm n) : Tower.Tm n :=
  .lam (.lam (functionType source target
    (NativeVectorAll.weaken2 element) (NativeVectorAll.weaken2 predicate) (.var 1) (.var 0)))

def consCase {n : Nat} : Tower.Tm n :=
  .lam (.lam (.lam (.lam (.lam
    (.pair (.fst (.var 0)) (.app (.var 1) (.snd (.var 0))))))))

def map {n : Nat} (source target : LevelExpr Nat)
    (element predicate length vector : Tower.Tm n) : Tower.Tm n :=
  vecEliminateApp element (motive source target element predicate)
    (.lam (.var 0)) consCase length vector

def forward : Tower.Tm 4 :=
  map resultLevel upperLevel (.var 3) (.var 2) (.var 1) (.var 0)
def forwardType : Tower.Tm 4 :=
  functionType resultLevel upperLevel (.var 3) (.var 2) (.var 1) (.var 0)
def backward : Tower.Tm 4 :=
  map upperLevel resultLevel (.var 3) (.var 2) (.var 1) (.var 0)
def backwardType : Tower.Tm 4 :=
  functionType upperLevel resultLevel (.var 3) (.var 2) (.var 1) (.var 0)


/-! ## Substitution and constructor-vector computation -/

theorem substitute_functionType {n m : Nat} (sigma : Sub Tower.Head n m)
    (source target : LevelExpr Nat) (element predicate length vector : Tower.Tm n) :
    subst sigma (functionType source target element predicate length vector) =
      functionType source target (subst sigma element) (subst sigma predicate)
        (subst sigma length) (subst sigma vector) := by
  simp only [functionType, subst, Canonical.substitute_allTypeAtUniverse, subst_liftSub_wk]

def forwardAt {n : Nat} (element predicate length vector : Tower.Tm n) : Tower.Tm n :=
  subst (Universes.arguments element predicate length vector) forward

def backwardAt {n : Nat} (element predicate length vector : Tower.Tm n) : Tower.Tm n :=
  subst (Universes.arguments element predicate length vector) backward

theorem consCase_beta (R : Rules Tower.Head) {n : Nat}
    (length head tail recursive bundle : Tower.Tm n) :
    TypedEquality.Reduces R
      (.app (.app (.app (.app (.app consCase length) head) tail) recursive) bundle)
      (.pair (.fst bundle) (.app recursive (.snd bundle))) := by
  let body : Tower.Tm (n + 5) :=
    .pair (.fst (.var 0)) (.app (.var 1) (.snd (.var 0)))
  let sigma : Sub Tower.Head (n + 5) n :=
    consSub bundle (consSub recursive (consSub tail (consSub head (consSub length ids))))
  have beta := lams_beta (R := R) 5 body [length, head, tail, recursive, bundle] rfl
  have assignment : extendSub ids (fun j => [length, head, tail, recursive, bundle].getD j defaultTm) 5 = sigma := rfl
  rw [assignment] at beta
  have target : subst sigma body = .pair (.fst bundle) (.app recursive (.snd bundle)) := rfl
  rw [target] at beta
  exact beta

theorem nil_steps {n : Nat} (source target : LevelExpr Nat)
    (element predicate bundle : Tower.Tm n) :
    TypedEquality.Reduces rules
      (.app (map source target element predicate zeroTm (vnilApp element)) bundle) bundle := by
  apply Relation.ReflTransGen.head
  · apply StepCore.congAppFun
    apply StepCore.root
    exact RootStep.declared ⟨IotaEvidence.vecNil element (motive source target element predicate)
      (.lam (.var 0)) consCase⟩
  · exact Relation.ReflTransGen.single
      (StepCore.betaPi (root := rules.computation) (headEq := rules.headEq) (.var 0) bundle)

theorem cons_steps {n : Nat} (source target : LevelExpr Nat)
    (element predicate length head tail evidence rest : Tower.Tm n) :
    TypedEquality.Reduces rules
      (.app (map source target element predicate (succApp length)
        (vconsApp element length head tail)) (.pair evidence rest))
      (.pair evidence (.app (map source target element predicate length tail) rest)) := by
  apply Relation.ReflTransGen.head
  · apply StepCore.congAppFun
    apply StepCore.root
    exact RootStep.declared ⟨IotaEvidence.vecCons element (motive source target element predicate)
      (.lam (.var 0)) consCase length head tail⟩
  · refine (consCase_beta rules length head tail
      (map source target element predicate length tail) (.pair evidence rest)).trans ?_
    apply Relation.ReflTransGen.head
    · exact .congPairFst (.betaSigmaFst evidence rest)
    · exact Relation.ReflTransGen.single (.congPairSnd (.congAppArg (.betaSigmaSnd evidence rest)))

theorem substitute_motive {n m : Nat} (sigma : Sub Tower.Head n m)
    (source target : LevelExpr Nat) (element predicate : Tower.Tm n) :
    subst sigma (motive source target element predicate) =
      motive source target (subst sigma element) (subst sigma predicate) := by
  simp only [motive, subst, substitute_functionType, NativeVectorAll.subst_weaken2]
  rfl

theorem substitute_consCase {n m : Nat} (sigma : Sub Tower.Head n m) :
    subst sigma (consCase : Tower.Tm n) = (consCase : Tower.Tm m) := rfl

theorem substitute_map {n m : Nat} (sigma : Sub Tower.Head n m)
    (source target : LevelExpr Nat) (element predicate length vector : Tower.Tm n) :
    subst sigma (map source target element predicate length vector) =
      map source target (subst sigma element) (subst sigma predicate)
        (subst sigma length) (subst sigma vector) := by
  simp only [map, vecEliminateApp, subst, substitute_motive, substitute_consCase]
  rfl

theorem forwardAt_eq_map {n : Nat} (element predicate length vector : Tower.Tm n) :
    forwardAt element predicate length vector =
      map resultLevel upperLevel element predicate length vector := by
  unfold forwardAt forward
  rw [substitute_map]
  rfl

theorem backwardAt_eq_map {n : Nat} (element predicate length vector : Tower.Tm n) :
    backwardAt element predicate length vector =
      map upperLevel resultLevel element predicate length vector := by
  unfold backwardAt backward
  rw [substitute_map]
  rfl

theorem cons_unfolds {n : Nat} (source target : LevelExpr Nat)
    (element predicate length head tail bundle : Tower.Tm n) :
    TypedEquality.Reduces rules
      (.app (map source target element predicate (succApp length)
        (vconsApp element length head tail)) bundle)
      (.pair (.fst bundle) (.app (map source target element predicate length tail) (.snd bundle))) := by
  apply Relation.ReflTransGen.head
  · apply StepCore.congAppFun
    apply StepCore.root
    exact RootStep.declared ⟨IotaEvidence.vecCons element (motive source target element predicate)
      (.lam (.var 0)) consCase length head tail⟩
  · exact consCase_beta rules length head tail (map source target element predicate length tail) bundle

theorem canonical_steps {n : Nat} (source target : LevelExpr Nat)
    (element predicate : Tower.Tm n) :
    ∀ (values : List (Tower.Tm n)) (bundle : Tower.Tm n),
      TypedEquality.Reduces rules
        (.app (map source target element predicate (numeral values.length)
          (encodeVector element values)) bundle)
        (PairSpine.expand values.length bundle)
  | [], bundle => nil_steps source target element predicate bundle
  | head :: tail, bundle =>
      (cons_unfolds source target element predicate (numeral tail.length) head
        (encodeVector element tail) bundle).trans
        (Relation.ReflTransGen.lift (Tm.pair (.fst bundle))
          (fun _ _ step => StepCore.congPairSnd step) _ _
            (canonical_steps source target element predicate tail (.snd bundle)))

theorem canonical_head {n : Nat} (source target : LevelExpr Nat)
    (element predicate : Tower.Tm n) (values : List (Tower.Tm n)) (bundle : Tower.Tm n)
    (position : Nat) (inside : position < values.length) :
    TypedEquality.Reduces rules
      (PairSpine.head position (.app (map source target element predicate (numeral values.length)
        (encodeVector element values)) bundle))
      (PairSpine.head position bundle) :=
  (PairSpine.head_reduces rules position
    (canonical_steps source target element predicate values bundle)).trans
      (PairSpine.head_expand rules values.length position bundle inside)

theorem canonical_tail {n : Nat} (source target : LevelExpr Nat)
    (element predicate : Tower.Tm n) (values : List (Tower.Tm n)) (bundle : Tower.Tm n) :
    TypedEquality.Reduces rules
      (PairSpine.tail values.length (.app (map source target element predicate (numeral values.length)
        (encodeVector element values)) bundle))
      (PairSpine.tail values.length bundle) :=
  (PairSpine.tail_reduces rules values.length
    (canonical_steps source target element predicate values bundle)).trans
      (PairSpine.tail_expand rules values.length bundle)

theorem canonical_quote_steps {n : Nat} (source target : LevelExpr Nat)
    (element predicate : Tower.Tm n) (values witnesses : List (Tower.Tm n))
    (lengths : values.length = witnesses.length) :
    TypedEquality.Reduces rules
      (.app (map source target element predicate (numeral values.length)
        (encodeVector element values)) (quoteWitnesses witnesses)) (quoteWitnesses witnesses) := by
  refine (canonical_steps source target element predicate values (quoteWitnesses witnesses)).trans ?_
  rw [lengths]
  exact PairSpine.expand_of_reduces_to_assemble rules witnesses unitEvidence
    (quoteWitnesses witnesses) .refl



/-- The independently checked open program has the same instantiated source computation. -/
theorem forward_canonical_steps {n : Nat} (element predicate : Tower.Tm n)
    (values : List (Tower.Tm n)) (bundle : Tower.Tm n) :
    TypedEquality.Reduces rules
      (.app (forwardAt element predicate (numeral values.length) (encodeVector element values)) bundle)
      (PairSpine.expand values.length bundle) := by
  rw [forwardAt_eq_map]
  exact canonical_steps resultLevel upperLevel element predicate values bundle

theorem backward_canonical_steps {n : Nat} (element predicate : Tower.Tm n)
    (values : List (Tower.Tm n)) (bundle : Tower.Tm n) :
    TypedEquality.Reduces rules
      (.app (backwardAt element predicate (numeral values.length) (encodeVector element values)) bundle)
      (PairSpine.expand values.length bundle) := by
  rw [backwardAt_eq_map]
  exact canonical_steps upperLevel resultLevel element predicate values bundle

/-- The complete round trip computes to one expansion of the original
supplied bundle. This is stronger than its separate head and tail readouts;
identifying that expansion with a neutral bundle uses a pair eta judgment. -/
theorem roundtrip_steps {n : Nat} (source target : LevelExpr Nat)
    (element predicate : Tower.Tm n) (values : List (Tower.Tm n)) (bundle : Tower.Tm n) :
    TypedEquality.Reduces rules
      (.app (map target source element predicate (numeral values.length) (encodeVector element values))
        (.app (map source target element predicate (numeral values.length) (encodeVector element values)) bundle))
      (PairSpine.expand values.length bundle) := by
  have first := Relation.ReflTransGen.lift
    (Tm.app (map target source element predicate (numeral values.length) (encodeVector element values)))
    (fun _ _ step => StepCore.congAppArg step) _ _
      (canonical_steps source target element predicate values bundle)
  have second := canonical_steps target source element predicate values (PairSpine.expand values.length bundle)
  exact (first.trans second).trans (PairSpine.expand_idempotent rules values.length bundle)

/-- A round trip preserves every supplied head observation on constructor vectors. -/
theorem roundtrip_head {n : Nat} (source target : LevelExpr Nat)
    (element predicate : Tower.Tm n) (values : List (Tower.Tm n)) (bundle : Tower.Tm n)
    (position : Nat) (inside : position < values.length) :
    TypedEquality.Reduces rules
      (PairSpine.head position
        (.app (map target source element predicate (numeral values.length) (encodeVector element values))
          (.app (map source target element predicate (numeral values.length) (encodeVector element values)) bundle)))
      (PairSpine.head position bundle) := by
  exact (PairSpine.head_reduces rules position
    (roundtrip_steps source target element predicate values bundle)).trans
      (PairSpine.head_expand rules values.length position bundle inside)

/-- The final tail is preserved too; it is not silently replaced by canonical unit evidence. -/
theorem roundtrip_tail {n : Nat} (source target : LevelExpr Nat)
    (element predicate : Tower.Tm n) (values : List (Tower.Tm n)) (bundle : Tower.Tm n) :
    TypedEquality.Reduces rules
      (PairSpine.tail values.length
        (.app (map target source element predicate (numeral values.length) (encodeVector element values))
          (.app (map source target element predicate (numeral values.length) (encodeVector element values)) bundle)))
      (PairSpine.tail values.length bundle) := by
  exact (PairSpine.tail_reduces rules values.length
    (roundtrip_steps source target element predicate values bundle)).trans
      (PairSpine.tail_expand rules values.length bundle)

namespace ClosedRoundtrip

/-- Two constructor positions with one arbitrary supplied evidence variable. -/
def subject : Tower.Tm 1 :=
  .app (map upperLevel resultLevel natTm (.lam natTm) (numeral 2)
    (encodeVector natTm [zeroTm, zeroTm]))
    (.app (map resultLevel upperLevel natTm (.lam natTm) (numeral 2)
      (encodeVector natTm [zeroTm, zeroTm])) (.var 0))

theorem computes : TypedEquality.Reduces rules subject (PairSpine.expand 2 (.var 0)) :=
  roundtrip_steps resultLevel upperLevel natTm (.lam natTm) [zeroTm, zeroTm] (.var 0)

theorem nontrivial : subject ≠ PairSpine.expand 2 (.var 0) := by decide

end ClosedRoundtrip

#print axioms roundtrip_steps
#print axioms ClosedRoundtrip.computes

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps

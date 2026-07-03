import Mettapedia.GraphTheory.FourColor.GoertzelLemma814

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: explicit component certificates

The generated direct parent/path certificates in the current chain model check
`chainSpecifiedKempeStep`, which computes the two-color component from scratch.
That is fine for the length-two base tables, but it is too large for the
remaining representative words.

This module introduces the smaller certificate shape intended for those
representatives: a row supplies the switched component explicitly.  The checker
then verifies that the supplied component is pair-colored, connected from the
seed, closed under adjacent pair-colored chain edges, disjoint from the fixed
input, and that switching it gives the claimed parent state.
-/

namespace GoertzelLemma818ComponentCertificate

open GoertzelLemma814

structure ChainComponentMoveCertificate where
  move : ChainMove
  component : List ChainEdge
  deriving DecidableEq, BEq, Repr, Inhabited

def chainEdge (occ : Nat) (edge : TauEdge) : ChainEdge :=
  { occ := occ, edge := edge }

def certifiedComponentNextLayer (orients : List TauOrient)
    (component seen : List ChainEdge) : List ChainEdge :=
  component.filter fun e =>
    !seen.contains e && seen.any (chainEdgesShareEndpoint orients e)

def closeCertifiedComponent (orients : List TauOrient)
    (component : List ChainEdge) : Nat → List ChainEdge → List ChainEdge
  | 0, seen => seen
  | n + 1, seen =>
      let layer := certifiedComponentNextLayer orients component seen
      closeCertifiedComponent orients component n (appendFresh seen layer)

def certifiedComponentConnectedFromSeed (orients : List TauOrient)
    (component : List ChainEdge) (seed : ChainEdge) : Bool :=
  let reached := closeCertifiedComponent orients component component.length [seed]
  component.all fun e => reached.contains e

def certifiedComponentPairColored (orients : List TauOrient)
    (states : List TauState) (a c : LColor)
    (component : List ChainEdge) : Bool :=
  component.all fun e =>
    (chainEdges orients).contains e && chainEdgeInPair states a c e

/--
Closure check for an explicit two-color component.

Every pair-colored chain edge adjacent to the supplied component must already
belong to the component.  Together with connectedness from the seed, this is a
finite certificate that the supplied list is exactly the seed component in the
two-color subgraph, without reducing `chainComponent`.
-/
def certifiedComponentClosed (orients : List TauOrient)
    (states : List TauState) (a c : LColor)
    (component : List ChainEdge) : Bool :=
  (chainEdges orients).all fun e =>
    !chainEdgeInPair states a c e ||
      !component.any (chainEdgesShareEndpoint orients e) ||
        component.contains e

def certifiedComponentMoveAudit (orients : List TauOrient)
    (states : List TauState)
    (cert : ChainComponentMoveCertificate) : Bool :=
  let move := cert.move
  !cert.component.isEmpty &&
    (chainEdges orients).contains move.seed &&
    cert.component.contains move.seed &&
    certifiedComponentPairColored orients states move.a move.c cert.component &&
    certifiedComponentConnectedFromSeed orients cert.component move.seed &&
    certifiedComponentClosed orients states move.a move.c cert.component &&
    chainComponentAvoidsInputs orients cert.component

def chainCertifiedKempeStep (orients : List TauOrient)
    (s t : List TauState) (cert : ChainComponentMoveCertificate) : Bool :=
  certifiedComponentMoveAudit orients s cert &&
    chainAgreesWithSwitch orients s t cert.component cert.move.a cert.move.c

theorem certifiedComponentPairColored_mem_chainEdges
    {orients : List TauOrient} {states : List TauState}
    {a c : LColor} {component : List ChainEdge} {edge : ChainEdge}
    (hpair :
      certifiedComponentPairColored orients states a c component = true)
    (hmem : edge ∈ component) :
    edge ∈ chainEdges orients := by
  unfold certifiedComponentPairColored at hpair
  rw [List.all_eq_true] at hpair
  have hedge := hpair edge hmem
  simp only [Bool.and_eq_true] at hedge
  exact List.contains_iff_mem.mp hedge.1

theorem certifiedComponentPairColored_mem_pair
    {orients : List TauOrient} {states : List TauState}
    {a c : LColor} {component : List ChainEdge} {edge : ChainEdge}
    (hpair :
      certifiedComponentPairColored orients states a c component = true)
    (hmem : edge ∈ component) :
    chainEdgeInPair states a c edge = true := by
  unfold certifiedComponentPairColored at hpair
  rw [List.all_eq_true] at hpair
  have hedge := hpair edge hmem
  simp only [Bool.and_eq_true] at hedge
  exact hedge.2

theorem certifiedComponentClosed_mem_of_adjacent_component
    {orients : List TauOrient} {states : List TauState}
    {a c : LColor} {component : List ChainEdge} {edge : ChainEdge}
    (hclosed :
      certifiedComponentClosed orients states a c component = true)
    (hchain : edge ∈ chainEdges orients)
    (hpair : chainEdgeInPair states a c edge = true)
    (hshare :
      component.any (chainEdgesShareEndpoint orients edge) = true) :
    edge ∈ component := by
  unfold certifiedComponentClosed at hclosed
  rw [List.all_eq_true] at hclosed
  have hedge := hclosed edge hchain
  simp [hpair, hshare] at hedge
  exact hedge

theorem nextChainComponentLayer_subset_certifiedComponent
    {orients : List TauOrient} {states : List TauState}
    {a c : LColor} {component seen : List ChainEdge}
    (hclosed :
      certifiedComponentClosed orients states a c component = true)
    (hseen : ∀ edge, edge ∈ seen → edge ∈ component)
    {edge : ChainEdge}
    (hmem : edge ∈ nextChainComponentLayer orients states a c seen) :
    edge ∈ component := by
  unfold nextChainComponentLayer at hmem
  rw [List.mem_filter] at hmem
  rcases hmem with ⟨hchain, hpred⟩
  simp only [Bool.and_eq_true] at hpred
  rcases hpred with ⟨⟨hedgePair, _hfresh⟩, hshareSeen⟩
  have hshareComponent :
      component.any (chainEdgesShareEndpoint orients edge) = true := by
    rw [List.any_eq_true] at hshareSeen
    rcases hshareSeen with ⟨other, hother, hshare⟩
    exact list_any_true_of_mem (hseen other hother) hshare
  exact
    certifiedComponentClosed_mem_of_adjacent_component hclosed hchain
      hedgePair hshareComponent

theorem closeChainComponent_subset_certifiedComponent
    {orients : List TauOrient} {states : List TauState}
    {a c : LColor} {component : List ChainEdge} {seed edge : ChainEdge}
    {n : Nat}
    (hseed : seed ∈ component)
    (hclosed :
      certifiedComponentClosed orients states a c component = true)
    (hmem :
      edge ∈ closeChainComponent orients states a c n [seed]) :
    edge ∈ component :=
  closeChainComponent_lift_property orients states a c n [seed]
    (fun edge => edge ∈ component)
    (by
      intro edge hedge
      simp at hedge
      subst edge
      exact hseed)
    (by
      intro seen edge hseen hedge
      exact
        nextChainComponentLayer_subset_certifiedComponent hclosed hseen hedge)
    edge hmem

theorem chainComponent_subset_certifiedComponent
    {orients : List TauOrient} {states : List TauState}
    {a c : LColor} {component : List ChainEdge} {seed edge : ChainEdge}
    (hseed : seed ∈ component)
    (hpair :
      certifiedComponentPairColored orients states a c component = true)
    (hclosed :
      certifiedComponentClosed orients states a c component = true)
    (hmem : edge ∈ chainComponent orients states a c seed) :
    edge ∈ component := by
  have hseedPair : chainEdgeInPair states a c seed = true :=
    certifiedComponentPairColored_mem_pair hpair hseed
  exact
    closeChainComponent_subset_certifiedComponent hseed hclosed
      (by simpa [chainComponent, hseedPair] using hmem)

theorem certifiedComponentNextLayer_mem_closeChainComponent_succ
    {orients : List TauOrient} {states : List TauState}
    {a c : LColor} {component seen : List ChainEdge}
    {seed edge : ChainEdge} {m : Nat}
    (hpair :
      certifiedComponentPairColored orients states a c component = true)
    (hseen :
      ∀ edge, edge ∈ seen →
        edge ∈ closeChainComponent orients states a c m [seed])
    (hmem : edge ∈ certifiedComponentNextLayer orients component seen) :
    edge ∈ closeChainComponent orients states a c (m + 1) [seed] := by
  unfold certifiedComponentNextLayer at hmem
  rw [List.mem_filter] at hmem
  rcases hmem with ⟨hcomponent, hpred⟩
  simp only [Bool.and_eq_true] at hpred
  rcases hpred with ⟨hfresh, hshareSeen⟩
  have hnextSeen :
      edge ∈ nextChainComponentLayer orients states a c seen := by
    unfold nextChainComponentLayer
    rw [List.mem_filter]
    exact
      ⟨certifiedComponentPairColored_mem_chainEdges hpair hcomponent,
        by
          rw [certifiedComponentPairColored_mem_pair hpair hcomponent,
            hfresh, hshareSeen]
          rfl⟩
  rcases nextChainComponentLayer_mem_mono_seen
      orients states a c (seen₁ := seen)
      (seen₂ := closeChainComponent orients states a c m [seed])
      hseen hnextSeen with hclose | hnext
  · exact closeChainComponent_mem_mono_succ
      orients states a c m [seed] hclose
  · exact closeChainComponent_mem_nextLayer_close
      orients states a c m [seed] hnext

theorem closeCertifiedComponent_subset_closeChainComponent
    {orients : List TauOrient} {states : List TauState}
    {a c : LColor} {component seen : List ChainEdge}
    {seed edge : ChainEdge} {m n : Nat}
    (hpair :
      certifiedComponentPairColored orients states a c component = true)
    (hseen :
      ∀ edge, edge ∈ seen →
        edge ∈ closeChainComponent orients states a c m [seed])
    (hmem : edge ∈ closeCertifiedComponent orients component n seen) :
    edge ∈ closeChainComponent orients states a c (m + n) [seed] := by
  induction n generalizing seen m with
  | zero =>
      exact hseen edge (by simpa [closeCertifiedComponent] using hmem)
  | succ n ih =>
      simp only [closeCertifiedComponent] at hmem
      let layer := certifiedComponentNextLayer orients component seen
      let seen' := appendFresh seen layer
      have hseen' :
          ∀ edge, edge ∈ seen' →
            edge ∈ closeChainComponent orients states a c (m + 1) [seed] := by
        intro edge hedge
        rcases mem_appendFresh_source_or_mem seen layer hedge with
          hseenEdge | hlayer
        · exact closeChainComponent_mem_mono_succ
            orients states a c m [seed] (hseen edge hseenEdge)
        · exact
            certifiedComponentNextLayer_mem_closeChainComponent_succ
              hpair hseen hlayer
      have hrec := ih hseen' hmem
      have hnat : m + (n + 1) = (m + 1) + n := by omega
      simpa [hnat, seen', layer] using hrec

theorem certifiedComponent_subset_chainComponent
    {orients : List TauOrient} {states : List TauState}
    {a c : LColor} {component : List ChainEdge} {seed edge : ChainEdge}
    (hseed : seed ∈ component)
    (hpair :
      certifiedComponentPairColored orients states a c component = true)
    (hconnected :
      certifiedComponentConnectedFromSeed orients component seed = true)
    (hnodup : component.Nodup)
    (hmem : edge ∈ component) :
    edge ∈ chainComponent orients states a c seed := by
  have hseedPair : chainEdgeInPair states a c seed = true :=
    certifiedComponentPairColored_mem_pair hpair hseed
  have hreached :
      edge ∈ closeCertifiedComponent orients component component.length [seed] := by
    unfold certifiedComponentConnectedFromSeed at hconnected
    rw [List.all_eq_true] at hconnected
    exact List.contains_iff_mem.mp (hconnected edge hmem)
  have hcloseComponentLength :
      edge ∈ closeChainComponent orients states a c (0 + component.length)
        [seed] := by
    exact
      closeCertifiedComponent_subset_closeChainComponent hpair
        (by
          intro other hother
          simp at hother
          subst other
          exact closeChainComponent_mem_of_seen orients states a c 0
            (by simp))
        hreached
  have hcomponentSub : component ⊆ chainEdges orients := by
    intro other hother
    exact certifiedComponentPairColored_mem_chainEdges hpair hother
  have hlen : component.length ≤ (chainEdges orients).length :=
    List.Subperm.length_le (List.subperm_of_subset hnodup hcomponentSub)
  obtain ⟨extra, hextra⟩ := Nat.exists_eq_add_of_le hlen
  have hclose :
      edge ∈ closeChainComponent orients states a c
        (chainEdges orients).length [seed] := by
    rw [hextra]
    exact closeChainComponent_mem_mono_add orients states a c
      component.length extra [seed]
      (by simpa using hcloseComponentLength)
  simpa [chainComponent, hseedPair] using hclose

theorem chainCertifiedKempeStep_implies_single_of_audit_fields
    (orients : List TauOrient) (s t : List TauState)
    (cert : ChainComponentMoveCertificate)
    (hcolorPair :
      colorPairs.contains (cert.move.a, cert.move.c) = true)
    (hnodup : cert.component.Nodup)
    (_hnonempty : (!cert.component.isEmpty) = true)
    (hseedChain : (chainEdges orients).contains cert.move.seed = true)
    (hseedMem : cert.component.contains cert.move.seed = true)
    (hpair :
      certifiedComponentPairColored orients s cert.move.a cert.move.c
        cert.component = true)
    (hconnected :
      certifiedComponentConnectedFromSeed orients cert.component
        cert.move.seed = true)
    (hclosed :
      certifiedComponentClosed orients s cert.move.a cert.move.c
        cert.component = true)
    (havoid : chainComponentAvoidsInputs orients cert.component = true)
    (hagree :
      chainAgreesWithSwitch orients s t cert.component cert.move.a
        cert.move.c = true) :
    chainSingleKempeStep orients s t = true := by
  let realComponent :=
    chainComponent orients s cert.move.a cert.move.c cert.move.seed
  have hseedMemList : cert.move.seed ∈ cert.component :=
    List.contains_iff_mem.mp hseedMem
  have hrealSubset :
      ∀ edge, edge ∈ realComponent → edge ∈ cert.component := by
    intro edge hedge
    exact
      chainComponent_subset_certifiedComponent hseedMemList hpair hclosed
        (by simpa [realComponent] using hedge)
  have hcertSubset :
      ∀ edge, edge ∈ cert.component → edge ∈ realComponent := by
    intro edge hedge
    exact
      certifiedComponent_subset_chainComponent hseedMemList hpair
        hconnected hnodup hedge
  have hcontainsEq :
      ∀ edge, realComponent.contains edge =
        cert.component.contains edge := by
    intro edge
    by_cases hreal : edge ∈ realComponent
    · have hcert : edge ∈ cert.component := hrealSubset edge hreal
      rw [List.contains_iff_mem.mpr hreal,
        List.contains_iff_mem.mpr hcert]
    · have hnotCert : edge ∉ cert.component := by
        intro hcert
        exact hreal (hcertSubset edge hcert)
      have hrealFalse : realComponent.contains edge = false :=
        bool_false_of_not_true (by
          intro hcontains
          exact hreal (List.contains_iff_mem.mp hcontains))
      have hcertFalse : cert.component.contains edge = false :=
        bool_false_of_not_true (by
          intro hcontains
          exact hnotCert (List.contains_iff_mem.mp hcontains))
      rw [hrealFalse, hcertFalse]
  have hseedReal : cert.move.seed ∈ realComponent :=
    hcertSubset cert.move.seed hseedMemList
  have hrealNonempty : (!realComponent.isEmpty) = true := by
    cases hcomp : realComponent with
    | nil =>
        rw [hcomp] at hseedReal
        cases hseedReal
    | cons _ _ =>
        rfl
  have hrealAvoid : chainComponentAvoidsInputs orients realComponent = true := by
    have hrealFalse :
        realComponent.any (fun e => (chainOuterInputEdges orients).contains e) =
          false := by
      rw [List.any_eq_false]
      intro edge hedge houter
      have houterFalse :=
        chainComponentAvoidsInputs_contains_false orients cert.component
          havoid (hrealSubset edge hedge)
      rw [houterFalse] at houter
      cases houter
    unfold chainComponentAvoidsInputs
    rw [hrealFalse]
    rfl
  have hrealAgree :
      chainAgreesWithSwitch orients s t realComponent cert.move.a
        cert.move.c = true := by
    unfold chainAgreesWithSwitch at hagree ⊢
    rw [List.all_eq_true] at hagree ⊢
    intro ge hge
    have hgeAgree := hagree ge hge
    let canonical := chainCanonicalEdge orients ge
    change
      colorEq (chainEdgeColor t ge)
          (if realComponent.contains canonical = true then
            swapColor cert.move.a cert.move.c (chainEdgeColor s canonical)
          else
            chainEdgeColor s canonical) = true
    change
      colorEq (chainEdgeColor t ge)
          (if cert.component.contains canonical = true then
            swapColor cert.move.a cert.move.c (chainEdgeColor s canonical)
          else
            chainEdgeColor s canonical) = true at hgeAgree
    rw [hcontainsEq canonical]
    exact hgeAgree
  unfold chainSingleKempeStep
  rw [List.any_eq_true]
  refine ⟨(cert.move.a, cert.move.c),
    List.contains_iff_mem.mp hcolorPair, ?_⟩
  rw [List.any_eq_true]
  refine ⟨cert.move.seed, List.contains_iff_mem.mp hseedChain, ?_⟩
  change
    (!realComponent.isEmpty &&
      chainComponentAvoidsInputs orients realComponent &&
        chainAgreesWithSwitch orients s t realComponent cert.move.a
          cert.move.c) = true
  rw [hrealNonempty, hrealAvoid, hrealAgree]
  rfl

theorem chainCertifiedKempeStep_implies_single
    (orients : List TauOrient) (s t : List TauState)
    (cert : ChainComponentMoveCertificate)
    (hcolorPair :
      colorPairs.contains (cert.move.a, cert.move.c) = true)
    (hnodup : cert.component.Nodup)
    (hstep : chainCertifiedKempeStep orients s t cert = true) :
    chainSingleKempeStep orients s t = true := by
  unfold chainCertifiedKempeStep at hstep
  simp only [Bool.and_eq_true] at hstep
  rcases hstep with ⟨haudit, hagree⟩
  unfold certifiedComponentMoveAudit at haudit
  simp only [Bool.and_eq_true] at haudit
  rcases haudit with
    ⟨⟨⟨⟨⟨⟨hnonempty, hseedChain⟩, hseedMem⟩, hpair⟩,
      hconnected⟩, hclosed⟩, havoid⟩
  exact
    chainCertifiedKempeStep_implies_single_of_audit_fields orients s t cert
      hcolorPair hnodup hnonempty hseedChain hseedMem hpair hconnected
      hclosed havoid hagree

structure ChainFiberCertifiedParentRow where
  source : Nat
  parent : Nat
  cert : ChainComponentMoveCertificate
  deriving DecidableEq, BEq, Repr, Inhabited

structure ChainFiberCertifiedCertificate where
  key : List LColor
  root : Nat
  maxDepth : Nat
  rows : List ChainFiberCertifiedParentRow
  deriving DecidableEq, BEq, Repr, Inhabited

def chainFiberCertifiedParentFromRows :
    List ChainFiberCertifiedParentRow → Nat → Nat
  | [], i => i
  | row :: rows, i =>
      if row.source == i then row.parent
      else chainFiberCertifiedParentFromRows rows i

def chainFiberCertifiedParentIter
    (rows : List ChainFiberCertifiedParentRow) : Nat → Nat → Nat
  | 0, i => i
  | n + 1, i =>
      chainFiberCertifiedParentIter rows n
        (chainFiberCertifiedParentFromRows rows i)

def chainFiberCertifiedParentRowValidFrom (orients : List TauOrient)
    (statesList : List (List TauState)) (indices : List Nat)
    (row : ChainFiberCertifiedParentRow) : Bool :=
  indices.contains row.source &&
    indices.contains row.parent &&
      let s := listGetD statesList row.source []
      let t := listGetD statesList row.parent []
      chainInputKey orients s == chainInputKey orients t &&
        (row.source == row.parent || chainCertifiedKempeStep orients s t row.cert)

def chainFiberCertifiedParentCertificateAuditFrom
    (orients : List TauOrient) (statesList : List (List TauState))
    (cert : ChainFiberCertifiedCertificate) : Bool :=
  let indices := chainFiberIndicesFrom orients statesList cert.key
  cert.key.length == 4 &&
    cert.root == chainFiberRootIndex indices &&
    (cert.rows.map fun row => row.source) == indices &&
    cert.rows.all
      (chainFiberCertifiedParentRowValidFrom orients statesList indices) &&
    cert.rows.all fun row =>
      chainFiberCertifiedParentIter cert.rows cert.maxDepth row.source ==
        cert.root

def chainFiberCertifiedParentCertificateAudit
    (orients : List TauOrient)
    (cert : ChainFiberCertifiedCertificate) : Bool :=
  chainFiberCertifiedParentCertificateAuditFrom orients
    (allChainStates orients) cert

def componentCert (move : ChainMove) (component : List ChainEdge) :
    ChainComponentMoveCertificate :=
  { move := move, component := component }

def certifiedFiberRow (source parent : Nat) (move : ChainMove)
    (component : List ChainEdge) : ChainFiberCertifiedParentRow :=
  { source := source
    parent := parent
    cert := componentCert move component }

/--
The first single-`tau` fixed-input fiber checked again through explicit
component certificates.  This is a smoke test for the representative-target
certificate shape: no row asks Lean to compute `chainComponent`.
-/
def tauSingleNormalFiber0ComponentCertificate :
    ChainFiberCertifiedCertificate :=
  { key := chainInputKey [TauOrient.normal] [stateAt 0]
    root := 0
    maxDepth := 2
    rows :=
      [ certifiedFiberRow 0 0 default []
      , certifiedFiberRow 1 0
          (chainMove LColor.b LColor.p 0 TauEdge.B5)
          [ chainEdge 0 TauEdge.B5
          , chainEdge 0 TauEdge.B6
          ]
      , certifiedFiberRow 2 0
          (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
          [ chainEdge 0 TauEdge.F4F5
          , chainEdge 0 TauEdge.B5
          , chainEdge 0 TauEdge.B7
          ]
      , certifiedFiberRow 3 1
          (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
          [ chainEdge 0 TauEdge.F4F5
          , chainEdge 0 TauEdge.B6
          , chainEdge 0 TauEdge.B7
          ]
      , certifiedFiberRow 48 0
          (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
          [ chainEdge 0 TauEdge.F2F3
          , chainEdge 0 TauEdge.F2F4
          , chainEdge 0 TauEdge.B4
          , chainEdge 0 TauEdge.B7
          ]
      , certifiedFiberRow 49 1
          (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
          [ chainEdge 0 TauEdge.F2F3
          , chainEdge 0 TauEdge.F2F4
          , chainEdge 0 TauEdge.B4
          , chainEdge 0 TauEdge.B7
          ]
      , certifiedFiberRow 50 2
          (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
          [ chainEdge 0 TauEdge.F2F3
          , chainEdge 0 TauEdge.F2F4
          , chainEdge 0 TauEdge.B4
          , chainEdge 0 TauEdge.F4F5
          , chainEdge 0 TauEdge.B6
          ]
      , certifiedFiberRow 51 48
          (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
          [ chainEdge 0 TauEdge.F4F5
          , chainEdge 0 TauEdge.B6
          , chainEdge 0 TauEdge.B7
          ]
      ] }

def tauSingleNormalFiber0ComponentStates : List (List TauState) :=
  allChainStates [TauOrient.normal]

def tauSingleNormalFiber0ComponentRows : List ChainFiberCertifiedParentRow :=
  tauSingleNormalFiber0ComponentCertificate.rows

theorem tauSingleNormalFiber0Component_row1_ok :
    chainCertifiedKempeStep [TauOrient.normal]
      (listGetD tauSingleNormalFiber0ComponentStates 1 [])
      (listGetD tauSingleNormalFiber0ComponentStates 0 [])
      (componentCert
        (chainMove LColor.b LColor.p 0 TauEdge.B5)
        [ chainEdge 0 TauEdge.B5
        , chainEdge 0 TauEdge.B6
        ]) = true := by
  decide

theorem tauSingleNormalFiber0Component_row2_ok :
    chainCertifiedKempeStep [TauOrient.normal]
      (listGetD tauSingleNormalFiber0ComponentStates 2 [])
      (listGetD tauSingleNormalFiber0ComponentStates 0 [])
      (componentCert
        (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
        [ chainEdge 0 TauEdge.F4F5
        , chainEdge 0 TauEdge.B5
        , chainEdge 0 TauEdge.B7
        ]) = true := by
  decide

theorem tauSingleNormalFiber0Component_row3_ok :
    chainCertifiedKempeStep [TauOrient.normal]
      (listGetD tauSingleNormalFiber0ComponentStates 3 [])
      (listGetD tauSingleNormalFiber0ComponentStates 1 [])
      (componentCert
        (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
        [ chainEdge 0 TauEdge.F4F5
        , chainEdge 0 TauEdge.B6
        , chainEdge 0 TauEdge.B7
        ]) = true := by
  decide

theorem tauSingleNormalFiber0Component_row48_ok :
    chainCertifiedKempeStep [TauOrient.normal]
      (listGetD tauSingleNormalFiber0ComponentStates 48 [])
      (listGetD tauSingleNormalFiber0ComponentStates 0 [])
      (componentCert
        (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
        [ chainEdge 0 TauEdge.F2F3
        , chainEdge 0 TauEdge.F2F4
        , chainEdge 0 TauEdge.B4
        , chainEdge 0 TauEdge.B7
        ]) = true := by
  decide

theorem tauSingleNormalFiber0Component_row49_ok :
    chainCertifiedKempeStep [TauOrient.normal]
      (listGetD tauSingleNormalFiber0ComponentStates 49 [])
      (listGetD tauSingleNormalFiber0ComponentStates 1 [])
      (componentCert
        (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
        [ chainEdge 0 TauEdge.F2F3
        , chainEdge 0 TauEdge.F2F4
        , chainEdge 0 TauEdge.B4
        , chainEdge 0 TauEdge.B7
        ]) = true := by
  decide

theorem tauSingleNormalFiber0Component_row50_ok :
    chainCertifiedKempeStep [TauOrient.normal]
      (listGetD tauSingleNormalFiber0ComponentStates 50 [])
      (listGetD tauSingleNormalFiber0ComponentStates 2 [])
      (componentCert
        (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
        [ chainEdge 0 TauEdge.F2F3
        , chainEdge 0 TauEdge.F2F4
        , chainEdge 0 TauEdge.B4
        , chainEdge 0 TauEdge.F4F5
        , chainEdge 0 TauEdge.B6
        ]) = true := by
  decide

theorem tauSingleNormalFiber0Component_row51_ok :
    chainCertifiedKempeStep [TauOrient.normal]
      (listGetD tauSingleNormalFiber0ComponentStates 51 [])
      (listGetD tauSingleNormalFiber0ComponentStates 48 [])
      (componentCert
        (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
        [ chainEdge 0 TauEdge.F4F5
        , chainEdge 0 TauEdge.B6
        , chainEdge 0 TauEdge.B7
        ]) = true := by
  decide

def tauSingleNormalFiber0ComponentParentCheck : Bool :=
  [0, 1, 2, 3, 48, 49, 50, 51].all fun i =>
    chainFiberCertifiedParentIter
      tauSingleNormalFiber0ComponentRows 2 i == 0

theorem tauSingleNormalFiber0ComponentParentCheck_ok :
    tauSingleNormalFiber0ComponentParentCheck = true := by
  decide

end GoertzelLemma818ComponentCertificate

end Mettapedia.GraphTheory.FourColor

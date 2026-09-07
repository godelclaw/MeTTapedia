import Mettapedia.GraphTheory.FourColor.GeneralSlabEmbedding

/-!
# Nested ambient sides with persistent crossing wires

For nested vertex sides, an edge can cross both cuts without meeting a
vertex of the intervening layer. Such an edge is an identity wire, not a
boundary dart attached to a layer vertex. The decomposition below retains
its original ambient dart and equality of its two nonzero boundary colours.
No supplied slab shape or absence of persistent crossings is assumed.
-/

namespace Mettapedia.GraphTheory.FourColor.TubeSlab.NestedSideWire

open GoertzelV24RotationCutDartDecomposition

universe u
variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable {RS : RotationSystem.{u, u, u} V E} {inner outer : V → Prop}

noncomputable section

def layer (inner outer : V → Prop) : V → Prop := fun v => outer v ∧ ¬ inner v

/-- The vertex-attached slab API internalizes every edge of its inner
boundary. Consequently it cannot represent a persistent crossing wire. -/
theorem attachedSlab_enters {Vt It : Type u} {k : ℕ} [NeZero k]
    {T : GoertzelV24OpenTangleComposition.TwoSidedOpenTangleData Vt It (Fin k) (Fin k)}
    (S : SlabOf RS T inner) (b : BoundaryDart RS inner) :
    S.inner' (RS.vertOf (RS.alpha b.1.1)) := by
  obtain ⟨i, hi⟩ := S.boundary_inner b
  rw [hi, RS.alpha_involutive]
  exact S.slab_inner' (Sum.inr (Sum.inl i))

theorem coloring_ext {keep : V → Prop} {a b : SideColoring RS keep}
    (h : a.color = b.color) : a = b := by
  cases a
  cases b
  cases h
  rfl

/-- Restrict on literal ambient darts; internal mates and vertex properness
are inherited without a boundary reindexing. -/
def restrict {small big : V → Prop} (hsub : ∀ v, small v → big v)
    (c : SideColoring RS big) : SideColoring RS small where
  color d := c.color ⟨d.1, hsub _ d.2⟩
  alpha_internal d h := c.alpha_internal ⟨d.1, hsub _ d.2⟩ (hsub _ h)
  ne_zero _ := c.ne_zero _
  proper _ _ hv hne := c.proper _ _ hv
    (fun h => hne (Subtype.ext (congrArg (fun z : RetainedDart RS big => z.1) h)))

def SeamAgreement (ci : SideColoring RS inner)
    (cs : SideColoring RS (layer inner outer)) : Prop :=
  ∀ (d : RetainedDart RS inner) (hs : layer inner outer (RS.vertOf (RS.alpha d.1))),
    ci.color d = cs.color ⟨RS.alpha d.1, hs⟩

def glueColor (ci : SideColoring RS inner) (cs : SideColoring RS (layer inner outer))
    (d : RetainedDart RS outer) : Color := by
  classical
  exact if hi : inner (RS.vertOf d.1) then ci.color ⟨d.1, hi⟩
    else cs.color ⟨d.1, ⟨d.2, hi⟩⟩

theorem glueColor_inner (ci : SideColoring RS inner)
    (cs : SideColoring RS (layer inner outer)) (d : RetainedDart RS outer)
    (hi : inner (RS.vertOf d.1)) :
    glueColor ci cs d = ci.color ⟨d.1, hi⟩ := by simp [glueColor, hi]

theorem glueColor_layer (ci : SideColoring RS inner)
    (cs : SideColoring RS (layer inner outer)) (d : RetainedDart RS outer)
    (hi : ¬ inner (RS.vertOf d.1)) :
    glueColor ci cs d = cs.color ⟨d.1, ⟨d.2, hi⟩⟩ := by simp [glueColor, hi]

/-- Glue two actual vertex pieces. Equality is required precisely on edges
joining the pieces; persistent outer boundary edges are not internalized. -/
def glue (ci : SideColoring RS inner) (cs : SideColoring RS (layer inner outer))
    (ha : SeamAgreement ci cs) : SideColoring RS outer where
  color := glueColor ci cs
  alpha_internal d ho := by
    classical
    by_cases hi : inner (RS.vertOf d.1)
    · by_cases hj : inner (RS.vertOf (RS.alpha d.1))
      · rw [glueColor_inner ci cs _ hj, glueColor_inner ci cs _ hi]
        exact ci.alpha_internal ⟨d.1, hi⟩ hj
      · rw [glueColor_layer ci cs _ hj, glueColor_inner ci cs _ hi]
        exact (ha ⟨d.1, hi⟩ ⟨ho, hj⟩).symm
    · by_cases hj : inner (RS.vertOf (RS.alpha d.1))
      · rw [glueColor_inner ci cs _ hj, glueColor_layer ci cs _ hi]
        have hx : layer inner outer (RS.vertOf (RS.alpha (RS.alpha d.1))) := by
          simpa only [RS.alpha_involutive, layer] using And.intro d.2 hi
        simpa only [RS.alpha_involutive] using ha ⟨RS.alpha d.1, hj⟩ hx
      · rw [glueColor_layer ci cs _ hj, glueColor_layer ci cs _ hi]
        exact cs.alpha_internal ⟨d.1, ⟨d.2, hi⟩⟩ ⟨ho, hj⟩
  ne_zero d := by
    classical
    by_cases hi : inner (RS.vertOf d.1)
    · rw [glueColor_inner ci cs _ hi]; exact ci.ne_zero _
    · rw [glueColor_layer ci cs _ hi]; exact cs.ne_zero _
  proper d d' hv hne := by
    classical
    by_cases hi : inner (RS.vertOf d.1)
    · have hj : inner (RS.vertOf d'.1) := hv ▸ hi
      rw [glueColor_inner ci cs _ hi, glueColor_inner ci cs _ hj]
      exact ci.proper _ _ hv (fun h => hne
        (Subtype.ext (congrArg (fun z : RetainedDart RS inner => z.1) h)))
    · have hj : ¬ inner (RS.vertOf d'.1) := hv ▸ hi
      rw [glueColor_layer ci cs _ hi, glueColor_layer ci cs _ hj]
      exact cs.proper _ _ hv (fun h => hne
        (Subtype.ext (congrArg (fun z : RetainedDart RS (layer inner outer) => z.1) h)))

variable (hsub : ∀ v, inner v → outer v)

theorem seam_restrict (c : SideColoring RS outer) :
    SeamAgreement (restrict hsub c)
      (restrict (fun _ h => h.1 : ∀ v, layer inner outer v → outer v) c) := by
  intro d hs
  exact (c.alpha_internal ⟨d.1, hsub _ d.2⟩ hs.1).symm

@[simp] theorem restrict_glue_inner (ci : SideColoring RS inner)
    (cs : SideColoring RS (layer inner outer)) (ha : SeamAgreement ci cs) :
    restrict hsub (glue ci cs ha) = ci := by
  apply coloring_ext
  funext d
  exact glueColor_inner ci cs ⟨d.1, hsub _ d.2⟩ d.2

@[simp] theorem restrict_glue_layer (ci : SideColoring RS inner)
    (cs : SideColoring RS (layer inner outer)) (ha : SeamAgreement ci cs) :
    restrict (fun _ h => h.1 : ∀ v, layer inner outer v → outer v) (glue ci cs ha) = cs := by
  apply coloring_ext
  funext d
  exact glueColor_layer ci cs ⟨d.1, d.2.1⟩ d.2.2

@[simp] theorem glue_restrict (c : SideColoring RS outer) :
    glue (restrict hsub c)
      (restrict (fun _ h => h.1 : ∀ v, layer inner outer v → outer v) c)
      (seam_restrict hsub c) = c := by
  apply coloring_ext
  funext d
  classical
  change glueColor _ _ d = _
  by_cases hi : inner (RS.vertOf d.1)
  · rw [glueColor_inner _ _ _ hi]; rfl
  · rw [glueColor_layer _ _ _ hi]; rfl

/-- Restriction and gluing give an actual bijection, including multiplicity
of colourings. A persistent crossing edge is retained in the inner piece. -/
def coloringEquiv : SideColoring RS outer ≃
    {p : SideColoring RS inner × SideColoring RS (layer inner outer) //
      SeamAgreement p.1 p.2} where
  toFun c := ⟨⟨restrict hsub c, restrict (fun _ h => h.1) c⟩, seam_restrict hsub c⟩
  invFun p := glue p.1.1 p.1.2 p.2
  left_inv := glue_restrict hsub
  right_inv p := by
    apply Subtype.ext
    exact Prod.ext (restrict_glue_inner hsub _ _ _) (restrict_glue_layer _ _ _)

/-- A prescription on original ambient darts, without reindexing or
forgetting the identities of frozen edges. -/
def Respects {keep : V → Prop} (fixed : Set RS.D) (value : RS.D → Color)
    (c : SideColoring RS keep) : Prop :=
  ∀ d : RetainedDart RS keep, d.1 ∈ fixed → c.color d = value d.1

/-- If no prescribed dart is based in the intervening material, all frozen
data is already in the inner restriction. This includes through wires. -/
theorem respects_restrict_iff (fixed : Set RS.D) (value : RS.D → Color)
    (havoid : ∀ d ∈ fixed, outer (RS.vertOf d) → inner (RS.vertOf d))
    (c : SideColoring RS outer) :
    Respects fixed value (restrict hsub c) ↔ Respects fixed value c := by
  constructor
  · intro hc d hd
    exact hc ⟨d.1, havoid d.1 hd d.2⟩ hd
  · intro hc d hd
    exact hc ⟨d.1, hsub _ d.2⟩ hd

/-- The physical gluing bijection restricts to fixed ambient colour data.
Its inverse does not change any prescribed dart, including one crossing
both boundaries and having no vertex in the material layer. -/
def fixedColoringEquiv (fixed : Set RS.D) (value : RS.D → Color)
    (havoid : ∀ d ∈ fixed, outer (RS.vertOf d) → inner (RS.vertOf d)) :
    {c : SideColoring RS outer // Respects fixed value c} ≃
      {p : {p : SideColoring RS inner × SideColoring RS (layer inner outer) //
        SeamAgreement p.1 p.2} // Respects fixed value p.1.1} :=
  (coloringEquiv hsub).subtypeEquiv (fun c => (respects_restrict_iff hsub fixed value havoid c).symm)

/-- The same ambient dart viewed on the inner cut. No permutation, new
edge, or layer vertex is introduced for a through wire. -/
def throughFromOuter (b : BoundaryDart RS outer) (hi : inner (RS.vertOf b.1.1)) :
    BoundaryDart RS inner :=
  ⟨⟨b.1.1, hi⟩, fun h => b.2 (hsub _ h)⟩

theorem throughFromOuter_dart (b : BoundaryDart RS outer)
    (hi : inner (RS.vertOf b.1.1)) : (throughFromOuter hsub b hi).1.1 = b.1.1 := rfl

/-- Boundary equations for an actual colouring of the intervening layer.
The last clause is the nonzero identity-wire constraint, independent of
layer vertices; it is essential even when all material equations hold. -/
def LayerBoundary (x : BoundaryDart RS inner → Color) (y : BoundaryDart RS outer → Color)
    (cs : SideColoring RS (layer inner outer)) : Prop :=
  (∀ (b : BoundaryDart RS inner) (ho : outer (RS.vertOf (RS.alpha b.1.1))),
    cs.color ⟨RS.alpha b.1.1, ⟨ho, b.2⟩⟩ = x b) ∧
  (∀ (b : BoundaryDart RS outer) (hi : ¬ inner (RS.vertOf b.1.1)),
    cs.color ⟨b.1.1, ⟨b.1.2, hi⟩⟩ = y b) ∧
  (∀ (b : BoundaryDart RS outer) (hi : inner (RS.vertOf b.1.1)),
    x (throughFromOuter hsub b hi) = y b ∧ x (throughFromOuter hsub b hi) ≠ 0)

def SlabRel (x : BoundaryDart RS inner → Color) (y : BoundaryDart RS outer → Color) : Prop :=
  ∃ cs, LayerBoundary hsub x y cs

def boundaryWord {keep : V → Prop} (c : SideColoring RS keep) : BoundaryDart RS keep → Color :=
  fun b => c.color b.1

theorem layerBoundary_restrict (c : SideColoring RS outer) :
    LayerBoundary hsub (boundaryWord (restrict hsub c)) (boundaryWord c)
      (restrict (fun _ h => h.1) c) := by
  refine ⟨?_, ?_, ?_⟩
  · intro b ho
    exact c.alpha_internal ⟨b.1.1, hsub _ b.1.2⟩ ho
  · intro b hi; rfl
  · intro b hi; exact ⟨rfl, c.ne_zero b.1⟩

theorem seam_of_layerBoundary (ci : SideColoring RS inner)
    {cs : SideColoring RS (layer inner outer)} {x : BoundaryDart RS inner → Color}
    {y : BoundaryDart RS outer → Color} (hx : boundaryWord ci = x)
    (hc : LayerBoundary hsub x y cs) : SeamAgreement ci cs := by
  intro d hs
  exact (congrFun hx ⟨d, hs.2⟩).trans (hc.1 ⟨d, hs.2⟩ hs.1).symm

theorem boundaryWord_glue (ci : SideColoring RS inner)
    {cs : SideColoring RS (layer inner outer)} {x : BoundaryDart RS inner → Color}
    {y : BoundaryDart RS outer → Color} (hx : boundaryWord ci = x)
    (hc : LayerBoundary hsub x y cs) :
    boundaryWord (glue ci cs (seam_of_layerBoundary hsub ci hx hc)) = y := by
  funext b
  classical
  change glueColor ci cs b.1 = y b
  by_cases hi : inner (RS.vertOf b.1.1)
  · rw [glueColor_inner _ _ _ hi]
    exact (congrFun hx (throughFromOuter hsub b hi)).trans (hc.2.2 b hi).1
  · rw [glueColor_layer _ _ _ hi]
    exact hc.2.1 b hi

/-- Exact composition of the stack's side supports, with all persistent
crossings copied. No slab-shape or no-through-edge premise is required. -/
theorem mem_sideSupport_iff (y : BoundaryDart RS outer → Color) :
    y ∈ sideSupport RS outer ↔
      ∃ x, x ∈ sideSupport RS inner ∧ SlabRel hsub x y := by
  constructor
  · rintro ⟨c, hc⟩
    have hy : boundaryWord c = y := funext hc
    refine ⟨boundaryWord (restrict hsub c), ⟨restrict hsub c, fun _ => rfl⟩,
      restrict (fun _ h => h.1) c, ?_⟩
    rw [← hy]
    exact layerBoundary_restrict hsub c
  · rintro ⟨x, ⟨ci, hx⟩, cs, hc⟩
    refine ⟨glue ci cs (seam_of_layerBoundary hsub ci (funext hx) hc), ?_⟩
    exact congrFun (boundaryWord_glue hsub ci (funext hx) hc)

/-- Actual colourings with a specified boundary word. -/
def WordColoring {keep : V → Prop} (w : BoundaryDart RS keep → Color) :=
  {c : SideColoring RS keep // boundaryWord c = w}

def LayerWordColoring (x : BoundaryDart RS inner → Color)
    (y : BoundaryDart RS outer → Color) :=
  {cs : SideColoring RS (layer inner outer) // LayerBoundary hsub x y cs}

instance finiteSideColoring {keep : V → Prop} : Finite (SideColoring RS keep) :=
  Finite.of_injective (fun c => c.color) (fun _ _ h => coloring_ext h)

instance finiteWordColoring {keep : V → Prop} (w : BoundaryDart RS keep → Color) :
    Finite (WordColoring w) := inferInstanceAs (Finite {_c : SideColoring RS keep // _})

instance finiteLayerWordColoring (x : BoundaryDart RS inner → Color)
    (y : BoundaryDart RS outer → Color) : Finite (LayerWordColoring hsub x y) :=
  inferInstanceAs (Finite {_cs : SideColoring RS (layer inner outer) // _})

/-- The intermediate boundary word is determined by the inner colouring;
this prevents counting the same outer colouring more than once. -/
def assembleWord (y : BoundaryDart RS outer → Color)
    (p : Σ x, WordColoring x × LayerWordColoring hsub x y) : WordColoring y :=
  ⟨glue p.2.1.1 p.2.2.1 (seam_of_layerBoundary hsub _ p.2.1.2 p.2.2.2),
    boundaryWord_glue hsub _ p.2.1.2 p.2.2.2⟩

theorem assembleWord_injective (y : BoundaryDart RS outer → Color) :
    Function.Injective (assembleWord hsub y) := by
  rintro ⟨x, ⟨⟨ci, hci⟩, ⟨cs, hcs⟩⟩⟩ ⟨x', ⟨⟨ci', hci'⟩, ⟨cs', hcs'⟩⟩⟩ heq
  have hg := congrArg (fun z : WordColoring y => z.1) heq
  change glue ci cs (seam_of_layerBoundary hsub ci hci hcs) =
    glue ci' cs' (seam_of_layerBoundary hsub ci' hci' hcs') at hg
  have hi := congrArg (restrict hsub) hg
  simp only [restrict_glue_inner] at hi
  have hs := congrArg
    (restrict (fun _ h => h.1 : ∀ v, layer inner outer v → outer v)) hg
  simp only [restrict_glue_layer] at hs
  have hx : x = x' := hci.symm.trans ((congrArg boundaryWord hi).trans hci')
  cases hx
  cases hi
  cases hs
  rfl

theorem assembleWord_surjective (y : BoundaryDart RS outer → Color) :
    Function.Surjective (assembleWord hsub y) := by
  rintro ⟨c, hc⟩
  have hl : LayerBoundary hsub (boundaryWord (restrict hsub c)) y
      (restrict (fun _ h => h.1) c) := by
    rw [← hc]
    exact layerBoundary_restrict hsub c
  refine ⟨⟨boundaryWord (restrict hsub c), ⟨restrict hsub c, rfl⟩,
    ⟨restrict (fun _ h => h.1) c, hl⟩⟩, ?_⟩
  apply Subtype.ext
  exact glue_restrict hsub c

/-- Boundary-fibre decomposition, not just a support equivalence. -/
def wordColoringEquiv (y : BoundaryDart RS outer → Color) :
    (Σ x, WordColoring x × LayerWordColoring hsub x y) ≃ WordColoring y :=
  Equiv.ofBijective (assembleWord hsub y)
    ⟨assembleWord_injective hsub y, assembleWord_surjective hsub y⟩

def sideCount {keep : V → Prop} (w : BoundaryDart RS keep → Color) : ℕ :=
  Nat.card (WordColoring w)

def slabCount (x : BoundaryDart RS inner → Color) (y : BoundaryDart RS outer → Color) : ℕ :=
  Nat.card (LayerWordColoring hsub x y)

theorem sideCount_ne_zero_iff {keep : V → Prop} (w : BoundaryDart RS keep → Color) :
    sideCount w ≠ 0 ↔ w ∈ sideSupport RS keep := by
  rw [sideCount, Nat.card_ne_zero]
  constructor
  · rintro ⟨⟨⟨c, hc⟩⟩, _⟩
    exact ⟨c, congrFun hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨⟨⟨c, funext hc⟩⟩, inferInstance⟩

theorem slabCount_ne_zero_iff (x : BoundaryDart RS inner → Color)
    (y : BoundaryDart RS outer → Color) : slabCount hsub x y ≠ 0 ↔ SlabRel hsub x y := by
  rw [slabCount, Nat.card_ne_zero]
  constructor
  · rintro ⟨⟨⟨c, hc⟩⟩, _⟩
    exact ⟨c, hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨⟨⟨c, hc⟩⟩, inferInstance⟩

/-- Physical Count composition for nested sides: sum over the complete
inner boundary word, multiplying actual inner and layer multiplicities.
Persistent crossing wires appear in `slabCount` as nonzero identity constraints. -/
theorem sideCount_eq_sum (y : BoundaryDart RS outer → Color) :
    sideCount y = ∑ x : BoundaryDart RS inner → Color, sideCount x * slabCount hsub x y := by
  classical
  unfold sideCount slabCount
  rw [← Nat.card_congr (wordColoringEquiv hsub y), Nat.card_sigma]
  simp only [Nat.card_prod]

theorem slabCount_eq_zero_of_wire_mismatch
    (x : BoundaryDart RS inner → Color) (y : BoundaryDart RS outer → Color)
    (b : BoundaryDart RS outer) (hi : inner (RS.vertOf b.1.1))
    (hne : x (throughFromOuter hsub b hi) ≠ y b) : slabCount hsub x y = 0 := by
  letI : IsEmpty (LayerWordColoring hsub x y) :=
    ⟨fun c => hne (c.2.2.2 b hi).1⟩
  exact Nat.card_of_isEmpty

/-- Every input word accepted by a layer is nonzero, including the ports
whose edges never visit a layer vertex. -/
theorem LayerBoundary.input_ne_zero
    {x : BoundaryDart RS inner → Color} {y : BoundaryDart RS outer → Color}
    {cs : SideColoring RS (layer inner outer)} (hc : LayerBoundary hsub x y cs)
    (b : BoundaryDart RS inner) : x b ≠ 0 := by
  classical
  by_cases ho : outer (RS.vertOf (RS.alpha b.1.1))
  · rw [← hc.1 b ho]
    exact cs.ne_zero _
  · let bo : BoundaryDart RS outer := ⟨⟨b.1.1, hsub _ b.1.2⟩, ho⟩
    exact (hc.2.2 bo b.1.2).2

theorem LayerBoundary.output_ne_zero
    {x : BoundaryDart RS inner → Color} {y : BoundaryDart RS outer → Color}
    {cs : SideColoring RS (layer inner outer)} (hc : LayerBoundary hsub x y cs)
    (b : BoundaryDart RS outer) : y b ≠ 0 := by
  classical
  by_cases hi : inner (RS.vertOf b.1.1)
  · rw [← (hc.2.2 b hi).1]
    exact (hc.2.2 b hi).2
  · rw [← hc.2.1 b hi]
    exact cs.ne_zero _

theorem slabCount_eq_zero_of_zero_input
    (x : BoundaryDart RS inner → Color) (y : BoundaryDart RS outer → Color)
    (b : BoundaryDart RS inner) (hz : x b = 0) : slabCount hsub x y = 0 := by
  letI : IsEmpty (LayerWordColoring hsub x y) :=
    ⟨fun c => LayerBoundary.input_ne_zero hsub c.2 b hz⟩
  exact Nat.card_of_isEmpty

/-- The empty intervening layer has no dart colours to choose. Its boundary
behaviour consists only of the persistent wires. -/
def emptyLayerColoring (keep : V → Prop) : SideColoring RS (layer keep keep) where
  color d := False.elim (d.2.2 d.2.1)
  alpha_internal d _ := False.elim (d.2.2 d.2.1)
  ne_zero d := False.elim (d.2.2 d.2.1)
  proper d _ _ _ := False.elim (d.2.2 d.2.1)

theorem layerBoundary_refl (x : BoundaryDart RS inner → Color) (hx : ∀ b, x b ≠ 0) :
    LayerBoundary (fun _ h => h : ∀ v, inner v → inner v) x x
      (emptyLayerColoring inner) := by
  refine ⟨?_, ?_, ?_⟩
  · intro b ho; exact (b.2 ho).elim
  · intro b hi; exact (hi b.1.2).elim
  · intro b hi; exact ⟨rfl, hx b⟩

/-- The zero-material physical transfer is the identity on nonzero Tait
words, with zero rows on words containing the zero colour. -/
theorem slabCount_refl (x y : BoundaryDart RS inner → Color) :
    slabCount (fun _ h => h : ∀ v, inner v → inner v) x y =
      if x = y ∧ ∀ b, x b ≠ 0 then 1 else 0 := by
  classical
  by_cases hxy : x = y
  · subst y
    by_cases hx : ∀ b, x b ≠ 0
    · rw [if_pos ⟨rfl, hx⟩]
      apply Nat.card_eq_one_iff_exists.mpr
      refine ⟨⟨emptyLayerColoring inner, layerBoundary_refl x hx⟩, ?_⟩
      intro c
      apply Subtype.ext
      apply coloring_ext
      funext d
      exact (d.2.2 d.2.1).elim
    · rw [if_neg (fun h => hx h.2)]
      obtain ⟨b, hb⟩ := not_forall.mp hx
      exact slabCount_eq_zero_of_zero_input (fun _ h => h) x x b (not_not.mp hb)
  · rw [if_neg (fun h => hxy h.1)]
    obtain ⟨b, hb⟩ := Function.ne_iff.mp hxy
    exact slabCount_eq_zero_of_wire_mismatch (fun _ h => h) x y b b.1.2 hb

section Coordinates

open GoertzelV24OpenTangleComposition GoertzelV24PhysicalClosedCountBridge
open GoertzelV24ClosedCountReplacement

variable {L R : Type u}

/-- Input coordinate of a persistent output wire. This map is induced by
the literal ambient dart; arbitrary independent port permutations are not
silently identified. -/
def wireIndex (mi : L ≃ BoundaryDart RS inner) (mo : R ≃ BoundaryDart RS outer)
    (r : R) (hi : inner (RS.vertOf (mo r).1.1)) : L :=
  mi.symm (throughFromOuter hsub (mo r) hi)

theorem wireIndex_dart (mi : L ≃ BoundaryDart RS inner) (mo : R ≃ BoundaryDart RS outer)
    (r : R) (hi : inner (RS.vertOf (mo r).1.1)) :
    (mi (wireIndex hsub mi mo r hi)).1.1 = (mo r).1.1 := by
  simp only [wireIndex, Equiv.apply_symm_apply, throughFromOuter_dart]

def coordinateRel (mi : L ≃ BoundaryDart RS inner) (mo : R ≃ BoundaryDart RS outer)
    (x : L → Color) (y : R → Color) : Prop :=
  SlabRel hsub (fun b => x (mi.symm b)) (fun b => y (mo.symm b))

theorem coordinateRel_wire (mi : L ≃ BoundaryDart RS inner)
    (mo : R ≃ BoundaryDart RS outer) {x : L → Color} {y : R → Color}
    (hrel : coordinateRel hsub mi mo x y) (r : R)
    (hi : inner (RS.vertOf (mo r).1.1)) : x (wireIndex hsub mi mo r hi) = y r := by
  obtain ⟨cs, hc⟩ := hrel
  simpa only [wireIndex, Equiv.symm_apply_apply] using (hc.2.2 (mo r) hi).1

/-- Consumer bridge to the existing physical inner supports. Coordinates
may be the stack's cyclic labels; their geometric admissibility is not
asserted by this purely colouring-level transport. -/
theorem mem_innerSupport_iff (mi : L ≃ BoundaryDart RS inner)
    (mo : R ≃ BoundaryDart RS outer) (ri : RetainedDart RS inner)
    (ro : RetainedDart RS outer) (y : R → Color) :
    y ∈ innerSupport (rightClosedPortTangle (OpenTangleData.ofVertexSide RS outer ro) mo) ↔
      ∃ x, x ∈ innerSupport
        (rightClosedPortTangle (OpenTangleData.ofVertexSide RS inner ri) mi) ∧
        coordinateRel hsub mi mo x y := by
  rw [mem_innerSupport_ofVertexSide_iff, mem_sideSupport_iff hsub]
  constructor
  · rintro ⟨x, hx, hrel⟩
    refine ⟨fun l => x (mi l), ?_, ?_⟩
    · rw [mem_innerSupport_ofVertexSide_iff]
      simpa only [Equiv.apply_symm_apply] using hx
    · simpa only [coordinateRel, Equiv.apply_symm_apply] using hrel
  · rintro ⟨x, hx, hrel⟩
    refine ⟨fun b => x (mi.symm b), ?_, hrel⟩
    exact (mem_innerSupport_ofVertexSide_iff RS inner ri mi x).mp hx

end Coordinates

end
end Mettapedia.GraphTheory.FourColor.TubeSlab.NestedSideWire

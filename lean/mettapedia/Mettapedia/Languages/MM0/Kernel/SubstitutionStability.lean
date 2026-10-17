import Mettapedia.Languages.MM0.Kernel.Proof
import Mettapedia.Languages.MM0.Kernel.ProofChecking
import Mettapedia.Languages.MM0.Kernel.DefinitionFreeConversion
import Mettapedia.Computability.ComputationalTrinity

/-!
# MM0 judgments are stable under admissible substitution

An admissible substitution sends the variables of a formal context to
expressions of a target context: bound variables to bound variables of the
same sort, regular variables to saturated expressions of their sort, and every
bound image avoids the expressions substituted for variables that do not
depend on it.

* **Freshness transports** (`Admissible.transport_fresh`): a bound variable
  that does not occur in an expression has an image that does not occur in the
  substituted expression.
* **Admissibility composes** (`Admissible.comp`) and the identity substitution
  of a context is admissible (`admissible_identity`).
* **Conversion is stable** (`Admissible.converts`), including definition
  unfolding: the substituted dummy images stay fresh (`Admissible.unfolds`).
* **Derivability is stable** (`Admissible.derives`): theorem applications
  compose their instantiations with the substitution.
* **Checked witnesses are stable** (`Admissible.checksConv`,
  `Admissible.checks`): a proof witness moved along the substitution
  (`moveProof`) checks the substituted judgment.

Hence contexts and admissible substitutions form a category
(`AdmissibleContext`), derivable statements form a presheaf on it
(`derivableFace`), and so do checked proof witnesses (`witnessFace`).
Forgetting the witness is a natural transformation onto derivability
(`forgetWitness`), surjective at every context (`forgetWitness_surjective`)
and not injective (`SubstitutionStabilityControls.two_witnesses`): MM0
derivability is a contextual face, not only a property of the empty context,
and its retained certificates move with it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel

open Preterm

namespace Substitution

variable {signature : TermSignature}

/-! ## Freshness and support under substitution -/

/-- **Freshness transports along an admissible substitution.** -/
theorem Admissible.transport_fresh {formal target : Context} {expressions : List Preterm}
    (admitted : Admissible signature formal target expressions) {bound image sort : Nat}
    (formalBound : formal[bound]? = some (.bound sort))
    (boundImage : expressions[bound]? = some (.var image)) {source result : Preterm}
    (fresh : ¬ HasVar formal bound source)
    (substituted : Substitutes (ofList expressions) source result) :
    ¬ HasVar target image result := by
  induction substituted with
  | @var index value lookup =>
      have inRange : index < formal.length := by
        rw [← admitted.length_eq]
        exact (List.getElem?_eq_some_iff.mp lookup).1
      obtain ⟨binder, formalLookup⟩ : ∃ binder, formal[index]? = some binder :=
        ⟨formal[index], List.getElem?_eq_getElem inRange⟩
      exact admitted.preserves_independence formalBound formalLookup fresh boundImage lookup
  | term index => intro has; cases has
  | app _ _ functionIh argumentIh =>
      intro has
      rcases (hasVar_app_iff _ _ _ _).mp has with inFunction | inArgument
      · exact functionIh (fun h => fresh (.function h)) inFunction
      · exact argumentIh (fun h => fresh (.argument h)) inArgument

theorem Admissible.lookup_fits {formal target : Context} {expressions : List Preterm}
    (admitted : Admissible signature formal target expressions) {index : Nat}
    {value : Preterm} (lookup : expressions[index]? = some value) :
    ∃ binder, formal[index]? = some binder ∧ FitsBinder signature target value binder := by
  have inRange : index < formal.length := by
    rw [← admitted.length_eq]
    exact (List.getElem?_eq_some_iff.mp lookup).1
  refine ⟨formal[index], List.getElem?_eq_getElem inRange, ?_⟩
  exact typed_lookup admitted.typed (List.getElem?_eq_getElem inRange) lookup

/-- Substituted expressions have support in the target context. -/
theorem Admissible.support_of_substitutes {formal target : Context}
    {expressions : List Preterm} (admitted : Admissible signature formal target expressions)
    {source result : Preterm} (substituted : Substitutes (ofList expressions) source result) :
    ∃ support, Supports target result support := by
  induction substituted with
  | var lookup =>
      obtain ⟨binder, _, fits⟩ := admitted.lookup_fits lookup
      exact fits.support_exists
  | term index => exact ⟨_, .term index⟩
  | app _ _ functionIh argumentIh =>
      obtain ⟨left, leftSupport⟩ := functionIh
      obtain ⟨right, rightSupport⟩ := argumentIh
      exact ⟨_, .app leftSupport rightSupport⟩

/-- A bound formal variable is sent to a bound target variable of its sort. -/
theorem Admissible.bound_image {formal target : Context} {expressions : List Preterm}
    (admitted : Admissible signature formal target expressions) {index sort : Nat}
    (formalBound : formal[index]? = some (.bound sort)) :
    ∃ image, expressions[index]? = some (.var image) ∧ target[image]? = some (.bound sort) := by
  have inRange : index < expressions.length := by
    rw [admitted.length_eq]
    exact (List.getElem?_eq_some_iff.mp formalBound).1
  obtain ⟨value, valueLookup⟩ : ∃ value, expressions[index]? = some value :=
    ⟨_, List.getElem?_eq_getElem inRange⟩
  have fits := typed_lookup admitted.typed formalBound valueLookup
  cases fits with
  | bound lookup => exact ⟨_, valueLookup, lookup⟩

/-- An expression typed in the formal context can be substituted. -/
theorem Admissible.substitutes_of_hasType {formal target : Context}
    {expressions : List Preterm} (admitted : Admissible signature formal target expressions)
    {source : Preterm} {remaining : Context} {sort : Nat}
    (typing : HasType signature formal source remaining sort) :
    ∃ result, Substitutes (ofList expressions) source result ∧
      HasType signature target result remaining sort := by
  obtain ⟨result, computed⟩ := admitted.instantiate_defined typing
  obtain ⟨_, substituted⟩ := (instantiate_eq_some_iff _ _ _ _ _ _).mp computed
  exact ⟨result, substituted, typing.substitute admitted.typed substituted⟩

theorem Admissible.fitsBinder {formal target : Context} {expressions : List Preterm}
    (admitted : Admissible signature formal target expressions) {source result : Preterm}
    {binder : Binder} (fits : FitsBinder signature formal source binder)
    (substituted : Substitutes (ofList expressions) source result) :
    FitsBinder signature target result binder := by
  cases fits with
  | bound lookup =>
      cases substituted with
      | var image =>
          obtain ⟨found, imageLookup, targetLookup⟩ := admitted.bound_image lookup
          change expressions[_]? = _ at image
          rw [image] at imageLookup
          cases imageLookup
          exact .bound targetLookup
  | regular typing => exact .regular (typing.substitute admitted.typed substituted)

/-! ## Lists -/

theorem forall₂_exists {α β : Type} {relation : α → β → Prop} :
    ∀ {sources : List α}, (∀ source ∈ sources, ∃ result, relation source result) →
      ∃ results, List.Forall₂ relation sources results
  | [], _ => ⟨[], .nil⟩
  | source :: sources, defined => by
      obtain ⟨result, related⟩ := defined source (by simp)
      obtain ⟨results, rest⟩ := forall₂_exists (sources := sources)
        (fun other member => defined other (List.mem_cons_of_mem _ member))
      exact ⟨result :: results, .cons related rest⟩

theorem forall₂_deterministic {substitution : Substitution} :
    ∀ {sources first second : List Preterm},
      List.Forall₂ (Substitutes substitution) sources first →
      List.Forall₂ (Substitutes substitution) sources second → first = second
  | [], [], [], .nil, .nil => rfl
  | _ :: _, _ :: _, _ :: _, .cons head rest, .cons head' rest' => by
      rw [head.deterministic head', forall₂_deterministic rest rest']

/-- Substituting the images of a list substitution is substituting along the
composite list. -/
theorem ofList_compose {values images : List Preterm} {expressions : List Preterm}
    (substituted : List.Forall₂ (Substitutes (ofList expressions)) values images) :
    compose (ofList expressions) (ofList values) = ofList images := by
  funext index
  simp only [compose, ofList]
  induction substituted generalizing index with
  | nil => simp
  | cons head _ ih =>
      cases index with
      | zero => simpa using head.eval
      | succ index => simpa using ih index

theorem substitutes_compose_iff {values images expressions : List Preterm}
    (substituted : List.Forall₂ (Substitutes (ofList expressions)) values images)
    {source result : Preterm} :
    Substitutes (ofList images) source result ↔
      ∃ middle, Substitutes (ofList values) source middle ∧
        Substitutes (ofList expressions) middle result := by
  rw [← ofList_compose substituted]
  exact ⟨Substitutes.factor, fun ⟨_, before, after⟩ => before.compose after⟩

/-- A second substitution is defined on every image of a first one whose
values it can substitute. -/
theorem substitutes_after {values expressions : List Preterm}
    (defined : ∀ (index : Nat) (value : Preterm), values[index]? = some value →
      ∃ result, Substitutes (ofList expressions) value result)
    {source middle : Preterm} (substituted : Substitutes (ofList values) source middle) :
    ∃ result, Substitutes (ofList expressions) middle result := by
  induction substituted with
  | var lookup => exact defined _ _ lookup
  | term index => exact ⟨_, .term index⟩
  | app _ _ functionIh argumentIh =>
      obtain ⟨function', functionSubstituted⟩ := functionIh
      obtain ⟨argument', argumentSubstituted⟩ := argumentIh
      exact ⟨_, .app functionSubstituted argumentSubstituted⟩

/-! ## Composition and identity -/

theorem forall₂_lookup {α β : Type} {relation : α → β → Prop} :
    ∀ {sources : List α} {results : List β}, List.Forall₂ relation sources results →
      ∀ {index : Nat} {result : β}, results[index]? = some result →
        ∃ source, sources[index]? = some source ∧ relation source result
  | [], [], .nil, _, _, lookup => by simp at lookup
  | _ :: _, _ :: _, .cons head rest, index, result, lookup => by
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at lookup
          subst lookup
          exact ⟨_, rfl, head⟩
      | succ index =>
          simp only [List.getElem?_cons_succ] at lookup
          exact forall₂_lookup rest lookup

/-- **Admissibility composes.** -/
theorem Admissible.comp {first middle last : Context} {values expressions images : List Preterm}
    (before : Admissible signature first middle values)
    (after : Admissible signature middle last expressions)
    (substituted : List.Forall₂ (Substitutes (ofList expressions)) values images) :
    Admissible signature first last images := by
  have typed : List.Forall₂ (FitsBinder signature last) images first := by
    have fits := before.typed
    clear before
    induction substituted generalizing first with
    | nil => cases fits; exact .nil
    | cons head _ ih =>
        cases fits with
        | cons headFits restFits => exact .cons (after.fitsBinder headFits head) (ih restFits)
  refine ⟨typed, ?_⟩
  rintro ⟨⟨binder, expression⟩, position⟩ member sort image same ⟨⟨otherBinder, otherExpression⟩,
    otherPosition⟩ otherMember notDepends
  simp only [Prod.mk.injEq] at same
  obtain ⟨rfl, rfl⟩ := same
  simp only [entries, List.mem_zipIdx_iff_getElem?, List.getElem?_zip_eq_some] at member otherMember
  obtain ⟨formalLookup, imageLookup⟩ := member
  obtain ⟨otherFormal, otherImageLookup⟩ := otherMember
  obtain ⟨value, valueLookup, valueSubstituted⟩ := forall₂_lookup substituted imageLookup
  obtain ⟨otherValue, otherValueLookup, otherSubstituted⟩ :=
    forall₂_lookup substituted otherImageLookup
  have boundFits := typed_lookup before.typed formalLookup valueLookup
  cases boundFits with
  | @bound middleIndex _ middleLookup =>
      cases valueSubstituted with
      | var middleImage =>
          have middleFresh : ¬ HasVar middle middleIndex otherValue := by
            have sourceMember : ((.bound sort, .var middleIndex), position) ∈
                entries first values := by
              simp [entries, List.mem_zipIdx_iff_getElem?, List.getElem?_zip_eq_some,
                formalLookup, valueLookup]
            have otherSourceMember : ((otherBinder, otherValue), otherPosition) ∈
                entries first values := by
              simp [entries, List.mem_zipIdx_iff_getElem?, List.getElem?_zip_eq_some,
                otherFormal, otherValueLookup]
            exact before.independent _ sourceMember sort middleIndex rfl _ otherSourceMember
              notDepends
          exact after.transport_fresh middleLookup middleImage middleFresh otherSubstituted

/-- The identity substitution of a context. -/
def identityList (context : Context) : List Preterm :=
  (List.range context.length).map Preterm.var

theorem identityList_getElem? (context : Context) (index : Nat) :
    (identityList context)[index]? = if index < context.length then some (.var index) else none := by
  simp only [identityList, List.getElem?_map]
  split
  · rename_i inRange
    simp [List.getElem?_eq_getElem (by simpa using inRange : index < (List.range context.length).length)]
  · rename_i outside
    simp [List.getElem?_eq_none (by simpa using outside : (List.range context.length).length ≤ index)]

/-- **The identity substitution is admissible.** -/
theorem admissible_identity (context : Context) : Admissible signature context context (identityList context) := by
  have typed : List.Forall₂ (FitsBinder signature context) (identityList context) context := by
    rw [List.forall₂_iff_get]
    refine ⟨by simp [identityList], fun index inRange _ => ?_⟩
    simp only [identityList, List.get_eq_getElem, List.getElem_map, List.getElem_range]
    have lookup : context[index]? = some context[index] :=
      List.getElem?_eq_getElem (by simpa [identityList] using inRange)
    cases binder : context[index] with
    | bound sort => exact .bound (binder ▸ lookup)
    | regular sort dependencies =>
        exact .regular (by
          have typing := HasType.var (signature := signature) (binder ▸ lookup)
          simpa [Binder.sort] using typing)
  refine ⟨typed, ?_⟩
  rintro ⟨⟨binder, expression⟩, position⟩ member sort image same ⟨⟨otherBinder, otherExpression⟩,
    otherPosition⟩ otherMember notDepends
  simp only [Prod.mk.injEq] at same
  obtain ⟨rfl, rfl⟩ := same
  simp only [entries, List.mem_zipIdx_iff_getElem?, List.getElem?_zip_eq_some,
    identityList_getElem?] at member otherMember
  obtain ⟨formalLookup, imageLookup⟩ := member
  obtain ⟨otherFormal, otherImageLookup⟩ := otherMember
  split at imageLookup
  · simp only [Option.some.injEq, Preterm.var.injEq] at imageLookup
    subst imageLookup
    split at otherImageLookup
    · simp only [Option.some.injEq] at otherImageLookup
      subst otherImageLookup
      exact fun has => notDepends ((Binder.dependsOn_iff_hasVar otherFormal).mpr has)
    · cases otherImageLookup
  · cases imageLookup

theorem substitutes_identity {context : Context} {source : Preterm}
    (inScope : ∀ index, Occurs index source → index < context.length) :
    Substitutes (ofList (identityList context)) source source := by
  apply substitute_sound
  rw [substitute_congr (ofList (identityList context)) Substitution.identity source
    (fun index occurs => by simp [ofList, identityList_getElem?, inScope index occurs,
      Substitution.identity])]
  exact substitute_identity source

theorem forall₂_mem {α β : Type} {relation : α → β → Prop} :
    ∀ {sources : List α} {results : List β}, List.Forall₂ relation sources results →
      ∀ {result : β}, result ∈ results → ∃ source ∈ sources, relation source result
  | [], [], .nil, _, member => by simp at member
  | _ :: _, _ :: _, .cons head rest, result, member => by
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨_, List.mem_cons_self, head⟩
      · obtain ⟨source, sourceMember, related⟩ := forall₂_mem rest later
        exact ⟨source, List.mem_cons_of_mem _ sourceMember, related⟩

/-! ## Unfolding -/

/-- Fresh dummy images stay fresh under an admissible substitution. -/
theorem Admissible.freshDummies {formal target : Context} {expressions : List Preterm}
    (admitted : Admissible signature formal target expressions) {arguments : List Preterm}
    {sorts images : List Nat} (fresh : Definition.FreshDummies formal arguments sorts images) :
    ∀ {arguments' : List Preterm} {images' : List Nat},
      List.Forall₂ (Substitutes (ofList expressions)) arguments arguments' →
      List.Forall₂ (fun image image' => expressions[image]? = some (.var image')) images images' →
      Definition.FreshDummies target arguments' sorts images' := by
  induction fresh with
  | nil => intro arguments' images' _ imagesMoved; cases imagesMoved; exact .nil _
  | @cons arguments sort image sorts images lookup freshFor rest ih =>
      intro arguments' images' argumentsMoved imagesMoved
      cases imagesMoved with
      | @cons _ image' _ images'' moved restMoved =>
          obtain ⟨found, foundLookup, targetLookup⟩ := admitted.bound_image lookup
          rw [moved] at foundLookup
          cases foundLookup
          refine .cons targetLookup (fun expression' member => ?_) ?_
          · obtain ⟨expression, expressionMember, substituted⟩ := forall₂_mem argumentsMoved member
            exact ⟨admitted.support_of_substitutes substituted,
              admitted.transport_fresh lookup moved (freshFor expression expressionMember).2
                substituted⟩
          · exact ih (List.rel_append argumentsMoved (.cons (.var moved) .nil)) restMoved

theorem freshDummies_bound {formal : Context} {arguments : List Preterm} {sorts images : List Nat}
    (fresh : Definition.FreshDummies formal arguments sorts images) :
    ∀ image ∈ images, ∃ sort, formal[image]? = some (.bound sort) := by
  induction fresh with
  | nil => simp
  | cons lookup _ _ ih =>
      intro image member
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨_, lookup⟩
      · exact ih image later

theorem Admissible.fitsBinders {formal target : Context} {expressions : List Preterm}
    (admitted : Admissible signature formal target expressions) :
    ∀ {sources results : List Preterm} {binders : Context},
      List.Forall₂ (FitsBinder signature formal) sources binders →
      List.Forall₂ (Substitutes (ofList expressions)) sources results →
      List.Forall₂ (FitsBinder signature target) results binders
  | [], [], [], .nil, .nil => .nil
  | _ :: _, _ :: _, _ :: _, .cons headFits restFits, .cons head rest =>
      .cons (admitted.fitsBinder headFits head) (admitted.fitsBinders restFits rest)

theorem forall₂_var_images {expressions : List Preterm} :
    ∀ {images images' : List Nat},
      List.Forall₂ (fun image image' => expressions[image]? = some (.var image')) images images' →
      List.Forall₂ (Substitutes (ofList expressions)) (images.map Preterm.var)
        (images'.map Preterm.var)
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons head rest => .cons (.var head) (forall₂_var_images rest)

/-- The image of a variable under a list substitution, when that image is a
variable; otherwise the variable itself. -/
def variableImage (expressions : List Preterm) (index : Nat) : Nat :=
  match expressions[index]? with
  | some (.var image) => image
  | _ => index

theorem variableImage_eq {expressions : List Preterm} {index image : Nat}
    (lookup : expressions[index]? = some (.var image)) : variableImage expressions index = image := by
  simp [variableImage, lookup]

theorem forall₂_variableImage {expressions : List Preterm} :
    ∀ {images images' : List Nat},
      List.Forall₂ (fun image image' => expressions[image]? = some (.var image')) images images' →
        images' = images.map (variableImage expressions)
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons head rest => by
      rw [List.map_cons, variableImage_eq head, ← forall₂_variableImage rest]

/-- Unfolding is stable: the substituted arguments unfold, with the
substituted dummy images, to the substituted result. -/
theorem Admissible.unfolds {definitions : Definition.Signature} {formal target : Context}
    {expressions : List Preterm} (admitted : Admissible signature formal target expressions)
    {symbol : Nat} {arguments : List Preterm} {images : List Nat} {result : Preterm}
    (unfolded : Definition.Unfolds signature definitions formal symbol arguments images result)
    {arguments' : List Preterm} {result' : Preterm}
    (argumentsMoved : List.Forall₂ (Substitutes (ofList expressions)) arguments arguments')
    (resultMoved : Substitutes (ofList expressions) result result') :
    Definition.Unfolds signature definitions target symbol arguments'
      (images.map (variableImage expressions)) result' := by
  cases unfolded with
  | @intro declaration body _ termLookup bodyLookup typed fresh bodySubstituted =>
      obtain ⟨images', imagesMoved⟩ : ∃ images',
          List.Forall₂ (fun image image' => expressions[image]? = some (.var image')) images
            images' := by
        apply forall₂_exists
        intro image member
        obtain ⟨sort, lookup⟩ := freshDummies_bound fresh image member
        obtain ⟨image', moved, _⟩ := admitted.bound_image lookup
        exact ⟨image', moved⟩
      have valuesMoved := List.rel_append argumentsMoved (forall₂_var_images imagesMoved)
      rw [← forall₂_variableImage imagesMoved]
      exact .intro termLookup bodyLookup (admitted.fitsBinders typed argumentsMoved)
        (admitted.freshDummies fresh argumentsMoved imagesMoved)
        ((substitutes_compose_iff valuesMoved).mpr ⟨result, bodySubstituted, resultMoved⟩)

/-! ## Conversion -/

/-- **Conversion is stable under admissible substitution.** -/
theorem Admissible.converts {definitions : Definition.Signature} {formal target : Context}
    {expressions : List Preterm} (admitted : Admissible signature formal target expressions)
    {left right : Preterm} {sort : Nat}
    (conversion : Converts signature definitions formal left right sort) :
    ∀ {left' right' : Preterm}, Substitutes (ofList expressions) left left' →
      Substitutes (ofList expressions) right right' →
        Converts signature definitions target left' right' sort := by
  induction conversion using Converts.rec
      (motive_2 := fun lefts rights binders _ =>
        ∀ (lefts' rights' : List Preterm),
          List.Forall₂ (Substitutes (ofList expressions)) lefts lefts' →
          List.Forall₂ (Substitutes (ofList expressions)) rights rights' →
            ConvertsArgs signature definitions target lefts' rights' binders) with
  | refl typed =>
      intro left' right' leftMoved rightMoved
      rw [leftMoved.deterministic rightMoved]
      exact .refl (typed.substitute admitted.typed rightMoved)
  | symm _ ih =>
      intro left' right' leftMoved rightMoved
      exact .symm (ih rightMoved leftMoved)
  | trans first _ firstIh secondIh =>
      intro left' right' leftMoved rightMoved
      obtain ⟨middle', middleMoved, _⟩ := admitted.substitutes_of_hasType first.typed.2
      exact .trans (firstIh leftMoved middleMoved) (secondIh middleMoved rightMoved)
  | congruence lookup _ ih =>
      intro left' right' leftMoved rightMoved
      obtain ⟨leftHead, lefts', rfl, leftHeadMoved, leftsMoved⟩ :=
        (substitutes_applyArgs_iff _ _ _ _).mp leftMoved
      obtain ⟨rightHead, rights', rfl, rightHeadMoved, rightsMoved⟩ :=
        (substitutes_applyArgs_iff _ _ _ _).mp rightMoved
      cases leftHeadMoved
      cases rightHeadMoved
      exact .congruence lookup (ih _ _ leftsMoved rightsMoved)
  | unfold lookup unfolded typed =>
      intro left' right' leftMoved rightMoved
      obtain ⟨head, arguments', rfl, headMoved, argumentsMoved⟩ :=
        (substitutes_applyArgs_iff _ _ _ _).mp leftMoved
      cases headMoved
      exact .unfold lookup (admitted.unfolds unfolded argumentsMoved rightMoved)
        (typed.substitute admitted.typed rightMoved)
  | nil =>
      rename_i lefts' rights' leftsMoved rightsMoved
      cases leftsMoved
      cases rightsMoved
      exact .nil
  | cons leftFits rightFits _ _ headIh tailIh =>
      rename_i lefts' rights' leftsMoved rightsMoved
      cases leftsMoved with
      | cons leftMoved leftsMoved =>
          cases rightsMoved with
          | cons rightMoved rightsMoved =>
              exact .cons (admitted.fitsBinder leftFits leftMoved)
                (admitted.fitsBinder rightFits rightMoved) (headIh leftMoved rightMoved)
                (tailIh _ _ leftsMoved rightsMoved)

/-! ## Derivations -/

theorem forall₂_mem_left {α β : Type} {relation : α → β → Prop} :
    ∀ {sources : List α} {results : List β}, List.Forall₂ relation sources results →
      ∀ {source : α}, source ∈ sources → ∃ result ∈ results, relation source result
  | [], [], .nil, _, member => by simp at member
  | _ :: _, _ :: _, .cons head rest, source, member => by
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨_, List.mem_cons_self, head⟩
      · obtain ⟨result, resultMember, related⟩ := forall₂_mem_left rest later
        exact ⟨result, List.mem_cons_of_mem _ resultMember, related⟩

theorem forall₂_compose {values images expressions : List Preterm}
    (valuesMoved : List.Forall₂ (Substitutes (ofList expressions)) values images) :
    ∀ {sources middles results : List Preterm},
      List.Forall₂ (Substitutes (ofList values)) sources middles →
      List.Forall₂ (Substitutes (ofList expressions)) middles results →
      List.Forall₂ (Substitutes (ofList images)) sources results
  | [], [], [], .nil, .nil => .nil
  | _ :: _, _ :: _, _ :: _, .cons first firstRest, .cons second secondRest =>
      .cons ((substitutes_compose_iff valuesMoved).mpr ⟨_, first, second⟩)
        (forall₂_compose valuesMoved firstRest secondRest)

/-- **Derivability is stable under admissible substitution.** -/
theorem Admissible.derives {definitions : Definition.Signature} {theorems : TheoremSignature}
    {formal target : Context} {expressions : List Preterm}
    (admitted : Admissible signature formal target expressions)
    {hypotheses hypotheses' : List Preterm}
    (hypothesesMoved : List.Forall₂ (Substitutes (ofList expressions)) hypotheses hypotheses')
    {expression : Preterm}
    (derived : Derives signature definitions theorems formal hypotheses expression) :
    ∀ {expression' : Preterm}, Substitutes (ofList expressions) expression expression' →
      Derives signature definitions theorems target hypotheses' expression' := by
  induction derived using Derives.rec
      (motive_2 := fun claims _ =>
        ∀ (claims' : List Preterm), List.Forall₂ (Substitutes (ofList expressions)) claims claims' →
          DerivesList signature definitions theorems target hypotheses' claims') with
  | hypothesis member =>
      intro expression' moved
      obtain ⟨other, otherMember, otherMoved⟩ := forall₂_mem_left hypothesesMoved member
      rw [moved.deterministic otherMoved]
      exact .hypothesis otherMember
  | @theoremApp index declaration arguments instantiation lookup instantiated _ childrenIh =>
      intro expression' moved
      obtain ⟨arguments', argumentsMoved⟩ : ∃ arguments',
          List.Forall₂ (Substitutes (ofList expressions)) arguments arguments' := by
        apply forall₂_exists
        intro argument member
        obtain ⟨binder, _, fits⟩ := forall₂_mem_left instantiated.admissible.typed member
        obtain ⟨result, substituted, _⟩ := admitted.substitutes_of_hasType fits.hasType
        exact ⟨result, substituted⟩
      have argumentsDefined : ∀ (position : Nat) (value : Preterm), arguments[position]? = some value →
          ∃ result, Substitutes (ofList expressions) value result := by
        intro position value lookup
        obtain ⟨_, _, fits⟩ := instantiated.admissible.lookup_fits lookup
        obtain ⟨result, substituted, _⟩ := admitted.substitutes_of_hasType fits.hasType
        exact ⟨result, substituted⟩
      obtain ⟨premises', premisesMoved⟩ : ∃ premises',
          List.Forall₂ (Substitutes (ofList expressions)) instantiation.hypotheses premises' := by
        apply forall₂_exists
        intro premise member
        obtain ⟨source, _, substituted⟩ := forall₂_mem instantiated.hypotheses member
        exact substitutes_after argumentsDefined substituted
      have instantiated' : TheoremDecl.Instantiates signature target declaration arguments'
          ⟨premises', expression'⟩ :=
        ⟨instantiated.admissible.comp admitted argumentsMoved,
          forall₂_compose argumentsMoved instantiated.hypotheses premisesMoved,
          (substitutes_compose_iff argumentsMoved).mpr
            ⟨_, instantiated.conclusion, moved⟩⟩
      exact .theoremApp lookup instantiated' (childrenIh premises' premisesMoved)
  | conversion converted _ ih =>
      intro expression' moved
      obtain ⟨left', leftMoved, _⟩ := admitted.substitutes_of_hasType converted.typed.1
      exact .conversion (admitted.converts converted leftMoved moved) (ih leftMoved)
  | nil =>
      rename_i claims' claimsMoved
      cases claimsMoved
      exact .nil
  | cons _ _ headIh tailIh =>
      rename_i claims' claimsMoved
      cases claimsMoved with
      | cons headMoved tailMoved => exact .cons (headIh headMoved) (tailIh _ tailMoved)

/-! ## Substituting whole lists -/

/-- Substitute every expression of a list, keeping an expression whose
substitution is undefined. On the lists used below every substitution is
defined. -/
def substituteAll (expressions values : List Preterm) : List Preterm :=
  values.map fun value => (value.substitute (ofList expressions)).getD value

theorem substituteAll_eq {expressions : List Preterm} :
    ∀ {values results : List Preterm},
      List.Forall₂ (Substitutes (ofList expressions)) values results →
        substituteAll expressions values = results
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons head rest => by
      simp only [substituteAll, List.map_cons] at *
      rw [head.eval]
      exact congrArg _ (substituteAll_eq rest)

theorem Admissible.substituteAll_forall₂ {formal target : Context}
    {expressions : List Preterm} (admitted : Admissible signature formal target expressions)
    {values : List Preterm} {binders : Context}
    (typed : List.Forall₂ (FitsBinder signature formal) values binders) :
    List.Forall₂ (Substitutes (ofList expressions)) values (substituteAll expressions values) := by
  obtain ⟨results, moved⟩ : ∃ results,
      List.Forall₂ (Substitutes (ofList expressions)) values results := by
    apply forall₂_exists
    intro value member
    obtain ⟨binder, _, fits⟩ := forall₂_mem_left typed member
    obtain ⟨result, substituted, _⟩ := admitted.substitutes_of_hasType fits.hasType
    exact ⟨result, substituted⟩
  rw [substituteAll_eq moved]
  exact moved

end Substitution

/-! ## The category of contexts and admissible substitutions -/

namespace Contextual

open CategoryTheory
open Substitution

/-- An MM0 context over a fixed term signature, as an object of the category of
admissible substitutions. -/
structure AdmissibleContext (signature : TermSignature) where
  context : Context

variable {signature : TermSignature}

/-- A morphism `Δ ⟶ Γ` is an admissible substitution of `Δ`-expressions for the
variables of `Γ`. -/
abbrev Morphism (source target : AdmissibleContext signature) : Type :=
  {expressions : List Preterm // Admissible signature target.context source.context expressions}

theorem substituteAll_identity {context : Context} {values : List Preterm} {binders : Context}
    (typed : List.Forall₂ (FitsBinder signature context) values binders) :
    substituteAll (identityList context) values = values := by
  apply substituteAll_eq
  induction typed with
  | nil => exact .nil
  | cons fits _ ih =>
      refine .cons (substitutes_identity fun index occurs => ?_) ih
      obtain ⟨support, supported⟩ := fits.support_exists
      obtain ⟨binder, lookup⟩ := supported.lookup_exists index occurs
      exact (List.getElem?_eq_some_iff.mp lookup).1

theorem substituteAll_of_identity {context : Context} {expressions : List Preterm}
    (length : expressions.length = context.length) :
    substituteAll expressions (identityList context) = expressions := by
  apply substituteAll_eq
  rw [List.forall₂_iff_get]
  refine ⟨by simp [identityList, length], fun index inRange _ => ?_⟩
  simp only [identityList, List.get_eq_getElem, List.getElem_map, List.getElem_range]
  exact .var (List.getElem?_eq_getElem (by simpa [identityList, length] using inRange))

instance category : Category (AdmissibleContext signature) where
  Hom := Morphism
  id context := ⟨identityList context.context, admissible_identity context.context⟩
  comp first second :=
    ⟨substituteAll first.1 second.1,
      second.2.comp first.2 (first.2.substituteAll_forall₂ second.2.typed)⟩
  id_comp second := by
    apply Subtype.ext
    exact substituteAll_identity second.2.typed
  comp_id first := by
    apply Subtype.ext
    exact substituteAll_of_identity first.2.length_eq
  assoc first second third := by
    apply Subtype.ext
    change substituteAll (substituteAll first.1 second.1) third.1 =
      substituteAll first.1 (substituteAll second.1 third.1)
    have secondMoved := first.2.substituteAll_forall₂ second.2.typed
    have thirdMoved := second.2.substituteAll_forall₂ third.2.typed
    have lastMoved := first.2.substituteAll_forall₂ (third.2.comp second.2 thirdMoved).typed
    exact substituteAll_eq (forall₂_compose secondMoved thirdMoved lastMoved)

/-! ## Derivable statements form a presheaf -/

variable (sorts : SortSignature) (signature) (definitions : Definition.Signature)
  (theorems : TheoremSignature)

/-- A derivable judgment whose hypotheses and conclusion are statements of the
context. -/
def DerivableAt (context : Context) : Type :=
  {judgment : List Preterm × Preterm //
    (∀ hypothesis ∈ judgment.1, IsStatement sorts signature context hypothesis) ∧
    IsStatement sorts signature context judgment.2 ∧
    Derives signature definitions theorems context judgment.1 judgment.2}

variable {sorts signature definitions theorems}

/-- Substitute one expression, keeping it when the substitution is undefined. -/
def substituteOne (expressions : List Preterm) (value : Preterm) : Preterm :=
  (value.substitute (ofList expressions)).getD value

theorem substituteOne_eq {expressions : List Preterm} {value result : Preterm}
    (moved : Substitutes (ofList expressions) value result) :
    substituteOne expressions value = result := by
  simp [substituteOne, moved.eval]

theorem statement_moves {formal target : Context} {expressions : List Preterm}
    (admitted : Admissible signature formal target expressions) {value : Preterm}
    (statement : IsStatement sorts signature formal value) :
    Substitutes (ofList expressions) value (substituteOne expressions value) := by
  obtain ⟨sort, _, typed, _⟩ := statement
  obtain ⟨result, moved, _⟩ := admitted.substitutes_of_hasType typed
  rw [substituteOne_eq moved]
  exact moved

theorem statements_move {formal target : Context} {expressions : List Preterm}
    (admitted : Admissible signature formal target expressions) {values : List Preterm}
    (statements : ∀ value ∈ values, IsStatement sorts signature formal value) :
    List.Forall₂ (Substitutes (ofList expressions)) values (substituteAll expressions values) := by
  obtain ⟨results, moved⟩ : ∃ results,
      List.Forall₂ (Substitutes (ofList expressions)) values results :=
    forall₂_exists fun value member => ⟨_, statement_moves admitted (statements value member)⟩
  rw [substituteAll_eq moved]
  exact moved

/-- Move a derivable judgment along an admissible substitution. -/
def DerivableAt.move {formal target : Context} {expressions : List Preterm}
    (admitted : Admissible signature formal target expressions)
    (judgment : DerivableAt signature sorts definitions theorems formal) :
    DerivableAt signature sorts definitions theorems target :=
  ⟨(substituteAll expressions judgment.1.1, substituteOne expressions judgment.1.2), by
    obtain ⟨⟨hypotheses, conclusion⟩, statements, statement, derived⟩ := judgment
    have hypothesesMoved := statements_move admitted statements
    have conclusionMoved := statement_moves admitted statement
    refine ⟨fun value member => ?_, statement.substitute admitted conclusionMoved,
      admitted.derives hypothesesMoved derived conclusionMoved⟩
    obtain ⟨source, sourceMember, moved⟩ := forall₂_mem hypothesesMoved member
    exact (statements source sourceMember).substitute admitted moved⟩

theorem statement_scoped {context : Context} {value : Preterm}
    (statement : IsStatement sorts signature context value) :
    ∀ index, Occurs index value → index < context.length := by
  obtain ⟨sort, _, typed, _⟩ := statement
  intro index occurs
  obtain ⟨support, supported⟩ := typed.support_exists
  obtain ⟨binder, lookup⟩ := supported.lookup_exists index occurs
  exact (List.getElem?_eq_some_iff.mp lookup).1

variable (sorts signature definitions theorems) in
/-- **MM0 derivability as a contextual face.** Derivable judgments between
statements form a presheaf on contexts and admissible substitutions. -/
def derivableFace : Mettapedia.Computability.ComputationalTrinity.Face.{0, 0, 0}
    (AdmissibleContext signature) where
  obj context := DerivableAt signature sorts definitions theorems context.unop.context
  map θ := TypeCat.ofHom fun judgment => judgment.move θ.unop.2
  map_id context := by
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨hypotheses, conclusion⟩, statements, statement, derived⟩
    apply Subtype.ext
    change (substituteAll (identityList _) hypotheses, substituteOne (identityList _) conclusion) =
      (hypotheses, conclusion)
    congr 1
    · apply substituteAll_eq
      obtain ⟨results, moved⟩ : ∃ results, List.Forall₂
          (Substitutes (ofList (identityList context.unop.context))) hypotheses results :=
        forall₂_exists fun value member =>
          ⟨value, substitutes_identity (statement_scoped (statements value member))⟩
      have same : results = hypotheses := by
        clear statement derived
        induction moved with
        | nil => rfl
        | cons head _ ih =>
            rw [head.deterministic (substitutes_identity (statement_scoped
              (statements _ List.mem_cons_self))),
              ih (fun value member => statements value (List.mem_cons_of_mem _ member))]
      rw [same] at moved
      exact moved
    · exact substituteOne_eq (substitutes_identity (statement_scoped statement))
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨hypotheses, conclusion⟩, statements, statement, derived⟩
    apply Subtype.ext
    change (substituteAll (substituteAll second.unop.1 first.unop.1) hypotheses,
        substituteOne (substituteAll second.unop.1 first.unop.1) conclusion) =
      (substituteAll second.unop.1 (substituteAll first.unop.1 hypotheses),
        substituteOne second.unop.1 (substituteOne first.unop.1 conclusion))
    have firstMoved := second.unop.2.substituteAll_forall₂ first.unop.2.typed
    have hypothesesMoved := statements_move first.unop.2 statements
    have conclusionMoved := statement_moves first.unop.2 statement
    have movedStatements : ∀ value ∈ substituteAll first.unop.1 hypotheses,
        IsStatement sorts signature _ value := fun value member => by
      obtain ⟨source, sourceMember, moved⟩ := forall₂_mem hypothesesMoved member
      exact (statements source sourceMember).substitute first.unop.2 moved
    congr 1
    · exact substituteAll_eq (forall₂_compose firstMoved hypothesesMoved
        (statements_move second.unop.2 movedStatements))
    · rw [substituteOne_eq (statement_moves second.unop.2
        (statement.substitute first.unop.2 conclusionMoved))]
      exact substituteOne_eq ((substitutes_compose_iff firstMoved).mpr
        ⟨_, conclusionMoved, statement_moves second.unop.2
          (statement.substitute first.unop.2 conclusionMoved)⟩)

/-! ## Checked witnesses move along admissible substitutions -/

mutual

/-- Move a conversion witness along a substitution: its expressions are
substituted and its dummy images are sent to their variable images. -/
def moveConv (expressions : List Preterm) : ConvWitness → ConvWitness
  | .refl expression => .refl (substituteOne expressions expression)
  | .symm child => .symm (moveConv expressions child)
  | .trans first second => .trans (moveConv expressions first) (moveConv expressions second)
  | .congruence symbol children => .congruence symbol (moveConvs expressions children)
  | .unfold symbol arguments images =>
      .unfold symbol (substituteAll expressions arguments) (images.map (variableImage expressions))

/-- Move a list of conversion witnesses along a substitution. -/
def moveConvs (expressions : List Preterm) : List ConvWitness → List ConvWitness
  | [] => []
  | child :: children => moveConv expressions child :: moveConvs expressions children

end

mutual

/-- Move a proof witness along a substitution: hypotheses keep their
positions, theorem arguments are substituted, conversions are moved. -/
def moveProof (expressions : List Preterm) : ProofWitness → ProofWitness
  | .hyp index => .hyp index
  | .theoremApp index arguments children =>
      .theoremApp index (substituteAll expressions arguments) (moveProofs expressions children)
  | .conversion witness child => .conversion (moveConv expressions witness) (moveProof expressions child)

/-- Move a list of proof witnesses along a substitution. -/
def moveProofs (expressions : List Preterm) : List ProofWitness → List ProofWitness
  | [] => []
  | child :: children => moveProof expressions child :: moveProofs expressions children

end

theorem forall₂_lookup_left {α β : Type} {relation : α → β → Prop} :
    ∀ {sources : List α} {results : List β}, List.Forall₂ relation sources results →
      ∀ {index : Nat} {source : α}, sources[index]? = some source →
        ∃ result, results[index]? = some result ∧ relation source result
  | [], [], .nil, _, _, lookup => by simp at lookup
  | _ :: _, _ :: _, .cons head rest, index, source, lookup => by
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at lookup
          subst lookup
          exact ⟨_, rfl, head⟩
      | succ index =>
          simp only [List.getElem?_cons_succ] at lookup ⊢
          exact forall₂_lookup_left rest lookup

/-- **A checked conversion witness, moved along an admissible substitution,
checks the substituted conversion.** -/
theorem _root_.Mettapedia.Languages.MM0.Kernel.Substitution.Admissible.checksConv {definitions : Definition.Signature} {formal target : Context}
    {expressions : List Preterm} (admitted : Admissible signature formal target expressions)
    {witness : ConvWitness} {left right : Preterm} {sort : Nat}
    (checked : ConvWitness.Checks signature definitions formal witness left right sort) :
    ∀ {left' right' : Preterm}, Substitutes (ofList expressions) left left' →
      Substitutes (ofList expressions) right right' →
        ConvWitness.Checks signature definitions target (moveConv expressions witness) left' right'
          sort := by
  induction checked using ConvWitness.Checks.rec
      (motive_2 := fun children lefts rights binders _ =>
        ∀ (lefts' rights' : List Preterm),
          List.Forall₂ (Substitutes (ofList expressions)) lefts lefts' →
          List.Forall₂ (Substitutes (ofList expressions)) rights rights' →
            ConvWitness.ChecksArgs signature definitions target (moveConvs expressions children)
              lefts' rights' binders) with
  | refl typed =>
      intro left' right' leftMoved rightMoved
      rw [leftMoved.deterministic rightMoved]
      simp only [moveConv]
      rw [substituteOne_eq rightMoved]
      exact .refl (typed.substitute admitted.typed rightMoved)
  | symm _ ih =>
      intro left' right' leftMoved rightMoved
      exact .symm (ih rightMoved leftMoved)
  | trans first _ firstIh secondIh =>
      intro left' right' leftMoved rightMoved
      obtain ⟨middle', middleMoved, _⟩ := admitted.substitutes_of_hasType first.typed.2
      exact .trans (firstIh leftMoved middleMoved) (secondIh middleMoved rightMoved)
  | congruence lookup _ ih =>
      intro left' right' leftMoved rightMoved
      obtain ⟨leftHead, lefts', rfl, leftHeadMoved, leftsMoved⟩ :=
        (substitutes_applyArgs_iff _ _ _ _).mp leftMoved
      obtain ⟨rightHead, rights', rfl, rightHeadMoved, rightsMoved⟩ :=
        (substitutes_applyArgs_iff _ _ _ _).mp rightMoved
      cases leftHeadMoved
      cases rightHeadMoved
      exact .congruence lookup (ih _ _ leftsMoved rightsMoved)
  | unfold lookup unfolded typed =>
      intro left' right' leftMoved rightMoved
      obtain ⟨head, arguments', rfl, headMoved, argumentsMoved⟩ :=
        (substitutes_applyArgs_iff _ _ _ _).mp leftMoved
      cases headMoved
      simp only [moveConv]
      rw [substituteAll_eq argumentsMoved]
      exact .unfold lookup (admitted.unfolds unfolded argumentsMoved rightMoved)
        (typed.substitute admitted.typed rightMoved)
  | nil =>
      rename_i lefts' rights' leftsMoved rightsMoved
      cases leftsMoved
      cases rightsMoved
      exact .nil
  | cons leftFits rightFits _ _ headIh tailIh =>
      rename_i lefts' rights' leftsMoved rightsMoved
      cases leftsMoved with
      | cons leftMoved leftsMoved =>
          cases rightsMoved with
          | cons rightMoved rightsMoved =>
              exact .cons (admitted.fitsBinder leftFits leftMoved)
                (admitted.fitsBinder rightFits rightMoved) (headIh leftMoved rightMoved)
                (tailIh _ _ leftsMoved rightsMoved)

/-- **A checked proof witness, moved along an admissible substitution,
checks the substituted judgment.** -/
theorem _root_.Mettapedia.Languages.MM0.Kernel.Substitution.Admissible.checks {definitions : Definition.Signature} {theorems : TheoremSignature}
    {formal target : Context} {expressions : List Preterm}
    (admitted : Admissible signature formal target expressions)
    {hypotheses hypotheses' : List Preterm}
    (hypothesesMoved : List.Forall₂ (Substitutes (ofList expressions)) hypotheses hypotheses')
    {witness : ProofWitness} {expression : Preterm}
    (checked : ProofWitness.Checks signature definitions theorems formal hypotheses witness expression) :
    ∀ {expression' : Preterm}, Substitutes (ofList expressions) expression expression' →
      ProofWitness.Checks signature definitions theorems target hypotheses'
        (moveProof expressions witness) expression' := by
  induction checked using ProofWitness.Checks.rec
      (motive_2 := fun children claims _ =>
        ∀ (claims' : List Preterm), List.Forall₂ (Substitutes (ofList expressions)) claims claims' →
          ProofWitness.ChecksList signature definitions theorems target hypotheses'
            (moveProofs expressions children) claims') with
  | hyp lookup =>
      intro expression' moved
      obtain ⟨other, otherLookup, otherMoved⟩ := forall₂_lookup_left hypothesesMoved lookup
      rw [moved.deterministic otherMoved]
      exact .hyp otherLookup
  | @theoremApp index declaration arguments children instantiation lookup instantiated _ childrenIh =>
      intro expression' moved
      have argumentsMoved := admitted.substituteAll_forall₂ instantiated.admissible.typed
      have argumentsDefined : ∀ (position : Nat) (value : Preterm), arguments[position]? = some value →
          ∃ result, Substitutes (ofList expressions) value result := by
        intro position value lookup
        obtain ⟨_, _, fits⟩ := instantiated.admissible.lookup_fits lookup
        obtain ⟨result, substituted, _⟩ := admitted.substitutes_of_hasType fits.hasType
        exact ⟨result, substituted⟩
      obtain ⟨premises', premisesMoved⟩ : ∃ premises',
          List.Forall₂ (Substitutes (ofList expressions)) instantiation.hypotheses premises' := by
        apply forall₂_exists
        intro premise member
        obtain ⟨source, _, substituted⟩ := forall₂_mem instantiated.hypotheses member
        exact substitutes_after argumentsDefined substituted
      have instantiated' : TheoremDecl.Instantiates signature target declaration
          (substituteAll expressions arguments) ⟨premises', expression'⟩ :=
        ⟨instantiated.admissible.comp admitted argumentsMoved,
          forall₂_compose argumentsMoved instantiated.hypotheses premisesMoved,
          (substitutes_compose_iff argumentsMoved).mpr
            ⟨_, instantiated.conclusion, moved⟩⟩
      exact .theoremApp lookup instantiated' (childrenIh premises' premisesMoved)
  | conversion converted _ ih =>
      intro expression' moved
      obtain ⟨left', leftMoved, _⟩ := admitted.substitutes_of_hasType converted.typed.1
      exact .conversion (admitted.checksConv converted leftMoved moved) (ih leftMoved)
  | nil =>
      rename_i claims' claimsMoved
      cases claimsMoved
      exact .nil
  | cons _ _ headIh tailIh =>
      rename_i claims' claimsMoved
      cases claimsMoved with
      | cons headMoved tailMoved => exact .cons (headIh headMoved) (tailIh _ tailMoved)

/-! ### The identity and composites move witnesses as expected -/

theorem hasType_scoped {context remaining : Context} {value : Preterm} {sort : Nat}
    (typed : HasType signature context value remaining sort) :
    ∀ index, Occurs index value → index < context.length := by
  intro index occurs
  obtain ⟨support, supported⟩ := typed.support_exists
  obtain ⟨binder, lookup⟩ := supported.lookup_exists index occurs
  exact (List.getElem?_eq_some_iff.mp lookup).1

theorem substituteOne_identity {context remaining : Context} {value : Preterm} {sort : Nat}
    (typed : HasType signature context value remaining sort) :
    substituteOne (identityList context) value = value :=
  substituteOne_eq (substitutes_identity (hasType_scoped typed))

theorem variableImage_identity {context : Context} {index : Nat} (inRange : index < context.length) :
    variableImage (identityList context) index = index :=
  variableImage_eq (by rw [identityList_getElem?, if_pos inRange])

theorem images_identity {context : Context} {arguments : List Preterm} {sorts images : List Nat}
    (fresh : Definition.FreshDummies context arguments sorts images) :
    images.map (variableImage (identityList context)) = images := by
  conv_rhs => rw [← List.map_id images]
  apply List.map_congr_left
  intro image member
  obtain ⟨sort, lookup⟩ := freshDummies_bound fresh image member
  exact variableImage_identity (List.getElem?_eq_some_iff.mp lookup).1

theorem moveConv_identity {definitions : Definition.Signature} {context : Context}
    {witness : ConvWitness} {left right : Preterm} {sort : Nat}
    (checked : ConvWitness.Checks signature definitions context witness left right sort) :
    moveConv (identityList context) witness = witness := by
  induction checked using ConvWitness.Checks.rec
      (motive_2 := fun children _ _ _ _ => moveConvs (identityList context) children = children) with
  | refl typed => simp only [moveConv, substituteOne_identity typed]
  | symm _ ih => simp only [moveConv, ih]
  | trans _ _ firstIh secondIh => simp only [moveConv, firstIh, secondIh]
  | congruence _ _ ih => simp only [moveConv, ih]
  | unfold _ unfolded _ =>
      cases unfolded with
      | intro _ _ typed fresh _ => simp only [moveConv, substituteAll_identity typed, images_identity fresh]
  | nil => rfl
  | cons _ _ _ _ headIh tailIh => simp only [moveConvs, headIh, tailIh]

theorem moveProof_identity {definitions : Definition.Signature} {theorems : TheoremSignature}
    {context : Context} {hypotheses : List Preterm} {witness : ProofWitness} {expression : Preterm}
    (checked : ProofWitness.Checks signature definitions theorems context hypotheses witness expression) :
    moveProof (identityList context) witness = witness := by
  induction checked using ProofWitness.Checks.rec
      (motive_2 := fun children _ _ => moveProofs (identityList context) children = children) with
  | hyp _ => rfl
  | theoremApp _ instantiated _ childrenIh =>
      simp only [moveProof, substituteAll_identity instantiated.admissible.typed, childrenIh]
  | conversion converted _ ih => simp only [moveProof, moveConv_identity converted, ih]
  | nil => rfl
  | cons _ _ headIh tailIh => simp only [moveProofs, headIh, tailIh]

section Composite

variable {first middle last : Context} {values expressions : List Preterm}

theorem substituteOne_comp (valuesAdmitted : Admissible signature first middle values)
    (expressionsAdmitted : Admissible signature middle last expressions)
    {value : Preterm} {remaining : Context} {sort : Nat}
    (typed : HasType signature first value remaining sort) :
    substituteOne expressions (substituteOne values value) =
      substituteOne (substituteAll expressions values) value := by
  have valuesMoved := expressionsAdmitted.substituteAll_forall₂ valuesAdmitted.typed
  obtain ⟨middleValue, toMiddle, middleTyped⟩ := valuesAdmitted.substitutes_of_hasType typed
  obtain ⟨lastValue, toLast, _⟩ := expressionsAdmitted.substitutes_of_hasType middleTyped
  rw [substituteOne_eq toMiddle, substituteOne_eq toLast,
    substituteOne_eq ((substitutes_compose_iff valuesMoved).mpr ⟨_, toMiddle, toLast⟩)]

theorem substituteAll_comp (valuesAdmitted : Admissible signature first middle values)
    (expressionsAdmitted : Admissible signature middle last expressions)
    {arguments : List Preterm} {binders : Context}
    (typed : List.Forall₂ (FitsBinder signature first) arguments binders) :
    substituteAll expressions (substituteAll values arguments) =
      substituteAll (substituteAll expressions values) arguments := by
  have valuesMoved := expressionsAdmitted.substituteAll_forall₂ valuesAdmitted.typed
  have toMiddle := valuesAdmitted.substituteAll_forall₂ typed
  have toLast := expressionsAdmitted.substituteAll_forall₂ (valuesAdmitted.fitsBinders typed toMiddle)
  exact (substituteAll_eq (forall₂_compose valuesMoved toMiddle toLast)).symm

theorem variableImage_comp (valuesAdmitted : Admissible signature first middle values)
    (expressionsAdmitted : Admissible signature middle last expressions)
    {index sort : Nat} (bound : first[index]? = some (.bound sort)) :
    variableImage expressions (variableImage values index) =
      variableImage (substituteAll expressions values) index := by
  obtain ⟨image, valueLookup, middleLookup⟩ := valuesAdmitted.bound_image bound
  obtain ⟨image', expressionLookup, _⟩ := expressionsAdmitted.bound_image middleLookup
  rw [variableImage_eq valueLookup, variableImage_eq expressionLookup]
  symm
  apply variableImage_eq
  simp [substituteAll, valueLookup, Preterm.substitute, Substitution.ofList, expressionLookup]

theorem moveConv_comp {definitions : Definition.Signature}
    (valuesAdmitted : Admissible signature first middle values)
    (expressionsAdmitted : Admissible signature middle last expressions)
    {witness : ConvWitness} {left right : Preterm} {sort : Nat}
    (checked : ConvWitness.Checks signature definitions first witness left right sort) :
    moveConv expressions (moveConv values witness) =
      moveConv (substituteAll expressions values) witness := by
  induction checked using ConvWitness.Checks.rec
      (motive_2 := fun children _ _ _ _ =>
        moveConvs expressions (moveConvs values children) =
          moveConvs (substituteAll expressions values) children) with
  | refl typed => simp only [moveConv, substituteOne_comp valuesAdmitted expressionsAdmitted typed]
  | symm _ ih => simp only [moveConv, ih]
  | trans _ _ firstIh secondIh => simp only [moveConv, firstIh, secondIh]
  | congruence _ _ ih => simp only [moveConv, ih]
  | unfold _ unfolded _ =>
      cases unfolded with
      | intro _ _ typed fresh _ =>
          simp only [moveConv, substituteAll_comp valuesAdmitted expressionsAdmitted typed, List.map_map]
          congr 1
          apply List.map_congr_left
          intro image member
          obtain ⟨sort, lookup⟩ := freshDummies_bound fresh image member
          exact variableImage_comp valuesAdmitted expressionsAdmitted lookup
  | nil => rfl
  | cons _ _ _ _ headIh tailIh => simp only [moveConvs, headIh, tailIh]

theorem moveProof_comp {definitions : Definition.Signature} {theorems : TheoremSignature}
    (valuesAdmitted : Admissible signature first middle values)
    (expressionsAdmitted : Admissible signature middle last expressions)
    {hypotheses : List Preterm} {witness : ProofWitness} {expression : Preterm}
    (checked : ProofWitness.Checks signature definitions theorems first hypotheses witness expression) :
    moveProof expressions (moveProof values witness) =
      moveProof (substituteAll expressions values) witness := by
  induction checked using ProofWitness.Checks.rec
      (motive_2 := fun children _ _ =>
        moveProofs expressions (moveProofs values children) =
          moveProofs (substituteAll expressions values) children) with
  | hyp _ => rfl
  | theoremApp _ instantiated _ childrenIh =>
      simp only [moveProof, childrenIh,
        substituteAll_comp valuesAdmitted expressionsAdmitted instantiated.admissible.typed]
  | conversion converted _ ih =>
      simp only [moveProof, moveConv_comp valuesAdmitted expressionsAdmitted converted, ih]
  | nil => rfl
  | cons _ _ headIh tailIh => simp only [moveProofs, headIh, tailIh]

end Composite

/-! ### Statements under the identity and composites -/

theorem statements_identity {context : Context} {values : List Preterm}
    (statements : ∀ value ∈ values, IsStatement sorts signature context value) :
    substituteAll (identityList context) values = values := by
  apply substituteAll_eq
  rw [List.forall₂_same]
  exact fun value member => substitutes_identity (statement_scoped (statements value member))

theorem statement_identity {context : Context} {value : Preterm}
    (statement : IsStatement sorts signature context value) :
    substituteOne (identityList context) value = value :=
  substituteOne_eq (substitutes_identity (statement_scoped statement))

theorem statements_comp {first middle last : Context} {values expressions : List Preterm}
    (valuesAdmitted : Admissible signature first middle values)
    (expressionsAdmitted : Admissible signature middle last expressions) {hypotheses : List Preterm}
    (statements : ∀ value ∈ hypotheses, IsStatement sorts signature first value) :
    substituteAll expressions (substituteAll values hypotheses) =
      substituteAll (substituteAll expressions values) hypotheses := by
  have valuesMoved := expressionsAdmitted.substituteAll_forall₂ valuesAdmitted.typed
  have hypothesesMoved := statements_move valuesAdmitted statements
  have movedStatements : ∀ value ∈ substituteAll values hypotheses,
      IsStatement sorts signature middle value := fun value member => by
    obtain ⟨source, sourceMember, moved⟩ := forall₂_mem hypothesesMoved member
    exact (statements source sourceMember).substitute valuesAdmitted moved
  exact (substituteAll_eq (forall₂_compose valuesMoved hypothesesMoved
    (statements_move expressionsAdmitted movedStatements))).symm

theorem statement_comp {first middle last : Context} {values expressions : List Preterm}
    (valuesAdmitted : Admissible signature first middle values)
    (expressionsAdmitted : Admissible signature middle last expressions) {value : Preterm}
    (statement : IsStatement sorts signature first value) :
    substituteOne expressions (substituteOne values value) =
      substituteOne (substituteAll expressions values) value := by
  obtain ⟨sort, _, typed, _⟩ := statement
  exact substituteOne_comp valuesAdmitted expressionsAdmitted typed

/-! ### Checked witnesses form a presheaf over derivability -/

variable (sorts signature definitions theorems) in
/-- A checked proof witness of a judgment whose hypotheses and conclusion are
statements of the context. -/
def WitnessAt (context : Context) : Type :=
  {judgment : List Preterm × Preterm × ProofWitness //
    (∀ hypothesis ∈ judgment.1, IsStatement sorts signature context hypothesis) ∧
    IsStatement sorts signature context judgment.2.1 ∧
    ProofWitness.Checks signature definitions theorems context judgment.1 judgment.2.2 judgment.2.1}

/-- Move a checked witness along an admissible substitution. -/
def WitnessAt.move {formal target : Context} {expressions : List Preterm}
    (admitted : Admissible signature formal target expressions)
    (judgment : WitnessAt signature sorts definitions theorems formal) :
    WitnessAt signature sorts definitions theorems target :=
  ⟨(substituteAll expressions judgment.1.1, substituteOne expressions judgment.1.2.1,
      moveProof expressions judgment.1.2.2), by
    obtain ⟨⟨hypotheses, conclusion, witness⟩, statements, statement, checked⟩ := judgment
    have hypothesesMoved := statements_move admitted statements
    have conclusionMoved := statement_moves admitted statement
    refine ⟨fun value member => ?_, statement.substitute admitted conclusionMoved,
      admitted.checks hypothesesMoved checked conclusionMoved⟩
    obtain ⟨source, sourceMember, moved⟩ := forall₂_mem hypothesesMoved member
    exact (statements source sourceMember).substitute admitted moved⟩

variable (sorts signature definitions theorems) in
/-- **MM0 checked witnesses as a contextual face.** -/
def witnessFace : Mettapedia.Computability.ComputationalTrinity.Face.{0, 0, 0}
    (AdmissibleContext signature) where
  obj context := WitnessAt signature sorts definitions theorems context.unop.context
  map θ := TypeCat.ofHom fun judgment => judgment.move θ.unop.2
  map_id context := by
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨hypotheses, conclusion, witness⟩, statements, statement, checked⟩
    apply Subtype.ext
    change (substituteAll (identityList _) hypotheses, substituteOne (identityList _) conclusion,
        moveProof (identityList _) witness) = (hypotheses, conclusion, witness)
    rw [statements_identity statements, statement_identity statement, moveProof_identity checked]
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨hypotheses, conclusion, witness⟩, statements, statement, checked⟩
    apply Subtype.ext
    change (substituteAll (substituteAll second.unop.1 first.unop.1) hypotheses,
        substituteOne (substituteAll second.unop.1 first.unop.1) conclusion,
        moveProof (substituteAll second.unop.1 first.unop.1) witness) =
      (substituteAll second.unop.1 (substituteAll first.unop.1 hypotheses),
        substituteOne second.unop.1 (substituteOne first.unop.1 conclusion),
        moveProof second.unop.1 (moveProof first.unop.1 witness))
    rw [statements_comp first.unop.2 second.unop.2 statements,
      statement_comp first.unop.2 second.unop.2 statement,
      moveProof_comp first.unop.2 second.unop.2 checked]

variable (sorts signature definitions theorems) in
/-- **Forgetting the witness is natural.** -/
def forgetWitness :
    witnessFace signature sorts definitions theorems ⟶
      derivableFace signature sorts definitions theorems where
  app _ := TypeCat.ofHom fun judgment =>
    ⟨(judgment.1.1, judgment.1.2.1), judgment.2.1, judgment.2.2.1, judgment.2.2.2.derives⟩
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro judgment
    rfl

/-- **Every derivable judgment has a checked witness**, at every context. -/
theorem forgetWitness_surjective (context : (AdmissibleContext signature)ᵒᵖ) :
    Function.Surjective ((forgetWitness signature sorts definitions theorems).app context) := by
  rintro ⟨⟨hypotheses, conclusion⟩, statements, statement, derived⟩
  obtain ⟨witness, checked⟩ := derived.certificate_exists
  exact ⟨⟨(hypotheses, conclusion, witness), statements, statement, checked⟩, rfl⟩

end Contextual

/-! ## Controls -/

namespace SubstitutionStabilityControls

open Substitution

/-- One binary term on two bound variables of sort 0, with result sort 1. -/
def signature : TermSignature
  | 0 => some ⟨[.bound 0, .bound 0], 1, ∅⟩
  | _ => none

def noDefinitions : Definition.Signature := fun _ => none

/-- `distinct x y` for two bound variables. -/
def distinct (left right : Nat) : Preterm := .app (.app (.term 0) (.var left)) (.var right)

/-- One axiom: `distinct x y` for any two bound variables. -/
def theorems : TheoremSignature
  | 0 => some ⟨[.bound 0, .bound 0], [], distinct 0 1⟩
  | _ => none

def twoBound : Context := [.bound 0, .bound 0]

/-- A typed substitution that identifies the two bound variables. -/
def coincident : List Preterm := [.var 0, .var 0]

theorem distinct_derivable : Derives signature noDefinitions theorems twoBound [] (distinct 0 1) :=
  .theoremApp (index := 0) (arguments := identityList twoBound) (instantiation := ⟨[], distinct 0 1⟩)
    rfl ⟨admissible_identity twoBound, .nil, substitute_sound rfl⟩ .nil

theorem coincident_typed :
    List.Forall₂ (FitsBinder signature twoBound) coincident twoBound :=
  .cons (.bound rfl) (.cons (.bound rfl) .nil)

theorem coincident_moves :
    Substitutes (ofList coincident) (distinct 0 1) (distinct 0 0) := substitute_sound rfl

/-- Every derivable statement of the axiom names two different variables. -/
theorem derivable_distinct {expression : Preterm}
    (derived : Derives signature noDefinitions theorems twoBound [] expression) :
    ∃ left right, expression = distinct left right ∧ left ≠ right := by
  induction derived using Derives.rec (motive_2 := fun _ _ => True) with
  | hypothesis member => cases member
  | @theoremApp index declaration arguments instantiation lookup instantiated _ _ =>
      obtain ⟨premises, conclusion⟩ := instantiation
      cases index with
      | succ index => cases lookup
      | zero =>
          simp only [theorems, Option.some.injEq] at lookup
          subst lookup
          have typed := instantiated.admissible.typed
          cases typed with
          | cons firstFits restFits =>
              cases restFits with
              | cons secondFits nilFits =>
                  cases nilFits
                  cases firstFits with
                  | @bound first _ firstLookup =>
                      cases secondFits with
                      | @bound second _ secondLookup =>
                          have conclusion := instantiated.conclusion
                          simp only [distinct] at conclusion
                          cases conclusion with
                          | app head argument =>
                              cases head with
                              | app termMoved firstArgument =>
                                  cases termMoved
                                  cases firstArgument with
                                  | var firstImage =>
                                      cases argument with
                                      | var secondImage =>
                                          simp only [ofList, List.getElem?_cons_zero,
                                            List.getElem?_cons_succ, Option.some.injEq]
                                            at firstImage secondImage
                                          subst firstImage secondImage
                                          refine ⟨first, second, rfl, fun same => ?_⟩
                                          subst same
                                          have independent :=
                                            instantiated.admissible.preserves_independence
                                              (u := 0) (v := 1) (sort := 0) (binder := .bound 0)
                                              (image := first) (expression := .var first)
                                              rfl rfl (by
                                                intro has
                                                cases has with
                                                | regular lookup => cases lookup)
                                              rfl rfl
                                          exact independent (.bound firstLookup)
  | conversion converted _ ih =>
      rw [← Converts.eq_of_no_definitions (fun _ => rfl) converted]
      exact ih
  | nil => trivial
  | cons => trivial

/-- **Independence is required.** A typed substitution that identifies two
bound variables sends a derivable judgment to an underivable one; it is not
admissible, so it is not a morphism of the category. -/
theorem independence_required :
    Derives signature noDefinitions theorems twoBound [] (distinct 0 1) ∧
      List.Forall₂ (FitsBinder signature twoBound) coincident twoBound ∧
      Substitutes (ofList coincident) (distinct 0 1) (distinct 0 0) ∧
      ¬ Derives signature noDefinitions theorems twoBound [] (distinct 0 0) ∧
      ¬ Admissible signature twoBound twoBound coincident := by
  refine ⟨distinct_derivable, coincident_typed, coincident_moves, fun derived => ?_, fun admitted => ?_⟩
  · obtain ⟨left, right, same, different⟩ := derivable_distinct derived
    simp only [distinct, Preterm.app.injEq, Preterm.var.injEq, true_and] at same
    exact different (same.1.symm.trans same.2)
  · obtain ⟨left, right, same, different⟩ :=
      derivable_distinct (admitted.derives .nil distinct_derivable coincident_moves)
    simp only [distinct, Preterm.app.injEq, Preterm.var.injEq, true_and] at same
    exact different (same.1.symm.trans same.2)

/-- `distinct 0 1` is a statement of sort 1 over two bound variables. -/
theorem distinct_typed : HasType signature twoBound (distinct 0 1) [] 1 :=
  .bound (.bound (.term (declaration := ⟨[.bound 0, .bound 0], 1, ∅⟩) rfl) rfl) rfl

/-- The hypothesis itself, as a witness. -/
def directWitness : ProofWitness := .hyp 0

/-- The hypothesis followed by a reflexive conversion, as a witness. -/
def detourWitness : ProofWitness := .conversion (.refl (distinct 0 1)) (.hyp 0)

/-- **Witnesses retain more than derivability**: two different witnesses check
one judgment, so forgetting the witness is not injective. -/
theorem two_witnesses :
    ProofWitness.Checks signature noDefinitions theorems twoBound [distinct 0 1] directWitness
        (distinct 0 1) ∧
      ProofWitness.Checks signature noDefinitions theorems twoBound [distinct 0 1] detourWitness
        (distinct 0 1) ∧
      directWitness ≠ detourWitness :=
  ⟨.hyp rfl, .conversion (.refl distinct_typed) (.hyp rfl), by simp [directWitness, detourWitness]⟩

/-- **Positive**: the identity substitution moves a checked witness to
itself. -/
theorem detour_moves_identity :
    Contextual.moveProof (identityList twoBound) detourWitness = detourWitness :=
  Contextual.moveProof_identity two_witnesses.2.1

end SubstitutionStabilityControls

#print axioms Substitution.Admissible.transport_fresh
#print axioms Substitution.Admissible.comp
#print axioms Substitution.admissible_identity
#print axioms Substitution.Admissible.converts
#print axioms Substitution.Admissible.derives
#print axioms Contextual.derivableFace
#print axioms Substitution.Admissible.checksConv
#print axioms Substitution.Admissible.checks
#print axioms Contextual.witnessFace
#print axioms Contextual.forgetWitness
#print axioms Contextual.forgetWitness_surjective
#print axioms SubstitutionStabilityControls.two_witnesses
#print axioms SubstitutionStabilityControls.independence_required

end Mettapedia.Languages.MM0.Kernel
